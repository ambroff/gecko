#[macro_use]
extern crate bitflags;
#[macro_use]
extern crate log;

mod command;
mod conv;
mod descriptors_cpu;
mod device;
mod internal;
mod pool;
mod resource;
mod root_constants;
mod window;

use hal::{
    adapter,
    format as f,
    image,
    memory,
    pso::PipelineStage,
    queue as q,
    Features,
    Hints,
    Limits,
};

use winapi::{
    shared::{dxgi, dxgi1_2, dxgi1_4, dxgi1_6, minwindef::TRUE, winerror},
    um::{d3d12, d3d12sdklayers, handleapi, synchapi, winbase},
    Interface,
};

use std::{
    borrow::Borrow,
    ffi::OsString,
    fmt,
    mem,
    os::windows::ffi::OsStringExt,
    //TODO: use parking_lot
    sync::{Arc, Mutex},
};

use self::descriptors_cpu::DescriptorCpuPool;

#[derive(Debug)]
pub(crate) struct HeapProperties {
    pub page_property: d3d12::D3D12_CPU_PAGE_PROPERTY,
    pub memory_pool: d3d12::D3D12_MEMORY_POOL,
}

// https://msdn.microsoft.com/de-de/library/windows/desktop/dn770377(v=vs.85).aspx
// Only 16 input slots allowed.
const MAX_VERTEX_BUFFERS: usize = 16;

const NUM_HEAP_PROPERTIES: usize = 3;

// Memory types are grouped according to the supported resources.
// Grouping is done to circumvent the limitations of heap tier 1 devices.
// Devices with Tier 1 will expose `BuffersOnl`, `ImageOnly` and `TargetOnly`.
// Devices with Tier 2 or higher will only expose `Universal`.
enum MemoryGroup {
    Universal = 0,
    BufferOnly,
    ImageOnly,
    TargetOnly,

    NumGroups,
}

// https://msdn.microsoft.com/de-de/library/windows/desktop/dn788678(v=vs.85).aspx
static HEAPS_NUMA: [HeapProperties; NUM_HEAP_PROPERTIES] = [
    // DEFAULT
    HeapProperties {
        page_property: d3d12::D3D12_CPU_PAGE_PROPERTY_NOT_AVAILABLE,
        memory_pool: d3d12::D3D12_MEMORY_POOL_L1,
    },
    // UPLOAD
    HeapProperties {
        page_property: d3d12::D3D12_CPU_PAGE_PROPERTY_WRITE_COMBINE,
        memory_pool: d3d12::D3D12_MEMORY_POOL_L0,
    },
    // READBACK
    HeapProperties {
        page_property: d3d12::D3D12_CPU_PAGE_PROPERTY_WRITE_BACK,
        memory_pool: d3d12::D3D12_MEMORY_POOL_L0,
    },
];

static HEAPS_UMA: [HeapProperties; NUM_HEAP_PROPERTIES] = [
    // DEFAULT
    HeapProperties {
        page_property: d3d12::D3D12_CPU_PAGE_PROPERTY_NOT_AVAILABLE,
        memory_pool: d3d12::D3D12_MEMORY_POOL_L0,
    },
    // UPLOAD
    HeapProperties {
        page_property: d3d12::D3D12_CPU_PAGE_PROPERTY_WRITE_COMBINE,
        memory_pool: d3d12::D3D12_MEMORY_POOL_L0,
    },
    // READBACK
    HeapProperties {
        page_property: d3d12::D3D12_CPU_PAGE_PROPERTY_WRITE_BACK,
        memory_pool: d3d12::D3D12_MEMORY_POOL_L0,
    },
];

static HEAPS_CCUMA: [HeapProperties; NUM_HEAP_PROPERTIES] = [
    // DEFAULT
    HeapProperties {
        page_property: d3d12::D3D12_CPU_PAGE_PROPERTY_NOT_AVAILABLE,
        memory_pool: d3d12::D3D12_MEMORY_POOL_L0,
    },
    // UPLOAD
    HeapProperties {
        page_property: d3d12::D3D12_CPU_PAGE_PROPERTY_WRITE_BACK,
        memory_pool: d3d12::D3D12_MEMORY_POOL_L0,
    },
    //READBACK
    HeapProperties {
        page_property: d3d12::D3D12_CPU_PAGE_PROPERTY_WRITE_BACK,
        memory_pool: d3d12::D3D12_MEMORY_POOL_L0,
    },
];

#[derive(Debug, Copy, Clone)]
pub enum QueueFamily {
    // Specially marked present queue.
    // It's basically a normal 3D queue but D3D12 swapchain creation requires an
    // associated queue, which we don't know on `create_swapchain`.
    Present,
    Normal(q::QueueType),
}

const MAX_QUEUES: usize = 16; // infinite, to be fair

impl q::QueueFamily for QueueFamily {
    fn queue_type(&self) -> q::QueueType {
        match *self {
            QueueFamily::Present => q::QueueType::General,
            QueueFamily::Normal(ty) => ty,
        }
    }
    fn max_queues(&self) -> usize {
        match *self {
            QueueFamily::Present => 1,
            QueueFamily::Normal(_) => MAX_QUEUES,
        }
    }
    fn id(&self) -> q::QueueFamilyId {
        // This must match the order exposed by `QUEUE_FAMILIES`
        q::QueueFamilyId(match *self {
            QueueFamily::Present => 0,
            QueueFamily::Normal(q::QueueType::General) => 1,
            QueueFamily::Normal(q::QueueType::Compute) => 2,
            QueueFamily::Normal(q::QueueType::Transfer) => 3,
            _ => unreachable!(),
        })
    }
}

impl QueueFamily {
    fn native_type(&self) -> native::CmdListType {
        use hal::queue::QueueFamily as _;
        use native::CmdListType as Clt;

        let queue_type = self.queue_type();
        match queue_type {
            q::QueueType::General | q::QueueType::Graphics => Clt::Direct,
            q::QueueType::Compute => Clt::Compute,
            q::QueueType::Transfer => Clt::Copy,
        }
    }
}

static QUEUE_FAMILIES: [QueueFamily; 4] = [
    QueueFamily::Present,
    QueueFamily::Normal(q::QueueType::General),
    QueueFamily::Normal(q::QueueType::Compute),
    QueueFamily::Normal(q::QueueType::Transfer),
];

//Note: fields are dropped in the order of declaration, so we put the
// most owning fields last.
pub struct PhysicalDevice {
    features: Features,
    hints: Hints,
    limits: Limits,
    format_properties: Arc<FormatProperties>,
    private_caps: Capabilities,
    heap_properties: &'static [HeapProperties; NUM_HEAP_PROPERTIES],
    memory_properties: adapter::MemoryProperties,
    // Indicates that there is currently an active logical device.
    // Opening the same adapter multiple times will return the same D3D12Device again.
    is_open: Arc<Mutex<bool>>,
    adapter: native::WeakPtr<dxgi1_2::IDXGIAdapter2>,
    library: Arc<native::D3D12Lib>,
}

impl fmt::Debug for PhysicalDevice {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str("PhysicalDevice")
    }
}

unsafe impl Send for PhysicalDevice {}
unsafe impl Sync for PhysicalDevice {}

impl adapter::PhysicalDevice<Backend> for PhysicalDevice {
    unsafe fn open(
        &self,
        families: &[(&QueueFamily, &[q::QueuePriority])],
        requested_features: Features,
    ) -> Result<adapter::Gpu<Backend>, hal::device::CreationError> {
        let lock = self.is_open.try_lock();
        let mut open_guard = match lock {
            Ok(inner) => inner,
            Err(_) => return Err(hal::device::CreationError::TooManyObjects),
        };

        if !self.features().contains(requested_features) {
            return Err(hal::device::CreationError::MissingFeature);
        }

        let device_raw = match self
            .library
            .create_device(self.adapter, native::FeatureLevel::L11_0)
        {
            Ok((device, hr)) if winerror::SUCCEEDED(hr) => device,
            Ok((_, hr)) => {
                error!("error on device creation: {:x}", hr);
                return Err(hal::device::CreationError::InitializationFailed);
            }
            Err(e) => panic!("device creation failed with {:?}", e),
        };

        // Always create the presentation queue in case we want to build a swapchain.
        let (present_queue, hr_queue) = device_raw.create_command_queue(
            QueueFamily::Present.native_type(),
            native::Priority::Normal,
            native::CommandQueueFlags::empty(),
            0,
        );
        if !winerror::SUCCEEDED(hr_queue) {
            error!("error on queue creation: {:x}", hr_queue);
        }

        let mut device = Device::new(device_raw, &self, present_queue);
        device.features = requested_features;

        let queue_groups = families
            .into_iter()
            .map(|&(&family, priorities)| {
                use hal::queue::QueueFamily as _;
                let mut group = q::QueueGroup::new(family.id());

                let create_idle_event = || native::Event::create(true, false);

                match family {
                    QueueFamily::Present => {
                        // Exactly **one** present queue!
                        // Number of queues need to be larger than 0 else it
                        // violates the specification.
                        let queue = CommandQueue {
                            raw: device.present_queue.clone(),
                            idle_fence: device.create_raw_fence(false),
                            idle_event: create_idle_event(),
                        };
                        device.append_queue(queue.clone());
                        group.add_queue(queue);
                    }
                    QueueFamily::Normal(_) => {
                        let list_type = family.native_type();
                        for _ in 0 .. priorities.len() {
                            let (queue, hr_queue) = device_raw.create_command_queue(
                                list_type,
                                native::Priority::Normal,
                                native::CommandQueueFlags::empty(),
                                0,
                            );

                            if winerror::SUCCEEDED(hr_queue) {
                                let queue = CommandQueue {
                                    raw: queue,
                                    idle_fence: device.create_raw_fence(false),
                                    idle_event: create_idle_event(),
                                };
                                device.append_queue(queue.clone());
                                group.add_queue(queue);
                            } else {
                                error!("error on queue creation: {:x}", hr_queue);
                            }
                        }
                    }
                }

                group
            })
            .collect();

        *open_guard = true;

        Ok(adapter::Gpu {
            device,
            queue_groups,
        })
    }

    fn format_properties(&self, fmt: Option<f::Format>) -> f::Properties {
        let idx = fmt.map(|fmt| fmt as usize).unwrap_or(0);
        self.format_properties.get(idx).properties
    }

    fn image_format_properties(
        &self,
        format: f::Format,
        dimensions: u8,
        tiling: image::Tiling,
        usage: image::Usage,
        view_caps: image::ViewCapabilities,
    ) -> Option<image::FormatProperties> {
        conv::map_format(format)?; //filter out unknown formats
        let format_info = self.format_properties.get(format as usize);

        let supported_usage = {
            use hal::image::Usage as U;
            let props = match tiling {
                image::Tiling::Optimal => format_info.properties.optimal_tiling,
                image::Tiling::Linear => format_info.properties.linear_tiling,
            };
            let mut flags = U::empty();
            // Note: these checks would have been nicer if we had explicit BLIT usage
            if props.contains(f::ImageFeature::BLIT_SRC) {
                flags |= U::TRANSFER_SRC;
            }
            if props.contains(f::ImageFeature::BLIT_DST) {
                flags |= U::TRANSFER_DST;
            }
            if props.contains(f::ImageFeature::SAMPLED) {
                flags |= U::SAMPLED;
            }
            if props.contains(f::ImageFeature::STORAGE) {
                flags |= U::STORAGE;
            }
            if props.contains(f::ImageFeature::COLOR_ATTACHMENT) {
                flags |= U::COLOR_ATTACHMENT;
            }
            if props.contains(f::ImageFeature::DEPTH_STENCIL_ATTACHMENT) {
                flags |= U::DEPTH_STENCIL_ATTACHMENT;
            }
            flags
        };
        if !supported_usage.contains(usage) {
            return None;
        }

        let max_resource_size =
            (d3d12::D3D12_REQ_RESOURCE_SIZE_IN_MEGABYTES_EXPRESSION_A_TERM as usize) << 20;
        Some(match tiling {
            image::Tiling::Optimal => image::FormatProperties {
                max_extent: match dimensions {
                    1 => image::Extent {
                        width: d3d12::D3D12_REQ_TEXTURE1D_U_DIMENSION,
                        height: 1,
                        depth: 1,
                    },
                    2 => image::Extent {
                        width: d3d12::D3D12_REQ_TEXTURE2D_U_OR_V_DIMENSION,
                        height: d3d12::D3D12_REQ_TEXTURE2D_U_OR_V_DIMENSION,
                        depth: 1,
                    },
                    3 => image::Extent {
                        width: d3d12::D3D12_REQ_TEXTURE3D_U_V_OR_W_DIMENSION,
                        height: d3d12::D3D12_REQ_TEXTURE3D_U_V_OR_W_DIMENSION,
                        depth: d3d12::D3D12_REQ_TEXTURE3D_U_V_OR_W_DIMENSION,
                    },
                    _ => return None,
                },
                max_levels: d3d12::D3D12_REQ_MIP_LEVELS as _,
                max_layers: match dimensions {
                    1 => d3d12::D3D12_REQ_TEXTURE1D_ARRAY_AXIS_DIMENSION as _,
                    2 => d3d12::D3D12_REQ_TEXTURE2D_ARRAY_AXIS_DIMENSION as _,
                    _ => return None,
                },
                sample_count_mask: if dimensions == 2
                    && !view_caps.contains(image::ViewCapabilities::KIND_CUBE)
                    && !usage.contains(image::Usage::STORAGE)
                {
                    format_info.sample_count_mask
                } else {
                    0x1
                },
                max_resource_size,
            },
            image::Tiling::Linear => image::FormatProperties {
                max_extent: match dimensions {
                    2 => image::Extent {
                        width: d3d12::D3D12_REQ_TEXTURE2D_U_OR_V_DIMENSION,
                        height: d3d12::D3D12_REQ_TEXTURE2D_U_OR_V_DIMENSION,
                        depth: 1,
                    },
                    _ => return None,
                },
                max_levels: 1,
                max_layers: 1,
                sample_count_mask: 0x1,
                max_resource_size,
            },
        })
    }

    fn memory_properties(&self) -> adapter::MemoryProperties {
        self.memory_properties.clone()
    }

    fn features(&self) -> Features {
        self.features
    }

    fn hints(&self) -> Hints {
        self.hints
    }

    fn limits(&self) -> Limits {
        self.limits
    }
}

#[derive(Clone)]
pub struct CommandQueue {
    pub(crate) raw: native::CommandQueue,
    idle_fence: native::Fence,
    idle_event: native::Event,
}

impl fmt::Debug for CommandQueue {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str("CommandQueue")
    }
}

impl CommandQueue {
    unsafe fn destroy(&self) {
        handleapi::CloseHandle(self.idle_event.0);
        self.idle_fence.destroy();
        self.raw.destroy();
    }
}

unsafe impl Send for CommandQueue {}
unsafe impl Sync for CommandQueue {}

impl q::CommandQueue<Backend> for CommandQueue {
    unsafe fn submit<'a, T, Ic, S, Iw, Is>(
        &mut self,
        submission: q::Submission<Ic, Iw, Is>,
        fence: Option<&resource::Fence>,
    ) where
        T: 'a + Borrow<command::CommandBuffer>,
        Ic: IntoIterator<Item = &'a T>,
        S: 'a + Borrow<resource::Semaphore>,
        Iw: IntoIterator<Item = (&'a S, PipelineStage)>,
        Is: IntoIterator<Item = &'a S>,
    {
        // Reset idle fence and event
        // That's safe here due to exclusive access to the queue
        self.idle_fence.signal(0);
        synchapi::ResetEvent(self.idle_event.0);

        // TODO: semaphores
        let mut lists = submission
            .command_buffers
            .into_iter()
            .map(|buf| buf.borrow().as_raw_list())
            .collect::<Vec<_>>();
        self.raw
            .ExecuteCommandLists(lists.len() as _, lists.as_mut_ptr());

        if let Some(fence) = fence {
            assert_eq!(winerror::S_OK, self.raw.Signal(fence.raw.as_mut_ptr(), 1));
        }
    }

    unsafe fn present<'a, W, Is, S, Iw>(
        &mut self,
        swapchains: Is,
        _wait_semaphores: Iw,
    ) -> Result<Option<hal::window::Suboptimal>, hal::window::PresentError>
    where
        W: 'a + Borrow<window::Swapchain>,
        Is: IntoIterator<Item = (&'a W, hal::window::SwapImageIndex)>,
        S: 'a + Borrow<resource::Semaphore>,
        Iw: IntoIterator<Item = &'a S>,
    {
        // TODO: semaphores
        for (swapchain, _) in swapchains {
            swapchain.borrow().inner.Present(1, 0);
        }

        Ok(None)
    }

    unsafe fn present_surface(
        &mut self,
        surface: &mut window::Surface,
        _image: resource::ImageView,
        _wait_semaphore: Option<&resource::Semaphore>,
    ) -> Result<Option<hal::window::Suboptimal>, hal::window::PresentError> {
        surface.present();
        Ok(None)
    }

    fn wait_idle(&self) -> Result<(), hal::device::OutOfMemory> {
        self.raw.signal(self.idle_fence, 1);
        assert_eq!(
            winerror::S_OK,
            self.idle_fence.set_event_on_completion(self.idle_event, 1)
        );

        unsafe {
            synchapi::WaitForSingleObject(self.idle_event.0, winbase::INFINITE);
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
enum MemoryArchitecture {
    NUMA,
    UMA,
    CacheCoherentUMA,
}

#[derive(Debug, Clone, Copy)]
pub struct Capabilities {
    heterogeneous_resource_heaps: bool,
    memory_architecture: MemoryArchitecture,
}

#[derive(Clone, Debug)]
struct CmdSignatures {
    draw: native::CommandSignature,
    draw_indexed: native::CommandSignature,
    dispatch: native::CommandSignature,
}

impl CmdSignatures {
    unsafe fn destroy(&self) {
        self.draw.destroy();
        self.draw_indexed.destroy();
        self.dispatch.destroy();
    }
}

// Shared objects between command buffers, owned by the device.
#[derive(Debug)]
struct Shared {
    pub signatures: CmdSignatures,
    pub service_pipes: internal::ServicePipes,
}

impl Shared {
    unsafe fn destroy(&self) {
        self.signatures.destroy();
        self.service_pipes.destroy();
    }
}

pub struct Device {
    raw: native::Device,
    private_caps: Capabilities,
    features: Features,
    format_properties: Arc<FormatProperties>,
    heap_properties: &'static [HeapProperties],
    // CPU only pools
    rtv_pool: Mutex<DescriptorCpuPool>,
    dsv_pool: Mutex<DescriptorCpuPool>,
    srv_uav_pool: Mutex<DescriptorCpuPool>,
    sampler_pool: Mutex<DescriptorCpuPool>,
    descriptor_update_pools: Mutex<Vec<descriptors_cpu::HeapLinear>>,
    // CPU/GPU descriptor heaps
    heap_srv_cbv_uav: Mutex<resource::DescriptorHeap>,
    heap_sampler: Mutex<resource::DescriptorHeap>,
    events: Mutex<Vec<native::Event>>,
    shared: Arc<Shared>,
    // Present queue exposed by the `Present` queue family.
    // Required for swapchain creation. Only a single queue supports presentation.
    present_queue: native::CommandQueue,
    // List of all queues created from this device, including present queue.
    // Needed for `wait_idle`.
    queues: Vec<CommandQueue>,
    // Indicates that there is currently an active device.
    open: Arc<Mutex<bool>>,
    library: Arc<native::D3D12Lib>,
}

impl fmt::Debug for Device {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str("Device")
    }
}

unsafe impl Send for Device {} //blocked by ComPtr
unsafe impl Sync for Device {} //blocked by ComPtr

impl Device {
    fn new(
        device: native::Device,
        physical_device: &PhysicalDevice,
        present_queue: native::CommandQueue,
    ) -> Self {
        // Allocate descriptor heaps
        let rtv_pool = DescriptorCpuPool::new(device, native::DescriptorHeapType::Rtv);
        let dsv_pool = DescriptorCpuPool::new(device, native::DescriptorHeapType::Dsv);
        let srv_uav_pool = DescriptorCpuPool::new(device, native::DescriptorHeapType::CbvSrvUav);
        let sampler_pool = DescriptorCpuPool::new(device, native::DescriptorHeapType::Sampler);

        let heap_srv_cbv_uav = Self::create_descriptor_heap_impl(
            device,
            native::DescriptorHeapType::CbvSrvUav,
            true,
            1_000_000, // maximum number of CBV/SRV/UAV descriptors in heap for Tier 1
        );

        let heap_sampler = Self::create_descriptor_heap_impl(
            device,
            native::DescriptorHeapType::Sampler,
            true,
            2_048,
        );

        let draw_signature = Self::create_command_signature(device, device::CommandSignature::Draw);
        let draw_indexed_signature =
            Self::create_command_signature(device, device::CommandSignature::DrawIndexed);
        let dispatch_signature =
            Self::create_command_signature(device, device::CommandSignature::Dispatch);

        let signatures = CmdSignatures {
            draw: draw_signature,
            draw_indexed: draw_indexed_signature,
            dispatch: dispatch_signature,
        };
        let service_pipes =
            internal::ServicePipes::new(device, Arc::clone(&physical_device.library));
        let shared = Shared {
            signatures,
            service_pipes,
        };

        Device {
            raw: device,
            library: Arc::clone(&physical_device.library),
            private_caps: physical_device.private_caps,
            features: Features::empty(),
            format_properties: physical_device.format_properties.clone(),
            heap_properties: physical_device.heap_properties,
            rtv_pool: Mutex::new(rtv_pool),
            dsv_pool: Mutex::new(dsv_pool),
            srv_uav_pool: Mutex::new(srv_uav_pool),
            sampler_pool: Mutex::new(sampler_pool),
            descriptor_update_pools: Mutex::new(Vec::new()),
            heap_srv_cbv_uav: Mutex::new(heap_srv_cbv_uav),
            heap_sampler: Mutex::new(heap_sampler),
            events: Mutex::new(Vec::new()),
            shared: Arc::new(shared),
            present_queue,
            queues: Vec::new(),
            open: Arc::clone(&physical_device.is_open),
        }
    }

    fn append_queue(&mut self, queue: CommandQueue) {
        self.queues.push(queue);
    }

    /// Get the native d3d12 device.
    ///
    /// Required for FFI with libraries like RenderDoc.
    pub unsafe fn as_raw(&self) -> *mut d3d12::ID3D12Device {
        self.raw.as_mut_ptr()
    }
}

impl Drop for Device {
    fn drop(&mut self) {
        *self.open.lock().unwrap() = false;

        unsafe {
            for queue in &mut self.queues {
                queue.destroy();
            }

            self.shared.destroy();
            self.heap_srv_cbv_uav.lock().unwrap().destroy();
            self.heap_sampler.lock().unwrap().destroy();
            self.rtv_pool.lock().unwrap().destroy();
            self.dsv_pool.lock().unwrap().destroy();
            self.srv_uav_pool.lock().unwrap().destroy();
            self.sampler_pool.lock().unwrap().destroy();

            for pool in &*self.descriptor_update_pools.lock().unwrap() {
                pool.destroy();
            }

            // Debug tracking alive objects
            let (debug_device, hr_debug) = self.raw.cast::<d3d12sdklayers::ID3D12DebugDevice>();
            if winerror::SUCCEEDED(hr_debug) {
                debug_device.ReportLiveDeviceObjects(d3d12sdklayers::D3D12_RLDO_DETAIL);
                debug_device.destroy();
            }

            self.raw.destroy();
        }
    }
}

#[derive(Debug)]
pub struct Instance {
    pub(crate) factory: native::Factory4,
    library: Arc<native::D3D12Lib>,
    lib_dxgi: native::DxgiLib,
}

impl Drop for Instance {
    fn drop(&mut self) {
        unsafe {
            self.factory.destroy();
        }
    }
}

unsafe impl Send for Instance {}
unsafe impl Sync for Instance {}

impl hal::Instance<Backend> for Instance {
    fn create(_: &str, _: u32) -> Result<Self, hal::UnsupportedBackend> {
        let lib_main = match native::D3D12Lib::new() {
            Ok(lib) => lib,
            Err(_) => return Err(hal::UnsupportedBackend),
        };

        #[cfg(debug_assertions)]
        {
            // Enable debug layer
            match lib_main.get_debug_interface() {
                Ok((debug_controller, hr)) if winerror::SUCCEEDED(hr) => {
                    debug_controller.enable_layer();
                    unsafe {
                        debug_controller.Release();
                    }
                }
                _ => {
                    warn!("Unable to get D3D12 debug interface");
                }
            }
        }

        let lib_dxgi = native::DxgiLib::new().unwrap();

        // The `DXGI_CREATE_FACTORY_DEBUG` flag is only allowed to be passed to
        // `CreateDXGIFactory2` if the debug interface is actually available. So
        // we check for whether it exists first.
        let factory_flags = match lib_dxgi.get_debug_interface1() {
            Ok((queue, hr)) if winerror::SUCCEEDED(hr) => {
                unsafe { queue.destroy() };
                native::FactoryCreationFlags::DEBUG
            }
            _ => native::FactoryCreationFlags::empty(),
        };

        // Create DXGI factory
        let factory = match lib_dxgi.create_factory2(factory_flags) {
            Ok((factory, hr)) if winerror::SUCCEEDED(hr) => factory,
            Ok((_, hr)) => {
                info!("Failed on dxgi factory creation: {:?}", hr);
                return Err(hal::UnsupportedBackend);
            }
            Err(_) => return Err(hal::UnsupportedBackend),
        };

        Ok(Instance {
            factory,
            library: Arc::new(lib_main),
            lib_dxgi,
        })
    }

    fn enumerate_adapters(&self) -> Vec<adapter::Adapter<Backend>> {
        use self::memory::Properties;

        // Try to use high performance order by default (returns None on Windows < 1803)
        let (use_f6, factory6) = unsafe {
            let (f6, hr) = self.factory.cast::<dxgi1_6::IDXGIFactory6>();
            if winerror::SUCCEEDED(hr) {
                // It's okay to decrement the refcount here because we
                // have another reference to the factory already owned by `self`.
                f6.destroy();
                (true, f6)
            } else {
                (false, native::WeakPtr::null())
            }
        };

        // Enumerate adapters
        let mut cur_index = 0;
        let mut adapters = Vec::new();
        loop {
            let adapter = if use_f6 {
                let mut adapter2 = native::WeakPtr::<dxgi1_2::IDXGIAdapter2>::null();
                let hr = unsafe {
                    factory6.EnumAdapterByGpuPreference(
                        cur_index,
                        2, // HIGH_PERFORMANCE
                        &dxgi1_2::IDXGIAdapter2::uuidof(),
                        adapter2.mut_void() as *mut *mut _,
                    )
                };

                if hr == winerror::DXGI_ERROR_NOT_FOUND {
                    break;
                }

                adapter2
            } else {
                let mut adapter1 = native::WeakPtr::<dxgi::IDXGIAdapter1>::null();
                let hr1 = unsafe {
                    self.factory
                        .EnumAdapters1(cur_index, adapter1.mut_void() as *mut *mut _)
                };

                if hr1 == winerror::DXGI_ERROR_NOT_FOUND {
                    break;
                }

                let (adapter2, hr2) = unsafe { adapter1.cast::<dxgi1_2::IDXGIAdapter2>() };
                if !winerror::SUCCEEDED(hr2) {
                    error!("Failed casting to Adapter2");
                    break;
                }

                unsafe {
                    adapter1.destroy();
                }
                adapter2
            };

            cur_index += 1;

            // Check for D3D12 support
            // Create temporary device to get physical device information
            let device = match self
                .library
                .create_device(adapter, native::FeatureLevel::L11_0)
            {
                Ok((device, hr)) if winerror::SUCCEEDED(hr) => device,
                _ => continue,
            };

            // We have found a possible adapter
            // acquire the device information
            let mut desc: dxgi1_2::DXGI_ADAPTER_DESC2 = unsafe { mem::zeroed() };
            unsafe {
                adapter.GetDesc2(&mut desc);
            }

            let device_name = {
                let len = desc.Description.iter().take_while(|&&c| c != 0).count();
                let name = <OsString as OsStringExt>::from_wide(&desc.Description[.. len]);
                name.to_string_lossy().into_owned()
            };

            let mut features_architecture: d3d12::D3D12_FEATURE_DATA_ARCHITECTURE =
                unsafe { mem::zeroed() };
            assert_eq!(winerror::S_OK, unsafe {
                device.CheckFeatureSupport(
                    d3d12::D3D12_FEATURE_ARCHITECTURE,
                    &mut features_architecture as *mut _ as *mut _,
                    mem::size_of::<d3d12::D3D12_FEATURE_DATA_ARCHITECTURE>() as _,
                )
            });

            let info = adapter::AdapterInfo {
                name: device_name,
                vendor: desc.VendorId as usize,
                device: desc.DeviceId as usize,
                device_type: if (desc.Flags & dxgi::DXGI_ADAPTER_FLAG_SOFTWARE) != 0 {
                    adapter::DeviceType::VirtualGpu
                } else if features_architecture.CacheCoherentUMA == TRUE {
                    adapter::DeviceType::IntegratedGpu
                } else {
                    adapter::DeviceType::DiscreteGpu
                },
            };

            let mut features: d3d12::D3D12_FEATURE_DATA_D3D12_OPTIONS = unsafe { mem::zeroed() };
            assert_eq!(winerror::S_OK, unsafe {
                device.CheckFeatureSupport(
                    d3d12::D3D12_FEATURE_D3D12_OPTIONS,
                    &mut features as *mut _ as *mut _,
                    mem::size_of::<d3d12::D3D12_FEATURE_DATA_D3D12_OPTIONS>() as _,
                )
            });

            let depth_bounds_test_supported = {
                let mut features2: d3d12::D3D12_FEATURE_DATA_D3D12_OPTIONS2 =
                    unsafe { mem::zeroed() };
                let hr = unsafe {
                    device.CheckFeatureSupport(
                        d3d12::D3D12_FEATURE_D3D12_OPTIONS2,
                        &mut features2 as *mut _ as *mut _,
                        mem::size_of::<d3d12::D3D12_FEATURE_DATA_D3D12_OPTIONS2>() as _,
                    )
                };
                if hr == winerror::S_OK {
                    features2.DepthBoundsTestSupported != 0
                } else {
                    false
                }
            };

            let heterogeneous_resource_heaps =
                features.ResourceHeapTier != d3d12::D3D12_RESOURCE_HEAP_TIER_1;

            let uma = features_architecture.UMA == TRUE;
            let cc_uma = features_architecture.CacheCoherentUMA == TRUE;

            let (memory_architecture, heap_properties) = match (uma, cc_uma) {
                (true, true) => (MemoryArchitecture::CacheCoherentUMA, &HEAPS_CCUMA),
                (true, false) => (MemoryArchitecture::UMA, &HEAPS_UMA),
                (false, _) => (MemoryArchitecture::NUMA, &HEAPS_NUMA),
            };

            // https://msdn.microsoft.com/en-us/library/windows/desktop/dn788678(v=vs.85).aspx
            let base_memory_types: [adapter::MemoryType; NUM_HEAP_PROPERTIES] =
                match memory_architecture {
                    MemoryArchitecture::NUMA => [
                        // DEFAULT
                        adapter::MemoryType {
                            properties: Properties::DEVICE_LOCAL,
                            heap_index: 0,
                        },
                        // UPLOAD
                        adapter::MemoryType {
                            properties: Properties::CPU_VISIBLE | Properties::COHERENT,
                            heap_index: 1,
                        },
                        // READBACK
                        adapter::MemoryType {
                            properties: Properties::CPU_VISIBLE
                                | Properties::COHERENT
                                | Properties::CPU_CACHED,
                            heap_index: 1,
                        },
                    ],
                    MemoryArchitecture::UMA => [
                        // DEFAULT
                        adapter::MemoryType {
                            properties: Properties::DEVICE_LOCAL,
                            heap_index: 0,
                        },
                        // UPLOAD
                        adapter::MemoryType {
                            properties: Properties::DEVICE_LOCAL
                                | Properties::CPU_VISIBLE
                                | Properties::COHERENT,
                            heap_index: 0,
                        },
                        // READBACK
                        adapter::MemoryType {
                            properties: Properties::DEVICE_LOCAL
                                | Properties::CPU_VISIBLE
                                | Properties::COHERENT
                                | Properties::CPU_CACHED,
                            heap_index: 0,
                        },
                    ],
                    MemoryArchitecture::CacheCoherentUMA => [
                        // DEFAULT
                        adapter::MemoryType {
                            properties: Properties::DEVICE_LOCAL,
                            heap_index: 0,
                        },
                        // UPLOAD
                        adapter::MemoryType {
                            properties: Properties::DEVICE_LOCAL
                                | Properties::CPU_VISIBLE
                                | Properties::COHERENT
                                | Properties::CPU_CACHED,
                            heap_index: 0,
                        },
                        // READBACK
                        adapter::MemoryType {
                            properties: Properties::DEVICE_LOCAL
                                | Properties::CPU_VISIBLE
                                | Properties::COHERENT
                                | Properties::CPU_CACHED,
                            heap_index: 0,
                        },
                    ],
                };

            let memory_types = if heterogeneous_resource_heaps {
                base_memory_types.to_vec()
            } else {
                // We multiplicate the base memory types depending on the resource usage:
                //     0.. 3: Reserved for futures use
                //     4.. 6: Buffers
                //     7.. 9: Images
                //    10..12: Targets
                //
                // The supported memory types for a resource can be requested by asking for
                // the memory requirements. Memory type indices are encoded as bitflags.
                // `device::MEM_TYPE_MASK` (0b111) defines the bitmask for one base memory type group.
                // The corresponding shift masks (`device::MEM_TYPE_BUFFER_SHIFT`,
                // `device::MEM_TYPE_IMAGE_SHIFT`, `device::MEM_TYPE_TARGET_SHIFT`)
                // denote the usage group.
                let mut types = Vec::new();
                for i in 0 .. MemoryGroup::NumGroups as _ {
                    types.extend(base_memory_types.iter().map(|mem_type| {
                        let mut ty = mem_type.clone();

                        // Images and Targets are not host visible as we can't create
                        // a corresponding buffer for mapping.
                        if i == MemoryGroup::ImageOnly as _ || i == MemoryGroup::TargetOnly as _ {
                            ty.properties.remove(Properties::CPU_VISIBLE);
                            // Coherent and cached can only be on memory types that are cpu visible
                            ty.properties.remove(Properties::COHERENT);
                            ty.properties.remove(Properties::CPU_CACHED);
                        }
                        ty
                    }));
                }
                types
            };

            let memory_heaps = {
                // Get the IDXGIAdapter3 from the created device to query video memory information.
                let adapter_id = unsafe { device.GetAdapterLuid() };
                let adapter = {
                    let mut adapter = native::WeakPtr::<dxgi1_4::IDXGIAdapter3>::null();
                    unsafe {
                        assert_eq!(
                            winerror::S_OK,
                            self.factory.EnumAdapterByLuid(
                                adapter_id,
                                &dxgi1_4::IDXGIAdapter3::uuidof(),
                                adapter.mut_void(),
                            )
                        );
                    }
                    adapter
                };

                let query_memory = |segment: dxgi1_4::DXGI_MEMORY_SEGMENT_GROUP| unsafe {
                    let mut mem_info: dxgi1_4::DXGI_QUERY_VIDEO_MEMORY_INFO = mem::zeroed();
                    assert_eq!(
                        winerror::S_OK,
                        adapter.QueryVideoMemoryInfo(0, segment, &mut mem_info)
                    );
                    mem_info.Budget
                };

                let local = query_memory(dxgi1_4::DXGI_MEMORY_SEGMENT_GROUP_LOCAL);
                match memory_architecture {
                    MemoryArchitecture::NUMA => {
                        let non_local = query_memory(dxgi1_4::DXGI_MEMORY_SEGMENT_GROUP_NON_LOCAL);
                        vec![local, non_local]
                    }
                    _ => vec![local],
                }
            };
            //TODO: find a way to get a tighter bound?
            let sample_count_mask = 0x3F;

            let physical_device = PhysicalDevice {
                library: Arc::clone(&self.library),
                adapter,
                features:
                    // TODO: add more features, based on
                    // https://msdn.microsoft.com/de-de/library/windows/desktop/mt186615(v=vs.85).aspx
                    Features::ROBUST_BUFFER_ACCESS |
                    Features::IMAGE_CUBE_ARRAY |
                    Features::GEOMETRY_SHADER |
                    Features::TESSELLATION_SHADER |
                    Features::NON_FILL_POLYGON_MODE |
                    if depth_bounds_test_supported { Features::DEPTH_BOUNDS } else { Features::empty() } |
                    //logic_op: false, // Optional on feature level 11_0
                    Features::MULTI_DRAW_INDIRECT |
                    Features::FORMAT_BC |
                    Features::INSTANCE_RATE |
                    Features::SAMPLER_MIP_LOD_BIAS |
                    Features::SAMPLER_ANISOTROPY |
                    Features::TEXTURE_DESCRIPTOR_ARRAY |
                    Features::SAMPLER_MIRROR_CLAMP_EDGE |
                    Features::NDC_Y_UP |
                    Features::SAMPLED_TEXTURE_DESCRIPTOR_INDEXING |
                    Features::STORAGE_TEXTURE_DESCRIPTOR_INDEXING |
                    Features::UNSIZED_DESCRIPTOR_ARRAY |
                    Features::DRAW_INDIRECT_COUNT,
                hints:
                    Hints::BASE_VERTEX_INSTANCE_DRAWING,
                limits: Limits { // TODO
                    max_image_1d_size: d3d12::D3D12_REQ_TEXTURE1D_U_DIMENSION as _,
                    max_image_2d_size: d3d12::D3D12_REQ_TEXTURE2D_U_OR_V_DIMENSION as _,
                    max_image_3d_size: d3d12::D3D12_REQ_TEXTURE3D_U_V_OR_W_DIMENSION as _,
                    max_image_cube_size: d3d12::D3D12_REQ_TEXTURECUBE_DIMENSION as _,
                    max_image_array_layers: d3d12::D3D12_REQ_TEXTURE2D_ARRAY_AXIS_DIMENSION as _,
                    max_texel_elements: 0,
                    max_patch_size: 0,
                    max_viewports: d3d12::D3D12_VIEWPORT_AND_SCISSORRECT_OBJECT_COUNT_PER_PIPELINE as _,
                    max_viewport_dimensions: [d3d12::D3D12_VIEWPORT_BOUNDS_MAX as _; 2],
                    max_framebuffer_extent: hal::image::Extent { //TODO
                        width: 4096,
                        height: 4096,
                        depth: 1,
                    },
                    max_compute_work_group_count: [
                        d3d12::D3D12_CS_THREAD_GROUP_MAX_X,
                        d3d12::D3D12_CS_THREAD_GROUP_MAX_Y,
                        d3d12::D3D12_CS_THREAD_GROUP_MAX_Z,
                    ],
                    max_compute_work_group_size: [
                        d3d12::D3D12_CS_THREAD_GROUP_MAX_THREADS_PER_GROUP,
                        1, //TODO
                        1, //TODO
                    ],
                    max_vertex_input_attributes: d3d12::D3D12_IA_VERTEX_INPUT_RESOURCE_SLOT_COUNT as _,
                    max_vertex_input_bindings: 31, //TODO
                    max_vertex_input_attribute_offset: 255, // TODO
                    max_vertex_input_binding_stride: d3d12::D3D12_REQ_MULTI_ELEMENT_STRUCTURE_SIZE_IN_BYTES as _,
                    max_vertex_output_components: 16, // TODO
                    min_texel_buffer_offset_alignment: 1, // TODO
                    min_uniform_buffer_offset_alignment: 256, // Required alignment for CBVs
                    min_storage_buffer_offset_alignment: 1, // TODO
                    framebuffer_color_sample_counts: sample_count_mask,
                    framebuffer_depth_sample_counts: sample_count_mask,
                    framebuffer_stencil_sample_counts: sample_count_mask,
                    max_color_attachments: d3d12::D3D12_SIMULTANEOUS_RENDER_TARGET_COUNT as _,
                    buffer_image_granularity: 1,
                    non_coherent_atom_size: 1, //TODO: confirm
                    max_sampler_anisotropy: 16.,
                    optimal_buffer_copy_offset_alignment: d3d12::D3D12_TEXTURE_DATA_PLACEMENT_ALIGNMENT as _,
                    optimal_buffer_copy_pitch_alignment: d3d12::D3D12_TEXTURE_DATA_PITCH_ALIGNMENT as _,
                    min_vertex_input_binding_stride_alignment: 1,
                    .. Limits::default() //TODO
                },
                format_properties: Arc::new(FormatProperties::new(device)),
                private_caps: Capabilities {
                    heterogeneous_resource_heaps,
                    memory_architecture,
                },
                heap_properties,
                memory_properties: adapter::MemoryProperties {
                    memory_types,
                    memory_heaps,
                },
                is_open: Arc::new(Mutex::new(false)),
            };

            let queue_families = QUEUE_FAMILIES.to_vec();

            adapters.push(adapter::Adapter {
                info,
                physical_device,
                queue_families,
            });
        }
        adapters
    }

    unsafe fn create_surface(
        &self,
        has_handle: &impl raw_window_handle::HasRawWindowHandle,
    ) -> Result<window::Surface, hal::window::InitError> {
        match has_handle.raw_window_handle() {
            raw_window_handle::RawWindowHandle::Windows(handle) => {
                Ok(self.create_surface_from_hwnd(handle.hwnd))
            }
            _ => Err(hal::window::InitError::UnsupportedWindowHandle),
        }
    }

    unsafe fn destroy_surface(&self, _surface: window::Surface) {
        // TODO: Implement Surface cleanup
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum Backend {}
impl hal::Backend for Backend {
    type Instance = Instance;
    type PhysicalDevice = PhysicalDevice;
    type Device = Device;

    type Surface = window::Surface;
    type Swapchain = window::Swapchain;

    type QueueFamily = QueueFamily;
    type CommandQueue = CommandQueue;
    type CommandBuffer = command::CommandBuffer;

    type Memory = resource::Memory;
    type CommandPool = pool::CommandPool;

    type ShaderModule = resource::ShaderModule;
    type RenderPass = resource::RenderPass;
    type Framebuffer = resource::Framebuffer;

    type Buffer = resource::Buffer;
    type BufferView = resource::BufferView;
    type Image = resource::Image;
    type ImageView = resource::ImageView;
    type Sampler = resource::Sampler;

    type ComputePipeline = resource::ComputePipeline;
    type GraphicsPipeline = resource::GraphicsPipeline;
    type PipelineLayout = resource::PipelineLayout;
    type PipelineCache = ();
    type DescriptorSetLayout = resource::DescriptorSetLayout;
    type DescriptorPool = resource::DescriptorPool;
    type DescriptorSet = resource::DescriptorSet;

    type Fence = resource::Fence;
    type Semaphore = resource::Semaphore;
    type Event = ();
    type QueryPool = resource::QueryPool;
}

fn validate_line_width(width: f32) {
    // Note from the Vulkan spec:
    // > If the wide lines feature is not enabled, lineWidth must be 1.0
    // Simply assert and no-op because DX12 never exposes `Features::LINE_WIDTH`
    assert_eq!(width, 1.0);
}

#[derive(Clone, Copy, Debug, Default)]
struct FormatInfo {
    properties: f::Properties,
    sample_count_mask: u8,
}

#[derive(Debug)]
pub struct FormatProperties {
    info: Box<[Mutex<Option<FormatInfo>>]>,
    device: native::Device,
}

impl Drop for FormatProperties {
    fn drop(&mut self) {
        unsafe {
            self.device.destroy();
        }
    }
}

impl FormatProperties {
    fn new(device: native::Device) -> Self {
        let mut buf = Vec::with_capacity(f::NUM_FORMATS);
        buf.push(Mutex::new(Some(FormatInfo::default())));
        for _ in 1 .. f::NUM_FORMATS {
            buf.push(Mutex::new(None))
        }
        FormatProperties {
            info: buf.into_boxed_slice(),
            device,
        }
    }

    fn get(&self, idx: usize) -> FormatInfo {
        let mut guard = self.info[idx].lock().unwrap();
        if let Some(info) = *guard {
            return info;
        }
        let format: f::Format = unsafe { mem::transmute(idx as u32) };
        let dxgi_format = match conv::map_format(format) {
            Some(format) => format,
            None => {
                let info = FormatInfo::default();
                *guard = Some(info);
                return info;
            }
        };

        let properties = {
            let mut props = f::Properties::default();
            let mut data = d3d12::D3D12_FEATURE_DATA_FORMAT_SUPPORT {
                Format: dxgi_format,
                Support1: unsafe { mem::zeroed() },
                Support2: unsafe { mem::zeroed() },
            };
            assert_eq!(winerror::S_OK, unsafe {
                self.device.CheckFeatureSupport(
                    d3d12::D3D12_FEATURE_FORMAT_SUPPORT,
                    &mut data as *mut _ as *mut _,
                    mem::size_of::<d3d12::D3D12_FEATURE_DATA_FORMAT_SUPPORT>() as _,
                )
            });
            let can_buffer = 0 != data.Support1 & d3d12::D3D12_FORMAT_SUPPORT1_BUFFER;
            let can_image = 0
                != data.Support1
                    & (d3d12::D3D12_FORMAT_SUPPORT1_TEXTURE1D
                        | d3d12::D3D12_FORMAT_SUPPORT1_TEXTURE2D
                        | d3d12::D3D12_FORMAT_SUPPORT1_TEXTURE3D
                        | d3d12::D3D12_FORMAT_SUPPORT1_TEXTURECUBE);
            let can_linear = can_image && !format.surface_desc().is_compressed();
            if can_image {
                props.optimal_tiling |= f::ImageFeature::SAMPLED | f::ImageFeature::BLIT_SRC;
            }
            if can_linear {
                props.linear_tiling |= f::ImageFeature::SAMPLED | f::ImageFeature::BLIT_SRC;
            }
            if data.Support1 & d3d12::D3D12_FORMAT_SUPPORT1_IA_VERTEX_BUFFER != 0 {
                props.buffer_features |= f::BufferFeature::VERTEX;
            }
            if data.Support1 & d3d12::D3D12_FORMAT_SUPPORT1_SHADER_SAMPLE != 0 {
                props.optimal_tiling |= f::ImageFeature::SAMPLED_LINEAR;
            }
            if data.Support1 & d3d12::D3D12_FORMAT_SUPPORT1_RENDER_TARGET != 0 {
                props.optimal_tiling |=
                    f::ImageFeature::COLOR_ATTACHMENT | f::ImageFeature::BLIT_DST;
                if can_linear {
                    props.linear_tiling |=
                        f::ImageFeature::COLOR_ATTACHMENT | f::ImageFeature::BLIT_DST;
                }
            }
            if data.Support1 & d3d12::D3D12_FORMAT_SUPPORT1_BLENDABLE != 0 {
                props.optimal_tiling |= f::ImageFeature::COLOR_ATTACHMENT_BLEND;
            }
            if data.Support1 & d3d12::D3D12_FORMAT_SUPPORT1_DEPTH_STENCIL != 0 {
                props.optimal_tiling |= f::ImageFeature::DEPTH_STENCIL_ATTACHMENT;
            }
            if data.Support1 & d3d12::D3D12_FORMAT_SUPPORT1_SHADER_LOAD != 0 {
                //TODO: check d3d12::D3D12_FORMAT_SUPPORT2_UAV_TYPED_LOAD ?
                if can_buffer {
                    props.buffer_features |= f::BufferFeature::UNIFORM_TEXEL;
                }
            }
            if data.Support2 & d3d12::D3D12_FORMAT_SUPPORT2_UAV_ATOMIC_ADD != 0 {
                //TODO: other atomic flags?
                if can_buffer {
                    props.buffer_features |= f::BufferFeature::STORAGE_TEXEL_ATOMIC;
                }
                if can_image {
                    props.optimal_tiling |= f::ImageFeature::STORAGE_ATOMIC;
                }
            }
            if data.Support2 & d3d12::D3D12_FORMAT_SUPPORT2_UAV_TYPED_STORE != 0 {
                if can_buffer {
                    props.buffer_features |= f::BufferFeature::STORAGE_TEXEL;
                }
                if can_image {
                    props.optimal_tiling |= f::ImageFeature::STORAGE;
                }
            }
            //TODO: blits, linear tiling
            props
        };

        let mut sample_count_mask = 0;
        for i in 0 .. 6 {
            let mut data = d3d12::D3D12_FEATURE_DATA_MULTISAMPLE_QUALITY_LEVELS {
                Format: dxgi_format,
                SampleCount: 1 << i,
                Flags: 0,
                NumQualityLevels: 0,
            };
            assert_eq!(winerror::S_OK, unsafe {
                self.device.CheckFeatureSupport(
                    d3d12::D3D12_FEATURE_MULTISAMPLE_QUALITY_LEVELS,
                    &mut data as *mut _ as *mut _,
                    mem::size_of::<d3d12::D3D12_FEATURE_DATA_MULTISAMPLE_QUALITY_LEVELS>() as _,
                )
            });
            if data.NumQualityLevels != 0 {
                sample_count_mask |= 1 << i;
            }
        }

        let info = FormatInfo {
            properties,
            sample_count_mask,
        };
        *guard = Some(info);
        info
    }
}
