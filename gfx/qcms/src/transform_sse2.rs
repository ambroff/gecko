use crate::transform::{qcms_transform, Format, BGRA, CLAMPMAXVAL, FLOATSCALE, RGB, RGBA};
use ::libc;
#[cfg(target_arch = "x86")]
pub use std::arch::x86::{
    __m128, __m128i, _mm_add_ps, _mm_cvtps_epi32, _mm_load_ps, _mm_load_ss, _mm_max_ps, _mm_min_ps,
    _mm_mul_ps, _mm_set1_ps, _mm_setzero_ps, _mm_shuffle_ps, _mm_store_si128,
};
#[cfg(target_arch = "x86_64")]
pub use std::arch::x86_64::{
    __m128, __m128i, _mm_add_ps, _mm_cvtps_epi32, _mm_load_ps, _mm_load_ss, _mm_max_ps, _mm_min_ps,
    _mm_mul_ps, _mm_set1_ps, _mm_setzero_ps, _mm_shuffle_ps, _mm_store_si128,
};

#[repr(align(16))]
struct Output([u32; 4]);

unsafe extern "C" fn qcms_transform_data_template_lut_sse2<F: Format>(
    mut transform: *const qcms_transform,
    mut src: *const libc::c_uchar,
    mut dest: *mut libc::c_uchar,
    mut length: usize,
) {
    let mut mat: *const [f32; 4] = (*transform).matrix.as_ptr();
    let mut input: Output = std::mem::zeroed();
    /* share input and output locations to save having to keep the
     * locations in separate registers */
    let mut output: *const u32 = &mut input as *mut Output as *mut u32;
    /* deref *transform now to avoid it in loop */
    let mut igtbl_r: *const f32 = (*transform).input_gamma_table_r.as_ref().unwrap().as_ptr();
    let mut igtbl_g: *const f32 = (*transform).input_gamma_table_g.as_ref().unwrap().as_ptr();
    let mut igtbl_b: *const f32 = (*transform).input_gamma_table_b.as_ref().unwrap().as_ptr();
    /* deref *transform now to avoid it in loop */
    let mut otdata_r: *const u8 = (*transform)
        .output_table_r
        .as_deref()
        .unwrap()
        .data
        .as_ptr();
    let mut otdata_g: *const u8 = (*transform)
        .output_table_g
        .as_deref()
        .unwrap()
        .data
        .as_ptr();
    let mut otdata_b: *const u8 = (*transform)
        .output_table_b
        .as_deref()
        .unwrap()
        .data
        .as_ptr();
    /* input matrix values never change */
    let mat0: __m128 = _mm_load_ps((*mat.offset(0isize)).as_ptr());
    let mat1: __m128 = _mm_load_ps((*mat.offset(1isize)).as_ptr());
    let mat2: __m128 = _mm_load_ps((*mat.offset(2isize)).as_ptr());
    /* these values don't change, either */
    let max: __m128 = _mm_set1_ps(CLAMPMAXVAL);
    let min: __m128 = _mm_setzero_ps();
    let scale: __m128 = _mm_set1_ps(FLOATSCALE);
    let components: libc::c_uint = if F::kAIndex == 0xff { 3 } else { 4 } as libc::c_uint;
    /* working variables */
    let mut vec_r: __m128;
    let mut vec_g: __m128;
    let mut vec_b: __m128;
    let mut result: __m128;
    let mut alpha: libc::c_uchar = 0;
    /* CYA */
    if length == 0 {
        return;
    }
    /* one pixel is handled outside of the loop */
    length = length - 1;
    /* setup for transforming 1st pixel */
    vec_r = _mm_load_ss(&*igtbl_r.offset(*src.offset(F::kRIndex as isize) as isize));
    vec_g = _mm_load_ss(&*igtbl_g.offset(*src.offset(F::kGIndex as isize) as isize));
    vec_b = _mm_load_ss(&*igtbl_b.offset(*src.offset(F::kBIndex as isize) as isize));
    if F::kAIndex != 0xff {
        alpha = *src.offset(F::kAIndex as isize)
    }
    src = src.offset(components as isize);
    let mut i: libc::c_uint = 0;
    while (i as usize) < length {
        /* position values from gamma tables */
        vec_r = _mm_shuffle_ps(vec_r, vec_r, 0);
        vec_g = _mm_shuffle_ps(vec_g, vec_g, 0);
        vec_b = _mm_shuffle_ps(vec_b, vec_b, 0);
        /* gamma * matrix */
        vec_r = _mm_mul_ps(vec_r, mat0);
        vec_g = _mm_mul_ps(vec_g, mat1);
        vec_b = _mm_mul_ps(vec_b, mat2);
        /* store alpha for this pixel; load alpha for next */
        if F::kAIndex != 0xff {
            *dest.offset(F::kAIndex as isize) = alpha;
            alpha = *src.offset(F::kAIndex as isize)
        }
        /* crunch, crunch, crunch */
        vec_r = _mm_add_ps(vec_r, _mm_add_ps(vec_g, vec_b));
        vec_r = _mm_max_ps(min, vec_r);
        vec_r = _mm_min_ps(max, vec_r);
        result = _mm_mul_ps(vec_r, scale);
        /* store calc'd output tables indices */
        _mm_store_si128(output as *mut __m128i, _mm_cvtps_epi32(result));
        /* load gamma values for next loop while store completes */
        vec_r = _mm_load_ss(&*igtbl_r.offset(*src.offset(F::kRIndex as isize) as isize));
        vec_g = _mm_load_ss(&*igtbl_g.offset(*src.offset(F::kGIndex as isize) as isize));
        vec_b = _mm_load_ss(&*igtbl_b.offset(*src.offset(F::kBIndex as isize) as isize));
        src = src.offset(components as isize);
        /* use calc'd indices to output RGB values */
        *dest.offset(F::kRIndex as isize) = *otdata_r.offset(*output.offset(0isize) as isize);
        *dest.offset(F::kGIndex as isize) = *otdata_g.offset(*output.offset(1isize) as isize);
        *dest.offset(F::kBIndex as isize) = *otdata_b.offset(*output.offset(2isize) as isize);
        dest = dest.offset(components as isize);
        i = i + 1
    }
    /* handle final (maybe only) pixel */
    vec_r = _mm_shuffle_ps(vec_r, vec_r, 0);
    vec_g = _mm_shuffle_ps(vec_g, vec_g, 0);
    vec_b = _mm_shuffle_ps(vec_b, vec_b, 0);
    vec_r = _mm_mul_ps(vec_r, mat0);
    vec_g = _mm_mul_ps(vec_g, mat1);
    vec_b = _mm_mul_ps(vec_b, mat2);
    if F::kAIndex != 0xff {
        *dest.offset(F::kAIndex as isize) = alpha
    }
    vec_r = _mm_add_ps(vec_r, _mm_add_ps(vec_g, vec_b));
    vec_r = _mm_max_ps(min, vec_r);
    vec_r = _mm_min_ps(max, vec_r);
    result = _mm_mul_ps(vec_r, scale);
    _mm_store_si128(output as *mut __m128i, _mm_cvtps_epi32(result));
    *dest.offset(F::kRIndex as isize) = *otdata_r.offset(*output.offset(0isize) as isize);
    *dest.offset(F::kGIndex as isize) = *otdata_g.offset(*output.offset(1isize) as isize);
    *dest.offset(F::kBIndex as isize) = *otdata_b.offset(*output.offset(2isize) as isize);
}
#[no_mangle]
pub unsafe extern "C" fn qcms_transform_data_rgb_out_lut_sse2(
    mut transform: *const qcms_transform,
    mut src: *const libc::c_uchar,
    mut dest: *mut libc::c_uchar,
    mut length: usize,
) {
    qcms_transform_data_template_lut_sse2::<RGB>(transform, src, dest, length);
}
#[no_mangle]
pub unsafe extern "C" fn qcms_transform_data_rgba_out_lut_sse2(
    mut transform: *const qcms_transform,
    mut src: *const libc::c_uchar,
    mut dest: *mut libc::c_uchar,
    mut length: usize,
) {
    qcms_transform_data_template_lut_sse2::<RGBA>(transform, src, dest, length);
}

#[no_mangle]
pub unsafe extern "C" fn qcms_transform_data_bgra_out_lut_sse2(
    mut transform: *const qcms_transform,
    mut src: *const libc::c_uchar,
    mut dest: *mut libc::c_uchar,
    mut length: usize,
) {
    qcms_transform_data_template_lut_sse2::<BGRA>(transform, src, dest, length);
}
