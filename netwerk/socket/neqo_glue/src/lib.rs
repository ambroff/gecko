/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

use neqo_common::{self as common, qlog::NeqoQlog, qwarn, Datagram, Role};
use neqo_common::event::Provider;
use neqo_crypto::{init, PRErrorCode};
use neqo_http3::Error as Http3Error;
use neqo_http3::{Http3Client, Http3ClientEvent, Http3Parameters, Http3State};
use neqo_qpack::QpackSettings;
use neqo_transport::Error as TransportError;
use neqo_transport::{CongestionControlAlgorithm, FixedConnectionIdManager, Output, QuicVersion};
use nserror::*;
use nsstring::*;
use qlog::QlogStreamer;
use std::cell::RefCell;
use std::convert::TryFrom;
use std::fs::OpenOptions;
use std::net::SocketAddr;
use std::path::PathBuf;
use std::ptr;
use std::rc::Rc;
use std::slice;
use std::str;
use std::time::Instant;
use thin_vec::ThinVec;
use xpcom::{interfaces::nsrefcnt, AtomicRefcnt, RefCounted, RefPtr};

#[repr(C)]
pub struct NeqoHttp3Conn {
    conn: Http3Client,
    local_addr: SocketAddr,
    remote_addr: SocketAddr,
    refcnt: AtomicRefcnt,
    packets_to_send: Vec<Datagram>,
}

impl NeqoHttp3Conn {
    fn new(
        origin: &nsACString,
        alpn: &nsACString,
        local_addr: &nsACString,
        remote_addr: &nsACString,
        max_table_size: u64,
        max_blocked_streams: u16,
        qlog_dir: &nsACString,
    ) -> Result<RefPtr<NeqoHttp3Conn>, nsresult> {
        // Nss init.
        init();

        let origin_conv = str::from_utf8(origin).map_err(|_| NS_ERROR_INVALID_ARG)?;

        let alpn_conv = str::from_utf8(alpn).map_err(|_| NS_ERROR_INVALID_ARG)?;

        let local: SocketAddr = match str::from_utf8(local_addr) {
            Ok(s) => match s.parse() {
                Ok(addr) => addr,
                Err(_) => return Err(NS_ERROR_INVALID_ARG),
            },
            Err(_) => return Err(NS_ERROR_INVALID_ARG),
        };

        let remote: SocketAddr = match str::from_utf8(remote_addr) {
            Ok(s) => match s.parse() {
                Ok(addr) => addr,
                Err(_) => return Err(NS_ERROR_INVALID_ARG),
            },
            Err(_) => return Err(NS_ERROR_INVALID_ARG),
        };

        let http3_settings = Http3Parameters {
            qpack_settings: QpackSettings {
                max_table_size_encoder: max_table_size,
                max_table_size_decoder: max_table_size,
                max_blocked_streams,
            },
            max_concurrent_push_streams: 0,
        };

        let quic_version = match alpn_conv {
            "h3-30" => QuicVersion::Draft30,
            "h3-29" => QuicVersion::Draft29,
            "h3-28" => QuicVersion::Draft28,
            "h3-27" => QuicVersion::Draft27,
            _ => return Err(NS_ERROR_INVALID_ARG),
        };

        let mut conn = match Http3Client::new(
            origin_conv,
            Rc::new(RefCell::new(FixedConnectionIdManager::new(3))),
            local,
            remote,
            &CongestionControlAlgorithm::NewReno,
            quic_version,
            &http3_settings,
        ) {
            Ok(c) => c,
            Err(_) => return Err(NS_ERROR_INVALID_ARG),
        };

        if !qlog_dir.is_empty() {
            let qlog_dir_conv = str::from_utf8(qlog_dir).map_err(|_| NS_ERROR_INVALID_ARG)?;
            let mut qlog_path = PathBuf::from(qlog_dir_conv);
            qlog_path.push(format!("{}.qlog", origin));

            // Emit warnings but to not return an error if qlog initialization
            // fails.
            match OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(&qlog_path)
            {
                Err(_) => qwarn!("Could not open qlog path: {}", qlog_path.display()),
                Ok(f) => {
                    let streamer = QlogStreamer::new(
                        qlog::QLOG_VERSION.to_string(),
                        Some("Firefox Client qlog".to_string()),
                        Some("Firefox Client qlog".to_string()),
                        None,
                        std::time::Instant::now(),
                        common::qlog::new_trace(Role::Client),
                        Box::new(f),
                    );

                    match NeqoQlog::enabled(streamer, &qlog_path) {
                        Err(_) => qwarn!("Could not write to qlog path: {}", qlog_path.display()),
                        Ok(nq) => conn.set_qlog(nq),
                    }
                }
            }
        }

        let conn = Box::into_raw(Box::new(NeqoHttp3Conn {
            conn,
            local_addr: local,
            remote_addr: remote,
            refcnt: unsafe { AtomicRefcnt::new() },
            packets_to_send: Vec::new(),
        }));
        unsafe { Ok(RefPtr::from_raw(conn).unwrap()) }
    }
}

#[no_mangle]
pub unsafe extern "C" fn neqo_http3conn_addref(conn: &NeqoHttp3Conn) -> nsrefcnt {
    conn.refcnt.inc()
}

#[no_mangle]
pub unsafe extern "C" fn neqo_http3conn_release(conn: &NeqoHttp3Conn) -> nsrefcnt {
    let rc = conn.refcnt.dec();
    if rc == 0 {
        Box::from_raw(conn as *const _ as *mut NeqoHttp3Conn);
    }
    rc
}

// xpcom::RefPtr support
unsafe impl RefCounted for NeqoHttp3Conn {
    unsafe fn addref(&self) {
        neqo_http3conn_addref(self);
    }
    unsafe fn release(&self) {
        neqo_http3conn_release(self);
    }
}

// Allocate a new NeqoHttp3Conn object.
#[no_mangle]
pub extern "C" fn neqo_http3conn_new(
    origin: &nsACString,
    alpn: &nsACString,
    local_addr: &nsACString,
    remote_addr: &nsACString,
    max_table_size: u64,
    max_blocked_streams: u16,
    qlog_dir: &nsACString,
    result: &mut *const NeqoHttp3Conn,
) -> nsresult {
    *result = ptr::null_mut();

    match NeqoHttp3Conn::new(
        origin,
        alpn,
        local_addr,
        remote_addr,
        max_table_size,
        max_blocked_streams,
        qlog_dir,
    ) {
        Ok(http3_conn) => {
            http3_conn.forget(result);
            NS_OK
        }
        Err(e) => e,
    }
}

/* Process a packet.
 * packet holds packet data.
 */
#[no_mangle]
pub extern "C" fn neqo_http3conn_process_input(
    conn: &mut NeqoHttp3Conn,
    packet: *const u8,
    len: u32,
) {
    let array = unsafe { slice::from_raw_parts(packet, len as usize) };
    conn.conn.process_input(
        Datagram::new(conn.remote_addr, conn.local_addr, array.to_vec()),
        Instant::now(),
    );
}

/* Process output and store data to be sent into conn.packets_to_send.
 * neqo_http3conn_get_data_to_send will be called to pick up this data.
 */
#[no_mangle]
pub extern "C" fn neqo_http3conn_process_output(conn: &mut NeqoHttp3Conn) -> u64 {
    loop {
        let out = conn.conn.process_output(Instant::now());
        match out {
            Output::Datagram(dg) => {
                conn.packets_to_send.push(dg);
            }
            Output::Callback(to) => {
                let timeout = to.as_millis() as u64;
                // Necko resolution is in milliseconds whereas neqo resolution
                // is in nanoseconds. If we called process_output too soon due
                // to this difference, we might do few unnecessary loops until
                // we waste the remaining time. To avoid it, we return 1ms when
                // the timeout is less than 1ms.
                if timeout == 0 {
                    break 1;
                }
                break timeout;
            }
            Output::None => break std::u64::MAX,
        }
    }
}

#[no_mangle]
pub extern "C" fn neqo_http3conn_has_data_to_send(conn: &mut NeqoHttp3Conn) -> bool {
    !conn.packets_to_send.is_empty()
}

#[no_mangle]
pub extern "C" fn neqo_http3conn_get_data_to_send(
    conn: &mut NeqoHttp3Conn,
    packet: &mut ThinVec<u8>,
) -> nsresult {
    match conn.packets_to_send.pop() {
        None => NS_BASE_STREAM_WOULD_BLOCK,
        Some(d) => {
            packet.extend_from_slice(&d);
            NS_OK
        }
    }
}

#[no_mangle]
pub extern "C" fn neqo_http3conn_close(conn: &mut NeqoHttp3Conn, error: u64) {
    conn.conn.close(Instant::now(), error, "");
}

fn is_excluded_header(name: &str) -> bool {
    if (name == "connection")
        || (name == "host")
        || (name == "keep-alive")
        || (name == "proxy-connection")
        || (name == "te")
        || (name == "transfer-encoding")
        || (name == "upgrade")
        || (name == "sec-websocket-key")
    {
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn neqo_http3conn_fetch(
    conn: &mut NeqoHttp3Conn,
    method: &nsACString,
    scheme: &nsACString,
    host: &nsACString,
    path: &nsACString,
    headers: &nsACString,
    stream_id: &mut u64,
) -> nsresult {
    let mut hdrs = Vec::new();
    // this is only used for headers built by Firefox.
    // Firefox supplies all headers already prepared for sending over http1.
    // They need to be split into (String, String) pairs.
    match str::from_utf8(headers) {
        Err(_) => {
            return NS_ERROR_INVALID_ARG;
        }
        Ok(h) => {
            for elem in h.split("\r\n").skip(1) {
                if elem.starts_with(':') {
                    // colon headers are for http/2 and 3 and this is http/1
                    // input, so that is probably a smuggling attack of some
                    // kind.
                    continue;
                }
                if elem.len() == 0 {
                    continue;
                }
                let hdr_str: Vec<_> = elem.splitn(2, ":").collect();
                let name = hdr_str[0].trim().to_lowercase();
                if is_excluded_header(&name) {
                    continue;
                }
                let value = if hdr_str.len() > 1 {
                    String::from(hdr_str[1].trim())
                } else {
                    String::new()
                };

                hdrs.push((name, value));
            }
        }
    }

    let method_tmp = match str::from_utf8(method) {
        Ok(m) => m,
        Err(_) => {
            return NS_ERROR_INVALID_ARG;
        }
    };
    let scheme_tmp = match str::from_utf8(scheme) {
        Ok(s) => s,
        Err(_) => {
            return NS_ERROR_INVALID_ARG;
        }
    };
    let host_tmp = match str::from_utf8(host) {
        Ok(h) => h,
        Err(_) => {
            return NS_ERROR_INVALID_ARG;
        }
    };
    let path_tmp = match str::from_utf8(path) {
        Ok(p) => p,
        Err(_) => {
            return NS_ERROR_INVALID_ARG;
        }
    };
    match conn.conn.fetch(
        Instant::now(),
        method_tmp,
        scheme_tmp,
        host_tmp,
        path_tmp,
        &hdrs,
    ) {
        Ok(id) => {
            *stream_id = id;
            NS_OK
        }
        Err(Http3Error::StreamLimitError) => NS_BASE_STREAM_WOULD_BLOCK,
        Err(_) => NS_ERROR_UNEXPECTED,
    }
}

#[no_mangle]
pub extern "C" fn neqo_htttp3conn_send_request_body(
    conn: &mut NeqoHttp3Conn,
    stream_id: u64,
    buf: *const u8,
    len: u32,
    read: &mut u32,
) -> nsresult {
    let array = unsafe { slice::from_raw_parts(buf, len as usize) };
    match conn.conn.send_request_body(stream_id, array) {
        Ok(amount) => {
            *read = u32::try_from(amount).unwrap();
            if amount == 0 {
                NS_BASE_STREAM_WOULD_BLOCK
            } else {
                NS_OK
            }
        }
        Err(_) => NS_ERROR_UNEXPECTED,
    }
}

// This is only used for telemetry. Therefore we only return error code
// numbers and do not label them. Recording telemetry is easier with a
// number.
#[repr(C)]
pub enum CloseError {
    QuicTransportError(u64),
    Http3AppError(u64),
}

impl From<neqo_transport::CloseError> for CloseError {
    fn from(error: neqo_transport::CloseError) -> CloseError {
        match error {
            neqo_transport::CloseError::Transport(c) => CloseError::QuicTransportError(c),
            neqo_transport::CloseError::Application(c) => CloseError::Http3AppError(c),
        }
    }
}

// Reset a stream with streamId.
#[no_mangle]
pub extern "C" fn neqo_http3conn_reset_stream(
    conn: &mut NeqoHttp3Conn,
    stream_id: u64,
    error: u64,
) -> nsresult {
    match conn.conn.stream_reset(stream_id, error) {
        Ok(()) => NS_OK,
        Err(_) => NS_ERROR_INVALID_ARG,
    }
}

// Close sending side of a stream with stream_id
#[no_mangle]
pub extern "C" fn neqo_http3conn_close_stream(
    conn: &mut NeqoHttp3Conn,
    stream_id: u64,
) -> nsresult {
    match conn.conn.stream_close_send(stream_id) {
        Ok(()) => NS_OK,
        Err(_) => NS_ERROR_INVALID_ARG,
    }
}

#[repr(C)]
pub enum Http3Event {
    /// A request stream has space for more data to be send.
    DataWritable {
        stream_id: u64,
    },
    /// A server has send STOP_SENDING frame.
    StopSending {
        stream_id: u64,
        error: u64,
    },
    HeaderReady {
        stream_id: u64,
        fin: bool,
    },
    /// New bytes available for reading.
    DataReadable {
        stream_id: u64,
    },
    /// Peer reset the stream.
    Reset {
        stream_id: u64,
        error: u64,
        local: bool,
    },
    /// A PushPromise
    PushPromise {
        push_id: u64,
        request_stream_id: u64,
    },
    /// A push response headers are ready.
    PushHeaderReady {
        push_id: u64,
        fin: bool,
    },
    /// New bytes are available on a push stream for reading.
    PushDataReadable {
        push_id: u64,
    },
    /// A push has been canceled.
    PushCanceled {
        push_id: u64,
    },
    PushReset {
        push_id: u64,
        error: u64,
    },
    RequestsCreatable,
    AuthenticationNeeded,
    ZeroRttRejected,
    ConnectionConnected,
    GoawayReceived,
    ConnectionClosing {
        error: CloseError,
    },
    ConnectionClosed {
        error: CloseError,
    },
    ResumptionToken {
        expire_in: u64, // microseconds
    },
    NoEvent,
}

fn convert_h3_to_h1_headers(
    headers: Vec<(String, String)>,
    ret_headers: &mut ThinVec<u8>,
) -> nsresult {
    if headers.iter().filter(|(k, _)| k == ":status").count() != 1 {
        return NS_ERROR_ILLEGAL_VALUE;
    }

    let (_, status_val) = headers
        .iter()
        .find(|(k, _)| k == ":status")
        .expect("must be one");

    ret_headers.extend_from_slice(b"HTTP/3 ");
    ret_headers.extend_from_slice(status_val.as_bytes());
    ret_headers.extend_from_slice(b"\r\n");

    for (key, value) in headers.iter().filter(|(k, _)| k != ":status") {
        ret_headers.extend_from_slice(key.as_bytes());
        ret_headers.extend_from_slice(b": ");
        ret_headers.extend_from_slice(value.as_bytes());
        ret_headers.extend_from_slice(b"\r\n");
    }
    ret_headers.extend_from_slice(b"\r\n");
    return NS_OK;
}

#[no_mangle]
pub extern "C" fn neqo_http3conn_event(
    conn: &mut NeqoHttp3Conn,
    ret_event: &mut Http3Event,
    data: &mut ThinVec<u8>,
) -> nsresult {
    while let Some(evt) = conn.conn.next_event() {
        let fe = match evt {
            Http3ClientEvent::DataWritable { stream_id } => Http3Event::DataWritable { stream_id },
            Http3ClientEvent::StopSending { stream_id, error } => {
                Http3Event::StopSending { stream_id, error }
            }
            Http3ClientEvent::HeaderReady {
                stream_id,
                headers,
                fin,
                interim,
            } => {
                if interim {
                    // This are 1xx responses and they are ignored.
                    Http3Event::NoEvent
                } else {
                    let res = convert_h3_to_h1_headers(headers, data);
                    if res != NS_OK {
                        return res;
                    }
                    Http3Event::HeaderReady { stream_id, fin }
                }
            }
            Http3ClientEvent::DataReadable { stream_id } => Http3Event::DataReadable { stream_id },
            Http3ClientEvent::Reset { stream_id, error, local } =>
                Http3Event::Reset { stream_id, error, local },
            Http3ClientEvent::PushPromise {
                push_id,
                request_stream_id,
                headers,
            } => {
                let res = convert_h3_to_h1_headers(headers, data);
                if res != NS_OK {
                    return res;
                }
                Http3Event::PushPromise {
                    push_id,
                    request_stream_id,
                }
            }
            Http3ClientEvent::PushHeaderReady {
                push_id,
                headers,
                fin,
                interim,
            } => {
                if interim {
                    Http3Event::NoEvent
                } else {
                    let res = convert_h3_to_h1_headers(headers, data);
                    if res != NS_OK {
                        return res;
                    }
                    Http3Event::PushHeaderReady { push_id, fin }
                }
            }
            Http3ClientEvent::PushDataReadable { push_id } => {
                Http3Event::PushDataReadable { push_id }
            }
            Http3ClientEvent::PushCanceled { push_id } => Http3Event::PushCanceled { push_id },
            Http3ClientEvent::PushReset { push_id, error } => Http3Event::PushReset { push_id, error },
            Http3ClientEvent::RequestsCreatable => Http3Event::RequestsCreatable,
            Http3ClientEvent::AuthenticationNeeded => Http3Event::AuthenticationNeeded,
            Http3ClientEvent::ZeroRttRejected => Http3Event::ZeroRttRejected,
            Http3ClientEvent::ResumptionToken(token) => {
                // expiration_time time is Instant, transform it into microseconds it will
                // be valid for. Necko code will add the value to PR_Now() to get the expiration
                // time in PRTime.
                if token.expiration_time() > Instant::now() {
                    let e = (token.expiration_time() - Instant::now()).as_micros();
                    if let Ok(expire_in) = u64::try_from(e) {
                        data.extend_from_slice(token.as_ref());
                        Http3Event::ResumptionToken { expire_in }
                    } else {
                        Http3Event::NoEvent
                    }
                } else {
                    Http3Event::NoEvent
                }
            }
            Http3ClientEvent::GoawayReceived => Http3Event::GoawayReceived,
            Http3ClientEvent::StateChange(state) => match state {
                Http3State::Connected => Http3Event::ConnectionConnected,
                Http3State::Closing(error_code) => Http3Event::ConnectionClosing {
                    error: error_code.into(),
                },
                Http3State::Closed(error_code) => Http3Event::ConnectionClosed {
                    error: error_code.into(),
                },
                _ => Http3Event::NoEvent,
            },
        };

        if !matches!(fe, Http3Event::NoEvent) {
            *ret_event = fe;
            return NS_OK;
        }
    }

    *ret_event = Http3Event::NoEvent;
    NS_OK
}

// Read response data into buf.
#[no_mangle]
pub extern "C" fn neqo_http3conn_read_response_data(
    conn: &mut NeqoHttp3Conn,
    stream_id: u64,
    buf: *mut u8,
    len: u32,
    read: &mut u32,
    fin: &mut bool,
) -> nsresult {
    let array = unsafe { slice::from_raw_parts_mut(buf, len as usize) };
    match conn
        .conn
        .read_response_data(Instant::now(), stream_id, &mut array[..])
    {
        Ok((amount, fin_recvd)) => {
            *read = u32::try_from(amount).unwrap();
            *fin = fin_recvd;
            NS_OK
        }
        Err(Http3Error::InvalidStreamId)
        | Err(Http3Error::TransportError(TransportError::NoMoreData)) => NS_ERROR_INVALID_ARG,
        Err(_) => NS_ERROR_NET_HTTP3_PROTOCOL_ERROR,
    }
}

#[repr(C)]
pub struct NeqoSecretInfo {
    set: bool,
    version: u16,
    cipher: u16,
    group: u16,
    resumed: bool,
    early_data: bool,
    alpn: nsCString,
    signature_scheme: u16,
}

#[no_mangle]
pub extern "C" fn neqo_http3conn_tls_info(
    conn: &mut NeqoHttp3Conn,
    sec_info: &mut NeqoSecretInfo,
) -> nsresult {
    match conn.conn.tls_info() {
        Some(info) => {
            sec_info.set = true;
            sec_info.version = info.version();
            sec_info.cipher = info.cipher_suite();
            sec_info.group = info.key_exchange();
            sec_info.resumed = info.resumed();
            sec_info.early_data = info.early_data_accepted();
            sec_info.alpn = match info.alpn() {
                Some(a) => nsCString::from(a),
                None => nsCString::new(),
            };
            sec_info.signature_scheme = info.signature_scheme();
            NS_OK
        }
        None => NS_ERROR_NOT_AVAILABLE,
    }
}

#[repr(C)]
pub struct NeqoCertificateInfo {
    certs: ThinVec<ThinVec<u8>>,
    stapled_ocsp_responses_present: bool,
    stapled_ocsp_responses: ThinVec<ThinVec<u8>>,
    signed_cert_timestamp_present: bool,
    signed_cert_timestamp: ThinVec<u8>,
}

#[no_mangle]
pub extern "C" fn neqo_http3conn_peer_certificate_info(
    conn: &mut NeqoHttp3Conn,
    neqo_certs_info: &mut NeqoCertificateInfo,
) -> nsresult {
    let mut certs_info = match conn.conn.peer_certificate() {
        Some(certs) => certs,
        None => return NS_ERROR_NOT_AVAILABLE,
    };

    neqo_certs_info.certs = certs_info
        .map(|cert| cert.iter().cloned().collect())
        .collect();

    match &mut certs_info.stapled_ocsp_responses() {
        Some(ocsp_val) => {
            neqo_certs_info.stapled_ocsp_responses_present = true;
            neqo_certs_info.stapled_ocsp_responses = ocsp_val
                .iter()
                .map(|ocsp| ocsp.iter().cloned().collect())
                .collect();
        }
        None => {
            neqo_certs_info.stapled_ocsp_responses_present = false;
        }
    };

    match certs_info.signed_cert_timestamp() {
        Some(sct_val) => {
            neqo_certs_info.signed_cert_timestamp_present = true;
            neqo_certs_info
                .signed_cert_timestamp
                .extend_from_slice(sct_val);
        }
        None => {
            neqo_certs_info.signed_cert_timestamp_present = false;
        }
    };

    NS_OK
}

#[no_mangle]
pub extern "C" fn neqo_http3conn_authenticated(conn: &mut NeqoHttp3Conn, error: PRErrorCode) {
    conn.conn.authenticated(error.into(), Instant::now());
}

#[no_mangle]
pub extern "C" fn neqo_http3conn_set_resumption_token(
    conn: &mut NeqoHttp3Conn,
    token: &mut ThinVec<u8>,
) {
    let _ = conn.conn.enable_resumption(Instant::now(), token);
}

#[no_mangle]
pub extern "C" fn neqo_http3conn_is_zero_rtt(conn: &mut NeqoHttp3Conn) -> bool {
    conn.conn.state() == Http3State::ZeroRtt
}
