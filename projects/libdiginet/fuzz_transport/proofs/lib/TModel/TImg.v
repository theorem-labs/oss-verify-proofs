(* The model (TSess0, TCb, TSess, TOps) is the same for the plain and the ubsan build. Where the C code stores a
   code or read-only data ADDRESS into a global, or passes one, the model takes it from a timg record; each build
   instantiates the record with its own addresses (lib/Prog/TImgP.v, lib/U/Prog/TImgU.v). Byte VALUES of
   read-only tables (HOST, DESK, SPEC_C24's name, ...) are constants of the model, not addresses. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

Record timg := TImg {
  ti_io_send : Z;        (* fuzz_transport.c:823 io_send, the value stored in g_s.io.send *)
  ti_io_recv : Z;        (* :906 io_recv *)
  ti_io_now : Z;         (* :931 io_now *)
  ti_notice : Z;         (* :937 notice, the value stored in g_s.notify *)
  ti_spec_c24 : Z;       (* fuzz/spec.h:110 SPEC_C24, the value desk_named returns and OW.desk_p holds *)
  ti_spec_pc : Z;        (* spec.h:111 SPEC_PC *)
  ti_personalities : Z;  (* src/diginet_codec.c personalities[], what g_s.personality and a notice point into *)
}.

(* The heap block of the frame the current operation received (fuzz_transport.c:997 fuzz_dup), when there is
   one: its address and its bytes. A pointer the harness stores into OW (desk_body, dn[k].body) or g_rx points
   into it. *)
Record tframe := TFrame { tf_addr : Z; tf_bytes : list byte }.

(* struct diginet_notice (include/diginet/transport/diginet_session.h), as the harness's notice() reads it
   (fuzz_transport.c:937-973 and the checks it calls): every pointer field that notice() follows is replaced by
   what it reads there. n_pers is the personality pointer itself (0 = NULL); its device / strips are read from the
   image by the reader (check_state_desk :534-536). *)
Record tann := TAnn { ta_version : list byte (* 10 bytes *); ta_name : list byte (* 10 bytes *) }.
Record ntc := Ntc {
  n_kind : Z; n_state : Z; n_old : Z; n_reason : Z;
  n_counter : Z; n_retry : Z; n_mac_offset : Z;
  n_pers : Z;              (* const struct diginet_personality *, 0 = NULL *)
  n_ann : option tann;     (* None = .announce NULL *)
  n_body : list byte;      (* the n_body_len bytes at .body (empty when .body is unused) *)
  n_body_len : Z;
}.
