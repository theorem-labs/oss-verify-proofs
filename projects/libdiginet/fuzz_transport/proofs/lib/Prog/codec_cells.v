(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_codec proofs/libdiginet/fuzz_codec/lib/Prog/codec_cells.v at d8e4e696562a3ec070d61f99e264ce9d80f5a5bd to fuzz_transport's images; the RELRO block [RELRO_BASE, RELRO_BASE + RELRO_LEN) is fuzz_transport's whole .data.rel.ro, Prog/T/TContract.v's values *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

(** The shared vocabulary of the contracts of fuzz_codec's own functions in the plain image: the
    register forms of C arguments, byte lists, C strings, personalities, the RELRO tables, struct
    diginet_cmd and struct call as cells, and the text cursor of text_arg. *)

(** ---- register forms ---- *)

(** A 32-bit C argument v as the callers pass it: they load the field with lw, so the register holds
    v sign-extended from bit 31 (for an unsigned v in [0, 2^32) that is Mem.sx32 of v). *)
Definition arg_u32 (r : word) (v : Z) : Prop := 0 <= v < 2 ^ 32 /\ r = Z_to_bv 64 (s32 v).
(** An int argument v in [-2^31, 2^31): the register holds v sign-extended. *)
Definition arg_s32 (r : word) (v : Z) : Prop := - 2 ^ 31 <= v < 2 ^ 31 /\ r = Z_to_bv 64 v.
(** A uint8_t / uint16_t argument (w = 8 / 16) loaded with lbu / lhu: zero-extended. *)
Definition arg_zx (w : Z) (r : word) (v : Z) : Prop := 0 <= v < 2 ^ w /\ r = Z_to_bv 64 v.

(** ---- bytes ---- *)

Definition b8 (v : Z) : byte := Z_to_bv 8 v.
(** The byte values of a spec list, and the values of a memory byte list. *)
Definition bz (l : list Z) : list byte := map b8 l.
Definition zb (l : list byte) : list Z := map (fun b => bv_unsigned b) l.

(** [a, a + n) and [b, b + k) do not overlap. *)
Definition disj (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

(** A C string at a: the bytes tb from a hold a 0. The text specs of DgnLib / codec_owe read a
    string up to its first 0, so the bytes after it never matter. *)
Definition cstr (m : word -> option byte) (a : Z) (tb : list byte) : Prop :=
  bytes_at rsegs m a tb /\ In (b8 0) tb.

(** The bytes before the first 0. *)
Fixpoint cstring (l : list Z) : list Z :=
  match l with [] => [] | x :: l' => if x =? 0 then [] else x :: cstring l' end.

(** ---- personalities (diginet_codec.c:12-15; struct diginet_personality: desk@0, announce_name@8,
    device@16, strips@17, scribble_chars@18, counter_addr@19) ---- *)

Definition desk_ok (d : desk) : Prop :=
  0 <= d_dev d < 256 /\ 0 <= d_strips d < 256 /\ 0 <= d_chars d < 256 /\ 0 <= d_counter d < 256.

(** The four byte fields the encoders read at p + 16 .. p + 19 are those of d. *)
Definition pers_ok (m : word -> option byte) (p : Z) (d : desk) : Prop :=
  desk_ok d /\ bytes_at rsegs m (p + 16) (bz [d_dev d; d_strips d; d_chars d; d_counter d]).

(** The personality argument in a0: NULL for None, else a pointer to the fields of d. *)
Definition pers_arg (m : word -> option byte) (a0 : word) (pd : option desk) : Prop :=
  match pd with
  | None => a0 = Z_to_bv 64 0
  | Some d => bv_unsigned a0 <> 0 /\ pers_ok m (bv_unsigned a0) d
  end.

(** &personalities[0] in this image; personalities[1] is 24 bytes on. *)
Definition PERS : Z := 0x21420.

(** diginet_personality_of (diginet_codec.c:27-33) on the 64-bit argument register value d. *)
Definition pers_of (d : Z) : Z := if d =? 1 then PERS else if d =? 2 then PERS + 24 else 0.

(** The two announce names, "CNTRL|24" and "MAINUNIT". *)
Definition NAME_C24 : list Z := [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x34].
Definition NAME_PC : list Z := [0x4d; 0x41; 0x49; 0x4e; 0x55; 0x4e; 0x49; 0x54].

(** diginet_personality_from_name (diginet_codec.c:17-25) for the C string held by tb. *)
Definition from_name_res (tb : list byte) : Z :=
  if list_eq_dec Z.eq_dec (cstring (zb tb)) NAME_C24 then PERS
  else if list_eq_dec Z.eq_dec (cstring (zb tb)) NAME_PC then PERS + 24
  else 0.

(** ---- the RELRO tables: .data.rel.ro of fuzz_transport (SPEC_C24, SPEC_PC, op_announce's NAME,
    personalities[], stderr, stdout; the values of Prog/T/TContract.v) lies in
    [RELRO_BASE, RELRO_BASE + RELRO_LEN), inside a writable PT_LOAD, so mem_inv does not give their
    bytes; relro_img says the memory still holds the image's bytes there. ---- *)

Definition RELRO_BASE : Z := 0x213c8.
Definition RELRO_LEN : Z := 152.
Definition relro_img (m : word -> option byte) : Prop :=
  forall i, 0 <= i < RELRO_LEN ->
    mrd rsegs m (wa (RELRO_BASE + i)) = seg_rom rsegs (wa (RELRO_BASE + i)).

(** ---- struct diginet_cmd (32 bytes: bytes[24]@0, len@24, display@25, padding@26..27, key@28) ---- *)

(** The 32 bytes of a command after an encoder returns (rc, o), from the 32 bytes before the call:
    on failure (o = None) unchanged; on success bytes[0..len), len, display and key written, the
    bytes from len to 24 and the padding unchanged. *)
Definition cmd_out (before : list byte) (o : option cmd) : list byte :=
  match o with
  | None => before
  | Some (bs, k, disp) =>
      bz bs ++ skipn (length bs) (firstn 24 before) ++ bz [Z.of_nat (length bs); disp]
        ++ firstn 2 (skipn 26 before) ++ le4 (Z_to_bv 64 k)
  end.

(** The len, display and key fields of the 32 bytes o of a command. *)
Definition cmd_len (o : list byte) : Z := bv_unsigned (nth 24 o (b8 0)).
Definition cmd_display (o : list byte) : Z := bv_unsigned (nth 25 o (b8 0)).
Definition cmd_key (o : list byte) : Z :=
  fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 (firstn 4 (skipn 28 o)).

(** ---- struct call (fuzz_codec.c:74-90; 184 bytes) ---- *)

Record kcall := mkKcall {
  k_kind : Z; k_pad : list byte; k_p : Z; k_desk : Z;
  k_a : Z; k_b : Z; k_c : Z; k_delta : Z;
  k_bytes : list byte; k_n : Z; k_rc : Z;
  k_before : list byte; k_out : list byte;
  k_want_rc : Z; k_want : list byte; k_want_len : Z; k_want_key : Z; k_want_display : Z }.

(** kind@0 (int), padding@4, p@8, desk@16, a@24, b@28, c@32 (unsigned), delta@36 (int), bytes[24]@40,
    n@64 (size_t), rc@72 (int), before@76, out@108 (struct diginet_cmd), want_rc@140 (int),
    want[24]@144, want_len@168 (size_t), want_key@176 (uint32_t), want_display@180 (int). *)
Definition kcall_cells (k : kcall) : list cell :=
  [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
   CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k));
   CB 32 (k_before k); CB 32 (k_out k);
   C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
   C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))].

(** Each scalar field in the range of its C type. *)
Definition kcall_wf (k : kcall) : Prop :=
  - 2 ^ 31 <= k_kind k < 2 ^ 31 /\ 0 <= k_p k < 2 ^ 64 /\ 0 <= k_desk k < 2 ^ 64 /\
  0 <= k_a k < 2 ^ 32 /\ 0 <= k_b k < 2 ^ 32 /\ 0 <= k_c k < 2 ^ 32 /\ - 2 ^ 31 <= k_delta k < 2 ^ 31 /\
  0 <= k_n k < 2 ^ 64 /\ - 2 ^ 31 <= k_rc k < 2 ^ 31 /\ - 2 ^ 31 <= k_want_rc k < 2 ^ 31 /\
  0 <= k_want_len k < 2 ^ 64 /\ 0 <= k_want_key k < 2 ^ 32 /\ - 2 ^ 31 <= k_want_display k < 2 ^ 31.

(** k with want, want_len and want_display replaced (what owe_sysex writes). *)
Definition set_want (k : kcall) (w : list byte) (wl wd : Z) : kcall :=
  mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) (k_a k) (k_b k) (k_c k) (k_delta k)
          (k_bytes k) (k_n k) (k_rc k) (k_before k) (k_out k)
          (k_want_rc k) w wl (k_want_key k) wd.

(** ---- text_arg (fuzz_codec.c:523-529) on the cursor bytes data (struct fuzz_in, fuzz.h:29-70) ---- *)

(** fuzz_u16: two fuzz_u8, a missing byte reads 0. *)
Definition text_u16 (data : list byte) : Z :=
  bv_unsigned (nth 0 data (b8 0)) + 256 * bv_unsigned (nth 1 data (b8 0)).
(** The bytes fuzz_u16 takes, and the text length fuzz_take gives. *)
Definition text_hdr (data : list byte) : nat := Nat.min 2 (length data).
Definition text_len (data : list byte) : nat :=
  Nat.min (Z.to_nat (text_u16 data mod 65)) (length data - text_hdr data).
Definition text_taken (data : list byte) : list byte := firstn (text_len data) (skipn (text_hdr data) data).
Definition text_used (data : list byte) : nat := text_hdr data + text_len data.
