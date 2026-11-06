(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record adrv_consts := mkAConsts {
  c_main : Z; c_target_run : Z; c_emit_printf : Z; c_yfuzz : Z;          (* [comment removed for export] *)
  c_wrap_malloc : Z; c_wrap_free : Z; c_wrap_realloc : Z; c_wrap_memcpy : Z; c_wrap_read : Z;
  c_wrap_vprintf : Z; c_wrap_fprintf : Z; c_wrap_fwrite : Z;
  c_open : Z; c_close : Z; c_exit : Z;                                   (* [comment removed for export] *)
  c_tp : Z;                 (* [comment removed for export] *)
  c_errno : Z;              (* [comment removed for export] *)
  c_got_stderr : Z;         (* [comment removed for export] *)
  c_stderr_var : Z;         (* [comment removed for export] *)
  c_stderr_F : Z;           (* [comment removed for export] *)
  c_stdout_F : Z;           (* [comment removed for export] *)
  c_stdout_buf : Z;         (* [comment removed for export] *)
  c_got_fuzzinit : Z;       (* [comment removed for export] *)
  c_empty : Z;              (* [comment removed for export] *)
  c_initialized : Z;        (* [comment removed for export] *)
  c_seg3_lo : Z; c_seg3_hi : Z;          (* [comment removed for export] *)
  c_img_lo : Z; c_img_hi : Z;            (* [comment removed for export] *)
  c_ystat_lo : Z; c_ystat_hi : Z;        (* [comment removed for export] *)
  c_uras : list Z                        (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition ACONSTS : adrv_consts :=
  {| c_main := 0x81aa4; c_target_run := 0x81d74; c_emit_printf := 0x81efc; c_yfuzz := 0x81f44;
     c_wrap_malloc := 0x5409c; c_wrap_free := 0x54098; c_wrap_realloc := 0x540a0; c_wrap_memcpy := 0x52d44; c_wrap_read := 0x431d0;
     c_wrap_vprintf := 0x431e0; c_wrap_fprintf := 0x431ec; c_wrap_fwrite := 0x431d4;
     c_open := 0x91f84; c_close := 0xa3300; c_exit := 0x91d10;
     c_tp := 0x5e0b10; c_errno := 0x5e0a6c;
     c_got_stderr := 0xa5610; c_stderr_var := 0xa48a8; c_stderr_F := 0xa9088; c_stdout_F := 0xa9178; c_stdout_buf := 0x601220; c_got_fuzzinit := 0xa5618;
     c_empty := 0x5e01e0; c_initialized := 0x5e01d0;
     c_seg3_lo := 0xa4418; c_seg3_hi := 0xa6000; c_img_lo := 0x10000; c_img_hi := 0x603000;
     c_ystat_lo := 0xa8f60; c_ystat_hi := 0xa9040;
     c_uras := [0x81af8; 0x81b4c; 0x81b70; 0x81ca0; 0x81dd8; 0x81e40; 0x81e6c] |}.

(* [comment removed for export] *)
Definition AMALLOC_STACK : Z := 8192.    (* [comment removed for export] *)
Definition AICP_STACK : Z := 8192.       (* [comment removed for export] *)
Definition AYFUZZ_STACK : Z := 16384.    (* [comment removed for export] *)
Definition AEXIT_STACK : Z := 8192.

Definition A_SB : Z := 0x7fff8000.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ff_bytes (cls : Z) : Z := Z.shiftl 64 cls.
Definition in_fframe (LF : list (Z * Z)) (a : Z) : Prop :=
  exists f, In f LF /\ (snd f <= a < snd f + ff_bytes (fst f) \/ A_SB + snd f / 8 <= a < A_SB + snd f / 8 + Z.shiftl 8 (fst f)).

(* [comment removed for export] *)
Definition A_FMT_emit : Z := 0x1486e.        (* [comment removed for export] *)
Definition A_FMT_usage : Z := 0x1592b.       (* [comment removed for export] *)
Definition A_FMT_too_big : Z := 0x19817.     (* [comment removed for export] *)
Definition A_FMT_cannot_open : Z := 0x1d8ba. (* [comment removed for export] *)
Definition A_FMT_read_error : Z := 0x1d8cf.  (* [comment removed for export] *)
Definition A_S_overrun : Z := 0x1593c.       (* [comment removed for export] *)
Definition A_S_short : Z := 0x1fa90.         (* [comment removed for export] *)
Definition A_S_oom : Z := 0x1485a.           (* [comment removed for export] *)
Record adrv_fmts := mkAFmts { f_usage : Z; f_too_big : Z; f_cannot_open : Z; f_read_error : Z; f_emit : Z;
                              f_s_overrun : Z; f_s_short : Z; f_s_oom : Z }.
Definition AFMTS : adrv_fmts := mkAFmts A_FMT_usage A_FMT_too_big A_FMT_cannot_open A_FMT_read_error A_FMT_emit A_S_overrun A_S_short A_S_oom.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ablock := mkABlock { ab_addr : Z; ab_size : Z }.
(* [comment removed for export] *)
Definition fblock : Type := (Z * Z)%type.

Definition in_ablock (LB : list ablock) (a : Z) : Prop :=
  exists b, In b LB /\ ab_addr b <= a < ab_addr b + ab_size b.
Fixpoint ab_remove (A : Z) (LB : list ablock) : list ablock :=
  match LB with [] => [] | b :: r => if Z.eqb (ab_addr b) A then r else b :: ab_remove A r end.

(* [comment removed for export] *)
Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.

(* [comment removed for export] *)
Inductive aevent : Type := EvMalloc (n : Z) (r : option Z) | EvFree (A : Z) | EvYfuzz.
Definition ev_big_or_free (e : aevent) : Prop := match e with EvMalloc n _ => 64512 < n | EvFree _ => True | EvYfuzz => False end.
Definition ev_is_malloc (e : aevent) : Prop := match e with EvMalloc _ _ => True | _ => False end.
Definition hist_payload_ok (H : list aevent) (n : Z) : Prop :=
  Forall ev_big_or_free H /\ (Forall ev_is_malloc H \/ 32763 <= n).

(* [comment removed for export] *)
Definition adrv_static (C : adrv_consts) (a : Z) : Prop :=
  (c_seg3_lo C <= a < c_seg3_hi C) \/ (c_initialized C <= a < c_initialized C + 32) \/ (c_ystat_lo C <= a < c_ystat_hi C)
  \/ (c_initialized C + 0x20990 <= a < c_initialized C + 0x20990 + 544).
(* [comment removed for export] *)
Definition aclient_addr (C : adrv_consts) (LB : list ablock) (LF : list fblock) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ in_ablock LB a \/ in_fframe LF a \/ adrv_static C a.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
(* [comment removed for export] *)
Definition ablock_range (C : adrv_consts) (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ c_img_hi C <= A.
End RC__1.
