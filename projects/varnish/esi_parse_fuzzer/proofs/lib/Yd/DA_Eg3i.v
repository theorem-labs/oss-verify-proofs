(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AGlofzw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Ey6n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition EXIT_ENTRY : Z := 0x989ac.
Definition EXIT_STACK : Z := 320.          (* [comment removed for export] *)
Definition TPV : Z := 0x5e83d8.            (* [comment removed for export] *)
Definition TID_CELL : Z := 0x5e8330.       (* [comment removed for export] *)
Definition EXIT_LOCK : Z := 0x608648.
Definition ATEXIT : Z := 0x608428.         (* [comment removed for export] *)
Definition TR_INCB : Z := 0x5e7a14.        (* [comment removed for export] *)
Definition AEF_GUARD : Z := 0x86d40.       (* [comment removed for export] *)
Definition CALL_TRAMP : Z := 0x98958.      (* [comment removed for export] *)
Definition NEED_LOCKS : Z := 0x60866b.     (* [comment removed for export] *)
Definition COV_FLAG : Z := 0x147260.       (* [comment removed for export] *)
Definition OFL_HEAD : Z := 0x608ad0.
Definition STDIN_F : Z := 0xadb08.
Definition STDOUT_F : Z := 0xada18.
Definition STDERR_F : Z := 0xad928.
Definition STDIO_WRITE : Z := 0x9debc.
Definition STDOUT_BUF : Z := 0x608ae8.       (* [comment removed for export] *)
Definition SSP_GOT : Z := 0xa9e38.        (* [comment removed for export] *)
Definition SSP_GUARD : Z := 0x608418.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_clean (v : word -> option byte) (f : Z) (wp rp : word) : Prop :=
     ro_cells rsegs v (f + 140) [C4 (Z_to_bv 64 4294967295)]
  /\ ro_cells rsegs v (f + 40) [C8 wp] /\ ro_cells rsegs v (f + 56) [C8 wp]
  /\ ro_cells rsegs v (f + 8) [C8 rp] /\ ro_cells rsegs v (f + 16) [C8 rp].

(* [comment removed for export] *)
Record stdout_pending (v : word -> option byte) (wb wp : Z) (wend bufp bufsz rp1 canary : word) (pending : list byte) : Prop := {
  sp_lock  : ro_cells rsegs v (STDOUT_F + 140) [C4 (Z_to_bv 64 4294967295)];
  sp_wpos  : rw_cells rsegs v (STDOUT_F + 32) [C8 wend; C8 (Z_to_bv 64 wp)];      (* [comment removed for export] *)
  sp_wbase : rw_cells rsegs v (STDOUT_F + 56) [C8 (Z_to_bv 64 wb)];
  sp_write : ro_cells rsegs v (STDOUT_F + 72) [C8 (Z_to_bv 64 STDIO_WRITE)];
  sp_buf   : ro_cells rsegs v (STDOUT_F + 88) [C8 bufp; C8 bufsz];
  sp_fd    : ro_cells rsegs v (STDOUT_F + 120) [C4 (Z_to_bv 64 1)];
  sp_rpos  : ro_cells rsegs v (STDOUT_F + 8) [C8 rp1; C8 rp1];
  sp_range : STDOUT_BUF <= wb < wp /\ wp <= STDOUT_BUF + 1024;       (* [comment removed for export] *)
  sp_len   : wp - wb = Z.of_nat (length pending);
  sp_max   : Z.of_nat (length pending) <= 0x4000000 (* [comment removed for export] *);
  sp_bytes : bytes_at rsegs v wb pending;
  sp_ssp   : ro_cells rsegs v SSP_GOT [C8 (Z_to_bv 64 SSP_GUARD)] /\ ro_cells rsegs v SSP_GUARD [C8 canary]
}.

(* [comment removed for export] *)
Record exit_cells (v : word -> option byte) (tid : Z) (ini : Z) (fin : byte)   (* [comment removed for export] *)
       (bss : list (list byte)) (b1 b2 b3 b4 : byte) (junk0 : list byte)
       (wp0 rp0 wp2 rp2 : word) : Prop := {
  ec_tid   : ro_cells rsegs v TID_CELL [C4 (Z_to_bv 64 tid)];
  ec_tidr  : 0 < tid < 2^31;
  ec_lock  : rw_cells rsegs v EXIT_LOCK [C4 (Z_to_bv 64 0)];
  (* [comment removed for export] *)
  ec_fin   : rw_cells rsegs v ATEXIT [C1 fin];
  ec_alock : ro_cells rsegs v (ATEXIT + 4) [C4 (Z_to_bv 64 0)];
  ec_ini   : ini = 0 \/ ini = 1;                                                  (* [comment removed for export] *)
  ec_slot  : rw_cells rsegs v (ATEXIT + 8) [C4 (Z_to_bv 64 (1 + ini))];
  ec_bf1   : rw_cells rsegs v (ATEXIT + 40) [C8 (Z_to_bv 64 (ini * CALL_TRAMP))];
  ec_ba1   : rw_cells rsegs v (ATEXIT + 296) [C8 (Z_to_bv 64 (ini * AEF_GUARD))];
  ec_incb  : ro_cells rsegs v TR_INCB [C1 (Z_to_bv 8 0)];
  ec_head  : rw_cells rsegs v (ATEXIT + 16) [C8 (Z_to_bv 64 (ATEXIT + 24))];
  ec_bnext : ro_cells rsegs v (ATEXIT + 24) [C8 (Z_to_bv 64 0)];
  ec_bf0   : ro_cells rsegs v (ATEXIT + 32) [C8 (Z_to_bv 64 0x98958)];
  ec_ba0   : ro_cells rsegs v (ATEXIT + 288) [C8 (Z_to_bv 64 0x76378)];
  ec_nlock : ro_cells rsegs v NEED_LOCKS [C1 (Z_to_bv 8 0)];
  ec_cov   : ro_cells rsegs v COV_FLAG [C1 (Z_to_bv 8 0)];
  (* [comment removed for export] *)
  ec_figot : ro_cells rsegs v 0xa9e68 [C8 (Z_to_bv 64 0xa8a18); C8 (Z_to_bv 64 0xa8a08)];
  ec_fiarr : ro_cells rsegs v 0xa8a08 [C8 (Z_to_bv 64 0x87728); C8 (Z_to_bv 64 0x36014)];
  ec_done  : rw_cells rsegs v 0xb1d50 [C1 (Z_to_bv 8 0)];                 (* [comment removed for export] *)
  ec_dfgot : ro_cells rsegs v 0xa9160 [C8 (Z_to_bv 64 0x98890); C8 (Z_to_bv 64 0)];
  ec_dso   : ro_cells rsegs v 0xaaec0 [C8 (Z_to_bv 64 0xaaec0)];
  (* [comment removed for export] *)
  ec_dtor  : dtor_consts v;
  ec_flag  : rw_cells rsegs v ELF_FLAG [C8 (Z_to_bv 64 1)];
  ec_mux   : rw_cells rsegs v MU_GLOBALS [C8 (Z_to_bv 64 0)];
  ec_odra  : rw_cells rsegs v ODR_A [C1 b1; C1 b2];
  ec_odrb  : rw_cells rsegs v ODR_B [C1 b3; C1 b4];
  ec_gsh   : gshadows v gtab bss;
  ec_msh   : rw_cells rsegs v (gsh GMETA) [CB 2072 junk0];
  (* [comment removed for export] *)
  ec_ofl   : ro_cells rsegs v OFL_HEAD [C8 (Z_to_bv 64 0)];
  ec_uin   : ro_cells rsegs v 0xadbf0 [C8 (Z_to_bv 64 STDIN_F)];
  ec_uout  : ro_cells rsegs v 0xadb00 [C8 (Z_to_bv 64 STDOUT_F)];
  ec_uerr  : ro_cells rsegs v 0xada10 [C8 (Z_to_bv 64 STDERR_F)];
  ec_in    : file_clean v STDIN_F wp0 rp0;
  ec_err   : file_clean v STDERR_F wp2 rp2
}.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition exit_spec_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model)
         (H HL : hull) (E : Z) (lo : Z)
         (tid : Z) (ini : Z) (fin : byte) (bss : list (list byte)) (b1 b2 b3 b4 : byte) (junk0 : list byte) (wp0 rp0 wp2 rp2 : word)
         (pending : list byte),
    let v := mrestrict (hidc H) m in
    H_off_segments rsegs (hidc H) -> MInv H HL E md -> m_halted md = None ->
    mem_inv rsegs v ->
    tp = Z_to_bv 64 TPV ->
    stk rsegs v lo (bv_unsigned sp) -> lo + EXIT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
    exit_cells v tid ini fin bss b1 b2 b3 b4 junk0 wp0 rp0 wp2 rp2 ->
    (   (pending = [] /\ exists wp1 rp1, file_clean v STDOUT_F wp1 rp1)
     \/ (exists wb wp wend bufp bufsz rp1 canary, stdout_pending v wb wp wend bufp bufsz rp1 canary pending
           /\ fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)))) ->
    srealizes rsegs
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 EXIT_ENTRY) fc None m (seg_rom rsegs)) md)
      (t_emit (W 1 pending) (t_exit (bv_and a0 (Z_to_bv 64 255)) (m_fs md))).

End CEIL.
