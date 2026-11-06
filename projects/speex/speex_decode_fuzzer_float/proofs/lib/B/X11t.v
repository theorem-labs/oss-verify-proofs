(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X07z.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X05m X09f X06d.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X12c X14x X0r0 X0ra X0v9 X0yr X12b X0z5 X0wl X0wn X0wm
X0ys X0x2 X0yt X0zq X11l X11k X0w7 X0yz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X11w.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_sb_slots, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Definition sblB_v544A (hb : Z) (sm : submode) : Z := hb - (if sm_double_codebook sm =? 0 then 0 else 224).

Definition sblB_dA_stmt (RT : rt_sig) : Prop :=
forall (Σ : rts RT) PMc (usp lo hb S OUT A D f sf MODE fsz FS sub fh PD ND : Z) (kh : nat) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(b : bits_st bptr) (sm : submode) (pad1 : list byte) (seed : word) (ex ows ler : list word)
(xs4 xs10 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
fdfs_only PMc -> mat_stable PMc -> X1cn.frm0 fc ->
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) -> v_480 v = Z_to_bv 64 sub -> v_456 v = Z_to_bv 64 (4 * sub) -> v_544 v = Z_to_bv 64 hb ->
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 132) [C4 seed] -> rw_cells bsegs m (S + 136) (sbp_cfg s pad1) ->
rw_cells bsegs m (S + 152) [C4 (Z_to_bv 64 (sbd_submodeID s))] ->
sbd_subframeSize s = FS -> sbd_frame_size s = fsz -> 0 <= sbd_submodeID s <= 7 ->
((sbd_mode s = ModeWB /\ FS = 40 /\ fsz = 160 /\ hb = usp + -1440) \/ (sbd_mode s = ModeUWB /\ FS = 80 /\ fsz = 320 /\ hb = usp + -1600)) ->
MODE = sbmode_struct (sbd_mode s) -> submode_at (sbm_submodes (sbd_mode s)) (sbd_submodeID s) = Some sm -> 0 <= sub < 4 ->
In (S, 160) (rt_live RT Σ) -> S mod 8 = 0 ->
bits_rep bsegs m A D b -> bits_ok b -> In (fh, kh) (rt_frames RT Σ) -> fh <= A -> A + BITS_SIZEOF <= fh + fs_size kh - 8 -> A mod 4 = 0 -> acc bsegs m A BITS_SIZEOF ->
In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b <= PD + ND -> PD <> S ->
rw_cells bsegs m (usp + -896) (f32 ler) -> length ler = 4%nat -> In (usp + -896, 16) (rt_pois RT Σ) ->
rw_cells bsegs m OUT (f32 ows) -> length ows = 2000%nat -> fh <= OUT -> OUT + 8000 <= fh + fs_size kh - 8 -> OUT mod 4 = 0 -> acc bsegs m OUT 8000 ->
hidp (A + BITS_SIZEOF <= OUT \/ OUT + 8000 <= A) ->
rw_cells bsegs m (hb + 32) (f32 ex) -> Z.of_nat (length ex) = FS -> In (hb + 32, 4 * FS) (rt_pois RT Σ) ->
pois_above (rt_pois RT Σ) hb -> rt_frames RT Σ <> [] ->
ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo hb -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + SB_LOOP_STACK <= usp + -1216 ->
usp mod 32 = 0 -> usp + 16 <= USTACK_TOP -> tp = Z_to_bv 64 0x638c98 ->
cps bsegs (ASTA RT Σ PMc (eq (MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_memset2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) xs4 (Z_to_bv 64 0x10360) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_memset2)) fc None m (seg_rom bsegs))))
(fun c => exists Σ', ASTA RT Σ' PMc (fun ms => exists (m' : mem) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs9 xs10' xt3 xt5 : word) (F' : bvmap 5 word) (fc' : bv 32)
(v' : sb_vslots) (seed' : word) (ex' : list word),
ms = MS (R_LB usp hb gp tp xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
xs2 (Z_to_bv 64 (hb + 32)) xs4 xs5 (Z_to_bv 64 (4 * FS)) xs9 xs10'
xt3 (Z_to_bv 64 (S + 72)) xt5 (Z_to_bv 64 (S + 88))) F' (Z_to_bv 64 SBLB_PC_J) fc' None m' (seg_rom bsegs)
/\ X1cn.frm0 fc' /\ rt_after RT Σ' hb lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) hb [(usp + -736, usp + -160); (S + 132, S + 136); (A, A + BITS_SIZEOF); (hb + 32, hb + 32 + 4 * FS)] m m'
/\ rw_cells bsegs m' (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v') /\ v_480 v' = Z_to_bv 64 sub /\ v_544 v' = Z_to_bv 64 (sblB_v544A hb sm)
/\ v_288 v' = v_288 v /\ v_392 v' = v_392 v /\ v_456 v' = v_456 v
/\ rw_cells bsegs m' (S + 132) [C4 seed']
/\ rw_cells bsegs m' (hb + 32) (f32 ex') /\ Z.of_nat (length ex') = FS
/\ bits_rep bsegs m' A D (sbsub_bits sm b) /\ bits_ok (sbsub_bits sm b) /\ acc bsegs m' A BITS_SIZEOF) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

