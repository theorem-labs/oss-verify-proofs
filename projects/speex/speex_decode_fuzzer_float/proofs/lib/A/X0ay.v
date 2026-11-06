(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05s X05u
X081 X05l X05m X09f X06d X069 X05y X05z X060 X05w X082 X08y X0b1 X0b0 X068.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X0wn X0ys X0x2 X0wp X0yt X0zq X11l X11k X0x1.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SbCalleeStmts.
Variable RT : rt_sig.

Definition ctl2_cps_at (d : dec_state bptr) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (OUTL OUT STEREO S : Z) (LBD : list block) (r : ctl_req) (P lo : Z),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (ctl_req_code r) -> a2 = Z_to_bv 64 P -> tp = Z_to_bv 64 0x638c98 ->
creq_grp1 r = false ->
DREP OUTL STEREO m S d LBD -> (match r with CtlSetInnovationSave _ => True | _ => OUTL = OUT end) ->
(dec_depth d <= 3)%nat -> List.NoDup (map blk_id LBD) -> blocks_al8 LBD ->
creq_ok OUT P r -> creq_pre STEREO m S d P r ->
(forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
(match r with CtlSetInnovationSave _ => True | _ => dst_obj RT Σ m P (creq_size r) end) ->
(length (rt_frames RT Σ) + dec_depth d <= FRAMES_MAX)%nat -> Z.of_nat (dec_depth d) <= rt_credit RT Σ + 1 ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
ART RT Σ m -> mem_inv bsegs m -> X1cn.frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + ctl_stack d <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_ctl m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (creq_ivs P r ++ blocks_ivs LBD) m m'
/\ DREP OUT STEREO m' S (snd (speex_decoder_ctl d r)) LBD
/\ creq_post STEREO m' P r (fst (speex_decoder_ctl d r))
/\ (EXCREADY m S d -> EXCREADY m' S (snd (speex_decoder_ctl d r)))
/\ (match r with CtlSetInnovationSave _ => True | _ => dst_obj RT Σ' m' P (creq_size r) end)) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - (Z.of_nat (dec_depth d) - 1) <= rt_credit RT Σ' <= rt_credit RT Σ
/\ rt_pois RT Σ' = rt_pois RT Σ).

Definition SBLOST_STACK : Z := 112 + 5776.

Definition sb_decode_lost_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (S OUT lo fh : Z) (kh : nat) (s : sbd_state bptr) (a : sb_addrs) (j : sb_junk) (ows : list word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 1 -> tp = Z_to_bv 64 0x638c98 ->
rw_cells bsegs m S (SBCELLS s a OUT j) -> sb_junk_ok s j -> sb_inv s -> sb_bufs bsegs m a j -> S mod 8 = 0 -> 0 < S -> sb_addrs_al a ->
List.NoDup (map blk_id (sb_blocks s S a)) -> (forall b, In b (sb_blocks s S a) -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
rw_cells bsegs m OUT (f32 ows) -> length ows = 2000%nat -> In (fh, kh) (rt_frames RT Σ) -> in_frame_obj RT Σ m fh kh OUT 8000 ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
ART RT Σ m -> mem_inv bsegs m -> X1cn.frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + SBLOST_STACK <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_sb_decode_lost m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' (j' : sb_junk) (ows' : list word),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) ((OUT, OUT + 8000) :: blocks_ivs (sb_blocks s S a)) m m'
/\ rw_cells bsegs m' S (SBCELLS (set_sbd_first s 1) a OUT j') /\ sb_junk_ok (set_sbd_first s 1) j' /\ sb_bufs bsegs m' a j'
/\ rw_cells bsegs m' OUT (f32 ows') /\ length ows' = 2000%nat /\ acc bsegs m' OUT 8000) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
End SbCalleeStmts.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SbCalleeStmts.
Variable RT : rt_sig.

Definition ctl2_cps_at (d : dec_state bptr) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (OUTL OUT STEREO S : Z) (LBD : list block) (r : ctl_req) (P lo : Z),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (ctl_req_code r) -> a2 = Z_to_bv 64 P -> tp = Z_to_bv 64 0x630458 ->
creq_grp1 r = false ->
DREP OUTL STEREO m S d LBD -> (match r with CtlSetInnovationSave _ => True | _ => OUTL = OUT end) ->
(dec_depth d <= 3)%nat -> List.NoDup (map blk_id LBD) -> blocks_al8 LBD ->
creq_ok OUT P r -> creq_pre STEREO m S d P r ->
(forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
(match r with CtlSetInnovationSave _ => True | _ => dst_obj RT Σ m P (creq_size r) end) ->
(length (rt_frames RT Σ) + dec_depth d <= FRAMES_MAX)%nat -> Z.of_nat (dec_depth d) <= rt_credit RT Σ + 1 ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
ART RT Σ m -> mem_inv asegs m -> X1cn.frm0 fc ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + ctl_stack d <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_ctl m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (creq_ivs P r ++ blocks_ivs LBD) m m'
/\ DREP OUT STEREO m' S (snd (speex_decoder_ctl d r)) LBD
/\ creq_post STEREO m' P r (fst (speex_decoder_ctl d r))
/\ (EXCREADY m S d -> EXCREADY m' S (snd (speex_decoder_ctl d r)))
/\ (match r with CtlSetInnovationSave _ => True | _ => dst_obj RT Σ' m' P (creq_size r) end)) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - (Z.of_nat (dec_depth d) - 1) <= rt_credit RT Σ' <= rt_credit RT Σ
/\ rt_pois RT Σ' = rt_pois RT Σ).

Definition SBLOST_STACK : Z := 112 + 5744.
Definition sb_decode_lost_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (S OUT lo fh : Z) (kh : nat) (s : sbd_state bptr) (a : sb_addrs) (j : sb_junk) (ows : list word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 1 -> tp = Z_to_bv 64 0x630458 ->
rw_cells asegs m S (SBCELLS s a OUT j) -> sb_junk_ok s j -> sb_inv s -> sb_bufs asegs m a j -> S mod 8 = 0 -> 0 < S -> sb_addrs_al a ->
List.NoDup (map blk_id (sb_blocks s S a)) -> (forall b, In b (sb_blocks s S a) -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
rw_cells asegs m OUT (f32 ows) -> length ows = 2000%nat -> In (fh, kh) (rt_frames RT Σ) -> in_frame_obj RT Σ m fh kh OUT 8000 ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
ART RT Σ m -> mem_inv asegs m -> X1cn.frm0 fc ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + SBLOST_STACK <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_sb_decode_lost m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' (j' : sb_junk) (ows' : list word),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) ((OUT, OUT + 8000) :: blocks_ivs (sb_blocks s S a)) m m'
/\ rw_cells asegs m' S (SBCELLS (set_sbd_first s 1) a OUT j') /\ sb_junk_ok (set_sbd_first s 1) j' /\ sb_bufs asegs m' a j'
/\ rw_cells asegs m' OUT (f32 ows') /\ length ows' = 2000%nat /\ acc asegs m' OUT 8000) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
End SbCalleeStmts.
