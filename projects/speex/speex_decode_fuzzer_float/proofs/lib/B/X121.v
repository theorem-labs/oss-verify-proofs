(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu X1dh X1dk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X05m X09f X06d.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0x2 X0yt X11l X0yd.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Definition A_lost_loop : Z := 0xc0d7c.
Definition PC_lost_seed : Z := 0xc0e34.
Section LOSTLOOP.
Variables (OUT NW S Y : Z).
Variables (rav spv gp tp s0v s1v a0v a4v s3v s4v s5v s6v s8v s10v s11v : word).
Variable m : mem.
Hypothesis EY : Y = OUT + 4 * NW.
Hypothesis OBY : aobj bsegs m Y (4 * NW).
Hypothesis O4 : OUT mod 4 = 0.
Hypothesis OP : 0 < OUT.
Hypothesis NWR : 1 <= NW <= 320.
Hypothesis OBS : aobj bsegs m S 160.
Hypothesis S8 : S mod 8 = 0.
Hypothesis SY : S + 160 <= Y \/ Y + 4 * NW <= S.
Local Notation W := [(Y, Y + 4 * NW)].
Definition lost_R (i : Z) (a1v a2v t5v t6v : word) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 3) (Z_to_bv 64 1664525) (Z_to_bv 64 1013904223) s0v s1v
a0v a1v a2v (Z_to_bv 64 NW) a4v (Z_to_bv 64 i) (Z_to_bv 64 1065353216) (Z_to_bv 64 (Z.shiftr (S + 128) 3 + SHB))
(Z_to_bv 64 OUT) s3v s4v s5v s6v (Z_to_bv 64 (S + 128)) s8v (Z_to_bv 64 SHB) s10v s11v (Z_to_bv 64 NW) (Z_to_bv 64 1) t5v t6v.
Definition lost_loop_post : machine_state -> Prop :=
fun ms' => exists (a1' a2' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ys : list word),
ms' = MS (lost_R NW a1' a2' t5' t6') F' (Z_to_bv 64 PC_lost_seed) fc' None m' (seg_rom bsegs)
/\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ frm0 fc' /\ Z.of_nat (length ys) = NW /\ rw_cells bsegs m' Y (f32 ys).
Lemma lost_loop : forall (rest dn : list word) (x le a1v a2v t5v t6v : word) (i off : Z) F fc m1,
Z.of_nat (length dn) + Z.of_nat (Datatypes.S (length rest)) = NW ->
i = Z.of_nat (length dn) -> off = 4 * i ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 (S + 128) [C4 le] ->
rw_cells bsegs m1 Y (f32 dn) -> rw_cells bsegs m1 (Y + off) (f32 (x :: rest)) ->
evt bsegs lost_loop_post (MS (lost_R i a1v a2v t5v t6v) F (Z_to_bv 64 A_lost_loop) fc None m1 (seg_rom bsegs)).
Proof using EY OBY O4 OP NWR OBS S8 SY.
induction rest as [|x' rest IH]; intros dn x le a1v a2v t5v t6v i off F fc m1 HL Hi Hoff FRM MU OF WM MI LE DONE X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof OBY as (OY0 & OY1 & _); pose proof OBS as (OS0 & OS1 & _); unfold APP_TOP in *;
unfold lost_R; rewrite !f32_cons, ?f32_nil in X.
- bato 0xc0dc4. replace (OUT + (i + NW + 0) * 4) with (Y + off) by lia.
assert (AL : (Y + off) mod 4 = 0) by (rewrite EY, Hoff; clear - O4; Z.div_mod_to_equations; lia).
bato 0xc0ddc. astep. chk_merge OBY 4.
bato 0xc0e10. cbn [length] in HL. rewrite (swrap32_small (i + 1)) by lia. replace (i + 1) with NW by lia. bato 0xc0e34.
unfold lost_loop_post, lost_R. finish.
2: { subst off i. chunk_snoc DONE X. f32_fold_snoc DONE. exact DONE. }
rewrite length_app. cbn [length] in *. lia.
- bato 0xc0dc4. replace (OUT + (i + NW + 0) * 4) with (Y + off) by lia.
assert (AL : (Y + off) mod 4 = 0) by (rewrite EY, Hoff; clear - O4; Z.div_mod_to_equations; lia).
bato 0xc0ddc. astep. chk_merge OBY 4.
bato 0xc0e10. cbn [length] in HL. rewrite (swrap32_small (i + 1)) by lia. astep. sh_if.
chunk_uncons X as X1. chunk_snoc DONE X1.
replace (Y + off + 4) with (Y + (off + 4)) in * by lia.
rewrite <- f32_cons in X. f32_fold_snoc DONE.
eapply (IH _ x' _ _ _ _ _ (i + 1) (off + 4)); try eassumption; try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End LOSTLOOP.

Ltac lslia1h := first [ lia | match goal with H : hid (_ \/ _) |- _ => unfold hid in H; lia end ].
Ltac lslia_ch := lazymatch goal with |- _ /\ _ => split; [lslia1h | lslia_ch] | |- True => exact I | |- _ => lslia1h end.
Local Ltac slia ::= lslia_ch.
Local Ltac tlia ::= tlia_one.

Definition RA_lost_iir : Z := 0xc0eb4.
Definition RA_lost_qmf : Z := 0xc0f48.
Definition A_lost_qmf : Z := 0xa8508.
Definition A_lost_h0 : Z := 0x27000.

Definition lost_frame (x0 : word) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
[C8 x0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma cells_size_lost_frame : forall x0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
cells_size (lost_frame x0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 112%nat.
Proof. intros. reflexivity. Qed.

Lemma lost_w1 : forall (usp lo S OUT Y fsz : Z) (s : sbd_state bptr) (a : sb_addrs) (fst0 le seed : word) (cw : word) (rest iq msp : list word)
(ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 36) [C4 fst0] -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) ->
rw_cells bsegs m (S + 128) [C4 le] -> rw_cells bsegs m (S + 132) [C4 seed] -> rw_cells bsegs m (S + 152) [C4 (Z_to_bv 64 (sbd_submodeID s))] ->
sbd_frame_size s = fsz -> sbd_full_frame_size s = 2 * fsz -> sbd_lpcSize s = 8 -> 1 <= fsz <= 320 -> 0 <= sbd_submodeID s <= 7 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> IMG_TOP_B <= S -> S + 160 <= lo ->
Y = OUT + 4 * fsz -> rw_cells bsegs m Y (f32 (cw :: rest)) -> Z.of_nat (length rest) + 1 = fsz -> aobj bsegs m Y (4 * fsz) -> OUT mod 4 = 0 -> 0 < OUT -> IMG_TOP_B <= Y -> Y + 4 * fsz <= lo ->
rw_cells bsegs m (a_iq a) (f32 iq) -> length iq = 8%nat -> aobj bsegs m (a_iq a) 32 -> a_iq a mod 4 = 0 -> 0 < a_iq a -> a_iq a + 32 <= lo ->
rw_cells bsegs m (a_msp a) (f32 msp) -> length msp = 8%nat -> aobj bsegs m (a_msp a) 32 -> a_msp a mod 4 = 0 -> 0 < a_msp a -> IMG_TOP_B <= a_msp a -> a_msp a + 32 <= lo ->
hidp (S + 160 <= SH_LO \/ SH_HI <= S) -> hidp (Y + 4 * fsz <= SH_LO \/ SH_HI <= Y) -> hidp (a_msp a + 32 <= SH_LO \/ SH_HI <= a_msp a) ->
hidp (S + 160 <= Y \/ Y + 4 * fsz <= S) -> hidp (S + 160 <= a_iq a \/ a_iq a + 32 <= S) -> hidp (S + 160 <= a_msp a \/ a_msp a + 32 <= S) ->
hidp (Y + 4 * fsz <= a_iq a \/ a_iq a + 32 <= Y) -> hidp (Y + 4 * fsz <= a_msp a \/ a_msp a + 32 <= Y) -> hidp (a_iq a + 32 <= a_msp a \/ a_msp a + 32 <= a_iq a) ->
stk bsegs m lo usp -> lo <= usp - 240 -> SH_HI <= lo -> usp < 2^63 ->
client_constsB m -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xt3 xt4 xt5 xt6 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (ys mv : list word) (seed' : word),
ms = MS (mkR (Z_to_bv 64 RA_lost_qmf) (Z_to_bv 64 (usp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (S + 152)) (Z_to_bv 64 1)
(Z_to_bv 64 OUT) (Z_to_bv 64 Y) (Z_to_bv 64 A_lost_h0) (Z_to_bv 64 OUT) (Z_to_bv 64 (2 * fsz)) (Z_to_bv 64 64) (Z_to_bv 64 (a_g0 a)) (Z_to_bv 64 (a_g1 a))
(Z_to_bv 64 OUT) a3 (Z_to_bv 64 S) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (S + 88)) (Z_to_bv 64 1) (Z_to_bv 64 (S + 20)) (Z_to_bv 64 SHB)
(Z_to_bv 64 (sbd_submodeID s)) (Z_to_bv 64 (Z.shiftr (S + 20) 3 + SHB)) xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 A_lost_qmf) fc1 None m1 (seg_rom bsegs)
/\ munch [(usp + -240, usp); (S + 36, S + 40); (S + 132, S + 136); (S + 152, S + 156); (Y, Y + 4 * fsz); (a_msp a, a_msp a + 32)] m m1
/\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ frm0 fc1 /\ stk bsegs m1 lo (usp + -112)
/\ rw_cells bsegs m1 (usp + -112) (lost_frame a3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
/\ rw_cells bsegs m1 S (sbp_hdr s a) /\ rw_cells bsegs m1 (S + 36) [C4 (Z_to_bv 64 1)] /\ rw_cells bsegs m1 (S + 40) (sbp_ptrs s a OUT)
/\ rw_cells bsegs m1 (S + 128) [C4 le] /\ rw_cells bsegs m1 (S + 132) [C4 seed'] /\ rw_cells bsegs m1 (S + 152) [C4 (Z_to_bv 64 1)]
/\ rw_cells bsegs m1 Y (f32 ys) /\ Z.of_nat (length ys) = fsz /\ rw_cells bsegs m1 (a_iq a) (f32 iq)
/\ rw_cells bsegs m1 (a_msp a) (f32 mv) /\ length mv = 8%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 OUT) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_sb_decode_lost) fc None m (seg_rom bsegs)).
Proof.
intros usp lo S OUT Y fsz s a fst0 le seed cw rest iq msp ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m.
intros HD FST PT LE SEED IDC EFS EFFS ELPC HFS HID OBS S8 SPOS SIMG SLO EY YC LR OBY O4 OPOS YIMG YLO IQC LIQ OBQ Q4 QPOS QLO MSPC LMSP OBM M4 MPOS MIMG MLO
SSH YSH MSH SY SQ SM YQ YM QM ST LO LOS SPH CC MI FRM.
unfold A_sb_decode_lost, RA_lost_qmf, RA_lost_iir, A_lost_qmf, A_lost_h0, lost_frame in *.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof OBS as (OS0 & OS1 & _). pose proof OBY as (OY0 & OY1 & _). pose proof OBQ as (OQ0 & OQ1 & _). pose proof OBM as (OM0 & OM1 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP_B in SIMG, YIMG, MIMG.
pose proof ST as (STa & STb & _).
repeat match goal with H : hidp ?P |- _ => change (hid P) in H end.
pose proof (munch_refl [(usp + -240, usp); (S + 36, S + 40); (S + 132, S + 136); (S + 152, S + 156); (Y, Y + 4 * fsz); (a_msp a, a_msp a + 32)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -240, usp); (S + 36, S + 40); (S + 132, S + 136); (S + 152, S + 156); (Y, Y + 4 * fsz); (a_msp a, a_msp a + 32)])
by (cbn [offsh]; clear - SSH YSH MSH LOS' LO HFS; unfold hid, SH_LO, SH_HI in *; lia).
unfold sbp_hdr in HD. rewrite EFS, EFFS, ELPC in HD. unfold sbp_ptrs in PT.
carve_frame 112%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0xc0d18. rewrite !sx32_small by (unfold int31; lia). bato 0xc0d7c.
replace (Z.land (S + 128) 7 + 3) with 3 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; clear - S8; Z.div_mod_to_equations; lia).
assert (ET3 : Z.land (bv_swrap 32 (0 - Z.b2z (9223372036854775808 <? Z.lxor fsz 9223372036854775808)) mod 18446744073709551616) fsz = fsz).
{ change 9223372036854775808 with (2^63). rewrite (zb_lxor_pow2_small fsz 63) by lia.
replace (2^63 <? fsz + 2^63) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
rewrite (swrap32_small (0 - 1)) by lia. change ((0 - 1) mod 18446744073709551616) with (2^64 - 1).
rewrite zb_land_mask_l by lia. apply Z.mod_small. lia. }
rewrite ET3. clear ET3.
replace (0 <? OUT) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
replace Y with (Y + 0) in YC at 1 by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch bsegs W m mc Y (4 * fsz) OBY MUc (shfree_of_aobj bsegs W m Y (4 * fsz) OF OBY)) as OBYc;
pose proof (aobj_munch bsegs W m mc S 160 OBS MUc (shfree_of_aobj bsegs W m S 160 OF OBS)) as OBSc;
call (lost_loop OUT fsz S Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc EY OBYc O4 OPOS HFS OBSc S8 ltac:(unfold hid in SY; exact SY) rest [] cw le _ _ _ _ 0 0 _ _ mc)
end
end.
{ cbn [length]. lia. }
{ reflexivity. }
{ reflexivity. }
{ assumption. }
{ apply munch_refl. }
{ cbn [offsh]. clear - YSH. unfold hid, SH_LO, SH_HI in *. lia. }
{ apply wmono_refl. }
{ assumption. }
{ assumption. }
{ rewrite f32_nil. apply rw_cells_nil. lia. }
{ assumption. }
clear OBYc OBSc. rename POST into YS1. rename PC0 into LYS1. rename PC into FRM1.
unfold lost_R. bato 0xa6ad8.
replace (fsz * 4 + OUT) with Y by lia.
rewrite sx32_small by (unfold int31; lia).
replace (Z_to_bv 64 fsz) with (Z_to_bv 64 (Z.of_nat (length x6))) by (rewrite LYS1; reflexivity).
replace (Z_to_bv 64 8) with (Z_to_bv 64 (Z.of_nat (length iq))) by (rewrite LIQ; reflexivity).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch bsegs W m mc Y (4 * fsz) OBY MUc (shfree_of_aobj bsegs W m Y (4 * fsz) OF OBY)) as OBYc;
pose proof (aobj_munch bsegs W m mc (a_iq a) 32 OBQ MUc (shfree_of_aobj bsegs W m (a_iq a) 32 OF OBQ)) as OBQc;
pose proof (aobj_munch bsegs W m mc (a_msp a) 32 OBM MUc (shfree_of_aobj bsegs W m (a_msp a) 32 OF OBM)) as OBMc;
call (iir_mem16_walk_ip x6 iq msp Y (a_iq a) (a_msp a) (usp + -112) lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc)
end
end.
{ rewrite LMSP, LIQ. reflexivity. }
{ rewrite LYS1. lia. }
{ rewrite LIQ. cbn. lia. }
{ rewrite LYS1. exact OBYc. }
{ rewrite LIQ. exact OBQc. }
{ rewrite LIQ. exact OBMc. }
{ rewrite EY. clear - O4. Z.div_mod_to_equations. lia. }
{ exact Q4. }
{ exact M4. }
{ lia. }
{ exact QPOS. }
{ exact MPOS. }
{ lia. }
{ exact LOS. }
{ lia. }
{ rewrite LYS1. clear - YSH. unfold hid in *. lia. }
{ rewrite LIQ. clear - MSH. unfold hid in *. cbn. lia. }
{ left. rewrite LYS1. lia. }
{ left. rewrite LIQ. cbn. lia. }
{ left. rewrite LIQ. cbn. lia. }
{ rewrite LIQ. clear - QM. unfold hid in *. cbn. lia. }
{ rewrite LYS1, LIQ. clear - YM. unfold hid in *. cbn. lia. }
{ rewrite LYS1, LIQ. clear - YQ. unfold hid in *. cbn. lia. }
{ exact YS1. }
{ exact IQC. }
{ exact MSPC. }
{ exact FRM1. }
{ assumption. }
{ unfold IMG_TOP_B. lia. }
{ unfold IMG_TOP_B. lia. }
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return.
exact (conj G1 (conj G2 (conj G3 G4))). }
{ assumption. }
clear OBYc OBQc OBMc POST FRM1. rename PC into ST2. rename PC0 into FRM2. rename PC1 into LYS2. rename PC2 into YS2. rename PC3 into LMSP2. rename PC4 into MSP2. rename PC5 into IQ2.
bato 0xc0ec0. rewrite !sx32_small by (unfold int31; lia). bato 0xa8508.
rewrite !sx32_small by (unfold int31; lia).
replace (fsz * 4 + OUT) with Y by lia.
apply evt_done. do 13 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM2|]. split; [exact ST2|]. split; [exact FR|].
split; [unfold sbp_hdr; rewrite EFS, EFFS, ELPC; exact HD|]. split; [exact FST|]. split; [unfold sbp_ptrs; exact PT|].
split; [exact LE|]. split; [exact SEED|]. split; [exact IDC|]. split; [exact YS2|]. split; [rewrite LYS2; exact LYS1|]. split; [exact IQ2|].
split; [exact MSP2| rewrite LMSP2; exact LIQ].
Qed.

Lemma lost_w2 : forall (usp lo S id : Z) (x0 : word)
(ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v s2v s3v s4v s5v s6v s7v s8v s11v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -112) (lost_frame x0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
rw_cells bsegs m (S + 152) [C4 (Z_to_bv 64 1)] -> aobj bsegs m S 160 -> S mod 8 = 0 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo -> 0 <= id <= 7 ->
stk bsegs m lo (usp + -112) -> lo <= usp + -112 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (v' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 v' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m1 (seg_rom bsegs)
/\ munch [(S + 152, S + 156)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp /\ rw_cells bsegs m1 (S + 152) [C4 (Z_to_bv 64 id)])
(MS (mkR (Z_to_bv 64 RA_lost_qmf) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (S + 152)) (Z_to_bv 64 1) v a1 a2 a3 a4 a5 a6 a7
s2v s3v s4v s5v s6v s7v s8v (Z_to_bv 64 SHB) (Z_to_bv 64 id) s11v t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_lost_qmf)) fc None m (seg_rom bsegs)).
Proof.
intros usp lo S id x0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v s2v s3v s4v s5v s6v s7v s8v s11v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m.
intros FR IDC OBS S8 SSH SLO HID ST LO LOS SPH MI.
unfold RA_lost_qmf, lost_frame in *.
replace (ret_pc (Z_to_bv 64 0xc0f48)) with (Z_to_bv 64 0xc0f48) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(S + 152, S + 156)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S + 152, S + 156)]) by (cbn [offsh]; clear - SSH; unfold SH_LO, SH_HI in *; lia).
bato 0xc0f60.
bato 0xc0f94. release_frame FR ST usp. astep. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact IDC].
Qed.
