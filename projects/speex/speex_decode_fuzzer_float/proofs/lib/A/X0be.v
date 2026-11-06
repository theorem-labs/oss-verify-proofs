(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05q X081 X05l X05m X09f X06d X069 X082
X0b1 X07l.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Definition A_lost_loop : Z := 0xb8738.
Definition PC_lost_seed : Z := 0xb87b8.
Section LOSTLOOP.
Variables (Y NW S : Z).
Variables (rav spv gp tp s0v s1v a0v a3v a4v s2v s3v s4v s5v s6v s7v s9v s10v s11v : word).
Variable m : mem.
Hypothesis OBY : aobj asegs m Y (4 * NW).
Hypothesis Y4 : Y mod 4 = 0.
Hypothesis OBS : aobj asegs m S 160.
Hypothesis S8 : S mod 8 = 0.
Hypothesis SY : S + 160 <= Y \/ Y + 4 * NW <= S.
Local Notation W := [(Y, Y + 4 * NW)].
Definition lost_R (ya cnt : Z) (a5v t5v t6v : word) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 1664525) (Z_to_bv 64 1013904223) (Z_to_bv 64 (Z.shiftr (S + 128) 3 + SHB)) s0v s1v
a0v (Z_to_bv 64 (S + 128)) (Z_to_bv 64 ya) a3v a4v a5v (Z_to_bv 64 1065353216) (Z_to_bv 64 cnt)
s2v s3v s4v s5v s6v s7v (Z_to_bv 64 SHB) s9v s10v s11v (Z_to_bv 64 3) (Z_to_bv 64 ya) t5v t6v.
Definition lost_loop_post : machine_state -> Prop :=
fun ms' => exists (a5' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ys : list word),
ms' = MS (lost_R (Y + 4 * NW) 0 a5' t5' t6') F' (Z_to_bv 64 PC_lost_seed) fc' None m' (seg_rom asegs)
/\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ frm0 fc' /\ Z.of_nat (length ys) = NW /\ rw_cells asegs m' Y (f32 ys).
Lemma lost_loop : forall (rest dn : list word) (x le a5v t5v t6v : word) (ya kz off : Z) F fc m1,
Z.of_nat (length dn) + Z.of_nat (Datatypes.S (length rest)) = NW -> NW < 2^31 ->
ya = Y + off -> kz = Z.of_nat (Datatypes.S (length rest)) -> off = 4 * Z.of_nat (length dn) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
rw_cells asegs m1 (S + 128) [C4 le] ->
rw_cells asegs m1 Y (f32 dn) -> rw_cells asegs m1 (Y + off) (f32 (x :: rest)) ->
evt asegs lost_loop_post (MS (lost_R ya kz a5v t5v t6v) F (Z_to_bv 64 A_lost_loop) fc None m1 (seg_rom asegs)).
Proof using OBY Y4 OBS S8 SY.
induction rest as [|x' rest IH]; intros dn x le a5v t5v t6v ya kz off F fc m1 HL HNW Hya Hkz Hoff FRM MU OF WM MI LE DONE X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof OBY as (OY0 & OY1 & _); pose proof OBS as (OS0 & OS1 & _); unfold APP_TOP in *; subst kz ya;
unfold lost_R; rewrite !f32_cons, ?f32_nil in X.
- ato 0xb873c.
ato 0xb8750. astep. chk_merge OBY 4.
ato 0xb8794. astep.
ato 0xb87b8.
replace (Y + off + 4) with (Y + 4 * NW) by (cbn [length] in HL; lia).
replace (Z.of_nat (Datatypes.S (length (@nil word))) + -1) with 0 by reflexivity.
unfold lost_loop_post, lost_R. finish.
2: { chunk_snoc DONE X. f32_fold_snoc DONE. exact DONE. }
rewrite length_app. cbn [length] in *. lia.
- ato 0xb8750. astep. chk_merge OBY 4.
ato 0xb8794. astep. cbn [length]. sh_if.
chunk_uncons X as X1. chunk_snoc DONE X1.
replace (Y + off + 4) with (Y + (off + 4)) in * by lia.
rewrite <- f32_cons in X. f32_fold_snoc DONE.
eapply (IH _ x' _ _ _ _ _ _ (off + 4)); try eassumption; try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End LOSTLOOP.

Ltac lslia1h := first [ lia | match goal with H : hid (_ \/ _) |- _ => unfold hid in H; lia end ].
Ltac lslia_ch := lazymatch goal with |- _ /\ _ => split; [lslia1h | lslia_ch] | |- True => exact I | |- _ => lslia1h end.
Local Ltac slia ::= lslia_ch.
Local Ltac tlia ::= tlia_one.

Definition RA_lost_iir : Z := 0xb8818.
Definition RA_lost_qmf : Z := 0xb8890.
Definition A_lost_qmf : Z := 0xa4b58.
Definition A_lost_h0 : Z := 0x27000.

Definition lost_frame (x0 : word) (j8 : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) : list cell :=
[C8 x0; CB 8 j8; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma cells_size_lost_frame : forall x0 j8 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10,
cells_size (lost_frame x0 j8 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) = 112%nat.
Proof. intros. reflexivity. Qed.

Lemma lost_w1 : forall (usp lo S OUT Y fsz : Z) (s : sbd_state bptr) (a : sb_addrs) (fst0 le seed : word) (cw : word) (rest iq msp : list word)
(ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 36) [C4 fst0] -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) ->
rw_cells asegs m (S + 128) [C4 le] -> rw_cells asegs m (S + 132) [C4 seed] -> rw_cells asegs m (S + 152) [C4 (Z_to_bv 64 (sbd_submodeID s))] ->
sbd_frame_size s = fsz -> sbd_full_frame_size s = 2 * fsz -> sbd_lpcSize s = 8 -> 1 <= fsz <= 320 -> 0 <= sbd_submodeID s <= 7 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> IMG_TOP <= S -> S + 160 <= lo ->
Y = OUT + 4 * fsz -> rw_cells asegs m Y (f32 (cw :: rest)) -> Z.of_nat (length rest) + 1 = fsz -> aobj asegs m Y (4 * fsz) -> Y mod 4 = 0 -> IMG_TOP <= Y -> Y + 4 * fsz <= lo ->
rw_cells asegs m (a_iq a) (f32 iq) -> length iq = 8%nat -> aobj asegs m (a_iq a) 32 -> a_iq a mod 4 = 0 -> a_iq a + 32 <= lo ->
rw_cells asegs m (a_msp a) (f32 msp) -> length msp = 8%nat -> aobj asegs m (a_msp a) 32 -> a_msp a mod 4 = 0 -> IMG_TOP <= a_msp a -> a_msp a + 32 <= lo ->
hidp (S + 160 <= SH_LO \/ SH_HI <= S) -> hidp (Y + 4 * fsz <= SH_LO \/ SH_HI <= Y) -> hidp (a_msp a + 32 <= SH_LO \/ SH_HI <= a_msp a) ->
hidp (S + 160 <= Y \/ Y + 4 * fsz <= S) -> hidp (S + 160 <= a_iq a \/ a_iq a + 32 <= S) -> hidp (S + 160 <= a_msp a \/ a_msp a + 32 <= S) ->
hidp (Y + 4 * fsz <= a_iq a \/ a_iq a + 32 <= Y) -> hidp (Y + 4 * fsz <= a_msp a \/ a_msp a + 32 <= Y) -> hidp (a_iq a + 32 <= a_msp a \/ a_msp a + 32 <= a_iq a) ->
stk asegs m lo usp -> lo <= usp - 192 -> SH_HI <= lo -> usp < 2^63 ->
client_consts m -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xt3 xt4 xt5 xt6 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (ys mv : list word) (seed' : word) (j8 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_lost_qmf) (Z_to_bv 64 (usp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (S + 152)) (Z_to_bv 64 1)
(Z_to_bv 64 OUT) (Z_to_bv 64 Y) (Z_to_bv 64 A_lost_h0) (Z_to_bv 64 OUT) (Z_to_bv 64 (2 * fsz)) (Z_to_bv 64 64) (Z_to_bv 64 (a_g0 a)) (Z_to_bv 64 (a_g1 a))
(Z_to_bv 64 OUT) a3 (Z_to_bv 64 S) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (S + 88)) (Z_to_bv 64 (S + 20)) (Z_to_bv 64 SHB)
(Z_to_bv 64 (sbd_submodeID s)) (Z_to_bv 64 (Z.shiftr (S + 20) 3 + SHB)) s11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 A_lost_qmf) fc1 None m1 (seg_rom asegs)
/\ munch [(usp + -192, usp); (S + 36, S + 40); (S + 132, S + 136); (S + 152, S + 156); (Y, Y + 4 * fsz); (a_msp a, a_msp a + 32)] m m1
/\ wmono asegs m m1 /\ mem_inv asegs m1 /\ frm0 fc1 /\ stk asegs m1 lo (usp + -112)
/\ rw_cells asegs m1 (usp + -112) (lost_frame a3 j8 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)
/\ rw_cells asegs m1 S (sbp_hdr s a) /\ rw_cells asegs m1 (S + 36) [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m1 (S + 40) (sbp_ptrs s a OUT)
/\ rw_cells asegs m1 (S + 128) [C4 le] /\ rw_cells asegs m1 (S + 132) [C4 seed'] /\ rw_cells asegs m1 (S + 152) [C4 (Z_to_bv 64 1)]
/\ rw_cells asegs m1 Y (f32 ys) /\ Z.of_nat (length ys) = fsz /\ rw_cells asegs m1 (a_iq a) (f32 iq)
/\ rw_cells asegs m1 (a_msp a) (f32 mv) /\ length mv = 8%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 OUT) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_sb_decode_lost) fc None m (seg_rom asegs)).
Proof.
intros usp lo S OUT Y fsz s a fst0 le seed cw rest iq msp ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m.
intros HD FST PT LE SEED IDC EFS EFFS ELPC HFS HID OBS S8 SPOS SIMG SLO EY YC LR OBY Y4 YIMG YLO IQC LIQ OBQ Q4 QLO MSPC LMSP OBM M4 MIMG MLO
SSH YSH MSH SY SQ SM YQ YM QM ST LO LOS SPH CC MI FRM.
unfold A_sb_decode_lost, RA_lost_qmf, RA_lost_iir, A_lost_qmf, A_lost_h0, lost_frame in *.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof OBS as (OS0 & OS1 & _). pose proof OBY as (OY0 & OY1 & _). pose proof OBQ as (OQ0 & OQ1 & _). pose proof OBM as (OM0 & OM1 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP in SIMG, YIMG, MIMG.
pose proof ST as (STa & STb & _).
repeat match goal with H : hidp ?P |- _ => change (hid P) in H end.
pose proof (munch_refl [(usp + -192, usp); (S + 36, S + 40); (S + 132, S + 136); (S + 152, S + 156); (Y, Y + 4 * fsz); (a_msp a, a_msp a + 32)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -192, usp); (S + 36, S + 40); (S + 132, S + 136); (S + 152, S + 156); (Y, Y + 4 * fsz); (a_msp a, a_msp a + 32)])
by (cbn [offsh]; clear - SSH YSH MSH LOS' LO HFS; unfold hid, SH_LO, SH_HI in *; lia).
unfold sbp_hdr in HD. rewrite EFS, EFFS, ELPC in HD. unfold sbp_ptrs in PT.
carve_frame 112%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb869c.
ato 0xb86d0.
rewrite !sx32_small by (unfold int31; lia).
astep. sh_if.
ato 0xb8738.
rewrite (Z.mod_small fsz 4294967296) by lia.
replace (OUT + fsz ≪ 2) with Y by (rewrite Z.shiftl_mul_pow2 by lia; lia).
replace (Z.land (S + 128) 7 + 3) with 3 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; clear - S8; Z.div_mod_to_equations; lia).
replace Y with (Y + 0) in YC at 1 by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch asegs W m mc Y (4 * fsz) OBY MUc (shfree_of_aobj asegs W m Y (4 * fsz) OF OBY)) as OBYc;
pose proof (aobj_munch asegs W m mc S 160 OBS MUc (shfree_of_aobj asegs W m S 160 OF OBS)) as OBSc;
call (lost_loop Y fsz S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc OBYc Y4 OBSc S8 ltac:(unfold hid in SY; exact SY) rest [] cw le _ _ _ Y _ 0 _ _ mc)
end
end.
{ cbn [length]. lia. }
{ lia. }
{ lia. }
{ lia. }
{ reflexivity. }
{ exact FRM. }
{ apply munch_refl. }
{ cbn [offsh]. clear - YSH. unfold hid, SH_LO, SH_HI in *. lia. }
{ apply wmono_refl. }
{ exact MI. }
{ exact LE. }
{ rewrite f32_nil. apply rw_cells_nil. lia. }
{ exact YC. }
clear OBYc OBSc FRM. rename POST into YS1. rename PC0 into LYS1. rename PC into FRM1.
unfold lost_R.
ato 0xa3860.
replace (OUT + fsz ≪ 2) with Y by (rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite sx32_small by (unfold int31; lia).
replace (Z_to_bv 64 fsz) with (Z_to_bv 64 (Z.of_nat (length x5))) by (rewrite LYS1; reflexivity).
replace (Z_to_bv 64 8) with (Z_to_bv 64 (Z.of_nat (length iq))) by (rewrite LIQ; reflexivity).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch asegs W m mc Y (4 * fsz) OBY MUc (shfree_of_aobj asegs W m Y (4 * fsz) OF OBY)) as OBYc;
pose proof (aobj_munch asegs W m mc (a_iq a) 32 OBQ MUc (shfree_of_aobj asegs W m (a_iq a) 32 OF OBQ)) as OBQc;
pose proof (aobj_munch asegs W m mc (a_msp a) 32 OBM MUc (shfree_of_aobj asegs W m (a_msp a) 32 OF OBM)) as OBMc;
call (iir_mem16_walk_ip x5 iq msp Y (a_iq a) (a_msp a) (usp + -112) lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc)
end
end.
{ rewrite LMSP, LIQ. reflexivity. }
{ rewrite LYS1. lia. }
{ rewrite LIQ. cbn. lia. }
{ rewrite LYS1. exact OBYc. }
{ rewrite LIQ. exact OBQc. }
{ rewrite LIQ. exact OBMc. }
{ exact Y4. }
{ exact Q4. }
{ exact M4. }
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
{ exact ST. }
{ unfold IMG_TOP. lia. }
{ unfold IMG_TOP. lia. }
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return.
exact (conj G1 (conj G2 (conj G3 G4))). }
{ assumption. }
clear OBYc OBQc OBMc POST FRM1. rename PC into ST2. rename PC0 into FRM2. rename PC1 into LYS2. rename PC2 into YS2. rename PC3 into LMSP2. rename PC4 into MSP2. rename PC5 into IQ2.
ato 0xa4b58.
rewrite !sx32_small by (unfold int31; lia).
rewrite (unsigned_lit fsz) by lia.
replace (OUT + fsz ≪ 2) with Y by (rewrite Z.shiftl_mul_pow2 by lia; lia).
apply evt_done. do 14 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM2|]. split; [exact ST2|]. split; [exact FR|].
split; [unfold sbp_hdr; rewrite EFS, EFFS, ELPC; exact HD|]. split; [exact FST|]. split; [unfold sbp_ptrs; exact PT|].
split; [exact LE|]. split; [exact SEED|]. split; [exact IDC|]. split; [exact YS2|]. split; [rewrite LYS2; exact LYS1|]. split; [exact IQ2|].
split; [exact MSP2| rewrite LMSP2; exact LIQ].
Qed.

Lemma lost_w2 : forall (usp lo S id : Z) (x0 : word) (j8 : list byte)
(ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v s2v s3v s4v s5v s6v s7v s10v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -112) (lost_frame x0 j8 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
rw_cells asegs m (S + 152) [C4 (Z_to_bv 64 1)] -> aobj asegs m S 160 -> S mod 8 = 0 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo -> 0 <= id <= 7 ->
stk asegs m lo (usp + -112) -> lo <= usp + -112 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (v' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 v' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m1 (seg_rom asegs)
/\ munch [(S + 152, S + 156)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp /\ rw_cells asegs m1 (S + 152) [C4 (Z_to_bv 64 id)])
(MS (mkR (Z_to_bv 64 RA_lost_qmf) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (S + 152)) (Z_to_bv 64 1) v a1 a2 a3 a4 a5 a6 a7
s2v s3v s4v s5v s6v s7v (Z_to_bv 64 SHB) (Z_to_bv 64 id) s10v s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_lost_qmf)) fc None m (seg_rom asegs)).
Proof.
intros usp lo S id x0 j8 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v s2v s3v s4v s5v s6v s7v s10v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m.
intros FR IDC OBS S8 SSH SLO HID ST LO LOS SPH MI.
unfold RA_lost_qmf, lost_frame in *.
replace (ret_pc (Z_to_bv 64 0xb8890)) with (Z_to_bv 64 0xb8890) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(S + 152, S + 156)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S + 152, S + 156)]) by (cbn [offsh]; clear - SSH; unfold SH_LO, SH_HI in *; lia).
ato 0xb88a8.
ato 0xb88d8. release_frame FR ST usp. astep. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact IDC].
Qed.
