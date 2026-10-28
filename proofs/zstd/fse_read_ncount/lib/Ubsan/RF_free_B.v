(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_malloc_fast.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rfree_fp_meta0 : forall st st0 m lo sp q a, rmrep st m -> meta_slot st q -> s_regions st0 = s_regions st ->
conc st q <= a < conc st q + 40 -> rfree_fp st0 lo sp a.
Proof.
intros st st0 m lo sp q a MR (ar & arr & k & Har & Hk & Eq) ER Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0010>56483444207.3100000CS2Hk2Ha2Ca3Sa12HG1H".
eapply rfree_fp_region; [rewrite ER; exact Hra | exact NK | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rftriv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (C : Z -> Prop) (m : word -> option byte) (st' : mstate) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ rpres_except C m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.
#[using="Type"] Lemma rfree_triv : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (g : aptr) (idx : Z),
let mr := get_meta_rec st g in
let st' := upd_meta g (m_set_freed (m_freed mr + bit idx)) st in
rmrep st m -> mem_inv usegs m -> meta_slot st g ->
s_regions st = s_regions st0 -> s_areas st = s_areas st0 ->
0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
m_freed mr <> 0 -> Z.lor (m_freed mr) (m_avail mr) + bit idx <> mask_upto (m_last_idx mr) ->
rw_cells usegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk usegs m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
evt usegs (rftriv_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (rfree_fp st0 lo (bv_unsigned sp)) m st')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0x4f3f8) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x153fc) fc None m (seg_rom usegs)).
Proof.
intros until idx. intros mr st' MR MI MSL ER EA HF HA HL HI TF TA Hfz Hall FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
pose proof (wmono_refl usegs m) as WM.
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
set (gw := wz (conc st g)) in *. Local Ltac2 Set LiaHints.tbl := fun () => "00I0>11805467289.911748580572.80 1800609155.89 24638473347.902499476299.82 25071629079.9127905021218.7934215470240.6735021863776.8236026199562.7940599821652.8040600329431.8043143329194.8143143329325.8243988483203.8847432413043.914814699815.91 49705053714.9151711223320.7854243526019.8857020422711.8057177349585.8262241974760.9164997134979.908832910886.80 00000700;00<00=00A00T00Z00i00m01401;01B01F01M01N01a01e01i01j01k01l02502H02I02RS2HG2HBS2HxSSS2HLS2LO4LOLE3GB12HG2HBS4LOLES3GB03GB15ATOPRS2HIS2HF2HAS2HL2HIS2HL2HIS2HFS2HF2HASS2LO4LOLE3GB12HG2HBS2HBS2HBSSSS2LO4LOLES3GB03GB23GB42HG2HBSS4LOLE2Hx".
assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
clearbody gw.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
unfold RNEED_LOCKS in *. atop_facts.
step. step. rewrite !sx32_wz_sxv by lia.
step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.
step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.land_comm _ (sxv (2 ^ idx))).
rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).
step. if_true.
st1.
step. if_cases K2; zify_cond K2.
{ exfalso. apply Hfz. apply (proj1 (sxv_zero (m_freed mr) ltac:(lia))). first [exact K2 | rewrite wz_unsigned in K2 by assumption; exact K2]. }
clear K2.
step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
step. if_cases K3; zify_cond K3.
{ exfalso. apply Hall. unfold bit, mask_upto. apply (proj1 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
rewrite !wz_unsigned in K3 by apply sxv_range. exact K3. }
clear K3 RSUM.
step. rewrite (wz_unsigned (sxv (2 ^ idx))), (wz_unsigned (sxv (m_freed mr))) by assumption.
rewrite (Z.add_comm (sxv (m_freed mr)) (sxv (2 ^ idx))). rewrite addw_word.
step. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
clear K4 RL.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR' : rmrep st' mX) end.
{ unfold st'. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
rewrite HG in MM.
eapply rw_cells_congr; [ | | | exact MM].
- unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
unfold bit. rewrite (free_store_val (m_freed mr) idx) by (assumption || lia). reflexivity.
- reflexivity.
- cbn. tauto. }
clear MUg MM.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z mX) as MUs;
pose proof (wmono_refl usegs mX) as WMs end.
step. step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
clear MR' MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply rfree_fp_stack. lia.
- intros x Hx. eapply (rfree_fp_meta0 st st0 m lo (bv_unsigned sp) g); [exact MR | exact MSL | symmetry; exact ER | lia]. }
finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rfree_tocall : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (g : aptr) (idx : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv usegs m -> meta_slot st g ->
0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
(m_freed mr = 0 \/ Z.lor (m_freed mr) (m_avail mr) + bit idx = mask_upto (m_last_idx mr)) ->
evt usegs (fun ms' => exists x2 x3 x4 x5 x6 x7,
ms' = MS (mkR (Z_to_bv 64 0x1546c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(Z_to_bv 64 (conc st g)) (Z_to_bv 64 idx) x2 x3 x4 x5 x6 x7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x155d4) fc None m (seg_rom usegs))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0x4f3f8) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x153fc) fc None m (seg_rom usegs)).
Proof.
intros until idx. intros mr MR MI MSL HF HA HL HI TF TA HNT.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
set (gw := wz (conc st g)) in *. Local Ltac2 Set LiaHints.tbl := fun () => "0070>2499476299.69 34215470240.5335021863776.6936026199562.6540600329431.6643143329325.6957020422711.6600000400C00G00N00U00\00]S2HLS3GB03GB15ATOPRS2HIS2HF2HAS2HL2HIS2HF2HAS".
assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
replace (Z_to_bv 64 (conc st g)) with gw by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
clearbody gw.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
unfold RNEED_LOCKS in *. atop_facts.
step. step. rewrite !sx32_wz_sxv by lia.
step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.
step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.land_comm _ (sxv (2 ^ idx))).
rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).
step. if_true. st1.
step. if_cases K2; zify_cond K2.
-
st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
st1. st1.
apply evt_done. do 6 eexists. reflexivity.
-
step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
step. if_cases K3; zify_cond K3.
+ st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
st1. st1.
apply evt_done. do 6 eexists. reflexivity.
+ exfalso. destruct HNT as [Hz|Hall].
* apply K2. rewrite ?wz_unsigned by apply sxv_range. rewrite Hz. reflexivity.
* apply K3. rewrite ?wz_unsigned by apply sxv_range.
apply (proj2 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
unfold bit, mask_upto in Hall. exact Hall.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
