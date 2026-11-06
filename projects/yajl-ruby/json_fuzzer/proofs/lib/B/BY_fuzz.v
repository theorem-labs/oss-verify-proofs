(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlFactsParse.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib RY_yalloc RY_fuzz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BYajlAlign B_iface BI_shadow BYajlRep BYajl_iface BY_rz BY_hand BY_client BY_fuzz1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma nbig_app : forall l1 l2, nbig (l1 ++ l2) = nbig l1 + nbig l2.
Proof. aceil. intros. unfold nbig. rewrite filter_app, length_app. lia. Qed.
Lemma nbig_le_len : forall l, nbig l <= Z.of_nat (length l).
Proof. aceil. intros l. unfold nbig. induction l as [|b l IH]; cbn; [lia|]. destruct (64512 <? ab_size b); cbn; lia. Qed.

Section W.
Variable Y : ay_params.

Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis AFLSEP : AHK_y_aflsep_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis RREFL : ayR_refl_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis YFREE : yacct_free_stmt Y.
Hypothesis YACNEW : yacct_new_stmt Y.
Hypothesis ASM1 : astack_malloc_stmt Y 1 AY_STACK_MALLOC_1.
Hypothesis FREL : AHK_y_fake_release_stmt Y.
Hypothesis AFLC : AHK_y_flag_cell_stmt Y.
Hypothesis YAL : ayalloc_stmt Y.
Hypothesis YPA : ayparse_stmt Y.
Hypothesis YFR : ayfree_stmt Y.
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells bsegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
Hypothesis URA_al : In 0x81e88 URA.      (* [comment removed for export] *)
Hypothesis URA_pa : In 0x81e98 URA.      (* [comment removed for export] *)
Hypothesis URA_fr : In 0x81ea0 URA.      (* [comment removed for export] *)

Ltac rchain := first [eassumption | eapply RRT; [eassumption| rchain]].

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.
Hypothesis STATY : AHK_y_statics_stmt Y.

(* [comment removed for export] *)
Section Tail.
Variables (LF : list fblock) (REST : list ablock) (T : Z) (txt : list Z) (OT OTn lo RR : Z) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (mo : Model) (s : y_APS Y).
Variables (SQ ff : Z).
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : y_APS Y) (LK : list ablock),
     ayfuzz_rpost Y sp m mo s LF REST T txt OT OTn lo RR a0' fc' m' mo' s' LK ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K.
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - (112 + (16 + (368 + (272 + (128 + 8192))))).
Hypothesis SPLT : bv_unsigned sp < 2^47.
Hypothesis SQR : bv_unsigned sp - 112 <= SQ <= bv_unsigned sp - 96.
Hypothesis FFsh : amem ff 128.
Hypothesis FFce : ff + 128 <= alloc_ceiling.
Hypothesis FFal : ff mod 128 = 0.
Hypothesis PFR : amem (y_aflag Y 1 ff) 1 /\ y_aflag Y 1 ff + 1 <= alloc_ceiling.
Hypothesis FRESH : forall g, In g LF -> In g ((1, ff) :: LF) /\ snd g <> snd (1, ff).
Hypothesis TB : (exists bt, In bt REST /\ ab_addr bt <= T /\ T + zlength txt <= ab_addr bt + ab_size bt) \/ zlength txt = 0.

(* [comment removed for export] *)
Lemma fuzz_tail : forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (LK : list ablock) (fcs : list cell) (w0 : word) (shf : list byte),
  y_AHK Y s1' (LK ++ REST) ((1, ff) :: LF) m1 mo1 -> LK = [] -> aystatics m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo SQ -> stk bsegs m1 (SQ + 16) (bv_unsigned sp + -80) -> frm0 fc1 ->
  rw_cells bsegs m1 SQ fcs -> cells_size fcs = 16%nat ->
  rw_cells bsegs m1 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m1 ff [C8 w0] -> rw_cells bsegs m1 (ff + 120) [C8 (Z_to_bv 64 (y_aflag Y 1 ff))] -> rw_cells bsegs m1 (ff / 8 + 2147450880) [CB 16 shf] ->
  atext_at m1 T txt ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s -> 0 + RR <= y_acredit Y s1' ->
  yleaf (yLLVMFuzzerTestOneInput txt (zlength txt)) 0 ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 ff) s3v s4v s5v (Z_to_bv 64 (ff / 8 + 2147450880)) (Z_to_bv 64 ff) (Z_to_bv 64 (-8)) s9 s10 s11 t3 t4 t5 t6)
                          F1 (Z_to_bv 64 AFZ_J) fc1 None m1 (seg_rom bsegs)) mo1) K.
Proof. aceil.
  intros until shf. intros AHK1 LKLEN YS1 MI1 ST1 GAP1 FRM1 FRQ FRQsz SV1 FF8 FFP SHC TXT1 PRES1 R1 SO1 CRED1 LEAF.
  unfold amem in FFsh, PFR.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  assert (E8F : ff = 8 * (ff / 8)) by (clear -CEILB FFal; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  arz_seg KIPY AHK1.
  pose proof (aypol_fframe Y _ ((1, ff) :: LF) _ _ LINK (1, ff) ff (ff + 128) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; rewrite ff_bytes_1; lia) ltac:(lia) ltac:(cbn; rewrite ff_bytes_1; lia)) as PFF.
  pose proof (aypol_ffshadow Y _ ((1, ff) :: LF) _ _ LINK (1, ff) (ff / 8 + 2147450880) (ff / 8 + 2147450880 + 16) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia)) as PFFS.
  eapply evtA_cut.
  { eapply afz5_seg; [ exact MI1 | exact SHC | exact FF8 | exact FFP | exact FFsh | lia | exact FFal | lia | exact PFF | exact PFFS ]. }
  cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & SH2 & FFM2 & FFP2).
  apply evtA_done. intros mo2 Hag2 HLI2 Hh2. destruct (BACK mo2 Hag2 HLI2) as [AHKb R2].
  assert (AHK2 : y_AHK Y s1' (LK ++ REST) ((1, ff) :: LF) m2 mo2).
  { eapply FRAMEY; [exact AHKb| exact MU2| exact WM2|].
    constructor; [right; right; right; left; exists (1, ff); split; [left; reflexivity| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia]|].
    constructor; [right; right; left; exists (1, ff); split; [left; reflexivity| cbn [fst snd]; rewrite ff_bytes_1; lia]| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS1 MU2 WM2 ltac:(constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; lia| constructor]])) as YS2.
  assert (PRES2 : ay_pres REST LF (bv_unsigned sp) [] m m2).
  { eapply ay_pres_trans; [exact PRES1|]. eapply ay_pres_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc _.
    apply outside_cons; [| apply outside_cons; [| exact I]].
    - eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK1| left; reflexivity| exact FRESH| intros b0 Hb0; apply in_or_app; right; exact Hb0| right; cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia| lia| aceil; lia| exact Hc].
    - eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK1| left; reflexivity| exact FRESH| intros b0 Hb0; apply in_or_app; right; exact Hb0| left; cbn [fst snd]; rewrite ff_bytes_1; lia| lia| aceil; lia| exact Hc]. }
  eapply (rw_cells_transport bsegs) in SV1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport bsegs) in FRQ; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; rewrite FRQsz; lia].
  eapply (stk_transport_disjoint bsegs) in ST1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; lia].
  eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; lia].
  assert (TXT2 : atext_at m2 T txt).
  { eapply aypres_text; [| exact TXT1| exact TB]. eapply ay_pres_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc _.
    apply outside_cons; [| apply outside_cons; [| exact I]].
    - eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK1| left; reflexivity| exact FRESH| intros b0 Hb0; apply in_or_app; right; exact Hb0| right; cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia| lia| aceil; lia| exact Hc].
    - eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK1| left; reflexivity| exact FRESH| intros b0 Hb0; apply in_or_app; right; exact Hb0| left; cbn [fst snd]; rewrite ff_bytes_1; lia| lia| aceil; lia| exact Hc]. }
  clear LINK BACK PFF PFFS MU2 WM2 MI1 YS1 PRES1 AHK1 TXT1.
  (* [comment removed for export] *)
  destruct (AFLC _ _ _ _ _ (1, ff) AHK2 (or_introl eq_refl)) as [[fl FLG] _]. cbn [fst snd] in FLG.
  (* [comment removed for export] *)
  arz_seg KIPY AHK2.
  assert (PPF : acc_ok (m_vm_lazy mo2) (y_aS Y s1') (Z_to_bv 64 (y_aflag Y 1 ff), 1%nat)).
  { apply LINK. unfold ay_acc. cbn [fst snd]. rewrite unsigned_lit by lia. do 6 right. left. exists (1, ff). split; [left; reflexivity|]. cbn [fst snd]. split; [reflexivity| reflexivity]. }
  pose proof (aypol_stack Y _ ((1, ff) :: LF) _ _ LINK (bv_unsigned sp - 96) (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  eapply evtA_cut.
  { eapply afz6_seg; [ exact MI2 | exact FLG | exact SV1 | exact (proj1 PFR) | exact (proj2 PFR) | lia | lia | exact PPF | exact PSTK ]. }
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FL3 & SV3).
  apply evtA_done. intros mo3 Hag3 HLI3 Hh3. destruct (BACK mo3 Hag3 HLI3) as [AHKc R3].
  pose proof (FREL _ _ _ _ _ _ 1 ff AHKc (or_introl eq_refl) MU3 WM3 FL3) as AHK3.
  cbn [ff_remove fst snd] in AHK3. rewrite !Z.eqb_refl in AHK3. cbn [andb] in AHK3.
  pose proof (aystatics_munch _ _ _ YS2 MU3 WM3 ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS3.
  assert (PRES3 : ay_pres REST LF (bv_unsigned sp) [] m m3).
  { eapply ay_pres_trans; [exact PRES2|]. eapply ay_pres_of_munch; [exact MU3| exact WM3|]. intros a Ha Hc _.
    eapply (ay_client_outside_flag Y LAYY AFLSEP _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK2| left; reflexivity| exact FRESH| intros b0 Hb0; apply in_or_app; right; exact Hb0| aceil; lia| exact Hc]. }
  assert (TXT3 : atext_at m3 T txt).
  { eapply aypres_text; [| exact TXT2| exact TB]. eapply ay_pres_of_munch; [exact MU3| exact WM3|]. intros a Ha Hc _.
    eapply (ay_client_outside_flag Y LAYY AFLSEP _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK2| left; reflexivity| exact FRESH| intros b0 Hb0; apply in_or_app; right; exact Hb0| aceil; lia| exact Hc]. }
  eapply (rw_cells_transport bsegs) in FRQ; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; rewrite FRQsz; lia].
  eapply (stk_transport_disjoint bsegs) in ST1; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; lia].
  eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; lia].
  pose proof (stk_release bsegs _ _ _ _ ST1 FRQ ltac:(lia)) as ST2. rewrite FRQsz in ST2. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in ST2.
  pose proof (stk_merge bsegs _ _ _ _ ST2 GAP1 ltac:(lia)) as ST3'.
  pose proof (stk_release bsegs _ _ _ _ ST3' SV3 ltac:(lia)) as ST4. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ST4.
  replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) in ST4 by lia.
  eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m3 mo3 s1' LK). unfold ayfuzz_rpost.
  split; [exact SO1|].
  split; [eapply RRT; [exact R1|]; eapply RRT; [exact R2| exact R3]|].
  split; [exact CRED1|].
  split; [split; [exact MI3|]; split; [exact ST4|]; split; [exact FRM1|]; split; [exact I| exact PRES3]|].
  split; [reflexivity|]. split; [exact TXT3|]. split; [exact LEAF|]. split; [exact LKLEN|].
  apply AYST_split. split; [exact AHK3| exact YS3].
Qed.
End Tail.

(* [comment removed for export] *)
Theorem ayfuzz_proof : ayfuzz_stmt Y.
Proof. aceil.
  unfold ayfuzz_stmt. intros LF REST T txt OT OTn lo RR K. intros until s.
  intros BAF K0 AY TXT TL TB TS FC1 FC0 GP FP EA0 EA1 CRED RR0 NBIG UA CONT. subst a0 a1. red in BAF.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM).
  apply AYST_split in AY. destruct AY as [AHK0 YS]. pose proof YS as (YCB & YBAE & YNOOP & STA). ay_statics_open STA.
  unfold AY_FUZZ_STACK, AY_PARSE_STACK, AY_DO_PARSE_STACK, AY_DECODE_STACK, AY_BUF_APPEND_STACK, AMALLOC_STACK, wz in *.
  aceil.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  destruct NONNEG as (NA0 & NB0 & NH0 & NN0). pose proof (zlength_nonneg txt) as TL0. pose proof (NN0 (zlength txt)) as NNL.
  pose proof YACNEW as YAN. unfold yacct_new_stmt in YAN. specialize (YAN (zlength txt) TL0).
  pose proof TXT as (TXB & TXF & T0 & TLIM).
  assert (TB' : (exists bt, In bt REST /\ ab_addr bt <= T /\ T + zlength txt <= ab_addr bt + ab_size bt) \/ zlength txt = 0) by (destruct TB as [X|[X _]]; [left; exact X| right; exact X]).
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG0 & _ & ND0).
  assert (TH : T + zlength txt <= 2^47).
  { destruct TB as [(bt & Hbt & B1 & B2)|[Z0 ->]]; [| unfold AY_EMPTY; lia]. pose proof (RNG0 _ Hbt) as X. unfold ablock_range in X; aceil. lia. }
  (* [comment removed for export] *)
  arz_seg KIPY AHK0.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ LF _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  eapply evtA_cut.
  { eapply afz1_seg; [ exact ST | exact MI | lia | lia | lia | exact SP16 | exact G1 | exact G2 | exact G3 | exact G4 | lia | lia | exact PSTK | exact PIMG ]. }
  cbv beta. intros ms1 (SQ & jq & m1 & -> & SQ32 & SQR & MU & WM & MI1 & ST1 & FR1 & SV1 & GAP1).
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHKb R1].
  assert (AHK1 : y_AHK Y s REST LF m1 mo1).
  { eapply FRAMEY; [exact AHKb| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; aceil; lia| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS1.
  assert (PRES1 : ay_pres REST LF (bv_unsigned sp) [] m m1).
  { eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _.
    eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK0| intros b0 Hb0; exact Hb0| aceil; lia| lia| exact Hc]. }
  assert (AGREE1 : forall a, bv_unsigned sp <= a < 2^47 -> m1 (wa a) = m (wa a)).
  { intros a Ha. destruct (PRES1 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  pose proof (aypres_text _ _ _ _ _ _ _ PRES1 TXT TB') as TXT1.
  clear LINK BACK PSTK PIMG. unfold AFZ_RET1, AY_STACK_MALLOC_1.
  (* [comment removed for export] *)
  eapply ASM1;
    [ exact K0 | exact AHK1 | rewrite FC1; lia
    | rewrite unsigned_lit by lia; exact ST1
    | aceil; lia
    | rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia
    | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; clear -CEILB SQ32; Z.div_mod_to_equations; lia
    | exact MI1 | exact TP | exact FRM
    | exact CRED
    | ].
  cbv beta. intros t0a t1a t2a a1a a2a a3a a4a a5a a6a a7a t3a t4a t5a t6a F2 fc2 m2 mo2 sa2 ff junk ST2 PRES2 WM2 MI2 FRM2 SO2 FF0 FFal FFsh FFce FFfr FFC FFS FLG AHK2 R2 CRED2.
  rewrite unsigned_lit in ST2, PRES2 by lia.
  rewrite ff_bytes_1 in FFal, FFsh, FFce, FFC, FFfr. unfold amem in FFsh. aceil.
  change (Z.to_nat (128 - 8)) with 120%nat in FFC. unfold oshw_lo, A_SB in FFS. rewrite shl8_1 in FFS. change (Z.to_nat 16) with 16%nat in FFS.
  assert (E8F : ff = 8 * (ff / 8)) by (clear -CEILB FFal; Z.div_mod_to_equations; lia).
  clear FLG.
  destruct (LAYY _ _ _ _ _ AHK2) as (LAYF2 & _ & _).
  assert (FRESH : forall g, In g LF -> In g ((1, ff) :: LF) /\ snd g <> snd (1, ff)).
  { intros g Hg. split; [right; exact Hg|]. cbn [snd]. destruct (LAYF2 g (or_intror Hg)) as (_ & _ & _ & L4 & _). pose proof (FFfr g Hg) as D.
    assert (EG : fst g = 0 \/ fst g = 1) by lia. destruct EG as [EG|EG]; rewrite EG in D; unfold ff_bytes in D;
      [change (Z.shiftl 64 0) with 64 in D| change (Z.shiftl 64 1) with 128 in D]; lia. }
  pose proof (LAYF2 _ (or_introl eq_refl)) as (_ & _ & _ & _ & PFR). cbn [fst snd] in PFR. unfold amem in PFR. aceil.
  clear LAYF2.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 FR1 ltac:(lia)) as FR2. pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 SV1 ltac:(lia)) as SV2. clear FR1 SV1.
  assert (GAP2 : stk bsegs m2 (SQ + 16) (bv_unsigned sp + -80)) by (eapply stk_agree; [eapply ay_pres_agree; exact PRES2| exact GAP1| intros a Ha; split; [left; lia| intros F0; exact F0]]). clear GAP1.
  pose proof (aystatics_pres _ _ _ _ _ YS1 PRES2) as (YCB2 & YBAE2 & YNOOP2). pose proof (STATY _ _ _ _ _ AHK2) as STA2.
  assert (YS2 : aystatics m2) by (exact (conj YCB2 (conj YBAE2 (conj YNOOP2 STA2)))). clear YCB2 YBAE2 YNOOP2.
  assert (PRES2w : ay_pres REST LF (bv_unsigned sp) [] m m2).
  { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES2| lia| intros b0 Hb0; exact Hb0| auto| auto]. }
  assert (AGREE2 : forall a, bv_unsigned sp <= a < 2^47 -> m2 (wa a) = m (wa a)).
  { intros a Ha. rewrite <- (AGREE1 a Ha). destruct (PRES2 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  pose proof (aypres_text _ _ _ _ _ _ _ PRES2 TXT1 TB') as TXT2.
  clear ST1 MI1 PRES2 AHK1 YS1 AGREE1 PRES1 AHK0 ST MI TXT1.
  (* [comment removed for export] *)
  arz_seg KIPY AHK2. ret_pc_lit. unfold wz.
  pose proof (aypol_stack Y _ ((1, ff) :: LF) _ _ LINK SQ (SQ + 16) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_fframe Y _ ((1, ff) :: LF) _ _ LINK (1, ff) ff (ff + 128) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; rewrite ff_bytes_1; lia) ltac:(lia) ltac:(cbn; rewrite ff_bytes_1; lia)) as PFF.
  pose proof (aypol_ffshadow Y _ ((1, ff) :: LF) _ _ LINK (1, ff) (2147450880 + ff / 8) (2147450880 + ff / 8 + 16) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia)) as PFFS.
  eapply evtA_cut.
  { eapply afz2_seg; [ exact MI2 | lia | lia | exact FR2 | exact FFC | exact FFS | exact FFsh | lia | exact FFal | exact PSTK | exact PFF | exact PFFS ]. }
  cbv beta. intros ms3 (a4b & a5b & j1 & j2 & j3 & m3 & -> & MU3 & WM3 & MI3 & FR3 & FFH3 & FSH3 & LJ1 & LJ2 & LJ3).
  apply evtA_done. intros mo3 Hag3 HLI3 Hh3. destruct (BACK mo3 Hag3 HLI3) as [AHKb R3].
  assert (AHK3 : y_AHK Y sa2 REST ((1, ff) :: LF) m3 mo3).
  { eapply FRAMEY; [exact AHKb| exact MU3| exact WM3|].
    constructor; [left; cbn [fst snd]; aceil; lia|].
    constructor; [right; right; left; exists (1, ff); split; [left; reflexivity| cbn [fst snd]; rewrite ff_bytes_1; lia]|].
    constructor; [right; right; right; left; exists (1, ff); split; [left; reflexivity| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia]| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS2 MU3 WM3 ltac:(constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; lia| constructor]]])) as YS3.
  assert (PRES3s : ay_pres REST LF (bv_unsigned sp) [] m2 m3).
  { eapply ay_pres_of_munch; [exact MU3| exact WM3|]. intros a Ha Hc _.
    apply outside_cons; [| apply outside_cons; [| apply outside_cons; [| exact I]]].
    - eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK2| intros b0 Hb0; exact Hb0| aceil; lia| lia| exact (ay_client_addr_mono _ _ ((1, ff) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)].
    - eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK2| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| left; cbn [fst snd]; rewrite ff_bytes_1; lia| lia| aceil; lia| exact Hc].
    - eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK2| left; reflexivity| exact FRESH| intros b0 Hb0; exact Hb0| right; cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia| lia| aceil; lia| exact Hc]. }
  pose proof (ay_pres_trans _ _ _ _ _ _ _ PRES2w PRES3s) as PRES3w.
  pose proof (aypres_text _ _ _ _ _ _ _ PRES3s TXT2) as TXT3'. specialize (TXT3' TB'). rename TXT3' into TXT3.
  assert (AGREE3 : forall a, bv_unsigned sp <= a < 2^47 -> m3 (wa a) = m (wa a)).
  { intros a Ha. destruct (PRES3w a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  eapply (rw_cells_transport bsegs) in SV2; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (stk_transport_disjoint bsegs) in GAP2; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; lia].
  eapply (stk_transport_disjoint bsegs) in ST2; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; lia].
  (* [comment removed for export] *)
  pose proof (proj1 (proj1 (ycells_app bsegs _ _ [_] [_; _; _; _; _; _; _; _]) FFH3)) as FF8.
  pose proof (sub_chunk m3 _ [_; _; _; _] [_] [_; _; _; _] FFH3) as CXC. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in CXC.
  eapply rw_cells_reshape with (cs' := [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in CXC; [| cbn; repeat split; exact I| cbn; repeat (first [reflexivity | apply f_equal2; [apply Z_to_bv8_mod; vm_compute; reflexivity|]])| reflexivity].
  pose proof (sub_chunk m3 _ [_; _; _; _; _; _] [_] [_; _] FFH3) as CFC. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in CFC.
  eapply rw_cells_reshape with (cs' := [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1)]) in CFC; [| cbn; repeat split; exact I| cbn; repeat (first [reflexivity | apply f_equal2; [apply Z_to_bv8_mod; vm_compute; reflexivity|]])| reflexivity].
  pose proof (sub_chunk m3 _ [_; _; _; _; _; _; _; _] [_] [] ltac:(rewrite app_nil_r; exact FFH3)) as FFP. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FFP.
  try replace (ff + 32 + 8 + 24 + 8 + 48) with (ff + 120) in FFP by lia. try replace (ff + 32 + 8 + 24) with (ff + 64) in CFC by lia.
  clear FFH3.
  pose proof (sub_chunk m3 _ [_; _; _; _] [_] [_; _; _; _; _; _; _; _] FSH3) as SX. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SX.
  pose proof (sub_chunk m3 _ [_; _; _; _; _; _; _; _] [_] [_; _; _; _] FSH3) as SC. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SC.
  eapply rw_cells_reshape with (cs' := [CB 1 [Z_to_bv 8 0]]) in SX; [| cbn; repeat split; reflexivity| reflexivity| reflexivity].
  eapply rw_cells_reshape with (cs' := [CB 1 [Z_to_bv 8 0]]) in SC; [| cbn; repeat split; reflexivity| reflexivity| reflexivity].
  apply u8arr_of_rw_cells in SX. apply u8arr_of_rw_cells in SC.
  assert (OSX3 : oshadow m3 (ff + 32) 8).
  { split; [clear -CEILB E8F; Z.div_mod_to_equations; lia|]. split; [lia|]. unfold A_SB.
    replace (2147450880 + (ff + 32) / 8) with (ff / 8 + 2147450880 + 4) by (clear -CEILB E8F; Z.div_mod_to_equations; lia). change (blk_shadow 8) with [Z_to_bv 8 0]. exact SX. }
  assert (OSC3 : oshadow m3 (ff + 64) 8).
  { split; [clear -CEILB E8F; Z.div_mod_to_equations; lia|]. split; [lia|]. unfold A_SB.
    replace (2147450880 + (ff + 64) / 8) with (ff / 8 + 2147450880 + 8) by (clear -CEILB E8F; Z.div_mod_to_equations; lia). change (blk_shadow 8) with [Z_to_bv 8 0]. exact SC. }
  clear SX SC.
  unfold F1b, F2b, F3b in FSH3.
  eapply rw_cells_reshape with (cs' := [CB 16 [Z_to_bv 8 241; Z_to_bv 8 241; Z_to_bv 8 241; Z_to_bv 8 241; Z_to_bv 8 0; Z_to_bv 8 242; Z_to_bv 8 242; Z_to_bv 8 242;
                                               Z_to_bv 8 0; Z_to_bv 8 243; Z_to_bv 8 243; Z_to_bv 8 243; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in FSH3;
    [| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity].
  rename FSH3 into SHC.
  pose proof (sub_chunk m3 _ [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] [] ltac:(rewrite app_nil_r; exact SV2)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned sp + -80 + 64) with (bv_unsigned sp - 16) in SV16 by lia.
  clear LINK BACK PSTK PFF PFFS MU3 WM3 YS2 PRES2w AGREE2 MI2 FR2 TXT2 PRES3s.
  unfold AFZ_RET2.
  (* [comment removed for export] *)
  eapply (YAL ((1, ff) :: LF) REST (ff + 64) (ff + 32) lo (zlength txt) (y_cost Y (zlength txt) + RR - y_phi_new Y (zlength txt)));
    [ red; rewrite ?unsigned_lit by lia; split; [clear -SQ32; Z.div_mod_to_equations; lia| clear -FFal; Z.div_mod_to_equations; lia]   (* [comment removed for export] *)
    | exact K0
    | apply AYST_split; split; [exact AHK3| exact YS3]
    | unfold wz; exact CFC
    | exact OSC3 | exact OSX3
    | exact TL0
    | unfold amem; clear -CEILB FFsh; lia
    | lia
    | aceil; lia
    | exists (1, ff); split; [left; reflexivity|]; cbn [fst snd]; split; [lia| reflexivity]
    | change (ff_live_class ((1, ff) :: LF) 1) with (S (ff_live_class LF 1)); rewrite FC1; lia
    | unfold ayframe_pre, AY_ALLOC_STACK, AY_LEX_ALLOC_STACK, AY_BUF_ALLOC_STACK, AMALLOC_STACK; aceil; rewrite unsigned_lit by lia;
      split; [exact ST2|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia|];
      split; [exact MI3|]; split; [exact TP| exact FRM2]
    | reflexivity | reflexivity | reflexivity | reflexivity
    | clear -CEILB CRED2 YAN; lia
    | clear -CEILB YAN RR0; lia
    | exact NBIG
    | rewrite unsigned_lit by lia; eapply USTEP; [rewrite unsigned_lit by lia; exact URA_al| lia| exact SV16| eapply UFRAME; [exact AGREE3| exact UA]]
    | ].
  cbv beta. intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c F4 fc4 m4 mo4 sa4 h mh (SO4 & R4 & CRED4 & (MI4 & ST4 & FRM4 & _ & PRES4) & CFC4 & RESA).
  rewrite unsigned_lit in ST4, PRES4 by lia.
  replace (ret_pc (Z_to_bv 64 0x81e88)) with (Z_to_bv 64 0x81e88) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES4 FR3 ltac:(lia)) as FR4. clear FR3.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES4 SV2 ltac:(lia)) as SV4. clear SV2 SV16.
  assert (GAP4 : stk bsegs m4 (SQ + 16) (bv_unsigned sp + -80)).
  { eapply stk_agree; [eapply ay_pres_agree; exact PRES4| exact GAP2| intros a Ha; split; [left; lia| intros F0; exact F0]]. }
  clear GAP2.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES4 FF8 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FF8_4. clear FF8.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES4 FFP (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FFP4. clear FFP.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES4 CXC (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as CXC4. clear CXC.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES4 SHC (or_introl eq_refl) ltac:(right; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold oshw_lo, A_SB; rewrite shl8_1; lia)) as SHC4. clear SHC.
  assert (OSX4 : oshadow m4 (ff + 32) 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES4| exact OSX3|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, ff). split; [left; reflexivity|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha E8F. Z.div_mod_to_equations. lia. }
  assert (PRES4w : ay_pres REST LF (bv_unsigned sp) [] m m4).
  { eapply ay_pres_trans; [exact PRES3w|]. eapply (ay_pres_weaken Y); [exact PRES4| lia| intros b0 Hb0; exact Hb0| intros f Hf; right; exact Hf| auto]. }
  assert (AGREE4 : forall a, bv_unsigned sp <= a < 2^47 -> m4 (wa a) = m (wa a)).
  { intros a Ha. destruct (PRES4w a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  pose proof (aypres_text _ _ _ _ _ _ _ PRES4 TXT3 TB') as TXT4.
  clear PRES3w AGREE3 ST2 MI3 PRES4 OSX3 OSC3.
  (* [comment removed for export] *)
  destruct RESA as (-> & HNZ & MCX & HL & HR4 & OSH & OSL & OSLB & OSDB & OSS & HIGH & AY4). unfold wz.
  pose proof (ypost_yleaf _ _ _ (yajl_alloc_post (zlength txt) TL0) HL) as AF. cbv beta iota in AF. destruct AF as (HINV & HBC & HST & HSS & HDB & HLB & HLE & HPE).
  apply AYST_split in AY4. destruct AY4 as [AHK4 YS4].
  destruct (BLKY _ _ _ _ _ AHK4) as (RNG4 & _ & _).
  pose proof (RNG4 _ ltac:(apply in_or_app; left; left; reflexivity)) as HRG. cbn [ab_addr ab_size blk_addr blk_size fst snd] in HRG. unfold ablock_range in HRG; aceil.
  (* [comment removed for export] *)
  arz_seg KIPY AHK4.
  eapply evtA_cut. { eapply afz3_seg; [exact MI4 | unfold SIZEOF_HANDLE in HRG; lia | lia]. }
  cbv beta. intros ms5 ->.
  apply evtA_done. intros mo5 Hag5 HLI5 Hh5. destruct (BACK mo5 Hag5 HLI5) as [AHK5 R5]. clear LINK BACK.
  pose proof (sub_chunk m4 _ [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] [] ltac:(rewrite app_nil_r; exact SV4)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned sp + -80 + 64) with (bv_unsigned sp - 16) in SV16 by lia.
  (* [comment removed for export] *)
  assert (TSHX : exists OT' OTn', zlength txt = 0 \/ (oshadow m4 OT' OTn' /\ OT' <= T /\ T + zlength txt <= OT' + OTn' /\ amem OT' OTn'
                       /\ OT' + OTn' <= alloc_ceiling /\ (exists bt, In bt REST /\ ab_addr bt <= OT' /\ OT' + OTn' <= ab_addr bt + ab_size bt))).
  { destruct (Z.eq_dec (zlength txt) 0) as [Z0|NZ]; [exists 0, 0; left; exact Z0|].
    destruct TB' as [(bt & Hbt & B1 & B2)| Z0]; [| exfalso; clear -CEILB Z0 NZ; lia].
    pose proof (RNG4 bt ltac:(apply in_or_app; right; exact Hbt)) as RT. unfold ablock_range, ACONSTS in RT. cbn [c_img_hi] in RT.
    destruct (BSHY _ _ _ _ _ bt AHK5 ltac:(apply in_or_app; right; exact Hbt) ltac:(clear -CEILB B1 B2 NZ TL0; lia)) as [OSB OHI].
    exists (ab_addr bt), (ab_size bt). right.
    split; [exact OSB|]. split; [exact B1|]. split; [exact B2|]. split; [exact OHI|]. split; [clear -CEILB RT; lia|].
    exists bt. split; [exact Hbt| clear -CEILB B1; lia]. }
  destruct TSHX as (OT' & OTn' & TSH').
  unfold AFZ_RET3.
  (* [comment removed for export] *)
  eapply (YPA ((1, ff) :: LF) REST h mh (mkCtx 0 0) T txt OT' OTn' lo (y_cost Y (zlength txt) + RR - y_phi_new Y (zlength txt)) K);
    [ red; rewrite ?unsigned_lit by lia; split; [clear -SQ32; Z.div_mod_to_equations; lia| rewrite MCX; clear -FFal; Z.div_mod_to_equations; lia]   (* [comment removed for export] *)
    | exact K0
    | apply AYST_split; split; [exact AHK5| exact YS4]
    | exact HR4
    | rewrite MCX; split; [unfold ctx_cells; cbn [cx_arrayLevel cx_objectLevel]; unfold wz; exact CXC4| cbn; lia]
    | exact TXT4 | exact TH | exact TL | exact TB' | exact TSH' | exact HINV
    | exact OSH | exact OSL | exact OSLB | exact OSDB | exact OSS
    | rewrite MCX; exact OSX4
    | rewrite MCX; exists (1, ff); split; [left; reflexivity|]; cbn [fst snd]; split; [lia| reflexivity]
    | change (ff_live_class ((1, ff) :: LF) 1) with (S (ff_live_class LF 1)); rewrite FC1; lia
    | change (ff_live_class ((1, ff) :: LF) 0) with (ff_live_class LF 0); rewrite FC0; lia
    | unfold ayframe_pre, AY_PARSE_STACK, AY_DO_PARSE_STACK, AY_DECODE_STACK, AY_BUF_APPEND_STACK, AMALLOC_STACK; aceil; rewrite unsigned_lit by lia;
      split; [exact ST4|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia|];
      split; [exact MI4|]; split; [exact TP| exact FRM4]
    | reflexivity | reflexivity | reflexivity
    | replace (h_set_off h 0) with h by (clear -CEILB HBC; destruct h; cbn in HBC |- *; subst; reflexivity); exact CRED4
    | clear -CEILB YAN RR0; lia
    | exact NBIG
    | rewrite unsigned_lit by lia; eapply USTEP; [rewrite unsigned_lit by lia; exact URA_pa| lia| exact SV16| eapply UFRAME; [exact AGREE4| exact UA]]
    | ].
  cbv beta. intros t0d t1d t2d a0d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d F6 fc6 m6 mo6 sa6 st h' cx' mh' LK (SO6 & R6 & CRED6 & (MI6 & ST6 & FRM6 & _ & PRES6) & HPL & -> & HR6 & MHS & CTX6 & TXT6 & OLD6 & ODD6 & OSS6 & LKZ6 & AY6 & NBLK).
  rewrite unsigned_lit in ST6, PRES6 by lia. rewrite MCX in PRES6.
  replace (ret_pc (Z_to_bv 64 0x81e98)) with (Z_to_bv 64 0x81e98) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof MHS as (MADDR & MLEX & MLB & MDB & MCTX).
  apply AYST_split in AY6. destruct AY6 as [AHK6 YS6].
  (* [comment removed for export] *)
  assert (NCX : forall a, bv_unsigned sp <= a \/ (ff <= a < ff + 8) \/ (ff + 120 <= a < ff + 128) \/ (ff / 8 + 2147450880 <= a < ff / 8 + 2147450880 + 16) \/ (SQ <= a < SQ + 16) \/ (SQ + 16 <= a < bv_unsigned sp) -> ~ yin_ivs [(ff + 32, ff + 32 + 8)] a).
  { intros a Ha. cbn. clear -CEILB Ha SQR FFsh FFce E8F LO CEIL. intros [X|[]]. lia. }
  pose proof (aypres_rw_cells _ _ _ _ _ _ _ _ PRES6 FR4 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| apply NCX; lia])) as FR6.
  pose proof (aypres_rw_cells _ _ _ _ _ _ _ _ PRES6 SV4 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| apply NCX; lia])) as SV6.
  assert (GAP6 : stk bsegs m6 (SQ + 16) (bv_unsigned sp + -80)).
  { eapply stk_agree; [eapply ay_pres_agree; exact PRES6| exact GAP4| intros a Ha; split; [left; lia| apply NCX; lia]]. }
  pose proof (aypres_rw_cells _ _ _ _ _ _ _ _ PRES6 FF8_4 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; exists (1, ff); split; [left; reflexivity| left; cbn [fst snd]; rewrite ff_bytes_1; lia]| apply NCX; lia])) as FF8_6.
  pose proof (aypres_rw_cells _ _ _ _ _ _ _ _ PRES6 FFP4 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; exists (1, ff); split; [left; reflexivity| left; cbn [fst snd]; rewrite ff_bytes_1; lia]| apply NCX; lia])) as FFP6.
  pose proof (aypres_rw_cells _ _ _ _ _ _ _ _ PRES6 SHC4 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; exists (1, ff); split; [left; reflexivity| right; cbn [fst snd]; unfold A_SB; rewrite shl8_1; lia]| apply NCX; lia])) as SHC6.
  assert (PRES6w : ay_pres REST LF (bv_unsigned sp) [] m m6).
  { eapply ay_pres_trans; [exact PRES4w|]. intros a Ha Hc _. apply PRES6; [exact Ha| |].
    - destruct Hc as [Hc|Hc]; [left; lia| right]. destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc| right; left| right; right; exact Hc].
      destruct Hc as (f & Hf & Hr). exists f. split; [right; exact Hf| exact Hr].
    - pose proof (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff) (ff + 32) (ff + 32 + 8) a AHK3 (or_introl eq_refl) FRESH
                    ltac:(intros b0 Hb0; exact Hb0) ltac:(left; cbn [fst snd]; rewrite ff_bytes_1; lia) ltac:(lia) ltac:(aceil; lia) Hc) as OUT.
      cbn in OUT. cbn. clear -CEILB OUT. intros [X|[]]. lia. }
  assert (AGREE6 : forall a, bv_unsigned sp <= a < 2^47 -> m6 (wa a) = m (wa a)).
  { intros a Ha. destruct (PRES6w a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  (* [comment removed for export] *)
  assert (INB : forall b, In b (abl (yblocks mh' h')) -> In b (abl (yblocks mh' h') ++ LK ++ REST)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK6 (INB _ (yb_in_hand mh' h')) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH6. cbn [ab_addr ab_size] in OSH6.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK6 (INB _ (yb_in_lexer mh' h')) ltac:(cbn; unfold SIZEOF_LEXER; lia))) as OSL6. cbn [ab_addr ab_size] in OSL6.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK6 (INB _ (yb_in_lexbuf mh' h')) ltac:(cbn; unfold SIZEOF_BUF; lia))) as OSLB6. cbn [ab_addr ab_size] in OSLB6.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK6 (INB _ (yb_in_decbuf mh' h')) ltac:(cbn; unfold SIZEOF_BUF; lia))) as OSDB6. cbn [ab_addr ab_size] in OSDB6.
  (* [comment removed for export] *)
  destruct (BLKY _ _ _ _ _ AHK6) as (RNG6 & _ & _).
  pose proof (RNG6 _ (INB _ (yb_in_hand mh' h'))) as AR1. pose proof (RNG6 _ (INB _ (yb_in_lexer mh' h'))) as AR2.
  pose proof (RNG6 _ (INB _ (yb_in_lexbuf mh' h'))) as AR3. pose proof (RNG6 _ (INB _ (yb_in_decbuf mh' h'))) as AR4.
  unfold ablock_range in AR1, AR2, AR3, AR4. cbn [ab_addr ab_size] in AR1, AR2, AR3, AR4.
  assert (BAFR : BYajlAlign.BA_ayfree ((1, ff) :: LF) (LK ++ REST) h' mh' lo RR K sp).
  { red. clear -AR1 AR2 AR3 AR4. repeat split; try lia; Z.div_mod_to_equations; lia. }
  clear RNG6 AR1 AR2 AR3 AR4.
  clear PRES4w AGREE4 ST4 MI4 AHK4 AHK5 YS4 FR4 SV4 SV16 GAP4 FF8_4 FFP4 CXC4 SHC4 OSX4 TXT4 PRES6.
  (* [comment removed for export] *)
  arz_seg KIPY AHK6.
  eapply evtA_cut. { eapply afz4_seg. exact MI6. }
  cbv beta. intros ms7 ->.
  apply evtA_done. intros mo7 Hag7 HLI7 Hh7. destruct (BACK mo7 Hag7 HLI7) as [AHK7 R7]. clear LINK BACK.
  pose proof (sub_chunk m6 _ [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] [] ltac:(rewrite app_nil_r; exact SV6)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned sp + -80 + 64) with (bv_unsigned sp - 16) in SV16 by lia.
  unfold AFZ_J.
  (* [comment removed for export] *)
  eapply (YFR ((1, ff) :: LF) (LK ++ REST) h' mh' lo RR K);
    [ exact BAFR
    | exact K0
    | apply AYST_split; split; [exact AHK7| exact YS6]
    | exact HR6
    | exact OSH6 | exact OSL6 | exact OSLB6 | exact OSDB6
    | unfold ayframe_pre, AY_FREE_STACK, AY_LEX_FREE_STACK, AY_BUF_FREE_STACK, AMALLOC_STACK; aceil; rewrite unsigned_lit by lia;
      split; [exact ST6|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia|];
      split; [exact MI6|]; split; [exact TP| exact FRM6]
    | rewrite MADDR; reflexivity
    | clear -CEILB CRED6 YAN RR0 NNL; lia
    | exact RR0
    | rewrite nbig_app; pose proof (nbig_le_len LK) as NBL; clear -CEILB NBIG NBLK NBL; unfold AY_NBIG_REST in *; lia
    | rewrite unsigned_lit by lia; eapply USTEP; [rewrite unsigned_lit by lia; exact URA_fr| lia| exact SV16| eapply UFRAME; [exact AGREE6| exact UA]]
    | ].
  cbv beta. intros t0e t1e t2e a0e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e F8 fc8 m8 mo8 sa8 (SO8 & R8 & CRED8 & (MI8 & ST8 & FRM8 & _ & PRES8) & AY8).
  rewrite unsigned_lit in ST8, PRES8 by lia. apply AYST_split in AY8. destruct AY8 as [AHK8 YS8].
  replace (ret_pc (Z_to_bv 64 0x81ea0)) with (Z_to_bv 64 0x81ea0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES8 FR6 ltac:(lia)) as FR8.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES8 SV6 ltac:(lia)) as SV8.
  assert (GAP8 : stk bsegs m8 (SQ + 16) (bv_unsigned sp + -80)).
  { eapply stk_agree; [eapply ay_pres_agree; exact PRES8| exact GAP6| intros a Ha; split; [left; lia| intros F0; exact F0]]. }
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES8 FF8_6 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FF8_8.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES8 FFP6 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FFP8.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES8 SHC6 (or_introl eq_refl) ltac:(right; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold oshw_lo, A_SB; rewrite shl8_1; lia)) as SHC8.
  assert (TB6 : (exists bt, In bt (LK ++ REST) /\ ab_addr bt <= T /\ T + zlength txt <= ab_addr bt + ab_size bt) \/ zlength txt = 0).
  { destruct TB' as [(bt & Hbt & B1 & B2)| Z0]; [left; exists bt; split; [apply in_or_app; right; exact Hbt| split; [exact B1| exact B2]]| right; exact Z0]. }
  pose proof (aypres_text _ _ _ _ _ _ _ PRES8 TXT6 TB6) as TXT8.
  assert (PRES8w : ay_pres REST LF (bv_unsigned sp) [] m m8).
  { eapply ay_pres_trans; [exact PRES6w|]. eapply (ay_pres_weaken Y); [exact PRES8| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0| intros f Hf; right; exact Hf| auto]. }
  eapply (fuzz_tail LF REST T txt OT OTn lo RR K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s SQ ff) with (LK := LK); try eassumption.
  all: try reflexivity.
  all: try rchain.
  all: try (rewrite ?SO8, ?SO6, ?SO4; exact SO2).
  all: try (eapply yfuzz_leaf_some; [exact HL| exact HPL]).
Qed.

End W.
End RC__1.
