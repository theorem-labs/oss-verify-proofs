(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Ltac2 Require Import Ltac2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlDecode YajlFactsBits YajlFactsLex YajlFactsDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib RY_decode1 RY_secinst.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AI_globals2 AI_lowshadow AYajlRep AYajl_iface AY_rz AY_hand AY_client
     AY_dec1 AY_dec2 AY_dec3 AY_dec4 AY_dec5 AY_dec6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Set Default Proof Mode "Classic".

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
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
Hypothesis STATY : AHK_y_statics_stmt Y.
Hypothesis ASM0 : astack_malloc_stmt Y 0 AY_STACK_MALLOC_0.
Hypothesis FREL : AHK_y_fake_release_stmt Y.
Hypothesis FND : AHK_y_fnodup_stmt Y.
Hypothesis AFLC : AHK_y_flag_cell_stmt Y.
Hypothesis BAPP2 : aybuf_append_stmt Y.
Hypothesis HEX : ayhexToDigit_stmt.
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells asegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
Hypothesis URA_a1 : In 0x8ac80 URA.      (* [comment removed for export] *)
Hypothesis URA_a2 : In 0x8ae50 URA.      (* [comment removed for export] *)
Hypothesis URA_a3 : In 0x8af54 URA.      (* [comment removed for export] *)
Hypothesis URA_a4 : In 0x8afc8 URA.      (* [comment removed for export] *)
Hypothesis ICPG : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals asegs m A_SB.
Hypothesis ICPG2 : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals2 asegs m.
Hypothesis ICPB : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window asegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).   (* [comment removed for export] *)
Hypothesis ICPR : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n).
Hypothesis LOWSH : forall s LB LF m mo, y_AHK Y s LB LF m mo -> low_shadow_ok m.
Hypothesis SSH0 : forall s LB LF m mo A n, y_AHK Y s LB LF m mo -> alloc_ceiling <= A -> 1 <= n -> A + n <= 2^47 ->
    exists ws, shadow_window asegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n) /\ ws = repeat (Z_to_bv 8 0) (length ws).

Theorem aystring_decode_proof : aystring_decode_stmt Y.
Proof. aceil.
  unfold aystring_decode_stmt. intros LF REST mbd db AF S str n OT OTn lo RR K. intros until s.
  intros K0 AY BR BI U0 YAF AFOK OSB OSD TB SF NL N26 SNZ S47 SBX TR TOBJ FLC FP EA0 EA1 EA2 CRED RR0 NBIG UA CONT. subst a0 a1 a2.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM).
  apply AYST_split in AY. destruct AY as [AHK0 YS]. pose proof YS as (YCB & YBAE & YNOOP & STA). ay_statics_open STA.
  unfold wz in TP. unfold wz.
  pose proof LO as LO0. unfold AY_DECODE_STACK, AY_BUF_APPEND_STACK, AMALLOC_STACK in LO0.
  pose proof CEIL as CE. aceil.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (zlength_nonneg str) as NL0. pose proof (proj1 TB) as S0.
  destruct AFOK as (ba & Hba & BA1 & BA2 & BA8 & OSBA & BAHI).
  assert (AFIN : exists b, In b REST /\ ab_addr b <= AF /\ AF + 32 <= ab_addr b + 8 * (ab_size b / 8) /\ AF mod 8 = 0 /\ oshw_hi 0 (2^47) <= ab_addr b) by (exists ba; repeat split; assumption).
  assert (INR : forall b0, In b0 REST -> In b0 (abl (buf_blocks mbd db) ++ REST)) by (intros b0 Hb0; apply in_or_app; right; exact Hb0).
  (* [comment removed for export] *)
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & _ & _).
  pose proof (RNG (mkABlock (mb_addr mbd) SIZEOF_BUF) ltac:(apply in_or_app; left; unfold buf_blocks; left; reflexivity)) as RB.
  unfold ablock_range, ACONSTS in RB. cbn [c_img_hi ab_addr ab_size] in RB. aceil.
  (* [comment removed for export] *)
  arz_seg KIPY AHK0.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ LF _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  eapply evtA_cut.
  { eapply adp1_seg; [ exact ST | exact MI | exact CE | lia | lia | exact SP16 | exact G1 | exact G2 | exact G3 | exact G4 | lia | lia | lia | exact PSTK | exact PIMG ]. }
  cbv beta. intros ms1 (SQ & jq & m1 & -> & SQ32 & SQR & MU & WM & MI1 & ST1 & FR1 & SV1 & GAP1).
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHKb R1]. clear LINK BACK PSTK PIMG.
  assert (AHK1 : y_AHK Y s (abl (buf_blocks mbd db) ++ REST) LF m1 mo1).
  { eapply FRAMEY; [exact AHKb| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; aceil; lia| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS1.
  assert (PRES1 : ay_pres (abl (buf_blocks mbd db) ++ REST) LF (bv_unsigned sp) [] m m1).
  { eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _.
    eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ _ (bv_unsigned sp)); [exact AHK0| intros b0 Hb0; exact Hb0| aceil; lia| lia| exact Hc]. }
  clear ST MI.
  (* [comment removed for export] *)
  eapply ASM0;
    [ exact K0 | exact AHK1 | exact FLC
    | rewrite unsigned_lit by lia; exact ST1
    | exact CEIL
    | rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia
    | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; clear -CEILB SQ32; Z.div_mod_to_equations; lia
    | exact MI1 | exact TP | exact FRM
    | exact CRED
    | ].
  cbv beta. intros t0a t1a t2a a1a a2a a3a a4a a5a a6a a7a t3a t4a t5a t6a F2 fc2 m2 mo2 sa2 FF junk ST2 PRES2 WM2 MI2 FRM2 SO2 FF0 FFal FFsh FFce FFfr FFC FFS FLG AHK2 R2 CRED2.
  rewrite unsigned_lit in ST2, PRES2 by lia.
  rewrite ff_bytes_0 in FFal, FFsh, FFce, FFC, FFfr. unfold amem in FFsh.
  change (Z.to_nat (64 - 8)) with 56%nat in FFC. unfold oshw_lo in FFS. rewrite shl8_0 in FFS. change (Z.to_nat 8) with 8%nat in FFS.
  replace (A_SB + FF / 8) with (2147450880 + FF / 8) in FFS by reflexivity.
  pose proof FFce as FC. aceil.
  assert (E8F : FF = 8 * (FF / 8)) by (clear -CEILB FFal; Z.div_mod_to_equations; lia).
  assert (FRESH : forall g, In g LF -> In g ((0, FF) :: LF) /\ snd g <> snd (0, FF)).
  { intros g Hg. split; [right; exact Hg|]. cbn [snd]. eapply notin_map_snd; [eapply FND; exact AHK2| exact Hg]. }
  destruct (LAYY _ _ _ _ _ AHK2) as (LAYF2 & _ & _).
  pose proof (LAYF2 _ (or_introl eq_refl)) as (_ & _ & _ & _ & PFR). cbn [fst snd] in PFR. unfold amem in PFR. clear LAYF2.
  destruct (AFLC _ _ _ _ _ (0, FF) AHK2 (or_introl eq_refl)) as [_ PFD]. cbn [fst snd] in PFD. rewrite ff_bytes_0 in PFD.
  clear FLG.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 FR1 ltac:(lia)) as FR2. pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 SV1 ltac:(lia)) as SV2. clear FR1 SV1.
  assert (GAP2 : stk asegs m2 (SQ + 152) (bv_unsigned sp + -104)) by (eapply stk_agree; [eapply ay_pres_agree; exact PRES2| exact GAP1| intros a Ha; split; [left; lia| intros F0; exact F0]]). clear GAP1.
  pose proof (aystatics_pres _ _ _ _ _ YS1 PRES2) as (YCB2 & YBAE2 & YNOOP2). pose proof (STATY _ _ _ _ _ AHK2) as STA2.
  assert (YS2 : aystatics m2) by (exact (conj YCB2 (conj YBAE2 (conj YNOOP2 STA2)))). clear YCB2 YBAE2 YNOOP2.
  assert (PRES12 : ay_pres (abl (buf_blocks mbd db) ++ REST) LF (bv_unsigned sp) [] m m2).
  { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES2| lia| intros b0 Hb0; exact Hb0| intros f Hf; exact Hf| auto]. }
  pose proof (aypres_block _ _ _ _ _ _ _ PRES12 YAF ltac:(exists ba; split; [apply INR; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB BA1 BA2; Z.div_mod_to_equations; lia)) as YAF2.
  pose proof ltac2:(inst_sec '@AY_dec6.buf_keep) as BKEEP.
  destruct (BKEEP _ _ [] _ _ _ _ _ AHK2 PRES12 BR OSD) as (BR2 & OSB2 & OSD2).
  Ltac txt_via str TR NL PRES TB INR :=
    let bt := fresh "bt" in let HBT := fresh "HBT" in
    destruct TR as [(bt & HBT & ? & ?)| ?];
    [ eapply aypres_block_bytes; [exact PRES| exact TB|]; exists bt; split; [exact (INR _ HBT)|]; rewrite zbytes_length; unfold zlength in NL; lia
    | assert (str = []) as -> by (destruct str; [reflexivity| unfold zlength in *; cbn in *; lia]);
      destruct TB as (? & ? & _); split; [assumption|]; split; [assumption|]; let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; cbn in Hi; lia ].
  assert (TB2 : bytes_at asegs m2 S (zbytes str)) by (txt_via str TR NL PRES12 TB INR).
  assert (PRES2w : ay_pres REST LF (bv_unsigned sp) [] m m2).
  { eapply (ay_pres_weaken Y); [exact PRES12| lia| exact INR| intros f Hf; exact Hf| auto]. }
  clear ST1 MI1 PRES2 PRES1 AHK1 YS1 BR OSB OSD TB YAF AHK0 PRES12.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 ADP_RET1)) with (Z_to_bv 64 ADP_RET1) by (symmetry; apply ret_pc_even; [unfold ADP_RET1; lia| reflexivity]).
  arz_seg KIPY AHK2. unfold wz.
  pose proof (aypol_stack Y _ ((0, FF) :: LF) _ _ LINK SQ (SQ + 152) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_fframe Y _ ((0, FF) :: LF) _ _ LINK (0, FF) FF (FF + 64) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; rewrite ff_bytes_0; lia) ltac:(lia) ltac:(cbn; rewrite ff_bytes_0; lia)) as PFF.
  pose proof (aypol_ffshadow Y _ ((0, FF) :: LF) _ _ LINK (0, FF) (2147450880 + FF / 8) (2147450880 + FF / 8 + 8) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_0; lia)) as PFFS.
  eapply evtA_cut.
  { eapply adp2_seg; [ exact MI2 | lia | lia | exact FR2 | exact FFC | exact FFS | exact FFsh | exact FC | exact FFal | lia | exact PSTK | exact PFF | exact PFFS ]. }
  cbv beta. intros ms3 (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & j0 & j128 & fj' & m3 & MU3 & WM3 & MI3 & FFH3 & FSH3 & LJ & CASES).
  pose proof ltac2:(inst_sec '@AY_dec6.own_writes) as OWNW.
  assert (STEP : forall mo3, magree mo2 mo3 -> LI (y_aS Y sa2) (y_aN Y sa2) (y_aEB Y sa2) mo3 -> m_halted mo3 = None ->
            y_AHK Y sa2 (abl (buf_blocks mbd db) ++ REST) ((0, FF) :: LF) m3 mo3 /\ ay_pres (abl (buf_blocks mbd db) ++ REST) LF (bv_unsigned sp) [] m2 m3 /\ aystatics m3 /\ y_ayR Y sa2 mo2 sa2 mo3).
  { intros mo3 Hag3 HLI3 Hh3. destruct (BACK mo3 Hag3 HLI3) as [AHKb R3].
    destruct (OWNW _ _ _ _ _ _ AHKb MU3 WM3 ltac:(unfold AY_dec6.own_iv; repeat (apply Forall_cons; [cbn [fst snd]; aceil; lia|]); apply Forall_nil)) as (AHK3 & PRES3 & YSf).
    split; [exact AHK3|]. split; [exact PRES3|]. split; [exact (YSf YS2)| exact R3]. }
  clear LINK BACK PSTK PFF PFFS OWNW.
  (* [comment removed for export] *)
  Ltac trm H MU WM := eapply (rw_cells_transport asegs) in H; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; first [lia| aceil; lia]].
  trm SV2 MU3 WM3.
  eapply (stk_transport_disjoint asegs) in GAP2; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; lia].
  eapply (stk_transport_disjoint asegs) in ST2; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; lia].
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [_] [8; 5; 19]%nat) in FFH3; [| reflexivity]. cbn [app mk_CB_cells] in FFH3.
  pose proof (sub_chunk m3 _ [] [_; _; _; _] [_; _; _] ltac:(exact FFH3)) as FFA3. cbn [cells_size csize Nat.add Z.of_nat] in FFA3. rewrite Z.add_0_r in FFA3.
  pose proof (sub_chunk m3 _ [_; _; _; _] [_] [_; _] ltac:(exact FFH3)) as U53. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in U53.
  pose proof (sub_chunk m3 _ [_; _; _; _; _] [_] [_] ltac:(exact FFH3)) as FJ3. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FJ3.
  pose proof (sub_chunk m3 _ [_; _; _; _; _; _] [_] [] ltac:(rewrite app_nil_r; exact FFH3)) as FFP3. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FFP3.
  destruct CASES as [(N0 & -> & (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w16 & sur & cp & FRQ3))| (NP & -> & (w0 & w16 & sur & cp & FRQ3))].
  - (* [comment removed for export] *)
    apply evtA_done. intros mo3 Hag3 HLI3 Hh3. destruct (STEP mo3 Hag3 HLI3 Hh3) as (AHK3 & PRES3 & YS3 & R3). clear STEP.
    destruct (BKEEP _ _ [] _ _ _ _ _ AHK3 PRES3 BR2 OSD2) as (BR3 & OSB3 & OSD3).
    pose proof (aypres_block _ _ _ _ _ _ _ PRES3 YAF2 ltac:(exists ba; split; [apply INR; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB BA1 BA2; Z.div_mod_to_equations; lia)) as YAF3.
    assert (TB3 : bytes_at asegs m3 S (zbytes str)) by (txt_via str TR NL PRES3 TB2 INR).
    assert (PRES3w : ay_pres REST LF (bv_unsigned sp) [] m m3).
    { eapply ay_pres_trans; [exact PRES2w|]. eapply (ay_pres_weaken Y); [exact PRES3| lia| exact INR| intros f Hf; exact Hf| auto]. }
    pose proof (sub_chunk m3 _ [] [_] [_; _; _; _; _; _] ltac:(exact FFH3)) as FF03. cbn [cells_size csize Nat.add Z.of_nat] in FF03. rewrite Z.add_0_r in FF03.
    pose proof (sub_chunk m3 _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _] [_; _] [_; _; _; _] ltac:(exact FRQ3)) as L112. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in L112.
    pose proof ltac2:(inst_sec '@AY_dec6.dec_exit) as DEXIT.
    eapply (DEXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m3 mo3 sa2 db mbd [] 0 0);
      [ exact AHK3 | exact YS3 | exact MI3 | exact ST2 | exact GAP2 | exact FRM2
      | exact FRQ3 | reflexivity | exact L112 | exact SV2 | exact FF03 | exact FFP3 | exact FSH3 | exact TB3
      | exact YAF3 | exact BR3 | exact BI | reflexivity | exact OSB3 | exact OSD3
      | exact PRES3w | eapply RRT; [exact R1|]; eapply RRT; [exact R2| exact R3] | exact SO2 | exact CRED2 | exact RR0
      | intros X; exfalso; exact (X eq_refl) | reflexivity | lia | lia | lia
      | intros bf Hbf; unfold ystring_decode; eapply yleaf_bind; [apply dlf_exit; lia|]; cbv beta iota; exact Hbf ].
  - (* [comment removed for export] *)
    apply evtA_done. intros mo3 Hag3 HLI3 Hh3. destruct (STEP mo3 Hag3 HLI3 Hh3) as (AHK3 & PRES3 & YS3 & R3). clear STEP.
    destruct (BKEEP _ _ [] _ _ _ _ _ AHK3 PRES3 BR2 OSD2) as (BR3 & OSB3 & OSD3).
    pose proof (aypres_block _ _ _ _ _ _ _ PRES3 YAF2 ltac:(exists ba; split; [apply INR; exact Hba|]; unfold alloc_cells; cbn; clear -CEILB BA1 BA2; Z.div_mod_to_equations; lia)) as YAF3.
    assert (TB3 : bytes_at asegs m3 S (zbytes str)) by (txt_via str TR NL PRES3 TB2 INR).
    assert (PRES3w : ay_pres REST LF (bv_unsigned sp) [] m m3).
    { eapply ay_pres_trans; [exact PRES2w|]. eapply (ay_pres_weaken Y); [exact PRES3| lia| exact INR| intros f Hf; exact Hf| auto]. }
    pose (HOKd := ltac2:(inst_sec '@AY_dec6.head_ok)).
    pose proof ltac2:(inst_sec '@AY_dec6.dec_step) as DSTEP.
    assert (HOK : forall f, HOKd f).
    { induction f as [|f IH]; [| exact (DSTEP f IH)]. subst HOKd. unfold AY_dec6.head_ok. intros. exfalso. lia. }
    eapply (HOK (decode_fuel n) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m3 mo3 sa2 db mbd [] 0 0);
      [ exact AHK3 | exact YS3 | exact MI3 | exact ST2 | exact GAP2 | exact FRM2
      | exact FRQ3 | exact SV2 | exact FFA3 | exact U53 | exact FJ3 | exact FFP3 | exact FSH3 | exact TB3
      | exact YAF3 | exact BR3 | exact BI | reflexivity | exact OSB3 | exact OSD3
      | exact PRES3w | eapply RRT; [exact R1|]; eapply RRT; [exact R2| exact R3] | exact SO2 | exact CRED2 | exact RR0
      | intros X; exfalso; exact (X eq_refl) | reflexivity | lia | lia | exact NP | exact SBX | unfold decode_fuel; lia | intros r Hr; exact Hr ].
Qed.

End W.
End RC__1.
