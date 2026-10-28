(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_StateStmt LbB_HKit LbB_HStKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoKit3 LbB_WoSt LbB_WoE0 LbB_WoE0b LbB_WoCut LbB_WoVec LbB_WoF.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma wr_at_of_definedW : forall m a n, HRep.defined m a n -> 0 <= a -> a + n <= 2 ^ 64 -> wr_at asegs m a n.
Proof.
  intros m a n D H0 H1. split; [lia|]. split; [lia|]. intros i Hi. pose proof (D i Hi) as Di.
  unfold wview, wa. destruct (m (Z_to_bv 64 (a + i))) as [b|] eqn:E; [discriminate | contradiction].
Qed.

Lemma wstk_wr : forall m lo hi a n, stk asegs m lo hi -> lo <= a -> a + n <= hi -> wr_at asegs m a n.
Proof.
  intros m lo hi a n ST H1 H2. pose proof (wr_at_of_stk asegs m lo hi ST) as (W0 & W1 & W).
  split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia.
Qed.

Lemma fld_of_cells : forall m A cs k c v, rw_cells asegs m A cs -> cell_at cs k = Some c ->
  cbytes c = word_to_le_bytes (csize c) (Z_to_bv 64 v) -> fld ASEGS m (A + Z.of_nat k) (csize c) v.
Proof.
  intros m A cs k c v Hc Hk Hb. unfold fld.
  pose proof (rw_cells_read asegs m A cs k c Hc Hk) as RD. rewrite Hb in RD. rewrite <- rdn_of_ov. exact RD.
Qed.

Lemma state_repA_wr : forall LB m st c, state_repA LB m st c -> 0 <= st -> st + 240 <= 2 ^ 64 -> wr_at asegs m st 240.
Proof. intros LB m st c R H0 H1. apply wr_at_of_definedW; [eapply sr_def; exact (proj1 R) | lia | lia]. Qed.

Lemma lb_small_permW : forall LB LB', Permutation LB' LB -> lb_small LB' = lb_small LB.
Proof. intros LB LB' P. induction P; rewrite ?lb_small_cons in *; lia. Qed.
Lemma nlarge_permW : forall LB LB', Permutation LB' LB -> nlarge LB' = nlarge LB.
Proof. intros LB LB' P. induction P; rewrite ?nlarge_cons in *; lia. Qed.
Lemma lb_small_appW : forall (L1 L2 : list block), lb_small (L1 ++ L2) = lb_small L1 + lb_small L2.
Proof. induction L1 as [|b L1 IH]; intros L2; [reflexivity|]. cbn [app]. rewrite !lb_small_cons, IH. lia. Qed.
Lemma nlarge_appW : forall (L1 L2 : list block), nlarge (L1 ++ L2) = nlarge L1 + nlarge L2.
Proof. induction L1 as [|b L1 IH]; intros L2; [reflexivity|]. cbn [app]. rewrite !nlarge_cons, IH. lia. Qed.

Section St2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma wmdef_keep : forall e ff fp XSc sk LBk m' p A n a k, wpre H e -> winv H e ff fp XSc sk LBk m' ->
    In (p, A, n) (w_LB e) -> A <= a -> a + k <= A + n -> mdef (w_m e) a k -> mdef m' a k.
  Proof.
    intros e ff fp XSc sk LBk m' p A n a k HP HI IN H1 H2 D i Hi.
    pose proof (ah_blocks H HH _ _ _ _ (wpre_RH0 H e HP) IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC.
    pose proof aceil_facts as ACF.
    pose proof (proj1 (wkeep H HH e ff fp XSc sk LBk m' (a + i) HP HI ltac:(lia) ltac:(left; exists p, A, n; split; [exact IN | left; lia]))) as E.
    unfold wa in E. rewrite E. apply D. exact Hi.
  Qed.

  Lemma wshad_keep : forall e ff fp XSc sk LBk m' p A n sbs, wpre H e -> winv H e ff fp XSc sk LBk m' ->
    In (p, A, n) (w_LB e) -> Z.of_nat (length sbs) = nsh n -> SHAD (w_m e) A sbs -> SHAD m' A sbs.
  Proof.
    intros e ff fp XSc sk LBk m' p A n sbs HP HI IN LEN (HA & HA8 & (B0 & B1 & B) & (W0 & W1 & W)).
    rewrite LEN in B1, W1, W.
    pose proof (ah_blocks H HH _ _ _ _ (wpre_RH0 H e HP) IN) as (C0 & C16 & Cn & CI & CC & CF & CAPP). cbn in C0, C16, Cn, CI, CC, CF, CAPP.
    pose proof aceil_facts as ACF.
    assert (X1 : A + n <= AAPP_HI) by (unfold AAPP_HI; lia).
    assert (SB : sh A + nsh n <= 0x10007fff8000) by (pose proof (sh_nsh_high A n ltac:(lia) ltac:(lia) X1); unfold AHI_LO in *; lia).
    assert (KP : forall a, sh A <= a < sh A + nsh n -> m' (wa a) = w_m e (wa a) /\ (wview asegs (w_m e) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha. apply (wkeep H HH e ff fp XSc sk LBk m' a HP HI); [unfold sh in *; rewrite ASHADOW_BASE_val in *; lia|].
      left. exists p, A, n. split; [exact IN | right; exact Ha]. }
    split; [exact HA|]. split; [exact HA8|]. split.
    - split; [exact B0|]. split; [rewrite LEN; exact B1|]. intros i Hi. unfold mrd.
      rewrite (proj1 (KP (sh A + Z.of_nat i) ltac:(lia))). exact (B i Hi).
    - split; [exact W0|]. split; [rewrite LEN; exact W1|]. intros i Hi. rewrite LEN in Hi.
      apply (proj2 (KP (sh A + i) ltac:(lia))). apply W. exact Hi.
  Qed.

  Lemma wwords_keep : forall e ff fp XSc sk LBk m', wpre H e -> winv H e ff fp XSc sk LBk m' ->
    (w_words e = 0 /\ w_n e = 0) \/ words_okA (w_LB e) m' (w_words e) (w_n e).
  Proof.
    intros e ff fp XSc sk LBk m' HP HI.
    pose proof HP as (_ & _ & _ & WD & _).
    destruct WD as [WD|(pw & kk & IN & H4 & W0 & W16 & W47 & MD & SHD)]; [left; exact WD | right].
    exists pw, kk. split; [exact IN|]. split; [exact H4|]. split; [exact W0|]. split; [exact W16|]. split; [exact W47|]. split.
    - eapply (wmdef_keep e ff fp XSc sk LBk m' pw (w_words e) kk); [exact HP | exact HI | exact IN | lia | lia | exact MD].
    - eapply (wshad_keep e ff fp XSc sk LBk m' pw (w_words e) kk); [exact HP | exact HI | exact IN | apply cc_gen_length; lia | exact SHD].
  Qed.

  Lemma wblk3_nodup : forall s LB m LBy (p1 p2 p3 : bptr) q1 q2 q3 n1 n2 n3,
    as_RHEAP H s LB m -> Permutation LB ([(p1, q1, n1); (p2, q2, n2); (p3, q3, n3)] ++ LBy) -> NoDup [q1; q2; q3].
  Proof.
    intros s LB m LBy p1 p2 p3 q1 q2 q3 n1 n2 n3 RH P.
    pose proof (nodup_fst_of_perm' H HH s LB m [(p1, q1, n1); (p2, q2, n2); (p3, q3, n3)] LBy [(q1, n1); (q2, n2); (q3, n3)] RH P
                  (Permutation_refl _)) as ND.
    exact ND.
  Qed.

  Lemma wst_P_rep : forall (e : went H) ff fp XSc sk LBk m (p1 p2 p3 : bptr) b1 b2 b3 LBy,
    wpre H e -> winv H e ff fp XSc sk LBk m -> wps3 ff m b1 b2 b3 ->
    In (p1, b1, 500) LBk -> In (p2, b2, 100) LBk -> In (p3, b3, 100) LBk ->
    Permutation LBk ([(p1, b1, 500); (p2, b2, 100); (p3, b3, 100)] ++ LBy) ->
    state_repA LBk m (ff + 3504) (mkfreshA 0 0 b1 b2 b3) /\ state_sh m (mkfreshA 0 0 b1 b2 b3)
    /\ 0 < b1 /\ 0 < b2 /\ 0 < b3.
  Proof.
    intros e ff fp XSc sk LBk m p1 p2 p3 b1 b2 b3 LBy HP HI (PST & (W1 & S1') & (W2 & S2') & (W3 & S3')) I1 I2 I3 P.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof aceil_facts as ACF.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    pose proof (ah_blocks H HH _ _ _ _ RH I1) as (A0 & A16 & An & AI & AC' & AF & AAPP). cbn in A0, A16, An, AI, AC'.
    pose proof (ah_blocks H HH _ _ _ _ RH I2) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC.
    pose proof (ah_blocks H HH _ _ _ _ RH I3) as (C0 & C16 & Cn & CI & CC & CF & CAPP). cbn in C0, C16, Cn, CI, CC.
    destruct PST as (Z46 & MC & V1 & V2 & V3).
    split; [| split; [apply st_sh_freshA; [exact S1' | exact S2' | exact S3'] | lia]].
    apply st_rep_freshA.
    - left. split; [reflexivity|]. split; [reflexivity | exact Z46].
    - exact MC.
    - unfold st_vecs_cells. replace (ff + 3504 + 168) with (ff + 3672) by lia.
      change [C8 (Z_to_bv 64 b1); C8 (Z_to_bv 64 b1); C8 (Z_to_bv 64 (b1 + 500)); C8 (Z_to_bv 64 b2); C8 (Z_to_bv 64 b2); C8 (Z_to_bv 64 (b2 + 100));
              C8 (Z_to_bv 64 b3); C8 (Z_to_bv 64 b3); C8 (Z_to_bv 64 (b3 + 100))]
        with (vtrip b1 500 ++ vtrip b2 100 ++ vtrip b3 100).
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact V1|]. cbn [cells_size csize vtrip Nat.add].
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [replace (ff + 3672 + Z.of_nat 24) with (ff + 3696) by lia; exact V2|].
      cbn [cells_size csize vtrip Nat.add]. replace (ff + 3672 + Z.of_nat 24 + Z.of_nat 24) with (ff + 3720) by lia. exact V3.
    - lia. - lia.
    - pose proof (winv_wf H _ _ _ _ _ _ _ HI) as (X0 & X1 & X). unfold WO_FLAGP in *.
      split; [lia|]. split; [lia|]. intros i Hi. replace (ff + 3504 + i) with (ff + (3504 + i)) by lia. apply X. lia.
    - clear - F3. Z.div_mod_to_equations. lia.
    - lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia.
    - exact (lbl_in _ _ _ _ I1). - exact (lbl_in _ _ _ _ I2). - exact (lbl_in _ _ _ _ I3).
    - exact (wblk3_nodup sk LBk m LBy p1 p2 p3 b1 b2 b3 500 100 100 RH P).
  Qed.

  Lemma wst_T_rep : forall (e : went H) ff fp XSc sk LBk m (p4 p5 p6 : bptr) g h k LBy,
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    wtst ff m (w_words e) (w_n e) (vtrip g 500) (vtrip h 100) (vtrip k 100) -> wblk m g 500 -> wblk m h 100 -> wblk m k 100 ->
    In (p4, g, 500) LBk -> In (p5, h, 100) LBk -> In (p6, k, 100) LBk ->
    Permutation LBk ([(p4, g, 500); (p5, h, 100); (p6, k, 100)] ++ LBy) ->
    state_repA LBk m (ff + 2752) (mkfreshA (w_words e) (w_n e) g h k) /\ state_sh m (mkfreshA (w_words e) (w_n e) g h k)
    /\ 0 < g /\ 0 < h /\ 0 < k.
  Proof.
    intros e ff fp XSc sk LBk m p4 p5 p6 g h k LBy HP HI (SC & Z22 & MC & V1 & V2 & V3) (W1 & S1') (W2 & S2') (W3 & S3') I1 I2 I3 P.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof aceil_facts as ACF.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    pose proof (ah_blocks H HH _ _ _ _ RH I1) as (A0 & A16 & An & AI & AC' & AF & AAPP). cbn in A0, A16, An, AI, AC'.
    pose proof (ah_blocks H HH _ _ _ _ RH I2) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC.
    pose proof (ah_blocks H HH _ _ _ _ RH I3) as (C0 & C16 & Cn & CI & CC & CF & CAPP). cbn in C0, C16, Cn, CI, CC.
    pose proof HP as (_ & _ & HN & WD & _).
    assert (WR : 0 <= w_words e < 2 ^ 64).
    { destruct WD as [(-> & _)|(pw & kk & IN & H4 & W0 & W16 & W47 & _)]; [lia|]. lia. }
    split; [| split; [apply st_sh_freshA; [exact S1' | exact S2' | exact S3'] | lia]].
    apply st_rep_freshA.
    - right. split; [exact SC | replace (ff + 2752 + 24) with (ff + 2776) by lia; exact Z22].
    - exact MC.
    - unfold st_vecs_cells. replace (ff + 2752 + 168) with (ff + 2920) by lia.
      change [C8 (Z_to_bv 64 g); C8 (Z_to_bv 64 g); C8 (Z_to_bv 64 (g + 500)); C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 (h + 100));
              C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 (k + 100))]
        with (vtrip g 500 ++ vtrip h 100 ++ vtrip k 100).
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact V1|]. cbn [cells_size csize vtrip Nat.add].
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [replace (ff + 2920 + Z.of_nat 24) with (ff + 2944) by lia; exact V2|].
      cbn [cells_size csize vtrip Nat.add]. replace (ff + 2920 + Z.of_nat 24 + Z.of_nat 24) with (ff + 2968) by lia. exact V3.
    - exact WR. - lia.
    - pose proof (winv_wf H _ _ _ _ _ _ _ HI) as (X0 & X1 & X). unfold WO_FLAGP in *.
      split; [lia|]. split; [lia|]. intros i Hi. replace (ff + 2752 + i) with (ff + (2752 + i)) by lia. apply X. lia.
    - clear - F3. Z.div_mod_to_equations. lia.
    - lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia.
    - exact (lbl_in _ _ _ _ I1). - exact (lbl_in _ _ _ _ I2). - exact (lbl_in _ _ _ _ I3).
    - exact (wblk3_nodup sk LBk m LBy p4 p5 p6 g h k 500 100 100 RH P).
  Qed.

  Definition wparser (ff : Z) (sc : stateC) : parserC := {| pc_cons := ff + 3376; pc_user := 0; pc_state := sc |}.

  Definition wpcells (e : went H) (ff : Z) (m : mem) : Prop :=
       rw_cells asegs m (ff + 3408) [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m (ff + 3456) [C4 (Z_to_bv 64 (w_env e))]
    /\ rw_cells asegs m (ff + 3464) [C8 (Z_to_bv 64 (ff + 3376)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C1 (b8 0)]
    /\ addressable m (ff + 3456) 288 /\ addressable m (ff + 3376) 48.

  Lemma wfc_wpcells : forall (e : went H) ff fp XSc sk LBk m, winv H e ff fp XSc sk LBk m -> wfc H e ff m -> wpcells e ff m.
  Proof.
    intros e ff fp XSc sk LBk m HI (_ & _ & C3 & C4 & C5 & C6 & _).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & _).
    split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
    split; [exact (wo_pad m ff C6 F3 ltac:(lia)) | exact (wo_cad m ff C6 F3 ltac:(lia))].
  Qed.

  Lemma wparser_mk : forall (e : went H) ff fp XSc sk LBk m sc,
    wpre H e -> winv H e ff fp XSc sk LBk m -> wpcells e ff m -> state_repA LBk m (ff + 3504) sc ->
    parser_repA LBk m (ff + 3456) (wparser ff sc)
    /\ (state_sh m sc -> parser_sh m (ff + 3456) (wparser ff sc))
    /\ fsin ((6, ff, fp) :: w_LF e) (ff + 3456) PARSER_SIZE /\ fsin ((6, ff, fp) :: w_LF e) (ff + 3376) 48
    /\ (ff + 3376) mod 16 = 0 /\ wr_at asegs m (ff + 3376) 48.
  Proof.
    intros e ff fp XSc sk LBk m sc HP HI WC SR.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof aceil_facts as ACF.
    destruct WC as (C3 & C4 & C5 & AP & AC).
    pose proof (winv_wf H _ _ _ _ _ _ _ HI) as WF. unfold WO_FLAGP in WF.
    assert (WRS : forall o n, 0 <= o -> 0 <= n -> o + n <= 4088 -> wr_at asegs m (ff + o) n).
    { intros o n Ho Hn Hk. destruct WF as (X0 & X1 & X). split; [lia|]. split; [lia|]. intros i Hi.
      replace (ff + o + i) with (ff + (o + i)) by lia. apply X. lia. }
    assert (MD : forall o n, 0 <= o -> 0 <= n -> o + n <= 4088 -> mdef m (ff + o) n).
    { intros o n Ho Hn Hk. apply mdef_of_wr_at; [apply WRS; lia | lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - unfold parser_repA. constructor; cbn [pc_cons pc_user pc_state wparser]; unfold ST_OFF, PARSER_SIZE.
      + replace (ff + 3456 + 8) with (ff + 3464 + Z.of_nat 0) by lia.
        apply (fld_of_cells m (ff + 3464) _ 0 (C8 (Z_to_bv 64 (ff + 3376))) (ff + 3376) C5 eq_refl eq_refl).
      + replace (ff + 3456 + 16) with (ff + 3464 + Z.of_nat 8) by lia.
        apply (fld_of_cells m (ff + 3464) _ 8 (C8 (Z_to_bv 64 0)) 0 C5 eq_refl eq_refl).
      + replace (ff + 3456 + 24) with (ff + 3464 + Z.of_nat 16) by lia.
        apply (fld_of_cells m (ff + 3464) _ 16 (C8 (Z_to_bv 64 0)) 0 C5 eq_refl eq_refl).
      + replace (ff + 3456 + 32) with (ff + 3464 + Z.of_nat 24) by lia.
        apply (fld_of_cells m (ff + 3464) _ 24 (C8 (Z_to_bv 64 0)) 0 C5 eq_refl eq_refl).
      + replace (ff + 3456 + 40) with (ff + 3464 + Z.of_nat 32) by lia.
        apply (fld_of_cells m (ff + 3464) _ 32 (C1 (b8 0)) 0 C5 eq_refl). vm_compute. reflexivity.
      + replace (ff + 3456 + 48) with (ff + 3504) by lia. exact (proj1 SR).
      + apply (MD 3456 48); lia.
      + clear - F3. Z.div_mod_to_equations. lia.
      + lia.
      + replace (ff + 3376 + 32) with (ff + 3408 + Z.of_nat 0) by lia.
        apply (fld_of_cells m (ff + 3408) _ 0 (C8 (Z_to_bv 64 0)) 0 C3 eq_refl eq_refl).
      + replace (ff + 3376 + 32) with (ff + 3408) by lia. apply (MD 3408 8); lia.
      + unfold apart. right. lia.
    - intros SH. split; [exact AP|]. split; [| exact SH].
      cbn [pc_cons wparser]. exact AC.
    - exists (6, ff, fp). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz 6) with 4096. unfold PARSER_SIZE. lia.
    - exists (6, ff, fp). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz 6) with 4096. lia.
    - clear - F3. Z.div_mod_to_equations. lia.
    - apply (WRS 3376 48); lia.
  Qed.
End St2.
