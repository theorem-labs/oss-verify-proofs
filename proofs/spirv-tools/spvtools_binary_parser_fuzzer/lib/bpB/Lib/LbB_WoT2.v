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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoKit3 LbB_WoSt LbB_WoSt2 LbB_WoE0 LbB_WoE0b LbB_WoCut LbB_WoVec.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section T2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Definition wtst0 (ff : Z) (m : mem) (v1 v2 v3 : list cell) : Prop :=
    rw_cells asegs m (ff + 3056) [CB 46 (poison_bytes 46 0)] /\ st_maps_cells m (ff + 3056)
    /\ rw_cells asegs m (ff + 3224) v1 /\ rw_cells asegs m (ff + 3248) v2 /\ rw_cells asegs m (ff + 3272) v3.

  Lemma wtst0_upd : forall ff m m' W v1 v2 v3 v1' v2' v3', wtst0 ff m v1 v2 v3 -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => snd iv <= ff + 3056 \/ ff + 3224 <= fst iv) W ->
    rw_cells asegs m' (ff + 3224) v1' -> rw_cells asegs m' (ff + 3248) v2' -> rw_cells asegs m' (ff + 3272) v3' ->
    wtst0 ff m' v1' v2' v3'.
  Proof.
    intros ff m m' W v1 v2 v3 v1' v2' v3' (C0 & (M1 & F1 & M2 & F2 & M3 & F3) & _ & _ & _) MU WM FW V1 V2 V3.
    assert (DJ : forall A k, ff + 3056 <= A -> A + k <= ff + 3224 -> disjoint_from W A k).
    { intros A k X1 X2. clear - FW X1 X2. induction W as [|[x y] W IH]; cbn; [exact I|].
      inversion FW as [|? ? K K2]; subst. cbn in K. split; [lia | apply IH; exact K2]. }
    split; [eapply rw_cells_transport; [exact C0 | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [unfold st_maps_cells; repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply DJ; cbn; lia])|].
    split; [exact V1|]. split; [exact V2 | exact V3].
  Qed.

  Lemma wtst0_apres : forall e ff fp XSc sk LBk LB m m' v1 v2 v3, wpre H e -> winv H e ff fp XSc sk LBk m ->
    wtst0 ff m v1 v2 v3 -> apres H LB (wS1 e) m m' -> v24 v1 -> v24 v2 -> v24 v3 -> wtst0 ff m' v1 v2 v3.
  Proof.
    intros e ff fp XSc sk LBk LB m m' v1 v2 v3 HP HI (C0 & (M1 & F1 & M2 & F2 & M3 & F3) & V1 & V2 & V3) AP Sz1 Sz2 Sz3.
    unfold v24 in *.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (FF1 & FF2 & FF3 & FF4 & FF5 & FF6 & FF7 & _).
    assert (CL : forall A k, ff <= A -> A + k <= ff + 4096 -> aclient_range H LB (wS1 e) A k).
    { intros A k X1 X2. right; right; right; right; left. lia. }
    split; [eapply (apres_rw_cells H); [exact AP | exact C0 | apply CL; cbn; lia]|].
    split; [unfold st_maps_cells; repeat split; (eapply (apres_rw_cells H); [exact AP | eassumption | apply CL; cbn; lia])|].
    split; [eapply (apres_rw_cells H); [exact AP | exact V1 | apply CL; rewrite ?Sz1; cbn; lia]|].
    split; [eapply (apres_rw_cells H); [exact AP | exact V2 | apply CL; rewrite ?Sz2; cbn; lia]|].
    eapply (apres_rw_cells H); [exact AP | exact V3 | apply CL; rewrite ?Sz3; cbn; lia].
  Qed.

  Lemma wst_T0_rep : forall (e : went H) ff fp XSc sk LBk m (p4 p5 p6 : bptr) g h k LBy,
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    wtst0 ff m (vtrip g 500) (vtrip h 100) (vtrip k 100) -> wblk m g 500 -> wblk m h 100 -> wblk m k 100 ->
    In (p4, g, 500) LBk -> In (p5, h, 100) LBk -> In (p6, k, 100) LBk ->
    Permutation LBk ([(p4, g, 500); (p5, h, 100); (p6, k, 100)] ++ LBy) ->
    state_repA LBk m (ff + 3056) (mkfreshA 0 0 g h k) /\ state_sh m (mkfreshA 0 0 g h k)
    /\ 0 < g /\ 0 < h /\ 0 < k.
  Proof.
    intros e ff fp XSc sk LBk m p4 p5 p6 g h k LBy HP HI (Z46 & MC & V1 & V2 & V3) (W1 & S1') (W2 & S2') (W3 & S3') I1 I2 I3 P.
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof aceil_facts as ACF.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (FF1 & FF2 & FF3 & FF4 & FF5 & FF6 & FF7 & _).
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    pose proof (ah_blocks H HH _ _ _ _ RH I1) as (A0 & A16 & An & AI & AC' & AF & AAPP). cbn in A0, A16, An, AI, AC'.
    pose proof (ah_blocks H HH _ _ _ _ RH I2) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC.
    pose proof (ah_blocks H HH _ _ _ _ RH I3) as (C0 & C16 & Cn & CI & CC & CF & CAPP). cbn in C0, C16, Cn, CI, CC.
    split; [| split; [apply st_sh_freshA; [exact S1' | exact S2' | exact S3'] | lia]].
    apply st_rep_freshA.
    - left. split; [reflexivity|]. split; [reflexivity | exact Z46].
    - exact MC.
    - unfold st_vecs_cells. replace (ff + 3056 + 168) with (ff + 3224) by lia.
      change [C8 (Z_to_bv 64 g); C8 (Z_to_bv 64 g); C8 (Z_to_bv 64 (g + 500)); C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 (h + 100));
              C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 k); C8 (Z_to_bv 64 (k + 100))]
        with (vtrip g 500 ++ vtrip h 100 ++ vtrip k 100).
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact V1|]. cbn [cells_size csize vtrip Nat.add].
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [replace (ff + 3224 + Z.of_nat 24) with (ff + 3248) by lia; exact V2|].
      cbn [cells_size csize vtrip Nat.add]. replace (ff + 3224 + Z.of_nat 24 + Z.of_nat 24) with (ff + 3272) by lia. exact V3.
    - lia. - lia.
    - destruct (winv_wf H _ _ _ _ _ _ _ HI) as (WF0 & WF1 & WFW). unfold WO_FLAGP in WF1, WFW. split; [lia|]. split; [lia|].
      intros i Hi. replace (ff + 3056 + i) with (ff + (3056 + i)) by lia. apply WFW. lia.
    - clear - FF3. Z.div_mod_to_equations. lia.
    - lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia.
    - exact (lbl_in _ _ _ _ I1). - exact (lbl_in _ _ _ _ I2). - exact (lbl_in _ _ _ _ I3).
    - exact (wblk3_nodup H HH sk LBk m LBy p4 p5 p6 g h k 500 100 100 RH P).
  Qed.

  Definition wsw (e : went H) (LB : list block) (c : stateC) (iv : Z * Z) : Prop :=
    (aceil <= fst iv /\ snd iv <= wSP e) \/ snd iv <= fst iv
    \/ (exists (q : bptr) u len, In (q, u, len) LB /\ (forall p n, In (p, n) (state_blocks c) -> p <> u)
                                 /\ sh u <= fst iv /\ snd iv <= sh u + nsh len).

  Lemma wstate_mu : forall (e : went H) ff fp XSc s LB m m' W c,
    wpre H e -> winv H e ff fp XSc s LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (wsw e LB c) W ->
    (forall p n, In (p, n) (state_blocks c) -> In (p, n) (lbl LB)) ->
    state_repA LB m (ff + 3504) c -> state_sh m c -> state_repA LB m' (ff + 3504) c /\ state_sh m' c.
  Proof.
    intros e ff fp XSc s LB m m' W c HP HI MU WM FW BL R S.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof aceil_facts as ACF.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).

    set (X := List.filter (fun iv : Z * Z => Z.ltb (fst iv) aceil && Z.ltb (fst iv) (snd iv)) W).
    assert (XIN : forall iv, In iv X -> exists (q : bptr) u len, In (q, u, len) LB /\ (forall p n, In (p, n) (state_blocks c) -> p <> u)
                                                           /\ sh u <= fst iv /\ snd iv <= sh u + nsh len).
    { intros iv Hiv. unfold X in Hiv. apply filter_In in Hiv. destruct Hiv as [Hiv Hb].
      apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2.
      pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as K. destruct K as [K|[K|K]]; [lia | lia | exact K]. }
    assert (XP : xpres H LB (wSP e) X m m').
    { eapply (xpres_of_munch H s LB (wSP e) X W m m m' HH RH MU WM).
      apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as K.
      destruct K as [K|[K|K]]; [left; exact K | right; intros a Ha; lia |].
      destruct K as (q & u & len & Hq & _ & K1 & K2).
      pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
      destruct (sh_aapp_range _ _ BAPP Bn) as (_ & SX & _).
      destruct (Z.lt_ge_cases (fst iv) aceil) as [L|L]; [| right; intros a Ha; exfalso; lia].
      right. intros a Ha. clear - Hiv L Ha. unfold X. induction W as [|iv' W IH]; [destruct Hiv|].
      cbn [List.filter]. destruct Hiv as [->|Hiv].
      - replace (Z.ltb (fst iv) aceil && Z.ltb (fst iv) (snd iv)) with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
        left. exact Ha.
      - destruct (Z.ltb (fst iv') aceil && Z.ltb (fst iv') (snd iv')); [right|]; apply IH; exact Hiv. }
    assert (BLO : forall p n, In (p, n) (state_blocks c) -> exists q, In (q, p, n) LB /\ 0 < p /\ p mod 16 = 0 /\ 0 <= n /\ p + n <= aceil /\ aapp p n).
    { intros p n Hin. destruct (lbl_in_inv _ _ _ (BL p n Hin)) as (q & Hq).
      pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
      exists q. repeat (split; [assumption|]). exact BAPP. }

    assert (NXO : forall a, ff + 3504 <= a < ff + 3744 -> ~ rin_ivs X a).
    { intros a Ha. apply rin_ivs_none. apply Forall_forall. intros iv Hiv.
      destruct (XIN iv Hiv) as (q & u & len & Hq & _ & K1 & K2).
      pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
      pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE u len F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) Bn). lia. }
    assert (NXB : forall p n a, In (p, n) (state_blocks c) -> p <= a < p + n -> ~ rin_ivs X a).
    { intros p n a Hin Ha. apply rin_ivs_none. apply Forall_forall. intros iv Hiv.
      destruct (XIN iv Hiv) as (q & u & len & Hq & _ & K1 & K2).
      destruct (BLO p n Hin) as (q' & Hq' & P0 & P16 & Pn & PC & PAPP).
      pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
      pose proof (aapp_disjoint_sh p n u len PAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) Bn). lia. }
    assert (NXS : forall p n a, In (p, n) (state_blocks c) -> sh p <= a < sh p + nsh n -> ~ rin_ivs X a).
    { intros p n a Hin Ha. apply rin_ivs_none. apply Forall_forall. intros iv Hiv.
      destruct (XIN iv Hiv) as (q & u & len & Hq & NEQ & K1 & K2).
      destruct (BLO p n Hin) as (q' & Hq' & P0 & P16 & Pn & PC & PAPP).
      pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
      assert (NE : q' <> q).
      { intros E. subst q'. pose proof (ah_nodup H HH _ _ _ RH) as ND.
        assert (EQ : (p, n) = (u, len)).
        { clear - ND Hq Hq'. induction LB as [|b LB IH]; [destruct Hq|]. cbn [map] in ND. inversion ND as [|? ? NI ND']; subst.
          destruct Hq as [->|Hq]; destruct Hq' as [E|Hq'].
          - injection E as <- <-. reflexivity.
          - exfalso. apply NI. apply in_map_iff. exists (q, p, n). split; [reflexivity | exact Hq'].
          - exfalso. apply NI. subst b. apply in_map_iff. exists (q, u, len). split; [reflexivity | exact Hq].
          - apply IH; assumption. }
        injection EQ as -> ->. exact (NEQ u len Hin eq_refl). }
      pose proof (ah_disj H HH _ _ _ (q', p, n) (q, u, len) RH Hq' Hq NE) as D. cbn in D.
      pose proof (sh_disj16 p n u len ltac:(lia) ltac:(clear - P16; Z.div_mod_to_equations; lia) Pn ltac:(lia)
                    ltac:(clear - B16; Z.div_mod_to_equations; lia) Bn D). lia. }
    split.
    - eapply (rep_keep H LB LB LB (wSP e) X m m' (ff + 3504) c R XP).
      + apply (objx_intro H). { left. lia. } intros a Ha _. exact (NXO a ltac:(lia)).
      + apply (blkx_intro H). intros p n Hin. split; [exact (BL p n Hin)|]. split; [exact (BL p n Hin)|].
        intros a Ha. exact (NXB p n a Hin Ha).
      + unfold AIMG_TOP. lia.
      + lia.
    - eapply (sh_keep H LB LB (wSP e) X m m' (ff + 3504) c R S XP).
      apply (blksh_intro H). intros p n Hin. split; [exact (BL p n Hin)|]. intros a Ha. exact (NXS p n a Hin Ha).
  Qed.

  Definition wfw (ff : Z) (iv : Z * Z) : Prop :=
    (ff <= fst iv /\ snd iv <= ff + 3504) \/ (ff + 3744 <= fst iv /\ snd iv <= ff + 4096) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512).

  Lemma wstate_mu_ff : forall (e : went H) ff fp XSc s LB m m' W c,
    wpre H e -> winv H e ff fp XSc s LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => wsw e LB c iv \/ wfw ff iv) W ->
    (forall p n, In (p, n) (state_blocks c) -> In (p, n) (lbl LB)) ->
    state_repA LB m (ff + 3504) c -> state_sh m c -> state_repA LB m' (ff + 3504) c /\ state_sh m' c.
  Proof.
    intros e ff fp XSc s LB m m' W c HP HI MU WM FW BL R S.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof aceil_facts as ACF.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).

    set (X := List.filter (fun iv : Z * Z => Z.ltb (fst iv) aceil && Z.ltb (fst iv) (snd iv)) W).
    assert (XIN : forall iv, In iv X -> (exists (q : bptr) u len, In (q, u, len) LB /\ (forall p n, In (p, n) (state_blocks c) -> p <> u)
                                                           /\ sh u <= fst iv /\ snd iv <= sh u + nsh len) \/ wfw ff iv).
    { intros iv Hiv. unfold X in Hiv. apply filter_In in Hiv. destruct Hiv as [Hiv Hb].
      apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2.
      pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as K. destruct K as [[K|[K|K]]|K]; [lia | lia | left; exact K | right; exact K]. }
    assert (XMEM : forall iv, In iv W -> fst iv < aceil -> fst iv < snd iv -> forall a, fst iv <= a < snd iv -> rin_ivs X a).
    { intros iv Hiv L L2 a Ha. clear - Hiv L L2 Ha. unfold X. induction W as [|iv' W IH]; [destruct Hiv|].
      cbn [List.filter]. destruct Hiv as [->|Hiv].
      - replace (Z.ltb (fst iv) aceil && Z.ltb (fst iv) (snd iv)) with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
        left. exact Ha.
      - destruct (Z.ltb (fst iv') aceil && Z.ltb (fst iv') (snd iv')); [right|]; apply IH; exact Hiv. }
    assert (XP : xpres H LB (wSP e) X m m').
    { eapply (xpres_of_munch H s LB (wSP e) X W m m m' HH RH MU WM).
      apply Forall_forall. intros iv Hiv.
      destruct (Z.le_gt_cases (snd iv) (fst iv)) as [E0|E0]; [right; intros a Ha; lia|].
      destruct (Z.lt_ge_cases (fst iv) aceil) as [L|L]; [right; exact (XMEM iv Hiv L E0)|].
      pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as K.
      destruct K as [[K|[K|K]]|K]; [left; exact K | lia | |].
      - destruct K as (q & u & len & Hq & _ & K1 & K2).
        pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
        destruct (sh_aapp_range _ _ BAPP Bn) as (_ & SX & _). lia.
      - unfold wfw in K. destruct K as [K|[K|K]]; [lia | lia | left; split; [lia | unfold AHI_LO in *; lia]]. }
    assert (BLO : forall p n, In (p, n) (state_blocks c) -> exists q, In (q, p, n) LB /\ 0 < p /\ p mod 16 = 0 /\ 0 <= n /\ p + n <= aceil /\ aapp p n
                         /\ (p + n + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= p - 16)).
    { intros p n Hin. destruct (lbl_in_inv _ _ _ (BL p n Hin)) as (q & Hq).
      pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
      exists q. repeat (split; [assumption|]). first [exact BF | split; [exact BAPP | exact BF]]. }

    assert (NXO : forall a, ff + 3504 <= a < ff + 3744 -> ~ rin_ivs X a).
    { intros a Ha. apply rin_ivs_none. apply Forall_forall. intros iv Hiv.
      destruct (XIN iv Hiv) as [(q & u & len & Hq & _ & K1 & K2)|K].
      - pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
        pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE u len F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) Bn). lia.
      - unfold wfw in K. lia. }
    assert (NXB : forall p n a, In (p, n) (state_blocks c) -> p <= a < p + n -> ~ rin_ivs X a).
    { intros p n a Hin Ha. apply rin_ivs_none. apply Forall_forall. intros iv Hiv.
      destruct (BLO p n Hin) as (q' & Hq' & P0 & P16 & Pn & PC & PAPP & PF).
      destruct (XIN iv Hiv) as [(q & u & len & Hq & _ & K1 & K2)|K].
      - pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
        pose proof (aapp_disjoint_sh p n u len PAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) Bn). lia.
      - unfold wfw in K. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in *. lia. }
    assert (NXS : forall p n a, In (p, n) (state_blocks c) -> sh p <= a < sh p + nsh n -> ~ rin_ivs X a).
    { intros p n a Hin Ha. apply rin_ivs_none. apply Forall_forall. intros iv Hiv.
      destruct (BLO p n Hin) as (q' & Hq' & P0 & P16 & Pn & PC & PAPP & PF).
      destruct (XIN iv Hiv) as [(q & u & len & Hq & NEQ & K1 & K2)|K]; cycle 1.
      { destruct (sh_aapp_range _ _ PAPP Pn) as (SA1 & SA2 & SA3).
        assert (SAT : 0x7fff8000 <= sh AIMG_TOP) by (unfold sh; rewrite ASHADOW_BASE_val; unfold AIMG_TOP; Z.div_mod_to_equations; lia).
        unfold wfw in K. destruct K as [K|[K|K]].
        - unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in *. lia.
        - unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in *. lia.
        - pose proof (sh_disj16 p n ff 4096 ltac:(lia) ltac:(clear - P16; Z.div_mod_to_equations; lia) Pn ltac:(unfold AIMG_TOP, AFS_HDR in *; lia)
                        ltac:(clear - F3; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold AFS_HDR in *; lia)) as D.
          change (nsh 4096) with 512 in D. lia. }
      pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
      assert (NE : q' <> q).
      { intros E. subst q'. pose proof (ah_nodup H HH _ _ _ RH) as ND.
        assert (EQ : (p, n) = (u, len)).
        { clear - ND Hq Hq'. induction LB as [|b LB IH]; [destruct Hq|]. cbn [map] in ND. inversion ND as [|? ? NI ND']; subst.
          destruct Hq as [->|Hq]; destruct Hq' as [E|Hq'].
          - injection E as <- <-. reflexivity.
          - exfalso. apply NI. apply in_map_iff. exists (q, p, n). split; [reflexivity | exact Hq'].
          - exfalso. apply NI. subst b. apply in_map_iff. exists (q, u, len). split; [reflexivity | exact Hq].
          - apply IH; assumption. }
        injection EQ as -> ->. exact (NEQ u len Hin eq_refl). }
      pose proof (ah_disj H HH _ _ _ (q', p, n) (q, u, len) RH Hq' Hq NE) as D. cbn in D.
      pose proof (sh_disj16 p n u len ltac:(lia) ltac:(clear - P16; Z.div_mod_to_equations; lia) Pn ltac:(lia)
                    ltac:(clear - B16; Z.div_mod_to_equations; lia) Bn D). lia. }
    split.
    - eapply (rep_keep H LB LB LB (wSP e) X m m' (ff + 3504) c R XP).
      + apply (objx_intro H). { left. lia. } intros a Ha _. exact (NXO a ltac:(lia)).
      + apply (blkx_intro H). intros p n Hin. split; [exact (BL p n Hin)|]. split; [exact (BL p n Hin)|].
        intros a Ha. exact (NXB p n a Hin Ha).
      + unfold AIMG_TOP. lia.
      + lia.
    - eapply (sh_keep H LB LB (wSP e) X m m' (ff + 3504) c R S XP).
      apply (blksh_intro H). intros p n Hin. split; [exact (BL p n Hin)|]. intros a Ha. exact (NXS p n a Hin Ha).
  Qed.

  Lemma wstate_ap : forall (e : went H) ff fp XSc s LB LB' m m' c,
    wpre H e -> winv H e ff fp XSc s LB m -> apres H LB (wS1 e) m m' ->
    (forall p n, In (p, n) (state_blocks c) -> In (p, n) (lbl LB) /\ In (p, n) (lbl LB')) ->
    state_repA LB m (ff + 3504) c -> state_sh m c -> state_repA LB' m' (ff + 3504) c /\ state_sh m' c.
  Proof.
    intros e ff fp XSc s LB LB' m m' c HP HI AP BL R S.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof aceil_facts as ACF.
    pose proof (xpres_of_apres H LB (wS1 e) [] m m' AP) as XP.
    split.
    - eapply (rep_keep H LB LB' LB (wS1 e) [] m m' (ff + 3504) c R XP).
      + apply (objx_intro H). { left. lia. } intros a _ _ [].
      + apply (blkx_intro H). intros p n Hin. destruct (BL p n Hin) as [L1 L2]. split; [exact L1|]. split; [exact L2|]. intros a _ [].
      + unfold AIMG_TOP. lia.
      + lia.
    - eapply (sh_keep H LB LB (wS1 e) [] m m' (ff + 3504) c R S XP).
      apply (blksh_intro H). intros p n Hin. split; [exact (proj1 (BL p n Hin))|]. intros a _ [].
  Qed.
End T2.
