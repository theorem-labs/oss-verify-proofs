(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_SR LbB_Conv LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoSt LbB_WoR2 LbB_WoE0.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Cut.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Definition wpst (ff : Z) (m : mem) (v1 v2 v3 : list cell) : Prop :=
    rw_cells asegs m (ff + 3504) [CB 46 (poison_bytes 46 0)] /\ st_maps_cells m (ff + 3504)
    /\ rw_cells asegs m (ff + 3672) v1 /\ rw_cells asegs m (ff + 3696) v2 /\ rw_cells asegs m (ff + 3720) v3.

  Definition wtst (ff : Z) (m : mem) (words n : Z) (v1 v2 v3 : list cell) : Prop :=
    rw_cells asegs m (ff + 2752) [C8 (Z_to_bv 64 words); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m (ff + 2776) [CB 22 (poison_bytes 22 0)] /\ st_maps_cells m (ff + 2752)
    /\ rw_cells asegs m (ff + 2920) v1 /\ rw_cells asegs m (ff + 2944) v2 /\ rw_cells asegs m (ff + 2968) v3.

  Definition wblk (m : mem) (b n : Z) : Prop := wr_at asegs m b n /\ SHAD m b (cc_gen n 0).

  Definition v24 (v : list cell) : Prop := cells_size v = 24%nat.

  Ltac djw :=
    let K := fresh "K" in
    lazymatch goal with
    | |- disjoint_from ?W ?A ?n =>
      match goal with FW : Forall _ W |- _ =>
        clear - FW; induction W as [|[x y] W IH]; cbn; [exact I|];
        inversion FW as [|? ? K ?]; subst; cbn in K; split; [lia | apply IH; assumption] end
    end.

  Lemma wpst_munch : forall ff m m' W v1 v2 v3, wpst ff m v1 v2 v3 -> munch W m m' -> wmono asegs m m' ->
    v24 v1 -> v24 v2 -> v24 v3 ->
    Forall (fun iv : Z * Z => snd iv <= ff + 3504 \/ ff + 3744 <= fst iv) W -> wpst ff m' v1 v2 v3.
  Proof.
    intros ff m m' W v1 v2 v3 (C0 & (M1 & F1 & M2 & F2 & M3 & F3) & V1 & V2 & V3) MU WM S1 S2 S3 FW.
    unfold v24 in *.
    assert (DJ : forall A n, ff + 3504 <= A -> A + n <= ff + 3744 -> disjoint_from W A n).
    { intros A n X1 X2. clear - FW X1 X2. induction W as [|[x y] W IH]; cbn; [exact I|].
      inversion FW as [|? ? K K2]; subst. cbn in K. split; [lia | apply IH; exact K2]. }
    split; [eapply rw_cells_transport; [exact C0 | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [unfold st_maps_cells; repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply DJ; cbn; lia])|].
    split; [eapply rw_cells_transport; [exact V1 | exact MU | exact WM | apply DJ; rewrite ?S1; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact V2 | exact MU | exact WM | apply DJ; rewrite ?S2; cbn; lia]|].
    eapply rw_cells_transport; [exact V3 | exact MU | exact WM | apply DJ; rewrite ?S3; cbn; lia].
  Qed.

  Lemma wtst_munch : forall ff m m' W words n v1 v2 v3, wtst ff m words n v1 v2 v3 -> munch W m m' -> wmono asegs m m' ->
    v24 v1 -> v24 v2 -> v24 v3 ->
    Forall (fun iv : Z * Z => snd iv <= ff + 2752 \/ ff + 2992 <= fst iv) W -> wtst ff m' words n v1 v2 v3.
  Proof.
    intros ff m m' W words n v1 v2 v3 (C0 & C1 & (M1 & F1 & M2 & F2 & M3 & F3) & V1 & V2 & V3) MU WM S1 S2 S3 FW.
    unfold v24 in *.
    assert (DJ : forall A k, ff + 2752 <= A -> A + k <= ff + 2992 -> disjoint_from W A k).
    { intros A k X1 X2. clear - FW X1 X2. induction W as [|[x y] W IH]; cbn; [exact I|].
      inversion FW as [|? ? K K2]; subst. cbn in K. split; [lia | apply IH; exact K2]. }
    split; [eapply rw_cells_transport; [exact C0 | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C1 | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [unfold st_maps_cells; repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply DJ; cbn; lia])|].
    split; [eapply rw_cells_transport; [exact V1 | exact MU | exact WM | apply DJ; rewrite ?S1; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact V2 | exact MU | exact WM | apply DJ; rewrite ?S2; cbn; lia]|].
    eapply rw_cells_transport; [exact V3 | exact MU | exact WM | apply DJ; rewrite ?S3; cbn; lia].
  Qed.

  Lemma wblk_munch : forall m m' W b n, wblk m b n -> munch W m m' -> wmono asegs m m' -> 0 <= n ->
    Forall (fun iv : Z * Z => (snd iv <= sh b \/ sh b + nsh n <= fst iv)) W -> wblk m' b n.
  Proof.
    intros m m' W b n (WR & SB) MU WM Hn FW. split; [exact (wr_at_wmono _ _ _ _ WR WM)|].
    eapply SHAD_transport; [exact SB | exact MU | exact WM |]. rewrite cc_gen_length by lia.
    clear - FW. induction W as [|[x y] W IH]; cbn; [exact I|].
    inversion FW as [|? ? K K2]; subst. cbn in K. split; [lia | apply IH; exact K2].
  Qed.

  Lemma wpst_apres : forall e ff fp XSc sk LBk LB m m' v1 v2 v3, wpre H e -> winv H e ff fp XSc sk LBk m ->
    wpst ff m v1 v2 v3 -> apres H LB (wS1 e) m m' -> v24 v1 -> v24 v2 -> v24 v3 -> wpst ff m' v1 v2 v3.
  Proof.
    intros e ff fp XSc sk LBk LB m m' v1 v2 v3 HP HI (C0 & (M1 & F1 & M2 & F2 & M3 & F3) & V1 & V2 & V3) AP S1 S2 S3.
    unfold v24 in *.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (FF1 & FF2 & FF3 & FF4 & FF5 & FF6 & FF7 & _).
    assert (CL : forall A k, ff <= A -> A + k <= ff + 4096 -> aclient_range H LB (wS1 e) A k).
    { intros A k X1 X2. right; right; right; right; left. lia. }
    split; [eapply (apres_rw_cells H); [exact AP | exact C0 | apply CL; cbn; lia]|].
    split; [unfold st_maps_cells; repeat split; (eapply (apres_rw_cells H); [exact AP | eassumption | apply CL; cbn; lia])|].
    split; [eapply (apres_rw_cells H); [exact AP | exact V1 | apply CL; rewrite ?S1; cbn; lia]|].
    split; [eapply (apres_rw_cells H); [exact AP | exact V2 | apply CL; rewrite ?S2; cbn; lia]|].
    eapply (apres_rw_cells H); [exact AP | exact V3 | apply CL; rewrite ?S3; cbn; lia].
  Qed.

  Lemma wtst_apres : forall e ff fp XSc sk LBk LB m m' words n v1 v2 v3, wpre H e -> winv H e ff fp XSc sk LBk m ->
    wtst ff m words n v1 v2 v3 -> apres H LB (wS1 e) m m' -> v24 v1 -> v24 v2 -> v24 v3 -> wtst ff m' words n v1 v2 v3.
  Proof.
    intros e ff fp XSc sk LBk LB m m' words n v1 v2 v3 HP HI (C0 & C1 & (M1 & F1 & M2 & F2 & M3 & F3) & V1 & V2 & V3) AP Sz1 Sz2 Sz3.
    unfold v24 in *.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (FF1 & FF2 & FF3 & FF4 & FF5 & FF6 & FF7 & _).
    assert (CL : forall A k, ff <= A -> A + k <= ff + 4096 -> aclient_range H LB (wS1 e) A k).
    { intros A k X1 X2. right; right; right; right; left. lia. }
    split; [eapply (apres_rw_cells H); [exact AP | exact C0 | apply CL; cbn; lia]|].
    split; [eapply (apres_rw_cells H); [exact AP | exact C1 | apply CL; cbn; lia]|].
    split; [unfold st_maps_cells; repeat split; (eapply (apres_rw_cells H); [exact AP | eassumption | apply CL; cbn; lia])|].
    split; [eapply (apres_rw_cells H); [exact AP | exact V1 | apply CL; rewrite ?Sz1; cbn; lia]|].
    split; [eapply (apres_rw_cells H); [exact AP | exact V2 | apply CL; rewrite ?Sz2; cbn; lia]|].
    eapply (apres_rw_cells H); [exact AP | exact V3 | apply CL; rewrite ?Sz3; cbn; lia].
  Qed.

  Lemma wblk_apres : forall LB SP m m' p b n, wblk m b n -> apres H LB SP m m' -> In (p, b, n) LB -> 0 <= n -> wblk m' b n.
  Proof.
    intros LB SP m m' p b n (WR & SB) AP IN Hn. split.
    - eapply (apres_wr_at H); [exact AP | exact WR | eapply (aclient_range_block H); [exact IN | lia | lia]].
    - eapply (apres_SHAD H); [exact AP | exact SB |]. rewrite cc_gen_length by lia. eapply (aclient_range_block_sh H). exact IN.
  Qed.

  Lemma wfc_apres : forall e ff fp XSc sk LBk LB m m', wpre H e -> winv H e ff fp XSc sk LBk m ->
    wfc H e ff m -> apres H LB (wS1 e) m m' -> wfc H e ff m'.
  Proof.
    intros e ff fp XSc sk LBk LB m m' HP HI W AP.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (FF1 & FF2 & FF3 & FF4 & FF5 & FF6 & FF7 & FF8 & FF9 & FF10 & FF11 & FF12 & FF13 & _).
    assert (CL : forall A k, ff <= A -> A + k <= ff + 4096 -> aclient_range H LB (wS1 e) A k).
    { intros A k X1 X2. right; right; right; right; left. lia. }
    assert (CS : forall A k, wS1 e <= A -> aclient_range H LB (wS1 e) A k) by (intros A k X; left; exact X).
    unfold wfc in W |- *.
    repeat lazymatch type of W with _ /\ _ => let C := fresh "C" in destruct W as [C W] end.
    repeat lazymatch goal with |- _ /\ _ => split end.
    all: first [ eapply (apres_rw_cells H); [exact AP | eassumption | first [apply CS; lia | apply CL; cbn; lia]]
               | eapply (apres_u8arr H); [exact AP | eassumption | right; right; right; right; right; left; rewrite length_map; cbn; lia] ].
  Qed.
End Cut.
