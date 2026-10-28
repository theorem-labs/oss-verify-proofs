(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_DStat.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma rin_ivs_none' : forall X a, Forall (fun iv : Z * Z => a < fst iv \/ snd iv <= a) X -> ~ rin_ivs X a.
Proof.
  induction X as [|iv X IH]; intros a F; cbn; [tauto|]. inversion F as [|? ? F1 F2]; subst.
  intros [K|K]; [lia| exact (IH a F2 K)].
Qed.
Lemma rin_ivs_above : forall X a b, Forall (fun iv : Z * Z => b <= fst iv) X -> a < b -> ~ rin_ivs X a.
Proof. intros X a b F Hab. apply rin_ivs_none'. eapply Forall_impl; [| exact F]. intros iv K. cbn beta in K. left. lia. Qed.
Lemma outside_above : forall (W : list (Z * Z)) a b, Forall (fun iv : Z * Z => b <= fst iv) W -> a < b -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a b F Hab; [exact I|]. cbn [outside]. pose proof (Forall_inv F) as F1. cbn in F1.
  split; [lia | exact (IH a b (Forall_inv_tail F) Hab)].
Qed.

Lemma aimg_client_below : forall a, aimg_client a -> 0 <= a < AIMG_TOP.
Proof. intros a K. unfold aimg_client, AIMG_TOP in *. lia. Qed.

Lemma LINV_P5_munch_hi : forall (W : list (Z * Z)) m m', LINV_P5 m -> munch W m m' ->
  Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV_P5 m'.
Proof.
  intros W m m' LV MU FW. eapply LINV_P5_cl; [exact LV|]. intros a Ha Hc. unfold wa. apply MU.
  rewrite unsigned_lit by exact Ha. eapply outside_above; [exact FW | exact (proj2 (aimg_client_below a Hc))].
Qed.

Section K.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma LINV_P5_xpres_hi : forall LB SP X m m', LINV_P5 m -> xpres H LB SP X m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) X -> LINV_P5 m'.
  Proof.
    intros LB SP X m m' LV XP FX. eapply LINV_P5_cl; [exact LV|]. intros a Ha Hc.
    apply XP; [exact Ha|]. split; [right; left; exact Hc|].
    eapply rin_ivs_above; [exact FX | exact (proj2 (aimg_client_below a Hc))].
  Qed.

  Lemma fs_scratch_above : forall LF m iv, as_RFS H LF m -> fs_scratch H LF iv -> AIMG_TOP <= fst iv.
  Proof.
    intros LF m iv RFS SC. pose proof (ah_RFS_range H HH _ _ RFS) as [(F1 & F2 & F3 & F4) _].
    destruct SC as [-> | (k & ff & fp & FF & E)]; [cbn; unfold AFS_FLAGS, AFS_SIZE in *; lia|].
    pose proof (fresh_frame_facts H _ _ _ _ FF) as (Kk & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
    destruct E as [-> | [-> | ->]]; cbn [fst snd]; [lia | lia |].
    pose proof (sh_mono AIMG_TOP ff ltac:(lia)) as SM.
    unfold sh, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
  Qed.

End K.
