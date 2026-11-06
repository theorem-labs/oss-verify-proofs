(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AYajlRep AYajl_iface AY_rz AY_hand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Definition ay_fnodup_stmt (Y : ay_params) : Prop :=
  forall s LB LF m mo, y_AHK Y s LB LF m mo -> List.NoDup (map snd LF).
(* [comment removed for export] *)
Definition ay_aflag_cell_stmt (Y : ay_params) : Prop :=
  forall s LB LF m mo f, y_AHK Y s LB LF m mo -> In f LF -> exists fl, rw_cells asegs m (y_aflag Y (fst f) (snd f)) [C1 fl].
(* [comment removed for export] *)
Definition yalloc_hand (hb lb db sb : yptr) (bb : nat) : yhandle :=
  mkHandle hb lb (mkLexer 0 0 LE_ok ybuf_zero bb 0 0 1 1) None 0 db ybuf_zero [ST_start] 128 (Some sb).
Definition yphi_new_alloc_stmt (Y : ay_params) : Prop :=
  forall L (hb lb db sb : yptr) (bb : nat), 0 <= L ->
    y_acharge Y 104 + y_acharge Y 48 + 2 * y_acharge Y 32 + y_acharge Y 128 + 4 * y_free_cost Y + 2 * y_phi_buf Y ybuf_zero
    + y_phi_hand Y (yalloc_hand hb lb db sb bb) L <= y_phi_new Y L.

Lemma ff_bytes_1 : ff_bytes 1 = 128. Proof. reflexivity. Qed.
Lemma oshw_hi_0 : oshw_hi 0 (2^47) = 17594333495296. Proof. reflexivity. Qed.
Lemma shl8_1 : Z.shiftl 8 1 = 16. Proof. reflexivity. Qed.

Lemma notin_map_snd : forall (LF : list fblock) N ff f, List.NoDup (map snd ((N, ff) :: LF)) -> In f LF -> snd f <> ff.
Proof. aceil.
  intros LF N ff f ND Hf E. cbn [map snd] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
  apply NI. rewrite <- E. apply in_map. exact Hf.
Qed.

Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. aceil. induction W1 as [|[u v] W1 IH]; intros; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma munch_app : forall W1 W2 m1 m2 m3, munch W1 m1 m2 -> munch W2 m2 m3 -> munch (W1 ++ W2) m1 m3.
Proof. aceil. intros W1 W2 m1 m2 m3 H1 H2 x Hx. apply outside_app in Hx. destruct Hx as [X1 X2]. rewrite (H2 x X2). apply H1, X1. Qed.

Lemma ay_client_addr_mono : forall REST LF LF' SP a, (forall f, In f LF -> In f LF') -> ay_client_addr REST LF SP a -> ay_client_addr REST LF' SP a.
Proof. aceil.
  intros REST LF LF' SP a HL Hc. destruct Hc as [Hc|[Hc|[(f & Hf & Hr)|Hc]]]; [left; exact Hc| right; left; exact Hc| | right; right; right; exact Hc].
  right; right; left. exists f. split; [apply HL; exact Hf| exact Hr].
Qed.

Lemma sub_chunk : forall m A cs1 cs2 cs3,
  rw_cells asegs m A (cs1 ++ cs2 ++ cs3) -> rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. aceil.
  intros m A cs1 cs2 cs3 H. apply (proj1 (ycells_app asegs _ _ cs1 (cs2 ++ cs3))) in H. destruct H as [_ H].
  apply (proj1 (ycells_app asegs _ _ cs2 cs3)) in H. destruct H as [H _]. exact H.
Qed.

Section W.
Variable Y : ay_params.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis AFLSEP : AHK_y_aflsep_stmt Y.

(* [comment removed for export] *)
Lemma ay_client_outside_fframe : forall s LB LF' m mo REST LF SP f lo hi a,
  y_AHK Y s LB LF' m mo -> In f LF' -> (forall g, In g LF -> In g LF' /\ snd g <> snd f) -> (forall b, In b REST -> In b LB) ->
  (snd f <= lo /\ hi <= snd f + ff_bytes (fst f) \/ oshw_lo (snd f) <= lo /\ hi <= oshw_lo (snd f) + Z.shiftl 8 (fst f)) ->
  lo < hi -> alloc_ceiling <= SP -> ay_client_addr REST LF SP a -> outside [(lo, hi)] a.
Proof. aceil.
  intros s LB LF' m mo REST LF SP f lo hi a AHK Hf HG HR HW Hlh HSP Hc. cbn. split; [| exact I].
  destruct (LAYY _ _ _ _ _ AHK) as (LAYF & LAYFB & LAYFF).
  destruct (LAYF _ Hf) as (L1 & L2 & L3 & L4 & L5 & L6).
  pose proof (ff_shadow_top2 f L4 ltac:(clear -CEILB L1; unfold amem in L1; lia) L2) as T. rewrite oshw_hi_0 in T.
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & SEP & ND).
  assert (EF : fst f = 0 \/ fst f = 1) by lia.
  assert (E8f : snd f = 8 * (snd f / 8)).
  { clear -CEILB L3 L4 EF. destruct EF as [EF|EF]; rewrite EF in L3; unfold ff_bytes in L3;
      [change (Z.shiftl 64 0) with 64 in L3| change (Z.shiftl 64 1) with 128 in L3]; Z.div_mod_to_equations; lia. }
  unfold oshw_lo, A_SB, amem in *; aceil. clear L5 L6 L3.
  destruct Hc as [Hc|[(b & Hb & Hr)|[(g & Hg & Hr)|Hc]]].
  - clear -CEILB L1 L2 T EF HW Hlh HSP Hc E8f.
    destruct EF as [EF|EF]; rewrite EF in *; unfold ff_bytes in *; [change (Z.shiftl 8 0) with 8 in *; change (Z.shiftl 64 0) with 64 in *| change (Z.shiftl 8 1) with 16 in *; change (Z.shiftl 64 1) with 128 in *]; lia.
  - destruct (LAYFB f b Hf (HR _ Hb)) as [D1 _].
    pose proof (BSHY _ _ _ _ _ b AHK (HR _ Hb)) as BS.
    pose proof (RNG _ (HR _ Hb)) as Rb. unfold ablock_range in Rb.
    assert (C : ab_size b <= 0 \/ 0 < ab_size b) by lia. destruct C as [C|C]; [lia|].
    destruct (BS C) as [_ B2]. unfold amem in B2. clear BS RNG SEP ND LAYF LAYFB LAYFF HG HR AHK.
    clear -CEILB L1 L2 T EF HW Hlh Hr D1 B2 Rb C E8f.
    destruct EF as [EF|EF]; rewrite EF in *; unfold ff_bytes in *; [change (Z.shiftl 8 0) with 8 in *; change (Z.shiftl 64 0) with 64 in *| change (Z.shiftl 8 1) with 16 in *; change (Z.shiftl 64 1) with 128 in *]; lia.
  - destruct (HG _ Hg) as [HgL NE].
    destruct (LAYF _ HgL) as (M1 & M2 & M3 & M4 & _ & _).
    pose proof (LAYFF _ _ HgL Hf NE) as D.
    pose proof (ff_shadow_top2 g M4 ltac:(clear -CEILB M1; unfold amem in M1; lia) M2) as Tg. rewrite oshw_hi_0 in Tg. unfold oshw_lo, A_SB in Tg.
    assert (EG : fst g = 0 \/ fst g = 1) by lia.
    unfold A_SB, amem in Hr, M1.
    assert (E8g : snd g = 8 * (snd g / 8)).
    { clear -CEILB M3 M4 EG. destruct EG as [EG|EG]; rewrite EG in M3; unfold ff_bytes in M3;
        [change (Z.shiftl 64 0) with 64 in M3| change (Z.shiftl 64 1) with 128 in M3]; Z.div_mod_to_equations; lia. }
    clear RNG SEP ND LAYF LAYFB LAYFF HG HR AHK M3.
    clear -CEILB L1 L2 T EF HW Hlh Hr M1 M2 Tg EG D E8g E8f.
    destruct EF as [EF|EF]; rewrite EF in *; destruct EG as [EG|EG]; rewrite EG in *; unfold ff_bytes in *;
      try change (Z.shiftl 8 0) with 8 in *; try change (Z.shiftl 64 0) with 64 in *; try change (Z.shiftl 8 1) with 16 in *; try change (Z.shiftl 64 1) with 128 in *;
      (destruct Hr as [Hr|Hr]; destruct HW as [HW|HW]; lia).
  - unfold ay_static in Hc. clear -CEILB L1 L2 T EF HW Hlh Hc E8f.
    destruct EF as [EF|EF]; rewrite EF in *; unfold ff_bytes in *; [change (Z.shiftl 8 0) with 8 in *; change (Z.shiftl 64 0) with 64 in *| change (Z.shiftl 8 1) with 16 in *; change (Z.shiftl 64 1) with 128 in *]; lia.
Qed.

(* [comment removed for export] *)
Lemma ay_client_outside_flag : forall s LB LF' m mo REST LF SP f a,
  y_AHK Y s LB LF' m mo -> In f LF' -> (forall g, In g LF -> In g LF' /\ snd g <> snd f) -> (forall b, In b REST -> In b LB) ->
  alloc_ceiling <= SP -> ay_client_addr REST LF SP a -> outside [(y_aflag Y (fst f) (snd f), y_aflag Y (fst f) (snd f) + 1)] a.
Proof. aceil.
  intros s LB LF' m mo REST LF SP f a AHK Hf HG HR HSP Hc. cbn. split; [| exact I].
  destruct (LAYY _ _ _ _ _ AHK) as (LAYF & LAYFB & LAYFF).
  destruct (LAYF _ Hf) as (L1 & L2 & L3 & L4 & L5 & L6). unfold amem in L1, L5.
  aceil.
  destruct Hc as [Hc|[(b & Hb & Hr)|[(g & Hg & Hr)|Hc]]].
  - clear -CEILB L5 L6 HSP Hc. lia.
  - destruct (LAYFB f b Hf (HR _ Hb)) as [_ D2]. clear -CEILB D2 Hr. lia.
  - destruct (HG _ Hg) as [HgL NE].
    pose proof (AFLSEP _ _ _ _ _ f g AHK Hf HgL ltac:(intros E; apply NE; symmetry; exact E)) as D.
    destruct (LAYF _ HgL) as (M1 & M2 & M3 & M4 & _ & _). unfold amem in M1.
    pose proof (ff_shadow_top2 g M4 ltac:(clear -CEILB M1; lia) M2) as Tg. rewrite oshw_hi_0 in Tg. unfold oshw_lo, A_SB in Tg.
    unfold A_SB in Hr. clear -CEILB L5 L6 D M1 M2 Tg Hr. destruct Hr as [Hr|Hr]; lia.
  - unfold ay_static in Hc. clear -CEILB L5 Hc. lia.
Qed.

End W.
End RC__1.
