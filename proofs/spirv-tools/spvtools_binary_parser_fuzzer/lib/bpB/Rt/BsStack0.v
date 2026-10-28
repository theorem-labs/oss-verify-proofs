(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsIface BsCXXHeap BXXRep.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition stack0 (m : mem) (lo hi : Z) : Prop :=
  exists g, aceil <= g <= lo /\ lo <= hi <= AAPP_HI /\ (hi - g) mod 8 = 0 /\ addressable m g (hi - g).

Definition stack0_ok (iv : Z * Z) : Prop := AHI_LO <= fst iv \/ snd iv <= sh aceil.

Lemma stack0_bounds : forall m lo hi, stack0 m lo hi -> aceil <= lo /\ lo <= hi <= AAPP_HI.
Proof. intros m lo hi (g & H1 & H2 & _). lia. Qed.

Lemma stack0_read0 : forall m lo hi a w x,
  stack0 m lo hi -> lo <= a -> 1 <= w -> a + w <= hi -> x = wa (sh a) ->
  ov_read_bytes asegs m x 1 = Some [b8 0].
Proof.
  intros m lo hi a w x (g & H1 & H2 & H3 & AD) Hlo Hw Hhi ->.
  eapply (addressable_read0_w m g (hi - g) a w); [exact AD| lia| lia| | reflexivity].
  replace (8 * ((hi - g) / 8)) with (hi - g) by (Z.div_mod_to_equations; nia). lia.
Qed.

Lemma stack0_accessible : forall m lo hi a n,
  stack0 m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> accessible m a n.
Proof.
  intros m lo hi a n (g & H1 & H2 & H3 & AD) ? ? ?. eapply addressable_accessible; [exact AD| lia| lia| lia].
Qed.

Lemma stack0_in_app_mem : forall m lo hi a b,
  stack0 m lo hi -> lo <= a -> b + 8 <= hi -> in_app_mem a b.
Proof. intros m lo hi a b (g & H1 & H2 & _) ? ?. right. acb; unfold AHI_LO in *. lia. Qed.

Lemma stack0_stk : forall m lo hi, stack0 m lo hi -> exists g, aceil <= g <= lo /\ g mod 8 = 0 /\ stk asegs m (sh g) (sh hi).
Proof.
  intros m lo hi (g & H1 & H2 & H3 & [Hn SH]). exists g. pose proof (SHAD_aligned _ _ _ SH) as [G0 G8].
  split; [lia|]. split; [exact G8|].
  pose proof (stk_of_rw_cells asegs m _ _ (SHAD_rw_cells _ _ _ SH)) as K. cbn [cells_size csize Nat.add] in K.
  rewrite Nat.add_0_r, shadow_of_length in K by lia.
  replace (sh g + nsh (hi - g)) with (sh hi) in K; [exact K|].
  unfold nsh. rewrite (sh_rel g hi G8) by lia. Z.div_mod_to_equations. nia.
Qed.

Lemma stack0_shvis : forall m lo hi a b,
  stack0 m lo hi -> lo + 64 <= a -> a <= b -> b + 64 <= hi -> shvis m a b.
Proof.
  intros m lo hi a b ST Ha Hab Hb. pose proof (stack0_bounds _ _ _ ST) as [B1 B2]. acb.
  destruct (stack0_stk _ _ _ ST) as (g & G1 & G8 & K). unfold shvis.
  pose proof (hull_lo_le a ltac:(lia)) as (L1 & L2 & L3). pose proof (hull_hi_ge b ltac:(lia)) as (R1 & R2 & R3).
  destruct K as (K0 & K1 & K). split; [pose proof (sh_mono g (hull_lo a) ltac:(lia)); lia|].
  split; [pose proof (sh_mono (hull_hi b) hi ltac:(lia)); lia|].
  intros x Hx. apply K. pose proof (sh_mono g (hull_lo a) ltac:(lia)). pose proof (sh_mono (hull_hi b) hi ltac:(lia)). lia.
Qed.

Lemma stack0_ok_disjoint : forall W g n, Forall stack0_ok W -> aceil <= g -> 0 <= n -> g + n <= AAPP_HI ->
  disjoint_from W (sh g) (nsh n).
Proof.
  induction W as [|[l h] W IH]; intros g n HW Hg Hn Hhi; cbn; [exact I|].
  pose proof (Forall_inv HW) as H1. cbn in H1. unfold stack0_ok in H1. cbn in H1.
  pose proof (sh_nsh_high g n ltac:(acb; lia) Hn Hhi) as T.
  pose proof (sh_mono aceil g Hg) as U.
  split; [lia| apply IH; [exact (Forall_inv_tail HW)| lia| lia| lia]].
Qed.

Lemma stack0_transport : forall W m m' lo hi,
  stack0 m lo hi -> munch W m m' -> wmono asegs m m' -> Forall stack0_ok W -> stack0 m' lo hi.
Proof.
  intros W m m' lo hi (g & H1 & H2 & H3 & AD) MU WM HW. exists g. split; [lia|]. split; [lia|]. split; [exact H3|].
  eapply addressable_transport; [exact AD| exact MU| exact WM|]. apply stack0_ok_disjoint; [exact HW| lia| lia| lia].
Qed.

Lemma stack0_ok_app : forall l h, AHI_LO <= l -> stack0_ok (l, h).
Proof. intros l h H. left. exact H. Qed.

Lemma stack0_ok_aapp : forall A n l h, aapp A n -> A <= l -> h <= A + n -> stack0_ok (l, h).
Proof.
  intros A n l h AP Hl Hh. destruct AP as [[P1 P2]|[P1 P2]]; [right| left]; cbn; [| lia].
  acb. unfold sh, ALOWSH_LO in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
Qed.

Lemma stack0_ok_sh : forall A n, 0 <= A -> 0 <= n -> A + n <= aceil -> stack0_ok (sh A, sh A + nsh n).
Proof.
  intros A n HA Hn Hhi. right. cbn. unfold nsh.
  unfold sh. acb. Z.div_mod_to_equations. nia.
Qed.

Section X.
  Variable H : asr.

  Lemma stack0_xpres : forall LB SP X m m' lo hi,
    xpres H LB SP X m m' -> stack0 m lo hi -> Forall stack0_ok X -> stack0 m' lo hi.
  Proof.
    intros LB SP X m m' lo hi XP (g & H1 & H2 & H3 & [Hn (G0 & G8 & [UB UW])]) HX.
    assert (CL : xclient_range H LB SP X (sh g) (nsh (hi - g))).
    { split.
      - right; right; right; right; right; right. pose proof (sh_mono aceil g (proj1 H1)).
        pose proof (sh_nsh_high g (hi - g) G0 ltac:(lia) ltac:(lia)). lia.
      - eapply Forall_impl; [| exact HX]. intros [l h] K. cbn. unfold stack0_ok in K. cbn in K.
        pose proof (sh_mono aceil g (proj1 H1)). pose proof (sh_nsh_high g (hi - g) G0 ltac:(lia) ltac:(lia)). lia. }
    exists g. split; [lia|]. split; [lia|]. split; [exact H3|]. split; [exact Hn|]. split; [exact G0|]. split; [exact G8|].
    rewrite <- (shadow_of_length (hi - g)) in CL by lia. split.
    - eapply xpres_bytes_at; [exact XP| exact UB| exact CL].
    - eapply xpres_wr_at; [exact XP| exact UW| exact CL].
  Qed.
End X.

End HCW.

