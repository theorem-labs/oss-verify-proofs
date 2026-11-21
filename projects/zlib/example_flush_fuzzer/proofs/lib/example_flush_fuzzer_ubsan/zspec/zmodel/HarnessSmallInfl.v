(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb ModelRel
  InflateInv InflateInvRun InflateInvTab InflateInvKit InflateInvApi InflateInvLoop InflateInvCall
  Deflate DeflateInvKeep BoundArith HarnessKit HarnessSmall HarnessFacts HarnessSmallStages HarnessSmallFacts InflateLeave InflateRc InflateCall.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma init_u16_range : forall g b i, 0 <= init_u16 g b i < 2 ^ 16.
Proof. intros. unfold init_u16. pose proof (wrap8_range (g (b + 2 * i))). pose proof (wrap8_range (g (b + 2 * i + 1))). lia. Qed.
Lemma init_u32_range : forall g b i, 0 <= init_u32 g b i < 2 ^ 32.
Proof. intros. unfold init_u32. pose proof (init_u16_range g b (2 * i)). pose proof (init_u16_range g b (2 * i + 1)). lia. Qed.
Lemma init_u64_range : forall g b i, 0 <= init_u64 g b i < 2 ^ 64.
Proof. intros. unfold init_u64. pose proof (init_u32_range g b (2 * i)). pose proof (init_u32_range g b (2 * i + 1)). lia. Qed.

Lemma arr_get_u16of : forall g o n i, arr_get (iarr_u16_of g o n) i = init_u16 g o i.
Proof. intros. unfold iarr_u16_of. apply arr_get_init. Qed.
Lemma arr_get_u32of : forall g o n i, arr_get (iarr_u32_of g o n) i = init_u32 g o i.
Proof. intros. unfold iarr_u32_of. apply arr_get_init. Qed.

Definition ist0 (g : Z -> Z) (b : blk) : inflate_state :=
  Eval lazy -[init_u32 init_u64 init_u16 iarr_u16_of iarr_u32_of swrap32 arr_make] in (fst (iinit_state ivar_ref g b zstrm0)).

Lemma iinit_eq : forall g b z, fst (iinit_state ivar_ref g b z) = ist0 g b.
Proof. intros. reflexivity. Qed.

Lemma UR_ist0 : forall g b, UR (ist0 g b).
Proof.
  intros. unfold UR, SRNGq, ist0.
  cbn -[init_u32 init_u64 init_u16 iarr_u16_of iarr_u32_of swrap32 Z.pow Z.le Z.lt arr_len arr_get ARRB arr_make].
  pose proof (init_u64_range g 32 0).
  pose proof (init_u32_range g 92 0). pose proof (init_u32_range g 96 0). pose proof (init_u32_range g 100 0).
  pose proof (init_u32_range g 120 0). pose proof (init_u32_range g 124 0). pose proof (init_u32_range g 128 0).
  pose proof (init_u32_range g 132 0). pose proof (init_u32_range g 136 0). pose proof (init_u32_range g 140 0).
  pose proof (init_u32_range g 7152 0).
  unfold HEAD, SYNC.
  repeat match goal with |- _ /\ _ => split end.
  all: try lia.
  all: first [ unfold ARRB; split; [| split]; intros i Hi; first [rewrite arr_get_u16of; apply init_u16_range | rewrite arr_get_u32of; apply init_u32_range]
             | intros i Hi; rewrite arr_len_make in Hi; lia
             | rewrite arr_len_make; reflexivity ].
Qed.

Lemma UR_iinit : forall g b z, UR (fst (iinit_state ivar_ref g b z)).
Proof. intros. rewrite iinit_eq. apply UR_ist0. Qed.

Theorem UI_iinit : forall g b z, UI (fst (iinit_state ivar_ref g b z)).
Proof.
  intros g b z. split; [apply UR_iinit|].
  unfold iinit_state.
  destruct (inflateReset ivar_ref (iset_wbits (iset_wrap (iinit_pre ivar_ref g b) 5) 15) z) as [[s' z'] rc] eqn:E.
  assert (RC : rc = Z_OK).
  { apply (f_equal snd) in E. cbn [snd] in E. rewrite <- E. reflexivity. }
  cbn [fst].
  pose proof (is_of_oracle_lens (iv_lay ivar_ref) g b) as (L1 & L2 & L3).
  exact (reset_ok ivar_ref _ z s' z' rc E RC ltac:(exact L1) ltac:(exact L2) ltac:(exact L3)).
Qed.

Corollary UI_is0 : forall kI, UI (is0 kI).
Proof. intros kI. unfold is0. apply UI_iinit. Qed.



Section LOOP.
  Variable compr : arr.
  Variable n : Z.
  Hypothesis Hn : 1 <= n <= 2 ^ 20.
  Hypothesis Hlen : arr_len compr = cb n.
  Hypothesis Hcb : u8a compr.


  Record II (s : inflate_state) (c : czs) (unc : arr) : Prop := MkII {
    ii_ui : UI s;
    ii_zs : zret_ok (mkZRet 0 [] (cz_z c) Z_OK);
    ii_in : cz_next_in c = zs_total_in (cz_z c);
    ii_out : cz_next_out c = zs_total_out (cz_z c);
    ii_inle : 0 <= cz_next_in c <= cb n;
    ii_outle : 0 <= cz_next_out c <= n;
    ii_len : arr_len unc = n }.




End LOOP.
