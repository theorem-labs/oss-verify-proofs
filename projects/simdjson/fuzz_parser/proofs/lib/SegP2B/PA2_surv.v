(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec StoreOk AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLin SegTmpl SegGhost SegCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S.

Definition survivesQ (kn : list kentry) (PR : option (list SC.wn)) (K : kentry) : bool :=
  match K with
  | KWr a n | KUnk a n => SC.pres_in kn PR (a_base a) (a_off a) n
  | _ => SC.survivesP kn [] PR K
  end.

Definition incl_kn (l1 l2 : list kentry) : bool := forallb (fun k => existsb (APC.kentry_eqb k) l2) l1.

Section Sound.
Variable segs : list Segment.

Lemma addr_succ : forall a : Z, (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1).
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. rewrite Zplus_mod_idemp_l. f_equal.
Qed.

Lemma store_ok_ext : forall m (M1 M2 : word -> option byte) (a : Z),
  (forall i, 0 <= i < Z.of_nat m -> M2 (Z_to_bv 64 (a + i)) = M1 (Z_to_bv 64 (a + i))) ->
  store_ok segs M2 (Z_to_bv 64 a) m = store_ok segs M1 (Z_to_bv 64 a) m.
Proof.
  induction m as [|m IH]; intros M1 M2 a H; [reflexivity|].
  cbn [store_ok]. unfold wview. rewrite !addr_succ.
  assert (H0 : M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  assert (HS : forall i, 0 <= i < Z.of_nat m -> M2 (Z_to_bv 64 (a + 1 + i)) = M1 (Z_to_bv 64 (a + 1 + i)))
    by (intros i Hi; rewrite <- Z.add_assoc; apply H; lia).
  rewrite H0. destruct (M1 (Z_to_bv 64 a)) as [b|]; [exact (IH M1 M2 (a + 1) HS)|].
  match goal with |- context [find_segment ?S ?A ?N] => destruct (find_segment S A N) as [sg|]; [|reflexivity] end.
  destruct (seg_writable sg); [|reflexivity].
  destruct (segment_byte_at _ _); [|reflexivity].
  exact (IH M1 M2 (a + 1) HS).
Qed.

Lemma survivesQ_ok : forall E M1 M2 kn PR K,
  know_ok segs E M1 kn ->
  (forall x : word, SC.in_PR E PR (bv_unsigned x) -> M2 x = M1 x) ->
  kentry_ok segs E M1 K -> survivesQ kn PR K = true -> kentry_ok segs E M2 K.
Proof.
  intros E M1 M2 kn PR K HK FR HK1 Hs.
  assert (OUTR : forall b k n, SC.pres_in kn PR b k n = true -> flat E (SA b k) (elenZ E n) ->
            forall i, 0 <= i < elenZ E n -> M2 (Z_to_bv 64 (estart E (SA b k) + i)) = M1 (Z_to_bv 64 (estart E (SA b k) + i))).
  { intros b k n Hp Hfl i Hi. apply FR.
    rewrite u_small by (destruct Hfl as (?&?&?&?); lia). apply (SC.pres_in_ok segs E M1 kn PR b k n HK Hp). lia. }
  destruct K as [[kb kk] w v|[kb kk] n|[kb kk] n bk|lo hi|ae am|re rlo rhi|[wb wk] wn0|da1 dn1 da2 dn2|[kb kk] n fc|[kb kk] n];
    cbn [survivesQ SC.survivesP SC.win_apart forallb kentry_ok a_base a_off andb] in Hs, HK1 |- *.
  - (* [comment removed for export] *) remember (Nat.leb w 8) as c eqn:Hc. destruct c; [|cbn in Hs; discriminate].
    symmetry in Hc. apply Nat.leb_le in Hc. destruct HK1 as (Hw & Hfl & Hrd).
    split; [exact Hw|]. split; [exact Hfl|]. rewrite <- Hrd. apply rdn_ext.
    + rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
    + intros x Hx. rewrite (flat_u E _ _ Hfl) in Hx. apply FR.
      apply (SC.pres_in_ok segs E M1 kn PR kb kk (elen w) HK Hs). rewrite elenZ_elen by exact Hc. lia.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUTR kb kk n Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) destruct HK1 as (Hfl & Hl & Hz). split; [exact Hfl|]. split; [exact Hl|].
    intros i Hi. rewrite (OUTR kb kk n Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) remember (Z.ltb (hi - lo) (2^64)) as c eqn:Hc. destruct c; [|cbn in Hs; discriminate].
    symmetry in Hc. apply Z.ltb_lt in Hc. destruct HK1 as (Hlo & Hhi & Hn).
    split; [exact Hlo|]. split; [exact Hhi|]. intros i Hi.
    assert (E0 : estart E (SA (ELit 0) lo) = lo) by (unfold estart; cbn [a_base a_off edenot]; rewrite Z_to_bv_unsigned; reflexivity).
    assert (E1 : elenZ E (ELit (hi - lo)) = hi - lo)
      by (unfold elenZ; cbn [edenot]; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; apply Z.mod_small; lia).
    rewrite FR; [apply Hn; exact Hi|].
    rewrite u_small by lia. apply (SC.pres_in_ok segs E M1 kn PR (ELit 0) lo (ELit (hi - lo)) HK Hs). rewrite E0, E1. lia.
  - exact HK1.
  - exact HK1.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hs0]. split; [exact Hfl|]. intros d m Hd Hm.
    rewrite (store_ok_ext m M1 M2); [apply Hs0; assumption|]. intros i Hi.
    rewrite <- Z.add_assoc. apply (OUTR wb wk wn0 Hs Hfl). lia.
  - exact HK1.
  - (* [comment removed for export] *) remember (SC.pres_in kn PR kb kk n) as c eqn:Ha. destruct c; [|cbn in *; discriminate]. symmetry in Ha.
    destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUTR kb kk n Ha Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUTR kb kk n Hs Hfl i Hi). apply Hz. exact Hi.
Qed.

Lemma survivesQ_all_ok : forall E M1 M2 kn PR,
  know_ok segs E M1 kn ->
  (forall x : word, SC.in_PR E PR (bv_unsigned x) -> M2 x = M1 x) ->
  know_ok segs E M2 (List.filter (survivesQ kn PR) kn).
Proof.
  intros E M1 M2 kn PR HK FR. unfold know_ok. apply Forall_forall. intros K HKin. apply filter_In in HKin as [HKin Hs].
  exact (survivesQ_ok E M1 M2 kn PR K HK FR (proj1 (Forall_forall _ _) HK K HKin) Hs).
Qed.

Lemma know_ok_incl : forall E M l1 l2, know_ok segs E M l2 -> incl_kn l1 l2 = true -> know_ok segs E M l1.
Proof.
  intros E M l1 l2 H2 H. unfold know_ok. apply Forall_forall. intros K HK. unfold incl_kn in H.
  pose proof (proj1 (forallb_forall _ _) H K HK) as Hx. apply existsb_exists in Hx as (K' & HK' & Heq).
  apply APS.kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) H2 K HK').
Qed.
End Sound.
