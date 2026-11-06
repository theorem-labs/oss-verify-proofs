(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib ShapeLaws.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec ShapeLawsX Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib MallocDefs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots SymPlanSoundA SymPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section G.
Variable RSEGS : list Segment.
Local Abbreviation slots_ok := (SSL.slots_ok RSEGS) (only parsing).
Local Abbreviation slot_ok_agree := (SSL.slot_ok_agree RSEGS) (only parsing).
Local Abbreviation slots_keep_sound := (SSL.slots_keep_sound RSEGS) (only parsing).
Local Abbreviation slots_ok_ext := (SSL.slots_ok_ext RSEGS) (only parsing).
Local Abbreviation cs_ok := (SPSA.cs_ok RSEGS) (only parsing).
Local Abbreviation kentry_keep_sem := (SPS.kentry_keep_sem RSEGS) (only parsing).
Local Abbreviation know_ok_havoc := (SPS.know_ok_havoc RSEGS) (only parsing).
Local Abbreviation know_ok_ext := (SPS.know_ok_ext RSEGS) (only parsing).
Variable nx0 : N.
Hypothesis nx0_pos : nx0_okP nx0.

(* [comment removed for export] *)
Definition inr (lo n : Z) (x : word) : bool := (Z.leb lo (bv_unsigned x) && Z.ltb (bv_unsigned x) (lo + n))%bool.

Lemma inr_spec : forall lo n x, inr lo n x = true <-> (lo <= bv_unsigned x < lo + n)%Z.
Proof.
  intros lo n x. unfold inr. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma inr_false : forall lo n x, inr lo n x = false <-> ~ (lo <= bv_unsigned x < lo + n)%Z.
Proof.
  intros lo n x. rewrite <- inr_spec. destruct (inr lo n x); split; congruence.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rng_lo (E : env) (r : expr * Z * expr) : Z := match r with (b, o, n) => estart E (SA b o) end.
Definition rng_len (E : env) (r : expr * Z * expr) : Z := match r with (b, o, n) => elenZ E n end.

Fixpoint inrs (E : env) (rs : list (expr * Z * expr)) (x : word) : bool :=
  match rs with
  | [] => false
  | r :: rest => inr (rng_lo E r) (rng_len E r) x || inrs E rest x
  end.

(* [comment removed for export] *)
Fixpoint slots_keeps (k : list kentry) (rs : list (expr * Z * expr)) (ss : list sslot) : list sslot :=
  match rs with
  | [] => ss
  | (b, o, n) :: rest => slots_keeps k rest (slots_keep k b o n ss)
  end.

(* [comment removed for export] *)
Lemma know_ok_memeq : forall E M M' k,
  (forall x : word, M' x = M x) -> know_ok RSEGS E M k -> know_ok RSEGS E M' k.
Proof.
  intros E M M' k EQ HK. unfold know_ok in *. apply Forall_forall. intros K HinK.
  pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
  eapply (kentry_keep_sem E M M' K (match kfoot E K with Some (s, l) => s + l | None => 0 end) 0);
    [exact HKK | unfold kfoot_apart; destruct (kfoot E K) as [[s l]|]; [lia | exact I] | intros x _; apply EQ].
Qed.

Lemma slots_ok_memeq : forall E M M' ss,
  (forall x : word, M' x = M x) -> slots_ok E M ss -> slots_ok E M' ss.
Proof.
  intros E M M' ss EQ HS. unfold slots_ok in *. apply Forall_forall. intros s Hin.
  eapply slot_ok_agree; [exact (proj1 (Forall_forall _ _) HS s Hin) | intros x _ _; apply EQ].
Qed.

(* [comment removed for export] *)
Lemma havocs_frame : forall E rs M0 k0 M M',
  know_ok RSEGS E M0 k0 ->
  (forall x : word, inrs E rs x = false -> M' x = M x) ->
  mem_grows M M' ->
  (forall k, know_ok RSEGS E M k -> know_ok RSEGS E M' (kn_havocs k rs))
  /\ (forall ss, slots_ok E M ss -> slots_ok E M' (slots_keeps k0 rs ss)).
Proof.
  intros E rs M0 k0. induction rs as [|[[b o] n] rest IH]; intros M M' HK0 Hout Hg.
  - assert (EQ : forall x, M' x = M x) by (intros x; apply Hout; reflexivity).
    split; [intros k HK; cbn [kn_havocs]; eapply know_ok_memeq; eassumption
          | intros ss HS; cbn [slots_keeps]; eapply slots_ok_memeq; eassumption].
  - set (a := estart E (SA b o)). set (l := elenZ E n).
    set (M1 := fun x : word => if inrs E rest x then M x else M' x).
    assert (O1 : forall x : word, (bv_unsigned x < a \/ a + l <= bv_unsigned x)%Z -> M1 x = M x).
    { intros x Hx. unfold M1. destruct (inrs E rest x) eqn:Er; [reflexivity|].
      apply Hout. cbn [inrs]. rewrite Er, orb_false_r. apply inr_false. unfold rng_lo, rng_len. fold a l. lia. }
    assert (G1 : mem_grows M M1).
    { intros x Hx. unfold M1. destruct (inrs E rest x); [exact Hx | exact (Hg x Hx)]. }
    assert (O2 : forall x : word, inrs E rest x = false -> M' x = M1 x).
    { intros x Hx. unfold M1. rewrite Hx. reflexivity. }
    assert (G2 : mem_grows M1 M').
    { intros x Hx. unfold M1 in Hx. destruct (inrs E rest x); [exact (Hg x Hx) | exact Hx]. }
    destruct (IH M1 M' HK0 O2 G2) as [IHk IHs].
    split.
    + intros k HK. cbn [kn_havocs]. apply IHk. eapply know_ok_havoc; [exact HK | exact O1 | exact G1].
    + intros ss HS. cbn [slots_keeps]. apply IHs. eapply (slots_keep_sound E M0 k0); [exact HK0 | exact HS | exact O1].
Qed.

(* [comment removed for export] *)
Lemma outside_of_inrs : forall E rs (regs : list (word * Z)) x,
  Forall2 (fun r g => bv_unsigned (fst g) = rng_lo E r /\ snd g = rng_len E r /\ 0 <= rng_lo E r /\ rng_lo E r + rng_len E r <= 2 ^ 64) rs regs ->
  inrs E rs x = false -> outside x regs.
Proof.
  intros E rs regs x HF. induction HF as [|r [gb gn] rs' regs' (H1 & H2 & H3 & H4) HF IH]; intros Hin; cbn [outside]; [exact I|].
  cbn [inrs] in Hin. apply Bool.orb_false_iff in Hin as [Hr Hrest]. cbn [fst snd] in H1, H2.
  split; [| apply IH; exact Hrest].
  apply inr_false in Hr. unfold in_rng. subst gn. rewrite H1. lia.
Qed.


Lemma env_agree_refl' : forall b E, env_agree b E E.
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.

Lemma env_agree_trans' : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite (A1 n Hn); apply A2; exact Hn | congruence]. Qed.

(* [comment removed for export] *)
Lemma cs_ok_bump1 : forall E cs R M model a,
  cs_ok E cs R M model -> fresh_ok nx0 cs = true ->
  cs_ok (ext1 E (s_next (c_ss cs)) a) (bump_next cs 1) R M model.
Proof.
  intros E cs R M model a HC Hf. unfold fresh_ok in Hf.
  apply andb_prop in Hf as [Hf Hnx]. apply andb_prop in Hf as [Hf Hslv]. apply andb_prop in Hf as [Hf Hmv].
  apply andb_prop in Hf as [Hsv Hkv].
  pose proof (ext1_agree E (s_next (c_ss cs)) a) as Hag.
  destruct HC as [HR HK HL Hh Hlz Hmt Hfd HV HSL].
  constructor; cbn [bump_next c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - eapply regs_ok_ext; [exact Hag | exact Hsv | exact HR].
  - eapply know_ok_ext; [exact Hag | exact Hkv | exact HK].
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - (* [comment removed for export] *)
    eapply (SPS.vm_ok_ext RSEGS); [exact Hag | | exact Hmv | exact HV].
    apply N.leb_le in Hnx. pose proof nx0_pos as Hnp. unfold nx0_okP in Hnp. lia.
  - eapply slots_ok_ext; [exact Hag | exact Hslv | exact HSL].
Qed.

Lemma expr_vars_lt_mono : forall b b' e, (b <= b')%N -> SP.expr_vars_lt b e = true -> SP.expr_vars_lt b' e = true.
Proof.
  intros b b' e Hle. induction e; cbn [SP.expr_vars_lt]; intros He; try reflexivity.
  - apply N.ltb_lt in He. apply N.ltb_lt. lia.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - exact (IHe He).
Qed.

Lemma slots_vars_lt_mono : forall b b' ss, (b <= b')%N -> slots_vars_lt b ss = true -> slots_vars_lt b' ss = true.
Proof.
  intros b b' ss Hle H. unfold slots_vars_lt in *. apply forallb_forall. intros x Hx.
  pose proof (proj1 (forallb_forall _ _) H x Hx) as Hs. unfold slot_vars_lt in *.
  repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end.
  rewrite !(expr_vars_lt_mono b b') by assumption. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof.
  intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | |lo hi| | | |]; cbn [kimg_cut1]; try (apply Forall_one; exact HKK).
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hap; [apply Forall_one; exact HKK|].
  apply Bool.orb_false_iff in Hap as [Hap1 Hap2]. apply Z.leb_gt in Hap1. apply Z.leb_gt in Hap2.
  cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Himg).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:E1; [|constructor]. apply Z.ltb_lt in E1. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
  - destruct (Z.ltb (a + n) hi) eqn:E2; [|constructor]. apply Z.ltb_lt in E2. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
Qed.

(* [comment removed for export] *)

Lemma kept_regs : forall (R R' : bvmap 5 word),
  (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
     getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
  forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr R' r = getr R r.
Proof.
  intros R R' Hk r Hr0 Hn.
  pose proof (kept_of_not_caller_saved r
    (map (fun k => Z_to_bv 5 (Z.of_nat k)) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat)
    ltac:(intros k Hin; apply (in_map (fun k : nat => Z_to_bv 5 (Z.of_nat k))); exact Hin) Hr0 Hn) as Hin.
  apply in_map_iff in Hin as (k & <- & Hin). apply Hk. exact Hin.
Qed.


Lemma u_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros E. cbn [edenot]. apply u64_lit. lia. Qed.

Lemma flat_abs0 : forall E off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z ->
  flat E (SA (ELit 0) off) n.
Proof. intros E off n H0 Hn Hnw Hlt. unfold flat, estart. cbn [a_base a_off]. rewrite u_lit0. lia. Qed.

Lemma adenot_abs0 : forall E off, adenot E (SA (ELit 0) off) = Z_to_bv 64 off.
Proof. intros E off. rewrite adenot_SA, u_lit0. f_equal. Qed.

End G.
