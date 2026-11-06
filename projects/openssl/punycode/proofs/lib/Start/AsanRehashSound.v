(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg AgentLib
  AsanAcct AsanAcctShape SpinAlg Hoare.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound
  AsanPlanSoundSums AsanNodesLib AsanNodesLibSound.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanRehashModel AsanRehash AsanHookKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RHNS.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import APSX. Import RHN. Import HKIT.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation W := LBNS.W (only parsing).
#[local] Notation rd_ok := LBNS.rd_ok (only parsing).
#[local] Notation inr := LBNS.inr (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Specs.
Variable SEGS : list Segment.
#[local] Notation wr_ok := (LBNS.wr_ok SEGS) (only parsing).
#[local] Notation cell := (LBNS.cell SEGS) (only parsing).

(* [comment removed for export] *)
Definition rh_FP (mapz B N sp : Z) (x : word) : Prop := inr x (mapz + 8) 8 \/ inr x B (32 * N) \/ inr x (sp - 16) 16.

Definition rehash_contract (T : rtab) (ilo ihi : Z) : Prop :=
  forall regs M (Bo No B N sp ra : Z) (olds ks' : list Z) (pl : list (Z * Z)) (ne0 tb0 : Z),
    getr regs 10%bv = W (r_map T) -> getr regs 11%bv = W Bo -> getr regs 12%bv = W (Bo + 32 * No) ->
    getr regs 2%bv = W sp -> getr regs 1%bv = W ra ->
    RHM.rehash0 N olds = Some (ks', pl) -> Z.of_nat (length olds) = No ->
    Forall (fun key => 0 <= key < 2 ^ 64) olds -> List.NoDup (List.filter RHM.is_live olds) ->
    64 <= N <= 2 ^ 20 -> Z.land (N - 1) N = 0 -> 1 <= No <= 2 ^ 20 ->
    0 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
    (* [comment removed for export] *)
    cell M (r_map T) 8 (W B) -> cell M (r_map T + 8) 4 (W ne0) -> cell M (r_map T + 12) 4 (W tb0) -> cell M (r_map T + 16) 4 (W N) ->
    wr_ok M (r_map T) 20 ->
    (* [comment removed for export] *)
    (forall j, 0 <= j < No -> cell M (Bo + 32 * j) 8 (W (nth (Z.to_nat j) olds 0))) -> rd_ok M Bo (32 * No) ->
    (* [comment removed for export] *)
    wr_ok M B (32 * N) -> rd_ok M B (32 * N) -> wr_ok M (sp - 16) 16 -> rd_ok M (sp - 16) 16 -> sp mod 16 = 0 ->
    (* [comment removed for export] *)
    0 < Bo -> Bo + 32 * No <= 2 ^ 47 -> Bo mod 8 = 0 -> 0 < B -> B + 32 * N <= 2 ^ 47 -> B mod 8 = 0 -> sp < 2 ^ 47 ->
    (Bo + 32 * No <= ilo \/ ihi <= Bo) -> (B + 32 * N <= ilo \/ ihi <= B) -> ihi <= sp - 16 ->
    ilo <= r_map T -> r_map T + 20 <= ihi ->
    (Bo + 32 * No <= B \/ B + 32 * N <= Bo) -> (sp <= Bo \/ Bo + 32 * No <= sp - 16) -> (sp <= B \/ B + 32 * N <= sp - 16) ->
    (* [comment removed for export] *)
    (forall s, In s SEGS -> seg_writable s = false -> forall z, Z.of_N (seg_base s) <= z < Z.of_N (seg_base s) + Z.of_N (seg_size s) -> M (W z) = None) ->
    exists regs' M',
      msteps SEGS (mkst regs (W (r_entry T)) M (seg_rom SEGS)) (mkst regs' (W ra) M' (seg_rom SEGS))
      /\ (forall r : bv 5, ~ In (ridx r) rh_fresh -> getr regs' r = getr regs r)
      /\ cell M' (r_map T + 8) 4 (W (Z.of_nat (length pl))) /\ cell M' (r_map T + 12) 4 (W 0)
      /\ (forall d, 0 <= d < N -> cell M' (B + 32 * d) 8 (W (nth (Z.to_nat d) ks' 0)))
      /\ (forall x, ~ rh_FP (r_map T) B N sp x -> M' x = M x) /\ mem_grows M M'.
End Specs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis HULL_le : img_lo A <= img_hi A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Hypothesis NX0_spw : AP.expr_vars_lt nx0 e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.
Variable T : rtab.

#[local] Notation cell := (LBNS.cell SEGS) (only parsing).
#[local] Notation wr_ok := (LBNS.wr_ok SEGS) (only parsing).
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH ISP FS0) (only parsing).
#[local] Notation MR := (Mr A argH) (only parsing).

Hypothesis RHC : rehash_contract SEGS T (img_lo A) (img_hi A).

Lemma zmem_false : forall x l, zmem x l = false -> ~ List.In x l.
Proof.
  intros x l. induction l as [|y r IH]; intros Hm Hin; [destruct Hin|]. cbn [zmem] in Hm.
  destruct (Z.eqb x y) eqn:Exy; [discriminate|]. apply Z.eqb_neq in Exy.
  destruct Hin as [Hy|Hin]; [apply Exy; symmetry; exact Hy | exact (IH Hm Hin)].
Qed.
Lemma znodup_sound : forall l, znodup l = true -> List.NoDup l.
Proof.
  induction l as [|x r IH]; intros H; [constructor|]. cbn [znodup] in H. destruct (zmem x r) eqn:Hm; [discriminate|].
  constructor; [exact (zmem_false x r Hm) | exact (IH H)].
Qed.


(* [comment removed for export] *)
Lemma upd_length : forall ks i v, length (RHM.upd ks i v) = length ks.
Proof. induction ks as [|k r IH]; intros i v; [reflexivity|]. destruct i; cbn [RHM.upd length]; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma rehash_length : forall N olds ks j pl ks' pl', RHM.rehash N ks olds j pl = Some (ks', pl') -> length ks' = length ks.
Proof.
  intros N olds. induction olds as [|k r IH]; intros ks j pl ks' pl' H; cbn [RHM.rehash] in H.
  - injection H as <- _. reflexivity.
  - destruct (RHM.is_live k); [|exact (IH _ _ _ _ _ H)].
    destruct (RHM.probe_free N ks (RHM.hash0 N k) 1 (Z.to_nat N)) as [d|]; [|discriminate].
    rewrite (IH _ _ _ _ _ H). apply upd_length.
Qed.
Lemma rehash0_length : forall N olds ks' pl, RHM.rehash0 N olds = Some (ks', pl) -> length ks' = Z.to_nat N.
Proof. intros N olds ks' pl H. unfold RHM.rehash0 in H. rewrite (rehash_length _ _ _ _ _ _ _ H). apply repeat_length. Qed.

(* [comment removed for export] *)
Lemma key_facts_ok : forall E (M' : word -> option byte) b o Bz, estart E (SA b o) = Bz -> 0 <= Bz ->
  forall ks off, 0 <= off -> Bz + off + 32 * Z.of_nat (length ks) <= 2 ^ 64 ->
  (forall d, 0 <= d < Z.of_nat (length ks) -> cell M' (Bz + off + 32 * d) 8 (W (nth (Z.to_nat d) ks 0))) ->
  Forall (kentry_ok SEGS E M') (key_facts b (o + off) ks).
Proof.
  intros E M' b o Bz Hs HB ks. induction ks as [|key r IH]; intros off Hoff Hfit Hc; cbn [key_facts]; [constructor|].
  cbn [length] in Hfit. rewrite Nat2Z.inj_succ in Hfit.
  constructor.
  - apply (kword_intro SEGS E M' b (o + off) 8 (ELit key) (Bz + off) (W key)); [lia | | lia | lia | lia | | reflexivity].
    + unfold estart in *. cbn [a_base a_off] in *. lia.
    + specialize (Hc 0 ltac:(cbn [length]; lia)). rewrite Z.mul_0_r, Z.add_0_r in Hc. exact Hc.
  - replace (o + off + 32) with (o + (off + 32)) by lia. apply IH; [lia | lia |].
    intros d Hd. specialize (Hc (d + 1) ltac:(cbn [length]; lia)).
    replace (Bz + off + 32 * (d + 1)) with (Bz + (off + 32) + 32 * d) in Hc by lia.
    replace (Z.to_nat (d + 1)) with (S (Z.to_nat d)) in Hc by lia. exact Hc.
Qed.


(* [comment removed for export] *)
Lemma collect_in : forall k nb o v, In (o, v) (collect k nb) -> exists v0, In (KWord (SA nb o) 8 (ELit v0)) k /\ v = v0 mod two64.
Proof.
  induction k as [|K r IH]; intros nb o v H; [destruct H|]. cbn [collect] in H.
  destruct K as [[b o'] w e| | | | | | | | |]; try (destruct (IH nb o v H) as (v0 & Hin & Hv); exists v0; split; [right; exact Hin | exact Hv]).
  destruct e as [z| | | | | | |]; try (destruct (IH nb o v H) as (v0 & Hin & Hv); exists v0; split; [right; exact Hin | exact Hv]).
  destruct (Nat.eqb w 8 && expr_eqb b nb)%bool eqn:Eb.
  - destruct H as [H|H].
    + injection H as <- <-. apply andb_prop in Eb as [E1 E2]. apply Nat.eqb_eq in E1. apply expr_eqb_eq in E2. subst w b.
      exists z. split; [left; reflexivity | reflexivity].
    + destruct (IH nb o v H) as (v0 & Hin & Hv). exists v0. split; [right; exact Hin | exact Hv].
  - destruct (IH nb o v H) as (v0 & Hin & Hv). exists v0. split; [right; exact Hin | exact Hv].
Qed.
Lemma alookup_in : forall l o v, alookup l o = Some v -> In (o, v) l.
Proof.
  induction l as [|[o' v'] r IH]; intros o v H; [discriminate|]. cbn [alookup] in H.
  destruct (Z.eqb o o') eqn:E; [apply Z.eqb_eq in E; injection H as <-; subst o'; left; reflexivity | right; exact (IH o v H)].
Qed.
Lemma keys_of_in : forall l n o ks, keys_of l o n = Some ks ->
  length ks = n /\ forall b, 0 <= b < Z.of_nat n -> In (o + 32 * b, nth (Z.to_nat b) ks 0) l.
Proof.
  intros l n. induction n as [|n IH]; intros o ks H; cbn [keys_of] in H.
  - injection H as <-. split; [reflexivity | intros b Hb; cbn in Hb; lia].
  - destruct (alookup l o) as [v|] eqn:Ha; [|discriminate]. destruct (keys_of l (o + 32) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    destruct (IH (o + 32) r Hr) as [Hl Hc]. split; [cbn [length]; rewrite Hl; reflexivity|]. intros b Hb. rewrite Nat2Z.inj_succ in Hb.
    destruct (Z.eq_dec b 0) as [->|Nb].
    + change (Z.to_nat 0) with 0%nat. cbn [nth]. rewrite Z.mul_0_r, Z.add_0_r. exact (alookup_in l o v Ha).
    + replace (nth (Z.to_nat b) (v :: r) 0) with (nth (Z.to_nat (b - 1)) r 0).
      2:{ replace (Z.to_nat b) with (S (Z.to_nat (b - 1))) by lia. reflexivity. }
      replace (o + 32 * b) with (o + 32 + 32 * (b - 1)) by lia. apply Hc. lia.
Qed.

(* [comment removed for export] *)
Lemma kword_cell : forall E (M : word -> option byte) b o v, kentry_ok SEGS E M (KWord (SA b o) 8 (ELit v)) ->
  cell M (estart E (SA b o)) 8 (W (v mod two64)).
Proof.
  intros E M b o v (_ & F & Hrd). unfold LBNS.cell. rewrite LBNS.W_mod.
  assert (Ea : adenot E (SA b o) = W (estart E (SA b o))).
  { apply bv_eq. rewrite (flat_u E _ _ F). unfold LBNS.W. destruct F as (F0 & F1 & _). rewrite u64_lit by lia. reflexivity. }
  rewrite <- Ea. exact Hrd.
Qed.

Lemma keys_cells : forall E (M : word -> option byte) k nb no N ks, know_ok SEGS E M k ->
  keys_of (collect k nb) no N = Some ks ->
  length ks = N /\ forall b, 0 <= b < Z.of_nat N -> cell M (estart E (SA nb no) + 32 * b) 8 (W (nth (Z.to_nat b) ks 0)).
Proof.
  intros E M k nb no N ks HK H. destruct (keys_of_in _ _ _ _ H) as [Hl Hc]. split; [exact Hl|]. intros b Hb.
  destruct (collect_in k nb _ _ (Hc b Hb)) as (v0 & Hin & Hv). rewrite Hv.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK. pose proof (kword_cell E M nb (no + 32 * b) v0 HKK) as X.
  replace (estart E (SA nb (no + 32 * b))) with (estart E (SA nb no) + 32 * b) in X by (unfold estart; cbn [a_base a_off]; lia). exact X.
Qed.


Lemma cut0_ok : forall E (M : word -> option byte) k b o n, know_ok SEGS E M k ->
  know_ok SEGS E M (match b with ELit 0 => kimg_cut k o n | _ => k end).
Proof.
  intros E M k b o n HK. destruct b as [z| | | | | | |]; try exact HK. destruct z; try exact HK. apply kimg_cut_sound. exact HK.
Qed.

Lemma havs_mix : forall E (M M' : word -> option byte) rs k (P : word -> bool),
  Forall (fun r : hrange => 0 <= snd r < 2 ^ 64) rs -> mem_grows M M' ->
  know_ok SEGS E (LBNS.mixm P M M') k ->
  know_ok SEGS E (LBNS.mixm (fun x => (P x || in_rs E rs x)%bool) M M') (RHN.havs k rs).
Proof.
  intros E M M' rs. induction rs as [|[[b o] n] rest IH]; intros k P Hn Hg HK.
  - assert (EQ : P = (fun x : word => (P x || in_rs E [] x)%bool)).
    { apply functional_extensionality. intros x. cbn [in_rs existsb]. rewrite orb_false_r. reflexivity. }
    exact (eq_ind _ (fun P0 => know_ok SEGS E (LBNS.mixm P0 M M') k) HK _ EQ).
  - apply Forall_cons_iff in Hn as [Hn1 Hn]. cbn [snd] in Hn1. cbn [RHN.havs].
    assert (El : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
    set (P1 := fun x => (P x || LBNS.inrb (estart E (SA b o)) n x)%bool).
    set (k0 := match b with ELit 0 => kimg_cut k o n | _ => k end).
    assert (K1 : know_ok SEGS E (LBNS.mixm P1 M M') (kn_havocM k0 b o (ELit n))).
    { rewrite kn_havocM_eq.
      apply (w_know_ok_havoc SEGS E (LBNS.mixm P M M') (LBNS.mixm P1 M M') k0 b o (ELit n) (cut0_ok E _ k b o n HK)).
      - intros x Hx. rewrite El in Hx. unfold LBNS.mixm, P1.
        destruct (LBNS.inrb (estart E (SA b o)) n x) eqn:Hb; [|rewrite orb_false_r; reflexivity].
        exfalso. apply LBNS.inrb_inr in Hb. unfold LBNS.inr in Hb. lia.
      - apply LBNS.mixm_grows2; [exact Hg|]. intros x Hx. unfold P1. rewrite Hx. reflexivity. }
    specialize (IH _ P1 Hn Hg K1).
    assert (EQ : (fun x : word => (P1 x || in_rs E rest x)%bool) = (fun x : word => (P x || in_rs E ((b, o, n) :: rest) x)%bool)).
    { apply functional_extensionality. intros x. unfold P1. cbn [in_rs existsb]. rewrite orb_assoc. reflexivity. }
    exact (eq_ind _ (fun P0 => know_ok SEGS E (LBNS.mixm P0 M M') (RHN.havs (kn_havocM k0 b o (ELit n)) rest)) IH _ EQ).
Qed.

Lemma havs_sound : forall E (M M' : word -> option byte) rs k,
  Forall (fun r : hrange => 0 <= snd r < 2 ^ 64) rs -> mem_grows M M' -> know_ok SEGS E M k ->
  (forall x, in_rs E rs x = false -> M' x = M x) ->
  know_ok SEGS E M' (RHN.havs k rs).
Proof.
  intros E M M' rs k Hn Hg HK Hout.
  pose proof (havs_mix E M M' rs k (fun _ => false) Hn Hg HK) as X.
  assert (EQ : LBNS.mixm (fun x : word => (false || in_rs E rs x)%bool) M M' = M').
  { apply functional_extensionality. intros x. unfold LBNS.mixm. cbn [orb].
    destruct (in_rs E rs x) eqn:Hb; [reflexivity | symmetry; exact (Hout x Hb)]. }
  exact (eq_ind _ (fun M0 => know_ok SEGS E M0 (RHN.havs k rs)) X _ EQ).
Qed.


(* [comment removed for export] *)
Lemma lit_cell : forall E M k a (w : nat) z, know_ok SEGS E M k -> (1 <= w <= 8)%nat -> kreadZ SEGS k (ELit 0) a w = Some z ->
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> cell M a w (W z).
Proof.
  intros E M k a w z HK Hw H H0 H1. unfold kreadZ in H.
  destruct (know_lookup SEGS k (ELit 0) a w false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  assert (Ua : bv_unsigned (edenot E (ELit a)) = a) by (cbn [edenot]; apply u64_lit; lia).
  pose proof (LBNS.lookup_cell SEGS E M k (ELit a) 0 w (ELit z0) hs HK Hw) as X. cbn [split_lit fst snd] in X.
  rewrite Z.add_0_r in X. rewrite Ua in X. rewrite Z.add_0_r in X. rewrite LBNS.W_mod. change (Z_to_bv 64 z0) with (edenot E (ELit z0)).
  apply X; [exact HL | unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia | lia | lia].
Qed.

Lemma lit_cell8e : forall E M k a v, know_ok SEGS E M k -> kread8e SEGS k (ELit 0) a = Some v ->
  0 <= a -> a + 8 <= 2 ^ 64 -> cell M a 8 (edenot E v).
Proof.
  intros E M k a v HK H H0 H1. unfold kread8e in H.
  destruct (know_lookup SEGS k (ELit 0) a 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  assert (Ua : bv_unsigned (edenot E (ELit a)) = a) by (cbn [edenot]; apply u64_lit; lia).
  pose proof (LBNS.lookup_cell SEGS E M k (ELit a) 0 8 v hs HK ltac:(lia)) as X. cbn [split_lit fst snd] in X.
  rewrite Z.add_0_r in X. rewrite Ua in X. rewrite Z.add_0_r in X.
  apply X; [exact HL | unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia | lia | lia].
Qed.

Lemma lit1_w : forall E e z, lit1 e = Some z -> edenot E e = W z.
Proof. intros E e z H. destruct e; try discriminate. cbn [lit1] in H. injection H as <-. cbn [edenot]. symmetry. apply LBNS.W_mod. Qed.

(* [comment removed for export] *)
Lemma store_all_wr_ok : forall (M : word -> option byte) a n, 0 <= a -> a + n < 2 ^ 64 -> 0 <= n ->
  (forall m, Z.of_nat m <= n -> store_ok SEGS M (W a) m = true) -> wr_ok M a n.
Proof.
  intros M a n Ha Hn Hn0 Hst x m Hx Hxm.
  apply (store_ok_sub SEGS M (W a) (Z.to_nat n) (W x) m).
  - rewrite LBNS.u_W by lia. lia.
  - apply Hst. lia.
  - rewrite !LBNS.u_W by lia. lia.
  - rewrite !LBNS.u_W by lia. lia.
Qed.

Lemma div_mod8 : forall k z, 3 <= k -> (2 ^ k | z) -> z mod 8 = 0.
Proof.
  intros k z Hk [q Hq]. subst z. replace k with (3 + (k - 3)) by lia. rewrite Z.pow_add_r by lia.
  change (2 ^ 3) with 8. replace (q * (8 * 2 ^ (k - 3))) with (q * 2 ^ (k - 3) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma div_mod16 : forall k z, 4 <= k -> (2 ^ k | z) -> z mod 16 = 0.
Proof.
  intros k z Hk [q Hq]. subst z. replace k with (4 + (k - 4)) by lia. rewrite Z.pow_add_r by lia.
  change (2 ^ 4) with 16. replace (q * (16 * 2 ^ (k - 4))) with (q * 2 ^ (k - 4) * 16) by lia. apply Z.mod_mul. lia.
Qed.


(* [comment removed for export] *)
Lemma ovl_facts : forall E M k e n, know_ok SEGS E M k -> LBN.ovl_ok A k e (ELit n) = true -> 0 < n < 2 ^ 63 ->
  bv_unsigned (edenot E e) + n < 2 ^ 64 ->
  let a := bv_unsigned (edenot E e) in
  rd_ok M a n /\ wr_ok M a n /\ (a + n <= img_lo A \/ img_hi A <= a) /\ estart E (SA (fst (split_lit e)) (snd (split_lit e))) = a.
Proof.
  intros E M k e n HK H Hn Hfit a.
  assert (El : elenZ E (ELit n) = n) by (apply elenZ_lit; lia).
  destruct (LBNS.ovl_ok_sound SEGS A SEGS_in_hull HULL_ok HULL_le E M k e (ELit n) HK H ltac:(rewrite El; lia)) as (Hrd & _ & Hst & Hoff & Hs).
  rewrite El in *. fold a in Hrd, Hst, Hoff, Hs. pose proof (u64_range (edenot E e)) as Ra. fold a in Ra.
  split; [exact Hrd|]. split; [apply store_all_wr_ok; [lia | exact Hfit | lia | exact Hst]|]. split; [exact Hoff | exact Hs].
Qed.

Lemma rh_fresh_nodup : List.NoDup rh_fresh.
Proof.
  unfold rh_fresh. repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Theorem node_rehash_sound : node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (fun cs => node_rehash SEGS A nx0 T cs).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  unfold node_rehash in Hn.
  destruct (negb (Z.eqb (pc cs) (r_entry T))) eqn:Hpc0; [discriminate|]. apply negb_false_iff in Hpc0. apply Z.eqb_eq in Hpc0.
  cbv zeta in Hn.
  destruct (split_lit (reg cs 11)) as [ob oo] eqn:Hspo. destruct (split_lit (eaddz (reg cs 2) (-16))) as [sb so] eqn:Hsps.
  destruct (lit1 (reg cs 10)) as [mapv|] eqn:L10; [|discriminate]. destruct (lit1 (reg cs 1)) as [ra|] eqn:L1; [|discriminate].
  destruct (kread8e SEGS (kn cs) (ELit 0) (r_map T)) as [B|] eqn:KB; [|discriminate].
  destruct (kreadZ SEGS (kn cs) (ELit 0) (r_map T + 8) 4) as [ne0|] eqn:Kne; [|discriminate].
  destruct (kreadZ SEGS (kn cs) (ELit 0) (r_map T + 12) 4) as [tb0|] eqn:Ktb; [|discriminate].
  destruct (kreadZ SEGS (kn cs) (ELit 0) (r_map T + 16) 4) as [N|] eqn:KN; [|discriminate].
  destruct (xlo (kn cs) (esub (reg cs 12) (reg cs 11))) as [dlo|] eqn:Hdlo; [|discriminate].
  destruct (xhi (kn cs) (esub (reg cs 12) (reg cs 11))) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (split_lit B) as [nb no] eqn:Hspb.
  destruct (keys_of (collect (kn cs) ob) oo (Z.to_nat (dlo / 32))) as [olds|] eqn:Hrk; [|discriminate].
  destruct (xlo (kn cs) (reg cs 11)) as [olo|] eqn:Holo; [|discriminate]. destruct (xhi (kn cs) (reg cs 11)) as [ohi|] eqn:Hohi; [|discriminate].
  destruct (xlo (kn cs) B) as [blo|] eqn:Hblo; [|discriminate]. destruct (xhi (kn cs) B) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate]. destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  destruct (RHM.rehash0 N olds) as [[ks' pl]|] eqn:Hrh; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of Hn with Some (with_ss cs (mk_ss _ ?sr ?kf _)) = _ => remember sr as srF eqn:HsrF; remember kf as kF eqn:HkF end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Cmw]. apply andb_prop in Hc as [Hc Cmhi]. apply andb_prop in Hc as [Hc Cmlo]. apply andb_prop in Hc as [Hc Cap3]. apply andb_prop in Hc as [Hc Cap2]. apply andb_prop in Hc as [Hc Cap1]. apply andb_prop in Hc as [Hc Covs]. apply andb_prop in Hc as [Hc Csphi]. apply andb_prop in Hc as [Hc Csplo]. apply andb_prop in Hc as [Hc Csal]. apply andb_prop in Hc as [Hc Covb]. apply andb_prop in Hc as [Hc Cbal]. apply andb_prop in Hc as [Hc Cbhi]. apply andb_prop in Hc as [Hc Cblo]. apply andb_prop in Hc as [Hc Covo]. apply andb_prop in Hc as [Hc Coal]. apply andb_prop in Hc as [Hc Cohi]. apply andb_prop in Hc as [Hc Colo]. apply andb_prop in Hc as [Hc Crng]. apply andb_prop in Hc as [Hc Cnd]. apply andb_prop in Hc as [Hc Cra4]. apply andb_prop in Hc as [Hc Cra1]. apply andb_prop in Hc as [Hc Cra0]. apply andb_prop in Hc as [Hc Cpow]. apply andb_prop in Hc as [Hc CN2]. apply andb_prop in Hc as [Hc CN1]. apply andb_prop in Hc as [Hc CNo2]. apply andb_prop in Hc as [Hc CNo1]. apply andb_prop in Hc as [Hc Cd32]. apply andb_prop in Hc as [Hc Cdeq]. apply andb_prop in Hc as [Hc Cmap]. apply andb_prop in Hc as [Hc CvB]. apply andb_prop in Hc as [Hc Cro]. rename Hc into Hfresh.
  apply Z.eqb_eq in Cmap, Cdeq, Cd32, Cpow, Cra4. apply Z.leb_le in CNo1, CNo2, CN1, CN2, Cra0, Cohi, Coal, Cbhi, Cbal, Csal, Csplo, Cmlo, Cmhi.
  apply Z.ltb_lt in Cra1, Colo, Cblo, Csphi. subst mapv dhi.
  set (No := dlo / 32) in *.
  pose proof HULL_ok as (HU0 & HU1 & HU2 & HU3). unfold KHI in HU3.
  assert (Hih : 0 <= img_hi A) by (clear - HU0 HULL_le; lia).
  assert (HdNo : dlo = 32 * No) by (unfold No; clear - Cd32; pose proof (Z.div_mod dlo 32 ltac:(lia)); lia).
  (* [comment removed for export] *)
  set (Bo := bv_unsigned (edenot E (reg cs 11))) in *. set (Bz := bv_unsigned (edenot E B)) in *. set (spz := bv_unsigned (edenot E (reg cs 2))) in *.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Holo) as X1. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hohi) as X2. fold Bo in X1, X2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hblo) as X3. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as X4. fold Bz in X3, X4.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as X5. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as X6. fold spz in X5, X6.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hdlo) as X7. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as X8.
  rewrite LBNS.u_esub in X7, X8. fold Bo in X7, X8.
  assert (Eend : bv_unsigned (edenot E (reg cs 12)) = Bo + 32 * No).
  { pose proof (u64_range (edenot E (reg cs 12))) as Re. set (ez := bv_unsigned (edenot E (reg cs 12))) in *.
    pose proof (u64_range (edenot E (reg cs 11))) as Ro. fold Bo in Ro.
    clear - Re Ro X7 X8 HdNo CNo1 CNo2 X1 X2 Colo Cohi.
    assert (Hm : (ez - Bo) mod 2 ^ 64 = dlo) by lia.
    assert (Hq : exists q, ez - Bo = dlo + 2 ^ 64 * q) by (exists ((ez - Bo) / 2 ^ 64); pose proof (Z.div_mod (ez - Bo) (2 ^ 64) ltac:(lia)); lia).
    destruct Hq as [q Hq]. assert (q = 0) by lia. subst q. lia. }
  assert (Ees : bv_unsigned (edenot E (eaddz (reg cs 2) (-16))) = spz - 16).
  { rewrite u_eaddz. fold spz. apply Z.mod_small. pose proof (u64_range (edenot E (reg cs 2))) as Rs. fold spz in Rs. clear - Rs X5 Csplo Hih. lia. }
  (* [comment removed for export] *)
  assert (A1 : 0 < 32 * No < 2 ^ 63) by (clear - CNo1 CNo2; lia). assert (A2 : Bo + 32 * No < 2 ^ 64) by (clear - X2 Cohi; lia).
  assert (A3 : 0 < 32 * N < 2 ^ 63) by (clear - CN1 CN2; lia). assert (A4 : Bz + 32 * N < 2 ^ 64) by (clear - X4 Cbhi; lia).
  assert (A5 : spz - 16 + 16 < 2 ^ 64) by (clear - X6 Csphi; lia).
  destruct (ovl_facts E M (kn cs) (reg cs 11) (32 * No) HKN Covo A1 A2) as (Ord & _ & Ooff & Ost). fold Bo in Ord, Ooff, Ost.
  destruct (ovl_facts E M (kn cs) B (32 * N) HKN Covb A3 A4) as (Nrd & Nwr & Noff & Nst). fold Bz in Nrd, Nwr, Noff, Nst.
  destruct (ovl_facts E M (kn cs) (eaddz (reg cs 2) (-16)) 16 HKN Covs ltac:(clear; lia) ltac:(rewrite Ees; exact A5)) as (Srd & Swr & Soff & Sst).
  rewrite Ees in Srd, Swr, Soff, Sst. rewrite Hspo in Ost. rewrite Hspb in Nst. rewrite Hsps in Sst. cbn [fst snd] in Ost, Nst, Sst.
  (* [comment removed for export] *)
  assert (Am : 0 <= r_map T /\ r_map T + 20 <= 2 ^ 47) by (clear - HU0 HU3 Cmlo Cmhi; lia).
  pose proof (lit_cell8e E M (kn cs) _ _ HKN KB ltac:(clear - Am; lia) ltac:(clear - Am; lia)) as CB. rewrite <- (LBNS.W_u (edenot E B)) in CB. fold Bz in CB.
  pose proof (lit_cell E M (kn cs) _ 4 _ HKN ltac:(clear; lia) Kne ltac:(clear - Am; lia) ltac:(clear - Am; lia)) as Cne.
  pose proof (lit_cell E M (kn cs) _ 4 _ HKN ltac:(clear; lia) Ktb ltac:(clear - Am; lia) ltac:(clear - Am; lia)) as Ctb.
  pose proof (lit_cell E M (kn cs) _ 4 _ HKN ltac:(clear; lia) KN ltac:(clear - Am; lia) ltac:(clear - Am; lia)) as CN.
  assert (Esm : estart E (SA (ELit 0) (r_map T)) = r_map T) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by (clear - Am; lia); clear; lia).
  destruct (kwr_wr_ok SEGS E M (kn cs) (ELit 0) (r_map T) 20 HKN Cmw ltac:(clear; lia) ltac:(rewrite Esm; clear - Am; lia)) as (Wm & _ & _). rewrite Esm in Wm.
  (* [comment removed for export] *)
  destruct (keys_cells E M (kn cs) ob oo (Z.to_nat No) olds HKN Hrk) as (Hlen & Hkeys'). rewrite Ost in Hkeys'. rewrite Z2Nat.id in Hkeys' by (clear - CNo1; lia).
  (* [comment removed for export] *)
  assert (Rg : forall r, (0 < r < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat r)) = edenot E (reg cs r)).
  { intros r Hr. exact (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model r HC Hr). }
  assert (G10 : getr R 10%bv = W (r_map T)) by (change (getr R 10%bv) with (getr R (Z_to_bv 5 (Z.of_nat 10))); rewrite (Rg 10%nat) by (clear; lia); exact (lit1_w E _ _ L10)).
  assert (G1 : getr R 1%bv = W ra) by (change (getr R 1%bv) with (getr R (Z_to_bv 5 (Z.of_nat 1))); rewrite (Rg 1%nat) by (clear; lia); exact (lit1_w E _ _ L1)).
  assert (G11 : getr R 11%bv = W Bo) by (change (getr R 11%bv) with (getr R (Z_to_bv 5 (Z.of_nat 11))); rewrite (Rg 11%nat) by (clear; lia); unfold Bo; symmetry; apply LBNS.W_u).
  assert (G12 : getr R 12%bv = W (Bo + 32 * No)) by (change (getr R 12%bv) with (getr R (Z_to_bv 5 (Z.of_nat 12))); rewrite (Rg 12%nat) by (clear; lia); rewrite <- Eend; symmetry; apply LBNS.W_u).
  assert (G2 : getr R 2%bv = W spz) by (change (getr R 2%bv) with (getr R (Z_to_bv 5 (Z.of_nat 2))); rewrite (Rg 2%nat) by (clear; lia); unfold spz; symmetry; apply LBNS.W_u).
  (* [comment removed for export] *)
  pose proof (ealign_sound SEGS E M (kn cs) (reg cs 11) HKN) as [_ Ao]. fold Bo in Ao. pose proof (div_mod8 _ _ Coal Ao) as Ao8.
  pose proof (ealign_sound SEGS E M (kn cs) B HKN) as [_ Ab]. fold Bz in Ab. pose proof (div_mod8 _ _ Cbal Ab) as Ab8.
  pose proof (ealign_sound SEGS E M (kn cs) (reg cs 2) HKN) as [_ As]. fold spz in As. pose proof (div_mod16 _ _ Csal As) as As16.
  (* [comment removed for export] *)
  assert (ElNo : elenZ E (ELit (32 * No)) = 32 * No) by (apply elenZ_lit; clear - A1; lia).
  assert (ElN : elenZ E (ELit (32 * N)) = 32 * N) by (apply elenZ_lit; clear - A3; lia).
  assert (El16 : elenZ E (ELit 16) = 16) by (apply elenZ_lit; clear; lia).
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Cap1) as P1. rewrite Ost, Nst, ElNo, ElN in P1.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Cap2) as P2. rewrite Ost, Sst, ElNo, El16 in P2.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Cap3) as P3. rewrite Nst, Sst, ElN, El16 in P3.
  (* [comment removed for export] *)
  assert (RO : forall sg, In sg SEGS -> seg_writable sg = false -> forall z, Z.of_N (seg_base sg) <= z < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) -> M (W z) = None).
  { intros sg Hsg Hw z Hz. unfold ro_cov in Cro. rewrite forallb_forall in Cro. specialize (Cro sg Hsg). rewrite Hw in Cro. cbn [orb] in Cro.
    exact (img_cov_sound SEGS E M (kn cs) _ _ HKN Cro z Hz). }
  (* [comment removed for export] *)
  pose proof (znodup_sound _ Cnd) as Hnd.
  assert (Hrng : Forall (fun key => 0 <= key < 2 ^ 64) olds).
  { apply Forall_forall. intros key Hin. rewrite forallb_forall in Crng. specialize (Crng key Hin). apply andb_prop in Crng as [Y1 Y2].
    apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. clear - Y1 Y2. lia. }
  assert (B1 : Z.of_nat (length olds) = No) by (rewrite Hlen; apply Z2Nat.id; clear - CNo1; lia).
  assert (B2 : 64 <= N <= 2 ^ 20) by (clear - CN1 CN2; lia). assert (B3 : 1 <= No <= 2 ^ 20) by (clear - CNo1 CNo2; lia).
  assert (B4 : 0 <= ra < 2 ^ 47) by (clear - Cra0 Cra1; lia).
  assert (B5 : 0 < Bo) by (clear - X1 Colo; lia). assert (B6 : Bo + 32 * No <= 2 ^ 47) by (clear - X2 Cohi; lia).
  assert (B7 : 0 < Bz) by (clear - X3 Cblo; lia). assert (B8 : Bz + 32 * N <= 2 ^ 47) by (clear - X4 Cbhi; lia).
  assert (B9 : spz < 2 ^ 47) by (clear - X6 Csphi; lia).
  assert (B10 : img_hi A <= spz - 16) by (clear - X5 Csplo; lia).
  assert (B11 : spz <= Bo \/ Bo + 32 * No <= spz - 16) by (clear - P2; lia).
  assert (B12 : spz <= Bz \/ Bz + 32 * N <= spz - 16) by (clear - P3; lia).
  destruct (RHC R M Bo No Bz N spz ra olds ks' pl ne0 tb0 G10 G11 G12 G2 G1 Hrh B1 Hrng Hnd B2 Cpow B3
              B4 Cra4 CB Cne Ctb CN Wm Hkeys' Ord Nwr Nrd Swr Srd As16 B5 B6 Ao8 B7 B8 Ab8 B9
              Ooff Noff B10 Cmlo Cmhi P1 B11 B12 RO)
    as (regs' & M' & Hms & Kkept & Kne' & Ktb' & Kkeys & Hfr & Hg).
  (* [comment removed for export] *)
  set (nx := nxt cs) in *.
  set (E' := LBNS.ext_regs E nx rh_fresh regs').
  pose proof (LBNS.ext_regs_agree E nx rh_fresh regs') as Hag. fold E' in Hag.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle). fold nx in Fsr, Fkn, Fle.
  assert (Ag : forall e, expr_vars_lt nx e = true -> edenot E' e = edenot E e).
  { intros e He. symmetry. apply (edenot_agree' nx); assumption. }
  assert (AgS : forall e o, expr_vars_lt nx e = true -> estart E' (SA e o) = estart E (SA e o)).
  { intros e o He. unfold estart. cbn [a_base a_off]. rewrite (Ag e He). reflexivity. }
  assert (Vreg : forall r, (r < 32)%nat -> expr_vars_lt nx (reg cs r) = true) by (intros r Hr; apply nth_sr_vars_lt'; assumption).
  assert (Vnb : expr_vars_lt nx nb = true) by exact (split_lit_vars B nb no nx Hspb CvB).
  pose proof (know_ok_agree' SEGS nx E E' M (kn cs) Hag Fkn HKN) as HKN'.
  assert (Ees' : bv_unsigned (edenot E' (eaddz (reg cs 2) (-16))) = spz - 16).
  { rewrite u_eaddz, (Ag _ (Vreg 2%nat ltac:(clear; lia))). fold spz. apply Z.mod_small. clear - X5 Csplo B9 Hih. lia. }
  destruct (ovl_facts E' M (kn cs) (eaddz (reg cs 2) (-16)) 16 HKN' Covs ltac:(clear; lia) ltac:(rewrite Ees'; exact A5)) as (_ & _ & _ & Sst').
  rewrite Ees', Hsps in Sst'. cbn [fst snd] in Sst'.
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH ISP argH_high NX0_spw argH_agree SINV_frame SINV_agree FS0
            cs E E' R FULL model TT ra srF kF (nx + NRH)%nat regs' M' HC Hfresh Hag).
  - rewrite Hpc0. exact Hms.
  - rewrite HsrF. apply (LBNS.regs_after_region E (s_regs (a_ss cs)) R regs' nx rh_fresh (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr).
    + exact rh_fresh_nodup.
    + intros r _ Hnin. exact (Kkept r Hnin).
  - rewrite HkF.
    constructor; [|constructor; [|apply Forall_app; split]].
    + apply (kword_intro SEGS E' M' (ELit 0) (r_map T + 8) 4 _ (r_map T + 8) (W (Z.of_nat (length pl))));
        [clear; lia | | clear - Am; lia | clear - Am; lia | clear - Am; lia | exact Kne' | reflexivity].
      unfold estart. cbn [a_base a_off edenot]. rewrite u64_lit by (clear - Am; lia). clear; lia.
    + apply (kword_intro SEGS E' M' (ELit 0) (r_map T + 12) 4 _ (r_map T + 12) (W 0));
        [clear; lia | | clear - Am; lia | clear - Am; lia | clear - Am; lia | exact Ktb' | reflexivity].
      unfold estart. cbn [a_base a_off edenot]. rewrite u64_lit by (clear - Am; lia). clear; lia.
    + replace no with (no + 0) by (clear; lia).
      apply (key_facts_ok E' M' nb no Bz ltac:(rewrite (AgS nb no Vnb); exact Nst) ltac:(clear - B7; lia) ks' 0 ltac:(clear; lia)).
      * rewrite (rehash0_length _ _ _ _ Hrh), Z2Nat.id by (clear - B2; lia). clear - A4. lia.
      * intros d Hd. rewrite Z.add_0_r. apply Kkeys. rewrite (rehash0_length _ _ _ _ Hrh), Z2Nat.id in Hd by (clear - B2; lia). exact Hd.
    + apply (havs_sound E' M M' _ (kn cs)); [repeat constructor; cbn [snd]; clear - A3; lia | exact Hg | exact HKN' |].
      intros x Hx. apply Hfr. apply in_rs_false in Hx.
      apply Forall_cons_iff in Hx as [Y1 Hx]. apply Forall_cons_iff in Hx as [Y2 Hx]. apply Forall_cons_iff in Hx as [Y3 _]. cbn [fst snd] in Y1, Y2, Y3.
      rewrite (AgS nb no Vnb), Nst in Y1. rewrite Sst' in Y3.
      assert (Em8 : estart E' (SA (ELit 0) (r_map T + 8)) = r_map T + 8) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by (clear - Am; lia); clear; lia).
      rewrite Em8 in Y2. unfold rh_FP. intros [F1|[F2|F3]]; [exact (Y2 F1) | exact (Y1 F2) | apply Y3; unfold LBNS.inr in *; clear - F3; lia].
  - intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
    split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

End Sound.

End RHNS.
