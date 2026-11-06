(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec SymStepR StoreOk IslInterp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ISLS.
Import ISL.

Lemma zkey_inj : forall a b, zkey a = zkey b -> a = b.
Proof. intros [|p|p] [|q|q]; cbn; intros H; try discriminate; try reflexivity; injection H as ->; reflexivity. Qed.

Lemma upd_length : forall {A} n (v : A) l, length (upd n v l) = length l.
Proof. intros A n v l. revert n. induction l as [|x t IH]; intros [|n]; cbn; auto. Qed.
Lemma nth_upd_same : forall {A} n (v d : A) l, (n < length l)%nat -> nth n (upd n v l) d = v.
Proof. intros A n v d l. revert n. induction l as [|x t IH]; intros [|n] H; cbn in *; try lia; auto. apply IH. lia. Qed.
Lemma nth_upd_other : forall {A} n m (v d : A) l, n <> m -> nth m (upd n v l) d = nth m l d.
Proof. intros A n m v d l. revert n m. induction l as [|x t IH]; intros [|n] [|m] H; cbn; auto; try lia. Qed.
Lemma nth_error_upd_same : forall {A} n (v : A) l, (n < length l)%nat -> nth_error (upd n v l) n = Some v.
Proof. intros A n v l. revert n. induction l as [|x t IH]; intros [|n] H; cbn in *; try lia; auto. apply IH. lia. Qed.
Lemma nth_error_upd_other : forall {A} n m (v : A) l, n <> m -> nth_error (upd n v l) m = nth_error l m.
Proof. intros A n m v l. revert n m. induction l as [|x t IH]; intros [|n] [|m] H; cbn; auto; try lia. Qed.

Lemma in_ivs_true : forall l a, in_ivs l a = true -> exists lo hi, In (lo, hi) l /\ lo <= a < hi.
Proof.
  induction l as [|[lo hi] t IH]; cbn; intros a H; [discriminate|].
  apply orb_true_iff in H. destruct H as [H|H].
  - apply andb_true_iff in H. destruct H as [H1 H2]. exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH a H) as (lo' & hi' & Hin & Hr). exists lo', hi'. split; [right; exact Hin | exact Hr].
Qed.

Lemma aval_eqb_eq : forall a b, aval_eqb a b = true -> a = b.
Proof.
  intros [x|k o] [y|k' o']; cbn; intros H; try discriminate.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma aaddr_eqb_eq : forall a b, aaddr_eqb a b = true -> a = b.
Proof.
  intros [x|k o] [y|k' o']; cbn; intros H; try discriminate.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma aaddr_eqb_neq : forall a b, aaddr_eqb a b = false -> a <> b.
Proof.
  intros a b H Heq. subst b. destruct a as [x|k o]; cbn in H.
  - rewrite Z.eqb_refl in H. discriminate.
  - rewrite Nat.eqb_refl, Z.eqb_refl in H. discriminate.
Qed.

Lemma kn_find_in : forall l a b, kn_find l a = Some b -> In (a, b) l.
Proof.
  induction l as [|[x b'] t IH]; cbn; intros a b H; [discriminate|].
  destruct (Z.eqb_spec x a) as [->|Hne]; [injection H as <-; left; reflexivity | right; apply IH; exact H].
Qed.

Lemma wz_add : forall x d : Z, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + d) = Z_to_bv 64 (x + d).
Proof.
  intros x d. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite bv_wrap_add_idemp_l. reflexivity.
Qed.
Lemma wz_wrap : forall x : Z, Z_to_bv 64 (bv_wrap 64 x) = Z_to_bv 64 x.
Proof. intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. lia. Qed.
Lemma wz_small : forall x : Z, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. intros x H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact H. Qed.
Lemma wz_succ : forall x : Z, (Z_to_bv 64 x + 1)%bv = Z_to_bv 64 (x + 1).
Proof.
  intros x. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1 : word)) with 1. rewrite bv_wrap_add_idemp_l. reflexivity.
Qed.
Lemma wz_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y Hx Hy Hne. unfold bv_eqb. rewrite !wz_small by assumption. apply Z.eqb_neq. exact Hne. Qed.
Lemma bv_eqb_true' : forall {n} (x y : bv n), bv_eqb x y = true -> x = y.
Proof. intros n x y H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.
Lemma bv_eq_dec' : forall {n} (x y : bv n), {x = y} + {x <> y}.
Proof. intros n x y. destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned y)) as [H|H]; [left; apply bv_eq; exact H | right; intro Hc; apply H; subst; reflexivity]. Qed.
Lemma bv_eqb_true : forall x y : word, bv_eqb x y = true -> x = y.
Proof. intros x y H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Section Sound.
Context {fx : FPState}.
Variable segs : list Segment.
Variable C : cfg.
Variable E : nat -> word.
Variable M0 : word -> option byte.

Definition vden (v : aval) : word :=
  match v with AL z => Z_to_bv 64 z | AS k off => Z_to_bv 64 (bv_unsigned (E k) + off) end.
Definition bden (b : abyte) : byte :=
  match b with BL z => Z_to_bv 8 z | BS k off i => nth i (word_to_le_bytes 8 (vden (AS k off))) (Z_to_bv 8 0) end.
Definition rbase (rg : region) : Z := bv_unsigned (E (rg_k rg)).
Definition aden (ad : aaddr) : word :=
  match ad with
  | AAbs a => Z_to_bv 64 a
  | ARg j off => match nth_error (c_rgs C) j with Some rg => Z_to_bv 64 (rbase rg + off) | None => Z_to_bv 64 0 end
  end.
Definition rb (M : word -> option byte) (x : word) : option byte :=
  match M x with Some b => Some b | None => seg_rom segs x end.

Record init_ok : Prop := IOK {
  io_hi : 0 < c_abs_hi C <= 2 ^ 62;
  io_kn : forall a ab, In (a, ab) (c_kn0 C) -> rb M0 (Z_to_bv 64 a) = Some (bden ab);
  io_clear : forall a, in_ivs (c_clear C) a = true -> M0 (Z_to_bv 64 a) = None;
  io_zero : forall a, in_ivs (c_zero C) a = true -> rb M0 (Z_to_bv 64 a) = Some (Z_to_bv 8 0);
  io_rg : forall j rg, nth_error (c_rgs C) j = Some rg ->
      c_abs_hi C <= rbase rg + rg_lo rg /\ rbase rg + rg_hi rg <= 2 ^ 64 /\ rbase rg mod 8 = 0 /\
      (forall off, rg_lo rg <= off < rg_hi rg -> M0 (Z_to_bv 64 (rbase rg + off)) <> None);
  io_apart : forall j j' rg rg', nth_error (c_rgs C) j = Some rg -> nth_error (c_rgs C) j' = Some rg' -> j <> j' ->
      rbase rg + rg_hi rg <= rbase rg' + rg_lo rg' \/ rbase rg' + rg_hi rg' <= rbase rg + rg_lo rg
}.
Hypothesis IO : init_ok.

Record msim (s : ast) (M : word -> option byte) : Prop := MSIM {
  ms_abs : forall a ab, PositiveMap.find (zkey a) (s_abs s) = Some ab ->
      0 < a < c_abs_hi C /\ in_ivs (c_wabs C) a = true /\ M (Z_to_bv 64 a) = Some (bden ab);
  ms_rg : forall j rg t off ab, nth_error (c_rgs C) j = Some rg -> nth_error (s_rgs s) j = Some t ->
      PositiveMap.find (zkey off) t = Some ab -> rg_lo rg <= off < rg_hi rg /\ M (Z_to_bv 64 (rbase rg + off)) = Some (bden ab);
  ms_rest : forall x : word, M x = M0 x \/ (exists ab, PositiveMap.find (zkey (bv_unsigned x)) (s_abs s) = Some ab) \/
      (exists j rg, nth_error (c_rgs C) j = Some rg /\ rbase rg + rg_lo rg <= bv_unsigned x < rbase rg + rg_hi rg);
  ms_def : forall j rg off, nth_error (c_rgs C) j = Some rg -> rg_lo rg <= off < rg_hi rg -> M (Z_to_bv 64 (rbase rg + off)) <> None
}.
Record sim (s : ast) (R : bvmap 5 word) (M : word -> option byte) (rv : option word) : Prop := SIM {
  sm_regs : forall r : reg, getr R r = vden (getreg s r);
  sm_rlen : length (s_regs s) = 32%nat;
  sm_r0 : nth 0 (s_regs s) (AL 0) = AL 0;
  sm_mem : msim s M;
  sm_resv : rv = option_map aden (s_resv s)
}.

Lemma aden_abs_u : forall a, 0 < a < c_abs_hi C -> bv_unsigned (aden (AAbs a)) = a.
Proof. intros a H. pose proof (io_hi IO). cbn. apply wz_small. lia. Qed.
Lemma aden_rg_u : forall j rg off, nth_error (c_rgs C) j = Some rg -> rg_lo rg <= off < rg_hi rg ->
  bv_unsigned (aden (ARg j off)) = rbase rg + off /\ c_abs_hi C <= rbase rg + off < 2 ^ 64.
Proof.
  intros j rg off Hj Ho. pose proof (io_hi IO). destruct (io_rg IO j rg Hj) as (H1 & H2 & _).
  cbn. rewrite Hj. split; [apply wz_small|]; lia.
Qed.
Lemma avalid_u : forall ad, avalid C ad = true ->
  exists u, bv_unsigned (aden ad) = u /\ 0 < u < 2 ^ 64 /\
    match ad with AAbs a => u = a /\ a < c_abs_hi C
                | ARg j off => exists rg, nth_error (c_rgs C) j = Some rg /\ rg_lo rg <= off < rg_hi rg /\ u = rbase rg + off /\ c_abs_hi C <= u end.
Proof.
  intros [a|j off] H; cbn [avalid] in H; pose proof (io_hi IO) as Hhi.
  - apply andb_true_iff in H. destruct H as [H1 H2]. exists a. rewrite aden_abs_u by lia. repeat split; lia.
  - destruct (nth_error (c_rgs C) j) as [rg|] eqn:Hj; [|discriminate].
    apply andb_true_iff in H. destruct H as [H1 H2].
    destruct (aden_rg_u j rg off Hj ltac:(lia)) as [Hu Hr]. exists (rbase rg + off). split; [exact Hu|]. split; [lia|].
    exists rg. repeat split; try lia.
Qed.
Lemma aden_neq : forall r ad, avalid C r = true -> avalid C ad = true -> r <> ad -> bv_unsigned (aden r) <> bv_unsigned (aden ad).
Proof.
  intros r ad Hr Ha Hne.
  destruct (avalid_u r Hr) as (u & Hu & Hur & Hk). destruct (avalid_u ad Ha) as (u' & Hu' & Hur' & Hk').
  rewrite Hu, Hu'. intro Heq. subst u'. apply Hne.
  destruct r as [a|j off], ad as [a'|j' off'].
  - destruct Hk, Hk'. congruence.
  - destruct Hk as [Hx Hlt]. destruct Hk' as (rg & _ & _ & _ & Hge). lia.
  - destruct Hk' as [Hx Hlt]. destruct Hk as (rg & _ & _ & _ & Hge). lia.
  - destruct Hk as (rg & Hj & Ho & Hv & _). destruct Hk' as (rg' & Hj' & Ho' & Hv' & _).
    destruct (Nat.eq_dec j j') as [->|Hjj].
    + rewrite Hj in Hj'. injection Hj' as <-. f_equal. lia.
    + exfalso. destruct (io_apart IO j j' rg rg' Hj Hj' Hjj); lia.
Qed.
Lemma aden_shift : forall ad, (match ad with ARg j _ => nth_error (c_rgs C) j <> None | _ => True end) ->
  aden (ashift ad 1) = (aden ad + 1)%bv.
Proof.
  intros [a|j off] H; cbn [ashift aden].
  - symmetry. apply wz_succ.
  - destruct (nth_error (c_rgs C) j) as [rg|]; [|congruence]. rewrite wz_succ. f_equal. lia.
Qed.

Lemma find_rg_sound : forall rgs k off j0 j, find_rg rgs k off j0 = Some j ->
  exists rg, nth_error rgs (j - j0) = Some rg /\ (j0 <= j)%nat /\ rg_k rg = k.
Proof.
  induction rgs as [|rg t IH]; cbn; intros k off j0 j H; [discriminate|].
  destruct (Nat.eqb (rg_k rg) k && (rg_lo rg <=? off) && (off <? rg_hi rg)) eqn:Hc.
  - injection H as <-. exists rg. rewrite Nat.sub_diag. cbn. repeat split; auto.
    apply andb_true_iff in Hc. destruct Hc as [Hc _]. apply andb_true_iff in Hc. destruct Hc as [Hc _]. apply Nat.eqb_eq. exact Hc.
  - destruct (IH k off (S j0) j H) as (rg' & Hn & Hle & Hk). exists rg'. repeat split; [|lia|exact Hk].
    replace (j - j0)%nat with (S (j - S j0)) by lia. exact Hn.
Qed.
Lemma classify_sound : forall v ad, classify C v = Some ad -> aden ad = vden v.
Proof.
  intros [z|k off] ad H; cbn in H.
  - injection H as <-. reflexivity.
  - destruct (find_rg (c_rgs C) k off 0) as [j|] eqn:Hf; [|discriminate]. injection H as <-.
    destruct (find_rg_sound _ _ _ _ _ Hf) as (rg & Hn & _ & Hk). rewrite Nat.sub_0_r in Hn.
    cbn. rewrite Hn. unfold rbase. rewrite Hk. reflexivity.
Qed.
Lemma vden_aaddi : forall v imm, vden (aaddi v imm) = v_addi (vden v) imm.
Proof.
  intros [z|k off] imm; cbn [aaddi vden]; unfold v_addi.
  - rewrite wz_wrap, wz_add. reflexivity.
  - rewrite wz_add. f_equal. lia.
Qed.

Lemma rnat_lt : forall r : reg, (rnat r < 32)%nat.
Proof. intros r. unfold rnat. pose proof (bv_unsigned_in_range 5 r) as H. change (bv_modulus 5) with 32 in H. lia. Qed.
Lemma rnat_inj : forall r r' : reg, rnat r = rnat r' -> r = r'.
Proof.
  intros r r' H. apply bv_eq. unfold rnat in H.
  pose proof (bv_unsigned_in_range 5 r). pose proof (bv_unsigned_in_range 5 r'). lia.
Qed.
Lemma rnat_0 : forall r : reg, bv_eqb r 0%bv = true -> rnat r = 0%nat.
Proof. intros r H. apply bv_eqb_true' in H. subst r. reflexivity. Qed.

Lemma vden_wlit : forall w : word, vden (wlit w) = w.
Proof. intros w. cbn. apply Z_to_bv_bv_unsigned. Qed.

Lemma sim_setreg : forall s R M rv rd v w, sim s R M rv -> vden v = w ->
  sim (setreg s rd v) (if bv_eqb rd 0%bv then R else regupd R rd w) M rv.
Proof.
  intros s R M rv rd v w [Hr Hl H0 Hm Hv] Hvw. unfold setreg.
  destruct (bv_eqb rd 0%bv) eqn:Hz; [constructor; assumption|].
  assert (Hrd : (rd <> 0)%bv) by (intro Hc; subst rd; discriminate Hz).
  assert (Hn0 : rnat rd <> 0%nat). { intro Hc. apply Hrd. apply rnat_inj. exact Hc. }
  constructor; cbn [s_regs s_abs s_rgs s_resv s_pc]; try assumption.
  - intros r. unfold getreg. cbn [s_regs]. destruct (bv_eq_dec' r rd) as [->|Hne].
    + rewrite getr_same by exact Hrd. rewrite nth_upd_same by (rewrite Hl; apply rnat_lt). symmetry. exact Hvw.
    + rewrite getr_other by exact Hne. rewrite nth_upd_other by (intro Hc; apply Hne; symmetry; apply rnat_inj; exact Hc). apply Hr.
  - rewrite upd_length. exact Hl.
  - rewrite nth_upd_other by exact Hn0. exact H0.
  - destruct Hm. constructor; assumption.
Qed.

Lemma msim_untouched_abs : forall s M a, msim s M -> 0 < a < c_abs_hi C -> PositiveMap.find (zkey a) (s_abs s) = None ->
  M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a).
Proof.
  intros s M a Hm Ha Hf. pose proof (io_hi IO) as Hhi.
  destruct (ms_rest s M Hm (Z_to_bv 64 a)) as [H|[(ab & H)|(j & rg & Hj & Hr)]]; [exact H| |].
  - rewrite wz_small in H by lia. congruence.
  - rewrite wz_small in Hr by lia. destruct (io_rg IO j rg Hj) as (H1 & _). lia.
Qed.

Lemma rdb_sound : forall s M ad ab, msim s M -> rdb segs C s ad = Some ab -> rb M (aden ad) = Some (bden ab).
Proof.
  intros s M [a|j off] ab Hm H; cbn [rdb] in H.
  - destruct ((0 <? a) && (a <? c_abs_hi C)) eqn:Hr; [|discriminate].
    apply andb_true_iff in Hr. destruct Hr as [Hr1 Hr2]. apply Z.ltb_lt in Hr1, Hr2.
    destruct (PositiveMap.find (zkey a) (s_abs s)) as [b|] eqn:Hf.
    + injection H as <-. destruct (ms_abs s M Hm a b Hf) as (_ & _ & HM). unfold rb. cbn [aden]. rewrite HM. reflexivity.
    + pose proof (msim_untouched_abs s M a Hm ltac:(lia) Hf) as HM.
      destruct (kn_find (c_kn0 C) a) as [b|] eqn:Hk.
      * injection H as <-. pose proof (io_kn IO a b (kn_find_in _ _ _ Hk)) as Hkn. unfold rb in *. cbn [aden]. rewrite HM. exact Hkn.
      * destruct (in_ivs (c_clear C) a) eqn:Hc.
        -- pose proof (io_clear IO a Hc) as H0. unfold rb. cbn [aden]. rewrite HM, H0.
           destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [|discriminate]. injection H as <-.
           cbn [bden]. rewrite Z_to_bv_bv_unsigned. reflexivity.
        -- destruct (in_ivs (c_zero C) a) eqn:Hz; [|discriminate]. injection H as <-.
           pose proof (io_zero IO a Hz) as H0. unfold rb in *. cbn [aden bden]. rewrite HM. exact H0.
  - destruct (nth_error (c_rgs C) j) as [rg|] eqn:Hj; [|discriminate].
    destruct (nth_error (s_rgs s) j) as [t|] eqn:Ht; [|discriminate].
    destruct ((rg_lo rg <=? off) && (off <? rg_hi rg)); [|discriminate].
    destruct (ms_rg s M Hm j rg t off ab Hj Ht H) as (_ & HM). unfold rb. cbn [aden]. rewrite Hj, HM. reflexivity.
Qed.
Lemma rdb_some_rg : forall s ad ab, rdb segs C s ad = Some ab -> match ad with ARg j _ => nth_error (c_rgs C) j <> None | _ => True end.
Proof. intros s [a|j off] ab H; [exact I|]. cbn [rdb] in H. destruct (nth_error (c_rgs C) j); [discriminate|discriminate]. Qed.

Lemma rdbs_sound : forall s M n ad l, msim s M -> rdbs segs C s ad n = Some l -> rdn segs M (aden ad) n = Some (map bden l).
Proof.
  intros s M n. induction n as [|n IH]; intros ad l Hm H; cbn [rdbs] in H.
  - injection H as <-. reflexivity.
  - destruct (rdb segs C s ad) as [b|] eqn:Hb; [|discriminate].
    destruct (rdbs segs C s (ashift ad 1) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    pose proof (rdb_sound s M ad b Hm Hb) as H1. unfold rb in H1.
    pose proof (IH _ _ Hm Hr) as H2. rewrite (aden_shift ad (rdb_some_rg s ad b Hb)) in H2.
    cbn [rdn map]. rewrite H1, H2. reflexivity.
Qed.
Lemma rdbs_length : forall s n ad l, rdbs segs C s ad n = Some l -> length l = n.
Proof.
  intros s n. induction n as [|n IH]; intros ad l H; cbn [rdbs] in H.
  - injection H as <-. reflexivity.
  - destruct (rdb segs C s ad); [|discriminate]. destruct (rdbs segs C s (ashift ad 1) n) eqn:Hr; [|discriminate].
    injection H as <-. cbn. f_equal. eapply IH. exact Hr.
Qed.

Lemma lits_sound : forall l zs, lits l = Some zs -> map bden l = zbytes zs.
Proof.
  induction l as [|[b|k o i] t IH]; cbn; intros zs H; try discriminate.
  - injection H as <-. reflexivity.
  - destruct (lits t) as [r|]; [|discriminate]. injection H as <-. cbn. f_equal. apply IH. reflexivity.
Qed.
Lemma le8_nths : forall w : word, let l := word_to_le_bytes 8 w in let d := Z_to_bv 8 0 in
  [nth 0 l d; nth 1 l d; nth 2 l d; nth 3 l d; nth 4 l d; nth 5 l d; nth 6 l d; nth 7 l d] = l.
Proof.
  intros w l d. pose proof (length_N_to_le_bytes 8 w) as Hl. fold l in Hl.
  destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 t]]]]]]]]]; cbn in Hl; try discriminate. reflexivity.
Qed.
Lemma sym8_bytes : forall k o, map bden [BS k o 0; BS k o 1; BS k o 2; BS k o 3; BS k o 4; BS k o 5; BS k o 6; BS k o 7]
  = word_to_le_bytes 8 (vden (AS k o)).
Proof. intros k o. cbn [map bden]. apply le8_nths. Qed.
Lemma is_sym8_sound : forall l v, is_sym8 l = Some v -> map bden l = word_to_le_bytes 8 (vden v).
Proof.
  intros l v H. unfold is_sym8 in H.
  destruct l as [|[?|k o [|?]] l]; try discriminate.
  destruct l as [|[?|k1 o1 [|[|?]]] l]; try discriminate.
  destruct l as [|[?|k2 o2 [|[|[|?]]]] l]; try discriminate.
  destruct l as [|[?|k3 o3 [|[|[|[|?]]]]] l]; try discriminate.
  destruct l as [|[?|k4 o4 [|[|[|[|[|?]]]]]] l]; try discriminate.
  destruct l as [|[?|k5 o5 [|[|[|[|[|[|?]]]]]]] l]; try discriminate.
  destruct l as [|[?|k6 o6 [|[|[|[|[|[|[|?]]]]]]]] l]; try discriminate.
  destruct l as [|[?|k7 o7 [|[|[|[|[|[|[|[|?]]]]]]]]] l]; try discriminate.
  destruct l; try discriminate.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
  cbn [aval_eqb] in Hc.
  repeat (apply andb_true_iff in Hc; destruct Hc as [Hc ?]).
  repeat match goal with
         | Hq : _ && _ = true |- _ => apply andb_true_iff in Hq; destruct Hq
         | Hq : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in Hq; subst
         | Hq : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hq; subst
         end.
  apply sym8_bytes.
Qed.
Lemma load8_le : forall (w : word) sx, load_result SZ8 sx (word_to_le_bytes 8 w) = w.
Proof.
  intros w sx. unfold load_result.
  rewrite (le_word_v (word_to_le_bytes 8 w) w) by (rewrite <- n_to_le_8_spec; apply bytes_le_n_to_le_8).
  apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned.
Qed.
Lemma load_val_sound : forall sz sx l v, load_val sz sx l = Some v -> vden v = load_result sz sx (map bden l).
Proof.
  intros sz sx l v H. unfold load_val in H. destruct (lits l) as [zs|] eqn:Hl.
  - injection H as <-. rewrite vden_wlit, (lits_sound l zs Hl). reflexivity.
  - destruct sz; try discriminate. rewrite (is_sym8_sound l v H), load8_le. reflexivity.
Qed.
Lemma blits_den : forall bs, map bden (blits bs) = bs.
Proof. induction bs as [|b t IH]; cbn; [reflexivity|]. rewrite Z_to_bv_bv_unsigned. f_equal. exact IH. Qed.
Lemma store_bytes_sound : forall n v l, store_bytes n v = Some l -> map bden l = word_to_le_bytes n (vden v) /\ length l = n.
Proof.
  intros n [z|k o] l H; cbn [store_bytes] in H.
  - injection H as <-. rewrite blits_den. split; [reflexivity|]. unfold blits. rewrite length_map. apply length_N_to_le_bytes.
  - destruct (Nat.eqb n 8) eqn:Hn; [|discriminate]. apply Nat.eqb_eq in Hn. subst n. injection H as <-.
    split; [apply sym8_bytes | reflexivity].
Qed.

Definition wr1 (M : word -> option byte) (x : word) (b : byte) : word -> option byte :=
  fun y => if bv_eqb y x then Some b else M y.
Definition has_rg (s : ast) (ad : aaddr) : Prop :=
  match ad with ARg j _ => nth_error (s_rgs s) j <> None | _ => True end.

Lemma wr_chk_valid : forall ad, wr_chk segs C ad = true -> avalid C ad = true.
Proof.
  intros [a|j off] H; cbn [wr_chk avalid] in *; [|exact H].
  apply andb_true_iff in H. destruct H as [H _]. apply andb_true_iff in H. destruct H as [H _]. exact H.
Qed.

Lemma wr1_other : forall M x b y, bv_unsigned y <> bv_unsigned x -> wr1 M x b y = M y.
Proof. intros M x b y H. unfold wr1, bv_eqb. destruct (Z.eqb_spec (bv_unsigned y) (bv_unsigned x)); [contradiction|reflexivity]. Qed.
Lemma wr1_same : forall M x b, wr1 M x b x = Some b.
Proof. intros M x b. unfold wr1. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma wrb_sound : forall s M ad ab, msim s M -> wr_chk segs C ad = true -> has_rg s ad ->
  msim (wrb s ad ab) (wr1 M (aden ad) (bden ab)).
Proof.
  intros s M ad ab Hm Hchk Hhas. pose proof (wr_chk_valid ad Hchk) as Hval. pose proof (io_hi IO) as Hhi.
  destruct (avalid_u ad Hval) as (u & Hu & Hur & Hk).
  assert (Hoth : forall ad', avalid C ad' = true -> ad' <> ad -> wr1 M (aden ad) (bden ab) (aden ad') = M (aden ad')).
  { intros ad' Hv' Hne. apply wr1_other. apply aden_neq; assumption. }
  destruct ad as [a|j off]; cbn [wrb].
  - destruct Hk as [-> Halt].
    cbn [wr_chk] in Hchk. apply andb_true_iff in Hchk. destruct Hchk as [Hchk _]. apply andb_true_iff in Hchk. destruct Hchk as [_ Hw].
    constructor; cbn [s_abs s_rgs].
    + intros a' ab' Hf. destruct (Z.eq_dec a' a) as [->|Hne].
      * rewrite PositiveMap.gss in Hf. injection Hf as <-. repeat split; try lia; [exact Hw|]. apply wr1_same.
      * rewrite PositiveMap.gso in Hf by (intro Hc; apply Hne; apply zkey_inj; exact Hc).
        destruct (ms_abs s M Hm a' ab' Hf) as (Hr & Hw' & HM). repeat split; try lia; [exact Hw'|].
        change (Z_to_bv 64 a') with (aden (AAbs a')). rewrite Hoth; [exact HM | | congruence].
        cbn [avalid]. apply andb_true_iff. split; [apply Z.ltb_lt | apply Z.ltb_lt]; lia.
    + intros j rg t off ab' Hj Ht Hf. destruct (ms_rg s M Hm j rg t off ab' Hj Ht Hf) as (Hr & HM). split; [exact Hr|].
      pose proof (Hoth (ARg j off)) as Ho. cbn [aden avalid] in Ho |- *. rewrite Hj in Ho. rewrite Ho; [exact HM | | discriminate].
      apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    + intros x. destruct (Z.eq_dec (bv_unsigned x) a) as [Hx|Hx].
      * right. left. exists ab. rewrite Hx. apply PositiveMap.gss.
      * rewrite wr1_other by (rewrite Hu; exact Hx).
        destruct (ms_rest s M Hm x) as [H|[(ab' & H)|H]]; [left; exact H | | right; right; exact H].
        right. left. exists ab'. rewrite PositiveMap.gso; [exact H|]. intro Hc. apply Hx. apply zkey_inj. exact Hc.
    + intros j rg off Hj Ho. unfold wr1. destruct (bv_eqb _ _); [discriminate | apply (ms_def s M Hm j rg off Hj Ho)].
  - destruct Hk as (rg & Hj & Ho & -> & Hge). cbn [has_rg] in Hhas.
    destruct (nth_error (s_rgs s) j) as [t|] eqn:Ht; [|congruence].
    assert (Hjl : (j < length (s_rgs s))%nat) by (apply nth_error_Some; congruence).
    assert (Had : aden (ARg j off) = Z_to_bv 64 (rbase rg + off)) by (cbn [aden]; rewrite Hj; reflexivity).
    rewrite Had in *.
    constructor; cbn [s_abs s_rgs].
    + intros a' ab' Hf. destruct (ms_abs s M Hm a' ab' Hf) as (Hr & Hw' & HM). repeat split; try lia; [exact Hw'|].
      change (Z_to_bv 64 a') with (aden (AAbs a')). rewrite Hoth; [exact HM | | discriminate].
      cbn [avalid]. apply andb_true_iff. split; [apply Z.ltb_lt | apply Z.ltb_lt]; lia.
    + intros j' rg' t' off' ab' Hj' Ht' Hf. destruct (Nat.eq_dec j' j) as [->|Hjj].
      * rewrite Hj in Hj'. injection Hj' as <-. rewrite nth_error_upd_same in Ht' by exact Hjl. injection Ht' as <-.
        destruct (Z.eq_dec off' off) as [->|Hoo].
        -- rewrite PositiveMap.gss in Hf. injection Hf as <-. split; [lia|].
           apply wr1_same.
        -- rewrite PositiveMap.gso in Hf by (intro Hc; apply Hoo; apply zkey_inj; exact Hc).
           destruct (ms_rg s M Hm j rg t off' ab' Hj Ht Hf) as (Hr & HM). split; [exact Hr|].
           pose proof (Hoth (ARg j off')) as Hot. cbn [aden avalid] in Hot. rewrite Hj in Hot. rewrite Hot; [exact HM | | congruence].
           apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
      * rewrite nth_error_upd_other in Ht' by (intro Hc; apply Hjj; symmetry; exact Hc).
        destruct (ms_rg s M Hm j' rg' t' off' ab' Hj' Ht' Hf) as (Hr & HM). split; [exact Hr|].
        pose proof (Hoth (ARg j' off')) as Hot. cbn [aden avalid] in Hot. rewrite Hj' in Hot. rewrite Hot; [exact HM | | congruence].
        apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    + intros x. destruct (Z.eq_dec (bv_unsigned x) (rbase rg + off)) as [Hx|Hx].
      * right. right. exists j, rg. split; [exact Hj | lia].
      * rewrite wr1_other by (rewrite Hu; exact Hx). apply (ms_rest s M Hm x).
    + intros j' rg' off' Hj' Ho'. unfold wr1. destruct (bv_eqb _ _); [discriminate | apply (ms_def s M Hm j' rg' off' Hj' Ho')].
Qed.

Fixpoint wr_chks (ad : aaddr) (n : nat) : bool :=
  match n with O => true | S n' => wr_chk segs C ad && wr_chks (ashift ad 1) n' end.

Lemma wr_chk_rg : forall ad, wr_chk segs C ad = true -> match ad with ARg j _ => nth_error (c_rgs C) j <> None | _ => True end.
Proof. intros [a|j off] H; [exact I|]. cbn [wr_chk] in H. destruct (nth_error (c_rgs C) j); [discriminate|discriminate]. Qed.

Lemma wrbs_sound : forall l s M ad s', msim s M -> wrbs segs C s ad l = Some s' ->
  msim s' (wbytes M (aden ad) (map bden l)) /\ wr_chks ad (length l) = true /\
  s_regs s' = s_regs s /\ s_pc s' = s_pc s /\ s_resv s' = s_resv s.
Proof.
  induction l as [|b t IH]; intros s M ad s' Hm H; cbn [wrbs] in H.
  - injection H as <-. cbn. auto.
  - match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    apply andb_true_iff in Hc. destruct Hc as [Hchk Hhas].
    assert (Hh : has_rg s ad). { destruct ad as [a|j off]; cbn; [exact I|]. destruct (nth_error (s_rgs s) j); [discriminate|discriminate]. }
    pose proof (wrb_sound s M ad b Hm Hchk Hh) as Hm1.
    destruct (IH _ _ _ _ Hm1 H) as (Hm' & Hcs & Hr & Hp & Hv).
    rewrite (aden_shift ad (wr_chk_rg ad Hchk)) in Hm'.
    split; [exact Hm'|]. split; [cbn [length wr_chks]; rewrite Hchk, Hcs; reflexivity|].
    destruct ad; cbn [wrb s_regs s_pc s_resv] in Hr, Hp, Hv; auto.
Qed.

Lemma store_ok_chks : forall n ad s M, msim s M -> wr_chks ad n = true -> store_ok segs M (aden ad) n = true.
Proof.
  induction n as [|n IH]; intros ad s M Hm H; [reflexivity|].
  cbn [wr_chks] in H. apply andb_true_iff in H. destruct H as [Hchk Hcs].
  cbn [store_ok]. rewrite <- (aden_shift ad (wr_chk_rg ad Hchk)). rewrite (IH _ s M Hm Hcs).
  assert (Hw : wview segs M (aden ad) <> None).
  { destruct ad as [a|j off]; cbn [wr_chk] in Hchk.
    - apply andb_true_iff in Hchk. destruct Hchk as [_ Hwr]. unfold abs_wr in Hwr. cbn [aden].
      unfold wview in *. destruct (M (Z_to_bv 64 a)); [discriminate|].
      destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|]; [|discriminate].
      destruct (seg_writable sg); [|discriminate].
      destruct (segment_byte_at _ _); [discriminate|discriminate].
    - destruct (nth_error (c_rgs C) j) as [rg|] eqn:Hj; [|discriminate].
      apply andb_true_iff in Hchk. destruct Hchk as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      pose proof (ms_def s M Hm j rg off Hj ltac:(lia)) as Hd. cbn [aden]. rewrite Hj. unfold wview.
      destruct (M (Z_to_bv 64 (rbase rg + off))); [discriminate|congruence]. }
  destruct (wview segs M (aden ad)); [reflexivity|congruence].
Qed.

Lemma resv_upd_sound : forall o ad o', resv_upd C o ad = Some o' ->
  resv_inval_w (option_map aden o) (aden ad) = option_map aden o'.
Proof.
  intros [r|] ad o' H; cbn [resv_upd] in H; [|injection H as <-; reflexivity].
  cbn [option_map resv_inval_w]. destruct (aaddr_eqb r ad) eqn:He.
  - injection H as <-. apply aaddr_eqb_eq in He. subst r. rewrite Z.eqb_refl. reflexivity.
  - destruct (avalid C r && avalid C ad) eqn:Hv; [|discriminate]. injection H as <-.
    apply andb_true_iff in Hv. destruct Hv as [Hv1 Hv2].
    pose proof (aden_neq r ad Hv1 Hv2 (aaddr_eqb_neq _ _ He)) as Hne.
    destruct (Z.eqb_spec (bv_unsigned (aden r)) (bv_unsigned (aden ad))); [contradiction|reflexivity].
Qed.
Lemma aalign_sound : forall ad wd, aalign C ad (amo_bytes wd) = true -> bv_unsigned (aden ad) mod amo_bytes wd = 0.
Proof.
  intros ad wd H. unfold aalign in H. apply andb_true_iff in H. destruct H as [Hv Ha].
  destruct (avalid_u ad Hv) as (u & Hu & Hur & Hk). rewrite Hu.
  destruct ad as [a|j off].
  - destruct Hk as [-> _]. apply Z.eqb_eq. exact Ha.
  - destruct Hk as (rg & Hj & Ho & -> & _). apply Z.eqb_eq in Ha.
    destruct (io_rg IO j rg Hj) as (_ & _ & H8 & _).
    assert (Hb : rbase rg mod amo_bytes wd = 0).
    { destruct wd; cbn [amo_bytes]; [|exact H8].
      rewrite (Z.div_mod (rbase rg) 8) by lia. rewrite H8, Z.add_0_r. replace (8 * (rbase rg / 8)) with ((2 * (rbase rg / 8)) * 4) by lia.
      apply Z.mod_mul. lia. }
    rewrite Z.add_mod by (destruct wd; cbn; lia). rewrite Hb, Ha. cbn. destruct wd; reflexivity.
Qed.
Lemma fetch_entry_sound : forall pc i, fetch_entry segs pc = Some i ->
  exists w, fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4).
Proof.
  intros pc i H. unfold fetch_entry in H. destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|]; [|discriminate].
  exists w. destruct (is_ecall w); [discriminate|]. destruct (decode_any w) as [[i' sz]|]; [|discriminate].
  destruct (Z.eqb_spec sz 4); [|discriminate]. subst sz. injection H as <-. auto.
Qed.

Lemma abranch_sound : forall c a b t, abranch c a b = Some t -> branch_taken c (vden a) (vden b) = t.
Proof.
  intros c a b t H. unfold abranch in H.
  assert (Hg : (if aval_eqb a b then match c with BC_EQ => Some true | BC_NE => Some false | _ => None end else None) = Some t ->
               branch_taken c (vden a) (vden b) = t).
  { intros Hq. destruct (aval_eqb a b) eqn:Hab; [|discriminate]. apply aval_eqb_eq in Hab. subst b.
    destruct c; try discriminate; injection Hq as <-; cbn [branch_taken]; rewrite bv_eqb_refl; reflexivity. }
  destruct a as [x|k o], b as [y|k' o']; try (apply Hg; exact H).
  injection H as <-. reflexivity.
Qed.

Variable rom : word -> option byte.

Lemma wz_id : forall w : word, Z_to_bv 64 (bv_unsigned w) = w.
Proof. intros w. apply Z_to_bv_bv_unsigned. Qed.
Lemma pc_setreg : forall s rd v, s_pc (setreg s rd v) = s_pc s.
Proof. intros s rd v. unfold setreg. destruct (bv_eqb rd 0%bv); reflexivity. Qed.
Lemma pcw_setpc : forall s w, pcw (setpc s (bv_unsigned w)) = w.
Proof. intros s w. unfold pcw, setpc. cbn [s_pc]. apply wz_id. Qed.
Lemma pcw_setreg : forall s rd v, pcw (setreg s rd v) = pcw s.
Proof. intros. unfold pcw. rewrite pc_setreg. reflexivity. Qed.
Lemma pcw_setresv : forall s o, pcw (setresv s o) = pcw s.
Proof. reflexivity. Qed.
Lemma pcw_next : forall s, pcw (next s) = v_addi (pcw s) 4.
Proof. intros s. unfold next. apply pcw_setpc. Qed.

Lemma sim_setpc : forall s R M rv z, sim s R M rv -> sim (setpc s z) R M rv.
Proof. intros s R M rv z [H1 H2 H3 [A B D F] H5]. constructor; try assumption. constructor; assumption. Qed.
Lemma sim_next : forall s R M rv, sim s R M rv -> sim (next s) R M rv.
Proof. intros. apply sim_setpc. assumption. Qed.
Lemma sim_setresv : forall s R M rv o, sim s R M rv -> sim (setresv s o) R M (option_map aden o).
Proof. intros s R M rv o [H1 H2 H3 [A B D F] H5]. constructor; try assumption; [constructor; assumption | reflexivity]. Qed.
Lemma sim_newmem : forall s s' R M M' rv, sim s R M rv -> msim s' M' -> s_regs s' = s_regs s -> s_resv s' = s_resv s -> sim s' R M' rv.
Proof.
  intros s s' R M M' rv [H1 H2 H3 H4 H5] Hm Hr Hv. constructor; try assumption.
  - intros r. unfold getreg. rewrite Hr. apply H1.
  - rewrite Hr. exact H2.
  - rewrite Hr. exact H3.
  - rewrite Hv. exact H5.
Qed.
Lemma getreg_newmem : forall s s' r, s_regs s' = s_regs s -> getreg s' r = getreg s r.
Proof. intros s s' r H. unfold getreg. rewrite H. reflexivity. Qed.

Ltac regeq Hsim rs Hg Hn :=
  pose proof (sm_regs _ _ _ _ Hsim rs) as Hn; rewrite Hg in Hn; cbn [vden] in Hn.

Lemma astep_sound : forall s R M rv, sim s R M rv ->
  match astep segs C s with
  | SNext s' => exists R' M' rv', RiscvSemantics.step segs (mkstR R (pcw s) M rom rv) = MachineOk (mkstR R' (pcw s') M' rom rv') /\ sim s' R' M' rv'
  | SFin s' v imm => exists R', RiscvSemantics.step segs (mkstR R (pcw s) M rom rv) = MachineOk (mkstR R' (v_jalr (vden v) imm) M rom rv) /\ sim s' R' M rv
  | SStuck _ => True
  end.
Proof.
  intros s R M rv Hsim. unfold astep.
  destruct (fetch_entry segs (s_pc s)) as [i|] eqn:Hfe; [|exact I].
  destruct (fetch_entry_sound _ _ Hfe) as (w & Hf & He & Hd). fold (pcw s) in Hf.
  destruct i; try exact I.
  -
    eexists _, M, rv. rewrite pcw_next, pcw_setreg. split; [apply (stepR_lui segs R (pcw s) M rom rv w rd imm Hf He Hd)|].
    apply sim_next. apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    eexists _, M, rv. rewrite pcw_next, pcw_setreg. split; [apply (stepR_auipc segs R (pcw s) M rom rv w rd imm Hf He Hd)|].
    apply sim_next. apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    eexists _, M, rv. rewrite pcw_setpc. split; [apply (stepR_jal_link segs R (pcw s) M rom rv w rd imm Hf He Hd)|].
    apply sim_setpc. apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    destruct (getreg s rs1) as [x|k o] eqn:Hg.
    + regeq Hsim rs1 Hg Hr1. eexists _, M, rv. rewrite pcw_setpc. rewrite <- Hr1.
      split; [apply (stepR_jalr segs R (pcw s) M rom rv w rd rs1 imm Hf He Hd)|].
      apply sim_setpc. apply sim_setreg; [exact Hsim | apply vden_wlit].
    + pose proof (sm_regs _ _ _ _ Hsim rs1) as Hr1. rewrite Hg in Hr1. eexists. rewrite <- Hr1.
      split; [apply (stepR_jalr segs R (pcw s) M rom rv w rd rs1 imm Hf He Hd)|].
      apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    destruct (abranch c (getreg s rs1) (getreg s rs2)) as [[|]|] eqn:Htk; try exact I.
    + eexists R, M, rv. rewrite pcw_setpc. split; [|apply sim_setpc; exact Hsim].
      apply (stepR_branch_tk_gen segs R (pcw s) M rom rv w c rs1 rs2 imm Hf He Hd).
      rewrite (sm_regs _ _ _ _ Hsim rs1), (sm_regs _ _ _ _ Hsim rs2). apply abranch_sound. exact Htk.
    + eexists R, M, rv. rewrite pcw_next. split; [|apply sim_next; exact Hsim].
      apply (stepR_branch_ft_gen segs R (pcw s) M rom rv w c rs1 rs2 imm Hf He Hd).
      rewrite (sm_regs _ _ _ _ Hsim rs1), (sm_regs _ _ _ _ Hsim rs2). apply abranch_sound. exact Htk.
  -
    destruct (classify C (aaddi (getreg s rs1) (bv_signed imm))) as [ad|] eqn:Hcl; [|exact I].
    destruct (rdbs segs C s ad (msize_bytes sz)) as [l|] eqn:Hrd; [|exact I].
    destruct (load_val sz signed l) as [v|] eqn:Hlv; [|exact I].
    pose proof (classify_sound _ _ Hcl) as Had. rewrite vden_aaddi, <- (sm_regs _ _ _ _ Hsim rs1) in Had.
    pose proof (rdbs_sound s M _ _ _ (sm_mem _ _ _ _ Hsim) Hrd) as Hrn. rewrite Had in Hrn.
    eexists _, M, rv. rewrite pcw_next, pcw_setreg.
    split; [apply (stepR_load segs R (pcw s) M rom rv w sz signed rd rs1 imm _ Hf He Hd Hrn)|].
    apply sim_next. apply sim_setreg; [exact Hsim | apply load_val_sound; exact Hlv].
  -
    destruct (classify C (aaddi (getreg s rs1) (bv_signed imm))) as [ad|] eqn:Hcl; [|exact I].
    destruct (store_bytes (msize_bytes sz) (getreg s rs2)) as [l|] eqn:Hsb; [|exact I].
    destruct (resv_upd C (s_resv s) ad) as [rv'|] eqn:Hru; [|exact I].
    destruct (wrbs segs C s ad l) as [s'|] eqn:Hwr; [|exact I].
    pose proof (classify_sound _ _ Hcl) as Had. rewrite vden_aaddi, <- (sm_regs _ _ _ _ Hsim rs1) in Had.
    destruct (store_bytes_sound _ _ _ Hsb) as [Hbs Hlen]. rewrite <- (sm_regs _ _ _ _ Hsim rs2) in Hbs.
    destruct (wrbs_sound _ _ _ _ _ (sm_mem _ _ _ _ Hsim) Hwr) as (Hm' & Hcs & Hr' & Hp' & Hv').
    pose proof (store_ok_chks _ _ _ _ (sm_mem _ _ _ _ Hsim) Hcs) as Hok. rewrite Hlen, Had in Hok.
    pose proof (resv_upd_sound _ _ _ Hru) as Hrs. rewrite <- (sm_resv _ _ _ _ Hsim), Had in Hrs.
    rewrite Hbs, Had in Hm'.
    eexists R, _, _. rewrite pcw_next, pcw_setresv. unfold pcw. rewrite Hp'. fold (pcw s).
    split; [apply (stepR_store segs R (pcw s) M rom rv w sz rs1 rs2 imm Hf He Hd Hok)|].
    apply sim_next. rewrite Hrs. eapply sim_setresv. eapply sim_newmem; [exact Hsim | exact Hm' | exact Hr' | exact Hv'].
  -
    destruct (getreg s rs1) as [x|k o] eqn:Hg.
    + regeq Hsim rs1 Hg Hr1. eexists _, M, rv. rewrite pcw_next, pcw_setreg. rewrite <- Hr1.
      split; [apply (stepR_opimm_gen segs R (pcw s) M rom rv w op rd rs1 imm Hf He Hd)|].
      apply sim_next. apply sim_setreg; [exact Hsim | apply vden_wlit].
    + destruct op; try exact I.
      pose proof (sm_regs _ _ _ _ Hsim rs1) as Hr1. rewrite Hg in Hr1.
      eexists _, M, rv. rewrite pcw_next, pcw_setreg.
      split; [apply (stepR_opimm_gen segs R (pcw s) M rom rv w ALU_ADD rd rs1 imm Hf He Hd)|].
      apply sim_next. apply sim_setreg; [exact Hsim|].
      rewrite alu_addi, Hr1. change (AS k (o + bv_signed imm)) with (aaddi (AS k o) (bv_signed imm)). apply vden_aaddi.
  -
    destruct (getreg s rs1) as [x|k o] eqn:Hg; [|exact I].
    regeq Hsim rs1 Hg Hr1. eexists _, M, rv. rewrite pcw_next, pcw_setreg. rewrite <- Hr1.
    split; [apply (stepR_shiftimm_gen segs R (pcw s) M rom rv w op rd rs1 shamt Hf He Hd)|].
    apply sim_next. apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    destruct (getreg s rs1) as [x|k o] eqn:Hg1; [|exact I]. destruct (getreg s rs2) as [y|k' o'] eqn:Hg2; [|exact I].
    regeq Hsim rs1 Hg1 Hr1. regeq Hsim rs2 Hg2 Hr2. eexists _, M, rv. rewrite pcw_next, pcw_setreg. rewrite <- Hr1, <- Hr2.
    split; [apply (stepR_op_gen segs R (pcw s) M rom rv w op rd rs1 rs2 Hf He Hd)|].
    apply sim_next. apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    destruct (getreg s rs1) as [x|k o] eqn:Hg; [|exact I].
    regeq Hsim rs1 Hg Hr1. eexists _, M, rv. rewrite pcw_next, pcw_setreg. rewrite <- Hr1.
    split; [apply (stepR_opimm32_gen segs R (pcw s) M rom rv w rd rs1 imm Hf He Hd)|].
    apply sim_next. apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    destruct (getreg s rs1) as [x|k o] eqn:Hg; [|exact I].
    regeq Hsim rs1 Hg Hr1. eexists _, M, rv. rewrite pcw_next, pcw_setreg. rewrite <- Hr1.
    split; [apply (stepR_shiftimm32_gen segs R (pcw s) M rom rv w op rd rs1 shamt Hf He Hd)|].
    apply sim_next. apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    destruct (getreg s rs1) as [x|k o] eqn:Hg1; [|exact I]. destruct (getreg s rs2) as [y|k' o'] eqn:Hg2; [|exact I].
    regeq Hsim rs1 Hg1 Hr1. regeq Hsim rs2 Hg2 Hr2. eexists _, M, rv. rewrite pcw_next, pcw_setreg. rewrite <- Hr1, <- Hr2.
    split; [apply (stepR_op32_gen segs R (pcw s) M rom rv w op rd rs1 rs2 Hf He Hd)|].
    apply sim_next. apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    eexists R, M, rv. rewrite pcw_next. split; [apply (stepR_fence segs R (pcw s) M rom rv w fm pred succ rd rs1 Hf He Hd)|].
    apply sim_next. exact Hsim.
  -
    destruct (getreg s rs1) as [x|k o] eqn:Hg1; [|exact I]. destruct (getreg s rs2) as [y|k' o'] eqn:Hg2; [|exact I].
    regeq Hsim rs1 Hg1 Hr1. regeq Hsim rs2 Hg2 Hr2. eexists _, M, rv. rewrite pcw_next, pcw_setreg. rewrite <- Hr1, <- Hr2.
    split; [apply (stepR_mul_gen segs R (pcw s) M rom rv w op rd rs1 rs2 Hf He Hd)|].
    apply sim_next. apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    destruct (getreg s rs1) as [x|k o] eqn:Hg1; [|exact I]. destruct (getreg s rs2) as [y|k' o'] eqn:Hg2; [|exact I].
    regeq Hsim rs1 Hg1 Hr1. regeq Hsim rs2 Hg2 Hr2. eexists _, M, rv. rewrite pcw_next, pcw_setreg. rewrite <- Hr1, <- Hr2.
    split; [apply (stepR_mul32_gen segs R (pcw s) M rom rv w op rd rs1 rs2 Hf He Hd)|].
    apply sim_next. apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    destruct (classify C (getreg s rs1)) as [ad|] eqn:Hcl; [|exact I].
    destruct (aalign C ad (amo_bytes w0)) eqn:Hal; [|exact I].
    destruct (rdbs segs C s ad (amo_nbytes w0)) as [l|] eqn:Hrd; [|exact I].
    destruct (lits l) as [zs|] eqn:Hl; [|exact I].
    pose proof (classify_sound _ _ Hcl) as Had. rewrite <- (sm_regs _ _ _ _ Hsim rs1) in Had.
    pose proof (rdbs_sound s M _ _ _ (sm_mem _ _ _ _ Hsim) Hrd) as Hrn. rewrite (lits_sound _ _ Hl), Had in Hrn.
    pose proof (aalign_sound _ _ Hal) as Ha. rewrite Had in Ha.
    eexists _, M, _. rewrite pcw_next, pcw_setresv, pcw_setreg.
    split; [apply (stepR_lr segs R (pcw s) M rom rv w w0 aq rl rd rs1 _ Hf He Hd Ha Hrn)|].
    apply sim_next. rewrite <- Had. change (Some (aden ad)) with (option_map aden (Some ad)). eapply sim_setresv.
    apply sim_setreg; [exact Hsim | apply vden_wlit].
  -
    destruct (classify C (getreg s rs1)) as [ad|] eqn:Hcl; [|exact I].
    destruct (s_resv s) as [r|] eqn:Hres; [|exact I].
    destruct (aalign C ad (amo_bytes w0) && aaddr_eqb r ad) eqn:Hal; [|exact I].
    apply andb_true_iff in Hal. destruct Hal as [Hal Hre]. apply aaddr_eqb_eq in Hre. subst r.
    destruct (store_bytes (amo_nbytes w0) (getreg s rs2)) as [l|] eqn:Hsb; [|exact I].
    destruct (wrbs segs C s ad l) as [s'|] eqn:Hwr; [|exact I].
    pose proof (classify_sound _ _ Hcl) as Had. rewrite <- (sm_regs _ _ _ _ Hsim rs1) in Had.
    destruct (store_bytes_sound _ _ _ Hsb) as [Hbs Hlen]. rewrite <- (sm_regs _ _ _ _ Hsim rs2) in Hbs.
    destruct (wrbs_sound _ _ _ _ _ (sm_mem _ _ _ _ Hsim) Hwr) as (Hm' & Hcs & Hr' & Hp' & Hv').
    pose proof (store_ok_chks _ _ _ _ (sm_mem _ _ _ _ Hsim) Hcs) as Hok. rewrite Hlen, Had in Hok.
    pose proof (aalign_sound _ _ Hal) as Ha. rewrite Had in Ha.
    rewrite Hbs, Had in Hm'.
    pose proof (sm_resv _ _ _ _ Hsim) as Hrv. rewrite Hres in Hrv. cbn [option_map] in Hrv. rewrite Had in Hrv. subst rv.
    eexists _, _, None. rewrite pcw_next, pcw_setresv, pcw_setreg. unfold pcw. rewrite Hp'. fold (pcw s).
    split; [apply (stepR_sc_ok segs R (pcw s) M rom w w0 aq rl rd rs1 rs2 _ Hf He Hd Ha eq_refl Hok)|].
    apply sim_next. change (@None word) with (option_map aden None). eapply sim_setresv.
    apply sim_setreg; [|reflexivity]. eapply sim_newmem; [exact Hsim | exact Hm' | exact Hr' | exact Hv'].
  -
    destruct (classify C (getreg s rs1)) as [ad|] eqn:Hcl; [|exact I].
    destruct (getreg s rs2) as [y|k' o'] eqn:Hg2; [|exact I].
    destruct (aalign C ad (amo_bytes w0)) eqn:Hal; [|exact I].
    destruct (rdbs segs C s ad (amo_nbytes w0)) as [l|] eqn:Hrd; [|exact I].
    destruct (resv_upd C (s_resv s) ad) as [rv'|] eqn:Hru; [|exact I].
    destruct (lits l) as [zs|] eqn:Hl; [|exact I].
    destruct (wrbs segs C s ad (blits (amo_store_bytes op w0 (zbytes zs) (Z_to_bv 64 y)))) as [s'|] eqn:Hwr; [|exact I].
    pose proof (classify_sound _ _ Hcl) as Had. rewrite <- (sm_regs _ _ _ _ Hsim rs1) in Had.
    regeq Hsim rs2 Hg2 Hr2.
    pose proof (rdbs_sound s M _ _ _ (sm_mem _ _ _ _ Hsim) Hrd) as Hrn. rewrite (lits_sound _ _ Hl), Had in Hrn.
    pose proof (aalign_sound _ _ Hal) as Ha. rewrite Had in Ha.
    destruct (wrbs_sound _ _ _ _ _ (sm_mem _ _ _ _ Hsim) Hwr) as (Hm' & Hcs & Hr' & Hp' & Hv').
    pose proof (store_ok_chks _ _ _ _ (sm_mem _ _ _ _ Hsim) Hcs) as Hok.
    assert (Hlen : length (blits (amo_store_bytes op w0 (zbytes zs) (Z_to_bv 64 y))) = amo_nbytes w0).
    { unfold blits. rewrite length_map. unfold amo_store_bytes. destruct w0; apply length_Z_to_le_bytes. }
    rewrite Hlen, Had in Hok. rewrite blits_den, Had, <- Hr2 in Hm'.
    pose proof (resv_upd_sound _ _ _ Hru) as Hrs. rewrite <- (sm_resv _ _ _ _ Hsim), Had in Hrs.
    eexists _, _, _. rewrite pcw_next, pcw_setresv, pcw_setreg. unfold pcw. rewrite Hp'. fold (pcw s).
    split; [apply (stepR_amo segs R (pcw s) M rom rv w op w0 aq rl rd rs1 rs2 _ Hf He Hd Ha Hrn Hok)|].
    apply sim_next. rewrite Hrs. eapply sim_setresv.
    apply sim_setreg; [|apply vden_wlit]. eapply sim_newmem; [exact Hsim | exact Hm' | exact Hr' | exact Hv'].
Qed.

Theorem arun_sound : forall fuel s R M rv, sim s R M rv ->
  match arun segs C fuel s with
  | RFin s' v imm => exists R' M' rv', msteps segs (mkstR R (pcw s) M rom rv) (mkstR R' (v_jalr (vden v) imm) M' rom rv') /\ sim s' R' M' rv'
  | ROut s' => exists R' M' rv', msteps segs (mkstR R (pcw s) M rom rv) (mkstR R' (pcw s') M' rom rv') /\ sim s' R' M' rv'
  | RStuck _ _ => True
  end.
Proof.
  induction fuel as [|f IH]; intros s R M rv Hsim; cbn [arun].
  - exists R, M, rv. split; [apply mst_refl | exact Hsim].
  - pose proof (astep_sound s R M rv Hsim) as Hst. destruct (astep segs C s) as [s1|s1 v imm|c]; [| |exact I].
    + destruct Hst as (R1 & M1 & rv1 & Hstep & Hsim1). specialize (IH s1 R1 M1 rv1 Hsim1).
      destruct (arun segs C f s1) as [s' v imm|s'|c pc]; [| |exact I].
      * destruct IH as (R' & M' & rv' & Hms & Hs'). exists R', M', rv'. split; [|exact Hs'].
        eapply mst_step; [apply mkstR_svc | exact Hstep | exact Hms].
      * destruct IH as (R' & M' & rv' & Hms & Hs'). exists R', M', rv'. split; [|exact Hs'].
        eapply mst_step; [apply mkstR_svc | exact Hstep | exact Hms].
    + destruct Hst as (R1 & Hstep & Hsim1). exists R1, M, rv. split; [|exact Hsim1].
      eapply mst_step; [apply mkstR_svc | exact Hstep | apply mst_refl].
Qed.

Theorem arunS_sound : forall stops fuel s R M rv, sim s R M rv ->
  match arunS segs C stops fuel s with
  | RFin s' v imm => exists R' M' rv', msteps segs (mkstR R (pcw s) M rom rv) (mkstR R' (v_jalr (vden v) imm) M' rom rv') /\ sim s' R' M' rv'
  | ROut s' => exists R' M' rv', msteps segs (mkstR R (pcw s) M rom rv) (mkstR R' (pcw s') M' rom rv') /\ sim s' R' M' rv'
  | RStuck _ _ => True
  end.
Proof.
  intros stops. induction fuel as [|f IH]; intros s R M rv Hsim; cbn [arunS].
  - exists R, M, rv. split; [apply mst_refl | exact Hsim].
  - destruct (existsb (Z.eqb (s_pc s)) stops); [exists R, M, rv; split; [apply mst_refl | exact Hsim]|].
    pose proof (astep_sound s R M rv Hsim) as Hst. destruct (astep segs C s) as [s1|s1 v imm|c]; [| |exact I].
    + destruct Hst as (R1 & M1 & rv1 & Hstep & Hsim1). specialize (IH s1 R1 M1 rv1 Hsim1).
      destruct (arunS segs C stops f s1) as [s' v imm|s'|c pc]; [| |exact I].
      * destruct IH as (R' & M' & rv' & Hms & Hs'). exists R', M', rv'. split; [|exact Hs'].
        eapply mst_step; [apply mkstR_svc | exact Hstep | exact Hms].
      * destruct IH as (R' & M' & rv' & Hms & Hs'). exists R', M', rv'. split; [|exact Hs'].
        eapply mst_step; [apply mkstR_svc | exact Hstep | exact Hms].
    + destruct Hst as (R1 & Hstep & Hsim1). exists R1, M, rv. split; [|exact Hsim1].
      eapply mst_step; [apply mkstR_svc | exact Hstep | apply mst_refl].
Qed.

Lemma sim_init : forall s R,
  (forall r : reg, getr R r = vden (getreg s r)) -> length (s_regs s) = 32%nat -> nth 0 (s_regs s) (AL 0) = AL 0 ->
  (forall k, PositiveMap.find k (s_abs s) = None) ->
  (forall j t, nth_error (s_rgs s) j = Some t -> forall k, PositiveMap.find k t = None) ->
  s_resv s = None ->
  sim s R M0 None.
Proof.
  intros s R Hr Hl H0 Ha Hg Hv. constructor; try assumption; [|rewrite Hv; reflexivity].
  constructor.
  - intros a ab Hf. rewrite Ha in Hf. discriminate.
  - intros j rg t off ab Hj Ht Hf. rewrite (Hg j t Ht) in Hf. discriminate.
  - intros x. left. reflexivity.
  - intros j rg off Hj Ho. destruct (io_rg IO j rg Hj) as (_ & _ & _ & Hd). apply Hd. exact Ho.
Qed.

Lemma cell_lit_sound : forall s M ad n zs, msim s M -> cell_lit segs C s ad n = Some zs -> rdn segs M (aden ad) n = Some (zbytes zs).
Proof.
  intros s M ad n zs Hm H. unfold cell_lit in H. destruct (rdbs segs C s ad n) as [l|] eqn:Hr; [|discriminate].
  rewrite (rdbs_sound s M n ad l Hm Hr), (lits_sound l zs H). reflexivity.
Qed.

Lemma msim_frame : forall s M (x : word), msim s M ->
  (forall lo hi, In (lo, hi) (c_wabs C) -> ~ lo <= bv_unsigned x < hi) ->
  (forall j rg, nth_error (c_rgs C) j = Some rg -> ~ rbase rg + rg_lo rg <= bv_unsigned x < rbase rg + rg_hi rg) ->
  M x = M0 x.
Proof.
  intros s M x Hm Hw Hg. destruct (ms_rest s M Hm x) as [H|[(ab & H)|(j & rg & Hj & Hr)]]; [exact H| |].
  - destruct (ms_abs s M Hm _ _ H) as (_ & Hin & _). destruct (in_ivs_true _ _ Hin) as (lo & hi & Hi & Hr). exfalso. exact (Hw lo hi Hi Hr).
  - exfalso. exact (Hg j rg Hj Hr).
Qed.
Lemma msim_grows : forall s M, msim s M -> mem_grows M0 M.
Proof.
  intros s M Hm x Hx. destruct (ms_rest s M Hm x) as [H|[(ab & H)|(j & rg & Hj & Hr)]].
  - rewrite H. exact Hx.
  - destruct (ms_abs s M Hm _ _ H) as (_ & _ & HM). rewrite wz_id in HM. rewrite HM. discriminate.
  - pose proof (ms_def s M Hm j rg (bv_unsigned x - rbase rg) Hj ltac:(lia)) as Hd.
    replace (rbase rg + (bv_unsigned x - rbase rg)) with (bv_unsigned x) in Hd by lia. rewrite wz_id in Hd. exact Hd.
Qed.

Lemma std_regs_nth : forall f k, (1 <= k < 32)%nat -> nth k (std_regs f) (AL 0) = f k.
Proof.
  intros f k Hk. unfold std_regs. destruct k as [|k']; [lia|]. cbn [nth].
  rewrite (nth_indep _ (AL 0) (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth. f_equal. rewrite seq_nth by lia. reflexivity.
Qed.
Lemma std_regs_ok : forall f R pc a g v,
  (forall k, (1 <= k < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = vden (f k)) ->
  forall r : reg, getr R r = vden (getreg (ST pc (std_regs f) a g v) r).
Proof.
  intros f R pc a g v H r. unfold getreg. cbn [s_regs]. destruct (Nat.eq_dec (rnat r) 0) as [H0|H0].
  - assert (r = Z_to_bv 5 0) as -> by (apply rnat_inj; exact H0). reflexivity.
  - pose proof (rnat_lt r) as Hlt. rewrite std_regs_nth by lia. rewrite <- (H (rnat r)) by lia. f_equal.
    unfold rnat. rewrite Z2Nat.id by (pose proof (bv_unsigned_in_range 5 r); lia). symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma regs_same_sound : forall rs l0 l1, regs_same rs l0 l1 = true -> forall r, In r rs -> nth r l0 (AL 0) = nth r l1 (AL 0).
Proof.
  induction rs as [|r0 t IH]; cbn; intros l0 l1 H r Hin; [contradiction|].
  apply andb_true_iff in H. destruct H as [H1 H2]. destruct Hin as [<-|Hin]; [apply aval_eqb_eq; exact H1 | apply IH; assumption].
Qed.

End Sound.
Lemma rdn_rb : forall segs M n a bs, rdn segs M (Z_to_bv 64 a) n = Some bs ->
  forall i, (i < n)%nat -> rb segs M (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)).
Proof.
  intros segs M n. induction n as [|n IH]; intros a bs H i Hi; [lia|].
  cbn [rdn] in H. fold (rb segs M (Z_to_bv 64 a)) in H. destruct (rb segs M (Z_to_bv 64 a)) as [b|] eqn:Hb; [|discriminate].
  rewrite wz_succ in H. destruct (rdn segs M (Z_to_bv 64 (a + 1)) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
  destruct i as [|i]; [rewrite Z.add_0_r; exact Hb|].
  cbn [nth]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply IH; [exact Hr | lia].
Qed.
Lemma vden_AS0 : forall (E : nat -> word) k, vden E (AS k 0) = E k.
Proof. intros E k. cbn. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma lor_shl8 : forall a X, 0 <= a < 256 -> 0 <= X -> Z.lor a (Z.shiftl X 8) = a + 256 * X.
Proof.
  intros a X Ha HX.
  assert (Hl : Z.land a (Z.shiftl X 8) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0. destruct (Z.lt_ge_cases i 8) as [Hlt|Hge].
    - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite (Z_testbit_high 8 a i) by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact Hl. rewrite <- Z.add_nocarry_lxor by exact Hl. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.
Lemma le_roundtrip : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b t IH]; [reflexivity|]. cbn [length bytes_le_to_Z Z_to_le_bytes].
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg t) as Ht.
  rewrite lor_shl8 by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. rewrite bv_wrap8_mod. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z t) with (bv_unsigned b + bytes_le_to_Z t * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z t) with (bytes_le_to_Z t * 256 + bv_unsigned b) by lia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (bv_unsigned b)) by lia. rewrite Z.add_0_r. exact IH.
Qed.
Lemma le_roundtrip8 : forall bs : list byte, length bs = 8%nat -> word_to_le_bytes 8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hb.
  rewrite bv_wrap_small by (pose proof (bytes_le_to_Z_nonneg bs); change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite <- Hl at 1. apply le_roundtrip.
Qed.

End ISLS.
