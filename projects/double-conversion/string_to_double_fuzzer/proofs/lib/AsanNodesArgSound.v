(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib Hoare RefMemcpyLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctShape.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcctNoLazy.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ArgLoops AsanNodesArg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import AN.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.


Lemma eeq_sound : forall SEGS E M k a b,
  know_ok SEGS E M k -> eeq k a b = true -> edenot E a = edenot E b.
Proof.
  intros SEGS E M k a b HK H. unfold eeq in H.
  destruct (expr_eqb a b) eqn:He. { apply expr_eqb_eq in He. subst. reflexivity. }
  destruct (split_lit a) as [ab ak] eqn:Ha. destruct (split_lit b) as [bb bk] eqn:Hb.
  destruct (expr_eqb ab bb) eqn:Hab.
  - apply expr_eqb_eq in Hab. subst bb. apply Z.eqb_eq in H.
    rewrite (APS.split_lit_denot E a ab ak Ha), (APS.split_lit_denot E b ab bk Hb). apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in H.
    rewrite <- (Zplus_mod_idemp_r ak), <- (Zplus_mod_idemp_r bk), H. reflexivity.
  - destruct (lin_ge0 k [(a, 0)] [(b, 0)]) eqn:H1; [|discriminate]. rename H into H2.
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as A2.
    cbn [xt_den] in A1, A2. apply bv_eq. lia.
Qed.

Lemma argc_ok_sound : forall SEGS E M k i,
  know_ok SEGS E M k -> argc_ok k i = true -> i = 0%nat \/ 2 <= bv_unsigned (edenot E (EVar V_ARGC)).
Proof.
  intros SEGS E M k i HK H. destruct i as [|i]; [left; reflexivity|right].
  cbn [argc_ok] in H. destruct (xlo k (EVar V_ARGC)) as [lo|] eqn:Hlo; [|discriminate].
  apply Z.leb_le in H. pose proof (xlo_sound SEGS E M k _ lo HK Hlo). lia.
Qed.

Lemma arg_idx_some : forall args i, arg_idx args = Some i -> (i = 0 \/ i = 1)%nat.
Proof.
  intros args i H. unfold arg_idx in H.
  destruct args as [|[z| | | | | | |] [|]]; try discriminate;
    destruct z as [|p|p]; try discriminate; try (injection H as <-; auto);
    destruct p; try discriminate; injection H as <-; auto.
Qed.

Lemma reg_lit5 : forall n, (n < 32)%nat -> bv_unsigned (Z_to_bv 5 (Z.of_nat n)) = Z.of_nat n.
Proof.
  intros n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia.
Qed.

Lemma bv5_of_nat : forall (r : bv 5) n, bv_unsigned r = Z.of_nat n -> r = Z_to_bv 5 (Z.of_nat n).
Proof. intros r n H. apply bv_eq. pose proof (u5_range r). rewrite reg_lit5 by lia. exact H. Qed.

(* [comment removed for export] *)
Lemma regs_ok_post3 : forall E sr R R' n1 (r1 : bv 5) e1 n2 (r2 : bv 5) e2 n3 (r3 : bv 5) e3,
  regs_ok E sr R -> (0 < n1 < 32)%nat -> (0 < n2 < 32)%nat -> (0 < n3 < 32)%nat ->
  bv_unsigned r1 = Z.of_nat n1 -> bv_unsigned r2 = Z.of_nat n2 -> bv_unsigned r3 = Z.of_nat n3 ->
  getr R' r1 = edenot E e1 -> getr R' r2 = edenot E e2 -> getr R' r3 = edenot E e3 ->
  (forall r : bv 5, r <> r1 -> r <> r2 -> r <> r3 -> getr R' r = getr R r) ->
  n1 <> n2 -> n1 <> n3 -> n2 <> n3 ->
  regs_ok E (sr_upd (sr_upd (sr_upd sr n1 e1) n2 e2) n3 e3) R'.
Proof.
  intros E sr R R' n1 r1 e1 n2 r2 e2 n3 r3 e3 HR H1 H2 H3 U1 U2 U3 G1 G2 G3 Gr D12 D13 D23 r.
  pose proof (bv5_of_nat r1 n1 U1) as E1. pose proof (bv5_of_nat r2 n2 U2) as E2. pose proof (bv5_of_nat r3 n3 U3) as E3.
  unfold sr_get. destruct (bv_eqb r 0%bv) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. unfold getr. rewrite Hr0. reflexivity.
  - rewrite !nth_sr_upd.
    pose proof (u5_range r) as Hr. unfold ridx.
    destruct (Nat.eqb (Z.to_nat (bv_unsigned r)) n3) eqn:Q3.
    { apply Nat.eqb_eq in Q3. rewrite (bv5_of_nat r n3), <- E3 by lia. exact G3. }
    destruct (Nat.eqb (Z.to_nat (bv_unsigned r)) n2) eqn:Q2.
    { apply Nat.eqb_eq in Q2. rewrite (bv5_of_nat r n2), <- E2 by lia. exact G2. }
    destruct (Nat.eqb (Z.to_nat (bv_unsigned r)) n1) eqn:Q1.
    { apply Nat.eqb_eq in Q1. rewrite (bv5_of_nat r n1), <- E1 by lia. exact G1. }
    apply Nat.eqb_neq in Q1. apply Nat.eqb_neq in Q2. apply Nat.eqb_neq in Q3.
    rewrite Gr.
    + specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. unfold ridx in HR. exact HR.
    + intros ->. apply Q1. rewrite U1. apply Nat2Z.id.
    + intros ->. apply Q2. rewrite U2. apply Nat2Z.id.
    + intros ->. apply Q3. rewrite U3. apply Nat2Z.id.
Qed.

(* [comment removed for export] *)
Lemma ret_lit_facts : forall cs r, ret_lit cs = Some r ->
  reg cs 1 = ELit r /\ 0 <= r < two64 /\ r mod 2 = 0.
Proof.
  intros cs r H. unfold ret_lit in H. destruct (reg cs 1) as [z| | | | | | |] eqn:Hr; try discriminate.
  destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

(* [comment removed for export] *)

Lemma rdn1_overlay : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma rdn_of_nth : forall segs m n (a : word) (f : nat -> byte),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < n)%nat -> rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [f j]) ->
  rdn segs m a n = Some (map f (seq 0 n)).
Proof.
  intros segs m n; induction n as [|n IH]; intros a f Hnw Hall; [reflexivity|].
  cbn [rdn seq map].
  pose proof (Hall 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [rdn] in H0.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
  injection H0 as ->.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv (fun j => f (S j))); [rewrite <- seq_shift, map_map; reflexivity | lia |].
    intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
    apply Hall. lia.
Qed.

Lemma rdn_nth : forall segs m n (a : word) bs j,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  rdn segs m a n = Some bs -> (j < n)%nat ->
  rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros segs m n; induction n as [|n IH]; intros a bs j Hnw H Hj; [lia|].
  cbn [rdn] in H.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|] eqn:Hb0; [|discriminate].
  destruct (rdn segs m (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate]. injection H as <-.
  destruct j as [|j'].
  - cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [rdn]. rewrite Hb0. reflexivity.
  - cbn [nth]. destruct n as [|n'']; [lia|].
    assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    replace (bv_unsigned a + Z.of_nat (S j')) with (bv_unsigned (a + 1)%bv + Z.of_nat j') by lia.
    apply (IH (a + 1)%bv rest j'); [lia | exact Hrest | lia].
Qed.

Lemma length_rdn : forall segs m n (a : word) bs, rdn segs m a n = Some bs -> length bs = n.
Proof.
  intros segs m n; induction n as [|n IH]; intros a bs H; cbn [rdn] in H.
  - injection H as <-. reflexivity.
  - destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
    destruct (rdn segs m (a + 1)%bv n) as [rest|] eqn:Hr; [|discriminate]. injection H as <-. cbn. f_equal. eapply IH. exact Hr.
Qed.

(* [comment removed for export] *)

Lemma page_base_le' : forall a : word,
  bv_unsigned (page_base a) <= bv_unsigned a /\ bv_unsigned a < bv_unsigned (page_base a) + 4096 /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Qed.

Lemma page_in_ranges_bounds' : forall (a : word) l lo hi,
  Forall (fun iv => lo <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= hi) l ->
  page_in_ranges (page_base a) l = true ->
  lo <= bv_unsigned a /\ bv_unsigned a + 1 <= hi + 4095.
Proof.
  intros a l lo hi Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
  pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.


(* [comment removed for export] *)
Lemma lazy_page_out' : forall (ilo ihi : Z) (w : word) l top,
  0 <= ilo /\ ilo mod 4096 = 0 /\ ihi mod 4096 = 0 ->
  Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ilo \/ ihi <= bv_unsigned (fst iv))
                    /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= top) l ->
  page_in_ranges (page_base w) l = true ->
  (bv_unsigned w < ilo \/ ihi <= bv_unsigned w) /\ bv_unsigned w < top.
Proof.
  intros ilo ihi w l top HU Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
  pose proof (page_base_le' w) as (P1 & P2 & P3). unfold page_size in H2.
  split; [|lia]. destruct L1 as [L1|L1]; [left; lia | right; lia].
Qed.
Lemma A_wf_allowA' : forall A E cs, A_wf (allowA A E cs).
Proof.
  intros A E cs. unfold A_wf, allowA. apply Forall_forall. intros iv Hin.
  apply in_flat_map in Hin as [p [_ Hin]]. unfold allow1 in Hin.
  pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
  destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; unfold page_size.
  - pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))). unfold uE in *.
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
  - pose proof (pagedown_le (sh_lo A E p)). pose proof (pageup_ge (sh_hi A E p)). unfold sh_lo, sh_hi, uE in *.
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
Qed.

Section Vis.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
Variable LINV : (word -> option byte) -> Prop.   (* [comment removed for export] *)
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  Definition Hv (E : env) (cs : acs) (model : Model) : word -> bool := fun a => negb (vis A E cs model a).

  (* [comment removed for export] *)
  Lemma Hv_high : forall E cs model (a : word), alloc_top (m_vmmaps model) <= bv_unsigned a -> Hv E cs model a = false.
  Proof.
    intros E cs model a Ha. unfold Hv, vis. apply negb_false_iff.
    replace (alloc_top (m_vmmaps model) <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Ha).
    rewrite orb_true_r. reflexivity.
  Qed.

  Lemma Hv_hull : forall E cs model (a : word), in_hull A (bv_unsigned a) = true -> Hv E cs model a = false.
  Proof. intros E cs model a Ha. unfold Hv, vis. rewrite Ha. reflexivity. Qed.

  Lemma lazy_cover_vis : forall E cs R FULL model,
    cs_ok SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model -> lazy_cover (Hv E cs model) (m_vm_lazy model) (allowA A E cs).
  Proof.
    intros E cs R FULL model HC w Hlz Hh. unfold Hv in Hh.
    apply negb_false_iff in Hh. unfold vis in Hh. rename Hh into Hv0.
    pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (H0 & H1 & H2 & H3).
    pose proof (lazy_page_out' (img_lo A) (img_hi A) w _ _ (conj H0 (conj H1 H2)) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HC) Hlz) as [B1 B2].   (* [comment removed for export] *)
    apply orb_prop in Hv0 as [Hv0|Hv0].
    - apply orb_prop in Hv0 as [Hv0|Hv0].
      + unfold in_hull in Hv0. apply andb_prop in Hv0 as [Hv1 Hv2]. apply Z.leb_le in Hv1. apply Z.ltb_lt in Hv2. exfalso. lia.
      + apply Z.leb_le in Hv0. exfalso. lia.
    - apply andb_prop in Hv0 as [_ Hv0]. rewrite Hlz in Hv0. cbn [negb orb] in Hv0.
      pose proof (page_base_le' w) as (P1 & P2 & P3).
      unfold page_allowedb, allowA. apply existsb_exists. unfold page_size.
      unfold in_allow in Hv0. apply orb_prop in Hv0 as [Hv0|Hv0].
      + unfold in_vis in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
        apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
        exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
        * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. left. reflexivity.
        * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      + unfold in_sh in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
        apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
        exists (pagedown (sh_lo A E p), pageup (sh_hi A E p)). split.
        * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. right. left. reflexivity.
        * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
  Qed.

  Lemma H_off_segments_vis : forall E cs model, H_off_segments SEGS (Hv E cs model).
  Proof.
    intros E cs model a Hh. unfold Hv in Hh. apply negb_true_iff in Hh. unfold vis in Hh.
    apply orb_false_iff in Hh as [Hh _]. apply orb_false_iff in Hh as [Hh _].
    apply SEGS_in_hull. exact Hh.
  Qed.

  Lemma mrestrict_Hv_high : forall E cs model FULL (a : word),
    alloc_top (m_vmmaps model) <= bv_unsigned a -> mrestrict (Hv E cs model) FULL a = FULL a.   (* [comment removed for export] *)
  Proof. intros. unfold mrestrict. rewrite Hv_high by assumption. reflexivity. Qed.

  Lemma mrestrict_Hv_hull : forall E cs model FULL (a : word),
    in_hull A (bv_unsigned a) = true -> mrestrict (Hv E cs model) FULL a = FULL a.
  Proof. intros. unfold mrestrict. rewrite Hv_hull by assumption. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma Mr_grows_Hv : forall E cs model FULL,
    mem_grows (Mr A argH E cs model FULL) (mrestrict (Hv E cs model) FULL).
  Proof.
    intros E cs model FULL a. unfold Mr, mrestrict, hid, Hv.
    destruct (argH E a), (vis A E cs model a); cbn; auto.
  Qed.
End Vis.

Lemma with_ss_idem : forall cs s1 s2, with_ss (with_ss cs s1) s2 = with_ss cs s2.
Proof. reflexivity. Qed.
Lemma a_ss_with_ss : forall cs s, a_ss (with_ss cs s) = s.
Proof. reflexivity. Qed.

Lemma munrestrict_mrestrict : forall (H : word -> bool) FULL, munrestrict H FULL (mrestrict H FULL) = FULL.
Proof.
  intros H FULL. apply functional_extensionality. intros a. unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kept_ok (regs regs' : bvmap 5 word) : Prop :=
  forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr regs' r = getr regs r.

Lemma reg_of_ridx : forall (r : bv 5) n, ridx r = n -> r = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros r n H. unfold ridx in H. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32%Z in Hr.
  unfold bv_wrap. change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma regs_ok_pointwise : forall E sr R,
  (forall r : bv 5, r <> 0%bv -> getr R r = edenot E (nth (ridx r) sr (ELit 0))) -> regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
    cbn [edenot]. apply getr_zero.
  - apply H. intros X. subst r. unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate.
Qed.

Lemma caller_saved_nodup : List.NoDup caller_saved.
Proof.
  unfold caller_saved.
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma nth_sr_fresh_out : forall cs0 nx sr i,
  ~ In i cs0 -> nth i (sr_fresh sr cs0 nx) (ELit 0) = nth i sr (ELit 0).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr i Hn; cbn [sr_fresh]; [reflexivity|].
  rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
  destruct (Nat.eqb_spec i c) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_fresh_in : forall cs0 nx sr j,
  List.NoDup cs0 -> (j < length cs0)%nat -> nth (nth j cs0 0%nat) (sr_fresh sr cs0 nx) (ELit 0) = EVar (nx + j).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr j Hnd Hj; cbn [length] in Hj; [lia|].
  inversion Hnd as [|c' t' Hnotin Hnd']; subst.
  cbn [sr_fresh]. destruct j as [|j].
  - cbn [nth]. rewrite nth_sr_fresh_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. f_equal. lia.
  - cbn [nth]. rewrite IH by (assumption || lia). f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition ext_call (E : env) (nx : nat) (R' : bvmap 5 word) : env :=
  Env (fun n => if (Nat.leb nx n && Nat.ltb n (nx + NCS))%bool
                then getr R' (Z_to_bv 5 (Z.of_nat (nth (n - nx) caller_saved 0%nat)))
                else ev E n) (eb E).

Lemma ext_call_agree : forall E nx R', env_agree nx E (ext_call E nx R').
Proof.
  intros E nx R'. split; [|reflexivity]. intros n Hn. cbn [ext_call ev].
  destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.

Lemma ext_call_var : forall E nx R' j, (j < NCS)%nat ->
  ev (ext_call E nx R') (nx + j) = getr R' (Z_to_bv 5 (Z.of_nat (nth j caller_saved 0%nat))).
Proof.
  intros E nx R' j Hj. cbn [ext_call ev].
  replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + NCS))%bool with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma nth_sr_vars_lt' : forall b sr r, sr_vars_lt b sr = true -> (r < 32)%nat -> expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma regs_after_call : forall E sr R R' nx rv,
  regs_ok E sr R -> sr_vars_lt nx sr = true -> kept_ok R R' ->
  match rv with Some e => expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
  regs_ok (ext_call E nx R')
          (match rv with Some e => sr_upd (sr_fresh sr caller_saved nx) 10 e | None => sr_fresh sr caller_saved nx end) R'.
Proof.
  intros E sr R R' nx rv HR Hsv Hkept Hrv.
  pose proof (ext_call_agree E nx R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree' nx); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
  apply regs_ok_pointwise. intros r Hr0.
  assert (CASES : forall i, (i < 32)%nat -> In i caller_saved \/ ~ In i caller_saved).
  { intros i _. destruct (in_dec Nat.eq_dec i caller_saved); auto. }
  pose proof (ridx_range r) as Hrr.
  assert (GEN : getr R' r = edenot (ext_call E nx R') (nth (ridx r) (sr_fresh sr caller_saved nx) (ELit 0))).
  { destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
    - destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
      rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
      cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    - rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
      rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      exact X. }
  destruct rv as [e|]; [|exact GEN].
  destruct Hrv as [Hev Ha0]. rewrite nth_sr_upd.
  destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10]; [|exact GEN].
  rewrite (reg_of_ridx r 10 H10). change (Z.of_nat 10) with 10%Z.
  rewrite Ha0. apply (edenot_agree' nx); [exact Hag | exact Hev].
Qed.

(* [comment removed for export] *)
Lemma kept_regs : forall (R R' : bvmap 5 word),
  (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
     getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
  kept_ok R R'.
Proof.
  intros R R' Hk r Hr0 Hn. pose proof (ridx_range r) as Hrr.
  rewrite (reg_of_ridx r (ridx r) eq_refl).
  destruct (in_dec Nat.eq_dec (ridx r) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat) as [Hin|Hnin]; [apply Hk; exact Hin|].
  exfalso. assert (Hz : ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (reg_of_ridx r 0%nat X). apply bv_eq. reflexivity. }
  unfold caller_saved in Hn. remember (ridx r) as n eqn:Hn'. clear Hn' r Hr0 Hk.
  do 32 (destruct n as [|n]; [cbn in Hn, Hnin; tauto|]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NodesArg.
  (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
Variable LINV : (word -> option byte) -> Prop.   (* [comment removed for export] *)
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis argH_top : forall E M (a : word), SINV E M -> argH E a = true -> bv_unsigned (edenot E e_sp0) <= bv_unsigned a.   (* [comment removed for export] *)
  Hypothesis nx0_ge : APS.nx0_ok nx0.                                                                       (* [comment removed for export] *)
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis LINV_frame : forall M M' : word -> option byte, (forall a : word, in_lfp A (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M'.
Hypothesis LFP_hull : forall z, in_lfp A z = true -> img_lo A <= z < img_hi A.

  Let G : argtab := argtab_of A.

  (* [comment removed for export] *)
  Variables wi0 wi1 wi2 wi3 wi4 wi5 wi6 : bv 32.
  Hypothesis Xis : 0 <= g_istrlen G /\ g_istrlen G + 28 < 2 ^ 64.
  Hypothesis Fi0 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G)) = Some wi0.
  Hypothesis Fi1 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 4)) = Some wi1.
  Hypothesis Fi2 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 8)) = Some wi2.
  Hypothesis Fi3 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 12)) = Some wi3.
  Hypothesis Fi4 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 16)) = Some wi4.
  Hypothesis Fi5 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 20)) = Some wi5.
  Hypothesis Fi6 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 24)) = Some wi6.
  Hypothesis Ei : is_ecall wi0 = false /\ is_ecall wi1 = false /\ is_ecall wi2 = false /\ is_ecall wi3 = false
                  /\ is_ecall wi4 = false /\ is_ecall wi5 = false /\ is_ecall wi6 = false.
  Hypothesis Di0 : decode_any wi0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
  Hypothesis Di1 : decode_any wi1 = Some (Op ALU_ADD 12 10 11, 4%Z).
  Hypothesis Di2 : decode_any wi2 = Some (Load SZ1 false 12 12 0, 4%Z).
  Hypothesis Di3 : decode_any wi3 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis Di4 : decode_any wi4 = Some (Branch BC_NE 12 0 8180, 4%Z).
  Hypothesis Di5 : decode_any wi5 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
  Hypothesis Di6 : decode_any wi6 = Some (Jalr 0 1 0, 4%Z).

  (* [comment removed for export] *)
  Variables usp STR0 TOP argc : Z.
  Variables argv0 argv1 : list byte.
  Let L0 : Z := Z.of_nat (length argv0).
  Let L1 : Z := Z.of_nat (length argv1).
  Let STR1 : Z := STR0 + L0 + 1.
  Definition STR (i : nat) : Z := match i with O => STR0 | _ => STR1 end.
  Definition ARG (i : nat) : list byte := match i with O => argv0 | _ => argv1 end.
  Definition LEN (i : nat) : Z := Z.of_nat (length (ARG i)).
  (* [comment removed for export] *)
  Definition arg_ok (i : nat) : Prop := match i with O => True | _ => 2 <= argc end.

  Hypothesis Lay : 0x7fff80000000 <= usp /\ usp + 176 <= STR0 /\ STR0 + L0 + 1 <= TOP
                   /\ (2 <= argc -> STR1 + L1 + 1 <= TOP)
                   /\ TOP mod 8 = 0 /\ TOP + 16 <= 2 ^ 47 /\ L0 <= 131071 /\ L1 <= 131071 /\ 1 <= argc <= 1024.
  Hypothesis Hnz : forall i j, (j < length (ARG i))%nat -> bv_unsigned (byte_at (ARG i) j) <> 0.

  Hypothesis SINV_vals : forall E M, SINV E M ->
    uE E e_sp0 = usp /\ uE E e_str0 = STR0 /\ edenot E (EVar V_L0) = Z_to_bv 64 L0
    /\ edenot E (EVar V_ARGC) = Z_to_bv 64 argc /\ edenot E (EVar V_L1) = Z_to_bv 64 L1
    /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.
  (* [comment removed for export] *)
  Hypothesis SINV_rd : forall E M (a : word), SINV E M -> STR0 <= bv_unsigned a < TOP -> exists b, M a = Some b.
  (* [comment removed for export] *)
  Hypothesis SINV_str : forall E M i j, SINV E M -> arg_ok i -> (j <= length (ARG i))%nat ->
    M (Z_to_bv 64 (STR i + Z.of_nat j)) = Some (byte_at (ARG i) j).

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH LINV FS0) (only parsing).

  (* [comment removed for export] *)
  Lemma alloc_top_usp : forall E cs R FULL model, CSOK E cs R FULL model -> alloc_top (m_vmmaps model) = usp - 8388608.
  Proof.
    intros E cs R FULL model HC. pose proof (cs_alloc_top _ _ _ _ _ _ _ _ _ _ _ _ HC) as (AT & _ & _).
    pose proof (SINV_vals E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (US & _). unfold uE in US. rewrite US in AT. unfold STK in AT. exact AT.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma LEN_le : forall i, LEN i <= 131071.
  Proof. intros [|i]; unfold LEN, ARG; [fold L0|fold L1]; lia. Qed.

  Lemma STR_range : forall i, arg_ok i -> 0x7fff80000000 + 176 + ioff i <= STR i /\ STR i + LEN i + 1 <= TOP.
  Proof.
    intros [|i] Hi; unfold STR, LEN, ARG, arg_ok, ioff in *; [fold L0; lia|].
    fold L1. unfold STR1 in *. pose proof (Zle_0_nat (length argv0)) as HL0. unfold L0 in *. lia.
  Qed.

  Lemma STR0_le : forall i, STR0 <= STR i.
  Proof. intros [|i]; unfold STR, STR1; pose proof (Zle_0_nat (length argv0)) as HL0; unfold L0 in *; lia. Qed.

  Lemma STR_bounds : forall i, 0x7fff80000000 + 176 <= STR i <= TOP.
  Proof. intros [|i]; unfold STR, STR1; pose proof (Zle_0_nat (length argv0)) as HL0; unfold L0 in *; lia. Qed.

  Section WithState.
    Variables (E : env) (M : word -> option byte).
    Hypothesis HS : SINV E M.

    Lemma val_len : forall i, edenot E (len_e i) = Z_to_bv 64 (LEN i).
    Proof.
      destruct (SINV_vals E M HS) as (_ & _ & V3 & _ & V7 & _). intros [|i]; cbn [len_e LEN ARG]; [exact V3 | exact V7].
    Qed.

    Lemma u_len : forall i, uE E (len_e i) = LEN i.
    Proof. intros i. unfold uE. rewrite val_len. pose proof (LEN_le i). pose proof (Zle_0_nat (length (ARG i))). unfold LEN in *. apply u64_lit. lia. Qed.

    Lemma u_str : forall i, uE E (str_e i) = STR i.
    Proof.
      destruct (SINV_vals E M HS) as (V0 & V1 & V3 & _). intros [|i]; cbn [str_e STR]; [exact V1|].
      unfold e_str1, eadd, eaddz, uE. rewrite !mkAlu_denot, V3, edenot_lit. rewrite !u_add64, !u64_lit by (unfold STR1 in *; lia).
      unfold uE in V1. rewrite V1. unfold STR1. rewrite (Z.mod_small (L0 + 1)) by lia. rewrite Z.mod_small by lia. lia.
    Qed.

    Lemma val_str : forall i, edenot E (str_e i) = Z_to_bv 64 (STR i).
    Proof. intros i. rewrite <- (u_str i). unfold uE. symmetry. apply Z_to_bv_bv_unsigned. Qed.

    Lemma u_nul : forall i, uE E (nul_e i) = STR i + LEN i.
    Proof.
      intros i. unfold nul_e, eadd, uE. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64.
      pose proof (u_str i) as U1. pose proof (u_len i) as U2. unfold uE in U1, U2. rewrite U1, U2.
      pose proof (LEN_le i). pose proof (Zle_0_nat (length (ARG i))). pose proof (STR_bounds i). unfold LEN in *.
      apply Z.mod_small. lia.
    Qed.

    Lemma u_argc : uE E (EVar V_ARGC) = argc.
    Proof. destruct (SINV_vals E M HS) as (_ & _ & _ & V & _). unfold uE. rewrite V. apply u64_lit. lia. Qed.

    Lemma u_sp0 : uE E e_sp0 = usp.
    Proof. destruct (SINV_vals E M HS) as (V & _). exact V. Qed.

    Lemma eb_arg : forall i, eb E (blob_of i) = ARG i.
    Proof. destruct (SINV_vals E M HS) as (_ & _ & _ & _ & _ & B1 & B2). intros [|i]; cbn [blob_of ARG]; assumption. Qed.
  End WithState.

  Lemma arg_ok_of : forall E M M' k i, SINV E M -> know_ok SEGS E M' k -> argc_ok k i = true -> arg_ok i.
  Proof.
    intros E M M' k i HS HK H. destruct (argc_ok_sound SEGS E M' k i HK H) as [->|H2]; [exact I|].
    destruct i; [exact I|]. cbn [arg_ok]. pose proof (u_argc E M HS) as U. unfold uE in U. rewrite U in H2. exact H2.
  Qed.

  (* [comment removed for export] *)
  Lemma arg_extra_bound : forall E M M' k s l, SINV E M -> know_ok SEGS E M' k -> is_arg_extra k s l = true ->
    uE E s + uE E l + 1 <= TOP.
  Proof.
    intros E M M' k s l HS HK H. unfold is_arg_extra in H.
    assert (CASE : forall i, eeq k s (str_e i) = true -> eeq k l (len_e i) = true -> arg_ok i -> uE E s + uE E l + 1 <= TOP).
    { intros i Es El Hi. unfold uE. rewrite (eeq_sound SEGS E M' k _ _ HK Es), (eeq_sound SEGS E M' k _ _ HK El).
      pose proof (u_str E M HS i) as U1. pose proof (u_len E M HS i) as U2. unfold uE in U1, U2. rewrite U1, U2.
      pose proof (STR_range i Hi) as [_ R2]. exact R2. }
    rewrite !if_andb, !if_orb in H.
    apply orb_prop in H as [H|H].
    - apply andb_prop in H as [Es El]. exact (CASE 0%nat Es El I).
    - apply andb_prop in H as [Es H]. apply andb_prop in H as [El Hac]. exact (CASE 1%nat Es El (arg_ok_of E M M' k 1 HS HK Hac)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma kr_sound : forall E M e lo hi, lo <= uE E e <= hi -> kentry_ok SEGS E M (KRange e lo hi).
  Proof. intros E M e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  Lemma str_facts_ok : forall E M0 M k i, SINV E M0 -> know_ok SEGS E M k -> arg_ok i ->
    know_ok SEGS E M (str_facts k i).
  Proof.
    intros E M0 M k i HS HK Hi. unfold str_facts. pose proof (STR_range i Hi) as [R1 R2]. pose proof Lay as LAY.
    repeat apply Forall_cons; [| |apply Forall_nil].
    - apply kr_sound. rewrite (u_str E M0 HS). unfold str_hi, STRLO, TOPNUL.
      destruct (xlo k (len_e i)) as [lo|] eqn:Hlo.
      + pose proof (xlo_sound SEGS E M k _ lo HK Hlo) as X. pose proof (u_len E M0 HS i) as U. unfold uE in U. rewrite U in X.
        pose proof (Zle_0_nat (length (ARG i))). unfold LEN in *. destruct i; cbn [ioff] in *; lia.
      + pose proof (Zle_0_nat (length (ARG i))). unfold LEN in *. destruct i; cbn [ioff] in *; lia.
    - apply kr_sound. rewrite (u_nul E M0 HS). unfold STRLO, TOPNUL. pose proof (Zle_0_nat (length (ARG i))). unfold LEN in *.
      destruct i; cbn [ioff] in *; lia.
  Qed.

  Lemma srl3_val : forall E M k e, know_ok SEGS E M k -> uE E (mkSrl k e 3) = uE E e / 8.
  Proof.
    intros E M k e HK. unfold uE. rewrite (mkSrl_denot SEGS E M k e 3 (Z_to_bv 64 3) HK) by reflexivity.
    rewrite u_srl64. reflexivity.
  Qed.

  Lemma srl_facts_ok : forall E M0 M k i, SINV E M0 -> know_ok SEGS E M k -> arg_ok i ->
    know_ok SEGS E M (srl_facts k i).
  Proof.
    intros E M0 M k i HS HK Hi. unfold srl_facts. pose proof (STR_range i Hi) as [R1 R2]. pose proof Lay as LAY.
    pose proof (Zle_0_nat (length (ARG i))) as HL. unfold LEN in *.
    repeat apply Forall_cons; [| |apply Forall_nil]; apply kr_sound; rewrite (srl3_val E M k _ HK).
    - rewrite (u_str E M0 HS). unfold str_hi, STRLO, TOPNUL.
      destruct (xlo k (len_e i)) as [lo|] eqn:Hlo.
      + pose proof (xlo_sound SEGS E M k _ lo HK Hlo) as X. pose proof (u_len E M0 HS i) as U. unfold uE in U. rewrite U in X.
        unfold LEN in X. destruct i; cbn [ioff] in *; lia.
      + destruct i; cbn [ioff] in *; lia.
    - rewrite (u_nul E M0 HS). unfold STRLO, TOPNUL, LEN. destruct i; cbn [ioff] in *; lia.
  Qed.

  Lemma know_ok_app : forall E M k1 k2, know_ok SEGS E M k1 -> know_ok SEGS E M k2 -> know_ok SEGS E M (k1 ++ k2).
  Proof. intros. unfold know_ok in *. apply Forall_app. auto. Qed.

  Lemma len_fact_ok : forall E M0 M k i, SINV E M0 -> know_ok SEGS E M (len_fact k i).
  Proof.
    intros E M0 M k i HS. unfold len_fact.
    assert (K : kentry_ok SEGS E M (KRange (len_e i) 0 LMAX)).
    { apply kr_sound. rewrite (u_len E M0 HS). pose proof (LEN_le i). pose proof (Zle_0_nat (length (ARG i))). unfold LEN, LMAX in *. lia. }
    destruct (xhi k (len_e i)) as [hi|]; [destruct (Z.leb hi LMAX)|]; try apply Forall_nil; apply Forall_cons; auto.
  Qed.

  Lemma strlen_facts_ok : forall E M0 M k i, SINV E M0 -> know_ok SEGS E M k -> arg_ok i ->
    let k1 := strlen_facts1 k i ++ k in
    know_ok SEGS E M (strlen_facts2 k1 i ++ k1).
  Proof.
    intros E M0 M k i HS HK Hi. cbv zeta.
    assert (K1 : know_ok SEGS E M (strlen_facts1 k i ++ k)).
    { apply know_ok_app; [|exact HK]. unfold strlen_facts1.
      apply know_ok_app; [eapply len_fact_ok; exact HS|]. apply know_ok_app; [|eapply str_facts_ok; eauto; exact I].
      destruct i; [apply Forall_nil | eapply str_facts_ok; eauto]. }
    apply know_ok_app; [|exact K1]. unfold strlen_facts2.
    apply know_ok_app; [|eapply srl_facts_ok; eauto; exact I].
    destruct i; [apply Forall_nil | eapply srl_facts_ok; eauto].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Theorem xn_sound_argstrlen : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => node_argstrlen A cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_argstrlen in Hn.
    destruct (arg_idx args) as [i|] eqn:Hai; [|discriminate].
    destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
    destruct (Z.eqb (pc cs) (g_istrlen (argtab_of A)) && eeq (kn cs) (reg cs 10) (str_e i) && argc_ok (kn cs) i)%bool eqn:Hc; [|discriminate].
    injection Hn as <-.
    apply andb_prop in Hc as [Hc Hargc]. apply andb_prop in Hc as [Hpc Heq]. apply Z.eqb_eq in Hpc. fold G in Hpc.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (arg_ok_of E _ _ (kn cs) i HS HK Hargc) as Hi.
    destruct (ret_lit_facts cs ret Hret) as (Hr1 & Hrr & Hre).
    pose proof Lay as LAY. pose proof (STR_range i Hi) as [R1 R2]. pose proof (Zle_0_nat (length (ARG i))) as HL.
    pose proof (STR_bounds i) as SB.
    destruct Xis as [X1 X2]. destruct Ei as (Ei0 & Ei1 & Ei2 & Ei3 & Ei4 & Ei5 & Ei6).
    (* [comment removed for export] *)
    pose proof (reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 10 HC ltac:(lia)) as H10.
    rewrite (eeq_sound SEGS E _ (kn cs) _ _ HK Heq), (val_str E FULL HS i) in H10.
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
    pose proof (reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 1 HC ltac:(lia)) as H1.
    rewrite Hr1, edenot_lit in H1.
    replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) in H1 by (apply bv_eq; reflexivity).
    assert (Hrok : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u64_lit by (unfold two64 in Hrr; lia); exact Hre).
    (* [comment removed for export] *)
    set (H2 := Hv A E cs model).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    assert (RD : forall j, (j <= length (ARG i))%nat ->
              rdn SEGS (mrestrict H2 FULL) (Z_to_bv 64 (STR i + Z.of_nat j)) 1 = Some [byte_at (ARG i) j]).
    { intros j Hj. apply rdn1_overlay. unfold H2. rewrite mrestrict_Hv_high.
      - apply (SINV_str E FULL i j HS Hi Hj).
      - rewrite (alloc_top_usp _ _ _ _ _ HC), u64_lit; pose proof (STR0_le i); pose proof Lay; unfold LEN in *; lia. }
    destruct (istrlen_run SEGS (g_istrlen G) wi0 wi1 wi2 wi3 wi4 wi5 wi6 (conj X1 X2) Fi0 Fi1 Fi2 Fi3 Fi4 Fi5 Fi6
                Ei0 Ei1 Ei2 Ei3 Ei4 Ei5 Ei6 Di0 Di1 Di2 Di3 Di4 Di5 Di6
                (mrestrict H2 FULL) (seg_rom SEGS) (STR i) (length (ARG i)) (byte_at (ARG i))
                ltac:(unfold LEN in *; lia) RD (Hnz i) ltac:(rewrite byte_at_len; reflexivity)
                R (Z_to_bv 64 ret) H10 Hrok H1) as [R' [Hms Hpost]].
    unfold cfg_of. fold ms.
    assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 ret) (mrestrict H2 FULL) (seg_rom SEGS))).
    { unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
    apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis SEGS A SEGS_in_hull E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_vis SEGS A LIMIT SINV argH LINV FS0 HULL_ok E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 ret) (mrestrict H2 FULL) (seg_rom SEGS)))
      with (mkst R' (Z_to_bv 64 ret) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
    rewrite munrestrict_mrestrict.
    specialize (Hk E R' FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold cfg_of, pc in Hk. cbn [set_pc set_reg add_kn set_kn with_ss a_ss mk_ss s_pc] in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
    (* [comment removed for export] *)
    unfold set_pc, set_reg, add_kn, set_kn. rewrite !a_ss_with_ss, !with_ss_idem. cbn [s_regs s_know s_next kn a_ss].
    eapply cs_ok_frame; [exact SINV_frame | exact LINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | | intros; reflexivity | intros; reflexivity].
    - cbn [s_regs]. destruct Hpost as (P10 & P11 & P12 & Pag).
      eapply (regs_ok_post3 E _ R R' 10 10%bv _ 11 11%bv _ 12 12%bv _ (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC)); try lia; try reflexivity.
      + rewrite P10, (val_len E FULL HS i). reflexivity.
      + rewrite P11. unfold eaddz. rewrite mkAlu_denot, (val_len E FULL HS i), edenot_lit.
        pose proof (LEN_le i) as HLe. unfold LEN in *.
        apply bv_eq. rewrite u_add64. rewrite !u64_lit by lia. symmetry. apply Z.mod_small. lia.
      + rewrite P12, edenot_lit. reflexivity.
      + intros r N1 N2 N3. apply (Pag r). intros [Hr|[Hr|Hr]]; subst r; [apply N1|apply N2|apply N3]; reflexivity.
    - cbn [s_know]. first [apply (strlen_facts_ok E _ _ (kn cs) i HS HK Hi) | idtac "KNOW-GOAL"; match goal with |- ?g => idtac g end; fail].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)


  Theorem xn_sound_argnul : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => node_argnul SEGS cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_argnul in Hn.
    destruct (arg_idx args) as [i|] eqn:Hai; [|discriminate].
    destruct (Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 && argc_ok (kn cs) i)%bool eqn:Hc; [|discriminate].
    destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
    destruct (is_ecall w) eqn:Hec; [discriminate|].
    destruct (decode_any w) as [[ins sz]|] eqn:Hd; [|discriminate].
    destruct ins; try discriminate. destruct sz0; try discriminate. destruct signed; try discriminate.
    rename rd into rd'. rename rs1 into rs. rename imm into imm'.
    destruct sz as [|p|p]; try discriminate. do 3 (destruct p as [p|p|]; try discriminate).
    destruct (negb (bv_eqb rd' 0%bv) && negb (bv_eqb rs 0%bv) && eeq (kn cs) (eaddz (reg cs (ridx rs)) (bv_signed imm')) (nul_e i))%bool eqn:Hc2;
      [|discriminate].
    injection Hn as <-.
    apply andb_prop in Hc as [Hc Hargc]. apply andb_prop in Hc as [Hp0 Hp4]. apply Z.leb_le in Hp0. apply Z.ltb_lt in Hp4.
    apply andb_prop in Hc2 as [Hc2 Heq]. apply andb_prop in Hc2 as [Hrd Hrs]. apply negb_true_iff in Hrd. apply negb_true_iff in Hrs.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (arg_ok_of E _ _ (kn cs) i HS HK Hargc) as Hi.
    pose proof Lay as LAY. pose proof (STR_range i Hi) as [R1 R2]. pose proof (Zle_0_nat (length (ARG i))) as HL.
    pose proof (STR_bounds i) as SB.
    (* [comment removed for export] *)
    assert (Hrsn : (0 < ridx rs < 32)%nat).
    { unfold ridx. pose proof (u5_range rs). split; [|lia].
      destruct (Z.eq_dec (bv_unsigned rs) 0) as [Z0|]; [|lia]. exfalso.
      assert (rs = 0%bv) by (apply bv_eq; exact Z0). subst rs. rewrite bv_eqb_refl in Hrs. discriminate. }
    pose proof (reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model (ridx rs) HC Hrsn) as Hvrs.
    rewrite ridx_roundtrip in Hvrs.
    assert (Haddr : v_addi (getr R rs) (bv_signed imm') = Z_to_bv 64 (STR i + Z.of_nat (length (ARG i)))).
    { pose proof (eeq_sound SEGS E _ (kn cs) _ _ HK Heq) as EQ. unfold eaddz in EQ. rewrite mkAlu_denot, edenot_lit in EQ.
      rewrite Hvrs. unfold v_addi. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
      pose proof (u_nul E FULL HS i) as UN. unfold uE in UN. rewrite <- EQ in UN. rewrite u_add64, u_lit64 in UN.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      unfold LEN in UN. rewrite u64_lit by lia. unfold two64 in UN.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      rewrite Zplus_mod_idemp_r in UN. exact UN. }
    (* [comment removed for export] *)
    set (H2 := Hv A E cs model).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    assert (RD : rdn SEGS (mrestrict H2 FULL) (v_addi (getr R rs) (bv_signed imm')) 1 = Some [byte_at (ARG i) (length (ARG i))]).
    { rewrite Haddr. apply rdn1_overlay. unfold H2. rewrite mrestrict_Hv_high.
      - apply (SINV_str E FULL i (length (ARG i)) HS Hi ltac:(lia)).
      - rewrite (alloc_top_usp _ _ _ _ _ HC), u64_lit; pose proof (STR0_le i); pose proof Lay; unfold LEN in *; lia. }
    pose proof (step_lbu SEGS R (Z_to_bv 64 (pc cs)) (mrestrict H2 FULL) (seg_rom SEGS) w rd' rs imm' _ Hf Hec Hd RD) as STEP.
    rewrite Hrd, byte_at_len in STEP. change (bv_unsigned (Z_to_bv 8 0)) with 0 in STEP.
    rewrite v_addi_lit in STEP by (unfold two64 in *; lia).
    assert (Hms' : msteps SEGS (restrict H2 ms) (mkst (regupd R rd' (Z_to_bv 64 0)) (Z_to_bv 64 (pc cs + 4)) (mrestrict H2 FULL) (seg_rom SEGS))).
    { unfold ms. rewrite restrict_mkst. eapply mst_step; [reflexivity | exact STEP | apply mst_refl]. }
    unfold cfg_of. fold ms.
    apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis SEGS A SEGS_in_hull E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_vis SEGS A LIMIT SINV argH LINV FS0 HULL_ok E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2 (ms_mem ms) (mkst (regupd R rd' (Z_to_bv 64 0)) (Z_to_bv 64 (pc cs + 4)) (mrestrict H2 FULL) (seg_rom SEGS)))
      with (mkst (regupd R rd' (Z_to_bv 64 0)) (Z_to_bv 64 (pc cs + 4)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
    rewrite munrestrict_mrestrict.
    specialize (Hk E (regupd R rd' (Z_to_bv 64 0)) FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold cfg_of, pc in Hk. cbn [set_pc set_reg with_ss a_ss mk_ss s_pc] in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
    unfold set_pc, set_reg. rewrite !a_ss_with_ss, !with_ss_idem. cbn [s_regs s_know s_next kn a_ss].
    eapply cs_ok_frame; [exact SINV_frame | exact LINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | exact HK | intros; reflexivity | intros; reflexivity].
    cbn [s_regs].
    pose proof (regs_ok_upd E (s_regs (a_ss cs)) R rd' (Z_to_bv 64 0) (ELit 0) (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) (edenot_lit E 0)) as RU.
    rewrite Hrd in RU. exact RU.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma call_node_sound_vis : forall cs cs' E R FULL model T (ret : Z) rv k' regs' M2',
    CSOK E cs R FULL model ->
    after_call nx0 cs ret rv k' = Some cs' ->
    msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (mrestrict (Hv A E cs model) FULL) (seg_rom SEGS))
                (mkst regs' (Z_to_bv 64 ret) M2' (seg_rom SEGS)) ->
    kept_ok R regs' ->
    match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
    let FULL' := munrestrict (Hv A E cs model) FULL M2' in
    know_ok SEGS E (Mr A argH E cs model FULL') k' ->
    (forall a, hid A argH E cs model a = true -> FULL' a = FULL a) ->
    (forall a, in_lfp A (bv_unsigned a) = true -> FULL' a = FULL a) ->     (* [comment removed for export] *)
    (forall E' R' FULL'' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL'' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg_of SEGS R' (pc cs') FULL'' model') T) ->
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T.
  Proof.
    intros cs cs' E R FULL model T ret rv k' regs' M2' HC Hac Hms Hkept Hrv FULL' HK' Hhid Hlfp Hk.
    unfold after_call in Hac.
    match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
    apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
    injection Hac as <-.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (H2 := Hv A E cs model).
    unfold cfg_of.
    apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis SEGS A SEGS_in_hull E cs model) SEGS_wx (allowA A E cs)
             (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 ret) M2' (seg_rom SEGS)) model T
             (lazy_cover_vis SEGS A LIMIT SINV argH LINV FS0 HULL_ok E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC)).
    - rewrite restrict_mkst. exact Hms.
    - intros model' Hinv' Hsame Hclean.
      set (E' := ext_call E (nxt cs) regs').
      pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
      change (unrestrict H2 (ms_mem (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst regs' (Z_to_bv 64 ret) M2' (seg_rom SEGS)))
        with (mkst regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
      apply (Hk E' regs' FULL' model').
      + split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
      + pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree nx0_ge SINV_agree LINV FS0 E E' cs R FULL model Hag Hfresh HC) as HC1.
        pose proof (hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
        eapply (cs_ok_frame SEGS A LIMIT SINV argH SINV_frame LINV LINV_frame FS0 E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
        * rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
        * cbn [s_regs mk_ss]. apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
          destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
        * reflexivity.
        * cbn [s_know mk_ss]. unfold Mr. rewrite HH.
          eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
        * intros a Ha. rewrite HH in Ha. exact (Hhid a Ha).
        * exact Hlfp.
      + apply (same_but_materialized_frame _ _ Hsame).
  Qed.

  (* [comment removed for export] *)
  Lemma after_call_cs_ok : forall cs cs' E R FULL model (ret : Z) rv k' regs' FULL',
    CSOK E cs R FULL model ->
    after_call nx0 cs ret rv k' = Some cs' ->
    kept_ok R regs' ->
    match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
    know_ok SEGS E (Mr A argH E cs model FULL') k' ->
    (forall a, hid A argH E cs model a = true -> FULL' a = FULL a) ->
    (forall a, in_lfp A (bv_unsigned a) = true -> FULL' a = FULL a) ->     (* [comment removed for export] *)
    CSOK (ext_call E (nxt cs) regs') cs' regs' FULL' model
    /\ (env_agree nx0 E (ext_call E (nxt cs) regs') /\ env_agree (nxt cs) E (ext_call E (nxt cs) regs')) /\ pc cs' = ret.
  Proof.
    intros cs cs' E R FULL model ret rv k' regs' FULL' HC Hac Hkept Hrv HK' Hhid Hlfp.
    unfold after_call in Hac.
    match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
    apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
    injection Hac as <-.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (E' := ext_call E (nxt cs) regs').
    pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
    split; [|split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag] | reflexivity]].
    pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree nx0_ge SINV_agree LINV FS0 E E' cs R FULL model Hag Hfresh HC) as HC1.
    pose proof (hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
    eapply (cs_ok_frame SEGS A LIMIT SINV argH SINV_frame LINV LINV_frame FS0 E' cs R FULL model _ regs' FULL' model HC1 (same_but_materialized_refl model)).
    - rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - cbn [s_regs mk_ss]. apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
      destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
    - reflexivity.
    - cbn [s_know mk_ss]. unfold Mr. rewrite HH. eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
    - intros a Ha. rewrite HH in Ha. exact (Hhid a Ha).
    - exact Hlfp.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis Gro_hull : img_lo A <= g_ro_lo G /\ g_ro_hi G <= img_hi A.
  Hypothesis MEMCHR : forall mem (s : word) (buf : list byte) (K n : Z) rom regs (ret : word),
    rdn SEGS mem s (length buf) = Some buf ->
    (bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf) ->
    bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64 ->
    0 <= K -> bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0 ->
    (forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0) ->
    K + 8 <= n -> n < 2 ^ 64 ->
    (forall i, g_ro_lo G <= i < g_ro_hi G -> mem (Z_to_bv 64 i) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = s -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (g_memchr G)) mem rom) (mkst regs' ret mem rom)
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 (bv_unsigned s + K).

  Lemma kimg_cover_sound : forall E M k a b,
    know_ok SEGS E M k -> kimg_cover k a b = true -> forall i, a <= i < b -> M (Z_to_bv 64 i) = None.
  Proof.
    intros E M k a b HK H i Hi. unfold kimg_cover in H. apply existsb_exists in H as [K [Hin HKb]].
    destruct K as [| | |lo hi| | | | | |]; try discriminate. apply andb_prop in HKb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as KK. cbn [kentry_ok] in KK. destruct KK as (_ & _ & KK). apply KK. lia.
  Qed.

  (* [comment removed for export] *)
  Definition win_len (i : nat) : Z := (STR i + LEN i) / 8 * 8 + 8 - STR i.

  Lemma win_len_bounds : forall i, arg_ok i -> LEN i + 1 <= win_len i <= LEN i + 8 /\ STR i + win_len i <= TOP.
  Proof.
    intros i Hi. pose proof (STR_range i Hi) as [R1 R2]. pose proof Lay as LAY. pose proof (STR_bounds i) as SB.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof (Zle_0_nat (length (ARG i))) as HL. unfold win_len in *. unfold LEN in *. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  Theorem xn_sound_argmemchr : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => node_argmemchr A nx0 cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_argmemchr in Hn.
    destruct (arg_idx args) as [i|] eqn:Hai; [|discriminate].
    destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
    destruct (reg_lit cs 11) as [c|] eqn:Hc11; [|discriminate].
    destruct (reg_lit cs 12) as [n|] eqn:Hn12; [|discriminate].
    match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [|discriminate] end.
    apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [Hc Hargc]. apply andb_prop in Hc as [Hc Hnhi].
    apply andb_prop in Hc as [Hc Hnlo]. apply andb_prop in Hc as [Hc Hc0]. apply andb_prop in Hc as [Hpc Heq].
    apply Z.eqb_eq in Hpc. fold G in Hpc, Hcov. apply Z.eqb_eq in Hc0. subst c. apply Z.leb_le in Hnlo. apply Z.ltb_lt in Hnhi.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (arg_ok_of E _ _ (kn cs) i HS HK Hargc) as Hi.
    destruct (ret_lit_facts cs ret Hret) as (Hr1 & Hrr & Hre).
    pose proof Lay as LAY. pose proof (STR_range i Hi) as [R1 R2]. pose proof (Zle_0_nat (length (ARG i))) as HL.
    pose proof (STR_bounds i) as SB. pose proof (win_len_bounds i Hi) as [W1 W2]. pose proof (LEN_le i) as HLe.
    assert (HL0 : 0 <= LEN i) by (unfold LEN; lia).
    (* [comment removed for export] *)
    pose proof (reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 10 HC ltac:(lia)) as H10.
    rewrite (eeq_sound SEGS E _ (kn cs) _ _ HK Heq), (val_str E FULL HS i) in H10.
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
    destruct (reg_lit_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 11 0 HC ltac:(lia) Hc11) as [H11 _].
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in H11 by (apply bv_eq; reflexivity).
    destruct (reg_lit_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 12 n HC ltac:(lia) Hn12) as [H12 Hnrange].
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in H12 by (apply bv_eq; reflexivity).
    pose proof (reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 1 HC ltac:(lia)) as H1.
    rewrite Hr1, edenot_lit in H1.
    replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) in H1 by (apply bv_eq; reflexivity).
    assert (Hrok : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u64_lit by (unfold two64 in Hrr; lia); exact Hre).
    (* [comment removed for export] *)
    set (H2 := Hv A E cs model). set (M2 := mrestrict H2 FULL).
    assert (Hsome : forall j, Z.of_nat j < win_len i -> exists b, M2 (Z_to_bv 64 (STR i + Z.of_nat j)) = Some b).
    { intros j Hj. unfold M2, H2. rewrite mrestrict_Hv_high by (rewrite (alloc_top_usp _ _ _ _ _ HC), u64_lit; pose proof (STR0_le i); pose proof Lay; lia).
      apply (SINV_rd E FULL _ HS). pose proof (STR0_le i). rewrite u64_lit; lia. }
    assert (Hstr : forall j, (j <= length (ARG i))%nat -> M2 (Z_to_bv 64 (STR i + Z.of_nat j)) = Some (byte_at (ARG i) j)).
    { intros j Hj. unfold M2, H2. rewrite mrestrict_Hv_high by (rewrite (alloc_top_usp _ _ _ _ _ HC), u64_lit; pose proof (STR0_le i); pose proof Lay; unfold LEN in *; lia).
      apply (SINV_str E FULL i j HS Hi Hj). }
    set (byte := fun j : nat => match M2 (Z_to_bv 64 (STR i + Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end).
    set (nb := Z.to_nat (win_len i)).
    assert (Hnb : Z.of_nat nb = win_len i) by (unfold nb; rewrite Z2Nat.id; lia).
    assert (RD : rdn SEGS M2 (Z_to_bv 64 (STR i)) nb = Some (map byte (seq 0 nb))).
    { apply rdn_of_nth; rewrite u64_lit by lia; [lia|]. intros j Hj. apply rdn1_overlay.
      unfold byte. destruct (Hsome j ltac:(lia)) as [b Hb]. rewrite Hb. reflexivity. }
    assert (Hnth : forall j, (j < nb)%nat -> nth j (map byte (seq 0 nb)) (Z_to_bv 8 0) = byte j).
    { intros j Hj. rewrite (nth_indep _ (Z_to_bv 8 0) (byte 0%nat)) by (rewrite length_map, length_seq; exact Hj).
      rewrite map_nth, seq_nth by exact Hj. reflexivity. }
    destruct (MEMCHR M2 (Z_to_bv 64 (STR i)) (map byte (seq 0 nb)) (LEN i) n (seg_rom SEGS) R (Z_to_bv 64 ret))
      as [regs' (Hms & Hkept & Ha0)].
    { rewrite length_map, length_seq. exact RD. }
    { rewrite length_map, length_seq, u64_lit by lia. unfold nb. rewrite Z2Nat.id by lia. unfold win_len. lia. }
    { rewrite length_map, length_seq, u64_lit by lia. unfold nb. rewrite Z2Nat.id by lia. lia. }
    { unfold LEN. lia. }
    { rewrite Hnth by lia. unfold byte. unfold LEN. rewrite Nat2Z.id, (Hstr (length (ARG i))) by lia.
      rewrite byte_at_len. reflexivity. }
    { intros j Hj. rewrite Hnth by lia. unfold byte. unfold LEN in Hj. rewrite Nat2Z.id in Hj.
      rewrite (Hstr j) by lia. apply Hnz. exact Hj. }
    { unfold LMAX in Hnlo. lia. }
    { lia. }
    { intros a Ha. unfold M2, H2, mrestrict. destruct (Hv A E cs model (Z_to_bv 64 a)); [reflexivity|].
      pose proof (kimg_cover_sound E _ (kn cs) _ _ HK Hcov a Ha) as X. unfold Mr, mrestrict in X.
      pose proof HULL_ok as HU; unfold hull_ok in HU. destruct Gro_hull as [G1 G2].
      rewrite (hid_hull A HULL_ok argH argH_high E cs model) in X;
        [exact X|]. unfold in_hull. rewrite u64_lit by (unfold KHI in HU; lia). apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
    { exact Hrok. } { exact H1. } { exact H10. } { exact H11. } { exact H12. }
    (* [comment removed for export] *)
    eapply (call_node_sound_vis cs cs' E R FULL model T ret (Some (nul_e i)) (kn cs) regs' M2 HC Hn).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - cbv beta iota. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite Ha0, u64_lit by lia. pose proof (u_nul E FULL HS i) as UN. unfold uE in UN.
      rewrite <- UN. apply Z_to_bv_bv_unsigned.
    - unfold M2, H2. rewrite munrestrict_mrestrict. exact HK.
    - intros a Ha. unfold M2, H2. rewrite munrestrict_mrestrict. reflexivity.
    - intros a Ha. unfold M2, H2. rewrite munrestrict_mrestrict. reflexivity.
    - exact Hk.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis MEMCPY : forall mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    0 <= n -> length bs = Z.to_nat n ->
    rdn SEGS mem0 src (length bs) = Some bs ->
    store_ok SEGS mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (x_memcpy A)) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 dst bs) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

  (* [comment removed for export] *)
  Hypothesis argH_usp : forall E (a : word), argH E a = true -> usp + 16 <= bv_unsigned a.

  (* [comment removed for export] *)
  Lemma kwritable0_x_sound : forall E M allkn k b off n,
    know_ok SEGS E M allkn ->
    know_ok SEGS E M k -> kwritable0_x allkn k b off n = true ->
    (forall m, Z.of_nat m <= elenZ E n ->
       store_ok SEGS M (Z_to_bv 64 (estart E (SA b off))) m = true)
    /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
  Proof.
    intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
    apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable0_x] in H.
    destruct K as [| | | | | |[wb wk] wn| | |]; try exact (IH Hrest H).
    assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable0_x allkn rest b off n) = true ->
                   (c1 || c2)%bool = true \/ kwritable0_x allkn rest b off n = true)
      by (intros [|] [|]; cbn; auto).
    apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
    cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
    unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
    pose proof (u64_range (edenot E n)) as Hnr.
    assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                   bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                   (forall m, Z.of_nat m <= elenZ E n -> store_ok SEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
                   /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
    { intros A1 B1. split; [|unfold elenZ in *; lia]. intros m Hm.
      replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
      apply Hs; lia. }
    apply orb_prop in H as [H|H].
    - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
      apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
      destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
      destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
      pose proof (xhi_sound SEGS E M allkn n nh Hall Hxh). pose proof (xlo_sound SEGS E M allkn wn wl Hall Hxl).
      apply CORE; unfold elenZ in *; lia.
    - pose proof (xinsideL_sound SEGS E M allkn b off n wb wk wn Hall H) as [A1 B1].
      unfold estart in A1, B1. cbn [a_base a_off] in A1, B1. apply CORE; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma kwritable_x_sound : forall E M allkn kk b off n,
    know_ok SEGS E M allkn ->
    know_ok SEGS E M kk -> kwritable_x A allkn kk b off n = true ->
    (forall m, Z.of_nat m <= elenZ E n ->
       store_ok SEGS M (Z_to_bv 64 (estart E (SA b off))) m = true)
    /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
  Proof.
    intros E M allkn kk b off n Hall HK H. unfold kwritable_x in H. apply andb_prop in H as [H _].
    exact (kwritable0_x_sound E M allkn kk b off n Hall HK H).
  Qed.
  Lemma kwritable_x_lfp : forall E M allkn kk b off n,
    know_ok SEGS E M allkn -> kwritable_x A allkn kk b off n = true ->
    forall z, in_lfp A z = true -> z < estart E (SA b off) \/ estart E (SA b off) + elenZ E n <= z.
  Proof.
    intros E M allkn kk b off n Hall H z Hz. unfold kwritable_x in H. apply andb_prop in H as [_ H].
    unfold estart, elenZ; cbn [a_base a_off]. exact (APS.lfp_apart_x_sound SEGS A E M allkn b off n Hall H z Hz).
  Qed.

  (* [comment removed for export] *)
  Lemma kwritable0_sound : forall E M allkn k b off n,
    know_ok SEGS E M allkn ->
    know_ok SEGS E M k -> kwritable0 allkn k b off n = true -> 0 <= n ->
    store_ok SEGS M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
    /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
  Proof.
    intros E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
    apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable0] in H.
    destruct K as [| | | | | |[wb wk] wn| | |]; try exact (IH Hrest H).
    cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
    unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
    assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                   bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                   store_ok SEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
                   /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
    { intros A1 B1. split; [|lia].
      replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
      apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
    lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
    - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
      apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
      destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hc0.
      pose proof (xlo_sound SEGS E M allkn wn wl Hall Hx) as Hwl. unfold elenZ in *. apply CORE; lia.
    - lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
      apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
      apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
      destruct (xinsideL_sound SEGS E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
      unfold elenZ in I2 at 1. rewrite edenot_lit, u64_lit in I2 by lia.
      unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma kwritable_sound : forall E M allkn kk b off n,
    know_ok SEGS E M allkn ->
    know_ok SEGS E M kk -> kwritable A allkn kk b off n = true -> 0 <= n ->
    store_ok SEGS M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
    /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
  Proof.
    intros E M allkn kk b off n Hall HK H Hn. unfold kwritable in H. apply andb_prop in H as [H _].
    exact (kwritable0_sound E M allkn kk b off n Hall HK H Hn).
  Qed.
  Lemma kwritable_lfp : forall E M allkn kk b off n,
    know_ok SEGS E M allkn -> kwritable A allkn kk b off n = true ->
    forall z, in_lfp A z = true -> z < estart E (SA b off) \/ estart E (SA b off) + n <= z.
  Proof.
    intros E M allkn kk b off n Hall H z Hz. unfold kwritable in H. apply andb_prop in H as [_ H].
    unfold estart; cbn [a_base a_off]. exact (APS.lfp_apartz_sound SEGS A E M allkn b off n Hall H z Hz).
  Qed.

  (* [comment removed for export] *)
  Lemma store_ok_not_hid : forall E cs model FULL (x : word),
    store_ok SEGS (Mr A argH E cs model FULL) x 1 = true -> hid A argH E cs model x = false.
  Proof.
    intros E cs model FULL x Hs. cbn [store_ok] in Hs.
    destruct (wview SEGS (Mr A argH E cs model FULL) x) as [b|] eqn:Hw; [|discriminate].
    unfold wview in Hw. unfold Mr, mrestrict in Hw.
    destruct (hid A argH E cs model x) eqn:Hh; [|reflexivity].
    destruct (find_segment SEGS (bv_unsigned x) 1) as [seg|] eqn:Hf; [|discriminate].
    (* [comment removed for export] *)
    exfalso. pose proof HULL_ok as HU; unfold hull_ok in HU.
    assert (Hin : in_hull A (bv_unsigned x) = true).
    { destruct (in_hull A (bv_unsigned x)) eqn:Hi; [reflexivity|]. rewrite (SEGS_in_hull x Hi) in Hf. discriminate. }
    rewrite (hid_hull A HULL_ok argH argH_high E cs model x Hin) in Hh. discriminate.
  Qed.

  Lemma map_byte_at : forall (l : list byte), map (byte_at l) (seq 0 (length l)) = l.
  Proof.
    intros l. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite length_map, length_seq; reflexivity|].
    intros n Hn. rewrite length_map, length_seq in Hn.
    rewrite (nth_indep _ (Z_to_bv 8 0) (byte_at l 0%nat)) by (rewrite length_map, length_seq; exact Hn).
    rewrite map_nth, seq_nth by exact Hn. cbn [Nat.add]. apply nth_lt_byte_at. exact Hn.
  Qed.

  Theorem xn_sound_memcpyarg_ref : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => node_memcpyarg A nx0 cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_memcpyarg in Hn.
    destruct (arg_idx args) as [i|] eqn:Hai; [|discriminate].
    destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
    destruct (split_lit (reg cs 10)) as [db dk] eqn:Hsplit.
    match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [|discriminate] end.
    destruct (base_range (kn cs) db) as [[dlo dhi]|] eqn:Hbr; [|discriminate].
    destruct (xlo (kn cs) (len_e i)) as [nlo|] eqn:Hnlo; [|discriminate].
    destruct (xhi (kn cs) (len_e i)) as [nhi|] eqn:Hnhi; [|discriminate].
    match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc2; [|discriminate] end.
    apply andb_prop in Hc as [Hc Hargc]. apply andb_prop in Hc as [Hc Heqn]. apply andb_prop in Hc as [Hpc Heqs]. apply Z.eqb_eq in Hpc.
    apply andb_prop in Hc2 as [Hc2 Hsep]. apply andb_prop in Hc2 as [Hc2 Hwr]. apply andb_prop in Hc2 as [Hc2 Hoff].
    apply andb_prop in Hc2 as [Hc2 Hd2]. apply andb_prop in Hc2 as [Hc2 Hd1]. apply andb_prop in Hc2 as [Hn1 Hn2].
    apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. apply Z.leb_le in Hd1. apply Z.ltb_lt in Hd2.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (arg_ok_of E _ _ (kn cs) i HS HK Hargc) as Hi.
    destruct (ret_lit_facts cs ret Hret) as (Hr1 & Hrr & Hre).
    pose proof Lay as LAY. pose proof (STR_range i Hi) as [R1 R2]. pose proof (LEN_le i) as HLe.
    assert (HL0 : 0 <= LEN i) by (unfold LEN; lia). pose proof (STR_bounds i) as SB. pose proof (STR0_le i) as S0.
    set (MR := Mr A argH E cs model FULL) in HK.
    (* [comment removed for export] *)
    pose proof (val_len E FULL HS i) as VL. pose proof (u_len E FULL HS i) as UL.
    assert (EL : elenZ E (len_e i) = LEN i) by (unfold elenZ; exact UL).
    pose proof (base_range_sound SEGS E MR (kn cs) db dlo dhi HK Hbr) as [B1 B2].
    assert (Ud : bv_unsigned (edenot E (reg cs 10)) = estart E (SA db dk)).
    { apply (u_of_split E (reg cs 10) db dk Hsplit). unfold estart; cbn [a_base a_off]. unfold LMAX, two64 in *. lia. }
    pose proof (lin_ge0_sound SEGS E MR (kn cs) _ _ HK Hsep) as SEP. cbn [xt_den] in SEP.
    pose proof (u_sp0 E FULL HS) as USP. unfold uE in USP. rewrite USP in SEP. unfold uE in UL. rewrite UL, Ud in SEP.
    destruct (kwritable_x_sound E MR (kn cs) (kn cs) db dk (len_e i) HK HK Hwr) as (ST & F1 & F2). rewrite EL in ST, F2.
    set (d := estart E (SA db dk)) in *.
    (* [comment removed for export] *)
    pose proof (reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 10 HC ltac:(lia)) as H10.
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
    assert (H10' : getr R 10 = Z_to_bv 64 d) by (rewrite H10, <- Ud; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 11 HC ltac:(lia)) as H11.
    rewrite (eeq_sound SEGS E _ (kn cs) _ _ HK Heqs), (val_str E FULL HS i) in H11.
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in H11 by (apply bv_eq; reflexivity).
    pose proof (reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 12 HC ltac:(lia)) as H12.
    rewrite (eeq_sound SEGS E _ (kn cs) _ _ HK Heqn), VL in H12.
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in H12 by (apply bv_eq; reflexivity).
    pose proof (reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 1 HC ltac:(lia)) as H1.
    rewrite Hr1, edenot_lit in H1.
    replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) in H1 by (apply bv_eq; reflexivity).
    assert (Hrok : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u64_lit by (unfold two64 in Hrr; lia); exact Hre).
    (* [comment removed for export] *)
    set (H2 := Hv A E cs model). set (M2 := mrestrict H2 FULL).
    assert (GR : mem_grows MR M2) by (unfold MR, M2, H2; apply Mr_grows_Hv).
    assert (Hstr : forall j, (j <= length (ARG i))%nat -> M2 (Z_to_bv 64 (STR i + Z.of_nat j)) = Some (byte_at (ARG i) j)).
    { intros j Hj. unfold M2, H2. rewrite mrestrict_Hv_high by (rewrite (alloc_top_usp _ _ _ _ _ HC), u64_lit; pose proof (STR0_le i); pose proof Lay; unfold LEN in *; lia).
      apply (SINV_str E FULL i j HS Hi Hj). }
    assert (RDs : rdn SEGS M2 (Z_to_bv 64 (STR i)) (length (ARG i)) = Some (ARG i)).
    { rewrite <- (map_byte_at (ARG i)) at 2. apply rdn_of_nth; rewrite u64_lit by lia; [unfold LEN in *; lia|].
      intros j Hj. apply rdn1_overlay. apply Hstr. lia. }
    assert (STd : store_ok SEGS M2 (Z_to_bv 64 d) (length (ARG i)) = true).
    { eapply store_ok_mono; [exact GR|]. apply ST. unfold LEN. lia. }
    (* [comment removed for export] *)
    assert (NH : forall j, (j < length (ARG i))%nat -> hid A argH E cs model (Z_to_bv 64 (d + Z.of_nat j)) = false).
    { intros j Hj. apply (store_ok_not_hid E cs model FULL).
      pose proof (ST (S j) ltac:(unfold LEN; lia)) as S1. fold MR.
      apply (store_ok_sub SEGS MR (Z_to_bv 64 d) (Z_to_bv 64 (d + Z.of_nat j)) (S j) 1); [| exact S1 | |];
        rewrite !u64_lit by (unfold LEN in *; lia); unfold LEN in *; lia. }
    (* [comment removed for export] *)
    destruct (MEMCPY M2 (Z_to_bv 64 d) (Z_to_bv 64 (STR i)) (LEN i) (ARG i) R (Z_to_bv 64 ret) HL0
                ltac:(unfold LEN; rewrite Nat2Z.id; reflexivity) RDs STd) as [regs' (Hms & Hkept & Ha0)].
    { rewrite !u64_lit by (unfold LEN in *; lia). left. lia. }
    { rewrite u64_lit by lia. unfold LEN in *. lia. }
    { rewrite u64_lit by (unfold LEN in *; lia). lia. }
    { exact Hrok. } { exact H1. } { exact H10'. } { exact H11. } { rewrite H12. reflexivity. }
    eapply (call_node_sound_vis cs cs' E R FULL model T ret (Some (reg cs 10)) _ regs' (wbytes M2 (Z_to_bv 64 d) (ARG i)) HC Hn).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - cbv beta iota. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0.
      rewrite <- H10'. exact H10.
    - (* [comment removed for export] *)
      cbv zeta.
      assert (FE : munrestrict H2 FULL (wbytes M2 (Z_to_bv 64 d) (ARG i)) = wbytes FULL (Z_to_bv 64 d) (ARG i)).
      { apply functional_extensionality. intros x. unfold munrestrict.
        pose proof (u64_range x) as Hx.
        destruct (Z_lt_dec (bv_unsigned x) d) as [Hlt|Hge].
        { rewrite !wbytes_out by (rewrite u64_lit; unfold LEN in *; lia). unfold M2, mrestrict. destruct (H2 x); reflexivity. }
        destruct (Z_lt_dec (bv_unsigned x) (d + Z.of_nat (length (ARG i)))) as [Hin|Hout].
        2:{ rewrite !wbytes_out by (rewrite u64_lit; unfold LEN in *; lia). unfold M2, mrestrict. destruct (H2 x); reflexivity. }
        set (j := Z.to_nat (bv_unsigned x - d)).
        assert (Hxj : x = Z_to_bv 64 (bv_unsigned (Z_to_bv 64 d) + Z.of_nat j)).
        { subst j. rewrite u64_lit, Z2Nat.id by (unfold LEN in *; lia). replace (d + (bv_unsigned x - d)) with (bv_unsigned x) by lia.
          symmetry. apply Z_to_bv_bv_unsigned. }
        assert (Hh : H2 x = false).
        { unfold H2. pose proof (NH j ltac:(lia)) as N. pose proof Hxj as Hxj'. rewrite u64_lit in Hxj' by (unfold LEN in *; lia). rewrite <- Hxj' in N.
          unfold hid in N. apply orb_false_iff in N as [_ N]. unfold Hv. rewrite N. reflexivity. }
        rewrite Hh. rewrite Hxj. rewrite !wbytes_nth by (rewrite ?u64_lit; unfold LEN in *; lia). reflexivity. }
      unfold H2 in FE |- *. rewrite FE.
      assert (ME : Mr A argH E cs model (wbytes FULL (Z_to_bv 64 d) (ARG i)) = wbytes MR (Z_to_bv 64 d) (ARG i)).
      { apply functional_extensionality. intros x. unfold MR, Mr, mrestrict.
        pose proof (u64_range x) as Hx.
        destruct (Z_lt_dec (bv_unsigned x) d) as [Hlt|Hge].
        { rewrite !wbytes_out by (rewrite u64_lit; unfold LEN in *; lia). reflexivity. }
        destruct (Z_lt_dec (bv_unsigned x) (d + Z.of_nat (length (ARG i)))) as [Hin|Hout].
        2:{ rewrite !wbytes_out by (rewrite u64_lit; unfold LEN in *; lia). reflexivity. }
        set (j := Z.to_nat (bv_unsigned x - d)).
        assert (Hxj : x = Z_to_bv 64 (bv_unsigned (Z_to_bv 64 d) + Z.of_nat j)).
        { subst j. rewrite u64_lit, Z2Nat.id by (unfold LEN in *; lia). replace (d + (bv_unsigned x - d)) with (bv_unsigned x) by lia.
          symmetry. apply Z_to_bv_bv_unsigned. }
        assert (N : hid A argH E cs model x = false).
        { pose proof (NH j ltac:(lia)) as N0. pose proof Hxj as Hxj'. rewrite u64_lit in Hxj' by (unfold LEN in *; lia).
          rewrite <- Hxj' in N0. exact N0. }
        rewrite N. rewrite Hxj. rewrite !wbytes_nth by (rewrite ?u64_lit; unfold LEN in *; lia). reflexivity. }
      rewrite ME.
      apply Forall_cons.
      + (* [comment removed for export] *)
        cbn [kentry_ok]. rewrite EL. split; [|split].
        * unfold flat. fold d. unfold LEN in *. lia.
        * rewrite (eb_arg E FULL HS i). reflexivity.
        * intros j Hj. fold d. rewrite (eb_arg E FULL HS i).
          replace (d + j) with (bv_unsigned (Z_to_bv 64 d) + Z.of_nat (Z.to_nat j)) by (rewrite u64_lit, Z2Nat.id by (unfold LEN in *; lia); lia).
          rewrite wbytes_nth by (rewrite ?u64_lit; unfold LEN in *; lia). reflexivity.
      + apply (know_ok_havoc SEGS E MR _ (kn cs) db dk (len_e i) HK).
        * intros x Hx. rewrite EL in Hx. fold d in Hx. apply wbytes_out; rewrite u64_lit; unfold LEN in *; lia.
        * intros x Hx. destruct (Z_lt_dec (bv_unsigned x) d) as [Hlt|Hge].
          { rewrite wbytes_out by (rewrite u64_lit; unfold LEN in *; lia). exact Hx. }
          destruct (Z_lt_dec (bv_unsigned x) (d + Z.of_nat (length (ARG i)))) as [Hin|Hout].
          2:{ rewrite wbytes_out by (rewrite u64_lit; unfold LEN in *; lia). exact Hx. }
          replace x with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 d) + Z.of_nat (Z.to_nat (bv_unsigned x - d)))).
          2:{ rewrite u64_lit, Z2Nat.id by (unfold LEN in *; lia). replace (d + (bv_unsigned x - d)) with (bv_unsigned x) by lia. apply Z_to_bv_bv_unsigned. }
          rewrite wbytes_nth by (rewrite ?u64_lit; unfold LEN in *; lia). discriminate.
    - (* [comment removed for export] *)
      cbv zeta. intros a Ha. unfold munrestrict. fold H2.
      destruct (H2 a) eqn:Hh; [reflexivity|].
      assert (OUT : bv_unsigned a < d \/ d + Z.of_nat (length (ARG i)) <= bv_unsigned a).
      { destruct (Z_lt_dec (bv_unsigned a) d); [left; lia|].
        destruct (Z_le_dec (d + Z.of_nat (length (ARG i))) (bv_unsigned a)); [right; lia|]. exfalso.
        pose proof (NH (Z.to_nat (bv_unsigned a - d)) ltac:(lia)) as N.
        rewrite Z2Nat.id in N by lia. replace (d + (bv_unsigned a - d)) with (bv_unsigned a) in N by lia.
        rewrite Z_to_bv_bv_unsigned in N. rewrite N in Ha. discriminate. }
      rewrite wbytes_out by (rewrite u64_lit; unfold LEN in *; lia). unfold M2, mrestrict. rewrite Hh. reflexivity.
    - (* [comment removed for export] *)
      cbv zeta. intros a Ha. unfold munrestrict. fold H2.
      destruct (H2 a) eqn:Hh; [reflexivity|].
      destruct (kwritable_x_lfp E MR (kn cs) (kn cs) db dk (len_e i) HK Hwr (bv_unsigned a) Ha) as [X|X]; fold d in X; rewrite ?EL in X;
        rewrite wbytes_out by (rewrite u64_lit; unfold LEN in *; lia); unfold M2, mrestrict; rewrite Hh; reflexivity.
    - exact Hk.
  Qed.
  (* [comment removed for export] *)
  Theorem xn_sound_memcpyarg : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (fun cs => node_memcpyargM A nx0 cs args).
  Proof. intros args. rewrite node_memcpyargM_feq. apply xn_sound_memcpyarg_ref. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rdn_Mr_FULL : forall E cs model FULL n (a : word) bs,
    rdn SEGS (Mr A argH E cs model FULL) a n = Some bs -> rdn SEGS FULL a n = Some bs.
  Proof.
    intros E cs model FULL n. induction n as [|n IH]; intros a bs H; [exact H|].
    cbn [rdn] in H |- *.
    assert (BYTE : forall b, (match Mr A argH E cs model FULL a with Some b0 => Some b0 | None => seg_rom SEGS a end) = Some b ->
                             (match FULL a with Some b0 => Some b0 | None => seg_rom SEGS a end) = Some b).
    { intros b Hb. unfold Mr, mrestrict in Hb. destruct (hid A argH E cs model a) eqn:Hh; [|exact Hb].
      (* [comment removed for export] *)
      unfold seg_rom in Hb. destruct (memory_read SEGS a 1) as [[|b0 l]|] eqn:Hm; try discriminate.
      unfold memory_read in Hm. destruct (find_segment SEGS (bv_unsigned a) (Z.of_N 1)) as [seg|] eqn:Hf; [|discriminate].
      assert (Hin : in_hull A (bv_unsigned a) = true).
      { destruct (in_hull A (bv_unsigned a)) eqn:Hi; [reflexivity|]. change (Z.of_N 1) with 1 in Hf. rewrite (SEGS_in_hull a Hi) in Hf. discriminate. }
      rewrite (hid_hull A HULL_ok argH argH_high E cs model a Hin) in Hh. discriminate. }
    destruct (match Mr A argH E cs model FULL a with Some b0 => Some b0 | None => seg_rom SEGS a end) as [b|] eqn:Hb; [|discriminate].
    rewrite (BYTE b eq_refl).
    destruct (rdn SEGS (Mr A argH E cs model FULL) (a + 1)%bv n) as [rest|] eqn:Hr; [|discriminate].
    rewrite (IH _ _ Hr). exact H.
  Qed.

  Lemma store_ok_Mr_FULL : forall E cs model FULL n (a : word),
    store_ok SEGS (Mr A argH E cs model FULL) a n = true -> store_ok SEGS FULL a n = true.
  Proof.
    intros E cs model FULL n a H. eapply store_ok_mono; [|exact H].
    intros x Hx. unfold Mr, mrestrict in Hx. destruct (hid A argH E cs model x); [exfalso; apply Hx; reflexivity | exact Hx].
  Qed.

  Lemma kreadZ_rdn : forall E M k b off n z,
    know_ok SEGS E M k -> kreadZ SEGS k b off n = Some z -> (1 <= n <= 8)%nat ->
    flat E (SA b off) (Z.of_nat n) ->
    rdn SEGS M (adenot E (SA b off)) n = Some (word_to_le_bytes n (Z_to_bv 64 z)) /\ 0 <= z < 2 ^ (8 * Z.of_nat n) /\ z < two64.
  Proof.
    intros E M k b off n z HK H Hn Hfl. unfold kreadZ in H.
    pose proof (know_lookup_sound SEGS E M k b off n false [] [] HK ltac:(lia) ltac:(lia)) as Hs.
    destruct (know_lookup SEGS k b off n false [] []) as [v scs h|scs h|]; try discriminate.
    destruct v as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
    destruct (Hs ltac:(constructor) Hfl) as (bs & P1 & P2 & P3). unfold extz in P3. cbn [edenot] in P3.
    pose proof (bytes_le_to_Z_bound bs) as Hbnd. rewrite P2 in Hbnd.
    assert (Hlt : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    apply (f_equal bv_unsigned) in P3. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in P3.
    rewrite (Z.mod_small (bytes_le_to_Z bs)) in P3 by lia. unfold two64. rewrite <- P3.
    split; [|lia]. rewrite P1. f_equal. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    rewrite Z.mod_small by lia. rewrite <- P2. symmetry. apply Z_to_le_bytes_lez.
  Qed.

  Lemma kread8e_rdn : forall E M k b off v,
    know_ok SEGS E M k -> kread8e SEGS k b off = Some v -> flat E (SA b off) 8 ->
    rdn SEGS M (adenot E (SA b off)) 8 = Some (word_to_le_bytes 8 (edenot E v)).
  Proof.
    intros E M k b off v HK H Hfl. unfold kread8e in H.
    pose proof (know_lookup_sound SEGS E M k b off 8 false [] [] HK ltac:(lia) ltac:(lia)) as Hs.
    destruct (know_lookup SEGS k b off 8 false [] []) as [v' scs h|scs h|]; try discriminate.
    destruct scs; [|discriminate]. injection H as ->.
    destruct (Hs ltac:(constructor) Hfl) as (bs & P1 & P2 & P3). unfold extz in P3.
    rewrite P1, <- P3. f_equal. unfold word_to_le_bytes.
    pose proof (bytes_le_to_Z_bound bs) as Hbnd. rewrite P2 in Hbnd. change (8 * Z.of_nat 8) with 64 in Hbnd.
    rewrite Z_to_bv_unsigned, bv_wrap64_mod. rewrite Z.mod_small by lia. rewrite <- P2. symmetry. apply Z_to_le_bytes_lez.
  Qed.

  Lemma find_blob_sound : forall E M k b o len bk,
    know_ok SEGS E M k -> find_blob k b o = Some (len, bk) -> kentry_ok SEGS E M (KBlob (SA b o) len bk).
  Proof.
    intros E M k b o len bk HK. induction k as [|K rest IH]; cbn [find_blob]; intros H; [discriminate|].
    apply Forall_cons_iff in HK as [HKK Hrest].
    destruct K as [| |[kb kk] len' bk'| | | | | | |]; try (apply IH; assumption).
    destruct (expr_eqb kb b && Z.eqb kk o)%bool eqn:Heq; [|apply IH; assumption].
    apply andb_prop in Heq as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst.
    injection H as <- <-. exact HKK.
  Qed.

  Lemma map_byte_at' : forall (l : list byte), map (byte_at l) (seq 0 (length l)) = l.
  Proof.
    intros l. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite length_map, length_seq; reflexivity|].
    intros n0 Hn. rewrite length_map, length_seq in Hn.
    rewrite (nth_indep _ (Z_to_bv 8 0) (byte_at l 0%nat)) by (rewrite length_map, length_seq; exact Hn).
    rewrite map_nth, seq_nth by exact Hn. cbn [Nat.add]. apply nth_lt_byte_at. exact Hn.
  Qed.

  Lemma adenot_SA' : forall E b off, adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off)).
  Proof. intros. unfold adenot, v_addi, estart. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition pbytes (E : env) (ps : list spiece) : list byte := flat_map (piece_den E) ps.

  Lemma pbytes_app : forall E a b, pbytes E (a ++ b) = pbytes E a ++ pbytes E b.
  Proof. intros. unfold pbytes. rewrite flat_map_app. reflexivity. Qed.

  Lemma pbytes_flush : forall E lit acc, pbytes E (rev (flush_lit lit acc)) = pbytes E (rev acc) ++ map (Z_to_bv 8) (rev lit).
  Proof.
    intros E lit acc. unfold flush_lit. destruct lit as [|z l].
    - cbn. rewrite app_nil_r. reflexivity.
    - cbn [rev]. rewrite pbytes_app. cbn. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma blob_pick : forall k n (b : nat) n' (b' : nat),
    (match foldK k n with ELit 0 => None | n'' => Some (n'', b) end) = Some (n', b') -> n' = foldK k n /\ b' = b.
  Proof.
    intros k n b n' b' H. destruct (foldK k n) as [z| | | | | | |]; try (injection H as <- <-; auto).
    destruct z as [|p|p]; try discriminate; injection H as <- <-; auto.
  Qed.

  (* [comment removed for export] *)
  Lemma pieces_walk_sound : forall E M k fuel c wp lit acc ps (wb : Z) (sofar : list byte),
    know_ok SEGS E M k ->
    pieces_walk SEGS fuel k c wp lit acc = Some ps ->
    sofar = pbytes E (rev acc) ++ map (Z_to_bv 8) (rev lit) ->
    0 <= wb -> wb + Z.of_nat (length sofar) = uE E c ->
    rdn SEGS M (Z_to_bv 64 wb) (length sofar) = Some sofar ->
    exists all, pbytes E ps = all /\ rdn SEGS M (Z_to_bv 64 wb) (length all) = Some all
                /\ wb + Z.of_nat (length all) = uE E wp.
  Proof.
    intros E M k fuel. induction fuel as [|fuel IH]; intros c wp lit acc ps wb sofar HK H Hsf Hwb Hc Hrd; [discriminate|].
    unfold uE in *. cbn [pieces_walk] in H.
    destruct (eeq k c wp) eqn:Heq.
    - injection H as <-. exists sofar. rewrite pbytes_flush, <- Hsf. split; [reflexivity|]. split; [exact Hrd|].
      rewrite Hc. unfold uE. rewrite (eeq_sound SEGS E M k c wp HK Heq). reflexivity.
    - destruct (split_lit c) as [cb ck] eqn:Hsp.
      destruct (match find_blob k cb ck with
                | Some (n, b) => match foldK k n with ELit 0 => None | n' => Some (n', b) end
                | None => None end) as [[n' b]|] eqn:Hblob.
      + (* [comment removed for export] *)
        destruct (find_blob k cb ck) as [[n b']|] eqn:Hfb; [|discriminate].
        destruct (blob_pick k n b' n' b Hblob) as [En' <-].
        assert (Hn' : edenot E n' = edenot E n) by (rewrite En'; exact (foldK_denot SEGS E M k n HK)).
        destruct (xhi k c) as [ch|] eqn:Hch; [|discriminate]. destruct (xhi k n') as [nh|] eqn:Hnh; [|discriminate].
        destruct (Z.ltb (ch + nh) two64) eqn:Hlt; [|discriminate]. apply Z.ltb_lt in Hlt.
        pose proof (xhi_sound SEGS E M k c ch HK Hch) as Xc. pose proof (xhi_sound SEGS E M k n' nh HK Hnh) as Xn. rewrite Hn' in Xn.
        unfold two64 in Hlt.
        pose proof (find_blob_sound E M k cb ck n b HK Hfb) as KB. cbn [kentry_ok] in KB. destruct KB as (Hfl & Hlen & Hby).
        pose proof (u_of_split E c cb ck Hsp ltac:(destruct Hfl as (?&?&?&?); lia)) as Uc.
        specialize (IH (eadd c n') wp [] (SPBlob b :: flush_lit lit acc) ps wb (sofar ++ eb E b) HK H).
        destruct IH as (all & P1 & P2 & P3).
        * cbn [rev map]. rewrite app_nil_r, pbytes_app, pbytes_flush, <- Hsf. cbn [pbytes flat_map piece_den]. rewrite app_nil_r. reflexivity.
        * exact Hwb.
        * rewrite length_app. unfold eadd, uE. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64, Hn'.
          unfold uE in Hc. unfold elenZ in Hlen.
          destruct Hfl as (F1 & F2 & F3 & F4). unfold elenZ in F4. rewrite Z.mod_small; lia.
        * rewrite length_app. eapply rdn_app; [exact Hrd|].
          replace (Z_to_bv 64 wb + nat_to_word (length sofar))%bv with (Z_to_bv 64 (estart E (SA cb ck))).
          2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
              destruct Hfl as (F1 & F2 & F3 & F4). rewrite <- Uc, <- Hc. pose proof (u64_range (edenot E c)).
              Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
              rewrite (Z.mod_small (Z.of_nat _)) by lia. rewrite !Z.mod_small by lia. reflexivity. }
              Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          rewrite <- (map_byte_at' (eb E b)) at 2.
          apply rdn_of_nth; rewrite u64_lit by (destruct Hfl as (?&?&?&?); lia).
          { destruct Hfl as (?&?&?&?). unfold elenZ in *. lia. }
          intros j Hj. apply rdn1_overlay. rewrite Hby by (unfold elenZ in *; lia). rewrite Nat2Z.id, nth_lt_byte_at by exact Hj. reflexivity.
        * exists all. auto.
      + (* [comment removed for export] *)
        destruct (kreadZ SEGS k cb ck 1) as [z|] eqn:Hz; [|discriminate].
        destruct (flat_x k cb ck (ELit 2)) eqn:Hfx; [|discriminate]. clear Hblob.
        pose proof (flat_x_sound SEGS E M k cb ck (ELit 2) HK Hfx) as Hfl0.
        rewrite edenot_lit, u64_lit in Hfl0 by lia.
        assert (Hfl : flat E (SA cb ck) 1) by (unfold flat; lia).
        destruct (kreadZ_rdn E M k cb ck 1 z HK Hz ltac:(lia) Hfl) as (RD1 & Hz8 & _).
        change (8 * Z.of_nat 1) with 8 in Hz8.
        pose proof (u_of_split E c cb ck Hsp ltac:(destruct Hfl as (?&?&?&?); lia)) as Uc.
        specialize (IH (eaddz c 1) wp (z :: lit) acc ps wb (sofar ++ [Z_to_bv 8 z]) HK H).
        destruct IH as (all & P1 & P2 & P3).
        * rewrite Hsf. cbn [rev]. rewrite map_app. cbn [map]. rewrite app_assoc. reflexivity.
        * exact Hwb.
        * rewrite length_app. cbn [length]. unfold eaddz, uE. rewrite mkAlu_denot, edenot_lit. rewrite u_add64, (u64_lit 1) by lia.
          destruct Hfl0 as (G1 & G2 & G3). rewrite Z.mod_small; lia.
        * rewrite length_app. cbn [length]. eapply rdn_app; [exact Hrd|].
          replace (Z_to_bv 64 wb + nat_to_word (length sofar))%bv with (adenot E (SA cb ck)).
          2:{ rewrite adenot_SA'. apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
              destruct Hfl as (F1 & F2 & F3 & F4). rewrite <- Uc, <- Hc.
              pose proof (u64_range (edenot E c)).
              Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
              rewrite (Z.mod_small (Z.of_nat _)) by lia. rewrite !Z.mod_small by lia. reflexivity. }
              Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          rewrite RD1. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. f_equal. apply bv_eq.
          rewrite !Z_to_bv_unsigned. unfold bv_wrap.
          change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with (2 ^ 8). rewrite (Z.mod_small z (2 ^ 64)) by lia. reflexivity.
        * exists all. auto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis STDIO : forall (H : word -> bool) regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
    H_off_segments SEGS H -> lazy_all_hidden H model ->
    range_avoids H (Z_to_bv 64 (su - 112)) 112 -> range_avoids H (Z_to_bv 64 wb) (length pending) -> range_avoids H s (length extra) ->
    getr regs 2%bv = Z_to_bv 64 su -> getr regs 10%bv = Z_to_bv 64 f -> getr regs 11%bv = s -> getr regs 12%bv = l -> getr regs 1%bv = ret ->
    4294967296 + 112 <= su -> su <= 0x800000000000 ->
    store_ok SEGS mem (Z_to_bv 64 (su - 112)) 112 = true ->
    g_file_lo G <= f -> f + 232 <= g_file_hi G ->
    rdn SEGS mem (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wp)) ->
    rdn SEGS mem (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wb)) ->
    rdn SEGS mem (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
    rdn SEGS mem (Z_to_bv 64 (f + 88)) 8 = Some (word_to_le_bytes 8 bufp) ->
    rdn SEGS mem (Z_to_bv 64 (f + 96)) 8 = Some (word_to_le_bytes 8 bufsz) ->
    rdn SEGS mem (Z_to_bv 64 (g_canary_got G)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (g_canary G))) ->
    rdn SEGS mem (Z_to_bv 64 (g_canary G)) 8 = Some (word_to_le_bytes 8 can) ->
    0 < fd < 2147483648 ->
    fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_halted model = None ->
    0 <= wb <= wp -> wp < 0x800000000000 -> wp - wb = Z.of_nat (length pending) -> bv_unsigned l = Z.of_nat (length extra) ->   (* [comment removed for export] *)
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 40 ->   (* [comment removed for export] *)
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30 ->
    (wp <= su - 112 \/ su <= wb) -> (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s) ->
    bv_unsigned s + bv_unsigned l <= 0x800000000000 ->   (* [comment removed for export] *)
    rdn SEGS mem (Z_to_bv 64 wb) (length pending) = Some pending -> rdn SEGS mem s (length extra) = Some extra ->
    ret_ok ret -> K [] ->
    (forall regs' mem',
       getr regs' 10%bv = l -> getr regs' 2%bv = Z_to_bv 64 su -> getr regs' 1%bv = ret ->
       getr regs' 8%bv = getr regs 8%bv -> getr regs' 9%bv = getr regs 9%bv ->
       getr regs' 18%bv = getr regs 18%bv -> getr regs' 19%bv = getr regs 19%bv -> getr regs' 20%bv = getr regs 20%bv ->
       getr regs' 21%bv = getr regs 21%bv -> getr regs' 22%bv = getr regs 22%bv -> getr regs' 23%bv = getr regs 23%bv ->
       getr regs' 24%bv = getr regs 24%bv -> getr regs' 25%bv = getr regs 25%bv -> getr regs' 26%bv = getr regs 26%bv ->
       getr regs' 27%bv = getr regs 27%bv -> getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
       (forall x : word, ~ (su - 112 <= bv_unsigned x < su) -> ~ (f + 32 <= bv_unsigned x < f + 48) ->
                          ~ (f + 56 <= bv_unsigned x < f + 64) -> mem' x = mem x) ->
       mem_grows mem mem' ->
       rdn SEGS mem' (Z_to_bv 64 (f + 32)) 8 = Some (word_to_le_bytes 8 (v_add bufp bufsz)) ->
       rdn SEGS mem' (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 bufp) ->
       rdn SEGS mem' (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 bufp) ->
       srealizes SEGS (mkCfg (mkst regs' ret mem' (seg_rom SEGS)) model) K) ->
    srealizes SEGS (mkCfg (mkst regs (Z_to_bv 64 (g_stdio_write G)) mem (seg_rom SEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
  Hypothesis Gfile : img_lo A <= g_file_lo G /\ g_file_hi G <= img_hi A /\ img_lo A <= g_canary_got G /\ g_canary_got G + 8 <= img_hi A
                     /\ img_lo A <= g_canary G /\ g_canary G + 8 <= img_hi A.

  (* [comment removed for export] *)
  Definition inr (lo n : Z) (x : word) : bool := (Z.leb lo (bv_unsigned x) && Z.ltb (bv_unsigned x) (lo + n))%bool.
  Lemma inr_spec : forall lo n x, inr lo n x = true <-> (lo <= bv_unsigned x < lo + n)%Z.
  Proof. intros lo n x. unfold inr. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
  Lemma inr_false : forall lo n x, inr lo n x = false <-> ~ (lo <= bv_unsigned x < lo + n)%Z.
  Proof. intros lo n x. rewrite <- inr_spec. destruct (inr lo n x); split; congruence. Qed.

  Lemma know_ok_havoc3 : forall E M M' k b1 o1 n1 b2 o2 n2 b3 o3 n3,
    know_ok SEGS E M k ->
    (forall x : word,
       ~ (estart E (SA b1 o1) <= bv_unsigned x < estart E (SA b1 o1) + elenZ E n1)%Z ->
       ~ (estart E (SA b2 o2) <= bv_unsigned x < estart E (SA b2 o2) + elenZ E n2)%Z ->
       ~ (estart E (SA b3 o3) <= bv_unsigned x < estart E (SA b3 o3) + elenZ E n3)%Z ->
       M' x = M x) ->
    mem_grows M M' ->
    know_ok SEGS E M' (kn_havoc (kn_havoc (kn_havoc k b1 o1 n1) b2 o2 n2) b3 o3 n3).
  Proof.
    intros E M M' k b1 o1 n1 b2 o2 n2 b3 o3 n3 HK Hout Hg.
    set (a1 := estart E (SA b1 o1)). set (l1 := elenZ E n1).
    set (a2 := estart E (SA b2 o2)). set (l2 := elenZ E n2).
    set (a3 := estart E (SA b3 o3)). set (l3 := elenZ E n3).
    set (M1 := fun x : word => if (inr a2 l2 x || inr a3 l3 x)%bool then M x else M' x).
    set (M2 := fun x : word => if inr a3 l3 x then M x else M' x).
    assert (O1 : forall x : word, (bv_unsigned x < a1 \/ a1 + l1 <= bv_unsigned x)%Z -> M1 x = M x).
    { intros x Hx. unfold M1. destruct (inr a2 l2 x) eqn:E2; [reflexivity|]. destruct (inr a3 l3 x) eqn:E3; [reflexivity|].
      cbn [orb]. apply inr_false in E2. apply inr_false in E3. apply Hout; [lia | exact E2 | exact E3]. }
    assert (G1 : mem_grows M M1).
    { intros x Hx. unfold M1. destruct (inr a2 l2 x || inr a3 l3 x)%bool; [exact Hx | exact (Hg x Hx)]. }
    assert (O2 : forall x : word, (bv_unsigned x < a2 \/ a2 + l2 <= bv_unsigned x)%Z -> M2 x = M1 x).
    { intros x Hx. unfold M1, M2. destruct (inr a3 l3 x) eqn:E3; [rewrite orb_true_r; reflexivity|].
      destruct (inr a2 l2 x) eqn:E2; [|reflexivity]. apply inr_spec in E2. lia. }
    assert (G2 : mem_grows M1 M2).
    { intros x Hx. unfold M1, M2 in *. destruct (inr a3 l3 x); [rewrite orb_true_r in Hx; exact Hx|].
      destruct (inr a2 l2 x); cbn [orb] in Hx; [exact (Hg x Hx) | exact Hx]. }
    assert (O3 : forall x : word, (bv_unsigned x < a3 \/ a3 + l3 <= bv_unsigned x)%Z -> M' x = M2 x).
    { intros x Hx. unfold M2. destruct (inr a3 l3 x) eqn:E3; [|reflexivity]. apply inr_spec in E3. lia. }
    assert (G3 : mem_grows M2 M').
    { intros x Hx. unfold M2 in Hx. destruct (inr a3 l3 x); [exact (Hg x Hx) | exact Hx]. }
    eapply know_ok_havoc; [| exact O3 | exact G3].
    eapply know_ok_havoc; [| exact O2 | exact G2].
    eapply know_ok_havoc; [exact HK | exact O1 | exact G1].
  Qed.

  Lemma kimg_cut_sound : forall E M k a n, know_ok SEGS E M k -> know_ok SEGS E M (kimg_cut k a n).
  Proof.
    intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
    destruct K as [| | |lo hi| | | | | |]; cbn [kimg_cut1]; try (apply Forall_cons; [exact HKK|apply Forall_nil]).
    destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hap; [apply Forall_cons; [exact HKK|apply Forall_nil]|].
    apply Bool.orb_false_iff in Hap as [Hap1 Hap2]. apply Z.leb_gt in Hap1. apply Z.leb_gt in Hap2.
    cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Himg).
    apply Forall_app. split.
    - destruct (Z.ltb lo a) eqn:E1; [|constructor]. apply Z.ltb_lt in E1. apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok].
      split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
    - destruct (Z.ltb (a + n) hi) eqn:E2; [|constructor]. apply Z.ltb_lt in E2. apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok].
      split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kread_bytes_rdn : forall E M k len b off zs,
    know_ok SEGS E M k -> kread_bytes SEGS len k b off = Some zs ->
    (0 <= bv_unsigned (edenot E b) + off)%Z -> (bv_unsigned (edenot E b) + off + Z.of_nat len <= 2 ^ 64)%Z ->
    rdn SEGS M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) len = Some (map (fun z => Z_to_bv 8 z) zs)
    /\ length zs = len.
  Proof.
    intros E M k len. induction len as [|len IH]; intros b off zs HK H Hlo Hhi.
    - cbn in H. injection H as <-. split; reflexivity.
    - cbn [kread_bytes] in H.
      destruct (kreadZ SEGS k b off 1) as [z|] eqn:Hz; [|discriminate].
      destruct (kread_bytes SEGS len k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate].
      injection H as <-.
      assert (Hfl : flat E (SA b off) 1) by (unfold flat, estart; cbn [a_base a_off]; lia).
      destruct (kreadZ_rdn E M k b off 1 z HK Hz ltac:(lia) Hfl) as (Hrd & Hzr & _). change (8 * Z.of_nat 1) with 8 in Hzr.
      rewrite adenot_SA' in Hrd. unfold estart in Hrd. cbn [a_base a_off] in Hrd.
      destruct (IH b (off + 1)%Z rest HK Hrest ltac:(lia) ltac:(lia)) as [Hrd2 Hlen].
      split; [| cbn; lia].
      change (S len) with (1 + len)%nat. cbn [map].
      change (Z_to_bv 8 z :: map (fun z0 : Z => Z_to_bv 8 z0) rest) with ([Z_to_bv 8 z] ++ map (fun z0 : Z => Z_to_bv 8 z0) rest).
      eapply rdn_app.
      + rewrite Hrd. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. f_equal. apply bv_eq.
        rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with (2 ^ 8).
        rewrite (Z.mod_small z (2 ^ 64)) by lia. reflexivity.
      + replace (Z_to_bv 64 (bv_unsigned (edenot E b) + off) + nat_to_word 1)%bv
          with (Z_to_bv 64 (bv_unsigned (edenot E b) + (off + 1))); [exact Hrd2|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        change (Z.of_nat 1) with 1%Z. rewrite (Z.mod_small 1) by lia.
        rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kblob_rdn : forall E M b k len bk,
    kentry_ok SEGS E M (KBlob (SA b k) len bk) ->
    rdn SEGS M (Z_to_bv 64 (estart E (SA b k))) (length (eb E bk)) = Some (eb E bk).
  Proof.
    intros E M b k len bk HK. cbn [kentry_ok] in HK. destruct HK as (Hfl & Hlen & Hb).
    rewrite <- (map_byte_at' (eb E bk)) at 2.
    apply rdn_of_nth; rewrite u64_lit by (destruct Hfl as (?&?&?&?); lia).
    { destruct Hfl as (?&?&?&?). unfold elenZ in *. lia. }
    intros j Hj. apply rdn1_overlay. rewrite Hb by (unfold elenZ in *; lia). rewrite Nat2Z.id, nth_lt_byte_at by exact Hj. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma extra_pieces_sound : forall E cs model FULL k s l ps,
    SINV E FULL -> know_ok SEGS E (Mr A argH E cs model FULL) k ->
    extra_pieces SEGS k s l = Some ps ->
    exists extra, pbytes E ps = extra
      /\ rdn SEGS FULL (edenot E s) (length extra) = Some extra
      /\ bv_unsigned (edenot E l) = Z.of_nat (length extra)
      /\ bv_unsigned (edenot E s) + Z.of_nat (length extra) <= 2 ^ 64
      /\ (extra = [] \/ (exists i, arg_ok i /\ bv_unsigned (edenot E s) = STR i /\ extra = ARG i)
          \/ rdn SEGS (Mr A argH E cs model FULL) (edenot E s) (length extra) = Some extra).
  Proof.
    intros E cs model FULL k s l ps HS HK H. unfold extra_pieces in H.
    set (MR := Mr A argH E cs model FULL) in *.
    pose proof (u64_range (edenot E s)) as Hsr.
    (* [comment removed for export] *)
    assert (GEN : forall lz,
      (forall z, lz = Some z -> bv_unsigned (edenot E l) = z /\ 0 < z < two64) ->
      (if (if eeq k s (str_e 0) then eeq k l (len_e 0) else false) then Some [SPBlob (blob_of 0)]
       else if (if eeq k s (str_e 1) then (eeq k l (len_e 1) && argc_ok k 1)%bool else false) then Some [SPBlob (blob_of 1)]
       else let '(sb, sk) := split_lit s in
            match find_blob k sb sk with
            | Some (n, b) => if eeq k n l then Some [SPBlob b] else None
            | None => match lz with
                      | Some z => if flat_x k sb sk (ELit z) then
                                    match kread_bytes SEGS (Z.to_nat z) k sb sk with Some bs => Some [SPLit bs] | None => None end
                                  else None
                      | None => None
                      end
            end) = Some ps ->
      exists extra, pbytes E ps = extra
        /\ rdn SEGS FULL (edenot E s) (length extra) = Some extra
        /\ bv_unsigned (edenot E l) = Z.of_nat (length extra)
        /\ bv_unsigned (edenot E s) + Z.of_nat (length extra) <= 2 ^ 64
        /\ (extra = [] \/ (exists i, arg_ok i /\ bv_unsigned (edenot E s) = STR i /\ extra = ARG i)
            \/ rdn SEGS MR (edenot E s) (length extra) = Some extra)).
    { intros lz LZ HH.
      assert (ARGCASE : forall i, eeq k s (str_e i) = true -> eeq k l (len_e i) = true -> arg_ok i -> ps = [SPBlob (blob_of i)] ->
        exists extra, pbytes E ps = extra
          /\ rdn SEGS FULL (edenot E s) (length extra) = Some extra
          /\ bv_unsigned (edenot E l) = Z.of_nat (length extra)
          /\ bv_unsigned (edenot E s) + Z.of_nat (length extra) <= 2 ^ 64
          /\ (extra = [] \/ (exists i, arg_ok i /\ bv_unsigned (edenot E s) = STR i /\ extra = ARG i)
              \/ rdn SEGS MR (edenot E s) (length extra) = Some extra)).
      { intros i Es El Hi ->. exists (ARG i). cbn [pbytes flat_map piece_den]. rewrite app_nil_r, (eb_arg E FULL HS i).
        pose proof (eeq_sound SEGS E MR k _ _ HK Es) as Vs. pose proof (eeq_sound SEGS E MR k _ _ HK El) as Vl.
        rewrite Vs, Vl, (val_str E FULL HS i), (val_len E FULL HS i).
        pose proof (STR_range i Hi) as [R1 R2]. pose proof (STR_bounds i) as SB. pose proof Lay as LAY.
        pose proof (Zle_0_nat (length (ARG i))) as HL. unfold LEN in *.
        rewrite !u64_lit by lia. split; [reflexivity|]. split; [|split; [reflexivity|split; [lia| right; left; exists i; auto]]].
        rewrite <- (map_byte_at' (ARG i)) at 2. apply rdn_of_nth; rewrite u64_lit by lia; [lia|].
        intros j Hj. apply rdn1_overlay. apply (SINV_str E FULL i j HS Hi). lia. }
      rewrite !if_andb in HH.
      destruct (eeq k s (str_e 0) && eeq k l (len_e 0))%bool eqn:C0.
      { apply andb_prop in C0 as [Es El]. injection HH as <-. apply (ARGCASE 0%nat Es El I eq_refl). }
      destruct (eeq k s (str_e 1) && (eeq k l (len_e 1) && argc_ok k 1))%bool eqn:C1.
      { apply andb_prop in C1 as [Es C1]. apply andb_prop in C1 as [El Hac]. injection HH as <-.
        apply (ARGCASE 1%nat Es El (arg_ok_of E FULL MR k 1 HS HK Hac) eq_refl). }
      destruct (split_lit s) as [sb sk] eqn:Hsp.
      destruct (find_blob k sb sk) as [[n b]|] eqn:Hfb.
      - destruct (eeq k n l) eqn:Enl; [|discriminate]. injection HH as <-.
        pose proof (find_blob_sound E MR k sb sk n b HK Hfb) as KB.
        pose proof KB as KB'. cbn [kentry_ok] in KB'. destruct KB' as (Hfl & Hlen & Hby).
        pose proof (u_of_split E s sb sk Hsp ltac:(destruct Hfl as (?&?&?&?); lia)) as Us.
        exists (eb E b). cbn [pbytes flat_map piece_den]. rewrite app_nil_r.
        pose proof (kblob_rdn E MR sb sk n b KB) as RB. rewrite <- Us, Z_to_bv_bv_unsigned in RB.
        split; [reflexivity|]. split; [apply (rdn_Mr_FULL E cs model FULL); exact RB|].
        split; [rewrite <- (eeq_sound SEGS E MR k _ _ HK Enl); unfold elenZ in Hlen; lia|].
        split; [destruct Hfl as (?&?&?&?); unfold elenZ in *; lia|]. right. right. exact RB.
      - destruct lz as [z|]; [|discriminate]. destruct (LZ z eq_refl) as [Vl Hz].
        destruct (flat_x k sb sk (ELit z)) eqn:Hfx; [|discriminate].
        destruct (kread_bytes SEGS (Z.to_nat z) k sb sk) as [bs|] eqn:Hkb; [|discriminate]. injection HH as <-.
        pose proof (flat_x_sound SEGS E MR k sb sk (ELit z) HK Hfx) as Hfl0. rewrite edenot_lit, u64_lit in Hfl0 by (unfold two64 in Hz; lia).
        destruct (kread_bytes_rdn E MR k (Z.to_nat z) sb sk bs HK Hkb ltac:(unfold estart in Hfl0; cbn [a_base a_off] in Hfl0; lia)
                    ltac:(unfold estart in Hfl0; cbn [a_base a_off] in Hfl0; lia)) as [RB Lbs].
        pose proof (u_of_split E s sb sk Hsp ltac:(lia)) as Us. unfold estart in Us; cbn [a_base a_off] in Us.
        rewrite <- Us, Z_to_bv_bv_unsigned in RB.
        exists (map (fun z0 => Z_to_bv 8 z0) bs). cbn [pbytes flat_map piece_den]. rewrite app_nil_r, length_map, Lbs.
        split; [reflexivity|]. split; [apply (rdn_Mr_FULL E cs model FULL); exact RB|].
        split; [rewrite Vl, Z2Nat.id by lia; reflexivity|].
        split; [unfold estart in Hfl0; cbn [a_base a_off] in Hfl0; rewrite Z2Nat.id by lia; lia|]. right. right. exact RB. }
    destruct l as [z| | | | | | |];
      try (apply (GEN None); [intros z Hz; discriminate | exact H]).
    (* [comment removed for export] *)
    cbv beta iota zeta in H.
    destruct (Z.eq_dec (z mod two64) 0) as [Z0|Z0].
    - rewrite Z0 in H. injection H as <-. exists []. cbn. rewrite Z.add_0_r.
      split; [reflexivity|]. split; [reflexivity|]. split; [cbn [edenot]; rewrite Z_to_bv_unsigned, bv_wrap64_mod; exact Z0|].
      split; [lia|]. left. reflexivity.
    - apply (GEN (Some (z mod two64))).
      + intros z' Hz'. injection Hz' as <-. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod. unfold two64 in *.
        pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)). split; [reflexivity | lia].
      + destruct (z mod two64) as [|p|p]; [exfalso; apply Z0; reflexivity | exact H | exact H].
  Qed.

  (* [comment removed for export] *)
  Lemma lazyH_bounds : forall E cs R FULL model (w : word),
    CSOK E cs R FULL model -> lazyH model w = true ->
    (bv_unsigned w < img_lo A \/ img_hi A <= bv_unsigned w) /\ bv_unsigned w < alloc_top (m_vmmaps model).
  Proof.
    intros E cs R FULL model w HC Hw. unfold lazyH, mkH in Hw. apply andb_prop in Hw as [Hp _].
    pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (U0 & U1 & U2 & U3).
    exact (lazy_page_out' (img_lo A) (img_hi A) w _ _ (conj U0 (conj U1 U2)) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HC) Hp).
  Qed.

  (* [comment removed for export] *)
  Lemma lazyH_bounds' : forall E cs R FULL model (w : word),
    CSOK E cs R FULL model -> lazyH model w = true ->
    (bv_unsigned w < img_lo A \/ img_hi A <= bv_unsigned w) /\ bv_unsigned w < usp - 8388608.
  Proof. intros E cs R FULL model w HC Hw. rewrite <- (alloc_top_usp _ _ _ _ _ HC). exact (lazyH_bounds E cs R FULL model w HC Hw). Qed.

  Lemma lazyH_off_segments : forall E cs R FULL model,
    CSOK E cs R FULL model -> H_off_segments SEGS (lazyH model).
  Proof.
    intros E cs R FULL model HC a Ha. pose proof (lazyH_bounds E cs R FULL model a HC Ha) as [B1 B2].
    apply SEGS_in_hull. unfold in_hull. apply andb_false_iff. destruct B1 as [B1|B1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma off_lazy_avoids : forall E cs R FULL model (a : Z) n,
    CSOK E cs R FULL model -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    ((img_lo A <= a /\ a + Z.of_nat n <= img_hi A) \/ usp - 8388608 <= a) ->
    range_avoids (lazyH model) (Z_to_bv 64 a) n.
  Proof.
    intros E cs R FULL model a n HC Ha Hn Hoff. apply range_avoids_by_addr; [exact Ha | exact Hn |].
    intros w Hw Hin. pose proof (lazyH_bounds' E cs R FULL model w HC Hw). lia.
  Qed.

  Lemma off_lazy_sound : forall E M0 M k b n hi lo,
    SINV E M0 -> know_ok SEGS E M k -> off_lazy A k b n = true ->
    xhi k (eadd b n) = Some hi -> xlo k b = Some lo ->
    (img_lo A <= bv_unsigned (edenot E b) /\ bv_unsigned (edenot E (eadd b n)) <= img_hi A)
    \/ usp - 8388608 <= bv_unsigned (edenot E b).
  Proof.
    intros E M0 M k b n hi lo HS HK H Hhi Hlo. unfold off_lazy in H. rewrite Hhi, Hlo in H. rewrite if_orb in H.
    pose proof (xhi_sound SEGS E M k _ hi HK Hhi). pose proof (xlo_sound SEGS E M k _ lo HK Hlo).
    apply orb_prop in H as [H|H].
    - apply andb_prop in H as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2. left. lia.
    - right. pose proof (lin_ge0_sound SEGS E M k _ _ HK H) as LG. cbn [xt_den] in LG.
      pose proof (SINV_vals E M0 HS) as (US & _). unfold uE in US. rewrite US in LG. unfold STK in LG. lia.
  Qed.

  Lemma flat_abs0 : forall E off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z ->
    flat E (SA (ELit 0) off) n.
  Proof. intros E off n H0 Hn Hnw Hlt. unfold flat, estart. cbn [a_base a_off]. rewrite edenot_lit, u64_lit by lia. lia. Qed.

  Lemma adenot_abs0 : forall E off, 0 <= off < 2 ^ 64 -> adenot E (SA (ELit 0) off) = Z_to_bv 64 off.
  Proof. intros E off H. rewrite adenot_SA'. unfold estart. cbn [a_base a_off]. rewrite edenot_lit, u64_lit by lia. f_equal. Qed.

  (* [comment removed for export] *)
  Definition emit_stmt' : Prop := emit_stmt SEGS A nx0 LIMIT (xe SEGS A nx0) SINV argH LINV FS0.

End NodesArg.

End FPW_1.
