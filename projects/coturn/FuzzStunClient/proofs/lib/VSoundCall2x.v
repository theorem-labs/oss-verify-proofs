(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VCert VItab VDriverMatch VContract VDriver VSoundMatch VSound VSoundCall VSoundCall2 VState2 VStepMem2 VCert2 VContract2 VDriverMatch2 VDriver2 VGamma2 VStepMem2SoundA VStepMem2SoundC VSound2 VSoundStep2 VSoundContract2 VSoundMatch2 VSoundAll2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac liae := Z.to_euclidean_division_equations; lia.
Local Ltac niae := Z.to_euclidean_division_equations; nia.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma list_choice {T U} (R : T -> U -> Prop) : forall l : list T,
  (forall x, In x l -> exists y, R x y) -> exists ys, Forall2 R l ys.
Proof.
  induction l as [|x t IH]; intros H; [exists []; constructor|].
  destruct (H x (or_introl eq_refl)) as [y Hy]. destruct (IH ltac:(intros z Hz; apply H; right; exact Hz)) as [ys Hys].
  exists (y :: ys). constructor; auto.
Qed.

Lemma Forall2_nth_r {TA TB} (R : TA -> TB -> Prop) : forall l1 l2 i y,
  Forall2 R l1 l2 -> nth_error l2 i = Some y -> exists x, nth_error l1 i = Some x /\ R x y.
Proof.
  intros l1 l2 i y H. revert i. induction H as [|x y0 l1 l2 Hxy H IH]; intros i Hi; [destruct i; discriminate|].
  destruct i as [|i]; cbn in Hi |- *; [injection Hi as ->; exists x; auto|exact (IH _ Hi)].
Qed.

Lemma Forall2_In_r {TA TB} (R : TA -> TB -> Prop) l1 l2 y :
  Forall2 R l1 l2 -> In y l2 -> exists x, In x l1 /\ R x y.
Proof.
  intros H Hy. destruct (in_nth_error _ _ Hy) as [i Hi]. destruct (Forall2_nth_r R _ _ _ _ H Hi) as (x & Hx & Rx).
  exists x. split; [eapply nth_error_In; exact Hx|exact Rx].
Qed.

Lemma Forall2_In_l {TA TB} (R : TA -> TB -> Prop) l1 l2 x :
  Forall2 R l1 l2 -> In x l1 -> exists y, In y l2 /\ R x y.
Proof.
  intros H. induction H as [|x0 y l1 l2 Hxy H IH]; intros Hx; [destruct Hx|].
  destruct Hx as [<-|Hx]; [exists y; split; [now left|exact Hxy]|]. destruct (IH Hx) as (y' & Hy' & R'). exists y'. split; [now right|exact R'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma vs_globs_materialize : forall l X, vs_globs (materialize X l) = vs_globs X.
Proof.
  induction l as [|[r i] t IH]; intros X; cbn [materialize]; [reflexivity|]. rewrite IH.
  unfold materialize1. destruct (get_reg X r); [reflexivity|].
  unfold afresh, fresh_lin. cbn. unfold set_reg. destruct (Z.eqb r 0); destruct X; reflexivity.
Qed.

Lemma insert_prio2_in V l x : In x (insert_prio2 V l) -> x = V \/ In x l.
Proof.
  induction l as [|W t IH]; simpl.
  - intros [H|[]]; auto.
  - destruct (Z.ltb (u_prio (u1 V)) (u_prio (u1 W))); simpl; intros H.
    + destruct H as [H|H]; auto.
    + destruct H as [H|H]; [auto|]. destruct (IH H); auto.
Qed.

Lemma hinted_variants2_in calls pc all V : In V (hinted_variants2 calls pc all) -> In V all.
Proof.
  induction calls as [|c t IH]; simpl; [tauto|]. destruct (Z.eqb (call_pc c) pc); [|exact IH].
  intros H. apply in_app_or in H as [H|H]; [|exact (IH H)]. apply filter_In in H. tauto.
Qed.

Lemma done_index_in : forall done k V,
  In V (match pm_get k (done_index done) with Some l => l | None => [] end) -> In V done.
Proof.
  induction done as [|W t IH]; intros k V H; cbn [done_index fold_right] in H.
  - rewrite pm_get_empty in H. destruct H.
  - fold (done_index t) in H. unfold idx_add in H.
    destruct (Pos.eq_dec (zkey (u_entry (u1 W))) k) as [E|E].
    + rewrite E, pm_get_set_same in H. destruct H as [H|H]; [left; exact H|].
      right. rewrite <- E in H. exact (IH _ _ H).
    + rewrite pm_get_set_other in H by exact E. right. exact (IH _ _ H).
Qed.

Lemma call_variants2_in G done U pc tgt V :
  In V (call_variants2 (mk_denv2 G done U) pc tgt) -> In V done /\ u_entry (u1 V) = tgt.
Proof.
  unfold call_variants2.
  assert (GEN : forall l, In V (fold_right insert_prio2 [] l) -> In V l).
  { induction l as [|W t IH]; simpl; [tauto|]. intros H. apply insert_prio2_in in H as [->|H]; auto. }
  set (cands := List.filter (fun V => Z.eqb (u_entry (u1 V)) tgt)
                  (match pm_get (zkey tgt) (de2_vidx (mk_denv2 G done U)) with Some l => l | None => [] end)).
  assert (CI : In V cands -> In V done /\ u_entry (u1 V) = tgt).
  { intros H. apply filter_In in H as [H1 H2]. apply Z.eqb_eq in H2. split; [|exact H2].
    exact (done_index_in done (zkey tgt) V H1). }
  intros H. destruct (hinted_variants2 (u_calls (u1 (de2_U (mk_denv2 G done U)))) pc cands) as [|W l] eqn:HV.
  - apply GEN in H. exact (CI H).
  - rewrite <- HV in H. apply hinted_variants2_in in H. exact (CI H).
Qed.

Lemma try_variants2_sound D A spoff npc : forall l msgs succs,
  try_variants2 D A l spoff npc msgs = SN2 succs ->
  exists V, In V l /\ try_variant2 D A V spoff npc = SN2 succs.
Proof.
  induction l as [|V t IH]; simpl; intros msgs succs H; [discriminate|].
  destruct (try_variant2 D A V spoff npc) as [s|m] eqn:T.
  - inversion H; subst. exists V. auto.
  - destruct (IH _ _ H) as [V' [Hin HT]]. exists V'. auto.
Qed.

Lemma apply_exits2_in P B sigma spoff npc : forall l succs X B1' sigma',
  apply_exits2 P B sigma spoff npc l = Some succs -> In X l ->
  apply_exit2v (v1 B) sigma spoff (v1 (load_cstate2 P X npc [])) = Some (B1', sigma') ->
  exists B', apply_exit2w B B1' sigma' (load_cstate2 P X npc []) = Some B' /\ In B' succs.
Proof.
  induction l as [|Y t IH]; intros succs X B1' sigma' H Hin HV; [destruct Hin|]. cbn [apply_exits2] in H.
  destruct Hin as [->|Hin].
  - rewrite HV in H. destruct (apply_exit2w B B1' sigma' (load_cstate2 P X npc [])) as [B'|] eqn:HW; [|discriminate].
    destruct (apply_exits2 P B sigma spoff npc t) as [r|]; [|discriminate]. injection H as <-.
    exists B'. split; [reflexivity|now left].
  - destruct (apply_exit2v (v1 B) sigma spoff (v1 (load_cstate2 P Y npc []))) as [[B1y sy]|] eqn:HY.
    + destruct (apply_exit2w B B1y sy (load_cstate2 P Y npc [])) as [By|]; [|discriminate].
      destruct (apply_exits2 P B sigma spoff npc t) as [r|] eqn:HT; [|discriminate]. injection H as <-.
      destruct (IH r X B1' sigma' eq_refl Hin HV) as (B'' & H1 & H2). exists B''. split; [exact H1|now right].
    + destruct (IH succs X B1' sigma' H Hin HV) as (B'' & H1 & H2). exists B''. auto.
Qed.

Lemma try_variant2_inv D A V spoff npc succs :
  try_variant2 D A V spoff npc = SN2 succs ->
  let A0 := set_reg2 (materialize2 A) 1 (Some (lconst npc)) in
  let sigma00 := sigma_sregs (v1 A0) sreg_idx (pm_set RA (lconst npc) pm_empty) in
  exists sigma0 skip8 sigma B,
    u_root (u1 V) = None
    /\ prebind_args A0 (cs_rgn (u2_pre V)) (cs_divdef (u2_pre V)) sigma00 = Some (sigma0, skip8)
    /\ match_state2 isv_call2 is_sreg_key true MM_call sigma0
         (drop_divdefs skip8 (load_cstate2 (de2_P D) (u2_pre V) (u_entry (u1 V)) [])) A0 = MOk sigma
    /\ footprint_ok2 D A0 sigma V spoff = true
    /\ vp_fdepth (de2_P D) + Z.of_nat (length (fakes_of (vs_rgn A0))) <= u2_fdepth V
    /\ pm_forallb (fun _ e => lin_below e (vs2_next A0)) sigma = true
    /\ call_base2 D A0 V sigma spoff npc = Some B
    /\ apply_exits2 (de2_P D) B sigma spoff npc (u2_exits V) = Some succs
    /\ forallb (fun B' => vstate_below_b (v1 B') && globs_in_fcells (de2_P D) B') succs = true.
Proof.
  unfold try_variant2. destruct (u_root (u1 V)); [discriminate|]. cbv zeta.
  destruct (prebind_args _ _ _ _) as [[sigma0 skip8]|] eqn:PB; [|discriminate].
  destruct (match_state2 _ _ _ _ _ _ _) as [sigma|m] eqn:M; [|discriminate].
  destruct (footprint_ok2 D _ sigma V spoff) eqn:FP; [|discriminate]. cbn [negb].
  destruct (Z.leb_spec (vp_fdepth (de2_P D) + Z.of_nat (length (fakes_of (vs_rgn (set_reg2 (materialize2 A) 1 (Some (lconst npc))))))) (u2_fdepth V)) as [FD|]; [|discriminate]. cbn [negb].
  destruct (pm_forallb _ sigma) eqn:PF; [|discriminate]. cbn [negb].
  destruct (call_base2 D _ V sigma spoff npc) as [B|] eqn:CB; [|discriminate].
  destruct (apply_exits2 _ B sigma spoff npc (u2_exits V)) as [succs'|] eqn:AE; [|discriminate].
  destruct (forallb _ _) eqn:WB; [|discriminate].
  intros X; inversion X; subst. exists sigma0, skip8, sigma, B. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma RB_eval isv A sigma nu s b' c :
  RB isv A sigma s b' c -> vsubst nu sigma s = nu b' + c.
Proof.
  intros [(e & G & EV & _)|(G & _ & -> & -> & _)]; unfold vsubst; rewrite G; [apply EV|lia].
Qed.

Lemma RB_functional isv A sigma s b1 c1 b2 c2 :
  RB isv A sigma s b1 c1 -> RB isv A sigma s b2 c2 -> b1 = b2 /\ c1 = c2.
Proof.
  intros [(e & G & EV & _)|(G & _ & E1 & C1 & _)] [(e' & G' & EV' & _)|(G' & _ & E2 & C2 & _)]; try congruence.
  - rewrite G in G'. injection G' as <-.
    pose proof (EV (fun _ => 0)) as X0. rewrite (EV' (fun _ => 0)) in X0.
    pose proof (EV (fun x => if Pos.eqb x b1 then 1 else 0)) as X1. rewrite (EV' (fun x => if Pos.eqb x b1 then 1 else 0)), Pos.eqb_refl in X1.
    destruct (Pos.eqb_spec b2 b1) as [->|]; [split; [reflexivity|lia]|lia].
  - subst. auto.
Qed.

Lemma ranges_eqb_eq : forall a b, ranges_eqb a b = true -> a = b.
Proof.
  induction a as [|[x1 y1] t IH]; intros [|[x2 y2] t2]; cbn [ranges_eqb]; try discriminate; [reflexivity|].
  intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  rewrite (IH _ H3). subst. reflexivity.
Qed.

Lemma covered_wordZ l x m a : In (wordZ x, m) l -> 0 <= x -> x <= a -> a + 1 <= x + m -> a < 2 ^ 64 -> covered l a 1.
Proof.
  intros Hin H0 H1 H2 H3. exists (wordZ x), m. split; [exact Hin|]. rewrite u_wordZ by lia. lia.
Qed.

Lemma outside_forall a l : outside a l <-> (forall b n, In (b, n) l -> ~ in_rng a b n).
Proof.
  induction l as [|[b n] t IH]; cbn [outside].
  - split; [intros _ ? ? []|intros; exact I].
  - split.
    + intros [H1 H2] b' n' [E|Hin]; [injection E as <- <-; exact H1|]. exact (proj1 IH H2 _ _ Hin).
    + intros H. split; [apply H; now left|]. apply (proj2 IH). intros b' n' Hin. apply H. now right.
Qed.

Lemma classes_regions_mono P fs L L' : forall n e,
  (forall cp, In cp L -> In cp L') ->
  In e (classes_regions P fs n L') -> In e (classes_regions P fs n L).
Proof.
  induction n as [|k IH]; intros e SUB H; cbn [classes_regions] in H |- *; [exact H|].
  apply in_app_iff in H as [H|H]; apply in_app_iff; [left; exact (IH _ SUB H)|right].
  unfold class_regions in H |- *. apply in_flat_map in H as (pos & Hpos & H). apply in_flat_map. exists pos. split; [exact Hpos|].
  destruct (existsb (fun cp : Z * Z => Z.eqb (fst cp) (Z.of_nat k) && Z.eqb (snd cp) pos) L') eqn:X'; [destruct H|].
  destruct (existsb (fun cp : Z * Z => Z.eqb (fst cp) (Z.of_nat k) && Z.eqb (snd cp) pos) L) eqn:X; [|exact H].
  apply existsb_exists in X as [cp [Hcp Hb]]. exfalso.
  assert (X2 : existsb (fun cp : Z * Z => Z.eqb (fst cp) (Z.of_nat k) && Z.eqb (snd cp) pos) L' = true).
  { apply existsb_exists. exists cp. split; [exact (SUB _ Hcp)|exact Hb]. }
  rewrite X2 in X'. discriminate.
Qed.

(* [comment removed for export] *)
Lemma class_regions_P (P P' : vparams2) fs cid L : vp_shoff P = vp_shoff P' -> class_regions P fs cid L = class_regions P' fs cid L.
Proof. intros H. unfold class_regions. rewrite H. reflexivity. Qed.

Lemma classes_regions_P (P P' : vparams2) fs L : forall n, vp_shoff P = vp_shoff P' -> classes_regions P fs n L = classes_regions P' fs n L.
Proof. induction n as [|k IH]; intros H; cbn [classes_regions]; [reflexivity|]. rewrite (IH H), (class_regions_P P P' _ _ _ H). reflexivity. Qed.

Lemma fs_regions_P (P P' : vparams2) E : vp_shoff P = vp_shoff P' -> vp_fs P = vp_fs P' -> fs_regions P E = fs_regions P' E.
Proof. intros H1 H2. unfold fs_regions. rewrite H2, (classes_regions_P P P' _ _ _ H1). reflexivity. Qed.

Lemma shadow_nest_arith sp0 lo hi lo' hi' ua shoff :
  sp0 mod 16 = 0 -> lo mod 8 = 0 -> hi mod 8 = 0 -> lo' mod 8 = 0 -> hi' mod 8 = 0 ->
  lo' <= lo -> hi <= hi' ->
  shoff + (sp0 + lo) / 8 <= ua < shoff + (sp0 + lo) / 8 + (hi - lo) / 8 ->
  shoff + (sp0 + lo') / 8 <= ua < shoff + (sp0 + lo') / 8 + (hi' - lo') / 8.
Proof.
  intros S16 L8 H8 L8' H8' LE1 LE2 R.
  pose proof (Z.div_mod sp0 16 ltac:(lia)) as DS. rewrite S16, Z.add_0_r in DS.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as DL. rewrite L8, Z.add_0_r in DL.
  pose proof (Z.div_mod hi 8 ltac:(lia)) as DH. rewrite H8, Z.add_0_r in DH.
  pose proof (Z.div_mod lo' 8 ltac:(lia)) as DL'. rewrite L8', Z.add_0_r in DL'.
  pose proof (Z.div_mod hi' 8 ltac:(lia)) as DH'. rewrite H8', Z.add_0_r in DH'.
  set (s := sp0 / 16) in *. set (l := lo / 8) in *. set (h := hi / 8) in *. set (l' := lo' / 8) in *. set (h' := hi' / 8) in *.
  assert (E1 : (sp0 + lo) / 8 = 2 * s + l) by (rewrite DS, DL; replace (16 * s + 8 * l) with ((2 * s + l) * 8) by lia; apply Z.div_mul; lia).
  assert (E1' : (sp0 + lo') / 8 = 2 * s + l') by (rewrite DS, DL'; replace (16 * s + 8 * l') with ((2 * s + l') * 8) by lia; apply Z.div_mul; lia).
  assert (E3 : (hi - lo) / 8 = h - l) by (rewrite DH, DL; replace (8 * h - 8 * l) with ((h - l) * 8) by lia; apply Z.div_mul; lia).
  assert (E3' : (hi' - lo') / 8 = h' - l') by (rewrite DH', DL'; replace (8 * h' - 8 * l') with ((h' - l') * 8) by lia; apply Z.div_mul; lia).
  rewrite E1, E3 in R. rewrite E1', E3'.
  assert (LL : l' <= l) by (clear - LE1 DL DL'; lia). assert (HH : h <= h') by (clear - LE2 DH DH'; lia).
  clear - R LL HH. lia.
Qed.

Lemma in_unit_regions2_args P E e : In e (arg_regions P E) -> In e (unit_regions2 P E).
Proof. intros H. unfold unit_regions2. rewrite !in_app_iff. auto. Qed.
Lemma in_unit_regions2_shadow P E e fsv : vp_fs P = Some fsv -> In e (stack_shadow_regions P E) -> In e (unit_regions2 P E).
Proof. intros H1 H. unfold unit_regions2. rewrite H1, !in_app_iff. auto. Qed.
Lemma in_unit_regions2_fs P E e : In e (fs_regions P E) -> In e (unit_regions2 P E).
Proof. intros H. unfold unit_regions2. rewrite !in_app_iff. auto. Qed.

Lemma shadow_cover_arith sp0 lo0 hi0 off shoff :
  sp0 mod 16 = 0 -> lo0 mod 8 = 0 -> hi0 mod 8 = 0 -> lo0 / 8 <= off < hi0 / 8 ->
  0 <= sp0 + lo0 -> hi0 <= 0 -> 0 <= shoff <= 2 ^ 32 -> sp0 < 2 ^ 64 ->
  0 <= shoff + (sp0 + lo0) / 8
  /\ shoff + (sp0 + lo0) / 8 <= shoff + sp0 / 8 + off
  /\ shoff + sp0 / 8 + off + 1 <= shoff + (sp0 + lo0) / 8 + (hi0 - lo0) / 8
  /\ shoff + sp0 / 8 + off < 2 ^ 64.
Proof.
  intros S16 L8 H8 OFF P0 HN SH SP.
  pose proof (Z.div_mod sp0 16 ltac:(lia)) as DS. rewrite S16, Z.add_0_r in DS.
  pose proof (Z.div_mod lo0 8 ltac:(lia)) as DL. rewrite L8, Z.add_0_r in DL.
  pose proof (Z.div_mod hi0 8 ltac:(lia)) as DH. rewrite H8, Z.add_0_r in DH.
  set (s := sp0 / 16) in *. set (l := lo0 / 8) in *. set (h := hi0 / 8) in *.
  assert (E1 : (sp0 + lo0) / 8 = 2 * s + l) by (rewrite DS, DL; replace (16 * s + 8 * l) with ((2 * s + l) * 8) by lia; apply Z.div_mul; lia).
  assert (E2 : sp0 / 8 = 2 * s) by (rewrite DS; replace (16 * s) with ((2 * s) * 8) by lia; apply Z.div_mul; lia).
  assert (E3 : (hi0 - lo0) / 8 = h - l) by (rewrite DH, DL; replace (8 * h - 8 * l) with ((h - l) * 8) by lia; apply Z.div_mul; lia).
  rewrite E1, E2, E3. (ltac2:(LK.k [@OFF; @P0; @HN; @SH; @SP; @DS; @DL; @DH; @E3]); lia).
Qed.

(* [comment removed for export] *)
Lemma div8_add_l m x : (8 * m + x) / 8 = m + x / 8.
Proof. rewrite Z.mul_comm. rewrite Z.div_add_l by lia. reflexivity. Qed.

Lemma div8_mono a b : a <= b -> a / 8 <= b / 8.
Proof. intros. apply Z.div_le_mono; lia. Qed.

Lemma div8_sep a b : a + 8 <= b -> a / 8 < b / 8.
Proof. intros H. assert (a / 8 + 1 <= b / 8); [|lia]. replace (a / 8 + 1) with ((a + 1 * 8) / 8) by (rewrite Z.div_add by lia; lia). apply Z.div_le_mono; lia. Qed.

Lemma div8_split lo d : lo / 8 + d / 8 <= (lo + d + 7) / 8.
Proof.
  apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.mul_div_le lo 8 ltac:(lia)). pose proof (Z.mul_div_le d 8 ltac:(lia)). lia.
Qed.

Lemma div8_exact_range a n y : a mod 8 = 0 -> n mod 8 = 0 -> a / 8 <= y < a / 8 + n / 8 <-> a <= 8 * y < a + n.
Proof.
  intros A N. pose proof (Z.div_mod a 8 ltac:(lia)) as DA. rewrite A, Z.add_0_r in DA.
  pose proof (Z.div_mod n 8 ltac:(lia)) as DN. rewrite N, Z.add_0_r in DN. lia.
Qed.

(* [comment removed for export] *)
Lemma isv_call2_ASYM2 i : 0 <= i < 8 -> isv_call2 (ASYM2 i) = true.
Proof.
  intros Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
Qed.

Lemma isv_call2_ASYM8 i : 0 <= i < 8 -> isv_call2 (ASYM8 i) = true.
Proof.
  intros Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
Qed.

Lemma sub_sigma_set_new sigma k e : pm_get k sigma = None -> sub_sigma sigma (pm_set k e sigma).
Proof. intros Hk k' e' G. rewrite pm_get_set_other; [exact G|]. intros ->. congruence. Qed.

Lemma prebind_args_spec A0 pre_dd : forall l sigma sigma' sk,
  prebind_args A0 l pre_dd sigma = Some (sigma', sk) ->
  sub_sigma sigma sigma'
  /\ (forall s0, binds_only isv_call2 s0 sigma -> binds_only isv_call2 s0 sigma')
  /\ (forall q, In q sk ->
        exists i bc c bc8 rc e,
          0 <= i < 8 /\ q = ASYM8 i
          /\ (forall d, In d pre_dd -> fst d = q -> fst (snd d) = lsym (ASYM2 i) /\ snd (snd d) = 8)
          /\ pm_get (ASYM2 i) sigma' = Some e /\ (forall nu, eval nu e = nu bc + c) /\ is_base A0 bc = true
          /\ comp A0 bc = Some bc8 /\ base_res8 A0 bc = Some rc
          /\ pm_get q sigma' = Some (laddc (lsym bc8) ((c + rc) / 8))).
Proof.
  induction l as [|sr t IH]; intros sigma sigma' sk H; cbn [prebind_args] in H.
  - injection H as <- <-. split; [apply sub_sigma_refl|]. split; [auto|]. intros q [].
  - destruct (sr_kind sr) eqn:K; try (exact (IH _ _ _ H)).
    set (b := sr_base sr) in *. set (i := Z.pos b - 19) in *.
    destruct (Z.leb 0 i && Z.ltb i 8) eqn:RI; [|discriminate]. cbn [negb] in H.
    apply andb_prop in RI as [RI1 RI2]. apply Z.leb_le in RI1. apply Z.ltb_lt in RI2.
    assert (Eb : b = ASYM2 i) by (unfold ASYM2, i; lia).
    destruct (get_reg (v1 A0) (10 + i)) as [e|] eqn:GR; [|discriminate].
    set (sigma1 := match pm_get b sigma with Some _ => sigma | None => pm_set b e sigma end) in *.
    assert (S1 : sub_sigma sigma sigma1 /\ (forall s0, binds_only isv_call2 s0 sigma -> binds_only isv_call2 s0 sigma1)
                 /\ exists e1, pm_get b sigma1 = Some e1).
    { unfold sigma1. destruct (pm_get b sigma) as [e0|] eqn:G0.
      - split; [apply sub_sigma_refl|]. split; [auto|]. exists e0. exact G0.
      - split; [apply sub_sigma_set_new; exact G0|]. split.
        + intros s0 BO k v Hk. rewrite pm_get_set in Hk. destruct (Pos.eqb_spec k b) as [->|]; [right; rewrite Eb; apply isv_call2_ASYM2; lia|exact (BO _ _ Hk)].
        + exists e. apply pm_get_set_same. }
    destruct S1 as (U1 & O1 & e1 & G1).
    set (b8 := ASYM8 i) in *.
    destruct (existsb (fun d : sym * (lin * Z) => Pos.eqb (fst d) b8) pre_dd) eqn:NEED; cbn [negb] in H.
    + destruct (forallb _ pre_dd) eqn:OK8; cbn [negb] in H; [|discriminate].
      destruct (pm_get b8 sigma1) eqn:G8; [discriminate|].
      destruct (resolve_base isv_call2 A0 sigma1 b) as [[bc c]|] eqn:RBq; [|discriminate].
      destruct (comp A0 bc) as [bc8|] eqn:CP; [|discriminate].
      destruct (base_res8 A0 bc) as [rc|] eqn:BR; [|discriminate].
      destruct (prebind_args A0 t pre_dd (pm_set b8 (laddc (lsym bc8) ((c + rc) / 8)) sigma1)) as [[s2 sk2]|] eqn:REC; [|discriminate].
      injection H as <- <-.
      destruct (IH _ _ _ REC) as (U2 & O2 & Q2).
      pose proof (sub_sigma_set_new sigma1 b8 (laddc (lsym bc8) ((c + rc) / 8)) G8) as U12.
      split; [eapply sub_sigma_trans; [exact U1|eapply sub_sigma_trans; [exact U12|exact U2]]|]. split.
      { intros s0 BO. apply O2. intros k v Hk. rewrite pm_get_set in Hk.
        destruct (Pos.eqb_spec k b8) as [->|]; [right; apply isv_call2_ASYM8; lia|exact (O1 _ BO _ _ Hk)]. }
      intros q [<-|Hq]; [|exact (Q2 _ Hq)].
      pose proof (resolve_base_spec _ _ _ _ _ _ RBq) as RBf.
      destruct RBf as [(e2 & Ge2 & EV2 & IB2)|(Gn & _)]; [|rewrite G1 in Gn; discriminate].
      exists i, bc, c, bc8, rc, e2. split; [lia|]. split; [reflexivity|]. split.
      { intros d Hd Hq. rewrite forallb_forall in OK8. specialize (OK8 _ Hd). cbn beta in OK8.
        rewrite Hq, Pos.eqb_refl in OK8. cbn [negb orb] in OK8. apply andb_prop in OK8 as [X1 X2].
        apply lin_eqb_eq in X1. apply Z.eqb_eq in X2. rewrite <- Eb. auto. }
      split; [apply U2; rewrite pm_get_set_other; [rewrite <- Eb; exact Ge2|]; unfold b8, ASYM2, ASYM8; lia|].
      split; [exact EV2|]. split; [exact IB2|]. split; [exact CP|]. split; [exact BR|].
      apply U2. apply pm_get_set_same.
    + destruct (prebind_args A0 t pre_dd sigma1) as [[s2 sk2]|] eqn:REC; [|discriminate]. injection H as <- <-.
      destruct (IH _ _ _ REC) as (U2 & O2 & Q2).
      split; [eapply sub_sigma_trans; [exact U1|exact U2]|]. split; [intros s0 BO; apply O2, O1, BO|]. exact Q2.
Qed.

Lemma unit_static_ok2_mod8 G P U : unit_static_ok2 G P U = None -> mod8_ok P U = true.
Proof.
  unfold unit_static_ok2.
  destruct (cstate2_ok P (u2_pre U) && cstate2_iface_b (u2_pre U) && wrgn_ok U (u2_pre U)); [|discriminate].
  destruct (pre_canonical2 G P U); [|discriminate].
  destruct (forallb _ (u2_cuts U)); [|discriminate].
  destruct (pc_ok (u_entry (u1 U))); [|discriminate].
  destruct (forallb _ (u2_exits U)); [|discriminate].
  cbn [negb].
  destruct (ge2_ranks G && negb _); [discriminate|].
  destruct (forallb _ (u_wstack (u1 U))); [|discriminate].
  destruct (forallb _ (vp_wcells (p1 P))); [|discriminate].
  destruct (Z.ltb 0 (u_sp (u1 U)) || _); [discriminate|].
  destruct (mod8_ok P U); [reflexivity|discriminate].
Qed.

Lemma mod8_facts P U : mod8_ok P U = true -> has_asan P = true ->
  u_sp (u1 U) mod 8 = 0 /\ vp_frame (p1 P) mod 8 = 0.
Proof.
  unfold mod8_ok. intros H HA. rewrite HA in H. cbn [negb orb] in H.
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition survives (KL : list (Z * Z)) (off w : Z) : Prop :=
  forall lo hi, In (lo, hi) KL -> off + w <= lo \/ hi <= off.

Lemma rgn_kill_spec r lo hi :
  rshape r (rgn_kill r lo hi)
  /\ (forall k w v, In (k, (w, v)) (vr_cells (rgn_kill r lo hi)) -> In (k, (w, v)) (vr_cells r) /\ (k + w <= lo \/ hi <= k))
  /\ (forall f, In f (vr_nul (rgn_kill r lo hi)) -> In f (vr_nul r) /\ (snd f < lo \/ hi <= fst f)).
Proof.
  split; [repeat split; reflexivity|]. split.
  - intros k w v Hin. cbn [rgn_kill vr_cells] in Hin. split; [eapply cm_kill_sub; exact Hin|].
    pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin). lia.
  - intros f Hf. cbn [rgn_kill vr_nul] in Hf. apply filter_In in Hf as [H1 H2].
    split; [exact H1|]. apply Bool.orb_prop in H2 as [H2|H2]; [apply Z.ltb_lt in H2|apply Z.leb_le in H2]; lia.
Qed.

Lemma rgn_kill_ranges_spec : forall l r,
  rshape r (rgn_kill_ranges r l)
  /\ (forall k w v, In (k, (w, v)) (vr_cells (rgn_kill_ranges r l)) -> In (k, (w, v)) (vr_cells r) /\ survives l k w)
  /\ (forall f, In f (vr_nul (rgn_kill_ranges r l)) -> In f (vr_nul r) /\ survives l (fst f) (snd f - fst f + 1)).
Proof.
  induction l as [|[lo hi] t IH]; intros r; cbn [rgn_kill_ranges].
  - split; [apply rshape_refl|]. split; [intros; split; [assumption|intros ? ? []]|intros; split; [assumption|intros ? ? []]].
  - destruct (IH (rgn_kill r lo hi)) as (S1 & C1 & N1). destruct (rgn_kill_spec r lo hi) as (S0 & C0 & N0).
    split; [eapply rshape_trans; [exact S0|exact S1]|]. split.
    + intros k w v Hin. destruct (C1 _ _ _ Hin) as [Hin0 SV]. destruct (C0 _ _ _ Hin0) as [Hin1 D].
      split; [exact Hin1|]. intros lo' hi' [E|Hin']; [injection E as <- <-; exact D|exact (SV _ _ Hin')].
    + intros f Hf. destruct (N1 _ Hf) as [Hf0 SV]. destruct (N0 _ Hf0) as [Hf1 D].
      split; [exact Hf1|]. intros lo' hi' [E|Hin']; [injection E as <- <-; lia|exact (SV _ _ Hin')].
Qed.

(* [comment removed for export] *)
Lemma rgn_cut_spec r lo hi :
  rshape r (rgn_cut r lo hi)
  /\ (forall k w v, In (k, (w, v)) (vr_cells (rgn_cut r lo hi)) ->
        (k + w <= lo \/ hi <= k)
        /\ exists k0 w0, In (k0, (w0, v)) (vr_cells r) /\ k0 <= k /\ k + w <= k0 + w0
                         /\ ((k, w) = (k0, w0) \/ (0 < w /\ exists e, v = Some e /\ lin_is_const e = true)))
  /\ (forall f, In f (vr_nul (rgn_cut r lo hi)) -> In f (vr_nul r) /\ (snd f < lo \/ hi <= fst f)).
Proof.
  split; [repeat split; reflexivity|]. split.
  - intros k w v Hin. cbn [rgn_cut vr_cells] in Hin. apply sh_cut_in in Hin as (k0 & w0 & H0 & K1 & K2 & DJ & PC).
    split; [exact DJ|]. exists k0, w0. auto.
  - intros f Hf. cbn [rgn_cut vr_nul] in Hf. apply filter_In in Hf as [H1 H2].
    split; [exact H1|]. apply Bool.orb_prop in H2 as [H2|H2]; [apply Z.ltb_lt in H2|apply Z.leb_le in H2]; lia.
Qed.

(* [comment removed for export] *)
Definition subcell (sh : bool) (cl : cellmap) (k w : Z) (v : absval) : Prop :=
  In (k, (w, v)) cl
  \/ (sh = true /\ 0 < w /\ exists k0 w0 e, In (k0, (w0, Some e)) cl /\ v = Some e /\ lin_is_const e = true
                                          /\ k0 <= k /\ k + w <= k0 + w0).

Definition subcells (sh : bool) (cl' cl : cellmap) : Prop :=
  forall k w v, In (k, (w, v)) cl' -> subcell sh cl k w v.

Lemma subcells_refl sh cl : subcells sh cl cl.
Proof. intros k w v H. left. exact H. Qed.

Lemma subcells_incl sh cl' cl : incl cl' cl -> subcells sh cl' cl.
Proof. intros H k w v Hin. left. apply H. exact Hin. Qed.

Lemma subcells_nil sh cl : subcells sh [] cl.
Proof. intros ? ? ? []. Qed.

Lemma subcell_trans sh cl1 cl2 k w v : subcells sh cl2 cl1 -> subcell sh cl2 k w v -> subcell sh cl1 k w v.
Proof.
  intros H [Hin|(SH & W & k0 & w0 & e & Hin & -> & CE & K1 & K2)]; [exact (H _ _ _ Hin)|].
  destruct (H _ _ _ Hin) as [Hin1|(_ & _ & k1 & w1 & e1 & Hin1 & E1 & CE1 & K3 & K4)].
  - right. split; [exact SH|]. split; [exact W|]. exists k0, w0, e. auto 10.
  - injection E1 as <-. right. split; [exact SH|]. split; [exact W|]. exists k1, w1, e. repeat (split; [first [assumption|reflexivity]|]). lia.
Qed.

Lemma subcells_trans sh cl1 cl2 cl3 : subcells sh cl2 cl1 -> subcells sh cl3 cl2 -> subcells sh cl3 cl1.
Proof. intros H12 H23 k w v Hin. eapply subcell_trans; [exact H12|exact (H23 _ _ _ Hin)]. Qed.

(* [comment removed for export] *)
Lemma subcell_in_nil sh k w v : subcell sh [] k w v -> False.
Proof. intros [[]|(_ & _ & ? & ? & ? & [] & _)]. Qed.

(* [comment removed for export] *)
Lemma subcell_src sh cl k w v : subcell sh cl k w v ->
  exists k0 w0 v0, In (k0, (w0, v0)) cl /\ k0 <= k /\ k + w <= k0 + w0
                   /\ ((k, w, v) = (k0, w0, v0) \/ (sh = true /\ 0 < w /\ exists e, v0 = Some e /\ v = Some e /\ lin_is_const e = true)).
Proof.
  intros [Hin|(SH & W & k0 & w0 & e & Hin & -> & CE & K1 & K2)].
  - exists k, w, v. split; [exact Hin|]. split; [lia|]. split; [lia|]. left; reflexivity.
  - exists k0, w0, (Some e). split; [exact Hin|]. split; [exact K1|]. split; [exact K2|]. right. split; [exact SH|]. split; [exact W|]. exists e; auto.
Qed.

(* [comment removed for export] *)
Definition thins (l l' : list vregion) : Prop :=
  Forall2 (fun r r' => rshape r r' /\ subcells (is_shadow r) (vr_cells r') (vr_cells r) /\ incl (vr_nul r') (vr_nul r)) l l'.

Lemma rshape_is_shadow r r' : rshape r r' -> is_shadow r' = is_shadow r.
Proof. intros (_ & _ & SK & _). unfold is_shadow. rewrite SK. reflexivity. Qed.

Lemma thins_refl l : thins l l.
Proof. induction l; constructor; auto. split; [apply rshape_refl|]. split; [apply subcells_refl|apply incl_refl]. Qed.

Lemma thins_trans l1 l2 l3 : thins l1 l2 -> thins l2 l3 -> thins l1 l3.
Proof.
  intros H12. revert l3. induction H12 as [|x y t t' (S1 & C1 & N1) HT IH]; intros l3 H23; [inversion H23; constructor|].
  inversion H23 as [|y' z t2 t3 (S2 & C2 & N2) HT2]; subst. constructor; [|apply IH; assumption].
  split; [eapply rshape_trans; eauto|]. split; [|eapply incl_tran; eauto].
  rewrite (rshape_is_shadow _ _ S1) in C2. eapply subcells_trans; eauto.
Qed.

Lemma thins_shape l l' : thins l l' -> shape_map l l'.
Proof. induction 1 as [|x y t t' (S & _) HT IH]; constructor; auto. Qed.

Lemma thins_map f l : (forall r, rshape r (f r) /\ subcells (is_shadow r) (vr_cells (f r)) (vr_cells r) /\ incl (vr_nul (f r)) (vr_nul r)) -> thins l (map f l).
Proof. intros H. induction l; cbn; constructor; auto. Qed.

Lemma thins_upd l r r' :
  In r l -> rshape r r' -> subcells (is_shadow r) (vr_cells r') (vr_cells r) -> incl (vr_nul r') (vr_nul r) ->
  List.NoDup (map vr_base l) -> thins l (rgn_upd l r').
Proof.
  intros Hin SH IC IN ND. induction l as [|x t IH]; [destruct Hin|]. cbn [rgn_upd map] in ND |- *.
  apply List.NoDup_cons_iff in ND as [NX ND].
  pose proof SH as (SB & _).
  destruct (Pos.eqb_spec (vr_base x) (vr_base r')) as [EB|NB].
  - destruct Hin as [->|Hin].
    + constructor; [auto|apply thins_refl].
    + exfalso. apply NX. rewrite EB, SB. apply in_map_iff. exists r. auto.
  - destruct Hin as [->|Hin]; [exfalso; apply NB; symmetry; exact SB|].
    constructor; [split; [apply rshape_refl|split; [apply subcells_refl|apply incl_refl]]|]. apply IH; auto.
Qed.

Lemma thins_in_back l l' r' : thins l l' -> In r' l' ->
  exists r, In r l /\ rshape r r' /\ subcells (is_shadow r) (vr_cells r') (vr_cells r) /\ incl (vr_nul r') (vr_nul r).
Proof.
  intros H Hin. destruct (Forall2_In_r _ _ _ _ H Hin) as (r & Hr & X). exists r. split; [exact Hr|exact X].
Qed.

Lemma thins_bases l l' : thins l l' -> map vr_base l' = map vr_base l.
Proof. intros H. apply shape_map_bases. apply thins_shape. exact H. Qed.

Lemma kill_fs_cells_thins l : thins l (kill_fs_cells l).
Proof.
  unfold kill_fs_cells. apply thins_map. intros r. destruct (vr_kind r).
  all: try (split; [apply rshape_refl|split; [apply subcells_refl|apply incl_refl]]).
  split; [repeat split; reflexivity|]. cbn. split; [apply subcells_nil|intros ? []].
Qed.

Lemma kill_fs_cells_fs l r' : In r' (kill_fs_cells l) -> vr_kind r' = RK_fs -> vr_cells r' = [] /\ vr_nul r' = [].
Proof.
  unfold kill_fs_cells. intros H K. apply in_map_iff in H as (r & <- & Hr).
  destruct (vr_kind r) eqn:Kr; cbn in K; try (rewrite Kr in K; discriminate). split; reflexivity.
Qed.

Lemma kill_shadow_sp_thins fr V1u spoff l : thins l (kill_shadow_sp fr V1u spoff l).
Proof.
  unfold kill_shadow_sp. apply thins_map. intros r.
  destruct (vr_kind r) eqn:K; try (split; [apply rshape_refl|split; [apply subcells_refl|apply incl_refl]]).
  destruct (Pos.eqb of_ SP0); [|split; [apply rshape_refl|split; [apply subcells_refl|apply incl_refl]]].
  destruct (rgn_cut_spec r ((- fr) / 8) ((spoff + 7) / 8)) as (S & C & N).
  split; [exact S|]. split; [|intros f H; exact (proj1 (N _ H))].
  intros k w v H. destruct (C _ _ _ H) as (_ & k0 & w0 & H0 & K1 & K2 & PC).
  destruct PC as [E|(W & e & -> & CE)]; [injection E as -> ->; left; exact H0|].
  right. split; [unfold is_shadow; rewrite K; reflexivity|]. split; [exact W|]. exists k0, w0, e. auto 10.
Qed.

Lemma kill_shadow_sp_sp0 fr V1u spoff l r' :
  In r' (kill_shadow_sp fr V1u spoff l) -> vr_kind r' = RK_shadow SP0 ->
  (forall k w v, In (k, (w, v)) (vr_cells r') -> k + w <= (- fr) / 8 \/ (spoff + 7) / 8 <= k)
  /\ (forall f, In f (vr_nul r') -> snd f < (- fr) / 8 \/ (spoff + 7) / 8 <= fst f).
Proof.
  unfold kill_shadow_sp. intros H K. apply in_map_iff in H as (r & E & Hr).
  destruct (vr_kind r) as [| | |o|] eqn:Kr; try (subst r'; rewrite Kr in K; discriminate).
  destruct (Pos.eqb_spec o SP0) as [->|NE]; [|subst r'; rewrite Kr in K; injection K as E'; exfalso; exact (NE E')].
  subst r'. destruct (rgn_cut_spec r ((- fr) / 8) ((spoff + 7) / 8)) as (S & C & N).
  split; [intros k w v Hin; exact (proj1 (C _ _ _ Hin))|intros f Hf; exact (proj2 (N _ Hf))].
Qed.

Lemma havoc_other_args_thins l b : thins l (havoc_other_args l b).
Proof.
  unfold havoc_other_args. apply thins_map. intros r. destruct (vr_kind r); try (split; [apply rshape_refl|split; [apply subcells_refl|apply incl_refl]]).
  destruct (Pos.eqb (vr_base r) b); [split; [apply rshape_refl|split; [apply subcells_refl|apply incl_refl]]|].
  split; [repeat split; reflexivity|]. cbn. split; [apply subcells_nil|intros ? []].
Qed.

Lemma havoc_other_args_arg l b r' : In r' (havoc_other_args l b) -> vr_kind r' = RK_arg -> vr_base r' <> b -> vr_cells r' = [] /\ vr_nul r' = [].
Proof.
  unfold havoc_other_args. intros H K NB. apply in_map_iff in H as (r & E & Hr).
  destruct (vr_kind r) eqn:Kr; try (subst r'; rewrite Kr in K; discriminate).
  destruct (Pos.eqb_spec (vr_base r) b) as [EB|NEB]; [subst r'; exfalso; exact (NB EB)|]. subst r'. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kill_wrgn_spec A sigma : forall l rg rg',
  kill_wrgn A sigma rg l = Some rg' -> List.NoDup (map vr_base rg) ->
  thins rg rg'
  /\ (forall i lo hi b' c r', In (i, (lo, hi)) l -> resolve_base isv_call2 A sigma (ASYM2 i) = Some (b', c) ->
        In r' rg' -> vr_base r' = b' ->
        (forall k w v, In (k, (w, v)) (vr_cells r') -> k + w <= lo + c \/ hi + c <= k)
        /\ (forall f, In f (vr_nul r') -> snd f < lo + c \/ hi + c <= fst f))
  /\ (forall i lo hi b' c pr r', In (i, (lo, hi)) l -> resolve_base isv_call2 A sigma (ASYM2 i) = Some (b', c) ->
        rgn_get rg b' = Some pr -> vr_kind pr = RK_arg ->
        In r' rg' -> vr_kind r' = RK_arg -> vr_base r' <> b' -> vr_cells r' = [] /\ vr_nul r' = []).
Proof.
  induction l as [|[i [lo hi]] t IH]; intros rg rg' H ND; cbn [kill_wrgn] in H.
  - injection H as <-. split; [apply thins_refl|]. split; [intros ? ? ? ? ? ? []|intros ? ? ? ? ? ? ? []].
  - destruct (resolve_base isv_call2 A sigma (ASYM2 i)) as [[b' c]|] eqn:RS; [|discriminate].
    destruct (rgn_get rg b') as [pr|] eqn:Gpr; [|discriminate].
    set (rg1 := match vr_kind pr with RK_arg => havoc_other_args rg b' | _ => rg end) in H.
    destruct (rgn_get_in _ _ _ Gpr) as [Hpr Bpr].
    assert (T1 : thins rg rg1) by (unfold rg1; destruct (vr_kind pr); try apply thins_refl; apply havoc_other_args_thins).
    assert (ND1 : List.NoDup (map vr_base rg1)) by (rewrite (thins_bases _ _ T1); exact ND).
    assert (Hpr1 : In pr rg1).
    { unfold rg1. destruct (vr_kind pr) eqn:Kp; try exact Hpr.
      unfold havoc_other_args. apply in_map_iff. exists pr. rewrite Kp, Bpr, Pos.eqb_refl. auto. }
    destruct (rgn_kill_spec pr (lo + c) (hi + c)) as (SKL & CK & NK).
    set (kr := rgn_kill pr (lo + c) (hi + c)) in *.
    assert (T2 : thins rg1 (rgn_upd rg1 kr)).
    { apply (thins_upd rg1 pr kr Hpr1 SKL); [intros k w v Hx; left; exact (proj1 (CK _ _ _ Hx))|intros f Hf; exact (proj1 (NK _ Hf))|exact ND1]. }
    set (rg2 := rgn_upd rg1 kr) in *.
    assert (ND2 : List.NoDup (map vr_base rg2)) by (rewrite (thins_bases _ _ T2); exact ND1).
    destruct (IH _ _ H ND2) as (T3 & WIN & HAV).
    assert (T13 : thins rg rg') by (eapply thins_trans; [exact T1|eapply thins_trans; [exact T2|exact T3]]).
    split; [exact T13|].
    assert (Bkr : vr_base kr = b') by (destruct SKL as (SB & _); rewrite SB; exact Bpr).
    assert (INkr : In kr rg2).
    { unfold rg2. apply rgn_upd_in_new. rewrite Bkr, <- Bpr. apply in_map_iff. exists pr. auto. }
    split.
    + intros i0 lo0 hi0 b0 c0 r' [E|Hin] RS0 Hr' Br'; [|exact (WIN _ _ _ _ _ _ Hin RS0 Hr' Br')].
      injection E as <- <- <-. rewrite RS in RS0. injection RS0 as <- <-.
      destruct (thins_in_back _ _ _ T3 Hr') as (x & Hx & Sx & Cx & Nx).
      assert (x = kr) as ->.
      { apply (nodup_map_inj vr_base _ _ _ ND2 Hx INkr). destruct Sx as (SB & _). rewrite <- SB, Br', Bkr. reflexivity. }
      split; [|intros f Hf; exact (proj2 (NK _ (Nx _ Hf)))].
      intros k w v Hc. destruct (subcell_src _ _ _ _ _ (Cx _ _ _ Hc)) as (k0 & w0 & v0 & H0 & K1 & K2 & _).
      pose proof (proj2 (CK _ _ _ H0)) as DJ0. clear - DJ0 K1 K2. lia.
    + intros i0 lo0 hi0 b0 c0 pr0 r' [E|Hin] RS0 G0 K0 Hr' Kr' NB.
      * injection E as <- <- <-. rewrite RS in RS0. injection RS0 as <- <-. rewrite Gpr in G0. injection G0 as <-.
        destruct (thins_in_back _ _ _ (thins_trans _ _ _ T2 T3) Hr') as (x & Hx & Sx & Cx & Nx).
        destruct Sx as (SB & _ & SK & _).
        unfold rg1 in Hx. rewrite K0 in Hx.
        destruct (havoc_other_args_arg _ _ _ Hx ltac:(rewrite <- SK; exact Kr') ltac:(rewrite <- SB; exact NB)) as [C0 N0].
        rewrite C0 in Cx. rewrite N0 in Nx. split; [destruct (vr_cells r') as [|[yk [yw yv]] ?]; [reflexivity|exfalso; eapply subcell_in_nil; exact (Cx _ _ _ (or_introl eq_refl))]|].
        destruct (vr_nul r') as [|y ?]; [reflexivity|destruct (Nx y (or_introl eq_refl))].
      * destruct (shape_map_get _ _ _ _ (thins_shape _ _ (thins_trans _ _ _ T1 T2)) G0) as (pr2 & G2 & S2).
        destruct S2 as (_ & _ & SK2 & _).
        exact (HAV _ _ _ _ _ _ _ Hin RS0 G2 ltac:(rewrite SK2; exact K0) Hr' Kr' NB).
Qed.

(* [comment removed for export] *)
Lemma set_exit_rcells_in sigma c : forall l cl k w v, In (k, (w, v)) (set_exit_rcells cl sigma c l) ->
  In (k, (w, v)) cl \/ exists off v0 e', In (off, (w, v0)) l /\ k = off + c /\ osubst2_v sigma v0 = Some e' /\ v = Some e'.
Proof.
  induction l as [|[off [w0 v0]] t IH]; intros cl k w v H; cbn [set_exit_rcells] in H; [auto|].
  destruct (IH _ _ _ _ H) as [H1|(off' & v1 & e' & A1 & A2 & A3 & A4)].
  - destruct (osubst2_v sigma v0) as [e'|] eqn:Ho.
    + apply cm_set_in in H1 as [H1|H1].
      * injection H1 as -> -> ->. right. exists off, v0, e'. split; [now left|auto].
      * left. eapply cm_kill_sub; eauto.
    + left. eapply cm_kill_sub; eauto.
  - right. exists off', v1, e'. split; [now right|auto].
Qed.

Lemma wb_fits_spec xr pr c : wb_fits xr pr c = true ->
  vr_disp xr = vr_disp pr /\ vr_lo pr <= vr_lo xr + c /\ vr_hi xr + c <= vr_hi pr /\ is_shadow xr = is_shadow pr
  /\ match vr_kind pr with RK_shadow s => s <> DATA | _ => True end
  /\ (forall k w v, In (k, (w, v)) (vr_cells xr) -> vr_lo xr <= k /\ 0 < w /\ k + w <= vr_hi xr).
Proof.
  unfold wb_fits. intros H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [destruct (is_shadow xr), (is_shadow pr); try reflexivity; discriminate|].
  split; [destruct (vr_kind pr); try exact I; destruct (Pos.eqb_spec of_ DATA); [discriminate|assumption]|].
  intros k w v Hin. rewrite forallb_forall in H6. specialize (H6 _ Hin). cbn [fst snd] in H6.
  apply andb_prop in H6 as [H6 Z3]. apply andb_prop in H6 as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. apply Z.leb_le in Z3. auto.
Qed.

Lemma in_rev_append_iff {T : Type} (a b : list T) x : In x (rev_append a b) <-> In x a \/ In x b.
Proof. rewrite rev_append_rev, in_app_iff, <- in_rev. tauto. Qed.

Lemma cm_skip_in : forall s rp o rp1 s1, cm_skip rp s o = (rp1, s1) ->
  forall x, In x (rev_append rp1 s1) <-> In x (rev_append rp s).
Proof.
  induction s as [|[k [w v]] t IH]; intros rp o rp1 s1 H x; cbn [cm_skip] in H.
  - injection H as <- <-. reflexivity.
  - destruct (Z.leb (k + w) o).
    + rewrite (IH _ _ _ _ H x). cbn [rev_append]. reflexivity.
    + injection H as <- <-. reflexivity.
Qed.

Lemma cm_kill_s_sub m lo hi x : In x (cm_kill_s m lo hi) -> In x m.
Proof.
  induction m as [|[k [w v]] t IH]; cbn [cm_kill_s]; [simpl; tauto|].
  destruct (Z.leb hi k); [tauto|]. destruct (Z.ltb lo (k + w)); [intros H; right; auto|].
  intros [H|H]; [left; exact H|right; auto].
Qed.

Lemma sh_cut_s_in m lo hi k w v :
  In (k, (w, v)) (sh_cut_s m lo hi) ->
  exists k0 w0, In (k0, (w0, v)) m /\ k0 <= k /\ k + w <= k0 + w0 /\
                ((k, w) = (k0, w0) \/ (0 < w /\ exists e, v = Some e /\ lin_is_const e = true)).
Proof.
  induction m as [|[k0 [w0 v0]] t IH]; cbn [sh_cut_s]; [simpl; tauto|].
  destruct (Z.leb_spec hi k0) as [HK|HK].
  - intros H. exists k, w. split; [exact H|]. split; [lia|]. split; [lia|]. left; reflexivity.
  - destruct (Z.ltb_spec lo (k0 + w0)) as [HL|HL].
    + intros H. apply in_app_or in H as [H|H]; [|apply in_app_or in H as [H|H]].
      * destruct (Z.ltb_spec k0 lo); [|destruct H].
        destruct v0 as [e|]; [|destruct H]. destruct (lin_is_const e) eqn:CE; [|destruct H].
        destruct H as [H|[]]. injection H as <- <- <-. exists k0, w0. split; [now left|]. split; [lia|]. split; [lia|].
        right. split; [lia|]. exists e; auto.
      * destruct (Z.ltb_spec hi (k0 + w0)); [|destruct H].
        destruct v0 as [e|]; [|destruct H]. destruct (lin_is_const e) eqn:CE; [|destruct H].
        destruct H as [H|[]]. injection H as <- <- <-. exists k0, w0. split; [now left|]. split; [lia|]. split; [lia|].
        right. split; [lia|]. exists e; auto.
      * destruct (IH H) as (k1 & w1 & X1 & X2). exists k1, w1. split; [right; exact X1|exact X2].
    + intros [H|H].
      * injection H as <- <- <-. exists k0, w0. split; [now left|]. split; [lia|]. split; [lia|]. left; reflexivity.
      * destruct (IH H) as (k1 & w1 & X1 & X2). exists k1, w1. split; [right; exact X1|exact X2].
Qed.

Lemma set_exit_shcells_t_in : forall l rp s k w v, In (k, (w, v)) (set_exit_shcells_t rp s l) ->
  subcell true (rev_append rp s) k w v
  \/ exists e off0 w0, In (off0, (w0, Some e)) l /\ v = Some e /\ lin_is_const e = true
                       /\ off0 <= k /\ k + w <= off0 + w0 /\ ((k, w) = (off0, w0) \/ 0 < w).
Proof.
  induction l as [|[off [w0 v0]] t IH]; intros rp s k w v H; cbn [set_exit_shcells_t] in H; [left; left; exact H|].
  destruct (cm_skip rp s off) as [rp1 s1] eqn:SK.
  (* [comment removed for export] *)
  assert (CUT : forall k' w' v', subcell true (rev_append rp1 (sh_cut_s s1 off (off + w0))) k' w' v' -> subcell true (rev_append rp s) k' w' v').
  { intros k' w' v' SC. eapply subcell_trans; [|exact SC]. intros k1 w1 v1 Hin.
    apply in_rev_append_iff in Hin as [Hin|Hin].
    - left. apply (cm_skip_in _ _ _ _ _ SK). apply in_rev_append_iff. left. exact Hin.
    - apply sh_cut_s_in in Hin as (k2 & w2 & H2 & K1 & K2 & PC).
      assert (H2' : In (k2, (w2, v1)) (rev_append rp s)) by (apply (cm_skip_in _ _ _ _ _ SK); apply in_rev_append_iff; right; exact H2).
      destruct PC as [E|(W & e & -> & CE)]; [injection E as -> ->; left; exact H2'|].
      right. split; [reflexivity|]. split; [exact W|]. exists k2, w2, e. auto 10. }
  destruct (IH _ _ _ _ _ H) as [SC|(e & off1 & w1 & A1 & A2 & A3 & A4 & A5 & A6)];
    [|right; exists e, off1, w1; split; [now right|auto 10]].
  destruct v0 as [e0|]; [|left; exact (CUT _ _ _ SC)].
  destruct (lin_is_const e0) eqn:CE; [|left; exact (CUT _ _ _ SC)].
  destruct SC as [Hin|(_ & W & k0 & w9 & e & Hin & -> & CE' & K1 & K2)].
  - apply in_rev_append_iff in Hin as [Hin|Hin].
    + left. apply CUT. left. apply in_rev_append_iff. left. exact Hin.
    + apply cm_set_in in Hin as [Hin|Hin].
      * injection Hin as -> -> ->. right. exists e0, off, w0. split; [now left|]. split; [reflexivity|]. split; [exact CE|].
        split; [lia|]. split; [lia|]. left; reflexivity.
      * left. apply CUT. left. apply in_rev_append_iff. right. exact Hin.
  - apply in_rev_append_iff in Hin as [Hin|Hin].
    + left. apply CUT. right. split; [reflexivity|]. split; [exact W|]. exists k0, w9, e. split; [apply in_rev_append_iff; left; exact Hin|]. auto 10.
    + apply cm_set_in in Hin as [Hin|Hin].
      * injection Hin as -> -> ->. right. exists e0, off, w0. split; [now left|]. split; [reflexivity|]. split; [exact CE|].
        split; [exact K1|]. split; [exact K2|]. right; exact W.
      * left. apply CUT. right. split; [reflexivity|]. split; [exact W|]. exists k0, w9, e. split; [apply in_rev_append_iff; right; exact Hin|]. auto 10.
Qed.

Lemma set_exit_shcells_in : forall l cl k w v, In (k, (w, v)) (set_exit_shcells cl l) ->
  subcell true cl k w v
  \/ exists e off0 w0, In (off0, (w0, Some e)) l /\ v = Some e /\ lin_is_const e = true
                       /\ off0 <= k /\ k + w <= off0 + w0 /\ ((k, w) = (off0, w0) \/ 0 < w).
Proof. intros l cl k w v H. exact (set_exit_shcells_t_in l [] cl k w v H). Qed.

(* [comment removed for export] *)
Definition wb_cell (A : vstate2) (sigma : pmap lin) (l : list vregion) (r : vregion) (k w : Z) (v : absval) : Prop :=
  exists xr c off w0 v0,
    In xr l /\ In (off, (w0, v0)) (vr_cells xr)
    /\ vr_disp xr = vr_disp r /\ vr_lo r <= vr_lo xr + c /\ vr_hi xr + c <= vr_hi r /\ is_shadow xr = is_shadow r
    /\ vr_lo xr <= off /\ 0 < w0 /\ off + w0 <= vr_hi xr
    /\ off + c <= k /\ k + w <= off + c + w0 /\ 0 < w
    /\ ((vr_kind xr = RK_arg /\ k = off + c /\ w = w0 /\ resolve_base isv_call2 A sigma (vr_base xr) = Some (vr_base r, c)
         /\ match vr_kind r with RK_fake _ _ | RK_arg => True | _ => False end
         /\ exists e', osubst2_v sigma v0 = Some e' /\ v = Some e')
        \/ (vr_kind xr = RK_shadow SP0 /\ vr_kind r = RK_shadow SP0 /\ c = 0
            /\ exists e, v0 = Some e /\ v = Some e /\ lin_is_const e = true)).

Lemma wb_cell_weaken A sigma xr t r r0 k w v : wb_cell A sigma t r k w v -> rshape r0 r -> wb_cell A sigma (xr :: t) r0 k w v.
Proof.
  intros (xr' & c & off & w0 & v0 & A1 & A2 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & B1 & B2 & B3 & A11) (SB & SD & SK & SL & SH & SW & S8).
  exists xr', c, off, w0, v0. split; [right; exact A1|]. split; [exact A2|].
  rewrite <- SD, <- SL, <- SH in *. unfold is_shadow in *. rewrite <- SK, <- SB in *.
  repeat (split; [assumption|]). exact A11.
Qed.

(* [comment removed for export] *)
Lemma wb_cell_piece A sigma l r k1 w1 e k w :
  wb_cell A sigma l r k1 w1 (Some e) -> is_shadow r = true -> lin_is_const e = true ->
  k1 <= k -> k + w <= k1 + w1 -> 0 < w -> wb_cell A sigma l r k w (Some e).
Proof.
  intros (xr & c & off & w0 & v0 & A1 & A2 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & B1 & B2 & B3 & CASES) SH CE K1 K2 W.
  exists xr, c, off, w0, v0. repeat (split; [assumption|]). split; [lia|]. split; [lia|]. split; [exact W|].
  destruct CASES as [(KX & _ & _ & _ & KR & _)|(KX & KR & C0 & e' & E1 & E2 & CE')].
  - exfalso. unfold is_shadow in SH. destruct (vr_kind r); try discriminate; destruct KR.
  - right. split; [exact KX|]. split; [exact KR|]. split; [exact C0|]. exists e'. auto.
Qed.

Lemma write_back_spec A sigma : forall l rg rg',
  write_back_args A rg sigma l = Some rg' -> List.NoDup (map vr_base rg) ->
  shape_map rg rg'
  /\ (forall r', In r' rg' -> exists r, In r rg /\ rshape r r' /\ vr_nul r' = vr_nul r /\
        forall k w v, In (k, (w, v)) (vr_cells r') -> subcell (is_shadow r) (vr_cells r) k w v \/ wb_cell A sigma l r k w v).
Proof.
  induction l as [|xr t IH]; intros rg rg' H ND; cbn [write_back_args] in H.
  - injection H as <-. split; [apply shape_map_refl|]. intros r' Hr'. exists r'. split; [exact Hr'|]. split; [apply rshape_refl|]. split; [reflexivity|].
    intros k w v Hc. left; left; exact Hc.
  - assert (STEP : forall pr newcells,
              In pr rg ->
              (forall k w v, In (k, (w, v)) newcells -> subcell (is_shadow pr) (vr_cells pr) k w v \/ wb_cell A sigma (xr :: t) pr k w v) ->
              write_back_args A (rgn_upd rg (set_cells pr newcells)) sigma t = Some rg' ->
              shape_map rg rg'
              /\ (forall r', In r' rg' -> exists r, In r rg /\ rshape r r' /\ vr_nul r' = vr_nul r /\
                    forall k w v, In (k, (w, v)) (vr_cells r') -> subcell (is_shadow r) (vr_cells r) k w v \/ wb_cell A sigma (xr :: t) r k w v)).
    { intros pr nc Hpr NC H'.
      set (pr' := set_cells pr nc) in *.
      assert (SH : shape_map rg (rgn_upd rg pr')).
      { apply rgn_upd_shape; [|apply in_map_iff; exists pr; auto].
        intros x Hx Bx. assert (x = pr) as -> by (apply (nodup_map_inj vr_base _ _ _ ND Hx Hpr); exact Bx). apply rshape_set_cells. }
      assert (ND' : List.NoDup (map vr_base (rgn_upd rg pr'))) by (rewrite (shape_map_bases _ _ SH); exact ND).
      destruct (IH _ _ H' ND') as [SH2 PR2].
      split; [eapply shape_map_trans; [exact SH|exact SH2]|].
      intros r' Hr'. destruct (PR2 _ Hr') as (r1 & Hr1 & S1 & N1 & C1).
      (* [comment removed for export] *)
      assert (CASE : r1 = pr' \/ In r1 rg).
      { clear - Hr1. induction rg as [|x q IHq]; cbn [rgn_upd] in Hr1; [destruct Hr1 as [<-|[]]; now left|].
        destruct (Pos.eqb (vr_base x) (vr_base pr')); [destruct Hr1 as [<-|Hr1]; [now left|right; now right]|].
        destruct Hr1 as [<-|Hr1]; [right; now left|]. destruct (IHq Hr1) as [X|X]; [now left|right; now right]. }
      destruct CASE as [->|Hin1].
      - exists pr. split; [exact Hpr|]. split; [eapply rshape_trans; [apply rshape_set_cells|exact S1]|]. split; [exact N1|].
        assert (ISH : is_shadow pr' = is_shadow pr) by reflexivity. rewrite ISH in C1.
        intros k w v Hc. destruct (C1 _ _ _ Hc) as [SC|W]; [|right; eapply wb_cell_weaken; [exact W|apply rshape_set_cells]].
        cbn [pr' set_cells vr_cells] in SC.
        destruct SC as [Hin|(SHp & W & k0 & w0 & e & Hin & -> & CE & K1 & K2)].
        + destruct (NC _ _ _ Hin) as [X|X]; [now left|now right].
        + destruct (NC _ _ _ Hin) as [X|X].
          * left. eapply (subcell_trans _ _ [(k0, (w0, Some e))]).
            -- intros k' w' v' [E0|[]]. injection E0 as <- <- <-. exact X.
            -- right. split; [exact SHp|]. split; [exact W|]. exists k0, w0, e. split; [now left|]. auto.
          * right. eapply wb_cell_piece; eauto.
      - exists r1. split; [exact Hin1|]. split; [exact S1|]. split; [exact N1|].
        intros k w v Hc. destruct (C1 _ _ _ Hc) as [X|W]; [now left|right].
        eapply wb_cell_weaken; [exact W|apply rshape_refl]. }
    assert (SKIP : write_back_args A rg sigma t = Some rg' ->
              shape_map rg rg'
              /\ (forall r', In r' rg' -> exists r, In r rg /\ rshape r r' /\ vr_nul r' = vr_nul r /\
                    forall k w v, In (k, (w, v)) (vr_cells r') -> subcell (is_shadow r) (vr_cells r) k w v \/ wb_cell A sigma (xr :: t) r k w v)).
    { intros H'. destruct (IH _ _ H' ND) as [SH2 PR2]. split; [exact SH2|].
      intros r' Hr'. destruct (PR2 _ Hr') as (r1 & Hr1 & S1 & N1 & C1). exists r1. split; [exact Hr1|]. split; [exact S1|]. split; [exact N1|].
      intros k w v Hc. destruct (C1 _ _ _ Hc) as [X|W]; [now left|right]. eapply wb_cell_weaken; [exact W|apply rshape_refl]. }
    destruct (vr_kind xr) as [cid fl| |owner|s|] eqn:KX; try discriminate.
    + (* [comment removed for export] *)
      destruct (resolve_base isv_call2 A sigma (vr_base xr)) as [[b' c]|] eqn:RS; [|discriminate].
      destruct (rgn_get rg b') as [pr|] eqn:Gpr; [|discriminate].
      destruct (rgn_get_in _ _ _ Gpr) as [Hpr Bpr].
      assert (KK : match vr_kind pr with RK_fake _ _ | RK_arg => True | _ => False end /\ wb_fits xr pr c = true
                   /\ write_back_args A (rgn_upd rg (set_cells pr (set_exit_rcells (vr_cells pr) sigma c (vr_cells xr)))) sigma t = Some rg').
      { destruct (vr_kind pr); try discriminate; (destruct (wb_fits xr pr c); [auto|discriminate]). }
      destruct KK as (KP & WF & H'). destruct (wb_fits_spec _ _ _ WF) as (F1 & F2 & F3 & F4 & F5 & F6).
      eapply STEP; [exact Hpr| |exact H']. intros k w v Hc. apply set_exit_rcells_in in Hc as [Hc|(off & v0 & e' & A1 & A2 & A3 & A4)]; [left; left; exact Hc|right].
      destruct (F6 _ _ _ A1) as (Y1 & Y2 & Y3).
      exists xr, c, off, w, v0. split; [now left|]. split; [exact A1|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|].
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [lia|]. split; [lia|]. split; [exact Y2|].
      left. split; [exact KX|]. split; [exact A2|]. split; [reflexivity|]. split; [rewrite Bpr; exact RS|]. split; [exact KP|]. exists e'. auto.
    + (* [comment removed for export] *)
      destruct (Pos.eqb_spec s SP0) as [->|NS]; [|exact (SKIP H)].
      destruct (rgn_shadow_of rg SP0) as [pr|] eqn:Gpr; [|exact (SKIP H)].
      destruct (rgn_shadow_of_in _ _ _ Gpr) as [Hpr Kpr].
      destruct (wb_fits xr pr 0) eqn:WF; [|discriminate]. destruct (wb_fits_spec _ _ _ WF) as (F1 & F2 & F3 & F4 & F5 & F6).
      assert (ISH : is_shadow pr = true) by (unfold is_shadow; rewrite Kpr; reflexivity).
      eapply STEP; [exact Hpr| |exact H]. rewrite ISH. intros k w v Hc.
      apply set_exit_shcells_in in Hc as [Hc|(e & off0 & w0 & A1 & A2 & A3 & A4 & A5 & A6)]; [left; exact Hc|right].
      destruct (F6 _ _ _ A1) as (Y1 & Y2 & Y3).
      exists xr, 0, off0, w0, (Some e). split; [now left|]. split; [exact A1|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|].
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [lia|]. split; [lia|].
      split; [destruct A6 as [E|W]; [injection E as -> ->; exact Y2|exact W]|].
      right. split; [exact KX|]. split; [exact Kpr|]. split; [reflexivity|]. exists e. auto.
    + (* [comment removed for export] *) exact (SKIP H).
Qed.

Lemma set_exit_slots2_t_in sigma spoff : forall l rp s x, In x (set_exit_slots2_t rp s sigma spoff l) ->
  In x (rev_append rp s) \/ exists v0 e, In (fst x, (fst (snd x), v0)) l /\ spoff <= fst x /\ osubst2_v sigma v0 = Some e /\ snd (snd x) = Some e.
Proof.
  induction l as [|[off [w v]] t IH]; intros rp s [k [w' v']] H; cbn [set_exit_slots2_t] in H; [auto|].
  destruct (Z.leb_spec spoff off).
  - destruct (cm_skip rp s off) as [rp1 s1] eqn:SK.
    destruct (IH _ _ _ H) as [H1|(v0 & e & A1 & A2 & A3 & A4)].
    + apply in_rev_append_iff in H1 as [H1|H1].
      * left. apply (cm_skip_in _ _ _ _ _ SK). apply in_rev_append_iff. left. exact H1.
      * destruct (osubst2_v sigma v) as [e'|] eqn:Ho.
        -- apply cm_set_in in H1 as [H1|H1].
           ++ inversion H1; subst. right. exists v, e'. simpl. auto.
           ++ left. apply (cm_skip_in _ _ _ _ _ SK). apply in_rev_append_iff. right. eapply cm_kill_s_sub; eauto.
        -- left. apply (cm_skip_in _ _ _ _ _ SK). apply in_rev_append_iff. right. eapply cm_kill_s_sub; eauto.
    + right. exists v0, e. simpl in *. auto 10.
  - destruct (IH _ _ _ H) as [H1|(v0 & e & A1 & A2 & A3 & A4)]; [auto|]. right. exists v0, e. simpl in *. auto 10.
Qed.

Lemma set_exit_slots2_in sigma spoff : forall l sl x, In x (set_exit_slots2 sl sigma spoff l) ->
  In x sl \/ exists v0 e, In (fst x, (fst (snd x), v0)) l /\ spoff <= fst x /\ osubst2_v sigma v0 = Some e /\ snd (snd x) = Some e.
Proof. intros l sl x H. exact (set_exit_slots2_t_in sigma spoff l [] sl x H). Qed.

Lemma set_exit_globs2_in sigma : forall l gl x, In x (set_exit_globs2 gl sigma l) ->
  In x gl \/ exists v0, In (fst x, (fst (snd x), v0)) l /\ snd (snd x) = osubst2_v sigma v0.
Proof.
  induction l as [|[a [w v]] t IH]; intros gl [k [w' v']] H; simpl in *; [auto|].
  destruct (IH _ _ H) as [H1|(v0 & A1 & A2)].
  - apply cm_set_in in H1 as [H1|H1].
    + inversion H1; subst. right. exists v. simpl. auto.
    + left. eapply cm_kill_sub; eauto.
  - right. exists v0. simpl in *. auto.
Qed.

Lemma set_exit_divdefs_get sigma : forall l dd q x m, pm_get q (set_exit_divdefs dd sigma l) = Some (x, m) ->
  pm_get q dd = Some (x, m)
  \/ exists q0 x0, In (q0, (x0, m)) l /\ isv_join2 q0 = true /\ sym_image sigma q0 = Some q /\ osubst2 sigma x0 = Some x.
Proof.
  induction l as [|[q0 [x0 m0]] t IH]; intros dd q x m H; cbn [set_exit_divdefs] in H; [auto|].
  destruct (IH _ _ _ _ H) as [H1|(q1 & x1 & A1 & A2 & A3 & A4)]; [|right; exists q1, x1; split; [now right|auto]].
  destruct (isv_join2 q0) eqn:J; [|left; exact H1].
  destruct (sym_image sigma q0) as [q'|] eqn:SI; [|left; exact H1].
  destruct (osubst2 sigma x0) as [x'|] eqn:OS; [|left; exact H1].
  rewrite pm_get_set in H1. destruct (Pos.eqb_spec q q') as [->|NE]; [|left; exact H1].
  injection H1 as <- <-. right. exists q0, x0. split; [now left|auto].
Qed.

Lemma in_CALLER_SAVED_dec2 (z : Z) : 0 < z < 32 ->
  In z CALLER_SAVED \/ (z = 2 \/ z = 3 \/ z = 4 \/ In z (map fst sreg_idx)).
Proof.
  intros Hz. unfold CALLER_SAVED, sreg_idx. simpl.
  assert (H : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13
              \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24
              \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29 \/ z = 30 \/ z = 31) by lia.
  repeat (destruct H as [H|H]; [subst; tauto|]). subst; tauto.
Qed.

Lemma fetch_word_even2 SEGS pc w : fetch_word SEGS pc = Some w -> bv_unsigned pc mod 2 = 0.
Proof.
  unfold fetch_word. destruct (Z.eqb_spec (bv_unsigned pc mod 2) 0); simpl; [auto|discriminate].
Qed.

(* [comment removed for export] *)
Section Call2x.
  Variable SEGS : list Segment.
  Variable G : genv2.
  Variable rom : word -> option byte.
  Variable done : list vunit2.
  Variable U : vunit2.
  Variable E : venv2.
  Variables mem0 mem_e : word -> option byte.

  Let D := mk_denv2 G done U.
  Let P := unit_params2 G U.
  Let G1 := genv1_of G.
  Local Notation gammaP := (gamma2 SEGS P E mem0).
  Local Notation gammaPE := (gammaE SEGS G U E mem0 mem_e).

  Hypothesis DONE : Forall (unit_okS2 SEGS G rom) done.
  Hypothesis PO0 : params_ok2 SEGS (ge2_P0 G).
  Hypothesis PO : params_ok2 SEGS P.
  Hypothesis STATIC : unit_static_ok2 G P U = None.
  Hypothesis VSTEP2 : forall A i succs nu regs mem (pc : word) w,
    vstep2 P A i = VR2_next succs ->
    gammaP A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.

  (* [comment removed for export] *)
  Lemma materialize2_sound A nu regs mem :
    gammaP A nu regs mem ->
    exists nu1, gammaP (materialize2 A) nu1 regs mem /\ ext (vs2_next A) nu nu1
                /\ (vs2_next A <= vs2_next (materialize2 A))%positive
                /\ flags_step P E A (materialize2 A) nu nu1 mem mem.
  Proof using G1 PO.
    intros HG.
    destruct (materialize_sound SEGS G1 (u1 U) (ev1 E) (zpatch P E mem0 mem) (v1 A) nu regs mem sreg_idx
                sreg_idx_range (gamma2_v1 _ _ _ _ _ _ _ _ HG))
      as (nu1 & G1' & X1 & L1).
    destruct (gamma2_lift SEGS P E mem0 PO A (materialize (v1 A) sreg_idx) nu nu1 regs regs mem mem HG G1' X1 L1
                (frame_mod_refl _ _)) as (HG1 & _ & FL1).
    { apply globs_in_fcells_sound. rewrite (globs_in_fcells_same P A); [exact (gamma2_globs_in_fcells _ _ _ _ _ _ _ _ HG)|].
      cbn [v1 with_v1]. apply vs_globs_materialize. }
    { left; reflexivity. }
    exists nu1. split; [exact HG1|]. split; [exact X1|]. split; [exact L1|exact FL1].
  Qed.

  (* [comment removed for export] *)
  Lemma PO1 : params_ok SEGS (unit_params G1 (u1 U)).
  Proof using PO. exact (proj1 PO). Qed.

  Lemma VSTEP1 (m0 : word -> option byte) : forall A i succs nu regs mem (pc : word) w,
    vstep (unit_params G1 (u1 U)) A i = VR_next succs ->
    gamma SEGS (unit_params G1 (u1 U)) (ev1 E) m0 A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    step_post SEGS (unit_params G1 (u1 U)) (ev1 E) m0 A nu succs regs mem pc rom.
  Proof using PO.
    intros A i succs nu regs mem pc w Hv HG Hpc Hf He Hd.
    exact (vstep_sound SEGS (unit_params G1 (u1 U)) (ev1 E) m0 PO1 A nu regs mem pc rom w i succs HG Hpc Hf He Hd Hv).
  Qed.

  Lemma PV_ok2 V : In V done -> params_ok2 SEGS (unit_params2 G V).
  Proof using DONE PO0. intros HV. apply (unit_params2_ok SEGS G V PO0). rewrite Forall_forall in DONE. exact (proj1 (DONE V HV)). Qed.

  (* [comment removed for export] *)
  Let D1 := mk_denv G1 (map u1 done) (u1 U).

  Lemma footprint_ok2_v1 A0 sigma V spoff :
    footprint_ok2 D A0 sigma V spoff = true ->
    footprint_ok D1 (u1 V) spoff = true /\ forallb (wrgn_admissible D A0 sigma) (u2_wrgn V) = true.
  Proof using G1 P done.
    unfold footprint_ok2, footprint_ok. change (de2_U D) with U. change (de2_P D) with P. change (de_U D1) with (u1 U).
    change (de_P D1) with (p1 P).
    intros H. apply andb_prop in H as [H W]. split; [exact H|exact W].
  Qed.

  (* [comment removed for export] *)
  Definition callee_env2 (npc : Z) (nuV : val) (L : list (Z * Z)) : venv2 :=
    mkEnv2 (callee_env (ev1 E) npc nuV) (e_fs E) (map (fun i => nuV (ASYM2 (Z.of_nat i))) (seq 0 8)) (e_live E ++ L).

  Lemma flags_step_rgn A A1 A2 nu nu' mem mem' :
    vs_rgn A1 = vs_rgn A2 ->
    flags_step P E A A1 nu nu' mem mem' -> flags_step P E A A2 nu nu' mem mem'.
  Proof using G U. intros ER H. unfold flags_step, own_flags in *. rewrite <- ER. exact H. Qed.

  (* [comment removed for export] *)
  Lemma comp_sound Ax nu regs mem bc bc8 :
    gammaP Ax nu regs mem -> comp Ax bc = Some bc8 -> nu bc8 = nu bc / 8.
  Proof using G U.
    intros HG HC. pose proof HG as (_ & _ & _ & HF2 & HDD & _).
    unfold comp, env_comp in HC.
    destruct (Pos.eqb_spec bc SP0) as [->|N1].
    { injection HC as <-. rewrite (HF2 SP8 (e_sp0 (ev1 E) / 8) eq_refl), (HF2 SP0 (e_sp0 (ev1 E)) eq_refl). reflexivity. }
    destruct (Pos.eqb_spec bc DATA) as [->|N2].
    { injection HC as <-. rewrite (HF2 DATA8 (e_data (ev1 E) / 8) eq_refl), (HF2 DATA (e_data (ev1 E)) eq_refl). reflexivity. }
    destruct (Pos.eqb_spec bc FSB) as [->|N3].
    { injection HC as <-. rewrite (HF2 FS8 (e_fs E / 8) eq_refl), (HF2 FSB (e_fs E) eq_refl). reflexivity. }
    match type of HC with (match ?cand with _ => _ end) = _ => destruct cand as [c|]; [|discriminate] end.
    unfold divdef_is in HC. destruct (pm_get c (vs_divdef Ax)) as [[x' m']|] eqn:Gd; [|discriminate].
    destruct (Z.eqb_spec m' 8) as [->|]; [|discriminate]. destruct (lin_eqb x' (lsym bc)) eqn:LE; [|discriminate]. cbn [andb] in HC.
    injection HC as <-. destruct (HDD _ _ _ Gd) as [_ X]. rewrite X, (lin_eqb_sound nu _ _ LE), eval_lsym. reflexivity.
  Qed.

  Lemma base_res8_sound Ax nu regs mem bc rc :
    gammaP Ax nu regs mem -> base_res8 Ax bc = Some rc -> 0 <= rc < 8 /\ nu bc mod 8 = rc.
  Proof using G U.
    intros HG HB. pose proof (gamma2_v1 _ _ _ _ _ _ _ _ HG) as (_ & _ & _ & HS & _).
    unfold base_res8 in HB. destruct (pm_get bc (scong (vs_store (v1 Ax)))) as [[m r]|] eqn:Gc; [|discriminate].
    destruct (Z.eqb_spec m 0) as [|Hm]; [discriminate|]. destruct (Z.eqb_spec (m mod 8) 0) as [Hm8|]; [|discriminate]. cbn [negb andb] in HB.
    injection HB as <-. pose proof (sat_cong _ _ HS _ _ _ Gc) as [k Hk].
    split; [apply Z.mod_pos_bound; lia|].
    apply Z.mod_divide in Hm8 as [m' ->]; [|lia].
    replace (nu bc) with (r + (k * m') * 8) by lia. rewrite Z.mod_add; [reflexivity|lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition am_is (A Am : vstate2) : Prop := Am = materialize2 A.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Callee2.
    Variable V : vunit2.
    Hypothesis VIN : In V done.
    Let PV := unit_params2 G V.

    Lemma V_ok2 : unit_okS2 SEGS G rom V.
    Proof using DONE VIN. rewrite Forall_forall in DONE. apply DONE. exact VIN. Qed.

    Lemma V_static2 :
      cstate2_ok PV (u2_pre V) = true /\ cstate2_iface_b (u2_pre V) = true /\ wrgn_ok V (u2_pre V) = true
      /\ pre_canonical2 G PV V = true
      /\ (forall X, In X (u2_exits V) -> cstate2_ok PV X = true /\ cstate2_iface_b X = true /\ wrgn_ok V X = true)
      /\ mod8_ok PV V = true.
    Proof using DONE VIN.
      destruct V_ok2 as [ST _]. unfold unit_static_ok2 in ST. fold PV in ST.
      destruct (cstate2_ok PV (u2_pre V) && cstate2_iface_b (u2_pre V) && wrgn_ok V (u2_pre V)) eqn:C0; [|discriminate].
      destruct (pre_canonical2 G PV V) eqn:PC; [|discriminate].
      destruct (forallb (fun c => pc_ok (cut2_pc c) && forallb (fun cs => cstate2_ok PV cs && wrgn_ok V cs) (cut2_states c)) (u2_cuts V)); [|discriminate].
      destruct (pc_ok (u_entry (u1 V))); [|discriminate].
      destruct (forallb (fun cs => cstate2_ok PV cs && cstate2_iface_b cs && wrgn_ok V cs) (u2_exits V)) eqn:EX; [|discriminate].
      cbn [negb] in ST.
      destruct (ge2_ranks G && negb _); [discriminate|].
      destruct (forallb _ (u_wstack (u1 V))); [|discriminate].
      destruct (forallb _ (vp_wcells (p1 PV))); [|discriminate].
      destruct (Z.ltb 0 (u_sp (u1 V)) || _); [discriminate|].
      destruct (mod8_ok PV V) eqn:M8; [|discriminate].
      apply andb_prop in C0 as [C0 C3]. apply andb_prop in C0 as [C1 C2].
      split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [reflexivity|]. split; [|reflexivity].
      intros X HX. rewrite forallb_forall in EX. specialize (EX _ HX). apply andb_prop in EX as [EX E3]. apply andb_prop in EX as [E1 E2]. auto.
    Qed.

    (* [comment removed for export] *)
    Lemma load_cstate2_PV X pc ctx : load_cstate2 P X pc ctx = load_cstate2 PV X pc ctx.
    Proof using G U V. reflexivity. Qed.

    (* [comment removed for export] *)
    Variables (A Am : vstate2) (spoff npc : Z) (sigma0 sigma : pmap lin) (skip8 : list sym).
    Hypothesis EAm : am_is A Am.
    Let A0 := set_reg2 Am 1 (Some (lconst npc)).
    Let S := load_cstate2 P (u2_pre V) (u_entry (u1 V)) [].
    Let sigma00 := sigma_sregs (v1 A0) sreg_idx (pm_set RA (lconst npc) pm_empty).
    Hypothesis PRE : prebind_args A0 (cs_rgn (u2_pre V)) (cs_divdef (u2_pre V)) sigma00 = Some (sigma0, skip8).
    Hypothesis MATCH : match_state2 isv_call2 is_sreg_key true MM_call sigma0 (drop_divdefs skip8 S) A0 = MOk sigma.
    Hypothesis NPC : 0 <= npc < 2 ^ 64.
    Hypothesis FP : footprint_ok2 D A0 sigma V spoff = true.
    Hypothesis FDEP : vp_fdepth P + Z.of_nat (length (fakes_of (vs_rgn A0))) <= u2_fdepth V.

    (* [comment removed for export] *)
    Definition fake_slots_of (nu : val) (mem : word -> option byte) (L : list (Z * Z)) : Prop :=
      Forall2 (fun r cp => exists fl, vr_kind r = RK_fake (fst cp) fl /\ 0 <= fst cp <= 4 /\ 0 <= snd cp < fs_nframes (fst cp)
                              /\ rbase nu r = frame_addr (e_fs E) (fst cp) (snd cp)
                              /\ nu fl = flag_addr (e_fs E) (fst cp) (snd cp)
                              /\ (exists b, rdn SEGS mem (wordZ (nu fl)) 1 = Some [b] /\ bv_unsigned b = 1)
                              /\ ~ In cp (e_live E) /\ vr_lo r = 0 /\ vr_hi r = fake_size (fst cp) /\ vp_fs P <> None)
              (fakes_of (vs_rgn A0)) L.

    Lemma A0_sregs2 r i : In (r, i) sreg_idx -> exists e, get_reg (v1 A0) r = Some e /\ pm_get (SREG i) sigma00 = Some e.
    Proof using EAm NPC.
      intros Hin. pose proof (sreg_idx_range _ _ Hin) as Hr.
      assert (Hr1 : r <> 1).
      { unfold sreg_idx in Hin. simpl in Hin. repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; lia|]). destruct Hin. }
      destruct (materialize_regs_some sreg_idx (v1 A) r sreg_idx_range) as [e He]; [left; apply in_map_iff; exists (r, i); auto|lia|].
      assert (He' : get_reg (v1 Am) r = Some e) by (pose proof EAm as E0; unfold am_is in E0; rewrite E0; unfold materialize2, with_v1; cbn [v1]; exact He).
      exists e. split.
      - unfold A0, set_reg2, with_v1. cbn [v1]. rewrite get_reg_set_reg_other; auto; lia.
      - unfold sigma00. eapply sigma_sregs_in; [apply sreg_idx_distinct|exact Hin|].
        unfold A0, set_reg2, with_v1. cbn [v1]. rewrite get_reg_set_reg_other; auto; lia.
    Qed.

    Lemma sigma00_fixed s : isv_call2 s = false -> pm_get s sigma00 = None.
    Proof using A0.
      intros Hs. unfold sigma00. rewrite sigma_sregs_other.
      - rewrite pm_get_set_other; [apply pm_get_empty|]. intros X. subst. cbv in Hs. discriminate.
      - intros r i Hin. unfold sreg_idx in Hin. simpl in Hin. intros X. subst s.
        repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; cbv in Hs; discriminate|]). destruct Hin.
    Qed.

    Lemma sigma00_RA : pm_get RA sigma00 = Some (lconst npc).
    Proof using A0.
      unfold sigma00. rewrite sigma_sregs_other; [apply pm_get_set_same|].
      intros r i Hin. unfold sreg_idx in Hin. simpl in Hin.
      repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; discriminate|]). destruct Hin.
    Qed.

    Lemma sigma00_binds_only : binds_only isv_call2 pm_empty sigma00.
    Proof using A0.
      intros k e Hk. destruct (isv_call2 k) eqn:IS; [now right|]. rewrite (sigma00_fixed _ IS) in Hk. discriminate.
    Qed.

    (* [comment removed for export] *)
    Lemma match_call_inv :
      exists sigma1 defer1,
        match_regions isv_call2 true MM_call (drop_divdefs skip8 S) A0 (sigma0, []) = inl (sigma1, defer1)
        /\ match_state_f isv_call2 is_sreg_key true sigma1 (v1 S) (v1 A0) = MOk sigma
        /\ check_defer sigma defer1 = true
        /\ match_divdefs sigma (drop_divdefs skip8 S) A0 = true.
    Proof using MATCH.
      pose proof MATCH as M. unfold match_state2 in M.
      destruct (match_regions isv_call2 true MM_call (drop_divdefs skip8 S) A0 (sigma0, [])) as [[sigma1 defer1]|] eqn:MR; [|discriminate].
      change (v1 (drop_divdefs skip8 S)) with (v1 S) in M.
      destruct (match_state_f isv_call2 is_sreg_key true sigma1 (v1 S) (v1 A0)) as [sg|] eqn:M1; [|discriminate].
      rewrite check_defer_f_eq in M.   (* [comment removed for export] *)
      destruct (check_defer sg defer1) eqn:CD; [|discriminate].
      destruct (match_divdefs sg (drop_divdefs skip8 S) A0) eqn:MD; [|discriminate].
      cbn [negb] in M. injection M as ->. exists sigma1, defer1. auto.
    Qed.

    (* [comment removed for export] *)
    Lemma fake_slots_exist nu1 regs1 mem1 : gammaP A0 nu1 regs1 mem1 -> exists L, fake_slots_of nu1 mem1 L.
    Proof using .
      intros HGm. pose proof HGm as (_ & _ & _ & _ & _ & HRG & _).
      apply list_choice. intros r Hr. apply fakes_of_in in Hr as [Hr (cid & fl & K)].
      pose proof (HRG _ Hr) as (_ & _ & _ & _ & _ & _ & _ & KO). unfold kind_ok in KO. rewrite K in KO.
      destruct KO as (F1 & F2 & F3 & F4 & _ & pos & P1 & P2 & P3 & P4 & P5 & _).
      exists (cid, pos), fl. cbn [fst snd]. repeat (split; [first [assumption|reflexivity]|]). exact F1.
    Qed.

    (* [comment removed for export] *)
    Lemma fake_slots_nodup nu mem L :
      fake_slots_of nu mem L -> live_ok nu A0 -> bases_distinct (map vr_base (fakes_of (vs_rgn A0))) = true -> List.NoDup L.
    Proof using NPC.
      intros HL HLV BD. pose proof (bases_distinct_nodup _ BD) as ND. destruct HLV as (_ & _ & LV3 & _).
      apply List.NoDup_nth_error. intros i j Hi EQ.
      destruct (nth_error L i) as [cp|] eqn:Ni; [|exfalso; apply nth_error_None in Ni; lia].
      symmetry in EQ.
      destruct (Forall2_nth_r _ _ _ _ _ HL Ni) as (ri & Nri & fi & Ki & _ & _ & Bi & _).
      destruct (Forall2_nth_r _ _ _ _ _ HL EQ) as (rj & Nrj & fj & Kj & _ & _ & Bj & _).
      destruct (PeanoNat.Nat.eq_dec i j) as [|NE]; [assumption|]. exfalso.
      pose proof (nodup_map_nth vr_base _ _ _ _ _ ND Nri Nrj NE) as NB.
      destruct (fakes_of_in _ _ (nth_error_In _ _ Nri)) as [Iri _]. destruct (fakes_of_in _ _ (nth_error_In _ _ Nrj)) as [Irj _].
      specialize (LV3 ri rj Iri Irj). rewrite Ki, Kj in LV3. apply (LV3 NB). rewrite Bi, Bj. reflexivity.
    Qed.

    Lemma callee_entry2 nu1 regs1 mem1 :
      gammaP A0 nu1 regs1 mem1 ->
      let nuV := vsubst nu1 sigma in
      exists L, fake_slots_of nu1 mem1 L
        /\ gamma2 SEGS PV (callee_env2 npc nuV L) mem0 S nuV regs1 mem1
        /\ sub_sigma sigma00 sigma /\ binds_only isv_call2 sigma00 sigma.
    Proof using D1 DONE EAm FDEP FP MATCH NPC PO PRE VIN.
      intros HGm. cbv zeta.
      pose proof HGm as (HV1 & HE2 & HMC2 & HF2 & HDD & HRG & HLV & HB2 & HGL & HFLI & HMEM).
      pose proof HV1 as (HE & HMC & HF & HS & HC & HMo & HV & HR & HSl & HGl & HN & HB).
      destruct V_static2 as (ST1 & ST2 & ST3 & PC2 & _ & M8).
      destruct (cstate2_ok_parts _ _ ST1) as (ST1a & WF & ST1c). apply andb_prop in ST1c as [GF SD].
      destruct (cstate2_wf_parts _ WF) as (WF1 & J0 & WBW & WRB & WBD & WDD & WLB & WLM & WSK).
      destruct (load_cstate2_v1_facts PV (u2_pre V) (u_entry (u1 V)) [] ST1) as (WS & WG & BEL & _).
      destruct (fake_slots_exist nu1 regs1 mem1 HGm) as [L HL]. exists L. split; [exact HL|].
      set (EV := callee_env2 npc (vsubst nu1 sigma) L).
      (* [comment removed for export] *)
      destruct (prebind_args_spec _ _ _ _ _ _ PRE) as (U0 & O0 & Q0).
      destruct match_call_inv as (sigma1 & defer1 & MR & M1 & CD & MD).
      destruct (match_regions_spec_call _ _ _ _ _ _ _ MR (O0 _ sigma00_binds_only)) as (NOFAKES & BD & U1 & BO1 & OF).
      destruct (match_state_f_sound SEGS (p1 P) (p1 PV) (ev1 E) (ev1 EV) eq_refl eq_refl eq_refl
                  isv_call2 is_sreg_key true sigma1 (v1 S) (v1 A0) sigma nu1 regs1 mem1
                  M1 HS HC HMo HV HR HSl HGl HN WS WG) as (Sub & BO & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
      pose proof (check_defer_sound _ _ CD) as DEF.
      assert (SUB0 : sub_sigma sigma00 sigma) by (eapply sub_sigma_trans; [exact U0|eapply sub_sigma_trans; [exact U1|exact Sub]]).
      assert (BOF : binds_only isv_call2 pm_empty sigma).
      { eapply binds_only_trans; [exact BO1|exact BO]. }
      assert (BO0 : binds_only isv_call2 sigma00 sigma).
      { intros k e Hk. destruct (BOF _ _ Hk) as [X|X]; [rewrite pm_get_empty in X; discriminate|right; exact X]. }
      split; [|split; [exact SUB0|exact BO0]].
      set (nuV := vsubst nu1 sigma) in *.
      assert (UNB : forall s, isv_call2 s = false -> nuV s = nu1 s).
      { intros s Hs. unfold nuV, vsubst. destruct (pm_get s sigma) as [e|] eqn:Gs; [|reflexivity].
        destruct (BOF _ _ Gs) as [Hg|Hv]; [rewrite pm_get_empty in Hg; discriminate|congruence]. }
      destruct (zpatch_env_indep P E EV (PO2_zsyms SEGS P PO) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as (ZRW & ZREG & ZP).
      assert (ZRW' : forall a, in_rw_zones PV EV a = in_rw_zones P E a) by (intros a; rewrite ZRW; reflexivity).
      assert (ZP' : forall m0 m a, zpatch PV EV m0 m a = zpatch P E m0 m a) by (intros m0 m a; rewrite ZP; reflexivity).
      assert (ZANY : forall a, in_any_zone PV EV a = in_any_zone P E a).
      { intros a. unfold in_any_zone. change (vp_fzones PV) with (vp_fzones P).
        pose proof (PO2_zsyms SEGS P PO) as ZS. rewrite forallb_forall in ZS.
        induction (vp_fzones P) as [|z t IH]; [reflexivity|]. cbn [existsb].
        rewrite IH by (intros z' Hz'; apply ZS; right; exact Hz'). f_equal.
        unfold in_zoneb. destruct (zone_env_indep EV E z (ZS z (or_introl eq_refl)) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [-> ->]. reflexivity. }
      split.
      { (* [comment removed for export] *)
        split.
        { (* [comment removed for export] *) destruct HE as (E1&E2'&E3&E4&E5&E6&E7&E8&E9&E10&E11). unfold env_ok. cbn [ev1 EV callee_env2 callee_env e_sp0 e_data e_size e_ra e_tp e_gp e_sregs].
          change (vp_splo (p1 PV)) with (vp_splo (p1 P)). change (vp_sphi (p1 PV)) with (vp_sphi (p1 P)).
          change (vp_nmax (p1 PV)) with (vp_nmax (p1 P)). change (vp_frame (p1 PV)) with (vp_frame (p1 P)).
          repeat split; auto; try lia. }
        split.
        { (* [comment removed for export] *) destruct HMC as (M1' & M2 & M3 & M4). split; [exact M1'|]. split; [exact M2|]. split; [exact M3|].
          eapply frame_mod_mem0_ext; [|exact M4]. intros a. symmetry. apply ZP'. }
        split.
        { (* [comment removed for export] *)
          intros s z Hfz. apply fix_val_callee in Hfz.
          destruct Hfz as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|(i & Hi & -> & ->)]]]]]];
            try (rewrite UNB by reflexivity; apply HF; reflexivity).
          - unfold nuV, vsubst. rewrite (SUB0 _ _ sigma00_RA). apply eval_lconst.
          - reflexivity. }
        split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
        split.
        { (* [comment removed for export] *)
          intros r e Hr0 Hg. destruct (is_sreg_key (reg_key (bv_unsigned r))) eqn:SK; [|apply S5; auto].
          destruct (is_sreg_key_spec _ SK) as (ri & i & Hin & Hk).
          pose proof (sreg_idx_range _ _ Hin) as Hri.
          assert (Hrz : bv_unsigned r = ri).
          { unfold reg_key, zkey in Hk. pose proof (bv_unsigned_in_range 5 r). lia. }
          destruct (A0_sregs2 _ _ Hin) as (ei & Gei & Sei).
          unfold pre_canonical2 in PC2. apply andb_prop in PC2 as [PC2 _]. apply andb_prop in PC2 as [PC2 _].
          apply andb_prop in PC2 as [_ PC2].
          unfold sregs_intact in PC2. rewrite forallb_forall in PC2. specialize (PC2 _ Hin). cbn [fst snd] in PC2.
          unfold absval_eqb, get_reg in PC2. change (load_cstate2 PV (u2_pre V) (u_entry (u1 V)) []) with S in PC2.
          destruct (Z.eqb_spec ri 0); [lia|].
          rewrite <- Hrz in PC2. rewrite Hg in PC2. apply lin_eqb_eq in PC2. subst e.
          rewrite eval_lsym. unfold nuV, vsubst. rewrite (SUB0 _ _ Sei).
          apply (HR r ei Hr0). unfold get_reg in Gei. rewrite Hrz. destruct (Z.eqb_spec ri 0); [lia|]. exact Gei. }
        split; [exact S6|]. split; [exact S7|]. split; [exact S8|exact BEL]. }
      (* [comment removed for export] *)
      pose proof (fake_slots_nodup _ _ _ HL HLV BD) as NDL.
      assert (LFACT : forall cp, In cp L -> 0 <= fst cp <= 4 /\ 0 <= snd cp < fs_nframes (fst cp) /\ ~ In cp (e_live E)
                                          /\ (exists b, rdn SEGS mem1 (wordZ (flag_addr (e_fs E) (fst cp) (snd cp))) 1 = Some [b] /\ bv_unsigned b = 1)
                                          /\ vp_fs P <> None).
      { intros cp Hcp. destruct (Forall2_In_r _ _ _ _ HL Hcp) as (r & Hr & fl & K & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
        rewrite <- C4. auto 10. }
      assert (ZLH : forall z, In z (vp_fzones P) -> zone_lo EV z = zone_lo E z /\ zone_hi EV z = zone_hi E z).
      { intros z Hz. pose proof (PO2_zsyms SEGS P PO) as ZS. rewrite forallb_forall in ZS.
        apply (zone_env_indep EV E z (ZS z Hz)); reflexivity. }
      pose proof HE2 as (HE1 & HD & HFS & HZ & HK).
      split.
      { (* [comment removed for export] *)
        split.
        { destruct HE as (E1&E2'&E3&E4&E5&E6&E7&E8&E9&E10&E11). unfold env_ok. cbn [ev1 EV callee_env2 callee_env e_sp0 e_data e_size e_ra e_tp e_gp e_sregs].
          change (vp_splo (p1 PV)) with (vp_splo (p1 P)). change (vp_sphi (p1 PV)) with (vp_sphi (p1 P)).
          change (vp_nmax (p1 PV)) with (vp_nmax (p1 P)). change (vp_frame (p1 PV)) with (vp_frame (p1 P)).
          repeat split; auto; try lia. }
        split.
        { destruct HD as (HD1 & HD2 & HD3 & HD4). split; [exact HD1|]. split; [exact HD2|]. split; [exact HD3|reflexivity]. }
        split.
        { (* [comment removed for export] *)
          unfold env_fs in HFS |- *. change (vp_fs PV) with (vp_fs P). change (vp_frame (p1 PV)) with (vp_frame (p1 P)).
          change (vp_datal PV) with (vp_datal P). change (vp_shoff PV) with (vp_shoff P).
          cbn [e_live e_fs ev1 EV callee_env2 callee_env e_sp0 e_data e_size].
          destruct (vp_fs P) as [[len ssl]|] eqn:EFS.
          - destruct HFS as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & REST).
            split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split.
            { apply Forall_app. split; [exact C6|]. apply Forall_forall. intros cp Hcp. destruct (LFACT _ Hcp) as (X1 & X2 & _). split; [exact X1|exact X2]. }
            split.
            { apply base.NoDup_ListNoDup. apply List.NoDup_app. 3:{ intros cp H1 H2. exact (proj1 (proj2 (proj2 (LFACT _ H2))) H1). }
              - apply base.NoDup_ListNoDup. exact C7.
              - exact NDL. }
            destruct REST as (R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16).
            split; [exact R8|]. split; [exact R9|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [|split; [exact R14|]].
            { intros HDL HSZ a Ha. rewrite ZRW'. exact (R13 HDL HSZ a Ha). }
            split; [|change (vp_imgend PV) with (vp_imgend P); exact R16].
            rewrite length_app, Nat2Z.inj_add, <- (Forall2_length HL). change (vp_fdepth PV) with (u2_fdepth V).
            clear - R15 FDEP. lia.
          - destruct HFS as [HL0 HF0]. split; [|exact HF0]. rewrite HL0. destruct L as [|cp t]; [reflexivity|].
            exfalso. destruct (LFACT cp (or_introl eq_refl)) as (_ & _ & _ & _ & X). exact (X eq_refl). }
        split.
        { (* [comment removed for export] *)
          destruct HZ as [Z1 Z2]. unfold env_zones. change (vp_fzones PV) with (vp_fzones P). change (vp_fcells (p1 PV)) with (vp_fcells (p1 P)).
          change (vp_pristine (p1 PV)) with (vp_pristine (p1 P)). change (vp_frame (p1 PV)) with (vp_frame (p1 P)).
          cbn [ev1 EV callee_env2 callee_env e_sp0 e_data e_size]. split.
          - intros z Hz. destruct (ZLH z Hz) as [X1 X2]. rewrite X1, X2. exact (Z1 z Hz).
          - intros z a Hz Ha. apply (Z2 z a Hz). unfold in_zone in Ha |- *. destruct (ZLH z Hz) as [X1 X2].
            rewrite X1, X2 in Ha. exact Ha. }
        { (* [comment removed for export] *)
          destruct HK as [K1 K2]. unfold env_kcells. change (vp_kcells PV) with (vp_kcells P). change (vp_kruns PV) with (vp_kruns P).
          change (vp_frame (p1 PV)) with (vp_frame (p1 P)). cbn [ev1 EV callee_env2 callee_env e_sp0]. split.
          - intros c x Hc Hx. rewrite ZRW'. exact (K1 c x Hc Hx).
          - intros c x Hc Hx. rewrite ZRW'. exact (K2 c x Hc Hx). } }
      split.
      { (* [comment removed for export] *)
        destruct HMC2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
        split; [exact Q1|]. split.
        { intros z a Hz Ha. apply (Q2 z a Hz). unfold in_zone in Ha |- *. destruct (ZLH z Hz) as [X1 X2]. rewrite X1, X2 in Ha. exact Ha. }
        split; [exact Q3|]. split; [|split; [|exact Q6]].
        { intros cp Hcp. cbn [e_live e_fs EV callee_env2] in Hcp |- *. apply in_app_iff in Hcp as [Hcp|Hcp]; [exact (Q4 cp Hcp)|].
          destruct (LFACT _ Hcp) as (_ & _ & _ & X & _). exact X. }
        { eapply (rtctx_ok_env SEGS P PV E EV); try reflexivity; [|exact Q5]. intros x. rewrite ZRW'. reflexivity. } }
      split.
      { (* [comment removed for export] *)
        assert (HFIX1 : gamma_fix (ev1 EV) nuV).
        { intros s z Hfz. apply fix_val_callee in Hfz.
          destruct Hfz as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|(i & Hi & -> & ->)]]]]]];
            try (rewrite UNB by reflexivity; apply HF; reflexivity).
          - unfold nuV, vsubst. rewrite (SUB0 _ _ sigma00_RA). apply eval_lconst.
          - reflexivity. }
        intros s z Hfz. unfold fix_val2 in Hfz. destruct (fix_val (ev1 EV) s) as [z0|] eqn:FV; [injection Hfz as <-; exact (HFIX1 _ _ FV)|].
        cbn [e_fs e_args ev1 EV callee_env2 callee_env e_sp0 e_data] in Hfz.
        destruct (Pos.eqb_spec s SP8) as [->|]; [injection Hfz as <-; rewrite UNB by reflexivity; exact (HF2 SP8 _ eq_refl)|].
        destruct (Pos.eqb_spec s DATA8) as [->|]; [injection Hfz as <-; rewrite UNB by reflexivity; exact (HF2 DATA8 _ eq_refl)|].
        destruct (Pos.eqb_spec s FSB) as [->|]; [injection Hfz as <-; rewrite UNB by reflexivity; exact (HF2 FSB _ eq_refl)|].
        destruct (Pos.eqb_spec s FS8) as [->|]; [injection Hfz as <-; rewrite UNB by reflexivity; exact (HF2 FS8 _ eq_refl)|].
        destruct (Pos.leb_spec 19 s); [|discriminate]. destruct (Pos.leb_spec s 26); [|discriminate]. cbn [andb] in Hfz.
        rewrite nth_error_map, nth_error_seq in Hfz.
        destruct (PeanoNat.Nat.ltb_spec (Pos.to_nat s - 19) 8); [|discriminate]. cbn in Hfz. injection Hfz as <-.
        f_equal. unfold ASYM2. lia. }
      split.
      { (* [comment removed for export] *)
        pose proof (match_divdefs_sound _ _ _ nu1 MD HDD) as GDV.
        intros q x m Hq.
        assert (Hin : In (q, (x, m)) (cs_divdef (u2_pre V))) by (apply pm_of_list_get_in; exact Hq).
        destruct (in_dec Pos.eq_dec q skip8) as [IN8|NIN8].
        - destruct (Q0 _ IN8) as (i & bc & c & bc8 & rc & e & Hi & -> & DDQ & GA & EVA & IB & CP & BR & G8).
          destruct (DDQ _ Hin eq_refl) as [X1 X2]. cbn [fst snd] in X1, X2. subst x m. split; [lia|].
          assert (U0S : sub_sigma sigma0 sigma) by (eapply sub_sigma_trans; [exact U1|exact Sub]).
          rewrite eval_lsym. unfold nuV, vsubst. rewrite (U0S _ _ G8), (U0S _ _ GA), eval_laddc, eval_lsym, EVA.
          rewrite (comp_sound _ _ _ _ _ _ HGm CP). destruct (base_res8_sound _ _ _ _ _ _ HGm BR) as [R1 R2].
          rewrite <- R2. rewrite <- (Z.div_add_l (nu1 bc / 8) 8 (c + nu1 bc mod 8)) by lia. f_equal.
          rewrite (Z.div_mod (nu1 bc) 8) at 3 by lia. lia.
        - apply (GDV q x m). cbn [vs_divdef drop_divdefs]. change (vs_divdef S) with (pm_of_list (cs_divdef (u2_pre V))) in Hq.
          clear - Hq NIN8. induction skip8 as [|q0 t IH]; cbn [fold_right]; [exact Hq|].
          rewrite pm_get_remove_other; [apply IH; intros X; apply NIN8; right; exact X|]. intros ->. apply NIN8. now left. }
      pose proof (load_bases_nodup P (u2_pre V) (u_entry (u1 V)) [] WF) as NDB. change (vs_rgn (load_cstate2 P _ _ _)) with (vs_rgn S) in NDB.
      split.
      2:{ split.
          { (* [comment removed for export] *)
            unfold cstate2_iface_b in ST2. apply andb_prop in ST2 as [ST2 NF]. apply andb_prop in ST2 as [_ LV0].
            assert (ELV : vs_live S = []) by (change (vs_live S) with (cs_live (u2_pre V)); destruct (cs_live (u2_pre V)); [reflexivity|discriminate]).
            assert (NOF : forall r cid fl, In r (vs_rgn S) -> vr_kind r = RK_fake cid fl -> False).
            { intros r cid fl Hr K. pose proof (in_fakes_of _ _ _ _ Hr K) as X. change (vs_rgn S) with (vs_rgn (drop_divdefs skip8 S)) in X.
              rewrite NOFAKES in X. exact X. }
            split.
            { intros s. rewrite ELV. split; [intros []|]. intros (r & Hr & _ & K). destruct (vr_kind r) eqn:Kr; try contradiction. exact (NOF _ _ _ Hr Kr). }
            split; [rewrite ELV; constructor|]. split; [|exact NDB].
            intros r1 r2 Hr1 _. destruct (vr_kind r1) eqn:K1; try exact I. exfalso. exact (NOF _ _ _ Hr1 K1). }
          split; [|split; [exact (load_globs_ok2 PV _ _ _ GF)|split; [|intros ma mn mv []]]].
          2:{ (* [comment removed for export] *)
              intros NZ c p Hc Hp NL _. cbn [e_live e_fs EV callee_env2] in NL |- *.
              apply (HFLI NZ c p Hc Hp); [intros IN; apply NL; apply in_app_iff; left; exact IN|].
              intros OWN. rewrite own_flags_fakes in OWN. apply in_map_iff in OWN as (r & Er & Hr).
              destruct (Forall2_In_l _ _ _ _ HL Hr) as (cp & Hcp & fl & Kc & C1 & C2 & C3 & C4 & C5 & _).
              rewrite Kc in Er. rewrite C4 in Er.
              destruct (flag_addr_inj _ _ _ _ _ C1 C2 Hc Hp Er) as [E5 E6].
              apply NL. apply in_app_iff. right. destruct cp as [c' p']. cbn [fst snd] in E5, E6. subst. exact Hcp. }
          (* [comment removed for export] *)
          split; [change (vs_next (v1 S)) with (cs_next (c1 (u2_pre V))); unfold LAST_FIXED2, FIRST_FRESH2 in *; lia|].
          split.
          { intros r Hr. change (vs_next (v1 S)) with (cs_next (c1 (u2_pre V))).
            apply (load_regions_in P) in Hr as [[t [Ht ->]]|Hstd].
            - destruct (WBW _ Ht) as [BLW _]. destruct (srgn_below_facts _ _ BLW) as (Y1 & Y2 & Y3).
              split; [exact Y1|]. split.
              + intros k w e Hin. destruct (vregion_of_cells _ _ _ _ Hin) as [e' [E' Hin']]. injection E' as ->. exact (Y3 _ _ _ Hin').
              + cbn [vregion_of vr_kind]. destruct (sr_kind t) as [cid fl| | |] eqn:K; cbn [rkind_of]; try exact I.
                apply Y2. rewrite ?K. cbn. now left.
            - apply std_regions_cases in Hstd as [[-> _]|[-> _]]; cbn; (split; [unfold DATA8, FSB, FIRST_FRESH2 in *; lia|]); split; try exact I; intros ? ? ? [].
          }
          split; [intros x Hx; change (vs_next (v1 S)) with (cs_next (c1 (u2_pre V))); exact (WLB _ Hx)|].
          split; [|intros ma mn mv []].
          intros q x m Hq. change (vs_next (v1 S)) with (cs_next (c1 (u2_pre V))). change (vs_divdef S) with (pm_of_list (cs_divdef (u2_pre V))) in Hq.
          apply pm_of_list_get_in in Hq. destruct (WDD _ _ _ Hq) as (X1 & X2 & _). auto. }
      (* [comment removed for export] *)
      intros r Hr.
      pose proof (load_rgn_wf PV (u2_pre V) (u_entry (u1 V)) [] r ST1 Hr) as RWF.
      pose proof (OF r Hr) as OFr.
      apply (other_fact_mono _ _ _ _ _ _ _ defer1 _ Sub BOF (incl_refl _)) in OFr. unfold other_fact in OFr.
      assert (FSnz : forall pr, In pr (vs_rgn A0) -> match vr_kind pr with RK_flag _ => False | _ => True end -> vp_fs P <> None).
      { intros pr Hpr KK. pose proof (HRG _ Hpr) as (_ & _ & _ & _ & _ & _ & _ & KO). unfold kind_ok in KO.
        destruct (vr_kind pr); try tauto. }
      (* [comment removed for export] *)
      assert (GEN : forall pr c exact,
                rc_fact true exact A0 r pr c defer1 ->
                is_shadow r = is_shadow pr ->
                (is_data_shadow pr = false \/ is_data_shadow r = true) ->
                rbase nuV r = rbase nu1 pr + c ->
                In pr (vs_rgn A0) ->
                (forall lo hi off, In (lo, hi) (vr_w r) -> lo <= off < hi -> covered (unit_regions2 PV EV) (rbase nuV r + off) 1) ->
                kind_ok SEGS PV EV nuV S mem1 r ->
                region_ok SEGS PV EV nuV S mem1 r).
      { intros pr c exact RC SH DS RB Hpr COV KO.
        destruct (region_transfer_gen SEGS P E true PV EV nu1 sigma defer1 A0 mem1 r pr c exact DEF HS RC RWF SH DS RB (HRG _ Hpr) ZANY ZRW' COV)
          as (G1' & G2 & G3 & G4 & G5 & G6 & G7).
        split; [exact G1'|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|exact KO]. }
      pose proof (V_ok2) as [STV _]. destruct (unit_static_ok2_wsets _ _ _ STV) as (_ & _ & _ & W4).
      unfold cstate2_iface_b in ST2. apply andb_prop in ST2 as [ST2' NF]. rewrite forallb_forall in NF.
      assert (NORES : forall t', In t' (cs_rgn (u2_pre V)) -> sr_base t' <> SP0 /\ sr_base t' <> DATA /\ sr_base t' <> FSB).
      { intros t' Ht'. destruct (WRB _ Ht') as [R|(o & _ & _ & R)]; [|rewrite R; repeat split; discriminate].
        destruct (reserved_base_false _ R) as (N1 & N2 & _ & _ & N5 & _). auto. }
      apply (load_regions_in P) in Hr as [[t [Ht Er]]|Hstd].
      - (* [comment removed for export] *)
        pose proof (WSK _ Ht) as SK. unfold skind_struct_ok in SK.
        pose proof (NF _ Ht) as NFt. apply andb_prop in NFt as [NF1 NF2]. unfold is_fake, is_flagk in NF1, NF2.
        assert (KR : vr_kind r = rkind_of (sr_kind t)) by (rewrite Er; reflexivity).
        destruct (sr_kind t) as [cid fl| |owner|of_] eqn:KT; cbn [rkind_of] in KR; rewrite KR in OFr; try discriminate.
        + (* [comment removed for export] *)
          apply andb_prop in SK as [SK SKb8]. apply andb_prop in SK as [SK SKd]. apply andb_prop in SK as [SKa SKb].
          apply Pos.leb_le in SKa. apply Pos.leb_le in SKb. apply Z.eqb_eq in SKd.
          destruct OFr as (b' & c & pr & RBr & Gpr & Kpr & RC).
          destruct (rgn_get_in _ _ _ Gpr) as [Hpr Bpr].
          assert (NB : nuV (vr_base r) = nu1 b' + c) by exact (RB_eval _ _ _ _ _ _ _ RBr).
          pose proof RC as (ED & _ & LO & HI & _).
          assert (D0 : vr_disp r = 0) by (rewrite Er; exact SKd).
          assert (RB' : rbase nuV r = rbase nu1 pr + c) by (unfold rbase; rewrite <- ED, NB, Bpr; lia).
          set (i := Z.pos (sr_base t) - 19).
          assert (Hi : 0 <= i < 8) by (unfold i; lia).
          assert (Ebase : vr_base r = ASYM2 i) by (rewrite Er; cbn [vregion_of vr_base]; unfold ASYM2, i; lia).
          assert (KNF : match vr_kind pr with RK_flag _ => False | _ => True end) by (destruct Kpr as [K|(_ & ? & ? & K)]; rewrite K; exact I).
          pose proof (FSnz _ Hpr KNF) as F1.
          pose proof (HRG _ Hpr) as (PB1 & PB2 & _ & _ & _ & PRP & _ & KOp).
          destruct (PRP ltac:(unfold is_data_shadow; destruct Kpr as [K|(_ & ? & ? & K)]; rewrite K; reflexivity)) as [_ RP2].
          (* [comment removed for export] *)
          assert (WRG : forall lo hi, In (lo, hi) (vr_w r) -> exists lo' hi', In (i, (lo', hi')) (u2_wrgn V) /\ lo' <= lo /\ hi <= hi').
          { intros lo hi Hw. unfold wrgn_ok in ST3. rewrite forallb_forall in ST3. specialize (ST3 _ Ht). rewrite KT in ST3.
            rewrite forallb_forall in ST3. rewrite Er in Hw. cbn [vregion_of vr_w] in Hw. specialize (ST3 _ Hw). cbn beta in ST3.
            apply existsb_exists in ST3 as [[j [lo' hi']] [Hin Hb]]. cbn [fst snd] in Hb.
            apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2]. apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.leb_le in Hb3.
            exists lo', hi'. subst j. auto. }
          destruct (footprint_ok2_v1 _ _ _ _ FP) as [_ WAD]. rewrite forallb_forall in WAD.
          assert (ADM : forall lo' hi', In (i, (lo', hi')) (u2_wrgn V) ->
                    vr_disp pr = 0 /\ exists lo2 hi2, In (lo2, hi2) (vr_w pr) /\ lo2 <= lo' + c /\ lo' + c + (hi' - lo') <= hi2).
          { intros lo' hi' Hin. specialize (WAD _ Hin). unfold wrgn_admissible in WAD.
            destruct (resolve_base isv_call2 A0 sigma (ASYM2 i)) as [[b2 c2]|] eqn:RS2; [|discriminate].
            pose proof (resolve_base_spec _ _ _ _ _ _ RS2) as RB2. rewrite <- Ebase in RB2.
            destruct (RB_functional _ _ _ _ _ _ _ _ RBr RB2) as [<- <-]. rewrite Gpr in WAD.
            apply andb_prop in WAD as [WD WAD]. apply Z.eqb_eq in WD. split; [exact WD|].
            assert (IR : in_ranges (vr_w pr) (lo' + c) (hi' - lo') = true) by (destruct (vr_kind pr); try discriminate; exact WAD).
            destruct (in_ranges_sound _ _ _ IR) as (lo2 & hi2 & Hw2 & Z1 & Z2). exists lo2, hi2. auto. }
          apply (GEN pr c false RC ltac:(unfold is_shadow; rewrite KR; destruct Kpr as [K|(_ & ? & ? & K)]; rewrite K; reflexivity)
                   ltac:(left; unfold is_data_shadow; destruct Kpr as [K|(_ & ? & ? & K)]; rewrite K; reflexivity) RB' Hpr).
          * (* [comment removed for export] *)
            intros lo hi off Hw Hoff. destruct (WRG _ _ Hw) as (lo' & hi' & Hin & Z1 & Z2).
            destruct (ADM _ _ Hin) as (DP & lo2 & hi2 & Hw2 & Z3 & Z4).
            destruct (RP2 lo2 hi2 (off + c) Hw2 ltac:(lia)) as (QQ1 & _).
            destruct (RP2 lo2 hi2 (lo' + c) Hw2 ltac:(lia)) as (QQ0 & _).
            rewrite RB'. unfold rbase in PB1, PB2 |- *. rewrite DP, Bpr in PB1, PB2 |- *.
            apply (covered_wordZ _ (nuV (ASYM2 i) + lo') (hi' - lo')); try lia.
            -- apply in_unit_regions2_args. unfold arg_regions. apply in_map_iff. exists (i, (lo', hi')). split; [|exact Hin].
               f_equal. f_equal. cbn [e_args EV callee_env2].
               erewrite nth_error_nth; [reflexivity|]. rewrite nth_error_map, nth_error_seq.
               destruct (PeanoNat.Nat.ltb_spec (Z.to_nat i) 8); [|lia]. cbn. f_equal. f_equal. unfold ASYM2. lia.
            -- rewrite <- Ebase, NB. lia.
            -- rewrite <- Ebase, NB. lia.
            -- rewrite <- Ebase, NB. lia.
          * (* [comment removed for export] *)
            unfold kind_ok. rewrite KR. split; [exact F1|]. split.
            -- destruct Kpr as [Karg|(_ & cid & fl & Kfake)].
               ++ unfold kind_ok in KOp. rewrite Karg in KOp. destruct KOp as (_ & (cidL & posL & L1 & L2 & L3) & _).
                  exists cidL, posL. split; [cbn [e_live EV callee_env2]; apply in_app_iff; left; exact L1|].
                  cbn [e_fs EV callee_env2]. rewrite RB'. lia.
               ++ destruct (Forall2_In_l _ _ _ _ HL (in_fakes_of _ _ _ _ Hpr Kfake)) as (cp & Hcp & fl' & Kc & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
                  exists (fst cp), (snd cp). split; [cbn [e_live EV callee_env2]; apply in_app_iff; right; rewrite <- surjective_pairing; exact Hcp|].
                  cbn [e_fs EV callee_env2]. rewrite RB', <- C3. lia.
            -- exists i. split; [exact Hi|]. split; [exact Ebase|]. intros lo hi Hw. destruct (WRG _ _ Hw) as (lo' & hi' & Hin & Z1 & Z2).
               exists lo', hi'. split; [exact Hin|lia].
        + (* [comment removed for export] *)
          destruct OFr as (of' & c & pr & CASES & DD & CM & Gpr & BLb & RC).
          destruct (rgn_shadow_of_in _ _ _ Gpr) as [Hpr Kpr].
          pose proof RC as (ED & _ & LO & HI & WI & _).
          assert (NB : nuV (vr_base r) = nu1 (vr_base pr) + c / 8).
          { unfold nuV. rewrite (BL_eval _ _ _ _ _ BLb), eval_laddc, eval_lsym. reflexivity. }
          assert (RB' : rbase nuV r = rbase nu1 pr + c / 8) by (unfold rbase; rewrite <- ED, NB; lia).
          pose proof (Z.div_mod c 8 ltac:(lia)) as C8. rewrite CM, Z.add_0_r in C8.
          (* [comment removed for export] *)
          unfold shadow_disp_ok in SD. rewrite forallb_forall in SD. specialize (SD _ Ht). rewrite KT in SD. apply andb_prop in SD as [SD1 SD2]. apply Z.eqb_eq in SD1.
          assert (DISP : vr_disp r = vp_shoff P) by (rewrite Er; exact SD1).
          assert (SPX : of_ = SP0 -> sr_base t = SP8 /\ sr_lo t = - (vp_frame (p1 P) / 8) - 8 /\ sr_hi t = 1 /\ sr_w t = shadow_w (vp_wstack (p1 PV))).
          { intros ->. rewrite Pos.eqb_refl in SD2. cbn [negb orb] in SD2.
            apply andb_prop in SD2 as [SD2 X4]. apply andb_prop in SD2 as [SD2 X3]. apply andb_prop in SD2 as [X1 X2].
            apply Pos.eqb_eq in X1. apply Z.eqb_eq in X2. apply Z.eqb_eq in X3. apply ranges_eqb_eq in X4. auto. }
          assert (ALT : (of_ = SP0 /\ sr_base t = SP8)
                        \/ (of_ <> SP0 /\ of_ <> DATA /\ of_ <> FSB /\
                            exists t' b8, In t' (cs_rgn (u2_pre V)) /\ sr_base t' = of_ /\ sr_b8 t' = Some b8 /\ b8 = sr_base t
                                          /\ sr_kind t' = SK_arg /\ sr_w t = [])).
          { apply Bool.orb_prop in SK. destruct SK as [SK|SK].
            - apply andb_prop in SK as [SKo SKb']. apply Pos.eqb_eq in SKo. apply Pos.eqb_eq in SKb'. left; auto.
            - apply existsb_exists in SK as [t' [Ht' Hb]].
              apply andb_prop in Hb as [Hb E3]. apply andb_prop in Hb as [E1 E2]. apply Pos.eqb_eq in E1.
              destruct (sr_b8 t') as [b8|] eqn:EB; [|discriminate]. apply Pos.eqb_eq in E3.
              right. destruct (NORES _ Ht') as (N1 & N2 & N3). rewrite E1 in N1, N2, N3.
              split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. exists t', b8.
              pose proof (NF _ Ht') as NF'. apply andb_prop in NF' as [NF1' _]. unfold is_fake in NF1'.
              destruct (sr_kind t') eqn:KT'; try discriminate.
              destruct (sr_w t); [|discriminate]. auto 10. }
          pose proof (HRG _ Hpr) as (_ & _ & _ & _ & _ & _ & _ & KOp). unfold kind_ok in KOp. rewrite Kpr in KOp.
          destruct KOp as (F1 & _ & _ & _ & _ & OWK).
          assert (NDr : Pos.eqb of_ DATA = false).
          { destruct ALT as [[-> _]|(_ & X & _)]; [reflexivity|]. destruct (Pos.eqb_spec of_ DATA); [contradiction|reflexivity]. }
          apply (GEN pr (c / 8) (Pos.eqb of_ DATA) RC ltac:(unfold is_shadow; rewrite KR, Kpr; reflexivity)
                   ltac:(left; unfold is_data_shadow; rewrite Kpr, DD; exact NDr) RB' Hpr).
          * (* [comment removed for export] *)
            intros lo hi off Hw Hoff.
            destruct ALT as [[Eo Bt]|(N1 & N2 & N3 & t' & b8 & Ht' & E1 & EB & E3 & KT' & W0)].
            2:{ exfalso. rewrite Er in Hw. cbn [vregion_of vr_w] in Hw. rewrite W0 in Hw. exact Hw. }
            destruct (SPX Eo) as (B1 & L1 & H1 & W1). rewrite Er in Hw. cbn [vregion_of vr_w] in Hw. rewrite W1 in Hw.
            cbn in Hw. destruct Hw as [Elh|[]]. injection Elh as Elo Ehi.
            set (lo0 := - vp_frame (p1 P)) in *. set (hi0 := u_sp (u1 V)) in *.
            change (- vp_frame (p1 (ge2_P0 G)) / 8 = lo) with (lo0 / 8 = lo) in Elo.
            (* [comment removed for export] *)
            unfold mod8_ok in M8. change (has_asan PV) with (asan_mode P) in M8. unfold asan_mode in M8.
            pose proof HFS as HFS'. unfold env_fs in HFS'.
            destruct (vp_fs P) as [fsv|] eqn:EFS; [|exfalso; exact (F1 eq_refl)]. cbn [negb orb] in M8.
            apply andb_prop in M8 as [M81 M82]. apply Z.eqb_eq in M81. apply Z.eqb_eq in M82.
            destruct (unit_static_ok2_wsets _ _ _ STV) as (W1s & _ & W3s & _).
            assert (EF1 : vp_frame (p1 (unit_params2 G V)) = vp_frame (p1 P)) by reflexivity.
            assert (EF2 : vp_frame (p1 (ge2_P0 G)) = vp_frame (p1 P)) by reflexivity.
            apply Bool.orb_false_elim in W3s as [W3a W3b]. apply Z.ltb_ge in W3a. apply Z.ltb_ge in W3b.
            rewrite ?EF1, ?EF2 in W3b, M82, W1s.
            assert (AL : lo0 mod 8 = 0 /\ hi0 mod 8 = 0 /\ - vp_frame (p1 P) <= lo0 /\ hi0 <= 0).
            { subst lo0 hi0. split; [apply Z_mod_zero_opp_full; exact M82|]. split; [exact M81|]. clear - W3a. lia. }
            destruct AL as (AL1 & AL2 & AL3 & AL4).
            rewrite <- Elo, <- Ehi in Hoff.
            destruct HE as (E16 & Esp & _ & _ & _ & _ & _ & _ & _ & _ & Efr). rewrite ?EF2 in Efr.
            pose proof (PO2_shoff SEGS P PO) as SH0. destruct (PO2_fs SEGS P PO ltac:(rewrite EFS; discriminate)) as [SHV _].
            pose proof PO1 as (Pfr & Psphi & _). change (vp_frame (unit_params G1 (u1 U))) with (vp_frame (p1 P)) in Pfr.
            change (vp_sphi (unit_params G1 (u1 U))) with (vp_sphi (p1 P)) in Psphi. change (vp_sphi (p1 (ge2_P0 G))) with (vp_sphi (p1 P)) in Esp.
            change (vp_splo (p1 (ge2_P0 G))) with (vp_splo (p1 P)) in Esp.
            assert (NB8 : nuV (vr_base r) = e_sp0 (ev1 E) / 8).
            { rewrite Er. cbn [vregion_of vr_base]. rewrite B1, UNB by reflexivity. exact (HF2 SP8 _ eq_refl). }
            unfold rbase. rewrite DISP, NB8.
            destruct (shadow_cover_arith (e_sp0 (ev1 E)) lo0 hi0 off (vp_shoff P) E16 AL1 AL2 Hoff ltac:(clear -AL3 Efr; lia) AL4
                        ltac:(rewrite SHV; clear; lia) ltac:(clear -Esp Psphi; lia)) as (Y1 & Y2 & Y3 & Y4).
            apply (covered_wordZ _ (vp_shoff P + (e_sp0 (ev1 E) + lo0) / 8) ((hi0 - lo0) / 8)); [|exact Y1|exact Y2|exact Y3|exact Y4].
            apply (in_unit_regions2_shadow PV EV _ fsv EFS). unfold stack_shadow_regions. apply in_map_iff. exists (lo0, hi0). split; [reflexivity|left; reflexivity].
          * (* [comment removed for export] *)
            unfold kind_ok. rewrite KR. split; [exact F1|]. split; [exact DISP|].
            split. { intros Eo. destruct (SPX Eo) as (B1 & L1 & H1 & _). rewrite Er. cbn [vregion_of vr_base vr_lo vr_hi]. rewrite B1, L1, H1.
                     change (vp_frame (p1 PV)) with (vp_frame (p1 P)). split; [reflexivity|lia]. }
            split. { intros ->. exfalso. destruct ALT as [[X _]|(_ & X & _)]; [discriminate|exact (X eq_refl)]. }
            split. { intros ->. destruct ALT as [[X _]|(_ & _ & X & _)]; [discriminate|exact (X eq_refl)]. }
            intros N1 N2 N3. destruct ALT as [[X _]|(_ & _ & _ & t' & b8 & Ht' & E1 & EB & E3 & KT' & W0)]; [exfalso; exact (N1 X)|].
            exists (vregion_of t'). split; [rewrite <- E1; apply (stored_rgn_get P); [exact WF|exact Ht']|].
            split; [cbn [vregion_of vr_b8]; rewrite EB, E3, Er; reflexivity|].
            cbn [vregion_of vr_kind]. rewrite KT'. cbn [rkind_of].
            (* [comment removed for export] *)
            assert (RBo4 : RB isv_call2 A0 sigma of_ of' c /\ of' <> SP0 /\ of' <> DATA /\ of' <> FSB).
            { destruct CASES as [[[X|X] _]|(_ & _ & Q1 & Q2 & Q3 & X)]; [exfalso; exact (N1 X)|exfalso; exact (N2 X)|auto]. }
            destruct RBo4 as (RBo & Q1 & Q2 & Q3).
            assert (Eof : nuV of_ = nu1 of' + c) by exact (RB_eval _ _ _ _ _ _ _ RBo).
            destruct (OWK Q1 Q2 Q3) as (roA & GroA & B8A & MK).
            destruct (rgn_get_in _ _ _ GroA) as [HroA BroA].
            (* [comment removed for export] *)
            pose proof (OF (vregion_of t') (stored_in_loaded P _ _ _ _ Ht')) as OF'.
            apply (other_fact_mono _ _ _ _ _ _ _ defer1 _ Sub BOF (incl_refl _)) in OF'. unfold other_fact in OF'.
            cbn [vregion_of vr_kind] in OF'. rewrite KT' in OF'. cbn [rkind_of] in OF'.
            destruct OF' as (b2 & c2 & pr2 & RBr2 & Gpr2 & Kpr2 & RC2).
            cbn [vregion_of vr_base] in RBr2. rewrite E1 in RBr2.
            destruct (RB_functional _ _ _ _ _ _ _ _ RBo RBr2) as [<- <-].
            rewrite GroA in Gpr2. injection Gpr2 as <-.
            pose proof (proj1 RC2) as ED2. cbn [vregion_of vr_disp] in ED2.
            pose proof (WSK _ Ht') as SK'. unfold skind_struct_ok in SK'. rewrite KT' in SK'.
            apply andb_prop in SK' as [SK' _]. apply andb_prop in SK' as [SK' SKd']. apply Z.eqb_eq in SKd'.
            assert (RroA : rbase nu1 roA = nu1 of') by (unfold rbase; rewrite <- ED2, SKd', BroA; lia).
            assert (KEY : nuV (vr_base r) = (nuV of_) / 8
                          /\ match vr_kind roA with
                             | RK_fake cid _ => 0 <= c + 8 * vr_lo r /\ c + 8 * vr_hi r <= fake_size cid /\ nu1 of' = 8 * nu1 (vr_base pr)
                             | RK_arg => exists cid pos, In (cid, pos) (e_live E)
                                         /\ frame_addr (e_fs E) cid pos <= 8 * (nuV (vr_base r) + vr_lo r)
                                         /\ 8 * (nuV (vr_base r) + vr_hi r) <= frame_addr (e_fs E) cid pos + fake_size cid
                             | _ => False end).
            { rewrite NB, Eof. set (k := c / 8) in *.
              destruct (vr_kind roA) as [cidA flA| | | |]; try contradiction.
              - destruct MK as (MK1 & MK2 & MK3). rewrite RroA in MK1.
                split. { rewrite <- MK1, C8. replace (8 * nu1 (vr_base pr) + 8 * k) with ((nu1 (vr_base pr) + k) * 8) by (clear; lia).
                         rewrite Z.div_mul by (clear; lia). reflexivity. }
                split; [clear -LO MK2 C8; lia|]. split; [clear -HI MK3 C8; lia|]. symmetry; exact MK1.
              - destruct MK as (MK1 & MK2 & cidL & posL & L1 & L2 & L3). rewrite RroA in MK1.
                split. { rewrite MK1, C8. replace (8 * k) with (k * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). reflexivity. }
                exists cidL, posL. split; [exact L1|]. clear - L2 L3 LO HI C8 MK1. lia. }
            destruct KEY as [KEY1 KEY2].
            split; [unfold rbase; cbn [vregion_of vr_disp vr_base]; rewrite SKd', E1; rewrite KEY1; reflexivity|].
            split; [rewrite Er; cbn [vregion_of vr_w]; exact W0|].
            cbn [e_live e_fs EV callee_env2].
            destruct (vr_kind roA) as [cidA flA| | | |] eqn:KroA; try contradiction.
            -- destruct KEY2 as (KB1 & KB2 & KB3).
               destruct (Forall2_In_l _ _ _ _ HL (in_fakes_of _ _ _ _ HroA KroA)) as (cp & Hcp & fl' & Kc & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8' & C9).
               rewrite KroA in Kc. injection Kc as -> ->.
               exists (fst cp), (snd cp). split; [apply in_app_iff; right; rewrite <- surjective_pairing; exact Hcp|].
               rewrite <- C3, RroA, NB. clear - KB1 KB2 KB3 C8. lia.
            -- destruct KEY2 as (cidL & posL & L1 & L2 & L3). exists cidL, posL. split; [apply in_app_iff; left; exact L1|]. split; [exact L2|exact L3].
      - (* [comment removed for export] *)
        apply std_regions_cases in Hstd as [[Er HAS]|[Er HAS]]; subst r; cbn [SHD FSR vr_kind] in OFr.
        + (* [comment removed for export] *)
          destruct OFr as (of' & c0 & pr & CASES & DD & CM & Gpr & BLb & RC).
          assert (Eof : of' = DATA /\ c0 = 0) by (destruct CASES as [(_ & X1 & X2)|(_ & X & _)]; [auto|exfalso; exact (X eq_refl)]).
          destruct Eof as [-> ->].
          destruct (rgn_shadow_of_in _ _ _ Gpr) as [Hpr Kpr].
          pose proof (HRG _ Hpr) as (_ & _ & _ & _ & _ & _ & _ & KOp). unfold kind_ok in KOp. rewrite Kpr in KOp.
          assert (NB : nuV DATA8 = nu1 (vr_base pr)).
          { unfold nuV. rewrite (BL_eval _ _ _ _ _ BLb), eval_laddc, eval_lsym. cbn. liae. }
          destruct KOp as (F1 & DP & _).
          assert (RB' : rbase nuV (SHD P) = rbase nu1 pr + 0 / 8).
          { unfold rbase. cbn [SHD vr_disp vr_base]. rewrite NB, <- (proj1 RC). cbn [SHD vr_disp]. liae. }
          apply (GEN pr (0 / 8) true RC ltac:(unfold is_shadow; rewrite Kpr; reflexivity) ltac:(right; reflexivity) RB' Hpr).
          * intros lo hi off [].
          * unfold kind_ok. cbn [SHD vr_kind vr_disp vr_base]. split; [exact F1|]. split; [reflexivity|]. split; [intros X; discriminate|].
            split; [reflexivity|]. split; [intros X; discriminate|]. intros _ ND _. exfalso. exact (ND eq_refl).
        + (* [comment removed for export] *)
          destruct OFr as (pr & Gpr & Kpr & RC).
          destruct (rgn_get_in _ _ _ Gpr) as [Hpr Bpr].
          pose proof (HRG _ Hpr) as (_ & _ & _ & _ & _ & _ & _ & KOp). unfold kind_ok in KOp. rewrite Kpr in KOp.
          destruct KOp as (F1 & _ & DP & _).
          assert (NB : nuV FSB = e_fs E) by (rewrite UNB by reflexivity; exact (HF2 FSB _ eq_refl)).
          assert (RB' : rbase nuV FSR = rbase nu1 pr + 0).
          { unfold rbase. cbn [FSR vr_disp vr_base]. rewrite Bpr, DP, NB, (HF2 FSB _ eq_refl). lia. }
          apply (GEN pr 0 true RC ltac:(unfold is_shadow; rewrite Kpr; reflexivity) ltac:(left; unfold is_data_shadow; rewrite Kpr; reflexivity) RB' Hpr).
          * intros lo hi off Hw Hoff. cbn [FSR vr_w] in Hw. destruct Hw as [Hw|[]]. injection Hw as <- <-.
            unfold rbase. cbn [FSR vr_disp vr_base]. rewrite NB.
            pose proof HFS as HFS'. unfold env_fs in HFS'. destruct (vp_fs P) as [[len ssl]|] eqn:EFS; [|exfalso; exact (F1 eq_refl)].
            destruct HFS' as (_ & FLO & FHI & _ & FLEN & _).
            apply (covered_wordZ _ (e_fs E) 88); try (unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia).
            apply in_unit_regions2_fs. unfold fs_regions. change (vp_fs PV) with (vp_fs P). rewrite EFS. apply in_or_app. left. left. reflexivity.
          * unfold kind_ok. cbn [FSR vr_kind vr_base vr_disp vr_lo vr_hi]. split; [exact F1|]. repeat split; reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma regions_sub2 nu1 regs1 mem1 L (a : word) :
      gammaP A0 nu1 regs1 mem1 -> fake_slots_of nu1 mem1 L ->
      outside a (unit_regions2 P E) -> outside a (unit_regions2 PV (callee_env2 npc (vsubst nu1 sigma) L)).
    Proof using D1 DONE FP NPC PO STATIC VIN mem_e.
      intros HGm HL Hout. set (nuV := vsubst nu1 sigma). set (EV := callee_env2 npc nuV L).
      pose proof HGm as (HV1 & HE2 & HMC2 & HF2 & HDD & HRG & HLV & HB2 & HGL). pose proof HV1 as (HE & _).
      pose proof (proj1 (outside_forall _ _) Hout) as OUT.
      apply (proj2 (outside_forall _ _)). intros b n Hin Hrng.
      destruct (footprint_ok2_v1 _ _ _ _ FP) as [FP1 WAD]. rewrite forallb_forall in WAD.
      unfold unit_regions2 in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]]].
      - (* [comment removed for export] *)
        assert (O1 : outside a (unit_regions (p1 P) (ev1 E))).
        { apply (proj2 (outside_forall _ _)). intros b' n' Hin'. apply OUT. unfold unit_regions2. rewrite !in_app_iff. auto. }
        pose proof (regions_sub SEGS G1 rom (map u1 done) (u1 U) (ev1 E) mem0 PO1 (VSTEP1 mem0) (u1 V) spoff npc nuV a FP1 HE O1) as O2.
        exact (proj1 (outside_forall _ _) O2 b n Hin Hrng).
      - (* [comment removed for export] *)
        unfold arg_regions in Hin. apply in_map_iff in Hin as [[i [lo hi]] [Eb Hw]]. injection Eb as Eb1 Eb2. subst b n.
        specialize (WAD _ Hw). unfold wrgn_admissible in WAD.
        destruct (resolve_base isv_call2 A0 sigma (ASYM2 i)) as [[b' c]|] eqn:RS; [|discriminate].
        destruct (rgn_get (vs_rgn A0) b') as [pr|] eqn:Gpr; [|discriminate].
        apply andb_prop in WAD as [WD WAD]. apply Z.eqb_eq in WD.
        destruct (rgn_get_in _ _ _ Gpr) as [Hpr Bpr].
        assert (KNF : is_data_shadow pr = false /\ in_ranges (vr_w pr) (lo + c) (hi - lo) = true).
        { unfold is_data_shadow. destruct (vr_kind pr); try discriminate; auto. }
        destruct KNF as [NDS IR].
        pose proof (HRG _ Hpr) as (PB1 & PB2 & _ & _ & _ & PRP & _). destruct (PRP NDS) as [_ RP2].
        destruct (in_ranges_sound _ _ _ IR) as (lo2 & hi2 & Hw2 & Z1 & Z2).
        assert (EA : nth (Z.to_nat i) (e_args EV) 0 = nu1 b' + c).
        { destruct (unit_static_ok2_wsets _ _ _ (proj1 (V_ok2))) as (_ & _ & _ & W4). rewrite forallb_forall in W4.
          specialize (W4 _ Hw). cbn [fst snd] in W4. apply andb_prop in W4 as [W4 _]. apply andb_prop in W4 as [W4a W4b].
          apply Z.leb_le in W4a. apply Z.ltb_lt in W4b.
          cbn [e_args EV callee_env2]. erewrite nth_error_nth; [|rewrite nth_error_map, nth_error_seq;
            destruct (PeanoNat.Nat.ltb_spec (Z.to_nat i) 8); [reflexivity|lia]]. cbn.
          replace (ASYM2 (Z.of_nat (Z.to_nat i))) with (ASYM2 i) by (unfold ASYM2; f_equal; lia).
          exact (RB_eval _ _ _ _ _ _ _ (resolve_base_spec _ _ _ _ _ _ RS)). }
        assert (Hrng' : in_rng a (wordZ (nu1 b' + c + lo)) (hi - lo)) by (rewrite <- EA; exact Hrng). clear Hrng. rename Hrng' into Hrng.
        unfold in_rng in Hrng.
        destruct (Z.lt_ge_cases lo hi) as [LH|LH]; [|rewrite u_wordZ in Hrng; [lia|]].
        2:{ unfold rbase in PB1, PB2. rewrite WD, Bpr in PB1, PB2. destruct (RP2 lo2 hi2 (lo + c) Hw2 ltac:(lia)) as (Q0 & _). lia. }
        destruct (RP2 lo2 hi2 (lo + c) Hw2 ltac:(lia)) as (Q0 & _).
        unfold rbase in PB1, PB2, RP2. rewrite WD, Bpr in PB1, PB2, RP2.
        rewrite u_wordZ in Hrng by lia.
        destruct (RP2 lo2 hi2 (bv_unsigned a - nu1 b') Hw2 ltac:(lia)) as (_ & _ & _ & COV).
        destruct COV as (b0 & m0 & Hin0 & Y1 & Y2).
        apply (OUT b0 m0 Hin0). unfold in_rng. lia.
      - (* [comment removed for export] *)
        change (vp_fs PV) with (vp_fs P) in Hin.
        destruct (vp_fs P) as [fsv|] eqn:EFS; [|destruct Hin].
        unfold stack_shadow_regions in Hin. apply in_map_iff in Hin as [[lo hi] [Eb Hr]]. cbn [fst snd] in Eb. injection Eb as Eb1 Eb2. subst b n.
        cbn in Hr. destruct Hr as [Hr|[]]. injection Hr as Elo Ehi.
        change (vp_frame (p1 (ge2_P0 G))) with (vp_frame (p1 P)) in Elo. subst lo hi.
        cbn [ev1 EV callee_env2 callee_env e_sp0] in Hrng. change (vp_shoff PV) with (vp_shoff P) in Hrng.
        (* [comment removed for export] *)
        unfold footprint_ok in FP1. change (de_U D1) with (u1 U) in FP1. change (de_P D1) with (p1 P) in FP1.
        apply andb_prop in FP1 as [FP1 _]. apply andb_prop in FP1 as [FP1 _]. apply andb_prop in FP1 as [FP1 FS]. apply andb_prop in FP1 as [F1 F2].
        apply Z.leb_le in F1. apply Z.eqb_eq in F2.
        pose proof (mod8_facts _ _ (unit_static_ok2_mod8 _ _ _ STATIC) ltac:(unfold has_asan; change (vp_fs P) with (vp_fs P); rewrite EFS; reflexivity)) as [MU1 MU2].
        destruct V_static2 as (_ & _ & _ & _ & _ & M8).
        pose proof (mod8_facts _ _ M8 ltac:(unfold has_asan; change (vp_fs PV) with (vp_fs P); rewrite EFS; reflexivity)) as [MV1 MV2].
        destruct HE as (E16 & Esp & _ & _ & _ & _ & _ & _ & _ & _ & Efr).
        pose proof PO1 as (Pfr & Psphi & _ & _ & _ & PWS & _).
        assert (EF1 : vp_frame (p1 PV) = vp_frame (p1 P)) by reflexivity.
        assert (EF0 : vp_frame (p1 (ge2_P0 G)) = vp_frame (p1 P)) by reflexivity.
        assert (X1 : e_sp0 (ev1 E) < 2 ^ 64) by (eapply Z.le_lt_trans; [exact (proj2 Esp)|exact Psphi]).
        assert (X2 : vp_frame (p1 P) <= e_sp0 (ev1 E)) by exact Efr.
        assert (X3 : 0 <= vp_frame (p1 P)) by exact Pfr.
        clear Esp Psphi Efr Pfr.
        pose proof (PO2_shoff SEGS P PO) as SH0. destruct (PO2_fs SEGS P PO ltac:(rewrite EFS; discriminate)) as [SHV _].
        destruct (unit_static_ok2_wsets _ _ _ (proj1 V_ok2)) as (_ & _ & W3 & _).
        apply Bool.orb_false_elim in W3 as [W3a W3b]. apply Z.ltb_ge in W3a. apply Z.ltb_ge in W3b. rewrite ?EF1 in W3b.
        set (lo := - vp_frame (p1 P)) in *. set (hi := u_sp (u1 V)) in *.
        set (lo' := - vp_frame (p1 P)). set (hi' := u_sp (u1 U)).
        assert (Hin' : In (lo', hi') (vp_wstack (p1 P))) by (left; reflexivity).
        assert (AL1 : lo mod 8 = 0) by (unfold lo; apply Z_mod_zero_opp_full; exact MU2).
        assert (AL2 : hi mod 8 = 0) by exact MV1.
        assert (AL3 : lo' mod 8 = 0) by (unfold lo'; apply Z_mod_zero_opp_full; exact MU2).
        assert (AL4 : hi' mod 8 = 0) by exact MU1.
        assert (Z1 : lo' <= lo) by (unfold lo, lo'; clear; lia).
        assert (Z2 : hi <= hi') by (rewrite F2; exact F1).
        unfold in_rng in Hrng.
        destruct (Z.lt_ge_cases lo hi) as [LH|LH].
        2:{ (* [comment removed for export] *)
            assert ((hi - lo) / 8 <= 0) by (apply Z.div_le_upper_bound; lia). (ltac2:(LK.k [@Hrng; @EF1; @X2; @X3; @H]); lia). }
        pose proof (PWS _ Hin') as [_ W2]. cbn [snd] in W2.
        assert (B0 : 0 <= vp_shoff P + (e_sp0 (ev1 E) + lo) / 8 < 2 ^ 64).
        { split; [apply Z.add_nonneg_nonneg; [(ltac2:(LK.k [@X3; @SH0; @EF1; @X2; @W3a; @Z2; @LH]); lia)|apply Z.div_pos; (ltac2:(LK.k [@X3; @SH0; @EF1; @X2; @W3a; @Z2; @LH]); lia)]|].
          assert ((e_sp0 (ev1 E) + lo) / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; (ltac2:(LK.k [@X3; @X1; @W3a; @Z2; @LH]); lia)). (ltac2:(LK.k [@X3; @SHV; @LH; @H]); lia). }
        assert (B0' : 0 <= vp_shoff P + (e_sp0 (ev1 E) + lo') / 8 < 2 ^ 64).
        { split; [apply Z.add_nonneg_nonneg; [(ltac2:(LK.k [@X3; @SH0; @EF1; @X2; @W3a; @Z2; @LH]); lia)|apply Z.div_pos; (ltac2:(LK.k [@X3; @SH0; @EF1; @X2; @W3a; @Z2; @LH]); lia)]|].
          assert ((e_sp0 (ev1 E) + lo') / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; (ltac2:(LK.k [@X3; @X1; @W3a; @Z2; @LH]); lia)). (ltac2:(LK.k [@X3; @SHV; @LH; @H]); lia). }
        rewrite u_wordZ in Hrng by exact B0.
        pose proof (shadow_nest_arith (e_sp0 (ev1 E)) lo hi lo' hi' (bv_unsigned a) (vp_shoff P) E16 AL1 AL2 AL3 AL4 Z1 Z2 Hrng) as R'.
        apply (OUT (wordZ (vp_shoff P + (e_sp0 (ev1 E) + lo') / 8)) ((hi' - lo') / 8)).
        + apply (in_unit_regions2_shadow P E _ fsv EFS). unfold stack_shadow_regions. apply in_map_iff. exists (lo', hi'). split; [reflexivity|left; reflexivity].
        + unfold in_rng. rewrite u_wordZ by exact B0'. exact R'.
      - (* [comment removed for export] *)
        rewrite (fs_regions_P PV P) in Hin by reflexivity.
        unfold fs_regions in Hin.
        destruct (vp_fs P) as [fsv|] eqn:EFS; [|destruct Hin].
        cbn [e_fs e_live EV callee_env2] in Hin.
        apply (OUT b n); [|exact Hrng]. apply in_unit_regions2_fs. unfold fs_regions. rewrite EFS.
        apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin|right].
        apply (classes_regions_mono P (e_fs E) (e_live E) (e_live E ++ L)); [intros cp Hcp; apply in_app_iff; left; exact Hcp|].
        exact Hin.
    Qed.
  End Callee2.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma region_ok_rebuild (A A' : vstate2) (nu nu' : val) (mem mem' : word -> option byte) (r r' : vregion) :
    env_ok2 P E ->
    region_ok SEGS P E nu A mem r ->
    rshape r r' ->
    nu' (vr_base r) = nu (vr_base r) ->
    (match vr_kind r with RK_fake _ fl => nu' fl = nu fl | _ => True end) ->
    (is_data_shadow r = false \/ (vr_cells r' = [] /\ vr_nul r' = [])) ->
    mem_grows mem mem' ->
    (match vr_kind r with RK_fake _ fl => rdn SEGS mem' (wordZ (nu fl)) 1 = rdn SEGS mem (wordZ (nu fl)) 1 | _ => True end) ->
    (forall s ro, rgn_get (vs_rgn A) s = Some ro ->
        match vr_kind ro with RK_fake _ _ | RK_arg => True | _ => False end ->
        match vr_kind r with RK_flag o => o = s | RK_shadow s' => s' = s | _ => False end ->
        exists ro', rgn_get (vs_rgn A') s = Some ro' /\ rshape ro ro' /\ nu' (vr_base ro) = nu (vr_base ro)) ->
    (match vr_kind r with RK_fake _ _ => In (vr_base r) (vs_live A') | _ => True end) ->
    (match vr_kind r with RK_flag _ => vr_cells r' = [] | _ => True end) ->
    (forall off w v, In (off, (w, v)) (vr_cells r') ->
        vr_lo r <= off /\ 0 < w /\ off + w <= vr_hi r /\ rcell_holds SEGS (is_shadow r) nu' mem' (rbase nu r + off) w v) ->
    (forall lo hi, In (lo, hi) (vr_nul r') ->
        exists off b, lo <= off <= hi /\ vr_lo r <= off < vr_hi r /\
                      rdn SEGS mem' (wordZ (rbase nu r + off)) 1 = Some [b] /\ bv_unsigned b = 0) ->
    region_ok SEGS P E nu' A' mem' r'.
  Proof using G U.
    intros HE ROK SH NB NF DSC GR FLG GET LIVE' FLC HCELLS HNUL.
    pose proof ROK as (B1 & B2 & B3 & DS & CELLS & PERM & NUL & KIND).
    pose proof SH as (SB & SD & SK & SL & SHI & SW & S8).
    assert (RB : rbase nu' r' = rbase nu r) by (unfold rbase; rewrite SD, SB, NB; reflexivity).
    assert (DSH : is_data_shadow r' = is_data_shadow r) by (unfold is_data_shadow; rewrite SK; reflexivity).
    assert (ISH : is_shadow r' = is_shadow r) by (unfold is_shadow; rewrite SK; reflexivity).
    unfold region_ok, region_cells_ok, region_perm_ok, region_nul_ok. rewrite !RB, !SL, !SHI, !DSH, !SW, !ISH.
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split.
    { intros DD1. destruct DSC as [D0|[C0 N0]]; [rewrite D0 in DD1; discriminate|]. rewrite C0, N0. destruct (DS DD1) as (_ & W0 & _). auto. }
    split; [exact HCELLS|]. split; [|split; [exact HNUL|]].
    - intros ND. destruct (PERM ND) as [RD WR]. split.
      + intros off Hoff. destruct (RD off Hoff) as [Z1 [bb Hb]]. split; [exact Z1|]. eapply rdn1_grows; eauto.
      + intros lo hi off Hlh Hoff. destruct (WR lo hi off Hlh Hoff) as (W1 & W2 & W3 & W4).
        split; [exact W1|]. split; [exact W2|]. split; [eapply store_ok_mono; eauto|exact W4].
    - unfold kind_ok in KIND |- *. rewrite SK, RB, SB, SD, SL, SHI, SW.
      destruct (vr_kind r) as [cid fl| |owner|sbase|] eqn:K.
      + destruct KIND as (F1 & F2 & F3 & F4 & F5 & pos & Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
        exists pos. split; [exact Q1|]. split; [exact Q2|]. rewrite NF. split; [exact Q3|]. split; [|split; [exact Q5|exact LIVE']].
        destruct Q4 as (bb & Hb & Hb1). exists bb. split; [|exact Hb1]. rewrite FLG. exact Hb.
      + destruct KIND as (F1 & F2 & i & Hi & Hb & HW). split; [exact F1|]. split; [exact F2|].
        exists i. split; [exact Hi|]. split; [exact Hb|]. exact HW.
      + destruct KIND as (F1 & F2 & F3 & F4 & ro & cid & fl & Gq & KO & HB).
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact FLC|].
        destruct (GET _ _ Gq ltac:(rewrite KO; exact I) eq_refl) as (ro' & G' & SH' & _). exists ro', cid, fl. split; [exact G'|].
        destruct SH' as (_ & _ & SK' & _). rewrite SK'. auto.
      + destruct KIND as (F1 & F2 & F3 & F4 & F5 & F6).
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
        intros N1 N2 N3. destruct (F6 N1 N2 N3) as (ro & Gq & B8 & M).
        destruct (GET _ _ Gq ltac:(destruct (vr_kind ro); auto) eq_refl) as (ro' & G' & SH' & NB'). exists ro'. split; [exact G'|].
        pose proof SH' as (SB' & SD' & SK' & SL' & SHI' & SW' & S8'). rewrite S8', SK'.
        assert (RB' : rbase nu' ro' = rbase nu ro) by (unfold rbase; rewrite SD', SB', NB'; reflexivity). rewrite RB', NB.
        split; [exact B8|]. exact M.
      + exact KIND.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section PostCall2.
    Variable V : vunit2.
    Hypothesis VIN : In V done.
    Let PV := unit_params2 G V.
    Variables (A Am : vstate2) (spoff npc : Z) (sigma0 sigma : pmap lin) (skip8 : list sym) (B : vstate2).
    Hypothesis EAm : am_is A Am.
    Let A0 := set_reg2 Am 1 (Some (lconst npc)).
    Let S := load_cstate2 P (u2_pre V) (u_entry (u1 V)) [].
    Let sigma00 := sigma_sregs (v1 A0) sreg_idx (pm_set RA (lconst npc) pm_empty).
    Hypothesis PRE : prebind_args A0 (cs_rgn (u2_pre V)) (cs_divdef (u2_pre V)) sigma00 = Some (sigma0, skip8).
    Hypothesis MATCH : match_state2 isv_call2 is_sreg_key true MM_call sigma0 (drop_divdefs skip8 S) A0 = MOk sigma.
    Hypothesis NPC : 0 <= npc < 2 ^ 64.
    Hypothesis SIGB : sigma_below sigma (vs2_next A0).
    Hypothesis FP : footprint_ok2 D A0 sigma V spoff = true.
    Hypothesis ROOT : u_root (u1 V) = None.
    Hypothesis SPO : sp_offset (v1 A) = Some spoff.
    Hypothesis CB : call_base2 D A0 V sigma spoff npc = Some B.

    Variables (nu1 : val) (regs1 : bvmap 5 word) (mem1 : word -> option byte).
    Hypothesis HGm : gammaP A0 nu1 regs1 mem1.
    Variable L : list (Z * Z).
    Hypothesis HL : fake_slots_of Am npc nu1 mem1 L.
    Let nuV := vsubst nu1 sigma.
    Let EV := callee_env2 npc nuV L.

    (* [comment removed for export] *)
    Variables (X : cstate2) (nuV' : val) (regs2 : bvmap 5 word) (mem2 : word -> option byte).
    Let SX := load_cstate2 PV X npc [].
    Hypothesis XIN : In X (u2_exits V).
    Hypothesis XG : gamma2 SEGS PV EV mem0 SX nuV' regs2 mem2.
    Hypothesis XEXT : ext FIRST_FRESH2 nuV nuV'.
    Hypothesis XRA : getr regs2 1%bv = wordZ npc.
    Hypothesis XREGS : exit_regs2 G V nuV regs2.
    Hypothesis XFM : frame_mod mem1 mem2 (unit_regions2 PV EV).
    Hypothesis XFL : forall a, in_flags_zone PV EV a -> mem2 (wordZ a) = mem1 (wordZ a).

    (* [comment removed for export] *)
    Variables (b b' : positive) (nJ : nat).
    Hypothesis HB : b = vs2_next A0.
    Hypothesis HJ0 : (FIRST_FRESH2 <= b)%positive.
    Hypothesis NX : Z.pos (cs_next (c1 X)) = Z.pos FIRST_FRESH2 + Z.of_nat nJ.
    Hypothesis HB' : Z.pos b' = Z.pos b + Z.of_nat nJ.
    Let sigmax := sigma_joins FIRST_FRESH2 b nJ sigma.
    Definition nu2x : val := fun s =>
      let k := Z.pos s - Z.pos b in
      if Z.leb 0 k && Z.ltb k (Z.of_nat nJ) then nuV' (Z.to_pos (Z.pos FIRST_FRESH2 + k)) else nu1 s.

    Hypothesis GV : gamma2 SEGS PV EV mem0 S nuV regs1 mem1.
    Hypothesis SUB0 : sub_sigma sigma00 sigma.
    Hypothesis BO0 : binds_only isv_call2 sigma00 sigma.

    Lemma nu2x_old s : (s < b)%positive -> nu2x s = nu1 s.
    Proof using . intros Hs. unfold nu2x. destruct (Z.leb_spec 0 (Z.pos s - Z.pos b)) as [Y|Y]; [exfalso; clear -Hs Y; lia|reflexivity]. Qed.

    Lemma X_static2 : cstate2_ok PV X = true /\ cstate2_iface_b X = true /\ wrgn_ok V X = true.
    Proof using DONE VIN XIN. destruct (V_static2 V VIN) as (_ & _ & _ & _ & ST & _). exact (ST X XIN). Qed.

    Lemma XBEL : state_below (v1 SX) /\ (FIRST_FRESH2 <= cs_next (c1 X))%positive.
    Proof using DONE PV VIN XIN npc.
      destruct X_static2 as (XOK & _). destruct (load_cstate2_v1_facts PV X npc [] XOK) as (_ & _ & B1 & B2). split; [exact B1|exact B2].
    Qed.

    Lemma nu2x_join s : (FIRST_FRESH2 <= s)%positive -> (s < cs_next (c1 X))%positive -> vsubst nu2x sigmax s = nuV' s.
    Proof using HB' NX sigma.
      intros H1 H2. pose proof NX as NX'. pose proof HB' as HB''. clear - H1 H2 NX' HB''.
      unfold vsubst, sigmax, nu2x. rewrite sigma_joins_get.
      destruct (Z.leb_spec (Z.pos FIRST_FRESH2) (Z.pos s)); [|lia]. destruct (Z.ltb_spec (Z.pos s) (Z.pos FIRST_FRESH2 + Z.of_nat nJ)); [|lia].
      simpl. rewrite eval_lsym.
      replace (Z.pos (Z.to_pos (Z.pos b + (Z.pos s - Z.pos FIRST_FRESH2))) - Z.pos b) with (Z.pos s - Z.pos FIRST_FRESH2) by lia.
      destruct (Z.leb_spec 0 (Z.pos s - Z.pos FIRST_FRESH2)); [|lia]. destruct (Z.ltb_spec (Z.pos s - Z.pos FIRST_FRESH2) (Z.of_nat nJ)); [|lia].
      simpl. f_equal. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma lsubst_eval_x e :
      lin_below e (cs_next (c1 X)) = true -> eval nu2x (lsubst sigmax e) = eval nuV' e.
    Proof using HB HB' HJ0 NX SIGB XEXT.
      intros Hb. apply eval_lsubst_agree'. intros s Hs.
      pose proof (proj1 (lin_below_iff _ _) Hb s Hs) as Hsb.
      destruct (Pos.ltb_spec s FIRST_FRESH2) as [Hlo|Hhi]; [|apply nu2x_join; auto].
      unfold vsubst, sigmax. rewrite sigma_joins_get.
      destruct (Z.leb_spec (Z.pos FIRST_FRESH2) (Z.pos s)); [exfalso; clear -Hlo H; lia|]. simpl.
      rewrite (XEXT s Hlo). unfold nuV, vsubst.
      destruct (pm_get s sigma) as [es|] eqn:Gs.
      - apply eval_ext. intros s' Hs'. apply nu2x_old. rewrite HB. exact (proj1 (lin_below_iff _ _) (SIGB _ _ Gs) s' Hs').
      - apply nu2x_old. clear -Hlo HJ0. unfold FIRST_FRESH2 in *. lia.
    Qed.

    Lemma osubst2_eval e e' :
      lin_below e (cs_next (c1 X)) = true -> osubst2 sigmax e = Some e' -> eval nu2x e' = eval nuV' e.
    Proof using HB HB' HJ0 NX SIGB XEXT.
      intros Hb Ho. unfold osubst2 in Ho.
      match type of Ho with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
      inversion Ho; subst e'. apply lsubst_eval_x; auto.
    Qed.

    Lemma nu2x_new s : (FIRST_FRESH2 <= s)%positive -> (s < cs_next (c1 X))%positive ->
      nu2x (Z.to_pos (Z.pos b + (Z.pos s - Z.pos FIRST_FRESH2))) = nuV' s.
    Proof using NX.
      intros H1 H2. pose proof NX as NX'. clear - H1 H2 NX'. unfold nu2x.
      replace (Z.pos (Z.to_pos (Z.pos b + (Z.pos s - Z.pos FIRST_FRESH2))) - Z.pos b) with (Z.pos s - Z.pos FIRST_FRESH2) by lia.
      destruct (Z.leb_spec 0 (Z.pos s - Z.pos FIRST_FRESH2)); [|lia]. destruct (Z.ltb_spec (Z.pos s - Z.pos FIRST_FRESH2) (Z.of_nat nJ)); [|lia].
      simpl. f_equal. lia.
    Qed.

    Lemma ext_b : ext b nu1 nu2x.
    Proof using . intros s Hs. apply nu2x_old. exact Hs. Qed.

    Lemma sigmax_below : sigma_below sigmax b'.
    Proof using HB HB' SIGB.
      intros s e. unfold sigmax. rewrite sigma_joins_get.
      destruct (Z.leb (Z.pos FIRST_FRESH2) (Z.pos s) && Z.ltb (Z.pos s) (Z.pos FIRST_FRESH2 + Z.of_nat nJ)) eqn:C.
      - intros Y; inversion Y; subst e. apply lin_below_lsym. apply andb_prop in C as [C1 C2].
        apply Z.leb_le in C1. apply Z.ltb_lt in C2. clear -C1 C2 HB'. lia.
      - intros Gs. eapply lin_below_mono; [|exact (SIGB _ _ Gs)]. clear -HB HB'. subst b. lia.
    Qed.

    Lemma lsubst_x_below e : lin_below e (cs_next (c1 X)) = true -> lin_below (lsubst sigmax e) b' = true.
    Proof using HB HB' HJ0 NX SIGB.
      intros Hb. apply lsubst_below; [apply sigmax_below|].
      intros s Hs Hn. pose proof (proj1 (lin_below_iff _ _) Hb s Hs) as SB. pose proof NX as NX'. pose proof HB' as HB''. pose proof HJ0 as HJ0'.
      clear - SB Hn NX' HB'' HJ0'.
      unfold sigmax in Hn. rewrite sigma_joins_get in Hn.
      destruct (Z.leb_spec (Z.pos FIRST_FRESH2) (Z.pos s)); destruct (Z.ltb_spec (Z.pos s) (Z.pos FIRST_FRESH2 + Z.of_nat nJ)); simpl in Hn; try discriminate; lia.
    Qed.

    Lemma osubst2_below e e' : lin_below e (cs_next (c1 X)) = true -> osubst2 sigmax e = Some e' -> lin_below e' b' = true.
    Proof using HB HB' HJ0 NX SIGB.
      intros Hb Ho. unfold osubst2 in Ho.
      match type of Ho with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
      inversion Ho; subst e'. apply lsubst_x_below; auto.
    Qed.

    Lemma store_below_add_in_itv2 S0 c i S1 :
      store_below S0 b' = true -> lin_below c b' = true -> add_in_itv S0 c i = Some S1 -> store_below S1 b' = true.
    Proof using HB HB' HJ0 sigma.
      intros H1 H2. unfold add_in_itv.
      destruct (snd i) as [hi|].
      - destruct (add_constraint S0 (laddc c (- hi))) as [S2|] eqn:E1; [|discriminate].
        pose proof (store_below_add_constraint _ _ _ _ H1 (lin_below_laddc _ _ _ H2) E1) as H3.
        destruct (fst i) as [lo|]; [|intros Y; inversion Y; now subst].
        intros E2. eapply store_below_add_constraint; [exact H3| |exact E2].
        apply lin_below_laddc, lin_below_lneg, H2.
      - destruct (fst i) as [lo|]; [|intros Y; inversion Y; now subst].
        intros E2. eapply store_below_add_constraint; [exact H1| |exact E2].
        apply lin_below_laddc, lin_below_lneg, H2.
    Qed.

    Lemma add_boxes2_sound : forall l S0,
      sat nu2x S0 -> store_below S0 b' = true ->
      (forall s i, In (s, i) l -> pm_get s (sbox (vs_store (v1 SX))) = Some i) ->
      exists S1, add_boxes2 S0 sigmax l = Some S1 /\ sat nu2x S1 /\ store_below S1 b' = true.
    Proof using DONE HB HB' HJ0 NX SIGB VIN XEXT XG XIN.
      pose proof (gamma2_v1 _ _ _ _ _ _ _ _ XG) as XG1.
      induction l as [|[s i] t IH]; intros S0 HS HSB Hl; simpl; [eauto|].
      assert (Hsi : pm_get s (sbox (vs_store (v1 SX))) = Some i) by (apply Hl; now left).
      assert (Hin : in_itv (nuV' s) i).
      { destruct XG1 as (_&_&_&XS&_). exact (sat_box _ _ XS _ _ Hsi). }
      assert (Hs : (s < cs_next (c1 X))%positive).
      { destruct XBEL as [(_&SB&_) _]. eapply store_below_sound; [exact SB|]. left. eauto. }
      destruct (isv_join2 s) eqn:J.
      - unfold isv_join2 in J. apply Pos.leb_le in J.
        unfold sigmax at 1. rewrite sigma_joins_get.
        destruct (Z.leb_spec (Z.pos FIRST_FRESH2) (Z.pos s)); [|exfalso; clear -J H; lia]. destruct (Z.ltb_spec (Z.pos s) (Z.pos FIRST_FRESH2 + Z.of_nat nJ)); [|exfalso; clear -H0 Hs NX; lia].
        simpl. apply IH; [| |intros; apply Hl; now right].
        + apply sat_set_box; [exact HS|]. rewrite nu2x_new; auto.
        + apply store_below_set_box; [exact HSB|]. clear -H H0 HB' NX J Hs. unfold FIRST_FRESH2 in *. lia.
      - destruct (osubst2 sigmax (lsym s)) as [e|] eqn:Ho; [|apply IH; auto; intros; apply Hl; now right].
        assert (He : eval nu2x e = nuV' s).
        { rewrite (osubst2_eval _ _ (lin_below_lsym _ _ Hs) Ho). apply eval_lsym. }
        destruct (sat_add_in_itv nu2x S0 e i HS) as [S1 [E1 HS1]]; [rewrite He; exact Hin|].
        rewrite E1. apply IH; [exact HS1| |intros; apply Hl; now right].
        eapply store_below_add_in_itv2; [exact HSB| |exact E1]. eapply osubst2_below; [apply lin_below_lsym; exact Hs|exact Ho].
    Qed.

    Lemma add_congs2_sound : forall l S0,
      sat nu2x S0 -> store_below S0 b' = true ->
      (forall s mr, In (s, mr) l -> pm_get s (scong (vs_store (v1 SX))) = Some mr) ->
      exists S1, add_congs2 S0 sigmax l = Some S1 /\ sat nu2x S1 /\ store_below S1 b' = true.
    Proof using DONE HB' NX VIN XG XIN.
      pose proof (gamma2_v1 _ _ _ _ _ _ _ _ XG) as XG1.
      induction l as [|[s [m r]] t IH]; intros S0 HS HSB Hl; simpl; [eauto|].
      assert (Hsi : pm_get s (scong (vs_store (v1 SX))) = Some (m, r)) by (apply Hl; now left).
      assert (Hd : (m | nuV' s - r)).
      { destruct XG1 as (_&_&_&XS&_). exact (sat_cong _ _ XS _ _ _ Hsi). }
      assert (Hs : (s < cs_next (c1 X))%positive).
      { destruct XBEL as [(_&SB&_) _]. eapply store_below_sound; [exact SB|]. right; right. eauto. }
      destruct (isv_join2 s) eqn:J; [|apply IH; auto; intros; apply Hl; now right].
      unfold isv_join2 in J. apply Pos.leb_le in J.
      unfold sigmax at 1. rewrite sigma_joins_get.
      destruct (Z.leb_spec (Z.pos FIRST_FRESH2) (Z.pos s)); [|exfalso; clear -J H; lia]. destruct (Z.ltb_spec (Z.pos s) (Z.pos FIRST_FRESH2 + Z.of_nat nJ)); [|exfalso; clear -H0 Hs NX; lia].
      simpl.
      destruct (sat_add_cong nu2x S0 (Z.to_pos (Z.pos b + (Z.pos s - Z.pos FIRST_FRESH2))) m r HS) as [S1 [E1 HS1]]; [rewrite nu2x_new; auto|].
      rewrite E1. apply IH; [exact HS1| |intros; apply Hl; now right].
      eapply store_below_add_cong; [exact HSB| |exact E1]. clear -H H0 HB' NX J Hs. unfold FIRST_FRESH2 in *. lia.
    Qed.

    Lemma add_conss2_sound : forall l S0,
      sat nu2x S0 -> store_below S0 b' = true ->
      (forall c, In c l -> In c (scons (vs_store (v1 SX)))) ->
      exists S1, add_conss2 S0 sigmax l = Some S1 /\ sat nu2x S1 /\ store_below S1 b' = true.
    Proof using DONE HB HB' HJ0 NX SIGB VIN XEXT XG XIN.
      pose proof (gamma2_v1 _ _ _ _ _ _ _ _ XG) as XG1.
      induction l as [|c t IH]; intros S0 HS HSB Hl; simpl; [eauto|].
      assert (Hc : In c (scons (vs_store (v1 SX)))) by (apply Hl; now left).
      assert (Hle : eval nuV' c <= 0).
      { destruct XG1 as (_&_&_&XS&_). exact (sat_cons_in _ _ _ XS Hc). }
      assert (Hcb : lin_below c (cs_next (c1 X)) = true).
      { destruct XBEL as [(_&SB&_) _]. apply (proj2 (lin_below_iff _ _)). intros s Hs.
        eapply store_below_sound; [exact SB|]. right; left. eauto. }
      destruct (osubst2 sigmax c) as [c'|] eqn:Ho; [|apply IH; auto; intros; apply Hl; now right].
      pose proof (osubst2_eval _ _ Hcb Ho) as He.
      destruct (lin_is_const c') eqn:Hk.
      - rewrite (eval_is_const nu2x c' Hk) in He.
        destruct (Z.leb_spec (lc c') 0); [|exfalso; clear -He Hle H; lia]. apply IH; auto. intros; apply Hl; now right.
      - destruct (sat_add_constraint nu2x S0 c' HS) as [S1 [E1 HS1]]; [clear -He Hle; lia|].
        rewrite E1. apply IH; [exact HS1| |intros; apply Hl; now right].
        eapply store_below_add_constraint; [exact HSB| |exact E1]. eapply osubst2_below; eauto.
    Qed.

    (* [comment removed for export] *)
    Lemma kept_reg (r : reg) e :
      rz r <> 0 -> (rz r = 2 \/ rz r = 3 \/ rz r = 4 \/ In (rz r) (map fst sreg_idx)) ->
      pm_get (reg_key (rz r)) (vs_regs (v1 A0)) = Some e ->
      bv_unsigned (getr regs2 r) = zwrap 64 (eval nu1 e).
    Proof using DONE GV HGm VIN XREGS.
      intros Hr0 Hin Hg.
      pose proof (gamma2_v1 _ _ _ _ _ _ _ _ HGm) as (_&_&_&_&_&_&_&HR&_). rewrite <- (HR r e Hr0 Hg).
      pose proof (gamma2_v1 _ _ _ _ _ _ _ _ GV) as (_&_&_&_&_&_&_&GR&_).
      destruct (V_static2 V VIN) as (_ & _ & _ & PC & _). unfold pre_canonical2 in PC.
      apply andb_prop in PC as [PC P4]. apply andb_prop in PC as [PC P3]. apply andb_prop in PC as [PC P5]. apply andb_prop in PC as [P1 P2].
      change (v1 (load_cstate2 (unit_params2 G V) (u2_pre V) (u_entry (u1 V)) [])) with (v1 S) in P2, P3, P4, P5.
      destruct XREGS as (X2 & X3 & X4 & X5).
      assert (GETS : forall (z : Z) (l : lin), rz r = z -> absval_eqb (get_reg (v1 S) z) l = true ->
                     bv_unsigned (getr regs1 r) = zwrap 64 (eval nuV l)).
      { intros z l Hz Hb. unfold absval_eqb, get_reg in Hb. rewrite <- Hz in Hb.
        destruct (Z.eqb_spec (rz r) 0); [exfalso; exact (Hr0 e0)|].
        destruct (pm_get (reg_key (rz r)) (vs_regs (v1 S))) as [l'|] eqn:G'; [|discriminate]. apply lin_eqb_eq in Hb. subst l'.
        exact (GR r l Hr0 G'). }
      destruct Hin as [H|[H|[H|Hin]]].
      - assert (r = 2%bv) by (apply bv_eq; unfold rz in H; rewrite H; reflexivity). subst r.
        rewrite (GETS 2 _ eq_refl P2), eval_lsymc. exact X2.
      - assert (r = 3%bv) by (apply bv_eq; unfold rz in H; rewrite H; reflexivity). subst r.
        rewrite (GETS 3 _ eq_refl P3), eval_lsym. exact X3.
      - assert (r = 4%bv) by (apply bv_eq; unfold rz in H; rewrite H; reflexivity). subst r.
        rewrite (GETS 4 _ eq_refl P4), eval_lconst. exact X4.
      - apply in_map_iff in Hin as [[ri i] [Hri Hin]]. simpl in Hri. subst ri.
        unfold sregs_intact in P5. rewrite forallb_forall in P5. specialize (P5 _ Hin). simpl in P5.
        rewrite (GETS _ _ eq_refl P5), eval_lsym.
        assert (r = Z_to_bv 5 (rz r)) by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range).
        rewrite H. apply X5. exact Hin.
    Qed.

    Lemma reg_upd_get2 m r v k e :
      pm_get k (reg_upd m r v) = Some e ->
      (k = reg_key r /\ v = Some e) \/ (k <> reg_key r /\ pm_get k m = Some e).
    Proof using HB HB' HJ0 sigma.
      unfold reg_upd. destruct v as [e'|]; [rewrite pm_get_set|rewrite pm_get_remove]; destruct (Pos.eqb_spec k (reg_key r)); intros Hg.
      - left. inversion Hg; subst; auto.
      - right; auto.
      - discriminate.
      - right; auto.
    Qed.

    Lemma reg_key_eq2 a1 a2 : 0 < a1 -> 0 < a2 -> reg_key a1 = reg_key a2 -> a1 = a2.
    Proof using . unfold reg_key. clear. intros. lia. Qed.

    Lemma rz_pos_of2 (r : reg) : rz r <> 0 -> 0 < rz r < 32.
    Proof using . clear. intros H. pose proof (bv_unsigned_in_range 5 r) as R. unfold bv_modulus in R. unfold rz in *. simpl in R. lia. Qed.

    (* [comment removed for export] *)
    Lemma wcells_V_in_P c : In c (vp_wcells (p1 PV)) -> exists c', In c' (vp_wcells (p1 P)) /\ fst c' <= fst c /\ fst c + snd c <= fst c' + snd c'.
    Proof using D1 FP.
      destruct (footprint_ok2_v1 _ _ _ _ FP) as [FP1 _].
      unfold PV, P, unit_params2, unit_wcells2. cbn [p1 vp_wcells]. intros Hin.
      unfold footprint_ok in FP1. change (de_U D1) with (u1 U) in FP1. change (de_P D1) with (p1 P) in FP1.
      apply andb_prop in FP1 as [FP1 FE]. apply andb_prop in FP1 as [FP1 FG].
      apply in_app_iff in Hin as [Hin|Hin].
      - destruct (u_errno (u1 V)) eqn:EV'; [|destruct Hin]. simpl in FE. destruct Hin as [<-|[]].
        destruct (u_errno (u1 U)) eqn:EU; [|discriminate].
        exists (ci_errno (ge2_CI G), 4). simpl. split; [|clear; lia]. now left.
      - rewrite forallb_forall in FG. specialize (FG _ Hin). apply in_cells_sound in FG as [c' (H1&H2&H3)].
        exists c'. auto.
    Qed.

    Lemma wcells_PV_bound c : In c (vp_wcells (p1 PV)) -> 0 <= fst c /\ fst c + snd c <= vp_splo (p1 P) - vp_frame (p1 P).
    Proof using D1 FP PO.
      intros Hc. destruct (wcells_V_in_P _ Hc) as [c' (C1&C2&C3)].
      pose proof PO1 as (_&_&_&PF&PWC&_). destruct (PWC _ C1) as [f (F1&F2&F3)]. destruct (PF _ F1) as (G1'&G2&_).
      change (vp_splo (unit_params G1 (u1 U))) with (vp_splo (p1 P)) in G2. change (vp_frame (unit_params G1 (u1 U))) with (vp_frame (p1 P)) in G2.
      clear - C2 C3 F2 F3 G1' G2. lia.
    Qed.

    Lemma wstack_V_bound lo hi : In (lo, hi) (u_wstack (u1 V)) -> - vp_frame (p1 P) <= lo.
    Proof using DONE U VIN.
      intros Hr. destruct (unit_static_ok2_wsets _ _ _ (proj1 (V_ok2 V VIN))) as (W1 & _).
      rewrite forallb_forall in W1. specialize (W1 _ Hr). cbn [fst snd] in W1.
      apply andb_prop in W1 as [W1 _]. apply andb_prop in W1 as [W1 _]. apply Z.leb_le in W1. exact W1.
    Qed.

    (* [comment removed for export] *)
    Lemma extras_apart rb rn (a : word) :
      In (rb, rn) (arg_regions PV EV ++ (match vp_fs PV with None => [] | Some _ => stack_shadow_regions PV EV end) ++ fs_regions PV EV) ->
      in_rng a rb rn ->
      (~ (e_sp0 (ev1 E) - vp_frame (p1 P) <= bv_unsigned a < e_sp0 (ev1 E))
       /\ (forall c, In c (vp_fcells (p1 P)) -> ~ (fst c <= bv_unsigned a < fst c + snd c)))
      /\ vp_fs P <> None.
    Proof using D1 DONE FP HB HGm L NPC PO VIN X b' mem_e nJ nuV.
      intros Hin Hrng.
      match goal with |- ?G /\ _ => enough (MAINA : G /\ vp_fs P <> None) by exact MAINA end.
      pose proof HGm as (HV1 & HE2 & HMC2 & HF2 & HDD & HRG & HLV & HB2 & _). pose proof HV1 as (HE & _).
      pose proof HE2 as (_ & _ & HFS & [ZW ZA] & _).
      destruct HE as (E16 & Esp & _ & _ & _ & _ & _ & _ & _ & _ & Efr).
      pose proof PO1 as (Pfr & Psphi & _ & PFC & _).
      assert (X1 : e_sp0 (ev1 E) < 2 ^ 64) by (eapply Z.le_lt_trans; [exact (proj2 Esp)|exact Psphi]).
      assert (X2 : vp_frame (p1 P) <= e_sp0 (ev1 E)) by exact Efr.
      assert (X3 : 0 <= vp_frame (p1 P)) by exact Pfr.
      pose proof (PO2_shoff SEGS P PO) as SH0.
      apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
      - (* [comment removed for export] *)
        unfold arg_regions in Hin. apply in_map_iff in Hin as [[i [lo hi]] [Eb Hw]]. injection Eb as Eb1 Eb2. subst rb rn.
        destruct (footprint_ok2_v1 _ _ _ _ FP) as [_ WAD]. rewrite forallb_forall in WAD. specialize (WAD _ Hw). unfold wrgn_admissible in WAD.
        destruct (resolve_base isv_call2 A0 sigma (ASYM2 i)) as [[bq c]|] eqn:RS; [|discriminate].
        destruct (rgn_get (vs_rgn A0) bq) as [pr|] eqn:Gpr; [|discriminate].
        apply andb_prop in WAD as [WD WAD]. apply Z.eqb_eq in WD. destruct (rgn_get_in _ _ _ Gpr) as [Hpr Bpr].
        assert (KNF : is_data_shadow pr = false /\ in_ranges (vr_w pr) (lo + c) (hi - lo) = true).
        { unfold is_data_shadow. destruct (vr_kind pr); try discriminate; auto. }
        destruct KNF as [NDS IR].
        pose proof (HRG _ Hpr) as (PB1 & PB2 & _ & _ & _ & PRP & _). destruct (PRP NDS) as [_ RP2].
        destruct (in_ranges_sound _ _ _ IR) as (lo2 & hi2 & Hw2 & Z1 & Z2).
        assert (EA : nth (Z.to_nat i) (e_args EV) 0 = nu1 bq + c).
        { destruct (unit_static_ok2_wsets _ _ _ (proj1 (V_ok2 V VIN))) as (_ & _ & _ & W4). rewrite forallb_forall in W4.
          specialize (W4 _ Hw). cbn [fst snd] in W4. apply andb_prop in W4 as [W4 _]. apply andb_prop in W4 as [W4a W4b].
          apply Z.leb_le in W4a. apply Z.ltb_lt in W4b.
          cbn [e_args EV callee_env2]. erewrite nth_error_nth; [|rewrite nth_error_map, nth_error_seq;
            destruct (PeanoNat.Nat.ltb_spec (Z.to_nat i) 8); [reflexivity|lia]]. cbn.
          replace (ASYM2 (Z.of_nat (Z.to_nat i))) with (ASYM2 i) by (unfold ASYM2; f_equal; lia).
          exact (RB_eval _ _ _ _ _ _ _ (resolve_base_spec _ _ _ _ _ _ RS)). }
        assert (Hrng' : in_rng a (wordZ (nu1 bq + c + lo)) (hi - lo)) by (rewrite <- EA; exact Hrng). clear Hrng.
        unfold in_rng in Hrng'. unfold rbase in PB1, PB2, RP2. rewrite WD, Bpr in PB1, PB2, RP2.
        destruct (Z.lt_ge_cases lo hi) as [LH|LH].
        2:{ exfalso. clear - Hrng' LH. lia. }
        destruct (RP2 lo2 hi2 (lo + c) Hw2 ltac:(clear -Z1 Z2 LH; lia)) as (Q0 & _).
        rewrite u_wordZ in Hrng' by (clear -Q0 PB1 PB2; lia).
        destruct (RP2 lo2 hi2 (bv_unsigned a - nu1 bq) Hw2 ltac:(clear -Z1 Z2 Hrng'; lia)) as (_ & ZN & _).
        destruct (in_rw_zones_in P E _ ZN) as (z & Hz & _ & Hinz).
        destruct (ZA z _ Hz Hinz) as (N1 & N2 & _).
        replace (0 + nu1 bq + (bv_unsigned a - nu1 bq)) with (bv_unsigned a) in N1, N2 by (clear; lia).
        split; [|unfold kind_ok in PRP; pose proof (HRG _ Hpr) as (_ & _ & _ & _ & _ & _ & _ & PK); unfold kind_ok in PK; destruct (vr_kind pr); try discriminate; exact (proj1 PK)].
        split; [exact N1|]. intros c0 Hc0. exact (N2 c0 Hc0).
      - (* [comment removed for export] *)
        change (vp_fs PV) with (vp_fs P) in Hin. unfold env_fs in HFS.
        destruct (vp_fs P) as [[len ssl]|] eqn:EFS; [|destruct Hin].
        destruct HFS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C11 & _ & _ & C14 & _).
        destruct (PO2_fs SEGS P PO ltac:(rewrite EFS; discriminate)) as [SHV FCL].
        unfold stack_shadow_regions in Hin. apply in_map_iff in Hin as [[lo hi] [Eb Hr]]. cbn [fst snd] in Eb. injection Eb as Eb1 Eb2. subst rb rn.
        cbn [ev1 EV callee_env2 callee_env e_sp0] in Hrng. change (vp_shoff (ge2_P0 G)) with (vp_shoff P) in Hrng.
        assert (W : - vp_frame (p1 P) <= lo /\ hi <= 0).
        { cbn in Hr. destruct Hr as [Hr|[]].
          injection Hr as <- <-. destruct (unit_static_ok2_wsets _ _ _ (proj1 (V_ok2 V VIN))) as (_ & _ & W3 & _).
          apply Bool.orb_false_elim in W3 as [W3a W3b]. apply Z.ltb_ge in W3a. apply Z.ltb_ge in W3b.
          change (vp_frame (p1 (ge2_P0 G))) with (vp_frame (p1 P)). split; [clear; lia|exact W3a]. }
        destruct W as [Wlo Whi]. unfold in_rng in Hrng. split; [|discriminate].
        destruct (Z.lt_ge_cases lo hi) as [LH|LH].
        2:{ exfalso. assert ((hi - lo) / 8 <= 0) by (apply Z.div_le_upper_bound; clear -LH; lia). clear - H Hrng. lia. }
        assert (B0 : 0 <= vp_shoff P + (e_sp0 (ev1 E) + lo) / 8 < 2 ^ 64).
        { split; [apply Z.add_nonneg_nonneg; [exact SH0|apply Z.div_pos; clear -Wlo X2 X3; lia]|].
          assert ((e_sp0 (ev1 E) + lo) / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; clear -X1 LH Whi; lia). clear -H SHV. lia. }
        rewrite u_wordZ in Hrng by exact B0.
        assert (UB : (e_sp0 (ev1 E) + lo) / 8 + (hi - lo) / 8 <= e_sp0 (ev1 E) / 8).
        { apply (Z.le_trans _ ((e_sp0 (ev1 E) + lo + (hi - lo)) / 8)).
          - apply Z.div_le_lower_bound; [clear; lia|].
            pose proof (Z.mul_div_le (e_sp0 (ev1 E) + lo) 8 ltac:(clear; lia)). pose proof (Z.mul_div_le (hi - lo) 8 ltac:(clear; lia)). clear - H H0. lia.
          - apply Z.div_le_mono; clear -Whi; lia. }
        assert (UB2 : e_sp0 (ev1 E) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [clear; lia|]; unfold HIGH_MEM_END in C14; clear -C14; lia).
        unfold HIGH_MEM_BEG in C11. change (vp_frame (p1 (ge2_P0 G))) with (vp_frame (p1 P)) in C11.
        split; [clear - Hrng UB UB2 C11 SHV; lia|].
        assert (DP0 : 0 <= (e_sp0 (ev1 E) + lo) / 8) by (apply Z.div_pos; clear -Wlo X2 X3; lia).
        intros c0 Hc0 XX. specialize (FCL c0 Hc0). clear - Hrng SHV FCL XX DP0. lia.
      - (* [comment removed for export] *)
        rewrite (fs_regions_P PV P) in Hin by reflexivity.
        unfold fs_regions in Hin. unfold env_fs in HFS.
        destruct (vp_fs P) as [[len ssl]|] eqn:EFS; [|destruct Hin].
        destruct HFS as (_ & FLO & FHI & _ & FLEN & _ & _ & C8 & _ & _ & C11 & _ & _ & C14 & _ & CIE).
        destruct (PO2_fs SEGS P PO ltac:(rewrite EFS; discriminate)) as [SHV FCL].
        destruct (PO2_img SEGS P PO ltac:(rewrite EFS; discriminate)) as (IE0 & FCI & _).
        cbn [e_fs e_live EV callee_env2] in Hin.
        unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_FRAMES, FS_NCLASSES, FS_SSL in *. change (vp_frame (p1 (ge2_P0 G))) with (vp_frame (p1 P)) in C8, C11.
        split; [|discriminate].
        assert (GEN : forall lo n0, (e_fs E <= lo /\ lo + n0 <= e_fs E + len) \/ (vp_shoff P <= lo /\ lo + n0 <= vp_shoff P + 2 ^ 44) ->
                       in_rng a (wordZ lo) n0 ->
                       ~ (e_sp0 (ev1 E) - vp_frame (p1 P) <= bv_unsigned a < e_sp0 (ev1 E))
                       /\ (forall c, In c (vp_fcells (p1 P)) -> ~ (fst c <= bv_unsigned a < fst c + snd c))).
        { intros lo n0 CASES R. unfold in_rng in R.
          destruct (Z.lt_ge_cases 0 n0) as [N0|N0]; [|exfalso; clear -R N0; lia].
          destruct CASES as [[Y1 Y2]|[Y1 Y2]].
          - rewrite u_wordZ in R by (clear -Y1 Y2 FLO FHI N0; lia). split; [clear -R Y1 Y2 C8 N0; lia|].
            intros c0 Hc0 XX. specialize (FCI c0 Hc0). clear -R Y1 FLO FCI XX CIE. lia.
          - rewrite u_wordZ in R by (clear -Y1 Y2 SH0 SHV N0; lia). split; [clear -R Y1 Y2 C11 SHV N0; lia|].
            intros c0 Hc0 XX. specialize (FCL c0 Hc0). clear -R Y1 FCL XX SHV. lia. }
        apply in_app_iff in Hin as [Hin|Hin].
        + destruct Hin as [E0|[E0|[]]]; injection E0 as <- <-; (eapply GEN; [|exact Hrng]); left; unfold FS_FLAGS; clear -FLEN; lia.
        + (* [comment removed for export] *)
          assert (CL : forall k, In (rb, rn) (classes_regions P (e_fs E) k (e_live E ++ L)) -> Z.of_nat k <= 5 ->
                       exists cid pos, 0 <= cid < 5 /\ 0 <= pos < fs_nframes cid /\
                         ((rb, rn) = (wordZ (frame_addr (e_fs E) cid pos), fake_size cid)
                          \/ (rb, rn) = (wordZ (vp_shoff P + frame_addr (e_fs E) cid pos / 8), fake_size cid / 8))).
          { induction k as [|k IH]; cbn [classes_regions]; intros H Hk; [destruct H|].
            apply in_app_iff in H as [H|H]; [apply IH; [exact H|clear -Hk; lia]|].
            unfold class_regions in H. apply in_flat_map in H as (pos & Hpos & H).
            apply in_map_iff in Hpos as (pn & <- & Hpn). apply in_seq in Hpn.
            destruct (existsb _ _); [destruct H|].
            exists (Z.of_nat k), (Z.of_nat pn). split; [clear -Hk; lia|]. split; [clear -Hpn; lia|].
            destruct H as [E0|[E0|[]]]; [left|right]; symmetry; exact E0. }
          destruct (CL _ Hin ltac:(cbn; clear; lia)) as (cid & pos & Hc & Hp & CASES).
          pose proof (frame_in_class (e_fs E) cid pos ltac:(clear -Hc; lia) ltac:(clear -Hc; lia) Hp) as [F1 F2].
          pose proof (fake_size_bounds cid ltac:(clear -Hc; lia)) as FB.
          destruct CASES as [E0|E0]; injection E0 as -> ->; (eapply GEN; [|exact Hrng]).
          * left. unfold FS_FRAMES in F1, F2. clear - F1 F2 FB Hc FLEN. lia.
          * right. unfold FS_FRAMES in F1, F2.
            assert (A1 : 0 <= frame_addr (e_fs E) cid pos) by (clear - F1 Hc FLO; lia).
            assert (A2 : frame_addr (e_fs E) cid pos + fake_size cid <= 2 ^ 47) by (clear - F2 Hc FLEN FHI; lia).
            assert (A3 : 0 <= frame_addr (e_fs E) cid pos / 8) by (apply Z.div_pos; [exact A1|clear; lia]).
            assert (A4 : frame_addr (e_fs E) cid pos / 8 + fake_size cid / 8 <= 2 ^ 44).
            { apply (Z.le_trans _ ((frame_addr (e_fs E) cid pos + fake_size cid) / 8)).
              - apply Z.div_le_lower_bound; [clear; lia|].
                pose proof (Z.mul_div_le (frame_addr (e_fs E) cid pos) 8 ltac:(clear; lia)). pose proof (Z.mul_div_le (fake_size cid) 8 ltac:(clear; lia)).
                clear - H H0. lia.
              - apply Z.div_le_upper_bound; [clear; lia|]. clear - A2. lia. }
            change (vp_shoff (ge2_P0 G)) with (vp_shoff P). clear - A3 A4. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma outside_V2 (a len : Z) :
      0 <= a -> a + len <= 2 ^ 64 -> 0 <= len ->
      (e_sp0 (ev1 E) + spoff <= a \/ a + len <= e_sp0 (ev1 E) - vp_frame (p1 P)) ->
      (forall lo hi, In (lo, hi) (u_wstack (u1 V)) -> a + len <= e_sp0 (ev1 E) + lo \/ e_sp0 (ev1 E) + hi <= a) ->
      (forall c, In c (vp_wcells (p1 PV)) -> a + len <= fst c \/ fst c + snd c <= a) ->
      (vp_fs P <> None ->
       (e_sp0 (ev1 E) - vp_frame (p1 P) <= a /\ a + len <= e_sp0 (ev1 E))
       \/ (exists f, In f (vp_fcells (p1 P)) /\ fst f <= a /\ a + len <= fst f + snd f)) ->
      forall i, 0 <= i < len -> outside (wordZ (a + i)) (unit_regions2 PV EV).
    Proof using D1 DONE FP HB HGm L NPC PO VIN X b' mem_e nJ nuV.
      intros Ha Hal Hlen Hst Hws Hwc LOC i Hi.
      destruct (footprint_ok2_v1 _ _ _ _ FP) as [FP1 _].
      (* [comment removed for export] *)
      assert (O1 : outside (wordZ (a + i)) (unit_regions (p1 PV) (ev1 EV))).
      { pose proof (gamma2_v1 _ _ _ _ _ _ _ _ HGm) as (HE&_). destruct HE as (E1&E2'&E3&E4&E5&E6&E7&E8&E9&E10&E11).
        change (vp_frame (p1 P) <= e_sp0 (ev1 E)) in E11.
        pose proof PO1 as (P0'&P1'&_&_&_&PW&_). change (0 <= vp_frame (p1 P)) in P0'.
        assert (X1 : e_sp0 (ev1 E) < 2 ^ 64) by (eapply Z.le_lt_trans; [exact (proj2 E2')|exact P1']).
        unfold unit_regions. apply outside_app. split.
        - change (vp_wstack (p1 PV)) with ((- vp_frame (p1 P), u_sp (u1 V)) :: u_wstack (u1 V)).
          cbn [ev1 EV callee_env2 callee_env e_sp0 map].
          unfold footprint_ok in FP1. change (de_U D1) with (u1 U) in FP1. change (de_P D1) with (p1 P) in FP1.
          apply andb_prop in FP1 as [FP1 _]. apply andb_prop in FP1 as [FP1 _]. apply andb_prop in FP1 as [FP1 FS].
          apply andb_prop in FP1 as [F1 F2]. apply Z.leb_le in F1. apply Z.eqb_eq in F2.
          cbn [outside fst snd]. split.
          + unfold in_rng. rewrite !u_wordZ by (clear - Ha Hal Hi P0' E11 X1; lia). clear - Hst F2 Hi P0' E11. lia.
          + rewrite forallb_forall in FS.
            assert (GENW : forall l,
                      (forall lo hi, In (lo, hi) l -> a + len <= e_sp0 (ev1 E) + lo \/ e_sp0 (ev1 E) + hi <= a) ->
                      (forall r, In r l -> in_ranges (vp_wstack (p1 P)) (fst r) (snd r - fst r) = true) ->
                      outside (wordZ (a + i)) (map (fun r : Z * Z => (wordZ (e_sp0 (ev1 E) + fst r), snd r - fst r)) l)).
            { induction l as [|[lo hi] t IH]; intros Hl1 Hl2; cbn [outside map fst snd]; [exact I|].
              split; [|apply IH; intros; [apply Hl1|apply Hl2]; simpl; auto].
              unfold in_rng. pose proof (Hl1 lo hi ltac:(now left)) as Hr.
              pose proof (Hl2 (lo, hi) ltac:(now left)) as FW1. cbn [fst snd] in FW1.
              apply in_ranges_sound in FW1 as (lo' & hi' & Hin' & L1 & L2).
              pose proof (PW _ Hin') as HW. cbn [fst snd] in HW. change (- vp_frame (p1 P) <= lo' /\ hi' <= 0) in HW.
              pose proof (bv_unsigned_in_range 64 (wordZ (e_sp0 (ev1 E) + lo))) as BR.
              rewrite (u_wordZ (a + i)) by (clear - Ha Hal Hi; lia).
              destruct (Z.lt_decidable lo hi) as [Hlh|Hlh]; [|clear - Hlh BR; lia].
              rewrite !u_wordZ by (clear - HW L1 L2 Hlh P0' E11 X1; lia). clear - Hr Hi Hlh. lia. }
            apply GENW; [exact Hws|exact FS].
        - unfold cells_regions.
          assert (GEN : forall l, (forall c, In c l -> In c (vp_wcells (p1 PV))) ->
                         outside (wordZ (a + i)) (map (fun c : Z * Z => (wordZ (fst c), snd c)) l)).
          { induction l as [|c t IH]; intros Hl; cbn [outside map]; [exact I|]. split; [|apply IH; intros; apply Hl; now right].
            pose proof (Hl c ltac:(now left)) as HcV. specialize (Hwc _ HcV).
            pose proof (wcells_PV_bound _ HcV) as CBW.
            unfold in_rng. pose proof (bv_unsigned_in_range 64 (wordZ (fst c))) as BR.
            rewrite (u_wordZ (a + i)) by (clear - Ha Hal Hi; lia).
            destruct (Z.lt_decidable 0 (snd c)) as [Hc0|Hc0]; [|clear - Hc0 BR; lia].
            rewrite !u_wordZ by (clear - CBW Hc0 P0' E2' E11 X1; lia). clear - Hwc Hi Hc0. lia. }
          apply GEN. auto. }
      apply (proj2 (outside_forall _ _)). intros rb rn Hin Hrng.
      unfold unit_regions2 in Hin. apply in_app_iff in Hin as [Hin|Hin].
      - exact (proj1 (outside_forall _ _) O1 rb rn Hin Hrng).
      - destruct (extras_apart rb rn (wordZ (a + i)) Hin Hrng) as [[N1 N2] FSNZ].
        rewrite u_wordZ in N1, N2 by (clear - Ha Hal Hi; lia).
        destruct (LOC FSNZ) as [[L1 L2]|(f & Hf & L1 & L2)].
        + apply N1. clear - L1 L2 Hi. lia.
        + apply (N2 f Hf). clear - L1 L2 Hi. lia.
    Qed.

    Lemma rdn_unchanged2 (a : Z) (n : nat) :
      0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 ->
      (e_sp0 (ev1 E) + spoff <= a \/ a + Z.of_nat n <= e_sp0 (ev1 E) - vp_frame (p1 P)) ->
      (forall lo hi, In (lo, hi) (u_wstack (u1 V)) -> a + Z.of_nat n <= e_sp0 (ev1 E) + lo \/ e_sp0 (ev1 E) + hi <= a) ->
      (forall c, In c (vp_wcells (p1 PV)) -> a + Z.of_nat n <= fst c \/ fst c + snd c <= a) ->
      (vp_fs P <> None ->
       (e_sp0 (ev1 E) - vp_frame (p1 P) <= a /\ a + Z.of_nat n <= e_sp0 (ev1 E))
       \/ (exists f, In f (vp_fcells (p1 P)) /\ fst f <= a /\ a + Z.of_nat n <= fst f + snd f)) ->
      rdn SEGS mem2 (wordZ a) n = rdn SEGS mem1 (wordZ a) n.
    Proof using D1 DONE FP HB HGm NPC PO VIN X XFM b' mem_e nJ.
      intros Ha Han Hst Hws Hwc LOC. apply (rdn_same_outside SEGS mem1 mem2 (unit_regions2 PV EV) a n XFM); [clear -Ha; lia|exact Han|].
      intros i Hi. apply (outside_V2 a (Z.of_nat n) (proj1 Ha) Han ltac:(clear; lia) Hst Hws Hwc LOC i Hi).
    Qed.

    Lemma call_base2v_shape (Ax : vstate) :
      let Bx := call_base2v (ge2_CI G) Ax (u1 V) spoff npc in
      vs_store Bx = vs_store Ax /\ vs_next Bx = vs_next Ax /\ vs_conddef Bx = vs_conddef Ax /\ vs_moddef Bx = vs_moddef Ax
      /\ vs_valset Bx = vs_valset Ax /\ vs_pc Bx = npc
      /\ vs_regs Bx = pm_set (reg_key 1) (lconst npc) (regs_tops (vs_regs Ax) CALLER_SAVED)
      /\ vs_slots Bx = kill_ranges (cm_kill (vs_slots Ax) STACK_BOTTOM spoff) (u_wstack (u1 V))
      /\ vs_globs Bx = (let gl0 := kill_cells (vs_globs Ax) (u_wglobs (u1 V)) in
                        if u_errno (u1 V) then cm_kill gl0 (ci_errno (ge2_CI G)) (ci_errno (ge2_CI G) + 4) else gl0)
      /\ vs_nul Bx = List.filter (nul_survives spoff (u_wstack (u1 V))) (vs_nul Ax)
      /\ vs_ctx Bx = vs_ctx Ax /\ vs_ghosts Bx = vs_ghosts Ax.
    Proof using . repeat split; reflexivity. Qed.

    (* [comment removed for export] *)
    Lemma loc_untouched fsl y :
      vp_fs P = Some fsl ->
      ( (exists cid pos, In (cid, pos) (e_live E ++ L) /\ 0 <= cid <= 4 /\ 0 <= pos < fs_nframes cid
           /\ frame_addr (e_fs E) cid pos <= y < frame_addr (e_fs E) cid pos + fake_size cid
           /\ (forall i lo hi bq c, In (i, (lo, hi)) (u2_wrgn V) -> resolve_base isv_call2 A0 sigma (ASYM2 i) = Some (bq, c) ->
                 ~ (nu1 bq + c + lo <= y < nu1 bq + c + hi)))
      \/ (exists off, y = vp_shoff P + e_sp0 (ev1 E) / 8 + off /\ - (vp_frame (p1 P) / 8) - 8 <= off < 1
           /\ ~ ((- vp_frame (p1 P)) / 8 <= off < (spoff + 7) / 8))
      \/ (exists cid pos g, In (cid, pos) (e_live E ++ L) /\ 0 <= cid <= 4 /\ 0 <= pos < fs_nframes cid
           /\ y = vp_shoff P + frame_addr (e_fs E) cid pos / 8 + g /\ 0 <= g < fake_size cid / 8) ) ->
      outside (wordZ y) (unit_regions2 PV EV).
    Proof using D1 DONE FP GV HB HGm HL NPC PO PO0 VIN X b' nJ.
      intros EFS LOC.
      (* [comment removed for export] *)
      pose proof HGm as (HV1 & HE2 & HMC2 & HF2 & HDD & HRG & HLV & HB2 & _). pose proof HV1 as (HE & _).
      pose proof HE2 as (_ & _ & HFS & [ZW ZA] & _). unfold env_fs in HFS. rewrite EFS in HFS. destruct fsl as [len ssl].
      destruct HFS as (_ & FLO & FHI & FMOD & FLEN & FVAL & _ & C8 & _ & _ & C11 & _ & _ & C14 & _ & CIE).
      destruct HE as (E16 & Esp & _ & _ & _ & _ & _ & _ & _ & _ & Efr).
      pose proof PO1 as (Pfr & Psphi & _ & PFC & _ & PWS & _).
      assert (X1 : e_sp0 (ev1 E) < 2 ^ 47) by (unfold HIGH_MEM_END in C14; clear - C14; lia).
      assert (X2 : vp_frame (p1 P) <= e_sp0 (ev1 E)) by exact Efr.
      assert (X3 : 0 <= vp_frame (p1 P)) by exact Pfr.
      pose proof (PO2_shoff SEGS P PO) as SH0. destruct (PO2_fs SEGS P PO ltac:(rewrite EFS; discriminate)) as [SHV FCL].
      destruct (PO2_img SEGS P PO ltac:(rewrite EFS; discriminate)) as (IE0 & FCI & _).
      destruct FLO as [FLO0 FLOB]. unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG in FLOB.
      unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_FRAMES, FS_NCLASSES, FS_SSL in *.
      change (vp_frame (p1 (ge2_P0 G))) with (vp_frame (p1 P)) in C8, C11.
      assert (S8 : e_sp0 (ev1 E) mod 8 = 0).
      { pose proof (Z.div_mod (e_sp0 (ev1 E)) 16 ltac:(clear; lia)) as D16. rewrite E16 in D16.
        replace (e_sp0 (ev1 E)) with ((2 * (e_sp0 (ev1 E) / 16)) * 8) by (clear - D16; lia). apply Z_mod_mult. }
      pose proof (Z.div_mod (e_sp0 (ev1 E)) 8 ltac:(clear; lia)) as DS8. rewrite S8, Z.add_0_r in DS8.
      assert (VSL : forall cp, In cp (e_live E ++ L) -> 0 <= fst cp <= 4 /\ 0 <= snd cp < fs_nframes (fst cp)).
      { intros cp Hcp. apply in_app_iff in Hcp as [Hcp|Hcp].
        - rewrite Forall_forall in FVAL. exact (FVAL cp Hcp).
        - destruct (Forall2_In_r _ _ _ _ HL Hcp) as (r & Hr & fl & K & C1 & C2 & _). auto. }
      (* [comment removed for export] *)
      assert (FRB : forall cid pos, 0 <= cid <= 4 -> 0 <= pos < fs_nframes cid ->
                 e_fs E + 36864 <= frame_addr (e_fs E) cid pos /\ frame_addr (e_fs E) cid pos + fake_size cid <= e_fs E + len
                 /\ frame_addr (e_fs E) cid pos mod 8 = 0 /\ fake_size cid mod 8 = 0).
      { intros cid pos Hc Hp. pose proof (frame_in_class (e_fs E) cid pos ltac:(clear -Hc; lia) ltac:(clear -Hc; lia) Hp) as [F1 F2].
        unfold FS_FRAMES in F1, F2. split; [clear - F1 Hc; lia|]. split; [clear - F2 Hc FLEN; lia|].
        split.
        - pose proof (frame_addr_mod64 (e_fs E) cid pos FMOD ltac:(clear -Hc; lia)) as M64.
          apply Z.mod_divide in M64 as [q Hq]; [|clear; lia]. rewrite Hq. replace (q * 64) with ((q * 8) * 8) by (clear; lia). apply Z_mod_mult.
        - pose proof (fake_size_mod64 cid ltac:(clear -Hc; lia)) as M64.
          apply Z.mod_divide in M64 as [q Hq]; [|clear; lia]. rewrite Hq. replace (q * 64) with ((q * 8) * 8) by (clear; lia). apply Z_mod_mult. }
      (* [comment removed for export] *)
      assert (YLOC : (e_fs E + 36864 <= y < e_fs E + len)
                     \/ (vp_shoff P + (e_sp0 (ev1 E) - vp_frame (p1 P)) / 8 - 9 <= y <= vp_shoff P + e_sp0 (ev1 E) / 8)
                     \/ (exists cid pos, 0 <= cid <= 4 /\ 0 <= pos < fs_nframes cid /\
                           vp_shoff P + frame_addr (e_fs E) cid pos / 8 <= y < vp_shoff P + frame_addr (e_fs E) cid pos / 8 + fake_size cid / 8)).
      { destruct LOC as [(cid & pos & Hcp & Hc & Hp & R & _)|[(off & -> & Ro & _)|(cid & pos & g & Hcp & Hc & Hp & -> & Rg)]].
        - left. destruct (FRB cid pos Hc Hp) as (F1 & F2 & _). clear - R F1 F2. lia.
        - right; left. rewrite DS8 at 1. replace (8 * (e_sp0 (ev1 E) / 8) - vp_frame (p1 P)) with (8 * (e_sp0 (ev1 E) / 8) + (- vp_frame (p1 P))) by (clear; lia). rewrite div8_add_l.
          assert ((- vp_frame (p1 P)) / 8 <= - (vp_frame (p1 P) / 8)).
          { apply Z.div_le_upper_bound; [clear; lia|]. pose proof (Z.mul_div_le (vp_frame (p1 P)) 8 ltac:(clear; lia)). clear - H. lia. }
          clear - Ro H. lia.
        - right; right. exists cid, pos. split; [exact Hc|]. split; [exact Hp|]. clear - Rg. lia. }
      assert (Y64 : 0 <= y < 2 ^ 64).
      { destruct YLOC as [R|[R|(cid & pos & Hc & Hp & R)]].
        - clear - R FLO0 FLOB FLEN FHI. lia.
        - assert ((e_sp0 (ev1 E) - vp_frame (p1 P)) / 8 >= 2199090364416) by (apply Z.le_ge, Z.div_le_lower_bound; clear - C11; lia).
          assert (e_sp0 (ev1 E) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; clear - X1; lia).
          clear - R H H0 SHV. lia.
        - destruct (FRB cid pos Hc Hp) as (F1 & F2 & F3 & F4).
          pose proof (Z.div_mod (frame_addr (e_fs E) cid pos) 8 ltac:(clear; lia)) as DQ1. rewrite F3, Z.add_0_r in DQ1.
          pose proof (Z.div_mod (fake_size cid) 8 ltac:(clear; lia)) as DQ2. rewrite F4, Z.add_0_r in DQ2.
          clear - R DQ1 DQ2 F1 F2 FLO0 FLOB FLEN FHI SHV. lia. }
      (* [comment removed for export] *)
      assert (NSTK : ~ (e_sp0 (ev1 E) - vp_frame (p1 P) <= y < e_sp0 (ev1 E)) /\ forall c, In c (vp_fcells (p1 P)) -> ~ (fst c <= y < fst c + snd c)).
      { destruct YLOC as [R|[R|(cid & pos & Hc & Hp & R)]].
        - split; [clear - R C8; lia|]. intros c Hc XX. specialize (FCI c Hc). clear - R FLO0 FLOB FLEN FCI XX CIE. lia.
        - assert ((e_sp0 (ev1 E) - vp_frame (p1 P)) / 8 >= 2199090364416) by (apply Z.le_ge, Z.div_le_lower_bound; clear - C11; lia).
          assert (e_sp0 (ev1 E) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; clear - X1; lia).
          split; [clear - R H H0 SHV C11; lia|]. intros c Hc XX. specialize (FCL c Hc). clear - R H FCL XX SHV. lia.
        - destruct (FRB cid pos Hc Hp) as (F1 & F2 & F3 & F4).
          pose proof (Z.div_mod (frame_addr (e_fs E) cid pos) 8 ltac:(clear; lia)) as DQ1. rewrite F3, Z.add_0_r in DQ1.
          pose proof (Z.div_mod (fake_size cid) 8 ltac:(clear; lia)) as DQ2. rewrite F4, Z.add_0_r in DQ2.
          split; [clear - R DQ1 DQ2 F1 F2 FLO0 FLOB FLEN FHI SHV C11; lia|]. intros c Hc' XX. specialize (FCL c Hc'). clear - R DQ1 F1 FLO0 FLOB FLEN FCL XX SHV. lia. }
      destruct NSTK as [NST NFC].
      apply (proj2 (outside_forall _ _)). intros rb rn Hin Hrng.
      unfold unit_regions2 in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]]].
      - (* [comment removed for export] *)
        pose proof (gamma2_v1 _ _ _ _ _ _ _ _ GV) as (HEV & _).
        pose proof (outside_unit_regions SEGS PV EV (PV_ok2 V VIN) y HEV Y64 NST NFC) as O1.
        exact (proj1 (outside_forall _ _) O1 rb rn Hin Hrng).
      - (* [comment removed for export] *)
        unfold arg_regions in Hin. apply in_map_iff in Hin as [[i [lo hi]] [Eb Hw]]. injection Eb as Eb1 Eb2. subst rb rn.
        destruct (footprint_ok2_v1 _ _ _ _ FP) as [_ WAD]. rewrite forallb_forall in WAD. specialize (WAD _ Hw). unfold wrgn_admissible in WAD.
        destruct (resolve_base isv_call2 A0 sigma (ASYM2 i)) as [[bq c]|] eqn:RS; [|discriminate].
        destruct (rgn_get (vs_rgn A0) bq) as [pr|] eqn:Gpr; [|discriminate].
        apply andb_prop in WAD as [WD WAD]. apply Z.eqb_eq in WD. destruct (rgn_get_in _ _ _ Gpr) as [Hpr Bpr].
        assert (KNF : is_data_shadow pr = false /\ in_ranges (vr_w pr) (lo + c) (hi - lo) = true).
        { unfold is_data_shadow. destruct (vr_kind pr); try discriminate; auto. }
        destruct KNF as [NDS IR].
        pose proof (HRG _ Hpr) as (PB1 & PB2 & _ & _ & _ & PRP & _ & PK). destruct (PRP NDS) as [_ RP2].
        destruct (in_ranges_sound _ _ _ IR) as (lo2 & hi2 & Hw2 & Z1 & Z2).
        assert (EA : nth (Z.to_nat i) (e_args EV) 0 = nu1 bq + c).
        { destruct (unit_static_ok2_wsets _ _ _ (proj1 (V_ok2 V VIN))) as (_ & _ & _ & W4). rewrite forallb_forall in W4.
          specialize (W4 _ Hw). cbn [fst snd] in W4. apply andb_prop in W4 as [W4 _]. apply andb_prop in W4 as [W4a W4b].
          apply Z.leb_le in W4a. apply Z.ltb_lt in W4b.
          cbn [e_args EV callee_env2]. erewrite nth_error_nth; [|rewrite nth_error_map, nth_error_seq;
            destruct (PeanoNat.Nat.ltb_spec (Z.to_nat i) 8); [reflexivity|lia]]. cbn.
          replace (ASYM2 (Z.of_nat (Z.to_nat i))) with (ASYM2 i) by (unfold ASYM2; f_equal; (ltac2:(LK.k [@HB; @Efr; @FLO0; @FLOB; @FLEN; @C8; @C11; @X3; @DS8; @Bpr; @W4a]); lia)).
          exact (RB_eval _ _ _ _ _ _ _ (resolve_base_spec _ _ _ _ _ _ RS)). }
        assert (Hrng' : in_rng (wordZ y) (wordZ (nu1 bq + c + lo)) (hi - lo)) by (rewrite <- EA; exact Hrng). clear Hrng.
        unfold in_rng in Hrng'. rewrite (u_wordZ y) in Hrng' by exact Y64.
        destruct (Z.lt_ge_cases lo hi) as [LH|LH]; [|exfalso; clear - Hrng' LH; lia].
        unfold rbase in PB1, PB2, RP2. rewrite WD, Bpr in PB1, PB2, RP2.
        destruct (RP2 lo2 hi2 (lo + c) Hw2 ltac:(clear -Z1 Z2 LH; lia)) as (Q0 & _).
        rewrite u_wordZ in Hrng' by (clear -Q0 PB1 PB2; lia).
        destruct LOC as [(cid & pos & Hcp & Hc & Hp & R & NOWIN)|SHLOC].
        + apply (NOWIN _ _ _ _ _ Hw RS). clear - Hrng'. lia.
        + (* [comment removed for export] *)
          (* [comment removed for export] *)
          assert (WFS : e_fs E <= nu1 bq + c + lo /\ y < e_fs E + len).
          { destruct (RP2 lo2 hi2 (y - nu1 bq) Hw2 ltac:(clear -Z1 Z2 Hrng'; lia)) as (YB & _).
            unfold kind_ok in PK. destruct (vr_kind pr) as [cidp flp| | | |] eqn:Kp; try discriminate.
            - destruct PK as (_ & Pc & Plo & Phi & _ & posp & Pp & Pb & _). unfold rbase in Pb. rewrite WD, Bpr in Pb.
              destruct (FRB cidp posp Pc Pp) as (F1 & F2 & _). clear - Pb F1 F2 Q0 Plo Phi YB. lia.
            - destruct PK as (_ & (cidL & posL & L1 & L2 & L3) & _). unfold rbase in L2, L3. rewrite WD, Bpr in L2, L3.
              rewrite Forall_forall in FVAL. destruct (FVAL _ L1) as [Lc Lp]. cbn [fst snd] in Lc, Lp.
              destruct (FRB cidL posL Lc Lp) as (F1 & F2 & _). clear - L2 L3 F1 F2 Q0 YB. lia. }
          exfalso.
          destruct SHLOC as [(off & Ey & Ro & _)|(cid & pos & g & _ & Hc & Hp & Ey & Rg)].
          * assert (e_sp0 (ev1 E) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; clear - X1; lia).
            assert ((e_sp0 (ev1 E) - vp_frame (p1 P)) / 8 >= 2199090364416) by (apply Z.le_ge, Z.div_le_lower_bound; clear - C11; lia).
            clear - Ey Ro H H0 SHV FLO0 FLOB Hrng' WFS. liae.
          * destruct (FRB cid pos Hc Hp) as (F1 & F2 & F3 & F4).
            pose proof (Z.div_mod (frame_addr (e_fs E) cid pos) 8 ltac:(clear; lia)) as DQ1. rewrite F3, Z.add_0_r in DQ1.
            pose proof (Z.div_mod (fake_size cid) 8 ltac:(clear; lia)) as DQ2. rewrite F4, Z.add_0_r in DQ2.
            clear - Ey Rg DQ1 DQ2 F1 F2 FHI SHV FLO0 FLOB Hrng' WFS. lia.
      - (* [comment removed for export] *)
        change (vp_fs PV) with (vp_fs P) in Hin. rewrite EFS in Hin.
        unfold stack_shadow_regions in Hin. apply in_map_iff in Hin as [[lo' hi'] [Eb Hr]]. cbn [fst snd] in Eb. injection Eb as Eb1 Eb2. subst rb rn.
        cbn [ev1 EV callee_env2 callee_env e_sp0] in Hrng. change (vp_shoff (ge2_P0 G)) with (vp_shoff P) in Hrng.
        assert (Wb : - vp_frame (p1 P) <= lo' /\ hi' <= 0 /\ (lo', hi') = (- vp_frame (p1 P), spoff)).
        { destruct (footprint_ok2_v1 _ _ _ _ FP) as [FP1 _]. unfold footprint_ok in FP1.
          apply andb_prop in FP1 as [FP1 _]. apply andb_prop in FP1 as [FP1 _]. apply andb_prop in FP1 as [FP1 _]. apply andb_prop in FP1 as [F1 F2].
          apply Z.eqb_eq in F2.
          cbn in Hr. destruct Hr as [Hr|[]].
          injection Hr as <- <-. destruct (unit_static_ok2_wsets _ _ _ (proj1 (V_ok2 V VIN))) as (_ & _ & W3 & _).
          apply Bool.orb_false_elim in W3 as [W3a W3b]. apply Z.ltb_ge in W3a. apply Z.ltb_ge in W3b.
          change (vp_frame (p1 (ge2_P0 G))) with (vp_frame (p1 P)). split; [clear; lia|]. split; [exact W3a|]. rewrite F2. reflexivity. }
        destruct Wb as (Wlo & Whi & HrK).
        rewrite DS8 in Hrng at 1. rewrite div8_add_l in Hrng.
        unfold in_rng in Hrng. rewrite (u_wordZ y) in Hrng by exact Y64.
        destruct (Z.lt_ge_cases lo' hi') as [LH|LH].
        2:{ exfalso. assert ((hi' - lo') / 8 <= 0) by (apply Z.div_le_upper_bound; clear -LH; lia). clear - H Hrng. lia. }
        assert (LB : - (vp_frame (p1 P) / 8) - 1 <= lo' / 8).
        { assert ((- vp_frame (p1 P)) / 8 <= lo' / 8) by (apply div8_mono; exact Wlo).
          assert (- (vp_frame (p1 P) / 8) - 1 <= (- vp_frame (p1 P)) / 8); [|clear - H H0; lia].
          apply Z.div_le_lower_bound; [clear; lia|]. pose proof (Z.mul_div_le (vp_frame (p1 P)) 8 ltac:(clear; lia)).
          pose proof (Z.div_mod (vp_frame (p1 P)) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (vp_frame (p1 P)) 8 ltac:(clear; lia)). clear - H H0 H1. liae. }
        assert (UB : lo' / 8 + (hi' - lo') / 8 <= (hi' + 7) / 8) by (pose proof (div8_split lo' (hi' - lo')); replace (lo' + (hi' - lo') + 7) with (hi' + 7) in H by (clear; lia); exact H).
        assert (UB0 : (hi' + 7) / 8 <= 0 + 1) by (apply Z.div_le_upper_bound; clear - Whi; lia).
        assert (B0 : 0 <= vp_shoff P + (e_sp0 (ev1 E) / 8 + lo' / 8) < 2 ^ 64).
        { assert ((e_sp0 (ev1 E) - vp_frame (p1 P)) / 8 >= 2199090364416) by (apply Z.le_ge, Z.div_le_lower_bound; clear - C11; lia).
          assert (e_sp0 (ev1 E) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; clear - X1; lia).
          rewrite DS8 in H at 1. replace (8 * (e_sp0 (ev1 E) / 8) - vp_frame (p1 P)) with (8 * (e_sp0 (ev1 E) / 8) + - vp_frame (p1 P)) in H by (clear; lia).
          rewrite div8_add_l in H.
          assert ((- vp_frame (p1 P)) / 8 <= lo' / 8) by (apply div8_mono; exact Wlo).
          assert (0 <= (hi' - lo') / 8) by (apply Z.div_pos; clear - LH; lia).
          clear - H H0 H1 H2 SHV SH0 LB UB UB0. lia. }
        rewrite u_wordZ in Hrng by exact B0.
        destruct LOC as [(cid & pos & Hcp & Hc & Hp & R & _)|[(off & Ey & Ro & NOKILL)|(cid & pos & g & Hcp & Hc & Hp & Ey & Rg)]].
        + (* [comment removed for export] *)
          assert (e_sp0 (ev1 E) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; clear - X1; lia).
          destruct (FRB cid pos Hc Hp) as (F1 & F2 & _).
          pose proof (Z.div_mod (vp_frame (p1 P)) 8 ltac:(clear; lia)) as DF8. pose proof (Z.mod_pos_bound (vp_frame (p1 P)) 8 ltac:(clear; lia)) as MF8.
          assert (C11' : 17594333495296 <= e_sp0 (ev1 E) - vp_frame (p1 P)) by (clear - C11; unfold HIGH_MEM_BEG in C11; lia).
          clear - R F1 F2 FLO0 FLOB Hrng H UB UB0 SHV LB DS8 DF8 MF8 C11'. lia.
        + (* [comment removed for export] *)
          injection HrK as El Eh. apply NOKILL. rewrite El, Eh in Hrng, UB. clear - Hrng Ey UB.
          change (vp_frame (p1 (ge2_P0 G))) with (vp_frame (p1 P)) in *. lia.
        + (* [comment removed for export] *)
          destruct (FRB cid pos Hc Hp) as (F1 & F2 & F3 & F4).
          pose proof (Z.div_mod (frame_addr (e_fs E) cid pos) 8 ltac:(clear; lia)) as DQ1. rewrite F3, Z.add_0_r in DQ1.
          pose proof (Z.div_mod (fake_size cid) 8 ltac:(clear; lia)) as DQ2. rewrite F4, Z.add_0_r in DQ2.
          destruct C8 as [C8|C8].
          * (* [comment removed for export] *) clear - Hrng Ey Rg DQ1 DQ2 F2 C8 LB DS8. liae.
          * (* [comment removed for export] *) clear - Hrng Ey Rg DQ1 F1 C8 UB UB0 DS8. lia.
      - (* [comment removed for export] *)
        rewrite (fs_regions_P PV P) in Hin by reflexivity. unfold fs_regions in Hin. rewrite EFS in Hin.
        cbn [e_fs e_live EV callee_env2] in Hin. change (vp_shoff (ge2_P0 G)) with (vp_shoff P) in Hin.
        unfold in_rng in Hrng. rewrite (u_wordZ y) in Hrng by exact Y64.
        apply in_app_iff in Hin as [Hin|Hin].
        + (* [comment removed for export] *)
          assert (R0 : exists lo0 n0, (rb, rn) = (wordZ lo0, n0) /\ e_fs E <= lo0 /\ lo0 + n0 <= e_fs E + 36864 /\ 0 < n0).
          { destruct Hin as [E0|[E0|[]]]; symmetry in E0; [exists (e_fs E), 88|exists (e_fs E + FS_FLAGS), 32768]; (split; [exact E0|]); unfold FS_FLAGS; clear; lia. }
          destruct R0 as (lo0 & n0 & E0 & R1 & R2 & R3). injection E0 as -> ->.
          rewrite u_wordZ in Hrng by (clear - R1 R2 R3 FLO0 FLOB FLEN FHI; lia).
          destruct YLOC as [R|[R|(cid & pos & Hc & Hp & R)]].
          * clear - R R1 R2 Hrng. lia.
          * assert (e_sp0 (ev1 E) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; clear - X1; lia).
            assert ((e_sp0 (ev1 E) - vp_frame (p1 P)) / 8 >= 2199090364416) by (apply Z.le_ge, Z.div_le_lower_bound; clear - C11; lia).
            clear - R R1 R2 Hrng H H0 SHV FLO0 FLOB FLEN. lia.
          * destruct (FRB cid pos Hc Hp) as (F1 & F2 & F3 & F4).
            pose proof (Z.div_mod (frame_addr (e_fs E) cid pos) 8 ltac:(clear; lia)) as DQ1. rewrite F3, Z.add_0_r in DQ1.
            pose proof (Z.div_mod (fake_size cid) 8 ltac:(clear; lia)) as DQ2. rewrite F4, Z.add_0_r in DQ2.
            clear - R R1 R2 Hrng DQ1 DQ2 F1 F2 FHI SHV FLO0 FLOB FLEN. lia.
        + (* [comment removed for export] *)
          assert (CL : forall k, In (rb, rn) (classes_regions P (e_fs E) k (e_live E ++ L)) -> Z.of_nat k <= 5 ->
                       exists cid pos, 0 <= cid < 5 /\ 0 <= pos < fs_nframes cid /\ ~ In (cid, pos) (e_live E ++ L) /\
                         ((rb, rn) = (wordZ (frame_addr (e_fs E) cid pos), fake_size cid)
                          \/ (rb, rn) = (wordZ (vp_shoff P + frame_addr (e_fs E) cid pos / 8), fake_size cid / 8))).
          { induction k as [|k IH]; cbn [classes_regions]; intros H Hk; [destruct H|].
            apply in_app_iff in H as [H|H]; [apply IH; [exact H|clear -Hk; lia]|].
            unfold class_regions in H. apply in_flat_map in H as (pos & Hpos & H).
            apply in_map_iff in Hpos as (pn & <- & Hpn). apply in_seq in Hpn.
            destruct (existsb (fun cp : Z * Z => (fst cp =? Z.of_nat k) && (snd cp =? Z.of_nat pn)) (e_live E ++ L)) eqn:EXB; [destruct H|].
            exists (Z.of_nat k), (Z.of_nat pn). split; [clear -Hk; lia|]. split; [clear -Hpn; lia|]. split.
            { intros IN. assert (EXB' : existsb (fun cp : Z * Z => (fst cp =? Z.of_nat k) && (snd cp =? Z.of_nat pn)) (e_live E ++ L) = true).
              { apply existsb_exists. exists (Z.of_nat k, Z.of_nat pn). split; [exact IN|]. cbn [fst snd]. rewrite !Z.eqb_refl. reflexivity. }
              rewrite EXB' in EXB. discriminate. }
            destruct H as [E0|[E0|[]]]; [left|right]; symmetry; exact E0. }
          change (Z.to_nat FS_NCLASSES) with 5%nat in Hin. destruct (CL _ Hin ltac:(clear; cbn; lia)) as (cid2 & pos2 & Hc2 & Hp2 & NL2 & CASES).
          destruct (FRB cid2 pos2 ltac:(clear -Hc2; lia) Hp2) as (Q1' & Q2' & Q3' & Q4').
          pose proof (Z.div_mod (frame_addr (e_fs E) cid2 pos2) 8 ltac:(clear; lia)) as DR1. rewrite Q3', Z.add_0_r in DR1.
          pose proof (Z.div_mod (fake_size cid2) 8 ltac:(clear; lia)) as DR2. rewrite Q4', Z.add_0_r in DR2.
          pose proof (fake_size_bounds cid2 ltac:(clear -Hc2; lia)) as FB2.
          destruct CASES as [E0|E0]; injection E0 as -> ->; try change (vp_shoff (ge2_P0 G)) with (vp_shoff P) in Hrng.
          * (* [comment removed for export] *)
            rewrite u_wordZ in Hrng by (clear - Q1' Q2' FLO0 FLOB FLEN FHI FB2; lia).
            destruct LOC as [(cid & pos & Hcp & Hc & Hp & R & _)|SHLOC].
            -- assert (NE : cid <> cid2 \/ pos <> pos2) by (destruct (Z.eq_dec cid cid2) as [->|]; [right; intros ->; exact (NL2 Hcp)|left; assumption]).
               destruct (frames_disjoint (e_fs E) cid pos cid2 pos2 ltac:(clear -Hc; lia) Hp ltac:(clear -Hc2; lia) Hp2 NE); clear - R Hrng H; lia.
            -- destruct YLOC as [R|[R|(cid & pos & Hc & Hp & R)]].
               { destruct SHLOC as [(off & Ey & Ro & _)|(cid & pos & g & _ & Hc & Hp & Ey & Rg)].
                 - assert (e_sp0 (ev1 E) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; clear - X1; lia). assert ((e_sp0 (ev1 E) - vp_frame (p1 P)) / 8 >= 2199090364416) by (apply Z.le_ge, Z.div_le_lower_bound; clear - C11; lia). clear - Ey Ro H H0 SHV FLO0 FLOB FLEN Hrng Q1' Q2' C11 X2 R. liae.
                 - destruct (FRB cid pos Hc Hp) as (F1 & F2 & F3 & F4).
                   pose proof (Z.div_mod (frame_addr (e_fs E) cid pos) 8 ltac:(clear; lia)) as DQ1. rewrite F3, Z.add_0_r in DQ1.
                   pose proof (Z.div_mod (fake_size cid) 8 ltac:(clear; lia)) as DQ2. rewrite F4, Z.add_0_r in DQ2.
                   clear - Ey Rg DQ1 DQ2 F1 F2 FHI SHV FLO0 FLOB FLEN Hrng Q1' Q2'. lia. }
               { assert (e_sp0 (ev1 E) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; clear - X1; lia). assert ((e_sp0 (ev1 E) - vp_frame (p1 P)) / 8 >= 2199090364416) by (apply Z.le_ge, Z.div_le_lower_bound; clear - C11; lia). clear - R H H0 SHV FLO0 FLOB FLEN Hrng Q1' Q2'. lia. }
               { destruct (FRB cid pos Hc Hp) as (F1 & F2 & F3 & F4).
                 pose proof (Z.div_mod (frame_addr (e_fs E) cid pos) 8 ltac:(clear; lia)) as DQ1. rewrite F3, Z.add_0_r in DQ1.
                 pose proof (Z.div_mod (fake_size cid) 8 ltac:(clear; lia)) as DQ2. rewrite F4, Z.add_0_r in DQ2.
                 clear - R DQ1 DQ2 F1 F2 FHI SHV FLO0 FLOB FLEN Hrng Q1' Q2'. lia. }
          * (* [comment removed for export] *)
            rewrite u_wordZ in Hrng by (clear - Q1' Q2' FLO0 FLOB FLEN FHI SHV DR1 DR2 FB2; lia).
            destruct LOC as [(cid & pos & Hcp & Hc & Hp & R & _)|[(off & Ey & Ro & NOKILL)|(cid & pos & g & Hcp & Hc & Hp & Ey & Rg)]].
            -- (* [comment removed for export] *)
               destruct (FRB cid pos Hc Hp) as (F1 & F2 & _). clear - R F1 F2 FLO0 FLOB FLEN Hrng Q1' Q2' FHI SHV DR1 DR2. lia.
            -- (* [comment removed for export] *)
               assert ((e_sp0 (ev1 E) - vp_frame (p1 P)) / 8 >= 2199090364416) by (apply Z.le_ge, Z.div_le_lower_bound; clear - C11; lia).
               rewrite DS8 in H at 1. replace (8 * (e_sp0 (ev1 E) / 8) - vp_frame (p1 P)) with (8 * (e_sp0 (ev1 E) / 8) + - vp_frame (p1 P)) in H by (clear; lia).
               rewrite div8_add_l in H.
               assert (FB : (- vp_frame (p1 P)) / 8 <= - (vp_frame (p1 P) / 8)).
               { apply Z.div_le_upper_bound; [clear; lia|]. pose proof (Z.mul_div_le (vp_frame (p1 P)) 8 ltac:(clear; lia)). clear - H0. lia. }
               pose proof (Z.div_mod (vp_frame (p1 P)) 8 ltac:(clear; lia)) as DF. pose proof (Z.mod_pos_bound (vp_frame (p1 P)) 8 ltac:(clear; lia)) as MF.
               destruct C8 as [C8|C8]; clear - Hrng Ey Ro DR1 DR2 Q1' Q2' C8 DS8 DF MF. all: lia.
            -- (* [comment removed for export] *)
               destruct (FRB cid pos Hc Hp) as (F1 & F2 & F3 & F4).
               assert (NE : cid <> cid2 \/ pos <> pos2) by (destruct (Z.eq_dec cid cid2) as [->|]; [right; intros ->; exact (NL2 Hcp)|left; assumption]).
               pose proof (proj1 (div8_exact_range _ _ (y - vp_shoff P) F3 F4) ltac:(clear - Ey Rg; lia)) as IN1.
               pose proof (proj1 (div8_exact_range _ _ (y - vp_shoff P) Q3' Q4') ltac:(clear - Hrng; lia)) as IN2.
               destruct (frames_disjoint (e_fs E) cid pos cid2 pos2 ltac:(clear -Hc; lia) Hp ltac:(clear -Hc2; lia) Hp2 NE); clear - IN1 IN2 H; lia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Let rgK := kill_shadow_sp (vp_frame (p1 P)) (u1 V) spoff (kill_fs_cells (vs_rgn A0)).

    Lemma B_facts :
      kill_wrgn A0 sigma rgK (u2_wrgn V) = Some (vs_rgn B)
      /\ v1 B = call_base2v (ge2_CI G) (v1 A0) (u1 V) spoff npc
      /\ vs_live B = vs_live A0 /\ vs_divdef B = vs_divdef A0 /\ vs_memo B = [].
    Proof using CB P.
      pose proof CB as CB'. unfold call_base2 in CB'. change (de2_P D) with P in CB'. change (de2_G D) with G in CB'. fold rgK in CB'.
      destruct (kill_wrgn A0 sigma rgK (u2_wrgn V)) as [rgB|] eqn:KW; [|discriminate].
      assert (SINJ : forall (x y : vstate2), Some x = Some y -> x = y) by (clear; intros x y Hxy; injection Hxy as H'; exact H').
      apply SINJ in CB'. rewrite <- CB'. cbn [vs_rgn v1 vs_live vs_divdef vs_memo]. repeat split; reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma FSNZ r0 : In r0 (vs_rgn A0) -> exists fsl, vp_fs P = Some fsl.
    Proof using HGm.
      intros Hr0. pose proof HGm as (_ & _ & _ & _ & _ & HRG & _).
      assert (GEN : forall r, In r (vs_rgn A0) -> match vr_kind r with RK_flag _ => False | _ => True end -> vp_fs P <> None).
      { intros r Hr KK. pose proof (HRG _ Hr) as (_ & _ & _ & _ & _ & _ & _ & KO). unfold kind_ok in KO.
        destruct (vr_kind r); try exact (proj1 KO). destruct KK. }
      destruct (vp_fs P) as [fsl|] eqn:EFS; [exists fsl; reflexivity|exfalso].
      destruct (vr_kind r0) as [| |owner| |] eqn:K0; try (apply (GEN _ Hr0); [rewrite K0; exact I|reflexivity]).
      pose proof (HRG _ Hr0) as (_ & _ & _ & _ & _ & _ & _ & KO). unfold kind_ok in KO. rewrite K0 in KO.
      destruct KO as (_ & _ & _ & _ & ro & cid & fl & G0 & KO & _).
      apply (GEN ro (proj1 (rgn_get_in _ _ _ G0))); [rewrite KO; exact I|reflexivity].
    Qed.

    (* [comment removed for export] *)
    Lemma pipeline_facts r :
      In r (vs_rgn B) ->
      exists r0, In r0 (vs_rgn A0) /\ rshape r0 r /\ subcells (is_shadow r0) (vr_cells r) (vr_cells r0) /\ incl (vr_nul r) (vr_nul r0)
        /\ (vr_kind r = RK_fs -> vr_cells r = [] /\ vr_nul r = [])
        /\ (vr_kind r = RK_shadow SP0 ->
              (forall k w v, In (k, (w, v)) (vr_cells r) -> k + w <= (- vp_frame (p1 P)) / 8 \/ (spoff + 7) / 8 <= k)
              /\ (forall f, In f (vr_nul r) -> snd f < (- vp_frame (p1 P)) / 8 \/ (spoff + 7) / 8 <= fst f))
        /\ (forall i lo hi bq c, In (i, (lo, hi)) (u2_wrgn V) -> resolve_base isv_call2 A0 sigma (ASYM2 i) = Some (bq, c) -> vr_base r = bq ->
              (forall k w v, In (k, (w, v)) (vr_cells r) -> k + w <= lo + c \/ hi + c <= k)
              /\ (forall f, In f (vr_nul r) -> snd f < lo + c \/ hi + c <= fst f))
        /\ (forall i lo hi bq c pr, In (i, (lo, hi)) (u2_wrgn V) -> resolve_base isv_call2 A0 sigma (ASYM2 i) = Some (bq, c) ->
              rgn_get (vs_rgn A0) bq = Some pr -> vr_kind pr = RK_arg -> vr_kind r = RK_arg -> vr_base r <> bq -> vr_cells r = [] /\ vr_nul r = []).
    Proof using CB HGm rgK.
      intros Hr. destruct B_facts as (KW & _).
      pose proof HGm as (_ & _ & _ & _ & _ & _ & HLV & _). pose proof HLV as (_ & _ & _ & NDA).
      pose proof (kill_fs_cells_thins (vs_rgn A0)) as T0. pose proof (kill_shadow_sp_thins (vp_frame (p1 P)) (u1 V) spoff (kill_fs_cells (vs_rgn A0))) as T1.
      pose proof (thins_trans _ _ _ T0 T1) as T01. fold rgK in T1, T01.
      destruct (kill_wrgn_spec A0 sigma _ _ _ KW ltac:(rewrite (thins_bases _ _ T01); exact NDA)) as (T1B & WIN & HAV).
      destruct (thins_in_back _ _ _ T1B Hr) as (rk & Hrk & SK & CK & NK).
      destruct (thins_in_back _ _ _ T1 Hrk) as (rf & Hrf & SF & CF & NF).
      destruct (thins_in_back _ _ _ T0 Hrf) as (r0 & Hr0 & S0 & C0 & N0).
      pose proof (rshape_is_shadow _ _ S0) as I0F. pose proof (rshape_is_shadow _ _ SF) as IFK.
      rewrite IFK in CK. rewrite I0F in CF, CK.
      exists r0. split; [exact Hr0|]. split; [eapply rshape_trans; [exact S0|eapply rshape_trans; [exact SF|exact SK]]|].
      split; [eapply subcells_trans; [exact C0|eapply subcells_trans; [exact CF|exact CK]]|].
      split; [eapply incl_tran; [exact NK|eapply incl_tran; [exact NF|exact N0]]|].
      split.
      { intros KFS. destruct SK as (_ & _ & KK & _). destruct SF as (_ & _ & KF & _).
        destruct (kill_fs_cells_fs _ _ Hrf ltac:(clear - KK KF KFS; congruence)) as [CF0 NF0].
        rewrite CF0 in CF. rewrite NF0 in NF.
        split.
        - destruct (vr_cells r) as [|[yk [yw yv]] ?] eqn:EC; [reflexivity|exfalso].
          destruct (subcell_src _ _ _ _ _ (CK yk yw yv ltac:(first [rewrite EC; left; reflexivity | left; reflexivity]))) as (k1 & w1 & v1 & H1 & _).
          eapply subcell_in_nil. exact (CF _ _ _ H1).
        - destruct (vr_nul r) as [|y ?]; [reflexivity|destruct (NF y (NK y (or_introl eq_refl)))]. }
      split.
      { intros KSH. destruct SK as (_ & _ & KK & _).
        destruct (kill_shadow_sp_sp0 (vp_frame (p1 P)) (u1 V) spoff _ _ Hrk ltac:(clear - KK KSH; congruence)) as [CS NS].
        split; [|intros f Hf; exact (NS _ (NK _ Hf))].
        intros k w v Hin. destruct (subcell_src _ _ _ _ _ (CK _ _ _ Hin)) as (k1 & w1 & v1 & H1 & K1 & K2 & _).
        pose proof (CS _ _ _ H1) as DJ1. clear - DJ1 K1 K2. lia. }
      split.
      { intros i lo hi bq c Hin RS Hb. exact (WIN i lo hi bq c r Hin RS Hr Hb). }
      intros i lo hi bq c pr Hin RS G0 KP KR NB.
      destruct (shape_map_get _ _ _ _ (thins_shape _ _ T01) G0) as (prk & GK & SPK). destruct SPK as (_ & _ & KPK & _).
      exact (HAV i lo hi bq c prk r Hin RS GK ltac:(rewrite KPK; exact KP) Hr KR NB).
    Qed.

    (* [comment removed for export] *)
    Lemma WADM i lo hi bq c :
      In (i, (lo, hi)) (u2_wrgn V) -> resolve_base isv_call2 A0 sigma (ASYM2 i) = Some (bq, c) ->
      exists pr, rgn_get (vs_rgn A0) bq = Some pr /\ In pr (vs_rgn A0) /\ vr_base pr = bq /\ vr_disp pr = 0
        /\ match vr_kind pr with RK_fake _ _ | RK_arg => True | _ => False end
        /\ in_ranges (vr_w pr) (lo + c) (hi - lo) = true.
    Proof using D1 FP P.
      intros Hw RS. destruct (footprint_ok2_v1 _ _ _ _ FP) as [_ WAD]. rewrite forallb_forall in WAD. specialize (WAD _ Hw).
      unfold wrgn_admissible in WAD. rewrite RS in WAD.
      destruct (rgn_get (vs_rgn A0) bq) as [pr|] eqn:Gpr; [|discriminate].
      apply andb_prop in WAD as [WD WAD]. apply Z.eqb_eq in WD. destruct (rgn_get_in _ _ _ Gpr) as [Hpr Bpr].
      exists pr. split; [reflexivity|]. split; [exact Hpr|]. split; [exact Bpr|]. split; [exact WD|].
      destruct (vr_kind pr); try discriminate; auto.
    Qed.

    (* [comment removed for export] *)
    Definition avoid (r0 : vregion) (off : Z) : Prop :=
      (forall i lo hi bq c, In (i, (lo, hi)) (u2_wrgn V) -> resolve_base isv_call2 A0 sigma (ASYM2 i) = Some (bq, c) ->
          vr_base r0 = bq -> ~ (lo + c <= off < hi + c))
      /\ (vr_kind r0 = RK_shadow SP0 -> ~ ((- vp_frame (p1 P)) / 8 <= off < (spoff + 7) / 8))
      /\ (forall i lo hi bq c pr, In (i, (lo, hi)) (u2_wrgn V) -> resolve_base isv_call2 A0 sigma (ASYM2 i) = Some (bq, c) ->
          rgn_get (vs_rgn A0) bq = Some pr -> vr_kind pr = RK_arg -> vr_kind r0 = RK_arg -> vr_base r0 <> bq -> False).

    (* [comment removed for export] *)
    Lemma surv_outside fsl r0 off :
      vp_fs P = Some fsl -> In r0 (vs_rgn A0) ->
      match vr_kind r0 with RK_flag _ | RK_fs => False | _ => True end -> is_data_shadow r0 = false ->
      vr_lo r0 <= off < vr_hi r0 -> avoid r0 off ->
      outside (wordZ (rbase nu1 r0 + off)) (unit_regions2 PV EV).
    Proof using D1 DONE FP GV HB HGm HL NPC PO PO0 VIN X b' nJ.
      intros EFS Hr0 KK ND Hoff (AV1 & AV2 & AV3). apply (loc_untouched fsl _ EFS).
      pose proof HGm as (HV1 & HE2 & HMC2 & HF2 & HDD & HRG & HLV & HB2 & _).
      pose proof HE2 as (_ & _ & HFS & _). unfold env_fs in HFS. rewrite EFS in HFS. destruct fsl as [len ssl].
      destruct HFS as (_ & FLO & FHI & FMOD & FLEN & FVAL & _). rewrite Forall_forall in FVAL.
      pose proof HLV as (_ & _ & LV3 & NDA).
      pose proof (HRG _ Hr0) as (RB1 & RB2 & RB3 & RDS & RCELLS & RPERM & RNUL & KIND). unfold kind_ok in KIND.
      (* [comment removed for export] *)
      assert (LFK : forall r cid fl, In r (vs_rgn A0) -> vr_kind r = RK_fake cid fl ->
                exists cp, In cp L /\ fst cp = cid /\ 0 <= fst cp <= 4 /\ 0 <= snd cp < fs_nframes (fst cp)
                           /\ rbase nu1 r = frame_addr (e_fs E) (fst cp) (snd cp) /\ ~ In cp (e_live E)).
      { intros r cid fl Hr K. destruct (Forall2_In_l _ _ _ _ HL (in_fakes_of _ _ _ _ Hr K)) as (cp & Hcp & fl' & K' & C1 & C2 & C3 & C4 & C5 & C6 & _).
        assert (E1 : fst cp = cid) by (clear - K K'; congruence). exists cp. auto 10. }
      (* [comment removed for export] *)
      assert (FRM8 : forall cid pos, 0 <= cid <= 4 -> frame_addr (e_fs E) cid pos mod 8 = 0 /\ fake_size cid mod 8 = 0).
      { intros cid pos Hc. split.
        - pose proof (frame_addr_mod64 (e_fs E) cid pos FMOD ltac:(clear -Hc; lia)) as M64.
          apply Z.mod_divide in M64 as [q Hq]; [|clear; lia]. rewrite Hq. replace (q * 64) with ((q * 8) * 8) by (clear; lia). apply Z_mod_mult.
        - pose proof (fake_size_mod64 cid ltac:(clear -Hc; lia)) as M64.
          apply Z.mod_divide in M64 as [q Hq]; [|clear; lia]. rewrite Hq. replace (q * 64) with ((q * 8) * 8) by (clear; lia). apply Z_mod_mult. }
      (* [comment removed for export] *)
      assert (FINJ : forall c1 p1 c2 p2, 0 <= c1 <= 4 -> 0 <= p1 < fs_nframes c1 -> 0 <= c2 <= 4 -> 0 <= p2 < fs_nframes c2 ->
                frame_addr (e_fs E) c1 p1 = frame_addr (e_fs E) c2 p2 -> c1 = c2 /\ p1 = p2).
      { intros c1 p1 c2 p2 H1 H2 H3 H4 EQ.
        pose proof (fake_size_bounds c1 H1) as SZ1. pose proof (fake_size_bounds c2 H3) as SZ2.
        assert (NE : (c1 <> c2 \/ p1 <> p2) -> False).
        { intros NE. pose proof (frames_disjoint (e_fs E) c1 p1 c2 p2 ltac:(clear -H1; lia) H2 ltac:(clear -H3; lia) H4 NE) as DJ.
          clear - DJ EQ SZ1 SZ2. lia. }
        destruct (Z.eq_dec c1 c2) as [E1|N1]; [|exfalso; apply NE; left; exact N1].
        destruct (Z.eq_dec p1 p2) as [E2|N2]; [auto|exfalso; apply NE; right; exact N2]. }
      (* [comment removed for export] *)
      assert (WINF : forall cid pos, 0 <= cid <= 4 -> 0 <= pos < fs_nframes cid ->
                frame_addr (e_fs E) cid pos <= rbase nu1 r0 + off < frame_addr (e_fs E) cid pos + fake_size cid ->
                ((In (cid, pos) L /\ exists fl, vr_kind r0 = RK_fake cid fl /\ rbase nu1 r0 = frame_addr (e_fs E) cid pos)
                 \/ (In (cid, pos) (e_live E) /\ vr_kind r0 = RK_arg)) ->
                forall i lo hi bq c, In (i, (lo, hi)) (u2_wrgn V) -> resolve_base isv_call2 A0 sigma (ASYM2 i) = Some (bq, c) ->
                  vr_base r0 <> bq ->
                  ~ (nu1 bq + c + lo <= rbase nu1 r0 + off < nu1 bq + c + hi)).
      { intros cid pos Hc Hp YIN SLOT i lo hi bq c Hw RS NB IN.
        destruct (WADM _ _ _ _ _ Hw RS) as (pr & Gpr & Hpr & Bpr & Dpr & Kpr & IR).
        pose proof (HRG _ Hpr) as (PB1 & PB2 & _ & _ & _ & PRP & _ & PK). unfold kind_ok in PK.
        assert (NDSp : is_data_shadow pr = false) by (unfold is_data_shadow; destruct (vr_kind pr); auto; destruct Kpr).
        destruct (PRP NDSp) as [_ RP2].
        destruct (Z.lt_ge_cases lo hi) as [LH|LH]; [|clear - IN LH; lia].
        destruct (in_ranges_sound _ _ _ IR) as (lo2 & hi2 & Hw2 & Z1 & Z2).
        set (y := rbase nu1 r0 + off) in *.
        destruct (RP2 lo2 hi2 (y - nu1 bq) Hw2 ltac:(clear - Z1 Z2 IN LH; lia)) as (Q0 & _).
        assert (RBp : rbase nu1 pr = nu1 bq) by (unfold rbase; rewrite Dpr, Bpr; clear; lia).
        (* [comment removed for export] *)
        assert (FRp : exists c2 p2, 0 <= c2 <= 4 /\ 0 <= p2 < fs_nframes c2 /\ (c2 <> cid \/ p2 <> pos)
                       /\ frame_addr (e_fs E) c2 p2 <= rbase nu1 pr + vr_lo pr /\ rbase nu1 pr + vr_hi pr <= frame_addr (e_fs E) c2 p2 + fake_size c2).
        { destruct (vr_kind pr) as [cidp flp| | | |] eqn:Kp; try (destruct Kpr; fail).
          - destruct (LFK _ _ _ Hpr Kp) as (cp & Hcp & Ecid & Cc & Cp & RBcp & NLcp).
            destruct PK as (_ & _ & Plo & Phi & _). exists (fst cp), (snd cp).
            split; [exact Cc|]. split; [exact Cp|]. split.
            + destruct (Z.eq_dec (fst cp) cid) as [E1|]; [|left; assumption]. destruct (Z.eq_dec (snd cp) pos) as [E2|]; [|right; assumption].
              exfalso. destruct SLOT as [(SL & fl0 & K0 & RB0)|[SL KA]].
              * (* [comment removed for export] *)
                specialize (LV3 r0 pr Hr0 Hpr). rewrite K0, Kp in LV3. apply (LV3 ltac:(rewrite Bpr; exact NB)).
                rewrite RB0, RBcp, E1, E2. reflexivity.
              * apply NLcp. replace cp with (cid, pos); [exact SL|]. destruct cp; cbn in E1, E2; congruence.
            + rewrite Plo, Phi, RBcp, Ecid. clear. lia.
          - destruct PK as (_ & (c2 & p2 & L1 & L2 & L3) & _). destruct (FVAL _ L1) as [Cc Cp]. cbn [fst snd] in Cc, Cp.
            exists c2, p2. split; [exact Cc|]. split; [exact Cp|]. split; [|auto].
            destruct (Z.eq_dec c2 cid) as [E1|]; [|left; assumption]. destruct (Z.eq_dec p2 pos) as [E2|]; [|right; assumption].
            exfalso. subst c2 p2. destruct SLOT as [(SL & fl0 & K0 & RB0)|[SL KA]].
            + (* [comment removed for export] *)
              destruct (LFK _ _ _ Hr0 K0) as (cp & Hcp & Ecid & Cc' & Cp' & RBx & NLx).
              rewrite RB0 in RBx. destruct (FINJ _ _ _ _ Hc Hp Cc' Cp' RBx) as [E3 E4].
              apply NLx. replace cp with (cid, pos); [exact L1|]. destruct cp; cbn in E3, E4; congruence.
            + exact (AV3 _ _ _ _ _ _ Hw RS Gpr Kp KA NB). }
        destruct FRp as (c2 & p2 & Cc & Cp & NE & F1 & F2).
        pose proof (frames_disjoint (e_fs E) cid pos c2 p2 ltac:(clear -Hc; lia) Hp ltac:(clear -Cc; lia) Cp ltac:(clear -NE; lia)) as DJ.
        clear - IN Q0 RBp F1 F2 DJ YIN. lia. }
      destruct (vr_kind r0) as [cid fl| |owner|sb|] eqn:K0; try (destruct KK; fail).
      - (* [comment removed for export] *)
        destruct (LFK _ _ _ Hr0 K0) as (cp & Hcp & Ecid & Cc & Cp & RBcp & NLcp).
        destruct KIND as (_ & _ & Klo & Khi & _). rewrite Klo, Khi in Hoff.
        left. exists (fst cp), (snd cp). split; [apply in_app_iff; right; destruct cp; exact Hcp|]. split; [exact Cc|]. split; [exact Cp|].
        assert (YIN : frame_addr (e_fs E) (fst cp) (snd cp) <= rbase nu1 r0 + off < frame_addr (e_fs E) (fst cp) (snd cp) + fake_size (fst cp)).
        { rewrite RBcp. rewrite <- Ecid in Hoff. clear - Hoff. lia. }
        split; [exact YIN|].
        intros i lo hi bq c Hw RS. destruct (Pos.eq_dec (vr_base r0) bq) as [EB|NB].
        + (* [comment removed for export] *)
          destruct (WADM _ _ _ _ _ Hw RS) as (pr & Gpr & Hpr & Bpr & Dpr & _).
          assert (pr = r0) as -> by (apply (nodup_map_inj vr_base _ _ _ NDA Hpr Hr0); rewrite Bpr, EB; reflexivity).
          specialize (AV1 _ _ _ _ _ Hw RS EB). unfold rbase. rewrite Dpr, EB. clear - AV1. lia.
        + refine (WINF (fst cp) (snd cp) Cc Cp YIN _ i lo hi bq c Hw RS NB).
          left. split; [destruct cp; exact Hcp|]. exists fl. split; [rewrite Ecid; reflexivity|exact RBcp].
      - (* [comment removed for export] *)
        destruct KIND as (_ & (cid & pos & L1 & L2 & L3) & _). destruct (FVAL _ L1) as [Cc Cp]. cbn [fst snd] in Cc, Cp.
        left. exists cid, pos. split; [apply in_app_iff; left; exact L1|]. split; [exact Cc|]. split; [exact Cp|].
        assert (YIN : frame_addr (e_fs E) cid pos <= rbase nu1 r0 + off < frame_addr (e_fs E) cid pos + fake_size cid) by (clear - L2 L3 Hoff; lia).
        split; [exact YIN|].
        intros i lo hi bq c Hw RS. destruct (Pos.eq_dec (vr_base r0) bq) as [EB|NB].
        + destruct (WADM _ _ _ _ _ Hw RS) as (pr & Gpr & Hpr & Bpr & Dpr & _).
          assert (pr = r0) as -> by (apply (nodup_map_inj vr_base _ _ _ NDA Hpr Hr0); rewrite Bpr, EB; reflexivity).
          specialize (AV1 _ _ _ _ _ Hw RS EB). unfold rbase. rewrite Dpr, EB. clear - AV1. lia.
        + refine (WINF cid pos Cc Cp YIN _ i lo hi bq c Hw RS NB). right; auto.
      - (* [comment removed for export] *)
        destruct KIND as (_ & KD & KSP & KDT & KFS & KOTH).
        destruct (Pos.eq_dec sb SP0) as [->|NSP].
        + destruct (KSP eq_refl) as (KB & Klo & Khi). right; left. exists off.
          assert (N8 : nu1 SP8 = e_sp0 (ev1 E) / 8) by (apply HF2; reflexivity).
          split; [unfold rbase; rewrite KD, KB, N8; reflexivity|]. split; [clear - Klo Khi Hoff; lia|].
          exact (AV2 eq_refl).
        + destruct (Pos.eq_dec sb DATA) as [->|NDT]; [unfold is_data_shadow in ND; rewrite K0 in ND; discriminate|].
          destruct (KOTH NSP NDT KFS) as (ro & Gro & B8 & M). destruct (rgn_get_in _ _ _ Gro) as [Hro Bro].
          right; right.
          destruct (vr_kind ro) as [cr flr| | | |] eqn:Kro; try (destruct M; fail).
          * destruct M as (E8 & Klo & Khi). destruct (LFK _ _ _ Hro Kro) as (cp & Hcp & Ecid & Cc & Cp & RBcp & NLcp).
            destruct (FRM8 (fst cp) (snd cp) Cc) as [FM _].
            exists (fst cp), (snd cp), off. split; [apply in_app_iff; right; destruct cp; exact Hcp|]. split; [exact Cc|]. split; [exact Cp|].
            rewrite RBcp in E8. pose proof (Z.div_mod (frame_addr (e_fs E) (fst cp) (snd cp)) 8 ltac:(clear; lia)) as DQ. rewrite FM, Z.add_0_r in DQ.
            rewrite <- Ecid in Khi.
            split; [unfold rbase; rewrite KD; clear - E8 DQ; lia|].
            pose proof (Z.div_mod (fake_size (fst cp)) 8 ltac:(clear; lia)) as DQ2. rewrite (proj2 (FRM8 (fst cp) (snd cp) Cc)), Z.add_0_r in DQ2.
            clear - Klo Khi Hoff DQ2. lia.
          * destruct M as (E8 & _ & cid & pos & L1 & L2 & L3). destruct (FVAL _ L1) as [Cc Cp]. cbn [fst snd] in Cc, Cp.
            destruct (FRM8 cid pos Cc) as [FM SM].
            pose proof (Z.div_mod (frame_addr (e_fs E) cid pos) 8 ltac:(clear; lia)) as DQ. rewrite FM, Z.add_0_r in DQ.
            pose proof (Z.div_mod (fake_size cid) 8 ltac:(clear; lia)) as DQ2. rewrite SM, Z.add_0_r in DQ2.
            exists cid, pos, (nu1 (vr_base r0) + off - frame_addr (e_fs E) cid pos / 8).
            split; [apply in_app_iff; left; exact L1|]. split; [exact Cc|]. split; [exact Cp|].
            split; [unfold rbase; rewrite KD; clear; lia|]. clear - L2 L3 Hoff DQ DQ2. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma apply_exit2v_ok : exists B1', apply_exit2v (v1 B) sigma spoff (v1 SX) = Some (B1', sigmax).
    Proof using CB DONE HB HB' HGm HJ0 NX SIGB VIN XEXT XG XIN.
      pose proof HGm as (HV1 & _). pose proof HV1 as (HE&HMC&HF&HS&HC&HMo&HV&HR&HSl&HGl&HN&HB0). pose proof HB0 as (B10&B11&_).
      pose proof CB as CBc.
      unfold call_base2 in CBc. change (de2_P D) with P in CBc. change (de2_G D) with G in CBc.
      destruct (kill_wrgn A0 sigma (kill_shadow_sp (vp_frame (p1 P)) (u1 V) spoff (kill_fs_cells (vs_rgn A0))) (u2_wrgn V)) as [rgB|] eqn:KW; [|discriminate].
      assert (SINJ : forall (x y : vstate2), Some x = Some y -> x = y) by (clear; intros x y Hxy; injection Hxy as H'; exact H').
      pose proof (SINJ _ _ CBc) as EB.
      destruct (call_base2v_shape (v1 A0)) as (Q1&Q2&_).
      assert (VB : v1 B = call_base2v (ge2_CI G) (v1 A0) (u1 V) spoff npc) by (rewrite <- EB; reflexivity).
      unfold apply_exit2v. rewrite VB, Q2.
      assert (ENX : vs_next (v1 A0) = b) by (rewrite HB; reflexivity). rewrite ENX.
      assert (EnJ : (Pos.to_nat (vs_next (v1 SX)) - Pos.to_nat FIRST_FRESH2)%nat = nJ).
      { change (vs_next (v1 SX)) with (cs_next (c1 X)). clear -NX. unfold FIRST_FRESH2 in *. lia. }
      rewrite EnJ. fold sigmax. rewrite Q1.
      assert (SAT0 : sat nu2x (vs_store (v1 A0))).
      { eapply sat_ext; [|exact HS]. intros s Hs. symmetry. apply nu2x_old. rewrite HB. eapply store_below_sound; eauto. }
      assert (SB0 : store_below (vs_store (v1 A0)) b' = true).
      { eapply store_below_mono; [|exact B11]. rewrite ENX. clear -HB'; lia. }
      destruct (add_boxes2_sound (pm_elements (sbox (vs_store (v1 SX)))) (vs_store (v1 A0)) SAT0 SB0) as (S1 & E1' & SAT1 & SB1);
        [intros; apply pm_elements_sound; auto|]. rewrite E1'.
      destruct (add_congs2_sound (pm_elements (scong (vs_store (v1 SX)))) S1 SAT1 SB1) as (S2 & E2' & SAT2 & SB2);
        [intros; apply pm_elements_sound; auto|]. rewrite E2'.
      destruct (add_conss2_sound (scons (vs_store (v1 SX))) S2 SAT2 SB2) as (S3 & E3' & SAT3 & SB3); [auto|]. rewrite E3'.
      eexists. reflexivity.
    Qed.

    Theorem apply_exit2_sound B' :
      apply_exit2 B sigma spoff SX = Some B' ->
      vstate_below_b (v1 B') = true -> globs_in_fcells P B' = true ->
      gammaP B' nu2x regs2 mem2 /\ vs2_pc B' = npc /\ vs2_next B' = b'
      /\ (forall a, In a (own_flags B' nu2x) <-> In a (own_flags A0 nu1)).
    Proof using BO0 CB D1 DONE FP GV HB HB' HGm HJ0 HL NPC NX PO PO0 SIGB VIN XEXT XFL XFM XG XIN XRA XREGS mem_e rgK.
      intros HBE HWF HGF.
      pose proof HGm as (HV1 & HE2 & HMC2 & HF2 & HDD & HRG & HLV & HB2 & HGL & HFLI & HMEM).
      pose proof HV1 as (HE&HMC&HF&HS&HC&HMo&HV&HR&HSl&HGl&HN&HB0). pose proof HB0 as (B10&B11&B12&B13&B14&(B15&B16&B17)).
      pose proof (gamma2_v1 _ _ _ _ _ _ _ _ XG) as XG1.
      pose proof XG1 as (_&XMC&_&XS&_&_&XV&XR&XSl&XGl&XN&_). destruct XBEL as [(Y10&Y11&Y12&Y13&Y14&(Y15&Y16&Y17)) J0].
      assert (B10b : (LAST_FIXED < b)%positive) by (rewrite HB; exact B10). clear B10 Y10.
      (* [comment removed for export] *)
      pose proof CB as CBc.
      unfold call_base2 in CBc. change (de2_P D) with P in CBc. change (de2_G D) with G in CBc.
      destruct (kill_wrgn A0 sigma (kill_shadow_sp (vp_frame (p1 P)) (u1 V) spoff (kill_fs_cells (vs_rgn A0))) (u2_wrgn V)) as [rgB|] eqn:KW; [|discriminate].
      (* [comment removed for export] *)
      assert (SINJ : forall (x y : vstate2), Some x = Some y -> x = y) by (clear; intros x y Hxy; injection Hxy as H'; exact H').
      pose proof (SINJ _ _ CBc) as EB.
      destruct (call_base2v_shape (v1 A0)) as (Q1&Q2&Q3&Q4&Q5&Q6&Q7&Q8&Q9&Q10&Q11&Q12).
      (* [comment removed for export] *)
      assert (VB : v1 B = call_base2v (ge2_CI G) (v1 A0) (u1 V) spoff npc) by (rewrite <- EB; reflexivity).
      assert (RGB : vs_rgn B = rgB) by (rewrite <- EB; reflexivity).
      assert (LVB : vs_live B = vs_live A0) by (rewrite <- EB; reflexivity).
      assert (DDB : vs_divdef B = vs_divdef A0) by (rewrite <- EB; reflexivity).
      unfold apply_exit2, apply_exit2w in HBE. rewrite RGB, LVB, DDB in HBE. unfold apply_exit2v in HBE. rewrite VB, Q2 in HBE.
      assert (ENX : vs_next (v1 A0) = b) by (rewrite HB; reflexivity). rewrite ENX in HBE.
      assert (EnJ : (Pos.to_nat (vs_next (v1 SX)) - Pos.to_nat FIRST_FRESH2)%nat = nJ).
      { change (vs_next (v1 SX)) with (cs_next (c1 X)). clear -NX. unfold FIRST_FRESH2 in *. lia. }
      rewrite EnJ in HBE. fold sigmax in HBE. rewrite Q1 in HBE.
      assert (Eb' : Pos.of_nat (Pos.to_nat b + nJ) = b') by (clear -HB'; lia). rewrite Eb' in HBE.
      assert (SAT0 : sat nu2x (vs_store (v1 A0))).
      { eapply sat_ext; [|exact HS]. intros s Hs. symmetry. apply nu2x_old. rewrite HB. eapply store_below_sound; eauto. }
      assert (SB0 : store_below (vs_store (v1 A0)) b' = true).
      { eapply store_below_mono; [|exact B11]. rewrite ENX. clear -HB'; lia. }
      destruct (add_boxes2_sound (pm_elements (sbox (vs_store (v1 SX)))) (vs_store (v1 A0)) SAT0 SB0) as (S1 & E1' & SAT1 & SB1);
        [intros; apply pm_elements_sound; auto|]. rewrite E1' in HBE.
      destruct (add_congs2_sound (pm_elements (scong (vs_store (v1 SX)))) S1 SAT1 SB1) as (S2 & E2' & SAT2 & SB2);
        [intros; apply pm_elements_sound; auto|]. rewrite E2' in HBE.
      destruct (add_conss2_sound (scons (vs_store (v1 SX))) S2 SAT2 SB2) as (S3 & E3' & SAT3 & SB3); [auto|]. rewrite E3' in HBE.
      (* [comment removed for export] *)
      destruct (write_back_args B rgB sigmax (vs_rgn SX)) as [rg'|] eqn:WBK; [|discriminate].
      apply SINJ in HBE.
      (* [comment removed for export] *)
      match type of HBE with mkVS2 ?Bf _ _ _ _ = _ => set (BF := Bf) in HBE end.
      assert (FS : vs_store BF = S3) by reflexivity.
      assert (FN : vs_next BF = b') by reflexivity.
      assert (FPc : vs_pc BF = npc) by (unfold BF; cbn [vs_pc]; exact Q6).
      assert (FC : vs_conddef BF = vs_conddef (v1 A0)) by (unfold BF; cbn [vs_conddef]; exact Q3).
      assert (FM : vs_moddef BF = vs_moddef (v1 A0)) by (unfold BF; cbn [vs_moddef]; exact Q4).
      assert (FV : vs_valset BF = set_exit_valsets (vs_valset (v1 A0)) sigmax (pm_elements (vs_valset (v1 SX)))) by (unfold BF; cbn [vs_valset]; rewrite Q5; reflexivity).
      assert (FR : vs_regs BF = reg_upd (reg_upd (pm_set (reg_key 1) (lconst npc) (regs_tops (vs_regs (v1 A0)) CALLER_SAVED)) 10 (osubst2_v sigmax (get_reg (v1 SX) 10))) 11 (osubst2_v sigmax (get_reg (v1 SX) 11))) by (unfold BF; cbn [vs_regs]; rewrite Q7; reflexivity).
      assert (FSl : vs_slots BF = set_exit_slots2 (kill_ranges (cm_kill (vs_slots (v1 A0)) STACK_BOTTOM spoff) (u_wstack (u1 V))) sigmax spoff (vs_slots (v1 SX))) by (unfold BF; cbn [vs_slots]; rewrite Q8; reflexivity).
      assert (FG : vs_globs BF = set_exit_globs2 (let gl0 := kill_cells (vs_globs (v1 A0)) (u_wglobs (u1 V)) in
                                                  if u_errno (u1 V) then cm_kill gl0 (ci_errno (ge2_CI G)) (ci_errno (ge2_CI G) + 4) else gl0) sigmax (vs_globs (v1 SX))) by (unfold BF; cbn [vs_globs]; rewrite Q9; reflexivity).
      assert (FNl : vs_nul BF = add_exit_nuls (List.filter (nul_survives spoff (u_wstack (u1 V))) (vs_nul (v1 A0))) spoff (vs_nul (v1 SX))) by (unfold BF; cbn [vs_nul]; rewrite Q10; reflexivity).
      clearbody BF. subst B'. cbn [v1 vs_rgn vs_live vs_divdef own_flags] in HWF, HGF |- *.
      change (vs2_pc (mkVS2 BF rg' (vs_live A0) (set_exit_divdefs (vs_divdef A0) sigmax (pm_elements (vs_divdef SX))) [])) with (vs_pc BF).
      change (vs2_next (mkVS2 BF rg' (vs_live A0) (set_exit_divdefs (vs_divdef A0) sigmax (pm_elements (vs_divdef SX))) [])) with (vs_next BF).
      (* [comment removed for export] *)
      pose proof HLV as (_ & _ & _ & NDA).
      pose proof (thins_trans _ _ _ (kill_fs_cells_thins (vs_rgn A0)) (kill_shadow_sp_thins (vp_frame (p1 P)) (u1 V) spoff _)) as T01.
      pose proof (thins_bases _ _ T01) as BS01.
      destruct (kill_wrgn_spec A0 sigma _ _ _ KW ltac:(rewrite BS01; exact NDA)) as (T1B & WIN & HAV).
      pose proof (thins_trans _ _ _ T01 T1B) as T0B.
      assert (NDB : List.NoDup (map vr_base rgB)) by (rewrite (thins_bases _ _ T0B); exact NDA).
      destruct (write_back_spec B sigmax _ _ _ WBK NDB) as [SHW PROV].
      pose proof (shape_map_trans _ _ _ (thins_shape _ _ T0B) SHW) as SH0.
      assert (OWNEQ : forall a, In a (own_flags (mkVS2 BF rg' (vs_live A0) (set_exit_divdefs (vs_divdef A0) sigmax (pm_elements (vs_divdef SX))) []) nu2x) <-> In a (own_flags A0 nu1)).
      { intros a. rewrite (own_flags_shape A0 BF rg' nu2x (vs_live A0) _ [] SH0).
        rewrite (own_flags_ext A0 nu1 nu2x ltac:(intros s Hs; apply nu2x_old; rewrite HB; exact Hs) HB2). tauto. }
      split; [|split; [exact FPc|split; [exact FN|exact OWNEQ]]].
      apply vstate_below_b_sound in HWF.
      (* [comment removed for export] *)
      pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11).
      assert (Esplo : vp_splo (p1 P) <= e_sp0 (ev1 E) <= vp_sphi (p1 P)) by exact E2. assert (Efr : vp_frame (p1 P) <= e_sp0 (ev1 E)) by exact E11.
      pose proof PO1 as (P0f&P1s&_). assert (Pfr : 0 <= vp_frame (p1 P)) by exact P0f. assert (Psphi : vp_sphi (p1 P) < 2 ^ 64) by exact P1s.
      destruct (zpatch_env_indep P E EV (PO2_zsyms SEGS P PO) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as (ZRW & ZREG & ZP).
      assert (GV1 : gamma SEGS (p1 P) (ev1 E) (zpatch P E mem0 mem2) BF nu2x regs2 mem2).
      { split; [exact HE|]. split.
        { destruct XMC as (M1' & M2 & M3 & M4). split; [exact M1'|]. split; [exact M2|]. split; [exact M3|].
          eapply frame_mod_mem0_ext; [|exact M4]. intros a. rewrite ZP. reflexivity. }
        split.
        { eapply gamma_fix_ext; [|exact ext_b|exact HF]. exact B10b. }
        split; [rewrite FS; exact SAT3|]. split.
        { intros bb k x y Hg. rewrite FC in Hg. eapply (conddef_ext (vs_conddef (v1 A0)) nu1 nu2x b); eauto.
          - intros; rewrite HB; eapply B15; eauto.
          - apply ext_b. }
        split.
        { intros r x md Hg. rewrite FM in Hg. eapply (moddef_ext (vs_moddef (v1 A0)) nu1 nu2x b); eauto.
          - intros; rewrite HB; eapply B16; eauto.
          - apply ext_b. }
        split.
        { (* [comment removed for export] *)
          intros s zs Hg. rewrite FV in Hg. apply set_exit_valsets_get in Hg as [Hg|(s0 & Hin0 & SI & PM)].
          - rewrite nu2x_old; [apply HV; exact Hg|]. rewrite HB. eapply B17; eauto.
          - apply pm_elements_sound in Hin0. pose proof (XV _ _ Hin0) as Hv.
            assert (Hs0 : (s0 < cs_next (c1 X))%positive) by exact (Y17 _ _ Hin0).
            pose proof (lsubst_eval_x (lsym s0) (lin_below_lsym _ _ Hs0)) as EV0. rewrite eval_lsym in EV0.
            rewrite eval_lsubst, eval_lsym in EV0. unfold vsubst in EV0.
            unfold sym_image in SI. unfold pm_mem in PM. destruct (pm_get s0 sigmax) as [e0|] eqn:G0; [|discriminate].
            destruct (lin_single e0) as [[s1 k1]|] eqn:LS; [|discriminate].
            destruct (Z.eqb_spec k1 1); [|discriminate]. destruct (Z.eqb_spec (lc e0) 0); [|discriminate].
            simpl in SI. inversion SI; subst s1. rewrite (eval_single _ _ _ _ LS) in EV0.
            replace (nu2x s) with (nuV' s0) by (clear - EV0 e e1; lia). exact Hv. }
        split.
        { (* [comment removed for export] *)
          intros r e Hr0 Hg. rewrite FR in Hg.
          pose proof (rz_pos_of2 r Hr0) as RP. change (bv_unsigned r) with (rz r) in Hg |- *.
          assert (GEN10 : forall z e0 e', get_reg (v1 SX) z = Some e0 -> osubst2 sigmax e0 = Some e' -> rz r = z ->
                          bv_unsigned (getr regs2 r) = zwrap 64 (eval nu2x e')).
          { intros z e0 e' Hz Ho Hrz. unfold get_reg in Hz. destruct (Z.eqb_spec z 0) as [Ez|Ez]; [exfalso; clear -Ez Hrz Hr0; unfold rz in *; lia|].
            rewrite <- Hrz in Hz. rewrite (osubst2_eval _ _ (Y12 _ _ Hz) Ho). exact (XR r e0 Hr0 Hz). }
          apply reg_upd_get2 in Hg as [[K11 V11]|[K11 Hg]].
          { destruct (get_reg (v1 SX) 11) as [e0|] eqn:G11; [|discriminate]. simpl in V11.
            eapply (GEN10 11); eauto. apply reg_key_eq2; auto; [clear -RP|clear]; lia. }
          apply reg_upd_get2 in Hg as [[K10 V10]|[K10 Hg]].
          { destruct (get_reg (v1 SX) 10) as [e0|] eqn:G10; [|discriminate]. simpl in V10.
            eapply (GEN10 10); eauto. apply reg_key_eq2; auto; [clear -RP|clear]; lia. }
          rewrite pm_get_set in Hg.
          destruct (Pos.eqb_spec (reg_key (rz r)) (reg_key 1)) as [K1|K1].
          { inversion Hg; subst e. rewrite eval_lconst.
            assert (r = 1%bv).
            { apply bv_eq. apply reg_key_eq2 in K1; [|clear -RP; lia|clear; lia]. unfold rz in K1. rewrite K1. reflexivity. }
            subst r. rewrite XRA. rewrite u_wordZ by (clear -NPC; lia). symmetry. apply zwrap_id. clear -NPC; lia. }
          apply regs_tops_get in Hg as [Hg Hnot].
          rewrite (eval_ext_below _ _ _ _ ext_b) by (rewrite HB; exact (B12 _ _ Hg)).
          apply kept_reg; [exact Hr0| |exact Hg].
          destruct (in_CALLER_SAVED_dec2 (rz r) RP) as [Hcs|Hk]; [|exact Hk].
          exfalso. apply (Hnot _ Hcs); [clear -RP Hcs|reflexivity].
          unfold CALLER_SAVED in Hcs. simpl in Hcs. lia. }
        split.
        { (* [comment removed for export] *)
          intros off w v Hin. rewrite FSl in Hin. apply set_exit_slots2_in in Hin as [Hin|(v0 & e & Hin & Hoff & Ho & Hv)]; cbn [fst snd] in Hin; [|cbn [fst snd] in Hoff, Ho, Hv; subst v].
          - apply kill_ranges_in in Hin as [Hin Hdis]. cbn [fst snd] in Hdis.
            pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin) as Hbot. apply cm_kill_sub in Hin.
            destruct (HSl _ _ _ Hin) as [(R1&R2&R3) CH]. split; [split; [exact R1|split; [exact R2|exact R3]]|].
            assert (Hoff : spoff <= off) by (unfold STACK_BOTTOM in Hbot; clear - Hbot R1 R2 Efr Pfr Esplo Psphi; lia).
            destruct v as [e|]; [|exact I]. cbn [cell_holds] in CH |- *.
            rewrite (eval_ext_below _ _ _ _ ext_b) by (rewrite HB; exact (B13 _ _ _ Hin)).
            rewrite rdn_unchanged2; [exact CH|clear - R1 R2 R3 Efr Pfr Esplo Psphi; lia|clear - R1 R2 R3 Efr Pfr Esplo Psphi; lia|clear - Hoff; lia| | |].
            + intros lo hi Hr. specialize (Hdis _ _ Hr). clear - Hdis R2. lia.
            + intros c Hc. pose proof (wcells_PV_bound _ Hc). clear - H R1 R3 Efr Esplo. lia.
            + intros _. left. clear - R1 R2 R3. lia.
          - destruct (XSl _ _ _ Hin) as [(R1&R2&R3) CH]. split; [split; [exact R1|split; [exact R2|exact R3]]|].
            destruct v0 as [e0|]; [|discriminate]. simpl in Ho. cbn [cell_holds] in CH |- *.
            rewrite (osubst2_eval _ _ (Y13 _ _ _ Hin) Ho). exact CH. }
        split.
        { (* [comment removed for export] *)
          intros a w v Hin. rewrite FG in Hin. apply set_exit_globs2_in in Hin as [Hin|(v0 & Hin & Hv)]; cbn [fst snd] in Hin; [|cbn [fst snd] in Hv; subst v].
          - assert (Hin' : In (a, (w, v)) (kill_cells (vs_globs (v1 A0)) (u_wglobs (u1 V)))
                           /\ (u_errno (u1 V) = true -> ~ (a < ci_errno (ge2_CI G) + 4 /\ ci_errno (ge2_CI G) < a + w))).
            { destruct (u_errno (u1 V)); [|split; [exact Hin|discriminate]].
              split; [eapply cm_kill_sub; eauto|]. intros _. exact (cm_kill_disjoint _ _ _ _ _ _ Hin). }
            clear Hin. destruct Hin' as [Hin Herr]. apply kill_cells_in in Hin as [Hin Hdis]. cbn [fst snd] in Hdis.
            destruct (HGl _ _ _ Hin) as [(R1&R2&R3) CH]. split; [split; [exact R1|split; [exact R2|exact R3]]|].
            destruct v as [e|]; [|exact I]. cbn [cell_holds] in CH |- *.
            rewrite (eval_ext_below _ _ _ _ ext_b) by (rewrite HB; exact (B14 _ _ _ Hin)).
            replace a with (0 + a) by (clear; lia).
            rewrite rdn_unchanged2; [exact CH|clear - R1 R2 R3 Efr Pfr Esplo Psphi; lia|clear - R1 R2 R3 Efr Pfr Esplo Psphi; lia|clear - R1 R2 R3 Esplo; lia| | |].
            + intros lo hi Hr. pose proof (wstack_V_bound _ _ Hr). clear - H R2 R3 Esplo. lia.
            + intros c Hc. unfold PV, unit_params2, unit_wcells2 in Hc. cbn [p1 vp_wcells] in Hc. apply in_app_iff in Hc as [Hc|Hc].
              * destruct (u_errno (u1 V)); [|destruct Hc]. destruct Hc as [<-|[]]. simpl. specialize (Herr eq_refl). clear - Herr R2. lia.
              * destruct c as [ca cn]. specialize (Hdis _ _ Hc). simpl. clear - Hdis R2. lia.
            + intros FSNZ. right. destruct (HGL ltac:(unfold asan_mode; destruct (vp_fs P); [reflexivity|exfalso; exact (FSNZ eq_refl)]) _ _ _ Hin) as (f & Hf & F1 & F2).
              exists f. split; [exact Hf|]. clear - F1 F2 R2. lia.
          - destruct (XGl _ _ _ Hin) as [(R1&R2&R3) CH]. split; [split; [exact R1|split; [exact R2|exact R3]]|].
            destruct v0 as [e0|]; [|exact I]. simpl. cbn [cell_holds] in CH |- *.
            destruct (osubst2 sigmax e0) as [e|] eqn:Ho; [|exact I]. cbn [cell_holds].
            rewrite (osubst2_eval _ _ (Y14 _ _ _ Hin) Ho). exact CH. }
        split.
        { (* [comment removed for export] *)
          intros lo hi Hin. rewrite FNl in Hin. apply add_exit_nuls_in in Hin as [Hin|Hin].
          - apply filter_In in Hin as [Hin Hsv]. unfold nul_survives in Hsv. cbn [fst snd] in Hsv.
            apply andb_prop in Hsv as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Bool.negb_true_iff in Hs2.
            destruct (HN _ _ Hin) as (off & b0 & H1 & H2 & H3 & H4).
            exists off, b0. split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
            rewrite <- H3. apply (rdn_unchanged2 (e_sp0 (ev1 E) + off) 1); simpl.
            + clear - H2 Efr Pfr Esplo Psphi. lia.
            + clear - H2 Efr Pfr Esplo Psphi. lia.
            + clear - H1 Hs1. lia.
            + intros lo' hi' Hr.
              assert (NE : ~ (lo < hi' /\ lo' <= hi)).
              { intros Y1.
                assert (X1 : existsb (fun r : Z * Z => (lo <? snd r) && (fst r <=? hi)) (u_wstack (u1 V)) = true).
                { apply existsb_exists. exists (lo', hi'). split; [exact Hr|]. cbn [fst snd].
                  apply andb_true_intro. split; [apply Z.ltb_lt|apply Z.leb_le]; clear -Y1; lia. }
                rewrite X1 in Hs2. discriminate. }
              clear -NE H1. lia.
            + intros c Hc. pose proof (wcells_PV_bound _ Hc). clear - H H2 Efr Esplo. lia.
            + intros _. left. change (vp_frame (p1 (ge2_P0 G))) with (vp_frame (p1 P)). clear - H2. cbn [Z.of_nat Pos.of_succ_nat]. lia.
          - destruct (XN _ _ Hin) as (off & b0 & H1 & H2 & H3 & H4). exists off, b0.
            split; [exact H1|]. split; [exact H2|]. split; [exact H3|exact H4]. }
        exact HWF. }
      (* [comment removed for export] *)
      pose proof XG as (_ & XE2 & XMC2 & XF2 & XDD & XRG & XLV & XB2 & XGL & XFI & XMM).
      pose proof HB2 as (B20 & B2R & B2L & B2D & B2M).
      destruct XB2 as (_ & XBR & _ & XBD & _).
      assert (ZLH : forall z, In z (vp_fzones P) -> zone_lo EV z = zone_lo E z /\ zone_hi EV z = zone_hi E z).
      { intros z Hz. pose proof (PO2_zsyms SEGS P PO) as ZS. rewrite forallb_forall in ZS.
        apply (zone_env_indep EV E z (ZS z Hz)); reflexivity. }
      assert (FLZ : forall a, in_flags_zone P E a -> mem2 (wordZ a) = mem1 (wordZ a)).
      { intros a Ha. apply XFL. exact Ha. }
      assert (MG12 : mem_grows mem1 mem2) by exact (proj2 XFM).
      (* [comment removed for export] *)
      assert (VSX : forall s, (s < FIRST_FRESH2)%positive -> vsubst nu2x sigmax s = nuV s).
      { intros s Hs. assert (HsX : (s < cs_next (c1 X))%positive) by (pose proof (proj2 XBEL) as J0'; clear - Hs J0'; eapply Pos.lt_le_trans; [exact Hs|exact J0']).
        pose proof (lsubst_eval_x (lsym s) (lin_below_lsym _ _ HsX)) as EVs.
        rewrite eval_lsubst, !eval_lsym in EVs. rewrite EVs. exact (XEXT s Hs). }
      split; [exact GV1|]. split; [exact HE2|]. split.
      { (* [comment removed for export] *)
        destruct XMC2 as (MQ1 & MQ2 & MQ3 & MQ4 & MQ5 & MQ6).
        split; [exact MQ1|]. split.
        { intros z a Hz Ha. apply (MQ2 z a Hz). unfold in_zone in Ha |- *. destruct (ZLH z Hz) as [X1 X2]. rewrite X1, X2. exact Ha. }
        split; [exact MQ3|]. split.
        { intros cp Hcp. apply (MQ4 cp). cbn [e_live EV callee_env2]. apply in_app_iff. left. exact Hcp. }
        split; [|exact MQ6].
        eapply (rtctx_ok_env SEGS PV P EV E); try reflexivity; [|exact MQ5]. intros x. rewrite ZRW. reflexivity. }
      split.
      { assert (B75 : (75 < b)%positive) by (rewrite HB; unfold vs2_next; clear - B20; unfold LAST_FIXED2 in B20; lia).
        exact (@VStepMem2SoundA.gamma_fix2_ext E b nu1 nu2x B75 ext_b HF2). }
      split.
      { (* [comment removed for export] *)
        intros q x m Hq. cbn [vs_divdef] in Hq. apply set_exit_divdefs_get in Hq as [Hq|(q0 & x0 & Hin0 & J0q & SI & OS)].
        - destruct (HDD q x m Hq) as [DD1 DD2]. destruct (B2D q x m Hq) as [DQ1 DQ2]. split; [exact DD1|].
          rewrite nu2x_old by (rewrite HB; exact DQ1). rewrite (eval_ext_below _ _ _ _ ext_b) by (rewrite HB; exact DQ2). exact DD2.
        - apply pm_elements_sound in Hin0. destruct (XDD q0 x0 m Hin0) as [DD1 DD2]. destruct (XBD q0 x0 m Hin0) as [DQ1 DQ2].
          change (vs_next (v1 SX)) with (cs_next (c1 X)) in DQ1, DQ2.
          split; [exact DD1|]. rewrite (osubst2_eval _ _ DQ2 OS), <- DD2.
          unfold isv_join2 in J0q. apply Pos.leb_le in J0q.
          unfold sym_image in SI. unfold sigmax in SI. rewrite sigma_joins_get in SI.
          destruct (Z.leb_spec (Z.pos FIRST_FRESH2) (Z.pos q0)); [|exfalso; clear - J0q H; lia].
          destruct (Z.ltb_spec (Z.pos q0) (Z.pos FIRST_FRESH2 + Z.of_nat nJ)); [|exfalso; pose proof NX as NX'; clear - DQ1 H0 NX'; lia].
          cbn [andb lin_single lsym lt lc Z.eqb] in SI. injection SI as <-. apply nu2x_new; [exact J0q|exact DQ1]. }
      (* [comment removed for export] *)
      assert (REG : forall r', In r' rg' ->
                region_ok SEGS P E nu2x (mkVS2 BF rg' (vs_live A0) (set_exit_divdefs (vs_divdef A0) sigmax (pm_elements (vs_divdef SX))) []) mem2 r'
                /\ cells_syms_below (vr_cells r') b').
      { intros r' Hr'.
        destruct (PROV r' Hr') as (r & HrB & SHr & NULr & CELLr).
        assert (HrB' : In r (vs_rgn B)) by (rewrite RGB; exact HrB).
        destruct (pipeline_facts r HrB') as (r0 & Hr0 & SH0r & CI0 & NI0 & KFS & KSP & KWIN & KHAV).
        pose proof (rshape_trans _ _ _ SH0r SHr) as SH0r'.
        pose proof SH0r as (SBr & SDr & SKr & SLr & SHIr & SWr & S8r).
        pose proof (HRG _ Hr0) as ROK0. pose proof ROK0 as (RB1 & RB2 & RB3 & RDS & RCELLS & RPERM & RNUL & KIND0).
        destruct (B2R r0 Hr0) as (Bb0 & Bc0 & Bk0).
        assert (NB0 : nu2x (vr_base r0) = nu1 (vr_base r0)) by (apply nu2x_old; rewrite HB; exact Bb0).
        assert (BB' : (vs_next (v1 A0) <= b')%positive) by (change (vs_next (v1 A0)) with (vs2_next A0); rewrite <- HB; clear - HB'; lia).
        (* [comment removed for export] *)
        assert (CBL : forall e n, lin_is_const e = true -> lin_below e n = true).
        { clear. intros e n C. unfold lin_is_const in C. unfold lin_below. destruct (lt e); [reflexivity|discriminate]. }
        (* [comment removed for export] *)
        assert (SURVO : forall off, vr_lo r0 <= off < vr_hi r0 -> avoid r0 off ->
                  match vr_kind r0 with RK_flag _ | RK_fs => False | _ => True end -> is_data_shadow r0 = false ->
                  outside (wordZ (rbase nu1 r0 + off)) (unit_regions2 PV EV)).
        { intros off Hoff AV KK ND. destruct (FSNZ _ Hr0) as [fsl EFS]. exact (surv_outside fsl r0 off EFS Hr0 KK ND Hoff AV). }
        (* [comment removed for export] *)
        assert (AVC : forall k w v off, In (k, (w, v)) (vr_cells r) -> k <= off < k + w -> avoid r0 off).
        { intros k w v off Hin Hko. split; [|split].
          - intros i lo hi bq c Hw RS EBq. destruct (KWIN i lo hi bq c Hw RS ltac:(rewrite SBr; exact EBq)) as [WC _].
            specialize (WC _ _ _ Hin). clear - WC Hko. lia.
          - intros K0. destruct (KSP ltac:(rewrite SKr; exact K0)) as [CS _].
            specialize (CS _ _ _ Hin). clear - CS Hko. lia.
          - intros i lo hi bq c pr Hw RS G0 KP KA NB.
            destruct (KHAV i lo hi bq c pr Hw RS G0 KP ltac:(rewrite SKr; exact KA) ltac:(rewrite SBr; exact NB)) as [C0 _].
            rewrite C0 in Hin. destruct Hin. }
        assert (AVN : forall lo hi off, In (lo, hi) (vr_nul r) -> lo <= off <= hi -> avoid r0 off).
        { intros lo hi off Hin Hko. split; [|split].
          - intros i lo' hi' bq c Hw RS EBq. destruct (KWIN i lo' hi' bq c Hw RS ltac:(rewrite SBr; exact EBq)) as [_ WN].
            specialize (WN _ Hin). cbn [fst snd] in WN. clear - WN Hko. lia.
          - intros K0. destruct (KSP ltac:(rewrite SKr; exact K0)) as [_ NS].
            specialize (NS _ Hin). cbn [fst snd] in NS. clear - NS Hko. lia.
          - intros i lo' hi' bq c pr Hw RS G0 KP KA NB.
            destruct (KHAV i lo' hi' bq c pr Hw RS G0 KP ltac:(rewrite SKr; exact KA) ltac:(rewrite SBr; exact NB)) as [_ N0].
            rewrite N0 in Hin. destruct Hin. }
        (* [comment removed for export] *)
        assert (ISr : is_shadow r = is_shadow r0) by exact (rshape_is_shadow _ _ SH0r).
        assert (CELLA : forall off w v, subcell (is_shadow r) (vr_cells r) off w v ->
                  vr_lo r0 <= off /\ 0 < w /\ off + w <= vr_hi r0 /\ rcell_holds SEGS (is_shadow r0) nu2x mem2 (rbase nu1 r0 + off) w v
                  /\ (forall e, v = Some e -> lin_below e b' = true)).
        { intros off w v Hin.
          (* [comment removed for export] *)
          destruct (subcell_src _ _ _ _ _ Hin) as (k1 & w1 & v1 & Hin1 & K3 & K4 & _).
          rewrite ISr in Hin. pose proof (subcell_trans _ _ _ _ _ _ CI0 Hin) as Hsub0.
          destruct (subcell_src _ _ _ _ _ Hsub0) as (k0 & w0 & v0 & Hin0 & K1 & K2 & PIECE).
          destruct (RCELLS _ _ _ Hin0) as (L1 & L2 & L3 & RC).
          assert (W0 : 0 < w) by (destruct PIECE as [EQ0|(_ & W & _)]; [injection EQ0 as -> -> ->; exact L2|exact W]).
          split; [clear - L1 K1; lia|]. split; [exact W0|]. split; [clear - L3 K2; lia|].
          split.
          2:{ intros e ->. destruct PIECE as [EQ0|(_ & _ & e0 & EV0 & EV1 & CE)].
              - injection EQ0 as <- <- <-. eapply lin_below_mono; [exact BB'|exact (Bc0 _ _ _ Hin0)].
              - apply CBL. injection EV1 as <-. exact CE. }
          (* [comment removed for export] *)
          assert (KK : match vr_kind r0 with RK_flag _ | RK_fs => False | _ => True end /\ is_data_shadow r0 = false).
          { split.
            - unfold kind_ok in KIND0. destruct (vr_kind r0) eqn:K0; auto.
              + destruct KIND0 as (_ & _ & _ & C00 & _). rewrite C00 in Hin0. destruct Hin0.
              + destruct (KFS ltac:(rewrite SKr; reflexivity)) as [C00 _]. rewrite C00 in Hin1. destruct Hin1.
            - destruct (is_data_shadow r0) eqn:D0; [|reflexivity]. destruct (RDS eq_refl) as (C00 & _). rewrite C00 in Hin0. destruct Hin0. }
          destruct KK as [KK ND].
          assert (OUT : forall i, 0 <= i < w -> outside (wordZ (rbase nu1 r0 + off + i)) (unit_regions2 PV EV)).
          { intros i Hi. replace (rbase nu1 r0 + off + i) with (rbase nu1 r0 + (off + i)) by (clear; lia).
            apply SURVO; [clear - L1 L3 K1 K2 Hi; lia|apply (AVC k1 w1 v1 (off + i) Hin1); clear - Hi K3 K4; lia|exact KK|exact ND]. }
          destruct PIECE as [EQ0|(ISH & _ & e0 & -> & -> & CE)].
          - (* [comment removed for export] *)
            injection EQ0 as <- <- <-.
            unfold rcell_holds in RC |- *. destruct v as [e|]; [|exact I].
            destruct (is_shadow r0 && lin_is_const e).
            + intros i Hi. destruct (RC i Hi) as (kb & Hkb & Hkv). exists kb. split; [|exact Hkv]. rewrite <- Hkb.
              apply (rdn1_same_outside SEGS mem1 mem2 _ _ XFM); [clear - RB1 RB2 L1 L3 Hi; lia|exact (OUT i Hi)].
            + unfold cell_holds in RC |- *. rewrite (eval_ext_below _ _ _ _ ext_b) by (rewrite HB; exact (Bc0 _ _ _ Hin0)).
              destruct RC as (bs & Hbs & Hv). exists bs. split; [|exact Hv]. rewrite <- Hbs.
              apply (rdn_same_outside SEGS mem1 mem2 _ _ _ XFM); [clear - RB1 L1; lia|rewrite Z2Nat.id by (clear - L2; lia); clear - RB2 L3; lia|].
              intros i Hi. rewrite Z2Nat.id in Hi by (clear - L2; lia). exact (OUT i Hi).
          - (* [comment removed for export] *)
            unfold rcell_holds in RC |- *. rewrite ISH, CE in RC |- *. cbn [andb] in RC |- *.
            intros i Hi. destruct (RC (off - k0 + i) ltac:(clear - Hi K1 K2; lia)) as (kb & Hkb & Hkv). exists kb. split; [|exact Hkv].
            replace (rbase nu1 r0 + off + i) with (rbase nu1 r0 + k0 + (off - k0 + i)) by (clear; lia). rewrite <- Hkb.
            apply (rdn1_same_outside SEGS mem1 mem2 _ _ XFM); [clear - RB1 RB2 L1 L3 K1 K2 Hi; lia|].
            replace (rbase nu1 r0 + k0 + (off - k0 + i)) with (rbase nu1 r0 + off + i) by (clear; lia). exact (OUT i Hi). }
        (* [comment removed for export] *)
        assert (CELLB : forall off w v, wb_cell B sigmax (vs_rgn SX) r off w v ->
                  vr_lo r0 <= off /\ 0 < w /\ off + w <= vr_hi r0 /\ rcell_holds SEGS (is_shadow r0) nu2x mem2 (rbase nu1 r0 + off) w v
                  /\ (forall e, v = Some e -> lin_below e b' = true)).
        { intros off w v (xr & c & off0 & w0 & v0 & Hxr & Hc0 & XD & XLO & XHI & XSH & Y1 & Y2 & Y3 & P1 & P2 & P3 & CASES).
          rewrite <- SLr, <- SHIr. split; [clear - XLO Y1 P1; lia|]. split; [exact P3|]. split; [clear - XHI Y3 P2; lia|].
          pose proof (XRG _ Hxr) as (_ & _ & _ & _ & XCELLS & _ & _ & XKIND). destruct (XCELLS _ _ _ Hc0) as (_ & _ & _ & XRC).
          destruct (XBR _ Hxr) as (_ & XBc & _). change (vs_next (v1 SX)) with (cs_next (c1 X)) in XBc.
          assert (ISH : is_shadow r0 = is_shadow xr) by (unfold is_shadow in *; rewrite <- SKr; exact (eq_sym XSH)).
          rewrite ISH.
          destruct CASES as [(KX & -> & -> & RBx & KR & e' & OSV & ->)|(KX & KR & -> & e & -> & -> & CE)].
          - (* [comment removed for export] *)
            destruct v0 as [e0|]; [|discriminate]. cbn [osubst2_v] in OSV.
            unfold kind_ok in XKIND. rewrite KX in XKIND. destruct XKIND as (_ & _ & i & Hi & BX & _).
            assert (EA : rbase nuV' xr + off0 = rbase nu1 r0 + (off0 + c)).
            { rewrite BX in RBx. unfold rbase. rewrite BX, XD, <- SDr.
              rewrite (XEXT (ASYM2 i)) by (unfold ASYM2, FIRST_FRESH2; clear - Hi; lia).
              rewrite <- (VSX (ASYM2 i)) by (unfold ASYM2, FIRST_FRESH2; clear - Hi; lia).
              rewrite (RB_eval _ _ _ nu2x _ _ _ (resolve_base_spec _ _ _ _ _ _ RBx)), SBr, NB0. clear; lia. }
            rewrite <- EA. unfold rcell_holds in XRC |- *. unfold is_shadow. rewrite KX. cbn [andb].
            unfold is_shadow in XRC. rewrite KX in XRC. cbn [andb] in XRC. unfold cell_holds in XRC |- *.
            rewrite (osubst2_eval _ _ (XBc _ _ _ Hc0) OSV). split; [exact XRC|].
            intros e1 He1. injection He1 as <-. exact (osubst2_below _ _ (XBc _ _ _ Hc0) OSV).
          - (* [comment removed for export] *)
            unfold kind_ok in XKIND. rewrite KX in XKIND. destruct XKIND as (_ & XDS & XSP & _). destruct (XSP eq_refl) as (BX & _).
            unfold kind_ok in KIND0. rewrite <- SKr, KR in KIND0. destruct KIND0 as (_ & RD0 & RSP & _). destruct (RSP eq_refl) as (B0 & _).
            assert (EA : rbase nuV' xr = rbase nu1 r0).
            { unfold rbase. rewrite BX, XDS, B0, RD0. change (vp_shoff PV) with (vp_shoff P).
              rewrite (XEXT SP8) by (unfold SP8, FIRST_FRESH2; clear; lia).
              unfold nuV, vsubst. destruct (pm_get SP8 sigma) as [e8|] eqn:G8; [|reflexivity].
              exfalso. destruct (BO0 _ _ G8) as [X8|X8]; [|cbv in X8; discriminate].
              assert (SF8 : pm_get SP8 sigma00 = None) by exact (sigma00_fixed Am npc SP8 eq_refl).
              unfold sigma00, A0 in SF8, X8. rewrite SF8 in X8. discriminate. }
            rewrite <- EA.
            unfold rcell_holds in XRC |- *. unfold is_shadow. rewrite KX, CE. cbn [andb].
            unfold is_shadow in XRC. rewrite KX, CE in XRC. cbn [andb] in XRC. split.
            + (* [comment removed for export] *)
              intros i Hi. destruct (XRC (off - off0 + i) ltac:(clear - Hi P1 P2; lia)) as (kb & Hkb & Hkv). exists kb. split; [|exact Hkv].
              replace (rbase nuV' xr + off + i) with (rbase nuV' xr + off0 + (off - off0 + i)) by (clear; lia). exact Hkb.
            + intros e1 He1. injection He1 as <-. apply CBL. exact CE. }
        assert (CELLS' : forall off w v, In (off, (w, v)) (vr_cells r') ->
                  vr_lo r0 <= off /\ 0 < w /\ off + w <= vr_hi r0 /\ rcell_holds SEGS (is_shadow r0) nu2x mem2 (rbase nu1 r0 + off) w v
                  /\ (forall e, v = Some e -> lin_below e b' = true)).
        { intros off w v Hin. destruct (CELLr _ _ _ Hin) as [Hin1|WB]; [exact (CELLA _ _ _ Hin1)|exact (CELLB _ _ _ WB)]. }
        split; [|intros k w e Hin; destruct (CELLS' _ _ _ Hin) as (_ & _ & _ & _ & BL); exact (BL e eq_refl)].
        apply (region_ok_rebuild A0 _ nu1 nu2x mem1 mem2 r0 r' HE2 ROK0 SH0r' NB0).
        - destruct (vr_kind r0); auto. apply nu2x_old. rewrite HB. exact Bk0.
        - destruct (is_data_shadow r0) eqn:D0; [right|left; reflexivity].
          destruct (RDS eq_refl) as (C00 & _ & N00). rewrite NULr. split.
          + destruct (vr_cells r') as [|[k [w v]] t] eqn:EC; [reflexivity|exfalso].
            destruct (CELLr k w v ltac:(first [rewrite EC; left; reflexivity | left; reflexivity])) as [Hin1|WB].
            * destruct (subcell_src _ _ _ _ _ Hin1) as (k1 & w1 & v1 & Hk1 & _). pose proof (CI0 _ _ _ Hk1) as Hin0. rewrite C00 in Hin0. exact (subcell_in_nil _ _ _ _ Hin0).
            * destruct WB as (xr & c & off0 & w0 & v0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CASES).
              unfold is_data_shadow in D0. rewrite <- SKr in D0.
              destruct CASES as [(_ & _ & _ & _ & KR & _)|(_ & KR & _)]; [destruct (vr_kind r); try discriminate; destruct KR|rewrite KR in D0; cbv in D0; discriminate].
          + destruct (vr_nul r) as [|y t] eqn:EN; [reflexivity|]. pose proof (NI0 y ltac:(first [rewrite EN; left; reflexivity | left; reflexivity])) as Y0. rewrite N00 in Y0. destruct Y0.
        - exact MG12.
        - unfold kind_ok in KIND0. destruct (vr_kind r0) as [cid fl| | | |] eqn:K0; auto.
          destruct KIND0 as (_ & Kc & _ & _ & _ & pos & Kp & _ & Kfl & _). rewrite !rdn_1. rewrite FLZ; [reflexivity|].
          unfold in_flags_zone. destruct (vp_fs P) as [[len ssl]|] eqn:EFS; [|destruct (FSNZ _ Hr0) as [fsl EFS']; rewrite EFS in EFS'; discriminate].
          rewrite Kfl. pose proof (flag_addr_range (e_fs E) cid pos Kc Kp). unfold FS_FLAGS, FS_FRAMES in *. clear - H. lia.
        - intros s ro G0 _ _. destruct (shape_map_get _ _ _ _ SH0 G0) as (ro' & G' & SH'). exists ro'. split; [exact G'|]. split; [exact SH'|].
          apply nu2x_old. rewrite HB. exact (proj1 (B2R ro (proj1 (rgn_get_in _ _ _ G0)))).
        - unfold kind_ok in KIND0. destruct (vr_kind r0) eqn:K0; auto. cbn [vs_live].
          destruct KIND0 as (_ & _ & _ & _ & _ & pos & _ & _ & _ & _ & _ & LV). exact LV.
        - unfold kind_ok in KIND0. destruct (vr_kind r0) eqn:K0; auto.
          destruct KIND0 as (_ & _ & _ & C00 & _).
          destruct (vr_cells r') as [|[k [w v]] t] eqn:EC; [reflexivity|exfalso].
          destruct (CELLr k w v ltac:(first [rewrite EC; left; reflexivity | left; reflexivity])) as [Hin1|WB].
          + destruct (subcell_src _ _ _ _ _ Hin1) as (k1 & w1 & v1 & Hk1 & _). pose proof (CI0 _ _ _ Hk1) as Hin0. rewrite C00 in Hin0. exact (subcell_in_nil _ _ _ _ Hin0).
          + destruct WB as (xr & c & off0 & w0 & v0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CASES).
            destruct CASES as [(_ & _ & _ & _ & KR & _)|(_ & KR & _)]; rewrite SKr in KR; rewrite ?K0 in KR; [destruct KR|discriminate].
        - intros off w v Hin. destruct (CELLS' _ _ _ Hin) as (L1 & L2 & L3 & RC & _). auto.
        - (* [comment removed for export] *)
          intros lo hi Hin. rewrite NULr in Hin. pose proof (NI0 _ Hin) as Hin0.
          destruct (RNUL _ _ Hin0) as (off & bb & O1 & O2 & O3 & O4). exists off, bb. split; [exact O1|]. split; [exact O2|]. split; [|exact O4].
          rewrite <- O3.
          unfold kind_ok in KIND0. destruct (vr_kind r0) as [cid fl| |owner|sb|] eqn:K0.
          + apply (rdn1_same_outside SEGS mem1 mem2 _ _ XFM); [clear - RB1 RB2 O2; lia|].
            apply SURVO; [exact O2|exact (AVN _ _ _ Hin O1)|exact I|unfold is_data_shadow; rewrite K0; reflexivity].
          + apply (rdn1_same_outside SEGS mem1 mem2 _ _ XFM); [clear - RB1 RB2 O2; lia|].
            apply SURVO; [exact O2|exact (AVN _ _ _ Hin O1)|exact I|unfold is_data_shadow; rewrite K0; reflexivity].
          + (* [comment removed for export] *)
            destruct KIND0 as (Klo & Khi & Kd & _ & ro & cid & fl & Gro & Kro & Bfl).
            pose proof (HRG _ (proj1 (rgn_get_in _ _ _ Gro))) as (_ & _ & _ & _ & _ & _ & _ & KO). unfold kind_ok in KO. rewrite Kro in KO.
            destruct KO as (_ & Kc & _ & _ & _ & pos & Kp & _ & Kfa & _).
            rewrite !rdn_1. rewrite FLZ; [reflexivity|].
            unfold in_flags_zone. destruct (vp_fs P) as [[len ssl]|] eqn:EFS; [|destruct (FSNZ _ Hr0) as [fsl EFS']; rewrite EFS in EFS'; discriminate].
            unfold rbase. rewrite Kd, Bfl, Kfa. rewrite Klo, Khi in O2.
            pose proof (flag_addr_range (e_fs E) cid pos Kc Kp). unfold FS_FLAGS, FS_FRAMES in *. clear - H O2. lia.
          + destruct (Pos.eq_dec sb DATA) as [->|NDT].
            * destruct (RDS ltac:(unfold is_data_shadow; rewrite K0; reflexivity)) as (_ & _ & N00). rewrite N00 in Hin0. destruct Hin0.
            * apply (rdn1_same_outside SEGS mem1 mem2 _ _ XFM); [clear - RB1 RB2 O2; lia|].
              apply SURVO; [exact O2|exact (AVN _ _ _ Hin O1)|exact I|unfold is_data_shadow; rewrite K0; destruct (Pos.eqb_spec sb DATA); [contradiction|reflexivity]].
          + destruct (KFS ltac:(rewrite SKr; reflexivity)) as [_ N00]. rewrite N00 in Hin. destruct Hin. }
      split; [intros r' Hr'; exact (proj1 (REG r' Hr'))|].
      split.
      { (* [comment removed for export] *)
        assert (EXTb : ext (vs_next (v1 A0)) nu1 nu2x) by (intros s0 Hs0; apply nu2x_old; rewrite HB; exact Hs0).
        pose proof (@live_ok_frame A0 (v1 A0) nu1 nu2x EXTb HB2 HLV) as LVF.
        pose proof (live_ok_shape (with_v1 A0 (v1 A0)) BF rg' nu2x (set_exit_divdefs (vs_divdef A0) sigmax (pm_elements (vs_divdef SX))) [] LVF) as LVS.
        cbn [vs_rgn vs_live with_v1] in LVS. exact (LVS SH0). }
      split.
      { (* [comment removed for export] *)
        unfold state_below2. cbn [v1 vs_rgn vs_live vs_divdef vs_memo]. rewrite FN.
        assert (BB' : (vs_next (v1 A0) <= b')%positive) by (change (vs_next (v1 A0)) with (vs2_next A0); rewrite <- HB; clear - HB'; lia).
        split; [clear - B20 BB'; unfold LAST_FIXED2 in *; lia|].
        split.
        { intros r' Hr'. destruct (shape_map_in_back _ _ _ SH0 Hr') as (r0 & Hr0 & SHr). destruct SHr as (SB & _ & SK & _).
          destruct (B2R r0 Hr0) as (Y1 & Y2 & Y3). rewrite SB, SK. split; [clear - Y1 BB'; lia|].
          split; [exact (proj2 (REG r' Hr'))|]. destruct (vr_kind r0); auto. clear - Y3 BB'; lia. }
        split; [intros s0 Hs0; pose proof (B2L s0 Hs0); clear - H BB'; lia|].
        split; [|intros ? ? ? []].
        intros q x m Hq. apply set_exit_divdefs_get in Hq as [Hq|(q0 & x0 & Hin0 & J0q & SI & OS)].
        - destruct (B2D q x m Hq) as [DQ1 DQ2]. split; [clear - DQ1 BB'; lia|eapply lin_below_mono; [exact BB'|exact DQ2]].
        - apply pm_elements_sound in Hin0. destruct (XBD q0 x0 m Hin0) as [DQ1 DQ2]. change (vs_next (v1 SX)) with (cs_next (c1 X)) in DQ1, DQ2.
          split; [|exact (osubst2_below _ _ DQ2 OS)].
          unfold isv_join2 in J0q. apply Pos.leb_le in J0q.
          unfold sym_image in SI. unfold sigmax in SI. rewrite sigma_joins_get in SI.
          destruct (Z.leb_spec (Z.pos FIRST_FRESH2) (Z.pos q0)); [|exfalso; clear - J0q H; lia].
          destruct (Z.ltb_spec (Z.pos q0) (Z.pos FIRST_FRESH2 + Z.of_nat nJ)); [|exfalso; pose proof NX as NX'; clear - DQ1 H0 NX'; lia].
          cbn [andb lin_single lsym lt lc Z.eqb] in SI. injection SI as <-. pose proof HB' as HB''. clear - H H0 HB''. lia. }
      split; [apply globs_in_fcells_sound; exact HGF|].
      split; [|intros ? ? ? []].
      (* [comment removed for export] *)
      intros Hfs c p Hc Hp NL NO. rewrite OWNEQ in NO. destruct (HFLI Hfs c p Hc Hp NL NO) as (bb & Hbb & Hbb0).
      exists bb. split; [|exact Hbb0]. rewrite <- Hbb. apply FLZ.
      unfold in_flags_zone. destruct (vp_fs P) as [[len ssl]|] eqn:EFS; [|exfalso; exact (Hfs eq_refl)].
      pose proof (flag_addr_range (e_fs E) c p Hc Hp). unfold FS_FLAGS, FS_FRAMES in *. clear - H. lia.
    Qed.
  End PostCall2.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma zwrap64_mod2' x : zwrap 64 x mod 2 = x mod 2.
  Proof using . unfold zwrap. apply Z.mod_mod_divide. exists (2 ^ 63). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma gamma2_with_v1_set_pc Ax Y t nu regs mem : gammaP (with_v1 Ax (set_pc Y t)) nu regs mem -> gammaP (with_v1 Ax Y) nu regs mem.
  Proof using G U. intros H. destruct Y. exact H. Qed.

  Lemma fl_inv_with_v1_set_pc Ax Y t nu me mem :
    fl_inv G U E (with_v1 Ax (set_pc Y t)) nu me mem -> fl_inv G U E (with_v1 Ax Y) nu me mem.
  Proof using . intros H. destruct Y. exact H. Qed.

  Lemma vs_globs_set_reg Y r v : vs_globs (set_reg Y r v) = vs_globs Y.
  Proof using . unfold set_reg. destruct (Z.eqb r 0); [reflexivity|]. destruct Y; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma pos_le_add_aux2 : forall (r p s : positive) (n : nat), (r <= p)%positive -> Z.pos s = Z.pos p + Z.of_nat n -> (r <= s)%positive.
  Proof using . intros r p s n H1 H3. lia. Qed.

  Theorem call2_sound A (rd : reg) (imm : bv 21) vs succs nu regs mem (pc : word) w :
    do_call2 D A (wrap64 (vs2_pc A + bv_signed imm)) (npc_of (v1 A)) vs = SN2 succs ->
    vs <> [] -> vs = call_variants2 D (vs2_pc A) (wrap64 (vs2_pc A + bv_signed imm)) ->
    rz rd = 1 ->
    (FIRST_FRESH2 <= vs2_next A)%positive ->
    gammaPE A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) ->
    dstep_post2 SEGS G rom U E mem0 mem_e A succs nu regs pc mem.
  Proof using D1 DONE PO PO0 STATIC VSTEP2.
    intros Hx Hne Hvs Hrd HJ [HG HFI] Hpc Hf He Hd.
    set (tgt := wrap64 (vs2_pc A + bv_signed imm)) in *. set (npc := npc_of (v1 A)) in *.
    unfold do_call2 in Hx. destruct (sp_offset (v1 A)) as [spoff|] eqn:SPO; [|discriminate].
    destruct (try_variants2_sound _ _ _ _ _ _ _ Hx) as [V [HinV HTV]].
    rewrite Hvs in HinV. destruct (call_variants2_in G done U _ _ _ HinV) as [VIN EV].
    destruct (try_variant2_inv _ _ _ _ _ _ HTV) as (sigma0 & skip8 & sigma & B & ROOT & PRE & MATCH & FP & FDEP & PB & CB & AE & WB).
    change (de2_P D) with P in FDEP, AE, WB, MATCH.
    (* [comment removed for export] *)
    destruct (materialize2_sound A nu regs mem HG) as (num & HGm & Xm & Lm & FLm).
    assert (PCm : vs_pc (v1 (materialize2 A)) = vs_pc (v1 A)) by (unfold materialize2, with_v1; cbn [v1]; apply vs_pc_materialize).
    assert (GLm : vs_globs (v1 (materialize2 A)) = vs_globs (v1 A)) by (unfold materialize2, with_v1; cbn [v1]; apply vs_globs_materialize).
    remember (materialize2 A) as Am eqn:EAm0. assert (EAm : am_is A Am) by exact EAm0.
    (* [comment removed for export] *)
    assert (Hpcm : vs2_pc Am = bv_unsigned pc) by (unfold vs2_pc; rewrite PCm; exact Hpc).
    assert (Enpc : npc_of (v1 Am) = npc) by (unfold npc, npc_of; rewrite PCm; reflexivity).
    assert (Etgt : wrap64 (vs_pc (v1 Am) + bv_signed imm) = tgt) by (unfold tgt, vs2_pc; rewrite PCm; reflexivity).
    set (A1 := with_v1 Am (set_pc (set_reg (v1 Am) (rz rd) (Some (lconst (npc_of (v1 Am))))) (wrap64 (vs_pc (v1 Am) + bv_signed imm)))).
    assert (GL1 : vs_globs (v1 A1) = vs_globs (v1 A)).
    { rewrite <- GLm, <- (vs_globs_set_reg (v1 Am) (rz rd) (Some (lconst (npc_of (v1 Am))))). unfold A1, with_v1. cbn [v1].
      destruct (set_reg (v1 Am) (rz rd) (Some (lconst (npc_of (v1 Am))))). reflexivity. }
    assert (GIF1 : globs_in_fcells P A1 = true).
    { rewrite (globs_in_fcells_same P A A1 GL1). exact (gamma2_globs_in_fcells _ _ _ _ _ _ _ _ HG). }
    assert (Ej : vstep2 P Am (Jal rd imm) = VR2_next [A1]).
    { unfold vstep2.
      assert (ER : vstep2_raw P Am (Jal rd imm) = VR2_next [A1]) by (unfold vstep2_raw; destruct (asan_mode P); reflexivity).
      rewrite ER. unfold check_globs. cbn [forallb]. rewrite GIF1. reflexivity. }
    destruct (VSTEP2 _ _ _ _ _ _ _ _ Ej HGm Hpcm Hf He Hd) as (regs1 & pc1 & mem1 & A1' & nu1 & Hst & Hin1 & Hpc1 & X1 & L1 & FM1 & FL1 & HG1).
    destruct Hin1 as [<-|[]].
    assert (EA1 : A1 = with_v1 Am (set_pc (set_reg (v1 Am) 1 (Some (lconst npc))) tgt)) by (unfold A1; rewrite Hrd, Enpc, Etgt; reflexivity).
    clearbody A1. subst A1.
    assert (Hpc1' : bv_unsigned pc1 = tgt) by (rewrite <- Hpc1; reflexivity).
    set (A0 := set_reg2 Am 1 (Some (lconst npc))) in *.
    assert (HG0 : gammaP A0 nu1 regs1 mem1) by exact (gamma2_with_v1_set_pc Am _ tgt nu1 regs1 mem1 HG1).
    assert (NPC : 0 <= npc < 2 ^ 64) by (unfold npc, npc_of; rewrite wrap64_zwrap; apply zwrap64_range).
    assert (EN0 : vs2_next A0 = vs2_next Am).
    { unfold A0, set_reg2, with_v1. cbn [vs2_next v1]. apply vs_next_set_reg. }
    (* [comment removed for export] *)
    assert (FI0 : fl_inv G U E A0 nu1 mem_e mem1).
    { assert (FIm : fl_inv G U E Am num mem_e mem) by (eapply fl_inv_step; [exact HFI|exact FLm]).
      apply (fl_inv_with_v1_set_pc Am (set_reg (v1 Am) 1 (Some (lconst npc))) tgt nu1 mem_e mem1).
      exact (fl_inv_step G U E Am _ num nu1 mem_e mem mem1 FIm FL1). }
    (* [comment removed for export] *)
    destruct (callee_entry2 V VIN A Am spoff npc sigma0 sigma skip8 EAm PRE MATCH NPC FP FDEP nu1 regs1 mem1 HG0) as (L & HL & GV & SUB0 & BO0).
    pose proof (V_ok2 V VIN) as [STV OKV].
    set (nuV := vsubst nu1 sigma) in *. set (EV2 := callee_env2 npc nuV L) in *.
    assert (ERET : unit_ret2 V EV2 = npc).
    { unfold unit_ret2, unit_ret. rewrite ROOT. reflexivity. }
    assert (RET : ret_ok (wordZ (unit_ret2 V EV2))).
    { rewrite ERET. apply ret_ok_even. rewrite u_wordZ by lia.
      unfold npc, npc_of. pose proof (fetch_word_even _ _ _ Hf) as Ev. rewrite <- Hpc in Ev.
      rewrite wrap64_zwrap, zwrap64_mod2'. change (vs2_pc A) with (vs_pc (v1 A)) in Ev.
      replace (vs_pc (v1 A) + 4) with (vs_pc (v1 A) + 2 * 2) by lia.
      rewrite Z_mod_plus_full. exact Ev. }
    destruct (OKV EV2 mem0 nuV regs1 mem1 RET GV) as (regs2 & mem2 & Hrun & HEXIT).
    destruct HEXIT as (X & nuV' & XIN & [XG XFI] & XEXT & XRA & XREGS & XFM & XFL).
    rewrite ERET in Hrun, XRA. change (PU2 G V) with (unit_params2 G V) in XG, XFM, XFL. change (regionsU2 G V EV2) with (unit_regions2 (unit_params2 G V) EV2) in XFM.
    (* [comment removed for export] *)
    assert (SIGB : sigma_below sigma (vs2_next A0)).
    { intros s e Hs. exact (pm_forallb_sound _ _ PB s Hs). }
    set (b := vs2_next A0) in *.
    assert (HJ0 : (FIRST_FRESH2 <= b)%positive).
    { rewrite EN0. clear -HJ Lm. eapply Pos.le_trans; eauto. }
    pose proof (proj2 (XBEL V VIN npc X XIN)) as J0.
    set (nJ := (Pos.to_nat (cs_next (c1 X)) - Pos.to_nat FIRST_FRESH2)%nat). set (b' := Pos.of_nat (Pos.to_nat b + nJ)).
    assert (NX : Z.pos (cs_next (c1 X)) = Z.pos FIRST_FRESH2 + Z.of_nat nJ) by (unfold nJ; clear -J0; unfold FIRST_FRESH2 in *; lia).
    assert (HB' : Z.pos b' = Z.pos b + Z.of_nat nJ) by (unfold b'; clear; lia).
    destruct (apply_exit2v_ok V VIN Am spoff npc sigma B SIGB CB nu1 regs1 mem1 HG0 L X nuV' regs2 mem2 XIN XG XEXT b b' nJ eq_refl HJ0 NX HB') as [B1' HV'].
    destruct (apply_exits2_in P B sigma spoff npc (u2_exits V) succs X B1' _ AE XIN HV') as (B' & HW' & HinB).
    assert (HBE : apply_exit2 B sigma spoff (load_cstate2 (unit_params2 G V) X npc []) = Some B').
    { unfold apply_exit2. rewrite HV'. rewrite <- (load_cstate2_PV V). exact HW'. }
    assert (WBB : vstate_below_b (v1 B') = true /\ globs_in_fcells P B' = true).
    { rewrite forallb_forall in WB. specialize (WB _ HinB). apply andb_prop in WB. exact WB. }
    destruct WBB as [WBB GFB].
    destruct (apply_exit2_sound V VIN Am spoff npc sigma B NPC SIGB FP CB nu1 regs1 mem1 HG0 L HL X nuV' regs2 mem2 XIN XG XEXT XRA XREGS XFM XFL
                b b' nJ eq_refl HJ0 NX HB' GV BO0 B' HBE WBB GFB) as (HGB & HpcB & HnB & OWN).
    (* [comment removed for export] *)
    left. exists regs2, (wordZ npc), mem2, B', (nu2x nu1 nuV' b nJ).
    split.
    { eapply msteps_trans; [eapply msteps_one; [reflexivity|exact Hst]|].
      replace pc1 with (wordZ (u_entry (u1 V))); [exact Hrun|].
      rewrite EV. rewrite <- (wordZ_u pc1), Hpc1'. reflexivity. }
    split; [exact HinB|]. split; [rewrite HpcB; rewrite u_wordZ by lia; reflexivity|].
    split.
    { eapply ext_trans; [exact Lm| exact Xm|]. eapply ext_trans; [|exact X1|].
      - apply Pos.le_refl.
      - intros s Hs. apply (nu2x_old nu1 nuV' b nJ). rewrite EN0. exact Hs. }
    split.
    { rewrite HnB. rewrite <- EN0 in Lm. exact (pos_le_add_aux2 (vs2_next A) b b' nJ Lm HB'). }   (* [comment removed for export] *)
    split.
    { eapply frame_mod_trans_same; [exact FM1|].
      eapply frame_mod_weaken; [|exact XFM]. intros a Ha. eapply (regions_sub2 V VIN Am spoff npc sigma NPC FP nu1 regs1 mem1 L a HG0 HL Ha). }
    split; [exact HGB|].
    (* [comment removed for export] *)
    intros a Ha. destruct (FI0 a Ha) as [I1 I2]. split.
    - intros N. rewrite (XFL a Ha). apply I1. intros IN. apply N. apply OWN. exact IN.
    - intros IN. apply I2. apply OWN. exact IN.
  Qed.
End Call2x.

Theorem CALL_iface_holds SEGS G rom : CALL_iface SEGS G rom.
Proof.
  intros done U E mem0 mem_e DONE PO0 PO STATIC VSTEP2 A rd imm vs succs nu regs mem pc w Hx Hne Hvs Hrd HJ HG Hpc Hf He Hd.
  eapply call2_sound; eauto.
Qed.

