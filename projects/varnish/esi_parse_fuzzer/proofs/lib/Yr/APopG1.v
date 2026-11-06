(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMalmys AMalkbe.

Module APopDefs.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState LayoutPA AInv ALogic1 ARtSb8o AMalkbe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).

(* [comment removed for export] *)
Definition reg_upd (reg : Z -> region) (c : Z) (R : region) : Z -> region := fun c' => if Z.eqb c' c then R else reg c'.
(* [comment removed for export] *)
Definition newfree (cc nc : Z) : list Z := map (fun j => cc + (nc - 1 - Z.of_nat j)) (seq 0 (Z.to_nat nc)).
Definition grow (c : Z) (R : region) (ums fam nc : Z) : region :=
  RG (rg_mapped_user R + ums) (rg_allocated_user R + nc * class_size c) (rg_mapped_fa R + fam)
     (rg_free R ++ newfree (rg_allocated_user R / class_size c) nc).
(* [comment removed for export] *)
Definition popg (A : AState) (c ums fam nc : Z) : AState :=
  set_cache_inited (set_reg A (reg_upd (a_reg A) c (grow c (a_reg A c) ums fam nc))) true.
(* [comment removed for export] *)
Definition popA (A : AState) (n : Z) (key : list Z) (ums fam nc : Z) : AState := refA (popg A (class_of n) ums fam nc) n key.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma newfree_length : forall cc nc, 0 <= nc -> length (newfree cc nc) = Z.to_nat nc.
Proof. intros. unfold newfree. rewrite length_map, length_seq. reflexivity. Qed.
(* [comment removed for export] *)
Lemma newfree_in : forall cc nc k, 0 <= nc -> In k (newfree cc nc) <-> cc <= k < cc + nc.
Proof.
  intros cc nc k Hnc. unfold newfree. rewrite in_map_iff. split.
  - intros (j & <- & Hj). apply in_seq in Hj. lia.
  - intros Hk. exists (Z.to_nat (cc + nc - 1 - k)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma newfree_nodup : forall cc nc, 0 <= nc -> NoDup (newfree cc nc).
Proof.
  intros cc nc Hnc. unfold newfree. apply NoDup_fmap_2; [| apply NoDup_ListNoDup, seq_NoDup].
  intros x y E. lia.
Qed.

(* [comment removed for export] *)
Lemma popg_reg_c : forall A c ums fam nc, a_reg (popg A c ums fam nc) c = grow c (a_reg A c) ums fam nc.
Proof. intros. unfold popg, reg_upd. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma popg_reg_other : forall A c ums fam nc c', c' <> c -> a_reg (popg A c ums fam nc) c' = a_reg A c'.
Proof. intros. unfold popg, reg_upd. cbn. destruct (Z.eqb_spec c' c); [contradiction| reflexivity]. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma carved_count_grow : forall A c ums fam nc, 1 <= c <= 30 -> rg_allocated_user (a_reg A c) mod class_size c = 0 ->
  carved_count (popg A c ums fam nc) c = carved_count A c + nc.
Proof.
  intros A c ums fam nc Hc M. unfold carved_count, carved_count_. rewrite popg_reg_c. cbn [grow rg_allocated_user].
  pose proof (class_size_range c Hc). rewrite Z.div_add by lia. reflexivity.
Qed.
Lemma carved_count_grow_other : forall A c ums fam nc c', c' <> c -> carved_count (popg A c ums fam nc) c' = carved_count A c'.
Proof. intros. unfold carved_count, carved_count_. rewrite popg_reg_other by assumption. reflexivity. Qed.
End APopDefs.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalkbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.APopDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pasan).

(* [comment removed for export] *)
Definition dec_tiny (A : AState) (n : Z) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A - is_tiny n) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
(* [comment removed for export] *)
Definition popt (A : AState) (n ums : Z) : AState := dec_tiny (popg A (class_of n) ums 0 0) n.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_zero : forall c R, grow c R 0 0 0 = R.
Proof. intros c [mu au mfa fr]. unfold grow. cbn. rewrite Z.add_0_r, Z.add_0_r, Z.add_0_r. unfold newfree. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma class_regions_le : forall sb R R' c,
  0 <= rg_mapped_user R <= rg_mapped_user R' -> 0 <= rg_mapped_fa R <= rg_mapped_fa R' ->
  hull_le (hull_of (class_regions_ sb R c)) (hull_of (class_regions_ sb R' c)).
Proof.
  intros sb R R' c HU HF lo hi Hin. unfold hull_of, class_regions_ in *. cbv zeta in *.
  rewrite map_app in Hin. rewrite map_app. apply in_app_iff in Hin.
  destruct Hin as [Hin|Hin].
  - destruct (Z.eqb_spec (rg_mapped_user R) 0) as [E|NE]; [destruct Hin|].
    destruct (Z.eqb_spec (rg_mapped_user R') 0) as [E'|NE']; [exfalso; lia|].
    cbn [map fst snd] in Hin. destruct Hin as [Hin|[Hin|[]]].
    + injection Hin as <- <-. exists (region_beg sb c), (region_beg sb c + rg_mapped_user R'). split; [apply in_or_app; left; cbn; left; reflexivity| lia].
    + injection Hin as <- <-. eexists _, _. split; [apply in_or_app; left; cbn; right; left; reflexivity|].
      unfold shadow_region. cbv zeta. cbn [fst snd]. unfold round_down, round_up, sh, kShadowOffset. split; [lia|].
      apply Z.add_le_mono; [| lia]. nia.
  - destruct (Z.eqb_spec (rg_mapped_fa R) 0) as [E|NE]; [destruct Hin|].
    destruct (Z.eqb_spec (rg_mapped_fa R') 0) as [E'|NE']; [exfalso; lia|].
    cbn [map fst snd] in Hin. destruct Hin as [Hin|[Hin|[]]].
    + injection Hin as <- <-. eexists _, _. split; [apply in_or_app; right; cbn; left; reflexivity| lia].
    + injection Hin as <- <-. eexists _, _. split; [apply in_or_app; right; cbn; right; left; reflexivity|].
      unfold shadow_region. cbv zeta. cbn [fst snd]. unfold round_down, round_up, sh, kShadowOffset. split; [lia|].
      apply Z.add_le_mono; [| lia]. nia.
Qed.

Lemma classes_regions_le : forall sb reg reg' n,
  (forall c, 0 <= rg_mapped_user (reg c) <= rg_mapped_user (reg' c) /\ 0 <= rg_mapped_fa (reg c) <= rg_mapped_fa (reg' c)) ->
  hull_le (hull_of (classes_regions_ sb reg n)) (hull_of (classes_regions_ sb reg' n)).
Proof.
  intros sb reg reg' n H. induction n as [|n IH]; [apply hull_le_refl|].
  cbn [classes_regions_]. rewrite !hull_of_app. intros lo hi Hin. apply in_app_iff in Hin as [Hin|Hin].
  - (first [ pose proof ((IH lo hi Hin)) as dR_1; dex2 dR_1 as lo' hi'; dand3 dR_1 as X Y W | pose proof ((IH lo hi Hin)) as dR_1; dand5 dR_1 as lo' hi' X Y W | destruct (IH lo hi Hin) as (lo' & hi' & X & Y & W) ]). exists lo', hi'. split; [apply in_or_app; left; exact X| split; assumption].
  - destruct (H (Z.of_nat (S n))) as [HU HF]. (first [ pose proof ((class_regions_le sb _ _ (Z.of_nat (S n)) HU HF lo hi Hin)) as dR_2; dex2 dR_2 as lo' hi'; dand3 dR_2 as X Y W | pose proof ((class_regions_le sb _ _ (Z.of_nat (S n)) HU HF lo hi Hin)) as dR_2; dand5 dR_2 as lo' hi' X Y W | destruct (class_regions_le sb _ _ (Z.of_nat (S n)) HU HF lo hi Hin) as (lo' & hi' & X & Y & W) ]).
    exists lo', hi'. split; [apply in_or_app; right; exact X| split; assumption].
Qed.

(* [comment removed for export] *)
Lemma lclass_regions_le : forall sb R R' c,
  0 <= rg_mapped_user R <= rg_mapped_user R' -> 0 <= rg_mapped_fa R <= rg_mapped_fa R' ->
  hull_le (hull_of (lclass_regions_ sb R c)) (hull_of (lclass_regions_ sb R' c)).
Proof.
  intros sb R R' c HU HF lo hi Hin. unfold hull_of, lclass_regions_ in *. cbv zeta in *.
  rewrite map_app in Hin. rewrite map_app. apply in_app_iff in Hin.
  destruct Hin as [Hin|Hin].
  - destruct (Z.eqb_spec (rg_mapped_user R) 0) as [E|NE]; [destruct Hin|].
    destruct (Z.eqb_spec (rg_mapped_user R') 0) as [E'|NE']; [exfalso; lia|].
    cbn [map fst snd] in Hin. destruct Hin as [Hin|[]].
    injection Hin as <- <-. eexists _, _. split; [apply in_or_app; left; cbn; left; reflexivity|].
    unfold shadow_region. cbv zeta. cbn [fst snd]. unfold round_down, round_up, sh, kShadowOffset. split; [lia|].
    apply Z.add_le_mono; [| lia]. nia.
  - destruct (Z.eqb_spec (rg_mapped_fa R) 0) as [E|NE]; [destruct Hin|].
    destruct (Z.eqb_spec (rg_mapped_fa R') 0) as [E'|NE']; [exfalso; lia|].
    cbn [map fst snd] in Hin. destruct Hin as [Hin|[]].
    injection Hin as <- <-. eexists _, _. split; [apply in_or_app; right; cbn; left; reflexivity|].
    unfold shadow_region. cbv zeta. cbn [fst snd]. unfold round_down, round_up, sh, kShadowOffset. split; [lia|].
    apply Z.add_le_mono; [| lia]. nia.
Qed.
Lemma lclasses_regions_le : forall sb reg reg' n,
  (forall c, 0 <= rg_mapped_user (reg c) <= rg_mapped_user (reg' c) /\ 0 <= rg_mapped_fa (reg c) <= rg_mapped_fa (reg' c)) ->
  hull_le (hull_of (lclasses_regions_ sb reg n)) (hull_of (lclasses_regions_ sb reg' n)).
Proof.
  intros sb reg reg' n H. induction n as [|n IH]; [apply hull_le_refl|].
  cbn [lclasses_regions_]. rewrite !hull_of_app. intros lo hi Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (IH lo hi Hin) as (lo' & hi' & X & Y & W). exists lo', hi'. split; [apply in_or_app; left; exact X| split; assumption].
  - destruct (H (Z.of_nat (S n))) as [HU HF]. destruct (lclass_regions_le sb _ _ (Z.of_nat (S n)) HU HF lo hi Hin) as (lo' & hi' & X & Y & W).
    exists lo', hi'. split; [apply in_or_app; right; exact X| split; assumption].
Qed.

Lemma classes_eager_upd : forall reg c R n, (1 <= Z.to_nat c)%nat -> (Z.to_nat c <= n)%nat -> 0 <= c ->
  classes_eager_ (reg_upd reg c R) n = classes_eager_ reg n - rg_mapped_user (reg c) - rg_mapped_fa (reg c) + rg_mapped_user R + rg_mapped_fa R.
Proof.
  intros reg c R n H1 H2 H0. induction n as [|n IH]; [lia|].
  cbn [classes_eager_]. unfold reg_upd at 2 3. fold (reg_upd reg c R).
  destruct (Z.eqb_spec (Z.of_nat (S n)) c) as [E|NE].
  - assert (EQ : forall m, (m <= n)%nat -> classes_eager_ (reg_upd reg c R) m = classes_eager_ reg m).
    { intros m Hm. induction m as [|m IHm]; [reflexivity|]. cbn [classes_eager_]. rewrite IHm by lia. unfold reg_upd.
      destruct (Z.eqb_spec (Z.of_nat (S m)) c); [lia| reflexivity]. }
    rewrite EQ by lia. rewrite <- E. lia.
  - rewrite IH by lia. lia.
Qed.

Lemma hull_le_app2 : forall A A' B B', hull_le A A' -> hull_le B B' -> hull_le (A ++ B) (A' ++ B').
Proof.
  intros A A' B B' HA HB lo hi Hin. apply in_app_iff in Hin as [Hin|Hin].
  - (first [ pose proof ((HA lo hi Hin)) as dR_3; dex2 dR_3 as lo' hi'; dand3 dR_3 as X Y W | pose proof ((HA lo hi Hin)) as dR_3; dand5 dR_3 as lo' hi' X Y W | destruct (HA lo hi Hin) as (lo' & hi' & X & Y & W) ]). exists lo', hi'. split; [apply in_or_app; left; exact X| split; assumption].
  - (first [ pose proof ((HB lo hi Hin)) as dR_4; dex2 dR_4 as lo' hi'; dand3 dR_4 as X Y W | pose proof ((HB lo hi Hin)) as dR_4; dand5 dR_4 as lo' hi' X Y W | destruct (HB lo hi Hin) as (lo' & hi' & X & Y & W) ]). exists lo', hi'. split; [apply in_or_app; right; exact X| split; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_len_below : forall (l : list Z) (n : Z), 0 <= n -> NoDup l -> (forall k, In k l -> 0 <= k < n) -> Z.of_nat (length l) <= n.
Proof.
  intros l n Hn ND B. apply NoDup_ListNoDup in ND.
  assert (INCL : incl l (map Z.of_nat (seq 0 (Z.to_nat n)))).
  { intros k Hk. apply in_map_iff. exists (Z.to_nat k). pose proof (B k Hk). split; [lia| apply in_seq; lia]. }
  pose proof (NoDup_incl_length ND INCL) as L. rewrite length_map, length_seq in L. lia.
Qed.

Section G1.
Context {Clg : Ceiling}.
  Variables (A : AState) (c ums fam nc : Z).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (a_reg A c).
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation fr := (rg_free (a_reg A c)).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A c)))).
  #[warnings="-notation-for-abbreviation"] Local Notation cc := (rg_allocated_user (a_reg A c) / class_size c).
  #[warnings="-notation-for-abbreviation"] Local Notation Ag := (popg A c ums fam nc).
  Hypothesis W : WF A.
  Hypothesis CR : 1 <= c <= 30.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis UMS : 0 <= ums /\ ums mod kUserMapSize = 0 /\ mu + ums < au + 9 * class_size c + kUserMapSize /\
                   au <= class_size c * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c.
  Hypothesis FAM : 0 <= fam /\ fam mod kFreeArrayMapSize = 0 /\ mfa + fam <= 4 * cc + kFreeArrayMapSize /\ mfa + fam <= kFreeArraySize.
  Hypothesis NC : 0 <= nc /\ au + nc * class_size c <= mu + ums /\ 4 * (nf + nc) <= mfa + fam.
  Hypothesis POS : mu + ums = 0 -> fam = 0 /\ nc = 0.
  (* [comment removed for export] *)
  Hypothesis TAIL : mu + ums < au + nc * class_size c + 9 * class_size c + kUserMapSize.

  #[using="CR"] Lemma g1_csr : 32 <= class_size c <= kMaxSize. Proof. exact (class_size_range c CR). Qed.
  #[using="CR W Clg"] Lemma g1_reg : wf_region c R (Z.of_nat (length (a_paid A c))).
  Proof. (first [ pose proof ((wfR A W)) as dR_5; dand3 dR_5 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). exact (WR c CR). Qed.
  #[using="FAM UMS CR W fam ums Clg"] Lemma g1_cc : 0 <= cc /\ au = cc * class_size c.
  Proof.
    pose proof g1_csr as CSR. (first [ dand5 g1_reg as A1 _ _ A4 _ | destruct g1_reg as (A1 & _ & _ & A4 & _) ]). unfold kMaxSize in CSR.
    split; [apply Z.div_pos; lia|]. pose proof (Z_div_mod_eq_full au (class_size c)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CR W Clg"] Lemma popg_carved_c : carved_count Ag c = cc + nc.
  Proof. (first [ dand5 g1_reg as _ _ _ A4 _ | destruct g1_reg as (_ & _ & _ & A4 & _) ]). rewrite (carved_count_grow A c ums fam nc CR A4). reflexivity. Qed.
  Lemma popg_carved_other : forall c', c' <> c -> carved_count Ag c' = carved_count A c'.
  Proof. intros. apply carved_count_grow_other. assumption. Qed.
  #[using="NC CR W Clg"] Lemma popg_carved_mono : forall c', carved_count A c' <= carved_count Ag c'.
  Proof.
    intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite popg_carved_c; unfold carved_count, carved_count_; lia| rewrite popg_carved_other by assumption; lia].
  Qed.
  Lemma popg_carved_ : forall c', carved_count_ (a_reg Ag) c' = carved_count Ag c'. Proof. reflexivity. Qed.

  #[using="NC FAM UMS CR"] Lemma popg_free_iff : forall c' j, p_free_ (a_reg Ag) c' j <-> p_free_ (a_reg A) c' j \/ (c' = c /\ cc <= j < cc + nc).
  Proof.
    intros c' j. unfold p_free_. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite popg_reg_c. cbn [grow rg_free]. rewrite in_app_iff, (newfree_in _ _ _ (proj1 NC)). tauto.
    - rewrite popg_reg_other by assumption. split; [tauto|]. intros [H|[H _]]; [exact H| congruence].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma popg_virgin_other : forall c', c' <> c -> a_virgin A c' -> a_virgin Ag c'.
  Proof. intros c' NE [V1 V2]. split; [rewrite popg_reg_other by assumption; exact V1| exact V2]. Qed.

  (* [comment removed for export] *)
  #[using="FAM UMS CR W"] Lemma popg_hull_le : hull_le (pa_hull A) (pa_hull Ag).
  Proof.
    unfold pa_hull, ahull_of, ahull_of_, aregions_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_deadsh].
    rewrite !hull_of_app.
    apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply classes_regions_le. intros c'. unfold reg_upd. destruct (Z.eqb_spec c' c) as [->|NE]; [| (first [ pose proof ((wfR A W)) as dR_8; dand3 dR_8 as WR WZ _ | destruct (wfR A W) as (WR & WZ & _) ])].
    - cbn [grow rg_mapped_user rg_mapped_fa]. (first [ dand6 g1_reg as A1 _ _ _ A5 _ | destruct g1_reg as (A1 & _ & _ & _ & A5 & _) ]). lia.
    - destruct (Z_le_dec 1 c') as [L|L]; [destruct (Z_le_dec c' 30) as [L2|L2]|].
      + (first [ pose proof ((WR c' ltac:(lia))) as dR_10; dand6 dR_10 as A1 _ _ _ A5 _ | destruct (WR c' ltac:(lia)) as (A1 & _ & _ & _ & A5 & _) ]). lia.
      + rewrite (WZ c') by lia. cbn. lia.
      + rewrite (WZ c') by lia. cbn. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="FAM UMS CR W"] Lemma popg_lhull_le : hull_le (pa_lhull A) (pa_lhull Ag).
  Proof.
    unfold pa_lhull, alhull_of, alhull_of_, alregions_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_deadsh].
    rewrite !hull_of_app.
    apply hull_le_app2; [| apply hull_le_refl]. apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply lclasses_regions_le. intros c'. unfold reg_upd. destruct (Z.eqb_spec c' c) as [->|NE]; [| (first [ pose proof ((wfR A W)) as dR_8; dand3 dR_8 as WR WZ _ | destruct (wfR A W) as (WR & WZ & _) ])].
    - cbn [grow rg_mapped_user rg_mapped_fa]. (first [ dand6 g1_reg as A1 _ _ _ A5 _ | destruct g1_reg as (A1 & _ & _ & _ & A5 & _) ]). lia.
    - destruct (Z_le_dec 1 c') as [L|L]; [destruct (Z_le_dec c' 30) as [L2|L2]|].
      + (first [ pose proof ((WR c' ltac:(lia))) as dR_10; dand6 dR_10 as A1 _ _ _ A5 _ | destruct (WR c' ltac:(lia)) as (A1 & _ & _ & _ & A5 & _) ]). lia.
      + rewrite (WZ c') by lia. cbn. lia.
      + rewrite (WZ c') by lia. cbn. lia.
  Qed.
  #[using="FAM UMS CR"] Lemma popg_eager : pa_eager Ag = pa_eager A + ums + fam.
  Proof.
    unfold pa_eager, aeager_of, aeager_of_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec].
    rewrite (classes_eager_upd (a_reg A) c _ 31) by lia. cbn [grow rg_mapped_user rg_mapped_fa]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="FAM UMS"] Lemma popg_runtime_maps_in : forall b s, In (b, s) (runtime_maps A) -> exists b' s', In (b', s') (runtime_maps Ag) /\ b' <= b /\ b + s <= b' + s'.
  Proof.
    intros b s Hin. unfold runtime_maps, runtime_maps_ in *. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec] in *.
    apply in_app_iff in Hin as [Hin|Hin].
    { exists b, s. split; [apply in_or_app; left; exact Hin| lia]. }
    apply in_app_iff in Hin as [Hin|Hin].
    2: { exists b, s. split; [apply in_or_app; right; apply in_or_app; right; exact Hin| lia]. }
    apply in_flat_map in Hin as (c' & Hc' & Hin).
    lazymatch goal with |- context [flat_map ?F ?l] =>
      assert (E : exists b' s', In (b', s') (F c') /\ b' <= b /\ b + s <= b' + s');
      [| (first [ dex2 E as b' s'; destruct E as [E1 E2] | dand4 E as b' s' E1 E2 | destruct E as (b' & s' & E1 & E2) ]); exists b', s'; split; [| exact E2]; apply in_or_app; right; apply in_or_app; left; apply in_flat_map; exists c'; split; [exact Hc'| exact E1]]
    end.
    cbv beta. unfold reg_upd. destruct (Z.eqb_spec c' c) as [->|NE].
    - cbn [grow rg_mapped_user rg_mapped_fa]. destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-.
      + eexists _, _. split; [left; reflexivity| pose proof (proj1 UMS); lia].
      + eexists _, _. split; [right; left; reflexivity| pose proof (proj1 FAM); lia].
    - destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-.
      + eexists _, _. split; [left; reflexivity| lia].
      + eexists _, _. split; [right; left; reflexivity| lia].
  Qed.
  #[using="FAM UMS"] Lemma popg_heap_shadow : forall z, heap_shadow A z -> heap_shadow Ag z.
  Proof.
    intros z Hz. unfold heap_shadow, heap_shadow_, a_sb in *. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec].
    pose proof (proj1 UMS) as U0. pose proof (proj1 FAM) as F0.
    assert (M1 : mu / 8 <= (mu + ums) / 8) by (apply Z.div_le_mono; lia).
    assert (M2 : mfa / 8 <= (mfa + fam) / 8) by (apply Z.div_le_mono; lia).
    destruct Hz as [(c' & Hc' & Hz)|[(c' & Hc' & Hz)|Hz]]; [left| right; left| right; right; exact Hz]; exists c'; (split; [exact Hc'|]);
      cbv zeta in *; unfold reg_upd; (destruct (Z.eqb_spec c' c) as [->|NE]; [cbn [grow rg_mapped_user rg_mapped_fa]; lia| exact Hz]).
  Qed.
  #[using="FAM UMS"] Lemma popg_owned_mono : forall a, pa_owned A a -> pa_owned Ag a.
  Proof.
    intros a [Ha|Ha]; [left| right; exact Ha]. unfold aowned, aowned_ in *. cbn [popg set_cache_inited set_reg a_pl a_reg a_livemap a_sec a_fframes] in *.
    destruct Ha as [Ha|[[(Hr & NU & NF)|[Hs|Hf]]|Hg]]; [left; exact Ha| right; left| right; left; right; left| right; left; right; right; exact Hf| right; right; exact Hg].
    - left. split; [| exact (conj NU NF)]. (first [ dex2 Hr as b s; destruct Hr as [Hin Hb] | dand4 Hr as b s Hin Hb | destruct Hr as (b & s & Hin & Hb) ]). (first [ pose proof ((popg_runtime_maps_in b s Hin)) as dR_13; dex2 dR_13 as b' s'; dand3 dR_13 as Hin' L1 L2 | pose proof ((popg_runtime_maps_in b s Hin)) as dR_13; dand5 dR_13 as b' s' Hin' L1 L2 | destruct (popg_runtime_maps_in b s Hin) as (b' & s' & Hin' & L1 & L2) ]).
      exists b', s'. split; [exact Hin'| lia].
    - exact (popg_heap_shadow a Hs).
  Qed.
  (* [comment removed for export] *)
  #[using="NC FAM UMS CR"] Lemma popg_owned_new : forall a, pa_owned Ag a -> pa_owned A a \/
    (region_beg (a_sb A) c + mu <= a < region_beg (a_sb A) c + mu + ums) \/
    (region_beg (a_sb A) c + kFreeArrayOffset + mfa <= a < region_beg (a_sb A) c + kFreeArrayOffset + mfa + fam) \/
    (sh (region_beg (a_sb A) c) + mu / 8 <= a < sh (region_beg (a_sb A) c) + (mu + ums) / 8) \/
    (sh (region_beg (a_sb A) c + kFreeArrayOffset) + mfa / 8 <= a < sh (region_beg (a_sb A) c + kFreeArrayOffset) + (mfa + fam) / 8).
  Proof.
    intros a [Ha|Ha]; [| left; right; exact Ha]. unfold aowned, aowned_ in Ha. cbn [popg set_cache_inited set_reg a_pl a_reg a_livemap a_sec a_fframes] in Ha.
    unfold pa_owned, aowned, aowned_, a_sb.
    destruct Ha as [Ha|[[(Hr & NU & NF)|[Hs|Hf]]|Hg]].
    - left. left. left. exact Ha.
    - (first [ dex2 Hr as b s; destruct Hr as [Hin Hb] | dand4 Hr as b s Hin Hb | destruct Hr as (b & s & Hin & Hb) ]). unfold runtime_maps_ in Hin. apply in_app_iff in Hin as [Hin|Hin].
      { left. left. right. left. left. split; [| exact (conj NU NF)]. exists b, s. split; [apply in_or_app; left; exact Hin| exact Hb]. }
      apply in_app_iff in Hin as [Hin|Hin].
      2: { left. left. right. left. left. split; [| exact (conj NU NF)]. exists b, s. split; [apply in_or_app; right; apply in_or_app; right; exact Hin| exact Hb]. }
      apply in_flat_map in Hin as (c' & Hc' & Hin). cbv beta in Hin. unfold reg_upd in Hin.
      destruct (Z.eqb_spec c' c) as [->|NE].
      + cbn [grow rg_mapped_user rg_mapped_fa] in Hin. destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-.
        * destruct (Z_lt_le_dec a (region_beg (p_sb (a_pl A)) c + mu)) as [L|L]; [| right; left; lia].
          left. left. right. left. left. split; [| exact (conj NU NF)]. exists (region_beg (p_sb (a_pl A)) c), mu. split; [| lia].
          apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists c. split; [exact Hc'| left; reflexivity].
        * destruct (Z_lt_le_dec a (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset + mfa)) as [L|L]; [| right; right; left; lia].
          left. left. right. left. left. split; [| exact (conj NU NF)]. exists (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset), mfa. split; [| lia].
          apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists c. split; [exact Hc'| right; left; reflexivity].
      + left. left. right. left. left. split; [| exact (conj NU NF)]. exists b, s. split; [| exact Hb].
        apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists c'. split; [exact Hc'|]. exact Hin.
    - unfold heap_shadow_ in Hs. cbv zeta in Hs. unfold reg_upd in Hs.
      destruct Hs as [(c' & Hc' & Hs)|[(c' & Hc' & Hs)|Hs]].
      + destruct (Z.eqb_spec c' c) as [->|NE].
        * cbn [grow rg_mapped_user] in Hs. destruct (Z_lt_le_dec a (sh (region_beg (p_sb (a_pl A)) c) + mu / 8)) as [L|L]; [| right; right; right; left; lia].
          left. left. right. left. right. left. left. exists c. split; [exact Hc'| cbv zeta; lia].
        * left. left. right. left. right. left. left. exists c'. tauto.
      + destruct (Z.eqb_spec c' c) as [->|NE].
        * cbn [grow rg_mapped_fa] in Hs. destruct (Z_lt_le_dec a (sh (region_beg (p_sb (a_pl A)) c + kFreeArrayOffset) + mfa / 8)) as [L|L]; [| right; right; right; right; lia].
          left. left. right. left. right. left. right. left. exists c. split; [exact Hc'| cbv zeta; lia].
        * left. left. right. left. right. left. right. left. exists c'. tauto.
      + left. left. right. left. right. left. right. right. exact Hs.
    - left. left. right. left. right. right. exact Hf.
    - left. left. right. right. exact Hg.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="TAIL POS NC FAM UMS CR W nc fam ums Clg"] Lemma g1_states_bound : forall k,
    (p_cached_ (a_cache A) c k -> 0 <= k < cc) /\ (p_live_ (a_livemap A) c k -> 0 <= k < cc) /\
    (p_quar_ (a_qthread A) (a_qglobal A) c k -> 0 <= k < cc) /\ (p_batch_ (a_qthread A) (a_qglobal A) c k -> 0 <= k < cc).
  Proof.
    intros k. split; [| split; [| split]].
    - intros H. destruct (wfC A W) as (C1 & _). (first [ pose proof ((C1 c ltac:(lia))) as dR_15; dand4 dR_15 as _ _ B _ | destruct (C1 c ltac:(lia)) as (_ & _ & B & _) ]). exact (B k H).
    - ((first [ intro dR_33; dex2 dR_33 as u n; rename dR_33 into H | intro dR_33; dand3 dR_33 as u n H | intros (u & n & H) ])). destruct (wfV A W) as (V1 & _). pose proof (V1 u _ H) as X. cbv zeta in X. cbn [li_chunk li_n] in X.
      (first [ dand5 X as _ _ _ _ X | destruct X as (_ & _ & _ & _ & X) ]). exact X.
    - intros (n & H). (first [ pose proof ((wfQ A W)) as dR_17; dand3 dR_17 as Q1 Q2 _ | destruct (wfQ A W) as (Q1 & Q2 & _) ]).
      unfold q_entries in H. apply in_flat_map in H as (b & Hb & He). apply in_app_iff in Hb.
      assert (WB : wf_batch_ (a_reg A) (a_sec A) b) by (destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) Q1 b Hb)| exact (proj1 (Forall_forall _ _) Q2 b Hb)]).
      (first [ dand3 WB as _ _ WE | destruct WB as (_ & _ & WE) ]). pose proof (proj1 (Forall_forall _ _) WE _ He) as X. cbn [qe_chunk qe_n] in X. (first [ dand4 X as _ _ _ X | destruct X as (_ & _ & _ & X) ]). exact X.
    - intros [-> H]. (first [ pose proof ((wfQ A W)) as dR_20; dand3 dR_20 as Q1 Q2 _ | destruct (wfQ A W) as (Q1 & Q2 & _) ]). unfold batch_indices_ in H. apply in_map_iff in H as (b & <- & Hb). apply in_app_iff in Hb.
      assert (WB : wf_batch_ (a_reg A) (a_sec A) b) by (destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) Q1 b Hb)| exact (proj1 (Forall_forall _ _) Q2 b Hb)]).
      (first [ dand3 WB as _ X _ | destruct WB as (_ & X & _) ]). exact X.
  Qed.

  #[using="TAIL POS NC FAM UMS CR W"] Theorem pop_WF : WF Ag.
  Proof.
    pose proof g1_csr as CSR. pose proof g1_cc as [CC0 AUE]. (first [ pose proof (g1_reg) as dR_22; dand12 dR_22 as A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 | pose proof g1_reg as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) ]).
    destruct UMS as (U1 & U2 & U3). destruct FAM as (F1 & F2 & F3 & F4). destruct NC as (N1 & N2 & N3).
    pose proof popg_carved_c as CCg. pose proof popg_carved_other as CCo.
    (* [comment removed for export] *)
    pose proof (wf_au_cap A c W CR) as [AUC MUC]. pose proof (class_slack_range c) as SL.
    pose proof (nodup_len_below (rg_free R) cc ltac:(lia) A8 A9) as NFC.
    assert (NCS : 0 <= nc * class_size c) by (apply Z.mul_nonneg_nonneg; lia).
    assert (CC' : (au + nc * class_size c) / class_size c = cc + nc) by (apply Z.div_add; lia).
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN] eqn:EW. clear EW.
    constructor; rewrite ?popg_carved_; cbn [popg set_cache_inited set_reg a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs].
    - exact wP.
    - exact wM.
    - (* [comment removed for export] *) (first [ dand3 wR as R1 R2 R3 | destruct wR as (R1 & R2 & R3) ]). split; [| split].
      + intros c' Hc'. unfold reg_upd. destruct (Z.eqb_spec c' c) as [->|NE]; [| exact (R1 c' Hc')].
        unfold wf_region, grow. cbn [rg_mapped_user rg_allocated_user rg_mapped_fa rg_free].
        rewrite app_length, newfree_length by lia.
        split; [clear - A1 N1 N2 NCS TAIL; lia|]. split; [clear - A1 U1 U3 AUC CSR; unfold kAuCap, kFreeArrayOffset, kUserMapSize, kMaxSize in *; lia|].
        split; [unfold kUserMapSize in *; rewrite <- Zplus_mod_idemp_r, U2, Z.add_0_r; exact A3|].
        split; [rewrite Z_mod_plus_full; exact A4|].
        split; [clear - A5 F1 F4; lia|].
        split; [unfold kFreeArrayMapSize in *; rewrite <- Zplus_mod_idemp_r, F2, Z.add_0_r; exact A6|].
        split; [lia|].
        split. { apply (proj2 (list.NoDup_app _ _)). split; [exact A8|]. split; [| apply newfree_nodup; lia].
                 intros x Hx Hk. apply elem_of_In in Hx. apply elem_of_In in Hk. apply (newfree_in _ _ _ N1) in Hk. pose proof (A9 x Hx). lia. }
        split. { intros k Hk. rewrite Z.div_add by lia. apply in_app_iff in Hk as [Hk|Hk]; [pose proof (A9 k Hk); lia| apply (newfree_in _ _ _ N1) in Hk; lia]. }
        split. { intros Z0. destruct (POS Z0) as [-> ->]. destruct (A10 ltac:(lia)) as [E1 E2]. rewrite E1, E2. unfold newfree. cbn. split; reflexivity. }
        (* [comment removed for export] *)
        rewrite CC'. split.
        { clear - A1 A11 U1 U3 N1 N2 NCS CSR SL. unfold kUserMapSize in *. nia. }
        { clear - F3 N1. unfold kFreeArrayMapSize in *. lia. }
      + intros c' Hc'. unfold reg_upd. destruct (Z.eqb_spec c' c) as [->|NE]; [lia| exact (R2 c' Hc')].
      + intros _. reflexivity.
    - (* [comment removed for export] *) (first [ dand3 wC as C1 C31 C0 | destruct wC as (C1 & C31 & C0) ]). split; [| exact (conj C31 C0)].
      intros c' Hc'. (first [ pose proof ((C1 c' Hc')) as dR_25; dand4 dR_25 as X1 X2 X3 X4 | destruct (C1 c' Hc') as (X1 & X2 & X3 & X4) ]). cbv zeta. split; [exact X1|]. split; [exact X2|]. split; [| intros F; discriminate].
      intros k Hk. pose proof (X3 k Hk). pose proof (popg_carved_mono c') as M. unfold carved_count in M. cbn [popg set_cache_inited set_reg a_reg] in M. lia.
    - (* [comment removed for export] *) intros c' j Hc' Hj. cbv zeta.
      change (reg_upd (a_reg A) c (grow c R ums fam nc)) with (a_reg Ag). rewrite (popg_free_iff c' j).
      destruct (Z.eq_dec c' c) as [->|NE].
      + replace (carved_count_ (reg_upd (a_reg A) c (grow c R ums fam nc)) c) with (cc + nc) in Hj by (symmetry; exact CCg).
        destruct (Z_lt_le_dec j cc) as [L|L].
        * pose proof (wX c j Hc' ltac:(unfold carved_count_; lia)) as X. cbv zeta in X.
          assert (FF : (p_free_ (a_reg A) c j \/ c = c /\ cc <= j < cc + nc) <-> p_free_ (a_reg A) c j) by (split; [intros [H|[_ H]]; [exact H| lia]| tauto]).
          rewrite FF. exact X.
        * (* [comment removed for export] *) (first [ pose proof ((g1_states_bound j)) as dR_26; dand4 dR_26 as B1 B2 B3 B4 | pose proof (g1_states_bound j) as (B1 & B2 & B3 & B4) ]).
          assert (NJ1 : ~ p_cached_ (a_cache A) c j) by (intros H; pose proof (B1 H); lia).
          assert (NJ2 : ~ p_live_ (a_livemap A) c j) by (intros H; pose proof (B2 H); lia).
          assert (NJ3 : ~ p_quar_ (a_qthread A) (a_qglobal A) c j) by (intros H; pose proof (B3 H); lia).
          assert (NJ4 : ~ p_batch_ (a_qthread A) (a_qglobal A) c j) by (intros H; pose proof (B4 H); lia).
          assert (FJ : c = c /\ cc <= j < cc + nc) by (split; [reflexivity| lia]).
          tauto.
      + replace (carved_count_ (reg_upd (a_reg A) c (grow c R ums fam nc)) c') with (carved_count A c') in Hj by (symmetry; exact (CCo c' NE)).
        pose proof (wX c' j Hc' Hj) as X. cbv zeta in X.
        assert (FF : (p_free_ (a_reg A) c' j \/ c' = c /\ cc <= j < cc + nc) <-> p_free_ (a_reg A) c' j) by tauto.
        rewrite FF. exact X.
    - (* [comment removed for export] *) (first [ dand3 wV as V1 V2 V3 | destruct wV as (V1 & V2 & V3) ]). split; [| exact (conj V2 V3)].
      intros u li Hl. pose proof (V1 u li Hl) as X. cbv zeta in *. (first [ dand3 X as X1 X2 X3 | destruct X as (X1 & X2 & X3) ]). split; [exact X1|]. split; [exact X2|].
      destruct (li_chunk li) as [[c' k]|[mb n0]]; [| exact X3]. (first [ dand3 X3 as Y1 Y2 Y3 | destruct X3 as (Y1 & Y2 & Y3) ]). split; [exact Y1|]. split; [exact Y2|].
      pose proof (popg_carved_mono c') as M. unfold carved_count in M. cbn [popg set_cache_inited set_reg a_reg] in M. lia.
    - (* [comment removed for export] *) (first [ dand8 wQ as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct wQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]).
      assert (WBm : forall b, wf_batch_ (a_reg A) (a_sec A) b -> wf_batch_ (reg_upd (a_reg A) c (grow c R ums fam nc)) (a_sec A) b).
      { (intros b; (first [ intro dR_34; dand3 dR_34 as B1 B2 B3 | intros (B1 & B2 & B3) ])). split; [exact B1|]. split.
        - pose proof (popg_carved_mono kQuarantineBatchClass) as M. unfold carved_count in M. cbn [popg set_cache_inited set_reg a_reg] in M. lia.
        - apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) B3 e He) as (E1 & E2). split; [exact E1|].
          destruct (qe_chunk e) as [[c' k]|[mb n0]]; [| exact E2]. (first [ dand3 E2 as Y1 Y2 Y3 | destruct E2 as (Y1 & Y2 & Y3) ]). split; [exact Y1|]. split; [exact Y2|].
          pose proof (popg_carved_mono c') as M. unfold carved_count in M. cbn [popg set_cache_inited set_reg a_reg] in M. lia. }
      split; [apply Forall_forall; intros b Hb; apply WBm; exact (proj1 (Forall_forall _ _) Q1 b Hb)|].
      split; [apply Forall_forall; intros b Hb; apply WBm; exact (proj1 (Forall_forall _ _) Q2 b Hb)|].
      exact (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 Q8))))).
    - exact wS.
    - exact wD.
    - exact wF.
    - exact wB.
    - exact wI.
    - exact wE.
    - exact wJ.
    - exact wN.   (* [comment removed for export] *)
  Qed.
End G1.

(* [comment removed for export] *)
Section G1t.
Context {Clg : Ceiling}.
  Variables (A : AState) (n : Z).
  Hypothesis W : WF A.
  Hypothesis TINY : n < 16 -> 1 <= as_tinycred A.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End G1t.
