(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Bool Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 Qfya QYTG QPiB Qatc QSfG QdBa QpFQ Ql2m QjcB QLaA Q1am QoCS QQg5 QPWv QlOh QQCz QcV4 Q7RC QhnL QBv7 Qn5J QhfJ QvVk QwQw Q3dN Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QYTG.Mq0 QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq0 QdBa.Mq1 QpFQ QPiB Ql2m.Mq2 QYTG.Mq1 QjcB QLaA QdBa.Mq2 QLaA.Mq0 Q1am.Mq0 QoCS QQg5 QQg5.Mq3 QPWv Q1am.Mq1 QQg5.Mq0 QSfG QoCS.Mq0 QlOh.Mq0 QQCz QcV4 Q7RC QSfG.Mq0 QhnL QBv7.
Import Qn5J QhfJ QvVk QwQw Q3dN.Mq0.
Import Q6q3.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation SHF st := (c_meta_alloc_shift (s_ctx st)).
Notation CNT st := (c_avail_meta_count (s_ctx st)).
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lev (sc : Z) : nat := Z.to_nat (Z.max 1 (21 - sc)).
Definition LW (SH0 : Z) : Z := 2 ^ 20 + AMW (SH0 + 1).
Definition LD : nat := 5%nat.

#[using="Type"] Lemma lev_ge1 sc : (1 <= lev sc)%nat.
Proof. unfold lev. lia. Qed.
#[using="Type"] Lemma lev_step sc j : sc < 20 -> sc < j -> (lev j + 1 <= lev sc)%nat.
Proof. intros. unfold lev. lia. Qed.
#[using="Type"] Lemma lev_le21 sc : 0 <= sc -> (lev sc <= 21)%nat.
Proof. intros. unfold lev. lia. Qed.

Section NEST.
Context {T : Type} (isS : T -> bool) (P : T -> Prop).
Variables (SH0 Wf : Z) (Df : nat).
Hypothesis HSH0 : 0 <= SH0 <= 15.

Definition SHI (sc : Z) (st : mstate) : Prop :=
SHF st <= SH0 + 1 /\ (SHF st = SH0 + 1 -> Z.of_nat (lev sc) <= CNT st).

Definition NACT (sc : Z) (st : mstate) : Prop :=
forall j, sc <= j < 48 -> j <= 23 \/ j = sc -> active st j = None.

Definition SLOT_KS (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) : Prop :=
forall idle st L BL LS req (k : mstate -> Z -> M T) bail (κN κS : kind) W D,
Wf <= W -> (Df <= D)%nat ->
INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
NACT sc st -> SHI sc st ->
(forall st1 L1, SHF st1 <= SH0 + 2 -> KSUM isS P Wf Df L1 (k st1 (-1)) κN W D) ->
(forall st1 L1 LS1, SLOT_POST idle sc req st L BL st1 0 L1 LS1 -> active st1 sc <> None -> SHF st1 <= SH0 + 2 ->
KSUM isS P Wf Df L1 (k st1 0) κS W D) ->
KSUM isS P Wf Df L (rec st sc req k bail) κS (W + Z.of_nat (lev sc) * LW SH0) (D + lev sc * LD)%nat.

Section AG.
Variables (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z).
Hypothesis REC : forall j, sc < j < 48 -> SLOT_KS rec j.

#[using="HSH0 REC"] Theorem alloc_group_ks idle st L BL LS req (k : mstate -> optr -> M T) bail (κN κS : kind) W D :
Wf <= W -> (Df <= D)%nat ->
INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
NACT sc st -> SHI sc st ->
(forall st2 L2, SHF st2 <= SH0 + 2 -> KSUM isS P Wf Df L2 (k st2 None) κN W D) ->
(forall st2 go L2 LS2, AG_POST idle sc req st L BL st2 (Some go) L2 LS2 -> SHF st2 <= SH0 + 2 -> KSUM isS P Wf Df L2 (k st2 (Some go)) κS W D) ->
KSUM isS P Wf Df L (alloc_group T full_lay rec st sc req k bail) κS (W + Z.of_nat (lev sc) * LW SH0) (D + lev sc * LD)%nat.
Proof.
intros HW HD INV TF ND Hsc Hreq Hfit NA SHC HKN HKS.
pose proof (lev_ge1 sc) as LG1. pose proof (lev_le21 sc ltac:(lia)) as LG21.
assert (HA : active st sc = None) by (apply NA; [lia| right; reflexivity]).
unfold alloc_group.
assert (AK : κS = am_kind κN κS st) by reflexivity.
rewrite AK.

set (WR := W + (Z.of_nat (lev sc) - 1) * LW SH0 + 2 ^ 20).
set (DR := (D + (lev sc - 1) * LD + 1)%nat).
replace (W + Z.of_nat (lev sc) * LW SH0) with (WR + AMW (SH0 + 1)) by (subst WR; unfold LW; lia).
replace (D + lev sc * LD)%nat with (DR + AMD)%nat by (subst DR; unfold LD, AMD; lia).
assert (HWR : Wf <= WR) by (subst WR; unfold LW, AMW; pose proof (pow_SH (SH0 + 1) ltac:(lia)); unfold PGSZ; nia).
eapply (alloc_meta_ks isS P Wf Df BL _ bail (X_as idle) st L κN κS WR DR (SH0 + 1) HWR ltac:(lia));
[ | | exact INV| apply amf_refl| apply lf_refl| exact (proj1 SHC)| split; reflexivity].
-
intros st1 L1' LS1 INV1 AF LF SH1. cbn beta iota. eapply (KSUM_mono isS P Wf Df _ _ _ W D); [apply HKN; lia| subst WR; unfold LW, AMW; pose proof (pow_SH (SH0 + 1) ltac:(lia)); unfold PGSZ; nia| subst DR; unfold LD; lia].
-
intros st1 L1 LS1 m INV1 NIm AF LF SH1 AMQ1. cbn beta iota zeta.
change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
with (cnt0_of sc (usage st1 sc)).
change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
with (ag_cnt1 sc (usage st1 sc)).
change (lh_nest full_lay) with nest_layout.
assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
pose proof (ag_arith sc req (usage st1 sc)) as AR.
set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
+
set (ns := is_bouncing sc st1).
set (st1' := step_seq (account_bounce sc st1)).
set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
change (if (u1 <? 4 * c1) && negb ns
then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
else c1
else c1) with (ag_cnt2 sc c1 u1 ns).
set (c2 := ag_cnt2 sc c1 u1 ns).
specialize (AR u1 ns).
assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
KSUM isS P Wf Df L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
else let '(st2, rid) := new_region RKGroup r n3 st1' in
ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
(let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k))
κS WR DR).
{ intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
pose proof (grp_ok_sound sc c3 n3 GRP) as G. cbn zeta in G. destruct G as (_ & _ & G3 & _).
eapply (KSUM_mono isS P Wf Df _ _ _ (W + n3) (S D)); [| subst WR; pose proof (pow_SH (SH0 + 1) ltac:(lia)); unfold LW, AMW, PGSZ; nia| subst DR; unfold LD; lia].
apply (ag_mmap_ks isS P (SH0 + 1) idle st st1 L L1 BL LS1 m sc req c3 n3 k bail κN κS Wf W Df D HW HD INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED SH1
(amf_groups _ _ AF) (amf_hmetas _ _ AF)).
- intros st2 L2 _ S2. apply HKN. lia.
- intros st2 go L2 LS2 AG _ S2. apply (HKS st2 go L2 LS2 AG). lia. }
unfold ag_cn3 in GO. cbn zeta in GO.
destruct (negb ns && (c2 <=? 7)).
* destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
-- cbn beta iota. exact (GO _ _ eq_refl).
-- cbn beta iota. exact (GO _ _ eq_refl).
* cbn beta iota. exact (GO _ _ eq_refl).
+
pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
pose proof (nest_ok_sound sc c1 NEST) as N0. cbn zeta in N0.
set (size := UNIT * size_class sc) in *. set (j := size_to_class (UNIT + c1 * size - IB)) in *.
destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
assert (Hsc20 : sc < 20).
{ destruct (Z.lt_ge_cases sc 20) as [LT|GE]; [exact LT|]. exfalso.
pose proof (big_class_mmap sc (usage st1 sc) ltac:(unfold big_class; lia)) as HB'. fold c1 in HB'. unfold size in HB. lia. }
pose proof (lev_step sc j Hsc20 ltac:(lia)) as LJ.
eapply (KSUM_mono isS P Wf Df _ _ _ (W + Z.of_nat (lev j) * LW SH0) (D + lev j * LD)%nat);
[| subst WR; unfold LW, AMW; pose proof (pow_SH (SH0 + 1) ltac:(lia)); unfold PGSZ; nia| subst DR; unfold LD; nia].
apply (REC j ltac:(lia) (m :: idle) st1 L1 BL LS1 (UNIT + c1 * size - IB) _ bail κN κS W D HW HD INV1 TF1).
* apply NoDup_cons. split; [intros Hin; apply NIm; apply list_elem_of_In; exact Hin| exact ND].
* lia.
* exact N5.
* lia.
*
intros j' Hj' C'. rewrite HA1. apply NA; lia.
*
destruct SHC as [S1 S2]. split.
-- destruct AMQ1 as [[E _]|(_ & C0 & LE)]; [rewrite E; exact S1|].
destruct (Z.eq_dec (SHF st) (SH0 + 1)) as [E|NE]; [| lia]. pose proof (S2 E). lia.
-- intros E. destruct AMQ1 as [[E1 GE]|(C100 & C0 & LE)].
++ rewrite E1 in E. pose proof (S2 E). lia.
++ rewrite C100. pose proof (lev_le21 j ltac:(lia)). unfold NSLOTS. lia.
*
intros st2 L2 S2. change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq. apply HKN.
unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st2)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & QC).
rewrite (cb_shift _ _ QC). autorewrite with mst. exact S2.
*
intros st2 L2 LS2 (ACT & LIVE & GP2 & RES) HAj2 S2.
destruct RES as [(ABS & _)|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2' & _)]; [lia|].
change (0 <? 0) with false. cbn iota. rewrite HAj.
assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
assert (Ep : slot_of st2 g 0 = (fst bg, sstart (MR st2 g) 0)).
{ unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ 0 Hgh). }
rewrite Ep. rewrite ag_tail_eq.
specialize (STR ltac:(lia)).
assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA).
destruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig 0 sc c1 INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
pose proof (nst_facts st2 g bg 0 sc c1 NEST Hsc) as NF. cbn zeta in NF.
destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
rewrite Emr in MR'. rewrite Emr in Es.
eapply HKS.
2:{ rewrite agt_ctx. cbn [s_ctx upd_meta]. autorewrite with mst.
first [exact S2| rewrite <- (s_ctx_strip (nest_layout st2 g 0 j size c1)), strip_nest_layout; cbn; exact S2]. }
split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact (lf_live _ _ LF)|].
split.
{ eapply GP_trans; [exact (GP_amf _ _ AF)| eapply GP_trans; [exact GP2| apply GP_eq]].
- rewrite agt_regions. change (s_regions (nest_layout st2 g 0 j size c1) = s_regions st2).
rewrite <- (s_regions_strip (nest_layout st2 g 0 j size c1)), strip_nest_layout. reflexivity.
- rewrite agt_secret. change (s_secret (nest_layout st2 g 0 j size c1) = s_secret st2).
rewrite <- (s_secret_strip (nest_layout st2 g 0 j size c1)), strip_nest_layout. reflexivity.
- rewrite agt_ctx. cbn. change (c_init_done (s_ctx (nest_layout st2 g 0 j size c1)) = c_init_done (s_ctx st2)).
rewrite <- (s_ctx_strip (nest_layout st2 g 0 j size c1)), strip_nest_layout. reflexivity. }
exists (fst bg, sstart (MR st2 g) 0), (c1 - 1), (c1 - 1), 0.
rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
split; [exact INV'|]. split; [exact TF'|]. intros U. exfalso. destruct U as [U|U]; [cbn in U; lia|]. rewrite Es in U. cbn [m_sizeclass] in U. unfold size in U. lia.
Qed.
End AG.

#[using="HSH0"] Theorem alloc_slot_ks (f : nat) : forall sc, 49 - sc <= Z.of_nat f -> SLOT_KS (alloc_slot full_lay f) sc.
Proof.
induction f as [|f IH]; intros sc Hf idle st L BL LS req k bail κN κS W D HW HD INV TF ND Hsc Hreq Hfit NA SHC HKN HKS.
{ exfalso. cbn in Hf. lia. }
rewrite alloc_slot_S.
assert (HA : active st sc = None) by (apply NA; [lia| right; reflexivity]).
unfold try_avail. rewrite HA. change (negb (0 =? 0)) with false. cbn iota.
apply (alloc_group_ks (alloc_slot full_lay f) sc (fun j Hj => IH j ltac:(lia)) idle st L BL LS req _ bail κN κS W D HW HD INV TF ND Hsc Hreq Hfit NA SHC).
- intros st2 L2 S2. cbn beta iota. apply HKN. exact S2.
- intros st2 g L2 LS2 (ACT2 & LIVE2 & GP2 & RES2) S2.
destruct RES2 as (b & ai & last & ml & Hb & Em & Hai & Hl & FIT2 & STR & UND & INV2 & TF2' & AZ2).
cbn zeta.
destruct (slot_finish_ok T idle st2 L2 BL LS2 g b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl Hsc
ltac:(rewrite ACT2 by lia; exact HA) UND TF2')
as (LS4 & EQ & INV4 & TF4 & HA4 & ACT4 & G4 & TK4 & SH4 & L4 & SC4 & STR4 & SS4 & RG4 & SE4 & ID4).
rewrite EQ. eapply HKS; [| rewrite HA4; discriminate| ].
2:{ destruct (queue_frame (LActive sc) g (upd_meta g (fun r : meta => m_set_avail (m_avail r - 1) r) st2)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & QC).
rewrite (cb_shift _ _ QC). autorewrite with mst. exact S2. }
split; [intros sc' Hs; rewrite ACT4, ACT2 by lia; reflexivity|]. split; [exact LIVE2|].
split; [eapply GP_trans; [exact GP2| apply GP_eq; [exact RG4| exact SE4| exact ID4]]|].
right. exists g, b, ai. rewrite L4, SC4, STR4, G4, SS4.
split; [lia|]. split; [exact HA4|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact FIT2|]. split; [exact STR|].
split; [exact INV4|]. split; [exact TF4|].
intros U o Ho. unfold get_shadow. rewrite SH4. unfold undersized in U. rewrite SC4, STR4 in U.
assert (SCg2 : m_sizeclass (MR st2 g) = sc) by (rewrite Em; reflexivity).
apply AZ2; [| exact Ho]. unfold undersized. rewrite SCg2. exact U.
Qed.

End NEST.

Definition SMALLW (SH0 : Z) : Z := 21 * LW SH0.
Definition SMALLD : nat := (21 * 5)%nat.

Section SMALL.
Variables (SH0 W : Z) (D : nat) (XC : Z).
Hypothesis HSH0 : 0 <= SH0 <= 15.
Hypothesis HXC : 23 < XC.

#[using="HSH0 HXC"] Theorem malloc_core_small_ks st L BL LS n :
INVL x0 st L BL LS -> TF0 st -> 0 <= n < MMAP_THRESHOLD -> SHF st <= SH0 ->
(forall j, 0 <= j < 48 -> j <> XC -> active st j = None) ->
size_to_class n <> XC -> Z.lor (size_to_class n) 1 <> XC ->
KSUM isC (PSH (SH0 + 1)) W D L (malloc_core full_lay st n) KS (W + SMALLW SH0) (D + SMALLD)%nat.
Proof.
intros INV TF Hn SHC NA0 NX1 NX2. unfold SMALLW, SMALLD.
assert (Hov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; unfold IB, UNIT, MMAP_THRESHOLD in *; lia).
unfold malloc_core. rewrite Hov. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
set (sc0 := size_to_class n) in *.
assert (HA0 : active st sc0 = None) by (apply NA0; lia).
unfold malloc_small_ctrl. cbv zeta. fold sc0. rewrite !HA0.
set (sc := if (4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0) then _ else sc0).
assert (SC' : 0 <= sc < 48 /\ n + IB <= UNIT * size_class sc /\ sc <> XC).
{ subst sc.
destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| auto].
apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
apply Z.leb_le in E1. apply Z.ltb_lt in E2.
split; [| split; [| exact NX2]].
- rewrite (lor1_even sc0 ltac:(lia) EV). lia.
- rewrite (lor1_even sc0 ltac:(lia) EV). pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
clearbody sc. destruct SC' as (Hsc & FIT' & NXs).
assert (HAsc : active st sc = None) by (apply NA0; lia).
rewrite HAsc. change (lowbit 0) with 0. cbn [negb Z.eqb].
pose proof (lev_le21 sc ltac:(lia)) as L21.
eapply (KSUM_mono isC (PSH (SH0 + 1)) W D _ _ _ (W + Z.of_nat (lev sc) * LW SH0) (D + lev sc * LD)%nat);
[| unfold LW, AMW; pose proof (pow_SH (SH0 + 1) ltac:(lia)); unfold PGSZ; nia| unfold LD; nia].
apply (alloc_slot_ks isC (PSH (SH0 + 1)) SH0 W D HSH0 FUEL sc ltac:(unfold FUEL; lia) [] st L BL LS n _ (ret (st, @None (aptr * Z))) KN KS W D ltac:(lia) ltac:(lia) INV TF).
- apply NoDup_nil_2.
- exact Hsc.
- lia.
- exact FIT'.
- intros j Hj C. apply NA0; lia.
- split; [lia| intros E; lia].
- intros st1 L1 S1. change (-1 <? 0) with true. cbv iota. constructor; [unfold PSH; cbn [fst]; lia| lia| lia].
- intros st1 L1 LS1 _ HA1 S1. change (0 <? 0) with false. cbv iota. destruct (active st1 sc); [| congruence]. constructor; [unfold PSH; cbn [fst]; lia| lia| lia].
Qed.

#[using="HSH0 HXC"] Theorem malloc_small_ks st L BL LS n :
INVL x0 st L BL LS -> 0 <= n < MMAP_THRESHOLD -> SHF st <= SH0 ->
(forall j, 0 <= j < 48 -> j <> XC -> active st j = None) ->
size_to_class n <> XC -> Z.lor (size_to_class n) 1 <> XC ->
KSUM isM (PSH (SH0 + 1)) W D L (malloc st n) KS (W + SMALLW SH0) (D + SMALLD)%nat.
Proof.
intros INV Hn SHC NA0 NX1 NX2. unfold malloc.
set (st0 := set_tick (N.succ (s_tick st)) st).
assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
apply (KSUM_sbind_same isC isM (PSH (SH0 + 1)) (PSH (SH0 + 1)) W D).
- intros L' [st1 [[g idx]|]] W' D' HP HW' HD'; cbn [snd isC ksingle].
+ apply enframe_full_ks; [exact HW'| exact HD'| exact HP].
+ constructor; [exact HP| exact HW'| exact HD'].
- apply (malloc_core_small_ks st0 L BL LS n INV0 TF0' Hn); assumption.
Qed.

#[using="HSH0 HXC"] Theorem cmalloc_small_ks st L BL LS n :
INVL x0 st L BL LS -> 0 <= n < MMAP_THRESHOLD -> SHF st <= SH0 ->
(forall j, 0 <= j < 48 -> j <> XC -> active st j = None) ->
size_to_class n <> XC -> Z.lor (size_to_class n) 1 <> XC ->
KSUM isCC (PSH (SH0 + 1)) W D L (cmalloc (strip st) n) KS (W + SMALLW SH0) (D + SMALLD)%nat.
Proof.
intros INV Hn SHC NA0 NX1 NX2.
eapply (KSUM_strel (fun x => isM (snd x)) isCC (fun x => PSH (SH0 + 1) (snd x)) (PSH (SH0 + 1)) W D MREL); [apply (malloc_control pans0 pupd0 pans0_range st n tt)| | |].
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. unfold isM, isCC; cbn [snd]. destruct r1, r2; try reflexivity; destruct HM.
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. unfold PSH. cbn [fst]. rewrite <- E. exact (fun H => H).
- apply (KSUM_prun pans0 pupd0 pans0_range isM (PSH (SH0 + 1)) W D). apply (malloc_small_ks st L BL LS n INV Hn SHC NA0 NX1 NX2).
Qed.
End SMALL.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjcB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjcB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaiD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaiD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPWv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPWv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQCz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQCz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcV4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcV4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7RC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7RC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhnL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhnL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4en.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4en. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBv7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBv7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn5J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn5J. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhfJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhfJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvVk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwQw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwQw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3dN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dN.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3dN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dN.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation SHF st := (c_meta_alloc_shift (s_ctx st)).
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lone_under (st : mstate) (g : aptr) : Prop :=
m_sizeclass (MR st g) = 44 /\ get_stride (MR st g) < UNIT * size_class 44 /\ m_next (MR st g) = Some g.

Definition GSH (st : mstate) (g0 : optr) : Prop :=
(forall j, 0 <= j < 48 -> j <> 44 -> active st j = None)
/\ active st 44 = g0
/\ (forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st m) = 63 \/ g0 = Some m)
/\ (forall g, g0 = Some g -> lone_under st g /\ live_group st g).

Definition PG (SH : Z) {X : Type} (r : mstate * X) : Prop := PSH SH r /\ exists g0, GSH (fst r) g0.
Definition PGF (SHV : Z) (r : mstate) : Prop := PFR SHV r /\ exists g0, GSH r g0.

#[using="Type"] Lemma GSH_frame st st' g0 :
(forall j, active st' j = active st j) -> s_groups st' = s_groups st ->
(forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> MR st' m = MR st m) ->
GSH st g0 -> GSH st' g0.
Proof.
intros HA HG HM (S1 & S2 & S3 & S4). split; [| split; [| split]].
- intros j Hj NE. rewrite HA. exact (S1 j Hj NE).
- rewrite HA. exact S2.
- intros b m ai Hb. rewrite HG in Hb. rewrite (HM b m ai Hb). exact (S3 b m ai Hb).
- intros g Hg. destruct (S4 g Hg) as [(L1 & L2 & L3) [b [ai Hb]]]. split.
+ unfold lone_under. rewrite (HM b g ai Hb). auto.
+ exists b, ai. rewrite HG. exact Hb.
Qed.

#[using="Type"] Lemma GSH_amf st st' g0 : AM_frame st st' -> GSH st g0 -> GSH st' g0.
Proof. intros AF. apply GSH_frame; [exact (amf_active _ _ AF)| exact (amf_groups _ _ AF)| exact (amf_hmetas _ _ AF)]. Qed.

#[using="Type"] Lemma GSH_same st st' g0 : s_ctx st' = s_ctx st -> s_metas st' = s_metas st -> s_groups st' = s_groups st -> GSH st g0 -> GSH st' g0.
Proof.
intros EC EM EG. apply GSH_frame; [intros j; unfold active, ctx; rewrite EC; reflexivity| exact EG| intros; apply MR_of_metas; exact EM].
Qed.

#[using="Type"] Lemma GSH_strip st g0 : GSH st g0 <-> GSH (strip st) g0.
Proof. split; apply GSH_same; reflexivity. Qed.

#[using="Type"] Lemma GSH_step_seq st g0 : GSH st g0 -> GSH (step_seq st) g0.
Proof.
destruct (step_seq_fields st) as (_ & _ & A & _ & _ & M & G & _). apply GSH_frame; [exact A| exact G| intros; apply MR_of_metas; exact M].
Qed.

#[using="Type"] Lemma GSH_g0_hosted st g0 g : GSH st g0 -> g0 = Some g -> exists b ai, s_groups st !! b = Some (mkGhdr (Some g) ai).
Proof. intros (_ & _ & _ & S4) Hg. destruct (S4 g Hg) as [_ [b [ai Hb]]]. exists b, ai. exact Hb. Qed.

Section BIGG.
Variables (SH : Z) (W : Z) (D : nat).
Hypothesis HSH : 0 <= SH <= 16.

#[using="HSH"] Theorem malloc_core_big_gks st L BL LS n g0 :
INVL x0 st L BL LS -> GSH st g0 -> MMAP_THRESHOLD <= n -> n + IB + UNIT <= 2 ^ 30 -> SHF st <= SH ->
KSUM isC (PG SH) W D L (malloc_core full_lay st n) KS (W + BIGW SH n) (D + BIGD)%nat.
Proof.
intros INV HG Hbig Hn30 SHC. unfold BIGW, BIGD. pose proof (pow_SH SH HSH) as PS.
assert (Hov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; unfold IB, UNIT in *; lia).
unfold malloc_core. rewrite Hov. rewrite (proj2 (Z.leb_le _ _) Hbig).
set (needed := n + IB + UNIT).
assert (HN : 131072 <= needed <= 2 ^ 30) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (round_up_pg_ge needed) as RU.
replace (D + 6)%nat with (S (D + 5))%nat by lia.
eapply (ks_ev' isC (PG SH) W D L _ _ KN (am_kind KN KS st) _ (W + AMW SH) (D + 5)%nat);
[reflexivity| | unfold AMW; unfold PGSZ; nia| | | | intros E; discriminate E| unfold am_kind; destruct (am_quick st); reflexivity].
- cbn [esz_ok]. intros _. split; [lia|]. apply round_up_pg_le_al; [lia| reflexivity].
- cbn [ecost]. change (is_fixed (MAP_PRIVATE + MAP_ANON)) with false. cbv iota. lia.
-
intros a Ha Ca. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb]. cbn [eclass] in Ca. change (is_fixed (MAP_PRIVATE + MAP_ANON)) with false in Ca. cbv iota in Ca.
apply negb_false_iff in Ca. rewrite Ca. constructor; [| unfold AMW, PGSZ; nia| lia].
split; [unfold PSH; cbn [fst]; lia| exists g0; exact HG].
-
intros a Ha Ca. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb]. cbn [eclass] in Ca. change (is_fixed (MAP_PRIVATE + MAP_ANON)) with false in Ca. cbv iota in Ca.
apply negb_true_iff in Ca. rewrite Ca.
change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then Qfya.set_metas ((a, needed, 0) :: ld_metas L) L else Qfya.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. rewrite Ca. cbn iota.
destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha Ca ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
rewrite <- Est1, <- Erid in INV1.
set (L1 := Qfya.set_groups ((a, needed) :: ld_groups L) L) in *.
pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & _).
assert (AQ : am_kind KN KS st = am_kind KN KS (step_seq st1)) by reflexivity.
assert (HG1 : GSH st1 g0) by (rewrite Est1; apply (GSH_same st); [reflexivity| reflexivity| reflexivity| exact HG]).
pose proof (GSH_step_seq st1 g0 HG1) as HG2.
rewrite AQ. replace (D + 5)%nat with (S D + 4)%nat by lia.
eapply (alloc_meta_ks isC (PG SH) W D BL _ _ (xorph x0 (Some rid)) (step_seq st1) L1 KN KS W (S D) SH ltac:(lia) HSH);
[ | | exact INV2| apply amf_refl| apply lf_refl| | split; reflexivity].
+
intros st3 L3 LS3 INV3 AF LF SH3. cbn beta iota.
eapply (ks_ev' isC (PG SH) W D L3 _ _ KN KN _ W D); [reflexivity| exact I| lia| cbn; lia| | intros ru Hru C; cbn in C; discriminate C| intros _; reflexivity| reflexivity].
intros ru Hru _. cbn [answer_ok] in Hru. rewrite Hru. constructor; [| lia| lia].
split; [unfold PSH; cbn [fst]; rewrite s_ctx_drop_region; exact SH3|].
exists g0. cbn [fst]. apply (GSH_same st3); [reflexivity| reflexivity| reflexivity|]. exact (GSH_amf _ _ g0 AF HG2).
+
intros st3 L3 LS3 g INV3 NIg AF LF SH3 _. cbn beta iota zeta. constructor; [| lia| lia].
split; [unfold PSH; cbn -[Z.le Z.add]; exact SH3|].
exists g0. cbn [fst].
pose proof (GSH_amf _ _ g0 AF HG2) as HG3.
set (F := fun mr : meta => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096) (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))).
set (st4 := upd_meta g F st3).
match goal with |- GSH ?s _ => set (st7 := s) end.
assert (A7 : forall j, active st7 j = active st3 j) by (intros j; reflexivity).
assert (M7 : s_metas st7 = s_metas st4) by reflexivity.
assert (G7 : exists ai7, s_groups st7 = <[(rid, 0) := mkGhdr (Some g) ai7]> (s_groups st3)) by (eexists; reflexivity).
destruct G7 as [ai7 G7].
assert (MR4 : forall x, MR st4 x = if aptr_eqb x g then F (MR st3 g) else MR st3 x).
{ intros x. unfold st4, MR. rewrite get_meta_rec_upd. reflexivity. }
assert (NG : s_groups st3 !! (rid, 0) = None).
{ destruct (ir_orph _ _ _ (proj1 INV3) rid eq_refl) as (r & _ & _ & NOG). apply NOG. reflexivity. }
assert (HOST : forall b m ai, s_groups st3 !! b = Some (mkGhdr (Some m) ai) -> m <> g /\ b <> (rid, 0)).
{ intros b m ai Hb. split; [exact (idle_not_hosted _ st3 L3 BL LS3 g b m ai INV3 ltac:(left; reflexivity) Hb)| intros ->; rewrite NG in Hb; discriminate]. }
destruct HG3 as (S1 & S2 & S3 & S4).
split; [| split; [| split]].
* intros j Hj NE. rewrite A7. exact (S1 j Hj NE).
* rewrite A7. exact S2.
* intros b m ai Hb. rewrite G7 in Hb. rewrite (MR_of_metas st4 st7 m M7), MR4.
destruct (aptr_eq_dec b (rid, 0)) as [->|NE].
-- rewrite lookup_insert_eq in Hb. injection Hb as <- _. rewrite aptr_eqb_refl. left. reflexivity.
-- rewrite lookup_insert_ne in Hb by congruence. destruct (HOST b m ai Hb) as [NEg _].
rewrite (aptr_eqb_neq m g NEg). exact (S3 b m ai Hb).
* intros gg Hgg. destruct (S4 gg Hgg) as [LU [b [ai Hb]]]. destruct (HOST b gg ai Hb) as [NEg NEb].
split.
-- unfold lone_under. rewrite (MR_of_metas st4 st7 gg M7), MR4, (aptr_eqb_neq gg g NEg). exact LU.
-- exists b, ai. rewrite G7, lookup_insert_ne by congruence. exact Hb.
+ unfold step_seq. destruct (c_seq (ctx st1) =? 255); rewrite Est1; cbn; exact SHC.
Qed.

#[using="Type"] Lemma s_metas_enframe_at st g idx n off : s_metas (fst (enframe_at st g idx n off)) = s_metas st.
Proof.
unfold enframe_at. destruct (m_mem _); cbn -[wr8 wr16 set_size aadd];
destruct (negb (off =? 0)); cbn [fst]; rewrite s_metas_set_size, ?s_metas_wr8, ?s_metas_wr16, ?s_metas_wr8; reflexivity.
Qed.
#[using="Type"] Lemma s_groups_enframe_at st g idx n off : s_groups (fst (enframe_at st g idx n off)) = s_groups st.
Proof.
unfold enframe_at. destruct (m_mem _); cbn -[wr8 wr16 set_size aadd];
destruct (negb (off =? 0)); cbn [fst]; rewrite s_groups_set_size, ?s_groups_wr8, ?s_groups_wr16, ?s_groups_wr8; reflexivity.
Qed.

#[using="Type"] Lemma enframe_full_gks L st g idx n ctr W' D' : W <= W' -> (D <= D')%nat -> PG SH (st, tt) ->
KSUM isM (PG SH) W D L (enframe_full st g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) KS W' D'.
Proof.
intros HW' HD' [HP [g0 HG]]. unfold PSH in HP. cbn [fst] in HP, HG. unfold enframe_full, enframe_read_off. apply rd8_ks; [exact HW'|]. intros b3.
assert (LEAF : forall off, KSUM isM (PG SH) W D L (let '(st1, p) := enframe_at st g idx n off in ret (havoc p n st1, Some p)) KS W' D').
{ intros off. pose proof (s_ctx_enframe_at st g idx n off) as E.
pose proof (s_metas_enframe_at st g idx n off) as EM. pose proof (s_groups_enframe_at st g idx n off) as EG.
destruct (enframe_at _ _ _ _ _) as [st1 p]. cbn [fst] in E, EM, EG.
constructor; [| exact HW'| exact HD']. split.
- unfold PSH. cbn [fst]. rewrite s_ctx_havoc, E. exact HP.
- exists g0. cbn [fst]. apply (GSH_same st); [rewrite s_ctx_havoc; exact E| rewrite s_metas_havoc; exact EM| rewrite s_groups_havoc; exact EG| exact HG]. }
destruct (negb (b3 =? 0)).
- apply rd16_ks; [exact HW'|]. intros o16. apply LEAF.
- apply LEAF.
Qed.

#[using="HSH"] Theorem malloc_big_gks st L BL LS n g0 :
INVL x0 st L BL LS -> GSH st g0 -> MMAP_THRESHOLD <= n -> n + IB + UNIT <= 2 ^ 30 -> SHF st <= SH ->
KSUM isM (PG SH) W D L (malloc st n) KS (W + BIGW SH n) (D + BIGD)%nat.
Proof.
intros INV HG Hbig Hn30 SHC. unfold malloc.
apply (KSUM_sbind_same isC isM (PG SH) (PG SH) W D).
- intros L' [st1 [[g idx]|]] W' D' HP HW' HD'; cbn [snd isC ksingle].
+ apply enframe_full_gks; [exact HW'| exact HD'| exact HP].
+ constructor; [exact HP| exact HW'| exact HD'].
- apply (malloc_core_big_gks _ L BL LS n g0); [| | exact Hbig| exact Hn30| exact SHC].
+ apply INVL_set_tick; [| exact INV]. lia.
+ apply (GSH_same st); [reflexivity| reflexivity| reflexivity| exact HG].
Qed.

#[using="HSH"] Theorem cmalloc_big_gks st L BL LS n g0 :
INVL x0 st L BL LS -> GSH st g0 -> MMAP_THRESHOLD <= n -> n + IB + UNIT <= 2 ^ 30 -> SHF st <= SH ->
KSUM isCC (PG SH) W D L (cmalloc (strip st) n) KS (W + BIGW SH n) (D + BIGD)%nat.
Proof.
intros INV HG Hbig Hn30 SHC.
eapply (KSUM_strel (fun x => isM (snd x)) isCC (fun x => PG SH (snd x)) (PG SH) W D MREL); [apply (malloc_control pans0 pupd0 pans0_range st n tt)| | |].
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. unfold isM, isCC; cbn [snd]. destruct r1, r2; try reflexivity; destruct HM.
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. intros [HP [g1 HG1]]. split; [unfold PSH in HP |- *; cbn [fst] in HP |- *; rewrite <- E; exact HP|].
exists g1. cbn [fst] in HG1 |- *. rewrite <- E. apply (proj1 (GSH_strip st' g1)). exact HG1.
- apply (KSUM_prun pans0 pupd0 pans0_range isM (PG SH) W D). apply (malloc_big_gks st L BL LS n g0 INV HG Hbig Hn30 SHC).
Qed.

End BIGG.

#[using="Type"] Lemma mask_zero x : 0 <= x -> (forall k, 0 <= k -> Z.testbit x k = true -> k <= 0) -> Z.testbit x 0 = false -> x = 0.
Proof.
intros Hx Hb H0. apply Z.bits_inj_0. intros k.
destruct (Z.lt_ge_cases k 0) as [LT|GE]; [apply Z.testbit_neg_r; exact LT|].
destruct (Z.eq_dec k 0) as [->|NE]; [exact H0|].
destruct (Z.testbit x k) eqn:E; [| reflexivity]. exfalso. pose proof (Hb k GE E). lia.
Qed.

#[using="Type"] Lemma ntf_S {R} (dec : decoder R) f st g i (k : mstate -> mapinfo -> M R) bail :
nontrivial_free dec (S f) st g i k bail =
(let mr := get_meta_rec st g in
let self := bit i in
let sc := m_sizeclass mr in
let mask := Z.lor (m_freed mr) (m_avail mr) in
if (mask + self =? mask_upto (m_last_idx mr)) && okay_to_free st g then
match m_next mr with
| Some _ =>
guard 50 (sc <? 48) (
let activate_new := optr_eqb (active st sc) (Some g) in
let st1 := dequeue (LActive sc) g st in
match activate_new, active st1 sc with
| true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
| _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
end) bail
| None => free_group R dec (nontrivial_free dec f) st g k bail
end
else if mask =? 0 then
guard 51 (sc <? 48) (
let aor (st : mstate) := k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) self) r) st) None in
if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st aor bail
else aor st) bail
else
k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) self) r) st) None).
Proof. reflexivity. Qed.

#[using="Type"] Lemma FUEL_S : FUEL = S (Nat.pred FUEL).
Proof. reflexivity. Qed.

#[using="Type"] Lemma GSH_delA st1 stL g0 m bm aim :
GSH st1 g0 -> s_groups st1 !! bm = Some (mkGhdr (Some m) aim) ->
(forall b, (exists ai, s_groups st1 !! b = Some (mkGhdr (Some m) ai)) -> b = bm) ->
s_groups stL = delete bm (s_groups st1) ->
(forall b x ai, s_groups st1 !! b = Some (mkGhdr (Some x) ai) -> x <> m -> MR stL x = MR st1 x) ->
m_sizeclass (MR st1 m) = 63 -> (forall j, active stL j = active st1 j) -> GSH stL g0.
Proof.
intros (S1 & S2 & S3 & S4) Hbm INJ GL ML SC63 AL. split; [| split; [| split]].
- intros j Hj NE. rewrite AL. exact (S1 j Hj NE).
- rewrite AL. exact S2.
- intros b x ai Hb. rewrite GL in Hb. destruct (aptr_eq_dec b bm) as [->|NE]; [rewrite lookup_delete_eq in Hb; discriminate|].
rewrite lookup_delete_ne in Hb by congruence.
assert (NX : x <> m) by (intros ->; apply NE; apply INJ; exists ai; exact Hb).
rewrite (ML b x ai Hb NX). exact (S3 b x ai Hb).
- intros g Hg. destruct (S4 g Hg) as [LU [b [ai Hb]]].
assert (NX : g <> m) by (intros ->; destruct LU as (L1 & _); rewrite SC63 in L1; discriminate).
split; [unfold lone_under; rewrite (ML b g ai Hb NX); exact LU|].
exists b, ai. rewrite GL, lookup_delete_ne; [exact Hb|]. intros <-. rewrite Hbm in Hb. injection Hb as E _. exact (NX (eq_sym E)).
Qed.

#[using="Type"] Lemma GSH_delB st1 stL m bm aim :
GSH st1 (Some m) -> s_groups st1 !! bm = Some (mkGhdr (Some m) aim) ->
(forall b, (exists ai, s_groups st1 !! b = Some (mkGhdr (Some m) ai)) -> b = bm) ->
s_groups stL = delete bm (s_groups st1) ->
(forall b x ai, s_groups st1 !! b = Some (mkGhdr (Some x) ai) -> x <> m -> MR stL x = MR st1 x) ->
(forall j, j <> 44 -> active stL j = active st1 j) -> active stL 44 = None -> GSH stL None.
Proof.
intros (S1 & S2 & S3 & S4) Hbm INJ GL ML AL A44. split; [| split; [| split]].
- intros j Hj NE. rewrite (AL j NE). exact (S1 j Hj NE).
- exact A44.
- intros b x ai Hb. rewrite GL in Hb. destruct (aptr_eq_dec b bm) as [->|NE]; [rewrite lookup_delete_eq in Hb; discriminate|].
rewrite lookup_delete_ne in Hb by congruence.
assert (NX : x <> m) by (intros ->; apply NE; apply INJ; exists ai; exact Hb).
rewrite (ML b x ai Hb NX). destruct (S3 b x ai Hb) as [E|E]; [left; exact E| exfalso; apply NX; injection E as ->; reflexivity].
- intros g Hg. discriminate Hg.
Qed.

Section FREEG.
Variables (W : Z) (D : nat).

#[using="Type"] Theorem free_gks st L BL LS c off n g0 :
INVL x0 st L BL LS -> In ((c, off), n) BL -> GSH st g0 ->
KSUM isF (PGF (SHF st)) W D L (free st (Some (aadd c (UNIT * off)))) KS W (S D).
Proof.
intros INV Hk HG.
destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
cbn zeta in *.
set (st1 := wr16 (aadd (aadd c (UNIT * off)) (-2)) 0 (wr8 (aadd (aadd c (UNIT * off)) (-3)) 255 st)) in *.
pose proof (ce_ctx _ _ CE1) as CX1.
assert (EM1 : s_metas st1 = s_metas st) by reflexivity.
assert (EG1 : s_groups st1 = s_groups st) by reflexivity.
assert (HG1 : GSH st1 g0) by (apply (GSH_same st); [symmetry; exact CX1| exact EM1| exact EG1| exact HG]).
pose proof INV1 as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (inv_L_lists _ _ IL) as LO.
destruct Hm1 as [aim Hbm].
pose proof (ig_ok _ _ _ IG _ _ _ Hbm) as GO.
assert (INJ : forall b, (exists ai, s_groups st1 !! b = Some (mkGhdr (Some m) ai)) -> b = bm).
{ intros b Hb. exact (hosts_inj _ _ _ IM b bm m Hb (ex_intro _ aim Hbm)). }
assert (MEM : m_mem (MR st1 m) = Some bm).
{ destruct (im_hdr _ _ _ IM bm _ Hbm) as (m1 & E1 & MM & _). cbn in E1. injection E1 as <-. exact MM. }

assert (NFREE : forall b x ai, s_groups st1 !! b = Some (mkGhdr (Some x) ai) -> ~ In x (LS LFree)).
{ intros b x ai Hb Hin. pose proof (il_free _ _ IL x Hin) as E.
destruct (im_hdr _ _ _ IM b _ Hb) as (m1 & E1 & MM & _). cbn in E1. injection E1 as <-. rewrite E in MM. cbn in MM. discriminate. }

assert (CASES : (m_sizeclass (MR st1 m) = 63 /\ m_next (MR st1 m) = None) \/ (g0 = Some m /\ lone_under st1 m /\ active st1 44 = Some m)).
{ destruct HG1 as (S1 & S2 & S3 & S4). destruct (S3 bm m aim Hbm) as [E63|Eg].
- left. split; [exact E63|].
destruct (g_sc _ _ _ _ _ _ GO) as [[A _]|(_ & _ & _ & NL)]; [rewrite E63 in A; lia|].
destruct (m_next (MR st1 m)) as [q|] eqn:EN; [| reflexivity]. exfalso. apply NL. apply (proj1 (il_link _ _ IL m)). rewrite EN. discriminate.
- right. destruct (S4 m Eg) as [LU _]. split; [exact Eg|]. split; [exact LU|]. rewrite S2. exact Eg. }
assert (L0 : m_last_idx (MR st1 m) = 0 /\ m_maplen (MR st1 m) <> 0).
{ destruct CASES as [[E63 _]|(_ & (L1 & L2 & L3) & _)].
- destruct (g_sc _ _ _ _ _ _ GO) as [[A _]|(_ & B & C & _)]; [rewrite E63 in A; lia| auto].
- unfold get_stride in L2. rewrite L1 in L2.
destruct (Z.eqb_spec (m_last_idx (MR st1 m)) 0) as [E|NE]; [| cbn [andb] in L2; lia].
destruct (Z.eqb_spec (m_maplen (MR st1 m)) 0) as [E2|NE2]; [cbn [andb negb] in L2; lia|]. auto. }
destruct L0 as [L0 ML0].
assert (Hi0 : i = 0) by lia. subst i.
destruct (g_masks _ _ _ _ _ _ GO) as (MA0 & MF0 & MA1 & MF1 & _ & _).
pose proof (g_ai _ _ _ _ _ _ GO) as GAI.
assert (AV0 : m_avail (MR st1 m) = 0).
{ apply mask_zero; [exact MA0| intros k Hk0 Hb0; pose proof (MA1 k Hk0 Hb0); lia| exact NA]. }
assert (FR0 : m_freed (MR st1 m) = 0).
{ apply mask_zero; [exact MF0| intros k Hk0 Hb0; pose proof (MF1 k Hk0 Hb0); lia| exact NF]. }
assert (OK : okay_to_free st1 m = true).
{ unfold okay_to_free. fold (MR st1 m). rewrite (g_freeable _ _ _ _ _ _ GO). cbn [Z.eqb].
destruct CASES as [[E63 _]|(_ & (L1 & L2 & L3) & _)]; [rewrite E63; reflexivity|].
rewrite L1. rewrite (proj2 (Z.ltb_lt _ _) L2). reflexivity. }
unfold free. rewrite FH. cbn [sbind]. unfold free_tail.
rewrite (guard_true 60) by (unfold testbit; rewrite Z.lor_spec; fold (MR st1 m); unfold tbit in NA, NF; rewrite NA, NF; reflexivity).
fold (MR st1 m). rewrite FR0, AV0. cbn [Z.eqb orb negb].
rewrite FUEL_S, ntf_S. cbv zeta. fold (MR st1 m). rewrite FR0, AV0, L0, OK. change (Z.lor 0 0 + bit 0 =? mask_upto 0) with true. cbn [andb].

set (K := fun (st2 : mstate) (mi : mapinfo) => match mi with
| Some (base, len) => if negb (len =? 0) then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1)) else ret st2
| None => ret st2 end).
assert (TAIL : forall stD,
s_groups stD = s_groups st1 -> s_metas stD !! m <> None -> data_of (MR stD m) = data_of (MR st1 m) ->
c_meta_alloc_shift (s_ctx stD) = SHF st -> get_head stD LFree = get_head st1 LFree ->
(forall x, x <> m -> MR stD x = MR st1 x) ->
(forall stL, s_groups stL = delete bm (s_groups st1) ->
(forall b x ai, s_groups st1 !! b = Some (mkGhdr (Some x) ai) -> x <> m -> MR stL x = MR st1 x) ->
(forall j, active stL j = active stD j) -> exists g1, GSH stL g1) ->
KSUM isF (PGF (SHF st)) W D L (free_group mstate dec_hdr (nontrivial_free dec_hdr (Nat.pred FUEL)) stD m K (ret st1)) KS W (S D)).
{ intros stD GD PD DD SD HD MD GL.
apply data_of_eq in DD. destruct DD as (Dmem & Dav & Dfr & Dli & Dfa & Dsc & Dml).
unfold free_group. fold (MR stD m). rewrite Dmem, MEM, Dml, Dli, Dsc, L0.
replace (negb (m_maplen (MR st1 m) =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; exact ML0).
set (stU := if m_sizeclass (MR st1 m) <? 48 then set_usage (m_sizeclass (MR st1 m)) (usage stD (m_sizeclass (MR st1 m)) - (0 + 1)) stD else stD).
set (st2 := record_seq (m_sizeclass (MR st1 m)) (step_seq (del_slots bm (get_stride (MR stD m)) (0 + 1) (del_group bm stU)))).
rewrite free_meta_eq. unfold K.
replace (negb (m_maplen (MR st1 m) * 4096 =? 0)) with true.
2:{ symmetry. apply negb_true_iff, Z.eqb_neq. pose proof (g_maplen _ _ _ _ _ _ GO). lia. }

assert (FU : s_groups stU = s_groups stD /\ s_metas stU = s_metas stD /\ (forall j, active stU j = active stD j)
/\ c_meta_alloc_shift (s_ctx stU) = c_meta_alloc_shift (s_ctx stD) /\ get_head stU LFree = get_head stD LFree).
{ unfold stU. destruct (_ <? 48); repeat split; reflexivity. }
destruct FU as (GU & MU & AU & SU & HU).
destruct (step_seq_fields (del_slots bm (get_stride (MR stD m)) (0 + 1) (del_group bm stU))) as (_ & _ & AS & _ & _ & MS & GS & _).
assert (RSF : forall s sc, s_groups (record_seq sc s) = s_groups s /\ s_metas (record_seq sc s) = s_metas s /\ (forall j, active (record_seq sc s) j = active s j)
/\ c_meta_alloc_shift (s_ctx (record_seq sc s)) = c_meta_alloc_shift (s_ctx s) /\ get_head (record_seq sc s) LFree = get_head s LFree).
{ intros s sc. unfold record_seq. destruct (sc_in_seq_range sc); repeat split; reflexivity. }
destruct (RSF (step_seq (del_slots bm (get_stride (MR stD m)) (0 + 1) (del_group bm stU))) (m_sizeclass (MR st1 m))) as (GR & MRR & AR & SR & HR).
fold st2 in GR, MRR, AR, SR, HR.
assert (G2 : s_groups st2 = delete bm (s_groups st1)) by (rewrite GR, GS; cbn; rewrite GU, GD; reflexivity).
assert (M2 : s_metas st2 = s_metas stD) by (rewrite MRR, MS; cbn; exact MU).
assert (A2 : forall j, active st2 j = active stD j).
{ intros j. rewrite AR, AS. change (active (del_slots bm (get_stride (MR stD m)) (0 + 1) (del_group bm stU)) j) with (active stU j). apply AU. }
assert (S2' : c_meta_alloc_shift (s_ctx st2) = SHF st).
{ rewrite SR. unfold step_seq. destruct (c_seq _ =? 255); cbn; rewrite SU; exact SD. }
assert (H2 : get_head st2 LFree = get_head st1 LFree).
{ rewrite HR, <- HD, <- HU. unfold step_seq. destruct (c_seq _ =? 255); reflexivity. }
set (stF := fm_st st2 m).
destruct (queue_frame LFree m (put_meta m meta0 st2)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & QC).
change (queue_st LFree m (put_meta m meta0 st2)) with stF in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, QC.
assert (GF : s_groups stF = delete bm (s_groups st1)) by (rewrite Q5; cbn; exact G2).
assert (AF : forall j, active stF j = active stD j).
{ intros j. change (active stF j) with (get_head stF (LActive j)). unfold stF, fm_st. rewrite queue_head.
destruct (decide (LActive j = LFree)); [discriminate|]. rewrite <- A2. reflexivity. }
assert (SF : c_meta_alloc_shift (s_ctx stF) = SHF st) by (rewrite (cb_shift _ _ QC); cbn; exact S2').
assert (MF : forall b x ai, s_groups st1 !! b = Some (mkGhdr (Some x) ai) -> x <> m -> MR stF x = MR st1 x).
{ intros b x ai Hb NX. pose proof (NFREE b x ai Hb) as NXF.
rewrite <- (MD x NX). rewrite <- (MR_of_metas stD st2 x M2).
unfold stF, fm_st, MR, get_meta_rec. rewrite (queue_metas_other LFree m (put_meta m meta0 st2) x NX).
- cbn. rewrite lookup_insert_ne by congruence. reflexivity.
- intros a Ha. change (get_head (put_meta m meta0 st2) LFree) with (get_head st2 LFree) in Ha. rewrite H2 in Ha.
assert (Hin : In a (LS LFree)).
{ pose proof (il_head _ _ IL LFree) as HH. rewrite Ha in HH. destruct (LS LFree) as [|a' rest]; cbn in HH; [discriminate|]. injection HH as ->. left. reflexivity. }
split; [intros ->; exact (NXF Hin)|].
assert (NAm : a <> m) by (intros ->; exact (NFREE bm m aim Hbm Hin)).
unfold MR. rewrite (get_meta_rec_put_other _ _ _ _ NAm). fold (MR st2 a). rewrite (MR_of_metas stD st2 a M2), (MD a NAm).
destruct (lists_prev_in st1 LS LO LFree a Hin) as (y & Hy & HP & _). rewrite HP. intros E. injection E as ->. exact (NXF Hy). }
eapply (ks_ev' isF (PGF (SHF st)) W D L _ _ KS KS _ W D);
[reflexivity| exact I| lia| cbn; lia| | intros ru Hru C; cbn in C; discriminate C| intros _; reflexivity| reflexivity].
intros ru Hru _. cbn [answer_ok] in Hru. rewrite Hru. constructor; [| lia| lia].
split; [unfold PFR; cbn; exact SF|].
destruct (GL (drop_region (fst bm) stF) ltac:(cbn; exact GF) ltac:(intros b x ai Hb NX; unfold MR, get_meta_rec; cbn; apply (MF b x ai Hb NX)) ltac:(intros j; apply AF)) as [g1 HG'].
exists g1. exact HG'. }
destruct CASES as [[E63 NXT]|(Eg0 & LU & A44)].
-
rewrite NXT. apply TAIL.
+ reflexivity.
+ exact (g_present _ _ _ _ _ _ GO).
+ reflexivity.
+ rewrite <- CX1. reflexivity.
+ reflexivity.
+ intros; reflexivity.
+ intros stL GL ML AL. exists g0. exact (GSH_delA st1 stL g0 m bm aim HG1 Hbm INJ GL ML E63 AL).
-
destruct LU as (L44 & LSTR & LNX). rewrite LNX.
rewrite (guard_true 50) by (rewrite L44; reflexivity).
rewrite L44, A44. change (optr_eqb (Some m) (Some m)) with (aptr_eqb m m). rewrite aptr_eqb_refl.
pose proof (head_self_singleton _ st1 L (bl_remove c BL) LS 44 m INV1 A44 LNX) as HL.
assert (PRV : m_prev (MR st1 m) = Some m).
{ pose proof (il_dll _ _ IL (LActive 44)) as DL. rewrite HL in DL. cbn in DL. destruct DL as (_ & P & _). exact P. }
assert (AD : forall j, active (dequeue (LActive 44) m st1) j = if j =? 44 then None else active st1 j).
{ intros j. change (active (dequeue (LActive 44) m st1) j) with (get_head (dequeue (LActive 44) m st1) (LActive j)).
rewrite dequeue_head. fold (MR st1 m). rewrite LNX. change (optr_eqb (Some m) (Some m)) with (aptr_eqb m m). rewrite aptr_eqb_refl.
destruct (Z.eqb_spec j 44) as [->|NE]; [destruct (decide (LActive 44 = LActive 44)); [reflexivity| congruence]|].
destruct (decide (LActive j = LActive 44)) as [E|_]; [congruence| reflexivity]. }
rewrite (AD 44). rewrite Z.eqb_refl.
destruct (dequeue_frame (LActive 44) m st1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
apply TAIL.
+ exact F5.
+ apply dequeue_key_m.
+ apply dequeue_data.
+ rewrite (cb_shift _ _ FC), <- CX1. reflexivity.
+ rewrite dequeue_head. destruct (decide (LFree = LActive 44)); [discriminate| reflexivity].
+ intros x NX. unfold MR, get_meta_rec. rewrite (dequeue_metas_other (LActive 44) m st1 x NX); [reflexivity| |]; fold (MR st1 m); [rewrite PRV| rewrite LNX]; intros E; injection E as ->; exact (NX eq_refl).
+ intros stL GL ML AL. exists None. apply (GSH_delB st1 stL m bm aim); [rewrite <- Eg0; exact HG1| exact Hbm| exact INJ| exact GL| exact ML| |].
* intros j NE. rewrite AL, AD. replace (j =? 44) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
* rewrite AL, AD, Z.eqb_refl. reflexivity.
Qed.

Section CTRL.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

#[using="pans pupd Hpans"] Theorem cfree_gks (o : O) st L BL LS c off n g0 :
INVL x0 st L BL LS -> In ((c, off), n) BL -> GSH st g0 ->
KSUM isF (PGF (SHF st)) W D L (cfree (strip st) (Some c)) KS W (S D).
Proof.
intros INV Hk HG.
eapply (KSUM_strel (fun x => isF (snd x)) isF (fun x => PGF (SHF st) (snd x)) _ W D (FREL (O:=O)));
[apply (free_control pans pupd st (aadd c (UNIT * off)) c); exact (INVL_hdr_ok pans pupd st L BL LS c off n INV Hk)| | |].
- intros; reflexivity.
- intros [o' st'] cs E [HP [g1 HG1]]. unfold FREL in E. cbn [snd] in E, HP, HG1 |- *. rewrite <- E. split; [exact HP|]. exists g1. apply (proj1 (GSH_strip st' g1)). exact HG1.
- apply (KSUM_prun pans pupd Hpans isF (PGF _) W D). exact (free_gks st L BL LS c off n g0 INV Hk HG).
Unshelve. all: try exact o.
Qed.
End CTRL.
End FREEG.

#[using="Type"] Lemma gcnt_none st sc :
(forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st m) <> sc) -> gcnt st sc = 0.
Proof.
intros H. rewrite gcnt_unfold.
assert (ALL : forall bh, In bh (map_to_list (s_groups st)) -> gterm st sc bh = 0).
{ intros [b [gm ai]] Hin. apply (proj2 (list_elem_of_In _ _)) in Hin. apply elem_of_map_to_list in Hin. unfold gterm. cbn.
destruct gm as [m|]; [| reflexivity]. destruct (Z.eqb_spec (m_sizeclass (MR st m)) sc) as [E|NE]; [| reflexivity].
exfalso. exact (H b m ai Hin E). }
induction (map_to_list (s_groups st)) as [|x l IH]; [reflexivity|]. cbn [map zsum fold_right]. rewrite (ALL x ltac:(left; reflexivity)).
unfold zsum in IH. rewrite IH; [reflexivity|]. intros bh Hbh. apply ALL. right. exact Hbh.
Qed.

Section FIRSTG.
Variables (SH : Z) (W : Z) (D : nat).
Hypothesis HSH : 0 <= SH <= 16.

Definition first_req (n : Z) : Prop :=
1004 < n < MMAP_THRESHOLD /\ size_to_class n = 44 /\ round_up_pg (n + IB + UNIT) < UNIT * size_class 44 + UNIT.

#[using="Type"] Lemma first_req_65536 : first_req 65536.
Proof. unfold first_req. split; [unfold MMAP_THRESHOLD; lia|]. split; vm_compute; reflexivity. Qed.

#[using="HSH"] Theorem malloc_core_first_gks st L BL LS n :
INVL x0 st L BL LS -> TF0 st -> GSH st None -> first_req n -> SHF st <= SH ->
KSUM isC (PG SH) W D L (malloc_core full_lay st n) KS (W + FRESHW SH) (D + FRESHD)%nat.
Proof.
intros INV TF HG (Hn & SC44 & UND) SHC. unfold FRESHW, FRESHD.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
assert (Hov : size_overflows n = false) by (unfold size_overflows; apply Z.leb_gt; unfold IB, UNIT, MMAP_THRESHOLD in *; lia).
unfold malloc_core. rewrite Hov. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT]. rewrite SC44 in FIT.
destruct HG as (S1 & S2 & S3 & S4).
assert (HA : active st 44 = None) by exact S2.
unfold malloc_small_ctrl. rewrite SC44, HA. change ((4 <=? 44) && (44 <? 32)) with false. cbn [andb].
rewrite HA. change (lowbit 0) with 0. cbn [negb Z.eqb].
unfold FUEL. replace (D + 5)%nat with (S D + AMD)%nat by (unfold AMD; lia).
replace (W + (AMW SH + 2 ^ 20)) with (W + 2 ^ 20 + AMW SH) by lia.
assert (U0 : usage st 44 = 0).
{ rewrite (ia_usage _ IA 44 ltac:(lia)). apply gcnt_none. intros b m ai Hb E. destruct (S3 b m ai Hb) as [E'|E']; [rewrite E in E'; discriminate| discriminate]. }
assert (NB : is_bouncing 44 st = false) by reflexivity.
apply (alloc_slot_fresh_ks SH W D HSH isC (PG SH) 63 [] st L BL LS 44 n _ (ret (st, @None (aptr * Z))) KN KS INV TF); try assumption.
- apply NoDup_nil_2.
- unfold big_class. lia.
- lia.
- intros st1 L1 (A1 & G1 & M1) SH1'. change (-1 <? 0) with true. cbv iota. constructor; [| lia| lia].
split; [exact SH1'|]. exists None. cbn [fst]. apply (GSH_frame st st1 None A1 G1 M1). exact (conj S1 (conj S2 (conj S3 S4))).
- intros st1 L1 LS1 _ HA1 SL SH1'. change (0 <? 0) with false. cbv iota.
destruct SL as (g & c3 & n3 & E3 & HA4 & ACT4 & (b0 & ai0 & XG & XN & XM) & XH & NX4 & SC4 & STR4).
rewrite HA4. constructor; [| lia| lia]. split; [exact SH1'|]. exists (Some g). cbn [fst].

assert (E13 : c3 = 1 /\ n3 = round_up_pg (n + IB + UNIT)).
{ revert E3. unfold agu. rewrite U0, NB. change (Z.even 44 && (44 <? 32)) with false. cbn [andb Z.add].
unfold ag_cn3. cbn [negb andb]. replace (ag_cnt2 44 (ag_cnt1 44 0) 0 false <=? 7) with true by (vm_compute; reflexivity).
rewrite (proj2 (Z.ltb_lt _ _) UND). cbn [orb]. intros E. injection E as <- <-. split; reflexivity. }
destruct E13 as [-> ->]. change (1 - 1 =? 0) with true in STR4. cbv iota in STR4.
split; [| split; [| split]].
+ intros j Hj NE. rewrite (ACT4 j NE). exact (S1 j Hj NE).
+ exact HA4.
+ intros b m ai Hb. rewrite XG in Hb. destruct (aptr_eq_dec b b0) as [->|NE].
* rewrite lookup_insert_eq in Hb. injection Hb as <- _. right. reflexivity.
* rewrite lookup_insert_ne in Hb by congruence. destruct (XH b m ai Hb) as [NX EX]. rewrite EX.
destruct (S3 b m ai Hb) as [E|E]; [left; exact E| discriminate E].
+ intros g' Hg'. injection Hg' as <-. split.
* unfold lone_under. rewrite SC4, STR4, NX4. split; [reflexivity|]. split; [| reflexivity]. unfold UNIT, IB in *. lia.
* exists b0, ai0. rewrite XG, lookup_insert_eq. reflexivity.
Qed.

#[using="HSH"] Theorem malloc_first_gks st L BL LS n :
INVL x0 st L BL LS -> GSH st None -> first_req n -> SHF st <= SH ->
KSUM isM (PG SH) W D L (malloc st n) KS (W + FRESHW SH) (D + FRESHD)%nat.
Proof.
intros INV HG Hn SHC. unfold malloc.
set (st0 := set_tick (N.succ (s_tick st)) st).
assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
apply (KSUM_sbind_same isC isM (PG SH) (PG SH) W D).
- intros L' [st1 [[g idx]|]] W' D' HP HW' HD'; cbn [snd isC ksingle].
+ apply enframe_full_gks; [exact HW'| exact HD'| exact HP].
+ constructor; [exact HP| exact HW'| exact HD'].
- apply (malloc_core_first_gks st0 L BL LS n INV0 TF0'); [| exact Hn| exact SHC].
apply (GSH_same st); [reflexivity| reflexivity| reflexivity| exact HG].
Qed.

#[using="HSH"] Theorem cmalloc_first_gks st L BL LS n :
INVL x0 st L BL LS -> GSH st None -> first_req n -> SHF st <= SH ->
KSUM isCC (PG SH) W D L (cmalloc (strip st) n) KS (W + FRESHW SH) (D + FRESHD)%nat.
Proof.
intros INV HG Hn SHC.
eapply (KSUM_strel (fun x => isM (snd x)) isCC (fun x => PG SH (snd x)) (PG SH) W D MREL); [apply (malloc_control pans0 pupd0 pans0_range st n tt)| | |].
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. unfold isM, isCC; cbn [snd]. destruct r1, r2; try reflexivity; destruct HM.
- intros [o [st' r1]] [cs r2] [E HM]; cbn [fst snd] in E, HM |- *. intros [HP [g1 HG1]]. split; [unfold PSH in HP |- *; cbn [fst] in HP |- *; rewrite <- E; exact HP|].
exists g1. cbn [fst] in HG1 |- *. rewrite <- E. apply (proj1 (GSH_strip st' g1)). exact HG1.
- apply (KSUM_prun pans0 pupd0 pans0_range isM (PG SH) W D). apply (malloc_first_gks st L BL LS n INV HG Hn SHC).
Qed.

End FIRSTG.

#[using="Type"] Lemma GSH_init secret resv : GSH (minit secret resv) None.
Proof.
split; [| split; [| split]].
- intros j _ _. unfold active, get_head. cbn. rewrite lookup_empty. reflexivity.
- unfold active. cbn. rewrite lookup_empty. reflexivity.
- intros b m ai Hb. cbn in Hb. rewrite lookup_empty in Hb. discriminate.
- intros g Hg. discriminate.
Qed.

Definition stc44_f (k : Z) : bool := negb (stc_k k =? 44) || (4095 <=? k).
#[using="Type"] Lemma stc44_b_true : forallb stc44_f (zrange 0 8191) = true. Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma size_to_class_44_lb n : 0 <= n < MMAP_THRESHOLD -> size_to_class n = 44 -> 65517 <= n.
Proof.
intros Hn E. rewrite size_to_class_k in E. rewrite Z.shiftr_div_pow2 in E by lia. unfold IB, UNIT, MMAP_THRESHOLD in *.
set (k := (n + 4 - 1) / 2 ^ 4) in E.
assert (Hk : 0 <= k < 8191) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (Hk2 : 16 * k <= n + 3 < 16 * k + 16) by (subst k; change (2 ^ 4) with 16; pose proof (Z.div_mod (n + 4 - 1) 16 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 4 - 1) 16 ltac:(lia)); lia).
pose proof (forallb_zrange stc44_f 0 8191 k stc44_b_true ltac:(lia) ltac:(lia)) as H. unfold stc44_f in H.
rewrite E, Z.eqb_refl in H. cbn in H. apply Z.leb_le in H. lia.
Qed.

#[using="Type"] Lemma lor1_odd x : Z.testbit (Z.lor x 1) 0 = true.
Proof. rewrite Z.lor_spec. change (Z.testbit 1 0) with true. apply orb_true_r. Qed.

#[using="Type"] Lemma lor1_ne_44 x : Z.lor x 1 <> 44.
Proof. intros E. pose proof (lor1_odd x) as H. rewrite E in H. cbn in H. discriminate. Qed.

#[using="Type"] Lemma lor1_le x : 0 <= x -> Z.lor x 1 <= x + 1.
Proof. intros Hx. pose proof (Z.add_lor_land x 1). pose proof (Z.land_nonneg x 1). lia. Qed.

End RC__1.
