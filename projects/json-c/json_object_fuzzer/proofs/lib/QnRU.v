(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh QQwg QKTr QJBH QvG1 QDw3 QUxU QNwL QYnC QmP7 Q9Ho QYyZ QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QDw3 QUxU QNwL QYnC QmP7.Mq0 Q9Ho.Mq1 QYyZ.Mq0.
Import QlES. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Ltac gc_split GC :=
destruct GC as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A8b & A9 & A10 & A11 & A12 & A13).

Lemma gcons_retag_nonlive {BAND : Band} : forall a LB FS G RE X c i t0 t1,
gcons a LB FS G RE X -> tag_at G c i = Some t0 -> is_live t0 = false ->
(forall q, holds q t1 = false) -> is_live t1 = false ->
gcons a LB FS (set_tag c i t1 G) RE X.
Proof.
intros a LB FS G RE X c i t0 t1 GC Ht NL0 NH NL. gc_split GC.
pose proof (retag_at G c i t0 t1 Ht) as RT.
split; [exact A1|]. split.
{ intros q Aq nq Hq. destruct (A2 q Aq nq Hq) as [[H1|H1] H2]; split; [| exact H2| right; exact H1| exact H2].
left. destruct H1 as (id' & i' & E & Hn & HP & Ht' & Hi' & HA). exists id', i'. repeat (split; [assumption|]).
split; [| split; [exact Hi'| exact HA]]. rewrite RT.
destruct (Z.eqb_spec (class_of nq) c) as [EC|NC]; [destruct (Z.eqb_spec i' i) as [EI|NI]|]; cbn [andb]; try exact Ht'.
exfalso. rewrite EC, EI, Ht in Ht'. inversion Ht'. subst t0. cbn in NL0. discriminate. }
split; [exact A3|]. split.
{ intros c' i' q Hq. rewrite RT in Hq. destruct ((c' =? c) && (i' =? i)) eqn:E; [| exact (A4 _ _ _ Hq)].
inversion Hq; subst t1. cbn in NL. discriminate. }
split.
{ intros c' i' q Hq. rewrite RT in Hq. destruct ((c' =? c) && (i' =? i)) eqn:E; [| exact (A5 _ _ _ Hq)].
inversion Hq; subst t1. specialize (NH q). cbn in NH. rewrite aptr_eqb_refl' in NH. discriminate. }
split.
{ intros c' NE. rewrite ncarved_set_tag. apply A6. intros E. apply NE.
destruct (Z.eq_dec c' c) as [->|NC]; [rewrite set_tag_class, E; reflexivity| rewrite set_tag_other_class by exact NC; exact E]. }
split; [exact A7|]. split.
{ intros c1 i1 c2 i2 q u1 u2 H1 H2 K1 K2. rewrite RT in H1, H2.
destruct ((c1 =? c) && (i1 =? i)) eqn:E1; [inversion H1; subst u1; rewrite NH in K1; discriminate|].
destruct ((c2 =? c) && (i2 =? i)) eqn:E2; [inversion H2; subst u2; rewrite NH in K2; discriminate|].
exact (A8 _ _ _ _ q _ _ H1 H2 K1 K2). }
split.
{ intros c1 i1 t id1 n1 H1 K1. rewrite RT in H1. destruct ((c1 =? c) && (i1 =? i)) eqn:E; [inversion H1; subst t; rewrite NH in K1; discriminate|].
eapply A8b; eassumption. }
repeat (split; [assumption|]). exact A13.
Qed.

Lemma tag_at_gappend_inv : forall G c l c' i t,
tag_at (gappend c l G) c' i = Some t -> tag_at G c' i = Some t \/ (c' = c /\ In t l /\ ncarved G c <= i).
Proof.
intros G c l c' i t Ht. destruct (Z.lt_ge_cases i (ncarved G c')) as [LT|GE].
- left. rewrite tag_at_gappend_old in Ht by exact LT. exact Ht.
- destruct (Z.eq_dec c' c) as [->|NE].
+ right. rewrite tag_at_gappend_new in Ht by exact GE. split; [reflexivity|]. split; [| exact GE].
eapply nth_error_In. exact Ht.
+ exfalso. unfold tag_at, gappend in Ht. rewrite gset_ne in Ht by exact NE. unfold ncarved in GE.
destruct (Z.ltb_spec i 0); [discriminate|].
assert (L : (Z.to_nat i < length (G c'))%nat) by (apply nth_error_Some; rewrite Ht; discriminate). lia.
Qed.

Lemma gcons_gappend {BAND : Band} : forall a a' LB FS G RE X c l,
gcons a LB FS G RE X ->
1 <= c < kNumClasses ->
Forall (fun t => is_live t = false /\ forall q, holds q t = false) l ->
(forall c', c' <> c -> cls a' c' = cls a c') ->
ncarved G c * class_size c = c_alloc_user (cls a c) ->
c_alloc_user (cls a' c) = c_alloc_user (cls a c) + Z.of_nat (length l) * class_size c ->
0 <= c_alloc_user (cls a c) ->
c_alloc_user (cls a' c) <= c_mapped_user (cls a' c) -> c_mapped_user (cls a' c) <= kFreeArrayOffset ->
c_mapped_user (cls a' c) mod kUserMapSize = 0 ->
as_reg a' = as_reg a -> as_next a' = as_next a ->
gcons a' LB FS (gappend c l G) RE X.
Proof.
intros a a' LB FS G RE X c l GC Hc FL EO NCA EA A0 B1 B2 B3 ER EN. gc_split GC.
pose proof kconsts as (_ & _ & _ & K32 & _).
pose proof (class_size_facts c ltac:(rewrite K32 in Hc; lia)) as [S1 _].
assert (LP : 0 <= Z.of_nat (length l) * class_size c) by (clear - S1; nia).
assert (NEW : forall t, In t l -> is_live t = false /\ forall q, holds q t = false)
by (intros t Ht; exact (proj1 (List.Forall_forall _ _) FL t Ht)).
split; [exact A1|]. split.
{ intros q Aq nq Hq. destruct (A2 q Aq nq Hq) as [[H1|H1] H2]; split; [| exact H2| | exact H2].
- left. destruct H1 as (id' & i' & E & Hn & HP & Ht' & Hi' & HA). exists id', i'. repeat (split; [assumption|]).
split; [apply tag_at_gappend_Some_old; exact Ht'| split; [exact Hi'| exact HA]].
- right. destruct H1 as (mb & E & H3 & H4 & H5 & H6). exists mb. rewrite ER. repeat split; assumption. }
split; [exact A3|]. split.
{ intros c' i' q Hq. apply tag_at_gappend_inv in Hq as [Hq|(-> & Hin & _)]; [exact (A4 _ _ _ Hq)|].
destruct (NEW _ Hin) as [NL _]. cbn in NL. discriminate. }
split.
{ intros c' i' q Hq. apply tag_at_gappend_inv in Hq as [Hq|(-> & Hin & _)]; [exact (A5 _ _ _ Hq)|].
destruct (NEW _ Hin) as [_ NH]. specialize (NH q). cbn in NH. rewrite aptr_eqb_refl' in NH. discriminate. }
split.
{ intros c' NE. rewrite ncarved_gappend. destruct (Z.eqb_spec c' c) as [->|NC].
- split; [exact Hc|]. rewrite EA, <- NCA. clear. lia.
- rewrite gappend_other_class in NE by exact NC. destruct (A6 c' NE) as [X1 X2]. split; [exact X1|].
rewrite EO by exact NC. rewrite <- X2. lia. }
split.
{ intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NC]; [| rewrite EO by exact NC; apply A7; exact Hc'].
split; [| split; [exact B2| exact B3]]. clear - EA A0 B1 LP. lia. }
split.
{ intros c1 i1 c2 i2 q u1 u2 H1 H2 K1 K2.
apply tag_at_gappend_inv in H1 as [H1|(E1 & In1 & _)]; [| destruct (NEW _ In1) as [_ NH]; rewrite NH in K1; discriminate].
apply tag_at_gappend_inv in H2 as [H2|(E2 & In2 & _)]; [| destruct (NEW _ In2) as [_ NH]; rewrite NH in K2; discriminate].
exact (A8 _ _ _ _ q _ _ H1 H2 K1 K2). }
split.
{ intros c1 i1 t id1 n1 H1 K1. rewrite EN.
apply tag_at_gappend_inv in H1 as [H1|(E1 & In1 & _)]; [| destruct (NEW _ In1) as [_ NH]; rewrite NH in K1; discriminate].
eapply A8b; eassumption. }
rewrite ER. repeat (split; [assumption|]). exact A13.
Qed.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QDw3 QUxU QNwL QYnC QmP7.Mq0 QYyZ.Mq0.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma pairwise_disjoint_snoc : forall l iv,
pairwise_disjoint l -> Forall (fun jv => iv_disjoint jv iv) l -> pairwise_disjoint (l ++ [iv]).
Proof.
induction l as [|x l IH]; intros iv PD F; cbn.
- split; [constructor| exact I].
- destruct PD as [F1 PD]. inversion F; subst. split.
+ apply Forall_app. split; [exact F1| constructor; [assumption| constructor]].
+ apply IH; assumption.
Qed.

Lemma gcons_reg_add {BAND : Band} : forall a a1 LB FS G RE X mb msz n,
gcons a LB FS G RE X ->
as_reg a1 = as_reg a ++ [mkSec mb msz n] ->
(forall c, cls a1 c = cls a c) -> as_next a1 = as_next a ->
sec_ok RE X (mkSec mb msz n) ->
(forall e, In e (as_reg a) -> mb + msz <= se_beg e \/ se_beg e + se_size e <= mb) ->
0 < msz ->
gcons a1 LB FS G RE X.
Proof.
intros a a1 LB FS G RE X mb msz n GC ER EC EN SOK AVR MSZ. pose proof GC as GC0. gc_split GC.
split; [exact A1|]. split.
{ intros p A k H. destruct (A2 p A k H) as [[H1|H1] H2]; split; [left; exact H1| exact H2| | exact H2].
right. destruct H1 as (mb' & E & H3 & H4 & H5 & H6). exists mb'. rewrite ER. repeat (split; [assumption|]). split; [apply in_or_app; left; exact H5| exact H6]. }
split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split.
{ intros c Hc. destruct (A6 c Hc) as [X1 X2]. split; [exact X1|]. rewrite EC. exact X2. }
split. { intros c Hc. rewrite EC. apply A7. exact Hc. }
split; [exact A8|]. split. { intros c i t id k Ht Hh. rewrite EN. exact (A8b c i t id k Ht Hh). }
rewrite ER. split.
{ apply Forall_app. split; [exact A9| constructor; [exact SOK| constructor]]. }
split.
{ rewrite map_app. cbn [map]. apply pairwise_disjoint_snoc; [exact A10|].
apply List.Forall_forall. intros jv Hin. apply in_map_iff in Hin. destruct Hin as (e & <- & He).
unfold iv_disjoint. cbn [fst snd se_beg se_size]. pose proof (AVR e He). lia. }
split.
{ rewrite map_app. cbn [map se_beg]. apply NoDup_app; [exact A11| constructor; [intros []| constructor]|].
intros x Hx Hx2. cbn [In] in Hx2. destruct Hx2 as [Ex|[]]. apply in_map_iff in Hx. destruct Hx as (e & E & He).
pose proof (AVR e He) as D. pose proof (proj1 (List.Forall_forall _ _) A9 e He) as (_ & _ & _ & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1. pose proof kconsts as (_ & _ & _ & _ & KP & _). subst x. rewrite <- Ex in D. lia. }
split; [exact A12| exact A13].
Qed.

Lemma gcons_alloc_sec {BAND : Band} : forall a LB FS G RE X mb n,
gcons a LB FS G RE X ->
In (mkSec mb (sec_map_size n) n) (as_reg a) ->
~ In (ASec mb n) (map ablk_id LB) ->
0 <= n <= 2^26 -> from_primary n = false ->
gcons a ((ASec mb n, mb + kSecUserOff, n) :: LB) FS G RE X.
Proof.
intros a LB FS G RE X mb n GC HR NOTIN Hn HP. gc_split GC.
split; [exact A1|]. split.
{ intros p A k [H|H].
- inversion H; subst. split; [| lia]. right. exists mb. repeat (split; [first [reflexivity| lia| assumption]|]). reflexivity.
- exact (A2 p A k H). }
split. { cbn [map ablk_id fst]. constructor; [exact NOTIN| exact A3]. }
split.
{ intros c i q Hq. destruct (A4 _ _ _ Hq) as (id' & n' & A' & E & Hin & Hc'). exists id', n', A'. split; [exact E|]. split; [right; exact Hin| exact Hc']. }
split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A8b|].
split; [exact A9|]. split; [exact A10|]. split; [exact A11|]. split; [exact A12| exact A13].
Qed.

Lemma sec_id_fresh {BAND : Band} : forall a LB FS G RE X mb n,
gcons a LB FS G RE X -> ~ In mb (map se_beg (as_reg a)) -> ~ In (ASec mb n) (map ablk_id LB).
Proof.
intros a LB FS G RE X mb n GC NI Hin. apply in_map_iff in Hin. destruct Hin as ([[q A'] n'] & Eq & Hin). cbn in Eq. subst q.
gc_split GC. destruct (A2 _ _ _ Hin) as [[(id' & i1 & E & _)|(mb' & E & _ & _ & HR & _)] _]; [discriminate|].
injection E as Emb En. apply NI. apply in_map_iff. exists (mkSec mb' (sec_map_size n') n'). split; [cbn; congruence| exact HR].
Qed.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig Q0Do QyW2 Qp4j QSsj QNQk QkfD QUnM QqLk QZbm QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QNwL QYnC QSsj QNQk.Mq1 QkfD QUnM QqLk QZbm QYyZ.Mq5 QpY2.Mq7.
Import QlES. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Local Ltac rtk RT k H := pose proof (RT_img _ _ _ RT k _ _ eq_refl) as H; cbn [fst snd] in H;
lazymatch type of H with ro_cells _ _ ?a _ => let a' := eval vm_compute in a in change a with a' in H end.

Lemma RTconst_rt_consts {BAND : Band} : forall RE X m, RTconst RE X m -> rt_consts_at asegs m.
Proof.
intros RE X m RT. unfold rt_consts_at.
rtk RT 46%nat K46. rtk RT 47%nat K47. rtk RT 48%nat K48. rtk RT 49%nat K49. rtk RT 50%nat K50.
rtk RT 51%nat K51. rtk RT 52%nat K52. rtk RT 53%nat K53. rtk RT 54%nat K54.
rtk RT 18%nat K18. rtk RT 19%nat K19. rtk RT 20%nat K20. rtk RT 42%nat K42.
rtk RT 55%nat K55. rtk RT 23%nat K23. rtk RT 56%nat K56. rtk RT 57%nat K57. rtk RT 58%nat K58. rtk RT 59%nat K59. rtk RT 60%nat K60.
rtk RT 0%nat K0. rtk RT 40%nat K40. rtk RT 1%nat K1. rtk RT 2%nat K2. rtk RT 8%nat K8.
rtk RT 61%nat K61. rtk RT 62%nat K62. rtk RT 63%nat K63. rtk RT 64%nat K64. rtk RT 65%nat K65. rtk RT 66%nat K66.
rtk RT 67%nat K67. rtk RT 68%nat K68. rtk RT 16%nat K16. rtk RT 69%nat K69. rtk RT 70%nat K70.
rtk RT 71%nat K71. rtk RT 72%nat K72. rtk RT 73%nat K73. rtk RT 74%nat K74. rtk RT 75%nat K75. rtk RT 76%nat K76. rtk RT 77%nat K77. rtk RT 78%nat K78. rtk RT 79%nat K79. rtk RT 80%nat K80. rtk RT 81%nat K81. rtk RT 82%nat K82.
rtk RT 83%nat K83. rtk RT 84%nat K84. rtk RT 85%nat K85. rtk RT 86%nat K86. rtk RT 87%nat K87. rtk RT 88%nat K88. rtk RT 89%nat K89. rtk RT 90%nat K90. rtk RT 91%nat K91. rtk RT 92%nat K92. rtk RT 93%nat K93. rtk RT 94%nat K94.
rtk RT 95%nat K95. rtk RT 96%nat K96. rtk RT 97%nat K97. rtk RT 98%nat K98. rtk RT 99%nat K99. rtk RT 100%nat K100. rtk RT 101%nat K101.
pose proof (RT_rw _ _ _ RT 0%nat _ _ eq_refl) as W0. pose proof (RT_rw _ _ _ RT 1%nat _ _ eq_refl) as W1. cbn [fst snd] in W0, W1.

pose proof (proj1 (ro_cells_app asegs m 0x0e5da8 [C8 (wz 0x181628); C8 (wz 0x0ed2f8)] _) K19) as [K19a K19r].
pose proof (proj1 (ro_cells_app asegs m _ [C8 (wz 0x0efaf8)] _) K19r) as [_ K19b]. cbn [cells_size csize Nat.add Z.of_nat Z.add Pos.add Pos.of_succ_nat Pos.succ] in K19b.
lazymatch type of K19b with ro_cells _ _ ?a _ => let a' := eval vm_compute in a in change a with a' in K19b end.
pose proof (proj1 (ro_cells_app asegs m 0x0e5df0 [C8 (wz 0x0e7df8)] _) K20) as [K20a _].
pose proof (proj1 (ro_cells_app asegs m 0x0f07e0 [C8 (wz 0x7fffffffffff); C8 (wz 0); C8 (wz 0)] _) K1) as [K1a _].

assert (K0' : ro_cells asegs m 0x0f07d8 [C1 (b8 1); C1 (b8 1)]).
{ apply (proj2 (ro_cells_app asegs m 0x0f07d8 [C1 (b8 1)] [C1 (b8 1)])). split; [exact K0| exact K40]. }
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Section S.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRQ : ac_RQuar C = RQuar.
Hypothesis HRF : ac_RFake C = RFake.

Lemma ARUN_rt_consts : forall s LB FS RE m, ARUN C s LB FS RE m -> rt_consts_at asegs m.
Proof.
intros s LB FS RE m AR. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & _). rewrite HRT in R1. exact (RTconst_rt_consts RE X m R1).
Qed.

Lemma ARUN_errno : forall s LB FS RE m, ARUN C s LB FS RE m -> exists v : word, rw_cells asegs m 0x622dbc [C4 v].
Proof.
intros s LB FS RE m AR. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & R2 & _). rewrite HRS in R2. destruct R2 as (_ & [e ERR] & _). exists e. exact ERR.
Qed.

Lemma ARUN_errno_frame : forall s LB FS RE m m' (v : word),
ARUN C s LB FS RE m -> munch [(0x622dbc, 0x622dbc + 4)] m m' -> wmono asegs m m' ->
rw_cells asegs m' 0x622dbc [C4 v] -> ARUN C s LB FS RE m'.
Proof.
intros s LB FS RE m m' v AR MU WM ERR'. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
eapply ARUN_close; [exact PB| exact PF|].
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
assert (ES : forall x, 0x622dbc <= x < 0x622dbc + 4 -> fp_RStats RE X x) by (intros x Hx; right; left; unfold A_ERRNO; split; cbn [fst snd]; lia).
assert (AG : forall P : Z -> Prop, (forall x, P x -> fp_RStats RE X x -> False) -> agree_on asegs P m m').
{ intros P HP. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. cbn [outside]. split; [| exact I].
destruct (Z.lt_ge_cases x 0x622dbc); [lia|]. destruct (Z.lt_ge_cases x (0x622dbc + 4)); [| lia].
exfalso. exact (HP x Px (ES x ltac:(lia))). }
split; [exact GC|].
split; [eapply (ac_RTconst_frame C); [exact R1| exact WM| apply AG; intros x Px Sx; exact (fpS_excl _ _ _ _ _ _ GC x Sx ltac:(do 4 right; exact Px))]|].
split.
{ rewrite HRS in R2 |- *. destruct R2 as (HJ & _ & [b OOM]). split; [eapply hjunk_wmono; [exact HJ| exact WM]|]. split; [exists v; exact ERR'|].
exists b. eapply rw_cells_transport; [exact OOM| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
split; [eapply (ac_RPrim_frame C); [exact R3| exact WM| apply AG; intros x Px Sx; exact (fpP_RStats _ _ _ _ _ _ GC x Px Sx)]|].
split; [eapply (ac_RChunks_frame C); [exact R4| exact WM| apply AG; intros x Px Sx; exact (fpS_excl _ _ _ _ _ _ GC x Sx ltac:(left; exact Px))]|].
split; [eapply (ac_RSec_frame C); [exact R5| exact WM| apply AG; intros x Px Sx; exact (fpS_excl _ _ _ _ _ _ GC x Sx ltac:(right; left; exact Px))]|].
split; [eapply (ac_RQuar_frame C); [exact R6| exact WM| apply AG; intros x Px Sx; exact (fpQ_RStats _ _ _ _ _ _ GC x Px Sx)]|].
split; [eapply (ac_RDepot_frame C); [exact R7| exact WM| apply AG; intros x Px Sx; exact (fpS_excl _ _ _ _ _ _ GC x Sx ltac:(do 2 right; left; exact Px))]|].
eapply (ac_RFake_frame C); [exact R8| exact WM| apply AG; intros x Px Sx; exact (fpS_excl _ _ _ _ _ _ GC x Sx ltac:(do 3 right; left; exact Px))].
Qed.

Lemma ARUN_nbhd : forall s LB FS RE m p n, ARUN C s LB FS RE m -> amemset_whereA LB FS p n -> 0 < n ->
(exists w : word, rw_cells asegs m (8 * (SH p / 8)) [C8 w])
/\ (exists w : word, rw_cells asegs m (8 * (SH (p + n - 1) / 8)) [C8 w]).
Proof.
intros s LB FS RE m p n AR WH Hn. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & _ & R3 & R4 & _ & R6 & _ & R8). rewrite HRP in R3. rewrite HRC in R4. rewrite HRQ in R6. rewrite HRF in R8.
assert (WH0 : amemset_whereA LB0 FS0 p n).
{ destruct WH as [(q & A & n0 & Hin & H1 & H2)|(c & f & Hin & H1 & H2)].
- left. exists q, A, n0. split; [eapply Permutation_in; [exact PB| exact Hin]| split; assumption].
- right. exists c, f. split; [eapply Permutation_in; [exact PF| exact Hin]| split; assumption]. }
destruct (amemset_nbhd (ps_a s) LB0 FS0 G RE X m GC R3 R4 R6 R8 p n WH0 Hn) as [J1 J2].
split; [exact (hjunk_C8 _ _ J1)| exact (hjunk_C8 _ _ J2)].
Qed.
End S.
End Mq2.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW QwAs Qu3b QsGW Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import Qu3b.Mq3. Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import Qu3b.Mq1 QYyZ.Mq2.
Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition fwritex_entry := 0xd33c8%Z.
Definition FWRITEX_STACK : Z := (64 + MEMCPY_ICPT_STACK)%Z.

Definition FILE_cells (fl0 : byte) (j1 : list byte) (WEND WPOS : Z) (j2 : list byte) (lbfw : word) : list cell :=
[CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw].

Definition wfile (m : word -> option byte) (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word)
(B : Z) (content junk : list byte) : Prop :=
rw_cells asegs m Fp (FILE_cells fl0 j1 (B + Z.of_nat (length content) + Z.of_nat (length junk))
(B + Z.of_nat (length content)) j2 lbfw)
/\ rw_cells asegs m B [CB (length content) content; CB (length junk) junk]
/\ Z.land (bv_unsigned fl0) 32 = 0%Z
/\ (2147483648 <= bv_unsigned lbfw mod 4294967296)%Z
/\ (0 < B)%Z /\ (B + Z.of_nat (length content) + Z.of_nat (length junk) < 2^64)%Z
/\ (Fp + 148 <= B \/ B + Z.of_nat (length content) + Z.of_nat (length junk) <= Fp)%Z.

Definition fwritex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
(S : Z) (bs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
/\ bytes_at asegs m' S bs.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
intros segs m a n1 n2 H1 H2. unfold wr_at. split.
- intros (Ha & Hb & H). repeat split; try lia.
+ intros i Hi. apply H. lia.
+ intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
- intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
intros i Hi. destruct (Z.lt_ge_cases i n1).
+ apply HA. lia.
+ replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
rewrite wr_at_app by lia. rewrite bytes_at_app.
split.
- intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma sx32_neg : forall w : word, (2147483648 <= bv_unsigned w mod 4294967296)%Z ->
(9223372036854775808 <= bv_unsigned (sx32 w))%Z.
Proof.
intros w H. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq.
pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
change (2^64)%Z with 18446744073709551616%Z in *.
Z.div_mod_to_equations. lia.
Qed.

Ltac unwrap_in K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K; rewrite ?Z.mod_small in K by lia.

Lemma fwritex_spec {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte)
(fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte) (lo : Z),
wfile m (bv_unsigned a2) fl0 j1 j2 lbfw B content junk ->
bytes_at asegs m (bv_unsigned a0) bs ->
Z.of_nat (length bs) = bv_unsigned a1 ->
(length bs <= length junk)%nat ->
stk asegs m lo (bv_unsigned sp) ->
mem_inv asegs m ->
(band_lo <= lo)%Z -> (lo <= bv_unsigned sp - FWRITEX_STACK)%Z ->
(bv_unsigned a2 + 148 <= lo \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
(B + Z.of_nat (length content) + Z.of_nat (length junk) <= lo \/ bv_unsigned sp <= B)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= B + Z.of_nat (length content)
\/ B + Z.of_nat (length content) + Z.of_nat (length bs) <= bv_unsigned a0)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a2 \/ bv_unsigned a2 + 148 <= bv_unsigned a0)%Z ->
shadow_base asegs m -> rt_consts_at asegs m ->
rng_ok m (bv_unsigned a0) (Z.of_nat (length bs)) -> rng_ok m (B + Z.of_nat (length content)) (Z.of_nat (length bs)) ->
evt asegs (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(bv_unsigned a2) fl0 j1 j2 lbfw B content junk (bv_unsigned a0) bs lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd33c8) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb) SRC LEN LE ST MI CEIL LO SEP1 SEP2 SEP3 SEP4 SEP5 SB RC RS RD.
pose_word_ranges. pose proof CEIL as CEIL'. idtac. unfold FWRITEX_STACK, MEMCPY_ICPT_STACK in LO.
set (Fp := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
set (S := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 S) by (unfold S; rewrite Z_to_bv_bv_unsigned; reflexivity).
set (nc := length content) in *. set (nj := length junk) in *. set (lb := length bs) in *.
replace a1 with (Z_to_bv 64 (Z.of_nat lb)) by (rewrite LEN, Z_to_bv_bv_unsigned; reflexivity).
pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
pose proof (munch_refl [(lo, bv_unsigned sp); (B + Z.of_nat nc, B + Z.of_nat nc + Z.of_nat lb); (Fp + 40, Fp + 48)]%Z m) as MU.
pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUs.
pose proof (wmono_refl asegs m) as WM.
unfold FILE_cells in FC.
carve_frame 64%nat ST.
do 8 zstep.
zstep. zstep. zstep. zstep.
zstep. if_cases Kw; zify_cond Kw; unwrap_in Kw.
{ exfalso. lia. }
zstep. zstep.
zstep. if_cases Kr; zify_cond Kr; unwrap_in Kr.
2:{ exfalso. lia. }
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
2:{ exfalso. pose proof (sx32_neg lbfw LBF). lia. }
zstep. zstep.

apply (rw_cells_split_CB asegs _ _ [CB nc content] nj junk [] [lb; nj - lb]%nat) in BUF; [ | cbn; lia ].
cbn [mk_CB_cells app] in BUF.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUF].
cbn [cells_size csize Nat.add] in BUF. rewrite Nat.add_0_r in BUF.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFb BUFc].
cbn [cells_size csize] in BUFc. rewrite Nat.add_0_r in BUFc.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SB1;
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RC1;
assert (RS1 : rng_ok mc S (Z.of_nat lb))
by (eapply rng_ok_munch; [exact RS| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn; rewrite !SH_eq, ?KHI_eq in *;
left; pose proof (proj1 (proj2 RS)); Z.div_mod_to_equations; lia);
assert (RD1 : rng_ok mc (B + Z.of_nat nc) (Z.of_nat lb))
by (eapply rng_ok_munch; [exact RD| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn; rewrite !SH_eq, ?KHI_eq in *;
left; pose proof (proj1 (proj2 RD)); Z.div_mod_to_equations; lia)
end.
clear MUs.
zstep. call_u (memcpy_icpt_spec (B + Z.of_nat nc) S (Z.of_nat lb) lo bs (firstn lb junk));
[ exact SRC| rewrite Nat2Z.id; reflexivity| rewrite Nat2Z.id; exact BUFb| lia| assumption| lia
| unsigned_lits; eassumption| exact CEIL| unsigned_lits; unfold MEMCPY_ICPT_STACK; lia| unsigned_lits; lia| unsigned_lits; lia
| exact SB1| exact RC1| exact RS1| exact RD1|].
rewrite ?(unsigned_lit (B + Z.of_nat nc)), ?(unsigned_lit S), ?(unsigned_lit (Z.of_nat lb)) in * by lia.
rewrite !Nat2Z.id in *.
rewrite firstn_all2 in BUFc by (rewrite length_skipn; lia).
match goal with MC : rw_cells _ _ (B + Z.of_nat nc)%Z [CB lb bs] |- _ => rename MC into BUFb' end.
zstep. zstep. zstep. zstep.
replace (0 + Z.of_nat lb)%Z with (Z.of_nat lb) by lia.
replace (B + Z.of_nat nc + Z.of_nat lb)%Z with (B + Z.of_nat (length (content ++ bs)))%Z by (rewrite length_app; lia).
do 9 zstep.
match goal with STa : stk asegs ?mc lo (bv_unsigned sp + -64)%Z, FRx : rw_cells asegs ?mc (bv_unsigned sp + -64)%Z _ |- _ => release_frame FRx STa (bv_unsigned sp) end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (BUF : rw_cells asegs mm B ([] ++ [CB nc content; CB lb bs] ++ [CB (nj - lb)%nat (skipn lb junk)]));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [ eassumption |];
cbn [cells_size csize]; rewrite Nat.add_0_r;
apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [ exact BUFb' |];
cbn [cells_size csize]; rewrite Nat.add_0_r; eassumption
| apply rw_cells_merge in BUF; cbn [cells_size cells_bytes csize cbytes app Nat.add] in BUF;
rewrite Nat.add_0_r, app_nil_r in BUF ]
end.
apply evt_done. unfold fwritex_post.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [ ms_eq | ].
split. { replace (B + Z.of_nat (length (content ++ bs)))%Z with (B + Z.of_nat nc + Z.of_nat lb)%Z by (rewrite length_app; lia). assumption. }
repeat match goal with |- _ /\ _ => split end; try assumption.

unfold wfile, FILE_cells. rewrite !length_app, !length_skipn. fold nc lb nj.
rewrite !Nat2Z.inj_add, !Nat2Z.inj_sub by lia.
replace (B + (Z.of_nat nc + Z.of_nat lb) + (Z.of_nat nj - Z.of_nat lb))%Z with (B + Z.of_nat nc + Z.of_nat nj)%Z by lia.
match goal with FCx : rw_cells asegs _ Fp _ |- _ =>
replace (B + Z.of_nat nc + Z.of_nat lb)%Z with (B + (Z.of_nat nc + Z.of_nat lb))%Z in FCx by lia;
split; [exact FCx|] end.
split; [exact BUF|]. split; [exact FL|]. split; [exact LBF|]. split; [lia|]. split; lia.
Qed.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC QoNr QFd5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do.
Import QCiC.Mq1. Import QoNr. Import Q6sh QKTr.
Import Qu3b.Mq3. Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QTVW.Mq1 QFd5.Mq0 Qu3b.Mq1.
Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Definition got_ssp := 0xe6b80%Z.
Definition ssp_guard := 0x642ea0%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].

Definition pad_n (w l fl : Z) : Z :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z || (w <=? l)%Z then 0 else w - l.

Lemma pad_model : forall o c w l fl, (w - l < 256)%Z ->
pad o c w l fl = Some (o ++ zrepeat c (pad_n w l fl)).
Proof.
intros o c w l fl H. unfold pad, pad_n.
destruct (negb _ || _); [cbn; now rewrite app_nil_r|].
change PAD_FUEL with (S 63). cbn [pad_loop].
destruct (Z.leb_spec0 256 (w - l)); [lia|]. reflexivity.
Qed.

Ltac hyp := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.

Definition memset_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D C N lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(D, D + N); (lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q
/\ rw_cells asegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
Lemma memset_callZ {BAND : Band} : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q D C N lo : Z) (junk : list byte),
rw_cells asegs m D [CB (Z.to_nat N) junk] ->
mem_inv asegs m ->
(0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z -> (0 <= C < 256)%Z -> (0 <= N < 2^64)%Z ->
stk asegs m lo q -> band_lo <= lo -> lo <= q - MEMSET_ICPT_STACK -> (D + N <= lo \/ q <= D) ->
shadow_base asegs m -> rt_consts_at asegs m -> rng_ok m D N ->
evt asegs (memset_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N lo m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61738) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros DST MI Hq HD HC HN ST CEIL LO SEP SB RC RNG.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (memset_icpt_spec D C N lo junk ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
intros ms' P. unfold memset_icpt_post in P. unfold memset_postZ. rewrite !Eq in P. rewrite (Z.mod_small C 256) by lia. exact P.
Qed.

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr QvDJ.Mq3.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QTVW.Mq2 QYyZ.Mq1.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition strnlen_entry := 0xdbd10%Z.
Definition STRNLEN_STACK : Z := 32 + MEMCHR_ICPT_STACK.

Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
(wz (strnlen_res n buf))
a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ bytes_at asegs m' A buf.

Lemma strnlen_spec {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 (a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : word -> option byte) (A n : Z) (buf : list byte) (lo : Z),
stk asegs m lo (bv_unsigned sp) ->
bytes_at asegs m A buf ->
memchr_ok A 0 n buf ->
mem_inv asegs m ->
band_lo <= lo -> lo <= bv_unsigned sp - STRNLEN_STACK ->
A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A ->
0 < A -> 0 <= n < 2^64 ->
shadow_base asegs m -> rt_consts_at asegs m ->
rng_ok m A (memchr_len 0 n buf) ->
evt asegs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz strnlen_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST BUF OK MI CEIL LO SEP A0 N0 SB RC RNG.
pose proof CEIL as CEIL'. idtac. unfold STRNLEN_STACK, MEMCHR_ICPT_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
unfold strnlen_entry.
carve_frame 32%nat ST.
do 8 istep.
pose proof (shadow_base_munch _ _ _ SB MU ltac:(rt_wzones)) as SB1.
pose proof (rt_consts_at_munch _ _ _ RC MU WM ltac:(rt_wzones)) as RC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RNG1 : rng_ok mc A (memchr_len 0 n buf))
by (eapply rng_ok_munch; [exact RNG| exact MU| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn; rewrite !SH_eq, ?KHI_eq in *;
left; pose proof (proj1 (proj2 RNG)); Z.div_mod_to_equations; lia) end.
step. call_u (memchr_icpt_spec A n lo buf (wz 0));
[ eassumption| change (bv_unsigned (wz 0) mod 256) with 0; exact OK| assumption| lia| lia| unsigned_lits; eassumption| exact CEIL
| unsigned_lits; unfold MEMCHR_ICPT_STACK; lia| unsigned_lits; lia| exact SB1| exact RC1| change (bv_unsigned (wz 0) mod 256) with 0; exact RNG1|].
change (bv_unsigned (wz 0) mod 256) with 0 in *. change (0 mod 256) with 0 in *.
unfold memchr_res.
destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:FB.
- pose proof (find_byte_lt _ _ _ FB) as Hl. rewrite length_firstn in Hl.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; lia|].
stp. rewrite ?(unsigned_lit (A + Z.of_nat i)), ?(unsigned_lit A) by lia.
replace (A + Z.of_nat i + - A)%Z with (strnlen_res n buf) by (unfold strnlen_res; rewrite FB; lia).
do 4 step.
match goal with FRx : rw_cells asegs ?mc (bv_unsigned sp + -32) _, STx : stk asegs ?mc lo _ |- _ => release_frame FRx STx (bv_unsigned sp) end.
step. step.
apply evt_done. unfold strnlen_post. do 15 eexists. split; [reflexivity|].
repeat match goal with |- _ /\ _ => split; [eassumption|] end; eassumption.
- step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
step.
lazymatch goal with |- evt _ ?Q _ => set (PP := Q) end.
replace (wz n) with (wz (strnlen_res n buf)) by (unfold strnlen_res; rewrite FB; reflexivity).
subst PP.
do 3 step.
match goal with FRx : rw_cells asegs ?mc (bv_unsigned sp + -32) _, STx : stk asegs ?mc lo _ |- _ => release_frame FRx STx (bv_unsigned sp) end.
step. step.
apply evt_done. unfold strnlen_post. do 15 eexists. split; [reflexivity|].
repeat match goal with |- _ /\ _ => split; [eassumption|] end; eassumption.
Qed.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QNwL QYnC QSsj QYyZ.Mq5 QqLk.
Import QlES.
Import ListNotations. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Section S.
Context {BAND : Band}.

Lemma depot_keep_of_pzone : forall a LB0 FS0 G RE X (m m' : word -> option byte) W,
gcons a LB0 FS0 G RE X -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> pzone a LB0 G RE X x) -> depot_keep asegs m m'.
Proof.
intros a LB0 FS0 G RE X m m' W GC MU WM HW n [RC P]. split; [| exact P].
eapply (rw_cells_agree asegs (fun x => ~ pzone a LB0 G RE X x)); [| exact RC|].
- eapply agree_on_of_munch; [exact MU| exact WM|]. intros x NZ _. apply outside_intro. intros lo hi Hin Hx. exact (NZ (HW lo hi x Hin Hx)).
- intros y Hy. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hy. unfold DP_N in Hy.
assert (FD : fp_RDepot RE X y) by (left; unfold in_iv; cbn [fst snd]; lia).
intros [FQ|[FP|[FS|BL]]].
+ exact (fpQ_RDepot a LB0 FS0 G RE X GC y FQ FD).
+ exact (fpP_RDepot a LB0 FS0 G RE X GC y FP FD).
+ exact (fpS_excl a LB0 FS0 G RE X GC y FS (or_intror (or_intror (or_introl FD)))).
+ lia.
Qed.

Definition ezone (a : AState) (LB0 : list ablock) (G : ghost) (RE : aentry) (X : rlay) (x : Z) : Prop :=
fp_RQuar a LB0 G RE X x \/ fp_RPrim G RE X x \/ in_iv (rl_T X + 2800, 368) x \/ x = 0x171d60 \/ fp_RDepot RE X x \/ band_lo <= x.

Lemma errno_keep_of_ezone : forall a LB0 FS0 G RE X (m m' : word -> option byte) W,
gcons a LB0 FS0 G RE X -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> ezone a LB0 G RE X x) -> errno_keep asegs m m'.
Proof.
intros a LB0 FS0 G RE X m m' W GC MU WM HW. unfold errno_keep.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros y Hy _. apply outside_intro. intros lo hi Hin Hx.
assert (FS : fp_RStats RE X y) by (right; left; unfold in_iv, A_ERRNO; cbn [fst snd]; lia).
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & TC & _). cbn [fst snd] in TK, TC.
destruct (HW lo hi y Hin Hx) as [Z|[Z|[Z|[Z|[Z|Z]]]]].
- exact (fpQ_RStats a LB0 FS0 G RE X GC y Z FS).
- exact (fpP_RStats a LB0 FS0 G RE X GC y Z FS).
- unfold in_iv in Z. cbn [fst snd] in Z. lia.
- lia.
- exact (fpS_excl a LB0 FS0 G RE X GC y FS (or_intror (or_intror (or_introl Z)))).
- lia.
Qed.

Lemma ezone_of_qzone : forall a LB0 G RE X x, qzone a LB0 G RE X x -> ezone a LB0 G RE X x.
Proof. intros a LB0 G RE X x [H|H]; unfold ezone; [left; exact H| do 5 right; exact H]. Qed.

Definition free_step (m m' : word -> option byte) : Prop := depot_step m m' /\ errno_keep asegs m m'.
End S.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QpY2.Mq1 QYyZ.Mq4 QmP7.Mq0 Q9Ho.Mq1.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition ri_cellsL (v : Z) (x : cstate) (j1 j2 j3 j4 : list byte) : list cell :=
[ C8 (wz v); CB 8 j1; C8 (wz (c_num_freed x)); C8 (wz (c_mapped_fa x)); C8 (wz (c_alloc_user x)); C8 (wz 0);
C8 (wz (c_mapped_user x)); C8 (wz 0); CB 4 j2; C1 (b8 0); CB 3 j3; CB 56 j4 ].
Definition ri_tail (x : cstate) (j1 j2 j3 j4 : list byte) : list cell :=
[ CB 8 j1; C8 (wz (c_num_freed x)); C8 (wz (c_mapped_fa x)); C8 (wz (c_alloc_user x)); C8 (wz 0);
C8 (wz (c_mapped_user x)); C8 (wz 0); CB 4 j2; C1 (b8 0); CB 3 j3; CB 56 j4 ].

Lemma ri_cellsL_split : forall m A v x j1 j2 j3 j4,
rw_cells asegs m A (ri_cellsL v x j1 j2 j3 j4) <-> rw_cells asegs m A [C8 (wz v)] /\ rw_cells asegs m (A + 8) (ri_tail x j1 j2 j3 j4).
Proof. intros. apply (rw_cells_app asegs m A [C8 (wz v)]). Qed.

Section PerClass.
Variables (a : AState) (G : ghost) (RE : aentry) (X : rlay) (m : mem) (c : Z) (K : pcls) (v : Z).
Definition cr_cellsL : Prop :=
(exists j1 j2 j3 j4, rw_cells asegs m (ri_addr RE c) (ri_cellsL v (cls a c) j1 j2 j3 j4))
/\ rw_cells asegs m (pc_addr X c) (pc_cells (as_cache_inited a) c (cls a c))
/\ (exists CH, u32arr asegs m (pc_addr X c + 16) CH /\ length CH = 16%nat
/\ forall j, (j < length (pk_ca K))%nat -> nth_error CH j = Some (wz (coff c (nth j (pk_ca K) 0)))).
Definition class_repL : Prop := cr_cellsL /\ cr_pure a G c K /\ cr_region a G RE m c K.
End PerClass.

Definition RPrimL (a : AState) (G : ghost) (RE : aentry) (X : rlay) (m : mem) (cl v : Z) : Prop :=
exists K : Z -> pcls,
hjunk m (rl_T X + 2768) (rl_T X + 2800)
/\ (forall c, G c <> [] -> 1 <= c < kNumClasses)
/\ (forall c, 0 <= c < kNumClasses -> c <> cl -> class_rep a G RE X m c (K c))
/\ 0 <= cl < kNumClasses /\ class_repL a G RE X m cl (K cl) v.

Lemma class_repL_0 : forall a G RE X m c K, class_rep a G RE X m c K <-> class_repL a G RE X m c K 0.
Proof.
intros. split; intros (((j1 & j2 & j3 & j4 & RI) & PC & CHH) & B & C); (split; [| split; [exact B| exact C]]);
(split; [exists j1, j2, j3, j4; exact RI| split; [exact PC| exact CHH]]).
Qed.

Lemma RPrimL_un0 : forall a G RE X m cl, RPrimL a G RE X m cl 0 -> RPrim a G RE X m.
Proof.
intros a G RE X m cl (K & HJ & GNE & HC & Hcl & HCL). exists K. split; [exact HJ|]. split; [exact GNE|].
intros c Hc. destruct (Z.eq_dec c cl) as [->|NE]; [apply class_repL_0; exact HCL| exact (HC c Hc NE)].
Qed.

Lemma class_repL_split : forall a G RE X m c K v,
class_repL a G RE X m c K v <->
cr_cellsL a RE X m c K v /\ cr_pure a G c K /\
(1 <= c -> u32arr asegs m (fa_beg (ae_L RE) c) (map (fun i => Z_to_bv 64 (coff c i)) (pk_fl K))
/\ hjunk m (fa_beg (ae_L RE) c + 4 * c_num_freed (cls a c)) (fa_beg (ae_L RE) c + c_mapped_fa (cls a c))
/\ cr_user a G RE m c
/\ hjunk m (SH (fa_beg (ae_L RE) c)) (SH (fa_beg (ae_L RE) c + kFreeArraySize))).
Proof.
intros a G RE X m c K v. unfold class_repL, cr_region, cr_user. split.
- intros (A & B & C). split; [exact A|]. split; [exact B|]. intros Hc. specialize (C Hc). tauto.
- intros (A & B & C). split; [exact A|]. split; [exact B|]. intros Hc. specialize (C Hc). tauto.
Qed.

Lemma class_repL_ext : forall a a' G G' RE X m c K v,
class_repL a G RE X m c K v -> cls a' c = cls a c -> as_cache_inited a' = as_cache_inited a -> G' c = G c ->
class_repL a' G' RE X m c K v.
Proof.
intros a a' G G' RE X m c K v HC EC EI EG.
assert (TG : forall i, tag_at G' c i = tag_at G c i) by (intros i; unfold tag_at; rewrite EG; reflexivity).
unfold class_repL, cr_cellsL, cr_pure, cr_region in *. rewrite EC, EI, EG. setoid_rewrite TG. exact HC.
Qed.

Lemma RPrimL_open : forall a G RE X m cl v, RPrimL a G RE X m cl v ->
exists K : Z -> pcls, hjunk m (rl_T X + 2768) (rl_T X + 2800)
/\ (forall c, G c <> [] -> 1 <= c < kNumClasses)
/\ (forall c, 0 <= c < kNumClasses -> c <> cl -> class_rep a G RE X m c (K c))
/\ 0 <= cl < kNumClasses /\ class_repL a G RE X m cl (K cl) v.
Proof. intros a G RE X m cl v H. exact H. Qed.

Section ClassFrameL.
Context {BAND : Band}.
Variables (a : AState) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis RL : rlay_ok RE X.

Lemma class_repL_agree_but_mutex : forall m m' c K v w,
class_repL a G RE X m c K v -> 0 <= c < 32 ->
agree_on asegs (fun z => fp_cls RE X c z /\ ~ (ri_addr RE c <= z < ri_addr RE c + 8)) m m' ->
rw_cells asegs m' (ri_addr RE c) [C8 (Z_to_bv 64 w)] ->
class_repL a G RE X m' c K w.
Proof.
intros m m' c K v w HC Hc AG HEAD. pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof HC as (((j1 & j2 & j3 & j4 & RI) & PC & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
pose proof (reg_geom RE X RL c Hc) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
assert (NRI_lo : forall z, z < prim_lo RE + 137438953472 -> ~ (ri_addr RE c <= z < ri_addr RE c + 8)) by (intros z Hz; unfold ri_addr; lia).
assert (INFA : forall z, fa_beg (ae_L RE) c <= z < fa_beg (ae_L RE) c + kFreeArraySize ->
fp_cls RE X c z /\ ~ (ri_addr RE c <= z < ri_addr RE c + 8)).
{ intros z Hz. split; [do 2 right; left; exact Hz| apply NRI_lo; rewrite FB, KS in Hz; clear - Hz Hc; lia]. }
assert (INFS : forall z, SH (fa_beg (ae_L RE) c) <= z < SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8 ->
fp_cls RE X c z /\ ~ (ri_addr RE c <= z < ri_addr RE c + 8)).
{ intros z Hz. split; [do 3 right; left; split; cbn [fst snd]; lia| apply NRI_lo].
rewrite FB, KS in Hz. unfold SH, A_SHADOW_OFS in Hz. clear - Hz Hc PK. Z.div_mod_to_equations. lia. }
assert (INUZ : forall z, uzone RE c z -> fp_cls RE X c z /\ ~ (ri_addr RE c <= z < ri_addr RE c + 8)).
{ intros z [Hz|Hz].
- split; [do 4 right; left; exact Hz| apply NRI_lo; rewrite RB, KO in Hz; clear - Hz Hc; lia].
- split; [do 5 right; exact Hz| apply NRI_lo]. unfold in_sh in Hz. cbn [fst snd] in Hz.
rewrite RB, KO in Hz. unfold SH, A_SHADOW_OFS in Hz. clear - Hz Hc PK. Z.div_mod_to_equations. lia. }
assert (INPC : forall z, pc_addr X c <= z < pc_addr X c + 80 -> fp_cls RE X c z /\ ~ (ri_addr RE c <= z < ri_addr RE c + 8)).
{ intros z Hz. split; [right; left; exact Hz|]. unfold pc_addr in Hz. unfold ri_addr. rewrite RIq. clear - Hz TD Hc TB PK. lia. }
pose proof (agree_on_mono _ _ (uzone RE c) m m' AG INUZ) as AGU.
split; [split; [|split]| split; [exact PU|]].
- exists j1, j2, j3, j4. apply ri_cellsL_split. apply ri_cellsL_split in RI as [_ TL]. split; [exact HEAD|].
eapply rw_cells_agree; [exact AG| exact TL|]. intros z Hz. cbn [ri_tail cells_size csize Nat.add] in Hz.
split; [left; lia| lia].
- eapply rw_cells_agree; [exact AG| exact PC|]. intros z Hz. apply INPC. cbn [pc_cells cells_size csize Nat.add] in Hz. lia.
- exists CH. split; [| split; [exact LCH| exact HCH]]. eapply u32arr_agree; [exact AG| exact ACH|]. intros z Hz. apply INPC. rewrite LCH in Hz. cbn in Hz. lia.
- intros Hc1. specialize (REG Hc1). destruct REG as (FA & FJ & SL & UT & SS & US & UJ & FS).
assert (HU : cr_user a G RE m' c) by (eapply cr_user_agree; [exact PU| split; [exact SL| split; [exact UT| split; [exact SS| split; [exact US| exact UJ]]]]| lia| exact AGU]).
destruct HU as (SL' & UT' & SS' & US' & UJ').
assert (KS8 : kFreeArraySize = 8 * 67108864) by (rewrite KS; reflexivity).
split; [| split; [| split; [exact SL'| split; [exact UT'| split; [exact SS'| split; [exact US'| split; [exact UJ'|]]]]]]].
+ eapply u32arr_agree; [exact AG| exact FA|]. intros z Hz. rewrite length_map in Hz. apply INFA. lia.
+ eapply hjunk_agree; [exact AG| exact FJ|]. intros z Hz. apply INFA. lia.
+ eapply hjunk_agree; [exact AG| exact FS|]. intros z Hz. rewrite KS8, SH_plus8 in Hz. apply INFS. rewrite KS8, Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma class_repL_agree : forall m m' c K v,
class_repL a G RE X m c K v -> 0 <= c < 32 -> agree_on asegs (fp_cls RE X c) m m' -> class_repL a G RE X m' c K v.
Proof.
intros m m' c K v HC Hc AG. eapply class_repL_agree_but_mutex; [exact HC| exact Hc| |].
- eapply agree_on_mono; [exact AG|]. intros z [Hz _]. exact Hz.
- destruct HC as (((j1 & j2 & j3 & j4 & RI) & _) & _). apply ri_cellsL_split in RI as [HD _].
eapply rw_cells_agree; [exact AG| exact HD|]. intros z Hz. left. cbn [cells_size csize Nat.add] in Hz. lia.
Qed.
End ClassFrameL.

Lemma RPrimL_reclose {BAND : Band} : forall a a' G G' RE X m m' c (K : Z -> pcls) (Kc : pcls) w,
rlay_ok RE X ->
hjunk m (rl_T X + 2768) (rl_T X + 2800) ->
(forall c0, G c0 <> [] -> 1 <= c0 < kNumClasses) ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> class_rep a G RE X m c0 (K c0)) ->
0 <= c < kNumClasses ->
(forall c0, c0 <> c -> cls a' c0 = cls a c0) -> as_cache_inited a' = as_cache_inited a ->
(forall c0, c0 <> c -> G' c0 = G c0) -> (G' c <> [] -> 1 <= c) ->
wmono asegs m m' ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> agree_on asegs (fp_cls RE X c0) m m') ->
class_repL a' G' RE X m' c Kc w ->
RPrimL a' G' RE X m' c w.
Proof.
intros a a' G G' RE X m m' c K Kc w RL HJ GNE HCall Hc EC EI EG GC WM AGS HCc.
pose proof kconsts as (_ & _ & _ & K32 & _). rewrite K32 in *.
exists (fun c0 => if c0 =? c then Kc else K c0). split; [eapply hjunk_wmono; [exact HJ| exact WM]|]. split.
- intros c0 Hne. destruct (Z.eq_dec c0 c) as [->|NE]; [split; [apply GC; exact Hne| lia]|].
rewrite (EG c0 NE) in Hne. exact (GNE c0 Hne).
- split; [| split; [lia| rewrite Z.eqb_refl; exact HCc]].
intros c0 Hc0 NE. destruct (Z.eqb_spec c0 c) as [->|_]; [lia|].
eapply class_rep_ext; [| apply EC; exact NE| exact EI| apply EG; exact NE].
eapply class_rep_agree; [apply HCall; [exact Hc0| exact NE]| exact Hc0| apply AGS; [exact Hc0| exact NE]].
Qed.

Lemma RPrimL_stack {BAND : Band} : forall a G RE X m m' W cl v,
RPrimL a G RE X m cl v -> rlay_ok RE X -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => band_lo <= fst iv) W -> RPrimL a G RE X m' cl v.
Proof.
intros a G RE X m m' W cl v (K & HJ & GNE & HC & Hcl & HCL) RL MU WM FW.
pose proof kconsts as (_ & _ & _ & K32 & _).
assert (AGc : forall c0, 0 <= c0 < 32 -> agree_on asegs (fp_cls RE X c0) m m').
{ intros c0 Hc0. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as C. cbn [fst] in C.
pose proof (fp_cls_lt_ceil RE X RL c0 x Hc0 Fx). lia. }
exists K. split; [eapply hjunk_wmono; [exact HJ| exact WM]|].
split; [exact GNE|]. split.
- intros c0 Hc0 NE. eapply class_rep_agree; [exact (HC c0 Hc0 NE)| rewrite K32 in Hc0; exact Hc0| apply AGc; rewrite K32 in Hc0; exact Hc0].
- split; [exact Hcl|]. eapply class_repL_agree; [exact RL| exact HCL| rewrite K32 in Hcl; exact Hcl| apply AGc; rewrite K32 in Hcl; exact Hcl].
Qed.

Lemma RPrimL_gappend_nil : forall a G RE X m c cl v, RPrimL a G RE X m cl v -> RPrimL a (gappend c [] G) RE X m cl v.
Proof.
intros a G RE X m c cl v (K & HJ & GNE & HC & Hcl & HCL).
assert (EG : forall c0, gappend c [] G c0 = G c0).
{ intros c0. unfold gappend. destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite gset_eq, app_nil_r| rewrite gset_ne by exact NE]; reflexivity. }
exists K. split; [exact HJ|]. split; [intros c0 Hc0; apply GNE; rewrite <- EG; exact Hc0|]. split.
- intros c0 Hc0 NE. eapply class_rep_ext; [exact (HC c0 Hc0 NE)| reflexivity| reflexivity| apply EG].
- split; [exact Hcl|]. eapply class_repL_ext; [exact HCL| reflexivity| reflexivity| apply EG].
Qed.

Lemma RPrimL_mutex : forall a G RE X m cl v, RPrimL a G RE X m cl v -> rw_cells asegs m (ri_addr RE cl) [C8 (Z_to_bv 64 v)].
Proof.
intros a G RE X m cl v (K & _ & _ & _ & _ & (((j1 & j2 & j3 & j4 & RI) & _) & _)). apply ri_cellsL_split in RI as [HD _]. exact HD.
Qed.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I QJFf Qpj5 Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig Qc6I QJFf.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QpY2.Mq1 Q9Ho.Mq1 QmP7.Mq0 QYyZ.Mq0.
Import QUnM.
Import QYyZ.Mq5.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation b8 := (Z_to_bv 8).

Definition rq_keep (G : ghost) (RE : aentry) (JG : list Z) (Qs : list aptr) (x : Z) : Prop :=
(GQ <= x < GQ + 32) \/ (QMUT <= x < QMUT + 4) \/ (IA <= x < 0x171d38) \/ (IA_FLAG <= x < IA_FLAG + 4)
\/ (exists j, In j JG /\ (in_iv (slot_beg RE 24 j, class_size 24) x \/ in_sh (slot_beg RE 24 j, class_size 24) x))
\/ (exists id n i, In (APrim id n) Qs /\ tag_at G (class_of n) i = Some (TQuar (APrim id n))
/\ (in_iv (slot_beg RE (class_of n) i, class_size (class_of n)) x \/ in_sh (slot_beg RE (class_of n) i, class_size (class_of n)) x))
\/ (exists mb n, In (ASec mb n) Qs
/\ (mb + kPage <= x < mb + sec_map_size n \/ in_sh (mb + kPage, sec_map_size n - kPage) x)).

Section Keep.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Variables (QA : aptr -> Z) (JG : list Z) (Qs : list aptr).
Hypothesis FJG : Forall (fun j => tag_at G 24 j = Some TQOwn) JG.

Variable m0 : mem.
Hypothesis REP0 : forall q, In q Qs -> qptr_rep a LB0 G RE m0 QA q.

Local Notation KEEP := (rq_keep G RE JG Qs).

Lemma rq_transport : forall (m m' : mem) gq rb,
agree_on asegs KEEP m m' ->
qrep RE G m QA GQ gq JG -> rw_cells asegs m QMUT [C1 (b8 0); C1 (b8 rb); C1 (b8 0); C1 (b8 0)] -> ia_inv m ->
(forall q, In q Qs -> qptr_rep a LB0 G RE m QA q) ->
qrep RE G m' QA GQ gq JG /\ rw_cells asegs m' QMUT [C1 (b8 0); C1 (b8 rb); C1 (b8 0); C1 (b8 0)] /\ ia_inv m'
/\ (forall q, In q Qs -> qptr_rep a LB0 G RE m' QA q).
Proof.
intros m m' gq rb AG GQR HM HI REP. split; [| split; [| split]].
- eapply qrep_agree; [exact AG| exact GQR| | |].
+ intros x Hx. left. exact Hx.
+ intros j x Hj Hx. do 4 right; left. exists j. auto.
+ intros j x Hj Hx. do 4 right; left. exists j. auto.
- eapply rw_cells_agree; [exact AG| exact HM|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. lia.
- eapply ia_inv_agree; [exact AG| exact HI|]. intros x [Hx|Hx]; [do 2 right; left; exact Hx| do 3 right; left; exact Hx].
- intros q Hq. pose proof (REP q Hq) as R. destruct q as [id n|mb n]; cbn [qptr_rep] in R |- *.
+ destruct R as (i & Ht & Hpr & HQA & QM). exists i. split; [exact Ht|]. split; [exact Hpr|]. split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => in_iv (slot_beg RE (class_of n) i, class_size (class_of n)) x \/ in_sh (slot_beg RE (class_of n) i, class_size (class_of n)) x));
[| exact QM| |].
* eapply agree_on_mono; [exact AG|]. intros x Hx. do 5 right; left. exists id, n, i. auto.
* intros x Hx. left. split; cbn [fst snd]; lia.
* intros x Hx. right. split; cbn [fst snd]; [lia|].
replace (slot_beg RE (class_of n) i + class_size (class_of n) - slot_beg RE (class_of n) i) with (class_size (class_of n)) in Hx by lia. lia.
+ destruct R as (Hin & Hnl & Hpr & HQA & QM). split; [exact Hin|]. split; [exact Hnl|]. split; [exact Hpr|]. split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => mb + kPage <= x < mb + sec_map_size n \/ in_sh (mb + kPage, sec_map_size n - kPage) x)); [| exact QM| |].
* eapply agree_on_mono; [exact AG|]. intros x Hx. do 6 right. exists mb, n. auto.
* intros x Hx. left. exact Hx.
* intros x Hx. right. split; cbn [fst snd]; [lia|].
replace (mb + sec_map_size n - (mb + kPage)) with (sec_map_size n - kPage) in Hx by lia. lia.
Qed.

Lemma rq_keep_fp : forall x, KEEP x -> fp_RQuar a LB0 G RE X x.
Proof.
intros x [H|[H|[H|[H|[H|[H|H]]]]]]; unfold GQ, QMUT, IA, IA_FLAG in *.
- right; right; left. split; cbn [fst snd]; lia.
- right; right; left. split; cbn [fst snd]; lia.
- do 3 right; left. split; cbn [fst snd]; lia.
- do 4 right; left. split; cbn [fst snd]; lia.
- destruct H as (j & Hj & [Hx|Hx]); pose proof (proj1 (List.Forall_forall _ _) FJG j Hj) as Tj.
+ do 5 right; left. exists 24, j, TQOwn. auto.
+ do 6 right; left. exists 24, j, TQOwn. auto.
- destruct H as (id & n & i & Hq & Ht & [Hx|Hx]).
+ do 5 right; left. exists (class_of n), i, (TQuar (APrim id n)). auto.
+ do 6 right; left. exists (class_of n), i, (TQuar (APrim id n)). auto.
- destruct H as (mb & n & Hq & Hx). pose proof (REP0 _ Hq) as (Hin & Hnl & _). destruct Hx as [Hx|Hx].
+ do 7 right; left. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req]. auto.
+ do 8 right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req]. auto.
Qed.

Lemma keep_pzoneP : forall x, (fp_RPrim G RE X x \/ fp_RStats RE X x \/ band_lo <= x) -> KEEP x -> False.
Proof.
intros x [F|[F|F]] K; pose proof (rq_keep_fp x K) as Q.
- exact (fpQ_RPrim a LB0 FS0 G RE X GC x Q F).
- exact (fpQ_RStats a LB0 FS0 G RE X GC x Q F).
- pose proof (fp_RQuar_cz a LB0 FS0 G RE X GC x Q ltac:(left; exact F)). exact H.
Qed.

Lemma keep_TQ : forall x, rl_T X + 80 <= x < rl_T X + 208 -> KEEP x -> False.
Proof.
intros x Hx K. pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & TC & TP & _). cbn [fst snd] in TK, TC, TP.
unfold iv_disjoint in TP; cbn [fst snd] in TP. rewrite ?KHI_eq in TK. pose proof SH_band as SHB0. pose proof kconsts as (_ & _ & _ & _ & KP & _).
destruct K as [H|[H|[H|[H|[H|[H|H]]]]]]; unfold GQ, QMUT, IA, IA_FLAG, A_INSTANCE in *; try lia.
- destruct H as (j & Hj & [Hj2|Hj2]); pose proof (proj1 (List.Forall_forall _ _) FJG j Hj) as Tj.
+ pose proof (slot_prim a LB0 FS0 G RE X GC 24 j TQOwn Tj) as (P1 & P2 & _). unfold prim_hi, prim_lo in *. destruct Hj2; cbn [fst snd] in *. lia.
+ pose proof (slot_band a LB0 FS0 G RE X GC 24 j TQOwn x Tj Hj2). lia.
- destruct H as (id & n & i & Hq & Ht & [H2|H2]).
+ pose proof (slot_prim a LB0 FS0 G RE X GC _ _ _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in *. destruct H2; cbn [fst snd] in *. lia.
+ pose proof (slot_band a LB0 FS0 G RE X GC _ _ _ x Ht H2). lia.
- destruct H as (mb & n & Hq & H2). pose proof (REP0 _ Hq) as (Hin & _ & Hpr & _).
pose proof (sec_facts a LB0 FS0 G RE X GC _ Hin) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
pose proof (sec_map_size_ge n ltac:(lia) Hpr) as [M1 M2].
destruct H2 as [H2|H2].
+ pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D. lia.
+ pose proof (sec_band a LB0 FS0 G RE X GC (mkSec mb (sec_map_size n) n) x Hin). cbn [se_beg se_size] in H. specialize (H H2). lia.
Qed.

Lemma keep_slot : forall c i t x, tag_at G c i = Some t ->
(c = 24 -> In i JG -> False) -> (forall id n, t = TQuar (APrim id n) -> In (APrim id n) Qs -> False) ->
(in_iv (slot_beg RE c i, class_size c) x \/ in_sh (slot_beg RE c i, class_size c) x) -> KEEP x -> False.
Proof.
intros c i t x Ht NJ NQ Hx K. pose proof kconsts as (_ & _ & _ & _ & KP & _). pose proof SH_band as SHB0.
pose proof (slot_prim a LB0 FS0 G RE X GC c i t Ht) as (P1 & P2 & P3 & _ & _ & _ & _ & SZ & _).
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in *. rewrite ?KHI_eq in PK. idtac.
assert (XB : (al_space_beg (ae_L RE) <= x < al_space_beg (ae_L RE) + 2^37 + 4096) \/ (0x2008fff7000 <= x < SH band_lo)).
{ destruct Hx as [Hx|Hx]; [left; destruct Hx; cbn [fst snd] in *; lia| right; exact (slot_band a LB0 FS0 G RE X GC c i t x Ht Hx)]. }

assert (OTHER : forall c' i' t', tag_at G c' i' = Some t' -> (c <> c' \/ i <> i') ->
(in_iv (slot_beg RE c' i', class_size c') x \/ in_sh (slot_beg RE c' i', class_size c') x) -> False).
{ intros c' i' t' Ht' NE Hx'. pose proof (slots_disjoint a LB0 FS0 G RE X GC c i t c' i' t' Ht Ht' NE) as D.
pose proof (slot_prim a LB0 FS0 G RE X GC c' i' t' Ht') as (P1' & P2' & P3' & _ & _ & _ & _ & SZ' & _). unfold prim_hi, prim_lo in *.
destruct Hx as [Hx|Hx], Hx' as [Hx'|Hx'].
- destruct Hx, Hx'; cbn [fst snd] in *. lia.
- pose proof (slot_band a LB0 FS0 G RE X GC c' i' t' x Ht' Hx'). destruct Hx; cbn [fst snd] in *. lia.
- pose proof (slot_band a LB0 FS0 G RE X GC c i t x Ht Hx). destruct Hx'; cbn [fst snd] in *. lia.
- exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (slot_beg RE c' i') (class_size c') x P3 P3' ltac:(lia) ltac:(lia) D Hx Hx'). }
destruct K as [H|[H|[H|[H|[H|[H|H]]]]]]; unfold GQ, QMUT, IA, IA_FLAG, A_INSTANCE in *; try lia.
- destruct H as (j & Hj & Hj2). pose proof (proj1 (List.Forall_forall _ _) FJG j Hj) as Tj.
apply (OTHER 24 j TQOwn Tj); [| exact Hj2]. destruct (Z.eq_dec c 24) as [->|NE]; [right; intros ->; exact (NJ eq_refl Hj)| left; exact NE].
- destruct H as (id & n & i' & Hq & Ht' & H2).
apply (OTHER _ _ _ Ht'); [| exact H2]. destruct (Z.eq_dec c (class_of n)) as [->|NE]; [right; intros ->| left; exact NE].
rewrite Ht in Ht'. injection Ht' as E. exact (NQ id n E Hq).
- destruct H as (mb & n & Hq & H2). pose proof (REP0 _ Hq) as (Hin & _ & Hpr & _).
pose proof (sec_facts a LB0 FS0 G RE X GC _ Hin) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1. rewrite ?KHI_eq in E2. idtac.
pose proof (sec_map_size_ge n ltac:(lia) Hpr) as [M1 M2].
destruct Hx as [Hx|Hx], H2 as [H2|H2].
+ destruct Hx; cbn [fst snd] in *. lia.
+ pose proof (sec_band a LB0 FS0 G RE X GC (mkSec mb (sec_map_size n) n) x Hin) as SB. cbn [se_beg se_size] in SB. specialize (SB H2). destruct Hx; cbn [fst snd] in *. lia.
+ pose proof (slot_band a LB0 FS0 G RE X GC c i t x Ht Hx). lia.
+ exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (mb + kPage) (sec_map_size n - kPage) x P3 ltac:(rewrite KP; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hx H2).
Qed.

Lemma keep_sec : forall e x, In e (as_reg a) -> (forall n, In (ASec (se_beg e) n) Qs -> False) ->
(se_beg e + kPage <= x < se_beg e + se_size e \/ in_sh (se_beg e + kPage, se_size e - kPage) x) -> KEEP x -> False.
Proof.
intros e x He NQ Hx K. pose proof kconsts as (_ & _ & _ & _ & KP & _). pose proof SH_band as SHB0.
pose proof (sec_facts a LB0 FS0 G RE X GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & _). unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1.
rewrite ?KHI_eq in E2. idtac. pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1.
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in *. rewrite ?KHI_eq in PK. idtac.
assert (XB : (se_beg e + kPage <= x < se_beg e + se_size e) \/ (0x7fff7000 <= x < 0x10007fff8000)).
{ destruct Hx as [Hx|Hx]; [left; exact Hx| right; exact (sec_band a LB0 FS0 G RE X GC e x He Hx)]. }
assert (SLOT : forall c' i' t', tag_at G c' i' = Some t' ->
(in_iv (slot_beg RE c' i', class_size c') x \/ in_sh (slot_beg RE c' i', class_size c') x) -> False).
{ intros c' i' t' Ht' Hx'. pose proof (slot_prim a LB0 FS0 G RE X GC c' i' t' Ht') as (P1' & P2' & P3' & _ & _ & _ & _ & SZ' & _). unfold prim_hi, prim_lo in *.
destruct Hx as [Hx|Hx], Hx' as [Hx'|Hx'].
- destruct Hx'; cbn [fst snd] in *. lia.
- pose proof (slot_band a LB0 FS0 G RE X GC c' i' t' x Ht' Hx'). lia.
- pose proof (sec_band a LB0 FS0 G RE X GC e x He Hx). destruct Hx'; cbn [fst snd] in *. lia.
- exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (slot_beg RE c' i') (class_size c') x ltac:(rewrite KP; Z.div_mod_to_equations; lia) P3' ltac:(lia) ltac:(lia) ltac:(lia) Hx Hx'). }
destruct K as [H|[H|[H|[H|[H|[H|H]]]]]]; unfold GQ, QMUT, IA, IA_FLAG, A_INSTANCE in *; try lia.
- destruct H as (j & Hj & Hj2). exact (SLOT 24 j TQOwn (proj1 (List.Forall_forall _ _) FJG j Hj) Hj2).
- destruct H as (id & n & i' & Hq & Ht' & H2). exact (SLOT _ _ _ Ht' H2).
- destruct H as (mb & n & Hq & H2). pose proof (REP0 _ Hq) as (Hin & _ & Hpr & _).
destruct (decide (se_beg e = mb)) as [EQ|NE].
{ exfalso. apply (NQ n). rewrite EQ. exact Hq. }
pose proof (sec_facts a LB0 FS0 G RE X GC _ Hin) as (E1' & E2' & E3' & E4' & E5' & E6' & _). cbn [se_beg se_size se_req] in *.
rewrite ?KHI_eq in E2'. idtac. pose proof (sec_map_size_ge n ltac:(lia) Hpr) as [M1' M2'].
pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg a) e (mkSec mb (sec_map_size n) n)
(gc_sec_disj a LB0 FS0 G RE X GC) He Hin ltac:(cbn; intros EQ; apply NE; exact (f_equal fst EQ))) as D.
unfold iv_disjoint in D. cbn [fst snd se_beg se_size] in D.
destruct Hx as [Hx|Hx], H2 as [H2|H2].
+ (first [ clear - D M2' M1' E6' E2' E1' NE XB PK M1 E6 E2 E1 KP H2 n mb Hx x e RE BAND; lia | lia ]).
+ pose proof (sec_band a LB0 FS0 G RE X GC (mkSec mb (sec_map_size n) n) x Hin) as SB. cbn [se_beg se_size] in SB. specialize (SB H2). (first [ clear - SB D M2' M1' E6' E2' E1' NE PK M2 M1 E6 E4 E2 E1 KP n mb Hx x e RE BAND; lia | lia ]).
+ pose proof (sec_band a LB0 FS0 G RE X GC e x He Hx). (first [ clear - H D M2' M1' E6' E2' E1' NE PK M2 M1 E6 E4 E2 E1 KP H2 n mb x e RE BAND; lia | lia ]).
+ exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (mb + kPage) (sec_map_size n - kPage) x
ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H20 q3 H10 q1 H0 H r q D M1' E6' E2' E1' r1 NE PK M1 E6 E2 E1 r3 n mb e RE BAND; lia | lia ])) ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H20 q3 H10 q1 H0 H r q D M1' E6' E2' E1' r1 NE PK M1 E6 E2 E1 r3 n mb e RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D M2' M1' E6' E2' E1' NE PK M2 M1 E6 E4 E2 E1 KP n mb e RE BAND; lia | lia ])) Hx H2).
Qed.
End Keep.

Lemma rq_keep_tags : forall G G' RE JG Qs x,
(forall c i q, tag_at G c i = Some (TQuar q) <-> tag_at G' c i = Some (TQuar q)) ->
rq_keep G RE JG Qs x -> rq_keep G' RE JG Qs x.
Proof.
intros G G' RE JG Qs x TQ K. destruct K as [H|[H|[H|[H|[H|[H|H]]]]]]; unfold rq_keep; try tauto.
destruct H as (id & n & i & Hq & Ht & Hx). do 5 right; left. exists id, n, i. split; [exact Hq|]. split; [apply TQ; exact Ht| exact Hx].
Qed.

Lemma qptr_rep_ext {BAND : Band} : forall a a' LB G G' RE m QA q,
qptr_rep a LB G RE m QA q -> as_reg a' = as_reg a ->
(forall c i q, tag_at G c i = Some (TQuar q) <-> tag_at G' c i = Some (TQuar q)) ->
qptr_rep a' LB G' RE m QA q.
Proof.
intros a a' LB G G' RE m QA q R ER TQ. destruct q as [id n|mb n]; cbn [qptr_rep] in R |- *.
- destruct R as (i & Ht & R). exists i. split; [apply TQ; exact Ht| exact R].
- rewrite ER. exact R.
Qed.

Lemma qchunk_mem_agree_but_user {BAND : Band} : forall (P : Z -> Prop) m m' lo hi A n,
agree_on asegs P m m' -> wmono asegs m m' -> qchunk_mem m lo hi A n ->
(forall x, lo <= x < A -> P x) -> (forall x, SH lo <= x < SH lo + (hi - lo) / 8 -> P x) ->
qchunk_mem m' lo hi A n.
Proof.
intros P m m' lo hi A n AG WM QM HP HS.
pose proof (qchunk_geom m lo hi A n QM) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & q & g & r & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
destruct QM as (LEFT & (b1 & id & Hb1 & HDR) & JUNK & (sj & SHD) & PURE).
split; [| split; [| split; [| split; [| exact PURE]]]].
- intros Hrz. destruct (LEFT Hrz) as [L1 L2]. split.
+ eapply rw_cells_agree; [exact AG| exact L1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply HP. lia.
+ eapply hjunk_agree; [exact AG| exact L2|]. intros x Hx. apply HP. lia.
- exists b1, id. split; [exact Hb1|]. eapply rw_cells_agree; [exact AG| exact HDR|]. intros x Hx. cbn [qhdr_cells cells_size csize Nat.add] in Hx. apply HP. lia.
- eapply hjunk_wmono; [exact JUNK| exact WM].
- exists sj. eapply rw_cells_agree; [exact AG| exact SHD|]. intros x Hx. apply HS.
cbn [cells_size csize] in Hx. unfold fas in Hx. rewrite !Nat.add_0_r, !Nat2Z.inj_add, !Z2Nat.id in Hx by lia.
rewrite Q1, Q4, Q6, Q8 in *. rewrite !(Z.mul_comm 8), !Z.div_mul in Hx |- * by lia. lia.
Qed.

Lemma RQuarM_pend_agree {BAND : Band} : forall rb bt bg p A a LB FS G RE X m m',
gcons a LB FS G RE X -> RQuarM rb bt bg [(p, A)] a LB G RE X m -> wmono asegs m m' ->
agree_on asegs (fun x => fp_RQuar a LB G RE X x /\ ~ (A <= x < A + 8)) m m' ->
RQuarM rb bt bg [(p, A)] a LB G RE X m'.
Proof.
intros rb bt bg p A a LB FS G RE X m m' GC RQ WM AG.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND).
pose proof PQA as PQA0. apply Forall_cons_iff in PQA as [EQA _]. cbn [fst snd] in EQA.
pose proof HT as (TQC & BMT & FJT & QWT). pose proof HG as (GQC & BMG & FJG & QWG).
assert (FJ : Forall (fun j => tag_at G 24 j = Some TQOwn) (JT ++ JG)) by (apply Forall_app; split; assumption).
set (Qs' := qptrs (as_tq a) ++ qptrs (as_gq a)).
assert (EQQ : qall [(p, A)] a = p :: Qs') by reflexivity.
assert (NDQ : List.NoDup (p :: Qs')) by (rewrite <- EQQ; exact NDP).
assert (NIp : ~ In p Qs') by (inversion NDQ; assumption).
assert (REP' : forall q', In q' Qs' -> qptr_rep a LB G RE m QA q') by (intros q' Hq; apply REP; rewrite EQQ; right; exact Hq).
pose proof (REP p ltac:(rewrite EQQ; left; reflexivity)) as REPp.

assert (PC0 : exists lo hi, qchunk_mem m lo hi A (aptr_req p)
/\ (forall x, lo <= x < hi \/ in_sh (lo, hi - lo) x -> fp_RQuar a LB G RE X x)
/\ (forall x, lo <= x < hi \/ in_sh (lo, hi - lo) x -> rq_keep G RE (JT ++ JG) Qs' x -> False)
/\ (forall x, lo <= x < hi -> ~ (rl_T X <= x < rl_T X + 4096))
/\ (qchunk_mem m' lo hi A (aptr_req p) -> qptr_rep a LB G RE m' QA p)).
{ destruct p as [id n0|mb n0]; cbn [qptr_rep aptr_req] in REPp |- *.
- destruct REPp as (i & Ht & Hpr & HQA & QM). rewrite EQA in QM. exists (slot_beg RE (class_of n0) i), (slot_beg RE (class_of n0) i + class_size (class_of n0)).
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & _). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & _ & _ & TD & _). unfold iv_disjoint, prim_hi, prim_lo in TD, P1, P2; cbn [fst snd] in TD.
split; [exact QM|]. split; [| split; [| split]].
+ intros x [Hx|Hx]; [do 5 right; left| do 6 right; left]; exists (class_of n0), i, (TQuar (APrim id n0)); (split; [exact Ht|]); (split; [reflexivity|]).
* split; cbn [fst snd]; lia.
* replace (slot_beg RE (class_of n0) i + class_size (class_of n0) - slot_beg RE (class_of n0) i) with (class_size (class_of n0)) in Hx by lia. exact Hx.
+ intros x Hx K. refine (keep_slot a LB FS G RE X GC QA (JT ++ JG) Qs' FJ m REP' (class_of n0) i _ x Ht _ _ _ K).
* intros E24 Hi. pose proof (proj1 (List.Forall_forall _ _) FJ i Hi) as Ti. rewrite E24, Ti in Ht. discriminate.
* intros id' n' E Hq. injection E as <- <-. exact (NIp Hq).
* destruct Hx as [Hx|Hx]; [left; split; cbn [fst snd]; lia| right].
replace (slot_beg RE (class_of n0) i + class_size (class_of n0) - slot_beg RE (class_of n0) i) with (class_size (class_of n0)) in Hx by lia. exact Hx.
+ intros x Hx. lia.
+ intros QM'. exists i. split; [exact Ht|]. split; [exact Hpr|]. split; [exact HQA|]. rewrite EQA. exact QM'.
- destruct REPp as (Hin & Hnl & Hpr & HQA & QM). rewrite EQA in QM. exists (mb + kPage), (mb + sec_map_size n0).
split; [exact QM|]. split; [| split; [| split]].
+ intros x [Hx|Hx]; [do 7 right; left| do 8 right]; exists (mkSec mb (sec_map_size n0) n0); cbn [se_beg se_size se_req]; (split; [exact Hin|]); (split; [exact Hnl|]).
* lia.
* replace (mb + sec_map_size n0 - (mb + kPage)) with (sec_map_size n0 - kPage) in Hx by lia. exact Hx.
+ intros x Hx K. refine (keep_sec a LB FS G RE X GC QA (JT ++ JG) Qs' FJ m REP' (mkSec mb (sec_map_size n0) n0) x Hin _ _ K); cbn [se_beg se_size].
* intros n' Hq. pose proof (REP' _ Hq) as (Hin' & _). cbn [qptr_rep] in Hin'.
pose proof (NoDup_map_In_inj se_beg (as_reg a) _ _ (gc_sec_nodup a LB FS G RE X GC) Hin Hin' eq_refl) as E. injection E as En. subst n'. exact (NIp Hq).
* destruct Hx as [Hx|Hx]; [left; lia| right]. replace (mb + sec_map_size n0 - (mb + kPage)) with (sec_map_size n0 - kPage) in Hx by lia. exact Hx.
+ intros x Hx. pose proof (sec_facts _ _ _ _ _ _ GC _ Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & D3). cbn [se_beg se_size] in D3.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D. lia.
+ intros QM'. split; [exact Hin|]. split; [exact Hnl|]. split; [exact Hpr|]. split; [exact HQA|]. rewrite EQA. exact QM'. }
destruct PC0 as (plo & phi & QMp & PZ & PK & PT & PBACK).
pose proof (qchunk_geom _ _ _ _ _ QMp) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & q & g & r & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).

assert (AGK : agree_on asegs (fun x => rq_keep G RE (JT ++ JG) Qs' x \/ rl_T X + 80 <= x < rl_T X + 112) m m').
{ eapply agree_on_mono; [exact AG|]. intros x [K|K].
- split; [exact (rq_keep_fp a LB G RE X QA (JT ++ JG) Qs' FJ m REP' x K)|]. intros Hx. apply (PK x); [left; lia| exact K].
- split; [left; split; cbn [fst snd]; lia|]. intros Hx. apply (PT x); [lia|].
pose proof (rlay_obj_facts RE X _ (gc_rlay _ _ _ _ _ _ GC) (T_obj RE X)) as (_ & TK & _). cbn [fst] in TK. lia. }
assert (HT' : qrep RE G m' QA (TQ X) (as_tq a) JT).
{ eapply qrep_agree; [exact AGK| exact HT| intros x Hx; right; unfold TQ in Hx; lia| |].
- intros j x Hj Hx. left. do 4 right; left. exists j. split; [apply in_app_iff; left; exact Hj| left; exact Hx].
- intros j x Hj Hx. left. do 4 right; left. exists j. split; [apply in_app_iff; left; exact Hj| right; exact Hx]. }
destruct (rq_transport a LB G RE QA JG Qs' m m' (as_gq a) rb) as (HG' & HM' & HI' & REP2).
{ eapply agree_on_mono; [exact AGK|]. intros x Kx. left. revert Kx. unfold rq_keep. intros [K|[K|[K|[K|[K|[K|K]]]]]]; try (clear - K; tauto).
do 4 right; left. destruct K as (j & Hj & K). exists j. split; [apply in_app_iff; right; exact Hj| exact K]. }
{ exact HG. } { exact HM. } { exact HI. } { exact REP'. }

assert (QMp' : qchunk_mem m' plo phi A (aptr_req p)).
{ eapply (qchunk_mem_agree_but_user (fun x => (plo <= x < A) \/ in_sh (plo, phi - plo) x)); [| exact WM| exact QMp| intros x Hx; left; exact Hx| intros x Hx; right; split; cbn [fst snd]; lia].
eapply agree_on_mono; [exact AG|]. intros x Hx. split.
- apply PZ. destruct Hx as [Hx|Hx]; [left; lia| right; exact Hx].
- destruct Hx as [Hx|Hx]; [lia|].
assert (PB0 : plo + (phi - plo) <= band_lo) by lia.
pose proof (in_sh_band plo (phi - plo) x ltac:(Z.div_mod_to_equations; lia) ltac:(lia) (proj1 G3) PB0 Hx) as B0. unfold kLowEnd, KHI in B0.
clear - B0 G3 G1 G2 Q3 Q5. lia. }
exists JT, JG, QA. split; [exact HT'|]. split; [exact HG'|]. split; [exact HM'|]. split; [exact HI'|].
repeat (split; [assumption|]). split; [| split; [exact TQP| split; [exact PQA0| exact BND]]].
intros q' Hq. rewrite EQQ in Hq. destruct Hq as [<-|Hq]; [exact (PBACK QMp')| exact (REP2 q' Hq)].
Qed.

Lemma batches_mem_nx_QA : forall RE m (QA QA' : aptr -> Z) bs J fin,
(forall q, In q (concat (map b_chunks bs)) -> QA' q = QA q) ->
batches_mem_nx RE m QA bs J fin -> batches_mem_nx RE m QA' bs J fin.
Proof.
intros RE m QA QA' bs. induction bs as [|b bs IH]; intros J fin E H; destruct J as [|j J]; cbn in H |- *; try exact H.
destruct H as [(B1 & B2 & B3 & B4) H]. split; [| apply IH; [intros q Hq; apply E; cbn; apply in_app_iff; right; exact Hq| exact H]].
split; [exact B1|]. split; [| split; [exact B3| exact B4]].
replace (map (fun p => Z_to_bv 64 (QA' p - 16)) (b_chunks b)) with (map (fun p => Z_to_bv 64 (QA p - 16)) (b_chunks b)); [exact B2|].
apply map_ext_in. intros q Hq. rewrite (E q); [reflexivity|]. cbn. apply in_app_iff. left. exact Hq.
Qed.

Lemma qrep_QA : forall RE G m (QA QA' : aptr -> Z) C q J,
(forall p, In p (qptrs q) -> QA' p = QA p) -> qrep RE G m QA C q J -> qrep RE G m QA' C q J.
Proof.
intros RE G m QA QA' C q J E (R1 & R2 & R3 & R4). split; [exact R1|]. split; [| split; [exact R3| exact R4]].
eapply batches_mem_nx_QA; [exact E| exact R2].
Qed.

Section Free.
Context {BAND : Band}.
Variables (a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB FS G RE X.
Variables (rb bt bg : Z) (m m' : mem) (p : aptr) (A n : Z).
Hypothesis RQ : RQuarM rb bt bg [] a LB G RE X m.
Hypothesis INB : In (p, A, n) LB.
Hypothesis AG : agree_on asegs (fp_RQuar a LB G RE X) m m'.

Let QA' (QA : aptr -> Z) : aptr -> Z := fun q => if aptr_eqb q p then A else QA q.

Lemma QA'_p : forall QA, QA' QA p = A.
Proof. intros QA. unfold QA'. rewrite aptr_eqb_refl'. reflexivity. Qed.
Lemma QA'_other : forall QA q, q <> p -> QA' QA q = QA q.
Proof. intros QA q NE. unfold QA'. destruct (aptr_eqb q p) eqn:E; [| reflexivity]. exfalso. apply NE. apply aptr_eqb_true. exact E. Qed.

Lemma RQuarM_free_prim : forall id c i,
p = APrim id n -> c = class_of n -> tag_at G c i = Some (TLive p) -> A = slot_beg RE c i + rz_size n ->
qchunk_mem m' (slot_beg RE c i) (slot_beg RE c i + class_size c) A n ->
RQuarM rb bt bg [(p, A)] a (alb_remove p LB) (set_tag c i (TQuar p) G) RE X m'.
Proof.
intros id c i Ep Ec Ht HA QM'.
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND).
pose proof (retag_at G c i (TLive p) (TQuar p) Ht) as RT.
destruct (gc_blocks a LB FS G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn & HP & Ht0 & _)|(mb & E0 & _)]; [| subst p; discriminate].
assert (NIq : ~ In p (qall [] a)).
{ intros Hin. pose proof (REP p Hin) as R. rewrite Ep in R. cbn [qptr_rep] in R. destruct R as (i' & Ht' & _).
rewrite <- Ep, <- Ec in Ht'.
pose proof (gc_unique a LB FS G RE X GC _ _ _ _ p _ _ Ht Ht' ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
rewrite Ht in Ht'. discriminate. }
assert (EQA : forall q, In q (qall [] a) -> QA' QA q = QA q) by (intros q Hq; apply QA'_other; intros ->; exact (NIq Hq)).
assert (T1 : forall c' i', tag_at (set_tag c i (TQuar p) G) c' i' = Some TQOwn <-> tag_at G c' i' = Some TQOwn).
{ intros c' i'. rewrite RT. destruct ((c' =? c) && (i' =? i)) eqn:E; [| tauto].
apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' i'. rewrite Ht. split; intros; discriminate. }
assert (T2 : forall c' i' q, q <> p -> (tag_at G c' i' = Some (TQuar q) <-> tag_at (set_tag c i (TQuar p) G) c' i' = Some (TQuar q))).
{ intros c' i' q NE. rewrite RT. destruct ((c' =? c) && (i' =? i)) eqn:E; [| tauto].
apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' i'. rewrite Ht. split; intros HH; [discriminate| injection HH as HH; exfalso; exact (NE (eq_sym HH))]. }
assert (QREP : forall Cq qq J, (forall x, Cq <= x < Cq + 32 -> fp_RQuar a LB G RE X x) -> (forall q, In q (qptrs qq) -> In q (qall [] a)) ->
qrep RE G m QA Cq qq J -> qrep RE (set_tag c i (TQuar p) G) m' (QA' QA) Cq qq J).
{ intros Cq qq J HC HQ R. pose proof R as (_ & _ & R3 & _).
assert (R' : qrep RE G m' QA Cq qq J).
{ eapply qrep_agree; [exact AG| exact R| exact HC| |].
- intros j x Hj Hx. do 5 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)|]. auto.
- intros j x Hj Hx. do 6 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)|]. auto. }
apply (qrep_QA RE _ m' QA (QA' QA)) in R'; [| intros q Hq; apply EQA; apply HQ; exact Hq].
destruct R' as (R1' & R2' & R3' & R4'). split; [exact R1'|]. split; [exact R2'|]. split; [| exact R4'].
apply List.Forall_forall. intros j Hj. apply T1. exact (proj1 (List.Forall_forall _ _) R3' j Hj). }
exists JT, JG, (QA' QA).
split; [apply QREP; [intros x Hx; left; unfold TQ in Hx; split; cbn [fst snd]; lia| intros q Hq; unfold qall; cbn [map app]; apply in_app_iff; left; exact Hq| exact HT]|].
split; [apply QREP; [intros x Hx; right; right; left; unfold GQ in Hx; split; cbn [fst snd]; lia| intros q Hq; unfold qall; cbn [map app]; apply in_app_iff; right; exact Hq| exact HG]|].
split; [eapply rw_cells_agree; [exact AG| exact HM|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; right; left; unfold QMUT in Hx; split; cbn [fst snd]; lia|].
split; [eapply ia_inv_agree; [exact AG| exact HI|]; intros x [Hx|Hx]; [do 3 right; left| do 4 right; left]; unfold IA, IA_FLAG in *; split; cbn [fst snd]; lia|].
split; [exact ND|]. split; [intros j Hj; apply TQO; apply T1; exact Hj|]. split; [intros c' j Hj; apply (C24 c' j); apply T1; exact Hj|].
assert (EQQ : qall [(p, A)] a = p :: qall [] a) by reflexivity. rewrite EQQ.
split; [constructor; [exact NIq| exact NDP]|].
split.
{ intros q [<-|Hq].
- rewrite Ep. cbn [qptr_rep]. rewrite <- Ep, <- Ec. exists i. split; [rewrite RT, !Z.eqb_refl; reflexivity|]. split; [exact HP|].
rewrite QA'_p. split; [exact HA| exact QM'].
- assert (NE : q <> p) by (intros ->; exact (NIq Hq)).
pose proof (REP q Hq) as R. destruct q as [idq nq|mbq nq]; cbn [qptr_rep] in R |- *.
+ destruct R as (iq & Htq & Hpr & HQA & QM). exists iq. split; [apply (T2 _ _ _ NE); exact Htq|]. split; [exact Hpr|].
rewrite (QA'_other QA _ NE). split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => in_iv (slot_beg RE (class_of nq) iq, class_size (class_of nq)) x \/ in_sh (slot_beg RE (class_of nq) iq, class_size (class_of nq)) x));
[| exact QM| intros x Hx; left; split; cbn [fst snd]; lia| intros x Hx; right; split; cbn [fst snd]; [lia|]].
* eapply agree_on_mono; [exact AG|]. intros x [Hx|Hx]; [do 5 right; left| do 6 right; left]; exists (class_of nq), iq, (TQuar (APrim idq nq)); auto.
* replace (slot_beg RE (class_of nq) iq + class_size (class_of nq) - slot_beg RE (class_of nq) iq) with (class_size (class_of nq)) in Hx by lia. lia.
+ destruct R as (Hin & Hnl & Hpr & HQA & QM). split; [exact Hin|]. split; [intros (A2 & HL); apply Hnl; exists A2; exact (proj1 (proj1 (In_alb_remove _ _ _) HL))|].
split; [exact Hpr|]. rewrite (QA'_other QA _ NE). split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => mbq + kPage <= x < mbq + sec_map_size nq \/ in_sh (mbq + kPage, sec_map_size nq - kPage) x));
[| exact QM| intros x Hx; left; exact Hx| intros x Hx; right; split; cbn [fst snd]; [lia|]].
* eapply agree_on_mono; [exact AG|]. intros x [Hx|Hx]; [do 7 right; left| do 8 right]; exists (mkSec mbq (sec_map_size nq) nq); cbn [se_beg se_size se_req]; auto.
* replace (mbq + sec_map_size nq - (mbq + kPage)) with (sec_map_size nq - kPage) in Hx by lia. lia. }
split.
{ intros c' i' q Hq'. rewrite RT in Hq'. destruct ((c' =? c) && (i' =? i)) eqn:E.
- injection Hq' as <-. apply andb_prop in E as [E1 _]. apply Z.eqb_eq in E1. subst c'. split; [left; reflexivity| rewrite Ep; cbn; symmetry; exact Ec].
- destruct (TQP c' i' q Hq') as [H1 H2]. split; [right; exact H1| exact H2]. }
split; [constructor; [cbn [fst snd]; apply QA'_p| constructor]| exact BND].
Qed.

Lemma RQuarM_free_sec : forall mb,
p = ASec mb n -> In (mkSec mb (sec_map_size n) n) (as_reg a) -> A = mb + kSecUserOff ->
qchunk_mem m' (mb + kPage) (mb + sec_map_size n) A n ->
RQuarM rb bt bg [(p, A)] a (alb_remove p LB) G RE X m'.
Proof.
intros mb Ep He HA QM'.
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND).
destruct (gc_blocks a LB FS G RE X GC p A n INB) as [(id0 & i0 & E0 & _)|(mb0 & E0 & Hn & HP & _)]; [subst p; discriminate|].
assert (NIq : ~ In p (qall [] a)).
{ intros Hin. pose proof (REP p Hin) as R. rewrite Ep in R. cbn [qptr_rep] in R. destruct R as (_ & Hnl & _).
apply Hnl. exists A. cbn [se_beg se_req]. rewrite <- Ep. exact INB. }
assert (EQA : forall q, In q (qall [] a) -> QA' QA q = QA q) by (intros q Hq; apply QA'_other; intros ->; exact (NIq Hq)).
assert (QREP : forall Cq qq J, (forall x, Cq <= x < Cq + 32 -> fp_RQuar a LB G RE X x) -> (forall q, In q (qptrs qq) -> In q (qall [] a)) ->
qrep RE G m QA Cq qq J -> qrep RE G m' (QA' QA) Cq qq J).
{ intros Cq qq J HC HQ R. pose proof R as (_ & _ & R3 & _).
assert (R' : qrep RE G m' QA Cq qq J).
{ eapply qrep_agree; [exact AG| exact R| exact HC| |].
- intros j x Hj Hx. do 5 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)|]. auto.
- intros j x Hj Hx. do 6 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)|]. auto. }
apply (qrep_QA RE _ m' QA (QA' QA)) in R'; [exact R'| intros q Hq; apply EQA; apply HQ; exact Hq]. }
exists JT, JG, (QA' QA).
split; [apply QREP; [intros x Hx; left; unfold TQ in Hx; split; cbn [fst snd]; lia| intros q Hq; unfold qall; cbn [map app]; apply in_app_iff; left; exact Hq| exact HT]|].
split; [apply QREP; [intros x Hx; right; right; left; unfold GQ in Hx; split; cbn [fst snd]; lia| intros q Hq; unfold qall; cbn [map app]; apply in_app_iff; right; exact Hq| exact HG]|].
split; [eapply rw_cells_agree; [exact AG| exact HM|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; right; left; unfold QMUT in Hx; split; cbn [fst snd]; lia|].
split; [eapply ia_inv_agree; [exact AG| exact HI|]; intros x [Hx|Hx]; [do 3 right; left| do 4 right; left]; unfold IA, IA_FLAG in *; split; cbn [fst snd]; lia|].
split; [exact ND|]. split; [exact TQO|]. split; [exact C24|].
assert (EQQ : qall [(p, A)] a = p :: qall [] a) by reflexivity. rewrite EQQ.
split; [constructor; [exact NIq| exact NDP]|].
split.
{ intros q [<-|Hq].
- rewrite Ep. cbn [qptr_rep]. split; [exact He|]. split.
+ intros (A2 & HL). cbn [se_beg se_req] in HL. apply In_alb_remove in HL as [_ NE]. apply NE. reflexivity.
+ split; [exact HP|]. rewrite <- Ep, QA'_p. split; [exact HA| exact QM'].
- assert (NE : q <> p) by (intros ->; exact (NIq Hq)).
pose proof (REP q Hq) as R. destruct q as [idq nq|mbq nq]; cbn [qptr_rep] in R |- *.
+ destruct R as (iq & Htq & Hpr & HQA & QM). exists iq. split; [exact Htq|]. split; [exact Hpr|].
rewrite (QA'_other QA _ NE). split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => in_iv (slot_beg RE (class_of nq) iq, class_size (class_of nq)) x \/ in_sh (slot_beg RE (class_of nq) iq, class_size (class_of nq)) x));
[| exact QM| intros x Hx; left; split; cbn [fst snd]; lia| intros x Hx; right; split; cbn [fst snd]; [lia|]].
* eapply agree_on_mono; [exact AG|]. intros x [Hx|Hx]; [do 5 right; left| do 6 right; left]; exists (class_of nq), iq, (TQuar (APrim idq nq)); auto.
* replace (slot_beg RE (class_of nq) iq + class_size (class_of nq) - slot_beg RE (class_of nq) iq) with (class_size (class_of nq)) in Hx by lia. lia.
+ destruct R as (Hin & Hnl & Hpr & HQA & QM). split; [exact Hin|]. split; [intros (A2 & HL); apply Hnl; exists A2; exact (proj1 (proj1 (In_alb_remove _ _ _) HL))|].
split; [exact Hpr|]. rewrite (QA'_other QA _ NE). split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => mbq + kPage <= x < mbq + sec_map_size nq \/ in_sh (mbq + kPage, sec_map_size nq - kPage) x));
[| exact QM| intros x Hx; left; exact Hx| intros x Hx; right; split; cbn [fst snd]; [lia|]].
* eapply agree_on_mono; [exact AG|]. intros x [Hx|Hx]; [do 7 right; left| do 8 right]; exists (mkSec mbq (sec_map_size nq) nq); cbn [se_beg se_size se_req]; auto.
* replace (mbq + sec_map_size nq - (mbq + kPage)) with (sec_map_size nq - kPage) in Hx by lia. lia. }
split.
{ intros c' i' q Hq'. destruct (TQP c' i' q Hq') as [H1 H2]. split; [right; exact H1| exact H2]. }
split; [constructor; [cbn [fst snd]; apply QA'_p| constructor]| exact BND].
Qed.
End Free.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Q0Do.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QYyZ.Mq5.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Z.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Variables (mb msz : Z).
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis MSZ : 4096 <= msz.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Hypothesis AVQ : mb + msz <= ptrarr_lo RE \/ ptrarr_lo RE + 0x800000 <= mb.
Hypothesis AVR : forall e, In e (as_reg a) -> mb + msz <= se_beg e \/ se_beg e + se_size e <= mb.

Set Default Proof Using "GC MBP MBK MBC MSZ AVO AVP AVQ AVR".

Lemma prim_hi_eq : prim_hi RE = prim_lo RE + 2^37 + 0x1000. Proof. reflexivity. Qed.
Lemma region_info_eq : region_info RE = prim_lo RE + 2^37. Proof. reflexivity. Qed.

Definition nmap (x : Z) : Prop := mb <= x < mb + msz \/ in_sh (mb, msz) x.

Local Ltac lits := rewrite ?KHI_eq in *.

Lemma nmap_where : forall x, nmap x ->
(mb <= x < mb + msz)
\/ (0x7fff7000 <= x < 0x10007fff8000 /\ in_sh (mb, msz) x).
Proof.
intros x [H|H]; [left; exact H| right; split; [| exact H]].
pose proof (in_sh_band mb msz x ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(clear - MBK MBC; lia) MBC H) as B.
unfold kLowEnd, KHI in B. exact B.
Qed.

Lemma nmap_apart : forall lo len x, lo mod 8 = 0 -> 0 <= len -> lowhigh lo len -> lo + len <= band_lo ->
(mb + msz <= lo \/ lo + len <= mb) ->
nmap x -> (lo <= x < lo + len \/ in_sh (lo, len) x) -> False.
Proof.
intros lo len x AL L K C D NM [R|R].
- destruct (nmap_where x NM) as [M|[B M]]; [lia|]. clear - K R B. lia.
- pose proof (in_sh_band lo len x AL L K C R) as B. unfold kLowEnd, KHI in B. destruct (nmap_where x NM) as [M|[B' M]].
+ clear - MBK M B. lia.
+ exact (in_sh_disjoint lo len mb msz x AL ltac:(clear - MBP; Z.div_mod_to_equations; lia) L ltac:(lia) ltac:(lia) R M).
Qed.

Lemma nmap_low : forall x, 0x10000 <= x < 0x645000 -> nmap x -> False.
Proof. intros x Hx NM. destruct (nmap_where x NM) as [M|[B _]]; [clear - MBK M Hx; lia| lia]. Qed.

Lemma nmap_obj : forall o x, In o (rlay_objs RE X) -> in_iv o x -> nmap x -> False.
Proof.
intros o x Ho [O1 O2] NM. cbn [fst snd] in O1, O2. pose proof (rl_objs_lia _ _ _ _ _ _ GC o Ho) as (OA & OK & OC & _).
destruct (AVO o Ho); destruct (nmap_where x NM) as [M|[B M]]; lits; lia.
Qed.

Lemma nmap_prim : forall x, prim_lo RE <= x < prim_lo RE + 2^37 + 0x1000 -> nmap x -> False.
Proof.
intros x Hx NM. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). rewrite ?prim_hi_eq in *.
destruct (nmap_where x NM) as [M|[B M]]; lits; lia.
Qed.

Lemma nmap_prim_sh : forall lo len x, lo mod 8 = 0 -> 0 <= len -> prim_lo RE <= lo -> lo + len <= prim_lo RE + 2^37 + 0x1000 ->
in_sh (lo, len) x -> nmap x -> False.
Proof.
intros lo len x AL L P1 P2 R NM. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). rewrite ?prim_hi_eq in *.
lits. eapply (nmap_apart lo len x AL L); [lia| lia| lia| exact NM| right; exact R].
Qed.

Lemma nmap_sec : forall e x, In e (as_reg a) ->
(se_beg e <= x < se_beg e + se_size e \/ in_sh (se_beg e, kPage) x \/ in_sh (se_beg e + kPage, se_size e - kPage) x) -> nmap x -> False.
Proof.
intros e x He R NM. pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1. pose proof kconsts as (_ & _ & _ & _ & KP & _).
pose proof (AVR e He) as D.
destruct R as [R|[R|R]].
- eapply (nmap_apart (se_beg e) (se_size e) x); [clear - E1; Z.div_mod_to_equations; lia| lia| lia| lia| lia| exact NM| left; exact R].
- eapply (nmap_apart (se_beg e) kPage x); [clear - E1; Z.div_mod_to_equations; lia| rewrite KP; lia| lia| rewrite KP; lia| rewrite KP; lia| exact NM| right; exact R].
- eapply (nmap_apart (se_beg e + kPage) (se_size e - kPage) x); [rewrite KP; clear - E1; Z.div_mod_to_equations; lia| rewrite KP; lia| rewrite KP; lia| lia| rewrite KP; lia| exact NM| right; exact R].
Qed.

Lemma nmap_slot : forall c i t x, tag_at G c i = Some t ->
(in_iv (slot_beg RE c i, class_size c) x \/ in_sh (slot_beg RE c i, class_size c) x) -> nmap x -> False.
Proof.
intros c i t x Ht [R|R] NM; pose proof (slot_prim _ _ _ _ _ _ GC c i t Ht) as (P1 & P2 & P3 & _ & _ & _ & _ & S1 & _); rewrite ?prim_hi_eq in *.
- destruct R as [R1 R2]; cbn [fst snd] in R1, R2. apply (nmap_prim x); [lia| exact NM].
- eapply (nmap_prim_sh (slot_beg RE c i) (class_size c) x); [exact P3| lia| lia| lia| exact R| exact NM].
Qed.

Lemma nmap_region : forall c x, 1 <= c <= 31 ->
(reg_beg (ae_L RE) c <= x < reg_beg (ae_L RE) c + kFreeArrayOffset \/ in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) x
\/ fa_beg (ae_L RE) c <= x < fa_beg (ae_L RE) c + kFreeArraySize \/ in_sh (fa_beg (ae_L RE) c, kFreeArraySize) x) -> nmap x -> False.
Proof.
intros c x Hc R NM. pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof kconsts as (_ & KO & KS & _).
pose proof (reg_beg_align RE X c (gc_rlay _ _ _ _ _ _ GC)) as (RA & _ & FA).
destruct R as [R|[R|[R|R]]].
- apply (nmap_prim x); [rewrite KO in R; lia| exact NM].
- eapply (nmap_prim_sh (reg_beg (ae_L RE) c) kFreeArrayOffset x); [exact RA| rewrite KO; lia| lia| rewrite KO, KS in *; lia| exact R| exact NM].
- apply (nmap_prim x); [rewrite KS in R; lia| exact NM].
- eapply (nmap_prim_sh (fa_beg (ae_L RE) c) kFreeArraySize x); [exact FA| rewrite KS; lia| lia| rewrite KS; lia| exact R| exact NM].
Qed.

Lemma nmap_RPrim : forall x, nmap x -> fp_RPrim G RE X x -> False.
Proof.
intros x NM F. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). rewrite ?prim_hi_eq in *.
destruct (fp_RPrim_loc G RE X x F) as [H|H|c Hc H|c Hc H|c Hc H _|c Hc H _].
- apply (nmap_prim x); [rewrite region_info_eq in H; lia| exact NM].
- eapply (nmap_obj _ x (T_obj RE X)); [split; cbn [fst snd]; lia| exact NM].
- eapply (nmap_region c x Hc); [do 2 right; left; exact H| exact NM].
- eapply (nmap_region c x Hc); [do 3 right; exact H| exact NM].
- eapply (nmap_region c x Hc); [left; exact H| exact NM].
- eapply (nmap_region c x Hc); [right; left; exact H| exact NM].
Qed.

Lemma nmap_RQuar : forall x, nmap x -> fp_RQuar a LB0 G RE X x -> False.
Proof.
intros x NM F.
destruct (fp_RQuar_loc a LB0 G RE X x F) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- eapply (nmap_obj _ x (T_obj RE X)); [split; cbn [fst snd]; lia| exact NM].
- apply (nmap_low x); [| exact NM]. pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT). lia.
- eapply (nmap_slot c i t x Ht); [left; exact H| exact NM].
- eapply (nmap_slot c i t x Ht); [right; exact H| exact NM].
- eapply (nmap_sec e x He); [left; pose proof kconsts as (_ & _ & _ & _ & KP & _); lia| exact NM].
- eapply (nmap_sec e x He); [do 2 right; exact H| exact NM].
Qed.

Lemma nmap_RChunks : forall x, nmap x -> fp_RChunks a LB0 G RE X x -> False.
Proof.
intros x NM [[[H|H] _]|[H|H]].
- destruct H as (c & i & t & Ht & _ & Hx). eapply (nmap_slot c i t x Ht); [left; exact Hx| exact NM].
- destruct H as (e & He & _ & Hx). eapply (nmap_sec e x He); [left; pose proof kconsts as (_ & _ & _ & _ & KP & _); lia| exact NM].
- destruct H as (c & i & t & Ht & _ & Hx). eapply (nmap_slot c i t x Ht); [right; exact Hx| exact NM].
- destruct H as (e & He & _ & Hx). eapply (nmap_sec e x He); [do 2 right; exact Hx| exact NM].
Qed.

Lemma nmap_RSec : forall x, nmap x -> fp_RSec a RE X x -> False.
Proof.
intros x NM [H|[H|[H|H]]].
- apply (nmap_low x); [| exact NM]. destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold A_INSTANCE in *. lia.
- destruct H as [H1 H2]; cbn [fst snd] in H1, H2. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & QK & QC & _). unfold ptrarr_hi, ptrarr_lo in *.
destruct (nmap_where x NM) as [M|[B M]]; lits; lia.
- destruct H as (e & He & Hx). eapply (nmap_sec e x He); [left; pose proof (sec_facts _ _ _ _ _ _ GC e He) as (_ & _ & _ & E4 & E5 & E6 & _);
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]; rewrite <- E4 in M1; pose proof kconsts as (_ & _ & _ & _ & KP & _); lia| exact NM].
- destruct H as (e & He & Hx). eapply (nmap_sec e x He); [right; left; exact Hx| exact NM].
Qed.

Lemma nmap_RDepot : forall x, nmap x -> fp_RDepot RE X x -> False.
Proof.
intros x NM [H|[H|[H|H]]].
- apply (nmap_low x); [| exact NM]. destruct H as [H1 H2]; cbn [fst snd] in H1, H2. lia.
- eapply (nmap_obj _ x (dn_obj RE X)); [exact H| exact NM].
- eapply (nmap_obj _ x (ssb_obj RE X)); [exact H| exact NM].
- eapply (nmap_obj _ x (T_obj RE X)); [subst x; split; cbn [fst snd]; lia| exact NM].
Qed.

Lemma nmap_RStats : forall x, nmap x -> fp_RStats RE X x -> False.
Proof.
intros x NM [H|[H|H]].
- eapply (nmap_obj _ x (T_obj RE X)); [destruct H as [H1 H2]; cbn [fst snd] in H1, H2; split; cbn [fst snd]; lia| exact NM].
- apply (nmap_low x); [| exact NM]. destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold A_ERRNO in *. lia.
- apply (nmap_low x); [| exact NM]. lia.
Qed.

Lemma nmap_RFake : forall x, nmap x -> fp_RFake FS0 RE X x -> False.
Proof.
intros x NM F. pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
destruct (fp_RFake_zone RE X FS0 x F) as [R|R].
- exact (nmap_obj _ x (fs_obj RE X) R NM).
- eapply (nmap_apart (ae_fs_base RE) A_FS_MAP_SIZE x); [clear - FAL; Z.div_mod_to_equations; lia| unfold A_FS_MAP_SIZE; lia| exact (proj1 FK)| exact FC
| destruct (AVO _ (fs_obj RE X)); cbn [fst snd] in *; lia| exact NM| right; exact R].
Qed.

Lemma nmap_client : forall LB FS SP x, Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> nmap x -> False.
Proof.
intros LB FS SP x PB PF CSP CA NM.
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
destruct (nmap_where x NM) as [M|[B M]].
- destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
+ lits. lia.
+ cbn [ala_client_data a_alayout] in C1. unfold a_client_data in C1. lia.
+ assert (LU : in_live_user LB0 x) by (destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R]).
destruct (live_user_where _ _ _ _ _ _ GC x LU) as (p & A & n & Hin & Hx & [(c & i & Ht & R1 & R2)|(e & He & _ & R1 & R2)]).
* eapply (nmap_slot c i _ x Ht); [left; split; cbn [fst snd]; lia| exact NM].
* eapply (nmap_sec e x He); [left; pose proof kconsts as (_ & _ & _ & _ & KP & _); lia| exact NM].
+ assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range _ _ _ _ _ _ GC f Hf0) as (R1 & R2 & R3 & R4 & R5).
eapply (nmap_obj _ x (fs_obj RE X)); [split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia| exact NM].
+ assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
pose proof (frame_shadow_where _ _ _ _ _ _ GC x SHD) as FS'.
pose proof (in_sh_band (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(clear - FAL; Z.div_mod_to_equations; lia) ltac:(unfold A_FS_MAP_SIZE; lia) (proj1 FK) FC FS') as B0. unfold kLowEnd, KHI in B0. clear - MBK M B0. lia.
+ rewrite SH_247 in C1. lits. pose proof SH_band. lia.
+ cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. lia.
- pose proof M as M'. apply in_sh_bounds in M'; [| clear - MBP; Z.div_mod_to_equations; lia| lia].
destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
+ lits. lia.
+ cbn [ala_client_data a_alayout] in C1. unfold a_client_data in C1. rewrite !SH_eq in M'.
clear - M' C1 MBK MBP. Z.div_mod_to_equations. lia.
+ assert (LU : in_live_user LB0 x) by (destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R]).
pose proof (live_user_heap _ _ _ _ _ _ GC x LU). unfold kLowEnd in *. lits. lia.
+ assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range _ _ _ _ _ _ GC f Hf0) as (R1 & R2 & R3 & R4 & R5). lits. lia.
+ assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
pose proof (frame_shadow_where _ _ _ _ _ _ GC x SHD) as FS'.
eapply (nmap_apart (ae_fs_base RE) A_FS_MAP_SIZE x); [clear - FAL; Z.div_mod_to_equations; lia| unfold A_FS_MAP_SIZE; lia| exact (proj1 FK)| exact FC
| destruct (AVO _ (fs_obj RE X)); cbn [fst snd] in *; lia| exact NM| right; exact FS'].
+ pose proof (SH_mono (mb + msz) band_lo MBC). rewrite SH_eq in *. unfold SH, A_SHADOW_OFS in M'. lits. Z.div_mod_to_equations. lia.
+ cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. rewrite !SH_eq in M'.
clear - M' C1 MBK MBP. Z.div_mod_to_equations. lia.
Qed.
End Z.

Section Z0.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Set Default Proof Using "GC".

Lemma fpSec_RFake : forall x, fp_RSec a RE X x -> fp_RFake FS0 RE X x -> False.
Proof.
intros x FS F. pose proof kconsts as (_ & _ & _ & _ & KP & _).
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (FAL & FK & FC & _ & FQ). cbn [fst snd] in FAL, FK, FC, FQ. unfold iv_disjoint in FQ; cbn [fst snd] in FQ.
rewrite ?KHI_eq in *.
destruct (fp_RFake_zone RE X FS0 x F) as [R|R].
- destruct R as [R1 R2]; cbn [fst snd] in R1, R2. destruct FS as [H|[H|[H|H]]].
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold A_INSTANCE in *. lia.
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold ptrarr_lo in *. lia.
+ destruct H as (e & He & Hx). exact (obj_vs_sec a LB0 FS0 G RE X GC _ e x (fs_obj RE X) He ltac:(split; cbn [fst snd]; lia)
ltac:(pose proof (sec_facts _ _ _ _ _ _ GC e He) as (_ & _ & _ & E4 & E5 & E6 & _); pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]; rewrite <- E4 in M1; lia)).
+ destruct H as (e & He & Hx). pose proof (hdr_band a LB0 FS0 G RE X GC e x He Hx). lia.
- pose proof (fs_band a LB0 FS0 G RE X GC x R) as B. destruct FS as [H|[H|[H|H]]].
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold A_INSTANCE in *. lia.
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & QK & _). rewrite ?KHI_eq in QK. lia.
+ destruct H as (e & He & Hx). pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1. rewrite ?KHI_eq in E2. rewrite KP in *. lia.
+ destruct H as (e & He & Hx). pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & E9).
pose proof (proj1 (List.Forall_forall _ _) E9 _ (fs_obj RE X)) as D. unfold iv_disjoint in D. cbn [fst snd] in D.
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1.
exact (in_sh_disjoint (se_beg e) kPage (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(clear - E1; Z.div_mod_to_equations; lia) ltac:(clear - FAL; Z.div_mod_to_equations; lia)
ltac:(rewrite KP; lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(rewrite KP; unfold A_FS_MAP_SIZE in *; lia) Hx R).
Qed.

Lemma ssec_client : forall LB FS SP x, Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> fp_RSec a RE X x -> False.
Proof.
intros LB FS SP x PB PF CSP CA F.
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
assert (QC : czone LB0 RE x -> False) by (intros CZ; exact (fp_RSec_cz a LB0 FS0 G RE X GC x F CZ)).
assert (QL : x < band_lo) by (destruct (Z.lt_ge_cases x band_lo) as [L|GE]; [exact L| exfalso; apply QC; left; exact GE]).
destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
- lia.
- apply QC. right; left. exact C1.
- apply QC. do 2 right; left. destruct C1 as (b & Hb & R). exists b. split; [eapply Permutation_in; [exact PB| exact Hb]| exact R].
- assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range _ _ _ _ _ _ GC f Hf0) as (R1 & R2 & R3 & R4 & R5).
apply QC. do 3 right; left. split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia.
- assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
apply QC. do 4 right; left. exact (frame_shadow_where _ _ _ _ _ _ GC x SHD).
- apply QC. do 5 right; left. rewrite SH_247 in C1. exact C1.
- cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1.
destruct F as [H|[H|[H|H]]].
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold A_INSTANCE in *. lia.
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & QK & _). rewrite ?KHI_eq in QK. lia.
+ destruct H as (e & He & Hx). pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1. rewrite ?KHI_eq in E2. pose proof kconsts as (_ & _ & _ & _ & KP & _). rewrite KP in *. lia.
+ destruct H as (e & He & Hx). pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & [_ E2] & E3 & E4 & E5 & E6 & _).
pose proof kconsts as (_ & _ & _ & _ & KP & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1.
apply in_sh_bounds in Hx; [| clear - E1; Z.div_mod_to_equations; lia| rewrite KP; lia].
rewrite !SH_eq in Hx. rewrite KP in Hx. clear - Hx C1 E1 E2 E6 M1. destruct E2 as [E2|E2]; Z.div_mod_to_equations; lia.
Qed.
End Z0.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUvT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QJFf.Mq0.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QUvT QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition depot_put_entry : Z := 0x83ab8.
Definition depot_stack : Z := 224.

Definition MM_bytes : list byte := [149%bv; 233%bv; 209%bv; 91%bv; 147%bv; 167%bv; 164%bv; 198%bv]%list.
Definition MM8_bytes : list byte := [168%bv; 76%bv; 143%bv; 222%bv; 154%bv; 60%bv; 37%bv; 53%bv]%list.
Definition MSEED_bytes : list byte := [140%bv; 178%bv; 71%bv; 151%bv; 140%bv; 178%bv; 71%bv; 151%bv]%list.
Lemma depot_consts : forall m, mem_inv asegs m ->
ro_cells asegs m 0x102e8 [CB 8 MM_bytes] /\ ro_cells asegs m 0x10310 [CB 8 MM8_bytes] /\ ro_cells asegs m 0x10418 [CB 8 MSEED_bytes].
Proof.
intros m MI. split; [|split]; (apply (ro_cells_image asegs m); [exact MI| vm_compute; reflexivity| lia| cbn; lia]).
Qed.

Lemma bkt_shift : forall x, 0 <= x < 2^64 -> bv_unsigned (wz (x ≪ 44)) ≫ 42 = 4 * bkt x.
Proof.
intros x Hx. unfold bkt. rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change 1048575 with (Z.ones 20). rewrite Z.land_ones by lia.
change (2 ^ 64) with (2 ^ 20 * 2 ^ 44). rewrite Z.mul_mod_distr_r by lia.
change (2 ^ 44) with (4 * 2 ^ 42). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Lemma bkt_range : forall x, 0 <= bkt x < 2^20.
Proof.
intros x. unfold bkt. change 1048575 with (Z.ones 20). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma take_S_nth : forall {A} (l : list A) i x, nth_error l i = Some x -> take (S i) l = take i l ++ [x].
Proof.
intros A l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
- injection H as ->. reflexivity.
- rewrite (IH i x H). reflexivity.
Qed.

Lemma skipn_cons_nth : forall {A} (l : list A) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
intros A l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
- injection H as ->. reflexivity.
- apply IH. exact H.
Qed.

Lemma srliw16_small : forall s, 0 <= s < 65536 -> bv_swrap 32 (bv_wrap 32 s ≫ 16) = 0.
Proof.
intros s Hs. unfold bv_wrap. change (bv_modulus 32) with 4294967296. rewrite Z.mod_small by lia.
rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.

Lemma zext32_small : forall s, 0 <= s < 2^32 -> bv_unsigned (wz (s ≪ 32)) ≫ 32 = s.
Proof.
intros s Hs. rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.mul_mod_distr_r, Z.div_mul by lia. apply Z.mod_small. lia.
Qed.

Ltac if_lit2 :=
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota end.

Lemma land_m16_small : forall x, 0 <= x < 16 -> Z.land x 18446744073709551600 = 0.
Proof.
intros x Hx.
assert (E : 18446744073709551600 = Z.ldiff (Z.ones 64) (Z.ones 4)) by reflexivity. rewrite E, land_ldiff_distr_r.
rewrite Z.land_ones, Z.mod_small by lia. rewrite Z.ldiff_ones_r, Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.

Lemma amoadd_w_bytes : forall (st c : Z), 0 <= st -> 0 <= c -> st + c < 2^32 ->
Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 st)))) (low32 (Z_to_bv 64 c)))) = le4 (Z_to_bv 64 (st + c)).
Proof.
intros st c Hs Hc Hsc. cbv [amo_val]. rewrite bv_add_unsigned. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
unfold low32. rewrite extract_low_mod by lia. rewrite !unsigned_lit by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite !Z.mod_small by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia.
unfold le4. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma lxor_pow20 : forall a, 0 <= a < 2^20 -> Z.lxor a 1048576 = a + 1048576.
Proof.
intros a Ha. symmetry. apply Z.add_nocarry_lxor.
replace a with (Z.land a (Z.ones 20)) by (rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite <- Z.land_assoc. change (Z.land (Z.ones 20) 1048576) with 0. apply Z.land_0_r.
Qed.

Tactic Notation "call_pre" uconstr(SPEC) := eapply evt_cut; [eapply SPEC|].
Ltac post_later := match goal with MU : munch _ _ ?mc |- forall ms', _ -> _ => post_call_u asegs mc end.

Lemma zseq_snoc : forall n, 0 <= n -> zseq (n + 1) = zseq n ++ [n + 1].
Proof.
intros n Hn. unfold zseq. replace (Z.to_nat (n + 1)) with (Z.to_nat n + 1)%nat by lia.
rewrite seq_app, map_app. cbn [map seq]. f_equal. f_equal. lia.
Qed.

Lemma NoDup_snoc : forall {A} (l : list A) x, List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof.
intros A l x ND NI. induction l as [|y l IH]; cbn.
- constructor; [intros []| constructor].
- inversion ND; subst. constructor.
+ rewrite in_app_iff. cbn. intros [H|[H|[]]]; [contradiction| subst; apply NI; left; reflexivity].
+ apply IH; [assumption| intros H; apply NI; right; exact H].
Qed.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma hash_loop : forall (k : nat) (ws : list word) (i : Z) (h : word) (src cur fin : Z) m
(ra sp gp tp t0 t1 t2 s0 s1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
cur = src + 8 * i -> fin = src + 8 * Z.of_nat (length ws) ->
mem_inv asegs m -> u64arr asegs m src ws -> Z.of_nat k = Z.of_nat (length ws) - i -> 0 <= i < Z.of_nat (length ws) ->
0 <= src -> src + 8 * Z.of_nat (length ws) < 2^64 ->
evt asegs (fun ms' => exists a5' a6',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MM) (wz fin) (fold_left hstepw (skipn (Z.to_nat i) ws) h) a3
(wz fin) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x83b8c) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MM) (wz cur) h a3 (wz fin) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x83b68) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until fc; intros -> -> MI Q Hk Hi S0 S1; [lia|].
destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; lia].
pose proof (u64arr_read asegs m src ws i w (wa (src + 8 * i)) Q NTH ltac:(lia) eq_refl) as RD.
rewrite (skipn_cons_nth ws (Z.to_nat i) w NTH). cbn [fold_left].
unfold MM. do 8 istep. istep.
destruct (Z.lt_ge_cases (i + 1) (Z.of_nat (length ws))) as [LT|GE].
- if_true_u.
replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
eapply (IH ws (i + 1)); [| | exact MI| exact Q| lia| lia| lia| lia]; lia.
- if_false_u. apply evt_done. do 2 eexists.
replace (src + 8 * i + 8) with (src + 8 * Z.of_nat (length ws)) by lia.
rewrite skipn_all2 by lia. cbn [fold_left]. reflexivity.
Qed.

Definition find_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(H n : Z) (nh : Z -> Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' =>
(exists (sF : Z) (a1 a2 : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz sF) a1 a2 a3 a4 a5 a6 a7 s2 (wz H) s4 s5 (wz 65535) s7 (wz DP_MAP1) s9 s10 s11 t3 t4 t5 t6)
F (wz 0x83cfc) fc None m (seg_rom asegs)
/\ 1 <= sF <= n /\ nh sF = H)
\/ (exists (a0 a2 : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) a2 a3 a4 a5 a6 a7 s2 (wz H) s4 s5 (wz 65535) s7 (wz DP_MAP1) s9 s10 s11 t3 t4 t5 t6)
F (wz 0x83c50) fc None m (seg_rom asegs)
/\ forall j, 1 <= j <= n -> nh j <> H).

Lemma find_loop : forall (k : nat) (s : Z) (H n : Z) (nh ns : Z -> Z) m
(ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
mem_inv asegs m ->
rw_cells asegs m DP_MAP1 [C8 (wz (rl_dn X))] ->
(forall i, 1 <= i <= n ->
rw_cells asegs m (rl_dn X + 16 * i) [C8 (wz (nh i)); C4 (wz (lastb nh (bkt (nh i)) (Z.to_nat (i - 1)))); C4 (wz (ns i))]) ->
(forall i, 1 <= i <= n -> 0 <= nh i < 2^64) -> 0 <= H < 2^64 ->
1 <= n < 65536 -> 0 < rl_dn X -> rl_dn X + 0x100000 <= band_lo ->
s <= Z.of_nat k -> (s = 0 \/ (1 <= s <= n /\ bkt (nh s) = bkt H)) ->
(forall j, s < j <= n -> bkt (nh j) = bkt H -> nh j <> H) ->
evt asegs (find_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 F fc H n nh m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz s) a2 a3 a4 a5 a6 a7 s2 (wz H) s4 s5 (wz 65535) s7 (wz DP_MAP1) s9 s10 s11 t3 t4 t5 t6)
F (wz 0x83bf8) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until fc; intros MI CMAP CND NHR HR NR D1 D2 SK SH CHK.
- assert (s = 0) as -> by lia.
istep. if_true. apply evt_done. right. do 2 eexists. split; [reflexivity|].
intros j Hj E. destruct (Z.eq_dec (bkt (nh j)) (bkt H)) as [B|B]; [exact (CHK j ltac:(lia) B E)| apply B; rewrite E; reflexivity].
- destruct SH as [->|[SR SB]].
{ istep. if_true. apply evt_done. right. do 2 eexists. split; [reflexivity|].
intros j Hj E. destruct (Z.eq_dec (bkt (nh j)) (bkt H)) as [B|B]; [exact (CHK j ltac:(lia) B E)| apply B; rewrite E; reflexivity]. }
rewrite ?KHI_eq in D1. idtac. unfold DP_MAP1 in *.
pose proof (CND s ltac:(lia)) as NODE. pose proof (NHR s ltac:(lia)) as HS.
pose proof (lastb_range nh (bkt (nh s)) (Z.to_nat (s - 1))) as LR.
istep. if_false_u. istep. istep. rewrite (unsigned_lit s), srliw16_small by lia.
do 4 istep. if_false_u.
istep. istep. rewrite (unsigned_lit s), (zext32_small s) by lia.
istep. rewrite (unsigned_lit s) by lia. replace (Z.land s 65535) with s by (change 65535 with (Z.ones 16); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
istep. rewrite (unsigned_lit s), (Z.shiftl_mul_pow2 s 4) by lia. change (2 ^ 4) with 16. rewrite (Z.mul_comm s 16).
istep. remember (rl_dn X + 16 * s) as node eqn:En in |- *. rewrite <- En in NODE.
istep. istep. rewrite (sx32_small (lastb nh (bkt (nh s)) (Z.to_nat (s - 1)))) by lia.
clear NODE. subst node.
istep. if_cases E; zify_cond E.
+
rewrite ?(unsigned_lit H), ?(unsigned_lit (nh s)) in E by lia.
eapply (IH (lastb nh (bkt (nh s)) (Z.to_nat (s - 1)))); try eassumption; try lia.
* destruct (Z.eq_dec (lastb nh (bkt (nh s)) (Z.to_nat (s - 1))) 0) as [Z0|NZ]; [left; exact Z0| right].
split; [lia|]. rewrite (lastb_bkt nh (bkt (nh s)) (Z.to_nat (s - 1)) NZ). exact SB.
* intros j Hj Bj. destruct (Z.lt_ge_cases s j) as [LT|GE]; [apply CHK; lia|].
destruct (Z.eq_dec j s) as [->|NE]; [lia|].
exfalso. apply (lastb_max nh (bkt (nh s)) (Z.to_nat (s - 1)) j ltac:(lia)). rewrite Bj, SB. reflexivity.
+
rewrite ?(unsigned_lit H), ?(unsigned_lit (nh s)) in E by lia.
istep. apply evt_done. left. exists s. do 2 eexists. split; [reflexivity|]. split; [lia| symmetry; exact E].
Qed.

Lemma lock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (B v : Z),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells asegs m B [C4 (wz v)] -> 0 <= v < 2^31 -> B mod 4 = 0 -> 0 <= B -> B + 4 <= band_lo ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 4)] lo m
(fun a0' m' => a0' = wz v /\ exists lw : word, rw_cells asegs m' B [C4 lw]))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz B) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x8424c) fc None m (seg_rom asegs)).
Proof.
intros until v; intros MI ST CEIL LO TB VR BAL BLO BHI. pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (AMO : amo_aligned AW (wz B) = true) by (apply amo_aligned_intro4; lia).
carve_frame 48%nat ST.
step_until 0x84278. rewrite (sx32_small v) by lia.
istep. rewrite bv_lts_zero_r. if_true_u.
istep. amo_step AMO. rewrite (sx32_small v) by lia.
istep. if_false_u.
amo_step AMO.
istep. if_false. istep. if_true_u. step_until 0.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity| eexists; exact TB].
Qed.

Lemma shl44_shr41 : forall x, 0 <= x < 2^20 -> bv_unsigned (wz (x ≪ 44)) ≫ 41 = 8 * x.
Proof.
intros x Hx. rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite Z.mod_small by (change (2 ^ 64) with (2 ^ 20 * 2 ^ 44); nia).
change (2 ^ 44) with (8 * 2 ^ 41). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Lemma alloc_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (tf j40 ssb st cnt idxp pk : Z) (iw : word),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
rw_cells asegs m 0x1c19c8 [C8 (wz tf); C8 (wz j40); C8 (wz ssb); C4 (wz st)] ->
rw_cells asegs m idxp [C8 iw] ->
0 <= tf -> 2 <= cnt <= 31 -> tf + cnt < 2^20 -> 0x645000 <= ssb < 2^47 -> 0 <= st < 2^32 ->
bv_unsigned sp <= idxp -> idxp + 8 < 2^64 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp); (0x1c19c8, 0x1c19c8 + 8); (idxp, idxp + 8)] lo m
(fun a0' m' => a0' = wz (ssb + 8 * tf)
/\ rw_cells asegs m' 0x1c19c8 [C8 (wz (tf + cnt)); C8 (wz j40); C8 (wz ssb); C4 (wz st)]
/\ rw_cells asegs m' idxp [C8 (wz tf)]))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0x1c19c8) (wz cnt) (wz idxp) (wz pk) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x815e0) fc None m (seg_rom asegs)).
Proof.
intros until iw; intros MI ST CEIL LO SSC IDX TF CNT ROOM SSB STR IP1 IP2. pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (1841608, 1841608 + 8); (idxp, idxp + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (AMO : amo_aligned AD (wz 1841608) = true) by (apply amo_aligned_intro8; [lia| reflexivity]).
carve_frame 16%nat ST.
step_until 0x815f4. amo_step AMO.
cbv [amo_val] in SSC. rewrite bv_add_canon in SSC. rewrite !unsigned_lit in SSC by lia.
step_until 0. rewrite ?(unsigned_lit tf), ?(unsigned_lit (cnt + -1 + tf)), ?Z.shiftr_div_pow2 by lia. change (2 ^ 20) with 1048576.
rewrite (Z.div_small tf 1048576), (Z.div_small (cnt + -1 + tf) 1048576) by lia.
if_false_u. step_until 0. rewrite ?(unsigned_lit tf), ?Z.shiftr_div_pow2, ?(Z.div_small tf (2 ^ 32)) by lia. if_lit2.
step_until 0. if_false_u.
step_until 0x81648. rewrite ?(unsigned_lit tf), (shl44_shr41 tf) by lia.
step_until 0. release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|]. split; [exact SSC| exact IDX].
Qed.

Lemma memcpy_loop : forall (k : nat) (i : Z) (dst src n cd cs : Z) (ds bs : list byte) m
(ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc lo,
cd = dst + i -> cs = src + i ->
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
u8arr asegs m dst ds -> Z.of_nat (length ds) = n -> u8ro asegs m src bs -> n <= Z.of_nat (length bs) ->
take (Z.to_nat i) ds = take (Z.to_nat i) bs ->
Z.of_nat k = n - i -> 0 <= i < n -> 0 <= dst -> 0 <= src -> dst + n < 2^64 -> src + Z.of_nat (length bs) < 2^64 ->
(src + Z.of_nat (length bs) <= dst \/ dst + n <= src) -> (dst + n <= lo \/ bv_unsigned sp <= dst) ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(dst, dst + n)] lo m
(fun _ m' => u8arr asegs m' dst (take (Z.to_nat n) bs) /\ u8ro asegs m' src bs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz cs) (wz (dst + n)) (wz cd) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x74f00) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until lo; intros -> -> MI ST DA LD SB LB TK Hk Hi D0 S0 D1 S1 DISJ STKD; [lia|].
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
pose proof (munch_refl [(dst, dst + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:NTH; [| apply nth_error_None in NTH; lia].
pose proof (u8ro_read asegs m src bs i b (wa (src + i)) SB NTH ltac:(lia) eq_refl) as RD.
istep.
pose proof (u8arr_store_ok asegs m dst ds i (wa (dst + i)) DA ltac:(lia) eq_refl) as SOK.
step. rewrite le1_zxb.
pose proof (u8arr_write asegs m dst ds i b DA ltac:(lia)) as DA1. clear DA. store_done.
assert (TK1 : take (Z.to_nat (i + 1)) (upd ds (Z.to_nat i) b) = take (Z.to_nat (i + 1)) bs).
{ replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite take_upd_snoc by lia. rewrite TK.
rewrite (take_S_nth bs (Z.to_nat i) b NTH). reflexivity. }
istep. istep. istep.
destruct (Z.lt_ge_cases (i + 1) n) as [LT|GE].
- if_true_u.
eapply evt_mono.
{ eapply (IH (i + 1) dst src n _ _ (upd ds (Z.to_nat i) b) bs); try eassumption; try lia. rewrite upd_length. exact LD. }
cbv beta. intros ms' PO. unfold rpost in PO |- *. destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & E & MU' & WM' & REST).
do 16 eexists. split; [exact E|]. split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. exact REST.
- if_false_u. istep.
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
split; [| assumption]. replace (Z.to_nat n) with (Z.to_nat (i + 1)) by lia. rewrite <- TK1.
rewrite take_ge by (rewrite upd_length; lia). exact DA1.
Qed.

Lemma memcpy_spec : forall (dst src n : Z) (ds bs : list byte) m
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc lo,
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
u8arr asegs m dst ds -> Z.of_nat (length ds) = n -> u8ro asegs m src bs -> n <= Z.of_nat (length bs) ->
0 < n -> 0 <= dst -> 0 <= src -> dst + n < 2^64 -> src + Z.of_nat (length bs) < 2^64 ->
(src + Z.of_nat (length bs) <= dst \/ dst + n <= src) -> (dst + n <= lo \/ bv_unsigned sp <= dst) ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(dst, dst + n)] lo m
(fun _ m' => u8arr asegs m' dst (take (Z.to_nat n) bs) /\ u8ro asegs m' src bs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz src) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x74ef4) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros MI ST DA LD SB LB NP D0 S0 D1 S1 DISJ STKD.
istep. if_false_u. istep. istep.
eapply (memcpy_loop (Z.to_nat n) 0 dst src n dst src); try eassumption; try lia. reflexivity.
Qed.

Lemma cb_u8arr : forall m A n bs, rw_cells asegs m A [CB n bs] -> u8arr asegs m A bs.
Proof.
intros m A n bs [[WF BA] WR]. cbn in WF. destruct WF as [L _]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
cbn [cells_size csize Nat.add] in WR. rewrite Nat.add_0_r in WR. split; [exact BA|]. rewrite L. exact WR.
Qed.

Lemma le8_split32 : forall x, 0 <= x < 2^32 -> le8 (wz x) = le4 (wz x) ++ le4 (wz 0).
Proof.
intros x Hx. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app].
rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite !Z.shiftr_div_pow2 by lia.
rewrite ?(Z.div_small x (2 ^ 32)), ?(Z.div_small x (2 ^ 40)), ?(Z.div_small x (2 ^ 48)), ?(Z.div_small x (2 ^ 56)) by lia.
replace (x / 2 ^ (8 + 8 + 8 + 8 + 8 + 8 + 8)) with 0 by (symmetry; apply Z.div_small; lia).
reflexivity.
Qed.

Lemma rw_C8_split32 : forall m A x pre post, 0 <= x < 2^32 ->
rw_cells asegs m A (pre ++ C8 (wz x) :: post) -> rw_cells asegs m A (pre ++ C4 (wz x) :: C4 (wz 0) :: post).
Proof.
intros m A x pre post Hx H. eapply rw_cells_recast'; [exact H| |].
- destruct H as [[WF _] _]. apply cells_wf_app in WF as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn. cbn in W2. tauto.
- rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite (le8_split32 x Hx). rewrite <- !app_assoc. reflexivity.
Qed.

Lemma sstore_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (ap pp tr sz tf j40 ssb st : Z) (q : list word) (pw : word),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 80 ->
rw_cells asegs m ap [C8 (wz tr); C4 (wz sz); C4 (wz 0)] ->
rw_cells asegs m pp [C8 pw] ->
u64arr asegs m tr q -> Z.of_nat (length q) = 30 ->
rw_cells asegs m 0x1c19c8 [C8 (wz tf); C8 (wz j40); C8 (wz ssb); C4 (wz st)] ->
hjunk m ssb (ssb + 0x800000) ->
1 <= sz <= 30 -> 0 <= tf -> tf + 31 < 2^20 -> 0 <= st <= tf ->
ssb mod 8 = 0 -> 0x645000 <= ssb -> ssb + 0x800000 <= band_lo ->
bv_unsigned sp <= pp -> pp + 8 <= ap -> ap + 16 <= tr -> tr + 240 < 2^64 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned sp - 80, bv_unsigned sp); (pp, pp + 8); (0x1c19c8, 0x1c19c8 + 32); (ssb, ssb + 0x800000)] lo m
(fun a0' m' => a0' = wz (tf + 1)
/\ rw_cells asegs m' 0x1c19c8 [C8 (wz (tf + sz + 1)); C8 (wz j40); C8 (wz ssb); C4 (wz (st + sz + 1))]
/\ rw_cells asegs m' pp [C8 (wz 0)]
/\ rw_cells asegs m' ap [C8 (wz tr); C4 (wz sz); C4 (wz 0)]
/\ u64arr asegs m' tr q))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0x1c19c8) (wz ap) (wz pp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x814bc) fc None m (seg_rom asegs)).
Proof.
intros until pw; intros MI ST CEIL LO ARGS PACK TRQ LQ SSC JS SZ TF ROOM STR AL8 SLO SHI PP1 PP2 AP2 TR2.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (pp, pp + 8); (0x1c19c8, 0x1c19c8 + 32); (ssb, ssb + 0x800000)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 64%nat ST.
step_until 0x814e8. rewrite ?(sx32_small sz), ?(sx32_small 0) by lia.
step_until 0. if_true_u. step_until 0. if_false_u. step_until 0. if_true_u.
step_until 0x815e0.
lazymatch type of FR with rw_cells _ ?mc _ (?c0 :: ?rest) =>
destruct (proj1 (rw_cells_app asegs mc _ [c0] rest) FR) as [IDX FR'] end.
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR'.
replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in FR' by lia. clear FR.
call_u (alloc_spec).
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact SSC. } { exact IDX. }
{ lia. } { lia. } { lia. } { lia. } { lia. } { unsigned_lits. lia. } { unsigned_lits. lia. }
match goal with H : rw_cells asegs _ 1841608 _ |- _ => rename H into SSC' end.
match goal with H : rw_cells asegs _ (bv_unsigned sp + -64) _ |- _ => rename H into IDX' end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
istep. if_false_u.

pose proof (hjunk_wmono _ _ _ _ JS WM) as JSc.
pose proof (fun Hm => proj2 (hjunk_split _ _ (ssb + 8 * tf) _ JSc Hm)) as J1. specialize (J1 ltac:(lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (ssb + 8 * tf) (ssb + 8 * tf + Z.of_nat 8) _ J1 Hm)) as JH. specialize (JH ltac:(cbn; lia)).
destruct (hjunk_cells _ (ssb + 8 * tf) 8 JH) as [junkh SLOT].
pose proof (fun Hm => proj2 (hjunk_split _ _ (ssb + 8 * tf + 8) _ J1 Hm)) as J2. specialize (J2 ltac:(lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (ssb + 8 * tf + 8) (ssb + 8 * tf + 8 + Z.of_nat (Z.to_nat (8 * sz))) _ J2 Hm)) as JD.
specialize (JD ltac:(rewrite Z2Nat.id by lia; lia)).
destruct (hjunk_cells _ (ssb + 8 * tf + 8) (Z.to_nat (8 * sz)) JD) as [junkd DST]. clear JSc J1 JH J2 JD.
pose proof (cb_u8arr _ _ _ _ DST) as DSTA. assert (LJD : Z.of_nat (length junkd) = 8 * sz) by (destruct DST as [[[L _] _] _]; cbn in L; lia). clear DST.
remember (ssb + 8 * tf) as slot eqn:Eslot. rewrite <- ?Eslot in SLOT, DSTA.
assert (SLB : ssb <= slot /\ slot + 48 <= ssb + 0x800000) by (subst slot; lia).
do 3 istep. rewrite ?(sx32_small sz), ?(unsigned_lit sz), (Z.lor_0_l sz) by lia.
istep. istep. istep. rewrite ?(unsigned_lit sz), (Z.shiftl_mul_pow2 sz 3) by lia. change (2 ^ 3) with 8. rewrite (Z.mul_comm sz 8).
assert (LQ8 : Z.of_nat (length (u64s q)) = 240) by (rewrite u64s_length; lia).
istep. call_u (memcpy_spec (slot + 8) tr (8 * sz) junkd (u64s q)).
{ assumption. } { unsigned_lits. exact ST. } { exact DSTA. } { exact LJD. } { exact (proj1 TRQ). }
{ lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { unsigned_lits. lia. }
match goal with H : u8ro asegs _ tr _ |- _ => rename H into TRB end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.

istep. istep. istep. rewrite ?(unsigned_lit tf), ?Z.shiftr_div_pow2 by lia.
rewrite (unsigned_lit (tf / 2 ^ 16)) by (Z.div_mod_to_equations; lia).
rewrite (land_m16_small (tf / 2 ^ 16)) by (change (2 ^ 16) with 65536; Z.div_mod_to_equations; lia).
istep. istep.
assert (AMO4 : amo_aligned AW (wz 1841632) = true) by (apply amo_aligned_intro4; [lia| reflexivity]).
amo_step AMO4. rewrite (amoadd_w_bytes st (sz + 1)) by lia. mem_after_store. rewrite ?sext_extract_le4, ?(sx32_small st) by lia.
do 4 istep. rewrite ?(unsigned_lit st), (zext32_small st) by lia.
istep.
apply (rw_C8_split32 _ _ tf [] _) in IDX'; [| lia]. cbn [app] in IDX'.
istep. rewrite ?(sx32_small tf) by lia.
istep. rewrite (unsigned_lit (sz + 1 + st)) by lia. istep.
rewrite (lxor_pow20 (sz + 1 + st)) by lia. rewrite v_sltiu_b2z, unsigned_lit by lia.
replace (sz + 1 + st + 1048576 <? bv_wrap 64 1) with false by (symmetry; apply Z.ltb_ge; change (bv_wrap 64 1) with 1; lia). cbn [Z.b2z].
step_until 0x81594. istep. rewrite ?(sx32_small tf), (addiw_small tf 1) by lia.
step_until 0.
replace (bv_unsigned sp + -56) with (bv_unsigned sp + -64 + 8) in FR' by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (proj2 (rw_cells_app asegs mc (bv_unsigned sp + -64) [C4 (wz tf); C4 (wz 0)] _) (conj IDX' FR')) as FR end.
cbn [app] in FR. clear IDX' FR'. release_frame FR PC (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [reflexivity|].
replace (tf + sz + 1) with (tf + (sz + 1)) by lia. replace (st + sz + 1) with (st + (sz + 1)) by lia.
split; [exact SSC'|]. split; [exact PACK|]. split; [exact ARGS| exact TRQ].
Qed.

Lemma nstore_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (node ap tr sz tf j40 ssb st H : Z) (q : list word) (nj : list byte),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 112 ->
rw_cells asegs m node [CB 16 nj] ->
rw_cells asegs m ap [C8 (wz tr); C4 (wz sz); C4 (wz 0)] ->
u64arr asegs m tr q -> Z.of_nat (length q) = 30 ->
rw_cells asegs m 0x1c19c8 [C8 (wz tf); C8 (wz j40); C8 (wz ssb); C4 (wz st)] ->
hjunk m ssb (ssb + 0x800000) ->
1 <= sz <= 30 -> 0 <= tf -> tf + 31 < 2^20 -> 0 <= st <= tf -> 0 <= H < 2^64 ->
ssb mod 8 = 0 -> 0x645000 <= ssb -> ssb + 0x800000 <= band_lo -> 0x645000 <= node -> node + 16 <= band_lo ->
(node + 16 <= ssb \/ ssb + 0x800000 <= node) ->
bv_unsigned sp <= ap -> ap + 16 <= tr -> tr + 240 < 2^64 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned sp - 112, bv_unsigned sp); (node, node + 16); (0x1c19c8, 0x1c19c8 + 32); (ssb, ssb + 0x800000)] lo m
(fun a0' m' => exists nj4 : list byte, a0' = wz (tf + 1)
/\ rw_cells asegs m' node [C8 (wz H); CB 4 nj4; C4 (wz (tf + 1))]
/\ rw_cells asegs m' 0x1c19c8 [C8 (wz (tf + sz + 1)); C8 (wz j40); C8 (wz ssb); C4 (wz (st + sz + 1))]
/\ rw_cells asegs m' ap [C8 (wz tr); C4 (wz sz); C4 (wz 0)]
/\ u64arr asegs m' tr q))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz node) a1 (wz ap) (wz H) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x837d0) fc None m (seg_rom asegs)).
Proof.
intros until nj; intros MI ST CEIL LO NODE ARGS TRQ LQ SSC JS SZ TF ROOM STR HR AL8 SLO SHI NLO NHI NSS AP1 AP2 TR2.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (node, node + 16); (0x1c19c8, 0x1c19c8 + 32); (ssb, ssb + 0x800000)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
step_until 0x814bc.
lazymatch type of FR with rw_cells _ ?mc _ (?c0 :: ?c1 :: ?rest) =>
destruct (proj1 (rw_cells_app asegs mc _ [c0] (c1 :: rest)) FR) as [FRa FRb];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRb;
destruct (proj1 (rw_cells_app asegs mc _ [c1] rest) FRb) as [PK FRc];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRc end.
replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in PK, FRc by lia.
replace (bv_unsigned sp + -24 + 8) with (bv_unsigned sp + -16) in FRc by lia. clear FR FRb.
call_pre (sstore_spec).
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact ARGS. } { exact PK. } { exact TRQ. } { exact LQ. }
{ exact SSC. } { eapply hjunk_wmono; [exact JS| exact WM]. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { idtac. lia. }
{ unsigned_lits. lia. } { unsigned_lits. lia. } { lia. } { lia. }
post_later.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
match goal with H : rw_cells asegs _ 1841608 _ |- _ => rename H into SSC' end.
match goal with H : rw_cells asegs _ (bv_unsigned sp + -24) _ |- _ => rename H into PK' end.
match goal with H : rw_cells asegs _ ap _ |- _ => rename H into ARGS' end.
match goal with H : u64arr asegs _ tr _ |- _ => rename H into TRQ' end.
istep. istep. step_until 0. if_lit2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
replace (bv_unsigned sp + -24) with (bv_unsigned sp + -32 + 8) in PK' by lia;
pose proof (proj2 (rw_cells_app asegs mc (bv_unsigned sp + -32) [_] _) (conj FRa PK')) as FRab; cbn [app] in FRab;
replace (bv_unsigned sp + -16) with (bv_unsigned sp + -32 + 16) in FRc by lia;
pose proof (proj2 (rw_cells_app asegs mc (bv_unsigned sp + -32) [_; _] _) (conj FRab FRc)) as FR; cbn [app] in FR end.
clear FRa PK' FRc FRab.
step_until 0. release_frame FR ST' (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST'|].
eexists. split; [reflexivity|]. split; [exact NODE|]. split; [exact SSC'|]. split; [exact ARGS'| exact TRQ'].
Qed.

Lemma u64arr_take : forall m A ws k, u64arr asegs m A ws -> u64arr asegs m A (take k ws).
Proof.
intros m A ws k [BA WR]. rewrite <- (firstn_skipn k ws) in BA, WR. rewrite u64s_app in BA. apply bytes_at_app in BA as [BA _].
split; [exact BA|]. rewrite length_app in WR. destruct WR as (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros i Hi. apply W3. lia.
Qed.

Lemma depot_put_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (tr sz dn : Z) (q : list word),
rlay_ok RE X -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - depot_stack ->
u64arr asegs m tr q -> Z.of_nat (length q) = 30 ->
1 <= sz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= tr -> tr + 240 < 2^64 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned sp - depot_stack, bv_unsigned sp); (SS_BASE, DP_END); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000)] lo m
(fun a0' m' => exists id, a0' = wz id /\ 1 <= id < 2^16 /\ RDepot RE X m' /\ u64arr asegs m' tr q /\ exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz tr) (wz sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz depot_put_entry) fc None m (seg_rom asegs)).
Proof.
intros until q; intros RL RD MI ST CEIL LO TRQ LQ SZR0 DNH CAPN TR1 TR2.
pose (ks := map bv_unsigned (take (Z.to_nat sz) q)).
assert (LKS : length ks = Z.to_nat sz) by (unfold ks; rewrite length_map, length_take; lia).
assert (TK : take (length ks) q = map wz ks).
{ rewrite LKS. unfold ks. rewrite map_map. rewrite (map_ext (fun w : word => wz (bv_unsigned w)) (fun w => w)) by (intros w; apply Z_to_bv_bv_unsigned). rewrite map_id. reflexivity. }
assert (SZ : sz = Z.of_nat (length ks)) by lia.
clearbody ks. clear LKS.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
destruct RD as (n & tf & st & h0 & j40 & nh & ns & N1 & STR & TFR & HU & ND & DA & DK & DC & SA & SK & SC & TK1 & TC
& SSC & CTAB & CN & CMAP & CND & JD & JS & TU).
pose proof (depot_capacity n h0 nh ltac:(lia) (fun i Hi => proj1 (HU i Hi)) ND) as CAP.
rewrite ?KHI_eq in DK, SK, TK1. idtac.
pose proof (rlay_pd RE X RL) as PD. pd_pair PD 0 1 DTD. pd_pair PD 0 2 DTS. pd_pair PD 2 0 DNS. clear PD.
unfold depot_put_entry, depot_stack, SS_BASE, DP_END, DP_TAB, DP_N, DP_MAP1 in *.
assert (SZR : 1 <= sz <= 30) by exact SZR0.
assert (DN0 : depot_n asegs m n) by (split; [exact CN| exact N1]).
assert (EDN : n = dn) by (eapply (depot_n_fun m); [exact DN0| exact DNH| lia| unfold DEPOT_CAP in CAPN; lia]). subst dn.
assert (CAPN1 : n + 1 <= 32000) by (unfold DEPOT_CAP in CAPN; exact CAPN).
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (1841608, 6363632); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000)] m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MUs.
pose proof (wmono_refl asegs m) as WM.
destruct (depot_consts m MI) as (K1 & K2 & K3). unfold MM_bytes, MM8_bytes, MSEED_bytes in K1, K2, K3.
step_until 0x83ad8.
carve_frame 112%nat ST.
step_until 0. if_lit2.
step_until 0. rewrite ?(unsigned_lit sz), ?(swrap32_small (sz + 0)), ?Z.add_0_r by lia. if_false_u.
istep. if_false_u.

step_until 0x83b68.
rewrite !(unsigned_lit sz) by lia. replace (Z.land sz 4294967295) with sz by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite !(unsigned_lit sz), (Z.shiftl_mul_pow2 sz 3) by lia. change (2 ^ 3) with 8.
assert (HI : hinitw (wz sz) = wz (Z.lxor (bv_unsigned (wz (sz * MM8))) MSEED)).
{ unfold hinitw. rewrite !(unsigned_lit sz) by lia.
replace (Z.land sz 4294967295) with sz by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite !(unsigned_lit sz) by lia. reflexivity. }
unfold MM8, MSEED in HI. rewrite <- HI. clear HI.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
assert (TRKc : u64arr asegs mc' tr (map wz ks)) by (rewrite <- TK; apply u64arr_take; assumption) end.
eapply evt_cut.
{ eapply (hash_loop (Z.to_nat sz) (map wz ks) 0); try eassumption; rewrite ?length_map; lia. }
cbv beta. intros ms' (a5' & a6' & ->). cbn [Z.to_nat skipn]. unfold MM at 1.
rewrite (Z.shiftr_div_pow2 sz 32), (Z.div_small sz (2 ^ 32)) by lia.
replace (skipn (Z.to_nat 0) (map wz ks)) with (map wz ks) by reflexivity.
step_until 0x83bd8.
lazymatch goal with |- context [bv_unsigned (wz (bv_unsigned ?w ≪ 44)) ≫ 42] => remember w as HW eqn:EHW end.
assert (EH : hfinw (fold_left hstepw (map wz ks) (hinitw (wz sz))) = HW) by (rewrite EHW; reflexivity). clear EHW.
pose proof (bv_unsigned_in_range 64 HW) as HR. change (bv_modulus 64) with (2^64)%Z in HR.
rewrite (bkt_shift (bv_unsigned HW)) by lia.
set (H := bv_unsigned HW) in *. set (b := bkt H) in *. pose proof (bkt_range H) as BR. fold b in BR.
assert (DH : dhash ks = H) by (unfold dhash, H; rewrite <- EH, SZ; reflexivity).

set (v := lastb nh b (Z.to_nat n)). pose proof (lastb_range nh b (Z.to_nat n)) as VR. fold v in VR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TB : rw_cells asegs mc (1907160 + 4 * b) [C4 (wz v)])
by (eapply rw_cells_transport; [exact (CTAB b BR)| exact MUs| exact WM| cbn; lia]) end.
remember (1907160 + 4 * b) as tba eqn:Etba.
istep. rewrite (sx32_small v) by lia.
step_until 0x83bf8.
rewrite ?(unsigned_lit v) by lia. replace (Z.land v 2147483647) with v by (change 2147483647 with (Z.ones 31); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite <- (Z_to_bv_lit_self HW). fold H.

eapply evt_cut.
{ lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (find_loop (Z.to_nat v) v H n nh ns mc) end.
- assumption.
- exact CMAP.
- intros i Hi. eapply rw_cells_transport; [exact (CND i Hi)| exact MUs| exact WM| cbn; lia].
- intros i Hi. exact (proj2 (HU i Hi)).
- subst H. lia.
- lia. - rewrite ?KHI_eq. lia. - idtac. lia. - lia.
- destruct (Z.eq_dec v 0) as [Z0|NZ]; [left; exact Z0| right]. split; [lia|]. unfold v. rewrite (lastb_bkt nh b (Z.to_nat n)) by (fold v; lia). reflexivity.
- intros j Hj Bj. exfalso. apply (lastb_max nh b (Z.to_nat n) j ltac:(fold v; lia)). exact Bj. }
cbv beta. intros ms' [FOUND|MISS].
{
destruct FOUND as (sF & a1' & a2' & -> & SFR & SFH).
step_until 0. release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
exists sF. split; [reflexivity|]. split; [lia|]. split; [| split; [exact TRQ| exists n; split; [eapply (depot_keep_of_munch asegs _ m); [exact MUs| exact WM| repeat constructor; cbn [fst snd]; unfold DP_N; lia| exact DN0]| lia]]].
exists n, tf, st, h0, j40, nh, ns. unfold SS_BASE, DP_TAB, DP_N, DP_MAP1. repeat (split; [assumption|]).
split. { intros b' Hb'. eapply rw_cells_transport; [exact (CTAB b' Hb')| exact MUs| exact WM| cbn; lia]. }
repeat (split; [assumption|]).
split. { intros i Hi. eapply rw_cells_transport; [exact (CND i Hi)| exact MUs| exact WM| cbn; lia]. }
split; [eapply hjunk_wmono; [exact JD| exact WM]|]. split; [eapply hjunk_wmono; [exact JS| exact WM]|]. exact TU. }
destruct MISS as (a0' & a2' & -> & NOTIN). unfold DP_MAP1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eassert (MUf : munch [(bv_unsigned sp - 224, bv_unsigned sp); (tba, tba + 4); (6101464, 6101468);
(rl_dn X + 16 * (n + 1), rl_dn X + 16 * (n + 1) + 16); (1841608, 1841640); (rl_ssb X, rl_ssb X + 0x800000)] m mc)
by (eapply munch_weaken; [| exact MUs]; intros y Hy; cbn [outside fst snd] in Hy |- *; tauto) end.
clear MUs.
istep. istep. call_u (lock_spec).
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact TB. } { lia. } { subst tba. lia. } { lia. } { idtac. lia. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST1 end.
match goal with H : exists lw, rw_cells asegs _ tba _ |- _ => destruct H as [lw TBL] end.
istep. istep. if_true_u.

istep. istep. istep.
assert (AMO4 : amo_aligned AW (wz 6101464) = true) by (apply amo_aligned_intro4; [lia| reflexivity]).
amo_step AMO4. rewrite (amoadd_w_bytes n 1) by lia. mem_after_store. rewrite ?sext_extract_le4, ?(sx32_small n) by lia.
istep. rewrite (addiw_small n 1) by lia.
istep. istep. rewrite ?(unsigned_lit (n + 1)), (zext32_small (n + 1)) by lia.
istep. rewrite bv_lts_zero_r. if_false_u.
istep. istep. rewrite ?(unsigned_lit (n + 1)), (Z.shiftr_div_pow2 (n + 1) 16), (Z.div_small (n + 1) (2 ^ 16)) by lia.
step_until 0. if_false_u.
istep. rewrite ?(unsigned_lit (n + 1)) by lia. replace (Z.land (n + 1) 65535) with (n + 1) by (change 65535 with (Z.ones 16); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
istep. rewrite ?(unsigned_lit (n + 1)), (Z.shiftl_mul_pow2 (n + 1) 4) by lia. change (2 ^ 4) with 16. rewrite (Z.mul_comm (n + 1) 16).
step_until 0x837d0.

pose proof (hjunk_wmono _ _ _ _ JD WM) as JDc.
pose proof (fun Hm => proj1 (hjunk_split _ (rl_dn X + 16 * (n + 1)) (rl_dn X + 16 * (n + 1) + Z.of_nat 16) _ JDc Hm)) as JN. specialize (JN ltac:(cbn; lia)).
destruct (hjunk_cells _ (rl_dn X + 16 * (n + 1)) 16 JN) as [nj NODE]. clear JDc JN.
remember (rl_dn X + 16 * (n + 1)) as node eqn:Enode.
lazymatch type of FR with rw_cells _ ?mc _ (?c0 :: ?c1 :: ?c2 :: ?rest) =>
destruct (proj1 (rw_cells_app asegs mc _ [c0] (c1 :: c2 :: rest)) FR) as [FRa FRb];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRb;
destruct (proj1 (rw_cells_app asegs mc _ [c1; c2] rest) FRb) as [ARGS FRc];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRc end.
replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in ARGS, FRc by lia.
replace (bv_unsigned sp + -104 + 16) with (bv_unsigned sp + -88) in FRc by lia. clear FR FRb.
apply (rw_C8_split32 _ _ sz [C8 (wz tr)] []) in ARGS; [| lia]. cbn [app] in ARGS.
call_pre (nstore_spec).
{ assumption. } { unsigned_lits. exact ST1. } { exact CEIL'. } { unsigned_lits. lia. } { exact NODE. } { exact ARGS. } { exact TRQ. } { exact LQ. }
{ exact SSC. } { eapply hjunk_wmono; [exact JS| exact WM]. }
{ lia. } { lia. } { lia. } { lia. } { subst H. lia. } { exact SA. } { lia. } { idtac. lia. } { subst node. lia. } { subst node. idtac. lia. }
{ subst node. lia. }
{ unsigned_lits. lia. } { unsigned_lits. lia. } { lia. }
post_later.
match goal with H : exists nj4, _ |- _ => destruct H as (nj4 & Ea0 & NODE' & SSC' & ARGS' & TRQ') end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST2 end.

istep. istep. istep. istep. istep. if_lit2.
step_until 0.
release_frame FRa ST2 (bv_unsigned sp + -104). release_frame ARGS' ST2 (bv_unsigned sp + -88). release_frame FRc ST2 (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST2|].
exists (n + 1). split; [reflexivity|]. split; [lia|]. split; [| split; [exact TRQ'|]].
2:{ exists (n + 1). split; [| lia]. unfold depot_n, DP_N. split; [assumption| lia]. }

set (nh' := fun i => if i =? n + 1 then H else nh i). set (ns' := fun i => if i =? n + 1 then tf + 1 else ns i).
assert (NHE : forall j, 1 <= j <= Z.of_nat (Z.to_nat n) -> nh' j = nh j) by (intros j Hj; unfold nh'; destruct (Z.eqb_spec j (n + 1)); [lia| reflexivity]).
assert (NHN : nh' (n + 1) = H) by (unfold nh'; rewrite Z.eqb_refl; reflexivity).
exists (n + 1), (tf + sz + 1), (st + sz + 1), h0, j40, nh', ns'. unfold SS_BASE, DP_TAB, DP_N, DP_MAP1.
split; [lia|]. split; [lia|]. split; [lia|].
split. { intros i Hi. unfold nh'. destruct (Z.eqb_spec i (n + 1)) as [->|NE].
- split; [unfold DEPOT_CAP; lia| lia].
- destruct (HU i ltac:(lia)) as [_ HRi]. split; [unfold DEPOT_CAP; lia| exact HRi]. }
split. { rewrite zseq_snoc, map_app by lia. cbn [map]. rewrite NHN.
rewrite (map_ext_in nh' nh) by (intros j Hj; apply NHE; apply zseq_In in Hj; lia).
apply NoDup_snoc; [exact ND|]. intros Hin. apply in_map_iff in Hin as (j & Ej & Hj). apply zseq_In in Hj. exact (NOTIN j Hj Ej). }
repeat (split; [assumption|]).
split. { intros b' Hb'. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia. cbn [lastb].
replace (Z.of_nat (S (Z.to_nat n))) with (n + 1) by lia. rewrite NHN. fold b.
destruct (Z.eqb_spec b b') as [<-|NE].
- rewrite <- Etba. exact TBL.
- rewrite (lastb_ext nh nh') by exact NHE.
eapply rw_cells_transport; [exact (CTAB b' Hb')| exact MUf| exact WM| cbn; subst tba node; lia]. }
repeat (split; [assumption|]).
split. { intros i Hi. destruct (Z.eq_dec i (n + 1)) as [->|NE].
- rewrite NHN. replace (Z.to_nat (n + 1 - 1)) with (Z.to_nat n) by lia. rewrite (lastb_ext nh nh') by exact NHE. fold b. fold v.
unfold ns'. rewrite Z.eqb_refl. rewrite <- Enode. exact NODE'.
- rewrite (NHE i) by lia. rewrite (lastb_ext nh nh') by (intros j Hj; apply NHE; lia).
unfold ns'. replace (i =? n + 1) with false by (symmetry; apply Z.eqb_neq; lia).
eapply rw_cells_transport; [exact (CND i ltac:(lia))| exact MUf| exact WM| cbn; subst tba node; lia]. }
split. { replace (rl_dn X + 16 * (n + 1 + 1)) with (rl_dn X + 16 * (n + 1) + Z.of_nat 16) by lia.
eapply hjunk_wmono; [| exact WM].
exact (proj2 (hjunk_split _ _ (rl_dn X + 16 * (n + 1) + Z.of_nat 16) _ JD ltac:(cbn; lia))). }
split; [eapply hjunk_wmono; [exact JS| exact WM]|]. assumption.
Qed.

End Walk.
End Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QUvT QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QOJv.Mq4 QNQk.Mq2 QZbm QpY2.Mq9 QpY2.Mq4 QpME.Mq3 QYyZ.Mq6 QYyZ.Mq7.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Pure.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Local Notation FS := (ae_fs_base RE).

Lemma live_user_heap' : forall x, in_live_user LB0 x -> ((0 < x < kLowEnd /\ (x < 0x10000 \/ 0x645000 <= x)) \/ KHI <= x) /\ x < band_lo.
Proof. intros x LU. exact (live_user_heap _ _ _ _ _ _ GC x LU). Qed.

Lemma gcons_ff_add : forall c pos f,
fs_shape FS FS0 -> 0 <= c < kFsClasses -> 0 <= pos < fs_N c -> f = fs_frame FS c pos ->
~ In f (map ff_addr FS0) -> fframe_rangeA RE c f ->
gcons a LB0 ((c, f) :: FS0) G RE X.
Proof.
intros c pos f SHP Hc Hp Ef FRESH FR. pose proof SHP as [SHf ND].
pose proof GC as GC'. unfold gcons in GC' |- *. decompose [and] GC'.
match goal with H : forall g, In g FS0 -> fframe_rangeA _ _ _ |- _ => rename H into A12 end.
match goal with H : forall f1 f2, In f1 FS0 -> In f2 FS0 -> _ |- _ => rename H into A13 end.
repeat (split; [assumption|]).
assert (APART : forall g, In g FS0 -> ff_addr g + ff_size (ff_cls g) <= f \/ f + ff_size c <= ff_addr g).
{ intros g Hg. destruct (SHf g Hg) as (Hcg & pg & Hpg & Eg). rewrite Eg, Ef.
destruct (Z.eq_dec (ff_cls g) c) as [Ecg|NE].
- rewrite Ecg in *. assert (pg <> pos) by (intros ->; apply FRESH; rewrite Ef, <- Eg; apply in_map; exact Hg).
destruct (fs_frame_apart FS c pg pos ltac:(lia) ltac:(lia)); lia.
- destruct (fs_frame_apart_cls FS (ff_cls g) pg c pos Hcg Hc NE Hpg Hp); lia. }
split.
- intros g [<-|Hg]; [exact FR| exact (A12 g Hg)].
- intros f1 f2 [<-|G1] [<-|G2] NE; cbn [ff_addr ff_cls fst snd] in *.
+ exfalso. apply NE. reflexivity.
+ destruct (APART f2 G2); lia.
+ destruct (APART f1 G1); lia.
+ exact (A13 f1 f2 G1 G2 NE).
Qed.

End Pure.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRT : forall RE X m, ac_RTconst C RE X m <-> RTconst RE X m.
Hypothesis HRF : forall FS RE X m, ac_RFake C FS RE X m <-> RFake FS RE X m.

Lemma ARUNX_fs : forall a LB0 FS0 FS0' G RE X m m' W,
ARUNX C a LB0 FS0 G RE X m -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> czone LB0 RE x) ->
RTconst RE X m' -> RFake FS0' RE X m' -> gcons a LB0 FS0' G RE X ->
ARUNX C a LB0 FS0' G RE X m'.
Proof.
intros a LB0 FS0 FS0' G RE X m m' W AX MU WM HW RT' RF' GC'. pose proof (proj1 AX) as GC.
destruct AX as (_ & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
assert (AG : forall P : Z -> Prop, (forall x, P x -> czone LB0 RE x -> False) -> agree_on asegs P m m').
{ intros P HP. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro.
intros lo hi Hin Hx. exact (HP x Px (HW lo hi x Hin Hx)). }
split; [exact GC'|].
split; [apply HRT; exact RT'|].
split; [eapply (ac_RStats_frame C); [exact R2| exact WM| apply AG; intros x; apply (fp_RStats_cz a LB0 FS0 G RE X GC)]|].
split; [eapply (ac_RPrim_frame C); [exact R3| exact WM| apply AG; intros x; apply (fp_RPrim_cz a LB0 FS0 G RE X GC)]|].
split; [eapply (ac_RChunks_frame C); [exact R4| exact WM| apply AG; intros x; apply (fp_RChunks_cz a LB0 FS0 G RE X GC)]|].
split; [eapply (ac_RSec_frame C); [exact R5| exact WM| apply AG; intros x; apply (fp_RSec_cz a LB0 FS0 G RE X GC)]|].
split; [eapply (ac_RQuar_frame C); [exact R6| exact WM| apply AG; intros x; apply (fp_RQuar_cz a LB0 FS0 G RE X GC)]|].
split; [eapply (ac_RDepot_frame C); [exact R7| exact WM| apply AG; intros x; apply (fp_RDepot_cz a LB0 FS0 G RE X GC)]|].
apply HRF. exact RF'.
Qed.

Lemma fs_W_czone : forall LB0 RE (slo shi : Z) lo hi x,
band_lo <= slo -> ae_fs_base RE mod 8 = 0 ->
In (lo, hi) [(ae_fs_base RE, ae_fs_base RE + A_FS_MAP_SIZE); (SH (ae_fs_base RE), SH (ae_fs_base RE + A_FS_MAP_SIZE)); (slo, shi)] ->
lo <= x < hi -> czone LB0 RE x.
Proof.
intros LB0 RE slo shi lo hi x CE AL Hin Hx. unfold czone, in_iv, in_sh. cbn [fst snd].
assert (SHD : SH (ae_fs_base RE + A_FS_MAP_SIZE) = SH (ae_fs_base RE) + A_FS_MAP_SIZE / 8).
{ rewrite !SH_eq. unfold A_FS_MAP_SIZE. replace (ae_fs_base RE + 11571200) with (ae_fs_base RE + 1446400 * 8) by lia. rewrite Z.div_add by lia.
change (11571200 / 8) with 1446400. lia. }
cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.

Lemma filter_perm_length : forall (c : Z) (FS FS' : list fframe), Permutation FS FS' ->
length (filter (fun f : fframe => ff_cls f =? c) FS) = length (filter (fun f : fframe => ff_cls f =? c) FS').
Proof. intros c FS FS' P. apply Permutation_length. apply (Permutation_filter (fun f : fframe => ff_cls f =? c)). exact P. Qed.

Lemma fs_op_pres : forall a LB0 FS0 G RE X LB FSc (SP slo h szsh : Z) m m' c pos f,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> fs_shape (ae_fs_base RE) FS0 ->
(forall g, In g FSc -> In g FS0 /\ ff_addr g <> f) ->
0 <= c < kFsClasses -> 0 <= pos < fs_N c -> f = fs_frame (ae_fs_base RE) c pos ->
0 <= szsh <= ff_size c / 8 -> ae_fs_base RE <= h -> h + 8 <= ae_fs_base RE + 88 ->
band_lo <= slo -> band_lo <= SP ->
munch [(slo, SP); (h, h + 8); (fs_flag (ae_fs_base RE) c pos, fs_flag (ae_fs_base RE) c pos + 1); (f, f + ff_size c); (SH f, SH f + szsh)] m m' ->
wmono asegs m m' ->
aheap_presA asegs a_alayout LB FSc SP m m'.
Proof.
intros a LB0 FS0 G RE X LB FSc SP slo h szsh m m' c pos f GC PB SHP HFS Hc Hp Ef Hsz Hh1 Hh2 CE CSP MU WM.
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CEo & _). cbn [fst snd] in AL, K, CEo.
pose proof K as K'. pose proof CEo as CE'. rewrite ?KHI_eq in K'. idtac. unfold A_FS_MAP_SIZE in CE', K'.
pose proof (fs_frame_in_area (ae_fs_base RE) c pos Hc Hp) as [A1 A2]. rewrite <- Ef in A1, A2. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in A1, A2.
assert (SZ : 64 <= ff_size c) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c); lia).
assert (FAL : f mod 8 = 0) by (pose proof (fs_frame_align (ae_fs_base RE) c pos ltac:(Z.div_mod_to_equations; lia) ltac:(lia)); rewrite <- Ef in *; Z.div_mod_to_equations; lia).
pose proof (fs_flag_range (ae_fs_base RE) c pos Hc Hp) as FR.
assert (SHf : 0x800c0a00 <= SH f /\ SH f + ff_size c / 8 <= SH band_lo).
{ split; [rewrite SH_eq; clear - K' A1; Z.div_mod_to_equations; lia|].
replace (SH f + ff_size c / 8) with (SH (f + ff_size c)); [apply SH_mono; idtac; lia|].
rewrite !SH_eq. rewrite ff_size_eq in * by lia. replace (c + 6) with (Z.succ (Z.succ (Z.succ (c + 3)))) by lia.
rewrite !Z.pow_succ_r by lia. replace (2 * (2 * (2 * 2 ^ (c + 3)))) with (2 ^ (c + 3) * 8) by lia.
rewrite Z.div_add, Z.div_mul by lia. lia. }
pose proof SH_band as SHB0.
unfold aheap_presA. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x CA Hx. apply outside_intro. intros lo hi Hin [Y1 Y2].
cbn in Hin.
destruct CA as [C1|[C1|[C1|[(g & Hg & G1 & G2)|[(g & Hg & G1 & G2)|[C1|C1]]]]]].
-  pose proof SH_band. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
-  cbn [ala_client_data a_alayout] in C1. unfold a_client_data in C1.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
-
assert (LU : in_live_user LB0 x) by (destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R]).
pose proof (live_user_heap' _ _ _ _ _ _ GC x LU) as LH. rewrite ?KHI_eq in LH. unfold kLowEnd in LH.
pose proof (live_user_not_fs _ _ _ _ _ _ GC x LU) as NF. unfold A_FS_MAP_SIZE in NF. pose proof SH_band.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
-
destruct (HFS g Hg) as [Hg0 NEg]. pose proof SHP as [SHf' _]. destruct (SHf' g Hg0) as (Hcg & pg & Hpg & Eg).
pose proof (fs_frame_in_area (ae_fs_base RE) (ff_cls g) pg Hcg Hpg) as [B1 B2]. rewrite <- Eg in B1, B2. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in B1, B2.
assert (APART : ff_addr g + ff_size (ff_cls g) <= f \/ f + ff_size c <= ff_addr g).
{ rewrite Eg, Ef. destruct (Z.eq_dec (ff_cls g) c) as [Ecg|NE].
- rewrite Ecg in *. assert (pg <> pos) by (intros ->; apply NEg; rewrite Eg, Ef; reflexivity).
destruct (fs_frame_apart (ae_fs_base RE) c pg pos ltac:(lia) ltac:(lia)); lia.
- destruct (fs_frame_apart_cls (ae_fs_base RE) (ff_cls g) pg c pos Hcg Hc NE Hpg Hp); lia. }
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
-
destruct (HFS g Hg) as [Hg0 NEg]. pose proof SHP as [SHf' _]. destruct (SHf' g Hg0) as (Hcg & pg & Hpg & Eg).
pose proof (fs_frame_in_area (ae_fs_base RE) (ff_cls g) pg Hcg Hpg) as [B1 B2]. rewrite <- Eg in B1, B2. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in B1, B2.
assert (SZg : 64 <= ff_size (ff_cls g)) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 (ff_cls g)); lia).
assert (GAL : ff_addr g mod 8 = 0)
by (pose proof (fs_frame_align (ae_fs_base RE) (ff_cls g) pg ltac:(Z.div_mod_to_equations; lia) ltac:(lia)); rewrite <- Eg in *; Z.div_mod_to_equations; lia).
assert (APART : ff_addr g + ff_size (ff_cls g) <= f \/ f + ff_size c <= ff_addr g).
{ rewrite Eg, Ef. destruct (Z.eq_dec (ff_cls g) c) as [Ecg|NE].
- rewrite Ecg in *. assert (pg <> pos) by (intros ->; apply NEg; rewrite Eg, Ef; reflexivity).
destruct (fs_frame_apart (ae_fs_base RE) c pg pos ltac:(lia) ltac:(lia)); lia.
- destruct (fs_frame_apart_cls (ae_fs_base RE) (ff_cls g) pg c pos Hcg Hc NE Hpg Hp); lia. }
assert (GH : 0x7fff7000 <= x < 0x10007fff8000).
{ pose proof (@in_sh_band BAND (ff_addr g) (ff_size (ff_cls g)) x GAL ltac:(lia) ltac:(clear - K' B1 B2 SZg; lia) ltac:(lia) ltac:(split; cbn [fst snd]; lia)) as B0.
unfold kLowEnd, KHI in B0. exact B0. }
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; try lia.
eapply (in_sh_disjoint (ff_addr g) (ff_size (ff_cls g)) f (ff_size c) x GAL FAL ltac:(lia) ltac:(lia) APART (conj G1 G2)).
split; cbn [fst snd]; lia.
-  rewrite SH_247, ?KHI_eq in C1. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
-  cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. change (925696 / 8) with 115712 in C1.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
Qed.

Lemma RFake_shape : forall FS RE X m, RFake FS RE X m -> fs_shape (ae_fs_base RE) FS.
Proof. intros FS RE X m (_ & _ & _ & SHP & _). exact SHP. Qed.

Ltac open_run AR X G LB0 FS0 PB PF AX GC RT RF :=
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX);
pose proof (proj1 AX) as GC;
pose proof (proj1 (HRT _ _ _) (proj1 (proj2 AX))) as RT;
pose proof (proj1 (HRF _ _ _ _) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AX))))))))) as RF.

Lemma stack_malloc_0_A : astack_mallocA_stmt asegs a_alayout (ARUN C) 0 fsmalloc0_entry.
Proof.
unfold astack_mallocA_stmt. intros until lo. intros AR ROOM ST CEIL LO MI Htp Hgp Ha0 SZ SAL.
open_run AR X G LB0 FS0 PB PF AX GC RT RF. pose proof (proj1 GC) as RL.
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CEo & _). cbn [fst snd] in AL, K, CEo.
subst tp gp. cbn [ala_tp ala_gp ala_stack_malloc_stack a_alayout] in *.
rewrite (filter_perm_length 0 FS FS0 PF) in ROOM. change (fframe_cap 0) with (fs_N 0) in ROOM.
eapply evt_mono.
{ eapply (fsmalloc0_spec RE X); [exact RT| exact RL| exact RF| exact MI| exact ST| exact CEIL| lia| exact ROOM| exact Ha0]. }
cbv beta. intros ms' POST. unfold rpost in POST.
destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & STK'
& f & pos & junk & Ea0 & Ef & PR & FRESH & FR & RT' & RF' & BODY & SHC & MU2).
subst ms'. unfold std_postA. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact STK'|].
split.
{ eapply (fs_op_pres _ LB0 FS0 G RE X LB FS (bv_unsigned sp) (bv_unsigned sp - 224) (ae_fs_base RE) (ff_size 0 / 8) m m' 0 pos f GC PB
(RFake_shape _ _ _ _ RF)); try eassumption.
- intros g Hg. assert (Hg0 : In g FS0) by (eapply Permutation_in; [exact PF| exact Hg]). split; [exact Hg0|].
intros Eg. apply FRESH. rewrite <- Eg. apply in_map. exact Hg0.
- unfold kFsClasses. lia.
- change (ff_size 0 / 8) with 8. lia.
- lia. - lia. - lia. - lia. }
split; [reflexivity|]. split; [reflexivity|].
split.
{
eapply depot_keep_of_munch; [exact MU| exact WM|]. unfold DP_N.
constructor; [cbn [fst snd]; unfold A_FS_MAP_SIZE in *; lia|]. constructor; [cbn [fst snd]; rewrite !SH_eq; unfold A_FS_MAP_SIZE in *; Z.div_mod_to_equations; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
exists f, junk.
split; [exact Ea0|]. split; [exact FR|].
split.
{ apply (ARUN_close C s LB ((0, f) :: FS) RE m' X G LB0 ((0, f) :: FS0)); [exact PB| apply perm_skip; exact PF|].
eapply (ARUNX_fs _ LB0 FS0 _ G RE X m m'); [exact AX| exact MU| exact WM| | exact RT'| exact RF'|].
- intros lo' hi' x Hin Hx. eapply (fs_W_czone LB0 RE (bv_unsigned sp - 224) (bv_unsigned sp)); [lia| Z.div_mod_to_equations; lia| exact Hin| exact Hx].
- eapply (gcons_ff_add _ LB0 FS0 G RE X GC 0 pos f (RFake_shape _ _ _ _ RF)); [unfold kFsClasses; lia| exact PR| exact Ef| exact FRESH| exact FR]. }
split; [exact BODY|].
eapply rw_cells_recast'; [exact SHC| |].
- cbn. rewrite !repeat_length. easy.
- reflexivity.
Qed.

Lemma stack_malloc_1_A : astack_mallocA_stmt asegs a_alayout (ARUN C) 1 fsmalloc1_entry.
Proof.
unfold astack_mallocA_stmt. intros until lo. intros AR ROOM ST CEIL LO MI Htp Hgp Ha0 SZ SAL.
open_run AR X G LB0 FS0 PB PF AX GC RT RF. pose proof (proj1 GC) as RL.
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CEo & _). cbn [fst snd] in AL, K, CEo.
subst tp gp. cbn [ala_tp ala_gp ala_stack_malloc_stack a_alayout] in *.
rewrite (filter_perm_length 1 FS FS0 PF) in ROOM. change (fframe_cap 1) with (fs_N 1) in ROOM.
eapply evt_mono.
{ eapply (fsmalloc1_spec RE X); [exact RT| exact RL| exact RF| exact MI| exact ST| exact CEIL| lia| exact ROOM| exact Ha0]. }
cbv beta. intros ms' POST. unfold rpost in POST.
destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & STK'
& f & pos & junk & Ea0 & Ef & PR & FRESH & FR & RT' & RF' & BODY & SHC & MU2).
subst ms'. unfold std_postA. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact STK'|].
split.
{ eapply (fs_op_pres _ LB0 FS0 G RE X LB FS (bv_unsigned sp) (bv_unsigned sp - 224) (ae_fs_base RE + 8) (ff_size 1 / 8) m m' 1 pos f GC PB
(RFake_shape _ _ _ _ RF)); try eassumption.
- intros g Hg. assert (Hg0 : In g FS0) by (eapply Permutation_in; [exact PF| exact Hg]). split; [exact Hg0|].
intros Eg. apply FRESH. rewrite <- Eg. apply in_map. exact Hg0.
- unfold kFsClasses. lia.
- change (ff_size 1 / 8) with 16. lia.
- lia. - lia. - lia. - lia. }
split; [reflexivity|]. split; [reflexivity|].
split.
{
eapply depot_keep_of_munch; [exact MU| exact WM|]. unfold DP_N.
constructor; [cbn [fst snd]; unfold A_FS_MAP_SIZE in *; lia|]. constructor; [cbn [fst snd]; rewrite !SH_eq; unfold A_FS_MAP_SIZE in *; Z.div_mod_to_equations; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
exists f, junk.
split; [exact Ea0|]. split; [exact FR|].
split.
{ apply (ARUN_close C s LB ((1, f) :: FS) RE m' X G LB0 ((1, f) :: FS0)); [exact PB| apply perm_skip; exact PF|].
eapply (ARUNX_fs _ LB0 FS0 _ G RE X m m'); [exact AX| exact MU| exact WM| | exact RT'| exact RF'|].
- intros lo' hi' x Hin Hx. eapply (fs_W_czone LB0 RE (bv_unsigned sp - 224) (bv_unsigned sp)); [lia| Z.div_mod_to_equations; lia| exact Hin| exact Hx].
- eapply (gcons_ff_add _ LB0 FS0 G RE X GC 1 pos f (RFake_shape _ _ _ _ RF)); [unfold kFsClasses; lia| exact PR| exact Ef| exact FRESH| exact FR]. }
split; [exact BODY|].
eapply rw_cells_recast'; [exact SHC| |].
- cbn. rewrite !repeat_length. easy.
- reflexivity.
Qed.

Lemma stack_malloc_2_A : astack_mallocA_stmt asegs a_alayout (ARUN C) 2 fsmalloc2_entry.
Proof.
unfold astack_mallocA_stmt. intros until lo. intros AR ROOM ST CEIL LO MI Htp Hgp Ha0 SZ SAL.
open_run AR X G LB0 FS0 PB PF AX GC RT RF. pose proof (proj1 GC) as RL.
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CEo & _). cbn [fst snd] in AL, K, CEo.
subst tp gp. cbn [ala_tp ala_gp ala_stack_malloc_stack a_alayout] in *.
rewrite (filter_perm_length 2 FS FS0 PF) in ROOM. change (fframe_cap 2) with (fs_N 2) in ROOM.
eapply evt_mono.
{ eapply (fsmalloc2_spec RE X); [exact RT| exact RL| exact RF| exact MI| exact ST| exact CEIL| lia| exact ROOM| exact Ha0]. }
cbv beta. intros ms' POST. unfold rpost in POST.
destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & STK'
& f & pos & junk & Ea0 & Ef & PR & FRESH & FR & RT' & RF' & BODY & SHC & MU2).
subst ms'. unfold std_postA. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact STK'|].
split.
{ eapply (fs_op_pres _ LB0 FS0 G RE X LB FS (bv_unsigned sp) (bv_unsigned sp - 224) (ae_fs_base RE + 16) (ff_size 2 / 8) m m' 2 pos f GC PB
(RFake_shape _ _ _ _ RF)); try eassumption.
- intros g Hg. assert (Hg0 : In g FS0) by (eapply Permutation_in; [exact PF| exact Hg]). split; [exact Hg0|].
intros Eg. apply FRESH. rewrite <- Eg. apply in_map. exact Hg0.
- unfold kFsClasses. lia.
- change (ff_size 2 / 8) with 32. lia.
- lia. - lia. - lia. - lia. }
split; [reflexivity|]. split; [reflexivity|].
split.
{
eapply depot_keep_of_munch; [exact MU| exact WM|]. unfold DP_N.
constructor; [cbn [fst snd]; unfold A_FS_MAP_SIZE in *; lia|]. constructor; [cbn [fst snd]; rewrite !SH_eq; unfold A_FS_MAP_SIZE in *; Z.div_mod_to_equations; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
exists f, junk.
split; [exact Ea0|]. split; [exact FR|].
split.
{ apply (ARUN_close C s LB ((2, f) :: FS) RE m' X G LB0 ((2, f) :: FS0)); [exact PB| apply perm_skip; exact PF|].
eapply (ARUNX_fs _ LB0 FS0 _ G RE X m m'); [exact AX| exact MU| exact WM| | exact RT'| exact RF'|].
- intros lo' hi' x Hin Hx. eapply (fs_W_czone LB0 RE (bv_unsigned sp - 224) (bv_unsigned sp)); [lia| Z.div_mod_to_equations; lia| exact Hin| exact Hx].
- eapply (gcons_ff_add _ LB0 FS0 G RE X GC 2 pos f (RFake_shape _ _ _ _ RF)); [unfold kFsClasses; lia| exact PR| exact Ef| exact FRESH| exact FR]. }
split; [exact BODY|].
eapply rw_cells_recast'; [exact SHC| |].
- cbn. rewrite !repeat_length. easy.
- reflexivity.
Qed.

End Lift.
End Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QWRO Qu4g QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QWRO Qu4g QFQR QmP7 QmP7.Mq1 Q9Ho.Mq3 QYyZ.Mq8.
Import QlES. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Ltac gc_split GC :=
destruct GC as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A8b & A9 & A10 & A11 & A12 & A13).

Lemma gcons_retag_nonlive {BAND : Band} : forall a LB FS G RE X c i t0 t1,
gcons a LB FS G RE X -> tag_at G c i = Some t0 -> is_live t0 = false ->
(forall q, holds q t1 = false) -> is_live t1 = false ->
gcons a LB FS (set_tag c i t1 G) RE X.
Proof.
intros a LB FS G RE X c i t0 t1 GC Ht NL0 NH NL. gc_split GC.
pose proof (retag_at G c i t0 t1 Ht) as RT.
split; [exact A1|]. split.
{ intros q Aq nq Hq. destruct (A2 q Aq nq Hq) as [[H1|H1] H2]; split; [| exact H2| right; exact H1| exact H2].
left. destruct H1 as (id' & i' & E & Hn & HP & Ht' & Hi' & HA). exists id', i'. repeat (split; [assumption|]).
split; [| split; [exact Hi'| exact HA]]. rewrite RT.
destruct (Z.eqb_spec (class_of nq) c) as [EC|NC]; [destruct (Z.eqb_spec i' i) as [EI|NI]|]; cbn [andb]; try exact Ht'.
exfalso. rewrite EC, EI, Ht in Ht'. inversion Ht'. subst t0. cbn in NL0. discriminate. }
split; [exact A3|]. split.
{ intros c' i' q Hq. rewrite RT in Hq. destruct ((c' =? c) && (i' =? i)) eqn:E; [| exact (A4 _ _ _ Hq)].
inversion Hq; subst t1. cbn in NL. discriminate. }
split.
{ intros c' i' q Hq. rewrite RT in Hq. destruct ((c' =? c) && (i' =? i)) eqn:E; [| exact (A5 _ _ _ Hq)].
inversion Hq; subst t1. specialize (NH q). cbn in NH. rewrite aptr_eqb_refl' in NH. discriminate. }
split.
{ intros c' NE. rewrite ncarved_set_tag. apply A6. intros E. apply NE.
destruct (Z.eq_dec c' c) as [->|NC]; [rewrite set_tag_class, E; reflexivity| rewrite set_tag_other_class by exact NC; exact E]. }
split; [exact A7|]. split.
{ intros c1 i1 c2 i2 q u1 u2 H1 H2 K1 K2. rewrite RT in H1, H2.
destruct ((c1 =? c) && (i1 =? i)) eqn:E1; [inversion H1; subst u1; rewrite NH in K1; discriminate|].
destruct ((c2 =? c) && (i2 =? i)) eqn:E2; [inversion H2; subst u2; rewrite NH in K2; discriminate|].
exact (A8 _ _ _ _ q _ _ H1 H2 K1 K2). }
split.
{ intros c1 i1 t id1 n1 H1 K1. rewrite RT in H1. destruct ((c1 =? c) && (i1 =? i)) eqn:E; [inversion H1; subst t; rewrite NH in K1; discriminate|].
eapply A8b; eassumption. }
repeat (split; [assumption|]). exact A13.
Qed.

Lemma tag_at_gappend_inv : forall G c l c' i t,
tag_at (gappend c l G) c' i = Some t -> tag_at G c' i = Some t \/ (c' = c /\ In t l /\ ncarved G c <= i).
Proof.
intros G c l c' i t Ht. destruct (Z.lt_ge_cases i (ncarved G c')) as [LT|GE].
- left. rewrite tag_at_gappend_old in Ht by exact LT. exact Ht.
- destruct (Z.eq_dec c' c) as [->|NE].
+ right. rewrite tag_at_gappend_new in Ht by exact GE. split; [reflexivity|]. split; [| exact GE].
eapply nth_error_In. exact Ht.
+ exfalso. unfold tag_at, gappend in Ht. rewrite gset_ne in Ht by exact NE. unfold ncarved in GE.
destruct (Z.ltb_spec i 0); [discriminate|].
assert (L : (Z.to_nat i < length (G c'))%nat) by (apply nth_error_Some; rewrite Ht; discriminate). lia.
Qed.

Lemma gcons_gappend {BAND : Band} : forall a a' LB FS G RE X c l,
gcons a LB FS G RE X ->
1 <= c < kNumClasses ->
Forall (fun t => is_live t = false /\ forall q, holds q t = false) l ->
(forall c', c' <> c -> cls a' c' = cls a c') ->
ncarved G c * class_size c = c_alloc_user (cls a c) ->
c_alloc_user (cls a' c) = c_alloc_user (cls a c) + Z.of_nat (length l) * class_size c ->
0 <= c_alloc_user (cls a c) ->
c_alloc_user (cls a' c) <= c_mapped_user (cls a' c) -> c_mapped_user (cls a' c) <= kFreeArrayOffset ->
c_mapped_user (cls a' c) mod kUserMapSize = 0 ->
as_reg a' = as_reg a -> as_next a' = as_next a ->
gcons a' LB FS (gappend c l G) RE X.
Proof.
intros a a' LB FS G RE X c l GC Hc FL EO NCA EA A0 B1 B2 B3 ER EN. gc_split GC.
pose proof kconsts as (_ & _ & _ & K32 & _).
pose proof (class_size_facts c ltac:(rewrite K32 in Hc; lia)) as [S1 _].
assert (LP : 0 <= Z.of_nat (length l) * class_size c) by (clear - S1; nia).
assert (NEW : forall t, In t l -> is_live t = false /\ forall q, holds q t = false)
by (intros t Ht; exact (proj1 (List.Forall_forall _ _) FL t Ht)).
split; [exact A1|]. split.
{ intros q Aq nq Hq. destruct (A2 q Aq nq Hq) as [[H1|H1] H2]; split; [| exact H2| | exact H2].
- left. destruct H1 as (id' & i' & E & Hn & HP & Ht' & Hi' & HA). exists id', i'. repeat (split; [assumption|]).
split; [apply tag_at_gappend_Some_old; exact Ht'| split; [exact Hi'| exact HA]].
- right. destruct H1 as (mb & E & H3 & H4 & H5 & H6). exists mb. rewrite ER. repeat split; assumption. }
split; [exact A3|]. split.
{ intros c' i' q Hq. apply tag_at_gappend_inv in Hq as [Hq|(-> & Hin & _)]; [exact (A4 _ _ _ Hq)|].
destruct (NEW _ Hin) as [NL _]. cbn in NL. discriminate. }
split.
{ intros c' i' q Hq. apply tag_at_gappend_inv in Hq as [Hq|(-> & Hin & _)]; [exact (A5 _ _ _ Hq)|].
destruct (NEW _ Hin) as [_ NH]. specialize (NH q). cbn in NH. rewrite aptr_eqb_refl' in NH. discriminate. }
split.
{ intros c' NE. rewrite ncarved_gappend. destruct (Z.eqb_spec c' c) as [->|NC].
- split; [exact Hc|]. rewrite EA, <- NCA. clear. lia.
- rewrite gappend_other_class in NE by exact NC. destruct (A6 c' NE) as [X1 X2]. split; [exact X1|].
rewrite EO by exact NC. rewrite <- X2. lia. }
split.
{ intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NC]; [| rewrite EO by exact NC; apply A7; exact Hc'].
split; [| split; [exact B2| exact B3]]. clear - EA A0 B1 LP. lia. }
split.
{ intros c1 i1 c2 i2 q u1 u2 H1 H2 K1 K2.
apply tag_at_gappend_inv in H1 as [H1|(E1 & In1 & _)]; [| destruct (NEW _ In1) as [_ NH]; rewrite NH in K1; discriminate].
apply tag_at_gappend_inv in H2 as [H2|(E2 & In2 & _)]; [| destruct (NEW _ In2) as [_ NH]; rewrite NH in K2; discriminate].
exact (A8 _ _ _ _ q _ _ H1 H2 K1 K2). }
split.
{ intros c1 i1 t id1 n1 H1 K1. rewrite EN.
apply tag_at_gappend_inv in H1 as [H1|(E1 & In1 & _)]; [| destruct (NEW _ In1) as [_ NH]; rewrite NH in K1; discriminate].
eapply A8b; eassumption. }
rewrite ER. repeat (split; [assumption|]). exact A13.
Qed.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QWRO Qu4g QFQR QmP7 QmP7.Mq1 QYyZ.Mq8.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma pairwise_disjoint_snoc : forall l iv,
pairwise_disjoint l -> Forall (fun jv => iv_disjoint jv iv) l -> pairwise_disjoint (l ++ [iv]).
Proof.
induction l as [|x l IH]; intros iv PD F; cbn.
- split; [constructor| exact I].
- destruct PD as [F1 PD]. inversion F; subst. split.
+ apply Forall_app. split; [exact F1| constructor; [assumption| constructor]].
+ apply IH; assumption.
Qed.

Lemma gcons_reg_add {BAND : Band} : forall a a1 LB FS G RE X mb msz n,
gcons a LB FS G RE X ->
as_reg a1 = as_reg a ++ [mkSec mb msz n] ->
(forall c, cls a1 c = cls a c) -> as_next a1 = as_next a ->
sec_ok RE X (mkSec mb msz n) ->
(forall e, In e (as_reg a) -> mb + msz <= se_beg e \/ se_beg e + se_size e <= mb) ->
0 < msz ->
gcons a1 LB FS G RE X.
Proof.
intros a a1 LB FS G RE X mb msz n GC ER EC EN SOK AVR MSZ. pose proof GC as GC0. gc_split GC.
split; [exact A1|]. split.
{ intros p A k H. destruct (A2 p A k H) as [[H1|H1] H2]; split; [left; exact H1| exact H2| | exact H2].
right. destruct H1 as (mb' & E & H3 & H4 & H5 & H6). exists mb'. rewrite ER. repeat (split; [assumption|]). split; [apply in_or_app; left; exact H5| exact H6]. }
split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split.
{ intros c Hc. destruct (A6 c Hc) as [X1 X2]. split; [exact X1|]. rewrite EC. exact X2. }
split. { intros c Hc. rewrite EC. apply A7. exact Hc. }
split; [exact A8|]. split. { intros c i t id k Ht Hh. rewrite EN. exact (A8b c i t id k Ht Hh). }
rewrite ER. split.
{ apply Forall_app. split; [exact A9| constructor; [exact SOK| constructor]]. }
split.
{ rewrite map_app. cbn [map]. apply pairwise_disjoint_snoc; [exact A10|].
apply List.Forall_forall. intros jv Hin. apply in_map_iff in Hin. destruct Hin as (e & <- & He).
unfold iv_disjoint. cbn [fst snd se_beg se_size]. pose proof (AVR e He). lia. }
split.
{ rewrite map_app. cbn [map se_beg]. apply NoDup_app; [exact A11| constructor; [intros []| constructor]|].
intros x Hx Hx2. cbn [In] in Hx2. destruct Hx2 as [Ex|[]]. apply in_map_iff in Hx. destruct Hx as (e & E & He).
pose proof (AVR e He) as D. pose proof (proj1 (List.Forall_forall _ _) A9 e He) as (_ & _ & _ & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1. pose proof kconsts as (_ & _ & _ & _ & KP & _). subst x. rewrite <- Ex in D. lia. }
split; [exact A12| exact A13].
Qed.

Lemma gcons_alloc_sec {BAND : Band} : forall a LB FS G RE X mb n,
gcons a LB FS G RE X ->
In (mkSec mb (sec_map_size n) n) (as_reg a) ->
~ In (ASec mb n) (map ablk_id LB) ->
0 <= n <= 2^26 -> from_primary n = false ->
gcons a ((ASec mb n, mb + kSecUserOff, n) :: LB) FS G RE X.
Proof.
intros a LB FS G RE X mb n GC HR NOTIN Hn HP. gc_split GC.
split; [exact A1|]. split.
{ intros p A k [H|H].
- inversion H; subst. split; [| lia]. right. exists mb. repeat (split; [first [reflexivity| lia| assumption]|]). reflexivity.
- exact (A2 p A k H). }
split. { cbn [map ablk_id fst]. constructor; [exact NOTIN| exact A3]. }
split.
{ intros c i q Hq. destruct (A4 _ _ _ Hq) as (id' & n' & A' & E & Hin & Hc'). exists id', n', A'. split; [exact E|]. split; [right; exact Hin| exact Hc']. }
split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A8b|].
split; [exact A9|]. split; [exact A10|]. split; [exact A11|]. split; [exact A12| exact A13].
Qed.

Lemma sec_id_fresh {BAND : Band} : forall a LB FS G RE X mb n,
gcons a LB FS G RE X -> ~ In mb (map se_beg (as_reg a)) -> ~ In (ASec mb n) (map ablk_id LB).
Proof.
intros a LB FS G RE X mb n GC NI Hin. apply in_map_iff in Hin. destruct Hin as ([[q A'] n'] & Eq & Hin). cbn in Eq. subst q.
gc_split GC. destruct (A2 _ _ _ Hin) as [[(id' & i1 & E & _)|(mb' & E & _ & _ & HR & _)] _]; [discriminate|].
injection E as Emb En. apply NI. apply in_map_iff. exists (mkSec mb' (sec_map_size n') n'). split; [cbn; congruence| exact HR].
Qed.
End Mqd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C QKBN QjgW QXcn QV3O QsJM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO QFQR QmP7 QKBN QNQk.Mq6 QjgW QXcn QV3O QsJM QYyZ.Mqc QpY2.Mqh.
Import QlES. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Local Ltac rtk RT k H := pose proof (RT_img _ _ _ RT k _ _ eq_refl) as H; cbn [fst snd] in H;
lazymatch type of H with ro_cells _ _ ?a _ => let a' := eval vm_compute in a in change a with a' in H end.

Lemma RTconst_rt_consts {BAND : Band} : forall RE X m, RTconst RE X m -> rt_consts_at asegs m.
Proof.
intros RE X m RT. unfold rt_consts_at.
rtk RT 46%nat K46. rtk RT 47%nat K47. rtk RT 48%nat K48. rtk RT 49%nat K49. rtk RT 50%nat K50.
rtk RT 51%nat K51. rtk RT 52%nat K52. rtk RT 53%nat K53. rtk RT 54%nat K54.
rtk RT 18%nat K18. rtk RT 19%nat K19. rtk RT 20%nat K20. rtk RT 42%nat K42.
rtk RT 55%nat K55. rtk RT 23%nat K23. rtk RT 56%nat K56. rtk RT 57%nat K57. rtk RT 58%nat K58. rtk RT 59%nat K59. rtk RT 60%nat K60.
rtk RT 0%nat K0. rtk RT 40%nat K40. rtk RT 1%nat K1. rtk RT 2%nat K2. rtk RT 8%nat K8.
rtk RT 61%nat K61. rtk RT 62%nat K62. rtk RT 63%nat K63. rtk RT 64%nat K64. rtk RT 65%nat K65. rtk RT 66%nat K66.
rtk RT 67%nat K67. rtk RT 68%nat K68. rtk RT 16%nat K16. rtk RT 69%nat K69. rtk RT 70%nat K70.
rtk RT 71%nat K71. rtk RT 72%nat K72. rtk RT 73%nat K73. rtk RT 74%nat K74. rtk RT 75%nat K75. rtk RT 76%nat K76. rtk RT 77%nat K77. rtk RT 78%nat K78. rtk RT 79%nat K79. rtk RT 80%nat K80. rtk RT 81%nat K81. rtk RT 82%nat K82.
rtk RT 83%nat K83. rtk RT 84%nat K84. rtk RT 85%nat K85. rtk RT 86%nat K86. rtk RT 87%nat K87. rtk RT 88%nat K88. rtk RT 89%nat K89. rtk RT 90%nat K90. rtk RT 91%nat K91. rtk RT 92%nat K92. rtk RT 93%nat K93. rtk RT 94%nat K94.
rtk RT 95%nat K95. rtk RT 96%nat K96. rtk RT 97%nat K97. rtk RT 98%nat K98. rtk RT 99%nat K99. rtk RT 100%nat K100. rtk RT 101%nat K101.
rtk RT 102%nat K102.
rtk RT 103%nat K103.
pose proof (RT_rw _ _ _ RT 0%nat _ _ eq_refl) as W0. pose proof (RT_rw _ _ _ RT 1%nat _ _ eq_refl) as W1. cbn [fst snd] in W0, W1.

pose proof (proj1 (ro_cells_app asegs m 0x0e81a8 [C8 (wz 0x183ce8); C8 (wz 0x0ef9b8)] _) K19) as [K19a K19r].
pose proof (proj1 (ro_cells_app asegs m _ [C8 (wz 0x0f21b8)] _) K19r) as [_ K19b]. cbn [cells_size csize Nat.add Z.of_nat Z.add Pos.add Pos.of_succ_nat Pos.succ] in K19b.
lazymatch type of K19b with ro_cells _ _ ?a _ => let a' := eval vm_compute in a in change a with a' in K19b end.
pose proof (proj1 (ro_cells_app asegs m 0x0e81f0 [C8 (wz 0x0ea218)] _) K20) as [K20a _].
pose proof (proj1 (ro_cells_app asegs m 0x0f2ea0 [C8 (wz 0x7fffffffffff); C8 (wz 0); C8 (wz 0)] _) K1) as [K1a _].

assert (K0' : ro_cells asegs m 0x0f2e98 [C1 (b8 1); C1 (b8 1)]).
{ apply (proj2 (ro_cells_app asegs m 0x0f2e98 [C1 (b8 1)] [C1 (b8 1)])). split; [exact K0| exact K40]. }
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Section S.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRQ : ac_RQuar C = RQuar.
Hypothesis HRF : ac_RFake C = RFake.

Lemma ARUN_rt_consts : forall s LB FS RE m, ARUN C s LB FS RE m -> rt_consts_at asegs m.
Proof.
intros s LB FS RE m AR. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & _). rewrite HRT in R1. exact (RTconst_rt_consts RE X m R1).
Qed.

Lemma ARUN_errno : forall s LB FS RE m, ARUN C s LB FS RE m -> exists v : word, rw_cells asegs m 0x62547c [C4 v].
Proof.
intros s LB FS RE m AR. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & R2 & _). rewrite HRS in R2. destruct R2 as (_ & [e ERR] & _). exists e. exact ERR.
Qed.

Lemma ARUN_errno_frame : forall s LB FS RE m m' (v : word),
ARUN C s LB FS RE m -> munch [(0x62547c, 0x62547c + 4)] m m' -> wmono asegs m m' ->
rw_cells asegs m' 0x62547c [C4 v] -> ARUN C s LB FS RE m'.
Proof.
intros s LB FS RE m m' v AR MU WM ERR'. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
eapply ARUN_close; [exact PB| exact PF|].
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
assert (ES : forall x, 0x62547c <= x < 0x62547c + 4 -> fp_RStats RE X x) by (intros x Hx; right; left; unfold A_ERRNO; split; cbn [fst snd]; lia).
assert (AG : forall P : Z -> Prop, (forall x, P x -> fp_RStats RE X x -> False) -> agree_on asegs P m m').
{ intros P HP. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. cbn [outside]. split; [| exact I].
destruct (Z.lt_ge_cases x 0x62547c); [lia|]. destruct (Z.lt_ge_cases x (0x62547c + 4)); [| lia].
exfalso. exact (HP x Px (ES x ltac:(lia))). }
split; [exact GC|].
split; [eapply (ac_RTconst_frame C); [exact R1| exact WM| apply AG; intros x Px Sx; exact (fpS_excl _ _ _ _ _ _ GC x Sx ltac:(do 4 right; exact Px))]|].
split.
{ rewrite HRS in R2 |- *. destruct R2 as (HJ & _ & [b OOM]). split; [eapply hjunk_wmono; [exact HJ| exact WM]|]. split; [exists v; exact ERR'|].
exists b. eapply rw_cells_transport; [exact OOM| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
split; [eapply (ac_RPrim_frame C); [exact R3| exact WM| apply AG; intros x Px Sx; exact (fpP_RStats _ _ _ _ _ _ GC x Px Sx)]|].
split; [eapply (ac_RChunks_frame C); [exact R4| exact WM| apply AG; intros x Px Sx; exact (fpS_excl _ _ _ _ _ _ GC x Sx ltac:(left; exact Px))]|].
split; [eapply (ac_RSec_frame C); [exact R5| exact WM| apply AG; intros x Px Sx; exact (fpS_excl _ _ _ _ _ _ GC x Sx ltac:(right; left; exact Px))]|].
split; [eapply (ac_RQuar_frame C); [exact R6| exact WM| apply AG; intros x Px Sx; exact (fpQ_RStats _ _ _ _ _ _ GC x Px Sx)]|].
split; [eapply (ac_RDepot_frame C); [exact R7| exact WM| apply AG; intros x Px Sx; exact (fpS_excl _ _ _ _ _ _ GC x Sx ltac:(do 2 right; left; exact Px))]|].
eapply (ac_RFake_frame C); [exact R8| exact WM| apply AG; intros x Px Sx; exact (fpS_excl _ _ _ _ _ _ GC x Sx ltac:(do 3 right; left; exact Px))].
Qed.

Lemma ARUN_nbhd : forall s LB FS RE m p n, ARUN C s LB FS RE m -> amemset_whereA LB FS p n -> 0 < n ->
(exists w : word, rw_cells asegs m (8 * (SH p / 8)) [C8 w])
/\ (exists w : word, rw_cells asegs m (8 * (SH (p + n - 1) / 8)) [C8 w]).
Proof.
intros s LB FS RE m p n AR WH Hn. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & _ & R3 & R4 & _ & R6 & _ & R8). rewrite HRP in R3. rewrite HRC in R4. rewrite HRQ in R6. rewrite HRF in R8.
assert (WH0 : amemset_whereA LB0 FS0 p n).
{ destruct WH as [(q & A & n0 & Hin & H1 & H2)|(c & f & Hin & H1 & H2)].
- left. exists q, A, n0. split; [eapply Permutation_in; [exact PB| exact Hin]| split; assumption].
- right. exists c, f. split; [eapply Permutation_in; [exact PF| exact Hin]| split; assumption]. }
destruct (amemset_nbhd (ps_a s) LB0 FS0 G RE X m GC R3 R4 R6 R8 p n WH0 Hn) as [J1 J2].
split; [exact (hjunk_C8 _ _ J1)| exact (hjunk_C8 _ _ J2)].
Qed.
End S.
End Mqe.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1 QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mqc.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import Qu3b.Mq6. Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import Qu3b.Mq5 QYyZ.Mq9.
Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition fwritex_entry := 0xd5a8c%Z.
Definition FWRITEX_STACK : Z := (64 + MEMCPY_ICPT_STACK)%Z.

Definition FILE_cells (fl0 : byte) (j1 : list byte) (WEND WPOS : Z) (j2 : list byte) (lbfw : word) : list cell :=
[CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw].

Definition wfile (m : word -> option byte) (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word)
(B : Z) (content junk : list byte) : Prop :=
rw_cells asegs m Fp (FILE_cells fl0 j1 (B + Z.of_nat (length content) + Z.of_nat (length junk))
(B + Z.of_nat (length content)) j2 lbfw)
/\ rw_cells asegs m B [CB (length content) content; CB (length junk) junk]
/\ Z.land (bv_unsigned fl0) 32 = 0%Z
/\ (2147483648 <= bv_unsigned lbfw mod 4294967296)%Z
/\ (0 < B)%Z /\ (B + Z.of_nat (length content) + Z.of_nat (length junk) < 2^64)%Z
/\ (Fp + 148 <= B \/ B + Z.of_nat (length content) + Z.of_nat (length junk) <= Fp)%Z.

Definition fwritex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
(S : Z) (bs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
/\ bytes_at asegs m' S bs.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
intros segs m a n1 n2 H1 H2. unfold wr_at. split.
- intros (Ha & Hb & H). repeat split; try lia.
+ intros i Hi. apply H. lia.
+ intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
- intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
intros i Hi. destruct (Z.lt_ge_cases i n1).
+ apply HA. lia.
+ replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
rewrite wr_at_app by lia. rewrite bytes_at_app.
split.
- intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma sx32_neg : forall w : word, (2147483648 <= bv_unsigned w mod 4294967296)%Z ->
(9223372036854775808 <= bv_unsigned (sx32 w))%Z.
Proof.
intros w H. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq.
pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
change (2^64)%Z with 18446744073709551616%Z in *.
Z.div_mod_to_equations. lia.
Qed.

Ltac unwrap_in K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K; rewrite ?Z.mod_small in K by lia.

Lemma fwritex_spec {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte)
(fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte) (lo : Z),
wfile m (bv_unsigned a2) fl0 j1 j2 lbfw B content junk ->
bytes_at asegs m (bv_unsigned a0) bs ->
Z.of_nat (length bs) = bv_unsigned a1 ->
(length bs <= length junk)%nat ->
stk asegs m lo (bv_unsigned sp) ->
mem_inv asegs m ->
(band_lo <= lo)%Z -> (lo <= bv_unsigned sp - FWRITEX_STACK)%Z ->
(bv_unsigned a2 + 148 <= lo \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
(B + Z.of_nat (length content) + Z.of_nat (length junk) <= lo \/ bv_unsigned sp <= B)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= B + Z.of_nat (length content)
\/ B + Z.of_nat (length content) + Z.of_nat (length bs) <= bv_unsigned a0)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a2 \/ bv_unsigned a2 + 148 <= bv_unsigned a0)%Z ->
shadow_base asegs m -> rt_consts_at asegs m ->
rng_ok m (bv_unsigned a0) (Z.of_nat (length bs)) -> rng_ok m (B + Z.of_nat (length content)) (Z.of_nat (length bs)) ->
evt asegs (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(bv_unsigned a2) fl0 j1 j2 lbfw B content junk (bv_unsigned a0) bs lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5a8c) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb) SRC LEN LE ST MI CEIL LO SEP1 SEP2 SEP3 SEP4 SEP5 SB RC RS RD.
pose_word_ranges. pose proof CEIL as CEIL'. idtac. unfold FWRITEX_STACK, MEMCPY_ICPT_STACK in LO.
set (Fp := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
set (S := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 S) by (unfold S; rewrite Z_to_bv_bv_unsigned; reflexivity).
set (nc := length content) in *. set (nj := length junk) in *. set (lb := length bs) in *.
replace a1 with (Z_to_bv 64 (Z.of_nat lb)) by (rewrite LEN, Z_to_bv_bv_unsigned; reflexivity).
pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
pose proof (munch_refl [(lo, bv_unsigned sp); (B + Z.of_nat nc, B + Z.of_nat nc + Z.of_nat lb); (Fp + 40, Fp + 48)]%Z m) as MU.
pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUs.
pose proof (wmono_refl asegs m) as WM.
unfold FILE_cells in FC.
carve_frame 64%nat ST.
do 8 zstep.
zstep. zstep. zstep. zstep.
zstep. if_cases Kw; zify_cond Kw; unwrap_in Kw.
{ exfalso. lia. }
zstep. zstep.
zstep. if_cases Kr; zify_cond Kr; unwrap_in Kr.
2:{ exfalso. lia. }
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
2:{ exfalso. pose proof (sx32_neg lbfw LBF). lia. }
zstep. zstep.

apply (rw_cells_split_CB asegs _ _ [CB nc content] nj junk [] [lb; nj - lb]%nat) in BUF; [ | cbn; lia ].
cbn [mk_CB_cells app] in BUF.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUF].
cbn [cells_size csize Nat.add] in BUF. rewrite Nat.add_0_r in BUF.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFb BUFc].
cbn [cells_size csize] in BUFc. rewrite Nat.add_0_r in BUFc.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SB1;
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RC1;
assert (RS1 : rng_ok mc S (Z.of_nat lb))
by (eapply rng_ok_munch; [exact RS| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn; rewrite !SH_eq, ?KHI_eq in *;
left; pose proof (proj1 (proj2 RS)); Z.div_mod_to_equations; lia);
assert (RD1 : rng_ok mc (B + Z.of_nat nc) (Z.of_nat lb))
by (eapply rng_ok_munch; [exact RD| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn; rewrite !SH_eq, ?KHI_eq in *;
left; pose proof (proj1 (proj2 RD)); Z.div_mod_to_equations; lia)
end.
clear MUs.
zstep. call_u (memcpy_icpt_spec (B + Z.of_nat nc) S (Z.of_nat lb) lo bs (firstn lb junk));
[ exact SRC| rewrite Nat2Z.id; reflexivity| rewrite Nat2Z.id; exact BUFb| lia| assumption| lia
| unsigned_lits; eassumption| exact CEIL| unsigned_lits; unfold MEMCPY_ICPT_STACK; lia| unsigned_lits; lia| unsigned_lits; lia
| exact SB1| exact RC1| exact RS1| exact RD1|].
rewrite ?(unsigned_lit (B + Z.of_nat nc)), ?(unsigned_lit S), ?(unsigned_lit (Z.of_nat lb)) in * by lia.
rewrite !Nat2Z.id in *.
rewrite firstn_all2 in BUFc by (rewrite length_skipn; lia).
match goal with MC : rw_cells _ _ (B + Z.of_nat nc)%Z [CB lb bs] |- _ => rename MC into BUFb' end.
zstep. zstep. zstep. zstep.
replace (0 + Z.of_nat lb)%Z with (Z.of_nat lb) by lia.
replace (B + Z.of_nat nc + Z.of_nat lb)%Z with (B + Z.of_nat (length (content ++ bs)))%Z by (rewrite length_app; lia).
do 9 zstep.
match goal with STa : stk asegs ?mc lo (bv_unsigned sp + -64)%Z, FRx : rw_cells asegs ?mc (bv_unsigned sp + -64)%Z _ |- _ => release_frame FRx STa (bv_unsigned sp) end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (BUF : rw_cells asegs mm B ([] ++ [CB nc content; CB lb bs] ++ [CB (nj - lb)%nat (skipn lb junk)]));
[ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [ eassumption |];
cbn [cells_size csize]; rewrite Nat.add_0_r;
apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [ exact BUFb' |];
cbn [cells_size csize]; rewrite Nat.add_0_r; eassumption
| apply rw_cells_merge in BUF; cbn [cells_size cells_bytes csize cbytes app Nat.add] in BUF;
rewrite Nat.add_0_r, app_nil_r in BUF ]
end.
apply evt_done. unfold fwritex_post.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [ ms_eq | ].
split. { replace (B + Z.of_nat (length (content ++ bs)))%Z with (B + Z.of_nat nc + Z.of_nat lb)%Z by (rewrite length_app; lia). assumption. }
repeat match goal with |- _ /\ _ => split end; try assumption.

unfold wfile, FILE_cells. rewrite !length_app, !length_skipn. fold nc lb nj.
rewrite !Nat2Z.inj_add, !Nat2Z.inj_sub by lia.
replace (B + (Z.of_nat nc + Z.of_nat lb) + (Z.of_nat nj - Z.of_nat lb))%Z with (B + Z.of_nat nc + Z.of_nat nj)%Z by lia.
match goal with FCx : rw_cells asegs _ Fp _ |- _ =>
replace (B + Z.of_nat nc + Z.of_nat lb)%Z with (B + (Z.of_nat nc + Z.of_nat lb))%Z in FCx by lia;
split; [exact FCx|] end.
split; [exact BUF|]. split; [exact FL|]. split; [exact LBF|]. split; [lia|]. split; lia.
Qed.
End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr QvDJ.Mq3.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QTVW.Mq9 QYyZ.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition strnlen_entry := 0xde3d4%Z.
Definition STRNLEN_STACK : Z := 32 + MEMCHR_ICPT_STACK.

Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
(wz (strnlen_res n buf))
a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ bytes_at asegs m' A buf.

Lemma strnlen_spec {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 (a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : word -> option byte) (A n : Z) (buf : list byte) (lo : Z),
stk asegs m lo (bv_unsigned sp) ->
bytes_at asegs m A buf ->
memchr_ok A 0 n buf ->
mem_inv asegs m ->
band_lo <= lo -> lo <= bv_unsigned sp - STRNLEN_STACK ->
A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A ->
0 < A -> 0 <= n < 2^64 ->
shadow_base asegs m -> rt_consts_at asegs m ->
rng_ok m A (memchr_len 0 n buf) ->
evt asegs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz strnlen_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST BUF OK MI CEIL LO SEP A0 N0 SB RC RNG.
pose proof CEIL as CEIL'. idtac. unfold STRNLEN_STACK, MEMCHR_ICPT_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
unfold strnlen_entry.
carve_frame 32%nat ST.
do 8 istep.
pose proof (shadow_base_munch _ _ _ SB MU ltac:(rt_wzones)) as SB1.
pose proof (rt_consts_at_munch _ _ _ RC MU WM ltac:(rt_wzones)) as RC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RNG1 : rng_ok mc A (memchr_len 0 n buf))
by (eapply rng_ok_munch; [exact RNG| exact MU| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn; rewrite !SH_eq, ?KHI_eq in *;
left; pose proof (proj1 (proj2 RNG)); Z.div_mod_to_equations; lia) end.
step. call_u (memchr_icpt_spec A n lo buf (wz 0));
[ eassumption| change (bv_unsigned (wz 0) mod 256) with 0; exact OK| assumption| lia| lia| unsigned_lits; eassumption| exact CEIL
| unsigned_lits; unfold MEMCHR_ICPT_STACK; lia| unsigned_lits; lia| exact SB1| exact RC1| change (bv_unsigned (wz 0) mod 256) with 0; exact RNG1|].
change (bv_unsigned (wz 0) mod 256) with 0 in *. change (0 mod 256) with 0 in *.
unfold memchr_res.
destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:FB.
- pose proof (find_byte_lt _ _ _ FB) as Hl. rewrite length_firstn in Hl.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; lia|].
stp. rewrite ?(unsigned_lit (A + Z.of_nat i)), ?(unsigned_lit A) by lia.
replace (A + Z.of_nat i + - A)%Z with (strnlen_res n buf) by (unfold strnlen_res; rewrite FB; lia).
do 4 step.
match goal with FRx : rw_cells asegs ?mc (bv_unsigned sp + -32) _, STx : stk asegs ?mc lo _ |- _ => release_frame FRx STx (bv_unsigned sp) end.
step. step.
apply evt_done. unfold strnlen_post. do 15 eexists. split; [reflexivity|].
repeat match goal with |- _ /\ _ => split; [eassumption|] end; eassumption.
- step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
step.
lazymatch goal with |- evt _ ?Q _ => set (PP := Q) end.
replace (wz n) with (wz (strnlen_res n buf)) by (unfold strnlen_res; rewrite FB; reflexivity).
subst PP.
do 3 step.
match goal with FRx : rw_cells asegs ?mc (bv_unsigned sp + -32) _, STx : stk asegs ?mc lo _ |- _ => release_frame FRx STx (bv_unsigned sp) end.
step. step.
apply evt_done. unfold strnlen_post. do 15 eexists. split; [reflexivity|].
repeat match goal with |- _ /\ _ => split; [eassumption|] end; eassumption.
Qed.
End Mqg.

Module Mqh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO QFQR QmP7 QKBN QYyZ.Mqc QV3O.
Import QlES.
Import ListNotations. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Section S.
Context {BAND : Band}.

Lemma depot_keep_of_pzone : forall a LB0 FS0 G RE X (m m' : word -> option byte) W,
gcons a LB0 FS0 G RE X -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> pzone a LB0 G RE X x) -> depot_keep asegs m m'.
Proof.
intros a LB0 FS0 G RE X m m' W GC MU WM HW n [RC P]. split; [| exact P].
eapply (rw_cells_agree asegs (fun x => ~ pzone a LB0 G RE X x)); [| exact RC|].
- eapply agree_on_of_munch; [exact MU| exact WM|]. intros x NZ _. apply outside_intro. intros lo hi Hin Hx. exact (NZ (HW lo hi x Hin Hx)).
- intros y Hy. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hy. unfold DP_N in Hy.
assert (FD : fp_RDepot RE X y) by (left; unfold in_iv; cbn [fst snd]; lia).
intros [FQ|[FP|[FS|BL]]].
+ exact (fpQ_RDepot a LB0 FS0 G RE X GC y FQ FD).
+ exact (fpP_RDepot a LB0 FS0 G RE X GC y FP FD).
+ exact (fpS_excl a LB0 FS0 G RE X GC y FS (or_intror (or_intror (or_introl FD)))).
+ lia.
Qed.

Definition ezone (a : AState) (LB0 : list ablock) (G : ghost) (RE : aentry) (X : rlay) (x : Z) : Prop :=
fp_RQuar a LB0 G RE X x \/ fp_RPrim G RE X x \/ in_iv (rl_T X + 2800, 368) x \/ x = 0x174420 \/ fp_RDepot RE X x \/ band_lo <= x.

Lemma errno_keep_of_ezone : forall a LB0 FS0 G RE X (m m' : word -> option byte) W,
gcons a LB0 FS0 G RE X -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> ezone a LB0 G RE X x) -> errno_keep asegs m m'.
Proof.
intros a LB0 FS0 G RE X m m' W GC MU WM HW. unfold errno_keep.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros y Hy _. apply outside_intro. intros lo hi Hin Hx.
assert (FS : fp_RStats RE X y) by (right; left; unfold in_iv, A_ERRNO; cbn [fst snd]; lia).
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & TC & _). cbn [fst snd] in TK, TC.
destruct (HW lo hi y Hin Hx) as [Z|[Z|[Z|[Z|[Z|Z]]]]].
- exact (fpQ_RStats a LB0 FS0 G RE X GC y Z FS).
- exact (fpP_RStats a LB0 FS0 G RE X GC y Z FS).
- unfold in_iv in Z. cbn [fst snd] in Z. lia.
- lia.
- exact (fpS_excl a LB0 FS0 G RE X GC y FS (or_intror (or_intror (or_introl Z)))).
- lia.
Qed.

Lemma ezone_of_qzone : forall a LB0 G RE X x, qzone a LB0 G RE X x -> ezone a LB0 G RE X x.
Proof. intros a LB0 G RE X x [H|H]; unfold ezone; [left; exact H| do 5 right; exact H]. Qed.

Definition free_step (m m' : word -> option byte) : Prop := depot_step m m' /\ errno_keep asegs m m'.
End S.
End Mqh.

Module Mqi.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QpY2.Mqb QYyZ.Mqb QmP7.Mq1 Q9Ho.Mq3.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition ri_cellsL (v : Z) (x : cstate) (j1 j2 j3 j4 : list byte) : list cell :=
[ C8 (wz v); CB 8 j1; C8 (wz (c_num_freed x)); C8 (wz (c_mapped_fa x)); C8 (wz (c_alloc_user x)); C8 (wz 0);
C8 (wz (c_mapped_user x)); C8 (wz 0); CB 4 j2; C1 (b8 0); CB 3 j3; CB 56 j4 ].
Definition ri_tail (x : cstate) (j1 j2 j3 j4 : list byte) : list cell :=
[ CB 8 j1; C8 (wz (c_num_freed x)); C8 (wz (c_mapped_fa x)); C8 (wz (c_alloc_user x)); C8 (wz 0);
C8 (wz (c_mapped_user x)); C8 (wz 0); CB 4 j2; C1 (b8 0); CB 3 j3; CB 56 j4 ].

Lemma ri_cellsL_split : forall m A v x j1 j2 j3 j4,
rw_cells asegs m A (ri_cellsL v x j1 j2 j3 j4) <-> rw_cells asegs m A [C8 (wz v)] /\ rw_cells asegs m (A + 8) (ri_tail x j1 j2 j3 j4).
Proof. intros. apply (rw_cells_app asegs m A [C8 (wz v)]). Qed.

Section PerClass.
Variables (a : AState) (G : ghost) (RE : aentry) (X : rlay) (m : mem) (c : Z) (K : pcls) (v : Z).
Definition cr_cellsL : Prop :=
(exists j1 j2 j3 j4, rw_cells asegs m (ri_addr RE c) (ri_cellsL v (cls a c) j1 j2 j3 j4))
/\ rw_cells asegs m (pc_addr X c) (pc_cells (as_cache_inited a) c (cls a c))
/\ (exists CH, u32arr asegs m (pc_addr X c + 16) CH /\ length CH = 16%nat
/\ forall j, (j < length (pk_ca K))%nat -> nth_error CH j = Some (wz (coff c (nth j (pk_ca K) 0)))).
Definition class_repL : Prop := cr_cellsL /\ cr_pure a G c K /\ cr_region a G RE m c K.
End PerClass.

Definition RPrimL (a : AState) (G : ghost) (RE : aentry) (X : rlay) (m : mem) (cl v : Z) : Prop :=
exists K : Z -> pcls,
hjunk m (rl_T X + 2768) (rl_T X + 2800)
/\ (forall c, G c <> [] -> 1 <= c < kNumClasses)
/\ (forall c, 0 <= c < kNumClasses -> c <> cl -> class_rep a G RE X m c (K c))
/\ 0 <= cl < kNumClasses /\ class_repL a G RE X m cl (K cl) v.

Lemma class_repL_0 : forall a G RE X m c K, class_rep a G RE X m c K <-> class_repL a G RE X m c K 0.
Proof.
intros. split; intros (((j1 & j2 & j3 & j4 & RI) & PC & CHH) & B & C); (split; [| split; [exact B| exact C]]);
(split; [exists j1, j2, j3, j4; exact RI| split; [exact PC| exact CHH]]).
Qed.

Lemma RPrimL_un0 : forall a G RE X m cl, RPrimL a G RE X m cl 0 -> RPrim a G RE X m.
Proof.
intros a G RE X m cl (K & HJ & GNE & HC & Hcl & HCL). exists K. split; [exact HJ|]. split; [exact GNE|].
intros c Hc. destruct (Z.eq_dec c cl) as [->|NE]; [apply class_repL_0; exact HCL| exact (HC c Hc NE)].
Qed.

Lemma class_repL_split : forall a G RE X m c K v,
class_repL a G RE X m c K v <->
cr_cellsL a RE X m c K v /\ cr_pure a G c K /\
(1 <= c -> u32arr asegs m (fa_beg (ae_L RE) c) (map (fun i => Z_to_bv 64 (coff c i)) (pk_fl K))
/\ hjunk m (fa_beg (ae_L RE) c + 4 * c_num_freed (cls a c)) (fa_beg (ae_L RE) c + c_mapped_fa (cls a c))
/\ cr_user a G RE m c
/\ hjunk m (SH (fa_beg (ae_L RE) c)) (SH (fa_beg (ae_L RE) c + kFreeArraySize))).
Proof.
intros a G RE X m c K v. unfold class_repL, cr_region, cr_user. split.
- intros (A & B & C). split; [exact A|]. split; [exact B|]. intros Hc. specialize (C Hc). tauto.
- intros (A & B & C). split; [exact A|]. split; [exact B|]. intros Hc. specialize (C Hc). tauto.
Qed.

Lemma class_repL_ext : forall a a' G G' RE X m c K v,
class_repL a G RE X m c K v -> cls a' c = cls a c -> as_cache_inited a' = as_cache_inited a -> G' c = G c ->
class_repL a' G' RE X m c K v.
Proof.
intros a a' G G' RE X m c K v HC EC EI EG.
assert (TG : forall i, tag_at G' c i = tag_at G c i) by (intros i; unfold tag_at; rewrite EG; reflexivity).
unfold class_repL, cr_cellsL, cr_pure, cr_region in *. rewrite EC, EI, EG. setoid_rewrite TG. exact HC.
Qed.

Lemma RPrimL_open : forall a G RE X m cl v, RPrimL a G RE X m cl v ->
exists K : Z -> pcls, hjunk m (rl_T X + 2768) (rl_T X + 2800)
/\ (forall c, G c <> [] -> 1 <= c < kNumClasses)
/\ (forall c, 0 <= c < kNumClasses -> c <> cl -> class_rep a G RE X m c (K c))
/\ 0 <= cl < kNumClasses /\ class_repL a G RE X m cl (K cl) v.
Proof. intros a G RE X m cl v H. exact H. Qed.

Section ClassFrameL.
Context {BAND : Band}.
Variables (a : AState) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis RL : rlay_ok RE X.

Lemma class_repL_agree_but_mutex : forall m m' c K v w,
class_repL a G RE X m c K v -> 0 <= c < 32 ->
agree_on asegs (fun z => fp_cls RE X c z /\ ~ (ri_addr RE c <= z < ri_addr RE c + 8)) m m' ->
rw_cells asegs m' (ri_addr RE c) [C8 (Z_to_bv 64 w)] ->
class_repL a G RE X m' c K w.
Proof.
intros m m' c K v w HC Hc AG HEAD. pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof HC as (((j1 & j2 & j3 & j4 & RI) & PC & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
pose proof (reg_geom RE X RL c Hc) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
assert (NRI_lo : forall z, z < prim_lo RE + 137438953472 -> ~ (ri_addr RE c <= z < ri_addr RE c + 8)) by (intros z Hz; unfold ri_addr; lia).
assert (INFA : forall z, fa_beg (ae_L RE) c <= z < fa_beg (ae_L RE) c + kFreeArraySize ->
fp_cls RE X c z /\ ~ (ri_addr RE c <= z < ri_addr RE c + 8)).
{ intros z Hz. split; [do 2 right; left; exact Hz| apply NRI_lo; rewrite FB, KS in Hz; clear - Hz Hc; lia]. }
assert (INFS : forall z, SH (fa_beg (ae_L RE) c) <= z < SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8 ->
fp_cls RE X c z /\ ~ (ri_addr RE c <= z < ri_addr RE c + 8)).
{ intros z Hz. split; [do 3 right; left; split; cbn [fst snd]; lia| apply NRI_lo].
rewrite FB, KS in Hz. unfold SH, A_SHADOW_OFS in Hz. clear - Hz Hc PK. Z.div_mod_to_equations. lia. }
assert (INUZ : forall z, uzone RE c z -> fp_cls RE X c z /\ ~ (ri_addr RE c <= z < ri_addr RE c + 8)).
{ intros z [Hz|Hz].
- split; [do 4 right; left; exact Hz| apply NRI_lo; rewrite RB, KO in Hz; clear - Hz Hc; lia].
- split; [do 5 right; exact Hz| apply NRI_lo]. unfold in_sh in Hz. cbn [fst snd] in Hz.
rewrite RB, KO in Hz. unfold SH, A_SHADOW_OFS in Hz. clear - Hz Hc PK. Z.div_mod_to_equations. lia. }
assert (INPC : forall z, pc_addr X c <= z < pc_addr X c + 80 -> fp_cls RE X c z /\ ~ (ri_addr RE c <= z < ri_addr RE c + 8)).
{ intros z Hz. split; [right; left; exact Hz|]. unfold pc_addr in Hz. unfold ri_addr. rewrite RIq. clear - Hz TD Hc TB PK. lia. }
pose proof (agree_on_mono _ _ (uzone RE c) m m' AG INUZ) as AGU.
split; [split; [|split]| split; [exact PU|]].
- exists j1, j2, j3, j4. apply ri_cellsL_split. apply ri_cellsL_split in RI as [_ TL]. split; [exact HEAD|].
eapply rw_cells_agree; [exact AG| exact TL|]. intros z Hz. cbn [ri_tail cells_size csize Nat.add] in Hz.
split; [left; lia| lia].
- eapply rw_cells_agree; [exact AG| exact PC|]. intros z Hz. apply INPC. cbn [pc_cells cells_size csize Nat.add] in Hz. lia.
- exists CH. split; [| split; [exact LCH| exact HCH]]. eapply u32arr_agree; [exact AG| exact ACH|]. intros z Hz. apply INPC. rewrite LCH in Hz. cbn in Hz. lia.
- intros Hc1. specialize (REG Hc1). destruct REG as (FA & FJ & SL & UT & SS & US & UJ & FS).
assert (HU : cr_user a G RE m' c) by (eapply cr_user_agree; [exact PU| split; [exact SL| split; [exact UT| split; [exact SS| split; [exact US| exact UJ]]]]| lia| exact AGU]).
destruct HU as (SL' & UT' & SS' & US' & UJ').
assert (KS8 : kFreeArraySize = 8 * 67108864) by (rewrite KS; reflexivity).
split; [| split; [| split; [exact SL'| split; [exact UT'| split; [exact SS'| split; [exact US'| split; [exact UJ'|]]]]]]].
+ eapply u32arr_agree; [exact AG| exact FA|]. intros z Hz. rewrite length_map in Hz. apply INFA. lia.
+ eapply hjunk_agree; [exact AG| exact FJ|]. intros z Hz. apply INFA. lia.
+ eapply hjunk_agree; [exact AG| exact FS|]. intros z Hz. rewrite KS8, SH_plus8 in Hz. apply INFS. rewrite KS8, Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma class_repL_agree : forall m m' c K v,
class_repL a G RE X m c K v -> 0 <= c < 32 -> agree_on asegs (fp_cls RE X c) m m' -> class_repL a G RE X m' c K v.
Proof.
intros m m' c K v HC Hc AG. eapply class_repL_agree_but_mutex; [exact HC| exact Hc| |].
- eapply agree_on_mono; [exact AG|]. intros z [Hz _]. exact Hz.
- destruct HC as (((j1 & j2 & j3 & j4 & RI) & _) & _). apply ri_cellsL_split in RI as [HD _].
eapply rw_cells_agree; [exact AG| exact HD|]. intros z Hz. left. cbn [cells_size csize Nat.add] in Hz. lia.
Qed.
End ClassFrameL.

Lemma RPrimL_reclose {BAND : Band} : forall a a' G G' RE X m m' c (K : Z -> pcls) (Kc : pcls) w,
rlay_ok RE X ->
hjunk m (rl_T X + 2768) (rl_T X + 2800) ->
(forall c0, G c0 <> [] -> 1 <= c0 < kNumClasses) ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> class_rep a G RE X m c0 (K c0)) ->
0 <= c < kNumClasses ->
(forall c0, c0 <> c -> cls a' c0 = cls a c0) -> as_cache_inited a' = as_cache_inited a ->
(forall c0, c0 <> c -> G' c0 = G c0) -> (G' c <> [] -> 1 <= c) ->
wmono asegs m m' ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> agree_on asegs (fp_cls RE X c0) m m') ->
class_repL a' G' RE X m' c Kc w ->
RPrimL a' G' RE X m' c w.
Proof.
intros a a' G G' RE X m m' c K Kc w RL HJ GNE HCall Hc EC EI EG GC WM AGS HCc.
pose proof kconsts as (_ & _ & _ & K32 & _). rewrite K32 in *.
exists (fun c0 => if c0 =? c then Kc else K c0). split; [eapply hjunk_wmono; [exact HJ| exact WM]|]. split.
- intros c0 Hne. destruct (Z.eq_dec c0 c) as [->|NE]; [split; [apply GC; exact Hne| lia]|].
rewrite (EG c0 NE) in Hne. exact (GNE c0 Hne).
- split; [| split; [lia| rewrite Z.eqb_refl; exact HCc]].
intros c0 Hc0 NE. destruct (Z.eqb_spec c0 c) as [->|_]; [lia|].
eapply class_rep_ext; [| apply EC; exact NE| exact EI| apply EG; exact NE].
eapply class_rep_agree; [apply HCall; [exact Hc0| exact NE]| exact Hc0| apply AGS; [exact Hc0| exact NE]].
Qed.

Lemma RPrimL_stack {BAND : Band} : forall a G RE X m m' W cl v,
RPrimL a G RE X m cl v -> rlay_ok RE X -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => band_lo <= fst iv) W -> RPrimL a G RE X m' cl v.
Proof.
intros a G RE X m m' W cl v (K & HJ & GNE & HC & Hcl & HCL) RL MU WM FW.
pose proof kconsts as (_ & _ & _ & K32 & _).
assert (AGc : forall c0, 0 <= c0 < 32 -> agree_on asegs (fp_cls RE X c0) m m').
{ intros c0 Hc0. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as C. cbn [fst] in C.
pose proof (fp_cls_lt_ceil RE X RL c0 x Hc0 Fx). lia. }
exists K. split; [eapply hjunk_wmono; [exact HJ| exact WM]|].
split; [exact GNE|]. split.
- intros c0 Hc0 NE. eapply class_rep_agree; [exact (HC c0 Hc0 NE)| rewrite K32 in Hc0; exact Hc0| apply AGc; rewrite K32 in Hc0; exact Hc0].
- split; [exact Hcl|]. eapply class_repL_agree; [exact RL| exact HCL| rewrite K32 in Hcl; exact Hcl| apply AGc; rewrite K32 in Hcl; exact Hcl].
Qed.

Lemma RPrimL_gappend_nil : forall a G RE X m c cl v, RPrimL a G RE X m cl v -> RPrimL a (gappend c [] G) RE X m cl v.
Proof.
intros a G RE X m c cl v (K & HJ & GNE & HC & Hcl & HCL).
assert (EG : forall c0, gappend c [] G c0 = G c0).
{ intros c0. unfold gappend. destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite gset_eq, app_nil_r| rewrite gset_ne by exact NE]; reflexivity. }
exists K. split; [exact HJ|]. split; [intros c0 Hc0; apply GNE; rewrite <- EG; exact Hc0|]. split.
- intros c0 Hc0 NE. eapply class_rep_ext; [exact (HC c0 Hc0 NE)| reflexivity| reflexivity| apply EG].
- split; [exact Hcl|]. eapply class_repL_ext; [exact HCL| reflexivity| reflexivity| apply EG].
Qed.

Lemma RPrimL_mutex : forall a G RE X m cl v, RPrimL a G RE X m cl v -> rw_cells asegs m (ri_addr RE cl) [C8 (Z_to_bv 64 v)].
Proof.
intros a G RE X m cl v (K & _ & _ & _ & _ & (((j1 & j2 & j3 & j4 & RI) & _) & _)). apply ri_cellsL_split in RI as [HD _]. exact HD.
Qed.
End Mqi.

Module Mqj.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig Qc6I QJFf.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QpY2.Mqb Q9Ho.Mq3 QmP7.Mq1 QYyZ.Mq8.
Import QXcn.
Import QYyZ.Mqc.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation b8 := (Z_to_bv 8).

Definition rq_keep (G : ghost) (RE : aentry) (JG : list Z) (Qs : list aptr) (x : Z) : Prop :=
(GQ <= x < GQ + 32) \/ (QMUT <= x < QMUT + 4) \/ (IA <= x < 0x1743f8) \/ (IA_FLAG <= x < IA_FLAG + 4)
\/ (exists j, In j JG /\ (in_iv (slot_beg RE 24 j, class_size 24) x \/ in_sh (slot_beg RE 24 j, class_size 24) x))
\/ (exists id n i, In (APrim id n) Qs /\ tag_at G (class_of n) i = Some (TQuar (APrim id n))
/\ (in_iv (slot_beg RE (class_of n) i, class_size (class_of n)) x \/ in_sh (slot_beg RE (class_of n) i, class_size (class_of n)) x))
\/ (exists mb n, In (ASec mb n) Qs
/\ (mb + kPage <= x < mb + sec_map_size n \/ in_sh (mb + kPage, sec_map_size n - kPage) x)).

Section Keep.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Variables (QA : aptr -> Z) (JG : list Z) (Qs : list aptr).
Hypothesis FJG : Forall (fun j => tag_at G 24 j = Some TQOwn) JG.

Variable m0 : mem.
Hypothesis REP0 : forall q, In q Qs -> qptr_rep a LB0 G RE m0 QA q.

Local Notation KEEP := (rq_keep G RE JG Qs).

Lemma rq_transport : forall (m m' : mem) gq rb,
agree_on asegs KEEP m m' ->
qrep RE G m QA GQ gq JG -> rw_cells asegs m QMUT [C1 (b8 0); C1 (b8 rb); C1 (b8 0); C1 (b8 0)] -> ia_inv m ->
(forall q, In q Qs -> qptr_rep a LB0 G RE m QA q) ->
qrep RE G m' QA GQ gq JG /\ rw_cells asegs m' QMUT [C1 (b8 0); C1 (b8 rb); C1 (b8 0); C1 (b8 0)] /\ ia_inv m'
/\ (forall q, In q Qs -> qptr_rep a LB0 G RE m' QA q).
Proof.
intros m m' gq rb AG GQR HM HI REP. split; [| split; [| split]].
- eapply qrep_agree; [exact AG| exact GQR| | |].
+ intros x Hx. left. exact Hx.
+ intros j x Hj Hx. do 4 right; left. exists j. auto.
+ intros j x Hj Hx. do 4 right; left. exists j. auto.
- eapply rw_cells_agree; [exact AG| exact HM|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. lia.
- eapply ia_inv_agree; [exact AG| exact HI|]. intros x [Hx|Hx]; [do 2 right; left; exact Hx| do 3 right; left; exact Hx].
- intros q Hq. pose proof (REP q Hq) as R. destruct q as [id n|mb n]; cbn [qptr_rep] in R |- *.
+ destruct R as (i & Ht & Hpr & HQA & QM). exists i. split; [exact Ht|]. split; [exact Hpr|]. split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => in_iv (slot_beg RE (class_of n) i, class_size (class_of n)) x \/ in_sh (slot_beg RE (class_of n) i, class_size (class_of n)) x));
[| exact QM| |].
* eapply agree_on_mono; [exact AG|]. intros x Hx. do 5 right; left. exists id, n, i. auto.
* intros x Hx. left. split; cbn [fst snd]; lia.
* intros x Hx. right. split; cbn [fst snd]; [lia|].
replace (slot_beg RE (class_of n) i + class_size (class_of n) - slot_beg RE (class_of n) i) with (class_size (class_of n)) in Hx by lia. lia.
+ destruct R as (Hin & Hnl & Hpr & HQA & QM). split; [exact Hin|]. split; [exact Hnl|]. split; [exact Hpr|]. split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => mb + kPage <= x < mb + sec_map_size n \/ in_sh (mb + kPage, sec_map_size n - kPage) x)); [| exact QM| |].
* eapply agree_on_mono; [exact AG|]. intros x Hx. do 6 right. exists mb, n. auto.
* intros x Hx. left. exact Hx.
* intros x Hx. right. split; cbn [fst snd]; [lia|].
replace (mb + sec_map_size n - (mb + kPage)) with (sec_map_size n - kPage) in Hx by lia. lia.
Qed.

Lemma rq_keep_fp : forall x, KEEP x -> fp_RQuar a LB0 G RE X x.
Proof.
intros x [H|[H|[H|[H|[H|[H|H]]]]]]; unfold GQ, QMUT, IA, IA_FLAG in *.
- right; right; left. split; cbn [fst snd]; lia.
- right; right; left. split; cbn [fst snd]; lia.
- do 3 right; left. split; cbn [fst snd]; lia.
- do 4 right; left. split; cbn [fst snd]; lia.
- destruct H as (j & Hj & [Hx|Hx]); pose proof (proj1 (List.Forall_forall _ _) FJG j Hj) as Tj.
+ do 5 right; left. exists 24, j, TQOwn. auto.
+ do 6 right; left. exists 24, j, TQOwn. auto.
- destruct H as (id & n & i & Hq & Ht & [Hx|Hx]).
+ do 5 right; left. exists (class_of n), i, (TQuar (APrim id n)). auto.
+ do 6 right; left. exists (class_of n), i, (TQuar (APrim id n)). auto.
- destruct H as (mb & n & Hq & Hx). pose proof (REP0 _ Hq) as (Hin & Hnl & _). destruct Hx as [Hx|Hx].
+ do 7 right; left. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req]. auto.
+ do 8 right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req]. auto.
Qed.

Lemma keep_pzoneP : forall x, (fp_RPrim G RE X x \/ fp_RStats RE X x \/ band_lo <= x) -> KEEP x -> False.
Proof.
intros x [F|[F|F]] K; pose proof (rq_keep_fp x K) as Q.
- exact (fpQ_RPrim a LB0 FS0 G RE X GC x Q F).
- exact (fpQ_RStats a LB0 FS0 G RE X GC x Q F).
- pose proof (fp_RQuar_cz a LB0 FS0 G RE X GC x Q ltac:(left; exact F)). exact H.
Qed.

Lemma keep_TQ : forall x, rl_T X + 80 <= x < rl_T X + 208 -> KEEP x -> False.
Proof.
intros x Hx K. pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & TC & TP & _). cbn [fst snd] in TK, TC, TP.
unfold iv_disjoint in TP; cbn [fst snd] in TP. rewrite ?KHI_eq in TK. pose proof SH_band as SHB0. pose proof kconsts as (_ & _ & _ & _ & KP & _).
destruct K as [H|[H|[H|[H|[H|[H|H]]]]]]; unfold GQ, QMUT, IA, IA_FLAG, A_INSTANCE in *; try lia.
- destruct H as (j & Hj & [Hj2|Hj2]); pose proof (proj1 (List.Forall_forall _ _) FJG j Hj) as Tj.
+ pose proof (slot_prim a LB0 FS0 G RE X GC 24 j TQOwn Tj) as (P1 & P2 & _). unfold prim_hi, prim_lo in *. destruct Hj2; cbn [fst snd] in *. lia.
+ pose proof (slot_band a LB0 FS0 G RE X GC 24 j TQOwn x Tj Hj2). lia.
- destruct H as (id & n & i & Hq & Ht & [H2|H2]).
+ pose proof (slot_prim a LB0 FS0 G RE X GC _ _ _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in *. destruct H2; cbn [fst snd] in *. lia.
+ pose proof (slot_band a LB0 FS0 G RE X GC _ _ _ x Ht H2). lia.
- destruct H as (mb & n & Hq & H2). pose proof (REP0 _ Hq) as (Hin & _ & Hpr & _).
pose proof (sec_facts a LB0 FS0 G RE X GC _ Hin) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
pose proof (sec_map_size_ge n ltac:(lia) Hpr) as [M1 M2].
destruct H2 as [H2|H2].
+ pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D. lia.
+ pose proof (sec_band a LB0 FS0 G RE X GC (mkSec mb (sec_map_size n) n) x Hin). cbn [se_beg se_size] in H. specialize (H H2). lia.
Qed.

Lemma keep_slot : forall c i t x, tag_at G c i = Some t ->
(c = 24 -> In i JG -> False) -> (forall id n, t = TQuar (APrim id n) -> In (APrim id n) Qs -> False) ->
(in_iv (slot_beg RE c i, class_size c) x \/ in_sh (slot_beg RE c i, class_size c) x) -> KEEP x -> False.
Proof.
intros c i t x Ht NJ NQ Hx K. pose proof kconsts as (_ & _ & _ & _ & KP & _). pose proof SH_band as SHB0.
pose proof (slot_prim a LB0 FS0 G RE X GC c i t Ht) as (P1 & P2 & P3 & _ & _ & _ & _ & SZ & _).
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in *. rewrite ?KHI_eq in PK. idtac.
assert (XB : (al_space_beg (ae_L RE) <= x < al_space_beg (ae_L RE) + 2^37 + 4096) \/ (0x2008fff7000 <= x < SH band_lo)).
{ destruct Hx as [Hx|Hx]; [left; destruct Hx; cbn [fst snd] in *; lia| right; exact (slot_band a LB0 FS0 G RE X GC c i t x Ht Hx)]. }

assert (OTHER : forall c' i' t', tag_at G c' i' = Some t' -> (c <> c' \/ i <> i') ->
(in_iv (slot_beg RE c' i', class_size c') x \/ in_sh (slot_beg RE c' i', class_size c') x) -> False).
{ intros c' i' t' Ht' NE Hx'. pose proof (slots_disjoint a LB0 FS0 G RE X GC c i t c' i' t' Ht Ht' NE) as D.
pose proof (slot_prim a LB0 FS0 G RE X GC c' i' t' Ht') as (P1' & P2' & P3' & _ & _ & _ & _ & SZ' & _). unfold prim_hi, prim_lo in *.
destruct Hx as [Hx|Hx], Hx' as [Hx'|Hx'].
- destruct Hx, Hx'; cbn [fst snd] in *. lia.
- pose proof (slot_band a LB0 FS0 G RE X GC c' i' t' x Ht' Hx'). destruct Hx; cbn [fst snd] in *. lia.
- pose proof (slot_band a LB0 FS0 G RE X GC c i t x Ht Hx). destruct Hx'; cbn [fst snd] in *. lia.
- exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (slot_beg RE c' i') (class_size c') x P3 P3' ltac:(lia) ltac:(lia) D Hx Hx'). }
destruct K as [H|[H|[H|[H|[H|[H|H]]]]]]; unfold GQ, QMUT, IA, IA_FLAG, A_INSTANCE in *; try lia.
- destruct H as (j & Hj & Hj2). pose proof (proj1 (List.Forall_forall _ _) FJG j Hj) as Tj.
apply (OTHER 24 j TQOwn Tj); [| exact Hj2]. destruct (Z.eq_dec c 24) as [->|NE]; [right; intros ->; exact (NJ eq_refl Hj)| left; exact NE].
- destruct H as (id & n & i' & Hq & Ht' & H2).
apply (OTHER _ _ _ Ht'); [| exact H2]. destruct (Z.eq_dec c (class_of n)) as [->|NE]; [right; intros ->| left; exact NE].
rewrite Ht in Ht'. injection Ht' as E. exact (NQ id n E Hq).
- destruct H as (mb & n & Hq & H2). pose proof (REP0 _ Hq) as (Hin & _ & Hpr & _).
pose proof (sec_facts a LB0 FS0 G RE X GC _ Hin) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3). cbn [se_beg se_size se_req] in *.
unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1. rewrite ?KHI_eq in E2. idtac.
pose proof (sec_map_size_ge n ltac:(lia) Hpr) as [M1 M2].
destruct Hx as [Hx|Hx], H2 as [H2|H2].
+ destruct Hx; cbn [fst snd] in *. lia.
+ pose proof (sec_band a LB0 FS0 G RE X GC (mkSec mb (sec_map_size n) n) x Hin) as SB. cbn [se_beg se_size] in SB. specialize (SB H2). destruct Hx; cbn [fst snd] in *. lia.
+ pose proof (slot_band a LB0 FS0 G RE X GC c i t x Ht Hx). lia.
+ exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (mb + kPage) (sec_map_size n - kPage) x P3 ltac:(rewrite KP; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hx H2).
Qed.

Lemma keep_sec : forall e x, In e (as_reg a) -> (forall n, In (ASec (se_beg e) n) Qs -> False) ->
(se_beg e + kPage <= x < se_beg e + se_size e \/ in_sh (se_beg e + kPage, se_size e - kPage) x) -> KEEP x -> False.
Proof.
intros e x He NQ Hx K. pose proof kconsts as (_ & _ & _ & _ & KP & _). pose proof SH_band as SHB0.
pose proof (sec_facts a LB0 FS0 G RE X GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & _). unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1.
rewrite ?KHI_eq in E2. idtac. pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1.
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in *. rewrite ?KHI_eq in PK. idtac.
assert (XB : (se_beg e + kPage <= x < se_beg e + se_size e) \/ (0x7fff7000 <= x < 0x10007fff8000)).
{ destruct Hx as [Hx|Hx]; [left; exact Hx| right; exact (sec_band a LB0 FS0 G RE X GC e x He Hx)]. }
assert (SLOT : forall c' i' t', tag_at G c' i' = Some t' ->
(in_iv (slot_beg RE c' i', class_size c') x \/ in_sh (slot_beg RE c' i', class_size c') x) -> False).
{ intros c' i' t' Ht' Hx'. pose proof (slot_prim a LB0 FS0 G RE X GC c' i' t' Ht') as (P1' & P2' & P3' & _ & _ & _ & _ & SZ' & _). unfold prim_hi, prim_lo in *.
destruct Hx as [Hx|Hx], Hx' as [Hx'|Hx'].
- destruct Hx'; cbn [fst snd] in *. lia.
- pose proof (slot_band a LB0 FS0 G RE X GC c' i' t' x Ht' Hx'). lia.
- pose proof (sec_band a LB0 FS0 G RE X GC e x He Hx). destruct Hx'; cbn [fst snd] in *. lia.
- exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (slot_beg RE c' i') (class_size c') x ltac:(rewrite KP; Z.div_mod_to_equations; lia) P3' ltac:(lia) ltac:(lia) ltac:(lia) Hx Hx'). }
destruct K as [H|[H|[H|[H|[H|[H|H]]]]]]; unfold GQ, QMUT, IA, IA_FLAG, A_INSTANCE in *; try lia.
- destruct H as (j & Hj & Hj2). exact (SLOT 24 j TQOwn (proj1 (List.Forall_forall _ _) FJG j Hj) Hj2).
- destruct H as (id & n & i' & Hq & Ht' & H2). exact (SLOT _ _ _ Ht' H2).
- destruct H as (mb & n & Hq & H2). pose proof (REP0 _ Hq) as (Hin & _ & Hpr & _).
destruct (decide (se_beg e = mb)) as [EQ|NE].
{ exfalso. apply (NQ n). rewrite EQ. exact Hq. }
pose proof (sec_facts a LB0 FS0 G RE X GC _ Hin) as (E1' & E2' & E3' & E4' & E5' & E6' & _). cbn [se_beg se_size se_req] in *.
rewrite ?KHI_eq in E2'. idtac. pose proof (sec_map_size_ge n ltac:(lia) Hpr) as [M1' M2'].
pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg a) e (mkSec mb (sec_map_size n) n)
(gc_sec_disj a LB0 FS0 G RE X GC) He Hin ltac:(cbn; intros EQ; apply NE; exact (f_equal fst EQ))) as D.
unfold iv_disjoint in D. cbn [fst snd se_beg se_size] in D.
destruct Hx as [Hx|Hx], H2 as [H2|H2].
+ (first [ clear - D M2' M1' E6' E2' E1' NE XB PK M1 E6 E2 E1 KP H2 n mb Hx x e RE BAND; lia | lia ]).
+ pose proof (sec_band a LB0 FS0 G RE X GC (mkSec mb (sec_map_size n) n) x Hin) as SB. cbn [se_beg se_size] in SB. specialize (SB H2). (first [ clear - SB D M2' M1' E6' E2' E1' NE PK M2 M1 E6 E4 E2 E1 KP n mb Hx x e RE BAND; lia | lia ]).
+ pose proof (sec_band a LB0 FS0 G RE X GC e x He Hx). (first [ clear - H D M2' M1' E6' E2' E1' NE PK M2 M1 E6 E4 E2 E1 KP H2 n mb x e RE BAND; lia | lia ]).
+ exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (mb + kPage) (sec_map_size n - kPage) x
ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H20 q3 H10 q1 H0 H r q D M1' E6' E2' E1' r1 NE PK M1 E6 E2 E1 r3 n mb e RE BAND; lia | lia ])) ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H20 q3 H10 q1 H0 H r q D M1' E6' E2' E1' r1 NE PK M1 E6 E2 E1 r3 n mb e RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D M2' M1' E6' E2' E1' NE PK M2 M1 E6 E4 E2 E1 KP n mb e RE BAND; lia | lia ])) Hx H2).
Qed.
End Keep.

Lemma rq_keep_tags : forall G G' RE JG Qs x,
(forall c i q, tag_at G c i = Some (TQuar q) <-> tag_at G' c i = Some (TQuar q)) ->
rq_keep G RE JG Qs x -> rq_keep G' RE JG Qs x.
Proof.
intros G G' RE JG Qs x TQ K. destruct K as [H|[H|[H|[H|[H|[H|H]]]]]]; unfold rq_keep; try tauto.
destruct H as (id & n & i & Hq & Ht & Hx). do 5 right; left. exists id, n, i. split; [exact Hq|]. split; [apply TQ; exact Ht| exact Hx].
Qed.

Lemma qptr_rep_ext {BAND : Band} : forall a a' LB G G' RE m QA q,
qptr_rep a LB G RE m QA q -> as_reg a' = as_reg a ->
(forall c i q, tag_at G c i = Some (TQuar q) <-> tag_at G' c i = Some (TQuar q)) ->
qptr_rep a' LB G' RE m QA q.
Proof.
intros a a' LB G G' RE m QA q R ER TQ. destruct q as [id n|mb n]; cbn [qptr_rep] in R |- *.
- destruct R as (i & Ht & R). exists i. split; [apply TQ; exact Ht| exact R].
- rewrite ER. exact R.
Qed.

Lemma qchunk_mem_agree_but_user {BAND : Band} : forall (P : Z -> Prop) m m' lo hi A n,
agree_on asegs P m m' -> wmono asegs m m' -> qchunk_mem m lo hi A n ->
(forall x, lo <= x < A -> P x) -> (forall x, SH lo <= x < SH lo + (hi - lo) / 8 -> P x) ->
qchunk_mem m' lo hi A n.
Proof.
intros P m m' lo hi A n AG WM QM HP HS.
pose proof (qchunk_geom m lo hi A n QM) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & q & g & r & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
destruct QM as (LEFT & (b1 & id & Hb1 & HDR) & JUNK & (sj & SHD) & PURE).
split; [| split; [| split; [| split; [| exact PURE]]]].
- intros Hrz. destruct (LEFT Hrz) as [L1 L2]. split.
+ eapply rw_cells_agree; [exact AG| exact L1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply HP. lia.
+ eapply hjunk_agree; [exact AG| exact L2|]. intros x Hx. apply HP. lia.
- exists b1, id. split; [exact Hb1|]. eapply rw_cells_agree; [exact AG| exact HDR|]. intros x Hx. cbn [qhdr_cells cells_size csize Nat.add] in Hx. apply HP. lia.
- eapply hjunk_wmono; [exact JUNK| exact WM].
- exists sj. eapply rw_cells_agree; [exact AG| exact SHD|]. intros x Hx. apply HS.
cbn [cells_size csize] in Hx. unfold fas in Hx. rewrite !Nat.add_0_r, !Nat2Z.inj_add, !Z2Nat.id in Hx by lia.
rewrite Q1, Q4, Q6, Q8 in *. rewrite !(Z.mul_comm 8), !Z.div_mul in Hx |- * by lia. lia.
Qed.

Lemma RQuarM_pend_agree {BAND : Band} : forall rb bt bg p A a LB FS G RE X m m',
gcons a LB FS G RE X -> RQuarM rb bt bg [(p, A)] a LB G RE X m -> wmono asegs m m' ->
agree_on asegs (fun x => fp_RQuar a LB G RE X x /\ ~ (A <= x < A + 8)) m m' ->
RQuarM rb bt bg [(p, A)] a LB G RE X m'.
Proof.
intros rb bt bg p A a LB FS G RE X m m' GC RQ WM AG.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND).
pose proof PQA as PQA0. apply Forall_cons_iff in PQA as [EQA _]. cbn [fst snd] in EQA.
pose proof HT as (TQC & BMT & FJT & QWT). pose proof HG as (GQC & BMG & FJG & QWG).
assert (FJ : Forall (fun j => tag_at G 24 j = Some TQOwn) (JT ++ JG)) by (apply Forall_app; split; assumption).
set (Qs' := qptrs (as_tq a) ++ qptrs (as_gq a)).
assert (EQQ : qall [(p, A)] a = p :: Qs') by reflexivity.
assert (NDQ : List.NoDup (p :: Qs')) by (rewrite <- EQQ; exact NDP).
assert (NIp : ~ In p Qs') by (inversion NDQ; assumption).
assert (REP' : forall q', In q' Qs' -> qptr_rep a LB G RE m QA q') by (intros q' Hq; apply REP; rewrite EQQ; right; exact Hq).
pose proof (REP p ltac:(rewrite EQQ; left; reflexivity)) as REPp.

assert (PC0 : exists lo hi, qchunk_mem m lo hi A (aptr_req p)
/\ (forall x, lo <= x < hi \/ in_sh (lo, hi - lo) x -> fp_RQuar a LB G RE X x)
/\ (forall x, lo <= x < hi \/ in_sh (lo, hi - lo) x -> rq_keep G RE (JT ++ JG) Qs' x -> False)
/\ (forall x, lo <= x < hi -> ~ (rl_T X <= x < rl_T X + 4096))
/\ (qchunk_mem m' lo hi A (aptr_req p) -> qptr_rep a LB G RE m' QA p)).
{ destruct p as [id n0|mb n0]; cbn [qptr_rep aptr_req] in REPp |- *.
- destruct REPp as (i & Ht & Hpr & HQA & QM). rewrite EQA in QM. exists (slot_beg RE (class_of n0) i), (slot_beg RE (class_of n0) i + class_size (class_of n0)).
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & _). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & _ & _ & TD & _). unfold iv_disjoint, prim_hi, prim_lo in TD, P1, P2; cbn [fst snd] in TD.
split; [exact QM|]. split; [| split; [| split]].
+ intros x [Hx|Hx]; [do 5 right; left| do 6 right; left]; exists (class_of n0), i, (TQuar (APrim id n0)); (split; [exact Ht|]); (split; [reflexivity|]).
* split; cbn [fst snd]; lia.
* replace (slot_beg RE (class_of n0) i + class_size (class_of n0) - slot_beg RE (class_of n0) i) with (class_size (class_of n0)) in Hx by lia. exact Hx.
+ intros x Hx K. refine (keep_slot a LB FS G RE X GC QA (JT ++ JG) Qs' FJ m REP' (class_of n0) i _ x Ht _ _ _ K).
* intros E24 Hi. pose proof (proj1 (List.Forall_forall _ _) FJ i Hi) as Ti. rewrite E24, Ti in Ht. discriminate.
* intros id' n' E Hq. injection E as <- <-. exact (NIp Hq).
* destruct Hx as [Hx|Hx]; [left; split; cbn [fst snd]; lia| right].
replace (slot_beg RE (class_of n0) i + class_size (class_of n0) - slot_beg RE (class_of n0) i) with (class_size (class_of n0)) in Hx by lia. exact Hx.
+ intros x Hx. lia.
+ intros QM'. exists i. split; [exact Ht|]. split; [exact Hpr|]. split; [exact HQA|]. rewrite EQA. exact QM'.
- destruct REPp as (Hin & Hnl & Hpr & HQA & QM). rewrite EQA in QM. exists (mb + kPage), (mb + sec_map_size n0).
split; [exact QM|]. split; [| split; [| split]].
+ intros x [Hx|Hx]; [do 7 right; left| do 8 right]; exists (mkSec mb (sec_map_size n0) n0); cbn [se_beg se_size se_req]; (split; [exact Hin|]); (split; [exact Hnl|]).
* lia.
* replace (mb + sec_map_size n0 - (mb + kPage)) with (sec_map_size n0 - kPage) in Hx by lia. exact Hx.
+ intros x Hx K. refine (keep_sec a LB FS G RE X GC QA (JT ++ JG) Qs' FJ m REP' (mkSec mb (sec_map_size n0) n0) x Hin _ _ K); cbn [se_beg se_size].
* intros n' Hq. pose proof (REP' _ Hq) as (Hin' & _). cbn [qptr_rep] in Hin'.
pose proof (NoDup_map_In_inj se_beg (as_reg a) _ _ (gc_sec_nodup a LB FS G RE X GC) Hin Hin' eq_refl) as E. injection E as En. subst n'. exact (NIp Hq).
* destruct Hx as [Hx|Hx]; [left; lia| right]. replace (mb + sec_map_size n0 - (mb + kPage)) with (sec_map_size n0 - kPage) in Hx by lia. exact Hx.
+ intros x Hx. pose proof (sec_facts _ _ _ _ _ _ GC _ Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & D3). cbn [se_beg se_size] in D3.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D. lia.
+ intros QM'. split; [exact Hin|]. split; [exact Hnl|]. split; [exact Hpr|]. split; [exact HQA|]. rewrite EQA. exact QM'. }
destruct PC0 as (plo & phi & QMp & PZ & PK & PT & PBACK).
pose proof (qchunk_geom _ _ _ _ _ QMp) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & q & g & r & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).

assert (AGK : agree_on asegs (fun x => rq_keep G RE (JT ++ JG) Qs' x \/ rl_T X + 80 <= x < rl_T X + 112) m m').
{ eapply agree_on_mono; [exact AG|]. intros x [K|K].
- split; [exact (rq_keep_fp a LB G RE X QA (JT ++ JG) Qs' FJ m REP' x K)|]. intros Hx. apply (PK x); [left; lia| exact K].
- split; [left; split; cbn [fst snd]; lia|]. intros Hx. apply (PT x); [lia|].
pose proof (rlay_obj_facts RE X _ (gc_rlay _ _ _ _ _ _ GC) (T_obj RE X)) as (_ & TK & _). cbn [fst] in TK. lia. }
assert (HT' : qrep RE G m' QA (TQ X) (as_tq a) JT).
{ eapply qrep_agree; [exact AGK| exact HT| intros x Hx; right; unfold TQ in Hx; lia| |].
- intros j x Hj Hx. left. do 4 right; left. exists j. split; [apply in_app_iff; left; exact Hj| left; exact Hx].
- intros j x Hj Hx. left. do 4 right; left. exists j. split; [apply in_app_iff; left; exact Hj| right; exact Hx]. }
destruct (rq_transport a LB G RE QA JG Qs' m m' (as_gq a) rb) as (HG' & HM' & HI' & REP2).
{ eapply agree_on_mono; [exact AGK|]. intros x Kx. left. revert Kx. unfold rq_keep. intros [K|[K|[K|[K|[K|[K|K]]]]]]; try (clear - K; tauto).
do 4 right; left. destruct K as (j & Hj & K). exists j. split; [apply in_app_iff; right; exact Hj| exact K]. }
{ exact HG. } { exact HM. } { exact HI. } { exact REP'. }

assert (QMp' : qchunk_mem m' plo phi A (aptr_req p)).
{ eapply (qchunk_mem_agree_but_user (fun x => (plo <= x < A) \/ in_sh (plo, phi - plo) x)); [| exact WM| exact QMp| intros x Hx; left; exact Hx| intros x Hx; right; split; cbn [fst snd]; lia].
eapply agree_on_mono; [exact AG|]. intros x Hx. split.
- apply PZ. destruct Hx as [Hx|Hx]; [left; lia| right; exact Hx].
- destruct Hx as [Hx|Hx]; [lia|].
assert (PB0 : plo + (phi - plo) <= band_lo) by lia.
pose proof (in_sh_band plo (phi - plo) x ltac:(Z.div_mod_to_equations; lia) ltac:(lia) (proj1 G3) PB0 Hx) as B0. unfold kLowEnd, KHI in B0.
clear - B0 G3 G1 G2 Q3 Q5. lia. }
exists JT, JG, QA. split; [exact HT'|]. split; [exact HG'|]. split; [exact HM'|]. split; [exact HI'|].
repeat (split; [assumption|]). split; [| split; [exact TQP| split; [exact PQA0| exact BND]]].
intros q' Hq. rewrite EQQ in Hq. destruct Hq as [<-|Hq]; [exact (PBACK QMp')| exact (REP2 q' Hq)].
Qed.

Lemma batches_mem_nx_QA : forall RE m (QA QA' : aptr -> Z) bs J fin,
(forall q, In q (concat (map b_chunks bs)) -> QA' q = QA q) ->
batches_mem_nx RE m QA bs J fin -> batches_mem_nx RE m QA' bs J fin.
Proof.
intros RE m QA QA' bs. induction bs as [|b bs IH]; intros J fin E H; destruct J as [|j J]; cbn in H |- *; try exact H.
destruct H as [(B1 & B2 & B3 & B4) H]. split; [| apply IH; [intros q Hq; apply E; cbn; apply in_app_iff; right; exact Hq| exact H]].
split; [exact B1|]. split; [| split; [exact B3| exact B4]].
replace (map (fun p => Z_to_bv 64 (QA' p - 16)) (b_chunks b)) with (map (fun p => Z_to_bv 64 (QA p - 16)) (b_chunks b)); [exact B2|].
apply map_ext_in. intros q Hq. rewrite (E q); [reflexivity|]. cbn. apply in_app_iff. left. exact Hq.
Qed.

Lemma qrep_QA : forall RE G m (QA QA' : aptr -> Z) C q J,
(forall p, In p (qptrs q) -> QA' p = QA p) -> qrep RE G m QA C q J -> qrep RE G m QA' C q J.
Proof.
intros RE G m QA QA' C q J E (R1 & R2 & R3 & R4). split; [exact R1|]. split; [| split; [exact R3| exact R4]].
eapply batches_mem_nx_QA; [exact E| exact R2].
Qed.

Section Free.
Context {BAND : Band}.
Variables (a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB FS G RE X.
Variables (rb bt bg : Z) (m m' : mem) (p : aptr) (A n : Z).
Hypothesis RQ : RQuarM rb bt bg [] a LB G RE X m.
Hypothesis INB : In (p, A, n) LB.
Hypothesis AG : agree_on asegs (fp_RQuar a LB G RE X) m m'.

Let QA' (QA : aptr -> Z) : aptr -> Z := fun q => if aptr_eqb q p then A else QA q.

Lemma QA'_p : forall QA, QA' QA p = A.
Proof. intros QA. unfold QA'. rewrite aptr_eqb_refl'. reflexivity. Qed.
Lemma QA'_other : forall QA q, q <> p -> QA' QA q = QA q.
Proof. intros QA q NE. unfold QA'. destruct (aptr_eqb q p) eqn:E; [| reflexivity]. exfalso. apply NE. apply aptr_eqb_true. exact E. Qed.

Lemma RQuarM_free_prim : forall id c i,
p = APrim id n -> c = class_of n -> tag_at G c i = Some (TLive p) -> A = slot_beg RE c i + rz_size n ->
qchunk_mem m' (slot_beg RE c i) (slot_beg RE c i + class_size c) A n ->
RQuarM rb bt bg [(p, A)] a (alb_remove p LB) (set_tag c i (TQuar p) G) RE X m'.
Proof.
intros id c i Ep Ec Ht HA QM'.
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND).
pose proof (retag_at G c i (TLive p) (TQuar p) Ht) as RT.
destruct (gc_blocks a LB FS G RE X GC p A n INB) as [(id0 & i0 & E0 & Hn & HP & Ht0 & _)|(mb & E0 & _)]; [| subst p; discriminate].
assert (NIq : ~ In p (qall [] a)).
{ intros Hin. pose proof (REP p Hin) as R. rewrite Ep in R. cbn [qptr_rep] in R. destruct R as (i' & Ht' & _).
rewrite <- Ep, <- Ec in Ht'.
pose proof (gc_unique a LB FS G RE X GC _ _ _ _ p _ _ Ht Ht' ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
rewrite Ht in Ht'. discriminate. }
assert (EQA : forall q, In q (qall [] a) -> QA' QA q = QA q) by (intros q Hq; apply QA'_other; intros ->; exact (NIq Hq)).
assert (T1 : forall c' i', tag_at (set_tag c i (TQuar p) G) c' i' = Some TQOwn <-> tag_at G c' i' = Some TQOwn).
{ intros c' i'. rewrite RT. destruct ((c' =? c) && (i' =? i)) eqn:E; [| tauto].
apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' i'. rewrite Ht. split; intros; discriminate. }
assert (T2 : forall c' i' q, q <> p -> (tag_at G c' i' = Some (TQuar q) <-> tag_at (set_tag c i (TQuar p) G) c' i' = Some (TQuar q))).
{ intros c' i' q NE. rewrite RT. destruct ((c' =? c) && (i' =? i)) eqn:E; [| tauto].
apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' i'. rewrite Ht. split; intros HH; [discriminate| injection HH as HH; exfalso; exact (NE (eq_sym HH))]. }
assert (QREP : forall Cq qq J, (forall x, Cq <= x < Cq + 32 -> fp_RQuar a LB G RE X x) -> (forall q, In q (qptrs qq) -> In q (qall [] a)) ->
qrep RE G m QA Cq qq J -> qrep RE (set_tag c i (TQuar p) G) m' (QA' QA) Cq qq J).
{ intros Cq qq J HC HQ R. pose proof R as (_ & _ & R3 & _).
assert (R' : qrep RE G m' QA Cq qq J).
{ eapply qrep_agree; [exact AG| exact R| exact HC| |].
- intros j x Hj Hx. do 5 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)|]. auto.
- intros j x Hj Hx. do 6 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)|]. auto. }
apply (qrep_QA RE _ m' QA (QA' QA)) in R'; [| intros q Hq; apply EQA; apply HQ; exact Hq].
destruct R' as (R1' & R2' & R3' & R4'). split; [exact R1'|]. split; [exact R2'|]. split; [| exact R4'].
apply List.Forall_forall. intros j Hj. apply T1. exact (proj1 (List.Forall_forall _ _) R3' j Hj). }
exists JT, JG, (QA' QA).
split; [apply QREP; [intros x Hx; left; unfold TQ in Hx; split; cbn [fst snd]; lia| intros q Hq; unfold qall; cbn [map app]; apply in_app_iff; left; exact Hq| exact HT]|].
split; [apply QREP; [intros x Hx; right; right; left; unfold GQ in Hx; split; cbn [fst snd]; lia| intros q Hq; unfold qall; cbn [map app]; apply in_app_iff; right; exact Hq| exact HG]|].
split; [eapply rw_cells_agree; [exact AG| exact HM|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; right; left; unfold QMUT in Hx; split; cbn [fst snd]; lia|].
split; [eapply ia_inv_agree; [exact AG| exact HI|]; intros x [Hx|Hx]; [do 3 right; left| do 4 right; left]; unfold IA, IA_FLAG in *; split; cbn [fst snd]; lia|].
split; [exact ND|]. split; [intros j Hj; apply TQO; apply T1; exact Hj|]. split; [intros c' j Hj; apply (C24 c' j); apply T1; exact Hj|].
assert (EQQ : qall [(p, A)] a = p :: qall [] a) by reflexivity. rewrite EQQ.
split; [constructor; [exact NIq| exact NDP]|].
split.
{ intros q [<-|Hq].
- rewrite Ep. cbn [qptr_rep]. rewrite <- Ep, <- Ec. exists i. split; [rewrite RT, !Z.eqb_refl; reflexivity|]. split; [exact HP|].
rewrite QA'_p. split; [exact HA| exact QM'].
- assert (NE : q <> p) by (intros ->; exact (NIq Hq)).
pose proof (REP q Hq) as R. destruct q as [idq nq|mbq nq]; cbn [qptr_rep] in R |- *.
+ destruct R as (iq & Htq & Hpr & HQA & QM). exists iq. split; [apply (T2 _ _ _ NE); exact Htq|]. split; [exact Hpr|].
rewrite (QA'_other QA _ NE). split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => in_iv (slot_beg RE (class_of nq) iq, class_size (class_of nq)) x \/ in_sh (slot_beg RE (class_of nq) iq, class_size (class_of nq)) x));
[| exact QM| intros x Hx; left; split; cbn [fst snd]; lia| intros x Hx; right; split; cbn [fst snd]; [lia|]].
* eapply agree_on_mono; [exact AG|]. intros x [Hx|Hx]; [do 5 right; left| do 6 right; left]; exists (class_of nq), iq, (TQuar (APrim idq nq)); auto.
* replace (slot_beg RE (class_of nq) iq + class_size (class_of nq) - slot_beg RE (class_of nq) iq) with (class_size (class_of nq)) in Hx by lia. lia.
+ destruct R as (Hin & Hnl & Hpr & HQA & QM). split; [exact Hin|]. split; [intros (A2 & HL); apply Hnl; exists A2; exact (proj1 (proj1 (In_alb_remove _ _ _) HL))|].
split; [exact Hpr|]. rewrite (QA'_other QA _ NE). split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => mbq + kPage <= x < mbq + sec_map_size nq \/ in_sh (mbq + kPage, sec_map_size nq - kPage) x));
[| exact QM| intros x Hx; left; exact Hx| intros x Hx; right; split; cbn [fst snd]; [lia|]].
* eapply agree_on_mono; [exact AG|]. intros x [Hx|Hx]; [do 7 right; left| do 8 right]; exists (mkSec mbq (sec_map_size nq) nq); cbn [se_beg se_size se_req]; auto.
* replace (mbq + sec_map_size nq - (mbq + kPage)) with (sec_map_size nq - kPage) in Hx by lia. lia. }
split.
{ intros c' i' q Hq'. rewrite RT in Hq'. destruct ((c' =? c) && (i' =? i)) eqn:E.
- injection Hq' as <-. apply andb_prop in E as [E1 _]. apply Z.eqb_eq in E1. subst c'. split; [left; reflexivity| rewrite Ep; cbn; symmetry; exact Ec].
- destruct (TQP c' i' q Hq') as [H1 H2]. split; [right; exact H1| exact H2]. }
split; [constructor; [cbn [fst snd]; apply QA'_p| constructor]| exact BND].
Qed.

Lemma RQuarM_free_sec : forall mb,
p = ASec mb n -> In (mkSec mb (sec_map_size n) n) (as_reg a) -> A = mb + kSecUserOff ->
qchunk_mem m' (mb + kPage) (mb + sec_map_size n) A n ->
RQuarM rb bt bg [(p, A)] a (alb_remove p LB) G RE X m'.
Proof.
intros mb Ep He HA QM'.
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND).
destruct (gc_blocks a LB FS G RE X GC p A n INB) as [(id0 & i0 & E0 & _)|(mb0 & E0 & Hn & HP & _)]; [subst p; discriminate|].
assert (NIq : ~ In p (qall [] a)).
{ intros Hin. pose proof (REP p Hin) as R. rewrite Ep in R. cbn [qptr_rep] in R. destruct R as (_ & Hnl & _).
apply Hnl. exists A. cbn [se_beg se_req]. rewrite <- Ep. exact INB. }
assert (EQA : forall q, In q (qall [] a) -> QA' QA q = QA q) by (intros q Hq; apply QA'_other; intros ->; exact (NIq Hq)).
assert (QREP : forall Cq qq J, (forall x, Cq <= x < Cq + 32 -> fp_RQuar a LB G RE X x) -> (forall q, In q (qptrs qq) -> In q (qall [] a)) ->
qrep RE G m QA Cq qq J -> qrep RE G m' (QA' QA) Cq qq J).
{ intros Cq qq J HC HQ R. pose proof R as (_ & _ & R3 & _).
assert (R' : qrep RE G m' QA Cq qq J).
{ eapply qrep_agree; [exact AG| exact R| exact HC| |].
- intros j x Hj Hx. do 5 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)|]. auto.
- intros j x Hj Hx. do 6 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)|]. auto. }
apply (qrep_QA RE _ m' QA (QA' QA)) in R'; [exact R'| intros q Hq; apply EQA; apply HQ; exact Hq]. }
exists JT, JG, (QA' QA).
split; [apply QREP; [intros x Hx; left; unfold TQ in Hx; split; cbn [fst snd]; lia| intros q Hq; unfold qall; cbn [map app]; apply in_app_iff; left; exact Hq| exact HT]|].
split; [apply QREP; [intros x Hx; right; right; left; unfold GQ in Hx; split; cbn [fst snd]; lia| intros q Hq; unfold qall; cbn [map app]; apply in_app_iff; right; exact Hq| exact HG]|].
split; [eapply rw_cells_agree; [exact AG| exact HM|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; right; left; unfold QMUT in Hx; split; cbn [fst snd]; lia|].
split; [eapply ia_inv_agree; [exact AG| exact HI|]; intros x [Hx|Hx]; [do 3 right; left| do 4 right; left]; unfold IA, IA_FLAG in *; split; cbn [fst snd]; lia|].
split; [exact ND|]. split; [exact TQO|]. split; [exact C24|].
assert (EQQ : qall [(p, A)] a = p :: qall [] a) by reflexivity. rewrite EQQ.
split; [constructor; [exact NIq| exact NDP]|].
split.
{ intros q [<-|Hq].
- rewrite Ep. cbn [qptr_rep]. split; [exact He|]. split.
+ intros (A2 & HL). cbn [se_beg se_req] in HL. apply In_alb_remove in HL as [_ NE]. apply NE. reflexivity.
+ split; [exact HP|]. rewrite <- Ep, QA'_p. split; [exact HA| exact QM'].
- assert (NE : q <> p) by (intros ->; exact (NIq Hq)).
pose proof (REP q Hq) as R. destruct q as [idq nq|mbq nq]; cbn [qptr_rep] in R |- *.
+ destruct R as (iq & Htq & Hpr & HQA & QM). exists iq. split; [exact Htq|]. split; [exact Hpr|].
rewrite (QA'_other QA _ NE). split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => in_iv (slot_beg RE (class_of nq) iq, class_size (class_of nq)) x \/ in_sh (slot_beg RE (class_of nq) iq, class_size (class_of nq)) x));
[| exact QM| intros x Hx; left; split; cbn [fst snd]; lia| intros x Hx; right; split; cbn [fst snd]; [lia|]].
* eapply agree_on_mono; [exact AG|]. intros x [Hx|Hx]; [do 5 right; left| do 6 right; left]; exists (class_of nq), iq, (TQuar (APrim idq nq)); auto.
* replace (slot_beg RE (class_of nq) iq + class_size (class_of nq) - slot_beg RE (class_of nq) iq) with (class_size (class_of nq)) in Hx by lia. lia.
+ destruct R as (Hin & Hnl & Hpr & HQA & QM). split; [exact Hin|]. split; [intros (A2 & HL); apply Hnl; exists A2; exact (proj1 (proj1 (In_alb_remove _ _ _) HL))|].
split; [exact Hpr|]. rewrite (QA'_other QA _ NE). split; [exact HQA|].
eapply (qchunk_mem_agree (fun x => mbq + kPage <= x < mbq + sec_map_size nq \/ in_sh (mbq + kPage, sec_map_size nq - kPage) x));
[| exact QM| intros x Hx; left; exact Hx| intros x Hx; right; split; cbn [fst snd]; [lia|]].
* eapply agree_on_mono; [exact AG|]. intros x [Hx|Hx]; [do 7 right; left| do 8 right]; exists (mkSec mbq (sec_map_size nq) nq); cbn [se_beg se_size se_req]; auto.
* replace (mbq + sec_map_size nq - (mbq + kPage)) with (sec_map_size nq - kPage) in Hx by lia. lia. }
split.
{ intros c' i' q Hq'. destruct (TQP c' i' q Hq') as [H1 H2]. split; [right; exact H1| exact H2]. }
split; [constructor; [cbn [fst snd]; apply QA'_p| constructor]| exact BND].
Qed.
End Free.
End Mqj.

Module Mqk.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Q0Do.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QYyZ.Mqc.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Z.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Variables (mb msz : Z).
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis MSZ : 4096 <= msz.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Hypothesis AVQ : mb + msz <= ptrarr_lo RE \/ ptrarr_lo RE + 0x800000 <= mb.
Hypothesis AVR : forall e, In e (as_reg a) -> mb + msz <= se_beg e \/ se_beg e + se_size e <= mb.

Set Default Proof Using "GC MBP MBK MBC MSZ AVO AVP AVQ AVR".

Lemma prim_hi_eq : prim_hi RE = prim_lo RE + 2^37 + 0x1000. Proof. reflexivity. Qed.
Lemma region_info_eq : region_info RE = prim_lo RE + 2^37. Proof. reflexivity. Qed.

Definition nmap (x : Z) : Prop := mb <= x < mb + msz \/ in_sh (mb, msz) x.

Local Ltac lits := rewrite ?KHI_eq in *.

Lemma nmap_where : forall x, nmap x ->
(mb <= x < mb + msz)
\/ (0x7fff7000 <= x < 0x10007fff8000 /\ in_sh (mb, msz) x).
Proof.
intros x [H|H]; [left; exact H| right; split; [| exact H]].
pose proof (in_sh_band mb msz x ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(clear - MBK MBC; lia) MBC H) as B.
unfold kLowEnd, KHI in B. exact B.
Qed.

Lemma nmap_apart : forall lo len x, lo mod 8 = 0 -> 0 <= len -> lowhigh lo len -> lo + len <= band_lo ->
(mb + msz <= lo \/ lo + len <= mb) ->
nmap x -> (lo <= x < lo + len \/ in_sh (lo, len) x) -> False.
Proof.
intros lo len x AL L K C D NM [R|R].
- destruct (nmap_where x NM) as [M|[B M]]; [lia|]. clear - K R B. lia.
- pose proof (in_sh_band lo len x AL L K C R) as B. unfold kLowEnd, KHI in B. destruct (nmap_where x NM) as [M|[B' M]].
+ clear - MBK M B. lia.
+ exact (in_sh_disjoint lo len mb msz x AL ltac:(clear - MBP; Z.div_mod_to_equations; lia) L ltac:(lia) ltac:(lia) R M).
Qed.

Lemma nmap_low : forall x, 0x10000 <= x < 0x647000 -> nmap x -> False.
Proof. intros x Hx NM. destruct (nmap_where x NM) as [M|[B _]]; [clear - MBK M Hx; lia| lia]. Qed.

Lemma nmap_obj : forall o x, In o (rlay_objs RE X) -> in_iv o x -> nmap x -> False.
Proof.
intros o x Ho [O1 O2] NM. cbn [fst snd] in O1, O2. pose proof (rl_objs_lia _ _ _ _ _ _ GC o Ho) as (OA & OK & OC & _).
destruct (AVO o Ho); destruct (nmap_where x NM) as [M|[B M]]; lits; lia.
Qed.

Lemma nmap_prim : forall x, prim_lo RE <= x < prim_lo RE + 2^37 + 0x1000 -> nmap x -> False.
Proof.
intros x Hx NM. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). rewrite ?prim_hi_eq in *.
destruct (nmap_where x NM) as [M|[B M]]; lits; lia.
Qed.

Lemma nmap_prim_sh : forall lo len x, lo mod 8 = 0 -> 0 <= len -> prim_lo RE <= lo -> lo + len <= prim_lo RE + 2^37 + 0x1000 ->
in_sh (lo, len) x -> nmap x -> False.
Proof.
intros lo len x AL L P1 P2 R NM. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). rewrite ?prim_hi_eq in *.
lits. eapply (nmap_apart lo len x AL L); [lia| lia| lia| exact NM| right; exact R].
Qed.

Lemma nmap_sec : forall e x, In e (as_reg a) ->
(se_beg e <= x < se_beg e + se_size e \/ in_sh (se_beg e, kPage) x \/ in_sh (se_beg e + kPage, se_size e - kPage) x) -> nmap x -> False.
Proof.
intros e x He R NM. pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1. pose proof kconsts as (_ & _ & _ & _ & KP & _).
pose proof (AVR e He) as D.
destruct R as [R|[R|R]].
- eapply (nmap_apart (se_beg e) (se_size e) x); [clear - E1; Z.div_mod_to_equations; lia| lia| lia| lia| lia| exact NM| left; exact R].
- eapply (nmap_apart (se_beg e) kPage x); [clear - E1; Z.div_mod_to_equations; lia| rewrite KP; lia| lia| rewrite KP; lia| rewrite KP; lia| exact NM| right; exact R].
- eapply (nmap_apart (se_beg e + kPage) (se_size e - kPage) x); [rewrite KP; clear - E1; Z.div_mod_to_equations; lia| rewrite KP; lia| rewrite KP; lia| lia| rewrite KP; lia| exact NM| right; exact R].
Qed.

Lemma nmap_slot : forall c i t x, tag_at G c i = Some t ->
(in_iv (slot_beg RE c i, class_size c) x \/ in_sh (slot_beg RE c i, class_size c) x) -> nmap x -> False.
Proof.
intros c i t x Ht [R|R] NM; pose proof (slot_prim _ _ _ _ _ _ GC c i t Ht) as (P1 & P2 & P3 & _ & _ & _ & _ & S1 & _); rewrite ?prim_hi_eq in *.
- destruct R as [R1 R2]; cbn [fst snd] in R1, R2. apply (nmap_prim x); [lia| exact NM].
- eapply (nmap_prim_sh (slot_beg RE c i) (class_size c) x); [exact P3| lia| lia| lia| exact R| exact NM].
Qed.

Lemma nmap_region : forall c x, 1 <= c <= 31 ->
(reg_beg (ae_L RE) c <= x < reg_beg (ae_L RE) c + kFreeArrayOffset \/ in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) x
\/ fa_beg (ae_L RE) c <= x < fa_beg (ae_L RE) c + kFreeArraySize \/ in_sh (fa_beg (ae_L RE) c, kFreeArraySize) x) -> nmap x -> False.
Proof.
intros c x Hc R NM. pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof kconsts as (_ & KO & KS & _).
pose proof (reg_beg_align RE X c (gc_rlay _ _ _ _ _ _ GC)) as (RA & _ & FA).
destruct R as [R|[R|[R|R]]].
- apply (nmap_prim x); [rewrite KO in R; lia| exact NM].
- eapply (nmap_prim_sh (reg_beg (ae_L RE) c) kFreeArrayOffset x); [exact RA| rewrite KO; lia| lia| rewrite KO, KS in *; lia| exact R| exact NM].
- apply (nmap_prim x); [rewrite KS in R; lia| exact NM].
- eapply (nmap_prim_sh (fa_beg (ae_L RE) c) kFreeArraySize x); [exact FA| rewrite KS; lia| lia| rewrite KS; lia| exact R| exact NM].
Qed.

Lemma nmap_RPrim : forall x, nmap x -> fp_RPrim G RE X x -> False.
Proof.
intros x NM F. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). rewrite ?prim_hi_eq in *.
destruct (fp_RPrim_loc G RE X x F) as [H|H|c Hc H|c Hc H|c Hc H _|c Hc H _].
- apply (nmap_prim x); [rewrite region_info_eq in H; lia| exact NM].
- eapply (nmap_obj _ x (T_obj RE X)); [split; cbn [fst snd]; lia| exact NM].
- eapply (nmap_region c x Hc); [do 2 right; left; exact H| exact NM].
- eapply (nmap_region c x Hc); [do 3 right; exact H| exact NM].
- eapply (nmap_region c x Hc); [left; exact H| exact NM].
- eapply (nmap_region c x Hc); [right; left; exact H| exact NM].
Qed.

Lemma nmap_RQuar : forall x, nmap x -> fp_RQuar a LB0 G RE X x -> False.
Proof.
intros x NM F.
destruct (fp_RQuar_loc a LB0 G RE X x F) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- eapply (nmap_obj _ x (T_obj RE X)); [split; cbn [fst snd]; lia| exact NM].
- apply (nmap_low x); [| exact NM]. pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT). lia.
- eapply (nmap_slot c i t x Ht); [left; exact H| exact NM].
- eapply (nmap_slot c i t x Ht); [right; exact H| exact NM].
- eapply (nmap_sec e x He); [left; pose proof kconsts as (_ & _ & _ & _ & KP & _); lia| exact NM].
- eapply (nmap_sec e x He); [do 2 right; exact H| exact NM].
Qed.

Lemma nmap_RChunks : forall x, nmap x -> fp_RChunks a LB0 G RE X x -> False.
Proof.
intros x NM [[[H|H] _]|[H|H]].
- destruct H as (c & i & t & Ht & _ & Hx). eapply (nmap_slot c i t x Ht); [left; exact Hx| exact NM].
- destruct H as (e & He & _ & Hx). eapply (nmap_sec e x He); [left; pose proof kconsts as (_ & _ & _ & _ & KP & _); lia| exact NM].
- destruct H as (c & i & t & Ht & _ & Hx). eapply (nmap_slot c i t x Ht); [right; exact Hx| exact NM].
- destruct H as (e & He & _ & Hx). eapply (nmap_sec e x He); [do 2 right; exact Hx| exact NM].
Qed.

Lemma nmap_RSec : forall x, nmap x -> fp_RSec a RE X x -> False.
Proof.
intros x NM [H|[H|[H|H]]].
- apply (nmap_low x); [| exact NM]. destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold A_INSTANCE in *. lia.
- destruct H as [H1 H2]; cbn [fst snd] in H1, H2. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & QK & QC & _). unfold ptrarr_hi, ptrarr_lo in *.
destruct (nmap_where x NM) as [M|[B M]]; lits; lia.
- destruct H as (e & He & Hx). eapply (nmap_sec e x He); [left; pose proof (sec_facts _ _ _ _ _ _ GC e He) as (_ & _ & _ & E4 & E5 & E6 & _);
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]; rewrite <- E4 in M1; pose proof kconsts as (_ & _ & _ & _ & KP & _); lia| exact NM].
- destruct H as (e & He & Hx). eapply (nmap_sec e x He); [right; left; exact Hx| exact NM].
Qed.

Lemma nmap_RDepot : forall x, nmap x -> fp_RDepot RE X x -> False.
Proof.
intros x NM [H|[H|[H|H]]].
- apply (nmap_low x); [| exact NM]. destruct H as [H1 H2]; cbn [fst snd] in H1, H2. lia.
- eapply (nmap_obj _ x (dn_obj RE X)); [exact H| exact NM].
- eapply (nmap_obj _ x (ssb_obj RE X)); [exact H| exact NM].
- eapply (nmap_obj _ x (T_obj RE X)); [subst x; split; cbn [fst snd]; lia| exact NM].
Qed.

Lemma nmap_RStats : forall x, nmap x -> fp_RStats RE X x -> False.
Proof.
intros x NM [H|[H|H]].
- eapply (nmap_obj _ x (T_obj RE X)); [destruct H as [H1 H2]; cbn [fst snd] in H1, H2; split; cbn [fst snd]; lia| exact NM].
- apply (nmap_low x); [| exact NM]. destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold A_ERRNO in *. lia.
- apply (nmap_low x); [| exact NM]. lia.
Qed.

Lemma nmap_RFake : forall x, nmap x -> fp_RFake FS0 RE X x -> False.
Proof.
intros x NM F. pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
destruct (fp_RFake_zone RE X FS0 x F) as [R|R].
- exact (nmap_obj _ x (fs_obj RE X) R NM).
- eapply (nmap_apart (ae_fs_base RE) A_FS_MAP_SIZE x); [clear - FAL; Z.div_mod_to_equations; lia| unfold A_FS_MAP_SIZE; lia| exact (proj1 FK)| exact FC
| destruct (AVO _ (fs_obj RE X)); cbn [fst snd] in *; lia| exact NM| right; exact R].
Qed.

Lemma nmap_client : forall LB FS SP x, Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> nmap x -> False.
Proof.
intros LB FS SP x PB PF CSP CA NM.
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
destruct (nmap_where x NM) as [M|[B M]].
- destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
+ lits. lia.
+ cbn [ala_client_data a_alayout] in C1. unfold a_client_data in C1. lia.
+ assert (LU : in_live_user LB0 x) by (destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R]).
destruct (live_user_where _ _ _ _ _ _ GC x LU) as (p & A & n & Hin & Hx & [(c & i & Ht & R1 & R2)|(e & He & _ & R1 & R2)]).
* eapply (nmap_slot c i _ x Ht); [left; split; cbn [fst snd]; lia| exact NM].
* eapply (nmap_sec e x He); [left; pose proof kconsts as (_ & _ & _ & _ & KP & _); lia| exact NM].
+ assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range _ _ _ _ _ _ GC f Hf0) as (R1 & R2 & R3 & R4 & R5).
eapply (nmap_obj _ x (fs_obj RE X)); [split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia| exact NM].
+ assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
pose proof (frame_shadow_where _ _ _ _ _ _ GC x SHD) as FS'.
pose proof (in_sh_band (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(clear - FAL; Z.div_mod_to_equations; lia) ltac:(unfold A_FS_MAP_SIZE; lia) (proj1 FK) FC FS') as B0. unfold kLowEnd, KHI in B0. clear - MBK M B0. lia.
+ rewrite SH_247 in C1. lits. pose proof SH_band. lia.
+ cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. lia.
- pose proof M as M'. apply in_sh_bounds in M'; [| clear - MBP; Z.div_mod_to_equations; lia| lia].
destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
+ lits. lia.
+ cbn [ala_client_data a_alayout] in C1. unfold a_client_data in C1. rewrite !SH_eq in M'.
clear - M' C1 MBK MBP. Z.div_mod_to_equations. lia.
+ assert (LU : in_live_user LB0 x) by (destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R]).
pose proof (live_user_heap _ _ _ _ _ _ GC x LU). unfold kLowEnd in *. lits. lia.
+ assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range _ _ _ _ _ _ GC f Hf0) as (R1 & R2 & R3 & R4 & R5). lits. lia.
+ assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
pose proof (frame_shadow_where _ _ _ _ _ _ GC x SHD) as FS'.
eapply (nmap_apart (ae_fs_base RE) A_FS_MAP_SIZE x); [clear - FAL; Z.div_mod_to_equations; lia| unfold A_FS_MAP_SIZE; lia| exact (proj1 FK)| exact FC
| destruct (AVO _ (fs_obj RE X)); cbn [fst snd] in *; lia| exact NM| right; exact FS'].
+ pose proof (SH_mono (mb + msz) band_lo MBC). rewrite SH_eq in *. unfold SH, A_SHADOW_OFS in M'. lits. Z.div_mod_to_equations. lia.
+ cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. rewrite !SH_eq in M'.
clear - M' C1 MBK MBP. Z.div_mod_to_equations. lia.
Qed.
End Z.

Section Z0.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Set Default Proof Using "GC".

Lemma fpSec_RFake : forall x, fp_RSec a RE X x -> fp_RFake FS0 RE X x -> False.
Proof.
intros x FS F. pose proof kconsts as (_ & _ & _ & _ & KP & _).
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (FAL & FK & FC & _ & FQ). cbn [fst snd] in FAL, FK, FC, FQ. unfold iv_disjoint in FQ; cbn [fst snd] in FQ.
rewrite ?KHI_eq in *.
destruct (fp_RFake_zone RE X FS0 x F) as [R|R].
- destruct R as [R1 R2]; cbn [fst snd] in R1, R2. destruct FS as [H|[H|[H|H]]].
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold A_INSTANCE in *. lia.
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold ptrarr_lo in *. lia.
+ destruct H as (e & He & Hx). exact (obj_vs_sec a LB0 FS0 G RE X GC _ e x (fs_obj RE X) He ltac:(split; cbn [fst snd]; lia)
ltac:(pose proof (sec_facts _ _ _ _ _ _ GC e He) as (_ & _ & _ & E4 & E5 & E6 & _); pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]; rewrite <- E4 in M1; lia)).
+ destruct H as (e & He & Hx). pose proof (hdr_band a LB0 FS0 G RE X GC e x He Hx). lia.
- pose proof (fs_band a LB0 FS0 G RE X GC x R) as B. destruct FS as [H|[H|[H|H]]].
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold A_INSTANCE in *. lia.
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & QK & _). rewrite ?KHI_eq in QK. lia.
+ destruct H as (e & He & Hx). pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1. rewrite ?KHI_eq in E2. rewrite KP in *. lia.
+ destruct H as (e & He & Hx). pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & E9).
pose proof (proj1 (List.Forall_forall _ _) E9 _ (fs_obj RE X)) as D. unfold iv_disjoint in D. cbn [fst snd] in D.
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1.
exact (in_sh_disjoint (se_beg e) kPage (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(clear - E1; Z.div_mod_to_equations; lia) ltac:(clear - FAL; Z.div_mod_to_equations; lia)
ltac:(rewrite KP; lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(rewrite KP; unfold A_FS_MAP_SIZE in *; lia) Hx R).
Qed.

Lemma ssec_client : forall LB FS SP x, Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> fp_RSec a RE X x -> False.
Proof.
intros LB FS SP x PB PF CSP CA F.
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
assert (QC : czone LB0 RE x -> False) by (intros CZ; exact (fp_RSec_cz a LB0 FS0 G RE X GC x F CZ)).
assert (QL : x < band_lo) by (destruct (Z.lt_ge_cases x band_lo) as [L|GE]; [exact L| exfalso; apply QC; left; exact GE]).
destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
- lia.
- apply QC. right; left. exact C1.
- apply QC. do 2 right; left. destruct C1 as (b & Hb & R). exists b. split; [eapply Permutation_in; [exact PB| exact Hb]| exact R].
- assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range _ _ _ _ _ _ GC f Hf0) as (R1 & R2 & R3 & R4 & R5).
apply QC. do 3 right; left. split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia.
- assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
apply QC. do 4 right; left. exact (frame_shadow_where _ _ _ _ _ _ GC x SHD).
- apply QC. do 5 right; left. rewrite SH_247 in C1. exact C1.
- cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1.
destruct F as [H|[H|[H|H]]].
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. unfold A_INSTANCE in *. lia.
+ destruct H as [H1 H2]; cbn [fst snd] in H1, H2. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & QK & _). rewrite ?KHI_eq in QK. lia.
+ destruct H as (e & He & Hx). pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1. rewrite ?KHI_eq in E2. pose proof kconsts as (_ & _ & _ & _ & KP & _). rewrite KP in *. lia.
+ destruct H as (e & He & Hx). pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & [_ E2] & E3 & E4 & E5 & E6 & _).
pose proof kconsts as (_ & _ & _ & _ & KP & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1.
apply in_sh_bounds in Hx; [| clear - E1; Z.div_mod_to_equations; lia| rewrite KP; lia].
rewrite !SH_eq in Hx. rewrite KP in Hx. clear - Hx C1 E1 E2 E6 M1. destruct E2 as [E2|E2]; Z.div_mod_to_equations; lia.
Qed.
End Z0.
End Mqk.

Module Mql.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QJFf.Mq0.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QUvT.Mq0 QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk Q9Ho.Mq4 QV3O.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition depot_put_entry : Z := 0x83e90.
Definition depot_stack : Z := 224.

Definition MM_bytes : list byte := [149%bv; 233%bv; 209%bv; 91%bv; 147%bv; 167%bv; 164%bv; 198%bv]%list.
Definition MM8_bytes : list byte := [168%bv; 76%bv; 143%bv; 222%bv; 154%bv; 60%bv; 37%bv; 53%bv]%list.
Definition MSEED_bytes : list byte := [140%bv; 178%bv; 71%bv; 151%bv; 140%bv; 178%bv; 71%bv; 151%bv]%list.
Lemma depot_consts : forall m, mem_inv asegs m ->
ro_cells asegs m 0x102e8 [CB 8 MM_bytes] /\ ro_cells asegs m 0x10318 [CB 8 MM8_bytes] /\ ro_cells asegs m 0x10430 [CB 8 MSEED_bytes].
Proof.
intros m MI. split; [|split]; (apply (ro_cells_image asegs m); [exact MI| vm_compute; reflexivity| lia| cbn; lia]).
Qed.

Lemma bkt_shift : forall x, 0 <= x < 2^64 -> bv_unsigned (wz (x ≪ 44)) ≫ 42 = 4 * bkt x.
Proof.
intros x Hx. unfold bkt. rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change 1048575 with (Z.ones 20). rewrite Z.land_ones by lia.
change (2 ^ 64) with (2 ^ 20 * 2 ^ 44). rewrite Z.mul_mod_distr_r by lia.
change (2 ^ 44) with (4 * 2 ^ 42). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Lemma bkt_range : forall x, 0 <= bkt x < 2^20.
Proof.
intros x. unfold bkt. change 1048575 with (Z.ones 20). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma take_S_nth : forall {A} (l : list A) i x, nth_error l i = Some x -> take (S i) l = take i l ++ [x].
Proof.
intros A l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
- injection H as ->. reflexivity.
- rewrite (IH i x H). reflexivity.
Qed.

Lemma skipn_cons_nth : forall {A} (l : list A) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
intros A l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
- injection H as ->. reflexivity.
- apply IH. exact H.
Qed.

Lemma srliw16_small : forall s, 0 <= s < 65536 -> bv_swrap 32 (bv_wrap 32 s ≫ 16) = 0.
Proof.
intros s Hs. unfold bv_wrap. change (bv_modulus 32) with 4294967296. rewrite Z.mod_small by lia.
rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.

Lemma zext32_small : forall s, 0 <= s < 2^32 -> bv_unsigned (wz (s ≪ 32)) ≫ 32 = s.
Proof.
intros s Hs. rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.mul_mod_distr_r, Z.div_mul by lia. apply Z.mod_small. lia.
Qed.

Ltac if_lit2 :=
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota end.

Lemma land_m16_small : forall x, 0 <= x < 16 -> Z.land x 18446744073709551600 = 0.
Proof.
intros x Hx.
assert (E : 18446744073709551600 = Z.ldiff (Z.ones 64) (Z.ones 4)) by reflexivity. rewrite E, land_ldiff_distr_r.
rewrite Z.land_ones, Z.mod_small by lia. rewrite Z.ldiff_ones_r, Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.

Lemma amoadd_w_bytes : forall (st c : Z), 0 <= st -> 0 <= c -> st + c < 2^32 ->
Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 st)))) (low32 (Z_to_bv 64 c)))) = le4 (Z_to_bv 64 (st + c)).
Proof.
intros st c Hs Hc Hsc. cbv [amo_val]. rewrite bv_add_unsigned. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
unfold low32. rewrite extract_low_mod by lia. rewrite !unsigned_lit by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite !Z.mod_small by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia.
unfold le4. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma lxor_pow20 : forall a, 0 <= a < 2^20 -> Z.lxor a 1048576 = a + 1048576.
Proof.
intros a Ha. symmetry. apply Z.add_nocarry_lxor.
replace a with (Z.land a (Z.ones 20)) by (rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite <- Z.land_assoc. change (Z.land (Z.ones 20) 1048576) with 0. apply Z.land_0_r.
Qed.

Tactic Notation "call_pre" uconstr(SPEC) := eapply evt_cut; [eapply SPEC|].
Ltac post_later := match goal with MU : munch _ _ ?mc |- forall ms', _ -> _ => post_call_u asegs mc end.

Lemma zseq_snoc : forall n, 0 <= n -> zseq (n + 1) = zseq n ++ [n + 1].
Proof.
intros n Hn. unfold zseq. replace (Z.to_nat (n + 1)) with (Z.to_nat n + 1)%nat by lia.
rewrite seq_app, map_app. cbn [map seq]. f_equal. f_equal. lia.
Qed.

Lemma NoDup_snoc : forall {A} (l : list A) x, List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof.
intros A l x ND NI. induction l as [|y l IH]; cbn.
- constructor; [intros []| constructor].
- inversion ND; subst. constructor.
+ rewrite in_app_iff. cbn. intros [H|[H|[]]]; [contradiction| subst; apply NI; left; reflexivity].
+ apply IH; [assumption| intros H; apply NI; right; exact H].
Qed.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma hash_loop : forall (k : nat) (ws : list word) (i : Z) (h : word) (src cur fin : Z) m
(ra sp gp tp t0 t1 t2 s0 s1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
cur = src + 8 * i -> fin = src + 8 * Z.of_nat (length ws) ->
mem_inv asegs m -> u64arr asegs m src ws -> Z.of_nat k = Z.of_nat (length ws) - i -> 0 <= i < Z.of_nat (length ws) ->
0 <= src -> src + 8 * Z.of_nat (length ws) < 2^64 ->
evt asegs (fun ms' => exists a5' a6',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MM) (wz fin) (fold_left hstepw (skipn (Z.to_nat i) ws) h) a3
(wz fin) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x83f64) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MM) (wz cur) h a3 (wz fin) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x83f40) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until fc; intros -> -> MI Q Hk Hi S0 S1; [lia|].
destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; lia].
pose proof (u64arr_read asegs m src ws i w (wa (src + 8 * i)) Q NTH ltac:(lia) eq_refl) as RD.
rewrite (skipn_cons_nth ws (Z.to_nat i) w NTH). cbn [fold_left].
unfold MM. do 8 istep. istep.
destruct (Z.lt_ge_cases (i + 1) (Z.of_nat (length ws))) as [LT|GE].
- if_true_u.
replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
eapply (IH ws (i + 1)); [| | exact MI| exact Q| lia| lia| lia| lia]; lia.
- if_false_u. apply evt_done. do 2 eexists.
replace (src + 8 * i + 8) with (src + 8 * Z.of_nat (length ws)) by lia.
rewrite skipn_all2 by lia. cbn [fold_left]. reflexivity.
Qed.

Definition find_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(H n : Z) (nh : Z -> Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' =>
(exists (sF : Z) (a1 a2 : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz sF) a1 a2 a3 a4 a5 a6 a7 s2 (wz H) s4 s5 (wz 65535) s7 (wz DP_MAP1) s9 s10 s11 t3 t4 t5 t6)
F (wz 0x840d4) fc None m (seg_rom asegs)
/\ 1 <= sF <= n /\ nh sF = H)
\/ (exists (a0 a2 : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) a2 a3 a4 a5 a6 a7 s2 (wz H) s4 s5 (wz 65535) s7 (wz DP_MAP1) s9 s10 s11 t3 t4 t5 t6)
F (wz 0x84028) fc None m (seg_rom asegs)
/\ forall j, 1 <= j <= n -> nh j <> H).

Lemma find_loop : forall (k : nat) (s : Z) (H n : Z) (nh ns : Z -> Z) m
(ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
mem_inv asegs m ->
rw_cells asegs m DP_MAP1 [C8 (wz (rl_dn X))] ->
(forall i, 1 <= i <= n ->
rw_cells asegs m (rl_dn X + 16 * i) [C8 (wz (nh i)); C4 (wz (lastb nh (bkt (nh i)) (Z.to_nat (i - 1)))); C4 (wz (ns i))]) ->
(forall i, 1 <= i <= n -> 0 <= nh i < 2^64) -> 0 <= H < 2^64 ->
1 <= n < 65536 -> 0 < rl_dn X -> rl_dn X + 0x100000 <= band_lo ->
s <= Z.of_nat k -> (s = 0 \/ (1 <= s <= n /\ bkt (nh s) = bkt H)) ->
(forall j, s < j <= n -> bkt (nh j) = bkt H -> nh j <> H) ->
evt asegs (find_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 F fc H n nh m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz s) a2 a3 a4 a5 a6 a7 s2 (wz H) s4 s5 (wz 65535) s7 (wz DP_MAP1) s9 s10 s11 t3 t4 t5 t6)
F (wz 0x83fd0) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until fc; intros MI CMAP CND NHR HR NR D1 D2 SK SH CHK.
- assert (s = 0) as -> by lia.
istep. if_true. apply evt_done. right. do 2 eexists. split; [reflexivity|].
intros j Hj E. destruct (Z.eq_dec (bkt (nh j)) (bkt H)) as [B|B]; [exact (CHK j ltac:(lia) B E)| apply B; rewrite E; reflexivity].
- destruct SH as [->|[SR SB]].
{ istep. if_true. apply evt_done. right. do 2 eexists. split; [reflexivity|].
intros j Hj E. destruct (Z.eq_dec (bkt (nh j)) (bkt H)) as [B|B]; [exact (CHK j ltac:(lia) B E)| apply B; rewrite E; reflexivity]. }
rewrite ?KHI_eq in D1. idtac. unfold DP_MAP1 in *.
pose proof (CND s ltac:(lia)) as NODE. pose proof (NHR s ltac:(lia)) as HS.
pose proof (lastb_range nh (bkt (nh s)) (Z.to_nat (s - 1))) as LR.
istep. if_false_u. istep. istep. rewrite (unsigned_lit s), srliw16_small by lia.
do 4 istep. if_false_u.
istep. istep. rewrite (unsigned_lit s), (zext32_small s) by lia.
istep. rewrite (unsigned_lit s) by lia. replace (Z.land s 65535) with s by (change 65535 with (Z.ones 16); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
istep. rewrite (unsigned_lit s), (Z.shiftl_mul_pow2 s 4) by lia. change (2 ^ 4) with 16. rewrite (Z.mul_comm s 16).
istep. remember (rl_dn X + 16 * s) as node eqn:En in |- *. rewrite <- En in NODE.
istep. istep. rewrite (sx32_small (lastb nh (bkt (nh s)) (Z.to_nat (s - 1)))) by lia.
clear NODE. subst node.
istep. if_cases E; zify_cond E.
+
rewrite ?(unsigned_lit H), ?(unsigned_lit (nh s)) in E by lia.
eapply (IH (lastb nh (bkt (nh s)) (Z.to_nat (s - 1)))); try eassumption; try lia.
* destruct (Z.eq_dec (lastb nh (bkt (nh s)) (Z.to_nat (s - 1))) 0) as [Z0|NZ]; [left; exact Z0| right].
split; [lia|]. rewrite (lastb_bkt nh (bkt (nh s)) (Z.to_nat (s - 1)) NZ). exact SB.
* intros j Hj Bj. destruct (Z.lt_ge_cases s j) as [LT|GE]; [apply CHK; lia|].
destruct (Z.eq_dec j s) as [->|NE]; [lia|].
exfalso. apply (lastb_max nh (bkt (nh s)) (Z.to_nat (s - 1)) j ltac:(lia)). rewrite Bj, SB. reflexivity.
+
rewrite ?(unsigned_lit H), ?(unsigned_lit (nh s)) in E by lia.
istep. apply evt_done. left. exists s. do 2 eexists. split; [reflexivity|]. split; [lia| symmetry; exact E].
Qed.

Lemma lock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (B v : Z),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells asegs m B [C4 (wz v)] -> 0 <= v < 2^31 -> B mod 4 = 0 -> 0 <= B -> B + 4 <= band_lo ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 4)] lo m
(fun a0' m' => a0' = wz v /\ exists lw : word, rw_cells asegs m' B [C4 lw]))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz B) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x84624) fc None m (seg_rom asegs)).
Proof.
intros until v; intros MI ST CEIL LO TB VR BAL BLO BHI. pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (AMO : amo_aligned AW (wz B) = true) by (apply amo_aligned_intro4; lia).
carve_frame 48%nat ST.
step_until 0x84650. rewrite (sx32_small v) by lia.
istep. rewrite bv_lts_zero_r. if_true_u.
istep. amo_step AMO. rewrite (sx32_small v) by lia.
istep. if_false_u.
amo_step AMO.
istep. if_false. istep. if_true_u. step_until 0.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity| eexists; exact TB].
Qed.

Lemma shl44_shr41 : forall x, 0 <= x < 2^20 -> bv_unsigned (wz (x ≪ 44)) ≫ 41 = 8 * x.
Proof.
intros x Hx. rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite Z.mod_small by (change (2 ^ 64) with (2 ^ 20 * 2 ^ 44); nia).
change (2 ^ 44) with (8 * 2 ^ 41). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Lemma alloc_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (tf j40 ssb st cnt idxp pk : Z) (iw : word),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
rw_cells asegs m 0x1c4088 [C8 (wz tf); C8 (wz j40); C8 (wz ssb); C4 (wz st)] ->
rw_cells asegs m idxp [C8 iw] ->
0 <= tf -> 2 <= cnt <= 31 -> tf + cnt < 2^20 -> 0x647000 <= ssb < 2^47 -> 0 <= st < 2^32 ->
bv_unsigned sp <= idxp -> idxp + 8 < 2^64 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp); (0x1c4088, 0x1c4088 + 8); (idxp, idxp + 8)] lo m
(fun a0' m' => a0' = wz (ssb + 8 * tf)
/\ rw_cells asegs m' 0x1c4088 [C8 (wz (tf + cnt)); C8 (wz j40); C8 (wz ssb); C4 (wz st)]
/\ rw_cells asegs m' idxp [C8 (wz tf)]))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0x1c4088) (wz cnt) (wz idxp) (wz pk) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x819b8) fc None m (seg_rom asegs)).
Proof.
intros until iw; intros MI ST CEIL LO SSC IDX TF CNT ROOM SSB STR IP1 IP2. pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (1851528, 1851528 + 8); (idxp, idxp + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (AMO : amo_aligned AD (wz 1851528) = true) by (apply amo_aligned_intro8; [lia| reflexivity]).
carve_frame 16%nat ST.
step_until 0x819cc. amo_step AMO.
cbv [amo_val] in SSC. rewrite bv_add_canon in SSC. rewrite !unsigned_lit in SSC by lia.
step_until 0. rewrite ?(unsigned_lit tf), ?(unsigned_lit (cnt + -1 + tf)), ?Z.shiftr_div_pow2 by lia. change (2 ^ 20) with 1048576.
rewrite (Z.div_small tf 1048576), (Z.div_small (cnt + -1 + tf) 1048576) by lia.
if_false_u. step_until 0. rewrite ?(unsigned_lit tf), ?Z.shiftr_div_pow2, ?(Z.div_small tf (2 ^ 32)) by lia. if_lit2.
step_until 0. if_false_u.
step_until 0x81a20. rewrite ?(unsigned_lit tf), (shl44_shr41 tf) by lia.
step_until 0. release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|]. split; [exact SSC| exact IDX].
Qed.

Lemma memcpy_loop : forall (k : nat) (i : Z) (dst src n cd cs : Z) (ds bs : list byte) m
(ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc lo,
cd = dst + i -> cs = src + i ->
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
u8arr asegs m dst ds -> Z.of_nat (length ds) = n -> u8ro asegs m src bs -> n <= Z.of_nat (length bs) ->
take (Z.to_nat i) ds = take (Z.to_nat i) bs ->
Z.of_nat k = n - i -> 0 <= i < n -> 0 <= dst -> 0 <= src -> dst + n < 2^64 -> src + Z.of_nat (length bs) < 2^64 ->
(src + Z.of_nat (length bs) <= dst \/ dst + n <= src) -> (dst + n <= lo \/ bv_unsigned sp <= dst) ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(dst, dst + n)] lo m
(fun _ m' => u8arr asegs m' dst (take (Z.to_nat n) bs) /\ u8ro asegs m' src bs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz cs) (wz (dst + n)) (wz cd) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x752d8) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until lo; intros -> -> MI ST DA LD SB LB TK Hk Hi D0 S0 D1 S1 DISJ STKD; [lia|].
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
pose proof (munch_refl [(dst, dst + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:NTH; [| apply nth_error_None in NTH; lia].
pose proof (u8ro_read asegs m src bs i b (wa (src + i)) SB NTH ltac:(lia) eq_refl) as RD.
istep.
pose proof (u8arr_store_ok asegs m dst ds i (wa (dst + i)) DA ltac:(lia) eq_refl) as SOK.
step. rewrite le1_zxb.
pose proof (u8arr_write asegs m dst ds i b DA ltac:(lia)) as DA1. clear DA. store_done.
assert (TK1 : take (Z.to_nat (i + 1)) (upd ds (Z.to_nat i) b) = take (Z.to_nat (i + 1)) bs).
{ replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite take_upd_snoc by lia. rewrite TK.
rewrite (take_S_nth bs (Z.to_nat i) b NTH). reflexivity. }
istep. istep. istep.
destruct (Z.lt_ge_cases (i + 1) n) as [LT|GE].
- if_true_u.
eapply evt_mono.
{ eapply (IH (i + 1) dst src n _ _ (upd ds (Z.to_nat i) b) bs); try eassumption; try lia. rewrite upd_length. exact LD. }
cbv beta. intros ms' PO. unfold rpost in PO |- *. destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & E & MU' & WM' & REST).
do 16 eexists. split; [exact E|]. split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. exact REST.
- if_false_u. istep.
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
split; [| assumption]. replace (Z.to_nat n) with (Z.to_nat (i + 1)) by lia. rewrite <- TK1.
rewrite take_ge by (rewrite upd_length; lia). exact DA1.
Qed.

Lemma memcpy_spec : forall (dst src n : Z) (ds bs : list byte) m
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc lo,
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
u8arr asegs m dst ds -> Z.of_nat (length ds) = n -> u8ro asegs m src bs -> n <= Z.of_nat (length bs) ->
0 < n -> 0 <= dst -> 0 <= src -> dst + n < 2^64 -> src + Z.of_nat (length bs) < 2^64 ->
(src + Z.of_nat (length bs) <= dst \/ dst + n <= src) -> (dst + n <= lo \/ bv_unsigned sp <= dst) ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(dst, dst + n)] lo m
(fun _ m' => u8arr asegs m' dst (take (Z.to_nat n) bs) /\ u8ro asegs m' src bs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz src) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x752cc) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros MI ST DA LD SB LB NP D0 S0 D1 S1 DISJ STKD.
istep. if_false_u. istep. istep.
eapply (memcpy_loop (Z.to_nat n) 0 dst src n dst src); try eassumption; try lia. reflexivity.
Qed.

Lemma cb_u8arr : forall m A n bs, rw_cells asegs m A [CB n bs] -> u8arr asegs m A bs.
Proof.
intros m A n bs [[WF BA] WR]. cbn in WF. destruct WF as [L _]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
cbn [cells_size csize Nat.add] in WR. rewrite Nat.add_0_r in WR. split; [exact BA|]. rewrite L. exact WR.
Qed.

Lemma le8_split32 : forall x, 0 <= x < 2^32 -> le8 (wz x) = le4 (wz x) ++ le4 (wz 0).
Proof.
intros x Hx. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app].
rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite !Z.shiftr_div_pow2 by lia.
rewrite ?(Z.div_small x (2 ^ 32)), ?(Z.div_small x (2 ^ 40)), ?(Z.div_small x (2 ^ 48)), ?(Z.div_small x (2 ^ 56)) by lia.
replace (x / 2 ^ (8 + 8 + 8 + 8 + 8 + 8 + 8)) with 0 by (symmetry; apply Z.div_small; lia).
reflexivity.
Qed.

Lemma rw_C8_split32 : forall m A x pre post, 0 <= x < 2^32 ->
rw_cells asegs m A (pre ++ C8 (wz x) :: post) -> rw_cells asegs m A (pre ++ C4 (wz x) :: C4 (wz 0) :: post).
Proof.
intros m A x pre post Hx H. eapply rw_cells_recast'; [exact H| |].
- destruct H as [[WF _] _]. apply cells_wf_app in WF as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn. cbn in W2. tauto.
- rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite (le8_split32 x Hx). rewrite <- !app_assoc. reflexivity.
Qed.

Lemma sstore_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (ap pp tr sz tf j40 ssb st : Z) (q : list word) (pw : word),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 80 ->
rw_cells asegs m ap [C8 (wz tr); C4 (wz sz); C4 (wz 0)] ->
rw_cells asegs m pp [C8 pw] ->
u64arr asegs m tr q -> Z.of_nat (length q) = 30 ->
rw_cells asegs m 0x1c4088 [C8 (wz tf); C8 (wz j40); C8 (wz ssb); C4 (wz st)] ->
hjunk m ssb (ssb + 0x800000) ->
1 <= sz <= 30 -> 0 <= tf -> tf + 31 < 2^20 -> 0 <= st <= tf ->
ssb mod 8 = 0 -> 0x647000 <= ssb -> ssb + 0x800000 <= band_lo ->
bv_unsigned sp <= pp -> pp + 8 <= ap -> ap + 16 <= tr -> tr + 240 < 2^64 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned sp - 80, bv_unsigned sp); (pp, pp + 8); (0x1c4088, 0x1c4088 + 32); (ssb, ssb + 0x800000)] lo m
(fun a0' m' => a0' = wz (tf + 1)
/\ rw_cells asegs m' 0x1c4088 [C8 (wz (tf + sz + 1)); C8 (wz j40); C8 (wz ssb); C4 (wz (st + sz + 1))]
/\ rw_cells asegs m' pp [C8 (wz 0)]
/\ rw_cells asegs m' ap [C8 (wz tr); C4 (wz sz); C4 (wz 0)]
/\ u64arr asegs m' tr q))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0x1c4088) (wz ap) (wz pp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x81894) fc None m (seg_rom asegs)).
Proof.
intros until pw; intros MI ST CEIL LO ARGS PACK TRQ LQ SSC JS SZ TF ROOM STR AL8 SLO SHI PP1 PP2 AP2 TR2.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (pp, pp + 8); (0x1c4088, 0x1c4088 + 32); (ssb, ssb + 0x800000)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 64%nat ST.
step_until 0x818c0. rewrite ?(sx32_small sz), ?(sx32_small 0) by lia.
step_until 0. if_true_u. step_until 0. if_false_u. step_until 0. if_true_u.
step_until 0x819b8.
lazymatch type of FR with rw_cells _ ?mc _ (?c0 :: ?rest) =>
destruct (proj1 (rw_cells_app asegs mc _ [c0] rest) FR) as [IDX FR'] end.
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR'.
replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in FR' by lia. clear FR.
call_u (alloc_spec).
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact SSC. } { exact IDX. }
{ lia. } { lia. } { lia. } { lia. } { lia. } { unsigned_lits. lia. } { unsigned_lits. lia. }
match goal with H : rw_cells asegs _ 1851528 _ |- _ => rename H into SSC' end.
match goal with H : rw_cells asegs _ (bv_unsigned sp + -64) _ |- _ => rename H into IDX' end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
istep. if_false_u.

pose proof (hjunk_wmono _ _ _ _ JS WM) as JSc.
pose proof (fun Hm => proj2 (hjunk_split _ _ (ssb + 8 * tf) _ JSc Hm)) as J1. specialize (J1 ltac:(lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (ssb + 8 * tf) (ssb + 8 * tf + Z.of_nat 8) _ J1 Hm)) as JH. specialize (JH ltac:(cbn; lia)).
destruct (hjunk_cells _ (ssb + 8 * tf) 8 JH) as [junkh SLOT].
pose proof (fun Hm => proj2 (hjunk_split _ _ (ssb + 8 * tf + 8) _ J1 Hm)) as J2. specialize (J2 ltac:(lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (ssb + 8 * tf + 8) (ssb + 8 * tf + 8 + Z.of_nat (Z.to_nat (8 * sz))) _ J2 Hm)) as JD.
specialize (JD ltac:(rewrite Z2Nat.id by lia; lia)).
destruct (hjunk_cells _ (ssb + 8 * tf + 8) (Z.to_nat (8 * sz)) JD) as [junkd DST]. clear JSc J1 JH J2 JD.
pose proof (cb_u8arr _ _ _ _ DST) as DSTA. assert (LJD : Z.of_nat (length junkd) = 8 * sz) by (destruct DST as [[[L _] _] _]; cbn in L; lia). clear DST.
remember (ssb + 8 * tf) as slot eqn:Eslot. rewrite <- ?Eslot in SLOT, DSTA.
assert (SLB : ssb <= slot /\ slot + 48 <= ssb + 0x800000) by (subst slot; lia).
do 3 istep. rewrite ?(sx32_small sz), ?(unsigned_lit sz), (Z.lor_0_l sz) by lia.
istep. istep. istep. rewrite ?(unsigned_lit sz), (Z.shiftl_mul_pow2 sz 3) by lia. change (2 ^ 3) with 8. rewrite (Z.mul_comm sz 8).
assert (LQ8 : Z.of_nat (length (u64s q)) = 240) by (rewrite u64s_length; lia).
istep. call_u (memcpy_spec (slot + 8) tr (8 * sz) junkd (u64s q)).
{ assumption. } { unsigned_lits. exact ST. } { exact DSTA. } { exact LJD. } { exact (proj1 TRQ). }
{ lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { unsigned_lits. lia. }
match goal with H : u8ro asegs _ tr _ |- _ => rename H into TRB end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.

istep. istep. istep. rewrite ?(unsigned_lit tf), ?Z.shiftr_div_pow2 by lia.
rewrite (unsigned_lit (tf / 2 ^ 16)) by (Z.div_mod_to_equations; lia).
rewrite (land_m16_small (tf / 2 ^ 16)) by (change (2 ^ 16) with 65536; Z.div_mod_to_equations; lia).
istep. istep.
assert (AMO4 : amo_aligned AW (wz 1851552) = true) by (apply amo_aligned_intro4; [lia| reflexivity]).
amo_step AMO4. rewrite (amoadd_w_bytes st (sz + 1)) by lia. mem_after_store. rewrite ?sext_extract_le4, ?(sx32_small st) by lia.
do 4 istep. rewrite ?(unsigned_lit st), (zext32_small st) by lia.
istep.
apply (rw_C8_split32 _ _ tf [] _) in IDX'; [| lia]. cbn [app] in IDX'.
istep. rewrite ?(sx32_small tf) by lia.
istep. rewrite (unsigned_lit (sz + 1 + st)) by lia. istep.
rewrite (lxor_pow20 (sz + 1 + st)) by lia. rewrite v_sltiu_b2z, unsigned_lit by lia.
replace (sz + 1 + st + 1048576 <? bv_wrap 64 1) with false by (symmetry; apply Z.ltb_ge; change (bv_wrap 64 1) with 1; lia). cbn [Z.b2z].
step_until 0x8196c. istep. rewrite ?(sx32_small tf), (addiw_small tf 1) by lia.
step_until 0.
replace (bv_unsigned sp + -56) with (bv_unsigned sp + -64 + 8) in FR' by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (proj2 (rw_cells_app asegs mc (bv_unsigned sp + -64) [C4 (wz tf); C4 (wz 0)] _) (conj IDX' FR')) as FR end.
cbn [app] in FR. clear IDX' FR'. release_frame FR PC (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [reflexivity|].
replace (tf + sz + 1) with (tf + (sz + 1)) by lia. replace (st + sz + 1) with (st + (sz + 1)) by lia.
split; [exact SSC'|]. split; [exact PACK|]. split; [exact ARGS| exact TRQ].
Qed.

Lemma nstore_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (node ap tr sz tf j40 ssb st H : Z) (q : list word) (nj : list byte),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 112 ->
rw_cells asegs m node [CB 16 nj] ->
rw_cells asegs m ap [C8 (wz tr); C4 (wz sz); C4 (wz 0)] ->
u64arr asegs m tr q -> Z.of_nat (length q) = 30 ->
rw_cells asegs m 0x1c4088 [C8 (wz tf); C8 (wz j40); C8 (wz ssb); C4 (wz st)] ->
hjunk m ssb (ssb + 0x800000) ->
1 <= sz <= 30 -> 0 <= tf -> tf + 31 < 2^20 -> 0 <= st <= tf -> 0 <= H < 2^64 ->
ssb mod 8 = 0 -> 0x647000 <= ssb -> ssb + 0x800000 <= band_lo -> 0x647000 <= node -> node + 16 <= band_lo ->
(node + 16 <= ssb \/ ssb + 0x800000 <= node) ->
bv_unsigned sp <= ap -> ap + 16 <= tr -> tr + 240 < 2^64 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned sp - 112, bv_unsigned sp); (node, node + 16); (0x1c4088, 0x1c4088 + 32); (ssb, ssb + 0x800000)] lo m
(fun a0' m' => exists nj4 : list byte, a0' = wz (tf + 1)
/\ rw_cells asegs m' node [C8 (wz H); CB 4 nj4; C4 (wz (tf + 1))]
/\ rw_cells asegs m' 0x1c4088 [C8 (wz (tf + sz + 1)); C8 (wz j40); C8 (wz ssb); C4 (wz (st + sz + 1))]
/\ rw_cells asegs m' ap [C8 (wz tr); C4 (wz sz); C4 (wz 0)]
/\ u64arr asegs m' tr q))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz node) a1 (wz ap) (wz H) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x83ba8) fc None m (seg_rom asegs)).
Proof.
intros until nj; intros MI ST CEIL LO NODE ARGS TRQ LQ SSC JS SZ TF ROOM STR HR AL8 SLO SHI NLO NHI NSS AP1 AP2 TR2.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (node, node + 16); (0x1c4088, 0x1c4088 + 32); (ssb, ssb + 0x800000)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
step_until 0x81894.
lazymatch type of FR with rw_cells _ ?mc _ (?c0 :: ?c1 :: ?rest) =>
destruct (proj1 (rw_cells_app asegs mc _ [c0] (c1 :: rest)) FR) as [FRa FRb];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRb;
destruct (proj1 (rw_cells_app asegs mc _ [c1] rest) FRb) as [PK FRc];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRc end.
replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in PK, FRc by lia.
replace (bv_unsigned sp + -24 + 8) with (bv_unsigned sp + -16) in FRc by lia. clear FR FRb.
call_pre (sstore_spec).
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact ARGS. } { exact PK. } { exact TRQ. } { exact LQ. }
{ exact SSC. } { eapply hjunk_wmono; [exact JS| exact WM]. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { idtac. lia. }
{ unsigned_lits. lia. } { unsigned_lits. lia. } { lia. } { lia. }
post_later.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
match goal with H : rw_cells asegs _ 1851528 _ |- _ => rename H into SSC' end.
match goal with H : rw_cells asegs _ (bv_unsigned sp + -24) _ |- _ => rename H into PK' end.
match goal with H : rw_cells asegs _ ap _ |- _ => rename H into ARGS' end.
match goal with H : u64arr asegs _ tr _ |- _ => rename H into TRQ' end.
istep. istep. step_until 0. if_lit2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
replace (bv_unsigned sp + -24) with (bv_unsigned sp + -32 + 8) in PK' by lia;
pose proof (proj2 (rw_cells_app asegs mc (bv_unsigned sp + -32) [_] _) (conj FRa PK')) as FRab; cbn [app] in FRab;
replace (bv_unsigned sp + -16) with (bv_unsigned sp + -32 + 16) in FRc by lia;
pose proof (proj2 (rw_cells_app asegs mc (bv_unsigned sp + -32) [_; _] _) (conj FRab FRc)) as FR; cbn [app] in FR end.
clear FRa PK' FRc FRab.
step_until 0. release_frame FR ST' (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST'|].
eexists. split; [reflexivity|]. split; [exact NODE|]. split; [exact SSC'|]. split; [exact ARGS'| exact TRQ'].
Qed.

Lemma u64arr_take : forall m A ws k, u64arr asegs m A ws -> u64arr asegs m A (take k ws).
Proof.
intros m A ws k [BA WR]. rewrite <- (firstn_skipn k ws) in BA, WR. rewrite u64s_app in BA. apply bytes_at_app in BA as [BA _].
split; [exact BA|]. rewrite length_app in WR. destruct WR as (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros i Hi. apply W3. lia.
Qed.

Lemma depot_put_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (tr sz dn : Z) (q : list word),
rlay_ok RE X -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - depot_stack ->
u64arr asegs m tr q -> Z.of_nat (length q) = 30 ->
1 <= sz <= 30 -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= tr -> tr + 240 < 2^64 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned sp - depot_stack, bv_unsigned sp); (SS_BASE, DP_END); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000)] lo m
(fun a0' m' => exists id, a0' = wz id /\ 1 <= id < 2^16 /\ RDepot RE X m' /\ u64arr asegs m' tr q /\ exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz tr) (wz sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz depot_put_entry) fc None m (seg_rom asegs)).
Proof.
intros until q; intros RL RD MI ST CEIL LO TRQ LQ SZR0 DNH CAPN TR1 TR2.
pose (ks := map bv_unsigned (take (Z.to_nat sz) q)).
assert (LKS : length ks = Z.to_nat sz) by (unfold ks; rewrite length_map, length_take; lia).
assert (TK : take (length ks) q = map wz ks).
{ rewrite LKS. unfold ks. rewrite map_map. rewrite (map_ext (fun w : word => wz (bv_unsigned w)) (fun w => w)) by (intros w; apply Z_to_bv_bv_unsigned). rewrite map_id. reflexivity. }
assert (SZ : sz = Z.of_nat (length ks)) by lia.
clearbody ks. clear LKS.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
destruct RD as (n & tf & st & h0 & j40 & nh & ns & N1 & STR & TFR & HU & ND & DA & DK & DC & SA & SK & SC & TK1 & TC
& SSC & CTAB & CN & CMAP & CND & JD & JS & TU).
pose proof (depot_capacity n h0 nh ltac:(lia) (fun i Hi => proj1 (HU i Hi)) ND) as CAP.
rewrite ?KHI_eq in DK, SK, TK1. idtac.
pose proof (rlay_pd RE X RL) as PD. pd_pair PD 0 1 DTD. pd_pair PD 0 2 DTS. pd_pair PD 2 0 DNS. clear PD.
unfold depot_put_entry, depot_stack, SS_BASE, DP_END, DP_TAB, DP_N, DP_MAP1 in *.
assert (SZR : 1 <= sz <= 30) by exact SZR0.
assert (DN0 : depot_n asegs m n) by (split; [exact CN| exact N1]).
assert (EDN : n = dn) by (eapply (depot_n_fun m); [exact DN0| exact DNH| lia| unfold DEPOT_CAP in CAPN; lia]). subst dn.
assert (CAPN1 : n + 1 <= 32000) by (unfold DEPOT_CAP in CAPN; exact CAPN).
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (1851528, 6373552); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000)] m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MUs.
pose proof (wmono_refl asegs m) as WM.
destruct (depot_consts m MI) as (K1 & K2 & K3). unfold MM_bytes, MM8_bytes, MSEED_bytes in K1, K2, K3.
step_until 0x83eb0.
carve_frame 112%nat ST.
step_until 0. if_lit2.
step_until 0. rewrite ?(unsigned_lit sz), ?(swrap32_small (sz + 0)), ?Z.add_0_r by lia. if_false_u.
istep. if_false_u.

step_until 0x83f40.
rewrite !(unsigned_lit sz) by lia. replace (Z.land sz 4294967295) with sz by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite !(unsigned_lit sz), (Z.shiftl_mul_pow2 sz 3) by lia. change (2 ^ 3) with 8.
assert (HI : hinitw (wz sz) = wz (Z.lxor (bv_unsigned (wz (sz * MM8))) MSEED)).
{ unfold hinitw. rewrite !(unsigned_lit sz) by lia.
replace (Z.land sz 4294967295) with sz by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite !(unsigned_lit sz) by lia. reflexivity. }
unfold MM8, MSEED in HI. rewrite <- HI. clear HI.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
assert (TRKc : u64arr asegs mc' tr (map wz ks)) by (rewrite <- TK; apply u64arr_take; assumption) end.
eapply evt_cut.
{ eapply (hash_loop (Z.to_nat sz) (map wz ks) 0); try eassumption; rewrite ?length_map; lia. }
cbv beta. intros ms' (a5' & a6' & ->). cbn [Z.to_nat skipn]. unfold MM at 1.
rewrite (Z.shiftr_div_pow2 sz 32), (Z.div_small sz (2 ^ 32)) by lia.
replace (skipn (Z.to_nat 0) (map wz ks)) with (map wz ks) by reflexivity.
step_until 0x83fb0.
lazymatch goal with |- context [bv_unsigned (wz (bv_unsigned ?w ≪ 44)) ≫ 42] => remember w as HW eqn:EHW end.
assert (EH : hfinw (fold_left hstepw (map wz ks) (hinitw (wz sz))) = HW) by (rewrite EHW; reflexivity). clear EHW.
pose proof (bv_unsigned_in_range 64 HW) as HR. change (bv_modulus 64) with (2^64)%Z in HR.
rewrite (bkt_shift (bv_unsigned HW)) by lia.
set (H := bv_unsigned HW) in *. set (b := bkt H) in *. pose proof (bkt_range H) as BR. fold b in BR.
assert (DH : dhash ks = H) by (unfold dhash, H; rewrite <- EH, SZ; reflexivity).

set (v := lastb nh b (Z.to_nat n)). pose proof (lastb_range nh b (Z.to_nat n)) as VR. fold v in VR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TB : rw_cells asegs mc (1917080 + 4 * b) [C4 (wz v)])
by (eapply rw_cells_transport; [exact (CTAB b BR)| exact MUs| exact WM| cbn; lia]) end.
remember (1917080 + 4 * b) as tba eqn:Etba.
istep. rewrite (sx32_small v) by lia.
step_until 0x83fd0.
rewrite ?(unsigned_lit v) by lia. replace (Z.land v 2147483647) with v by (change 2147483647 with (Z.ones 31); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite <- (Z_to_bv_lit_self HW). fold H.

eapply evt_cut.
{ lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (find_loop (Z.to_nat v) v H n nh ns mc) end.
- assumption.
- exact CMAP.
- intros i Hi. eapply rw_cells_transport; [exact (CND i Hi)| exact MUs| exact WM| cbn; lia].
- intros i Hi. exact (proj2 (HU i Hi)).
- subst H. lia.
- lia. - rewrite ?KHI_eq. lia. - idtac. lia. - lia.
- destruct (Z.eq_dec v 0) as [Z0|NZ]; [left; exact Z0| right]. split; [lia|]. unfold v. rewrite (lastb_bkt nh b (Z.to_nat n)) by (fold v; lia). reflexivity.
- intros j Hj Bj. exfalso. apply (lastb_max nh b (Z.to_nat n) j ltac:(fold v; lia)). exact Bj. }
cbv beta. intros ms' [FOUND|MISS].
{
destruct FOUND as (sF & a1' & a2' & -> & SFR & SFH).
step_until 0. release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
exists sF. split; [reflexivity|]. split; [lia|]. split; [| split; [exact TRQ| exists n; split; [eapply (depot_keep_of_munch asegs _ m); [exact MUs| exact WM| repeat constructor; cbn [fst snd]; unfold DP_N; lia| exact DN0]| lia]]].
exists n, tf, st, h0, j40, nh, ns. unfold SS_BASE, DP_TAB, DP_N, DP_MAP1. repeat (split; [assumption|]).
split. { intros b' Hb'. eapply rw_cells_transport; [exact (CTAB b' Hb')| exact MUs| exact WM| cbn; lia]. }
repeat (split; [assumption|]).
split. { intros i Hi. eapply rw_cells_transport; [exact (CND i Hi)| exact MUs| exact WM| cbn; lia]. }
split; [eapply hjunk_wmono; [exact JD| exact WM]|]. split; [eapply hjunk_wmono; [exact JS| exact WM]|]. exact TU. }
destruct MISS as (a0' & a2' & -> & NOTIN). unfold DP_MAP1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eassert (MUf : munch [(bv_unsigned sp - 224, bv_unsigned sp); (tba, tba + 4); (6111384, 6111388);
(rl_dn X + 16 * (n + 1), rl_dn X + 16 * (n + 1) + 16); (1851528, 1851560); (rl_ssb X, rl_ssb X + 0x800000)] m mc)
by (eapply munch_weaken; [| exact MUs]; intros y Hy; cbn [outside fst snd] in Hy |- *; tauto) end.
clear MUs.
istep. istep. call_u (lock_spec).
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact TB. } { lia. } { subst tba. lia. } { lia. } { idtac. lia. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST1 end.
match goal with H : exists lw, rw_cells asegs _ tba _ |- _ => destruct H as [lw TBL] end.
istep. istep. if_true_u.

istep. istep. istep.
assert (AMO4 : amo_aligned AW (wz 6111384) = true) by (apply amo_aligned_intro4; [lia| reflexivity]).
amo_step AMO4. rewrite (amoadd_w_bytes n 1) by lia. mem_after_store. rewrite ?sext_extract_le4, ?(sx32_small n) by lia.
istep. rewrite (addiw_small n 1) by lia.
istep. istep. rewrite ?(unsigned_lit (n + 1)), (zext32_small (n + 1)) by lia.
istep. rewrite bv_lts_zero_r. if_false_u.
istep. istep. rewrite ?(unsigned_lit (n + 1)), (Z.shiftr_div_pow2 (n + 1) 16), (Z.div_small (n + 1) (2 ^ 16)) by lia.
step_until 0. if_false_u.
istep. rewrite ?(unsigned_lit (n + 1)) by lia. replace (Z.land (n + 1) 65535) with (n + 1) by (change 65535 with (Z.ones 16); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
istep. rewrite ?(unsigned_lit (n + 1)), (Z.shiftl_mul_pow2 (n + 1) 4) by lia. change (2 ^ 4) with 16. rewrite (Z.mul_comm (n + 1) 16).
step_until 0x83ba8.

pose proof (hjunk_wmono _ _ _ _ JD WM) as JDc.
pose proof (fun Hm => proj1 (hjunk_split _ (rl_dn X + 16 * (n + 1)) (rl_dn X + 16 * (n + 1) + Z.of_nat 16) _ JDc Hm)) as JN. specialize (JN ltac:(cbn; lia)).
destruct (hjunk_cells _ (rl_dn X + 16 * (n + 1)) 16 JN) as [nj NODE]. clear JDc JN.
remember (rl_dn X + 16 * (n + 1)) as node eqn:Enode.
lazymatch type of FR with rw_cells _ ?mc _ (?c0 :: ?c1 :: ?c2 :: ?rest) =>
destruct (proj1 (rw_cells_app asegs mc _ [c0] (c1 :: c2 :: rest)) FR) as [FRa FRb];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRb;
destruct (proj1 (rw_cells_app asegs mc _ [c1; c2] rest) FRb) as [ARGS FRc];
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRc end.
replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in ARGS, FRc by lia.
replace (bv_unsigned sp + -104 + 16) with (bv_unsigned sp + -88) in FRc by lia. clear FR FRb.
apply (rw_C8_split32 _ _ sz [C8 (wz tr)] []) in ARGS; [| lia]. cbn [app] in ARGS.
call_pre (nstore_spec).
{ assumption. } { unsigned_lits. exact ST1. } { exact CEIL'. } { unsigned_lits. lia. } { exact NODE. } { exact ARGS. } { exact TRQ. } { exact LQ. }
{ exact SSC. } { eapply hjunk_wmono; [exact JS| exact WM]. }
{ lia. } { lia. } { lia. } { lia. } { subst H. lia. } { exact SA. } { lia. } { idtac. lia. } { subst node. lia. } { subst node. idtac. lia. }
{ subst node. lia. }
{ unsigned_lits. lia. } { unsigned_lits. lia. } { lia. }
post_later.
match goal with H : exists nj4, _ |- _ => destruct H as (nj4 & Ea0 & NODE' & SSC' & ARGS' & TRQ') end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST2 end.

istep. istep. istep. istep. istep. if_lit2.
step_until 0.
release_frame FRa ST2 (bv_unsigned sp + -104). release_frame ARGS' ST2 (bv_unsigned sp + -88). release_frame FRc ST2 (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST2|].
exists (n + 1). split; [reflexivity|]. split; [lia|]. split; [| split; [exact TRQ'|]].
2:{ exists (n + 1). split; [| lia]. unfold depot_n, DP_N. split; [assumption| lia]. }

set (nh' := fun i => if i =? n + 1 then H else nh i). set (ns' := fun i => if i =? n + 1 then tf + 1 else ns i).
assert (NHE : forall j, 1 <= j <= Z.of_nat (Z.to_nat n) -> nh' j = nh j) by (intros j Hj; unfold nh'; destruct (Z.eqb_spec j (n + 1)); [lia| reflexivity]).
assert (NHN : nh' (n + 1) = H) by (unfold nh'; rewrite Z.eqb_refl; reflexivity).
exists (n + 1), (tf + sz + 1), (st + sz + 1), h0, j40, nh', ns'. unfold SS_BASE, DP_TAB, DP_N, DP_MAP1.
split; [lia|]. split; [lia|]. split; [lia|].
split. { intros i Hi. unfold nh'. destruct (Z.eqb_spec i (n + 1)) as [->|NE].
- split; [unfold DEPOT_CAP; lia| lia].
- destruct (HU i ltac:(lia)) as [_ HRi]. split; [unfold DEPOT_CAP; lia| exact HRi]. }
split. { rewrite zseq_snoc, map_app by lia. cbn [map]. rewrite NHN.
rewrite (map_ext_in nh' nh) by (intros j Hj; apply NHE; apply zseq_In in Hj; lia).
apply NoDup_snoc; [exact ND|]. intros Hin. apply in_map_iff in Hin as (j & Ej & Hj). apply zseq_In in Hj. exact (NOTIN j Hj Ej). }
repeat (split; [assumption|]).
split. { intros b' Hb'. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia. cbn [lastb].
replace (Z.of_nat (S (Z.to_nat n))) with (n + 1) by lia. rewrite NHN. fold b.
destruct (Z.eqb_spec b b') as [<-|NE].
- rewrite <- Etba. exact TBL.
- rewrite (lastb_ext nh nh') by exact NHE.
eapply rw_cells_transport; [exact (CTAB b' Hb')| exact MUf| exact WM| cbn; subst tba node; lia]. }
repeat (split; [assumption|]).
split. { intros i Hi. destruct (Z.eq_dec i (n + 1)) as [->|NE].
- rewrite NHN. replace (Z.to_nat (n + 1 - 1)) with (Z.to_nat n) by lia. rewrite (lastb_ext nh nh') by exact NHE. fold b. fold v.
unfold ns'. rewrite Z.eqb_refl. rewrite <- Enode. exact NODE'.
- rewrite (NHE i) by lia. rewrite (lastb_ext nh nh') by (intros j Hj; apply NHE; lia).
unfold ns'. replace (i =? n + 1) with false by (symmetry; apply Z.eqb_neq; lia).
eapply rw_cells_transport; [exact (CND i ltac:(lia))| exact MUf| exact WM| cbn; subst tba node; lia]. }
split. { replace (rl_dn X + 16 * (n + 1 + 1)) with (rl_dn X + 16 * (n + 1) + Z.of_nat 16) by lia.
eapply hjunk_wmono; [| exact WM].
exact (proj2 (hjunk_split _ _ (rl_dn X + 16 * (n + 1) + Z.of_nat 16) _ JD ltac:(cbn; lia))). }
split; [eapply hjunk_wmono; [exact JS| exact WM]|]. assumption.
Qed.

End Walk.
End Mql.

Module Mqm.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QUvT.Mq0 QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QOJv.Mqb QNQk QsJM QpY2 QpY2.Mqe QpME.Mqa QYyZ.Mqd QYyZ.Mqe.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Pure.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Local Notation FS := (ae_fs_base RE).

Lemma live_user_heap' : forall x, in_live_user LB0 x -> ((0 < x < kLowEnd /\ (x < 0x10000 \/ 0x647000 <= x)) \/ KHI <= x) /\ x < band_lo.
Proof. intros x LU. exact (live_user_heap _ _ _ _ _ _ GC x LU). Qed.

Lemma gcons_ff_add : forall c pos f,
fs_shape FS FS0 -> 0 <= c < kFsClasses -> 0 <= pos < fs_N c -> f = fs_frame FS c pos ->
~ In f (map ff_addr FS0) -> fframe_rangeA RE c f ->
gcons a LB0 ((c, f) :: FS0) G RE X.
Proof.
intros c pos f SHP Hc Hp Ef FRESH FR. pose proof SHP as [SHf ND].
pose proof GC as GC'. unfold gcons in GC' |- *. decompose [and] GC'.
match goal with H : forall g, In g FS0 -> fframe_rangeA _ _ _ |- _ => rename H into A12 end.
match goal with H : forall f1 f2, In f1 FS0 -> In f2 FS0 -> _ |- _ => rename H into A13 end.
repeat (split; [assumption|]).
assert (APART : forall g, In g FS0 -> ff_addr g + ff_size (ff_cls g) <= f \/ f + ff_size c <= ff_addr g).
{ intros g Hg. destruct (SHf g Hg) as (Hcg & pg & Hpg & Eg). rewrite Eg, Ef.
destruct (Z.eq_dec (ff_cls g) c) as [Ecg|NE].
- rewrite Ecg in *. assert (pg <> pos) by (intros ->; apply FRESH; rewrite Ef, <- Eg; apply in_map; exact Hg).
destruct (fs_frame_apart FS c pg pos ltac:(lia) ltac:(lia)); lia.
- destruct (fs_frame_apart_cls FS (ff_cls g) pg c pos Hcg Hc NE Hpg Hp); lia. }
split.
- intros g [<-|Hg]; [exact FR| exact (A12 g Hg)].
- intros f1 f2 [<-|G1] [<-|G2] NE; cbn [ff_addr ff_cls fst snd] in *.
+ exfalso. apply NE. reflexivity.
+ destruct (APART f2 G2); lia.
+ destruct (APART f1 G1); lia.
+ exact (A13 f1 f2 G1 G2 NE).
Qed.

End Pure.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRT : forall RE X m, ac_RTconst C RE X m <-> RTconst RE X m.
Hypothesis HRF : forall FS RE X m, ac_RFake C FS RE X m <-> RFake FS RE X m.

Lemma ARUNX_fs : forall a LB0 FS0 FS0' G RE X m m' W,
ARUNX C a LB0 FS0 G RE X m -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> czone LB0 RE x) ->
RTconst RE X m' -> RFake FS0' RE X m' -> gcons a LB0 FS0' G RE X ->
ARUNX C a LB0 FS0' G RE X m'.
Proof.
intros a LB0 FS0 FS0' G RE X m m' W AX MU WM HW RT' RF' GC'. pose proof (proj1 AX) as GC.
destruct AX as (_ & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
assert (AG : forall P : Z -> Prop, (forall x, P x -> czone LB0 RE x -> False) -> agree_on asegs P m m').
{ intros P HP. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro.
intros lo hi Hin Hx. exact (HP x Px (HW lo hi x Hin Hx)). }
split; [exact GC'|].
split; [apply HRT; exact RT'|].
split; [eapply (ac_RStats_frame C); [exact R2| exact WM| apply AG; intros x; apply (fp_RStats_cz a LB0 FS0 G RE X GC)]|].
split; [eapply (ac_RPrim_frame C); [exact R3| exact WM| apply AG; intros x; apply (fp_RPrim_cz a LB0 FS0 G RE X GC)]|].
split; [eapply (ac_RChunks_frame C); [exact R4| exact WM| apply AG; intros x; apply (fp_RChunks_cz a LB0 FS0 G RE X GC)]|].
split; [eapply (ac_RSec_frame C); [exact R5| exact WM| apply AG; intros x; apply (fp_RSec_cz a LB0 FS0 G RE X GC)]|].
split; [eapply (ac_RQuar_frame C); [exact R6| exact WM| apply AG; intros x; apply (fp_RQuar_cz a LB0 FS0 G RE X GC)]|].
split; [eapply (ac_RDepot_frame C); [exact R7| exact WM| apply AG; intros x; apply (fp_RDepot_cz a LB0 FS0 G RE X GC)]|].
apply HRF. exact RF'.
Qed.

Lemma fs_W_czone : forall LB0 RE (slo shi : Z) lo hi x,
band_lo <= slo -> ae_fs_base RE mod 8 = 0 ->
In (lo, hi) [(ae_fs_base RE, ae_fs_base RE + A_FS_MAP_SIZE); (SH (ae_fs_base RE), SH (ae_fs_base RE + A_FS_MAP_SIZE)); (slo, shi)] ->
lo <= x < hi -> czone LB0 RE x.
Proof.
intros LB0 RE slo shi lo hi x CE AL Hin Hx. unfold czone, in_iv, in_sh. cbn [fst snd].
assert (SHD : SH (ae_fs_base RE + A_FS_MAP_SIZE) = SH (ae_fs_base RE) + A_FS_MAP_SIZE / 8).
{ rewrite !SH_eq. unfold A_FS_MAP_SIZE. replace (ae_fs_base RE + 11571200) with (ae_fs_base RE + 1446400 * 8) by lia. rewrite Z.div_add by lia.
change (11571200 / 8) with 1446400. lia. }
cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.

Lemma filter_perm_length : forall (c : Z) (FS FS' : list fframe), Permutation FS FS' ->
length (filter (fun f : fframe => ff_cls f =? c) FS) = length (filter (fun f : fframe => ff_cls f =? c) FS').
Proof. intros c FS FS' P. apply Permutation_length. apply (Permutation_filter (fun f : fframe => ff_cls f =? c)). exact P. Qed.

Lemma fs_op_pres : forall a LB0 FS0 G RE X LB FSc (SP slo h szsh : Z) m m' c pos f,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> fs_shape (ae_fs_base RE) FS0 ->
(forall g, In g FSc -> In g FS0 /\ ff_addr g <> f) ->
0 <= c < kFsClasses -> 0 <= pos < fs_N c -> f = fs_frame (ae_fs_base RE) c pos ->
0 <= szsh <= ff_size c / 8 -> ae_fs_base RE <= h -> h + 8 <= ae_fs_base RE + 88 ->
band_lo <= slo -> band_lo <= SP ->
munch [(slo, SP); (h, h + 8); (fs_flag (ae_fs_base RE) c pos, fs_flag (ae_fs_base RE) c pos + 1); (f, f + ff_size c); (SH f, SH f + szsh)] m m' ->
wmono asegs m m' ->
aheap_presA asegs a_alayout LB FSc SP m m'.
Proof.
intros a LB0 FS0 G RE X LB FSc SP slo h szsh m m' c pos f GC PB SHP HFS Hc Hp Ef Hsz Hh1 Hh2 CE CSP MU WM.
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CEo & _). cbn [fst snd] in AL, K, CEo.
pose proof K as K'. pose proof CEo as CE'. rewrite ?KHI_eq in K'. idtac. unfold A_FS_MAP_SIZE in CE', K'.
pose proof (fs_frame_in_area (ae_fs_base RE) c pos Hc Hp) as [A1 A2]. rewrite <- Ef in A1, A2. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in A1, A2.
assert (SZ : 64 <= ff_size c) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c); lia).
assert (FAL : f mod 8 = 0) by (pose proof (fs_frame_align (ae_fs_base RE) c pos ltac:(Z.div_mod_to_equations; lia) ltac:(lia)); rewrite <- Ef in *; Z.div_mod_to_equations; lia).
pose proof (fs_flag_range (ae_fs_base RE) c pos Hc Hp) as FR.
assert (SHf : 0x800c0e00 <= SH f /\ SH f + ff_size c / 8 <= SH band_lo).
{ split; [rewrite SH_eq; clear - K' A1; Z.div_mod_to_equations; lia|].
replace (SH f + ff_size c / 8) with (SH (f + ff_size c)); [apply SH_mono; idtac; lia|].
rewrite !SH_eq. rewrite ff_size_eq in * by lia. replace (c + 6) with (Z.succ (Z.succ (Z.succ (c + 3)))) by lia.
rewrite !Z.pow_succ_r by lia. replace (2 * (2 * (2 * 2 ^ (c + 3)))) with (2 ^ (c + 3) * 8) by lia.
rewrite Z.div_add, Z.div_mul by lia. lia. }
pose proof SH_band as SHB0.
unfold aheap_presA. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x CA Hx. apply outside_intro. intros lo hi Hin [Y1 Y2].
cbn in Hin.
destruct CA as [C1|[C1|[C1|[(g & Hg & G1 & G2)|[(g & Hg & G1 & G2)|[C1|C1]]]]]].
-  pose proof SH_band. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
-  cbn [ala_client_data a_alayout] in C1. unfold a_client_data in C1.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
-
assert (LU : in_live_user LB0 x) by (destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R]).
pose proof (live_user_heap' _ _ _ _ _ _ GC x LU) as LH. rewrite ?KHI_eq in LH. unfold kLowEnd in LH.
pose proof (live_user_not_fs _ _ _ _ _ _ GC x LU) as NF. unfold A_FS_MAP_SIZE in NF. pose proof SH_band.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
-
destruct (HFS g Hg) as [Hg0 NEg]. pose proof SHP as [SHf' _]. destruct (SHf' g Hg0) as (Hcg & pg & Hpg & Eg).
pose proof (fs_frame_in_area (ae_fs_base RE) (ff_cls g) pg Hcg Hpg) as [B1 B2]. rewrite <- Eg in B1, B2. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in B1, B2.
assert (APART : ff_addr g + ff_size (ff_cls g) <= f \/ f + ff_size c <= ff_addr g).
{ rewrite Eg, Ef. destruct (Z.eq_dec (ff_cls g) c) as [Ecg|NE].
- rewrite Ecg in *. assert (pg <> pos) by (intros ->; apply NEg; rewrite Eg, Ef; reflexivity).
destruct (fs_frame_apart (ae_fs_base RE) c pg pos ltac:(lia) ltac:(lia)); lia.
- destruct (fs_frame_apart_cls (ae_fs_base RE) (ff_cls g) pg c pos Hcg Hc NE Hpg Hp); lia. }
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
-
destruct (HFS g Hg) as [Hg0 NEg]. pose proof SHP as [SHf' _]. destruct (SHf' g Hg0) as (Hcg & pg & Hpg & Eg).
pose proof (fs_frame_in_area (ae_fs_base RE) (ff_cls g) pg Hcg Hpg) as [B1 B2]. rewrite <- Eg in B1, B2. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in B1, B2.
assert (SZg : 64 <= ff_size (ff_cls g)) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 (ff_cls g)); lia).
assert (GAL : ff_addr g mod 8 = 0)
by (pose proof (fs_frame_align (ae_fs_base RE) (ff_cls g) pg ltac:(Z.div_mod_to_equations; lia) ltac:(lia)); rewrite <- Eg in *; Z.div_mod_to_equations; lia).
assert (APART : ff_addr g + ff_size (ff_cls g) <= f \/ f + ff_size c <= ff_addr g).
{ rewrite Eg, Ef. destruct (Z.eq_dec (ff_cls g) c) as [Ecg|NE].
- rewrite Ecg in *. assert (pg <> pos) by (intros ->; apply NEg; rewrite Eg, Ef; reflexivity).
destruct (fs_frame_apart (ae_fs_base RE) c pg pos ltac:(lia) ltac:(lia)); lia.
- destruct (fs_frame_apart_cls (ae_fs_base RE) (ff_cls g) pg c pos Hcg Hc NE Hpg Hp); lia. }
assert (GH : 0x7fff7000 <= x < 0x10007fff8000).
{ pose proof (@in_sh_band BAND (ff_addr g) (ff_size (ff_cls g)) x GAL ltac:(lia) ltac:(clear - K' B1 B2 SZg; lia) ltac:(lia) ltac:(split; cbn [fst snd]; lia)) as B0.
unfold kLowEnd, KHI in B0. exact B0. }
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; try lia.
eapply (in_sh_disjoint (ff_addr g) (ff_size (ff_cls g)) f (ff_size c) x GAL FAL ltac:(lia) ltac:(lia) APART (conj G1 G2)).
split; cbn [fst snd]; lia.
-  rewrite SH_247, ?KHI_eq in C1. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
-  cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. change (933888 / 8) with 116736 in C1.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia.
Qed.

Lemma RFake_shape : forall FS RE X m, RFake FS RE X m -> fs_shape (ae_fs_base RE) FS.
Proof. intros FS RE X m (_ & _ & _ & SHP & _). exact SHP. Qed.

Ltac open_run AR X G LB0 FS0 PB PF AX GC RT RF :=
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX);
pose proof (proj1 AX) as GC;
pose proof (proj1 (HRT _ _ _) (proj1 (proj2 AX))) as RT;
pose proof (proj1 (HRF _ _ _ _) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AX))))))))) as RF.

Lemma stack_malloc_0_A : astack_mallocA_stmt asegs a_alayout (ARUN C) 0 fsmalloc0_entry.
Proof.
unfold astack_mallocA_stmt. intros until lo. intros AR ROOM ST CEIL LO MI Htp Hgp Ha0 SZ SAL.
open_run AR X G LB0 FS0 PB PF AX GC RT RF. pose proof (proj1 GC) as RL.
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CEo & _). cbn [fst snd] in AL, K, CEo.
subst tp gp. cbn [ala_tp ala_gp ala_stack_malloc_stack a_alayout] in *.
rewrite (filter_perm_length 0 FS FS0 PF) in ROOM. change (fframe_cap 0) with (fs_N 0) in ROOM.
eapply evt_mono.
{ eapply (fsmalloc0_spec RE X); [exact RT| exact RL| exact RF| exact MI| exact ST| exact CEIL| lia| exact ROOM| exact Ha0]. }
cbv beta. intros ms' POST. unfold rpost in POST.
destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & STK'
& f & pos & junk & Ea0 & Ef & PR & FRESH & FR & RT' & RF' & BODY & SHC & MU2).
subst ms'. unfold std_postA. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact STK'|].
split.
{ eapply (fs_op_pres _ LB0 FS0 G RE X LB FS (bv_unsigned sp) (bv_unsigned sp - 224) (ae_fs_base RE) (ff_size 0 / 8) m m' 0 pos f GC PB
(RFake_shape _ _ _ _ RF)); try eassumption.
- intros g Hg. assert (Hg0 : In g FS0) by (eapply Permutation_in; [exact PF| exact Hg]). split; [exact Hg0|].
intros Eg. apply FRESH. rewrite <- Eg. apply in_map. exact Hg0.
- unfold kFsClasses. lia.
- change (ff_size 0 / 8) with 8. lia.
- lia. - lia. - lia. - lia. }
split; [reflexivity|]. split; [reflexivity|].
split.
{
eapply depot_keep_of_munch; [exact MU| exact WM|]. unfold DP_N.
constructor; [cbn [fst snd]; unfold A_FS_MAP_SIZE in *; lia|]. constructor; [cbn [fst snd]; rewrite !SH_eq; unfold A_FS_MAP_SIZE in *; Z.div_mod_to_equations; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
exists f, junk.
split; [exact Ea0|]. split; [exact FR|].
split.
{ apply (ARUN_close C s LB ((0, f) :: FS) RE m' X G LB0 ((0, f) :: FS0)); [exact PB| apply perm_skip; exact PF|].
eapply (ARUNX_fs _ LB0 FS0 _ G RE X m m'); [exact AX| exact MU| exact WM| | exact RT'| exact RF'|].
- intros lo' hi' x Hin Hx. eapply (fs_W_czone LB0 RE (bv_unsigned sp - 224) (bv_unsigned sp)); [lia| Z.div_mod_to_equations; lia| exact Hin| exact Hx].
- eapply (gcons_ff_add _ LB0 FS0 G RE X GC 0 pos f (RFake_shape _ _ _ _ RF)); [unfold kFsClasses; lia| exact PR| exact Ef| exact FRESH| exact FR]. }
split; [exact BODY|].
eapply rw_cells_recast'; [exact SHC| |].
- cbn. rewrite !repeat_length. easy.
- reflexivity.
Qed.

Lemma stack_malloc_1_A : astack_mallocA_stmt asegs a_alayout (ARUN C) 1 fsmalloc1_entry.
Proof.
unfold astack_mallocA_stmt. intros until lo. intros AR ROOM ST CEIL LO MI Htp Hgp Ha0 SZ SAL.
open_run AR X G LB0 FS0 PB PF AX GC RT RF. pose proof (proj1 GC) as RL.
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CEo & _). cbn [fst snd] in AL, K, CEo.
subst tp gp. cbn [ala_tp ala_gp ala_stack_malloc_stack a_alayout] in *.
rewrite (filter_perm_length 1 FS FS0 PF) in ROOM. change (fframe_cap 1) with (fs_N 1) in ROOM.
eapply evt_mono.
{ eapply (fsmalloc1_spec RE X); [exact RT| exact RL| exact RF| exact MI| exact ST| exact CEIL| lia| exact ROOM| exact Ha0]. }
cbv beta. intros ms' POST. unfold rpost in POST.
destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & STK'
& f & pos & junk & Ea0 & Ef & PR & FRESH & FR & RT' & RF' & BODY & SHC & MU2).
subst ms'. unfold std_postA. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact STK'|].
split.
{ eapply (fs_op_pres _ LB0 FS0 G RE X LB FS (bv_unsigned sp) (bv_unsigned sp - 224) (ae_fs_base RE + 8) (ff_size 1 / 8) m m' 1 pos f GC PB
(RFake_shape _ _ _ _ RF)); try eassumption.
- intros g Hg. assert (Hg0 : In g FS0) by (eapply Permutation_in; [exact PF| exact Hg]). split; [exact Hg0|].
intros Eg. apply FRESH. rewrite <- Eg. apply in_map. exact Hg0.
- unfold kFsClasses. lia.
- change (ff_size 1 / 8) with 16. lia.
- lia. - lia. - lia. - lia. }
split; [reflexivity|]. split; [reflexivity|].
split.
{
eapply depot_keep_of_munch; [exact MU| exact WM|]. unfold DP_N.
constructor; [cbn [fst snd]; unfold A_FS_MAP_SIZE in *; lia|]. constructor; [cbn [fst snd]; rewrite !SH_eq; unfold A_FS_MAP_SIZE in *; Z.div_mod_to_equations; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
exists f, junk.
split; [exact Ea0|]. split; [exact FR|].
split.
{ apply (ARUN_close C s LB ((1, f) :: FS) RE m' X G LB0 ((1, f) :: FS0)); [exact PB| apply perm_skip; exact PF|].
eapply (ARUNX_fs _ LB0 FS0 _ G RE X m m'); [exact AX| exact MU| exact WM| | exact RT'| exact RF'|].
- intros lo' hi' x Hin Hx. eapply (fs_W_czone LB0 RE (bv_unsigned sp - 224) (bv_unsigned sp)); [lia| Z.div_mod_to_equations; lia| exact Hin| exact Hx].
- eapply (gcons_ff_add _ LB0 FS0 G RE X GC 1 pos f (RFake_shape _ _ _ _ RF)); [unfold kFsClasses; lia| exact PR| exact Ef| exact FRESH| exact FR]. }
split; [exact BODY|].
eapply rw_cells_recast'; [exact SHC| |].
- cbn. rewrite !repeat_length. easy.
- reflexivity.
Qed.

Lemma stack_malloc_2_A : astack_mallocA_stmt asegs a_alayout (ARUN C) 2 fsmalloc2_entry.
Proof.
unfold astack_mallocA_stmt. intros until lo. intros AR ROOM ST CEIL LO MI Htp Hgp Ha0 SZ SAL.
open_run AR X G LB0 FS0 PB PF AX GC RT RF. pose proof (proj1 GC) as RL.
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CEo & _). cbn [fst snd] in AL, K, CEo.
subst tp gp. cbn [ala_tp ala_gp ala_stack_malloc_stack a_alayout] in *.
rewrite (filter_perm_length 2 FS FS0 PF) in ROOM. change (fframe_cap 2) with (fs_N 2) in ROOM.
eapply evt_mono.
{ eapply (fsmalloc2_spec RE X); [exact RT| exact RL| exact RF| exact MI| exact ST| exact CEIL| lia| exact ROOM| exact Ha0]. }
cbv beta. intros ms' POST. unfold rpost in POST.
destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & STK'
& f & pos & junk & Ea0 & Ef & PR & FRESH & FR & RT' & RF' & BODY & SHC & MU2).
subst ms'. unfold std_postA. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact STK'|].
split.
{ eapply (fs_op_pres _ LB0 FS0 G RE X LB FS (bv_unsigned sp) (bv_unsigned sp - 224) (ae_fs_base RE + 16) (ff_size 2 / 8) m m' 2 pos f GC PB
(RFake_shape _ _ _ _ RF)); try eassumption.
- intros g Hg. assert (Hg0 : In g FS0) by (eapply Permutation_in; [exact PF| exact Hg]). split; [exact Hg0|].
intros Eg. apply FRESH. rewrite <- Eg. apply in_map. exact Hg0.
- unfold kFsClasses. lia.
- change (ff_size 2 / 8) with 32. lia.
- lia. - lia. - lia. - lia. }
split; [reflexivity|]. split; [reflexivity|].
split.
{
eapply depot_keep_of_munch; [exact MU| exact WM|]. unfold DP_N.
constructor; [cbn [fst snd]; unfold A_FS_MAP_SIZE in *; lia|]. constructor; [cbn [fst snd]; rewrite !SH_eq; unfold A_FS_MAP_SIZE in *; Z.div_mod_to_equations; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
exists f, junk.
split; [exact Ea0|]. split; [exact FR|].
split.
{ apply (ARUN_close C s LB ((2, f) :: FS) RE m' X G LB0 ((2, f) :: FS0)); [exact PB| apply perm_skip; exact PF|].
eapply (ARUNX_fs _ LB0 FS0 _ G RE X m m'); [exact AX| exact MU| exact WM| | exact RT'| exact RF'|].
- intros lo' hi' x Hin Hx. eapply (fs_W_czone LB0 RE (bv_unsigned sp - 224) (bv_unsigned sp)); [lia| Z.div_mod_to_equations; lia| exact Hin| exact Hx].
- eapply (gcons_ff_add _ LB0 FS0 G RE X GC 2 pos f (RFake_shape _ _ _ _ RF)); [unfold kFsClasses; lia| exact PR| exact Ef| exact FRESH| exact FR]. }
split; [exact BODY|].
eapply rw_cells_recast'; [exact SHC| |].
- cbn. rewrite !repeat_length. easy.
- reflexivity.
Qed.

End Lift.
End Mqm.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoNr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoNr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFd5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFd5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Definition got_ssp := 0xe8f90%Z.
Definition ssp_guard := 0x645560%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].

Definition pad_n (w l fl : Z) : Z :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z || (w <=? l)%Z then 0 else w - l.

Lemma pad_model : forall o c w l fl, (w - l < 256)%Z ->
pad o c w l fl = Some (o ++ zrepeat c (pad_n w l fl)).
Proof.
intros o c w l fl H. unfold pad, pad_n.
destruct (negb _ || _); [cbn; now rewrite app_nil_r|].
change PAD_FUEL with (S 63). cbn [pad_loop].
destruct (Z.leb_spec0 256 (w - l)); [lia|]. reflexivity.
Qed.

Ltac hyp := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.

Definition memset_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D C N lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(D, D + N); (lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q
/\ rw_cells asegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
Lemma memset_callZ {BAND : Band} : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q D C N lo : Z) (junk : list byte),
rw_cells asegs m D [CB (Z.to_nat N) junk] ->
mem_inv asegs m ->
(0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z -> (0 <= C < 256)%Z -> (0 <= N < 2^64)%Z ->
stk asegs m lo q -> band_lo <= lo -> lo <= q - MEMSET_ICPT_STACK -> (D + N <= lo \/ q <= D) ->
shadow_base asegs m -> rt_consts_at asegs m -> rng_ok m D N ->
evt asegs (memset_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N lo m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61b10) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros DST MI Hq HD HC HN ST CEIL LO SEP SB RC RNG.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (memset_icpt_spec D C N lo junk ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
intros ms' P. unfold memset_icpt_post in P. unfold memset_postZ. rewrite !Eq in P. rewrite (Z.mod_small C 256) by lia. exact P.
Qed.

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.
