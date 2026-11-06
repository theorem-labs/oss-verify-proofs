(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd QCUT QwAs Qc6I QJFf QVsB Qsn5 Qknc QBrp Q2ui Q1KO QCiC Qpj5 QvDJ Q6sh QQwg QKTr QzgH QNqr QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB.
Import Qsn5 QJFf.Mq1 Qknc QBrp Q2ui Q1KO.
Import QCiC.Mq1 Qpj5.Mq1 QCiC QvDJ.Mq1.
Import Q6sh QQwg Qpj5.Mq0 QvDJ QKTr QzgH.
Import QNqr QeDS.
Import ListNotations.
Open Scope Z_scope.

Section LedgerCps.
Variable L : ALay.
Variable LV : lvp.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).
Variables TOT0 N0 : Z.
Hypothesis LL : ll_ok L LV BUDGET PERM TOT0 N0.

Lemma node_of_not_spin : forall e, is_spinA (node_of e) = false.
Proof. intros [len avoid|addr len|addr len|addr len]; reflexivity. Qed.

Lemma node_of_no_exit : forall e mo code mo', ~ nexit_raw (node_of e) mo code mo'.
Proof. intros [len avoid|addr len|addr len|addr len] mo code mo' H; exact H. Qed.

Lemma node_of_silent : forall e mo rsp mo' evs, nstep_raw LV (node_of e) mo rsp mo' evs -> evs = [].
Proof. intros [len avoid|addr len|addr len|addr len] mo rsp mo' evs H; cbn [node_of nstep_raw] in H; destruct H as [H _]; exact H. Qed.

Lemma ev_step_grant : forall e mo rsp mo' evs ans,
nstep_raw LV (node_of e) mo rsp mo' evs -> dec_of e rsp = Some ans -> exists b, ans = AOk b.
Proof.
intros [len avoid|addr len|addr len|addr len] mo rsp mo' evs ans Hst Hd; cbn [node_of dec_of] in *.
- cbn [nstep_raw] in Hst. destruct Hst as [_ Hst]. rewrite kind_anon in Hst.
destruct Hst as (a & ws & _ & _ & _ & _ & ->). unfold dec_anonA, rsp_grant in Hd.
destruct ws; [|]; match type of Hd with (if ?c then _ else _) = _ => destruct c end; inversion Hd; eauto.
- cbn [nstep_raw] in Hst. destruct Hst as [_ Hst]. rewrite kind_fixed in Hst.
assert (Hr : exists ws, rsp = rsp_grant (Z_to_bv 64 addr) (rlenw len) ws).
{ destruct (fixed_contained mo (Z_to_bv 64 addr) (rlenw len)); [destruct Hst as [_ ->]; eauto|].
destruct (fixed_free mo (Z_to_bv 64 addr) (rlenw len)); [|destruct Hst]. destruct Hst as (ws & _ & _ & _ & ->). eauto. }
destruct Hr as [ws ->]. unfold dec_fixedA, rsp_grant in Hd.
destruct ws; [|discriminate]. match type of Hd with (if ?c then _ else _) = _ => destruct c end; inversion Hd; eauto.
- cbn [nstep_raw] in Hst. destruct Hst as [_ Hst]. rewrite kind_remap in Hst. destruct Hst as [_ ->].
unfold dec_remapA, dec_fixedA_full, rsp_remap in Hd.
match type of Hd with (if ?c then _ else _) = _ => destruct c end; inversion Hd; eauto.
- unfold dec_munmapA in Hd. destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct us as [|[a n] us]; [discriminate|]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
match type of Hd with (if ?c then _ else _) = _ => destruct c end; inversion Hd; eauto.
Qed.

Definition aokG (e : evA) (a : ansA) : Prop := aok0 e a /\ exists b, a = AOk b.
Definition rokS {R} (P : R -> Prop) (r : res R) : Prop :=
match r with ROk x => P x | RSpin => False | RUnr _ => False end.

End LedgerCps.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqyb QOb0 Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB.
Import Qsn5 QJFf.Mq1 Qqyb.Mq0 Qknc QBrp Q2ui Q1KO.
Import QCiC.Mq1 QOb0.Mq0 Qt4u.Mq0 Q6sh QvDJ QKTr QzgH.
Import ListNotations.
Open Scope Z_scope.

Section LedgerForeign.
Variable L : ALay.
Variable LV : lvp.

Lemma ll_ok_ext : forall B P T N B' FG T' N',
ll_ok L LV B P T N -> 0 <= B' ->
(forall r, In r FG -> 0 < fst r /\ fst r < snd r /\ snd r <= kCeil) ->
0 <= T' <= T -> 0 <= N' <= N ->
ll_ok L LV B' (FG ++ P) T' N'.
Proof.
intros B P T N B' FG T' N' LL HB HFG HT HN. destruct LL as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12].
constructor; try assumption.
- intros r Hr. apply in_app_iff in Hr as [Hr|Hr]; [exact (HFG r Hr)| exact (l3 r Hr)].
- intros iv Hiv. destruct (l4 iv Hiv) as [H1 H2]. split; [exact H1|]. intros y Hy.
destruct (H2 y Hy) as [(r & Hr & R)|[H|H]]; [left; exists r; split; [apply in_app_iff; right; exact Hr| exact R]| right; left; exact H| right; right; exact H].
- destruct l5 as (r & Hr & R). exists r. split; [apply in_app_iff; right; exact Hr| exact R].
- destruct l6 as (r & Hr & R). exists r. split; [apply in_app_iff; right; exact Hr| exact R].
- destruct l7 as (r & Hr & R). exists r. split; [apply in_app_iff; right; exact Hr| exact R].
- destruct l8 as (r & Hr & R). exists r. split; [apply in_app_iff; right; exact Hr| exact R].
- intros y Hy. destruct (l9 y Hy) as (r & Hr & R). exists r. split; [apply in_app_iff; right; exact Hr| exact R].
- destruct l12 as (G0 & G1 & G2). split; [lia|]. split; [lia|].
assert (0 <= kMaxChunk + 4095) by (unfold kMaxChunk; lia). nia.
Qed.

Lemma app_cov_mono : forall P P' h y, (forall r, In r P -> In r P') -> app_cov LV P h y -> app_cov LV P' h y.
Proof. intros P P' h y HP [H|(r & Hr & R)]; [left; exact H| right; exists r; split; [apply HP; exact Hr| exact R]]. Qed.

Lemma KI_perm_equiv : forall B P P' T N g mo, (forall r, In r P <-> In r P') -> KI LV B P T N g mo -> KI LV B P' T N g mo.
Proof.
intros B P P' T N g mo HP K. destruct K as [k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11].
constructor; try assumption.
- intros r Hr. apply k3. apply HP. exact Hr.
- intros iv y Hiv Hy. destruct (k10 iv y Hiv Hy) as [H|[H|(y' & H & E)]]; [left; exact H| right; left| right; right; exists y'; split; [|exact E]];
(eapply app_cov_mono; [| exact H]); intros r Hr; apply HP; exact Hr.
Qed.

Theorem KI_chunk_to_perm : forall B P T N c chunks sp k mo,
KI LV B P T N (mkG (c :: chunks) (sp + k)) mo ->
count_occ pdec (vm_maps (m_vmmaps mo)) (cent c) = 1%nat -> 0 <= sp ->
KI LV (B - k) (civ c :: P) (T + snd c) (N + 1) (mkG chunks sp) mo.
Proof.
intros B P T N c chunks sp k mo K Hcnt Hsp. destruct K as [k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11]. cbn [g_chunks g_spent] in *.
pose proof (k4 c (or_introl eq_refl)) as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
assert (Ceil : kCeil = 0x7fffff800000) by apply kCeil_val. rewrite Ceil in C6. unfold kMaxChunk in C3.
assert (Ua : bv_unsigned (w64 (fst c)) = fst c) by (apply u_w64; lia).
assert (Un : bv_unsigned (w64 (snd c)) = snd c) by (apply u_w64; lia).
assert (Ez : z2w (civ c) = cent c).
{ unfold z2w, civ, cent. cbn [fst snd]. replace (fst c + snd c - fst c) with (snd c) by lia. reflexivity. }
apply region_free_app in C9 as [C9r C9m]. rewrite region_free_iff in C9m.
constructor; cbn [g_chunks g_spent]; try assumption.
-
intros r [<-|Hr].
+ unfold perm_ok. rewrite Ez. split; [exact C7|]. split.
{ intros e He. destruct (bv_eqb (fst e) (w64 (fst c))) eqn:E.
- apply Fs.bv_eqb_eq in E. left. destruct e as [eb es]. cbn [fst snd] in *. subst eb. unfold cent. f_equal. exact (C8 _ He eq_refl).
- right. assert (Hin : In e (map_remove (vm_maps (m_vmmaps mo)) (w64 (fst c)))).
{ apply In_map_remove. split; [exact He|]. intros E'. rewrite E', bv_eqb_refl in E. discriminate. }
specialize (C9m (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact Hin)). rewrite Ua, Un in C9m.
unfold zdisj, wiv2z, civ. cbn [fst snd]. lia. }
split; [exact Hcnt|]. split; [exact C9r|].
intros c' Hc'. pose proof (k4 c' (or_intror Hc')) as (D0 & _ & D2 & D3 & _ & _ & D6 & D7 & _). rewrite Ceil in D6. unfold kMaxChunk in D3.
assert (Ua' : bv_unsigned (w64 (fst c')) = fst c') by (apply u_w64; lia).
assert (Un' : bv_unsigned (w64 (snd c')) = snd c') by (apply u_w64; lia).
assert (Hne : fst c' <> fst c).
{ inversion k5 as [|x l Hnin _]; subst. intros E. apply Hnin. apply in_map_iff. exists c'. split; [exact E| exact Hc']. }
assert (Hin : In (cent c') (map_remove (vm_maps (m_vmmaps mo)) (w64 (fst c)))).
{ apply In_map_remove. split; [exact D7|]. unfold cent. cbn [fst]. intros E. apply Hne. rewrite <- Ua', <- Ua, E. reflexivity. }
specialize (C9m _ _ Hin). rewrite Ua, Un, Ua', Un' in C9m. unfold zdisj, civ. cbn [fst snd]. lia.
+ destruct (k3 r Hr) as (P1 & P2 & P3 & P4 & P5). unfold perm_ok. repeat split; try assumption.
intros c' Hc'. apply P5. right. exact Hc'.
- intros c' Hc'. apply k4. right. exact Hc'.
- inversion k5; assumption.
- lia.
- intros iv y Hiv Hy. destruct (k10 iv y Hiv Hy) as [H|[H|(y' & H & E)]]; [left; exact H| right; left| right; right; exists y'; split; [|exact E]];
(eapply app_cov_mono; [| exact H]); intros r Hr; right; exact Hr.
- destruct k11 as [T1 T2]. cbn [map snd] in T1. rewrite zsum_cons in T1. rewrite zlen_cons in T2. split; lia.
Qed.

Theorem KI_perm_to_chunk : forall B P T N r g k mo,
KI LV B (r :: P) T N g mo ->
~ In r P -> (forall r', In r' P -> 0 < fst r' /\ fst r' < snd r' /\ snd r' <= kCeil) ->
0 < fst r -> fst r mod 4096 = 0 -> (snd r - fst r) mod 4096 = 0 -> 0 < snd r - fst r <= kMaxChunk ->
(snd r <= kLowEnd \/ KHI <= fst r) -> snd r <= kCeil -> excl_entry LV (z2w r) = false ->
(forall iv y, In iv (lv_base LV) -> fst r <= y < snd r -> ~ (fst iv <= y < snd iv) /\ ~ (fst iv <= shz LV y < snd iv)) ->
0 <= k ->
KI LV (B + k) P (T - (snd r - fst r)) (N - 1) (mkG ((fst r, snd r - fst r) :: g_chunks g) (g_spent g + k)) mo.
Proof.
intros B P T N r g k mo K Hnin HP Hr0 Hal Hlal Hl Hpl Hceil Hex Hbase Hk.
destruct K as [k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11].
assert (Ceil : kCeil = 0x7fffff800000) by apply kCeil_val. rewrite Ceil in Hceil. unfold kMaxChunk in Hl.
set (l := snd r - fst r) in *.
destruct (k3 r (or_introl eq_refl)) as (P1 & P2 & P3 & P4 & P5).
assert (Ua : bv_unsigned (w64 (fst r)) = fst r) by (apply u_w64; lia).
assert (Un : bv_unsigned (w64 l) = l) by (apply u_w64; unfold l; lia).
assert (Ez : z2w r = cent (fst r, l)) by reflexivity.
assert (Ew : wiv2z (z2w r) = r) by (apply wiv2z_z2w; lia).
constructor; cbn [g_chunks g_spent]; try assumption.
-
intros r' Hr'. destruct (k3 r' (or_intror Hr')) as (Q1 & Q2 & Q3 & Q4 & Q5). unfold perm_ok. repeat split; try assumption.
intros c [<-|Hc]; [| exact (Q5 c Hc)].
destruct (Q2 (z2w r) P1) as [E|D].
+ exfalso. apply Hnin. destruct (HP r' Hr') as (A1 & A2 & A3). rewrite Ceil in A3.
assert (Ew' : wiv2z (z2w r') = r') by (apply wiv2z_z2w; lia). rewrite <- Ew, E, Ew'. exact Hr'.
+ rewrite Ew in D. unfold zdisj, civ in *. cbn [fst snd]. unfold l. destruct D; [right| left]; lia.
-
intros c [<-|Hc]; [| exact (k4 c Hc)]. unfold chunk_ok. cbn [fst snd]. rewrite <- Ez.
split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [unfold kMaxChunk; lia|]. split; [exact Hlal|].
split; [unfold l; destruct Hpl; [left| right]; lia|]. split; [rewrite Ceil; unfold l; lia|]. split; [exact P1|]. split.
{ intros e He Efst. destruct (P2 e He) as [->|D]; [reflexivity|]. exfalso.
pose proof (k6 e He) as Hne. unfold zdisj, wiv2z in D. cbn [fst snd] in D. rewrite Efst, Ua in D. unfold l in *. lia. }
split; [| exact Hex].
apply region_free_app. split; [exact P4|]. rewrite region_free_iff. intros b s Hin. apply In_map_remove in Hin as [Hin Hne]. cbn [fst] in Hne.
destruct (P2 (b, s) Hin) as [E|D].
+ exfalso. apply Hne. injection E as -> _. reflexivity.
+ unfold zdisj, wiv2z in D. cbn [fst snd] in D. change (fst (z2w r)) with (w64 (fst r)). change (snd (z2w r)) with (w64 l).
rewrite Ua, Un. unfold l. lia.
-
constructor; [| exact k5]. cbn [fst]. intros Hin. apply in_map_iff in Hin as (c & Efst & Hc).
pose proof (P5 c Hc) as D. pose proof (k4 c Hc) as (_ & _ & D2 & _). unfold zdisj, civ in D. cbn [fst snd] in D. unfold l in *. lia.
- lia.
- lia.
-
intros iv y Hiv Hy. destruct (k10 iv y Hiv Hy) as [H|[H|(y' & H & E)]]; [left; exact H| |].
+ right; left. destruct H as [H|(r' & [<-|Hr'] & Hx & R)]; [left; exact H| | right; exists r'; auto].
exfalso. exact (proj1 (Hbase iv y Hiv R) Hy).
+ right; right. exists y'. split; [| exact E]. destruct H as [H|(r' & [<-|Hr'] & Hx & R)]; [left; exact H| | right; exists r'; auto].
exfalso. subst y. exact (proj2 (Hbase iv y' Hiv R) Hy).
- destruct k11 as [T1 T2]. cbn [map snd]. rewrite zsum_cons, zlen_cons. split; lia.
Qed.

End LedgerForeign.
End Mq1.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi QHWH Qqcs QdTb Q1lV QLiw QTtp QwuX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QQIi QHWH Qqcs QdTb Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf.
Import Qsn5 QJFf.Mq1 Qknc QBrp Q2ui Q1KO.
Import QNqr QeDS QLiw QTtp.Mq0 QwuX.Mq0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section RuleT.
Variable segs : list Segment.
Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.

Theorem vjA_getrandom_tagged : forall (V : config -> Prop) (T : TSet) (P : Prop) (Qs : machine_state -> Prop) buf len c0 msv,
at_g segs (GGetrandom buf len) msv ->
cinvA L (cfg_ms c0) (cfg_model c0) ->
(P -> exists bs, Z.of_nat (length bs) = len /\ Qs (nret msv (mkEffect (len_word bs) [(Z_to_bv 64 buf, bs)] []))) ->
(forall bs c1, Z.of_nat (length bs) = len ->
drift L (cfg_model c0) (cfg_model c1) ->
cinvA L (cfg_ms c1) (cfg_model c1) -> m_halted (cfg_model c1) = None ->
VJ L (slbwP segs V T (Qs (nret msv (mkEffect (len_word bs) [(Z_to_bv 64 buf, bs)] []))))
c1 (nret msv (mkEffect (len_word bs) [(Z_to_bv 64 buf, bs)] []))) ->
VJ L (slbwP segs V T P) c0 msv.
Proof.
intros V T P Qs buf len c0 msv Hat HC Hgood HK.
apply (vj_silent_tagged gnode segs L (at_g segs) (gstep_raw L) (fun _ _ _ _ => False) (fun _ _ => True) (xinvA L) (fun _ => false)
(fun _ r r' => r = r') (jsome L) (jsome_stable L) (gnode_sound segs L Hsegs) (GGetrandom buf len) V T P Qs c0 msv Hat HC
eq_refl I).
- intros mo1 code mo' _ [].
- intros rsp mo' evs (mo1 & _ & mo2 & (-> & _) & _). reflexivity.
- intros rsp rsp2 <- HQ. exact HQ.
- intros HP. destruct (Hgood HP) as (bs & Hbs & HQ). exists (mkEffect (len_word bs) [(Z_to_bv 64 buf, bs)] []). split; [exact HQ|].
intros mo1 _. exists mo1. exists mo1. split; [| apply drift_refl]. split; [reflexivity|]. split; [reflexivity|]. exists bs. split; [exact Hbs| reflexivity].
- intros rsp c1 (mo1 & Hd1 & mo2 & (_ & -> & bs & Hbs & ->) & Hd2) HC1 Hh1.
apply (HK bs c1 Hbs); [exact (drift_trans L _ _ _ Hd1 Hd2)| exact HC1| exact Hh1].
Qed.

End RuleT.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QQIi QdTb QHWH Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB Qsn5 Qknc QBrp Q2ui Q1KO.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import QNqr QNqr.Mq0 QeDS.Mq1 QTtp.
Import QLiw.Mq3.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Section Closed.
Context {St : Type}.
Local Notation M := (Qpj5.Mq1.M St).

Definition wev (fd : Z) (bs : list Z) : list event := map (WriteEv (Z_to_bv 64 fd)) (to_bytes bs).

Lemma wev_app : forall fd a b, wev fd (a ++ b) = wev fd a ++ wev fd b.
Proof. intros. unfold wev, to_bytes. rewrite !map_app. reflexivity. Qed.

Lemma t_emit_app : forall e1 e2 (T : TSet), t_eq (t_emit e1 (t_emit e2 T)) (t_emit (e1 ++ e2) T).
Proof.
intros e1 e2 T tr. unfold t_emit. split.
- intros [Hp|(tr' & -> & [Hp|(tr'' & -> & HT)])].
+ left. apply is_prefix_app_r. exact Hp.
+ left. apply is_prefix_app_l. exact Hp.
+ right. exists tr''. split; [rewrite app_assoc; reflexivity| exact HT].
- intros [Hp|(tr'' & -> & HT)].
+ destruct (is_prefix_app_split e1 e2 tr Hp) as [H1|(b' & -> & H2)]; [left; exact H1|].
right. exists b'. split; [reflexivity|]. left. exact H2.
+ right. exists (e2 ++ tr''). split; [rewrite app_assoc; reflexivity|]. right. exists tr''. split; [reflexivity| exact HT].
Qed.

Lemma to_bytes_concat : forall iovs, concat (map to_bytes iovs) = to_bytes (concat iovs).
Proof. intros iovs. unfold to_bytes. rewrite concat_map. reflexivity. Qed.

Lemma concat_wv_advance : forall iovs cnt, (length iovs <= 2)%nat -> 0 <= cnt <= zlength (concat iovs) ->
concat (wv_advance iovs cnt) = skipn (Z.to_nat cnt) (concat iovs) /\ (length (wv_advance iovs cnt) <= 2)%nat.
Proof.
intros iovs cnt Hl Hc. unfold zlength in *. destruct iovs as [|v0 rest]; cbn [wv_advance].
- cbn in *. rewrite skipn_nil. split; [reflexivity| lia].
- destruct (zlength v0 <? cnt) eqn:E; unfold zlength in E.
+ apply Z.ltb_lt in E. destruct rest as [|v1 rest'].
* cbn in Hc. rewrite app_nil_r in Hc. lia.
* destruct rest' as [|v2 r3]; [|cbn in Hl; lia].
cbn [concat] in *. rewrite !app_nil_r in *. rewrite length_app in Hc. split; [|cbn; lia].
rewrite skipn_app. rewrite (skipn_all2 (n := Z.to_nat cnt) v0) by lia. cbn [app]. f_equal. unfold zlength. lia.
+ apply Z.ltb_ge in E. cbn [concat]. split; [|cbn in *; lia].
rewrite skipn_app. replace (Z.to_nat cnt - length v0)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma dec_writev_eff0 : forall rem k, 0 <= k < 2^64 ->
dec_writev rem (eff0 (Z_to_bv 64 k)) = if (((rem =? 0) && (k =? 0)) || ((1 <=? k) && (k <=? rem)))%bool then Some k else None.
Proof. intros rem k Hk. unfold dec_writev, eff0. cbn. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma wset_wv_loop : forall fd (Tk : unit * St -> TSet) (st : St) (fuel : nat) (iovs : list (list Z)) (rem : Z),
(length iovs <= 2)%nat -> rem = zlength (concat iovs) -> rem < 2^64 -> (Z.to_nat rem < fuel)%nat ->
t_eq (wset (mloop fuel (wv_body fd) (iovs, rem) st) (epostT Tk)) (t_emit (wev fd (concat iovs)) (Tk (tt, st))).
Proof.
intros fd Tk st fuel. induction fuel as [|f IH]; intros iovs rem Hl Hrem H64 Hf; [lia|].
cbn [mloop]. unfold mbind at 1.
eapply t_eq_trans; [apply wset_ebind|].
unfold wv_body at 1. cbn [fst snd]. unfold mbind at 1.
eapply t_eq_trans; [apply wset_ebind|].
unfold msys, enode. cbn [wset].
assert (Hlen : Z.of_nat (length (concat (map to_bytes iovs))) = rem).
{ rewrite to_bytes_concat. unfold to_bytes. rewrite length_map. exact (eq_sym Hrem). }
assert (Hrem0 : 0 <= rem) by (rewrite Hrem; unfold zlength; lia).

assert (STEP : forall k, 1 <= k <= rem ->
t_eq (t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) (concat (map to_bytes iovs))))
(wset match match dec_writev rem (eff0 (Z_to_bv 64 k)) with Some a => Some (a, st) | None => None end with
| Some a => Ret (Ok a) | None => Ret Unr end
(epostT (fun a : Z * St =>
wset ((if fst a =? rem then mret (inr tt) else mret (inl (wv_advance iovs (fst a), rem - fst a))) (snd a))
(epostT (fun a0 : (list (list Z) * Z + unit) * St =>
wset (match fst a0 with inl x' => mloop f (wv_body fd) x' | inr r => mret r end (snd a0)) (epostT Tk)))))))
(t_emit (wev fd (concat iovs)) (Tk (tt, st)))).
{ intros k Hk. rewrite dec_writev_eff0 by lia.
replace (((rem =? 0) && (k =? 0)) || ((1 <=? k) && (k <=? rem)))%bool with true
by (symmetry; apply orb_true_iff; right; apply andb_true_iff; split; [apply Z.leb_le | apply Z.leb_le]; lia).
cbn [wset epostT fst snd].
destruct (k =? rem) eqn:Ek.
- apply Z.eqb_eq in Ek. subst k. cbn [mret wset epostT fst snd].
rewrite firstn_all2 by lia. rewrite to_bytes_concat. apply t_eq_refl.
- apply Z.eqb_neq in Ek. cbn [mret wset epostT fst snd].
destruct (concat_wv_advance iovs k Hl ltac:(lia)) as [Ecat Hl'].
eapply t_eq_trans; [apply t_emit_ext; apply (IH (wv_advance iovs k) (rem - k) Hl')|].
+ rewrite Ecat. unfold zlength in *. rewrite length_skipn. lia.
+ lia.
+ lia.
+ rewrite Ecat. eapply t_eq_trans; [apply t_emit_app|].
rewrite to_bytes_concat.
replace (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) (to_bytes (concat iovs))) ++ wev fd (skipn (Z.to_nat k) (concat iovs)))
with (wev fd (concat iovs)); [apply t_eq_refl|].
unfold wev, to_bytes. rewrite <- (firstn_skipn (Z.to_nat k) (concat iovs)) at 1.
rewrite !map_app. rewrite firstn_map. reflexivity. }
intros tr. split.
- intros [->|(rsp & evs & Hn & He)]; [apply t_emit_has_nil|].
cbn [nio] in Hn. destruct Hn as [(Hall & -> & ->)|(k & Hk & -> & ->)].
+ assert (R0 : rem = 0) by (rewrite <- Hlen, Hall; reflexivity).
rewrite dec_writev_eff0 in He by lia. clear Hrem Hlen STEP. subst rem. cbn in He.
rewrite to_bytes_concat in Hall. unfold wev. rewrite Hall. exact He.
+ apply (proj1 (STEP k ltac:(lia) tr)). exact He.
- intros He. destruct (Z.eq_dec rem 0) as [E0|N0].
+ right. exists (eff0 (Z_to_bv 64 0)), [].
assert (Hall : concat (map to_bytes iovs) = []) by (apply length_zero_iff_nil; lia).
split; [cbn [nio]; left; auto|].
rewrite dec_writev_eff0 by lia. clear Hrem Hlen STEP. subst rem. cbn.
rewrite to_bytes_concat in Hall. unfold wev in He. rewrite Hall in He. exact He.
+ right. exists (eff0 (Z_to_bv 64 rem)), (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat rem) (concat (map to_bytes iovs)))).
split; [cbn [nio]; right; exists rem; repeat split; lia|].
apply (proj2 (STEP rem ltac:(lia) tr)). exact He.
Qed.

Lemma wset_stdio_writev : forall fd buf s (Tk : unit * St -> TSet) (st : St),
zlength buf + zlength s < 2^64 ->
t_eq (wset (stdio_writev fd buf s st) (epostT Tk)) (t_emit (wev fd (buf ++ s)) (Tk (tt, st))).
Proof.
intros fd buf s Tk st H64. unfold stdio_writev.
assert (E : concat (match buf with [] => [s] | _ => [buf; s] end) = buf ++ s)
by (destruct buf; cbn [concat app]; rewrite ?app_nil_r; reflexivity).
rewrite <- E. apply wset_wv_loop.
- destruct buf; cbn; lia.
- rewrite E. unfold zlength. rewrite length_app. lia.
- exact H64.
- lia.
Qed.

Lemma wpath_bind : forall {A B} (t : itree node A) (f : A -> itree node B) evs r,
wpath (Qc6I.bind node t f) evs r -> exists r1 e1 e2, wpath t e1 r1 /\ wpath (f r1) e2 r /\ evs = e1 ++ e2.
Proof.
intros A B t f. induction t as [r0|n k IH]; intros evs r H; cbn [Qc6I.bind wpath] in *.
- exists r0, [], evs. split; [split; reflexivity|]. split; [exact H| reflexivity].
- destruct H as (rsp & e1 & e2 & Hn & Hp & ->). destruct (IH rsp e2 r Hp) as (r1 & e3 & e4 & H1 & H2 & ->).
exists r1, (e1 ++ e3), e4. split; [exists rsp, e1, e3; repeat split; assumption|]. split; [exact H2| rewrite app_assoc; reflexivity].
Qed.

Lemma wpath_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) evs r,
wpath (ebind t f) evs r ->
(exists e1, wpath t e1 Unr) \/ exists a e1 e2, wpath t e1 (Ok a) /\ wpath (f a) e2 r /\ evs = e1 ++ e2.
Proof.
intros A B t f evs r H. unfold ebind in H. destruct (wpath_bind _ _ _ _ H) as ([|a] & e1 & e2 & H1 & H2 & ->).
- left. exists e1. exact H1.
- right. exists a, e1, e2. auto.
Qed.

Lemma wpath_wv_loop : forall fd (st : St) (fuel : nat) (iovs : list (list Z)) (rem : Z) evs r,
(length iovs <= 2)%nat -> rem = zlength (concat iovs) -> rem < 2^64 -> (Z.to_nat rem < fuel)%nat ->
wpath (mloop fuel (wv_body fd) (iovs, rem) st) evs r -> r = Ok (tt, st) /\ evs = wev fd (concat iovs).
Proof.
intros fd st fuel. induction fuel as [|f IH]; intros iovs rem evs r Hl Hrem H64 Hf H; [lia|].
cbn [mloop] in H. unfold mbind at 1 in H.
assert (Hlen : Z.of_nat (length (concat (map to_bytes iovs))) = rem).
{ rewrite to_bytes_concat. unfold to_bytes. rewrite length_map. exact (eq_sym Hrem). }
assert (Hrem0 : 0 <= rem) by (rewrite Hrem; unfold zlength; lia).
destruct (wpath_ebind _ _ _ _ H) as [(e1 & H1)|(p & e1 & e2 & H1 & H2 & ->)]; clear H;
unfold wv_body at 1 in H1; cbn [fst snd] in H1; unfold mbind at 1 in H1;
(destruct (wpath_ebind _ _ _ _ H1) as [(e3 & H3)|(q & e3 & e4 & H3 & H4 & E)]; clear H1);
unfold msys, enode in H3; cbn [wpath] in H3; destruct H3 as (rsp & e5 & e6 & Hn & Hp & E3); cbn [nio] in Hn.
all: destruct Hn as [(Hall & -> & ->)|(k & Hk & -> & ->)];
[ assert (R0 : rem = 0) by (rewrite <- Hlen, Hall; reflexivity); rewrite dec_writev_eff0 in Hp by lia
| rewrite dec_writev_eff0 in Hp by lia;
replace (((rem =? 0) && (k =? 0)) || ((1 <=? k) && (k <=? rem)))%bool with true in Hp
by (symmetry; apply orb_true_iff; right; apply andb_true_iff; split; [apply Z.leb_le | apply Z.leb_le]; lia) ].
- exfalso. rewrite R0 in Hp. cbn in Hp. destruct Hp as [Hp _]. discriminate.
- exfalso. cbn [wpath] in Hp. destruct Hp as [Hp _]. discriminate.
- exfalso. rewrite R0 in Hp. cbn in Hp. destruct Hp as [Hp _]. injection Hp as <-.
cbn [fst snd] in H4. rewrite R0 in H4. cbn in H4. destruct H4 as [H4 _]. discriminate.
- exfalso. cbn [wpath] in Hp. destruct Hp as [Hp _]. injection Hp as <-. cbn [fst snd] in H4.
destruct (k =? rem); cbn in H4; destruct H4 as [H4 _]; discriminate.
- exfalso. rewrite R0 in Hp. cbn in Hp. destruct Hp as [Hp _]. discriminate.
- exfalso. cbn [wpath] in Hp. destruct Hp as [Hp _]. discriminate.
- rewrite R0 in Hp. cbn in Hp. destruct Hp as [Hp ->]. injection Hp as <-.
cbn [fst snd] in H4. rewrite R0 in H4. cbn in H4. destruct H4 as [H4 ->]. injection H4 as <-. cbn [fst snd mret wpath] in H2.
destruct H2 as [<- ->]. subst e1. split; [reflexivity|].
rewrite to_bytes_concat in Hall. unfold wev. rewrite Hall. subst e3. reflexivity.
- cbn [wpath] in Hp. destruct Hp as [Hp ->]. injection Hp as <-. cbn [fst snd] in H4.
destruct (k =? rem) eqn:Ek.
+ apply Z.eqb_eq in Ek. subst k. cbn in H4. destruct H4 as [H4 ->]. injection H4 as <-. cbn [fst snd mret wpath] in H2. destruct H2 as [<- ->].
split; [reflexivity|]. subst e1 e3. rewrite !app_nil_r. rewrite firstn_all2 by lia. rewrite to_bytes_concat. reflexivity.
+ apply Z.eqb_neq in Ek. cbn in H4. destruct H4 as [H4 ->]. injection H4 as <-. cbn [fst snd] in H2.
destruct (concat_wv_advance iovs k Hl ltac:(lia)) as [Ecat Hl'].
destruct (IH (wv_advance iovs k) (rem - k) e2 r Hl') as [-> ->]; [| lia | lia | exact H2 |].
* rewrite Ecat. unfold zlength in *. rewrite length_skipn. lia.
* split; [reflexivity|]. subst e1 e3. rewrite !app_nil_r. rewrite Ecat. rewrite to_bytes_concat.
unfold wev, to_bytes. rewrite <- (firstn_skipn (Z.to_nat k) (concat iovs)) at 3.
rewrite !map_app. rewrite firstn_map. reflexivity.
Qed.

Lemma wpath_stdio_writev : forall fd buf s (st : St) evs r,
zlength buf + zlength s < 2^64 ->
wpath (stdio_writev fd buf s st) evs r -> r = Ok (tt, st) /\ evs = wev fd (buf ++ s).
Proof.
intros fd buf s st evs r H64 H. unfold stdio_writev in H.
assert (E : concat (match buf with [] => [s] | _ => [buf; s] end) = buf ++ s)
by (destruct buf; cbn [concat app]; rewrite ?app_nil_r; reflexivity).
rewrite <- E. eapply wpath_wv_loop; [| | | | exact H].
- destruct buf; cbn; lia.
- rewrite E. unfold zlength. rewrite length_app. lia.
- exact H64.
- lia.
Qed.

Definition nonemptyK {A} (Tk : A -> TSet) : Prop := forall x, Tk x [].

Lemma wset_nil : forall {R} (t : itree node R) Tk, (forall r, Tk r []) -> wset t Tk [].
Proof. intros R [r|n k] Tk H; cbn [wset]; [apply H| left; reflexivity]. Qed.

Lemma epostT_nil : forall {A} (Tk : A -> TSet), nonemptyK Tk -> forall r, epostT Tk r [].
Proof. intros A Tk H [|a]; cbn [epostT]; [reflexivity| apply H]. Qed.

Definition mio {A} (c : M A) : Prop := forall s, tio (c s).

Definition mdet {A} (c : M A) (s : St) (out : list event) (a : A) (s' : St) : Prop :=
(forall Tk : A * St -> TSet, nonemptyK Tk -> t_eq (wset (c s) (epostT Tk)) (t_emit out (Tk (a, s')))) /\
(forall evs r, wpath (c s) evs r -> r = Ok (a, s') /\ evs = out).

Lemma mio_ret : forall {A} (a : A), mio (mret a).
Proof. intros A a s. exact I. Qed.
Lemma mio_unr : forall {A}, mio (@munr St A).
Proof. intros A s. exact I. Qed.
Lemma mio_get : mio (@mget St).
Proof. intros s. exact I. Qed.

Lemma mio_upd : forall f, mio (@mupd St f).
Proof. intros f s. exact I. Qed.
Lemma mio_sys : forall {A} n (dec : resp -> option A), io_wnode n -> mio (msys n dec).
Proof. intros A n dec Hn s. cbn. split; [exact Hn|]. intros r. destruct (dec r); exact I. Qed.
Lemma mio_bind : forall {A B} (m : M A) (f : A -> M B), mio m -> (forall a, mio (f a)) -> mio (mbind m f).
Proof. intros A B m f Hm Hf s. unfold mbind. apply tio_ebind; [apply Hm|]. intros [a s']. apply Hf. Qed.
Lemma mio_loop : forall {X R} fuel (body : X -> M (X + R)), (forall x, mio (body x)) -> forall x, mio (mloop fuel body x).
Proof.
intros X R fuel body Hb. induction fuel as [|fuel IH]; intros x; cbn [mloop]; [apply mio_unr|].
apply mio_bind; [apply Hb|]. intros [x'|r]; [apply IH| apply mio_ret].
Qed.
Lemma mio_if : forall {A} (b : bool) (c1 c2 : M A), mio c1 -> mio c2 -> mio (if b then c1 else c2).
Proof. intros A [|] c1 c2 H1 H2; assumption. Qed.

Lemma mdet_ret : forall {A} (a : A) s, mdet (mret a) s [] a s.
Proof.
intros A a s. split.
- intros Tk HT. cbn [mret wset epostT]. apply t_eq_sym, t_emit_nil_eq, HT.
- intros evs r [<- ->]. split; reflexivity.
Qed.
Lemma mdet_get : forall s, mdet mget s [] s s.
Proof. intros s. exact (mdet_ret s s). Qed.

Lemma mdet_upd : forall f s, mdet (mupd f) s [] tt (f s).
Proof.
intros f s. split.
- intros Tk HT. cbn [mupd wset epostT]. apply t_eq_sym, t_emit_nil_eq, HT.
- intros evs r [<- ->]. split; reflexivity.
Qed.

Lemma mdet_bind : forall {A B} (m : M A) (f : A -> M B) s o1 a s1 o2 b s2,
mdet m s o1 a s1 -> mdet (f a) s1 o2 b s2 -> mdet (mbind m f) s (o1 ++ o2) b s2.
Proof.
intros A B m f s o1 a s1 o2 b s2 [W1 P1] [W2 P2]. split.
- intros Tk HT. unfold mbind. eapply t_eq_trans; [apply wset_ebind|].
eapply t_eq_trans; [apply (W1 (fun p => wset (f (fst p) (snd p)) (epostT Tk)))|].
+ intros [a' s']. apply wset_nil. apply epostT_nil. exact HT.
+ cbn [fst snd]. eapply t_eq_trans; [apply t_emit_ext; apply (W2 Tk HT)|]. apply t_emit_app.
- intros evs r H. unfold mbind in H. destruct (wpath_ebind _ _ _ _ H) as [(e1 & H1)|([a' s'] & e1 & e2 & H1 & H2 & ->)].
+ destruct (P1 _ _ H1) as [E _]. discriminate.
+ destruct (P1 _ _ H1) as [E ->]. injection E as -> ->. cbn [fst snd] in H2.
destruct (P2 _ _ H2) as [-> ->]. split; reflexivity.
Qed.

Lemma mdet_out_eq : forall {A} (c : M A) s out out' a s', out = out' -> mdet c s out a s' -> mdet c s out' a s'.
Proof. intros; subst; assumption. Qed.

Lemma dec_ioctl_enotty : dec_ioctl (efferr ENOTTY) = Some (SErr ENOTTY).
Proof. vm_compute. reflexivity. Qed.

Lemma mdet_ioctl : forall fd req s, mdet (msys (NIoctl fd req) dec_ioctl) s [] (SErr ENOTTY) s.
Proof.
intros fd req s. split.
- intros Tk HT. unfold msys, enode. cbn [wset]. intros tr. split.
+ intros [->|(rsp & evs & (-> & ->) & He)]; [apply t_emit_has_nil|].
rewrite dec_ioctl_enotty in He. cbn [wset epostT] in He. exact He.
+ intros He. right. exists (efferr ENOTTY), []. split; [split; reflexivity|].
rewrite dec_ioctl_enotty. cbn [wset epostT]. exact He.
- intros evs r H. unfold msys, enode in H. cbn [wpath nio] in H.
destruct H as (rsp & e1 & e2 & (-> & ->) & Hp & ->). rewrite dec_ioctl_enotty in Hp. cbn [wpath] in Hp.
destruct Hp as [<- ->]. split; reflexivity.
Qed.

Lemma mdet_stdio_writev : forall fd buf s st, zlength buf + zlength s < 2^64 ->
mdet (stdio_writev fd buf s) st (wev fd (buf ++ s)) tt st.
Proof.
intros fd buf s st H. split.
- intros Tk _. apply wset_stdio_writev. exact H.
- intros evs r Hp. apply (wpath_stdio_writev fd buf s st evs r H Hp).
Qed.

Lemma mio_stdio_writev : forall fd buf s, mio (stdio_writev (St:=St) fd buf s).
Proof.
intros fd buf s. unfold stdio_writev. apply mio_loop. intros [iovs rem]. unfold wv_body. cbn [fst snd].
apply mio_bind; [apply mio_sys; exact I|]. intros cnt. apply mio_if; apply mio_ret.
Qed.

End Closed.

Section Rule.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Lemma impl_tio_A : forall {R} (t : itree node R) Q ms,
tio t -> impl segs (at_node segs) t Q ms -> impl segs (at_nodeA LV segs) t Q ms.
Proof.
induction t as [r|n k IH]; intros Q ms Ht H; cbn in *; [exact H|].
destruct Ht as [Hn Hk]. eapply evt_mono; [exact H|]. cbv beta. intros ms1 [Hat Hc].
split; [destruct n; cbn in Hn |- *; try destruct Hn; exact Hat|]. intros rsp. apply IH; [apply Hk| apply Hc].
Qed.

Theorem implM_vj_det : forall {St A} (c : Qpj5.Mq1.M St A) (s : St) (Q : A -> St -> machine_state -> Prop)
(out : list event) (a : A) (s' : St) (K : TSet) c0 msv,
Qpj5.Mq1.implM segs c s Q msv ->
cinvA LV (cfg_ms c0) (cfg_model c0) ->
tio (c s) -> mdet c s out a s' -> K [] ->
(forall c1 msv1,
evt segs (Q a s') msv1 -> drift LV (cfg_model c0) (cfg_model c1) ->
cinvA LV (cfg_ms c1) (cfg_model c1) ->
msview LV (cfg_model c1) (cfg_ms c1) = msv1 \/ (c1 = c0 /\ msv1 = msv) ->
VJ LV (JS segs K) c1 msv1) ->
VJ LV (JS segs (t_emit out K)) c0 msv.
Proof.
intros St A c s Q out a s' K c0 msv Himpl HC Ht [HW HP] HK0 HK.
unfold Qpj5.Mq1.implM in Himpl. apply (impl_tio_A _ _ _ Ht) in Himpl.
pose proof (impl_vj_io segs LV Hwx Hsegs Hsh Hbx Hbc (c s) (epostT (fun _ : A * St => K)) _ c0 msv Himpl HC Ht) as V.
intros ms mo Hrel. unfold JS. eapply srz_conseq; [apply V; [|exact Hrel]| apply (HW (fun _ => K)); intros _; exact HK0].
intros r evs c1 msv1 HQ Hw Hd HC1 Hc1. destruct (HP evs r Hw) as [-> ->]. cbn [epostT epost fst snd] in *.
exact (HK c1 msv1 HQ Hd HC1 Hc1).
Qed.

End Rule.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB.
Import Qsn5 QJFf.Mq1 Qknc QBrp Q2ui Q1KO.
Import QCiC.Mq1 Qpj5.Mq1 QCiC Q6sh QKTr QzgH.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Definition vmst (mo mo' : Model) : Prop :=
vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) /\ alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo).

Lemma vmst_refl : forall mo, vmst mo mo.
Proof. intros; split; reflexivity. Qed.
Lemma vmst_trans : forall a b c, vmst a b -> vmst b c -> vmst a c.
Proof. intros a b c [H1 H2] [H3 H4]. split; congruence. Qed.

Lemma vmst_init_sp : forall mo mo', vmst mo mo' -> vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo).
Proof. intros mo mo' [_ H]. unfold alloc_top in H. apply bv_eq. lia. Qed.

Definition mmnode (n : node) : Prop :=
match n with NMmap _ _ _ _ | NMunmap _ _ | NSetTid | NBrk _ | NMprotect _ _ _ | NExit _ => True | _ => False end.

Fixpoint tmm {R} (t : itree node R) : Prop :=
match t with Ret _ => True | Vis n k => mmnode n /\ forall rsp, tmm (k rsp) end.

Section VmStable.
Variable LV : lvp.

Lemma nstep_raw_vmst : forall n mo rsp mo' evs, mmnode n -> nstep_raw LV n mo rsp mo' evs -> vmst mo mo'.
Proof.
intros n mo rsp mo' evs Hn Hst. destruct n; try (destruct Hn; fail); try (destruct Hst; fail).
- cbn -[mmap_kind anon_place_ok grant_model rsp_grant rsp_remap reveal wunit rlenw rlen fixed_contained fixed_free commit_model remap_model m_vmmaps] in Hst.
destruct Hst as [_ Hst]. destruct (mmap_kind _ _ _).
+ destruct Hst as (a & ws & _ & _ & _ & -> & _). split; [apply reserved_grant| apply top_grant].
+ destruct (fixed_contained _ _ _); [destruct Hst as [-> _]; split; [apply reserved_commit| apply top_commit]|].
destruct (fixed_free _ _ _); [| destruct Hst]. destruct Hst as (ws & _ & _ & -> & _). split; [apply reserved_grant| apply top_grant].
+ destruct Hst as [-> _]. split; [apply reserved_remap| apply top_remap].
+ destruct Hst.
- cbn -[munmap_model rsp_munmap rlenw m_vmmaps] in Hst. destruct Hst as (_ & -> & _). split; [apply reserved_munmap| apply top_munmap].
Qed.

Lemma tpath_vmst : forall {R} (t : itree node R) mo tr r mo', tmm t -> tpath (nstepA LV (nstep_raw LV)) t mo tr r mo' -> vmst mo mo'.
Proof.
induction t as [r0|n k IH]; intros mo tr r mo' Ht Hp; cbn [tpath] in Hp.
- destruct Hp as (_ & -> & _). apply vmst_refl.
- destruct Ht as [Hn Hk]. destruct Hp as (rsp & mo1 & evs & tr' & (mo0 & Hd & Hst) & Hp & _).
eapply vmst_trans; [| exact (IH rsp mo1 tr' r mo' (Hk rsp) Hp)].
pose proof (drift_frame LV _ _ Hd) as (_ & _ & _ & _ & _ & Hvm & _).
destruct (nstep_raw_vmst n mo0 rsp mo1 evs Hn Hst) as [H1 H2]. split; rewrite <- Hvm; assumption.
Qed.

Lemma tmm_bind : forall {A B} (t : itree node A) (f : A -> itree node B), tmm t -> (forall a, tmm (f a)) -> tmm (Qc6I.bind node t f).
Proof. induction t as [r|n k IH]; intros f Ht Hf; cbn; [apply Hf|]. destruct Ht as [Hn Hk]. split; [exact Hn| intros rsp; apply IH; auto]. Qed.

Lemma tmm_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)), tmm t -> (forall a, tmm (f a)) -> tmm (ebind t f).
Proof. intros A B t f Ht Hf. unfold ebind. apply tmm_bind; [exact Ht|]. intros [|a]; [exact I| apply Hf]. Qed.

Lemma node_of_mm : forall e, mmnode (node_of e).
Proof. intros [len avoid|addr len|addr len|addr len]; exact I. Qed.

Lemma membedA_tmm : forall {R} (t : T R) (s : PStateA), tmm (membedA t s).
Proof.
induction t as [[r| |w]|e k IH]; intros s; cbn [membedA].
- exact I.
- cbn. split; [exact I| intros rsp; exact I].
- exact I.
- rewrite ev_stepA_eq. unfold Qpj5.Mq1.mbind. apply tmm_ebind.
+ unfold Qpj5.Mq1.msys, enode. cbn [tmm]. split; [apply node_of_mm|]. intros rsp. destruct (dec_of e rsp); exact I.
+ intros [a s']. cbn [fst snd]. apply IH.
Qed.

End VmStable.

Section Entries.
Variable L : ALay.

Lemma raw_malloc_A_tmm : forall n ps, tmm (raw_malloc_A L n ps).
Proof.
intros n ps. unfold raw_malloc_A, Qpj5.Mq1.mbind, Qpj5.Mq1.mget. cbn [ebind Qc6I.bind fst snd].
apply tmm_ebind; [apply membedA_tmm|]. intros [[r a'] s1]. cbn. exact I.
Qed.

Lemma raw_free_A_tmm : forall p ps, tmm (raw_free_A L p ps).
Proof.
intros p ps. unfold raw_free_A, Qpj5.Mq1.mbind, Qpj5.Mq1.mget. cbn [ebind Qc6I.bind fst snd].
apply tmm_ebind; [apply membedA_tmm|]. intros [a' s1]. cbn. exact I.
Qed.

End Entries.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgT.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte) (only parsing).

Definition ablock : Type := (aptr * Z * Z)%type.
Definition ablk_id (b : ablock) : aptr := fst (fst b).
Definition ablk_addr (b : ablock) : Z := snd (fst b).
Definition ablk_size (b : ablock) : Z := snd b.
Definition alb_remove (p : aptr) (LB : list ablock) : list ablock :=
filter (fun b => negb (aptr_eqb (ablk_id b) p)) LB.
Definition in_ablock (LB : list ablock) (a : Z) : Prop :=
exists b, In b LB /\ ablk_addr b <= a < ablk_addr b + ablk_size b.

Definition SH (a : Z) : Z := a / 8 + kShadowOffset.
Definition gran (n k : Z) : Z := if 8 * k + 8 <=? n then 0 else n - 8 * k.

Definition fframe : Type := (Z * Z)%type.
Definition ff_cls (f : fframe) : Z := fst f.
Definition ff_addr (f : fframe) : Z := snd f.
Definition ff_size (cls : Z) : Z := 64 * 2 ^ cls.
Definition in_fframe_body (FS : list fframe) (a : Z) : Prop :=
exists f, In f FS /\ ff_addr f <= a < ff_addr f + ff_size (ff_cls f) - 8.
Definition in_fframe_shadow (FS : list fframe) (a : Z) : Prop :=
exists f, In f FS /\ SH (ff_addr f) <= a < SH (ff_addr f) + ff_size (ff_cls f) / 8.

Record dlayout : Type := mkDL {
dl_malloc : Z; dl_free : Z; dl_calloc : Z;
dl_tp : Z; dl_gp : Z;
dl_img_lo : Z; dl_img_hi : Z;
dl_ro_hi : Z;
dl_errno : Z;
dl_client_data : Z -> Prop;
dl_depot_n : Z;
dl_malloc_stack : Z; dl_free_stack : Z; dl_calloc_stack : Z;
dl_rtc : list (Z * list byte)
}.

Record aentry : Type := mkAE {
ae_sp0 : Z; ae_stack_top : Z; ae_fs_base : Z; ae_L : ALay
}.
Definition ae_stack_bottom (RE : aentry) : Z := ae_stack_top RE - 0x800000.

Section WithLayout.
Variable band_lo : Z.
Variable segs : list Segment.
Variable atn : node -> machine_state -> Prop.
Variable DL : dlayout.

Local Notation implMA := (@implMG PStateA segs atn).

Definition appr (A n : Z) : Prop :=
((0 < A /\ A + n <= kLowEnd) \/ KHI <= A) /\ (A + n <= dl_img_lo DL \/ dl_img_hi DL <= A).

Definition agree_on (P : Z -> Prop) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> P a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

Definition aclient_addrA (LB : list ablock) (FS : list fframe) (SP : Z) (a : Z) : Prop :=
SP <= a
\/ dl_client_data DL a
\/ in_ablock LB a
\/ in_fframe_body FS a
\/ in_fframe_shadow FS a
\/ (SH band_lo <= a < SH (2^47))
\/ (SH (dl_img_lo DL) <= a < SH (dl_ro_hi DL)).

Definition aheap_presA (LB : list ablock) (FS : list fframe) (SP : Z) (m m' : mem) : Prop :=
agree_on (aclient_addrA LB FS SP) m m'.

Definition dkeepA (a : Z) : Prop :=
dl_client_data DL a \/ (SH band_lo <= a < SH (2^47)) \/ (SH (dl_img_lo DL) <= a < SH (dl_ro_hi DL)).
Lemma dkeepA_client : forall LB FS SP a, dkeepA a -> aclient_addrA LB FS SP a.
Proof. intros LB FS SP a [H|[H|H]]; unfold aclient_addrA; [right; left; exact H| do 5 right; left; exact H| do 6 right; exact H]. Qed.

Definition ablock_rangeA (A n : Z) : Prop :=
(appr A n /\ (n <= 32768 -> KHI <= A)) /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= band_lo /\ A + 4096 <= band_lo.

Definition aclient_write_okA (LB : list ablock) (FS : list fframe) (iv : Z * Z) : Prop :=
band_lo <= fst iv
\/ (forall a, fst iv <= a < snd iv -> dl_client_data DL a)
\/ (exists b, In b LB /\ ablk_addr b <= fst iv /\ snd iv <= ablk_addr b + ablk_size b)
\/ (exists f, In f FS /\ ff_addr f <= fst iv /\ snd iv <= ff_addr f + ff_size (ff_cls f) - 8)
\/ (exists f, In f FS /\ SH (ff_addr f) <= fst iv /\ snd iv <= SH (ff_addr f) + ff_size (ff_cls f) / 8)
\/ (SH band_lo <= fst iv /\ snd iv <= SH (2^47)).

Definition unw_readable (RE : aentry) (m : mem) (lo : Z) : Prop :=
forall x, lo <= x < ae_stack_top RE -> 0 <= x < 2^64 -> exists b, mrd segs m (wa x) = Some b.
Definition DEPOT_CAP : Z := 32000.
Definition depot_n (m : mem) (n : Z) : Prop := rw_cells segs m (dl_depot_n DL) [C4 (Z_to_bv 64 n)] /\ 1 <= n.
Definition depot_keep (m m' : mem) : Prop := forall n, depot_n m n -> depot_n m' n.

Lemma depot_keep_of_munch : forall W m m', munch W m m' -> wmono segs m m' ->
Forall (fun iv => snd iv <= dl_depot_n DL \/ dl_depot_n DL + 4 <= fst iv) W -> depot_keep m m'.
Proof.
intros W m m' MU WM HW n [RC P]. split; [| exact P]. eapply rw_cells_transport; [exact RC| exact MU| exact WM|].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - HW. induction HW as [|[lo hi] W' H1 HW IH]; cbn [disjoint_from fst snd] in *; [exact I|]. split; [lia| exact IH].
Qed.

Definition errno_keep (m m' : mem) : Prop := agree_on (fun a => dl_errno DL <= a < dl_errno DL + 4) m m'.

Definition blk_shadow (m : mem) (A n : Z) : Prop :=
0 <= A /\ A mod 8 = 0 /\ 0 <= n /\ SH A + (n + 7) / 8 <= KHI /\
forall k, 0 <= k -> 8 * k < n -> bytes_at segs m (SH A + k) [Z_to_bv 8 (gran n k)].

Section Stmts.
Variable RUN : PStateA -> list ablock -> list fframe -> aentry -> mem -> Prop.

Definition std_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (LB : list ablock) (FS : list fframe) (lo : Z) (m : mem) (s' : PStateA) (ms' : machine_state)
(K : word  -> mem -> Prop) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ aheap_presA LB FS (bv_unsigned sp) m m'
/\ ps_soa s' = ps_soa s /\ ps_xa s' = ps_xa s
/\ K a0 m'.

Definition amallocA_stmt (L : ALay) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (n lo dn : Z),
ae_L RE = L ->
RUN s LB FS RE m ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - dl_malloc_stack DL ->
mem_inv segs m ->
tp = Z_to_bv 64 (dl_tp DL) -> gp = Z_to_bv 64 (dl_gp DL) ->
unw_readable RE m (bv_unsigned sp) -> depot_n m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 n -> 0 <= n <= 2^26 ->
implMA (raw_malloc_A L n) s
(fun r s' ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ RUN s' LB FS RE m'
| Some p => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req p = n
/\ RUN s' ((p, A, n) :: LB) FS RE m'
/\ rw_cells segs m' A [CB (Z.to_nat n) junk]
/\ blk_shadow m' A n
/\ (forall mb k, p = ASec mb k -> A = mb + kSecUserOff)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (dl_malloc DL)) fc None m (seg_rom segs)).

Definition acallocA_stmt (L : ALay) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (cnt sz lo dn : Z),
ae_L RE = L ->
RUN s LB FS RE m ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - dl_calloc_stack DL ->
mem_inv segs m ->
tp = Z_to_bv 64 (dl_tp DL) -> gp = Z_to_bv 64 (dl_gp DL) ->
unw_readable RE m (bv_unsigned sp) -> depot_n m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 2^26 ->
implMA (if calloc_overflows cnt sz then mret None else raw_malloc_A L (cnt * sz)) s
(fun r s' ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ RUN s' LB FS RE m'
| Some p => exists A,
a0' = Z_to_bv 64 A /\ ablock_rangeA A (cnt * sz) /\ aptr_req p = cnt * sz
/\ RUN s' ((p, A, cnt * sz) :: LB) FS RE m'
/\ rw_cells segs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
/\ blk_shadow m' A (cnt * sz)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (dl_calloc DL)) fc None m (seg_rom segs)).

Definition afreeA_stmt (L : ALay) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A n lo dn : Z),
ae_L RE = L ->
RUN s LB FS RE m -> In (p, A, n) LB ->
qroom (ps_a s) p ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - dl_free_stack DL ->
mem_inv segs m ->
tp = Z_to_bv 64 (dl_tp DL) -> gp = Z_to_bv 64 (dl_gp DL) ->
unw_readable RE m (bv_unsigned sp) -> depot_n m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 A ->
implMA (raw_free_A L p) s
(fun _ s' ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m s' ms'
(fun _ m' => (exists dn', depot_n m' dn' /\ dn <= dn' <= dn + 1) /\ errno_keep m m' /\ RUN s' (alb_remove p LB) FS RE m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (dl_free DL)) fc None m (seg_rom segs)).

Definition afree_nullA_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (lo : Z),
RUN s LB FS RE m ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - dl_free_stack DL ->
mem_inv segs m ->
tp = Z_to_bv 64 (dl_tp DL) -> gp = Z_to_bv 64 (dl_gp DL) ->
unw_readable RE m (bv_unsigned sp) ->
a0 = Z_to_bv 64 0 ->
evt segs (fun ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s ms'
(fun _ m' => depot_keep m m' /\ errno_keep m m' /\ RUN s LB FS RE m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (dl_free DL)) fc None m (seg_rom segs)).

Definition astrdupA_stmt (SD SD_stack : Z) (L : ALay) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (b : ablock) (src lo dn : Z) (str : list byte),
ae_L RE = L ->
RUN s LB FS RE m ->
In b LB -> ablk_addr b <= src -> src + Z.of_nat (length str) + 1 <= ablk_addr b + ablk_size b ->
bytes_at segs m src (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 <= 2^26 ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - SD_stack ->
mem_inv segs m ->
tp = Z_to_bv 64 (dl_tp DL) -> gp = Z_to_bv 64 (dl_gp DL) ->
unw_readable RE m (bv_unsigned sp) -> depot_n m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 src ->
implMA (raw_malloc_A L (Z.of_nat (length str) + 1)) s
(fun r s' ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ RUN s' LB FS RE m'
| Some p => exists A,
a0' = Z_to_bv 64 A /\ ablock_rangeA A (Z.of_nat (length str) + 1) /\ aptr_req p = Z.of_nat (length str) + 1
/\ RUN s' ((p, A, Z.of_nat (length str) + 1) :: LB) FS RE m'
/\ rw_cells segs m' A [CB (S (length str)) (str ++ [Z_to_bv 8 0])]
/\ blk_shadow m' A (Z.of_nat (length str) + 1)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SD) fc None m (seg_rom segs)).

Definition raw_realloc_A (L : ALay) (p : aptr) (n : Z) : Qpj5.Mq1.M PStateA (option aptr) :=
Qpj5.Mq1.mbind (raw_malloc_A L n) (fun r =>
match r with
| None => Qpj5.Mq1.mret None
| Some q => Qpj5.Mq1.mbind (raw_free_A L p) (fun _ => Qpj5.Mq1.mret (Some q))
end).

Definition areallocA_stmt (RL RL_stack : Z) (L : ALay) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A0 n0 n lo dn : Z) (old junk0 : list byte),
ae_L RE = L ->
RUN s LB FS RE m -> In (p, A0, n0) LB ->
qroom (ps_a s) p ->
rw_cells segs m A0 [CB (Z.to_nat n0) (old ++ junk0)] ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - RL_stack ->
mem_inv segs m ->
tp = Z_to_bv 64 (dl_tp DL) -> gp = Z_to_bv 64 (dl_gp DL) ->
unw_readable RE m (bv_unsigned sp) -> depot_n m dn -> dn + 2 <= DEPOT_CAP ->
a0 = Z_to_bv 64 A0 -> a1 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
implMA (raw_realloc_A L p n) s
(fun r s' ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n m' dn' /\ dn <= dn' <= dn + 2) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ RUN s' LB FS RE m'
| Some q => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req q = n
/\ RUN s' ((q, A, n) :: alb_remove p LB) FS RE m'
/\ rw_cells segs m' A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]
/\ blk_shadow m' A n
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RL) fc None m (seg_rom segs)).

End Stmts.

Record donor_core : Type := mkDC {
dc_run : PStateA -> list ablock -> list fframe -> aentry -> mem -> Prop;
dc_run_ext : forall s s' LB FS RE m, dc_run s LB FS RE m -> ps_a s' = ps_a s -> dc_run s' LB FS RE m;
dc_run_perm : forall s LB LB' FS FS' RE m, dc_run s LB FS RE m -> Permutation LB LB' -> Permutation FS FS' ->
dc_run s LB' FS' RE m;
dc_run_frame : forall s LB FS RE m m' W,
dc_run s LB FS RE m -> munch W m m' -> wmono segs m m' -> Forall (aclient_write_okA LB FS) W ->
dc_run s LB FS RE m';
dc_block_range : forall s LB FS RE m b, dc_run s LB FS RE m -> In b LB -> ablock_rangeA (ablk_addr b) (ablk_size b);
dc_block_small : forall s LB FS RE m b, dc_run s LB FS RE m -> In b LB -> ablk_size b <= 2^26;
dc_blocks_disjoint : forall s LB FS RE m b1 b2,
dc_run s LB FS RE m -> In b1 LB -> In b2 LB -> ablk_id b1 <> ablk_id b2 ->
ablk_addr b1 + Z.max (ablk_size b1) 1 <= ablk_addr b2 \/ ablk_addr b2 + Z.max (ablk_size b2) 1 <= ablk_addr b1;
dc_blocks_nodup : forall s LB FS RE m, dc_run s LB FS RE m -> List.NoDup (map ablk_id LB);
dc_block_shadow : forall s LB FS RE m p A n, dc_run s LB FS RE m -> In (p, A, n) LB -> blk_shadow m A n;
dc_errno : forall s LB FS RE m, dc_run s LB FS RE m -> exists v : word, rw_cells segs m (dl_errno DL) [C4 v];
dc_errno_frame : forall s LB FS RE m m' (v : word), dc_run s LB FS RE m ->
munch [(dl_errno DL, dl_errno DL + 4)] m m' -> wmono segs m m' -> rw_cells segs m' (dl_errno DL) [C4 v] -> dc_run s LB FS RE m';
dc_malloc : forall L, amallocA_stmt dc_run L;
dc_calloc : forall L, acallocA_stmt dc_run L;
dc_free : forall L, afreeA_stmt dc_run L;
dc_free_null : afree_nullA_stmt dc_run;

dc_rt_consts : forall s LB FS RE m, dc_run s LB FS RE m -> Forall (fun c => bytes_at segs m (fst c) (snd c)) (dl_rtc DL)
}.

Definition fframe_rangeA (RE : aentry) (cls f : Z) : Prop :=
ae_fs_base RE + 0x9000 <= f /\ f + ff_size cls <= ae_fs_base RE + 0xb00000 /\ f mod 64 = 0 /\ appr f (ff_size cls) /\ f + ff_size cls <= band_lo.
Definition ffs_remove (fa : Z) (FS : list fframe) : list fframe := filter (fun f => negb (ff_addr f =? fa)) FS.
Definition fframe_cap (cls : Z) : Z := 2 ^ (14 - cls).
Definition amemset_whereA (LB : list ablock) (FS : list fframe) (dst n : Z) : Prop :=
(exists p A n0, In (p, A, n0) LB /\ A <= dst /\ dst + n <= A + n0) \/ (exists c f, In (c, f) FS /\ f <= dst /\ dst + n <= f + ff_size c).

Definition astack_mallocA_stmt (RUN : PStateA -> list ablock -> list fframe -> aentry -> mem -> Prop) (cls entry stack_need : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (size lo : Z),
RUN s LB FS RE m ->
Z.of_nat (length (filter (fun f => ff_cls f =? cls) FS)) < fframe_cap cls ->
stk segs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - stack_need ->
mem_inv segs m ->
tp = Z_to_bv 64 (dl_tp DL) -> gp = Z_to_bv 64 (dl_gp DL) ->
a0 = Z_to_bv 64 size -> 0 < size <= ff_size cls -> size mod 8 = 0 ->
evt segs (fun ms' => std_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s ms'
(fun a0' m' => depot_keep m m' /\ exists f junk,
a0' = Z_to_bv 64 f /\ fframe_rangeA RE cls f
/\ RUN s LB ((cls, f) :: FS) RE m'
/\ rw_cells segs m' f [CB (Z.to_nat (ff_size cls - 8)) junk]
/\ rw_cells segs m' (SH f) [CB (Z.to_nat (ff_size cls / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (ff_size cls / 8)))]))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Record donor_fs (DCo : donor_core) (SM : Z -> Z) (SM_stack : Z) : Prop := mkDFS {
df_entry_facts : forall s LB FS RE m, dc_run DCo s LB FS RE m -> appr (ae_fs_base RE) 0xb09000 /\ ae_fs_base RE + 0xb09000 <= band_lo;
df_fframe_range : forall s LB FS RE m f, dc_run DCo s LB FS RE m -> In f FS -> fframe_rangeA RE (ff_cls f) (ff_addr f);
df_fframe_align : forall s LB FS RE m c0 f, dc_run DCo s LB FS RE m -> In (c0, f) FS -> c0 <= 6 -> f mod ff_size c0 = 0;
df_fframes_disjoint : forall s LB FS RE m f1 f2, dc_run DCo s LB FS RE m -> In f1 FS -> In f2 FS -> ff_addr f1 <> ff_addr f2 ->
ff_addr f1 + ff_size (ff_cls f1) <= ff_addr f2 \/ ff_addr f2 + ff_size (ff_cls f2) <= ff_addr f1;
df_fframe_block_disjoint : forall s LB FS RE m f b, dc_run DCo s LB FS RE m -> In f FS -> In b LB ->
ff_addr f + ff_size (ff_cls f) <= ablk_addr b \/ ablk_addr b + ablk_size b <= ff_addr f;
df_fs_block_disjoint : forall s LB FS RE m b, dc_run DCo s LB FS RE m -> In b LB ->
ablk_addr b + ablk_size b <= ae_fs_base RE \/ ae_fs_base RE + 0xb09000 <= ablk_addr b;
df_fframes_nodup : forall s LB FS RE m, dc_run DCo s LB FS RE m -> List.NoDup (map ff_addr FS);

df_fframe_release : forall c0 s LB FS RE m f (flag : word),
dc_run DCo s LB FS RE m -> In (c0, f) FS -> bytes_at segs m (f + ff_size c0 - 8) (le8 flag) ->
dc_run DCo s LB (ffs_remove f FS) RE (write_to_mem m flag [Z_to_bv 8 0])
/\ wview segs m flag <> None /\ bv_unsigned flag + 1 <= band_lo
/\ aheap_presA LB FS band_lo m (write_to_mem m flag [Z_to_bv 8 0]);
df_fframe_flag : forall c0 s LB FS RE m f, dc_run DCo s LB FS RE m -> In (c0, f) FS ->
exists flag : word, ro_cells segs m (f + ff_size c0 - 8) [C8 flag] /\ ae_fs_base RE + 0x1000 <= bv_unsigned flag < ae_fs_base RE + 0x9000;
df_stack_malloc : forall k, 0 <= k <= 2 \/ (k = 3 /\ SM 3 <> 0) -> astack_mallocA_stmt (dc_run DCo) k (SM k) SM_stack;

df_blk_slack : forall s LB FS RE m p A n, dc_run DCo s LB FS RE m -> In (p, A, n) LB ->
exists junk, bytes_at segs m (A + n) junk /\ Z.of_nat (length junk) = (16 - n mod 16) mod 16;
df_nbhd : forall s LB FS RE m p n, dc_run DCo s LB FS RE m -> amemset_whereA LB FS p n -> 0 < n ->
(exists w : word, rw_cells segs m (8 * (SH p / 8)) [C8 w]) /\ (exists w : word, rw_cells segs m (8 * (SH (p + n - 1) / 8)) [C8 w])
}.

Record donor_t2 (DCo : donor_core) (SD SD_stack RL RL_stack : Z) : Prop := mkDT2 {
dt_strdup : forall L, astrdupA_stmt (dc_run DCo) SD SD_stack L;
dt_realloc : forall L, areallocA_stmt (dc_run DCo) RL RL_stack L
}.

End WithLayout.
