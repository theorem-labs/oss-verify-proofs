(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi QdTb QHWH Q1lV Qcrs QUcd QCUT QwAs Qc6I QJFf Qsn5 Qknc QBrp Q2ui Q1KO QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QQIi QdTb QHWH Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf Qsn5 Qknc QBrp Q2ui Q1KO.
Import QNqr QNqr.Mq0.
Import ListNotations.
Open Scope Z_scope.

Theorem main_phase_cps : forall segs (LV : lvp) (T : TSet) (c : config),
cinvA LV (cfg_ms c) (cfg_model c) ->
m_halted (cfg_model c) = None ->
VJ LV (JS segs T) c (msview LV (cfg_model c) (cfg_ms c)) ->
srealizes segs c T.
Proof.
intros segs LV T [ms mo] HC Hh HV. cbn [cfg_ms cfg_model] in *.
exact (vj_enter LV (JS segs T) ms mo (proj1 (proj2 HC)) Hh HV).
Qed.
End Mq0.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS QGaR QwuX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QQIi QdTb QHWH Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I Qsn5 Qknc.
Import QNqr QeDS QGaR.
Import ListNotations.
Open Scope Z_scope.

Definition rsp_off (F : word -> bool) (rsp : resp) : Prop :=
forall v, restrict F (nret v rsp) = nret (restrict F v) rsp /\ (forall x, F x = true -> ms_mem (nret v rsp) x = ms_mem v x).

Section ImplCpsF.
Variable node : Type.
Variable segs : list Segment.
Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.
Variable at_node : node -> machine_state -> Prop.
Variable nstep_raw : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit_raw : node -> Model -> word -> Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Variable xinv : Model -> Prop.
Variable is_spin : node -> bool.
Variable rvar : node -> resp -> resp -> Prop.
Variable jinv : Model -> (word -> option byte) -> Prop.
Hypothesis jinv_stable : forall mo mo' m m',
vmeq mo mo' -> (forall a, hidden L mo a = true -> m' a = m a) -> jinv mo m -> jinv mo' m'.
Hypothesis NS : node_soundA node segs L at_node nstep_raw nexit_raw nsafe xinv is_spin rvar jinv.

Notation cinvA := (cinv L xinv jinv).
Notation nstA := (nstepA L nstep_raw).
Notation tpathA := (tpath nstA).

Variable J : config -> Prop.
Hypothesis J_nclosed : forall c (I : Type) (nx : I -> config) (i0 : I),
node_ok segs c I (fun _ => []) nx -> (forall i, J (nx i)) -> J c.

Variable F : word -> bool.
Hypothesis F_off : H_off_segments segs F.

Fixpoint tcpsF {R} (t : itree node R) (mo : Model) : Prop :=
match t with
| Ret _ => True
| Vis n k => is_spin n = false /\ nsafe n mo
/\ (forall ms, at_node n (restrict F ms) -> at_node n ms)
/\ (forall mo1 code mo', drift L mo mo1 -> ~ nexit_raw n mo1 code mo')
/\ (forall rsp mo' evs, nstA n mo rsp mo' evs -> evs = [] /\ rsp_off F rsp /\ tcpsF (k rsp) mo')
end.

Theorem impl_vj_F : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) c0 msv,
impl segs at_node t Q (restrict F msv) ->
cinvA (cfg_ms c0) (cfg_model c0) ->
tcpsF t (cfg_model c0) ->
(forall r c1 msv1,
evt segs (Q r) (restrict F msv1) ->
tpathA t (cfg_model c0) [] r (cfg_model c1) ->
cinvA (cfg_ms c1) (cfg_model c1) -> m_halted (cfg_model c1) = None ->
msview L (cfg_model c1) (cfg_ms c1) = msv1 \/ (c1 = c0 /\ msv1 = msv) ->
(forall x, F x = true -> ms_mem msv1 x = ms_mem msv x) ->
VJ L J c1 msv1) ->
VJ L J c0 msv.
Proof.
intros R t. induction t as [r|n k IH]; intros Q c0 msv Himpl HC Hcps HK.
- cbn [impl] in Himpl. intros ms mo Hrel.
assert (Hh0 : m_halted (cfg_model c0) = None).
{ destruct Hrel as (_ & Hd & _ & Hh & _).
pose proof (drift_frame L _ _ Hd) as (_ & _ & Hh1 & _). rewrite Hh1 in Hh. exact Hh. }
assert (Hp : tpathA (Ret r) (cfg_model c0) [] r (cfg_model c0)) by (cbn; auto).
exact (HK r c0 msv Himpl Hp HC Hh0 (or_intror (conj eq_refl eq_refl)) (fun _ _ => eq_refl) ms mo Hrel).
- cbn [impl] in Himpl.
apply (evt_restrict_lift segs F F_off Hwx) in Himpl. destruct Himpl as (msr1 & Hms & (Hat0 & Hk) & Hhs).
cbn [tcpsF] in Hcps. destruct Hcps as (Hsp & Hns & Hmono & Hnx & Hstep).
pose proof (Hmono _ Hat0) as Hat.
intros ms mo (Hv & Hd & HI & Hh & Hhid). destruct c0 as [ms0 mo0]. cbn [cfg_ms cfg_model] in *.
apply (msteps_view L segs Hwx Hsegs J (J_silent_closed segs L J J_nclosed) msv msr1 Hms mo ms (eq_sym Hv) HI Hh).
intros ms1 mo1 Hv1 Hd1 HI1 Hh1 Hhid1.
assert (Hd01 : drift L mo0 mo1) by exact (drift_trans L _ _ _ Hd Hd1).
assert (Hhid01 : forall a, hidden L mo0 a = true -> ms_mem ms1 a = ms_mem ms0 a).
{ intros a Ha. rewrite Hhid1 by (rewrite (hidden_ext L _ _ (drift_vmeq L _ _ Hd)); exact Ha). apply Hhid. exact Ha. }
assert (HC1 : cinvA ms1 mo1).
{ eapply (cinv_drift node segs L at_node nstep_raw nexit_raw nsafe xinv is_spin rvar jinv jinv_stable NS); [exact Hd01| exact Hhid01| exact HC]. }
assert (Hat1 : at_node n (msview L mo1 ms1)) by (rewrite Hv1; exact Hat).
assert (Hns1 : nsafe n mo1) by (eapply (nsA_safe_drift _ _ _ _ _ _ _ _ _ _ _ NS); eassumption).
set (c1 := mkCfg ms1 mo1).
set (Ix := { x : list event * config | sstep_cfg segs (alloc_only_cfg false) c1 (fst x) (SNext (snd x)) }).
assert (Hexpl : forall e st, sstep_cfg segs (alloc_only_cfg false) c1 e st ->
exists rsp ms' mo', st = SNext (mkCfg ms' mo') /\ e = [] /\ msview L mo' ms' = nret (msview L mo1 ms1) rsp /\
nstep_raw n mo1 rsp mo' e /\ cinvA ms' mo' /\ m_halted mo' = None).
{ intros e st Hst.
destruct (nsA_complete _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 e st Hsp Hat1 Hh1 HC1 Hns1 Hst)
as [(rsp & ms' & mo' & -> & Hv' & Hr & HC' & Hh')|(code & mo' & _ & Hx & _)].
- exists rsp, ms', mo'. destruct (Hstep rsp mo' e (ex_intro _ mo1 (conj Hd01 Hr))) as [-> _].
split; [reflexivity|]. split; [reflexivity|]. split; [exact Hv'|]. split; [exact Hr|]. split; [exact HC'| exact Hh'].
- exfalso. exact (Hnx mo1 code mo' Hd01 Hx). }
assert (Hnode : node_ok segs c1 Ix (fun _ => []) (fun i => snd (proj1_sig i))).
{ split.
- intros [[e c'] Hst]. cbn [fst snd proj1_sig] in *. destruct (Hexpl e _ Hst) as (_ & _ & _ & _ & -> & _). exact Hst.
- intros e st Hst. destruct (Hexpl e st Hst) as (rsp & ms' & mo' & -> & -> & _).
exists (exist _ ([], mkCfg ms' mo') Hst). split; reflexivity. }
assert (Hi0 : exists i : Ix, True).
{ destruct (nsA_progress _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 Hsp Hat1 Hh1 HC1 Hns1) as [(rsp & mo' & evs & Hr)|(code & mo' & Hx)].
- destruct (nsA_sound _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 rsp mo' evs Hsp Hat1 Hh1 HC1 Hns1 Hr) as (ms' & mo2 & rsp2 & Hst & _).
exists (exist _ (evs, mkCfg ms' mo2) Hst). exact I.
- exfalso. exact (Hnx mo1 code mo' Hd01 Hx). }
destruct Hi0 as [i0 _].
apply (J_nclosed c1 Ix (fun i => snd (proj1_sig i)) i0 Hnode).
intros [[e c'] Hst]. cbn [fst snd proj1_sig].
destruct (Hexpl e _ Hst) as (rsp & ms' & mo' & E & -> & Hv' & Hr & HC' & Hh'). injection E as ->.
assert (HstA : nstA n mo0 rsp mo' []) by (exists mo1; split; assumption).
destruct (Hstep rsp mo' [] HstA) as (_ & Hoff & Hcps').
destruct (Hoff msr1) as [Hcomm Hkeep].
apply (vj_enter L J ms' mo' (proj1 (proj2 HC')) Hh').
apply (IH rsp Q (mkCfg ms' mo') (msview L mo' ms')).
+ rewrite Hv', Hv1, Hcomm. apply Hk.
+ exact HC'.
+ exact Hcps'.
+ intros r c2 msv2 HQ Hp HC2 Hh2 Hc2 Hf2. apply (HK r c2 msv2 HQ); auto.
* cbn [tpath]. exists rsp, mo', [], []. split; [exact HstA|]. split; [exact Hp| reflexivity].
* destruct Hc2 as [Hc2| [-> ->]]; [left; exact Hc2|]. left. reflexivity.
* intros x Hx. rewrite (Hf2 x Hx), Hv', Hv1, (Hkeep x Hx). exact (Hhs x Hx).
Qed.

End ImplCpsF.

Import QJFf QBrp Q2ui.
Import QwuX.

Lemma write_to_mem_at : forall bs m1 m2 a x, m1 x = m2 x -> write_to_mem m1 a bs x = write_to_mem m2 a bs x.
Proof.
induction bs as [|b bs IH]; intros m1 m2 a x E; [exact E|]. cbn [write_to_mem]. apply IH.
destruct (bv_eqb x a); [reflexivity| exact E].
Qed.

Lemma apply_writes_at : forall ws m1 m2 x, m1 x = m2 x -> apply_writes m1 ws x = apply_writes m2 ws x.
Proof.
induction ws as [|[a bs] ws IH]; intros m1 m2 x E; [exact E|]. cbn [apply_writes]. apply IH. apply write_to_mem_at. exact E.
Qed.

Lemma apply_zeros_at : forall zs m1 m2 x, m1 x = m2 x -> apply_zeros m1 zs x = apply_zeros m2 zs x.
Proof. intros [|z zs] m1 m2 x E; [exact E|]. cbn [apply_zeros]. destruct (zeros_cover (z :: zs) x); [reflexivity| exact E]. Qed.

Lemma apply_unmaps_at : forall us m1 m2 x, m1 x = m2 x -> apply_unmaps m1 us x = apply_unmaps m2 us x.
Proof. intros [|u us] m1 m2 x E; [exact E|]. cbn [apply_unmaps]. destruct (zeros_cover (u :: us) x); [reflexivity| exact E]. Qed.

Lemma apply_zeros_off : forall zs m x, zeros_cover zs x = false -> apply_zeros m zs x = m x.
Proof. intros [|z zs] m x E; [reflexivity|]. cbn [apply_zeros]. rewrite E. reflexivity. Qed.

Lemma apply_unmaps_off : forall us m x, zeros_cover us x = false -> apply_unmaps m us x = m x.
Proof. intros [|u us] m x E; [reflexivity|]. cbn [apply_unmaps]. rewrite E. reflexivity. Qed.

Theorem rsp_off_eff : forall F r ws zs us,
wunit ws = true ->
(forall x, F x = true -> ~ In x (map fst ws)) ->
(forall x, F x = true -> zeros_cover zs x = false) ->
(forall x, F x = true -> zeros_cover us x = false) ->
rsp_off F (mkEffectU r ws zs us [] []).
Proof.
intros F r ws zs us Hw Hws Hzs Hus v. split.
- apply restrict_nret_mem. apply functional_extensionality. intros x. unfold mrestrict at 1.
destruct (F x) eqn:Fx.
+ rewrite (apply_writes_units_notIn ws _ x Hw (Hws x Fx)), (apply_zeros_off zs _ x (Hzs x Fx)), (apply_unmaps_off us _ x (Hus x Fx)).
unfold mrestrict. rewrite Fx. reflexivity.
+ apply apply_writes_at, apply_zeros_at, apply_unmaps_at. unfold mrestrict. rewrite Fx. reflexivity.
- intros x Fx. unfold nret, advance_past_svc, apply_effect.
cbn [ms_mem eff_writes eff_zeros eff_unmaps eff_copies eff_copyins apply_copies].
rewrite (apply_writes_units_notIn ws _ x Hw (Hws x Fx)), (apply_zeros_off zs _ x (Hzs x Fx)), (apply_unmaps_off us _ x (Hus x Fx)).
reflexivity.
Qed.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QQIi QdTb QHWH Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf Qsn5 Qknc QBrp Q2ui Q1KO.
Import QNqr QNqr.Mq0 QeDS.Mq1.
Import ListNotations.
Open Scope Z_scope.

Section NodeRulesA.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Local Notation NS := (nodesA_sound segs LV Hsegs Hsh Hbx Hbc).
Local Notation vis := (vj_vis_k node segs LV (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) (xinvA LV) is_spinA rvarA (jsome LV)
(jsome_stable LV) NS).

Lemma with_halted_fs : forall c mo, m_fs (with_halted c mo) = m_fs mo.
Proof. intros c mo. destruct mo; reflexivity. Qed.

Theorem vjA_exit : forall (code : Z) c0 msv,
at_nodeA LV segs (NExit code) msv ->
cinvA LV (cfg_ms c0) (cfg_model c0) ->
VJ LV (JS segs (t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs (cfg_model c0)))) c0 msv.
Proof.
intros code c0 msv Hat HC.
apply (vis (NExit code) (fun _ _ _ => t_nil) _ c0 msv eq_refl Hat HC I).
- intros; apply t_eq_refl.
- intros mo1 rsp evs c1 _ Hr. destruct Hr.
- intros mo1 Hd tr. pose proof (drift_frame LV _ _ Hd) as (_ & Hfs & _).
unfold t_exit, t_emit, t_nil. cbn [nstep_raw nexit_raw nexit]. split.
+ intros [Hp|(tr' & -> & ->)].
* right; right. eexists _, _. split; [split; reflexivity|]. rewrite with_halted_fs, Hfs. exact Hp.
* right; right. eexists _, _. split; [split; reflexivity|]. rewrite with_halted_fs, Hfs, app_nil_r. apply is_prefix_refl.
+ intros [->|[(rsp & mo' & evs & [] & _)|(c & mo' & (-> & ->) & Hp)]].
* left. apply is_prefix_nil.
* left. rewrite with_halted_fs, Hfs in Hp. exact Hp.
Qed.

Lemma writev_raw_inv : forall fd bufs mo1 rsp mo' evs,
(1 <= length (concat bufs))%nat ->
nstep_raw LV (NWritev fd bufs) mo1 rsp mo' evs ->
drift LV mo1 mo' /\
exists k : nat, (1 <= k)%nat /\ (k <= length (concat bufs))%nat /\ rsp = eff0 (Z_to_bv 64 (Z.of_nat k)) /\
evs = map (WriteEv (Z_to_bv 64 fd)) (firstn k (concat bufs)) /\ length evs = k.
Proof.
intros fd bufs mo1 rsp mo' evs Hnb (mo2 & (-> & Hr) & Hd). split; [exact Hd|].
cbn zeta in Hr. destruct Hr as [(Hnil & _)|(k & Hk & -> & ->)]; [rewrite Hnil in Hnb; cbn in Hnb; lia|].
exists (Z.to_nat k). rewrite Z2Nat.id by lia. repeat split; try lia.
rewrite length_map, length_firstn. lia.
Qed.

Theorem vjA_writev : forall (fd : Z) (bufs : list (list byte)) (Tn : nat -> TSet) c0 msv,
at_nodeA LV segs (NWritev fd bufs) msv ->
cinvA LV (cfg_ms c0) (cfg_model c0) ->
(1 <= length (concat bufs))%nat ->
(forall (k : nat) c1, (1 <= k)%nat -> (k <= length (concat bufs))%nat ->
drift LV (cfg_model c0) (cfg_model c1) ->
cinvA LV (cfg_ms c1) (cfg_model c1) -> m_halted (cfg_model c1) = None ->
msview LV (cfg_model c1) (cfg_ms c1) = nret msv (eff0 (Z_to_bv 64 (Z.of_nat k))) ->
VJ LV (JS segs (Tn k)) c1 (nret msv (eff0 (Z_to_bv 64 (Z.of_nat k))))) ->
VJ LV (JS segs (t_alt (fun i : wr_index (concat bufs) =>
t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (concat bufs))) (Tn (proj1_sig i))))) c0 msv.
Proof.
intros fd bufs Tn c0 msv Hat HC Hnb HK.
apply (vis (NWritev fd bufs) (fun _ _ evs => Tn (length evs)) _ c0 msv eq_refl Hat HC I).
- intros; apply t_eq_refl.
- intros mo1 rsp evs c1 Hd Hr HC1 Hh1 Hv1.
destruct (writev_raw_inv fd bufs mo1 rsp _ evs Hnb Hr) as (Hd1 & k & Hk1 & Hk2 & -> & _ & ->).
apply (HK k c1 Hk1 Hk2 (drift_trans LV _ _ _ Hd Hd1) HC1 Hh1 Hv1).
- intros mo1 Hd tr. unfold t_alt. split.
+ intros [[k [Hk1 Hk2]] Hem]. cbn [proj1_sig] in Hem. right; left.
exists (eff0 (Z_to_bv 64 (Z.of_nat k))), mo1, (map (WriteEv (Z_to_bv 64 fd)) (firstn k (concat bufs))). split.
* exists mo1. split; [|apply drift_refl]. split; [reflexivity|]. cbn zeta. right. exists (Z.of_nat k).
rewrite Nat2Z.id. repeat split; lia.
* rewrite length_map, length_firstn, Nat.min_l by lia. exact Hem.
+ intros [->|[(rsp & mo' & evs & Hr & Hem)|(c & mo' & [] & _)]].
* exists (exist _ 1%nat (conj (le_n 1) Hnb)). left. apply is_prefix_nil.
* destruct (writev_raw_inv fd bufs mo1 rsp mo' evs Hnb Hr) as (_ & k & Hk1 & Hk2 & _ & -> & Hlen).
exists (exist _ k (conj Hk1 Hk2)). cbn [proj1_sig]. rewrite Hlen in Hem. exact Hem.
Qed.

End NodeRulesA.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB QTtp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QQIi QdTb QHWH Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB Qsn5 Qknc QBrp Q2ui Q1KO.
Import QNqr QNqr.Mq0 QeDS.Mq1 QTtp.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Definition io_wnode (n : node) : Prop := match n with NWritev _ _ | NIoctl _ _ => True | _ => False end.

Definition nio (n : node) (rsp : resp) (evs : list event) : Prop :=
match n with
| NWritev fd bufs =>
let all := concat bufs in
(all = [] /\ rsp = eff0 (Z_to_bv 64 0) /\ evs = [])
\/ (exists k : Z, 1 <= k <= Z.of_nat (length all) /\ rsp = eff0 (Z_to_bv 64 k) /\
evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) all))
| NIoctl _ _ => evs = [] /\ rsp = efferr ENOTTY
| _ => False
end.

Fixpoint tio {R} (t : itree node R) : Prop :=
match t with
| Ret _ => True
| Vis n k => io_wnode n /\ forall r, tio (k r)
end.

Fixpoint wset {R} (t : itree node R) (Tk : R -> TSet) : TSet :=
match t with
| Ret r => Tk r
| Vis n k => fun tr => tr = [] \/ exists rsp evs, nio n rsp evs /\ t_emit evs (wset (k rsp) Tk) tr
end.

Fixpoint wpath {R} (t : itree node R) (evs : list event) (r : R) : Prop :=
match t with
| Ret r0 => r0 = r /\ evs = []
| Vis n k => exists rsp e1 e2, nio n rsp e1 /\ wpath (k rsp) e2 r /\ evs = e1 ++ e2
end.

Lemma t_emit_ext : forall evs (T T' : TSet), t_eq T T' -> t_eq (t_emit evs T) (t_emit evs T').
Proof.
intros evs T T' H tr. split; apply t_emit_mono; intros tr0 H0; [apply (proj1 (H tr0)) | apply (proj2 (H tr0))]; exact H0.
Qed.

Lemma wset_ext : forall {R} (t : itree node R) (Tk Tk' : R -> TSet), (forall r, t_eq (Tk r) (Tk' r)) -> t_eq (wset t Tk) (wset t Tk').
Proof.
intros R t Tk Tk' H. induction t as [r|n k IH]; cbn [wset]; [apply H|].
intros tr. split; intros [E|(rsp & evs & Hn & He)]; try (left; exact E); right; exists rsp, evs; (split; [exact Hn|]).
- apply (proj1 (t_emit_ext evs _ _ (IH rsp) tr)). exact He.
- apply (proj2 (t_emit_ext evs _ _ (IH rsp) tr)). exact He.
Qed.

Lemma wset_bind : forall {A B} (t : itree node A) (f : A -> itree node B) (Tk : B -> TSet),
t_eq (wset (Qc6I.bind node t f) Tk) (wset t (fun a => wset (f a) Tk)).
Proof.
intros A B t f Tk. induction t as [r|n k IH]; cbn [Qc6I.bind wset]; [apply t_eq_refl|].
intros tr. split; intros [E|(rsp & evs & Hn & He)]; try (left; exact E); right; exists rsp, evs; (split; [exact Hn|]).
- apply (proj1 (t_emit_ext evs _ _ (IH rsp) tr)). exact He.
- apply (proj2 (t_emit_ext evs _ _ (IH rsp) tr)). exact He.
Qed.

Definition epostT {A} (Tk : A -> TSet) : exc A -> TSet := fun r => match r with Unr => t_nil | Ok a => Tk a end.

Lemma wset_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) (Tk : B -> TSet),
t_eq (wset (ebind t f) (epostT Tk)) (wset t (epostT (fun a => wset (f a) (epostT Tk)))).
Proof.
intros A B t f Tk. unfold ebind. eapply t_eq_trans; [apply wset_bind|].
apply wset_ext. intros [|a]; cbn [epostT wset]; apply t_eq_refl.
Qed.

Lemma tio_bind : forall {A B} (t : itree node A) (f : A -> itree node B), tio t -> (forall a, tio (f a)) -> tio (Qc6I.bind node t f).
Proof.
induction t as [r|n k IH]; intros f Ht Hf; cbn in *; [apply Hf|].
destruct Ht as [Hn Hk]. split; [exact Hn|]. intros r. apply IH; [apply Hk| exact Hf].
Qed.

Lemma tio_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)), tio t -> (forall a, tio (f a)) -> tio (ebind t f).
Proof. intros A B t f Ht Hf. unfold ebind. apply tio_bind; [exact Ht|]. intros [|a]; cbn; [exact I| apply Hf]. Qed.

Section Bridge.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Local Notation NS := (nodesA_sound segs LV Hsegs Hsh Hbx Hbc).
Local Notation tsetKA := (tsetK node LV (nstep_raw LV) nexit_raw).
Local Notation nstA := (nstepA LV (nstep_raw LV)).

Lemma nstep_raw_nio : forall n mo rsp mo' evs, io_wnode n ->
(nstep_raw LV n mo rsp mo' evs <-> nio n rsp evs /\ drift LV mo mo').
Proof.
intros n mo rsp mo' evs Hn. destruct n; cbn in Hn; try destruct Hn; cbn [nstep_raw nstep nio].
- split.
+ intros (mo2 & (-> & H) & Hd). split; [exact H| exact Hd].
+ intros (H & Hd). exists mo. split; [split; [reflexivity| exact H]| exact Hd].
- split.
+ intros (mo2 & (-> & -> & ->) & Hd). split; [split; reflexivity| exact Hd].
+ intros ((-> & ->) & Hd). exists mo. split; [repeat split| exact Hd].
Qed.

Lemma nexit_raw_io : forall n mo code mo', io_wnode n -> ~ nexit_raw n mo code mo'.
Proof. intros n mo code mo' Hn H. destruct n; cbn in Hn, H; try destruct Hn; exact H. Qed.

Lemma tsetK_wset : forall {R} (t : itree node R) (Tk : R -> TSet) mo, tio t -> t_eq (tsetKA t Tk mo) (wset t Tk).
Proof.
intros R t Tk. induction t as [r|n k IH]; intros mo Ht; cbn [tsetK wset]; [apply t_eq_refl|].
cbn [tio] in Ht. destruct Ht as [Hn Hk]. intros tr. split.
- intros [E|[(mo1 & rsp & mo' & evs & Hd & Hr & He)|(mo1 & code & mo' & _ & Hx & _)]].
+ left; exact E.
+ right. apply (nstep_raw_nio n mo1 rsp mo' evs Hn) in Hr. destruct Hr as [Hr _].
exists rsp, evs. split; [exact Hr|]. apply (proj1 (t_emit_ext evs _ _ (IH rsp mo' (Hk rsp)) tr)). exact He.
+ exfalso. exact (nexit_raw_io n mo1 code mo' Hn Hx).
- intros [E|(rsp & evs & Hr & He)]; [left; exact E|]. right; left.
exists mo, rsp, mo, evs. split; [apply drift_refl|]. split.
+ apply (nstep_raw_nio n mo rsp mo evs Hn). split; [exact Hr| apply drift_refl].
+ apply (proj2 (t_emit_ext evs _ _ (IH rsp mo (Hk rsp)) tr)). exact He.
Qed.

Lemma tio_tsafe : forall {R} (t : itree node R) mo, tio t -> tsafe nstA (nsafeA LV) t mo.
Proof.
intros R t. induction t as [r|n k IH]; intros mo Ht; cbn [tsafe]; [exact I|].
destruct Ht as [Hn Hk]. split; [destruct n; cbn in Hn |- *; try destruct Hn; exact I|].
intros rsp mo' evs _. apply IH. apply Hk.
Qed.

Lemma tio_tobliv : forall {R} (t : itree node R), tio t -> tobliv rvarA t.
Proof.
intros R t. induction t as [r|n k IH]; intros Ht; cbn [tobliv]; [exact I|].
destruct Ht as [Hn Hk]. split; [|intros r; apply IH, Hk].
intros r r' [->|H]; [reflexivity|]. destruct n; cbn in Hn, H; try destruct Hn; destruct H.
Qed.

Lemma tio_tnospin : forall {R} (t : itree node R), tio t -> tnospin node is_spinA t.
Proof.
intros R t. induction t as [r|n k IH]; intros Ht; cbn [tnospin]; [exact I|].
destruct Ht as [Hn Hk]. split; [destruct n; cbn in Hn |- *; try destruct Hn; reflexivity|]. intros r; apply IH, Hk.
Qed.

Lemma tpathA_tio : forall {R} (t : itree node R) mo evs r mo', tio t ->
tpath nstA t mo evs r mo' -> wpath t evs r /\ drift LV mo mo'.
Proof.
intros R t. induction t as [r0|n k IH]; intros mo evs r mo' Ht Hp; cbn [tpath wpath] in *.
- destruct Hp as (-> & -> & ->). split; [split; reflexivity| apply drift_refl].
- destruct Ht as [Hn Hk]. destruct Hp as (rsp & mo1 & e1 & e2 & (mo0 & Hd0 & Hr) & Hp & ->).
apply (nstep_raw_nio n mo0 rsp mo1 e1 Hn) in Hr. destruct Hr as [Hr Hd1].
destruct (IH rsp mo1 e2 r mo' (Hk rsp) Hp) as [Hw Hd2].
split; [exists rsp, e1, e2; repeat split; assumption|].
exact (drift_trans LV _ _ _ (drift_trans LV _ _ _ Hd0 Hd1) Hd2).
Qed.

Theorem impl_vj_io : forall {R} (t : itree node R) (Tk : R -> TSet) (Q : R -> machine_state -> Prop) c0 msv,
impl segs (at_nodeA LV segs) t Q msv ->
cinvA LV (cfg_ms c0) (cfg_model c0) ->
tio t ->
(forall r evs c1 msv1,
evt segs (Q r) msv1 -> wpath t evs r -> drift LV (cfg_model c0) (cfg_model c1) ->
cinvA LV (cfg_ms c1) (cfg_model c1) ->
msview LV (cfg_model c1) (cfg_ms c1) = msv1 \/ (c1 = c0 /\ msv1 = msv) ->
VJ LV (JS segs (Tk r)) c1 msv1) ->
VJ LV (JS segs (wset t Tk)) c0 msv.
Proof.
intros R t Tk Q c0 msv Himpl HC Ht HK.
pose proof (impl_vj_vis node segs LV Hwx Hsegs (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) (xinvA LV) is_spinA rvarA (jsome LV)
(jsome_stable LV) NS t Tk Q c0 msv Himpl HC (tio_tsafe t _ Ht) (tio_tobliv t Ht) (tio_tnospin t Ht)) as V.
intros ms mo Hrel. unfold JS. eapply srz_conseq; [apply V; [|exact Hrel]| apply tsetK_wset; exact Ht].
intros r evs c1 msv1 HQ Hp HC1 Hc1. destruct (tpathA_tio t _ evs r _ Ht Hp) as [Hw Hd].
exact (HK r evs c1 msv1 HQ Hw Hd HC1 Hc1).
Qed.

End Bridge.
End Mq3.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHWH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHWH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Inductive gnode : Type := GGetrandom (buf len : Z).

Lemma lookup_ca_278 : lookup_ca checked_table 278 = Some arm_getrandom. Proof. reflexivity. Qed.

Section Getrandom.
Variable segs : list Segment.
Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.

Definition at_g (n : gnode) (ms : machine_state) : Prop :=
match n with
| GGetrandom buf len =>
ms_svc_pending ms = Some (Z_to_bv 64 278) /\
areg ms 10 = Z_to_bv 64 buf /\ areg ms 11 = Z_to_bv 64 len /\
(areg ms 12 = Z_to_bv 64 0 \/ areg ms 12 = Z_to_bv 64 GRND_NONBLOCK) /\
1 <= len <= 256 /\ buf + len <= task_size_max /\
wr_at segs (ms_mem ms) buf len
end.

Definition gstep (n : gnode) (mo : Model) (rsp : resp) (mo2 : Model) (evs : list event) : Prop :=
match n with
| GGetrandom buf len =>
evs = [] /\ mo2 = mo /\ exists bs, Z.of_nat (length bs) = len /\ rsp = mkEffect (len_word bs) [(Z_to_bv 64 buf, bs)] []
end.
Definition gstep_raw (n : gnode) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
exists mo2, gstep n mo rsp mo2 evs /\ drift L mo2 mo'.

Lemma getr_check_spec : forall ms mo buf len eff,
at_g (GGetrandom buf len) ms ->
check_syscall (sys_input segs ms (Z_to_bv 64 278)) eff mo
= check_getrandom (sys_input segs ms (Z_to_bv 64 278)) (Z_to_bv 64 buf) (Z_to_bv 64 len) (areg ms 12) eff mo.
Proof.
intros ms mo buf len eff (Hsvc & Ha0 & Ha1 & Ha2 & Hlen & Htop & Hwr).
erewrite check_syscall_arm; [| rewrite in_sysno_si; change (bv_unsigned (Z_to_bv 64 278)) with 278; exact lookup_ca_278].
autorewrite with arm_unfold. rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si. rewrite Ha0, Ha1. reflexivity.
Qed.

Lemma getr_check_shape : forall ms mo buf len eff,
at_g (GGetrandom buf len) ms ->
check_getrandom (sys_input segs ms (Z_to_bv 64 278)) (Z_to_bv 64 buf) (Z_to_bv 64 len) (areg ms 12) eff mo
= match eff with
| mkEffectU r [(a, bs)] [] [] [] [] =>
if bv_eqb a (Z_to_bv 64 buf) && bv_eqb r (len_word bs) && (Z.of_nat (length bs) =? len)
then CheckOk mo [] else CheckReject
| _ => CheckReject
end.
Proof.
intros ms mo buf len eff (Hsvc & Ha0 & Ha1 & Ha2 & Hlen & Htop & Hwr).
pose proof Hwr as (Hb0 & Hb1 & _). unfold task_size_max, TASK_SIZE in Htop.
unfold check_getrandom.
assert (Hfl : negb ((bv_unsigned (areg ms 12) =? 0) || (bv_unsigned (areg ms 12) =? GRND_NONBLOCK)) = false).
{ destruct Ha2 as [->| ->]; reflexivity. }
rewrite Hfl.
assert (Hul : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
assert (Hmc : negb (modeled_rw_count (Z_to_bv 64 len)) = false).
{ unfold modeled_rw_count. rewrite Hul. apply negb_false_iff. apply Z.leb_le. unfold rw_bytes_max. lia. }
rewrite Hmc. rewrite in_wmem_si.
pose proof (read_bytes_map_wr_at segs ms buf len len Hwr ltac:(lia) ltac:(lia)) as W.
destruct (read_bytes_map (ms_writable_byte segs ms) (Z_to_bv 64 buf) (Z_to_bv 64 len)) as [wv|]; [| congruence].
assert (Hz : negb (w_is0 (Z_to_bv 64 len)) = true).
{ unfold w_is0, bv_eqb. rewrite Hul. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply negb_true_iff. apply Z.eqb_neq. lia. }
rewrite Hz. rewrite Hul. replace (len <=? getrandom_small_max) with true by (symmetry; apply Z.leb_le; unfold getrandom_small_max; lia).
reflexivity.
Qed.

Lemma getr_check_ok_iff : forall ms mo buf len eff mo2 evs,
at_g (GGetrandom buf len) ms ->
(check_getrandom (sys_input segs ms (Z_to_bv 64 278)) (Z_to_bv 64 buf) (Z_to_bv 64 len) (areg ms 12) eff mo = CheckOk mo2 evs
<-> gstep (GGetrandom buf len) mo eff mo2 evs).
Proof.
intros ms mo buf len eff mo2 evs Hat. rewrite (getr_check_shape ms mo buf len eff Hat). cbn [gstep].
destruct eff as [r ws zs us cs ci]. split.
- intros H. destruct ws as [|[a bs] [|? ?]]; try discriminate. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (bv_eqb a (Z_to_bv 64 buf)) eqn:E1; [|discriminate].
destruct (bv_eqb r (len_word bs)) eqn:E2; [|discriminate].
destruct (Z.of_nat (length bs) =? len) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. apply Z.eqb_eq in E3. subst.
split; [reflexivity|]. split; [reflexivity|]. exists bs. split; reflexivity.
- intros (-> & -> & bs & Hbs & E). inversion E; subst. rewrite !bv_eqb_refl, Z.eqb_refl. reflexivity.
Qed.

Lemma getr_factsA : forall ms mo buf len,
at_g (GGetrandom buf len) (msview L mo ms) -> lv_inv L mo -> fdinv mo ->
file_facts segs L ms mo (gstep (GGetrandom buf len) mo).
Proof.
intros ms mo buf len Hat HI HX.
pose proof Hat as (Hsvc & Ha0 & Ha1 & Ha2 & Hlen & Htop & Hwrv). cbn [ms_svc_pending ms_mem msview restrict] in Hsvc, Hwrv.
change (mrestrict (hidden L mo) (ms_mem ms)) with (view L mo (ms_mem ms)) in Hwrv.
destruct (wr_at_view L segs Hsegs mo (ms_mem ms) _ _ Hwrv) as [Hwr Hvis].
assert (Hatf : at_g (GGetrandom buf len) ms).
{ split; [exact Hsvc|]. split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Ha2|]. split; [exact Hlen|]. split; [exact Htop| exact Hwr]. }
exists (Z_to_bv 64 278), (fun eff => check_getrandom (sys_input segs ms (Z_to_bv 64 278)) (Z_to_bv 64 buf) (Z_to_bv 64 len) (areg ms 12) eff mo).
split; [exact Hsvc|]. split; [|split; [|split]].
- intros eff. apply (getr_check_spec ms mo buf len eff Hatf).
- intros eff. rewrite (getr_check_shape ms mo buf len eff Hatf).
destruct eff as [r [|[a bs] [|? ?]] [|? ?] [|? ?] [|? ?] [|? ?]]; try discriminate.
destruct (_ && _); discriminate.
- intros eff mo2 evs Hck. apply (getr_check_ok_iff ms mo buf len eff mo2 evs Hatf) in Hck.
pose proof Hck as (-> & -> & bs & Hbs & ->).
split; [rewrite canon_of_canonical by reflexivity; exact Hck|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact HX|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app write_accesses].
apply ranges_avoid_cons; [|apply ranges_avoid_nil].
pose proof Hwr as (Hb0 & Hb1 & _). unfold task_size_max, TASK_SIZE in Htop.
intros k Hk. unfold woff. change (Z_to_bv 64 buf) with (wa buf). rewrite wa_unsigned by lia.
change (Z_to_bv 64 (buf + Z.of_nat k)) with (wa (buf + Z.of_nat k)). apply Hvis. lia.
- intros rsp mo2 evs HP. exists rsp. split.
+ apply canon_of_canonical. destruct HP as (_ & _ & bs & _ & ->). reflexivity.
+ apply (getr_check_ok_iff ms mo buf len rsp mo2 evs Hatf). exact HP.
Qed.

Notation CINV := (cinv L (xinvA L) (jsome L)).

Lemma getr_nodeA : forall buf len ms mo,
at_g (GGetrandom buf len) (msview L mo ms) -> m_halted mo = None -> CINV ms mo ->
(forall evs X, sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs X ->
exists rsp ms' mo', X = SNext (mkCfg ms' mo') /\ msview L mo' ms' = nret (msview L mo ms) rsp /\
gstep_raw (GGetrandom buf len) mo rsp mo' evs /\ CINV ms' mo' /\ m_halted mo' = None)
/\ (forall rsp mo' evs, gstep_raw (GGetrandom buf len) mo rsp mo' evs ->
exists ms' mo2, sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs (SNext (mkCfg ms' mo2)) /\
msview L mo2 ms' = nret (msview L mo ms) rsp /\
gstep_raw (GGetrandom buf len) mo rsp mo2 evs /\ msim mo' mo2 /\ m_halted mo2 = None)
/\ (exists rsp mo' evs, gstep_raw (GGetrandom buf len) mo rsp mo' evs).
Proof.
intros buf len ms mo Hat Hh HC. pose proof HC as ([HF HV] & HI & HJ).
destruct (getr_factsA ms mo buf len Hat HI HF) as (x8 & chk & Hsvc & Hchk & Hnu & Hok & Hcompl).
destruct (file_kit segs L ms mo x8 (gstep (GGetrandom buf len) mo) chk Hsvc Hh HC Hchk Hnu Hok Hcompl) as (K1 & K2 & K3).
split; [|split].
- intros evs X Hst. destruct (K1 evs X (sstep_cfg_sub segs _ _ _ _ Hst)) as (rsp & ms' & mo' & HX & Hv & HP & HC' & Hh').
exists rsp, ms', mo'. auto.
- intros rsp mo' evs (mo2 & HP & Hd).
destruct (K2 rsp mo2 mo' evs HP Hd) as (ms' & mo3 & Hst & Hv & HP3 & Hs & Hh3).
exists ms', mo3. split; [| auto].
apply sstep_cfg_nonalloc; [| exact Hst]. intros y Hy. destruct Hat as [Hs0 _].
change (ms_svc_pending ms = Some (Z_to_bv 64 278)) in Hs0. rewrite Hs0 in Hy. injection Hy as <-.
intros Hin. vm_compute in Hin. lia.
- destruct K3 as (rsp & mo2 & evs & HP). exists rsp, mo2, evs, mo2. split; [exact HP| apply drift_refl].
Qed.

Theorem gnode_sound :
node_soundA gnode segs L at_g gstep_raw (fun _ _ _ _ => False) (fun _ _ => True) (xinvA L) (fun _ => false)
(fun _ r r' => r = r') (jsome L).
Proof.
constructor.
- intros n msr Hsp. discriminate.
- intros n Hsp. discriminate.
- intros [buf len] ms mo evs X _ Hat Hh HC _ Hst. left. exact (proj1 (getr_nodeA buf len ms mo Hat Hh HC) evs X Hst).
- intros [buf len] ms mo rsp mo' evs _ Hat Hh HC _ Hr.
destruct (proj1 (proj2 (getr_nodeA buf len ms mo Hat Hh HC)) rsp mo' evs Hr) as (ms' & mo2 & Hst & Hv & HP & Hs & Hh2).
exists ms', mo2, rsp. auto 8.
- intros n ms mo code mo' _ _ _ _ _ [].
- intros [buf len] ms mo _ Hat Hh HC _. left. exact (proj2 (proj2 (getr_nodeA buf len ms mo Hat Hh HC))).
- intros [buf len] moA moB rsp mo' evs Hs (mo2 & (-> & -> & bs & Hbs & ->) & Hd).
exists moB. split.
+ exists moB. split; [split; [reflexivity|]; split; [reflexivity|]; exists bs; auto| apply drift_refl].
+ eapply msim_trans; [apply msim_sym; eapply drift_msim; exact Hd| exact Hs].
- intros n moA moB code mo' _ [].
- intros mo mo' Hd HX. eapply xinvA_drift; eassumption.
- intros n mo mo' _ _. exact I.
Qed.

End Getrandom.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDS.

Section Rule.
Variable segs : list Segment.
Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.
Variable J : config -> Prop.
Hypothesis J_nclosed : forall c (I : Type) (nx : I -> config) (i0 : I),
node_ok segs c I (fun _ => []) nx -> (forall i, J (nx i)) -> J c.

End Rule.
