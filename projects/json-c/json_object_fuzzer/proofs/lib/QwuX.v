(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi QdTb QHWH Q1lV Qcrs QUcd QCUT QwAs Qc6I Qsn5 Qknc QNqr QTtp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QQIi QdTb QHWH Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I Qsn5 Qknc.
Import QNqr QTtp.Mq0.
Import ListNotations.
Open Scope Z_scope.

Section NodeTagged.
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

Theorem vj_silent_tagged : forall (n : node) (V : config -> Prop) (T : TSet) (P : Prop) (Qs : machine_state -> Prop) c0 msv,
at_node n msv ->
cinvA (cfg_ms c0) (cfg_model c0) ->
is_spin n = false -> nsafe n (cfg_model c0) ->
(forall mo1 code mo', drift L (cfg_model c0) mo1 -> ~ nexit_raw n mo1 code mo') ->
(forall rsp mo' evs, nstA n (cfg_model c0) rsp mo' evs -> evs = []) ->
(forall rsp rsp2, rvar n rsp rsp2 -> Qs (nret msv rsp) -> Qs (nret msv rsp2)) ->
(P -> exists rsp, Qs (nret msv rsp) /\ forall mo1, drift L (cfg_model c0) mo1 -> exists mo', nstep_raw n mo1 rsp mo' []) ->
(forall rsp c1, nstA n (cfg_model c0) rsp (cfg_model c1) [] ->
cinvA (cfg_ms c1) (cfg_model c1) -> m_halted (cfg_model c1) = None ->
VJ L (slbwP segs V T (Qs (nret msv rsp))) c1 (nret msv rsp)) ->
VJ L (slbwP segs V T P) c0 msv.
Proof.
intros n V T P Qs c0 msv Hat HC Hsp Hns Hnx Hsil Hvar Hgood HK.
intros ms mo (Hv & Hd & HI & Hh & Hhid). destruct c0 as [ms0 mo0]. cbn [cfg_ms cfg_model] in *.
assert (HC1 : cinvA ms mo).
{ eapply (cinv_drift node segs L at_node nstep_raw nexit_raw nsafe xinv is_spin rvar jinv jinv_stable NS); [exact Hd| exact Hhid| exact HC]. }
assert (Hat1 : at_node n (msview L mo ms)) by (rewrite Hv; exact Hat).
assert (Hns1 : nsafe n mo) by (eapply (nsA_safe_drift _ _ _ _ _ _ _ _ _ _ _ NS); eassumption).
set (c1 := mkCfg ms mo).
set (Ix := { x : list event * config | sstep_cfg segs (alloc_only_cfg false) c1 (fst x) (SNext (snd x)) }).
assert (Hexpl : forall e st, sstep_cfg segs (alloc_only_cfg false) c1 e st ->
exists rsp ms' mo', st = SNext (mkCfg ms' mo') /\ e = [] /\ msview L mo' ms' = nret (msview L mo ms) rsp /\
nstep_raw n mo rsp mo' e /\ cinvA ms' mo' /\ m_halted mo' = None).
{ intros e st Hst.
destruct (nsA_complete _ _ _ _ _ _ _ _ _ _ _ NS n ms mo e st Hsp Hat1 Hh HC1 Hns1 Hst)
as [(rsp & ms' & mo' & -> & Hv' & Hr & HC' & Hh')|(code & mo' & _ & Hx & _)].
- exists rsp, ms', mo'. rewrite (Hsil rsp mo' e (ex_intro _ mo (conj Hd Hr))).
split; [reflexivity|]. split; [reflexivity|]. split; [exact Hv'|]. split; [rewrite <- (Hsil rsp mo' e (ex_intro _ mo (conj Hd Hr))); exact Hr|]. split; [exact HC'| exact Hh'].
- exfalso. exact (Hnx mo code mo' Hd Hx). }
assert (Hnode : node_ok segs c1 Ix (fun _ => []) (fun i => snd (proj1_sig i))).
{ split.
- intros [[e c'] Hst]. cbn [fst snd proj1_sig] in *. destruct (Hexpl e _ Hst) as (_ & _ & _ & _ & -> & _). exact Hst.
- intros e st Hst. destruct (Hexpl e st Hst) as (rsp & ms' & mo' & -> & -> & _).
exists (exist _ ([], mkCfg ms' mo') Hst). split; reflexivity. }
apply (slbwP_nclosedT segs V T P c1 Ix (fun i => snd (proj1_sig i))
(fun i => Qs (msview L (cfg_model (snd (proj1_sig i))) (cfg_ms (snd (proj1_sig i))))) Hnode).
- intros [[e c'] Hst]. cbn [fst snd proj1_sig].
destruct (Hexpl e _ Hst) as (rsp & ms' & mo' & E & -> & Hv' & Hr & HC' & Hh'). injection E as ->. cbn [cfg_model cfg_ms].
assert (HstA : nstA n mo0 rsp mo' []) by (exists mo; split; assumption).
rewrite Hv', Hv.
apply (vj_enter L _ ms' mo' (proj1 (proj2 HC')) Hh').
rewrite Hv', Hv. exact (HK rsp (mkCfg ms' mo') HstA HC' Hh').
- intros HP. destruct (Hgood HP) as (rsp & HQ & Hreal). destruct (Hreal mo Hd) as (mo' & Hr).
destruct (nsA_sound _ _ _ _ _ _ _ _ _ _ _ NS n ms mo rsp mo' [] Hsp Hat1 Hh HC1 Hns1 Hr) as (ms' & mo2 & rsp2 & Hst & Hv2 & _ & _ & Hrv & _).
exists (exist _ ([], mkCfg ms' mo2) Hst). cbn [fst snd proj1_sig cfg_model cfg_ms].
rewrite Hv2, Hv. exact (Hvar rsp rsp2 Hrv HQ).
Qed.

End NodeTagged.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui.
Import ListNotations.
Open Scope Z_scope.

Definition hid_add (H : word -> bool) (xs : list word) : word -> bool := fun x => H x || existsb (bv_eqb x) xs.

Lemma hid_add_In : forall H xs x, hid_add H xs x = true <-> H x = true \/ In x xs.
Proof.
intros H xs x. unfold hid_add. rewrite orb_true_iff, existsb_exists. split; intros [E|E]; auto.
- destruct E as (y & Hy & Eq). apply bv_eqb_eq in Eq. subst. right. exact Hy.
- right. exists x. split; [exact E| apply bv_eqb_refl].
Qed.

Lemma restrict_nret_mem : forall H H' ms r w1 z1 u1 w2 z2 u2,
mrestrict H' (apply_writes (apply_zeros (apply_unmaps (ms_mem ms) u1) z1) w1)
= apply_writes (apply_zeros (apply_unmaps (mrestrict H (ms_mem ms)) u2) z2) w2 ->
restrict H' (nret ms (mkEffectU r w1 z1 u1 [] [])) = nret (restrict H ms) (mkEffectU r w2 z2 u2 [] []).
Proof.
intros H H' ms r w1 z1 u1 w2 z2 u2 Hm.
unfold restrict, nret, advance_past_svc, apply_effect, set_reg in *.
replace (bv_eqb (10 : bv 5) 0) with false by reflexivity.
cbn [ms_regs ms_fregs ms_pc_val ms_pc ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins apply_copies] in *.
rewrite Hm. reflexivity.
Qed.

Theorem restrict_nret_grant : forall H ms r (a n : word) ws,
wunit ws = true ->
(forall x, In x (map fst ws) -> ms_mem ms x = None) ->
(forall x, zeros_cover [(a, n)] x = true -> H x = false /\ ~ In x (map fst ws)) ->
restrict (hid_add H (map fst ws)) (nret ms (mkEffectU r ws [(a, n)] [] [] []))
= nret (restrict H ms) (mkEffectU r [] [(a, n)] [] [] []).
Proof.
intros H ms r a n ws Hw Hnew Hrng. apply restrict_nret_mem.
apply functional_extensionality. intros x.
cbn [apply_unmaps apply_writes]. unfold mrestrict at 1. cbn [apply_zeros].
destruct (zeros_cover [(a, n)] x) eqn:Ez.
- destruct (Hrng x Ez) as [Hx Hnin].
assert (E : hid_add H (map fst ws) x = false).
{ destruct (hid_add H (map fst ws) x) eqn:E; [|reflexivity]. apply hid_add_In in E as [E|E]; [congruence| contradiction]. }
rewrite E, (apply_writes_units_notIn ws _ x Hw Hnin). cbn [apply_zeros]. rewrite Ez. reflexivity.
- unfold mrestrict. destruct (hid_add H (map fst ws) x) eqn:E.
+ apply hid_add_In in E as [E|E]; [rewrite E; reflexivity|]. rewrite (Hnew x E). destruct (H x); reflexivity.
+ assert (Hx : H x = false) by (destruct (H x) eqn:E2; [|reflexivity]; exfalso; assert (hid_add H (map fst ws) x = true) by (apply hid_add_In; left; exact E2); congruence).
assert (Hnin : ~ In x (map fst ws)) by (intros Hin; assert (hid_add H (map fst ws) x = true) by (apply hid_add_In; right; exact Hin); congruence).
rewrite (apply_writes_units_notIn ws _ x Hw Hnin). cbn [apply_zeros]. rewrite Ez, Hx. reflexivity.
Qed.

Theorem restrict_nret_unmap : forall H H' ms r (a n : word) us,
(forall x, H' x = true -> H x = true) ->
(forall x, H x = true -> H' x = false -> zeros_cover ((a, n) :: us) x = true) ->
(forall x, zeros_cover us x = true -> H x = true) ->
restrict H' (nret ms (mkEffectU r [] [] ((a, n) :: us) [] []))
= nret (restrict H ms) (mkEffectU r [] [] [(a, n)] [] []).
Proof.
intros H H' ms r a n us H1 H2 H3. apply restrict_nret_mem.
apply functional_extensionality. intros x.
cbn [apply_zeros apply_writes]. unfold mrestrict at 1. cbn [apply_unmaps].
assert (Ec : zeros_cover ((a, n) :: us) x = zeros_cover [(a, n)] x || zeros_cover us x).
{ unfold zeros_cover. cbn [existsb]. rewrite orb_false_r. reflexivity. }
unfold mrestrict.
destruct (zeros_cover [(a, n)] x) eqn:Ea.
- rewrite Ec. cbn [orb]. destruct (H' x); reflexivity.
- destruct (H x) eqn:Hx.
+ destruct (H' x) eqn:Hx'; [reflexivity|]. rewrite (H2 x Hx Hx'). reflexivity.
+ assert (Hx' : H' x = false) by (destruct (H' x) eqn:E; [rewrite (H1 x E) in Hx; discriminate| reflexivity]).
assert (Eu : zeros_cover us x = false) by (destruct (zeros_cover us x) eqn:E; [rewrite (H3 x E) in Hx; discriminate| reflexivity]).
rewrite Hx', Ec, Eu. reflexivity.
Qed.
