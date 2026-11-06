(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLiw.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaJW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaJW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaJW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaJW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVJy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVJy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QK1W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QK1W. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.
Import ListNotations.
Open Scope Z_scope.

Section ReallocQ.
Variable segs : list Segment.
Variable L : ALay.
Variable LV : lvp.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).
Variables TOT0 N0 : Z.
Hypothesis LL : ll_ok L LV BUDGET PERM TOT0 N0.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.
Variable FR : list (Z * Z).
Hypothesis HFR : Forall (fr_ok L PERM) FR.
Hypothesis F_off : H_off_segments segs (Fof LV FR).

Notation KIx := (KI LV BUDGET PERM TOT0 N0).
Notation F := (Fof LV FR).
Notation MSPEC := (mspec (nstepsA LV) (nsafeA LV)).
Notation tcpsFA := (tcpsF node LV (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) is_spinA F).

Definition realloc_leaf (X X' : list aptr) (p : aptr) (n : Z) (ps : PStateA) (mo0 : Model) (r : option aptr) (s' : PStateA) (mo' : Model) : Prop :=
exists a' g' q, r = Some q /\ s' = set_a a' ps /\ vm_onlyA mo0 mo' /\ KIx g' mo' /\ GS a' g' /\
as_spent a' <= as_spent (ps_a ps) + mcost n /\
ainv (q :: X') a' /\ ~ In q (allptrs X [] (ps_a ps)) /\ pshape n q /\
qtot a' <= qtot (ps_a ps) + aptr_used p + kBatchBytes.

Lemma set_a_set_a : forall a1 a2 ps, set_a a2 (set_a a1 ps) = set_a a2 ps.
Proof. intros a1 a2 [? ? ?]; reflexivity. Qed.
Lemma ps_a_set_a : forall a ps, ps_a (set_a a ps) = a.
Proof. intros a [? ? ?]; reflexivity. Qed.

Definition free_room_after (X : list aptr) : Prop :=
forall q a', ainv (q :: X) a' -> class_size kBatchClass * (tot (q :: X) [] 0 a' kBatchClass + 17) <= kFreeArrayOffset.

Theorem raw_realloc_A_specQ X X' p n g (ps : PStateA) (mo0 : Model) :
0 <= n -> n <= kMaxReq -> too_big n = false ->
ainv X (ps_a ps) -> GS (ps_a ps) g -> malloc_room X (ps_a ps) n ->
CAPS + as_spent (ps_a ps) + mcost n <= BUDGET -> zlen (as_reg (ps_a ps)) + 1 <= kMaxCnt -> KIx g mo0 ->
Permutation X (p :: X') -> free_room_after X ->
0 <= q_bytes (as_gq (ps_a ps)) -> 0 <= q_bytes (as_tq (ps_a ps)) -> qroom (ps_a ps) p ->
MSPEC (fun s0 mo => s0 = ps /\ mo = mo0) (raw_realloc_A L p n) (realloc_leaf X X' p n ps mo0).
Proof.
intros Hn H39 Htb AI G Hroom HB Hcnt K HP HFRA Hg0 Ht0 QR. unfold raw_realloc_A.
eapply mspec_bind; [exact (raw_malloc_A_specGq L LV BUDGET PERM TOT0 N0 LL X n g ps mo0 Hn H39 Htb AI G Hroom HB Hcnt K)|].
intros r. apply mspec_pointwise. intros s1 mo1 (a' & g' & q & -> & -> & Hv & K' & G' & Hsp & AI' & Hnin & Hshape & KT & KG).
assert (HP1 : Permutation (q :: X) (p :: q :: X')) by (etransitivity; [apply perm_skip; exact HP| apply perm_swap]).
eapply mspec_bind.
{ eapply mspec_pre; [exact (raw_free_A_specQ L LV BUDGET PERM TOT0 N0 LL (q :: X) (q :: X') p g' (set_a a' ps) mo1
ltac:(rewrite ps_a_set_a; exact AI') HP1 ltac:(rewrite ps_a_set_a; exact (HFRA q a' AI'))
ltac:(rewrite ps_a_set_a; exact G') ltac:(rewrite ps_a_set_a; lia) K'
ltac:(rewrite ps_a_set_a, KG; exact Hg0) ltac:(rewrite ps_a_set_a, KT; exact Ht0)
ltac:(rewrite ps_a_set_a; unfold qroom in *; rewrite KG, KT; exact QR))|].
intros s2 mo2 [-> ->]. split; reflexivity. }
intros []. apply mspec_ret.
intros s2 mo2 (a2 & g2 & -> & Hv2 & K2 & G2 & Hsp2 & AI2 & HQT). rewrite ps_a_set_a in *.
exists a2, g2, q. split; [reflexivity|]. split; [apply set_a_set_a|]. split; [exact (vm_onlyA_trans _ _ _ Hv Hv2)|]. split; [exact K2|]. split; [exact G2|].
split; [lia|]. split; [exact AI2|]. split; [exact Hnin|]. split; [exact Hshape|].
unfold qtot in *. rewrite KT, KG in HQT. exact HQT.
Qed.

Theorem raw_realloc_A_tcpsF X X' p n g (ps : PStateA) (mo0 : Model) :
0 <= n -> n <= kMaxReq -> too_big n = false ->
ainv X (ps_a ps) -> GS (ps_a ps) g -> malloc_room X (ps_a ps) n ->
CAPS + as_spent (ps_a ps) + mcost n <= BUDGET -> zlen (as_reg (ps_a ps)) + 1 <= kMaxCnt -> KIx g mo0 ->
Permutation X (p :: X') -> free_room_after X ->
tcpsFA (raw_realloc_A L p n ps) mo0.
Proof.
intros Hn H39 Htb AI G Hroom HB Hcnt K HP HFRA.
pose proof (raw_malloc_A_specGq L LV BUDGET PERM TOT0 N0 LL X n g ps mo0 Hn H39 Htb AI G Hroom HB Hcnt K ps mo0 (conj eq_refl eq_refl)) as Hspec.
unfold raw_realloc_A, Qpj5.Mq1.mbind at 1. unfold ebind. apply tcpsF_bind.
- exact (raw_malloc_A_tcpsF segs L LV BUDGET PERM TOT0 N0 LL FR HFR X n g ps mo0 Hn H39 Htb AI G Hroom HB Hcnt K).
- intros r mo1 Hp. pose proof (@twf_tpath _ _ _ _ _ _ _ _ _ Hspec Hp) as Hleaf.
destruct r as [|[r s1]]; [exact I|]. cbn [fst snd] in Hleaf |- *.
destruct Hleaf as (a' & g' & q & -> & -> & Hv & K' & G' & Hsp & AI' & Hnin & Hshape & KT & KG).
assert (HP1 : Permutation (q :: X) (p :: q :: X')) by (etransitivity; [apply perm_skip; exact HP| apply perm_swap]).
unfold Qpj5.Mq1.mbind at 1. unfold ebind. apply tcpsF_bind.
+ exact (raw_free_A_tcpsF segs L LV BUDGET PERM TOT0 N0 LL FR HFR (q :: X) (q :: X') p g' (set_a a' ps) mo1
ltac:(rewrite ps_a_set_a; exact AI') HP1 ltac:(rewrite ps_a_set_a; exact (HFRA q a' AI'))
ltac:(rewrite ps_a_set_a; exact G') ltac:(rewrite ps_a_set_a; lia) K').
+ intros [|[[] s2]] mo2 _; cbn; exact I.
Qed.

Lemma raw_realloc_A_tmm : forall p n ps, tmm (raw_realloc_A L p n ps).
Proof.
intros p n ps. unfold raw_realloc_A, Qpj5.Mq1.mbind at 1. apply tmm_ebind; [apply raw_malloc_A_tmm|].
intros [[q|] s1]; cbn [fst snd]; [| exact I].
unfold Qpj5.Mq1.mbind at 1. apply tmm_ebind; [apply raw_free_A_tmm|]. intros [[] s2]. exact I.
Qed.

Theorem arealloc_vj_Fq (T : TSet) (X X' : list aptr) (p : aptr) (n : Z) (g : ghost) (ps : PStateA)
(Q : option aptr -> PStateA -> machine_state -> Prop) (c0 : config) (msv : machine_state) :
implMG segs (at_nodeA LV segs) (raw_realloc_A L p n) ps Q (restrict F msv) ->
cinvA LV (cfg_ms c0) (cfg_model c0) ->
0 <= n -> n <= kMaxReq -> too_big n = false ->
ainv X (ps_a ps) -> GS (ps_a ps) g -> malloc_room X (ps_a ps) n ->
CAPS + as_spent (ps_a ps) + mcost n <= BUDGET -> zlen (as_reg (ps_a ps)) + 1 <= kMaxCnt -> KIx g (cfg_model c0) ->
Permutation X (p :: X') -> free_room_after X ->
0 <= q_bytes (as_gq (ps_a ps)) -> 0 <= q_bytes (as_tq (ps_a ps)) -> qroom (ps_a ps) p ->
(forall q ps' c1 msv1,
evt segs (Q (Some q) ps') (restrict F msv1) ->
(exists a' g', ps' = set_a a' ps /\ vm_onlyA (cfg_model c0) (cfg_model c1) /\ KIx g' (cfg_model c1) /\ GS a' g' /\
as_spent a' <= as_spent (ps_a ps) + mcost n /\ ainv (q :: X') a' /\ ~ In q (allptrs X [] (ps_a ps)) /\ pshape n q /\
qtot a' <= qtot (ps_a ps) + aptr_used p + kBatchBytes) ->
cinvA LV (cfg_ms c1) (cfg_model c1) -> m_halted (cfg_model c1) = None ->
vmst (cfg_model c0) (cfg_model c1) ->
(forall x, F x = true -> ms_mem msv1 x = ms_mem msv x) ->
VJ LV (JS segs T) c1 msv1) ->
VJ LV (JS segs T) c0 msv.
Proof.
intros Himpl HC Hn H39 Htb AI G Hroom HB Hcnt K HP HFRA Hg0 Ht0 QR HK. destruct c0 as [ms0 mo0]. cbn [cfg_ms cfg_model] in *.
pose proof (raw_realloc_A_specQ X X' p n g ps mo0 Hn H39 Htb AI G Hroom HB Hcnt K HP HFRA Hg0 Ht0 QR ps mo0 (conj eq_refl eq_refl)) as Hspec.
unfold implMG in Himpl.
eapply (impl_vj_F node segs LV Hwx Hsegs (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) (xinvA LV) is_spinA rvarA (jsome LV)
(jsome_stable LV) (nodesA_sound segs LV Hsegs Hsh Hbx Hbc) (JS segs T) (js_nclosed segs T) F F_off
(raw_realloc_A L p n ps) _ (mkCfg ms0 mo0) msv Himpl HC).
- exact (raw_realloc_A_tcpsF X X' p n g ps mo0 Hn H39 Htb AI G Hroom HB Hcnt K HP HFRA).
- intros r c1 msv1 HQ Hp HC1 Hh1 _ HF1. cbn [cfg_model] in Hp.
pose proof (@twf_tpath _ _ _ _ _ _ _ _ _ Hspec Hp) as Hleaf.
destruct r as [|[r ps']]; [destruct Hleaf|]. cbn [fst snd] in Hleaf.
destruct Hleaf as (a' & g' & q & -> & Hleaf). cbn [epost fst snd] in HQ.
apply (HK q ps' c1 msv1 HQ); [exists a', g'; exact Hleaf| exact HC1| exact Hh1| exact (tpath_vmst LV _ _ _ _ _ (raw_realloc_A_tmm p n ps) Hp)| exact HF1].
Qed.
End ReallocQ.
