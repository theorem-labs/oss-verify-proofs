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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgT.
Import ListNotations.
Open Scope Z_scope.

Section RulesQ.
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

Theorem raw_malloc_A_specGq X n g (ps : PStateA) (mo0 : Model) :
0 <= n -> n <= kMaxReq -> too_big n = false ->
ainv X (ps_a ps) -> GS (ps_a ps) g -> malloc_room X (ps_a ps) n ->
CAPS + as_spent (ps_a ps) + mcost n <= BUDGET -> zlen (as_reg (ps_a ps)) + 1 <= kMaxCnt -> KIx g mo0 ->
MSPEC (fun s0 mo => s0 = ps /\ mo = mo0) (raw_malloc_A L n)
(fun r s' mo' => exists a' g' p, r = Some p /\ s' = set_a a' ps /\ vm_onlyA mo0 mo' /\ KIx g' mo' /\ GS a' g' /\
as_spent a' <= as_spent (ps_a ps) + mcost n /\
ainv (p :: X) a' /\ ~ In p (allptrs X [] (ps_a ps)) /\ pshape n p /\
as_tq a' = as_tq (ps_a ps) /\ as_gq a' = as_gq (ps_a ps)).
Proof.
intros Hn H39 Htb AI G [R1 R2] HB Hcnt K. unfold raw_malloc_A.
eapply mspec_bind; [apply mspec_get|]. intros s0. cbn beta.
apply mspec_pointwise. intros s1 mo [-> [-> ->]].
eapply mspec_bind.
{ eapply mspec_pre; [eapply (membedA_specG L LV BUDGET PERM TOT0 N0 LL (asan_malloc L (ps_a ps) n) _ _ g ps mo0)|].
- apply tall_rokS; [| apply asan_malloc_ns].
apply tall_conj; [apply (asan_malloc_inv L X (ps_a ps) n AI Hn Htb R1 R2)| apply (asan_malloc_kq L X (ps_a ps) n AI Hn Htb R1 R2)].
- apply teva_aokG. apply (asan_malloc_teva L BUDGET aok0 (llo_lay _ _ _ _ _ _ LL) (aok_anon astate0) X g (ps_a ps) n AI Hn H39 R1 G HB Hcnt).
- exact K.
- intros s2 mo2 [-> ->]. split; reflexivity. }
intros [r a']. cbn beta iota. eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
intros s2 mo2 (s3 & -> & -> & [[Hpost Hkq] Hsome] & Hv & g' & [G' Hsp] & K'). cbn beta iota in Hpost, G', Hsp, Hsome. cbn [fst] in Hsome.
destruct r as [p|]; [|contradiction]. destruct Hpost as (HA & HN & HS). destruct Hkq as [KT KG]. cbn [snd] in KT, KG.
exists a', g', p. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hv|]. split; [exact K'|]. split; [exact G'|].
split; [exact Hsp|]. split; [exact HA|]. split; [exact HN|]. split; [exact HS|]. split; [exact KT| exact KG].
Qed.

Theorem raw_free_A_specQ X X' p g (ps : PStateA) (mo0 : Model) :
ainv X (ps_a ps) -> Permutation X (p :: X') ->
class_size kBatchClass * (tot X [] 0 (ps_a ps) kBatchClass + 17) <= kFreeArrayOffset ->
GS (ps_a ps) g -> CAPS + as_spent (ps_a ps) <= BUDGET -> KIx g mo0 ->
0 <= q_bytes (as_gq (ps_a ps)) -> 0 <= q_bytes (as_tq (ps_a ps)) -> qroom (ps_a ps) p ->
MSPEC (fun s0 mo => s0 = ps /\ mo = mo0) (raw_free_A L p)
(fun _ s' mo' => exists a' g', s' = set_a a' ps /\ vm_onlyA mo0 mo' /\ KIx g' mo' /\ GS a' g' /\
as_spent a' = as_spent (ps_a ps) /\ ainv X' a' /\ qtot a' <= qtot (ps_a ps) + aptr_used p + kBatchBytes).
Proof.
intros AI HP Hroom G HB K Hg0 Ht0 QR. unfold raw_free_A.
eapply mspec_bind; [apply mspec_get|]. intros s0. cbn beta.
apply mspec_pointwise. intros s1 mo [-> [-> ->]].
eapply mspec_bind.
{ eapply mspec_pre; [eapply (membedA_spec L LV BUDGET PERM TOT0 N0 LL (asan_free L (ps_a ps) p) _ _ g ps mo0)|].
- apply tall_conj; [apply (asan_free_inv L X X' p (ps_a ps) AI HP Hroom)| apply (asan_free_qb L X X' p (ps_a ps) AI HP Hroom Hg0 Ht0 QR)].
- apply (asan_free_teva L BUDGET aok0 (llo_lay _ _ _ _ _ _ LL) X X' p g (ps_a ps) AI HP Hroom G HB).
- exact K.
- intros s2 mo2 [-> ->]. split; reflexivity. }
intros a'. cbn beta. eapply mspec_upd'.
intros s2 mo2 (-> & [Hpost Hq] & Hv & g' & [G' Hsp] & K').
exists a', g'. split; [reflexivity|]. split; [exact Hv|]. split; [exact K'|]. split; [exact G'|]. split; [exact Hsp|]. split; [exact Hpost| exact Hq].
Qed.

Theorem amalloc_vj_Fq (T : TSet) (X : list aptr) (n : Z) (g : ghost) (ps : PStateA)
(Q : option aptr -> PStateA -> machine_state -> Prop) (c0 : config) (msv : machine_state) :
implMG segs (at_nodeA LV segs) (raw_malloc_A L n) ps Q (restrict F msv) ->
cinvA LV (cfg_ms c0) (cfg_model c0) ->
0 <= n -> n <= kMaxReq -> too_big n = false ->
ainv X (ps_a ps) -> GS (ps_a ps) g -> malloc_room X (ps_a ps) n ->
CAPS + as_spent (ps_a ps) + mcost n <= BUDGET -> zlen (as_reg (ps_a ps)) + 1 <= kMaxCnt -> KIx g (cfg_model c0) ->
(forall p ps' c1 msv1,
evt segs (Q (Some p) ps') (restrict F msv1) ->
(exists a' g', ps' = set_a a' ps /\ vm_onlyA (cfg_model c0) (cfg_model c1) /\ KIx g' (cfg_model c1) /\ GS a' g' /\
as_spent a' <= as_spent (ps_a ps) + mcost n /\ ainv (p :: X) a' /\ ~ In p (allptrs X [] (ps_a ps)) /\ pshape n p /\
as_tq a' = as_tq (ps_a ps) /\ as_gq a' = as_gq (ps_a ps)) ->
cinvA LV (cfg_ms c1) (cfg_model c1) -> m_halted (cfg_model c1) = None ->
vmst (cfg_model c0) (cfg_model c1) ->
(forall x, F x = true -> ms_mem msv1 x = ms_mem msv x) ->
VJ LV (JS segs T) c1 msv1) ->
VJ LV (JS segs T) c0 msv.
Proof.
intros Himpl HC Hn H39 Htb AI G Hroom HB Hcnt K HK. destruct c0 as [ms0 mo0]. cbn [cfg_ms cfg_model] in *.
pose proof (raw_malloc_A_specGq X n g ps mo0 Hn H39 Htb AI G Hroom HB Hcnt K ps mo0 (conj eq_refl eq_refl)) as Hspec.
unfold implMG in Himpl.
eapply (impl_vj_F node segs LV Hwx Hsegs (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) (xinvA LV) is_spinA rvarA (jsome LV)
(jsome_stable LV) (nodesA_sound segs LV Hsegs Hsh Hbx Hbc) (JS segs T) (js_nclosed segs T) F F_off
(raw_malloc_A L n ps) _ (mkCfg ms0 mo0) msv Himpl HC).
- exact (raw_malloc_A_tcpsF segs L LV BUDGET PERM TOT0 N0 LL FR HFR X n g ps mo0 Hn H39 Htb AI G Hroom HB Hcnt K).
- intros r c1 msv1 HQ Hp HC1 Hh1 _ HF1. cbn [cfg_model] in Hp.
pose proof (@twf_tpath _ _ _ _ _ _ _ _ _ Hspec Hp) as Hleaf.
destruct r as [|[r ps']]; [destruct Hleaf|]. cbn [fst snd] in Hleaf.
destruct Hleaf as (a' & g' & p & -> & Hleaf). cbn [epost fst snd] in HQ.
apply (HK p ps' c1 msv1 HQ); [exists a', g'; exact Hleaf| exact HC1| exact Hh1| exact (tpath_vmst LV _ _ _ _ _ (raw_malloc_A_tmm L n ps) Hp)| exact HF1].
Qed.

Theorem afree_vj_Fq (T : TSet) (X X' : list aptr) (p : aptr) (g : ghost) (ps : PStateA)
(Q : unit -> PStateA -> machine_state -> Prop) (c0 : config) (msv : machine_state) :
implMG segs (at_nodeA LV segs) (raw_free_A L p) ps Q (restrict F msv) ->
cinvA LV (cfg_ms c0) (cfg_model c0) ->
ainv X (ps_a ps) -> Permutation X (p :: X') ->
class_size kBatchClass * (tot X [] 0 (ps_a ps) kBatchClass + 17) <= kFreeArrayOffset ->
GS (ps_a ps) g -> CAPS + as_spent (ps_a ps) <= BUDGET -> KIx g (cfg_model c0) ->
0 <= q_bytes (as_gq (ps_a ps)) -> 0 <= q_bytes (as_tq (ps_a ps)) -> qroom (ps_a ps) p ->
(forall ps' c1 msv1,
evt segs (Q tt ps') (restrict F msv1) ->
(exists a' g', ps' = set_a a' ps /\ vm_onlyA (cfg_model c0) (cfg_model c1) /\ KIx g' (cfg_model c1) /\ GS a' g' /\
as_spent a' = as_spent (ps_a ps) /\ ainv X' a' /\
qtot a' <= qtot (ps_a ps) + aptr_used p + kBatchBytes) ->
cinvA LV (cfg_ms c1) (cfg_model c1) -> m_halted (cfg_model c1) = None ->
vmst (cfg_model c0) (cfg_model c1) ->
(forall x, F x = true -> ms_mem msv1 x = ms_mem msv x) ->
VJ LV (JS segs T) c1 msv1) ->
VJ LV (JS segs T) c0 msv.
Proof.
intros Himpl HC AI HP Hroom G HB K Hg0 Ht0 QR HK. destruct c0 as [ms0 mo0]. cbn [cfg_ms cfg_model] in *.
pose proof (raw_free_A_specQ X X' p g ps mo0 AI HP Hroom G HB K Hg0 Ht0 QR ps mo0 (conj eq_refl eq_refl)) as Hspec.
unfold implMG in Himpl.
eapply (impl_vj_F node segs LV Hwx Hsegs (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) (xinvA LV) is_spinA rvarA (jsome LV)
(jsome_stable LV) (nodesA_sound segs LV Hsegs Hsh Hbx Hbc) (JS segs T) (js_nclosed segs T) F F_off
(raw_free_A L p ps) _ (mkCfg ms0 mo0) msv Himpl HC).
- exact (raw_free_A_tcpsF segs L LV BUDGET PERM TOT0 N0 LL FR HFR X X' p g ps mo0 AI HP Hroom G HB K).
- intros r c1 msv1 HQ Hp HC1 Hh1 _ HF1. cbn [cfg_model] in Hp.
pose proof (@twf_tpath _ _ _ _ _ _ _ _ _ Hspec Hp) as Hleaf.
destruct r as [|[[] ps']]; [destruct Hleaf|]. cbn [fst snd] in Hleaf. cbn [epost fst snd] in HQ.
apply (HK ps' c1 msv1 HQ); [exact Hleaf| exact HC1| exact Hh1| exact (tpath_vmst LV _ _ _ _ _ (raw_free_A_tmm L p ps) Hp)| exact HF1].
Qed.

End RulesQ.
