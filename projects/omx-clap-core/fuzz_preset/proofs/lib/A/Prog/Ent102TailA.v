(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102TailA.v, with its module paths changed. *)
(* omx-clap-core/fuzz_preset (image-free; generic over the listing and the PAImg): THE ACCEPTED TAIL'S RUN PREMISES of
   the walk of LLVMFuzzerTestOneInput at the exact room position (lib/A/Ent102CutsA.v of record, the exact-position
   cuts). On the accepted arm (check_no_overread did not run out: ec_ranout E trp = false; the reading gave the tree t:
   ck_read (e_x E) = Some t) the model's events after the CNO piece, parse_noting's reading and expected()'s scratch
   are PresetRun.call_tail's accepted branch: round_trip t, the starved reading, the starved writes, pj_free (&doc).
   ec_tail_run states that window as the kit's prh_run_at at the cut index of cut_acc / cut_rm; ec_rt_run gives
   check_round_trip's entry premise (tcheck_round_trip_specX: prh_run_at .. (PresetReqAt.round_trip rp_sm t)) at
   cut_rm's index, and ec_crs1_run check_reject_clean_starved (.., &doc)'s (ck_crcs_evs at took = ck_ncalls x) at
   cut_crt's index, through the bridge ec_crcs1_evs (ck_crcs_evs .. = ec_rej E ++ ec_sw E t).
   The two facts the model needs of the entry are premises here, in the form ec_pre states them: the entry index
   (e_i0 E = length (hruns ..)) and the model's strtod is the reader's (e_sm E = ReaderRes.jr_strtod; a Theorem Labs lane's
   decision 17:59Z on a Theorem Labs lane's G4); a row takes both from ec_pre by type.
   SOURCES: lib/A/Ent102PosA.v (ec_supply_run, ec_call_evs_ranout_false), lib/A/PRH_Base.v prh_run_at_app_iff,
   lib/Spec/PresetRun.v call_rest / call_tail (the #102 model 5ac818ab1fe6), lib/A/PRH_FnCheck.v ck_crcs_evs /
   ck_read / ck_ncalls.
   rule 24: proves no function (kind: segment lemmas of the walk of LLVMFuzzerTestOneInput, rows LL5b / LL5c).
   NUMERALS: none but 0 (doc = 0 is the NULL tree argument). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnCheck Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Ent102PosA.
Import ListNotations.
Local Open Scope Z_scope.

Section T. Context {rc : YM05.RunCeil} {L : ptable asym} {PA : @PAImg rc L}.

(* the accepted tail's whole window, at cut_acc / cut_rm's index *)
Lemma ec_tail_run : forall (E : @ecx rc L PA) (trp : ec_trip) (t : jv),
  e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)) ->
  e_sm E = ReaderRes.jr_strtod ->
  Z.of_nat (length (e_x E)) <= EC_NMAX ->
  ec_ranout E trp = false ->
  ck_read (e_x E) = Some t ->
  prh_run_at (e_sm E) (e_x E) (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E))
    (ec_rt E t ++ ec_rej E ++ ec_sw E t ++ [PresetReqAt.HBulk (PresetReqAt.pj_frees (e_sm E) [] (e_x E))]).
Proof.
intros E [[o1 o2] o0] t Hi0 Hsm Hn Hr Ht.
pose proof (Ent102PosA.ec_supply_run (e_sm E) (e_x E) (e_os E) o1 o2 o0) as H.
rewrite <- Hi0 in H.
pose proof (Ent102PosA.ec_call_evs_ranout_false rc L PA E (o1, o2, o0)
  ltac:(unfold EC_NMAX in Hn; unfold PresetReqAt.MAXB; lia) Hr) as Hc.
unfold ec_call_evs in Hc. cbv beta iota zeta in Hc. rewrite Hc in H. clear Hc.
assert (Hjr : fst (PjGrammar.jr_run (e_sm E) (e_x E) []) = Some t) by (rewrite Hsm; exact Ht).
set (X := ec_rt E t ++ ec_rej E ++ ec_sw E t ++ [PresetReqAt.HBulk (PresetReqAt.pj_frees (e_sm E) [] (e_x E))]).
assert (Hrest : PresetRun.call_rest (e_sm E) (e_x E) = ec_pn E ++ ec_sc E ++ X).
{ unfold PresetRun.call_rest, PresetRun.call_tail. rewrite Hjr. reflexivity. }
rewrite Hrest in H.
replace (ec_cno_evs E (o1, o2, o0) ++ ec_pn E ++ ec_sc E ++ X)
  with ((ec_cno_evs E (o1, o2, o0) ++ ec_pn E ++ ec_sc E) ++ X) in H by (rewrite <- !app_assoc; reflexivity).
apply prh_run_at_app_iff in H as [_ H]. exact H.
Qed.

(* check_round_trip's entry premise at cut_rm's index *)
Lemma ec_rt_run : forall (E : @ecx rc L PA) (trp : ec_trip) (t : jv),
  e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)) ->
  e_sm E = ReaderRes.jr_strtod ->
  Z.of_nat (length (e_x E)) <= EC_NMAX ->
  ec_ranout E trp = false ->
  ck_read (e_x E) = Some t ->
  prh_run_at (e_sm E) (e_x E) (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E))
    (PresetReqAt.round_trip (e_sm E) t).
Proof.
intros E trp t Hi0 Hsm Hn Hr Ht.
pose proof (ec_tail_run E trp t Hi0 Hsm Hn Hr Ht) as H.
apply prh_run_at_app_iff in H as [H _]. exact H.
Qed.

(* check_reject_clean_starved (.., &doc)'s event list is the model's starved reading and writes *)
Lemma ec_crcs1_evs : forall (E : @ecx rc L PA) (t : jv) (doc : Z),
  e_sm E = ReaderRes.jr_strtod -> doc <> 0 ->
  ck_crcs_evs (e_sm E) (e_x E) (ck_ncalls (e_x E)) doc t = ec_rej E ++ ec_sw E t.
Proof.
intros E t doc Hsm Hd. unfold ck_crcs_evs, ec_rej, ec_sw, ck_ncalls.
rewrite (proj2 (Z.eqb_neq doc 0) Hd), Nat2Z.id, Hsm. reflexivity.
Qed.

(* its entry premise at cut_crt's index *)
Lemma ec_crs1_run : forall (E : @ecx rc L PA) (trp : ec_trip) (t : jv) (doc : Z),
  e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)) ->
  e_sm E = ReaderRes.jr_strtod ->
  Z.of_nat (length (e_x E)) <= EC_NMAX ->
  ec_ranout E trp = false ->
  ck_read (e_x E) = Some t -> doc <> 0 ->
  prh_run_at (e_sm E) (e_x E) (e_os E ++ [trp])
    (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rt E t))
    (ck_crcs_evs (e_sm E) (e_x E) (ck_ncalls (e_x E)) doc t).
Proof.
intros E trp t doc Hi0 Hsm Hn Hr Ht Hd.
pose proof (ec_tail_run E trp t Hi0 Hsm Hn Hr Ht) as H.
apply prh_run_at_app_iff in H as [_ H].
replace (ec_rej E ++ ec_sw E t ++ [PresetReqAt.HBulk (PresetReqAt.pj_frees (e_sm E) [] (e_x E))])
  with ((ec_rej E ++ ec_sw E t) ++ [PresetReqAt.HBulk (PresetReqAt.pj_frees (e_sm E) [] (e_x E))]) in H
  by (rewrite <- app_assoc; reflexivity).
apply prh_run_at_app_iff in H as [H _].
rewrite (ec_crcs1_evs E t doc Hsm Hd).
replace (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rt E t))%nat
  with (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E) + length (ec_rt E t))%nat
  by (rewrite !length_app; lia).
exact H.
Qed.
End T.

Print Assumptions ec_tail_run.
Print Assumptions ec_rt_run.
Print Assumptions ec_crs1_run.
