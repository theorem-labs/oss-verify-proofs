(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Ent102PosA.v, with its module paths and module names changed; 30 of its 75 lines of code are new or changed. *)
(* omx-clap-core/fuzz_preset (both images; image-free): THE SUPPLY of the exact room position for the walk of
   LLVMFuzzerTestOneInput (design the lane's note, the internal file exact-pos-design.md, section 3). The walk
   is its callees' supplier of the kit's run premise `prh_run_at sm x os i evs`; at the call's entry it gets both the
   position and the run premise of the whole call from the interface pre's iface_room_at, with NO new interface
   conjunct:
   - ec_pos_extend: a position reads only the prefix `firstn i (hruns sm x os)`, so it holds over `os ++ os'` for any
     os' when i is at most the length of the earlier events (the cuts before check_no_overread state it over the
     earlier calls' grants, and it extends to whatever triple check_no_overread's readings take);
   - ec_supply_run: the run premise of the WHOLE call, for every grant triple, BY CONSTRUCTION
     (hruns sm x (os ++ [trip]) = hruns sm x os ++ call_evs sm x trip);
   - ec_run_split: a callee's premise at a cut, from the call's premise, by PRH_Base.prh_run_at_app_iff.
   rule 24: proves no function (kind: segment lemmas). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base PRH_FnCheck Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ec_hruns_app : forall sm x a b,
  PresetRun.hruns sm x (a ++ b) = PresetRun.hruns sm x a ++ PresetRun.hruns sm x b.
Proof. intros sm x a b. unfold PresetRun.hruns. rewrite map_app. apply concat_app. Qed.

Lemma ec_hruns_snoc : forall sm x os o1 o2 o0,
  PresetRun.hruns sm x (os ++ [(o1, o2, o0)]) = PresetRun.hruns sm x os ++ PresetRun.call_evs sm x o1 o2 o0.
Proof.
intros sm x os o1 o2 o0. rewrite ec_hruns_app, PresetRun.hruns_cons. cbn [PresetRun.hruns map concat].
rewrite app_nil_r. reflexivity.
Qed.

(* a position at an index within the earlier events extends to any later grants *)
Lemma ec_pos_extend : forall sm x os os' i H0 hist S,
  (i <= length (PresetRun.hruns sm x os))%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  PresetRoomPos.iface_room_pos sm x (os ++ os') i H0 hist S.
Proof.
intros sm x os os' i H0 hist S Hi H. unfold PresetRoomPos.iface_room_pos in *.
rewrite ec_hruns_app, firstn_app.
replace (i - length (PresetRun.hruns sm x os))%nat with 0%nat by lia.
rewrite firstn_O, app_nil_r. exact H.
Qed.

(* the run premise of the whole call, for every grant triple *)
Lemma ec_supply_run : forall sm x os o1 o2 o0,
  PRH_Base.prh_run_at sm x (os ++ [(o1, o2, o0)]) (length (PresetRun.hruns sm x os))
    (PresetRun.call_evs sm x o1 o2 o0).
Proof.
intros sm x os o1 o2 o0. unfold PRH_Base.prh_run_at. rewrite ec_hruns_snoc.
rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O. cbn [app].
apply firstn_all.
Qed.

(* a callee's premise at a cut: the call's premise split at the prefix the cut has consumed *)
Lemma ec_run_split : forall sm x os i pre evs rest,
  PRH_Base.prh_run_at sm x os i (pre ++ evs ++ rest) ->
  PRH_Base.prh_run_at sm x os (i + length pre) evs.
Proof.
intros sm x os i pre evs rest H.
apply (proj1 (PRH_Base.prh_run_at_app_iff sm x os i pre (evs ++ rest))) in H.
destruct H as [_ H].
apply (proj1 (PRH_Base.prh_run_at_app_iff sm x os (i + length pre) evs rest)) in H.
exact (proj1 H).
Qed.

(* the two arm equations of the call's events, under the size guard (n <= MAXB) *)
Lemma ec_call_evs_ranout_true : forall rc L PA (E : @Ent102CutsA.ecx rc L PA) trp,
  Z.of_nat (length (Ent102CutsA.e_x E)) <= PresetReqAt.MAXB -> Ent102CutsA.ec_ranout E trp = true ->
  Ent102CutsA.ec_call_evs E trp = Ent102CutsA.ec_cno_evs E trp.
Proof.
intros rc L PA E [[o1 o2] o0] Hn Hr. unfold Ent102CutsA.ec_ranout in Hr.
unfold Ent102CutsA.ec_call_evs, Ent102CutsA.ec_cno_evs, PresetRun.call_evs. cbv zeta.
rewrite (proj2 (Z.ltb_ge _ _) Hn).
destruct (PresetRun.ranout _ _ o1); [reflexivity|]. destruct (PresetRun.ranout _ _ o2); [reflexivity|].
destruct (PresetRun.ranout _ _ o0); [|discriminate]. rewrite app_nil_r. reflexivity.
Qed.

Lemma ec_call_evs_ranout_false : forall rc L PA (E : @Ent102CutsA.ecx rc L PA) trp,
  Z.of_nat (length (Ent102CutsA.e_x E)) <= PresetReqAt.MAXB -> Ent102CutsA.ec_ranout E trp = false ->
  Ent102CutsA.ec_call_evs E trp =
  Ent102CutsA.ec_cno_evs E trp ++ PresetRun.call_rest (Ent102CutsA.e_sm E) (Ent102CutsA.e_x E).
Proof.
intros rc L PA E [[o1 o2] o0] Hn Hr. unfold Ent102CutsA.ec_ranout in Hr.
apply Bool.orb_false_iff in Hr as [Hr H0]. apply Bool.orb_false_iff in Hr as [H1 H2].
unfold Ent102CutsA.ec_call_evs, Ent102CutsA.ec_cno_evs, PresetRun.call_evs. cbv zeta.
rewrite (proj2 (Z.ltb_ge _ _) Hn), H1, H2, H0. rewrite <- !app_assoc. reflexivity.
Qed.

(* the model's reading is ck_read under ec_pre's strtod tie (PjGrammar.json_read sm x = fst (jr_run sm x [])) *)
Lemma ec_rd_ck_read : forall rc L PA (E : @Ent102CutsA.ecx rc L PA),
  Ent102CutsA.e_sm E = ReaderRes.jr_strtod ->
  fst (PjGrammar.jr_run (Ent102CutsA.e_sm E) (Ent102CutsA.e_x E) []) = PRH_FnCheck.ck_read (Ent102CutsA.e_x E).
Proof. intros rc L PA E H. rewrite H. reflexivity. Qed.

Print Assumptions ec_rd_ck_read.
Print Assumptions ec_call_evs_ranout_true.
Print Assumptions ec_call_evs_ranout_false.
Print Assumptions ec_pos_extend.
Print Assumptions ec_supply_run.
Print Assumptions ec_run_split.
