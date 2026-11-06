(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102Win.v, with its module paths changed; 28 of its 94 lines of code are new or changed and 1 line of the source is left out. *)
(* omx-clap-core/fuzz_preset (both images; IMAGE-FREE: lib/Spec and the kit's PRH_Base only): THE CONSUMER WINDOW of the
   walk of LLVMFuzzerTestOneInput, ONE shared lemma (owner's decision (A), 22:35Z). The batch kit's entry-keyed check texts
   (tcheck_round_trip_specX, tcheck_reject_clean_starved_specX) and the outcome clauses of its post-form texts
   (tparse_noting_specX, tcheck_as_written_specX) take `PRH_Base.prh_cons_from sm x os i k`: every ALLOCATION among
   the k events of the model run from position i is a consumer event (PresetRun.hcons true). In one call
   (PresetRun.call_evs x o1 o2 o0, appended to the run's earlier calls os), hcons is false exactly on check_no_overread's
   three P1 readings; so, when none of them ran out, EVERY position from the end of check_no_overread's piece
   (cno_part = the cut files' ec_cno_evs) to the end of the call is a consumer position, and the window holds for any
   i, k inside that range. Each LLVMF call site after cut_cno (parse_noting, check_as_written, check_round_trip,
   check_reject_clean_starved, pj_free) has its index there: e_i0 E = length (hruns (e_os E)) (ec_pre), the index is
   e_i0 E + length (ec_cno_evs E trp ++ ..), and ec_ranout E trp = false on the r = 0 path.
   The A' and B' walks cite it alike (sm := e_sm E, x := e_x E, os := e_os E, (o1, o2, o0) := trp).
   SATISFIABILITY (owner's VERIFY rule 1): prh_cons_from alone is witnessed at the real model values by a Theorem Labs lane's
   prh_cons_from_SAT (a working branch ef2d9b51785f, lib/A/zz_h8_cons.v blob 332a03a3ecc4: sm =
   jr_strtod, x = the bytes of {"a":1}, os = [(None, None, None)], i = 27, k = 10, with prh_run_at at the same window;
   negative control ctrl_P1_window_false); its JOINT satisfiability with the rest of each pre is carried by the walk's
   own witnesses (lib/A/Ent102SatA.v / lib/A/Prog/Ent102SatGA.v).
   rule 24: proves no function (kind: model lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base.
Import ListNotations.

Section W.
Variable sm : list Z -> Z * Z.

(* check_no_overread's piece of one call: call_evs up to its three frees, without call_rest - the body of the cut
   files' ec_cno_evs (Ent102CutsA.v / Ent102CutsB.v), so `ec_cno_evs E (o1, o2, o0) = cno_part (e_sm E) (e_x E) o1 o2 o0`
   by reflexivity (outside the section; destruct trp first) *)
Definition cno_part (x : list Z) (o1 o2 o0 : option nat) : list PresetReqAt.hev :=
  let n := Z.of_nat (length x) in
  let copy3 := [PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD);
                PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD)] in
  let free3 := [PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD);
                PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD)] in
  if (PresetReqAt.MAXB <? n)%Z then []
  else if PresetRun.ranout sm x o1 then copy3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ free3
  else if PresetRun.ranout sm x o2 then
    copy3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ PresetReqAt.parse_evs sm x (PresetRun.okof o2) ++
    PresetRun.p1_tfree sm x o1 ++ free3
  else
    copy3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ PresetReqAt.parse_evs sm x (PresetRun.okof o2) ++
    PresetReqAt.parse_evs sm x (PresetRun.okof o0) ++
    PresetRun.p1_tfree sm x o1 ++ PresetRun.p1_tfree sm x o2 ++ PresetRun.p1_tfree sm x o0 ++ free3.

Lemma hruns_snoc : forall x os o1 o2 o0,
  PresetRun.hruns sm x (os ++ [(o1, o2, o0)]) = PresetRun.hruns sm x os ++ PresetRun.call_evs sm x o1 o2 o0.
Proof. intros x os o1 o2 o0. unfold PresetRun.hruns. rewrite map_app, concat_app. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma hcons_snoc : forall x os o1 o2 o0,
  PresetRun.hcons sm x (os ++ [(o1, o2, o0)]) = PresetRun.hcons sm x os ++ PresetRun.call_cons sm x o1 o2 o0.
Proof. intros x os o1 o2 o0. unfold PresetRun.hcons. rewrite map_app, concat_app. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma nth_map_const : forall (A : Type) (b : bool) (l : list A) m d, (m < length l)%nat ->
  nth m (map (fun _ => b) l) d = b.
Proof.
  intros A b l. induction l as [|a l IH]; intros m d H; cbn in H; [lia|].
  destruct m as [|m]; cbn; [reflexivity|]. apply IH. lia.
Qed.

(* one call, none of its three readings ran out: every position of call_cons from the end of the cno piece on is
   true *)
Lemma call_cons_after_cno : forall x o1 o2 o0 m,
  (Z.of_nat (length x) <= PresetReqAt.MAXB)%Z ->
  PresetRun.ranout sm x o1 = false -> PresetRun.ranout sm x o2 = false -> PresetRun.ranout sm x o0 = false ->
  (length (cno_part x o1 o2 o0) <= m < length (PresetRun.call_evs sm x o1 o2 o0))%nat ->
  nth m (PresetRun.call_cons sm x o1 o2 o0) false = true.
Proof.
  intros x o1 o2 o0 m Hn H1 H2 H0 Hm.
  assert (HB : (PresetReqAt.MAXB <? Z.of_nat (length x))%Z = false) by (apply Z.ltb_ge; lia).
  unfold cno_part, PresetRun.call_evs in Hm. unfold PresetRun.call_cons. cbv zeta in *.
  rewrite HB, H1, H2, H0 in *. cbv iota in *. unfold PresetRun.flags.
  rewrite !length_app in Hm. cbn [length] in Hm.
  rewrite app_nth2 by (rewrite length_map; cbn [length]; lia). rewrite length_map. cbn [length].
  rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map.
  rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map.
  rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map.
  apply nth_map_const. rewrite !length_app. cbn [length]. lia.
Qed.

(* THE WINDOW: after check_no_overread's piece of the run's last call, when none of its readings ran out *)
Theorem cons_from_after_cno : forall x os o1 o2 o0 i k,
  (Z.of_nat (length x) <= PresetReqAt.MAXB)%Z ->
  PresetRun.ranout sm x o1 = false -> PresetRun.ranout sm x o2 = false -> PresetRun.ranout sm x o0 = false ->
  (length (PresetRun.hruns sm x os) + length (cno_part x o1 o2 o0) <= i)%nat ->
  (i + k <= length (PresetRun.hruns sm x (os ++ [(o1, o2, o0)])))%nat ->
  PRH_Base.prh_cons_from sm x (os ++ [(o1, o2, o0)]) i k.
Proof.
  intros x os o1 o2 o0 i k Hn H1 H2 H0 Hi Hk. unfold PRH_Base.prh_cons_from. intros j e Hj _.
  assert (Hc : nth (i + j) (PresetRun.hcons sm x (os ++ [(o1, o2, o0)])) false = true).
  { rewrite hruns_snoc, length_app in Hk. rewrite hcons_snoc.
    rewrite app_nth2 by (rewrite PresetRun.hcons_len; lia).
    rewrite PresetRun.hcons_len. apply call_cons_after_cno; [exact Hn | exact H1 | exact H2 | exact H0 | lia]. }
  destruct e; first [exact Hc | exact I].
Qed.


(* THE WINDOW AT A CUT, in the cut files' own terms (one copy for every row: LL4 / LL5b / LL5c and their B' twins;
   parent 02:0xZ): the cut files' ec_ranout E trp and ec_cno_evs E trp are, by conversion, ranout3 / cno_part3 at
   sm := e_sm E, x := e_x E, so a row applies it to its own E / trp without destructing trp. A call's events evs that
   the run holds at an index i after check_no_overread's piece are a consumer window (an empty evs is vacuous). *)
Definition ranout3 (x : list Z) (trp : option nat * option nat * option nat) : bool :=
  let '(o1, o2, o0) := trp in
  (PresetRun.ranout sm x o1 || PresetRun.ranout sm x o2 || PresetRun.ranout sm x o0)%bool.
Definition cno_part3 (x : list Z) (trp : option nat * option nat * option nat) : list PresetReqAt.hev :=
  let '(o1, o2, o0) := trp in cno_part x o1 o2 o0.

Lemma firstn_len_le : forall (A : Type) n (l : list A), length (firstn n l) = n -> (n <= length l)%nat.
Proof.
  intros A n. induction n as [|n IH]; intros [|a l] H; cbn [firstn length] in *; try lia.
  specialize (IH l ltac:(lia)). lia.
Qed.

Theorem cons_from_at_cut : forall x os trp i0 evs i,
  (Z.of_nat (length x) <= PresetReqAt.MAXB)%Z -> ranout3 x trp = false ->
  i0 = length (PresetRun.hruns sm x os) -> (i0 + length (cno_part3 x trp) <= i)%nat ->
  PRH_Base.prh_run_at sm x (os ++ [trp]) i evs ->
  PRH_Base.prh_cons_from sm x (os ++ [trp]) i (length evs).
Proof.
  intros x os [[o1 o2] o0] i0 evs i Hn Hro Hi0 Hi Hrun. cbn [ranout3 cno_part3] in *.
  apply orb_false_iff in Hro as [Hro Hr0]. apply orb_false_iff in Hro as [Hr1 Hr2].
  destruct evs as [|e0 evs'].
  - unfold PRH_Base.prh_cons_from. intros j e Hj. cbn in Hj. lia.
  - apply cons_from_after_cno; [exact Hn | exact Hr1 | exact Hr2 | exact Hr0 | rewrite <- Hi0; exact Hi |].
    unfold PRH_Base.prh_run_at in Hrun. apply (f_equal (@length _)) in Hrun. apply firstn_len_le in Hrun.
    rewrite length_skipn in Hrun.
    revert Hrun. cbn [length]. set (Lr := length (PresetRun.hruns sm x (os ++ [(o1, o2, o0)]))).
    intros Hm. change (S (length evs') <= Lr - i)%nat in Hm. clearbody Lr. lia.
Qed.
End W.

Print Assumptions cons_from_after_cno.
Print Assumptions cons_from_at_cut.
