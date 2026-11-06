(* fuzz_preset, kit: THE SUPPLY LEMMAS of the position sweep (the position census F7,
   the internal file CENSUS.md (the position census's record) table rows 5, 15-17, and :163-164). A text that makes run
   events states its OWN computed list as an entry premise (PRH_Base.prh_run_at); its caller holds the MODEL's list
   (lib/Spec/PresetReqAt.v). The lemmas here prove the two lists equal, so the caller's premise supplies the callee's.
   IMAGE-FREE: no image, no machine state, no allocator. Every statement is an equation over the pure models
   (WriterSpec, WriterApp, WriterValue, TxModel, PresetReqAt) and the kit's computed lists (PRH_FnWriter.prhWriter_evs /
   prhWriter_putN / prhWriter_k / prhWriter_pjw_evs, PRH_FnTx.prhtx_evs, PRH_FnCheck.ck_rtt_ns).
   ONE HOME: each lemma is stated here only. PRH_FnWriter.v keeps prhWriter_evs_failed and prhWriter_evs_app0 (the case
   ok = [] of prhWriter_evs_app below), PRH_FnTx.v keeps prhtx_evs_app; nothing here restates them. The generic facts
   are cited from their homes: YO0h.last_cons and YO0h.In_last (lib/Reusable/YO0h.v, whose closure is three list
   files and Stdlib), and PresetReqAtNoMiss.wcaps_pos (lib/Spec, the record blob f949715d7a12). A member of firstn is
   a member of the list: proved in place (three lines), NOT cited from YFhm.firstn_In - YFhm's Require chain reaches
   pin-dependent engine files (YF0x, YCeh) that fail on pins102, so citing it made this file unbuildable in every
   #102 closure (the kit owner's round-trip sub-walks, 2026-10-29). Same for YG06bcf.last_in_ne, replaced by
   YO0h.In_last (the same statement). tv_calls_tx_val and the size lemmas it uses
   (plen_cons, plen_wcomma, plen_wind, plen_spcs, plen_spcs_all, plen_strp) are TAKEN BY PATH from commit
   07b99cd9a99 lib/A/Prog/PReachEvs.v:679-716, each with its statement unchanged; this file
   is their one home in the kit.
   - (a) pj_write against the model. prhWriter_pjw_evs [] cnt fail (wdpieces t p) is PresetReqAt.w_evs t p when no
     call of the run is the chosen failure (prhWriter_pjw_evs_w_evs), and PresetReqAt.w_starved t p k when call k (from
     0) is (prhWriter_pjw_evs_w_starved). Both come from an induction over the pieces from any state that has not
     failed (prhWriter_evs0_chain, prhWriter_evs0_starved), which relates prhWriter_evs [] to
     chain cf_head c (grow_calls x c (piece_lens P)) for a text of length x and a capacity c. put1's counter is
     (w_cnt + 1) mod 2 ^ 64, so call j (from 0) of a run from g_count = cnt, 0 <= cnt < 2 ^ 64, sees
     (cnt + j) mod 2 ^ 64; the starved case states fail = cnt + k with cnt + k < 2 ^ 64 (no wrap).
   - (b) composition over outcome lists: prhWriter_evs / prhWriter_putN / prhWriter_k over P1 ++ P2, the outcomes split
     at prhWriter_k ok st P1 (the calls P1 consumes) (prhWriter_evs_app, prhWriter_putN_app, prhWriter_k_app, with
     prhWriter_k_cons); and under PRH_Base.prh_granted (no refusal) the outcomes' events and final state are the
     all-granted ones (prhWriter_granted; for pj_write, prhWriter_pjw_evs_granted).
   - (c) rendered() (round_trip_text's tx calls: tx_put "", tx_value, tx_put "\n" if pretty):
     prhtx_evs 0 0 (ck_rtt_ns t p) = PresetReqAt.r_evs t p (prhtx_evs_r_evs), from
     prhtx_evs len cap ks = chain 0 cap (tx_caps len cap ks) (prhtx_evs_chain: the raw realloc to 2 * need is the
     chain with no head) and TxModel.tv_calls t p d = PresetReqAt.tx_val p d t (tv_calls_tx_val). NO FINDING: the
     first empty put (tx_put "") is in both lists, and the two size lists agree on every tree.
   Nothing here is a function's proof (rule 24): segment lemmas. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base PRH_FnWriter PRH_FnTx PRH_FnCheck.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ (b) the writer's outcome lists *)

(* a failed writer stays as it is *)
Lemma sup_putN_failed : forall P ok st,
  WriterApp.w_failed st <> 0 -> PRH_FnWriter.prhWriter_putN ok st P = st.
Proof.
  induction P as [|b P IH]; intros ok st H; [reflexivity|]. cbn [PRH_FnWriter.prhWriter_putN].
  assert (G : PRH_FnWriter.prhWriter_grows st b = false).
  { unfold PRH_FnWriter.prhWriter_grows. apply andb_false_intro1. apply Z.eqb_neq. exact H. }
  assert (E : WriterApp.put1 st b = st).
  { unfold WriterApp.put1. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. }
  rewrite G, E. apply IH. exact H.
Qed.

(* a growing put appends its new capacity to the calls, whatever its outcome *)
Lemma sup_put1_calls : forall okb st b, PRH_FnWriter.prhWriter_grows st b = true ->
  WriterApp.w_calls (PRH_FnWriter.prhWriter_put1 okb st b) =
    WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (PRH_FnWriter.prhWriter_need st b)].
Proof.
  intros okb st b G. unfold PRH_FnWriter.prhWriter_put1. rewrite G.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [reflexivity|]. destruct okb; reflexivity.
Qed.

(* a put that does not grow keeps the calls and the counters *)
Lemma sup_put1_keep : forall st b, PRH_FnWriter.prhWriter_grows st b = false ->
  WriterApp.w_calls (WriterApp.put1 st b) = WriterApp.w_calls st /\
  WriterApp.w_cnt (WriterApp.put1 st b) = WriterApp.w_cnt st /\
  WriterApp.w_fail (WriterApp.put1 st b) = WriterApp.w_fail st.
Proof.
  intros st b G. unfold PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need in G. unfold WriterApp.put1.
  destruct (WriterApp.w_failed st =? 0) eqn:F.
  - cbn [andb negb] in *. apply Z.ltb_ge in G. rewrite (proj2 (Z.leb_le _ _) G).
    split; [reflexivity | split; reflexivity].
  - cbn [negb]. split; [reflexivity | split; reflexivity].
Qed.

Lemma sup_putN_calls : forall P ok st, exists L,
  WriterApp.w_calls (PRH_FnWriter.prhWriter_putN ok st P) = WriterApp.w_calls st ++ L.
Proof.
  induction P as [|b P IH]; intros ok st; cbn [PRH_FnWriter.prhWriter_putN].
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (PRH_FnWriter.prhWriter_grows st b) eqn:G; cbv beta iota.
    + destruct (IH (tl ok) (PRH_FnWriter.prhWriter_put1 (hd true ok) st b)) as [L E].
      rewrite sup_put1_calls in E by exact G. rewrite <- app_assoc in E. eexists. exact E.
    + destruct (IH ok (WriterApp.put1 st b)) as [L E]. rewrite (proj1 (sup_put1_keep st b G)) in E.
      exists L. exact E.
Qed.

Lemma sup_k_calls : forall ok st P L,
  WriterApp.w_calls (PRH_FnWriter.prhWriter_putN ok st P) = WriterApp.w_calls st ++ L ->
  PRH_FnWriter.prhWriter_k ok st P = length L.
Proof.
  intros ok st P L E. unfold PRH_FnWriter.prhWriter_k. rewrite E, length_app. lia.
Qed.

(* prhWriter_k one put at a time: a growing put consumes one outcome *)
Lemma prhWriter_k_cons : forall ok st b P,
  PRH_FnWriter.prhWriter_k ok st (b :: P) =
    if PRH_FnWriter.prhWriter_grows st b
    then S (PRH_FnWriter.prhWriter_k (tl ok) (PRH_FnWriter.prhWriter_put1 (hd true ok) st b) P)
    else PRH_FnWriter.prhWriter_k ok (WriterApp.put1 st b) P.
Proof.
  intros ok st b P. unfold PRH_FnWriter.prhWriter_k. cbn [PRH_FnWriter.prhWriter_putN].
  destruct (PRH_FnWriter.prhWriter_grows st b) eqn:G; cbv beta iota.
  - destruct (sup_putN_calls P (tl ok) (PRH_FnWriter.prhWriter_put1 (hd true ok) st b)) as [L E].
    rewrite E, sup_put1_calls by exact G. rewrite !length_app. cbn [length]. lia.
  - rewrite (proj1 (sup_put1_keep st b G)). reflexivity.
Qed.

(* THE COMPOSITION a caller that runs P1 then P2 needs: the state, the calls and the events over P1 ++ P2 under the
   outcomes ok, P2's outcomes being ok past the prhWriter_k ok st P1 calls P1 consumed *)
Lemma prhWriter_putN_app : forall P1 P2 ok st,
  PRH_FnWriter.prhWriter_putN ok st (P1 ++ P2) =
    PRH_FnWriter.prhWriter_putN (skipn (PRH_FnWriter.prhWriter_k ok st P1) ok)
      (PRH_FnWriter.prhWriter_putN ok st P1) P2.
Proof.
  induction P1 as [|b P1 IH]; intros P2 ok st.
  - unfold PRH_FnWriter.prhWriter_k. cbn [app PRH_FnWriter.prhWriter_putN]. rewrite Nat.sub_diag. reflexivity.
  - rewrite prhWriter_k_cons. cbn [app PRH_FnWriter.prhWriter_putN].
    destruct (PRH_FnWriter.prhWriter_grows st b); cbv beta iota; rewrite IH; [|reflexivity].
    destruct ok as [|o ok]; cbn [tl skipn]; [rewrite !skipn_nil|]; reflexivity.
Qed.

Lemma prhWriter_k_app : forall P1 P2 ok st,
  PRH_FnWriter.prhWriter_k ok st (P1 ++ P2) =
    (PRH_FnWriter.prhWriter_k ok st P1 +
     PRH_FnWriter.prhWriter_k (skipn (PRH_FnWriter.prhWriter_k ok st P1) ok)
       (PRH_FnWriter.prhWriter_putN ok st P1) P2)%nat.
Proof.
  intros P1 P2 ok st.
  destruct (sup_putN_calls P1 ok st) as [L1 E1].
  destruct (sup_putN_calls P2 (skipn (PRH_FnWriter.prhWriter_k ok st P1) ok) (PRH_FnWriter.prhWriter_putN ok st P1))
    as [L2 E2].
  assert (E12 : WriterApp.w_calls (PRH_FnWriter.prhWriter_putN ok st (P1 ++ P2)) = WriterApp.w_calls st ++ L1 ++ L2).
  { rewrite prhWriter_putN_app, E2, E1, <- app_assoc. reflexivity. }
  rewrite (sup_k_calls _ _ _ _ E12), (sup_k_calls _ _ _ _ E2), (sup_k_calls _ _ _ _ E1), length_app.
  reflexivity.
Qed.

Lemma prhWriter_evs_app {cp : YGcfNames.CfParams} : forall P1 P2 ok st,
  PRH_FnWriter.prhWriter_evs ok st (P1 ++ P2) =
    PRH_FnWriter.prhWriter_evs ok st P1 ++
    PRH_FnWriter.prhWriter_evs (skipn (PRH_FnWriter.prhWriter_k ok st P1) ok)
      (PRH_FnWriter.prhWriter_putN ok st P1) P2.
Proof.
  induction P1 as [|b P1 IH]; intros P2 ok st.
  - unfold PRH_FnWriter.prhWriter_k. cbn [app PRH_FnWriter.prhWriter_evs PRH_FnWriter.prhWriter_putN].
    rewrite Nat.sub_diag. reflexivity.
  - rewrite prhWriter_k_cons. cbn [app PRH_FnWriter.prhWriter_evs PRH_FnWriter.prhWriter_putN].
    destruct (PRH_FnWriter.prhWriter_grows st b); cbv beta iota; rewrite IH; [|reflexivity].
    rewrite <- app_assoc. destruct ok as [|o ok]; cbn [tl skipn]; [rewrite !skipn_nil|]; reflexivity.
Qed.

(* NO REFUSAL (PRH_Base.prh_granted over the calls the run makes): the events and the final state under the outcomes
   ok are the all-granted ones. A false outcome is then the chosen failure, which the writer takes by its own counter
   whatever the outcome; 0 <= g_count and g_fail_at < 2 ^ 64 (prh_ledger_bounds) make cnt + i = fail the counter's
   own (cnt + i) mod 2 ^ 64 = fail. *)
Lemma prhWriter_granted {cp : YGcfNames.CfParams} : forall P ok st,
  0 <= WriterApp.w_cnt st -> WriterApp.w_fail st < 2 ^ 64 ->
  PRH_Base.prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (PRH_FnWriter.prhWriter_k ok st P) ->
  PRH_FnWriter.prhWriter_evs ok st P = PRH_FnWriter.prhWriter_evs [] st P /\
  PRH_FnWriter.prhWriter_putN ok st P = PRH_FnWriter.prhWriter_putN [] st P.
Proof.
  assert (HM : 0 < 2 ^ 64) by (apply Z.pow_pos_nonneg; lia).
  induction P as [|b P IH]; intros ok st H0 HF G; [split; reflexivity|].
  rewrite prhWriter_k_cons in G. unfold PRH_Base.prh_granted in G.
  cbn [PRH_FnWriter.prhWriter_evs PRH_FnWriter.prhWriter_putN].
  destruct (PRH_FnWriter.prhWriter_grows st b) eqn:Gr; cbv beta iota in G |- *.
  - cbn [hd tl].
    destruct (WriterApp.w_cnt st =? WriterApp.w_fail st) eqn:E.
    + (* the chosen failure: every outcome gives the same failed state *)
      assert (Hs : forall okb, PRH_FnWriter.prhWriter_put1 okb st b = PRH_FnWriter.prhWriter_put1 true st b).
      { intro okb. unfold PRH_FnWriter.prhWriter_put1. rewrite Gr, E. reflexivity. }
      assert (Hf : WriterApp.w_failed (PRH_FnWriter.prhWriter_put1 true st b) <> 0).
      { unfold PRH_FnWriter.prhWriter_put1. rewrite Gr, E. cbn [WriterApp.w_failed]. lia. }
      rewrite (Hs (hd true ok)). cbn [orb app].
      rewrite !PRH_FnWriter.prhWriter_evs_failed by exact Hf. rewrite !sup_putN_failed by exact Hf.
      split; reflexivity.
    + destruct ok as [|o ok]; [split; reflexivity|]. cbn [hd tl] in *. destruct o.
      * set (st1 := PRH_FnWriter.prhWriter_put1 true st b) in *.
        assert (C : WriterApp.w_cnt st1 = (WriterApp.w_cnt st + 1) mod 2 ^ 64 /\
                    WriterApp.w_fail st1 = WriterApp.w_fail st).
        { unfold st1, PRH_FnWriter.prhWriter_put1. rewrite Gr, E. split; reflexivity. }
        destruct C as [C1 C2].
        destruct (IH ok st1) as [E1 E2].
        -- rewrite C1. apply Z.mod_pos_bound. exact HM.
        -- rewrite C2. exact HF.
        -- unfold PRH_Base.prh_granted. intros i Hi Hn. rewrite C1, C2.
           pose proof (G (S i) ltac:(lia) Hn) as Gi.
           rewrite Z.mod_small by lia. lia.
        -- rewrite E1, E2. split; reflexivity.
      * (* a refusal that is not the chosen failure: excluded *)
        exfalso. pose proof (G 0%nat ltac:(lia) eq_refl) as G0. apply Z.eqb_neq in E. lia.
  - destruct (sup_put1_keep st b Gr) as (_ & K1 & K2).
    destruct (IH ok (WriterApp.put1 st b)) as [E1 E2].
    + rewrite K1. exact H0.
    + rewrite K2. exact HF.
    + unfold PRH_Base.prh_granted. rewrite K1, K2. exact G.
    + split; [exact E1 | exact E2].
Qed.

Lemma prhWriter_pjw_evs_granted {cp : YGcfNames.CfParams} : forall P ok cnt fail,
  0 <= cnt -> fail < 2 ^ 64 ->
  PRH_Base.prh_granted ok cnt fail (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) P) ->
  PRH_FnWriter.prhWriter_pjw_evs ok cnt fail P = PRH_FnWriter.prhWriter_pjw_evs [] cnt fail P.
Proof.
  intros P ok cnt fail H0 HF G.
  destruct (prhWriter_granted P ok (WriterApp.w0 cnt fail) H0 HF G) as [E1 E2].
  unfold PRH_FnWriter.prhWriter_pjw_evs. cbv zeta. rewrite E1, E2. reflexivity.
Qed.

(* ================================================================ (a) pj_write against the model *)

(* NO CHOSEN FAILURE among the run's calls: from a writer that has not failed, with text txt and capacity c, the
   all-granted run of P makes the realloc chain of grow_calls, and leaves the text extended, the capacity grow_cap,
   the counter advanced by the number of calls (mod 2 ^ 64) and the calls extended *)
Lemma prhWriter_evs0_chain {cp : YGcfNames.CfParams} : forall P txt c cnt fail calls,
  0 <= cnt < 2 ^ 64 ->
  (forall j, (j < length (WriterSpec.grow_calls (Z.of_nat (length txt)) c (WriterSpec.piece_lens P)))%nat ->
     (cnt + Z.of_nat j) mod 2 ^ 64 <> fail) ->
  PRH_FnWriter.prhWriter_evs [] (WriterApp.mkW 0 txt c cnt fail calls) P =
    PresetReqAt.chain YGcfNames.cf_head c
      (WriterSpec.grow_calls (Z.of_nat (length txt)) c (WriterSpec.piece_lens P)) /\
  PRH_FnWriter.prhWriter_putN [] (WriterApp.mkW 0 txt c cnt fail calls) P =
    WriterApp.mkW 0 (txt ++ concat P)
      (WriterSpec.grow_cap (Z.of_nat (length txt)) c (WriterSpec.piece_lens P))
      ((cnt + Z.of_nat (length (WriterSpec.grow_calls (Z.of_nat (length txt)) c (WriterSpec.piece_lens P))))
         mod 2 ^ 64)
      fail (calls ++ WriterSpec.grow_calls (Z.of_nat (length txt)) c (WriterSpec.piece_lens P)).
Proof.
  assert (HM : 0 < 2 ^ 64) by (apply Z.pow_pos_nonneg; lia).
  induction P as [|b P IH]; intros txt c cnt fail calls Hc Hn.
  - cbn [PRH_FnWriter.prhWriter_evs PRH_FnWriter.prhWriter_putN WriterSpec.piece_lens map WriterSpec.grow_calls
         WriterSpec.grow_cap concat length Z.of_nat].
    split; [reflexivity|]. rewrite !app_nil_r, Z.add_0_r, Z.mod_small by exact Hc. reflexivity.
  - change (WriterSpec.piece_lens (b :: P)) with (Z.of_nat (length b) :: WriterSpec.piece_lens P) in Hn |- *.
    cbn [WriterSpec.grow_calls WriterSpec.grow_cap] in Hn |- *.
    cbn [PRH_FnWriter.prhWriter_evs PRH_FnWriter.prhWriter_putN hd tl].
    unfold PRH_FnWriter.prhWriter_put1, PRH_FnWriter.prhWriter_ev, PRH_FnWriter.prhWriter_grows,
      PRH_FnWriter.prhWriter_need, WriterApp.put1.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls
         Z.eqb andb negb].
    destruct (c <? Z.of_nat (length txt) + Z.of_nat (length b) + 1) eqn:G; cbv beta iota in Hn.
    + (* the put grows: call 0 of the run *)
      pose proof (Hn 0%nat ltac:(cbn [length]; lia)) as H0. cbn [Z.of_nat] in H0.
      rewrite Z.add_0_r, Z.mod_small in H0 by exact Hc. apply Z.eqb_neq in H0. rewrite H0.
      cbn [orb negb app PresetReqAt.chain concat length].
      destruct (IH (txt ++ b) (WriterSpec.newcap c (Z.of_nat (length txt) + Z.of_nat (length b) + 1))
                  ((cnt + 1) mod 2 ^ 64) fail
                  (calls ++ [WriterSpec.newcap c (Z.of_nat (length txt) + Z.of_nat (length b) + 1)]))
        as [E1 E2].
      * apply Z.mod_pos_bound. exact HM.
      * intros j Hj. rewrite length_app, Nat2Z.inj_add in Hj. rewrite Zplus_mod_idemp_l.
        pose proof (Hn (S j) ltac:(cbn [length]; lia)) as Hs.
        replace (cnt + 1 + Z.of_nat j) with (cnt + Z.of_nat (S j)) by lia. exact Hs.
      * rewrite length_app, Nat2Z.inj_add in E1, E2. rewrite E1, E2. split; [reflexivity|].
        rewrite <- !app_assoc, Zplus_mod_idemp_l. cbn [app].
        assert (Hs : forall n : nat, cnt + 1 + Z.of_nat n = cnt + Z.of_nat (S n)) by lia.
        rewrite Hs. reflexivity.
    + (* the put fits: no call *)
      assert (G' : (Z.of_nat (length txt) + Z.of_nat (length b) + 1 <=? c) = true).
      { apply Z.leb_le. apply Z.ltb_ge in G. lia. }
      rewrite G'. cbv beta iota.
      destruct (IH (txt ++ b) c cnt fail calls Hc) as [E1 E2].
      * intros j Hj. rewrite length_app, Nat2Z.inj_add in Hj. exact (Hn j Hj).
      * rewrite length_app, Nat2Z.inj_add in E1, E2. rewrite <- app_assoc in E2. rewrite E1, E2.
        cbn [concat]. split; reflexivity.
Qed.

(* CALL k (from 0) IS THE CHOSEN FAILURE, fail = cnt + k with no wrap: the run makes the first k reallocs of the
   chain, then fails at call k (failed = 1, the capacity of the k-th grow, or c if k = 0) and makes nothing more *)
Lemma prhWriter_evs0_starved {cp : YGcfNames.CfParams} : forall P txt c cnt fail calls k,
  0 <= cnt -> fail = cnt + Z.of_nat k -> fail < 2 ^ 64 ->
  (k < length (WriterSpec.grow_calls (Z.of_nat (length txt)) c (WriterSpec.piece_lens P)))%nat ->
  PRH_FnWriter.prhWriter_evs [] (WriterApp.mkW 0 txt c cnt fail calls) P =
    PresetReqAt.chain YGcfNames.cf_head c
      (firstn k (WriterSpec.grow_calls (Z.of_nat (length txt)) c (WriterSpec.piece_lens P))) /\
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN [] (WriterApp.mkW 0 txt c cnt fail calls) P) = 1 /\
  WriterApp.w_cap (PRH_FnWriter.prhWriter_putN [] (WriterApp.mkW 0 txt c cnt fail calls) P) =
    last (firstn k (WriterSpec.grow_calls (Z.of_nat (length txt)) c (WriterSpec.piece_lens P))) c.
Proof.
  assert (HM : 0 < 2 ^ 64) by (apply Z.pow_pos_nonneg; lia).
  induction P as [|b P IH]; intros txt c cnt fail calls k H0 Hf HfM Hk.
  - cbn [WriterSpec.piece_lens map WriterSpec.grow_calls length] in Hk. lia.
  - change (WriterSpec.piece_lens (b :: P)) with (Z.of_nat (length b) :: WriterSpec.piece_lens P) in Hk |- *.
    cbn [WriterSpec.grow_calls] in Hk |- *.
    cbn [PRH_FnWriter.prhWriter_evs PRH_FnWriter.prhWriter_putN hd tl].
    unfold PRH_FnWriter.prhWriter_put1, PRH_FnWriter.prhWriter_ev, PRH_FnWriter.prhWriter_grows,
      PRH_FnWriter.prhWriter_need, WriterApp.put1.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls
         Z.eqb andb negb].
    destruct (c <? Z.of_nat (length txt) + Z.of_nat (length b) + 1) eqn:G; cbv beta iota in Hk.
    + destruct k as [|k].
      * (* call 0 is the chosen failure *)
        cbn [Z.of_nat] in Hf. rewrite Z.add_0_r in Hf. subst fail. rewrite Z.eqb_refl. cbn [orb app firstn].
        assert (Hf : WriterApp.w_failed
                       (WriterApp.mkW 1 txt c ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1)
                          (calls ++ [WriterSpec.newcap c (Z.of_nat (length txt) + Z.of_nat (length b) + 1)]))
                     <> 0) by (cbn [WriterApp.w_failed]; lia).
        rewrite PRH_FnWriter.prhWriter_evs_failed by exact Hf. rewrite sup_putN_failed by exact Hf.
        cbn [WriterApp.w_failed WriterApp.w_cap PresetReqAt.chain last].
        split; [reflexivity | split; reflexivity].
      * (* a call after call 0 *)
        assert (Hne : (cnt =? fail) = false) by (apply Z.eqb_neq; lia).
        rewrite Hne. cbn [orb negb app firstn PresetReqAt.chain].
        rewrite (Z.mod_small (cnt + 1)) by lia.
        cbn [length] in Hk.
        destruct (IH (txt ++ b) (WriterSpec.newcap c (Z.of_nat (length txt) + Z.of_nat (length b) + 1))
                    (cnt + 1) fail
                    (calls ++ [WriterSpec.newcap c (Z.of_nat (length txt) + Z.of_nat (length b) + 1)]) k)
          as (E1 & E2 & E3).
        -- lia.
        -- lia.
        -- exact HfM.
        -- rewrite length_app, Nat2Z.inj_add. lia.
        -- rewrite length_app, Nat2Z.inj_add in E1, E3. rewrite E1, E2, E3, YO0h.last_cons.
           split; [reflexivity | split; reflexivity].
    + assert (G' : (Z.of_nat (length txt) + Z.of_nat (length b) + 1 <=? c) = true).
      { apply Z.leb_le. apply Z.ltb_ge in G. lia. }
      rewrite G'. cbv beta iota.
      destruct (IH (txt ++ b) c cnt fail calls k H0 Hf HfM) as (E1 & E2 & E3).
      * rewrite length_app, Nat2Z.inj_add. exact Hk.
      * rewrite length_app, Nat2Z.inj_add in E1, E3. rewrite E1, E2, E3.
        split; [reflexivity | split; reflexivity].
Qed.

(* THE SUPPLY OF tpj_write_specX's ENTRY PREMISE, no chosen failure among pj_write's calls: its list is the model's
   PresetReqAt.w_evs t p. The condition is exactly "fail is none of the counters the run's calls see",
   cnt, (cnt + 1) mod 2 ^ 64, .., (cnt + wcalls t p - 1) mod 2 ^ 64 (g_count a size_t, prh_ledger_bounds). *)
Lemma prhWriter_pjw_evs_w_evs {cp : YGcfNames.CfParams} : forall t p cnt fail,
  YGcfNames.cf_head = PresetReqAt.HEAD -> 0 <= cnt < 2 ^ 64 ->
  (forall j, (j < PresetReqAt.wcalls t p)%nat -> (cnt + Z.of_nat j) mod 2 ^ 64 <> fail) ->
  PRH_FnWriter.prhWriter_pjw_evs [] cnt fail (WriterValue.wdpieces t p) = PresetReqAt.w_evs t p.
Proof.
  intros t p cnt fail Hh Hc Hn. unfold PresetReqAt.wcalls, PresetReqAt.wcaps in Hn.
  unfold PRH_FnWriter.prhWriter_pjw_evs, PresetReqAt.w_evs, PresetReqAt.wcaps, WriterApp.w0. cbv zeta.
  destruct (prhWriter_evs0_chain (WriterValue.wdpieces t p) [] 0 cnt fail [] Hc Hn) as [E1 E2].
  rewrite E1, E2. cbn [WriterApp.w_failed Z.eqb orb]. rewrite app_nil_r, Hh. reflexivity.
Qed.

(* THE SUPPLY OF tpj_write_specX's ENTRY PREMISE for check_reject_clean_starved's starved write: call k (from 0) is
   the chosen failure, fail = cnt + k, with the no-wrap side condition fail < 2 ^ 64 (and 0 <= cnt); its list is the
   model's PresetReqAt.w_starved t p k: the first k reallocs, then fuzz_free (buf) if k > 0 *)
Lemma prhWriter_pjw_evs_w_starved {cp : YGcfNames.CfParams} : forall t p cnt fail k,
  YGcfNames.cf_head = PresetReqAt.HEAD -> 0 <= cnt -> fail = cnt + Z.of_nat k -> fail < 2 ^ 64 ->
  (k < PresetReqAt.wcalls t p)%nat ->
  PRH_FnWriter.prhWriter_pjw_evs [] cnt fail (WriterValue.wdpieces t p) = PresetReqAt.w_starved t p k.
Proof.
  intros t p cnt fail k Hh H0 Hf HfM Hk. unfold PresetReqAt.wcalls, PresetReqAt.wcaps in Hk.
  unfold PRH_FnWriter.prhWriter_pjw_evs, PresetReqAt.w_starved, PresetReqAt.wcaps, WriterApp.w0. cbv zeta.
  destruct (prhWriter_evs0_starved (WriterValue.wdpieces t p) [] 0 cnt fail [] k H0 Hf HfM Hk) as (E1 & E2 & E3).
  change (Z.of_nat (length (@nil Z))) with 0 in E1, E2, E3.
  rewrite E1, E2, E3, Hh. cbn [Z.eqb orb].
  destruct k as [|k]; [reflexivity|].
  assert (Hpos : 0 < last (firstn (S k) (PresetReqAt.wcaps t p)) 0).
  { pose proof (PresetReqAtNoMiss.wcaps_pos t p) as Hall. rewrite Forall_forall in Hall. apply Hall.
    assert (HF : forall (l : list Z) x, In x (firstn (S k) l) -> In x l).
    { intros l x Hx. rewrite <- (firstn_skipn (S k) l). apply in_or_app. left. exact Hx. }
    apply HF. apply YO0h.In_last. intro F. apply (f_equal (@length Z)) in F.
    rewrite length_firstn in F. cbn [length] in F. unfold PresetReqAt.wcaps in F. lia. }
  unfold PresetReqAt.wcaps in Hpos.
  assert (Hz : (last (firstn (S k) (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces t p))))
                  0 =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hz. reflexivity.
Qed.

(* ================================================================ (c) rendered() against the model *)

(* tx_put's raw realloc to 2 * need is the chain with no head *)
Lemma prhtx_evs_chain : forall ks len cap,
  PRH_FnTx.prhtx_evs len cap ks = PresetReqAt.chain 0 cap (PresetReqAt.tx_caps len cap ks).
Proof.
  induction ks as [|k ks IH]; intros len cap; [reflexivity|].
  cbn [PRH_FnTx.prhtx_evs PresetReqAt.tx_caps]. unfold TxModel.tx_cap1.
  destruct (Z.leb_spec (len + k + 1) cap) as [L|L].
  - rewrite (proj2 (Z.ltb_ge _ _) L). cbn [app]. apply IH.
  - rewrite (proj2 (Z.ltb_lt _ _) L). cbn [app PresetReqAt.chain]. unfold PRH_FnTx.prhtx_ev.
    rewrite IH, !Z.add_0_r. replace (2 * (len + k + 1)) with ((len + k + 1) * 2) by lia. reflexivity.
Qed.

(* plen_cons .. plen_strp and tv_calls_tx_val: taken by path from commit 07b99cd9a99
   lib/A/Prog/PReachEvs.v:679-716 (statements unchanged; TM = TxModel, WV = WriterValue, RA = PresetReqAt) *)
Lemma plen_cons : forall a P, TxModel.plen (a :: P) = Z.of_nat (length a) :: TxModel.plen P.
Proof. reflexivity. Qed.

Lemma plen_wcomma : forall i, TxModel.plen (WriterValue.wcomma i) = if Nat.eqb i 0 then [] else [1].
Proof. intros [|i]; reflexivity. Qed.

Lemma plen_wind : forall p d,
  TxModel.plen (WriterValue.wind p (Z.of_nat d)) = if p then PresetReqAt.tx_line d else [].
Proof.
  intros p d. unfold WriterValue.wind, PresetReqAt.tx_line. destruct p; [|reflexivity].
  rewrite Nat2Z.id. unfold TxModel.plen. rewrite map_cons, map_repeat. reflexivity.
Qed.

Lemma plen_spcs : forall c, TxModel.plen (TxModel.spcs c) = PresetReqAt.tx_ch c.
Proof.
  intro c. unfold TxModel.spcs, PresetReqAt.tx_ch, WriterSpec.special, WriterSpec.esc.
  destruct ((c =? 34) || (c =? 92)) eqn:E; [reflexivity|].
  apply orb_false_iff in E as [E1 E2]. rewrite E1, E2. cbn [orb].
  destruct (c <? 32) eqn:L.
  - rewrite (proj2 (Z.leb_gt 32 c) (proj1 (Z.ltb_lt c 32) L)).
    destruct (c =? 10); [reflexivity|]. destruct (c =? 9); [reflexivity|]. destruct (c =? 13); reflexivity.
  - rewrite (proj2 (Z.leb_le 32 c) (proj1 (Z.ltb_ge c 32) L)). reflexivity.
Qed.

Lemma plen_spcs_all : forall s, TxModel.plen (concat (map TxModel.spcs s)) = flat_map PresetReqAt.tx_ch s.
Proof.
  induction s as [|c s IH]; [reflexivity|]. cbn [map concat flat_map].
  rewrite TxModel.plen_app, IH, plen_spcs. reflexivity.
Qed.

Lemma plen_strp : forall s, TxModel.plen (TxModel.strp s) = PresetReqAt.tx_str s.
Proof.
  intros s. unfold TxModel.strp, PresetReqAt.tx_str. rewrite plen_cons, TxModel.plen_app, plen_spcs_all.
  reflexivity.
Qed.

(* the sizes of tx_value's tx_put calls, TxModel's (the texts' list) and the model's *)
Theorem tv_calls_tx_val : forall t p d, TxModel.tv_calls t p (Z.of_nat d) = PresetReqAt.tx_val p d t.
Proof.
  unfold TxModel.tv_calls.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using PjTree.jv_ind'; intros p d.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [TxModel.tvp PresetReqAt.tx_val]. apply plen_strp.
  - cbn [TxModel.tvp PresetReqAt.tx_val]. rewrite plen_cons, !TxModel.plen_app.
    match goal with
    | |- _ :: TxModel.plen (?G 0%nat items) ++ TxModel.plen ?M1 ++ _ = _ :: ?G' 0%nat items ++ ?M2 ++ _ =>
        assert (K1 : forall i, TxModel.plen (G i items) = G' i items);
        [| assert (K2 : TxModel.plen M1 = M2); [| rewrite K1, K2; reflexivity]]
    end.
    + revert IH. induction items as [|u r IHr]; intros IH i; [reflexivity|].
      inversion IH as [|? ? Hu Hr]; subst. cbv beta iota.
      rewrite !TxModel.plen_app, (IHr Hr (S i)).
      replace (Z.of_nat d + 1) with (Z.of_nat (S d)) by lia.
      rewrite plen_wcomma, plen_wind, (Hu p (S d)). reflexivity.
    + destruct items; [reflexivity|]. apply plen_wind.
  - cbn [TxModel.tvp PresetReqAt.tx_val]. rewrite plen_cons, !TxModel.plen_app.
    match goal with
    | |- _ :: TxModel.plen (?G 0%nat ms) ++ TxModel.plen ?M1 ++ _ = _ :: ?G' 0%nat ms ++ ?M2 ++ _ =>
        assert (K1 : forall i, TxModel.plen (G i ms) = G' i ms);
        [| assert (K2 : TxModel.plen M1 = M2); [| rewrite K1, K2; reflexivity]]
    end.
    + revert IH. induction ms as [|[k u] r IHr]; intros IH i; [reflexivity|].
      inversion IH as [|? ? Hu Hr]; subst. cbn [snd] in Hu. cbv beta iota.
      rewrite !TxModel.plen_app, (IHr Hr (S i)).
      replace (Z.of_nat d + 1) with (Z.of_nat (S d)) by lia.
      rewrite plen_wcomma, plen_wind, plen_strp, (Hu p (S d)). destruct p; reflexivity.
    + destruct ms; [reflexivity|]. apply plen_wind.
Qed.

(* THE SUPPLY OF rendered()'s tx calls in round_trip_text (tx_put "", tx_value (t, pretty, 0), tx_put "\n" if
   pretty, from the empty record): their events are the model's PresetReqAt.r_evs t p *)
Lemma prhtx_evs_r_evs : forall t p, PRH_FnTx.prhtx_evs 0 0 (PRH_FnCheck.ck_rtt_ns t p) = PresetReqAt.r_evs t p.
Proof.
  intros t p. unfold PRH_FnCheck.ck_rtt_ns, PresetReqAt.r_evs, PresetReqAt.rcaps.
  rewrite prhtx_evs_chain. pose proof (tv_calls_tx_val t p 0) as K. change (Z.of_nat 0) with 0 in K. rewrite K.
  reflexivity.
Qed.
