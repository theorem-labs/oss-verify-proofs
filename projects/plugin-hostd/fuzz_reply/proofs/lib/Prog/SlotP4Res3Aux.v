From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotParse SlotCaps3 SlotRI3 RelayRunT RelayRunF RelayModel RelayKeys RelayRep HarnessRep ListRep CheckRep ListTr
  HarnessTr send_line_b_c gesture_end_b_c gestures_end_b_c drain_b_c relay_remove_b_c relay_instance_gone_b_c
  SlotMove SlotNcMove3 SlotRun3 SlotP5R3 SlotP5R3G SlotP5Res3 SlotResR3 SlotReads op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_lem.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Lemma p4x_lines_range h : Forall zrange (lines (hs_state h) (bzs (pending_stream h))).
Proof. exact (proj1 (lines_range (bzs (pending_stream h)) (hs_state h) (zrange_bzs (hs_W h)) (zrange_bzs _))). Qed.

Definition OQ (c0 : Z) (o0 : adrF) (c1 : Z) (o1 : adrF) : Prop := c0 <= c1 /\ (c1 = c0 -> o1 = o0).

Lemma oq_refl c o : OQ c o c o.
Proof. split; [lia|reflexivity]. Qed.

Lemma oq_trans c0 o0 c1 o1 c2 o2 : OQ c0 o0 c1 o1 -> OQ c1 o1 c2 o2 -> OQ c0 o0 c2 o2.
Proof.
  intros [H1 E1] [H2 E2]. split; [lia|]. intros E. assert (c1 = c0) by lia. subst c2.
  rewrite (E2 ltac:(lia)). apply E1. lia.
Qed.

Lemma sl_oq f : forall mx no cap rem j o, 0 <= mx -> 0 <= no ->
  OQ cap o (fst (snd (sl_run f mx no cap rem j o))) (snd (snd (sl_run f mx no cap rem j o))).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hm Hn; cbn [sl_run]; [apply oq_refl|].
  destruct (Z.leb_spec rem 0) as [Hr|Hr]; [apply oq_refl|].
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
  assert (Hn0 : 0 < n).
  { unfold n. destruct (Z.eqb_spec mx 0) as [E|E]; cbn [negb andb]; [lia|].
    destruct (Z.ltb_spec mx rem); lia. }
  destruct (Z.ltb_spec cap (no + n)) as [Hc|Hc].
  - cbn [fst snd]. destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (Ret j) Hm ltac:(lia)) as [M _].
    split; [lia|]. intros E. lia.
  - apply IH; lia.
Qed.

Lemma send_oq live mx no cap len j o : 0 <= mx -> 0 <= no ->
  OQ cap o (send_line_cap live mx no cap len) (send_line_out live mx no cap len j o).
Proof.
  intros Hm Hn. unfold send_line_cap, send_line_out. destruct live; [|apply oq_refl].
  rewrite (sl_capi _ _ _ _ _ 0 adr0 j o). apply sl_oq; assumption.
Qed.

Lemma ge_oq live mx no cap xl j o : 0 <= mx -> 0 <= no -> 0 <= xl ->
  OQ cap o (gesture_end_cap live mx no cap xl) (gesture_end_out live mx no cap xl j o).
Proof.
  intros Hm Hn Hx. unfold gesture_end_cap, gesture_end_out. eapply oq_trans; [apply (send_oq live mx no cap xl j o Hm Hn)|].
  apply send_oq; lia.
Qed.

Lemma ke_oq xks : forall live mx no cap j o, 0 <= mx -> 0 <= no -> Forall (fun x => 0 <= fst x) xks ->
  OQ cap o (fst (snd (keys_end_run live mx no cap xks j o))) (snd (snd (keys_end_run live mx no cap xks j o))).
Proof.
  induction xks as [|[xl ka] r IH]; intros live mx no cap j o Hm Hn HX; cbn [keys_end_run fst snd]; [apply oq_refl|].
  apply Forall_cons_iff in HX as [Hx HX]. cbn [fst] in Hx.
  eapply oq_trans; [apply (ge_oq live mx no cap xl j o Hm Hn Hx)|]. apply IH; [exact Hm|lia|exact HX].
Qed.

Lemma seen_ka_nn H ka l j ha ks : 0 <= ka -> 0 <= snd (fst (seen_tr H ka l j ha ks)).
Proof.
  intros Hk. unfold seen_tr. destruct (gesture l) as [[[|] x]|]; [destruct (index_of x H)|destruct (index_of x H)|];
    cbn [fst snd]; lia.
Qed.

Lemma lines_oq live mx ls : forall no cap H ka j o ha ks, 0 <= mx -> 0 <= no -> 0 <= ka ->
  0 <= snd (snd (fst (lines_run live mx no cap H ka ls j o ha ks))) /\
  OQ cap o (fst (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks)))))
    (fst (fst (snd (lines_run live mx no cap H ka ls j o ha ks)))).
Proof.
  induction ls as [|l r IH]; intros no cap H ka j o ha ks Hm Hn Hk; cbn [lines_run fst snd];
    [split; [exact Hk|apply oq_refl]|].
  pose proof (send_oq live mx no cap (Z.of_nat (length l) + 1) j o Hm Hn) as S1.
  match goal with |- context [lines_run live mx ?n1 ?c1 ?H1 ?k1 r ?j1 ?o1 ?ha1 ?ks1] =>
    destruct (IH n1 c1 H1 k1 j1 o1 ha1 ks1 Hm ltac:(lia) (seen_ka_nn H ka l _ ha ks Hk)) as [K1 O1]
  end.
  split; [exact K1|]. eapply oq_trans; [exact S1|exact O1].
Qed.

Lemma pushes_capmono ls : forall n cap j v rs, 0 <= cap -> cap <= snd (fst (pushes_run n cap ls j v rs)).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs Hc; cbn [pushes_run fst snd]; [lia|].
  assert (P : cap <= push_cap n cap)
    by (unfold push_cap; destruct (Z.eqb_spec n cap); [destruct (Z.eqb_spec cap 0)|]; lia).
  etransitivity; [exact P|]. apply IH. lia.
Qed.

Lemma grow_nn cap used j b : 0 <= cap -> 0 <= fst (snd (grow_tr cap used j b)).
Proof. intros Hc. unfold grow_tr. destruct (cap - used <? 4096); [destruct (cap =? 0)|]; cbn [fst snd]; lia. Qed.

Lemma drain_inv lv mx f : forall s j a, 0 <= mx -> 0 <= ds_no s -> 0 <= ds_cap s -> 0 <= ds_ka s -> 0 <= ds_ecap s ->
  0 <= ds_no (fst (snd (drain_run f lv mx s j a))) /\ 0 <= ds_cap (fst (snd (drain_run f lv mx s j a))) /\
  0 <= ds_ka (fst (snd (drain_run f lv mx s j a))) /\ ds_ecap s <= ds_ecap (fst (snd (drain_run f lv mx s j a))) /\
  OQ (ds_ocap s) (da_out a) (ds_ocap (fst (snd (drain_run f lv mx s j a)))) (da_out (snd (snd (drain_run f lv mx s j a)))).
Proof.
  induction f as [|f IH]; intros s j a Hm Hn Hc Hk He; cbn [drain_run].
  - cbn [fst snd]. split; [exact Hn|]. split; [exact Hc|]. split; [exact Hk|]. split; [lia|apply oq_refl].
  - pose proof (grow_nn (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a) Hc) as Hg.
    destruct (ds_eintr s).
    + cbn [fst snd].
      match goal with |- context [drain_run f lv mx ?s1 ?j1 ?a1] =>
        pose proof (IH s1 j1 a1 Hm Hn Hg Hk He) as X; cbn [ds_ecap ds_ocap da_out] in X; exact X
      end.
    + destruct (ds_pend s) as [|r0 rs].
      * cbn [fst snd ds_no ds_cap ds_ka ds_ecap ds_ocap da_out].
        split; [exact Hn|]. split; [exact Hg|]. split; [exact Hk|]. split; [lia|apply oq_refl].
      * match goal with |- context [if ?c <=? 0 then _ else _] => destruct (c <=? 0) end.
        -- cbn [fst snd ds_no ds_cap ds_ka ds_ecap ds_ocap da_out].
           split; [exact Hn|]. split; [exact Hg|]. split; [exact Hk|]. split; [lia|apply oq_refl].
        -- match goal with |- context [chunk ?u ?sk ?d] => destruct (chunk u sk d) as [[u' sk'] rl] end.
           match goal with |- context [lines_run ?lv0 ?m ?no ?c ?H ?k rl ?jj ?o ?ha ?ks] =>
             pose proof (lines_oq lv0 m rl no c H k jj o ha ks Hm Hn Hk) as [LK LO];
             destruct (snd (fst (lines_run lv0 m no c H k rl jj o ha ks))) as [[oc' H'] ka'] eqn:E1;
             destruct (snd (lines_run lv0 m no c H k rl jj o ha ks)) as [[o' ha'] ks'] eqn:E2;
             try rewrite E1 in LK; try rewrite E1 in LO; try rewrite E2 in LO
           end.
           cbn [fst snd] in LK, LO. cbn [fst snd].
           match goal with |- context [pushes_run ?n0 ?c0 ?ls0 ?j0 ?v0 ?rs0] =>
             pose proof (pushes_capmono ls0 n0 c0 j0 v0 rs0 He) as PE
           end.
           match goal with |- context [drain_run f lv mx ?s2 ?j2 ?a2] =>
             assert (Hn2 : 0 <= ds_no s2) by (cbn [ds_no]; lia);
             assert (Hc2 : 0 <= ds_cap s2) by (cbn [ds_cap]; exact Hg);
             assert (Hk2 : 0 <= ds_ka s2) by (cbn [ds_ka]; exact LK);
             assert (He2 : ds_ecap s <= ds_ecap s2) by (cbn [ds_ecap]; exact PE);
             assert (HO2 : OQ (ds_ocap s) (da_out a) (ds_ocap s2) (da_out a2)) by (cbn [ds_ocap da_out]; exact LO);
             destruct (IH s2 j2 a2 Hm Hn2 Hc2 Hk2 ltac:(lia)) as (X1 & X2 & X3 & X4 & X5)
           end.
           split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [lia|].
           eapply oq_trans; [exact HO2|exact X5].
Qed.

Lemma live3_free_any b n p c : length (p3_live b) = 49%nat -> 0 <= c < 49 ->
  znth c (p3_live (pb3_free b n p)) <= znth c (p3_live b) - one_if c (band n).
Proof.
  intros Hl Hc. unfold pb3_free. cbn [p3_live]. unfold lv_add, one_if.
  destruct (band n) as [|q|q] eqn:B.
  - rewrite znth_zset by lia. rewrite Hl. destruct (Z.eqb_spec c 0); cbn [andb]; [|lia].
    replace (0 <? Z.of_nat 49) with true by reflexivity. cbn [andb]. subst. lia.
  - rewrite znth_zset by lia. rewrite Hl. destruct (Z.eqb_spec c (Z.pos q)); cbn [andb]; [|lia].
    destruct (Z.ltb_spec (Z.pos q) (Z.of_nat 49)); cbn [andb]; subst; lia.
  - unfold zset at 1. change (Z.to_nat (Z.neg q)) with 0%nat. change (znth (Z.neg q) (p3_live b)) with (znth 0 (p3_live b)).
    change (zupd (p3_live b) 0 (znth 0 (p3_live b) + -1)) with (zset 0 (znth 0 (p3_live b) + -1) (p3_live b)).
    rewrite znth_zset by lia. rewrite Hl. destruct (Z.eqb_spec c (Z.neg q)); [lia|].
    destruct (Z.eqb_spec c 0); cbn [andb]; [|lia]. replace (0 <? Z.of_nat 49) with true by reflexivity. cbn [andb].
    subst. lia.
Qed.

Lemma frees3 qs tr : forall b j, Forall ev_free tr -> length (p3_live b) = 49%nat ->
  length (p3_live (run3 qs b j tr)) = 49%nat /\ p3_cap (run3 qs b j tr) = p3_cap b /\
  p3_mcap (run3 qs b j tr) = p3_mcap b /\
  (forall c, 0 <= c < 49 -> znth c (p3_live (run3 qs b j tr)) <= znth c (p3_live b) - bcnt c (fsz tr)) /\
  p3_bytes (run3 qs b j tr) = p3_bytes b - zsum (fun n => n) (fsz tr).
Proof.
  induction tr as [|ev tr IH]; intros b j Hf Hl.
  - cbn [run_from fsz]. split; [exact Hl|]. split; [reflexivity|]. split; [reflexivity|].
    split; [intros c _; change (bcnt c []) with 0; lia|rewrite zsum_nil; lia].
  - apply Forall_cons_iff in Hf as [He Hf]. destruct ev as [n|n a|k n a]; cbn [ev_free] in He; try contradiction.
    cbn [run_from fsz].
    assert (Hl' : length (p3_live (pb3_free b n (resolveF qs a))) = 49%nat)
      by (unfold pb3_free; cbn [p3_live]; rewrite lv_add_length; exact Hl).
    destruct (IH (pb3_free b n (resolveF qs a)) j Hf Hl') as (L1 & C1 & M1 & V1 & B1).
    split; [exact L1|]. split; [rewrite C1; reflexivity|]. split; [rewrite M1; reflexivity|].
    split.
    + intros c Hc. rewrite bcnt_cons. pose proof (V1 c Hc). pose proof (live3_free_any b n (resolveF qs a) c Hl Hc). lia.
    + rewrite B1, zsum_cons. unfold pb3_free. cbn [p3_bytes]. lia.
Qed.

Definition ofree (n : Z) (a : adrF) : trF := if n =? 0 then [] else [RFree n a].

Lemma ofree_room qs b j n a : room3 qs b j (ofree n a).
Proof. unfold ofree. destruct (n =? 0); [exact I|cbn [room_from]; exact I]. Qed.

Lemma ofree_nret n a : nretF (ofree n a) = 0%nat.
Proof. unfold ofree. destruct (n =? 0); reflexivity. Qed.

Lemma ofree_eff qs b j n a : pk3_ok b ->
  pk3_ok (run3 qs b j (ofree n a)) /\ p3_cap (run3 qs b j (ofree n a)) = p3_cap b /\
  p3_mcap (run3 qs b j (ofree n a)) = p3_mcap b /\
  (forall c, 0 <= c < 49 -> znth c (p3_live (run3 qs b j (ofree n a))) <= znth c (p3_live b) - ncb n c) /\
  p3_bytes (run3 qs b j (ofree n a)) = p3_bytes b - n /\
  (forall S r, misT S r (p3_mis b) -> misT S r (p3_mis (run3 qs b j (ofree n a)))) /\
  (forall M0 S0 X T, misK M0 S0 (X ++ slot3 n (resolveF qs a) ++ T) (p3_mis b) ->
     misK M0 S0 (X ++ T) (p3_mis (run3 qs b j (ofree n a)))).
Proof.
  intros HP. pose proof HP as (Hl & _). unfold ofree, ncb, slot3. destruct (Z.eqb_spec n 0) as [E|E]; cbn [run_from].
  - subst n. split; [exact HP|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros c _; lia|].
    split; [lia|]. split; [intros S r H; exact H|]. intros M0 S0 X T HK. exact HK.
  - split; [apply pk3_free; exact HP|]. split; [reflexivity|]. split; [reflexivity|].
    split; [intros c Hc; exact (live3_free_any b n (resolveF qs a) c Hl Hc)|].
    unfold pb3_free. cbn [p3_bytes p3_mis]. split; [lia|]. split; [intros S r H; apply misT_free; exact H|].
    intros M0 S0 X T HK e He. unfold mis_del in He. apply filter_In in He as [He Hn].
    destruct (HK e He) as [Hx|Hx]; [left|right; exact Hx].
    rewrite !in_app_iff in Hx. rewrite in_app_iff.
    destruct Hx as [Hx|[[Hx|[]]|Hx]]; [left; exact Hx| |right; exact Hx].
    exfalso. rewrite Hx, sptr_eqb_refl in Hn. discriminate.
Qed.

Lemma rr_model lv mx NO CAP e h nm o : 0 <= mx -> 0 <= NO -> 0 <= CAP -> 0 <= re_cap e -> 0 <= ent_ka e ->
  0 <= hl_cap (hs_expected h) ->
  0 <= ds_no (after_drain lv mx NO CAP e h) /\ 0 <= ds_cap (after_drain lv mx NO CAP e h) /\
  0 <= ds_ka (after_drain lv mx NO CAP e h) /\ hl_cap (hs_expected h) <= ds_ecap (after_drain lv mx NO CAP e h) /\
  OQ CAP o (ds_ocap (after_drain lv mx NO CAP e h))
    (da_out (after_drain_adr lv mx NO CAP e h 0 (drain_start nm o e h))).
Proof.
  intros Hm Hn Hc Hr Hk He. unfold after_drain, after_drain_adr. destruct (re_eof e =? 0).
  - unfold drain_fin, drain_adr, drain_go.
    rewrite (drain_state_i _ lv mx (drain_init NO CAP e h) 0%nat dadr0 0%nat (drain_start nm o e h)).
    exact (drain_inv lv mx _ (drain_init NO CAP e h) 0%nat (drain_start nm o e h) Hm Hn Hr Hk He).
  - cbn [drain_init ds_no ds_cap ds_ka ds_ecap ds_ocap drain_start da_out].
    split; [exact Hn|]. split; [exact Hr|]. split; [exact Hk|]. split; [lia|apply oq_refl].
Qed.

Lemma rr_keys_cap lv mx NO CAP e h nm o j1 o1 :
  fst (snd (keys_end_run lv mx (ds_no (after_drain lv mx NO CAP e h)) (ds_ocap (after_drain lv mx NO CAP e h))
    (combine (map (fun x => Z.of_nat (length x)) (ds_H (after_drain lv mx NO CAP e h)))
       (da_keys (after_drain_adr lv mx NO CAP e h 0 (drain_start nm o e h)))) j1 o1)) =
  remove_entry_cap lv mx NO CAP e h.
Proof.
  unfold remove_entry_cap, gestures_end_cap. apply ke_capi.
  rewrite combine_fst; [rewrite map_map; cbn [fst]; rewrite map_id; reflexivity|].
  rewrite length_map. apply after_keys_len.
Qed.

Lemma rr_xks_nn (l : list (list Z)) (ks : list adrF) :
  Forall (fun x => 0 <= fst x) (combine (map (fun x => Z.of_nat (length x)) l) ks).
Proof.
  apply Forall_forall. intros [x y] Hx. apply in_combine_l in Hx. apply in_map_iff in Hx as (z & <- & _).
  cbn [fst]. lia.
Qed.

Lemma rr_tail qs b0 b CAP E EB EBB S r s a1 j1 xks capF lv mx :
  gc3 b0 CAP E EB EBB S r (ds_ocap s) (resolveF qs (da_out a1)) b -> rc3 b0 CAP E EBB capF ->
  Forall (fun x => 0 <= fst x) xks -> 0 <= ds_ocap s ->
  fst (snd (keys_end_run lv mx (ds_no s) (ds_ocap s) xks j1 (da_out a1))) <= capF ->
  0 <= ds_ka s -> 0 <= ds_cap s ->
  room3 qs b j1 (gestures_end_tr lv mx (ds_no s) (ds_ocap s) xks (ds_ka s) (ds_ka s) j1 (da_out a1) (da_hp a1) ++
                 ofree (ds_cap s) (da_buf a1)) /\
  pk3_ok (run3 qs b j1 (gestures_end_tr lv mx (ds_no s) (ds_ocap s) xks (ds_ka s) (ds_ka s) j1 (da_out a1) (da_hp a1) ++
                 ofree (ds_cap s) (da_buf a1))) /\
  p3_cap (run3 qs b j1 (gestures_end_tr lv mx (ds_no s) (ds_ocap s) xks (ds_ka s) (ds_ka s) j1 (da_out a1) (da_hp a1) ++
                 ofree (ds_cap s) (da_buf a1))) = p3_cap b0 /\
  p3_mcap (run3 qs b j1 (gestures_end_tr lv mx (ds_no s) (ds_ocap s) xks (ds_ka s) (ds_ka s) j1 (da_out a1) (da_hp a1) ++
                 ofree (ds_cap s) (da_buf a1))) = p3_mcap b0 /\
  (forall c, 0 <= c < 49 ->
     znth c (p3_live (run3 qs b j1 (gestures_end_tr lv mx (ds_no s) (ds_ocap s) xks (ds_ka s) (ds_ka s) j1 (da_out a1)
       (da_hp a1) ++ ofree (ds_cap s) (da_buf a1)))) <=
     znth c (p3_live b0) + ncb (fst (snd (keys_end_run lv mx (ds_no s) (ds_ocap s) xks j1 (da_out a1)))) c - ncb CAP c +
       E c - ncb (ds_ka s) c - ncb (ds_cap s) c) /\
  p3_bytes (run3 qs b j1 (gestures_end_tr lv mx (ds_no s) (ds_ocap s) xks (ds_ka s) (ds_ka s) j1 (da_out a1) (da_hp a1) ++
                 ofree (ds_cap s) (da_buf a1))) <=
    p3_bytes b0 + fst (snd (keys_end_run lv mx (ds_no s) (ds_ocap s) xks j1 (da_out a1))) - CAP + EB - ds_ka s - ds_cap s /\
  p3_bytes (run3 qs b j1 (gestures_end_tr lv mx (ds_no s) (ds_ocap s) xks (ds_ka s) (ds_ka s) j1 (da_out a1) (da_hp a1) ++
                 ofree (ds_cap s) (da_buf a1))) <=
    p3_bytes b0 + fst (snd (keys_end_run lv mx (ds_no s) (ds_ocap s) xks j1 (da_out a1))) - CAP + EBB /\
  misT (slot3 (fst (snd (keys_end_run lv mx (ds_no s) (ds_ocap s) xks j1 (da_out a1))))
          (resolveF qs (snd (snd (keys_end_run lv mx (ds_no s) (ds_ocap s) xks j1 (da_out a1))))) ++ S)
    (r + res3 (fst (snd (keys_end_run lv mx (ds_no s) (ds_ocap s) xks j1 (da_out a1)))))
    (p3_mis (run3 qs b j1 (gestures_end_tr lv mx (ds_no s) (ds_ocap s) xks (ds_ka s) (ds_ka s) j1 (da_out a1) (da_hp a1) ++
                 ofree (ds_cap s) (da_buf a1)))).
Proof.
  intros HG HR HX Ho Hf Hka Hcp.
  destruct (ke3 xks lv mx (ds_no s) (ds_ocap s) j1 (da_out a1) qs b b0 CAP E EB EBB S r capF HX Ho Hf HR HG) as [Rk Gk].
  set (k := keys_end_run lv mx (ds_no s) (ds_ocap s) xks j1 (da_out a1)) in *.
  unfold gestures_end_tr. fold k. change (if ds_ka s =? 0 then [] else [RFree (ds_ka s) (da_hp a1)]) with (ofree (ds_ka s) (da_hp a1)).
  rewrite <- app_assoc, room3_app, run3_app, room3_app, run3_app, ofree_nret, Nat.add_0_r.
  set (bk := run3 qs b j1 (fst k)) in *. set (j2 := (j1 + nretF (fst k))%nat).
  destruct Gk as (HP & HC & HM & HL & HB1 & HB2 & HS).
  destruct (ofree_eff qs bk j2 (ds_ka s) (da_hp a1) HP) as (P1 & C1 & M1 & L1 & B1 & S1 & _).
  set (b1 := run3 qs bk j2 (ofree (ds_ka s) (da_hp a1))) in *.
  destruct (ofree_eff qs b1 j2 (ds_cap s) (da_buf a1) P1) as (P2 & C2 & M2 & L2 & B2 & S2 & _).
  split; [split; [exact Rk|split; [apply ofree_room|apply ofree_room]]|].
  split; [exact P2|]. split; [congruence|]. split; [congruence|].
  split; [intros c Hc; pose proof (HL c Hc); pose proof (L1 c Hc); pose proof (L2 c Hc); lia|].
  split; [lia|]. split; [lia|]. apply S2, S1, HS.
Qed.

Definition rr_lines (e : rentry) (h : hsrc) : list (list Z) :=
  if re_eof e =? 0 then lines (hs_state h) (bzs (pending_stream h)) else [].

Lemma bcnt_nil c : bcnt c [] = 0.
Proof. reflexivity. Qed.

Theorem rr3 lv mx NO CAP e h nm o qs b S r capF :
  (re_eof e = 0 -> drain3 e h) -> 0 <= mx -> 0 <= NO -> 0 <= CAP ->
  0 <= re_cap e -> 0 <= ent_ka e -> 0 <= hl_cap (hs_expected h) ->
  remove_entry_cap lv mx NO CAP e h <= capF -> capF <= NMAX -> pk3_ok b ->
  (forall c, 0 <= c < 49 -> znth c (p3_live b) + cred h c + 64 <= znth c (p3_cap b)) ->
  p3_bytes b + 2 * capF + 2 * DRAIN_B <= BMAX ->
  misT (slot3 CAP (resolveF qs o) ++ dslots qs e h (drain_start nm o e h) ++ S) (r + res3 CAP + dres e h) (p3_mis b) ->
  room3 qs b 0 (remove_entry_tr lv mx NO CAP e h 0 (drain_start nm o e h)) /\
  pk3_ok (run3 qs b 0 (remove_entry_tr lv mx NO CAP e h 0 (drain_start nm o e h))) /\
  p3_cap (run3 qs b 0 (remove_entry_tr lv mx NO CAP e h 0 (drain_start nm o e h))) = p3_cap b /\
  p3_mcap (run3 qs b 0 (remove_entry_tr lv mx NO CAP e h 0 (drain_start nm o e h))) = p3_mcap b /\
  (exists dks, Forall (fun n => 0 <= n) dks /\
     (forall c, 0 <= c < 49 -> bcnt c dks + bcnt c (ekeys (rr_lines e h)) <= cred h c) /\
     zsum (fun n => n) dks + zsum (fun n => n) (ekeys (rr_lines e h)) <= credb h /\
     (forall c, 0 <= c < 49 ->
        znth c (p3_live (run3 qs b 0 (remove_entry_tr lv mx NO CAP e h 0 (drain_start nm o e h)))) <=
        znth c (p3_live b) + ncb (remove_entry_cap lv mx NO CAP e h) c - ncb CAP c - ncb (re_cap e) c -
        ncb (ent_ka e) c + ncb (16 * ds_ecap (after_drain lv mx NO CAP e h)) c - ncb (16 * hl_cap (hs_expected h)) c +
        bcnt c dks) /\
     p3_bytes (run3 qs b 0 (remove_entry_tr lv mx NO CAP e h 0 (drain_start nm o e h))) <=
       p3_bytes b + remove_entry_cap lv mx NO CAP e h - CAP - re_cap e - ent_ka e +
       16 * (ds_ecap (after_drain lv mx NO CAP e h) - hl_cap (hs_expected h)) + zsum (fun n => n) dks) /\
  p3_bytes (run3 qs b 0 (remove_entry_tr lv mx NO CAP e h 0 (drain_start nm o e h))) <= p3_bytes b + capF + DRAIN_B /\
  exists S' r', misT (slot3 (remove_entry_cap lv mx NO CAP e h)
                  (resolveF qs (remove_entry_out lv mx NO CAP e h 0 (drain_start nm o e h))) ++ S') r'
                  (p3_mis (run3 qs b 0 (remove_entry_tr lv mx NO CAP e h 0 (drain_start nm o e h)))).
Proof.
  intros Hd Hm Hn Hc Hr Hk He Hf HN HP HL HB HS.
  destruct (rr_model lv mx NO CAP e h nm o Hm Hn Hc Hr Hk He) as (Ns & Ncap & Nka & Necap & [Ho _]).
  pose proof (rr_keys_cap lv mx NO CAP e h nm o) as KC.
  assert (E3 : DRAIN_B = 1099511627776) by reflexivity.
  unfold remove_entry_tr, remove_entry_out, remove_entry_run. cbv zeta. cbn [fst snd]. unfold gestures_end_out.
  fold (ofree (ds_cap (after_drain lv mx NO CAP e h)) (da_buf (after_drain_adr lv mx NO CAP e h 0 (drain_start nm o e h)))).
  set (s := after_drain lv mx NO CAP e h) in *. set (a := drain_start nm o e h) in *.
  set (a1 := after_drain_adr lv mx NO CAP e h 0 a) in *.
  set (xks := combine (map (fun x => Z.of_nat (length x)) (ds_H s)) (da_keys a1)).
  assert (HX : Forall (fun x => 0 <= fst x) xks) by apply rr_xks_nn.
  assert (Ho' : 0 <= ds_ocap s) by lia.
  destruct (Z.eqb_spec (re_eof e) 0) as [Ee|Ee].
  - assert (Ee' : (re_eof e =? 0) = true) by (apply Z.eqb_eq; exact Ee).
    assert (Es : s = drain_fin lv mx NO CAP e h) by (unfold s, after_drain; try rewrite Ee'; reflexivity).
    assert (Ea1 : a1 = drain_adr lv mx NO CAP e h 0 a) by (unfold a1, after_drain_adr; try rewrite Ee'; reflexivity).
    assert (EL : rr_lines e h = lines (hs_state h) (bzs (pending_stream h))) by (unfold rr_lines; rewrite Ee'; reflexivity).
    try rewrite Ee'. rewrite EL.
    set (td := drain_tr lv mx NO CAP e h 0 a).
    set (j1 := (0 + nretF td)%nat).
    pose proof (KC j1 (da_out a1)) as KC1. fold s a1 xks in KC1.
    pose proof (ke_mono xks lv mx (ds_no s) (ds_ocap s) j1 (da_out a1) Ho') as KM.
    destruct (Hd Ee lv mx NO CAP Hm Hc) as [_ Hd']. cbv zeta in Hd'. rewrite <- Es in Hd'.
    assert (P5 : ds_ocap s <= NMAX) by lia.
    assert (P2 : forall c, 0 <= c < 49 -> znth c (p3_live b) + cred h c + DRAIN_HR <= znth c (p3_cap b))
      by (intros c Hc'; pose proof (HL c Hc'); unfold DRAIN_HR; lia).
    assert (P3 : p3_bytes b - CAP + 2 * ds_ocap s + DRAIN_B <= BMAX) by lia.
    destruct (Hd' qs b 0%nat a S r HP P5 P2 P3 HS)
      as (Rd & Pd & Cd & Md & (dks & Hk0 & Ld & Bd1 & Hkc & Hkb) & Bd2 & D & SD).
    fold td in Rd, Pd, Cd, Md, Ld, Bd1, Bd2, SD. rewrite <- Ea1 in SD.
    assert (Hkd : forall c, 0 <= c < 49 -> bcnt c dks <= cred h c).
    { intros c Hc'. pose proof (Hkc c Hc'). pose proof (bcnt_nonneg c (ekeys (lines (hs_state h) (bzs (pending_stream h))))).
      lia. }
    assert (G1 : gc3 b CAP (fun c => dchain e h s c + bcnt c dks) (dchainb e h s + zsum (fun n => n) dks) DRAIN_B
                   (D ++ S) r (ds_ocap s) (resolveF qs (da_out a1)) (run3 qs b 0 td)).
    { split; [exact Pd|]. split; [exact Cd|]. split; [exact Md|].
      split; [intros c Hc'; pose proof (Ld c Hc'); lia|]. split; [lia|]. split; [lia|]. exact SD. }
    assert (RC : rc3 b CAP (fun c => dchain e h s c + bcnt c dks) DRAIN_B capF).
    { split; [|split; [lia|exact HN]]. intros c Hc'. pose proof (HL c Hc'). pose proof (dchain_le3 e h s c).
      pose proof (Hkd c Hc'). pose proof (ncb_b CAP c). lia. }
    destruct (rr_tail qs b (run3 qs b 0 td) CAP _ _ _ (D ++ S) r s a1 j1 xks capF lv mx G1 RC HX Ho' ltac:(lia) Nka Ncap)
      as (Rt & Pt & Ct & Mt & Lt & Bt1 & Bt2 & St).
    rewrite KC1 in Lt, Bt1, Bt2, St.
    rewrite room3_app, run3_app. fold j1.
    split; [split; [exact Rd|exact Rt]|]. split; [exact Pt|]. split; [exact Ct|]. split; [exact Mt|].
    split; [|split; [lia|exists (D ++ S), (r + res3 (remove_entry_cap lv mx NO CAP e h))%nat; exact St]].
    exists dks. split; [exact Hk0|]. split; [exact Hkc|]. split; [exact Hkb|].
    split; [intros c Hc'; pose proof (Lt c Hc'); unfold dchain in *; lia|]. unfold dchainb in Bt1. lia.
  - assert (Ee' : (re_eof e =? 0) = false) by (apply Z.eqb_neq; exact Ee).
    assert (Es : s = drain_init NO CAP e h) by (unfold s, after_drain; try rewrite Ee'; reflexivity).
    assert (Ea1 : a1 = a) by (unfold a1, after_drain_adr; try rewrite Ee'; reflexivity).
    assert (EL : rr_lines e h = []) by (unfold rr_lines; rewrite Ee'; reflexivity).
    try rewrite Ee'. rewrite EL. cbn [app].
    pose proof (KC 0%nat (da_out a1)) as KC1. fold s a1 xks in KC1.
    pose proof (ke_mono xks lv mx (ds_no s) (ds_ocap s) 0%nat (da_out a1) Ho') as KM.
    assert (OC : ds_ocap s = CAP) by (rewrite Es; reflexivity).
    assert (G0 : gc3 b CAP (fun _ => 0) 0 0 (dslots qs e h a ++ S) (r + dres e h) (ds_ocap s) (resolveF qs (da_out a1)) b).
    { rewrite OC, Ea1. split; [exact HP|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros c _; lia|]. split; [lia|]. split; [lia|].
      eapply misT_r; [|exact HS]. lia. }
    assert (RC : rc3 b CAP (fun _ => 0) 0 capF).
    { split; [|split; [lia|exact HN]]. intros c Hc'. pose proof (HL c Hc'). pose proof (cred_nonneg h c).
      pose proof (ncb_b CAP c). lia. }
    destruct (rr_tail qs b b CAP _ _ _ (dslots qs e h a ++ S) (r + dres e h)%nat s a1 0%nat xks capF lv mx G0 RC HX Ho'
                ltac:(lia) Nka Ncap) as (Rt & Pt & Ct & Mt & Lt & Bt1 & Bt2 & St).
    rewrite KC1 in Lt, Bt1, Bt2, St.
    change (nretF []) with 0%nat. cbn [Nat.add].
    split; [exact Rt|]. split; [exact Pt|]. split; [exact Ct|]. split; [exact Mt|].
    split; [|split; [lia|eexists; eexists; exact St]].
    exists []. split; [constructor|]. change (ekeys []) with (@nil Z).
    split; [intros c _; rewrite !bcnt_nil; apply cred_nonneg|]. split; [rewrite !zsum_nil; pose proof (credb_nonneg h); lia|].
    assert (Es1 : ds_ka s = ent_ka e /\ ds_cap s = re_cap e /\ ds_ecap s = hl_cap (hs_expected h)) by (rewrite Es; auto).
    destruct Es1 as (X1 & X2 & X3). rewrite X1, X2 in Lt, Bt1 |- *. rewrite X3.
    split; [intros c Hc'; pose proof (Lt c Hc'); rewrite bcnt_nil; lia|]. rewrite zsum_nil. lia.
Qed.

Theorem rr_misK M0 S0 lv mx NO CAP e h nm o qs b T :
  0 <= mx -> 0 <= NO -> 0 <= CAP -> 0 <= re_cap e -> 0 <= ent_ka e -> 0 <= hl_cap (hs_expected h) ->
  misK M0 S0 (slot3 CAP (resolveF qs o) ++ dsl qs (drain_init NO CAP e h) (drain_start nm o e h) ++ T) (p3_mis b) ->
  misK M0 S0 (slot3 (remove_entry_cap lv mx NO CAP e h)
                (resolveF qs (remove_entry_out lv mx NO CAP e h 0 (drain_start nm o e h))) ++
              slot3 (ds_ecap (after_drain lv mx NO CAP e h))
                (resolveF qs (da_ev (after_drain_adr lv mx NO CAP e h 0 (drain_start nm o e h)))) ++ T)
    (p3_mis (run3 qs b 0 (remove_entry_tr lv mx NO CAP e h 0 (drain_start nm o e h)))).
Proof.
  intros Hm Hn Hc Hr Hk He HK.
  destruct (rr_model lv mx NO CAP e h nm o Hm Hn Hc Hr Hk He) as (_ & _ & _ & _ & [Ho _]).
  pose proof (rr_keys_cap lv mx NO CAP e h nm o) as KC.
  unfold remove_entry_tr, remove_entry_out, remove_entry_run. cbv zeta. cbn [fst snd]. unfold gestures_end_out.
  fold (ofree (ds_cap (after_drain lv mx NO CAP e h)) (da_buf (after_drain_adr lv mx NO CAP e h 0 (drain_start nm o e h)))).
  unfold gestures_end_tr.
  fold (ofree (ds_ka (after_drain lv mx NO CAP e h)) (da_hp (after_drain_adr lv mx NO CAP e h 0 (drain_start nm o e h)))).
  set (s := after_drain lv mx NO CAP e h) in *. set (a := drain_start nm o e h) in *.
  set (a1 := after_drain_adr lv mx NO CAP e h 0 a) in *.
  set (xks := combine (map (fun x => Z.of_nat (length x)) (ds_H s)) (da_keys a1)).
  assert (Ho' : 0 <= ds_ocap s) by lia.
  assert (KD : forall td b1, misK M0 S0 (slot3 (ds_ocap s) (resolveF qs (da_out a1)) ++ dsl qs s a1 ++ T) (p3_mis b1) ->
    misK M0 S0 (slot3 (remove_entry_cap lv mx NO CAP e h)
                  (resolveF qs (snd (snd (keys_end_run lv mx (ds_no s) (ds_ocap s) xks (0 + nretF td) (da_out a1))))) ++
                slot3 (ds_ecap s) (resolveF qs (da_ev a1)) ++ T)
      (p3_mis (run3 qs b1 (0 + nretF td) ((fst (keys_end_run lv mx (ds_no s) (ds_ocap s) xks (0 + nretF td) (da_out a1)) ++
         ofree (ds_ka s) (da_hp a1)) ++ ofree (ds_cap s) (da_buf a1))))).
  { intros td b1 H1.
    pose proof (ke_misK M0 S0 qs (dsl qs s a1 ++ T) xks lv mx (ds_no s) (ds_ocap s) (0 + nretF td) (da_out a1) b1 Ho' H1)
      as K1.
    pose proof (KC (0 + nretF td)%nat (da_out a1)) as KC1. fold s a1 xks in KC1. rewrite KC1 in K1.
    rewrite !run3_app.
    set (bk := run3 qs b1 (0 + nretF td) (fst (keys_end_run lv mx (ds_no s) (ds_ocap s) xks (0 + nretF td) (da_out a1)))) in *.
    unfold dsl in K1.
    assert (K2 : misK M0 S0 ((slot3 (remove_entry_cap lv mx NO CAP e h)
                  (resolveF qs (snd (snd (keys_end_run lv mx (ds_no s) (ds_ocap s) xks (0 + nretF td) (da_out a1))))) ++
                  slot3 (ds_cap s) (resolveF qs (da_buf a1))) ++ slot3 (ds_ka s) (resolveF qs (da_hp a1)) ++
                  (slot3 (ds_ecap s) (resolveF qs (da_ev a1)) ++ T)) (p3_mis bk)) by misK_perm K1.
    clear K1.
    assert (MF : forall b2 j n x X T', misK M0 S0 (X ++ slot3 n (resolveF qs x) ++ T') (p3_mis b2) ->
               misK M0 S0 (X ++ T') (p3_mis (run3 qs b2 j (ofree n x)))).
    { intros b2 j n x X T' H. unfold ofree, slot3 in *. destruct (Z.eqb_spec n 0) as [E|E]; cbn [run_from]; [exact H|].
      unfold pb3_free. cbn [p3_mis]. intros e0 He0. unfold mis_del in He0. apply filter_In in He0 as [He0 Hn0].
      destruct (H e0 He0) as [Hx|Hx]; [left|right; exact Hx].
      rewrite !in_app_iff in Hx. rewrite in_app_iff.
      destruct Hx as [Hx|[[Hx|[]]|Hx]]; [left; exact Hx| |right; exact Hx].
      exfalso. rewrite Hx, sptr_eqb_refl in Hn0. discriminate. }
    apply (MF _ _ (ds_cap s) (da_buf a1) (slot3 (remove_entry_cap lv mx NO CAP e h)
      (resolveF qs (snd (snd (keys_end_run lv mx (ds_no s) (ds_ocap s) xks (0 + nretF td) (da_out a1))))))
      (slot3 (ds_ecap s) (resolveF qs (da_ev a1)) ++ T)).
    eapply misK_S; [|apply (MF bk _ (ds_ka s) (da_hp a1) _ _ K2)].
    intros z Hz. rewrite !in_app_iff in *. tauto. }
  destruct (Z.eqb_spec (re_eof e) 0) as [Ee|Ee].
  - assert (Ee' : (re_eof e =? 0) = true) by (apply Z.eqb_eq; exact Ee).
    assert (Es : s = drain_fin lv mx NO CAP e h) by (unfold s, after_drain; try rewrite Ee'; reflexivity).
    assert (Ea1 : a1 = drain_adr lv mx NO CAP e h 0 a) by (unfold a1, after_drain_adr; try rewrite Ee'; reflexivity).
    try rewrite Ee'.
    set (td := drain_tr lv mx NO CAP e h 0 a).
    rewrite run3_app. apply KD.
    set (f := S (S (length (pending_stream h)))).
    destruct (drain_misK M0 S0 qs T f lv mx (drain_init NO CAP e h) 0%nat a b ltac:(cbn [drain_init ds_ocap]; exact Hc)
                ltac:(cbn [drain_init ds_ocap]; exact HK)) as [_ DK].
    assert (Es2 : fst (snd (drain_run f lv mx (drain_init NO CAP e h) 0 a)) = s).
    { rewrite Es. unfold drain_fin, drain_go. fold f. apply drain_state_i. }
    assert (Ea2 : snd (snd (drain_run f lv mx (drain_init NO CAP e h) 0 a)) = a1) by (rewrite Ea1; reflexivity).
    rewrite Es2, Ea2 in DK. exact DK.
  - assert (Ee' : (re_eof e =? 0) = false) by (apply Z.eqb_neq; exact Ee).
    assert (Es : s = drain_init NO CAP e h) by (unfold s, after_drain; try rewrite Ee'; reflexivity).
    assert (Ea1 : a1 = a) by (unfold a1, after_drain_adr; try rewrite Ee'; reflexivity).
    try rewrite Ee'. cbn [app].
    change (run3 qs b 0 ((fst (keys_end_run lv mx (ds_no s) (ds_ocap s) xks (0 + nretF []) (da_out a1)) ++
      ofree (ds_ka s) (da_hp a1)) ++ ofree (ds_cap s) (da_buf a1))) with
      (run3 qs b (0 + nretF []) ((fst (keys_end_run lv mx (ds_no s) (ds_ocap s) xks (0 + nretF []) (da_out a1)) ++
      ofree (ds_ka s) (da_hp a1)) ++ ofree (ds_cap s) (da_buf a1))).
    apply KD. rewrite Es, Ea1. cbn [drain_init ds_ocap]. unfold a. cbn [drain_start da_out]. exact HK.
Qed.

Lemma rr_oq lv mx NO CAP e h nm o : 0 <= mx -> 0 <= NO -> 0 <= CAP -> 0 <= re_cap e -> 0 <= ent_ka e ->
  0 <= hl_cap (hs_expected h) ->
  OQ CAP o (remove_entry_cap lv mx NO CAP e h) (remove_entry_out lv mx NO CAP e h 0 (drain_start nm o e h)).
Proof.
  intros Hm Hn Hc Hr Hk He.
  destruct (rr_model lv mx NO CAP e h nm o Hm Hn Hc Hr Hk He) as (Ns & _ & _ & _ & O1).
  pose proof (rr_keys_cap lv mx NO CAP e h nm o) as KC.
  unfold remove_entry_out, remove_entry_run. cbv zeta. cbn [snd]. unfold gestures_end_out.
  match goal with |- context [keys_end_run lv mx ?n ?c ?x ?j ?o1] =>
    rewrite <- (KC j o1); eapply oq_trans; [exact O1|apply ke_oq; [exact Hm|exact Ns|apply rr_xks_nn]]
  end.
Qed.

Lemma arr_sz_in l x : In x (map fst (arr_sz l)) -> x = hl_v l /\ hl_cap l <> 0.
Proof.
  unfold arr_sz. destruct (Z.eqb_spec (hl_cap l) 0) as [E|E]; [intros []|]. intros [<-|[]]. split; [reflexivity|exact E].
Qed.

Lemma slot3_in' p n x : In p (slot3 n x) -> n <> 0 /\ p = x.
Proof. unfold slot3. destruct (Z.eqb_spec n 0) as [E|E]; [intros []|intros [<-|[]]; split; [exact E|reflexivity]]. Qed.

Lemma slot3_mem n x : n <> 0 -> In x (slot3 n x).
Proof. intros H. unfold slot3. rewrite (proj2 (Z.eqb_neq n 0) H). left. reflexivity. Qed.

Theorem p4_mis_final (L0 L1 L2 L3 L4 : layout) (A0 A1 A2 A3 A4 : astate) (M0 M1 M2 M3 M4 : list (sptr * Z))
    (S0 : list sptr) (out CAP OUT' C1 ec hc hc' xe : Z) (pF pev1 pH ph1 : sptr) (e : rentry) (h h3 : hsrc)
    (V0 V' : rview) :
  let dels := out_move_dels out CAP OUT' C1 ++ entry_dels e ++ src_dels h in
  (forall e0, In e0 M0 -> exists n, In (fst e0, n) (user_blocks A0)) ->
  (forall e0, In e0 M1 -> exists n, In (fst e0, n) (user_blocks A1)) ->
  (forall e0, In e0 M2 -> exists n, In (fst e0, n) (user_blocks A2)) ->
  (forall e0, In e0 M3 -> exists n, In (fst e0, n) (user_blocks A3)) ->
  (forall e0, In e0 M4 -> exists n, In (fst e0, n) (user_blocks A4)) ->
  List.NoDup (map fst (blocks L0 A0)) -> List.NoDup (map fst (blocks L1 A1)) ->
  List.NoDup (map fst (blocks L3 A3)) ->
  (forall p n n', In (p, n) (user_blocks A0) -> In (p, n') (user_blocks A1) -> ptr_addr L1 p = ptr_addr L0 p) ->
  (forall p n n', In (p, n) (user_blocks A1) -> In (p, n') (user_blocks A2) -> ptr_addr L2 p = ptr_addr L1 p) ->
  (forall p n n', In (p, n) (user_blocks A2) -> In (p, n') (user_blocks A3) -> ptr_addr L3 p = ptr_addr L2 p) ->
  (forall p n n', In (p, n) (user_blocks A3) -> In (p, n') (user_blocks A4) -> ptr_addr L4 p = ptr_addr L3 p) ->
  misK M0 S0 (slot3 C1 pF ++ slot3 ec pev1 ++ []) M1 ->
  misK M1 (slot3 hc ph1) (slot3 hc' pH ++ []) M2 ->
  (forall e0, In e0 M3 -> In e0 M2) ->
  (forall e0, In e0 M4 -> In e0 M3 /\ forall x, In x (map fst (src_dels h3)) -> fst e0 <> sptr_of L3 A3 x) ->
  (forall x, In x (map fst (out_move_dels out CAP OUT' C1 ++ entry_dels e ++ arr_sz (hs_expected h))) ->
     In (sptr_of L0 A0 x) S0) ->
  (forall x, In x (map fst (arr_sz (hs_pending h)) ++ [hs_partial h]) -> In x (map fst (src_dels h3))) ->
  hc = hl_cap (hs_held h) -> ph1 = sptr_of L1 A1 (hl_v (hs_held h)) ->
  (hc' <> 0 -> (exists n, In (pH, n) (user_blocks A2)) /\ In (ptr_addr L2 pH) (map fst (src_dels h3))) ->
  (ec <> 0 -> (exists n, In (pev1, n) (user_blocks A1)) -> In (ptr_addr L1 pev1) (map fst (src_dels h3))) ->
  (C1 <> 0 -> C1 <> CAP -> (exists n, In (pF, n) (user_blocks A1)) /\ In (ptr_addr L1 pF) (rv_nc V')) ->
  (C1 <> 0 -> C1 = CAP -> (exists n, In (pF, n) (user_blocks A0)) /\ In (ptr_addr L0 pF) (rv_nc V0) /\
     ~ In (ptr_addr L0 pF) (map fst dels)) ->
  (forall p n n', In (p, n) (user_blocks A0) -> In (p, n') (user_blocks A4) -> In (ptr_addr L0 p) (rv_nc V0) ->
     ~ In (ptr_addr L0 p) (map fst dels) -> In (ptr_addr L4 p) (rv_nc V')) ->
  forall e0, In e0 M4 -> (In e0 M0 /\ ~ In (ptr_addr L0 (fst e0)) (map fst dels)) \/ In (ptr_addr L4 (fst e0)) (rv_nc V').
Proof.
  cbv zeta. intros U0 U1 U2 U3 U4 N0 N1 N3 Y1 Y2 Y3 Y4 K1 K2 F3 F4 SC PP Ehc Eph PH PE PF1 PF2 HK e0 He4.
  destruct (F4 e0 He4) as (He3 & Hfr). pose proof (F3 e0 He3) as He2.
  destruct (U4 e0 He4) as (n4 & B4). destruct (U3 e0 He3) as (n3 & B3). destruct (U2 e0 He2) as (n2 & B2).
  destruct (K2 e0 He2) as [Hs|(He1 & Hn1)].
  - rewrite app_nil_r in Hs. apply slot3_in' in Hs as (Hc' & Ep').
    exfalso. destruct (PH Hc') as (_ & Hx). rewrite <- Ep' in Hx. apply (Hfr _ Hx).
    rewrite <- (Y3 (fst e0) n2 n3 B2 B3). symmetry. exact (sptr_at L3 A3 (fst e0) n3 _ N3 B3 eq_refl).
  - destruct (U1 e0 He1) as (n1 & B1).
    destruct (K1 e0 He1) as [Hs|(He0 & Hn0)].
    + rewrite app_nil_r in Hs. apply in_app_or in Hs as [Hs|Hs]; apply slot3_in' in Hs as (Hc & Hp).
      * destruct (Z.eq_dec C1 CAP) as [EC|EC].
        -- destruct (PF2 Hc EC) as ((n0 & B0) & Hv & Hd). rewrite <- Hp in B0, Hv, Hd. right.
           exact (HK (fst e0) n0 n4 B0 B4 Hv Hd).
        -- destruct (PF1 Hc EC) as (_ & Hv). rewrite <- Hp in Hv. right.
           rewrite (Y4 (fst e0) n3 n4 B3 B4), (Y3 (fst e0) n2 n3 B2 B3), (Y2 (fst e0) n1 n2 B1 B2). exact Hv.
      * exfalso. assert (Hx : In (ptr_addr L1 pev1) (map fst (src_dels h3)))
          by (apply (PE Hc); exists n1; rewrite <- Hp; exact B1).
        rewrite <- Hp in Hx. apply (Hfr _ Hx).
        rewrite <- (Y2 (fst e0) n1 n2 B1 B2), <- (Y3 (fst e0) n2 n3 B2 B3). symmetry.
        exact (sptr_at L3 A3 (fst e0) n3 _ N3 B3 eq_refl).
    + left. split; [exact He0|]. intros Hx. destruct (U0 e0 He0) as (n0 & B0).
      assert (Ep : sptr_of L0 A0 (ptr_addr L0 (fst e0)) = fst e0) by exact (sptr_at L0 A0 (fst e0) n0 _ N0 B0 eq_refl).
      unfold src_dels in Hx. rewrite !map_app, !in_app_iff in Hx.
      destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
      * apply Hn0. rewrite <- Ep. apply SC. rewrite !map_app, !in_app_iff. left. exact Hx.
      * apply Hn0. rewrite <- Ep. apply SC. rewrite !map_app, !in_app_iff. right. left. exact Hx.
      * apply (Hfr (ptr_addr L0 (fst e0))); [apply PP; apply in_app_iff; left; exact Hx|].
        rewrite <- (Y1 (fst e0) n0 n1 B0 B1), <- (Y2 (fst e0) n1 n2 B1 B2), <- (Y3 (fst e0) n2 n3 B2 B3).
        symmetry. exact (sptr_at L3 A3 (fst e0) n3 _ N3 B3 eq_refl).
      * apply (Hfr (ptr_addr L0 (fst e0))); [apply PP; apply in_app_iff; right; exact Hx|].
        rewrite <- (Y1 (fst e0) n0 n1 B0 B1), <- (Y2 (fst e0) n1 n2 B1 B2), <- (Y3 (fst e0) n2 n3 B2 B3).
        symmetry. exact (sptr_at L3 A3 (fst e0) n3 _ N3 B3 eq_refl).
      * apply Hn0. rewrite <- Ep. apply SC. rewrite !map_app, !in_app_iff. right. right. exact Hx.
      * apply arr_sz_in in Hx as (Ex & Hc0). apply Hn1. rewrite Ehc. rewrite Eph.
        replace (sptr_of L1 A1 (hl_v (hs_held h))) with (fst e0); [exact (slot3_mem _ _ Hc0)|].
        rewrite <- Ex, <- (Y1 (fst e0) n0 n1 B0 B1). symmetry. exact (sptr_at L1 A1 (fst e0) n1 _ N1 B1 eq_refl).
Qed.

Lemma blk_nonneg L A x m : WF A -> In (x, m) (blocks L A) -> 0 <= m.
Proof.
  intros HW Hb. apply relay_remove_b_lem.rk_blocks_in in Hb as (p & _ & Hp). exact (relay_remove_b_lem.rk_ub_nonneg A p m HW Hp).
Qed.

Lemma rec_cred_sum_nn c P : 0 <= prom_c P c.
Proof. apply prom_c_nonneg. Qed.

Lemma cred_le_prom hj h i c : In (h, i) hj -> cred h c <= prom_c (pend_view hj) c.
Proof.
  intros Hin. apply in_split in Hin as (hj1 & hj2 & ->). unfold pend_view. rewrite map_app. cbn [map fst].
  pose proof (prom_c_nonneg (map (fun p => map snd (hl_recs (hs_pending (fst p)))) hj1) c) as N1.
  pose proof (prom_c_nonneg (map (fun p => map snd (hl_recs (hs_pending (fst p)))) hj2) c) as N2.
  unfold prom_c in *. rewrite zsum_app, zsum_cons. unfold cred. lia.
Qed.

Lemma credb_le_promb hj h i : In (h, i) hj -> credb h <= promb (pend_view hj).
Proof.
  intros Hin. apply in_split in Hin as (hj1 & hj2 & ->). unfold pend_view. rewrite map_app. cbn [map fst].
  pose proof (promb_nonneg (map (fun p => map snd (hl_recs (hs_pending (fst p)))) hj1)) as N1.
  pose proof (promb_nonneg (map (fun p => map snd (hl_recs (hs_pending (fst p)))) hj2)) as N2.
  unfold promb in *. rewrite zsum_app, zsum_cons. unfold credb. lia.
Qed.

Lemma ncb16 x c : ncb (16 * x) c = arr_c x c.
Proof.
  unfold ncb, arr_c. destruct (Z.eqb_spec x 0) as [E|E]; [subst x; reflexivity|].
  rewrite (proj2 (Z.eqb_neq (16 * x) 0)) by lia. reflexivity.
Qed.

Lemma src_cls h c : zsum (fun t => one_if c (band (snd t))) (src_dels h) =
  arr_c (hl_cap (hs_pending h)) c + one_if c (band PARTIAL_BYTES) + arr_c (hl_cap (hs_expected h)) c +
  arr_c (hl_cap (hs_held h)) c.
Proof.
  unfold src_dels, arr_sz, arr_c. rewrite !zsum_app, zsum_cons, zsum_nil.
  destruct (hl_cap (hs_pending h) =? 0); destruct (hl_cap (hs_expected h) =? 0); destruct (hl_cap (hs_held h) =? 0);
    rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Lemma src_sz h : zsum snd (src_dels h) =
  16 * hl_cap (hs_pending h) + PARTIAL_BYTES + 16 * hl_cap (hs_expected h) + 16 * hl_cap (hs_held h).
Proof.
  unfold src_dels, arr_sz. rewrite !zsum_app, zsum_cons, zsum_nil.
  destruct (Z.eqb_spec (hl_cap (hs_pending h)) 0); destruct (Z.eqb_spec (hl_cap (hs_expected h)) 0);
    destruct (Z.eqb_spec (hl_cap (hs_held h)) 0); rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Ltac ired := cbv iota beta; try change (0 =? 0) with true; cbv iota beta.

Lemma entry_cls e c : (re_hp e <> 0 -> re_kh e <> 0) ->
  zsum (fun t => one_if c (band (snd t))) (entry_dels e) = ncb (re_cap e) c + ncb (ent_ka e) c.
Proof.
  intros Hkh. unfold entry_dels, ent_ka, ncb. rewrite zsum_app.
  destruct (Z.eqb_spec (re_cap e) 0); destruct (Z.eqb_spec (re_hp e) 0) as [H|H]; ired;
    try rewrite (proj2 (Z.eqb_neq _ _) (Hkh H)); ired; rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Lemma entry_sz e : (re_hp e <> 0 -> re_kh e <> 0) -> zsum snd (entry_dels e) = re_cap e + ent_ka e.
Proof.
  intros Hkh. unfold entry_dels, ent_ka. rewrite zsum_app.
  destruct (Z.eqb_spec (re_cap e) 0); destruct (Z.eqb_spec (re_hp e) 0) as [H|H]; ired;
    rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Lemma p4_dl_le out CAP q1 C1 e h c : (re_hp e <> 0 -> re_kh e <> 0) ->
  ncb C1 c - ncb CAP c - ncb (re_cap e) c - ncb (ent_ka e) c - zsum (fun t => one_if c (band (snd t))) (src_dels h) <=
  dl_of (out_move_dels out CAP q1 C1 ++ entry_dels e ++ src_dels h) (out_move_adds out CAP q1 C1) c.
Proof.
  intros Hkh. unfold dl_of. rewrite !zsum_app, (entry_cls e c Hkh).
  assert (Eo : ncb C1 c - ncb CAP c <=
     zsum (fun t => one_if c (band (snd t))) (out_move_adds out CAP q1 C1) -
     zsum (fun t => one_if c (band (snd t))) (out_move_dels out CAP q1 C1)).
  { pose proof (one_if_b c (band C1)). pose proof (one_if_b c (band CAP)).
    unfold out_move_dels, out_move_adds, out_same, ncb.
    destruct (Z.eqb_spec q1 out); destruct (Z.eqb_spec C1 CAP) as [EC|EC]; cbn [andb orb];
      destruct (Z.eqb_spec CAP 0); destruct (Z.eqb_spec C1 0); rewrite ?zsum_cons, ?zsum_nil; cbn [snd];
      try (subst; lia); lia. }
  lia.
Qed.

Lemma p4_db_eq out CAP q1 C1 e h : (re_hp e <> 0 -> re_kh e <> 0) ->
  db_of (out_move_dels out CAP q1 C1 ++ entry_dels e ++ src_dels h) (out_move_adds out CAP q1 C1) =
  C1 - CAP - (re_cap e + ent_ka e) - zsum snd (src_dels h).
Proof.
  intros Hkh. unfold db_of. rewrite !zsum_app, (entry_sz e Hkh).
  unfold out_move_dels, out_move_adds, out_same.
  destruct (Z.eqb_spec q1 out); destruct (Z.eqb_spec C1 CAP) as [EC|EC]; cbn [andb orb];
    destruct (Z.eqb_spec CAP 0); rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Lemma len_ce (l : list rentry) : (length (concat (map entry_nc l)) <= 2 * length l)%nat.
Proof.
  induction l as [|x l IH]; [cbn; lia|]. cbn [map concat]. rewrite length_app. cbn [length].
  assert (length (entry_nc x) <= 2)%nat
    by (unfold entry_nc; rewrite length_app; destruct (re_cap x =? 0); destruct (re_hp x =? 0); ired; cbn [length]; lia).
  lia.
Qed.

Lemma len_cs (l : list (hsrc * nat)) : (length (concat (map (fun p => src_nc (fst p)) l)) <= 4 * length l)%nat.
Proof.
  induction l as [|x l IH]; [cbn; lia|]. cbn [map concat]. rewrite length_app. cbn [length].
  assert (length (src_nc (fst x)) <= 4)%nat.
  { unfold src_nc. rewrite !length_app. pose proof (arr_nc_len (hs_pending (fst x))).
    pose proof (arr_nc_len (hs_expected (fst x))). pose proof (arr_nc_len (hs_held (fst x))). cbn [length]. lia. }
  lia.
Qed.

Theorem p4_misT_start pl K L A b al alb G out es hj q e h i CAP qs :
  RI3_ledger rv_wt pl K (view_of G out es hj) L A b al alb -> res_ok_pack3 A b -> List.NoDup (map fst (blocks L A)) ->
  nth_error es q = Some e -> nth_error hj q = Some (h, i) -> (length es <= 4)%nat -> (length hj <= 4)%nat ->
  (re_hp e <> 0 -> re_kh e <> 0) -> (CAP = 0 -> forall m, ~ In (out, m) (blocks L A)) ->
  exists S, misT (slot3 CAP (resolveF qs (known_at L A out)) ++
                  dslots qs e h (drain_start (known_at L A) (known_at L A out) e h) ++ S)
    (0 + res3 CAP + dres e h) (p3_mis b).
Proof.
  intros HL HA HB Hqe Hqh Hes Hhj Hkh HO0.
  pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HI & _) & _).
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (HN & HU & _) & _).
  destruct (nth_error_split es q Hqe) as (es1 & es2 & Ees & Les).
  destruct (nth_error_split hj q Hqh) as (hj1 & hj2 & Ehj & Lhj).
  exists (map (sptr_of L A) (G :: concat (map entry_nc es1) ++ concat (map entry_nc es2) ++
    concat (map (fun p => src_nc (fst p)) hj1) ++ concat (map (fun p => src_nc (fst p)) hj2) ++
    arr_nc (hs_pending h) ++ [hs_partial h] ++ arr_nc (hs_held h))).
  split; [exact HN|]. split.
  - intros p Hp. apply in_map_iff in Hp as (e0 & <- & He0).
    destruct (HU e0 He0) as (_ & n & Hb).
    assert (Hx : In (ptr_addr L (fst e0)) (rv_nc (view_of G out es hj))).
    { apply HI. unfold mis_addrs. exact (in_map (fun e1 => ptr_addr L (fst e1)) _ e0 He0). }
    rewrite <- (sptr_at L A (fst e0) n _ HB Hb eq_refl).
    assert (Hxb : In (ptr_addr L (fst e0), n) (blocks L A))
      by (unfold blocks; exact (in_map (fun b0 => (ptr_addr L (fst b0), snd b0)) _ (fst e0, n) Hb)).
    set (x := ptr_addr L (fst e0)) in *. clearbody x. clear He0 Hb.
    cbn [resolve da_buf da_hp da_ev drain_start known_at].
    cbn [view_of rv_nc] in Hx. rewrite Ees, Ehj in Hx. rewrite !map_app, !concat_app in Hx. cbn [map concat fst] in Hx.
    rewrite !in_app_iff. unfold dslots, slot3. cbn [resolve da_buf da_hp da_ev drain_start known_at].
    destruct Hx as [Hx|[Hx|Hx]].
    + right. right. apply in_map. left. exact Hx.
    + destruct (Z.eqb_spec CAP 0) as [E|E].
      * exfalso. subst x. exact (HO0 E n Hxb).
      * left. left. rewrite Hx. reflexivity.
    + rewrite !in_app_iff in Hx.
      destruct Hx as [[Hx|[Hx|Hx]]|[Hx|[Hx|Hx]]].
      * right. right. apply in_map. right. rewrite !in_app_iff. left. exact Hx.
      * unfold entry_nc in Hx. apply in_app_or in Hx as [Hx|Hx].
        -- destruct (Z.eqb_spec (re_cap e) 0) as [C|C]; [destruct Hx|]. destruct Hx as [Hx|[]].
           right. left. rewrite !in_app_iff. left. left. rewrite Hx. reflexivity.
        -- destruct (Z.eqb_spec (re_hp e) 0) as [C|C]; [destruct Hx|]. destruct Hx as [Hx|[]].
           assert (Ek : (ent_ka e =? 0) = false)
             by (unfold ent_ka; rewrite (proj2 (Z.eqb_neq _ _) C); apply Z.eqb_neq; exact (Hkh C)).
           right. left. rewrite Ek, !in_app_iff. right. left. left. rewrite Hx. reflexivity.
      * right. right. apply in_map. right. rewrite !in_app_iff. right. left. exact Hx.
      * right. right. apply in_map. right. rewrite !in_app_iff. right. right. left. exact Hx.
      * unfold src_nc in Hx. rewrite !in_app_iff in Hx. destruct Hx as [Hx|[Hx|[Hx|Hx]]].
        -- right. right. apply in_map. right. rewrite !in_app_iff. right. right. right. right. left. exact Hx.
        -- right. right. apply in_map. right. rewrite !in_app_iff. right. right. right. right. right. left. exact Hx.
        -- unfold arr_nc in Hx. destruct (Z.eqb_spec (hl_cap (hs_expected h)) 0) as [C|C]; [destruct Hx|].
           destruct Hx as [Hx|[]]. right. left. rewrite !in_app_iff. right. right. left. rewrite Hx. reflexivity.
        -- right. right. apply in_map. right. rewrite !in_app_iff. right. right. right. right. right. right. exact Hx.
      * right. right. apply in_map. right. rewrite !in_app_iff. right. right. right. left. exact Hx.
  - rewrite !length_app, length_map. cbn [length]. rewrite !length_app. cbn [length].
    unfold dslots. rewrite !length_app.
    pose proof (slot3_res CAP (resolveF qs (known_at L A out))) as R1.
    pose proof (slot3_res (re_cap e) (resolveF qs (da_buf (drain_start (known_at L A) (known_at L A out) e h)))) as R2.
    pose proof (slot3_res (ent_ka e) (resolveF qs (da_hp (drain_start (known_at L A) (known_at L A out) e h)))) as R3.
    pose proof (slot3_res (hl_cap (hs_expected h)) (resolveF qs (da_ev (drain_start (known_at L A) (known_at L A out) e h))))
      as R4.
    unfold dres. pose proof (len_ce es1). pose proof (len_ce es2). pose proof (len_cs hj1). pose proof (len_cs hj2).
    pose proof (arr_nc_len (hs_pending h)). pose proof (arr_nc_len (hs_held h)).
    assert (L1 : (length es1 + length es2 <= 3)%nat) by (rewrite Ees, length_app in Hes; cbn [length] in Hes; lia).
    assert (L2 : (length hj1 + length hj2 <= 3)%nat) by (rewrite Ehj, length_app in Hhj; cbn [length] in Hhj; lia).
    unfold NC_MAX. lia.
Qed.
