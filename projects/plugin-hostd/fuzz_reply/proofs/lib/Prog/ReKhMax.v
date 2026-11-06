From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel RelayKeys gestures_end_b_c
  RelayRep HarnessRep drain_b_c relay_remove_b_c SlotParse SlotDrain3Aux SlotDrain3 SlotReads ReKhCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayCap SlotPass2Aux.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ekl_begin_cost : forall ls, 21 * Z.of_nat (length (ekl ls)) <= Z.of_nat (length (with_nul ls)).
Proof.
  induction ls as [|l ls IH]; [unfold ekl, with_nul; cbn [map concat length]; lia|].
  change (ekl (l :: ls)) with (ek1 l ++ ekl ls). rewrite length_app, RelayCap.with_nul_cons_len.
  assert (B1 : 21 * Z.of_nat (length (ek1 l)) <= Z.of_nat (length l) + 1).
  { unfold ek1. destruct (gesture l) as [[[|] x]|] eqn:Eg; cbn [length]; try lia.
    destruct (gesture_begin l x Eg) as [_ Eb]. pose proof (begin_line_len l Eb) as L20. unfold zlen in L20. lia. }
  lia.
Qed.

Lemma keys_total_count : forall ks, Forall (fun k => 14 <= Z.of_nat (length (key_text k))) ks ->
  19 * Z.of_nat (length ks) <= keys_total ks.
Proof.
  induction ks as [|k ks IH]; intros HF; [cbn; lia|].
  apply Forall_cons_iff in HF as [Hk HF]. cbv beta in Hk.
  change (keys_total (k :: ks)) with (Z.of_nat (length (key_text k)) + 5 + keys_total ks).
  specialize (IH HF). cbn [length]. lia.
Qed.

Lemma re_kh_drain_max : forall (live : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc),
  (re_eof e = 0 -> re_skip e = hs_overlong h /\ (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h))) ->
  (re_skip e = 0 \/ re_skip e = 1) ->
  Z.of_nat (length (re_U e)) = re_used e -> re_used e <= 6000 -> ~ In (Z_to_bv 8 0) (re_U e) ->
  0 <= hs_off h ->
  ds_ka (after_drain live mx NO CAP e h) <=
    Z.max (ent_ka e)
      (8 * (Z.of_nat (length (re_keys e)) +
            Z.of_nat (length (ekl (lines (hs_state h) (bzs (pending_stream h))))))).
Proof.
  intros live mx NO CAP e h HSK H01 HU HU6 HUZ Hoff.
  assert (RUN : forall f s j a, J1 (ds_u s) (ds_skip s) (ds_ref s) -> 0 <= ds_off s ->
    exists cs, d3str s = cs ++ d3str (fst (snd (drain_run f live mx s j a))) /\
      ds_ka (fst (snd (drain_run f live mx s j a))) <=
        Z.max (ds_ka s) (8 * (Z.of_nat (length (ds_H s)) + Z.of_nat (length (ekl (lines (ds_ref s) cs))))) /\
      Z.of_nat (length (ds_H (fst (snd (drain_run f live mx s j a))))) <=
        Z.of_nat (length (ds_H s)) + Z.of_nat (length (ekl (lines (ds_ref s) cs)))).
  { intros f. induction f as [|f IH]; intros s j a HJs Hos.
    - exists []. cbn [drain_run fst snd app]. rewrite lines_nil. unfold ekl. cbn [map concat length].
      split; [reflexivity|]. split; lia.
    - cbn [drain_run]. cbv zeta.
      destruct (ds_eintr s).
      + cbn [fst snd].
        match goal with |- context [drain_run f live mx ?s1 ?j1 ?a1] =>
          destruct (IH s1 j1 a1 HJs Hos) as (cs & C1 & C2 & C3) end.
        exists cs. split; [exact C1|]. split; [exact C2|exact C3].
      + destruct (ds_pend s) as [|r0 rs] eqn:Ep.
        * cbn [fst snd]. exists [].
          split; [unfold d3str; cbn [ds_pend ds_off]; rewrite Ep; reflexivity|].
          cbn [ds_ka ds_H]. rewrite lines_nil. unfold ekl. cbn [map concat length]. split; lia.
        * match goal with |- context [if Z.min ?x ?y <=? 0 then _ else _] => set (n := Z.min x y) end.
          destruct (Z.leb_spec n 0) as [En|En].
          -- cbn [fst snd]. exists [].
             split; [unfold d3str; cbn [ds_pend ds_off]; rewrite Ep; reflexivity|].
             cbn [ds_ka ds_H]. rewrite lines_nil. unfold ekl. cbn [map concat length]. split; lia.
          -- assert (Hn1 : n <= Z.of_nat (length r0) - ds_off s) by apply Z.le_min_l.
             set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)).
             destruct (chunk (ds_u s) (ds_skip s) d) as [[u' sk'] rl] eqn:Ech. cbv beta iota.
             pose proof (chunk_ok (ds_u s) (ds_skip s) (ds_ref s) d HJs) as CK. rewrite Ech in CK.
             cbv beta iota in CK. destruct CK as [Erl HJ2]. subst rl.
             match goal with
             | |- context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (lines (ds_ref s) d)
                             ?j3 ?o3 ?h3 ?k3] =>
               pose proof (re_kh_lines_run_max live mx (lines (ds_ref s) d) (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s)
                             j3 o3 h3 k3) as (L1 & L2 & _);
               destruct (snd (fst (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (lines (ds_ref s) d)
                             j3 o3 h3 k3))) as [[oc' H'] ka'] eqn:E1;
               destruct (snd (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (lines (ds_ref s) d)
                             j3 o3 h3 k3)) as [[o' ha'] ks'] eqn:E2
             end.
             try rewrite E1 in L1. try rewrite E1 in L2. cbn [fst snd] in L1, L2. cbv beta iota. cbn [fst snd].
             match goal with |- context [drain_run f live mx ?s2 ?j4 ?a2] =>
               assert (HO2 : 0 <= ds_off s2)
                 by (cbn [ds_off]; destruct (ds_off s + n =? Z.of_nat (length r0)); lia);
               destruct (IH s2 j4 a2 HJ2 HO2) as (cs & C1 & C2 & C3);
               assert (SE : d3str s = d ++ d3str s2)
                 by (unfold d; apply (round_str s s2 r0 rs n Ep Hos En Hn1); reflexivity);
               change (ds_ka s2) with ka' in C2; change (ds_H s2) with H' in C2, C3;
               change (ds_ref s2) with (feed (ds_ref s) d) in C2, C3
             end.
             exists (d ++ cs). split; [rewrite SE, C1, app_assoc; reflexivity|].
             rewrite lines_app, ekl_app, (length_app (ekl (lines (ds_ref s) d))).
             split; lia. }
  unfold after_drain.
  destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0]; [|cbn [ds_ka drain_init]; lia].
  change (ds_ka (drain_fin live mx NO CAP e h) <=
          Z.max (ent_ka e)
            (8 * (Z.of_nat (length (re_keys e)) +
                  Z.of_nat (length (ekl (lines (hs_state h) (bzs (pending_stream h)))))))).
  destruct (HSK E0) as [SKO SKW].
  assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)).
  { unfold J1, hs_state. cbn [ls_k ls_w]. rewrite SKO.
    split; [reflexivity|]. split.
    - intros F0. apply SKW. destruct H01 as [Q|Q]; [exact Q|]. rewrite <- SKO, Q in F0. discriminate.
    - split; [|exact (SlotPass2Aux.p2_nozero _ HUZ)].
      unfold bzs. rewrite length_map. apply Nat2Z.inj_le. change (Z.of_nat LINE_LIMIT) with 6000. lia. }
  unfold drain_fin, drain_go.
  destruct (RUN (S (S (length (pending_stream h)))) (drain_init NO CAP e h) 0%nat dadr0 HJ Hoff)
    as (cs & SE & KA & _).
  assert (EK : ds_ka (drain_init NO CAP e h) = ent_ka e) by reflexivity.
  assert (EH : ds_H (drain_init NO CAP e h) = keys_texts (re_keys e)) by reflexivity.
  assert (ER : ds_ref (drain_init NO CAP e h) = hs_state h) by reflexivity.
  rewrite EK, EH, ER in KA. rewrite d3str_init in SE.
  unfold keys_texts in KA. rewrite length_map in KA.
  assert (BC : Z.of_nat (length (ekl (lines (hs_state h) cs))) <=
               Z.of_nat (length (ekl (lines (hs_state h) (bzs (pending_stream h)))))).
  { rewrite SE, lines_app, ekl_app, length_app. lia. }
  lia.
Qed.

Lemma re_kh_begin_pay : forall (e : rentry) (h : hsrc),
  re_skip e = hs_overlong h -> (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  (hs_overlong h = 0 \/ hs_overlong h = 1) -> Z.of_nat (length (re_U e)) = re_used e ->
  Forall (fun k => 14 <= Z.of_nat (length (key_text k))) (re_keys e) ->
  19 * Z.of_nat (length (re_keys e)) +
  21 * Z.of_nat (length (ekl (lines (hs_state h) (bzs (pending_stream h))))) <=
    keys_total (re_keys e) + Z.of_nat (length (pending_stream h)) +
    (if re_skip e =? 0 then re_used e else 0).
Proof.
  intros e h SKO SKW HOV HU HKT.
  pose proof (reads_bound e h SKO SKW HOV HU) as RB.
  pose proof (ekl_begin_cost (lines (hs_state h) (bzs (pending_stream h)))) as B2.
  pose proof (keys_total_count (re_keys e) HKT) as K19.
  lia.
Qed.

Lemma rkm_grow_cap_set : forall cap used j b,
  (cap = 0 \/ cap = 8192 \/ cap = 16384) -> 0 <= used <= 6000 ->
  (fst (snd (grow_tr cap used j b)) = 0 \/ fst (snd (grow_tr cap used j b)) = 8192 \/
   fst (snd (grow_tr cap used j b)) = 16384).
Proof.
  intros cap used j b HS HU. unfold grow_tr.
  destruct (Z.ltb_spec (cap - used) 4096) as [HG|HG]; [|cbn [fst snd]; lia].
  destruct (Z.eqb_spec cap 0) as [->|HN]; cbn [fst snd]; lia.
Qed.

Lemma rkm_chunk_u_6000 : forall u skip d, zlen (fst (fst (chunk u skip d))) <= 6000.
Proof.
  intros u skip d. assert (LL : Z.of_nat LINE_LIMIT = 6000) by reflexivity.
  unfold chunk. destruct (scan skip u d) as [[sk r] ls].
  destruct (Nat.ltb_spec LINE_LIMIT (length r)) as [HL|HL]; cbn [fst snd]; unfold zlen;
    [cbn [length]; lia|lia].
Qed.

Lemma rkm_drain_cap_set : forall fuel live mx s j a,
  (ds_cap s = 0 \/ ds_cap s = 8192 \/ ds_cap s = 16384) -> zlen (ds_u s) <= 6000 ->
  (ds_cap (fst (snd (drain_run fuel live mx s j a))) = 0 \/
   ds_cap (fst (snd (drain_run fuel live mx s j a))) = 8192 \/
   ds_cap (fst (snd (drain_run fuel live mx s j a))) = 16384).
Proof.
  induction fuel as [|f IH]; intros live mx s j a HSET HU6; [cbn [drain_run fst snd]; lia|].
  cbn [drain_run]. cbv zeta.
  assert (ZU : 0 <= zlen (ds_u s)) by (unfold zlen; pose proof (Nat2Z.is_nonneg (length (ds_u s))); lia).
  assert (GSET : fst (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))) = 0 \/
                 fst (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))) = 8192 \/
                 fst (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))) = 16384)
    by (apply rkm_grow_cap_set; unfold zlen in *; lia).
  destruct (ds_eintr s).
  - match goal with |- context [drain_run f ?lv ?m ?s1 ?jj ?a1] =>
      pose proof (IH lv m s1 jj a1) as IH2 end.
    cbn [ds_cap ds_u] in IH2. specialize (IH2 GSET HU6). cbn [fst snd]. exact IH2.
  - destruct (ds_pend s) as [|r0 rs] eqn:EP; [cbn [fst snd ds_cap]; exact GSET|].
    destruct (Z.leb_spec (Z.min (Z.of_nat (length r0) - ds_off s)
               (fst (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a)))
                - Z.of_nat (length (ds_u s)))) 0) as [Hn0|Hn0];
      [cbn [fst snd ds_cap]; exact GSET|].
    cbv zeta.
    set (cap1 := fst (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a)))) in *.
    set (n := Z.min (Z.of_nat (length r0) - ds_off s) (cap1 - Z.of_nat (length (ds_u s)))) in *.
    set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)) in *.
    assert (CU6 : zlen (fst (fst (chunk (ds_u s) (ds_skip s) d))) <= 6000) by apply rkm_chunk_u_6000.
    destruct (chunk (ds_u s) (ds_skip s) d) as [[u2 sk2] rl2] eqn:Ech.
    cbn [fst snd] in CU6. cbv beta iota.
    match goal with
    | |- context [lines_run ?lv ?m ?no ?cp ?HH ?ka rl2 ?jj ?oo ?hh ?kk] =>
        destruct (snd (fst (lines_run lv m no cp HH ka rl2 jj oo hh kk))) as [[oc2 H2] ka2] eqn:E1;
        destruct (snd (lines_run lv m no cp HH ka rl2 jj oo hh kk)) as [[o2 ha2] ks2] eqn:E2
    end.
    cbv beta iota. cbn [fst snd].
    apply IH; cbn [ds_cap ds_u]; [exact GSET|exact CU6].
Qed.
