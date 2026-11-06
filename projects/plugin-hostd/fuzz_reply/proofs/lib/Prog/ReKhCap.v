From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel RelayKeys gestures_end_b_c
  RelayRep HarnessRep drain_b_c relay_remove_b_c SlotParse SlotDrain3Aux SlotDrain3 SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayCap SlotPass2Aux.
Import ListNotations.
Local Open Scope Z_scope.

Lemma re_kh_lines_run_max : forall live mx ls no cap H ka j o ha ks,
  snd (snd (fst (lines_run live mx no cap H ka ls j o ha ks))) <=
    Z.max ka (8 * (Z.of_nat (length H) + Z.of_nat (length (ekl ls)))) /\
  Z.of_nat (length (snd (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks)))))) <=
    Z.of_nat (length H) + Z.of_nat (length (ekl ls)) /\
  (ka = 0 \/ 8 <= ka ->
   snd (snd (fst (lines_run live mx no cap H ka ls j o ha ks))) = 0 \/
   8 <= snd (snd (fst (lines_run live mx no cap H ka ls j o ha ks)))).
Proof.
  intros live mx ls. induction ls as [|l r IH]; intros no cap H ka j o ha ks.
  - cbn [lines_run fst snd]. unfold ekl. cbn [map concat length].
    split; [lia|]. split; [lia|]. intros K; exact K.
  - cbn [lines_run fst snd]. cbv zeta. cbn [fst snd].
    change (ekl (l :: r)) with (ek1 l ++ ekl r). rewrite (length_app (ek1 l) (ekl r)).
    match goal with |- context [lines_run live mx ?n1 ?c1 (seen_arr H l) ?k1 r ?j1 ?o1 ?ha1 ?ks1] =>
      destruct (IH n1 c1 (seen_arr H l) k1 j1 o1 ha1 ks1) as (I1 & I2 & I3) end.
    match goal with |- context [snd (fst (seen_tr H ka l ?jj ha ks))] =>
      assert (SE : snd (fst (seen_tr H ka l jj ha ks)) <=
                     Z.max ka (8 * (Z.of_nat (length H) + Z.of_nat (length (ek1 l)))) /\
                   Z.of_nat (length (seen_arr H l)) <= Z.of_nat (length H) + Z.of_nat (length (ek1 l)) /\
                   (ka = 0 \/ 8 <= ka ->
                    snd (fst (seen_tr H ka l jj ha ks)) = 0 \/ 8 <= snd (fst (seen_tr H ka l jj ha ks))))
    end.
    { unfold seen_tr, seen_arr, ek1.
      destruct (gesture l) as [[[|] x]|]; [destruct (index_of x H) as [i|]|destruct (index_of x H) as [i|]|];
        cbn [fst snd length].
      - split; [lia|]. split; [lia|]. intros K; exact K.
      - rewrite length_app. cbn [length]. split; [lia|]. split; [lia|]. intros _; right; lia.
      - unfold swap_remove. pose proof (firstn_le_length (length H - 1) (set_nth i (last H []) H)) as Ls.
        split; [lia|]. split; [lia|]. intros K; exact K.
      - split; [lia|]. split; [lia|]. intros K; exact K.
      - split; [lia|]. split; [lia|]. intros K; exact K. }
    destruct SE as (S1 & S2 & S3).
    split; [lia|]. split; [lia|]. intros K. exact (I3 (S3 K)).
Qed.

Lemma re_kh_upper : forall (live : bool) (mx NO CAP : Z) (e e' : rentry) (h : hsrc),
  (re_eof e = 0 -> re_skip e = hs_overlong h /\ (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h))) ->
  (re_skip e = 0 \/ re_skip e = 1) ->
  Z.of_nat (length (re_U e)) = re_used e -> re_used e <= 6000 -> ~ In (Z_to_bv 8 0) (re_U e) ->
  0 <= hs_off h ->
  Forall (fun k => 14 <= Z.of_nat (length (key_text k))) (re_keys e) ->
  keys_total (re_keys e) + Z.of_nat (length (pending_stream h)) + (if re_skip e =? 0 then re_used e else 0) <
    2 ^ 26 ->
  (re_hp e <> 0 -> re_kh e <= 2 ^ 25) ->
  ent_ka e' = ds_ka (after_drain live mx NO CAP e h) ->
  re_hp e' <> 0 ->
  re_kh e' <= 2 ^ 25.
Proof.
  intros live mx NO CAP e e' h HSK H01 HU HU6 HUZ Hoff HKT HC Hkh E' Hp'.
  assert (P25 : 2 ^ 25 = 33554432) by reflexivity.
  assert (P26 : 2 ^ 26 = 67108864) by reflexivity.
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
  assert (K0 : ent_ka e <= 2 ^ 25).
  { unfold ent_ka. destruct (Z.eqb_spec (re_hp e) 0) as [Z0|Z0]; [lia|exact (Hkh Z0)]. }
  assert (KE : ent_ka e' = re_kh e') by (unfold ent_ka; rewrite (proj2 (Z.eqb_neq _ _) Hp'); reflexivity).
  rewrite <- KE, E'. unfold after_drain.
  destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0]; [|exact K0].
  change (ds_ka (drain_fin live mx NO CAP e h) <= 2 ^ 25).
  destruct (HSK E0) as [SKO SKW].
  assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)).
  { unfold J1, hs_state. cbn [ls_k ls_w]. rewrite SKO.
    split; [reflexivity|]. split.
    - intros F0. apply SKW. destruct H01 as [Q|Q]; [exact Q|]. rewrite <- SKO, Q in F0. discriminate.
    - split; [|exact (SlotPass2Aux.p2_nozero _ HUZ)].
      unfold bzs. rewrite length_map. apply Nat2Z.inj_le. change (Z.of_nat LINE_LIMIT) with 6000. lia. }
  assert (BEG : forall ls, 21 * Z.of_nat (length (ekl ls)) <= Z.of_nat (length (with_nul ls))).
  { induction ls as [|l ls IHl]; [unfold ekl, with_nul; cbn [map concat length]; lia|].
    change (ekl (l :: ls)) with (ek1 l ++ ekl ls). rewrite length_app, RelayCap.with_nul_cons_len.
    assert (B1 : 21 * Z.of_nat (length (ek1 l)) <= Z.of_nat (length l) + 1).
    { unfold ek1. destruct (gesture l) as [[[|] x]|] eqn:Eg; cbn [length]; try lia.
      destruct (gesture_begin l x Eg) as [_ Eb]. pose proof (begin_line_len l Eb) as L20. unfold zlen in L20. lia. }
    lia. }
  assert (KT : forall ks, Forall (fun k => 14 <= Z.of_nat (length (key_text k))) ks ->
                 19 * Z.of_nat (length ks) <= keys_total ks).
  { induction ks as [|k ks IHk]; intros HF; [cbn; lia|].
    apply Forall_cons_iff in HF as [Hk HF]. cbv beta in Hk.
    change (keys_total (k :: ks)) with (Z.of_nat (length (key_text k)) + 5 + keys_total ks).
    specialize (IHk HF). cbn [length]. lia. }
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
  assert (HOV : hs_overlong h = 0 \/ hs_overlong h = 1) by (rewrite <- SKO; exact H01).
  pose proof (reads_bound e h SKO SKW HOV HU) as RB.
  pose proof (BEG (lines (hs_state h) (bzs (pending_stream h)))) as B2.
  pose proof (KT (re_keys e) HKT) as K19.
  lia.
Qed.

Lemma re_kh_lower : forall (live : bool) (mx NO CAP : Z) (e e' : rentry) (h : hsrc),
  (re_hp e <> 0 -> 8 <= re_kh e) ->
  ent_ka e' = ds_ka (after_drain live mx NO CAP e h) ->
  re_hp e' <> 0 -> re_kh e' <> 0 ->
  8 <= re_kh e'.
Proof.
  intros live mx NO CAP e e' h He E' Hp' Hk'.
  assert (RUN : forall f s j a, ds_ka s = 0 \/ 8 <= ds_ka s ->
    ds_ka (fst (snd (drain_run f live mx s j a))) = 0 \/ 8 <= ds_ka (fst (snd (drain_run f live mx s j a)))).
  { intros f. induction f as [|f IH]; intros s j a Hk; [exact Hk|].
    cbn [drain_run]. cbv zeta.
    destruct (ds_eintr s); [cbn [fst snd]; apply IH; exact Hk|].
    destruct (ds_pend s) as [|r0 rs]; [cbn [fst snd ds_ka]; exact Hk|].
    match goal with |- context [if ?c <=? 0 then _ else _] => destruct (c <=? 0) end;
      [cbn [fst snd ds_ka]; exact Hk|].
    match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end. cbv beta iota.
    match goal with |- context [lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11] =>
      pose proof (proj2 (proj2 (re_kh_lines_run_max a1 a2 a7 a3 a4 a5 a6 a8 a9 a10 a11)) Hk) as LK;
      destruct (snd (fst (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11))) as [[oc' H'] ka'] eqn:E1;
      destruct (snd (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)) as [[o' ha'] ks'] eqn:E2
    end.
    try rewrite E1 in LK. cbn [snd] in LK. cbv beta iota. cbn [fst snd].
    apply IH. cbn [ds_ka]. exact LK. }
  assert (K0 : ent_ka e = 0 \/ 8 <= ent_ka e).
  { unfold ent_ka. destruct (Z.eqb_spec (re_hp e) 0) as [Z0|Z0]; [left; reflexivity|right; exact (He Z0)]. }
  assert (K1 : ds_ka (after_drain live mx NO CAP e h) = 0 \/ 8 <= ds_ka (after_drain live mx NO CAP e h)).
  { unfold after_drain. destruct (re_eof e =? 0); [unfold drain_fin, drain_go; apply RUN|]; exact K0. }
  assert (KE : ent_ka e' = re_kh e') by (unfold ent_ka; rewrite (proj2 (Z.eqb_neq _ _) Hp'); reflexivity).
  rewrite <- E', KE in K1. lia.
Qed.
