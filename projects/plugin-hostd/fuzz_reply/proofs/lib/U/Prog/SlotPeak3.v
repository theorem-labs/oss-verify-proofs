From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT SlotKept SlotPack
  AllocPack AllocPackRoom AllocBound AllocPack3 AllocPack3Room AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotInv SlotParse SlotCaps3 SlotRI3
  RelayRunT RelayRunF RelayRep HarnessRep RelayModel RelayKeys ListTr HarnessTr send_line_b_c drain_b_c SlotRun3
  SlotP5R3G SlotDrain3Aux SlotDrain3 SlotP5R3 SlotRI3P.
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tr_peak_mono tr Bd Bd' : Bd <= Bd' -> tr_peak tr Bd -> tr_peak tr Bd'.
Proof.
  intros Hle H tr1 e tr2 E. pose proof (H tr1 e tr2 E) as H1.
  destruct e; cbv beta iota in H1 |- *; first [exact I | lia].
Qed.

Lemma tr_peak_frees (tr : trF) Bd : Forall (fun e : tev => match e with RFree _ _ => True | _ => False end) tr ->
  tr_peak tr Bd.
Proof.
  intros HF tr1 e tr2 E. subst tr. apply Forall_app in HF as [_ HF]. pose proof (Forall_inv HF) as Hx.
  destruct e; cbv beta iota in Hx |- *; first [exact I | destruct Hx].
Qed.

Definition cpk (Bd cap n : Z) (ks : list Z) : Prop :=
  Forall (fun m => 0 <= m) ks /\ 0 <= n /\ n + zlen ks < 4194304 /\ zsum (fun m => m) ks <= NMAX /\
  zsum (fun m => m) ks + arr_pot cap + 67108864 <= Bd.

Lemma cpk_mono Bd Bd' cap n ks : Bd <= Bd' -> cpk Bd cap n ks -> cpk Bd' cap n ks.
Proof. intros Hle (H1 & H2 & H3 & H4 & H5). unfold cpk. split; [exact H1|]. lia. Qed.

Lemma cpk_drop Bd cap n n' ks : cpk Bd cap n ks -> 0 <= n' <= n -> cpk Bd cap n' ks.
Proof. intros (H1 & H2 & H3 & H4 & H5) Hn. unfold cpk. split; [exact H1|]. lia. Qed.

Lemma cpk_copy Bd cap n m ks : cpk Bd cap n (m :: ks) ->
  (0 <= m <= NMAX /\ m <= Bd) /\ cpk (Bd - m) cap (n + 1) ks.
Proof.
  intros (H1 & H2 & H3 & H4 & H5). apply Forall_cons_iff in H1 as [Hm H1].
  pose proof (zsum_id_nonneg ks H1) as Z0. rewrite zsum_id_cons in H4, H5. pose proof (arr_pot_b cap).
  unfold zlen in H3. cbn [length] in H3. split; [lia|]. unfold cpk, zlen. split; [exact H1|]. lia.
Qed.

Lemma cpk_first Bd n ks : cpk Bd 0 n ks -> 128 <= Bd /\ cpk (Bd - 128) 8 n ks.
Proof.
  intros (H1 & H2 & H3 & H4 & H5). pose proof (zsum_id_nonneg ks H1) as Z0.
  assert (P0 : arr_pot 0 = 134217728) by reflexivity. assert (P8 : arr_pot 8 = 134217600) by reflexivity.
  rewrite P0 in H5. split; [lia|]. unfold cpk. split; [exact H1|]. rewrite P8. lia.
Qed.

Lemma cpk_grow Bd cap ks : cpk Bd cap cap ks -> cap <> 0 ->
  (0 <= 32 * cap <= NMAX /\ 32 * cap <= Bd) /\ cpk (Bd - (32 * cap - 16 * cap)) (2 * cap) cap ks.
Proof.
  intros (H1 & H2 & H3 & H4 & H5) Hc0. pose proof (zsum_id_nonneg ks H1) as Z0.
  assert (Hz : 0 <= zlen ks) by (unfold zlen; lia).
  assert (Hcap : 0 < cap < 4194304) by lia.
  assert (P1 : arr_pot cap = 16 * (8388608 - cap)) by (unfold arr_pot; lia).
  assert (P2 : arr_pot (2 * cap) = 16 * (8388608 - 2 * cap)) by (unfold arr_pot; lia).
  assert (NV : NMAX = 536879104) by reflexivity.
  rewrite P1 in H5. split; [lia|]. unfold cpk. split; [exact H1|]. rewrite P2. lia.
Qed.

Lemma cpk_gm j s ln ks Bd : cpk Bd (sh_cap s) (sh_n s) (gm_keys s ln ++ ks) ->
  tr_peak (gesture_model_tr s ln) Bd /\
  cpk (Bd - tr_db (gesture_model_tr s ln)) (sh_cap (gesture_model_sh j s ln)) (sh_n (gesture_model_sh j s ln)) ks.
Proof.
  assert (NV : NMAX = 536879104) by reflexivity.
  unfold gesture_model_tr, gesture_model_sh, gm_keys. destruct (gesture ln) as [[[|] x]|].
  - destruct (existsb (list_eqb x) (sh_keys s)); cbn [app]; intros HP.
    + split; [apply tr_peak_nil|]. rewrite tr_db_nil, Z.sub_0_r. exact HP.
    + rewrite sh_cap_push, sh_n_push. unfold list_push_tr, list_grow_tr.
      destruct (Z.eqb_spec (sh_n s) (sh_cap s)) as [En|En]; [destruct (Z.eqb_spec (sh_cap s) 0) as [Ec|Ec]|];
        cbn [app].
      * rewrite (grow_cap_00 _ _ En Ec). rewrite Ec in HP.
        destruct (cpk_first _ _ _ HP) as [R1 P1]. destruct (cpk_copy _ _ _ _ _ P1) as [R2 P2].
        split.
        -- apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|].
           apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|apply tr_peak_nil].
        -- rewrite !tr_db_cons, tr_db_nil. cbn [ev_db]. eapply cpk_mono; [|exact P2]. lia.
      * rewrite (grow_cap_2 _ _ En Ec). rewrite En in HP |- *.
        destruct (cpk_grow _ _ _ HP Ec) as [R1 P1]. destruct (cpk_copy _ _ _ _ _ P1) as [R2 P2].
        split.
        -- apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|].
           apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|apply tr_peak_nil].
        -- rewrite !tr_db_cons, tr_db_nil. cbn [ev_db]. eapply cpk_mono; [|exact P2]. lia.
      * rewrite (grow_cap_id _ _ En). destruct (cpk_copy _ _ _ _ _ HP) as [R2 P2].
        split.
        -- apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|apply tr_peak_nil].
        -- rewrite tr_db_cons, tr_db_nil. cbn [ev_db]. eapply cpk_mono; [|exact P2]. lia.
  - destruct (find_key x (sh_keys s)) as [i|]; cbn [app]; intros HP.
    + unfold list_drop_tr, rec_drop_tr. split; [apply tr_peak_free|].
      change (sh_cap (list_drop_sh s i)) with (sh_cap s).
      rewrite tr_db_cons, tr_db_nil. cbn [ev_db].
      apply (cpk_drop _ _ (sh_n s)); [eapply cpk_mono; [|exact HP]; unfold rec_len; lia|].
      pose proof (sh_n_drop s i). split; [unfold sh_n; lia|lia].
    + split; [apply tr_peak_nil|]. rewrite tr_db_nil, Z.sub_0_r. exact HP.
  - cbn [app]. intros HP. split; [apply tr_peak_nil|]. rewrite tr_db_nil, Z.sub_0_r. exact HP.
Qed.

Lemma cpk_cnl rs : forall j s Bd, cpk Bd (sh_cap s) (sh_n s) (cnl_keys j s rs) ->
  tr_peak (check_no_loss_tr j s rs) Bd.
Proof.
  induction rs as [|r rs IH]; intros j s Bd HP; [apply tr_peak_nil|]. cbn [check_no_loss_tr cnl_keys] in *.
  destruct (cpk_gm j s (snd r) _ Bd HP) as [P1 C1].
  apply tr_peak_app; [exact P1|]. apply tr_peak_app; [unfold rec_drop_tr; apply tr_peak_free|].
  apply IH. unfold rec_drop_tr. rewrite tr_db_cons, tr_db_nil. cbn [ev_db].
  eapply cpk_mono; [|exact C1]. unfold rec_len. lia.
Qed.

Lemma cnl_peak3 : forall j s rs, 0 <= sh_cap s -> 0 <= sh_n s -> sh_n s + zlen (cnl_keys j s rs) < 2 ^ 22 ->
  zsum (fun n => n) (cnl_keys j s rs) <= NMAX ->
  tr_peak (check_no_loss_tr j s rs) (zsum (fun n => n) (cnl_keys j s rs) + 201326592).
Proof.
  intros j s rs _ Hn HN HS. apply cpk_cnl. pose proof (arr_pot_b (sh_cap s)). rewrite P22_v in HN.
  unfold cpk. split; [apply cnl_keys_nonneg|]. lia.
Qed.

Lemma steps_peak mxs j g t g' u : steps mxs j g t g' u -> bnd g mxs ->
  forall Bd, zsum (fun m => m) mxs - bkb g + NMAX + zsum (fun n => n) u <= Bd -> tr_peak t Bd.
Proof.
  induction 1 as [j g|j g n t g' u Hn Hs IH|j g n a t g' u Hn Hs IH|j ga gb k a n t g' u Hn Hm Hs IH];
    intros HB Bd HBd.
  - apply tr_peak_nil.
  - pose proof (zsum_id_nonneg u (steps_u _ _ _ _ _ _ Hs)) as ZU. pose proof (bnd_bkb g mxs HB) as BK.
    rewrite zsum_id_cons in HBd. apply tr_peak_cons. cbv beta iota. cbn [ev_db].
    split; [lia|]. apply (IH HB). lia.
  - apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [exact I|]. apply (IH HB). lia.
  - pose proof (zsum_id_nonneg u (steps_u _ _ _ _ _ _ Hs)) as ZU. pose proof (bnd_bkb _ mxs HB) as BK.
    pose proof (bnd_mid ga gb k a mxs HB) as Hk.
    assert (HB' : bnd (ga ++ (n, Ret j) :: gb) mxs) by (apply (bnd_upd ga gb k a); [exact HB|lia]).
    pose proof (bkb_upd ga gb k a n (Ret j)) as EB.
    destruct (Z.eqb_spec k 0) as [Ek|Ek]; apply tr_peak_cons; cbv beta iota; cbn [ev_db];
      (split; [lia|apply (IH HB'); lia]).
Qed.

Lemma sl_ocap f : forall mx no cap rem j o, 0 <= mx ->
  fst (snd (sl_run f mx no cap rem j o)) <= Z.max cap (2 * (no + Z.max 0 rem)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hmx; [cbn [sl_run fst snd]; lia|]. cbn [sl_run]. cbv zeta.
  destruct (Z.leb_spec rem 0) as [Er|Er]; [cbn [fst snd]; lia|].
  match goal with |- context [if ?c then mx else rem] => set (n := if c then mx else rem) in * end.
  assert (Hn : 0 < n <= rem).
  { unfold n. destruct (Z.eqb_spec mx 0); destruct (Z.ltb_spec mx rem); cbn [negb andb]; lia. }
  destruct (Z.ltb_spec cap (no + n)).
  - cbn [fst snd]. pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (Ret j) Hmx). lia.
  - pose proof (IH mx (no + n) cap (rem - n) j o Hmx). lia.
Qed.

Lemma send_ocap live mx no cap len : 0 <= mx ->
  send_line_cap live mx no cap len <= Z.max cap (2 * (no + Z.max 0 len)).
Proof. intros Hmx. unfold send_line_cap. destruct live; [apply sl_ocap; exact Hmx|lia]. Qed.

Lemma lines_ocap live mx ls : forall no cap H ka j o ha ks, 0 <= mx ->
  fst (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks)))) <=
    Z.max cap (2 * (no + zsum (fun l => zlen l + 1) ls)).
Proof.
  induction ls as [|l r IH]; intros no cap H ka j o ha ks Hmx.
  - cbn [lines_run fst snd]. rewrite zsum_nil. lia.
  - cbn [lines_run fst snd]. cbv zeta. rewrite zsum_cons. cbv beta.
    match goal with |- fst (fst (snd (fst (lines_run _ _ ?no1 ?cap1 ?H1 ?ka1 r ?j1 ?o1 ?ha1 ?ks1)))) <= _ =>
      pose proof (IH no1 cap1 H1 ka1 j1 o1 ha1 ks1 Hmx) as X end.
    pose proof (send_ocap live mx no cap (Z.of_nat (length l) + 1) Hmx) as Y.
    pose proof (zsum_nonneg (fun l0 => zlen l0 + 1) r ltac:(intros x _; unfold zlen; lia)) as Z1.
    unfold zlen in *. lia.
Qed.

Lemma with_nul_len rl : Z.of_nat (length (with_nul rl)) = zsum (fun l => zlen l + 1) rl.
Proof.
  induction rl as [|l r IH]; [reflexivity|]. unfold with_nul in *. cbn [map concat]. rewrite !length_app.
  cbn [length]. rewrite zsum_cons. cbv beta. unfold zlen in *. lia.
Qed.

Lemma drain_no lv mx : forall f s j a, 0 <= mx -> J1 (ds_u s) (ds_skip s) (ds_ref s) -> 0 <= ds_off s ->
  exists cs, d3str s = cs ++ d3str (fst (snd (drain_run f lv mx s j a))) /\
    ds_no (fst (snd (drain_run f lv mx s j a))) = ds_no s + zsum (fun l => zlen l + 1) (lines (ds_ref s) cs) /\
    ds_ocap (fst (snd (drain_run f lv mx s j a))) <=
      Z.max (ds_ocap s) (2 * ds_no (fst (snd (drain_run f lv mx s j a)))).
Proof.
  induction f as [|f IH]; intros s j a Hmx HJ Hoff.
  - exists []. cbn [drain_run fst snd app]. rewrite lines_nil, zsum_nil. split; [reflexivity|]. split; lia.
  - cbn [drain_run]. cbv zeta.
    set (g := grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a)) in *.
    destruct (ds_eintr s) eqn:Ee.
    + cbn [fst snd].
      match goal with |- context [drain_run f lv mx ?s1 ?j1 ?a1] =>
        destruct (IH s1 j1 a1 Hmx HJ Hoff) as (cs & S1 & S2 & S3) end.
      exists cs. split; [exact S1|]. split; [exact S2|exact S3].
    + destruct (ds_pend s) as [|r0 rs] eqn:Ep.
      * cbn [fst snd]. exists []. split; [unfold d3str; rewrite Ep; reflexivity|].
        cbn [ds_no ds_ocap app]. rewrite lines_nil, zsum_nil. split; lia.
      * set (n := Z.min (Z.of_nat (length r0) - ds_off s) (fst (snd g) - Z.of_nat (length (ds_u s)))) in *.
        destruct (Z.leb_spec n 0) as [En|En].
        -- cbn [fst snd]. exists []. split; [unfold d3str; rewrite Ep; reflexivity|].
           cbn [ds_no ds_ocap app]. rewrite lines_nil, zsum_nil. split; lia.
        -- assert (Hn1 : n <= Z.of_nat (length r0) - ds_off s) by apply Z.le_min_l.
           set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)) in *.
           destruct (chunk (ds_u s) (ds_skip s) d) as [[u' sk'] rl] eqn:Ech. cbv beta iota.
           pose proof (chunk_ok (ds_u s) (ds_skip s) (ds_ref s) d HJ) as CK. rewrite Ech in CK. cbv beta iota in CK.
           destruct CK as [Erl HJ2]. subst rl.
           set (ls := lines (ds_ref s) d) in *.
           match goal with |- context [lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls ?j3 (da_out a) (da_hp a) (da_keys a)] =>
             set (j3' := j3) in * end.
           set (sl := lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls j3' (da_out a) (da_hp a) (da_keys a)) in *.
           pose proof (lines_ocap lv mx ls (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3' (da_out a) (da_hp a) (da_keys a)
             Hmx) as M.
           change (lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls j3' (da_out a) (da_hp a) (da_keys a))
             with sl in M.
           destruct (snd (fst sl)) as [[oc' H'] ka'] eqn:E1. cbv beta iota.
           destruct (snd sl) as [[o' ha'] ks'] eqn:E2. cbv beta iota.
           try rewrite E1 in M. cbn [fst] in M.
           cbn [fst snd].
           match goal with |- context [drain_run f lv mx ?s2 ?j4 ?a2] =>
             set (s2' := s2) in *; set (a2' := a2) in *; set (j4' := j4) in * end.
           assert (SE : d3str s = d ++ d3str s2')
             by (unfold d; apply (round_str s s2' r0 rs n Ep Hoff En Hn1); reflexivity).
           assert (HJ2' : J1 (ds_u s2') (ds_skip s2') (ds_ref s2')) by exact HJ2.
           assert (Hoff2 : 0 <= ds_off s2').
           { change (0 <= if ds_off s + n =? Z.of_nat (length r0) then 0 else ds_off s + n).
             destruct (ds_off s + n =? Z.of_nat (length r0)); lia. }
           assert (Xno2 : ds_no s2' = ds_no s + zsum (fun l => zlen l + 1) ls)
             by (rewrite <- with_nul_len; reflexivity).
           assert (Xoc2 : ds_ocap s2' = oc') by reflexivity.
           assert (Xref2 : ds_ref s2' = feed (ds_ref s) d) by reflexivity.
           destruct (IH s2' j4' a2' Hmx HJ2' Hoff2) as (cs & S1 & S2 & S3).
           rewrite Xref2 in S2. rewrite Xoc2 in S3.
           pose proof (zsum_nonneg (fun l => zlen l + 1) (lines (feed (ds_ref s) d) cs)
             ltac:(intros x _; unfold zlen; lia)) as Z1.
           exists (d ++ cs). split; [|split].
           ++ rewrite SE, S1, app_assoc. reflexivity.
           ++ rewrite lines_app, zsum_app. fold ls. lia.
           ++ lia.
Qed.

Lemma drain_peak3 (e : rentry) (h : hsrc) (lv : bool) (mx NO CAP : Z) (j : nat) (a : dadr) :
  0 <= re_cap e -> 0 <= ent_ka e -> J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) -> 0 <= hs_off h ->
  re_nheld e + Z.of_nat (length (pending_stream h)) < 2 ^ 26 ->
  (hl_cap (hs_expected h) = 0 \/ exists k, 0 <= k /\ hl_cap (hs_expected h) = 8 * 2 ^ k) ->
  hl_n (hs_expected h) + Z.of_nat (length (pending_stream h)) < 2 ^ 25 ->
  0 <= mx -> 0 <= NO <= CAP -> ds_ocap (drain_fin lv mx NO CAP e h) <= NMAX ->
  (forall Bd, NMAX / 2 + Z.of_nat (length (pending_stream h)) + 6000 + 32768 + 2 ^ 30 + NMAX + credb h <= Bd ->
     tr_peak (drain_tr lv mx NO CAP e h j a) Bd) /\
  tr_db (drain_tr lv mx NO CAP e h j a) <= ds_ocap (drain_fin lv mx NO CAP e h) - CAP + 2 ^ 30 + 32768 + credb h.
Proof.
  intros Hcap Hka HJ Hoff Hnh Hpow Hen Hmx HNO HN.
  unfold drain_fin, drain_tr, drain_go in *.
  set (f := S (S (length (pending_stream h)))) in *.
  set (s0 := drain_init NO CAP e h) in *.
  rewrite (drain_st lv mx f s0 0 dadr0 j a) in HN |- *.
  set (sF := fst (snd (drain_run f lv mx s0 j a))) in *.
  set (aF := snd (snd (drain_run f lv mx s0 j a))) in *.
  set (td := fst (drain_run f lv mx s0 j a)) in *.
  assert (HL0 : zlen (d3str s0) = Z.of_nat (length (pending_stream h)))
    by (unfold s0; rewrite d3str_init; unfold zlen, bzs; rewrite length_map; reflexivity).
  assert (HD0 : d3I s0).
  { unfold d3I. rewrite HL0. unfold s0, drain_init.
    cbn [ds_u ds_skip ds_ref ds_cap ds_ka ds_ocap ds_off ds_ecap ds_en ds_H].
    split; [exact HJ|]. split; [exact Hcap|]. split; [exact Hka|]. split; [lia|]. split; [exact Hoff|].
    split; [exact Hpow|]. split; [exact Hen|].
    unfold zlen, keys_texts, re_nheld in *. rewrite length_map. exact Hnh. }
  set (mxs := [ds_ocap sF; Z.max (re_cap e) 32768; Z.max (ent_ka e) (2 ^ 29);
               Z.max (16 * hl_cap (hs_expected h)) (2 ^ 29)]).
  pose proof P29 as E29. pose proof P26 as E26. pose proof P25 as E25.
  assert (EN : NMAX = 536879104) by reflexivity. assert (EN2 : NMAX / 2 = 268439552) by reflexivity.
  assert (E30 : 2 ^ 30 = 1073741824) by reflexivity.
  assert (Hc0 : 0 <= hl_cap (hs_expected h)).
  { destruct Hpow as [->|(k & Hk & ->)]; [lia|]. pose proof (Z.pow_nonneg 2 k ltac:(lia)). lia. }
  assert (HmF : CAP <= ds_ocap sF)
    by exact (drain_ocap_mono lv mx f s0 j a ltac:(unfold s0, drain_init; cbn [ds_ocap]; lia)).
  destruct (drain_steps lv mx mxs f s0 j a HD0 ltac:(unfold mxs; cbn [nth]; lia) ltac:(unfold mxs; cbn [nth]; lia)
    ltac:(unfold mxs; cbn [nth]; lia) ltac:(unfold mxs; cbn [nth]; exact HN)
    ltac:(unfold mxs, sF; cbn [nth]; apply Z.le_refl)) as (u & cs & ST & SE & SC).
  change (fst (snd (drain_run f lv mx s0 j a))) with sF in ST, SE.
  change (snd (snd (drain_run f lv mx s0 j a))) with aF in ST.
  change (fst (drain_run f lv mx s0 j a)) with td in ST.
  set (g0 := [(CAP, da_out a); (re_cap e, da_buf a); (ent_ka e, da_hp a); (16 * hl_cap (hs_expected h), da_ev a)]).
  change (d3sig s0 a) with g0 in ST.
  assert (HB0 : bnd g0 mxs).
  { unfold bnd, g0, mxs. constructor; [cbv beta; cbn [fst]; lia|]. constructor; [cbv beta; cbn [fst]; lia|].
    constructor; [cbv beta; cbn [fst]; lia|]. constructor; [cbv beta; cbn [fst]; lia|]. constructor. }
  assert (HJw : ls_k (hs_state h) = false -> zlen (ls_w (hs_state h)) <= 6000 /\ nozero (ls_w (hs_state h))).
  { destruct HJ as (Hk & Hw & Hl & Hz). intros E. rewrite <- Hw by (rewrite Hk; exact E).
    split; [unfold zlen; apply LL_le; exact Hl|exact Hz]. }
  assert (ENEW : lines (hs_state h) (bzs (pending_stream h)) =
                 lines (hs_state h) cs ++ lines (feed (hs_state h) cs) (d3str sF)).
  { rewrite <- lines_app, <- SE. unfold s0. rewrite d3str_init. reflexivity. }
  assert (LFN : Forall (fun l => zlen l <= 6000) (lines (hs_state h) (bzs (pending_stream h))))
    by (apply lines_len6; intros E; exact (proj1 (HJw E))).
  destruct (new_cred h HJw) as [_ CR2].
  rewrite ENEW in LFN, CR2.
  destruct (chg_new (lines (hs_state h) cs) (lines (feed (hs_state h) cs) (d3str sF)) LFN) as [_ CN2].
  destruct SC as [_ SC2].
  assert (Er : ds_ref s0 = hs_state h) by reflexivity. rewrite Er in SC2.
  pose proof (ekl_line _ LFN) as (_ & _ & _ & EK).
  pose proof (zsum_id_nonneg _ EK) as EK0.
  assert (UZ : zsum (fun n => n) u <= credb h) by lia.
  destruct (drain_no lv mx f s0 j a Hmx HJ Hoff) as (cs' & SE' & NO' & OC').
  change (fst (snd (drain_run f lv mx s0 j a))) with sF in SE', NO', OC'.
  change (ds_no s0) with NO in NO'. change (ds_ref s0) with (hs_state h) in NO'.
  change (ds_ocap s0) with CAP in OC'.
  pose proof (lines_mass cs' (hs_state h)) as LM.
  assert (Lcs : zlen cs' <= Z.of_nat (length (pending_stream h))).
  { rewrite <- HL0, SE'. unfold zlen. rewrite length_app. lia. }
  assert (Lw : (if ls_k (hs_state h) then 0 else zlen (ls_w (hs_state h))) <= 6000).
  { destruct (ls_k (hs_state h)) eqn:Ek; cbv beta iota; [lia|]. exact (proj1 (HJw eq_refl)). }
  assert (HG : ds_ocap sF - CAP <= NMAX / 2 + Z.of_nat (length (pending_stream h)) + 6000) by lia.
  assert (Ebkb : bkb g0 = CAP + re_cap e + ent_ka e + 16 * hl_cap (hs_expected h))
    by (unfold bkb, g0, zsum; cbn [fold_right fst]; lia).
  assert (Emx : zsum (fun m => m) mxs = ds_ocap sF + Z.max (re_cap e) 32768 + Z.max (ent_ka e) (2 ^ 29) +
                                       Z.max (16 * hl_cap (hs_expected h)) (2 ^ 29))
    by (unfold mxs, zsum; cbn [fold_right]; lia).
  split.
  - intros Bd HBd. apply (steps_peak mxs j g0 td (d3sig sF aF) u ST HB0). rewrite Emx, Ebkb. lia.
  - pose proof (bnd_nonneg _ _ HB0) as HG0.
    destruct (steps_eff _ _ _ _ _ _ ST HG0) as (_ & _ & DB).
    pose proof (bnd_bkb _ _ (steps_bnd _ _ _ _ _ _ ST HB0)) as BK.
    rewrite Emx in BK. rewrite Ebkb in DB. lia.
Qed.
