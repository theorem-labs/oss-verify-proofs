From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT SlotKept SlotPack
  AllocPack AllocPackRoom AllocBound AllocPack3 AllocPack3Room.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotParse SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep RelayModel RelayKeys ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c drain_b_c SlotRun3 SlotP5R3G SlotDrain3Aux SlotDrain3 SlotP5Res3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require SlotPass2Mv.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition dw1 (cap : Z) (u : list Z) : Z := Z.max cap (DATA_PER * zlen u + 8192).

Definition dw2 (H : list (list Z)) (ka : Z) : Z := Z.max ka (8 * zlen H + 8).

Definition dw4 (n cap : Z) : Z := Z.max (16 * cap) (NC_PER * n + 128).

Definition dwI (s : dstate) : Prop := J1 (ds_u s) (ds_skip s) (ds_ref s) /\ 0 <= ds_off s.

Definition dwstep (s s' : dstate) (cs : list Z) : Prop :=
  d3str s = cs ++ d3str s' /\ ds_ref s' = feed (ds_ref s) cs /\
  dw1 (ds_cap s') (ds_u s') <= dw1 (ds_cap s) (ds_u s) + DATA_PER * zlen cs /\
  dw2 (ds_H s') (ds_ka s') <= dw2 (ds_H s) (ds_ka s) + 8 * zlen (ekl (lines (ds_ref s) cs)) /\
  dw4 (ds_en s') (ds_ecap s') <= dw4 (ds_en s) (ds_ecap s) + NC_PER * zlen (lines (ds_ref s) cs).

Lemma dw_zlen_app {A : Type} (l1 l2 : list A) : zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. unfold zlen. rewrite length_app. lia. Qed.

Lemma dw_step_nil s : dwstep s s [].
Proof.
  unfold dwstep. cbn [app]. rewrite feed_nil, lines_nil. unfold ekl, zlen. cbn [map concat length Z.of_nat].
  split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.

Lemma dw_step_trans s s1 s2 c1 c2 : dwstep s s1 c1 -> dwstep s1 s2 c2 -> dwstep s s2 (c1 ++ c2).
Proof.
  intros (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5). unfold dwstep.
  rewrite lines_app, <- A2, ekl_app, !dw_zlen_app.
  split; [rewrite A1, B1, app_assoc; reflexivity|].
  split; [rewrite B2, A2, feed_app; reflexivity|].
  unfold NC_PER, DATA_PER in *. lia.
Qed.

Lemma dw_grow cap u : dw1 (gcap cap (Z.of_nat (length u))) u <= dw1 cap u.
Proof.
  unfold dw1, gcap, grow_tr, DATA_PER, zlen.
  destruct (Z.ltb_spec (cap - Z.of_nat (length u)) 4096) as [L|L]; cbn [fst snd]; cbv zeta; [|lia].
  destruct (Z.eqb_spec cap 0); lia.
Qed.

Lemma dw_step_grow s s1 :
  ds_u s1 = ds_u s -> ds_H s1 = ds_H s -> ds_ka s1 = ds_ka s -> d3str s1 = d3str s -> ds_ref s1 = ds_ref s ->
  ds_en s1 = ds_en s -> ds_ecap s1 = ds_ecap s -> ds_cap s1 = gcap (ds_cap s) (Z.of_nat (length (ds_u s))) ->
  dwstep s s1 [].
Proof.
  intros E1 E2 E3 E4 E5 E6 E7 E8. unfold dwstep. rewrite E1, E2, E3, E4, E5, E6, E7, E8. cbn [app].
  rewrite feed_nil, lines_nil. pose proof (dw_grow (ds_cap s) (ds_u s)) as G.
  unfold ekl, zlen. cbn [map concat length Z.of_nat]. split; [reflexivity|]. split; [reflexivity|].
  unfold NC_PER, DATA_PER. lia.
Qed.

Lemma dw_seen H ka l : dw2 (seen_arr H l) (ska H ka l) <= dw2 H ka + 8 * zlen (ek1 l).
Proof.
  unfold dw2, seen_arr, ska, seen_tr, ek1, zlen.
  destruct (gesture l) as [[[|] x]|]; [destruct (index_of x H) as [i|]|destruct (index_of x H) as [i|]|];
    cbn [fst snd length]; cbv zeta; cbn [fst snd length]; try lia.
  - rewrite length_app. cbn [length]. lia.
  - unfold swap_remove. pose proof (firstn_len_le (length H - 1) (set_nth i (last H []) H)). lia.
Qed.

Lemma dw_lines lv mx ls : forall no cap H ka,
  dw2 (snd (fst (lrst lv mx no cap H ka ls))) (snd (lrst lv mx no cap H ka ls)) <= dw2 H ka + 8 * zlen (ekl ls).
Proof.
  induction ls as [|l r IH]; intros no cap H ka.
  - unfold lrst, ekl, zlen. cbn [lines_run fst snd map concat length Z.of_nat]. lia.
  - unfold lrst. cbn [lines_run fst snd]. cbv zeta. rewrite !seen_ka_c, !lines_st_c.
    change (ekl (l :: r)) with (ek1 l ++ ekl r). rewrite dw_zlen_app.
    pose proof (dw_seen H ka l) as S.
    match goal with |- dw2 (snd (fst (lrst _ _ ?n ?c _ _ _))) _ <= _ =>
      pose proof (IH n c (seen_arr H l) (ska H ka l)) as I end.
    lia.
Qed.

Lemma dw_pushes ls : forall n cap, dw4 (n + zlen ls) (pcap n cap ls) <= dw4 n cap + NC_PER * zlen ls.
Proof.
  induction ls as [|l r IH]; intros n cap.
  - unfold pcap, zlen. cbn [pushes_run fst snd length Z.of_nat]. rewrite Z.add_0_r. lia.
  - unfold pcap. cbn [pushes_run fst snd]. cbv zeta. rewrite pushes_cap_c.
    pose proof (IH (n + 1) (push_cap n cap)) as I.
    assert (P : dw4 (n + 1) (push_cap n cap) <= dw4 n cap + NC_PER).
    { unfold dw4, push_cap, NC_PER. destruct (Z.eqb_spec n cap) as [E|E]; [destruct (Z.eqb_spec cap 0)|]; lia. }
    assert (Ez : n + zlen (l :: r) = n + 1 + zlen r) by (unfold zlen; cbn [length]; lia).
    rewrite Ez. unfold zlen in *. cbn [length]. unfold NC_PER in *. lia.
Qed.

Lemma dw_scan_len d : forall skip acc, (length (snd (fst (scan skip acc d))) <= length acc + length d)%nat.
Proof.
  induction d as [|b d IH]; intros skip acc; [cbn; lia|]. cbn [scan].
  destruct (b =? 0).
  - generalize (IH false []). destruct (scan false [] d) as [[sk r] ls]. cbn [fst snd length]. lia.
  - generalize (IH skip (acc ++ [b])). rewrite length_app. cbn [length]. lia.
Qed.

Lemma dw_chunk_len u skip d : (length (fst (fst (chunk u skip d))) <= length u + length d)%nat.
Proof.
  unfold chunk. generalize (dw_scan_len d skip u). destruct (scan skip u d) as [[sk r] ls]. cbn [fst snd].
  destruct (Nat.ltb LINE_LIMIT (length r)); cbn [fst length]; lia.
Qed.

Lemma dw_step_round s s2 d :
  d3str s = d ++ d3str s2 -> ds_ref s2 = feed (ds_ref s) d ->
  (length (ds_u s2) <= length (ds_u s) + length d)%nat ->
  ds_cap s2 = gcap (ds_cap s) (Z.of_nat (length (ds_u s))) ->
  dw2 (ds_H s2) (ds_ka s2) <= dw2 (ds_H s) (ds_ka s) + 8 * zlen (ekl (lines (ds_ref s) d)) ->
  ds_en s2 = ds_en s + zlen (lines (ds_ref s) d) ->
  ds_ecap s2 = pcap (ds_en s) (ds_ecap s) (lines (ds_ref s) d) ->
  dwstep s s2 d.
Proof.
  intros E1 E2 L E4 W E6 E7. unfold dwstep. split; [exact E1|]. split; [exact E2|]. split.
  - rewrite E4. pose proof (dw_grow (ds_cap s) (ds_u s)) as G. unfold dw1 in *. unfold zlen, DATA_PER in *. lia.
  - split; [exact W|]. rewrite E6, E7. apply dw_pushes.
Qed.

Lemma dw_run lv mx : forall f s j a, dwI s -> exists cs, dwstep s (fst (snd (drain_run f lv mx s j a))) cs.
Proof.
  induction f as [|f IH]; intros s j a HI.
  - exists []. cbn [drain_run fst snd]. apply dw_step_nil.
  - pose proof HI as (HJ & Ho). cbn [drain_run]. cbv zeta. rewrite !grow_cap_c.
    destruct (ds_eintr s).
    + cbn [fst snd].
      match goal with |- exists cs, dwstep s (fst (snd (drain_run f lv mx ?s1 ?j1 ?a1))) cs =>
        destruct (IH s1 j1 a1 HI) as (cs & W);
        assert (G : dwstep s s1 []) by (apply dw_step_grow; reflexivity) end.
      exists ([] ++ cs). exact (dw_step_trans _ _ _ _ _ G W).
    + destruct (ds_pend s) as [|r0 rs] eqn:Ep.
      * cbn [fst snd]. exists []. apply dw_step_grow; try reflexivity.
        unfold d3str. cbn [ds_pend ds_off]. rewrite Ep. reflexivity.
      * match goal with |- context [if Z.min ?x ?y <=? 0 then _ else _] => set (n := Z.min x y) end.
        destruct (Z.leb_spec n 0) as [En|En].
        -- cbn [fst snd]. exists []. apply dw_step_grow; try reflexivity.
           unfold d3str. cbn [ds_pend ds_off]. rewrite Ep. reflexivity.
        -- assert (Hn1 : n <= Z.of_nat (length r0) - ds_off s) by apply Z.le_min_l.
           set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)).
           destruct (chunk (ds_u s) (ds_skip s) d) as [[u' sk'] rl] eqn:Ech. cbv beta iota.
           pose proof (chunk_ok (ds_u s) (ds_skip s) (ds_ref s) d HJ) as CK. rewrite Ech in CK. cbv beta iota in CK.
           destruct CK as [Erl HJ2]. subst rl.
           pose proof (dw_chunk_len (ds_u s) (ds_skip s) d) as CL. rewrite Ech in CL. cbn [fst] in CL.
           rewrite !pushes_cap_c, !lines_st_c.
           generalize (dw_lines lv mx (lines (ds_ref s) d) (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s)).
           destruct (lrst lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) (lines (ds_ref s) d)) as [[oc' H'] ka'].
           cbv beta iota. cbn [fst snd]. intros LW.
           match goal with |- context [snd (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11)] =>
             destruct (snd (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)) as [[o' ha'] ks'] end.
           cbv beta iota. cbn [fst snd].
           match goal with |- exists cs, dwstep s (fst (snd (drain_run f lv mx ?s2 ?j4 ?a2))) cs =>
             set (s2' := s2) in *; set (j4' := j4) in *; set (a2' := a2) in * end.
           assert (HI2 : dwI s2').
           { split; [exact HJ2|]. unfold s2'. cbn [ds_off]. destruct (ds_off s + n =? Z.of_nat (length r0)); lia. }
           destruct (IH s2' j4' a2' HI2) as (cs & W).
           assert (W1 : dwstep s s2' d).
           { apply dw_step_round.
             - unfold d. apply (round_str s s2' r0 rs n Ep Ho En Hn1); reflexivity.
             - reflexivity.
             - exact CL.
             - reflexivity.
             - exact LW.
             - reflexivity.
             - reflexivity. }
           exists (d ++ cs). exact (dw_step_trans _ _ _ _ _ W1 W).
Qed.

Lemma dw_lc l : zlen l <= 6000 -> 1 + 2 * zlen (ek1 l) <= zlen (line_copies l) /\ Forall (fun n => 0 <= n) (line_copies l).
Proof.
  intros HL.
  assert (E : line_copies l = (zlen l + 1) :: (if begin_line l then [zlen l - 5; zlen l - 5] else [])).
  { unfold line_copies. rewrite (proj2 (Z.leb_le (zlen l) LLIM)) by (unfold LLIM; lia). reflexivity. }
  rewrite E. assert (Z0 : 0 <= zlen l) by (unfold zlen; lia). unfold ek1.
  destruct (begin_line l) eqn:Eb.
  - pose proof (begin_line_len l Eb) as B.
    split; [destruct (gesture l) as [[[|] x]|]; unfold zlen in *; cbn [length Z.of_nat]; lia|].
    apply Forall_cons; [cbv beta; lia|]. apply Forall_cons; [cbv beta; lia|].
    apply Forall_cons; [cbv beta; lia|]. apply Forall_nil.
  - destruct (gesture l) as [[[|] x]|] eqn:Eg.
    + destruct (gesture_begin l x Eg) as [_ Eb']. congruence.
    + split; [unfold zlen; cbn [length Z.of_nat]; lia|]. apply Forall_cons; [cbv beta; lia|apply Forall_nil].
    + split; [unfold zlen; cbn [length Z.of_nat]; lia|]. apply Forall_cons; [cbv beta; lia|apply Forall_nil].
Qed.

Lemma dw_copies L : Forall (fun l => zlen l <= 6000) L ->
  zlen L + 2 * zlen (ekl L) <= zlen (flat_map line_copies L) /\ Forall (fun n => 0 <= n) (flat_map line_copies L).
Proof.
  induction L as [|l L IH]; intros HF.
  - unfold zlen, ekl. cbn [flat_map map concat length Z.of_nat]. split; [lia|apply Forall_nil].
  - apply Forall_cons_iff in HF as [Hl HF]. destruct (IH HF) as [I1 I2]. destruct (dw_lc l Hl) as [K1 K2].
    change (ekl (l :: L)) with (ek1 l ++ ekl L). cbn [flat_map].
    rewrite !dw_zlen_app. split; [unfold zlen in *; cbn [length]; lia|]. apply Forall_app. split; [exact K2|exact I2].
Qed.

Theorem drain_wt3_holds (e : rentry) (h : hsrc) :
  0 <= re_cap e ->
  0 <= ent_ka e ->
  J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) ->
  0 <= hs_off h ->
  re_nheld e + Z.of_nat (length (pending_stream h)) < 2 ^ 26 ->
  (hl_cap (hs_expected h) = 0 \/ exists k, 0 <= k /\ hl_cap (hs_expected h) = 8 * 2 ^ k) ->
  hl_n (hs_expected h) + Z.of_nat (length (pending_stream h)) < 2 ^ 25 ->
  Z.of_nat (length (re_U e)) <= re_used e ->
  drain_wt3 e h.
Proof.
  intros _ _ HJ Hoff _ _ _ Hu. unfold drain_wt3. intros lv mx NO CAP _ _.
  unfold drain_fin, drain_go.
  set (s0 := drain_init NO CAP e h).
  assert (HI : dwI s0) by (unfold dwI, s0, drain_init; cbn [ds_u ds_skip ds_ref ds_off]; split; [exact HJ|exact Hoff]).
  destruct (dw_run lv mx (S (S (length (pending_stream h)))) s0 0%nat dadr0 HI) as (cs & SE & _ & S1 & S2 & S4).
  set (sF := fst (snd (drain_run (S (S (length (pending_stream h)))) lv mx s0 0%nat dadr0))) in *.
  assert (EP : d3str s0 = bzs (pending_stream h)) by (unfold s0; apply d3str_init).
  assert (Er : ds_ref s0 = hs_state h) by reflexivity.
  rewrite Er in S2, S4.
  assert (ELs : lines (hs_state h) (bzs (pending_stream h)) =
                lines (hs_state h) cs ++ lines (feed (hs_state h) cs) (d3str sF))
    by (rewrite <- lines_app, <- SE, EP; reflexivity).
  assert (LcLs : zlen (lines (hs_state h) cs) <= zlen (lines (hs_state h) (bzs (pending_stream h))) /\
                 zlen (ekl (lines (hs_state h) cs)) <= zlen (ekl (lines (hs_state h) (bzs (pending_stream h))))).
  { rewrite ELs, ekl_app, !dw_zlen_app. unfold zlen. lia. }
  assert (Lcs : zlen cs <= Z.of_nat (length (pending_stream h))).
  { assert (E : Z.of_nat (length (pending_stream h)) = zlen (d3str s0))
      by (rewrite EP; unfold zlen, bzs; rewrite length_map; reflexivity).
    rewrite E, SE, dw_zlen_app. unfold zlen. lia. }
  assert (HJw : ls_k (hs_state h) = false -> zlen (ls_w (hs_state h)) <= 6000 /\ nozero (ls_w (hs_state h))).
  { destruct HJ as (Hk & Hw & Hl & Hz). intros E. rewrite <- Hw by (rewrite Hk; exact E).
    split; [unfold zlen; apply LL_le; exact Hl|exact Hz]. }
  assert (LFN : Forall (fun l => zlen l <= 6000) (lines (hs_state h) (bzs (pending_stream h))))
    by (apply lines_len6; intros E; exact (proj1 (HJw E))).
  destruct (new_cred h HJw) as [CR _].
  destruct (dw_copies _ LFN) as [CP CN].
  assert (F1 : Z.max (ds_cap sF) (DATA_PER * Z.of_nat (length (ds_u sF)) + 8192) <=
               Z.max (re_cap e) (DATA_PER * re_used e + 8192) + DATA_PER * zlen cs).
  { unfold dw1 in S1. unfold s0, drain_init in S1. cbn [ds_cap ds_u] in S1. unfold zlen, bzs in *.
    rewrite length_map in S1. unfold DATA_PER in *. lia. }
  assert (F2 : Z.max (ds_ka sF) (8 * Z.of_nat (length (ds_H sF)) + 8) <=
               Z.max (if re_hp e =? 0 then 0 else re_kh e) (8 * re_nheld e + 8) +
               8 * zlen (ekl (lines (hs_state h) (bzs (pending_stream h))))).
  { unfold dw2 in S2. unfold s0, drain_init in S2. cbn [ds_H ds_ka] in S2. unfold keys_texts, ent_ka in S2.
    unfold re_nheld. destruct LcLs as [_ LE]. unfold zlen in *. rewrite length_map in S2. lia. }
  assert (F3 : Z.max (16 * hl_cap (hs_pending h)) 128 <= nw_list (hs_pending h)).
  { unfold nw_list, hl_n, NC_PER. lia. }
  assert (F4 : Z.max (16 * ds_ecap sF)
                 (NC_PER * (hl_n (hs_expected h) + Z.of_nat (length (lines (hs_state h) (bzs (pending_stream h))))) +
                  128) <=
               nw_list (hs_expected h) + NC_PER * zlen (lines (hs_state h) (bzs (pending_stream h)))).
  { unfold dw4 in S4. unfold s0, drain_init in S4. cbn [ds_en ds_ecap] in S4. unfold nw_list.
    destruct LcLs as [LE _]. unfold zlen, NC_PER in *. lia. }
  assert (F5 : zlen (lines (hs_state h) (bzs (pending_stream h))) +
               2 * zlen (ekl (lines (hs_state h) (bzs (pending_stream h)))) <= zsumZ (cred h) (zseq 0 49)).
  { rewrite <- (bcnt_sum _ CN) in CP. eapply Z.le_trans; [exact CP|]. apply zsumZ_le. intros c _. exact (CR c). }
  assert (E0 : 0 <= zlen (ekl (lines (hs_state h) (bzs (pending_stream h))))) by (unfold zlen; lia).
  clear S1 S2 S4 LcLs CR CP CN ELs HJw LFN HJ SE EP Er.
  unfold drain_wt_src, nw_ent, nw_src.
  change (ekeys (lines (hs_state h) (bzs (pending_stream h)))) with (ekl (lines (hs_state h) (bzs (pending_stream h)))).
  unfold NC_PER, DATA_PER in *. lia.
Qed.

Lemma drain_wt_bridge (es : list rentry) (hj : list (hsrc * nat)) (e : rentry) (h : hsrc) (fin : dstate) :
  CF.SlotPass2Mv.drain_wt es hj e h fin = nc_wt es hj - nw_ent e - nw_src h + drain_wt_src fin h.
Proof. unfold CF.SlotPass2Mv.drain_wt, drain_wt_src. ring. Qed.
