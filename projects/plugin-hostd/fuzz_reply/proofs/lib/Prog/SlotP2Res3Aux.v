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
  HarnessTr send_line_b_c drain_b_c SlotMove SlotNcMove3 SlotRun3 SlotOp7R3 SlotResR3 SlotP5R3 SlotP5R3G SlotP5Res3
  SlotPass2Mv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotExitFinRes SlotExitMove.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Lemma p2r_ek_cb ls : zlen (ekeys ls) = Z.of_nat (count_begin ls).
Proof.
  induction ls as [|l ls IH]; [reflexivity|].
  rewrite ekeys_cons, count_begin_cons, <- IH. unfold zlen. rewrite length_app, Nat2Z.inj_add.
  assert (K : Z.of_nat (length (ekey_of l)) = (if is_begin l then 1 else 0)).
  { unfold ekey_of, is_begin. destruct (gesture l) as [[[|] x]|]; reflexivity. }
  rewrite K. reflexivity.
Qed.

Lemma p2r_ncb_le n c : ncb n c <= one_if c (band n).
Proof. unfold ncb. destruct (n =? 0); [pose proof (one_if_b c (band n)); lia|lia]. Qed.

Lemma p2r_arr_ncb cap c : arr_c cap c = ncb (16 * cap) c.
Proof.
  unfold arr_c, ncb. destruct (Z.eqb_spec cap 0) as [E|E].
  - subst cap. reflexivity.
  - rewrite (proj2 (Z.eqb_neq (16 * cap) 0)) by lia. reflexivity.
Qed.

Lemma p2r_dl_app d1 d2 a1 a2 c : dl_of (d1 ++ d2) (a1 ++ a2) c = dl_of d1 a1 c + dl_of d2 a2 c.
Proof. unfold dl_of. rewrite !zsum_app. lia. Qed.

Lemma p2r_db_app d1 d2 a1 a2 : db_of (d1 ++ d2) (a1 ++ a2) = db_of d1 a1 + db_of d2 a2.
Proof. unfold db_of. rewrite !zsum_app. lia. Qed.

Lemma p2r_arr_dl l l' c : dl_of (p2_arr_dels l l') (p2_arr_adds l l') c = arr_c (hl_cap l') c - arr_c (hl_cap l) c.
Proof.
  unfold dl_of, p2_arr_dels, p2_arr_adds, arr_sz, arr_c.
  destruct (p2_same (hl_v l) (hl_cap l) (hl_v l') (hl_cap l')) eqn:S; cbv beta iota.
  - unfold p2_same in S. apply andb_prop in S as [_ S]. apply Z.eqb_eq in S. rewrite S, zsum_nil. lia.
  - destruct (Z.eqb_spec (hl_cap l) 0); destruct (Z.eqb_spec (hl_cap l') 0); cbv beta iota;
      rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Lemma p2r_arr_db l l' : db_of (p2_arr_dels l l') (p2_arr_adds l l') = 16 * hl_cap l' - 16 * hl_cap l.
Proof.
  unfold db_of, p2_arr_dels, p2_arr_adds, arr_sz.
  destruct (p2_same (hl_v l) (hl_cap l) (hl_v l') (hl_cap l')) eqn:S; cbv beta iota.
  - unfold p2_same in S. apply andb_prop in S as [_ S]. apply Z.eqb_eq in S. rewrite S, zsum_nil. lia.
  - destruct (Z.eqb_spec (hl_cap l) 0); destruct (Z.eqb_spec (hl_cap l') 0); cbv beta iota;
      rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Lemma p2r_buf_dl e e' c : dl_of (p2_buf_dels e e') (p2_buf_adds e e') c = ncb (re_cap e') c - ncb (re_cap e) c.
Proof.
  unfold dl_of, p2_buf_dels, p2_buf_adds.
  destruct (p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e')) eqn:S; cbn [orb].
  - unfold p2_same in S. apply andb_prop in S as [_ S]. apply Z.eqb_eq in S. rewrite S, zsum_nil. lia.
  - unfold ncb. destruct (Z.eqb_spec (re_cap e) 0); destruct (Z.eqb_spec (re_cap e') 0); cbv beta iota;
      rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Lemma p2r_buf_db e e' : db_of (p2_buf_dels e e') (p2_buf_adds e e') = re_cap e' - re_cap e.
Proof.
  unfold db_of, p2_buf_dels, p2_buf_adds.
  destruct (p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e')) eqn:S; cbn [orb].
  - unfold p2_same in S. apply andb_prop in S as [_ S]. apply Z.eqb_eq in S. rewrite S, zsum_nil. lia.
  - destruct (Z.eqb_spec (re_cap e) 0); destruct (Z.eqb_spec (re_cap e') 0); cbv beta iota;
      rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Lemma p2r_hp_dl e e' c : (re_hp e <> 0 -> re_kh e <> 0) ->
  ncb (ent_ka e') c - ncb (ent_ka e) c <= dl_of (p2_hp_dels e e') (p2_hp_adds e e') c.
Proof.
  intros Hk. unfold dl_of, p2_hp_dels, p2_hp_adds, ent_ka.
  destruct (p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e')) eqn:S; cbn [orb].
  - unfold p2_same in S. apply andb_prop in S as [S1 S2]. apply Z.eqb_eq in S1, S2. rewrite S1, S2, zsum_nil. lia.
  - pose proof (p2r_ncb_le (re_kh e') c).
    destruct (Z.eqb_spec (re_hp e) 0) as [H0|H0]; destruct (Z.eqb_spec (re_hp e') 0) as [H1|H1]; cbv beta iota;
      rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; rewrite ?ncb_0; try rewrite (ncb_nz (re_kh e) c (Hk H0)); lia.
Qed.

Lemma p2r_hp_db e e' : db_of (p2_hp_dels e e') (p2_hp_adds e e') = ent_ka e' - ent_ka e.
Proof.
  unfold db_of, p2_hp_dels, p2_hp_adds, ent_ka.
  destruct (p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e')) eqn:S; cbn [orb].
  - unfold p2_same in S. apply andb_prop in S as [S1 S2]. apply Z.eqb_eq in S1, S2. rewrite S1, S2, zsum_nil. lia.
  - destruct (Z.eqb_spec (re_hp e) 0); destruct (Z.eqb_spec (re_hp e') 0); cbv beta iota;
      rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Lemma p2r_dr_dl out CAP q1 e e' h l' (s : dstate) c :
  (re_hp e <> 0 -> re_kh e <> 0) -> re_cap e' = ds_cap s -> ent_ka e' = ds_ka s -> hl_cap l' = ds_ecap s ->
  ncb (ds_ocap s) c - ncb CAP c + dchain e h s c <=
  dl_of (p2_dr_dels out CAP q1 (ds_ocap s) e e' (hs_expected h) l')
    (p2_dr_adds out CAP q1 (ds_ocap s) e e' (hs_expected h) l') c.
Proof.
  intros Hk E1 E2 E3. unfold p2_dr_dels, p2_dr_adds.
  rewrite !p2r_dl_app, p2r_buf_dl, p2r_arr_dl, !p2r_arr_ncb, E1, E3.
  pose proof (p2r_hp_dl e e' c Hk) as H. rewrite E2 in H.
  assert (O : ncb (ds_ocap s) c - ncb CAP c <=
              dl_of (out_move_dels out CAP q1 (ds_ocap s)) (out_move_adds out CAP q1 (ds_ocap s)) c)
    by exact (SlotExitFinRes.out_dl3 c out CAP q1 (ds_ocap s)).
  unfold dchain. lia.
Qed.

Lemma p2r_dr_db out CAP q1 e e' h l' (s : dstate) :
  re_cap e' = ds_cap s -> ent_ka e' = ds_ka s -> hl_cap l' = ds_ecap s ->
  ds_ocap s - CAP + dchainb e h s <=
  db_of (p2_dr_dels out CAP q1 (ds_ocap s) e e' (hs_expected h) l')
    (p2_dr_adds out CAP q1 (ds_ocap s) e e' (hs_expected h) l').
Proof.
  intros E1 E2 E3. unfold p2_dr_dels, p2_dr_adds.
  rewrite !p2r_db_app, p2r_buf_db, p2r_hp_db, p2r_arr_db, E1, E2, E3.
  assert (O : ds_ocap s - CAP <= db_of (out_move_dels out CAP q1 (ds_ocap s)) (out_move_adds out CAP q1 (ds_ocap s)))
    by exact (SlotExitFinRes.out_db3 out CAP q1 (ds_ocap s)).
  unfold dchainb. lia.
Qed.

Lemma p2r_da_sum h ks : Forall (fun n => 0 <= n) ks ->
  zsumZ (fun c => cred h c - bcnt c ks) (zseq 0 49) = zsumZ (cred h) (zseq 0 49) - zlen ks.
Proof.
  intros Hks. rewrite (zsumZ_ext _ (fun c => cred h c + (-1) * bcnt c ks)) by (intros; lia).
  rewrite zsumZ_add, zsumZ_mul_l, (bcnt_sum ks Hks). lia.
Qed.

Lemma p2r_prom p1 p2 X c : prom_c (p1 ++ X :: p2) c = prom_c p1 c + zsum (rec_cred c) X + prom_c p2 c.
Proof. unfold prom_c. rewrite zsum_app, zsum_cons. cbv beta. lia. Qed.

Lemma p2r_promb p1 p2 X : promb (p1 ++ X :: p2) = promb p1 + zsum rec_credb X + promb p2.
Proof. unfold promb. rewrite zsum_app, zsum_cons. cbv beta. lia. Qed.

Lemma p2r_pend_split hj1 h j hj2 :
  pend_view (hj1 ++ (h, j) :: hj2) = pend_view hj1 ++ map snd (hl_recs (hs_pending h)) :: pend_view hj2.
Proof. unfold pend_view. rewrite map_app. reflexivity. Qed.

Lemma p2r_cred_le p1 p2 h c : cred h c <= prom_c (p1 ++ map snd (hl_recs (hs_pending h)) :: p2) c.
Proof. rewrite p2r_prom. pose proof (prom_c_nonneg p1 c). pose proof (prom_c_nonneg p2 c). unfold cred. lia. Qed.

Lemma p2r_keep V L A V' L' A' dels adds x : nc_move V L A V' L' A' dels adds -> In x (rv_nc V) ->
  ~ In x (map fst dels) -> (exists m, In (x, m) (blocks L A)) -> In x (rv_nc V').
Proof.
  intros (R & gone & B & X & Y & HV & HV' & _ & _ & _ & _ & _ & _ & _ & HG) Hx Hd (m & Hm).
  apply (Permutation_in _ (Permutation_sym HV')). apply in_or_app. left.
  pose proof (Permutation_in _ HV Hx) as H1. apply in_app_or in H1 as [H1|H1]; [exact H1|].
  apply in_app_or in H1 as [H1|H1]; [contradiction|]. exfalso. exact (HG x H1 m Hm).
Qed.

Lemma p2r_dels_in out CAP q1 CAP' e e' l l' x : In x (map fst (p2_dr_dels out CAP q1 CAP' e e' l l')) ->
  (out = x /\ CAP <> 0 /\ out_same out CAP q1 CAP' = false) \/
  (re_buf e = x /\ re_cap e <> 0 /\ p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e') = false) \/
  (re_hp e = x /\ re_hp e <> 0 /\ p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e') = false) \/
  (hl_v l = x /\ hl_cap l <> 0 /\ p2_same (hl_v l) (hl_cap l) (hl_v l') (hl_cap l') = false).
Proof.
  unfold p2_dr_dels. rewrite !map_app, !in_app_iff. intros [H|[H|[H|H]]].
  - left. revert H. unfold out_move_dels. destruct (out_same out CAP q1 CAP'); cbn [orb]; [intros []|].
    destruct (Z.eqb_spec CAP 0) as [C|C]; cbv beta iota; [intros []|]. intros [H|[]]. cbn [fst] in H.
    split; [exact H|split; [exact C|reflexivity]].
  - right. left. revert H. unfold p2_buf_dels.
    destruct (p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e')); cbn [orb]; [intros []|].
    destruct (Z.eqb_spec (re_cap e) 0) as [C|C]; cbv beta iota; [intros []|]. intros [H|[]]. cbn [fst] in H.
    split; [exact H|split; [exact C|reflexivity]].
  - right. right. left. revert H. unfold p2_hp_dels.
    destruct (p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e')); cbn [orb]; [intros []|].
    destruct (Z.eqb_spec (re_hp e) 0) as [C|C]; cbv beta iota; [intros []|]. intros [H|[]]. cbn [fst] in H.
    split; [exact H|split; [exact C|reflexivity]].
  - right. right. right. revert H. unfold p2_arr_dels, arr_sz.
    destruct (p2_same (hl_v l) (hl_cap l) (hl_v l') (hl_cap l')); cbv beta iota; [intros []|].
    destruct (Z.eqb_spec (hl_cap l) 0) as [C|C]; cbv beta iota; [intros []|]. intros [H|[]]. cbn [fst] in H.
    split; [exact H|split; [exact C|reflexivity]].
Qed.

Lemma p2r_eb_buf e : re_cap e <> 0 -> In (re_buf e) (entry_blocks e).
Proof. intros C. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq _ _) C). cbv beta iota. apply in_or_app. left. left. reflexivity. Qed.

Lemma p2r_eb_hp e : re_hp e <> 0 -> In (re_hp e) (entry_blocks e).
Proof.
  intros C. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_hp e) 0) C). cbv beta iota.
  apply in_or_app. right. apply in_or_app. left. left. reflexivity.
Qed.

Lemma p2r_hb_exp h : hl_cap (hs_expected h) <> 0 -> In (hl_v (hs_expected h)) (hs_blocks h).
Proof.
  intros C. unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  unfold list_blocks. rewrite (proj2 (Z.eqb_neq _ _) C). cbv beta iota. apply in_or_app. left. left. reflexivity.
Qed.

Lemma p2r_eb_nd e : List.NoDup (entry_blocks e) -> re_cap e <> 0 -> re_hp e <> 0 -> re_buf e <> re_hp e.
Proof.
  intros H C1 C2 E. unfold entry_blocks in H. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) C1) in H.
  rewrite (proj2 (Z.eqb_neq (re_hp e) 0) C2) in H. cbv beta iota in H. cbn [app] in H.
  apply List.NoDup_cons_iff in H as [H _]. apply H. rewrite E. left. reflexivity.
Qed.

Lemma p2r_target G out es1 e es2 hj1 h j hj2 :
  List.NoDup (target_addrs G out (es1 ++ e :: es2) (hj1 ++ (h, j) :: hj2)) ->
  ~ In out (entry_blocks e) /\ ~ In out (hs_blocks h) /\ List.NoDup (entry_blocks e) /\
  (forall q, In q (entry_blocks e) -> ~ In q (hs_blocks h)).
Proof.
  intros H. destruct (SlotExitMove.mv_target _ _ _ _ H) as (_ & _ & _ & H4 & H5 & H6 & H7).
  assert (IE : forall q, In q (entry_blocks e) -> In q (concat (map entry_blocks (es1 ++ e :: es2)))).
  { intros q Hq. apply in_concat. exists (entry_blocks e). split; [|exact Hq].
    apply in_map. apply in_or_app. right. left. reflexivity. }
  assert (IH : forall q, In q (hs_blocks h) -> In q (concat (map (fun p => hs_blocks (fst p)) (hj1 ++ (h, j) :: hj2)))).
  { intros q Hq. apply in_concat. exists (hs_blocks h). split; [|exact Hq].
    apply in_map_iff. exists (h, j). split; [reflexivity|]. apply in_or_app. right. left. reflexivity. }
  split; [intros X; exact (H4 (IE _ X))|]. split; [intros X; exact (H5 (IH _ X))|]. split.
  - rewrite map_app, concat_app in H6. cbn [map concat] in H6.
    apply List.NoDup_app_remove_l in H6. apply List.NoDup_app_remove_r in H6. exact H6.
  - intros q Hq X. exact (H7 q (IE _ Hq) (IH _ X)).
Qed.

Lemma p2r_nd_out out CAP q1 CAP' e e' h l' :
  ~ In out (entry_blocks e) -> ~ In out (hs_blocks h) -> out_same out CAP q1 CAP' = true ->
  ~ In out (map fst (p2_dr_dels out CAP q1 CAP' e e' (hs_expected h) l')).
Proof.
  intros T1 T2 Os X. destruct (p2r_dels_in _ _ _ _ _ _ _ _ _ X) as [(_ & _ & O)|[(E & C & _)|[(E & C & _)|(E & C & _)]]].
  - rewrite Os in O. discriminate.
  - apply T1. rewrite <- E. exact (p2r_eb_buf e C).
  - apply T1. rewrite <- E. exact (p2r_eb_hp e C).
  - apply T2. rewrite <- E. exact (p2r_hb_exp h C).
Qed.

Lemma p2r_nd_buf out CAP q1 CAP' e e' h l' :
  ~ In out (entry_blocks e) -> List.NoDup (entry_blocks e) -> (forall q, In q (entry_blocks e) -> ~ In q (hs_blocks h)) ->
  re_cap e <> 0 -> p2_same (re_buf e) (re_cap e) (re_buf e') (re_cap e') = true ->
  ~ In (re_buf e) (map fst (p2_dr_dels out CAP q1 CAP' e e' (hs_expected h) l')).
Proof.
  intros T1 T3 T4 C0 S X.
  destruct (p2r_dels_in _ _ _ _ _ _ _ _ _ X) as [(E & _ & _)|[(_ & _ & S')|[(E & C & _)|(E & C & _)]]].
  - apply T1. rewrite E. exact (p2r_eb_buf e C0).
  - rewrite S in S'. discriminate.
  - exact (p2r_eb_nd e T3 C0 C (eq_sym E)).
  - apply (T4 (re_buf e) (p2r_eb_buf e C0)). rewrite <- E. exact (p2r_hb_exp h C).
Qed.

Lemma p2r_nd_hp out CAP q1 CAP' e e' h l' :
  ~ In out (entry_blocks e) -> List.NoDup (entry_blocks e) -> (forall q, In q (entry_blocks e) -> ~ In q (hs_blocks h)) ->
  re_hp e <> 0 -> p2_same (re_hp e) (re_kh e) (re_hp e') (re_kh e') = true ->
  ~ In (re_hp e) (map fst (p2_dr_dels out CAP q1 CAP' e e' (hs_expected h) l')).
Proof.
  intros T1 T3 T4 C0 S X.
  destruct (p2r_dels_in _ _ _ _ _ _ _ _ _ X) as [(E & _ & _)|[(E & C & _)|[(_ & _ & S')|(E & C & _)]]].
  - apply T1. rewrite E. exact (p2r_eb_hp e C0).
  - exact (p2r_eb_nd e T3 C C0 E).
  - rewrite S in S'. discriminate.
  - apply (T4 (re_hp e) (p2r_eb_hp e C0)). rewrite <- E. exact (p2r_hb_exp h C).
Qed.

Lemma p2r_nd_arr out CAP q1 CAP' e e' h l' :
  ~ In out (hs_blocks h) -> (forall q, In q (entry_blocks e) -> ~ In q (hs_blocks h)) ->
  hl_cap (hs_expected h) <> 0 ->
  p2_same (hl_v (hs_expected h)) (hl_cap (hs_expected h)) (hl_v l') (hl_cap l') = true ->
  ~ In (hl_v (hs_expected h)) (map fst (p2_dr_dels out CAP q1 CAP' e e' (hs_expected h) l')).
Proof.
  intros T2 T4 C0 S X.
  destruct (p2r_dels_in _ _ _ _ _ _ _ _ _ X) as [(E & _ & _)|[(E & C & _)|[(E & C & _)|(_ & _ & S')]]].
  - apply T2. rewrite E. exact (p2r_hb_exp h C0).
  - apply (T4 (re_buf e) (p2r_eb_buf e C)). rewrite E. exact (p2r_hb_exp h C0).
  - apply (T4 (re_hp e) (p2r_eb_hp e C)). rewrite E. exact (p2r_hb_exp h C0).
  - rewrite S in S'. discriminate.
Qed.

Lemma p2r_rv_out G out es hj : In out (rv_nc (view_of G out es hj)).
Proof. cbn [view_of rv_nc]. apply in_cons. apply in_eq. Qed.

Lemma p2r_rv_ent G out es hj e x : In e es -> In x (entry_nc e) -> In x (rv_nc (view_of G out es hj)).
Proof.
  intros He Hx. cbn [view_of rv_nc]. apply in_cons. apply in_cons. apply in_or_app. left.
  apply in_concat. exists (entry_nc e). split; [apply in_map; exact He|exact Hx].
Qed.

Lemma p2r_rv_src G out es hj p x : In p hj -> In x (src_nc (fst p)) -> In x (rv_nc (view_of G out es hj)).
Proof.
  intros Hp Hx. cbn [view_of rv_nc]. apply in_cons. apply in_cons. apply in_or_app. right.
  apply in_concat. exists (src_nc (fst p)). split; [|exact Hx]. apply in_map_iff. exists p. split; [reflexivity|exact Hp].
Qed.

Lemma p2r_enc_buf e : re_cap e <> 0 -> In (re_buf e) (entry_nc e).
Proof. intros C. unfold entry_nc. rewrite (proj2 (Z.eqb_neq _ _) C). cbv beta iota. apply in_or_app. left. left. reflexivity. Qed.

Lemma p2r_enc_hp e : re_hp e <> 0 -> In (re_hp e) (entry_nc e).
Proof.
  intros C. unfold entry_nc. rewrite (proj2 (Z.eqb_neq (re_hp e) 0) C). cbv beta iota.
  apply in_or_app. right. left. reflexivity.
Qed.

Lemma p2r_snc_exp h : hl_cap (hs_expected h) <> 0 -> In (hl_v (hs_expected h)) (src_nc h).
Proof.
  intros C. unfold src_nc. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  unfold arr_nc. rewrite (proj2 (Z.eqb_neq _ _) C). cbv beta iota. left. reflexivity.
Qed.

Lemma p2r_snc_held h : hl_cap (hs_held h) <> 0 -> In (hl_v (hs_held h)) (src_nc h).
Proof.
  intros C. unfold src_nc. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
  unfold arr_nc. rewrite (proj2 (Z.eqb_neq _ _) C). cbv beta iota. left. reflexivity.
Qed.

Lemma p2r_ka_hp e : ent_ka e <> 0 -> re_hp e <> 0.
Proof. unfold ent_ka. intros H X. rewrite X in H. apply H. reflexivity. Qed.

Lemma p2r_sptr_spec L A a n : List.NoDup (map fst (blocks L A)) -> In (a, n) (blocks L A) ->
  In (sptr_of L A a, n) (user_blocks A) /\ ptr_addr L (sptr_of L A a) = a.
Proof. intros HB Hb. exact (sptr_of_spec L A a n (proj2 (stdpp.base.NoDup_ListNoDup _) HB) Hb). Qed.

Definition p2r_rest (G : Z) (es1 es2 : list rentry) (hj1 hj2 : list (hsrc * nat)) (h : hsrc) : list Z :=
  G :: concat (map entry_nc es1) ++ concat (map entry_nc es2) ++ concat (map (fun p => src_nc (fst p)) hj1) ++
  concat (map (fun p => src_nc (fst p)) hj2) ++ arr_nc (hs_pending h) ++ hs_partial h :: arr_nc (hs_held h).

Lemma p2r_rv_in G out es1 e es2 hj1 h j hj2 x :
  In x (rv_nc (view_of G out (es1 ++ e :: es2) (hj1 ++ (h, j) :: hj2))) ->
  out = x \/ In x (entry_nc e) \/ In x (arr_nc (hs_expected h)) \/ In x (p2r_rest G es1 es2 hj1 hj2 h).
Proof.
  intros H. unfold view_of in H. cbn [rv_nc] in H. rewrite !map_app, !concat_app in H. cbn [map concat fst] in H.
  unfold p2r_rest. unfold src_nc in H |- *. cbn [In] in H |- *.
  repeat rewrite in_app_iff in H. repeat rewrite in_app_iff. cbn [In] in H |- *.
  repeat rewrite in_app_iff in H. repeat rewrite in_app_iff. tauto.
Qed.

Lemma p2r_enc_len (l : list rentry) : (length (concat (map entry_nc l)) <= 2 * length l)%nat.
Proof.
  induction l as [|e l IH]; [cbn; lia|]. cbn [map concat]. rewrite length_app.
  assert (length (entry_nc e) <= 2)%nat by (unfold entry_nc; destruct (re_cap e =? 0), (re_hp e =? 0); cbn; lia).
  cbn [length]. lia.
Qed.

Lemma p2r_snc_len (l : list (hsrc * nat)) : (length (concat (map (fun p => src_nc (fst p)) l)) <= 4 * length l)%nat.
Proof.
  induction l as [|p l IH]; [cbn; lia|]. cbn [map concat]. rewrite length_app.
  assert (length (src_nc (fst p)) <= 4)%nat.
  { unfold src_nc, arr_nc.
    destruct (hl_cap (hs_pending (fst p)) =? 0), (hl_cap (hs_expected (fst p)) =? 0), (hl_cap (hs_held (fst p)) =? 0);
      cbn; lia. }
  cbn [length]. lia.
Qed.

Lemma p2r_rest_len G es1 es2 hj1 hj2 h : (length es1 + length es2 <= 3)%nat -> (length hj1 + length hj2 <= 3)%nat ->
  (length (p2r_rest G es1 es2 hj1 hj2 h) <= 22)%nat.
Proof.
  intros H1 H2. unfold p2r_rest. cbn [length]. rewrite !length_app. cbn [length].
  pose proof (p2r_enc_len es1). pose proof (p2r_enc_len es2). pose proof (p2r_snc_len hj1). pose proof (p2r_snc_len hj2).
  pose proof (arr_nc_len (hs_pending h)). pose proof (arr_nc_len (hs_held h)). lia.
Qed.

Lemma p2r_misT L A b G out es1 e es2 hj1 h j hj2 CAP qs :
  mis_nc (view_of G out (es1 ++ e :: es2) (hj1 ++ (h, j) :: hj2)) L (p3_mis b) -> res_ok_pack3 A b ->
  List.NoDup (map fst (blocks L A)) -> (re_hp e <> 0 -> re_kh e <> 0) ->
  (CAP = 0 -> forall m, ~ In (out, m) (blocks L A)) ->
  (length es1 + length es2 <= 3)%nat -> (length hj1 + length hj2 <= 3)%nat ->
  misT (slot3 CAP (resolveF qs (known_at L A out)) ++ dslots qs e h (drain_start (known_at L A) (known_at L A out) e h) ++
        map (sptr_of L A) (p2r_rest G es1 es2 hj1 hj2 h)) (0 + res3 CAP + dres e h) (p3_mis b).
Proof.
  intros (HI & _) HA HB Hkh HO0 Hl1 Hl2.
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (HN & HU & _) & _).
  split; [exact HN|]. split.
  - intros p Hp. apply in_map_iff in Hp as (e0 & <- & He0).
    destruct (HU e0 He0) as (_ & n & Hb).
    assert (Hx : In (ptr_addr L (fst e0)) (rv_nc (view_of G out (es1 ++ e :: es2) (hj1 ++ (h, j) :: hj2)))).
    { apply HI. unfold mis_addrs. exact (in_map (fun e1 => ptr_addr L (fst e1)) _ e0 He0). }
    rewrite <- (sptr_at L A (fst e0) n _ HB Hb eq_refl).
    assert (Hxb : In (ptr_addr L (fst e0), n) (blocks L A))
      by (unfold blocks; exact (in_map (fun b0 => (ptr_addr L (fst b0), snd b0)) _ (fst e0, n) Hb)).
    set (x := ptr_addr L (fst e0)) in *. clearbody x. clear He0 Hb.
    unfold dslots. rewrite !in_app_iff.
    destruct (p2r_rv_in G out es1 e es2 hj1 h j hj2 x Hx) as [Hx1|[Hx1|[Hx1|Hx1]]].
    + subst x. destruct (Z.eqb_spec CAP 0) as [E|E]; [exfalso; exact (HO0 E n Hxb)|].
      left. rewrite (slot3_nz _ _ E). left. reflexivity.
    + unfold entry_nc in Hx1. apply in_app_or in Hx1 as [Hx1|Hx1].
      * destruct (Z.eqb_spec (re_cap e) 0) as [C|C]; [destruct Hx1|]. destruct Hx1 as [Hx1|[]]. subst x.
        right. left. left. rewrite (slot3_nz _ _ C). left. reflexivity.
      * destruct (Z.eqb_spec (re_hp e) 0) as [C|C]; [destruct Hx1|]. destruct Hx1 as [Hx1|[]]. subst x.
        assert (Ek : ent_ka e <> 0) by (unfold ent_ka; rewrite (proj2 (Z.eqb_neq _ _) C); exact (Hkh C)).
        right. left. right. left. rewrite (slot3_nz _ _ Ek). left. reflexivity.
    + unfold arr_nc in Hx1. destruct (Z.eqb_spec (hl_cap (hs_expected h)) 0) as [C|C]; [destruct Hx1|].
      destruct Hx1 as [Hx1|[]]. subst x. right. left. right. right. rewrite (slot3_nz _ _ C). left. reflexivity.
    + right. right. apply in_map. exact Hx1.
  - rewrite !length_app, length_map. unfold dslots, dres. rewrite !length_app.
    pose proof (p2r_rest_len G es1 es2 hj1 hj2 h Hl1 Hl2).
    pose proof (slot3_res CAP (resolveF qs (known_at L A out))).
    pose proof (slot3_res (re_cap e) (resolveF qs (da_buf (drain_start (known_at L A) (known_at L A out) e h)))).
    pose proof (slot3_res (ent_ka e) (resolveF qs (da_hp (drain_start (known_at L A) (known_at L A out) e h)))).
    pose proof (slot3_res (hl_cap (hs_expected h)) (resolveF qs (da_ev (drain_start (known_at L A) (known_at L A out) e h)))).
    unfold NC_MAX. lia.
Qed.

Lemma p2r_excl L A qs NO CAP out e e' h l' q1 CAP' p n :
  List.NoDup (map fst (blocks L A)) -> In (p, n) (user_blocks A) -> (re_hp e <> 0 -> re_kh e <> 0) ->
  ~ In p (slot3 (ds_ocap (drain_init NO CAP e h)) (resolveF qs (da_out (drain_start (known_at L A) (known_at L A out) e h))) ++
          dsl qs (drain_init NO CAP e h) (drain_start (known_at L A) (known_at L A out) e h) ++ []) ->
  ~ In (ptr_addr L p) (map fst (p2_dr_dels out CAP q1 CAP' e e' (hs_expected h) l')).
Proof.
  intros HB Hp Hk Hn X. apply Hn. rewrite app_nil_r. unfold dsl.
  cbn [drain_init ds_ocap ds_cap ds_ka ds_ecap drain_start da_out da_buf da_hp da_ev]. rewrite !in_app_iff.
  destruct (p2r_dels_in _ _ _ _ _ _ _ _ _ X) as [(E & C & _)|[(E & C & _)|[(E & C & _)|(E & C & _)]]].
  - left. rewrite (slot3_nz _ _ C). left. exact (sptr_at L A p n _ HB Hp (eq_sym E)).
  - right. left. rewrite (slot3_nz _ _ C). left. exact (sptr_at L A p n _ HB Hp (eq_sym E)).
  - right. right. left.
    assert (Ek : ent_ka e <> 0) by (unfold ent_ka; rewrite (proj2 (Z.eqb_neq _ _) C); exact (Hk C)).
    rewrite (slot3_nz _ _ Ek). left. exact (sptr_at L A p n _ HB Hp (eq_sym E)).
  - right. right. right. rewrite (slot3_nz _ _ C). left. exact (sptr_at L A p n _ HB Hp (eq_sym E)).
Qed.

Lemma p2r_lines_out mx ls : forall no cap H ka j o ha ks,
  fst (fst (snd (lines_run false mx no cap H ka ls j o ha ks))) = o.
Proof.
  induction ls as [|l ls IH]; intros no cap H ka j o ha ks; [reflexivity|].
  cbn [lines_run]. cbv zeta. cbn [snd fst]. rewrite IH. reflexivity.
Qed.

Lemma p2r_drain_out f mx : forall s j a, da_out (snd (snd (drain_run f false mx s j a))) = da_out a.
Proof.
  induction f as [|f IH]; intros s j a; [reflexivity|].
  cbn [drain_run]. cbv zeta. destruct (ds_eintr s).
  - cbn [snd fst]. rewrite IH. reflexivity.
  - destruct (ds_pend s) as [|r0 rs]; [reflexivity|].
    match goal with |- context [Z.min ?x ?y <=? 0] => destruct (Z.min x y <=? 0) end; [reflexivity|].
    match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
    match goal with |- context [lines_run false mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 ?o ?ha ?ks] =>
      pose proof (p2r_lines_out mx rl (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 o ha ks) as LC;
      destruct (lines_run false mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 o ha ks)
        as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
    cbn [snd fst] in LC |- *. rewrite IH. cbn [da_out]. exact LC.
Qed.

Lemma p2r_cap_nn f lv mx : forall s j a, 0 <= ds_cap s -> 0 <= ds_cap (fst (snd (drain_run f lv mx s j a))).
Proof.
  induction f as [|f IH]; intros s j a Hc; [exact Hc|]. cbn [drain_run]. cbv zeta.
  assert (G : 0 <= fst (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a)))).
  { unfold grow_tr. destruct (ds_cap s - Z.of_nat (length (ds_u s)) <? 4096); cbn [fst snd];
      [destruct (ds_cap s =? 0)|]; lia. }
  destruct (ds_eintr s).
  - cbn [fst snd]. apply IH. cbn [ds_cap]. exact G.
  - destruct (ds_pend s) as [|r0 rs]; [cbn [fst snd ds_cap]; exact G|].
    match goal with |- context [Z.min ?x ?y <=? 0] => destruct (Z.min x y <=? 0) end; [cbn [fst snd ds_cap]; exact G|].
    match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
    match goal with |- context [lines_run ?lv0 ?m ?no ?c ?H ?k rl ?jj ?o ?ha ?ks] =>
      destruct (lines_run lv0 m no c H k rl jj o ha ks) as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
    cbn [fst snd]. apply IH. cbn [ds_cap]. exact G.
Qed.
