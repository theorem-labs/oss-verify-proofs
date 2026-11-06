From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead
  SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotHeadQ RelayRunT RelayRunF HarnessGlue
  relay_event_b_c check_shape_event_c SlotPass7D SlotPass7R SlotPass7T2 HarnessFrame SlotMove.
From Stdlib Require Import Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Lemma drv_ub_nonneg : forall s p n, WF s -> In (p, n) (user_blocks s) -> 0 <= n.
Proof.
  intros s p n HW Hin.
  destruct (YO10.in_user_blocks_inv s (p, n) Hin) as (g & am & i & fr & Hg & Hi & Hfr & _ & E).
  apply (YO10.used_metas_usedX s g am HW) in Hg.
  destruct (YO10.block_in_slot s g am i fr HW Hg Hi Hfr) as (_ & _ & H).
  injection E as _ ->. exact H.
Qed.

Lemma drv_ta : forall G O es hj, target_addrs G O es hj =
  G :: O :: concat (map entry_blocks es) ++ concat (map (fun p => hs_blocks (fst p)) hj).
Proof. reflexivity. Qed.

Section DRV.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma drv_notE : forall L A mem md live OUT CAP res EL x m i,
  AllocExtra B (aa_MR API) -> (forall a, in_globals G_reply a -> img_plain B a) ->
  aa_MR API L A mem md -> In (x, m) (blocks L A) -> x <> OUT -> 0 <= i < m ->
  (forall q k, In (q, k) (blocks L A) -> q <> res /\ forall i, 0 <= i < k -> ~ (res <= q + i < res + EL + 1)) ->
  (live = true -> 0 < CAP -> In (OUT, CAP) (blocks L A)) ->
  ~ op7_E live OUT CAP res EL (x + i).
Proof.
  intros L A mem md live OUT CAP res EL x m i AX PL HM HIn HNE Hi RSEP HOB [X|X].
  - destruct (RSEP x m HIn) as (_ & R). exact (R i Hi X).
  - assert (NI : ~ in_img B (x + i)).
    { apply blocks_In in HIn as (p & Ep & Hp). subst x. exact (ax_blocks_img AX L A mem md p m i HM Hp Hi). }
    unfold event_writes, send_writes in X.
    assert (GW : op7_W (x + i) -> False).
    { intros W. apply NI. exact (proj1 (PL _ (op7_W_glob _ W))). }
    destruct X as [[X|[X|[X|(LV & X)]]]|X].
    + apply GW. unfold op7_W. left. exact X.
    + apply GW. unfold op7_W. right. left. exact X.
    + apply GW. unfold op7_W. right. right. left. exact X.
    + destruct (blocks_disjoint B API L A mem md x m OUT CAP HM HIn (HOB LV ltac:(lia)) HNE) as [D|D]; lia.
    + apply GW. unfold op7_W. right. right. right. exact X.
Qed.

End DRV.

Theorem op7_rb_driver_holds : op7_rb_driver_stmt.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res G es hj nout cap out cap'
    out' HF HM HWF RM HEL FRB RSEP BLK HOUT OUTF FRESH (DK1 & DK2 & DK3 & DK4).
  destruct (op7_frame B API LS SH SK ra empty rc fx j E CS HF) as (SEG & ERR & PL & AX & BW & SPLO & SPHI & IL).
  pose proof HF as (_ & _ & PRE & _).
  destruct PRE as (((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INP & _) & _ & _ & _) &
    _ & _ & _ & _ & _ & NT & _).
  destruct RM as (_ & _ & _ & _ & _ & KADDR & KBLK & KZERO & _ & _ & _ & KBYTE & _).
  set (live := op7_live cl br dd EL) in *.
  set (OUT := bv_unsigned out) in *.
  set (CAP := bv_unsigned cap) in *.
  assert (HOB : live = true -> 0 < CAP -> In (OUT, CAP) (blocks L A)).
  { intros _ HC. destruct HOUT as ((O & junk & [(C0 & _)|(_ & _ & IN & _)]) & _); [lia|exact IN]. }
  assert (DEP : forall q m, In (q, m) (user_blocks (ss_A E)) -> ~ In (ptr_addr (ss_L E) q, m) (ss_T E) -> 0 < m ->
      exists q', In (q', m) (user_blocks A) /\ ptr_addr L q' = ptr_addr (ss_L E) q /\
        In (ptr_addr L q', m) (blocks L A) /\ ptr_addr L q' <> OUT /\ ~ op7_F live OUT res (ptr_addr L q')).
  { intros q m Hq HT Hm. destruct (DK1 q m Hq HT) as (NTA & q' & Hq' & Eq').
    specialize (NTA Hm). rewrite drv_ta in NTA.
    assert (INB : In (ptr_addr L q', m) (blocks L A)) by (apply blocks_In; exists q'; split; [reflexivity|exact Hq']).
    assert (NO : ptr_addr L q' <> OUT) by (intros X; apply NTA; right; left; rewrite <- Eq'; symmetry; exact X).
    exists q'. split; [exact Hq'|]. split; [exact Eq'|]. split; [exact INB|]. split; [exact NO|].
    intros [X|(_ & X)]; [exact (proj1 (RSEP _ _ INB) X)|exact (NO X)]. }
  assert (KEEP : forall q m i, In (q, m) (user_blocks (ss_A E)) -> ~ In (ptr_addr (ss_L E) q, m) (ss_T E) ->
      0 <= i < m -> mbyte (ms_segs B) mem' (ptr_addr (ss_L E) q + i) = mbyte (ms_segs B) mem (ptr_addr (ss_L E) q + i)).
  { intros q m i Hq HT Hi. destruct (DEP q m Hq HT ltac:(lia)) as (q' & Hq' & Eq' & INB & NO & NF).
    rewrite <- Eq'.
    exact (KBYTE q' m i Hq' (KBLK q' m Hq' ltac:(lia) NF) NF Hi
      (drv_notE B (API rc) L A mem md live OUT CAP res EL (ptr_addr L q') m i AX PL HM INB NO Hi RSEP HOB)). }
  split; [|split; [|split]].
  - intros q m Hq HT. destruct (DK1 q m Hq HT) as (NTA & q' & Hq' & Eq').
    pose proof (drv_ub_nonneg A q' m HWF Hq') as Hm0.
    split.
    + intros Hm IN'. pose proof (NTA Hm) as NTA'. rewrite drv_ta in NTA', IN'.
      destruct (DEP q m Hq HT Hm) as (q'' & Hq'' & Eq'' & INB & NO & _).
      destruct IN' as [X|[X|X]]; [apply NTA'; left; exact X| |apply NTA'; right; right; exact X].
      destruct live eqn:LV.
      * apply (FRESH eq_refl (ptr_addr L q'') m INB NO Hm). rewrite Eq''. symmetry. exact X.
      * rewrite (OUTF eq_refl) in X. apply NTA'. right. left. exact X.
    + exists q'. destruct (Z.eq_dec m 0) as [E0|E0].
      * subst m. destruct (KZERO q' Hq') as (Z1 & Z2). split; [exact Z1|]. rewrite Z2. exact Eq'.
      * destruct (DEP q m Hq HT ltac:(lia)) as (q'' & Hq'' & Eq'' & INB & NO & NF).
        assert (EQ : ptr_addr L q' = ptr_addr L q'') by (rewrite Eq', Eq''; reflexivity).
        rewrite <- EQ in NF.
        pose proof (KBLK q' m Hq' ltac:(lia) NF) as KB.
        split; [exact KB|]. rewrite (KADDR q' m Hq' KB NF). exact Eq'.
  - intros q m i Hq HT Hne Hi. rewrite (KEEP q m i Hq HT Hi). exact (DK2 q m i Hq HT Hne Hi).
  - intros i Hi. rewrite <- (DK3 i Hi).
    destruct INP as [(HN0 & _)|(_ & q & Hq & Eq)]; [lia|].
    assert (HT : ~ In (ptr_addr (ss_L E) q, ss_n E) (ss_T E)) by (rewrite Eq; exact (NT ltac:(lia))).
    rewrite <- Eq. exact (KEEP q (ss_n E) i Hq HT Hi).
  - intros q m HIn. destruct (BLK q m HIn) as [(H1 & H2)|(LV & X & _)].
    + destruct (DK4 q m H1) as [Y|Y]; [left; exact Y|right].
      rewrite drv_ta in Y |- *. destruct Y as [Y|[Y|Y]]; [left; exact Y| |right; right; exact Y].
      destruct live eqn:LV.
      * exfalso. apply H2. split; [reflexivity|symmetry; exact Y].
      * right. left. rewrite (OUTF eq_refl). exact Y.
    + right. rewrite drv_ta. right. left. symmetry. exact X.
Qed.

(* ---- Op 7's nc move: the output buffer stays at (OUT, CAP), or (OUT, CAP) goes and (OUT', CAP') comes. ---- *)

Lemma mv7_ent_in : forall e x, In x (entry_nc e) -> In x (entry_blocks e).
Proof.
  intros e x Hx. unfold entry_nc in Hx. unfold entry_blocks.
  apply in_app_iff in Hx. rewrite !in_app_iff. tauto.
Qed.

Lemma mv7_src_in : forall h x, In x (src_nc h) -> In x (hs_blocks h).
Proof.
  intros h x Hx. unfold src_nc, arr_nc in Hx. unfold hs_blocks, list_blocks.
  rewrite !in_app_iff in Hx. rewrite !in_app_iff. tauto.
Qed.

Lemma mv7_rest_in : forall es hj x,
  In x (concat (map entry_nc es) ++ concat (map (fun p : hsrc * nat => src_nc (fst p)) hj)) ->
  In x (concat (map entry_blocks es) ++ concat (map (fun p : hsrc * nat => hs_blocks (fst p)) hj)).
Proof.
  intros es hj x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_or_app; [left|right].
  - apply in_concat in Hx as (l & Hl & Hx). apply in_map_iff in Hl as (e & <- & He).
    apply in_concat. exists (entry_blocks e). split; [apply in_map; exact He|exact (mv7_ent_in e x Hx)].
  - apply in_concat in Hx as (l & Hl & Hx). apply in_map_iff in Hl as (p & <- & Hp).
    apply in_concat. exists (hs_blocks (fst p)).
    split; [apply (in_map (fun p0 : hsrc * nat => hs_blocks (fst p0))); exact Hp|exact (mv7_src_in (fst p) x Hx)].
Qed.

(* A block of L A that rmid does not free (F) is a block of L' A'. *)
Lemma mv7_keep : forall rc B API K sp Ew Fw L A mem md L' A' mem' md' q k,
  WF A -> rmid (rc := rc) B API K sp Ew Fw L A mem md L' A' mem' md' -> In (q, k) (blocks L A) -> ~ Fw q ->
  In (q, k) (blocks L' A').
Proof.
  intros rc B API K sp Ew Fw L A mem md L' A' mem' md' q k HW (_ & _ & _ & _ & _ & PA & SV & Z0 & _) Hin NF.
  apply blocks_In in Hin as (p & <- & Hp). apply blocks_In.
  destruct (Z.eq_dec k 0) as [->|Hk].
  - destruct (Z0 p Hp) as (Hp' & EA). exists p. split; [exact EA|exact Hp'].
  - pose proof (drv_ub_nonneg A p k HW Hp) as Hn.
    pose proof (SV p k Hp ltac:(lia) NF) as Hp'. exists p. split; [exact (PA p k Hp Hp' NF)|exact Hp'].
Qed.

(* The nc move of op 7 from its block facts. Rn is the part of the view other than G and the output buffer. *)
Lemma mv7_move : forall (V V' : rview) (L : layout) (A : astate) (L' : layout) (A' : astate) (live : bool)
    (OUT CAP OUT' CAP' G : Z) (Rn : list Z),
  rv_nc V = G :: OUT :: Rn -> rv_nc V' = G :: OUT' :: Rn ->
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  (forall x m, In (x, m) (blocks L' A') -> 0 <= m) ->
  (forall x m, In (x, m) (blocks L A) -> 0 < x) ->
  (CAP = 0 /\ OUT = 0) \/ (0 < CAP /\ In (OUT, CAP) (blocks L A)) ->
  ~ In OUT (G :: Rn) ->
  (forall x m, In (x, m) (blocks L A) -> ~ (live = true /\ x = OUT) -> In (x, m) (blocks L' A')) ->
  (forall x m, In (x, m) (blocks L' A') ->
     (In (x, m) (blocks L A) /\ ~ (live = true /\ x = OUT)) \/ (live = true /\ x = OUT' /\ m = CAP')) ->
  (live = false -> CAP' = CAP /\ OUT' = OUT) ->
  (live = true -> 0 < CAP' /\ In (OUT', CAP') (blocks L' A') /\
     (forall q m, In (q, m) (blocks L A) -> q <> OUT -> 0 < m -> q <> OUT')) ->
  nc_move V L A V' L' A' (out_move_dels OUT CAP OUT' CAP') (out_move_adds OUT CAP OUT' CAP').
Proof.
  intros V V' L A L' A' live OUT CAP OUT' CAP' G Rn RV0 RV1 ND0 ND1 POS1 LOW OUT0 NOR KEEP BLK LF LT.
  unfold out_move_dels, out_move_adds.
  destruct (out_same OUT CAP OUT' CAP') eqn:ES; cbn [orb].
  - (* The output buffer stays. *)
    unfold out_same in ES. apply andb_prop in ES as [S1 S2]. apply Z.eqb_eq in S1, S2. subst OUT' CAP'.
    apply (mv_build V V' L A L' A' [] [] [] (G :: OUT :: Rn) [] (fun _ => true)).
    + exact ND0.
    + exact ND1.
    + rewrite RV0. cbn [map app]. rewrite ?app_nil_r. apply Permutation_refl.
    + rewrite RV1. cbn [map app]. rewrite ?app_nil_r. apply Permutation_refl.
    + intros u [].
    + constructor.
    + intros u [].
    + intros x m _ X. discriminate X.
    + intros x m Hx. left. split; [|reflexivity].
      destruct (BLK x m Hx) as [(H0 & _)|(LV & -> & ->)]; [exact H0|].
      destruct (LT LV) as (CP & _).
      destruct OUT0 as [(C0 & _)|(_ & IN)]; [lia|exact IN].
    + intros x m H0 _. destruct (Z.eq_dec x OUT) as [->|NO].
      * destruct live eqn:LV.
        -- destruct (LT eq_refl) as (CP & IN1 & _).
           destruct OUT0 as [(C0 & _)|(_ & IN)]; [lia|].
           rewrite (mv_fst_uniq _ _ _ _ ND0 H0 IN). exact IN1.
        -- apply KEEP; [exact H0|]. intros (X & _). discriminate X.
      * apply KEEP; [exact H0|]. intros (_ & X). exact (NO X).
    + intros u [].
    + constructor.
    + intros u [].
    + exact POS1.
    + intros u [].
    + intros g [].
  - (* relay_event moved the output buffer to (OUT', CAP'). *)
    assert (LV : live = true).
    { destruct live eqn:LV; [reflexivity|]. destruct (LF eq_refl) as (C1 & O1).
      unfold out_same in ES. rewrite C1, O1, !Z.eqb_refl in ES. cbn [andb] in ES. discriminate ES. }
    destruct (LT LV) as (CP & INn & FRS).
    pose (dl := if CAP =? 0 then @nil (Z * Z) else [(OUT, CAP)]).
    pose (gl := if CAP =? 0 then [OUT] else @nil Z).
    change (if CAP =? 0 then [] else [(OUT, CAP)]) with dl.
    assert (DLf : forall u, In u dl -> u = (OUT, CAP) /\ 0 < CAP /\ In u (blocks L A)).
    { intros u Hu. unfold dl in Hu. destruct (CAP =? 0) eqn:C; [destruct Hu|].
      destruct Hu as [<-|[]]. apply Z.eqb_neq in C.
      destruct OUT0 as [(C0 & _)|(Cp & IN0)]; [contradiction|]. split; [reflexivity|]. split; [exact Cp|exact IN0]. }
    assert (OG : Permutation [OUT] (map fst dl ++ gl)).
    { unfold dl, gl. destruct (CAP =? 0); apply Permutation_refl. }
    assert (GLf : forall g, In g gl -> g = OUT /\ CAP = 0).
    { intros g Hg. unfold gl in Hg. destruct (CAP =? 0) eqn:C; [|destruct Hg].
      destruct Hg as [<-|[]]. apply Z.eqb_eq in C. split; [reflexivity|exact C]. }
    apply (mv_build V V' L A L' A' dl [(OUT', CAP')] [] (G :: Rn) gl (fun x => negb (x =? OUT))).
    + exact ND0.
    + exact ND1.
    + rewrite RV0. cbn [app]. apply perm_skip.
      eapply Permutation_trans; [apply Permutation_cons_append|]. apply Permutation_app_head. exact OG.
    + rewrite RV1. cbn [app map fst]. apply perm_skip. apply Permutation_cons_append.
    + intros u Hu. exact (proj2 (proj2 (DLf u Hu))).
    + unfold dl. destruct (CAP =? 0); cbn [map fst]; repeat constructor. intros [].
    + intros u Hu. destruct (DLf u Hu) as (-> & _). cbn [fst]. rewrite Z.eqb_refl. reflexivity.
    + intros x m _ Kx. cbv beta in Kx. apply negb_false_iff in Kx. apply Z.eqb_eq in Kx. subst x. exact NOR.
    + intros x m Hx. destruct (BLK x m Hx) as [(H0 & NO)|(_ & -> & ->)].
      * left. split; [exact H0|]. cbv beta. apply negb_true_iff. apply Z.eqb_neq. intros ->.
        apply NO. split; [exact LV|reflexivity].
      * right. left. reflexivity.
    + intros x m H0 Kx. cbv beta in Kx. apply negb_true_iff in Kx. apply Z.eqb_neq in Kx.
      apply KEEP; [exact H0|]. intros (_ & X). exact (Kx X).
    + intros u [<-|[]]. exact INn.
    + cbn [app]. constructor; [intros []|constructor].
    + intros u [<-|[]]. cbn [fst]. destruct (Z.eq_dec OUT' OUT) as [E1|E1].
      * left. rewrite E1, Z.eqb_refl. reflexivity.
      * right. intros H0. exact (FRS OUT' CAP' H0 E1 CP eq_refl).
    + exact POS1.
    + intros u Hu. destruct (DLf u Hu) as (-> & Cp & _). cbn [snd]. lia.
    + intros g Hg m Hm. destruct (GLf g Hg) as (-> & C0).
      destruct OUT0 as [(_ & O0)|(Cp & _)]; [|lia].
      rewrite O0 in Hm. pose proof (LOW _ _ Hm). lia.
Qed.

Theorem op7_rb_move_holds : op7_rb_move_stmt.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res t nfd G es es' hj
    nout cap out cap' out' HF HM HWF RM RSEP BLK HOUT LF LT HEL HREL ENC.
  pose proof HF as (FF & _).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL rc fx). }
  assert (BLO : blocks_low B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
  pose proof RM as (M' & W' & _).
  pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NDA).
  unfold target_addrs in NDA. apply hf_nodup in NDA.
  apply List.NoDup_cons_iff in NDA as [NGA NDA]. apply List.NoDup_cons_iff in NDA as [NOA _].
  apply (mv7_move _ _ L A L' A' (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) (bv_unsigned out')
    (bv_unsigned cap') G (concat (map entry_nc es) ++ concat (map (fun p : hsrc * nat => src_nc (fst p)) hj))).
  - reflexivity.
  - unfold view_of. cbn [rv_nc]. rewrite ENC. reflexivity.
  - first [exact (NDB L A mem md HM) | apply NoDup_ListNoDup; exact (NDB L A mem md HM)].
  - first [exact (NDB L' A' mem' md' M') | apply NoDup_ListNoDup; exact (NDB L' A' mem' md' M')].
  - intros x m Hx. apply blocks_In in Hx as (p & _ & Hp). exact (drv_ub_nonneg A' p m W' Hp).
  - intros x m Hx. pose proof (BLO L A mem md x m HM Hx). lia.
  - pose proof HOUT as ((O & junk & OD) & _).
    destruct OD as [(X1 & X2 & _)|(X1 & _ & X3 & _)]; [left|right]; tauto.
  - intros [X|X].
    + apply NGA. rewrite X. left. reflexivity.
    + apply NOA. exact (mv7_rest_in es hj _ X).
  - intros x m Hx NL. apply (mv7_keep rc B (API rc) _ _ _ _ L A mem md L' A' mem' md' x m HWF RM Hx).
    intros [X|X]; [exact (proj1 (RSEP x m Hx) X)|exact (NL X)].
  - exact BLK.
  - intros X. destruct (LF X) as (-> & ->). split; reflexivity.
  - intros X. destruct (LT X) as (C1 & IN & FR). split; [|split; [exact IN|exact FR]].
    clear - C1 HEL. lia.
Qed.
