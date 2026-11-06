(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr Agree SysStep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HApxF HttpRepA AWKit HObjA HObjK HObjF H_freelist H_ListAddTail H_ListFind H_httpheader_free H_UpnpPrintf H_vfm_GX H2KitA HPrepA H_hlist_view H_pent_kit
     H_germ_GL H_germ_seg1 H_germ_seg.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Variable AI : am_if FI.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Hypothesis STACK_MALLOC_2 : stack_malloc_stmt FI 2.
Hypothesis STACK_MALLOC_3 : stack_malloc_stmt FI 3.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).
Local Notation hdr := (hdr FI AI).
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.
Local Notation hreg := (H_germ_seg1.hreg FI).

Fixpoint hvs_of (ns : list (BLK * Z)) (hs : list hdr) : list hv :=
  match ns, hs with
  | (b, it) :: ns', h :: hs' => mkHv (blk_addr b) it (hid FI AI h) (vA FI AI h) (vlen FI AI h) (vcap FI AI h) :: hvs_of ns' hs'
  | _, _ => []
  end.
#[using="Type"] Lemma hvs_of_ns3 : forall ns hs, map hv3 (hvs_of ns hs) = ns3_of FI AI ns hs.
Proof. induction ns as [|[b it] ns IH]; intros [|h hs]; cbn [hvs_of ns3_of map]; try reflexivity. rewrite IH. reflexivity. Qed.
#[using="Type"] Lemma hvs_of_W : forall ns hs, length ns = length hs ->
  hvW (hvs_of ns hs) = map (fun h => (vA FI AI h, vA FI AI h + (vcap FI AI h + 1))) hs.
Proof.
  induction ns as [|[b it] ns IH]; intros [|h hs] HL; cbn [length] in HL; try discriminate; [reflexivity|].
  cbn [hvs_of]. unfold hvW in *. cbn [map hvA hvCap]. rewrite IH by lia. reflexivity.
Qed.
#[using="Type"] Lemma hvs_of_In : forall ns hs x, map snd ns = map (hA FI AI) hs -> In x (hvs_of ns hs) ->
  exists b h, In (b, hA FI AI h) ns /\ In h hs /\ x = mkHv (blk_addr b) (hA FI AI h) (hid FI AI h) (vA FI AI h) (vlen FI AI h) (vcap FI AI h).
Proof.
  induction ns as [|[b it] ns IH]; intros [|h hs] x IT HI; cbn [hvs_of] in HI; try destruct HI.
  - cbn [map] in IT. injection IT as E1 E2. cbn [snd] in E1. subst it. exists b, h. split; [left; reflexivity|]. split; [left; reflexivity| symmetry; assumption].
  - cbn [map] in IT. injection IT as E1 E2. destruct (IH hs x E2 H) as (b' & h' & H1 & H2 & H3).
    exists b', h'. split; [right; exact H1|]. split; [right; exact H2| exact H3].
Qed.
#[using="Type"] Lemma hvs_of_hdr : forall ns hs h, length ns = length hs -> In h hs ->
  exists x, In x (hvs_of ns hs) /\ hvA x = vA FI AI h /\ hvLen x = vlen FI AI h /\ hvCap x = vcap FI AI h.
Proof.
  induction ns as [|[b it] ns IH]; intros [|h0 hs] h HL Hh; cbn [length] in HL; try discriminate; [destruct Hh|].
  cbn [hvs_of]. destruct Hh as [<-|Hh].
  - eexists. split; [left; reflexivity|]. cbn. repeat split.
  - destruct (IH hs h ltac:(lia) Hh) as (x & Hx & E). exists x. split; [right; exact Hx| exact E].
Qed.

#[using="Type"] Lemma blk_hreg : forall s (LB : BL) m (b : BLK), RHEAP_A FI AI s LB m -> In b LB -> hreg (blk_addr b) (blk_size b).
Proof.
  intros s LB m b HR Hb. destruct (am_block_range FI AI s LB m b HR Hb) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  unfold H_germ_seg1.hreg. split; [exact R5|]. split; [exact R4|]. split; [exact R7| exact R6].
Qed.
#[using="Type"] Lemma blk_apart8 : forall s (LB : BL) m (b1 b2 : BLK), RHEAP_A FI AI s LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
  ru8G (blk_addr b1 + blk_size b1) <= blk_addr b2 \/ ru8G (blk_addr b2 + blk_size b2) <= blk_addr b1.
Proof.
  intros s LB m b1 b2 HR H1 H2 NE.
  destruct (am_block_range FI AI s LB m b1 HR H1) as (_ & A1 & _). destruct (am_block_range FI AI s LB m b2 HR H2) as (_ & A2 & _).
  destruct (am_blocks_disjoint FI AI s LB m b1 b2 HR H1 H2 NE) as [D|D]; [left| right]; unfold ru8G; Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma nodup_app_neq : forall (L1 L2 : BL) (a b : BLK), NoDup (map blk_id (L1 ++ L2)) -> In a L1 -> In b L2 -> a <> b.
Proof.
  induction L1 as [|x L1 IH]; intros L2 a b ND Ha Hb E; [destruct Ha|]. cbn [app map] in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Ha as [->|Ha]; [| exact (IH L2 b b ND' Ha Hb eq_refl)]. apply NI. apply list_elem_of_In. apply in_map. apply in_or_app. right. exact Hb.
Qed.
#[using="Type"] Lemma nodup_app_r : forall (L1 L2 : BL), NoDup (map blk_id (L1 ++ L2)) -> NoDup (map blk_id L2).
Proof. induction L1 as [|x L1 IH]; intros L2 ND; [exact ND|]. cbn [app map] in ND. inversion ND; subst. apply IH. assumption. Qed.
#[using="Type"] Lemma nodup_app_l : forall (L1 L2 : BL), NoDup (map blk_id (L1 ++ L2)) -> NoDup (map blk_id L1).
Proof.
  induction L1 as [|x L1 IH]; intros L2 ND; [constructor|]. cbn [app map] in ND |- *. inversion ND as [|? ? NI ND']; subst. constructor; [| exact (IH L2 ND')].
  intros HI. apply NI. apply list_elem_of_In. apply list_elem_of_In in HI. rewrite map_app. apply in_or_app. left. exact HI.
Qed.
#[using="Type"] Lemma hdrs_pos : forall (hs : list hdr), NoDup (map blk_id (hdrs_blocks FI AI hs)) -> forall h h' (b : BLK),
  In h hs -> In h' hs -> In b (hblocks FI AI h) -> In b (hblocks FI AI h') -> h = h'.
Proof.
  induction hs as [|h0 hs IH]; intros ND h h' b Hh Hh' Hb Hb'; [destruct Hh|]. rewrite hdrs_blocks_cons in ND.
  destruct Hh as [<-|Hh]; destruct Hh' as [<-|Hh'].
  - reflexivity.
  - exfalso. exact (nodup_app_neq _ _ b b ND Hb (hdrs_blocks_In FI AI hs h' b Hh' Hb') eq_refl).
  - exfalso. exact (nodup_app_neq _ _ b b ND Hb' (hdrs_blocks_In FI AI hs h b Hh Hb) eq_refl).
  - exact (IH (nodup_app_r _ _ ND) h h' b Hh Hh' Hb Hb').
Qed.
#[using="Type"] Lemma hdr_nodup : forall (hs : list hdr), NoDup (map blk_id (hdrs_blocks FI AI hs)) -> forall h, In h hs -> NoDup (map blk_id (hblocks FI AI h)).
Proof.
  induction hs as [|h0 hs IH]; intros ND h Hh; [destruct Hh|]. rewrite hdrs_blocks_cons in ND.
  destruct Hh as [<-|Hh]; [exact (nodup_app_l _ _ ND)| exact (IH (nodup_app_r _ _ ND) h Hh)].
Qed.
#[using="Type"] Lemma hblocks_distinct : forall (hs : list hdr), NoDup (map blk_id (hdrs_blocks FI AI hs)) -> forall h h', In h hs -> In h' hs ->
  (hk FI AI h', hA FI AI h', 88) <> (vk FI AI h, vA FI AI h, vcap FI AI h + 1)
  /\ (nk FI AI h', nA FI AI h', ncap FI AI h' + 1) <> (vk FI AI h, vA FI AI h, vcap FI AI h + 1)
  /\ ((vk FI AI h', vA FI AI h', vcap FI AI h' + 1) = (vk FI AI h, vA FI AI h, vcap FI AI h + 1) -> h' = h).
Proof.
  intros hs ND h h' Hh Hh'.
  assert (VI : In (vk FI AI h, vA FI AI h, vcap FI AI h + 1) (hblocks FI AI h)) by (right; left; reflexivity).
  pose proof (hdr_nodup hs ND h Hh) as NDh.
  split; [| split].
  - intros E. assert (EH : h = h') by (apply (hdrs_pos hs ND h h' _ Hh Hh' VI); rewrite <- E; left; reflexivity). subst h'.
    change (hblocks FI AI h) with ([(hk FI AI h, hA FI AI h, 88)] ++ [(vk FI AI h, vA FI AI h, vcap FI AI h + 1); (nk FI AI h, nA FI AI h, ncap FI AI h + 1)]) in NDh.
    exact (nodup_app_neq _ _ _ _ NDh ltac:(left; reflexivity) ltac:(left; reflexivity) E).
  - intros E. assert (EH : h = h') by (apply (hdrs_pos hs ND h h' _ Hh Hh' VI); rewrite <- E; right; right; left; reflexivity). subst h'.
    change (hblocks FI AI h) with ([(hk FI AI h, hA FI AI h, 88); (vk FI AI h, vA FI AI h, vcap FI AI h + 1)] ++ [(nk FI AI h, nA FI AI h, ncap FI AI h + 1)]) in NDh.
    exact (nodup_app_neq _ _ _ _ NDh ltac:(right; left; reflexivity) ltac:(left; reflexivity) (eq_sym E)).
  - intros E. symmetry. apply (hdrs_pos hs ND h h' _ Hh Hh' VI). rewrite <- E. right; left; reflexivity.
Qed.
#[using="Type"] Lemma disjoint_from_app : forall W1 W2 X n, disjoint_from W1 X n -> disjoint_from W2 X n -> disjoint_from (W1 ++ W2) X n.
Proof. induction W1 as [|[a b] W1 IH]; intros W2 X n D1 D2; cbn [app disjoint_from] in *; [exact D2|]. destruct D1 as [D0 D1]. split; [exact D0| exact (IH W2 X n D1 D2)]. Qed.
#[using="Type"] Lemma blk_eq_dec : forall b1 b2 : BLK, b1 = b2 \/ b1 <> b2.
Proof.
  intros [[k1 a1] n1] [[k2 a2] n2]. destruct (am_K_eqb FI AI k1 k2) eqn:Q.
  - apply (proj1 (am_K_eqb_eq FI AI k1 k2)) in Q. subst k2. destruct (Z.eq_dec a1 a2) as [->|NA]; [| right; intros E; injection E; intros; contradiction].
    destruct (Z.eq_dec n1 n2) as [->|NN]; [left; reflexivity| right; intros E; injection E; intros; contradiction].
  - right. intros E. injection E as E1 E2 E3. subst k2. rewrite (proj2 (am_K_eqb_eq FI AI k1 k1) eq_refl) in Q. discriminate.
Qed.

Section VIEW.
Variables (s : PS) (LB : BL) (m : mem) (P : Z) (ns : list (BLK * Z)) (hs : list hdr) (X : Z).
Hypothesis HR : RHEAP_A FI AI s LB m.
Hypothesis PHL : p_hlist FI AI m P ns hs X.
Hypothesis XB : X <= 2^27 + 64.
Hypothesis SUB : bsub FI AI (hl_blocks FI AI ns hs) LB.
Hypothesis ND : NoDup (map blk_id (hl_blocks FI AI ns hs)).

#[using="m P hs X PHL SUB"] Lemma germ_node_blk : forall b it, In (b, it) ns -> In b LB /\ blk_size b = 24 /\ In b (map fst ns).
Proof.
  intros b it Hb. destruct PHL as (_ & _ & _ & DL & _). assert (Hf : In b (map fst ns)) by (apply (in_map fst _ _ Hb)).
  split; [apply SUB; unfold hl_blocks; apply in_or_app; left; exact Hf|]. split; [exact (proj1 (dlseg_facts FI AI _ _ _ _ _ _ DL Hb))| exact Hf].
Qed.
#[using="ns SUB"] Lemma germ_hdr_blk : forall h b, In h hs -> In b (hblocks FI AI h) -> In b LB /\ In b (hdrs_blocks FI AI hs).
Proof.
  intros h b Hh Hb. pose proof (hdrs_blocks_In FI AI hs h b Hh Hb) as Hbb. split; [apply SUB; unfold hl_blocks; apply in_or_app; right; exact Hbb| exact Hbb].
Qed.
#[using="ns ND"] Lemma germ_nd_hdrs : NoDup (map blk_id (hdrs_blocks FI AI hs)).
Proof. unfold hl_blocks in ND. exact (nodup_app_r _ _ ND). Qed.

#[using="s LB m P X HR PHL XB SUB"] Lemma germ_hpure : forall x, In x (hvs_of ns hs) -> H_germ_seg1.hpure FI x.
Proof.
  intros x Hx. pose proof PHL as (_ & _ & _ & DL & HM & IT & VB & _).
  destruct (hvs_of_In ns hs x IT Hx) as (b & h & Hb & Hh & ->).
  destruct (hdrs_mem_In FI AI hs m h HM Hh) as (_ & (P1 & P2 & _)). destruct (VB h Hh) as (V1 & _).
  destruct (germ_node_blk b _ Hb) as (BIN & BSZ & _).
  destruct (germ_hdr_blk h (hk FI AI h, hA FI AI h, 88) Hh ltac:(left; reflexivity)) as (IIN & _).
  destruct (germ_hdr_blk h (vk FI AI h, vA FI AI h, vcap FI AI h + 1) Hh ltac:(right; left; reflexivity)) as (VIN & _).
  unfold H_germ_seg1.hpure. cbn [hvN hvIt hvId hvA hvLen hvCap].
  split; [exact P1|]. split; [lia|].
  split; [rewrite <- BSZ; exact (blk_hreg s LB m b HR BIN)|].
  split; [exact (blk_hreg s LB m _ HR IIN)| exact (blk_hreg s LB m _ HR VIN)].
Qed.

#[using="s LB m P X HR PHL SUB ND"] Lemma germ_hapart : forall x x', In x (hvs_of ns hs) -> In x' (hvs_of ns hs) ->
  (hvN x' + 24 <= hvA x \/ ru8G (hvA x + (hvCap x + 1)) <= hvN x') /\ (hvIt x' + 88 <= hvA x \/ ru8G (hvA x + (hvCap x + 1)) <= hvIt x')
  /\ ((hvA x = hvA x' /\ hvLen x = hvLen x' /\ hvCap x = hvCap x') \/ ru8G (hvA x' + (hvCap x' + 1)) <= hvA x \/ ru8G (hvA x + (hvCap x + 1)) <= hvA x').
Proof.
  intros x x' Hx Hx'. pose proof PHL as (_ & _ & _ & DL & HM & IT & VB & _).
  destruct (hvs_of_In ns hs x IT Hx) as (b & h & Hb & Hh & ->). destruct (hvs_of_In ns hs x' IT Hx') as (b' & h' & Hb' & Hh' & ->).
  cbn [hvN hvIt hvId hvA hvLen hvCap].
  destruct (germ_node_blk b' _ Hb') as (BIN' & BSZ' & BF').
  destruct (germ_hdr_blk h' (hk FI AI h', hA FI AI h', 88) Hh' ltac:(left; reflexivity)) as (IIN' & IHB').
  destruct (germ_hdr_blk h' (vk FI AI h', vA FI AI h', vcap FI AI h' + 1) Hh' ltac:(right; left; reflexivity)) as (VIN' & VHB').
  destruct (germ_hdr_blk h (vk FI AI h, vA FI AI h, vcap FI AI h + 1) Hh ltac:(right; left; reflexivity)) as (VIN & VHB).
  pose proof (ru8G_spec (blk_addr b' + 24)) as (U1 & _). pose proof (ru8G_spec (hA FI AI h' + 88)) as (U2 & _).
  split; [| split].
  - assert (NE : b' <> (vk FI AI h, vA FI AI h, vcap FI AI h + 1)) by (unfold hl_blocks in ND; exact (nodup_app_neq _ _ _ _ ND BF' VHB)).
    destruct (blk_apart8 s LB m _ _ HR BIN' VIN NE) as [D|D]; cbn [blk_addr blk_size fst snd] in D; rewrite ?BSZ' in D; [left; lia| right; exact D].
  - pose proof (proj1 (hblocks_distinct hs germ_nd_hdrs h h' Hh Hh')) as NE.
    destruct (blk_apart8 s LB m _ _ HR IIN' VIN NE) as [D|D]; cbn [blk_addr blk_size fst snd] in D; [left; lia| right; exact D].
  - destruct (blk_eq_dec (vk FI AI h', vA FI AI h', vcap FI AI h' + 1) (vk FI AI h, vA FI AI h, vcap FI AI h + 1)) as [E|NE].
    + left. rewrite (proj2 (proj2 (hblocks_distinct hs germ_nd_hdrs h h' Hh Hh')) E). repeat split.
    + right. destruct (blk_apart8 s LB m _ _ HR VIN' VIN NE) as [D|D]; cbn [blk_addr blk_size fst snd] in D; [left; exact D| right; exact D].
Qed.

#[using="s HR"] Lemma blk_slack8 : forall (b : BLK) bs, In b LB -> bytes_at asegs m (blk_addr b) bs -> Z.of_nat (length bs) = blk_size b ->
  exists sl, bytes_at asegs m (blk_addr b + blk_size b) sl /\ blk_addr b + blk_size b + Z.of_nat (length sl) = ru8G (blk_addr b + blk_size b).
Proof.
  intros b bs HIN B L.
  destruct (am_block_range FI AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (ru8G_spec (blk_addr b + blk_size b)) as (RU & _).
  assert (RE : round_up8 (blk_addr b + blk_size b) = ru8G (blk_addr b + blk_size b)) by (unfold round_up8, ru8G; lia).
  destruct (bytes_at_extendA (Z.to_nat (ru8G (blk_addr b + blk_size b) - (blk_addr b + blk_size b))) m (blk_addr b) bs B) as (sl & B2 & L2).
  - intros x Hx. eapply (am_block_slack FI AI); [exact HR| exact HIN| rewrite RE; lia].
  - lia.
  - apply bytes_at_app in B2. destruct B2 as [_ B2]. rewrite L in B2. exists sl. split; [exact B2| rewrite L2; lia].
Qed.

#[using="s LB X HR PHL SUB"] Lemma germ_hview : H_germ_seg1.hview P (hd_addr FI AI ns (P + 312)) (hvs_of ns hs) m.
Proof.
  destruct (plist_view FI AI s LB m P ns hs X HR PHL SUB) as (LS & OBJ & LEN).
  pose proof PHL as (_ & _ & _ & DL & HM & IT & VB & _).
  unfold H_germ_seg1.hview. split; [rewrite hvs_of_ns3; exact LS|].
  intros x Hx. pose proof (in_map hv3 _ _ Hx) as H3. rewrite hvs_of_ns3 in H3.
  destruct (hvs_of_In ns hs x IT Hx) as (b & h & Hb & Hh & ->). unfold hv3 in H3. cbn [hvN hvIt hvId] in H3.
  destruct (OBJ _ _ _ H3) as (ON & OI).
  destruct (hdrs_mem_In FI AI hs m h HM Hh) as ((_ & VC & (vbs & VBk & VN) & _) & (P1 & _)).
  destruct (germ_hdr_blk h (vk FI AI h, vA FI AI h, vcap FI AI h + 1) Hh ltac:(right; left; reflexivity)) as (VIN & _).
  unfold H_germ_seg1.hitem. cbn [hvN hvIt hvId hvA hvLen hvCap].
  split; [exact ON|]. split; [exact OI|]. split; [exact VC|].
  split; [eapply (block_shw FI AI s LB m (vk FI AI h, vA FI AI h, vcap FI AI h + 1)); [exact HR| exact VIN| cbn; lia| cbn; lia| lia]|].
  split; [exists vbs; split; [exact VBk| exact VN]|].
  assert (BY : bytes_at asegs m (vA FI AI h) vbs) by (destruct VBk as [[_ BY] _]; cbn [cells_bytes cbytes] in BY; rewrite app_nil_r in BY; exact BY).
  assert (LV : Z.of_nat (length vbs) = vcap FI AI h + 1) by (destruct VBk as [[WF _] _]; cbn in WF; destruct WF as (W0 & _); rewrite W0; lia).
  exact (blk_slack8 (vk FI AI h, vA FI AI h, vcap FI AI h + 1) vbs VIN BY LV).
Qed.

#[using="AMS s LB X HR PHL SUB"] Lemma germ_fev : forall lo q (st : fsstate FI), RFAKE FI st m -> lb (fs_live FI st) P 504 -> alloc_ceiling <= lo -> forall m',
  munch ((lo, q) :: FSIV ([(P + 384, P + 400); (P + 440, P + 480); (ERRNO_G, ERRNO_G + 4)] ++ hvW (hvs_of ns hs))) m m' -> wmono asegs m m' -> FSENV FI m'.
Proof.
  intros lo q st RF PLB CLO m' MU WM. apply (am_fsenv FI AI s LB m'). eapply (am_heap_frame FI AI s LB m m' _ HR MU WM).
  destruct PLB as (g & Hg & G1 & G2). pose proof (live_wf FI st m RF) as LW. rewrite Forall_forall in LW.
  destruct (LW g Hg) as (KR & GLO & GHI & _). unfold ff_size in *.
  pose proof PHL as (_ & _ & _ & _ & _ & IT & _).
  assert (LEN : length ns = length hs) by (rewrite <- (length_map snd ns), IT, length_map; reflexivity).
  apply Forall_cons; [left; cbn [fst]; exact CLO|].
  apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|].
  apply Forall_cons; [do 4 right; cbn [fst snd]; lia|].
  apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|].
  apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|].
  apply Forall_cons; [right; left; exists 0x5e68c8, 0x5e68d0; cbn [fst snd]; split; [apply AMS; unfold a0_static; split; [lia| env_band]| split; [lia| split; [lia| unfold a0_wsafe; lia]]]|].
  rewrite (hvs_of_W ns hs LEN). apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (h & <- & Hh).
  destruct (germ_hdr_blk h (vk FI AI h, vA FI AI h, vcap FI AI h + 1) Hh ltac:(right; left; reflexivity)) as (VIN & _).
  right; right; left. exists (vk FI AI h, vA FI AI h, vcap FI AI h + 1). split; [exact VIN| cbn; lia].
Qed.
End VIEW.

Section POST.
Variables (s : PS) (LB : BL) (m m' : mem) (P : Z) (ns : list (BLK * Z)) (hs : list hdr) (X : Z) (lo q A cur : Z) (st : fsstate FI).
Hypothesis HR : RHEAP_A FI AI s LB m.
Hypothesis PHL : p_hlist FI AI m P ns hs X.
Hypothesis SUB : bsub FI AI (hl_blocks FI AI ns hs) LB.
Hypothesis ND : NoDup (map blk_id (hl_blocks FI AI ns hs)).
Hypothesis RF : RFAKE FI st m.
Hypothesis PLB : lb (fs_live FI st) P 504.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis ARNG : 0 <= A /\ A + cur < 2^64.
Local Notation WG := ((lo, q) :: FSIV ([(P + 384, P + 400); (P + 440, P + 480); (ERRNO_G, ERRNO_G + 4)] ++ hvW (hvs_of ns hs)))%Z.
Hypothesis MU : munch WG m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis HV' : H_germ_seg1.hview P (hd_addr FI AI ns (P + 312)) (hvs_of ns hs) m'.

#[using="s m X A cur st HR PHL SUB RF PLB CLO ARNG"] Lemma germ_dj : forall (b : BLK), In b LB -> (forall h, In h hs -> b <> (vk FI AI h, vA FI AI h, vcap FI AI h + 1)) ->
  disjoint_from WG (blk_addr b) (blk_size b).
Proof.
  intros b Hb NE. pose proof PHL as (_ & _ & _ & _ & _ & IT & _).
  assert (LEN : length ns = length hs) by (rewrite <- (length_map snd ns), IT, length_map; reflexivity).
  pose proof (proj2 (H_germ_seg1.hsafe_W0 FI P lo q st m A cur CLO RF ARNG PLB) _ _ (blk_hreg s LB m b HR Hb)) as D0.
  pose proof (ru8G_spec (blk_addr b + blk_size b)) as (U & _).
  destruct (am_block_range FI AI s LB m b HR Hb) as (_ & _ & R3 & _).
  change WG with (((lo, q) :: FSIV ([(P + 384, P + 400); (P + 440, P + 480); (ERRNO_G, ERRNO_G + 4)] ++ []))%Z ++ hvW (hvs_of ns hs)).
  apply disjoint_from_app; [eapply disjoint_from_sub; [exact D0| lia| lia]|].
  rewrite (hvs_of_W ns hs LEN). clear D0.
  assert (G : forall (l : list hdr), (forall h, In h l -> In h hs) -> disjoint_from (map (fun h => (vA FI AI h, vA FI AI h + (vcap FI AI h + 1))) l) (blk_addr b) (blk_size b)).
  { induction l as [|h l IH]; intros INC; cbn [map disjoint_from]; [exact I|]. split; [| apply IH; intros h' Hh'; apply INC; right; exact Hh'].
    assert (Hh : In h hs) by (apply INC; left; reflexivity).
    assert (VIN : In (vk FI AI h, vA FI AI h, vcap FI AI h + 1) LB) by (apply SUB; unfold hl_blocks; apply in_or_app; right; apply (hdrs_blocks_In FI AI hs h _ Hh); right; left; reflexivity).
    pose proof (ru8G_spec (vA FI AI h + (vcap FI AI h + 1))) as (U2 & _).
    destruct (blk_apart8 s LB m _ _ HR Hb VIN (NE h Hh)) as [D|D]; cbn [blk_addr blk_size fst snd] in D; lia. }
  apply G. intros h Hh. exact Hh.
Qed.

#[using="s LB m P ns X lo q A cur st HR PHL SUB ND RF PLB CLO ARNG MU WM HV'"] Lemma germ_hdrs_post : hdrs_mem FI AI m' hs.
Proof.
  pose proof PHL as (_ & _ & _ & _ & HM & IT & _).
  assert (LEN : length ns = length hs) by (rewrite <- (length_map snd ns), IT, length_map; reflexivity).
  assert (NDH : NoDup (map blk_id (hdrs_blocks FI AI hs))) by (unfold hl_blocks in ND; exact (nodup_app_r _ _ ND)).
  assert (G : forall (l : list hdr), (forall h, In h l -> In h hs) -> hdrs_mem FI AI m l -> hdrs_mem FI AI m' l).
  { induction l as [|h l IH]; intros INC HMl; cbn [HObjA.hdrs_mem] in *; [exact I|]. destruct HMl as (HO & HP & HMl').
    split; [| split; [exact HP| apply IH; [intros h' Hh'; apply INC; right; exact Hh'| exact HMl']]].
    assert (Hh : In h hs) by (apply INC; left; reflexivity).
    destruct HO as ([pad HCc] & VC & _ & NC & [nbs [NB NN]]). destruct HP as (P1 & P2 & P3 & P4 & _).
    assert (IIN : In (hk FI AI h, hA FI AI h, 88) LB) by (apply SUB; unfold hl_blocks; apply in_or_app; right; apply (hdrs_blocks_In FI AI hs h _ Hh); left; reflexivity).
    assert (NIN : In (nk FI AI h, nA FI AI h, ncap FI AI h + 1) LB) by (apply SUB; unfold hl_blocks; apply in_or_app; right; apply (hdrs_blocks_In FI AI hs h _ Hh); right; right; left; reflexivity).
    pose proof (germ_dj _ IIN (fun h0 Hh0 => proj1 (hblocks_distinct hs NDH h0 h Hh0 Hh))) as DI. cbn [blk_addr blk_size fst snd] in DI.
    pose proof (germ_dj _ NIN (fun h0 Hh0 => proj1 (proj2 (hblocks_distinct hs NDH h0 h Hh0 Hh)))) as DN. cbn [blk_addr blk_size fst snd] in DN.
    destruct (hvs_of_hdr ns hs h LEN Hh) as (x & Hx & E1 & E2 & E3).
    destruct (proj2 HV' x Hx) as (_ & _ & _ & _ & (vbs' & VB' & VN') & _). rewrite E1, E3 in VB'. rewrite E2 in VN'.
    split; [exists pad; eapply rw_cells_transport; [exact HCc| exact MU| exact WM| eapply disjoint_from_sub; [exact DI| lia| cbn; lia]]|].
    split; [eapply rw_cells_transport; [exact VC| exact MU| exact WM| eapply disjoint_from_sub; [exact DI| lia| unfold mbuf_cells; cbn; lia]]|].
    split; [exists vbs'; split; [exact VB'| exact VN']|].
    split; [eapply rw_cells_transport; [exact NC| exact MU| exact WM| eapply disjoint_from_sub; [exact DI| lia| unfold mbuf_cells; cbn; lia]]|].
    exists nbs. split; [| exact NN]. eapply rw_cells_transport; [exact NB| exact MU| exact WM| eapply disjoint_from_sub; [exact DN| lia| cbn; lia]]. }
  exact (G hs (fun h Hh => Hh) HM).
Qed.

#[using="s LB m hs X lo q A cur st HR PHL SUB ND RF PLB CLO ARNG MU WM"] Lemma germ_dlseg_post : dlseg FI AI m' ns (P + 288) (P + 312).
Proof.
  pose proof PHL as (_ & _ & _ & DL & _).
  eapply (dlseg_transport FI AI ns m m' _ _ _ DL MU WM). intros b it Hb.
  assert (Hf : In b (map fst ns)) by (apply (in_map fst _ _ Hb)).
  assert (BIN : In b LB) by (apply SUB; unfold hl_blocks; apply in_or_app; left; exact Hf).
  pose proof (proj1 (dlseg_facts FI AI _ _ _ _ _ _ DL Hb)) as BSZ. rewrite <- BSZ. apply (germ_dj b BIN).
  intros h Hh. unfold hl_blocks in ND. apply (nodup_app_neq _ _ _ _ ND Hf). apply (hdrs_blocks_In FI AI hs h _ Hh). right; left; reflexivity.
Qed.

#[using="s LB m lo q A cur st HR PHL SUB ND RF PLB CLO ARNG MU WM HV'"] Lemma germ_hlist_post :
  rw_cells asegs m' (P + 288) (lhead_cells (hd_addr FI AI ns (P + 312)) (last_addr FI AI ns (P + 288)) (zlength ns)) ->
  rw_cells asegs m' (P + 344) (fl_cells 0 0) ->
  rw_cells asegs m' (P + 368) [C8 (wz httpheader_free_entryA); C8 (wz httpmsg_compare_entryA)] ->
  p_hlist FI AI m' P ns hs X.
Proof.
  intros L1 L2 L3. pose proof PHL as (_ & _ & _ & _ & _ & IT & VB & ZL & X0).
  unfold p_hlist. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact germ_dlseg_post|]. split; [exact germ_hdrs_post|].
  split; [exact IT|]. split; [exact VB|]. split; [exact ZL| exact X0].
Qed.
End POST.

#[using="Type"] Lemma c4_norm : forall w : word, exists c, 0 <= c < 2^32 /\ le4 (wz c) = le4 w.
Proof.
  intros w. exists (bytes_le_to_Z (le4 w)). pose proof (bytes_le_to_Z_nonneg (le4 w)) as N. pose proof (bytes_le_to_Z_bound (le4 w)) as B.
  rewrite length_le4 in B. change (2 ^ (8 * Z.of_nat 4)) with (2^32) in B. split; [split; [exact N| exact B]|].
  unfold le4 at 1. rewrite unsigned_lit by lia. pose proof (Z_to_le_bytes_inv (le4 w)) as IV. rewrite length_le4 in IV. exact IV.
Qed.

#[using="IC AMS STACK_MALLOC_2 STACK_MALLOC_3 SET_SHADOW_F5"] Theorem germ_spec_A : germ_stmt_A FI AI (gstA GL_germ).
Proof.
  unfold germ_stmt_A.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st P lo cur A len cap okm bs ns hs X
         meth isreq maj min rm sc err hack pos entp clen csz esp eb el ev canary.
  intros HR RF FCO AE ST CLO LO QAL Q47 MI PLB PHI PAL0 SHWP SUB ND PMETH PRS PVER PHL XB PENT PMSG PCTL PSCAN CURR CLOW SHWE IWC GST SHZ SHR ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  set (hvs := hvs_of ns hs). set (first := hd_addr FI AI ns (P + 312)). set (last := last_addr FI AI ns (P + 288)). set (size := zlength ns).
  destruct PMETH as (PM & METHR). destruct PRS as (PRSc & RMR & SCR). destruct PVER as (PV & ISR & _ & _).
  pose proof PHL as (LHC & FLC & FFC & _ & _ & IT & _).
  assert (LEN : length ns = length hs) by (rewrite <- (length_map snd ns), IT, length_map; reflexivity).
  pose proof PMSG as (PMB & _). destruct PCTL as (PC & R_err & R_hack & R_pos & R_entp & R_clen & R_csz & R_esp).
  destruct CLOW as (CE & CG & CC).
  assert (ARNG : 0 <= A /\ A + cur < 2^64).
  { destruct (p_msg_facts FI AI m LB P A len cap okm bs s HR PMSG) as (F1 & F2 & _ & F4 & F5). destruct okm as [k|].
    - destruct (F5 ltac:(discriminate)) as (G1 & G2 & _). lia.
    - destruct (F4 eq_refl) as (G1 & G2 & _). lia. }
  assert (CURB : 0 <= cur < 2^64).
  { destruct (p_msg_facts FI AI m LB P A len cap okm bs s HR PMSG) as (F1 & F2 & _). unfold LMAX_A in F2. clear - F1 F2 CURR. lia. }
  assert (AL16 : q = 16 * (q / 16)) by (clear - QAL; Z.div_mod_to_equations; lia).
  assert (PAL : P = 8 * (P / 8)) by (clear - PAL0; Z.div_mod_to_equations; lia).
  assert (PLO : 0x609000 <= P).
  { destruct PLB as (g & Hg & G1 & G2). pose proof (live_wf FI st m RF) as LW. rewrite Forall_forall in LW. destruct (LW g Hg) as (_ & GLO & _).
    pose proof (fsb_ok FI) as (B1 & _). clear - G1 GLO B1. lia. }
  assert (QHI : q < 2^64) by (clear - Q47; lia). assert (Q63 : q < 2^63) by (clear - Q47; lia).
  assert (SHWCH : shw m A0_CHUNKED 8) by (unfold gstA, GL_germ in GST; exact (Forall_inv GST)).
  pose proof (am_fsenv FI AI s LB m HR) as FE0.
  assert (TPV : wz A0_TP = Z_to_bv 64 6187376) by reflexivity.
  assert (PL : rw_cells asegs m (P + 288) (llist_cells first last size 0 0 httpheader_free_entryA httpmsg_compare_entryA)).
  { pose proof (proj2 (rw_cells_app asegs m (P + 344) (fl_cells 0 0) [C8 (wz httpheader_free_entryA); C8 (wz httpmsg_compare_entryA)])) as Jc1.
    unfold fl_cells in Jc1 at 2. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in Jc1.
    change (Z.of_nat 24) with 24 in Jc1. replace (P + 344 + 24) with (P + 368) in Jc1 by lia. specialize (Jc1 (conj FLC FFC)).
    pose proof (proj2 (rw_cells_app asegs m (P + 288) (lhead_cells first last size) (fl_cells 0 0 ++ [C8 (wz httpheader_free_entryA); C8 (wz httpmsg_compare_entryA)]))) as Jc2.
    unfold lhead_cells in Jc2 at 2. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in Jc2.
    change (Z.of_nat 56) with 56 in Jc2. replace (P + 288 + 56) with (P + 344) in Jc2 by lia. exact (Jc2 (conj LHC Jc1)). }
  assert (PINV : H_germ_seg1.pinvG P meth rm sc isreq maj min A len cap cur csz canary first last size 0 0 httpheader_free_entryA m eb el (wz err) (wz hack) (wz pos) (wz entp) (wz clen) (wz esp)).
  { unfold H_germ_seg1.pinvG. split; [exact PM|]. split; [exact PRSc|]. split; [exact PV|]. split; [exact PL|]. split; [exact PENT|]. split; [exact PMB|].
    split; [exact PC|]. split; [exact PSCAN|]. split; [exists ev; exact CE|]. split; [exact CG|]. split; [exact CC| exact IWC]. }
  pose proof (germ_hpure s LB m P ns hs X HR PHL XB SUB) as HPURE.
  pose proof (germ_hapart s LB m P ns hs X HR PHL SUB ND) as HAPART.
  pose proof (germ_hview s LB m P ns hs X HR PHL SUB) as HV0.
  pose proof (germ_fev s LB m P ns hs X HR PHL SUB lo q st RF PLB CLO) as FEV.
  fold hvs in HPURE, HAPART, HV0, FEV. fold first in HV0.
  eapply evt_mono; [exact (H_germ_seg.germ_seg FI IC STACK_MALLOC_3 STACK_MALLOC_2 SET_SHADOW_F5 P lo q (q / 16) (P / 8) st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m meth rm sc isreq maj min A len cap cur csz canary first last size 0 0 httpheader_free_entryA hvs CLO LO AL16 QHI Q63 RF FCO FE0 PAL PLO PHI SHWP SHWCH SHWE TPV CURR METHR RMR SCR ISR ARNG PLB HPURE HAPART HV0 FEV t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 eb el (wz err) (wz hack) (wz pos) (wz entp) (wz clen) (wz esp) ST MI AE PINV)|].
  intros ms' PO.
  destruct PO as (r & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & st' & -> & MU & WM & MI' & FK & LIVE & RF' & ST' & AE' & XP).
  destruct XP as (errw' & hackw' & posw' & entpw' & clenw' & PINV' & HV' & CASES).
  destruct PINV' as (PM' & PRS' & PV' & PL' & PE' & PMB' & PC' & PS' & (ev' & CE') & CG' & CC' & IWC').

  assert (SZ1 : Z.of_nat (cells_size (lhead_cells first last size)) = 56) by reflexivity.
  assert (SZ2 : Z.of_nat (cells_size (fl_cells 0 0)) = 24) by reflexivity.
  pose proof (proj1 (rw_cells_app asegs m' (P + 288) (lhead_cells first last size) (fl_cells 0 0 ++ [C8 (wz httpheader_free_entryA); C8 (wz httpmsg_compare_entryA)]))) as Sc2.
  rewrite SZ1 in Sc2. replace (P + 288 + 56) with (P + 344) in Sc2 by lia. destruct (Sc2 PL') as [L1 L23].
  pose proof (proj1 (rw_cells_app asegs m' (P + 344) (fl_cells 0 0) [C8 (wz httpheader_free_entryA); C8 (wz httpmsg_compare_entryA)])) as Sc1.
  rewrite SZ2 in Sc1. replace (P + 344 + 24) with (P + 368) in Sc1 by lia. destruct (Sc1 L23) as [L2 L3].
  pose proof (germ_hlist_post s LB m m' P ns hs X lo q A cur st HR PHL SUB ND RF PLB CLO ARNG MU WM HV' L1 L2 L3) as PHL'.

  destruct (c4_norm clenw') as (cl & CLR & CLE).
  assert (PCn : rw_cells asegs m' (P + 440) [C4 errw'; C4 hackw'; C4 posw'; C4 entpw'; C4 (wz cl); C4 (wz 0); C8 (wz csz); C8 (wz cur)])
    by exact (rw_cells_recell asegs m' (P + 440) [C4 errw'; C4 hackw'; C4 posw'; C4 entpw'] (C4 clenw') (C4 (wz cl)) [C4 (wz 0); C8 (wz csz); C8 (wz cur)] PC' I CLE eq_refl).
  assert (FIN : forall err' hack' pos' entp', errw' = wz err' -> hackw' = wz hack' -> posw' = wz pos' -> entpw' = wz entp' ->
      0 <= err' < 2^31 -> 0 <= hack' <= 1 -> 0 <= pos' <= 4 -> 0 <= entp' <= 6 ->
      ((r = 0 /\ pos' = 4 /\ entp' = entp /\ err' = err /\ hack' = hack) \/ (r = 6 /\ pos' = pos /\ 2 <= entp' <= 4 /\ err' = err /\ hack' = hack)
       \/ (r = 3 /\ pos' = pos /\ entp' = entp /\ err' = 411)) ->
      germ_post_A FI AI ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo P ns hs X A cur err hack pos entp csz canary m
        (MS (mkR ra (Z_to_bv 64 q) gp (wz A0_TP) u0 u1 u2 s0 s1 (Z_to_bv 64 r) v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F_ (ret_pc ra) fc None m' (seg_rom asegs))).
  { intros err' hack' pos' entp' E1 E2 E3 E4 B1 B2 B3 B4 CS. subst errw' hackw' posw' entpw'.
    unfold germ_post_A. exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m', st', r, err', hack', pos', entp', cl, ev'.
    split; [reflexivity|].
    split; [unfold germ_WA; rewrite <- (hvs_of_W ns hs LEN); exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split. { eapply (fkeep_weaken FI _ (germ_WA FI AI P hs) st st m m' FK); [| intros g Hg; exact Hg].
             intros x Ho. unfold germ_WA in Ho. cbn [outside] in Ho |- *. destruct Ho as (O1 & O2 & O3 & _). split; [exact O1|]. split; [exact O2|]. split; [exact O3| exact I]. }
    split; [exact LIVE|]. split; [exact RF'|]. split; [exact ST'|]. split; [exact AE'|].
    split; [exact PE'|]. split; [unfold p_ctl, p_ctl_cells; split; [exact PCn|]; clear - B1 B2 B3 B4 CLR R_csz CURB; lia|].
    split; [exact PHL'|]. split; [split; [exact CE'| split; [exact CG'| exact CC']]|]. split; [exact IWC'| exact CS]. }
  destruct CASES as [(-> & -> & -> & -> & -> & _) | [(-> & -> & EN & -> & ->) | (-> & -> & -> & -> & HK & _)]].
  - apply (FIN err hack 4 entp); first [reflexivity | lia].
  - destruct EN as [-> | [-> | ->]]; [apply (FIN err hack pos 2)| apply (FIN err hack pos 3)| apply (FIN err hack pos 4)]; first [reflexivity | lia].
  - destruct HK as [-> | ->]; [apply (FIN 411 hack pos entp)| apply (FIN 411 1 pos entp)]; first [reflexivity | lia].
Qed.

End W.

