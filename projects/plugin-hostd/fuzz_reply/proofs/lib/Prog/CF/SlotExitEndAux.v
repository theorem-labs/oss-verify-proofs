From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
  YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09
  YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import
  Img0 Contract FrameAPI SlotKept SlotPack AllocPack AllocPack3 SlotPack3 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import source_reset_c check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c op_add_c SlotInv SlotSteps SlotRes SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessGlue HarnessFrame SlotEntryRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require SlotPass0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ea_c8 : forall segs m a v, rw_cells segs m a [C8 v] -> bytes_at segs m a (le8 v).
Proof. intros segs m a v [[_ X] _]. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. Qed.

Lemma ea_c1 : forall m a b, rw_cells rsegs m a [C1 b] -> mbyte rsegs m a = Some b.
Proof.
  intros m a b [[_ (_ & _ & X)] _]. pose proof (X 0%nat ltac:(cbn; lia)) as Y.
  rewrite Z.add_0_r in Y. exact Y.
Qed.

Lemma ea_outv : forall segs m a b c d, rw_cells segs m G_OUTV [C8 a; C8 b; C8 c; C8 d] ->
  bytes_at segs m 0x31000 (le8 b) /\ bytes_at segs m 0x31008 (le8 c) /\ bytes_at segs m 0x31010 (le8 d).
Proof.
  intros segs m a b c d H.
  destruct (hg_cut _ _ _ [C8 a] [C8 b; C8 c; C8 d] H) as [_ H1].
  destruct (hg_cut _ _ _ [C8 b] [C8 c; C8 d] H1) as [H2 H3].
  destruct (hg_cut _ _ _ [C8 c] [C8 d] H3) as [H4 H5].
  split; [exact (ea_c8 _ _ _ _ H2)|]. split; [exact (ea_c8 _ _ _ _ H4)|exact (ea_c8 _ _ _ _ H5)].
Qed.

Lemma ea_wN8 : forall m a w, bytes_at rsegs m a (le8 w) -> wN_at m a (bv_unsigned w) 8.
Proof. intros m a w H. exact (KindBGlue.bytes_at_le8_word rsegs m a w H). Qed.

Lemma ea_nth : forall (bs : list byte) k (b : byte), (k < length bs)%nat ->
  bv_unsigned (nth k bs (Z_to_bv 8 0)) = bv_unsigned b -> nth_error bs k = Some b.
Proof.
  intros bs k b Hk H. rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hk). f_equal. apply bv_eq. exact H.
Qed.

Lemma ea_w16 : forall m a, rw_cells rsegs m a [C4 (Z_to_bv 64 16)] -> wN_at m a 16 4.
Proof.
  intros m a [[_ (_ & _ & X)] _] k Hk.
  etransitivity; [exact (X k ltac:(cbn; lia))|].
  apply ea_nth; [cbn; lia|].
  destruct k as [|[|[|[|k]]]]; [vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|
    vm_compute; reflexivity|lia].
Qed.

Lemma ea_byte_at : forall m a bs v, bytes_at rsegs m a bs -> 0 <= v < 256 ->
  forallb (fun b => bv_unsigned b =? v) bs = true -> byte_at m a v (Z.of_nat (length bs)).
Proof.
  intros m a bs v (H0 & H1 & H) Hv HF i Hi.
  pose proof (H (Z.to_nat i) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  rewrite forallb_forall in HF. pose proof (HF b (nth_error_In _ _ Eb)) as Y. apply Z.eqb_eq in Y.
  transitivity (Some b); [exact X|]. f_equal. apply bv_eq. rewrite Y, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma ea_img_sink : forall B, ms_segs B = rsegs -> forall a, 0x51520 <= a < 0x51958 -> in_img B a.
Proof.
  intros B SEG a HA.
  assert (C : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x51520) &&
      (0x51958 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in C as (s & HS & HB). apply andb_prop in HB as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  unfold in_img. rewrite SEG. split; [intros EQ; rewrite EQ in HS; destruct HS|].
  exists s. split; [exact HS|lia].
Qed.

Lemma ea_T : forall B E TA L0 A0 (m0 : word -> option byte) (t : Z * Z),
  driver_kept B E TA L0 A0 m0 -> 0 < snd t ->
  (In (fst t) TA \/ (forall q m, In (q, m) (blocks L0 A0) -> 0 < m -> ~ In q TA -> q <> fst t)) ->
  In t (blocks (ss_L E) (ss_A E)) -> In t (ss_T E).
Proof.
  intros B E TA L0 A0 m0 [a n] (DK1 & _) Hn HC Hin. cbn [fst snd] in *.
  assert (D : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
  destruct (in_dec D (a, n) (ss_T E)) as [Y|N]; [exact Y|exfalso].
  unfold blocks in Hin. apply in_map_iff in Hin as ([q n'] & EQ & Hq). cbn [fst snd] in EQ.
  injection EQ as Ea En. subst n'.
  rewrite <- Ea in N. destruct (DK1 q n Hq N) as (NT & q' & Hq' & EQ').
  destruct HC as [HC|HC].
  - apply (NT Hn). rewrite Ea. exact HC.
  - apply (HC (ptr_addr L0 q') n).
    + exact (in_map (fun b => (ptr_addr L0 (fst b), snd b)) _ (q', n) Hq').
    + exact Hn.
    + rewrite EQ'. exact (NT Hn).
    + rewrite EQ'. exact Ea.
Qed.

Lemma ea_GI : forall j m (gw nw cw ow mx : word) br gn dd ei,
  rw_cells rsegs m G_LISTEN [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] ->
  rw_cells rsegs m G_WAKE0 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] ->
  rw_cells rsegs m G_THREAD_UP [C1 (Z_to_bv 8 0)] ->
  rw_cells rsegs m G_NSRC [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16)] ->
  rw_cells rsegs m G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (G_LOCK + 12) [CB 28 (nulbytes 28)] ->
  (forall i, (i < 4)%nat -> rw_cells rsegs m (G_S + SRC_SIZE * Z.of_nat i) [CB 96%nat (nulbytes 96)]) ->
  rw_cells rsegs m G_BROKEN [C1 (Z_to_bv 8 br)] -> rw_cells rsegs m G_GONE [C1 (Z_to_bv 8 gn)] ->
  rw_cells rsegs m G_DEAD [C1 (Z_to_bv 8 dd)] -> rw_cells rsegs m G_EINTR [C1 (Z_to_bv 8 ei)] ->
  (br = 0 \/ br = 1) -> (gn = 0 \/ gn = 1) -> (dd = 0 \/ dd = 1) -> (ei = 0 \/ ei = 1) ->
  rw_cells rsegs m G_SRC [C8 gw] -> rw_cells rsegs m G_OUTV [C8 mx; C8 nw; C8 cw; C8 ow] ->
  bv_unsigned nw <= bv_unsigned cw -> bv_unsigned cw <= TBBYTES -> (bv_unsigned cw = 0 -> bv_unsigned ow = 0) ->
  GI_t (S j) (kept_blocks 16 (bv_unsigned gw) (bv_unsigned cw) (bv_unsigned ow)) m.
Proof.
  intros j m gw nw cw ow mx br gn dd ei HL HW HT HN HK HK2 HZ HB HG HD HE B01 G01 D01 E01 HS HO NC HCB CZ.
  assert (BY : forall a cs, rw_cells rsegs m a cs -> bytes_at rsegs m a (cells_bytes cs))
    by (intros a cs [[_ X] _]; exact X).
  split; [|split].
  - unfold GI_reply. split; [|split; [|split; [|split]]].
    + assert (X : bytes_at rsegs m G_DATA (cells_bytes [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] ++
                                            cells_bytes [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))])).
      { apply bytes_at_app. split; [exact (BY _ _ HL)|].
        assert (E8 : G_DATA + Z.of_nat (length (cells_bytes [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))])) = G_WAKE0)
          by (vm_compute; reflexivity).
        rewrite E8. exact (BY _ _ HW). }
      exact (ea_byte_at m G_DATA _ 255 X ltac:(lia) ltac:(vm_compute; reflexivity)).
    + exact (ea_byte_at m G_THREAD_UP _ 0 (BY _ _ HT) ltac:(lia) ltac:(vm_compute; reflexivity)).
    + destruct (hg_cut _ _ _ [C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 16)] HN) as [X _].
      exact (ea_byte_at m G_NSRC _ 0 (BY _ _ X) ltac:(lia) ltac:(vm_compute; reflexivity)).
    + assert (X : bytes_at rsegs m G_LOCK
          (cells_bytes [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ cells_bytes [CB 28 (nulbytes 28)])).
      { apply bytes_at_app. split; [exact (BY _ _ HK)|].
        assert (E12 : G_LOCK + Z.of_nat (length (cells_bytes [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]))
                      = G_LOCK + 12) by (vm_compute; reflexivity).
        rewrite E12. exact (BY _ _ HK2). }
      exact (ea_byte_at m G_LOCK _ 0 X ltac:(lia) ltac:(vm_compute; reflexivity)).
    + intros x Hx. set (i := Z.to_nat (x / 96)).
      assert (Hi : (i < 4)%nat) by (unfold i; Z.div_mod_to_equations; lia).
      assert (Hix : SRC_SIZE * Z.of_nat i <= x < SRC_SIZE * Z.of_nat i + 96).
      { unfold i, SRC_SIZE. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
      pose proof (ea_byte_at m _ _ 0 (BY _ _ (HZ i Hi)) ltac:(lia) ltac:(vm_compute; reflexivity)) as Y.
      specialize (Y (x - SRC_SIZE * Z.of_nat i)).
      replace (G_S + SRC_SIZE * Z.of_nat i + (x - SRC_SIZE * Z.of_nat i)) with (G_S + x) in Y by lia.
      apply Y. cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold nulbytes. rewrite repeat_length. lia.
  - intros a Ha. unfold G_FLAGS in Ha. unfold flag_ok.
    pose proof (ea_c1 _ _ _ HB) as XB. pose proof (ea_c1 _ _ _ HG) as XG.
    pose proof (ea_c1 _ _ _ HD) as XD. pose proof (ea_c1 _ _ _ HE) as XE.
    unfold G_BROKEN, G_GONE, G_DEAD, G_EINTR in XB, XG, XD, XE.
    destruct Ha as [<-|[<-|[<-|[<-|[]]]]].
    + rewrite XB. destruct B01 as [->| ->]; [left|right]; reflexivity.
    + rewrite XG. destruct G01 as [->| ->]; [left|right]; reflexivity.
    + rewrite XD. destruct D01 as [->| ->]; [left|right]; reflexivity.
    + rewrite XE. destruct E01 as [->| ->]; [left|right]; reflexivity.
  - destruct (ea_outv _ _ _ _ _ _ HO) as (O1 & O2 & O3).
    exists 16, (bv_unsigned gw), (bv_unsigned nw), (bv_unsigned cw), (bv_unsigned ow).
    destruct (hg_cut _ _ _ [C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 16)] HN) as [_ X].
    split; [exact (ea_w16 _ _ X)|].
    split; [exact (ea_wN8 _ _ _ (ea_c8 _ _ _ _ HS))|].
    split; [exact (ea_wN8 _ _ _ O1)|]. split; [exact (ea_wN8 _ _ _ O2)|]. split; [exact (ea_wN8 _ _ _ O3)|].
    pose proof (bv_unsigned_in_range 64 nw) as R. unfold bv_modulus in R.
    split; [right; reflexivity|]. split; [lia|]. split; [split; [exact CZ|intros X0; discriminate X0]|].
    reflexivity.
Qed.

Lemma ea_post : forall CS B API LS SH SK ra empty rc fx j E TA L0 A0 m0 md0 (Ee Ff : Z -> Prop) L A regs' m md T',
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  aa_MR (API rc) L0 A0 m0 md0 -> (exists vm, md0 = with_vmmaps vm (ss_md E)) ->
  image_kept (rc := rc) B E m0 -> driver_kept B E TA L0 A0 m0 ->
  rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) Ee Ff L0 A0 m0 md0 L A m md ->
  (forall a, Ee a -> in_globals G_reply a \/ exists q n, In (q, n) (blocks L0 A0) /\ In q TA /\ q <= a < q + n) ->
  (forall q, Ff q -> In q TA) ->
  st_init_done A = true -> ro_agree (ms_segs B) m ->
  YK11.getr regs' (Z_to_bv 5 10) = Z_to_bv 64 0 -> regs_preserved (ss_regs E) regs' ->
  res_ok_pack3 A (PB3 (pb_live (TDP (ss_T E) T' (pb_of3 (ss_b E)))) (pb_bytes (TDP (ss_T E) T' (pb_of3 (ss_b E))))
    (CS (ss_pl E)) [] frame_MCAP) ->
  tb_live L A T' ->
  (forall t, In t T' -> In t (blocks (ss_L E) (ss_A E)) -> In t (ss_T E)) ->
  lib_post_p3 (rc := rc) (SH := SH) (SK := SK) B (API rc) (CS (ss_pl E)) frame_MCAP G_reply SLOT_STACK (ss_L E) (ss_A E)
    (ss_regs E) (ss_mem E) (ss_md E) (ss_p E) (ss_n E) (ss_b E) (LL 0 (m_fs (ss_md E)) []) (ss_T E) T'
    L A regs' m md.
Proof.
  intros CS B API LS SH SK ra empty rc fx j E TA L0 A0 m0 md0 Ee Ff L A regs' m md T'
    (FF & _ & HP & _) HM0 (vm & HVM) (IK1 & IK2 & IK3 & IK4) (DK1 & DK2 & DK3 & DK4) RM HEC HFC INIT RO R10 PRS
    RES TBL TIN.
  destruct HP as (PRE & _ & _ & _ & _ & _ & NI & _ & _ & _ & _).
  destruct PRE as (PRE & _ & _ & SINK & _ & FS & _ & _).
  destruct PRE as (HM & HW & _ & _ & _ & _ & SPLO & _ & _ & _ & _ & _ & _ & INPUT & _).
  pose proof (proj1 FF) as SEG.
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL rc fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (FG : forall a, in_globals G_reply a -> img_plain B a) by (unfold frame_facts, img_plain, G_reply in *; tauto).
  pose proof RM as (M1 & W1 & B1 & _ & _ & PA & SV & Z0 & _ & MD & BY & BK & SC).
  pose proof (aa_laws (API rc)) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as AC.
  assert (BLK0 : forall q n, In (q, n) (user_blocks A0) -> In (ptr_addr L0 q, n) (blocks L0 A0))
    by (intros q n H; exact (in_map (fun b => (ptr_addr L0 (fst b), snd b)) _ (q, n) H)).
  assert (NEimg : forall a, in_img B a -> ~ in_globals G_reply a -> ~ Ee a).
  { intros a Ha NG X. destruct (HEC a X) as [Y|(q & n & Hq & _ & Hr)]; [exact (NG Y)|].
    apply (hf_blk_img B (API rc) AX L0 A0 m0 md0 q n (a - q) HM0 Hq ltac:(lia)).
    replace (q + (a - q)) with a by lia. exact Ha. }
  assert (NEhi : forall a, YM05.alloc_ceiling <= a -> ~ Ee a).
  { intros a Ha X. destruct (HEC a X) as [Y|(q & n & Hq & _ & Hr)].
    - pose proof (hg_img_low B SEG a (proj1 (FG a Y))). lia.
    - pose proof (block_facts B (aa_MR (API rc)) LAWS _ _ _ _ q n (a - q) HM0 Hq ltac:(lia)) as (_ & _ & X2 & _).
      lia. }
  assert (NEblk : forall q' n i, In (q', n) (user_blocks A0) -> ~ In (ptr_addr L0 q') TA -> 0 <= i < n ->
      ~ Ee (ptr_addr L0 q' + i)).
  { intros q' n i Hq' NT Hi X. destruct (HEC _ X) as [Y|(q2 & n2 & Hq2 & T2 & Hr)].
    - apply (hf_blk_img B (API rc) AX L0 A0 m0 md0 _ n i HM0 (BLK0 q' n Hq') Hi). exact (proj1 (FG _ Y)).
    - assert (NEQ : q2 <> ptr_addr L0 q') by (intros EQ; apply NT; rewrite <- EQ; exact T2).
      destruct (blocks_disjoint B (API rc) L0 A0 m0 md0 q2 n2 (ptr_addr L0 q') n HM0 Hq2 (BLK0 q' n Hq') NEQ);
        lia. }
  assert (NFblk : forall q', ~ In (ptr_addr L0 q') TA -> ~ Ff (ptr_addr L0 q')).
  { intros q' NT X. exact (NT (HFC _ X)). }
  assert (IMGC : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
      ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G_reply a ->
      mbyte (ms_segs B) m a = mbyte (ms_segs B) (ss_mem E) a /\
      (writable_at (ms_segs B) (ss_mem E) a <-> writable_at (ms_segs B) m a)).
  { intros a HA H1 H2 H3 H4.
    destruct (rmid_img B (API rc) AX SLOT_STACK (spZ (ss_regs E)) Ee Ff L0 A0 m0 md0 L A m md a (hg_img_low B SEG)
      ltac:(lia) HM0 RM (conj HA (conj H1 (conj H2 H3))) (NEimg a HA H4)) as [X Y].
    destruct (IK1 a HA H1 H2 H3 H4) as [X0 Y0]. split; [congruence|tauto]. }
  unfold lib_post_p3.
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact INIT|].
  split; [exact R10|]. split; [exact PRS|].
  split.
  { destruct MD as (vm' & ->). subst md0. exists vm', (m_fds (ss_md E)), (m_statpins (ss_md E)).
    split; [rewrite YI04.with_vmmaps_twice, with_vmmaps_os_upd; reflexivity|intros; reflexivity]. }
  split.
  { intros q n Hq HT. destruct (DK1 q n Hq HT) as (NT & q' & Hq' & EQ).
    pose proof (CF.SlotPass0.p0_ub_nonneg _ _ _ HW Hq) as Hn0.
    destruct (Z.eq_dec n 0) as [->|Hn].
    - destruct (Z0 q' Hq') as (Hq'' & EQ'). exists q'. split; [exact Hq''|congruence].
    - assert (NT' : ~ In (ptr_addr L0 q') TA) by (rewrite EQ; apply NT; lia).
      pose proof (SV q' n Hq' ltac:(lia) (NFblk q' NT')) as Hq''.
      exists q'. split; [exact Hq''|]. rewrite (PA q' n Hq' Hq'' (NFblk q' NT')). exact EQ. }
  split.
  { intros a HA NS.
    assert (NO0 : ~ owned B L0 A0 a) by (intro X; pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM0 X); lia).
    assert (NO1 : ~ owned B L A a) by (intro X; pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M1 X); lia).
    destruct (BY a (or_introl HA) NO0 NO1 NS (NEhi a (proj1 HA))) as [X Y].
    destruct (IK3 a HA NS) as [X0 Y0]. split; [congruence|tauto]. }
  split; [exact IMGC|].
  split.
  { intros a HA. rewrite SEG. split; intros _; exact (proj1 (entry_global_access _ a HA)). }
  split.
  { intros q n i Hq HT HNP Hi. destruct (DK1 q n Hq HT) as (NT & q' & Hq' & EQ).
    assert (NT' : ~ In (ptr_addr L0 q') TA) by (rewrite EQ; apply NT; lia).
    pose proof (SV q' n Hq' ltac:(lia) (NFblk q' NT')) as Hq''.
    rewrite <- EQ. rewrite (BK q' n i Hq' Hq'' (NFblk q' NT') Hi (NEblk q' n i Hq' NT' Hi)).
    rewrite EQ. exact (DK2 q n i Hq HT HNP Hi). }
  split; [intros a HA; exact (SC a HA)|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact FS|].
  split.
  { destruct SINK as ((S1 & S2) & S3 & S4).
    assert (SK3 : @sk_threaded SK = 0x51520 + 1) by (unfold frame_facts in FF; tauto).
    assert (SK2 : @sk_ofl_lock SK = 0x51948) by (unfold frame_facts in FF; tauto).
    assert (SK1 : @sk_ofl_head SH = 0x51950) by (unfold frame_facts in FF; tauto).
    assert (EDB : ms_debruijn B = 0x104e0) by (unfold frame_facts in FF; tauto).
    assert (ELK : ms_lock B = 0x51590) by (unfold frame_facts in FF; tauto).
    assert (ELC : ms_libc B = 0x51520) by (unfold frame_facts in FF; tauto).
    assert (EGG : ms_got_guard B = 0x1fcf8) by (unfold frame_facts in FF; tauto).
    assert (EGD : ms_guard B = 0x51500) by (unfold frame_facts in FF; tauto).
    assert (ESC : ms_size_classes B = 0x10500) by (unfold frame_facts in FF; tauto).
    assert (ESM : ms_small_cnt B = 0x10560) by (unfold frame_facts in FF; tauto).
    assert (EMD : ms_med_cnt B = 0x1057b) by (unfold frame_facts in FF; tauto).
    assert (EVM : ms_vmlock B = Some 0x51d74) by (unfold frame_facts in FF; tauto).
    assert (ECX : ms_ctx B = 0x51598) by (unfold frame_facts in FF; tauto).
    assert (ETP : ms_tp B = 0x31290) by (unfold frame_facts in FF; tauto).
    assert (EOF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
    assert (VL : vml_lo B = 0x51d74 /\ vml_len B = 4) by (unfold vml_lo, vml_len; rewrite EVM; split; reflexivity).
    assert (SNK : forall a, (a = 0x51521 \/ 0x51948 <= a < 0x5194c \/ 0x51950 <= a < 0x51958) ->
        mbyte (ms_segs B) m a = mbyte (ms_segs B) (ss_mem E) a).
    { intros a Ha.
      destruct (Z_lt_le_dec a (ms_debruijn B + Z.max 32 (ms_debruijn_len B))) as [D|D].
      - rewrite (ax_tables AX L A m md a M1 ltac:(left; rewrite EDB in *; lia)).
        rewrite (ax_tables AX (ss_L E) (ss_A E) (ss_mem E) (ss_md E) a HM ltac:(left; rewrite EDB in *; lia)).
        reflexivity.
      - assert (NS : ~ static_owned B a).
        { unfold static_owned. destruct VL as [V1 V2].
          rewrite ELK, ELC, EGG, EGD, ESC, ESM, EMD, V1, V2. lia. }
        refine (proj1 (IMGC a (ea_img_sink B SEG a ltac:(lia)) NS _ _ _)).
        + rewrite ECX. unfold CTX_SIZE. lia.
        + unfold errno_addr. rewrite ETP, EOF. lia.
        + intros (lo & len & [EQ|[EQ|[]]] & HX); injection EQ as <- <-; lia. }
    assert (FDS : forall v x, m_fds (with_vmmaps v x) = m_fds x) by (intros v x; destruct x; reflexivity).
    split; [split|split].
    - eapply val_mem_frame; [|exact S1]. intros x Hx. apply SNK. rewrite SK3 in Hx. cbn in Hx. lia.
    - eapply val_mem_frame; [|exact S2]. intros x Hx. apply SNK. rewrite SK2 in Hx. cbn in Hx. lia.
    - apply val_mem_word_mem. apply val_mem_word_mem in S3. eapply val_mem_frame; [|exact S3].
      intros x Hx. apply SNK. rewrite SK1 in Hx. cbn in Hx. lia.
    - destruct MD as (vm' & ->). subst md0. rewrite !FDS. exact S4. }
  split; [exact RO|]. split; [exact RES|].
  split.
  { intros i Hi. destruct INPUT as [[NZ _]|(NP & q & HQ & QE)]; [lia|].
    assert (HT : ~ In (ptr_addr (ss_L E) q, ss_n E) (ss_T E)) by (rewrite QE; exact (NI NP)).
    destruct (DK1 q (ss_n E) HQ HT) as (NT & q' & Hq' & EQ).
    assert (NT' : ~ In (ptr_addr L0 q') TA) by (rewrite EQ; apply NT; lia).
    pose proof (SV q' _ Hq' NP (NFblk q' NT')) as Hq''.
    rewrite <- QE, <- EQ. rewrite (BK q' _ i Hq' Hq'' (NFblk q' NT') Hi (NEblk q' _ i Hq' NT' Hi)).
    rewrite EQ, QE. exact (DK3 i Hi). }
  split; [exact TBL|exact TIN].
Qed.
