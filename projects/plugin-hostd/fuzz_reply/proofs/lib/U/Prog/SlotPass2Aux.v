(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1247 of its 1329 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/drain_b_seg.v; 265 of its 301 lines of code are new or changed and 1293 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass2Run.v, with its module names changed; 1051 of its 1087 lines of code are new or changed and 265 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require MemNorm RoAdapt AllocBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead
  SlotHeadP SlotRes KindB HarnessGlue HarnessFrame SlotReads SlotEntryRun SlotEntry.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotHeadRun SlotHeadPick SlotHeadQ SlotHeadQD SlotPass1
  pthread_mutex_lock_c pthread_mutex_unlock_c pthread_mutex_lock_ro_c pthread_mutex_unlock_ro_c pthread_mutex_lock_ro
  pthread_mutex_unlock_ro SlotPass9G SlotPass2Run check_no_loss_read_c check_no_loss_c check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require RelayCap relay_remove_b_aux.
Import ListNotations.
Local Open Scope Z_scope.

Lemma p2_ff : forall B API LS SH SK ra empty rc fx j E CS,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  ms_segs B = rsegs /\ errno_addr B = 0x31acc /\ ms_tp B = 0x31b70 /\
  @frame_allocator rc fx B (API rc) /\
  (forall a, in_globals G_reply a -> img_plain B a) /\
  @YM05.alloc_ceiling rc + SLOT_STACK <= spZ (ss_regs E) /\ spZ (ss_regs E) < 2 ^ 63 /\
  spZ (ss_regs E) mod 16 = 0 /\ getr (ss_regs E) 4 = Z_to_bv 64 (ms_tp B) /\
  aa_MR (API rc) (ss_L E) (ss_A E) (ss_mem E) (ss_md E) /\
  ((ss_n E = 0 /\ ss_p E = empty) \/ (0 < ss_n E /\ exists q, In (q, ss_n E) (user_blocks (ss_A E)) /\
     ptr_addr (ss_L E) q = ss_p E)) /\
  (0 < ss_n E -> ~ In (ss_p E, ss_n E) (ss_T E)).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS (FF & _ & HP & _).
  destruct HP as (PRE & _ & _ & _ & _ & _ & NI & _).
  destruct PRE as (PRE & _).
  destruct PRE as (HM & HW & HB & INIT & RA & ALIGN & SPLO & SPHI & WST & TP & WERR & RP & RN & INPUT & ROD).
  assert (SEG : ms_segs B = rsegs) by (unfold frame_facts in FF; tauto).
  assert (ETP : ms_tp B = 0x31b70) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  split; [exact SEG|]. split; [unfold errno_addr; rewrite ETP, EOFF; reflexivity|]. split; [exact ETP|].
  split; [assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto);
    exact (ALL rc fx)|].
  split; [unfold frame_facts, G_reply, img_plain in *; tauto|].
  split; [exact SPLO|]. split; [exact SPHI|]. split; [exact ALIGN|]. split; [exact TP|]. split; [exact HM|].
  split; [exact INPUT|exact NI].
Qed.

Lemma p2_in_blocks : forall (L : layout) (A : astate) p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof. intros L A p n H. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) H). Qed.

Lemma p2_blk : forall rc fx B (API : AllocAPI B) L A mem md q m i,
  @frame_allocator rc fx B API -> aa_MR API L A mem md -> In (q, m) (blocks L A) -> 0 <= i < m ->
  ~ in_img B (q + i) /\ 4096 <= q /\ q + m <= @YM05.alloc_ceiling rc.
Proof.
  intros rc fx B API L A mem md q m i FA HM Hin Hi.
  assert (AX : AllocExtra B (aa_MR API)) by (unfold frame_allocator in FA; tauto).
  unfold blocks in Hin. apply in_map_iff in Hin as ([p k] & EQ & Hp). cbn [fst snd] in EQ. injection EQ as <- <-.
  destruct (mr_blocks _ _ (aa_laws API) L A mem md p k i HM Hp Hi) as (_ & B0 & B1 & _).
  split; [exact (ax_blocks_img AX L A mem md p k i HM Hp Hi)|]. split; assumption.
Qed.

Definition p2_es {rc : RunCeil} (B : malloc_syms) (sp : Z) (TA : list Z) (L : layout) (A : astate) (a : Z) : Prop :=
  in_globals G_reply a \/ (sp + 16 <= a < sp + 88) \/
  (0 <= a < @YM05.alloc_ceiling rc /\ ~ in_img B a /\
   forall x m, In (x, m) (blocks L A) -> ~ In x TA -> a < x \/ x + m <= a).

Lemma p2_es_blk : forall rc fx B (API : AllocAPI B) sp TA L A mem md q m a,
  @frame_allocator rc fx B API -> aa_MR API L A mem md -> In (q, m) (blocks L A) -> In q TA -> q <= a < q + m ->
  p2_es (rc := rc) B sp TA L A a.
Proof.
  intros rc fx B API sp TA L A mem md q m a FA HM Hq HT Ha.
  destruct (p2_blk rc fx B API L A mem md q m (a - q) FA HM Hq ltac:(lia)) as (NI & B0 & B1).
  replace (q + (a - q)) with a in NI by lia. right. right. split; [lia|]. split; [exact NI|].
  intros x m' Hx NT. assert (NE : q <> x) by (intros <-; exact (NT HT)).
  destruct (blocks_disjoint B API L A mem md q m x m' HM Hq Hx NE); lia.
Qed.

Lemma p2_kept : forall B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' Es Fs TA TA',
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  aa_MR (API rc) L A mem md -> WF A ->
  image_kept (rc := rc) B E mem -> stack_mid B E mem -> driver_kept B E TA L A mem ->
  rmid B (API rc) (SLOT_STACK - SLOT_FRAME) (slot_sp E) Es Fs L A mem md L' A' mem' md' ->
  (forall a, Es a -> p2_es (rc := rc) B (slot_sp E) TA L A a) ->
  (forall a, slot_sp E <= a < spZ (ss_regs E) -> ~ Es a \/ writable_at (ms_segs B) mem' a) ->
  (forall q, Fs q -> forall x m, In (x, m) (blocks L A) -> 0 < m -> ~ In x TA -> q <> x) ->
  (forall x, In x TA' -> In x TA \/ (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q TA -> q <> x)) ->
  (forall q m, In (q, m) (blocks L' A') -> (In (q, m) (blocks L A) /\ ~ In q TA) \/ In q TA') ->
  image_kept (rc := rc) B E mem' /\ stack_mid B E mem' /\ driver_kept B E TA' L' A' mem'.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' Es Fs TA TA' HF HM HWF HIK HST HDK RM
    HES HWR HFS HTA HB4.
  destruct (p2_ff B API LS SH SK ra empty rc fx j E CS HF)
    as (SEG & ERR & ETP & FA & PL & SPLO & SPHI & ALIGN & TP & MR0 & PIN & NI).
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (HIMG : forall x, in_img B x -> 0 <= x < @YM05.alloc_ceiling rc) by exact (hg_img_low B SEG).
  assert (HK : @YM05.alloc_ceiling rc <= slot_sp E - (SLOT_STACK - SLOT_FRAME))
    by (unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
  pose proof RM as (M1 & W1 & B1 & LY1 & LN1 & PA1 & SV1 & Z01 & OW1 & MD1 & BY1 & BK1 & SC1).
  assert (GIMG : forall a, in_globals G_reply a -> 0 <= a < 2 ^ 21).
  { intros a HG. destruct (PL a HG) as (HI & _). exact (in_img_low B SEG a HI). }
  assert (NES_IMG : forall a, in_img B a -> ~ in_globals G_reply a -> ~ Es a).
  { intros a HI NG HE. destruct (HES a HE) as [X|[X|(_ & X & _)]]; [exact (NG X)| |exact (X HI)].
    pose proof (in_img_low B SEG a HI). unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (NES_HI : forall a, @YM05.alloc_ceiling rc <= a -> Es a -> slot_sp E + 16 <= a < slot_sp E + 88).
  { intros a Ha HE. destruct (HES a HE) as [X|[X|(X & _)]]; [pose proof (GIMG a X); lia|exact X|lia]. }
  assert (BKP : forall x m, In (x, m) (blocks L A) -> ~ In x TA -> 0 < m ->
    (exists q', In (q', m) (user_blocks A) /\ ptr_addr L q' = x) ->
    In (x, m) (blocks L' A') /\ forall i, 0 <= i < m -> mbyte (ms_segs B) mem' (x + i) = mbyte (ms_segs B) mem (x + i)).
  { intros x m Hx NT Hm (q' & HQ & EQ).
    assert (NF : ~ Fs (ptr_addr L q')) by (rewrite EQ; intros X; exact (HFS _ X x m Hx Hm NT eq_refl)).
    pose proof (SV1 q' m HQ Hm NF) as HQ'. pose proof (PA1 q' m HQ HQ' NF) as EA.
    split; [rewrite <- EQ, <- EA; exact (p2_in_blocks L' A' q' m HQ')|].
    intros i Hi. rewrite <- EQ. apply (BK1 q' m i HQ HQ' NF Hi). rewrite EQ. intros HE.
    destruct (HES _ HE) as [X|[X|(_ & _ & X)]].
    - destruct (PL _ X) as (HI & _).
      exact (proj1 (p2_blk rc fx B (API rc) L A mem md x m i FA HM Hx Hi) HI).
    - destruct (p2_blk rc fx B (API rc) L A mem md x m i FA HM Hx Hi) as (_ & _ & X2).
      unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - destruct (X x m Hx NT); lia. }
  assert (STK : forall a cs, rw_cells (ms_segs B) mem a cs -> slot_sp E <= a ->
    a + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
    (a + Z.of_nat (cells_size cs) <= slot_sp E + 16 \/ slot_sp E + 88 <= a) -> rw_cells (ms_segs B) mem' a cs).
  { intros a cs H Ha Hb D.
    apply (rmid_rw_hi B (API rc) (SLOT_STACK - SLOT_FRAME) (slot_sp E) Es Fs L A mem md L' A' mem' md' a cs);
      try assumption.
    - unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - rewrite ERR. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - intros i Hi HE. pose proof (NES_HI (a + i) ltac:(unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia) HE). lia. }
  split.
  { destruct HIK as (I1 & I2 & I3 & I4). split; [|split; [|split]].
    - intros a HI HS HC HE HG. destruct (I1 a HI HS HC HE HG) as [EQA WQA].
      destruct (rmid_img B (API rc) AX _ _ _ _ _ _ _ _ _ _ _ _ a HIMG HK HM RM
        (conj HI (conj HS (conj HC HE))) (NES_IMG a HI HG)) as [EQB WQB].
      split; [congruence|tauto].
    - intros a HG. rewrite SEG. split; intros _; exact (proj1 (entry_global_access _ a HG)).
    - intros a HA HNS. destruct (I3 a HA HNS) as [EQA WQA].
      destruct (BY1 a (or_introl HA)) as [EQB WQB].
      + intros HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HM HO). lia.
      + intros HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a M1 HO). lia.
      + unfold sk. intros [X|X]; apply HNS; unfold lib_scratch;
          [left; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|right; exact X].
      + intros X. pose proof (NES_HI a ltac:(lia) X). apply HNS. unfold lib_scratch.
        left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
      + split; [congruence|tauto].
    - intros a HL.
      assert (D : sk B (SLOT_STACK - SLOT_FRAME) (slot_sp E) a \/ ~ sk B (SLOT_STACK - SLOT_FRAME) (slot_sp E) a)
        by (unfold sk; lia).
      destruct D as [S|NS]; [apply SC1; exact S|].
      assert (HA : slot_sp E <= a < spZ (ss_regs E)).
      { unfold lib_scratch in HL. unfold sk in NS. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
      destruct (HWR a HA) as [NE|W]; [|exact W].
      destruct (BY1 a) as [_ WQB].
      + left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
      + intros HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HM HO).
        unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
      + intros HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a M1 HO).
        unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
      + exact NS.
      + exact NE.
      + apply WQB. exact (I4 a HL). }
  split.
  { destruct HST as (S1 & S2 & S3). unfold stack_mid.
    split; [apply STK; [exact S1|lia|cbn; unfold slot_sp, SLOT_FRAME in *; lia|right; lia]|].
    split; [apply STK; [exact S2|lia|cbn; unfold slot_sp, SLOT_FRAME in *; lia|left; cbn; lia]|].
    apply STK; [exact S3|lia|cbn; unfold slot_sp, SLOT_FRAME in *; lia|left; cbn; lia]. }
  destruct HDK as (D1 & D2 & D3 & D4). split; [|split; [|split]].
  - intros q m HU HNT. destruct (D1 q m HU HNT) as (N1 & q1 & HQ1 & EQ1). split.
    + intros Hm HX. destruct (HTA _ HX) as [X|X]; [exact (N1 Hm X)|].
      apply (X (ptr_addr (ss_L E) q) m); [rewrite <- EQ1; exact (p2_in_blocks L A q1 m HQ1)|exact Hm|exact (N1 Hm)|reflexivity].
    + destruct (Z.eq_dec m 0) as [->|Hm0].
      * destruct (Z01 q1 HQ1) as (HQ1' & EA). exists q1. split; [exact HQ1'|congruence].
      * pose proof (entry_ub_nonneg A q1 m HWF HQ1). assert (Hm : 0 < m) by lia.
        assert (NF : ~ Fs (ptr_addr L q1)) by (intros X; exact (HFS _ X (ptr_addr L q1) m (p2_in_blocks L A q1 m HQ1)
          Hm ltac:(rewrite EQ1; exact (N1 Hm)) eq_refl)).
        pose proof (SV1 q1 m HQ1 Hm NF) as HQ1'. exists q1. split; [exact HQ1'|].
        rewrite (PA1 q1 m HQ1 HQ1' NF). exact EQ1.
  - intros q m i HU HNT HNP Hi. rewrite <- (D2 q m i HU HNT HNP Hi).
    destruct (D1 q m HU HNT) as (N1 & q1 & HQ1 & EQ1). assert (Hm : 0 < m) by lia.
    exact (proj2 (BKP (ptr_addr (ss_L E) q) m ltac:(rewrite <- EQ1; exact (p2_in_blocks L A q1 m HQ1)) (N1 Hm) Hm
      (ex_intro _ q1 (conj HQ1 EQ1))) i Hi).
  - intros i Hi. rewrite <- (D3 i Hi).
    destruct PIN as [(HN & _)|(HN & q & HQ & EP)]; [lia|].
    assert (HNT : ~ In (ptr_addr (ss_L E) q, ss_n E) (ss_T E)) by (rewrite EP; exact (NI HN)).
    destruct (D1 q (ss_n E) HQ HNT) as (N1 & q1 & HQ1 & EQ1).
    pose proof (proj2 (BKP (ptr_addr (ss_L E) q) (ss_n E) ltac:(rewrite <- EQ1; exact (p2_in_blocks L A q1 _ HQ1))
      (N1 HN) HN (ex_intro _ q1 (conj HQ1 EQ1))) i Hi) as X.
    rewrite EP in X. exact X.
  - intros q m HIN. destruct (HB4 q m HIN) as [(H1 & H2)|H].
    + destruct (D4 q m H1) as [X|X]; [left; exact X|exfalso; exact (H2 X)].
    + right. exact H.
Qed.

Definition op2_out (es : list rentry) (G SP S fd : Z)
    (x3 x4 x5 x6 x7 x8 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ms : machine_state) : Prop :=
  (Forall (fun e => re_fd e <> fd) es /\
   exists a0 a1 a2 a3 a4 a5 a6 a7 s2 : word,
     ms = MS (mkR (Z_to_bv 64 0x14348) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) a0 a1 a2 a3 a4 a5 a6 a7 s2
                  x19 (Z_to_bv 64 0x318a0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc
             None (write_to_mem m (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0))) (seg_rom rsegs)) \/
  (exists (i : nat) (e : rentry),
     nth_error es i = Some e /\ re_fd e = fd /\ Forall (fun e' => re_fd e' <> fd) (firstn i es) /\
     ((re_eof e = 1 /\
       exists a0 a1 a2 a3 a4 a5 a6 a7 : word,
         ms = MS (mkR (Z_to_bv 64 0x14348) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (G + 56 * Z.of_nat i)) x19 (Z_to_bv 64 0x318a0) x21 x22 x23 x24 x25 x26 x27 x28 x29
                      x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None
                 (write_to_mem m (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0))) (seg_rom rsegs)) \/
      (re_eof e = 0 /\
       exists (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m1 : word -> option byte),
         ms = MS (mkR (Z_to_bv 64 0x14378) (Z_to_bv 64 SP) x3 x4 y5 y6 y7 x8 (Z_to_bv 64 S)
                      (Z_to_bv 64 (G + 56 * Z.of_nat i)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (G + 56 * Z.of_nat i))
                      (Z_to_bv 64 0x318f8) (Z_to_bv 64 0x318a0) x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31) F
                 (Z_to_bv 64 DRAIN) fc None m1 (seg_rom rsegs) /\
         munch [(SP + 40, SP + 48); (0x318fc, 0x31900)] m m1 /\ wmono rsegs m m1 /\ MemNorm.ro_agree rsegs m1 /\
         rw_cells rsegs m1 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] /\
         rw_cells rsegs m1 (SP + 40) [C8 (Z_to_bv 64 0)]))).

Lemma op2_pre : pthread_mutex_lock_ro_contract -> forall (es : list rentry) (tail junk : list byte) (G SP S fd : Z)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  ov_read_bytes rsegs m (Z_to_bv 64 0x318b8) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length es)))) ->
  ov_read_bytes rsegs m (Z_to_bv 64 S) 4 = Some (le4 (Z_to_bv 64 fd)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x318d0) 8 = Some (le8 (Z_to_bv 64 G)) ->
  rw_cells rsegs m G [CB 896 (concat (map entry_bytes es) ++ tail)] ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  (length es <= 4)%nat -> 0 <= fd < 2 ^ 31 ->
  rw_cells rsegs m (SP + 40) [CB 8 junk] -> 2 ^ 20 <= SP -> SP + 48 <= 2 ^ 64 ->
  rw_cells rsegs m 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  MemNorm.ro_agree rsegs m ->
  0 < S < 2 ^ 64 -> S mod 8 = 0 ->
  (es <> [] -> 0 < G /\ G mod 8 = 0 /\ (G + 896 <= SP + 40 \/ SP + 48 <= G)) ->
  evt rsegs (op2_out es G SP S fd x3 x4 x5 x6 x7 x8 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
      (Z_to_bv 64 0x318a0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14334) fc None m (seg_rom rsegs)).
Proof.
  intros LCK es tail junk G SP S fd x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 F fc m RN RF RG TB HW Hlen Hfd HJ HSP HSP2 CK RO HS0 HS8 HGP.
  assert (SOK : store_ok rsegs m (Z_to_bv 64 (SP + 40)) 8 = true).
  { pose proof (rw_cells_store_ok _ _ _ _ 0%nat (CB 8 junk) 8%nat HJ eq_refl eq_refl) as X.
    change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X. }
  assert (HGP' : es <> [] -> 0 < G /\ G mod 8 = 0 /\ 0 <= SP /\ SP + 48 <= 2 ^ 64 /\
      (G + 896 <= SP + 40 \/ SP + 48 <= G)).
  { intros NE. destruct (HGP NE) as (G0 & G8 & GD). split; [exact G0|]. split; [exact G8|]. split; [lia|].
    split; [exact HSP2|exact GD]. }
  eapply evt_cut; [exact (op2_scan es tail G SP S fd x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m (seg_rom rsegs) RN RF RG TB HW Hlen Hfd SOK HS0 HS8 HGP')|].
  intros ms [(HN & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & ->)
            |(i & e & Hi & Hfe & Hpre & [(E1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & ->)
                                        |(E0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & ->)])].
  - apply evt_done. left. split; [exact HN|]. do 9 eexists. reflexivity.
  - apply evt_done. right. exists i, e. split; [exact Hi|]. split; [exact Hfe|]. split; [exact Hpre|].
    left. split; [exact E1|]. do 8 eexists. reflexivity.
  - set (m0 := write_to_mem m (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0))).
    assert (C0 : rw_cells rsegs m0 (SP + 40) [C8 (Z_to_bv 64 0)]).
    { pose proof (rw_cells_write _ _ _ _ 0%nat (CB 8 junk) (C8 (Z_to_bv 64 0)) HJ eq_refl eq_refl I) as X.
      change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X. }
    assert (MU0 : munch [(SP + 40, SP + 48)] m m0).
    { unfold m0. change (Z_to_bv 64 (SP + 40)) with (wa (SP + 40)).
      eapply munch_write; [apply munch_refl|lia|rewrite length_le8; lia|cbn [inside]; left; rewrite length_le8; lia]. }
    assert (WM0 : wmono rsegs m m0) by (unfold m0; apply wmono_write, wmono_refl).
    assert (CK0 : rw_cells rsegs m0 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
    { unfold m0. apply rw_cells_frame; [exact CK|lia|rewrite length_le8; lia|cbn; lia]. }
    assert (RO0 : MemNorm.ro_agree rsegs m0).
    { apply (g9_ro_munch [(SP + 40, SP + 48)] m m0 MU0); [|exact RO].
      intros a HA. cbn [outside]. split; [|exact I].
      destruct (Z_lt_le_dec (bv_unsigned a) (2 ^ 20)) as [L1|L1]; [lia|].
      pose proof (bv_unsigned_in_range 64 a) as AR. change (bv_modulus 64) with (2 ^ 64) in AR.
      pose proof (ro_addr_hi (bv_unsigned a) ltac:(lia)) as X. rewrite Z_to_bv_bv_unsigned in X. congruence. }
    destruct (g9_cut _ _ [_] [_; _] CK0) as [K0 K12].
    destruct (g9_cut _ _ [_] [_] K12) as [K1 K2]. clear K12.
    assert (K1' : rw_cells rsegs m0 0x318fc [C4 (Z_to_bv 64 0)]) by exact K1.
    assert (K2' : rw_cells rsegs m0 0x31900 [C4 (Z_to_bv 64 0)]) by exact K2.
    clear K1 K2.
    assert (TB0 : bytes_at rsegs m0 0x318f8 [hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))]).
    { pose proof (proj2 (proj1 K0)) as B0. cbn [cells_bytes cbytes] in B0. rewrite app_nil_r in B0.
      rewrite <- (firstn_skipn 1 (le4 (Z_to_bv 64 0))) in B0. apply bytes_at_app in B0. exact (proj1 B0). }
    eapply evt_cut.
    { eapply (LCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0x318f8
        (hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))));
        [reflexivity|exact TB0|reflexivity|exact K1'|intros k Hk; unfold wa; apply sp_ro_glob; cbn in Hk; lia|exact RO0]. }
    intros ms1 PO. unfold pthread_mutex_lock_post_ro in PO.
    destruct PO as (t0 & t1 & t2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3 & t4 & t5 & t6 & m1 & -> & MU1 & WM1 & RO1 & L16).
    rewrite (ret_pc_even 0x14370) by lia.
    eapply evt_cut; [apply op2_seg_drain|].
    intros ms2 ->. apply evt_done. right. exists i, e. split; [exact Hi|]. split; [exact Hfe|]. split; [exact Hpre|].
    right. split; [exact E0|]. do 15 eexists. split; [reflexivity|].
    assert (D1 : forall A cs, rw_cells rsegs m0 A cs -> A + Z.of_nat (cells_size cs) <= 0x318fc \/ 0x31900 <= A ->
      rw_cells rsegs m1 A cs).
    { intros A cs H D. eapply rw_cells_transport; [exact H|exact MU1|exact WM1|]. cbn [disjoint_from]. split; [lia|exact I]. }
    split.
    { assert (SUB0 : sub_fp [(SP + 40, SP + 48)] [(SP + 40, SP + 48); (0x318fc, 0x31900)]).
      { intros x HX. cbn [outside] in HX |- *. destruct HX as (H1 & H2 & _). split; [exact H1|exact I]. }
      assert (SUB1 : sub_fp [(0x318f8 + 4, 0x318f8 + 8)] [(SP + 40, SP + 48); (0x318fc, 0x31900)]).
      { intros x HX. cbn [outside] in HX |- *. destruct HX as (H1 & H2 & _). split; [lia|exact I]. }
      exact (munch_trans _ _ _ _ (munch_weaken _ _ _ _ SUB0 MU0) (munch_weaken _ _ _ _ SUB1 MU1)). }
    split; [eapply wmono_trans; [exact WM0|exact WM1]|].
    split; [exact RO1|].
    split.
    { pose proof (D1 _ _ K0 ltac:(cbn; lia)) as K01. pose proof (D1 _ _ K2' ltac:(cbn; lia)) as K21.
      apply (g9_join _ _ (0x318f8 + 4) [C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] K01); [|reflexivity].
      apply (g9_join _ _ 0x31900 [C4 (Z_to_bv 64 16)] [C4 (Z_to_bv 64 0)] L16); [exact K21|reflexivity]. }
    apply D1; [exact C0|cbn; lia].
Qed.

Lemma op2_mid : pthread_mutex_unlock_ro_contract -> check_no_loss_read_contract -> forall (SP HA : Z)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  0x31ae0 <= SP - 96 -> SP < 2 ^ 64 -> 0x31900 <= HA -> HA + 28 <= SP - 96 -> HA mod 8 = 0 ->
  stk rsegs m (SP - 96) SP -> RoAdapt.not_ro rsegs (SP - 96) 96 ->
  rw_cells rsegs m 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m (HA + 24) (le4 (Z_to_bv 64 0)) ->
  MemNorm.ro_agree rsegs m ->
  evt rsegs (fun ms => exists (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 0x14398) (Z_to_bv 64 SP) x3 x4 y5 y6 y7 x8 (Z_to_bv 64 HA) (Z_to_bv 64 HA)
                   (Z_to_bv 64 (SP + 40)) y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 4) x20 x21 x22 x23 x24 x25
                   x26 x27 y28 y29 y30 y31) F (Z_to_bv 64 CHECK_NO_LOSS) fc None m' (seg_rom rsegs) /\
      munch [(SP - 96, SP); (0x318fc, 0x31900)] m m' /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\
      stk rsegs m' (SP - 96) SP /\
      rw_cells rsegs m' 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 HA) x10 x11 x12 x13 x14 x15 x16 x17 x18
      (Z_to_bv 64 0x318f8) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14378) fc None m
      (seg_rom rsegs)).
Proof.
  intros ULK CNR SP HA x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m HS1 HS2 HA1 HA2 HA8 ST NRO CK RD RO.
  eapply evt_cut; [apply op2_seg_unlock|]. intros ms0 ->.
  eapply evt_cut.
  { eapply (ULK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0x318f8 (SP - 96));
      [reflexivity|exact CK|intros k Hk; unfold wa; apply sp_ro_glob; cbn in Hk; lia
      |rewrite unsigned_lit by lia; exact ST
      |rewrite unsigned_lit by lia; replace (SP - (SP - 96)) with 96 by lia; exact NRO
      |rewrite unsigned_lit by lia; lia|rewrite unsigned_lit by lia; lia|exact RO]. }
  intros ms1 PO. unfold pthread_mutex_unlock_post_ro in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & RO1 & ST1 & K1).
  rewrite (ret_pc_even 0x14384) by lia. rewrite unsigned_lit in MU1, ST1 by lia.
  eapply evt_cut; [apply op2_seg_cnlr|]. intros ms2 ->.
  assert (RD1 : bytes_at rsegs m1 (bv_unsigned (Z_to_bv 64 HA) + 24) (le4 (Z_to_bv 64 0))).
  { rewrite unsigned_lit by lia. eapply bytes_at_transport; [exact RD|exact MU1|]. cbn [disjoint_from length].
    rewrite length_le4. split; [lia|]. split; [lia|exact I]. }
  assert (NZ : bv_unsigned (Z_to_bv 64 HA) <> 0) by (rewrite unsigned_lit by lia; lia).
  assert (A8 : bv_unsigned (Z_to_bv 64 HA) mod 8 = 0) by (rewrite unsigned_lit by lia; exact HA8).
  eapply evt_cut; [exact (CNR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 NZ A8 ltac:(lia) RD1)|].
  intros ms3 (a0' & a1' & ->). rewrite (ret_pc_even 0x1438c) by lia.
  eapply evt_cut; [apply (op2_seg_cnl SP)|]. intros ms4 ->.
  apply evt_done. do 14 eexists. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact RO1|]. split; [exact ST1|exact K1].
Qed.

Lemma op2_end : check_shape_done_contract -> forall (SP : Z) (v : word)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  ov_read_bytes rsegs m (Z_to_bv 64 (SP + 40)) 8 = Some (le8 v) ->
  bytes_at rsegs m check_shape_done_c.G_NOUT (le8 v) ->
  evt rsegs (fun ms => exists a1' : word,
      ms = MS (mkR (Z_to_bv 64 0x145bc) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 v a1' x12 x13 x14 x15 x16 x17
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None m
                   (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
      x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14398) fc None m (seg_rom rsegs)).
Proof.
  intros CSD SP v x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m RD NB.
  eapply evt_cut; [exact (op2_seg_done SP v x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m (seg_rom rsegs) RD)|].
  intros ms0 ->.
  eapply evt_cut; [exact (CSD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NB)|].
  intros ms1 (a1' & ->). rewrite (ret_pc_even 0x145bc) by lia.
  eapply evt_cut; [apply op2_seg_tail|]. intros ms2 ->.
  apply evt_done. exists a1'. reflexivity.
Qed.

Definition p2_sbs (e e' : rentry) : Prop :=
  re_fd e' = re_fd e /\ re_eof e' = re_eof e /\ re_skip e' = re_skip e /\ re_pad1 e' = re_pad1 e /\
  re_buf e' = re_buf e /\ re_used e' = re_used e /\ re_cap e' = re_cap e /\ re_hp e' = re_hp e /\
  re_kh e' = re_kh e /\ re_pad2 e' = re_pad2 e /\ map fst (re_keys e') = map fst (re_keys e) /\
  re_U e' = re_U e /\ re_junk e' = re_junk e.

Lemma p2_sbs_refl : forall e, p2_sbs e e.
Proof. intros e. unfold p2_sbs. tauto. Qed.

Lemma p2_sbs_trans : forall e1 e2 e3, p2_sbs e1 e2 -> p2_sbs e2 e3 -> p2_sbs e1 e3.
Proof.
  intros e1 e2 e3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13)
    (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13).
  unfold p2_sbs. repeat split; congruence.
Qed.

Lemma p2_sbs_short : forall e, p2_sbs e (short_entry e).
Proof.
  intros e. unfold p2_sbs, short_entry. cbn. repeat split. rewrite map_map. apply map_ext. intros [[a t] s]. reflexivity.
Qed.

Lemma p2_fst_len : forall (ks ks' : list (Z * list byte * list byte)), map fst ks' = map fst ks -> length ks' = length ks.
Proof. intros ks ks' H. rewrite <- (length_map fst ks'), <- (length_map fst ks), H. reflexivity. Qed.

Lemma p2_fst_addr : forall (ks ks' : list (Z * list byte * list byte)), map fst ks' = map fst ks ->
  map key_addr ks' = map key_addr ks.
Proof.
  intros ks ks' H. unfold key_addr. rewrite <- (map_map fst fst ks'), <- (map_map fst fst ks), H. reflexivity.
Qed.

Lemma p2_fst_text : forall (ks ks' : list (Z * list byte * list byte)), map fst ks' = map fst ks ->
  map key_text ks' = map key_text ks.
Proof.
  intros ks ks' H. unfold key_text. rewrite <- (map_map fst snd ks'), <- (map_map fst snd ks), H. reflexivity.
Qed.

Lemma p2_fst_texts : forall (ks ks' : list (Z * list byte * list byte)), map fst ks' = map fst ks ->
  keys_texts ks' = keys_texts ks.
Proof.
  intros ks ks' H. unfold keys_texts. rewrite <- (map_map key_text bzs ks'), <- (map_map key_text bzs ks).
  rewrite (p2_fst_text ks ks' H). reflexivity.
Qed.

Lemma p2_fst_total : forall (ks ks' : list (Z * list byte * list byte)), map fst ks' = map fst ks ->
  keys_total ks' = keys_total ks.
Proof.
  induction ks as [|k ks IH]; intros [|k' ks'] H; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as H1 H2. change (Z.of_nat (length (key_text k')) + 5 + keys_total ks' =
    Z.of_nat (length (key_text k)) + 5 + keys_total ks). unfold key_text. rewrite H1, (IH ks' H2). reflexivity.
Qed.

Lemma p2_fst_ptrs : forall (ks ks' : list (Z * list byte * list byte)), map fst ks' = map fst ks ->
  key_ptrs ks' = key_ptrs ks.
Proof.
  intros ks ks' H. unfold key_ptrs. rewrite <- (map_map key_addr (fun a => le8 (Z_to_bv 64 a)) ks'),
    <- (map_map key_addr (fun a => le8 (Z_to_bv 64 a)) ks), (p2_fst_addr ks ks' H). reflexivity.
Qed.

Lemma p2_sbs_bytes : forall e e', p2_sbs e e' -> entry_bytes e' = entry_bytes e.
Proof.
  intros e e' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13). unfold entry_bytes, re_nheld.
  rewrite A1, A2, A3, A4, A5, A6, A7, A8, A10, (p2_fst_len _ _ A11). reflexivity.
Qed.

Lemma p2_sbs_blocks : forall e e', p2_sbs e e' -> entry_blocks e' = entry_blocks e.
Proof.
  intros e e' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13). unfold entry_blocks.
  rewrite A5, A7, A8, (p2_fst_addr _ _ A11). reflexivity.
Qed.

Lemma p2_sbs_cost : forall e e' p, p2_sbs e e' -> pair_cost e' p = pair_cost e p.
Proof.
  intros e e' p (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13). unfold pair_cost.
  rewrite A3, A6, (p2_fst_total _ _ A11). reflexivity.
Qed.

Lemma p2_sbs_texts : forall e e', p2_sbs e e' -> keys_texts (re_keys e') = keys_texts (re_keys e).
Proof. intros e e' (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A11 & _). exact (p2_fst_texts _ _ A11). Qed.

Lemma p2_sbs_nw : forall e e', p2_sbs e e' -> nw_ent e' = nw_ent e.
Proof.
  intros e e' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13). unfold nw_ent, re_nheld.
  rewrite A6, A7, A8, A9, (p2_fst_len _ _ A11). reflexivity.
Qed.

Lemma p2_sbs_wt : forall l l' hj, Forall2 p2_sbs l l' -> nc_wt l' hj = nc_wt l hj.
Proof.
  intros l l' hj H. assert (Z : AllocBound.zsum nw_ent l' = AllocBound.zsum nw_ent l).
  { induction H as [|x y l l' Hxy H IH]; [reflexivity|]. rewrite !AllocBound.zsum_cons, IH, (p2_sbs_nw x y Hxy).
    reflexivity. }
  unfold nc_wt. rewrite Z, (Forall2_length H). reflexivity.
Qed.

Lemma p2_slack_bytes : forall segs mem a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> present mem (a + i)) -> exists bs, length bs = n /\ bytes_at segs mem a bs.
Proof.
  intros segs mem a n H0 H1 HP. destruct (present_rw_cells segs mem a n H0 H1 HP) as [junk RW].
  exists junk. split; [exact (proj1 (proj1 (proj1 RW)))|].
  pose proof (proj2 (proj1 RW)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Definition p2_key_ok {rc : RunCeil} (B : malloc_syms) (L : layout) (A : astate) (mem : word -> option byte)
    (k : Z * list byte * list byte) : Prop :=
  In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A) /\
  fresh_block B (key_addr k) (Z.of_nat (length (key_text k)) + 1) /\
  bytes_at (ms_segs B) mem (key_addr k) (key_text k ++ Z_to_bv 8 0 :: key_slack k) /\
  ~ In (Z_to_bv 8 0) (key_text k) /\ 14 <= Z.of_nat (length (key_text k)) <= 6000 /\
  (- (key_addr k + Z.of_nat (length (key_text k)) + 1)) mod 8 <= Z.of_nat (length (key_slack k)).

Lemma p2_keys_rmid : forall rc fx B (API : AllocAPI B) K sp Es Fs L A mem md L' A' mem' md' ks,
  @frame_allocator rc fx B API -> aa_MR API L A mem md -> rmid B API K sp Es Fs L A mem md L' A' mem' md' ->
  Forall (p2_key_ok (rc := rc) B L A mem) ks ->
  (forall k, In k ks -> kept_block Es Fs L A (key_addr k)) ->
  exists ks', map fst ks' = map fst ks /\ Forall (p2_key_ok (rc := rc) B L' A' mem') ks'.
Proof.
  intros rc fx B API K sp Es Fs L A mem md L' A' mem' md' ks FA HM R.
  assert (BW : blocks_writable B API) by (unfold frame_allocator in FA; tauto).
  assert (BSP : block_slack_present B API) by (unfold frame_allocator in FA; tauto).
  pose proof R as (M1 & _).
  induction ks as [|k ks IH]; intros HF HK; [exists []; split; [reflexivity|constructor]|].
  inversion HF as [|? ? Hk Hks]; subst.
  destruct (IH Hks (fun k0 H => HK k0 (or_intror H))) as (ks' & E' & F').
  destruct k as [[addr txt] sl]. destruct Hk as (IN & FR & HB & NZ & LEN & PAD).
  unfold key_addr, key_text, key_slack in *. cbn [fst snd] in *.
  destruct (HK _ (or_introl eq_refl)) as (NF & NE). unfold key_addr in NF, NE. cbn [fst] in NF, NE.
  set (n := Z.of_nat (length txt) + 1) in *.
  assert (Hn : 0 < n) by (unfold n; lia).
  pose proof (proj1 (rmid_block B API BW K sp Es Fs L A mem md L' A' mem' md' addr n 0 R IN Hn NF ltac:(lia)
    (NE n 0 IN ltac:(lia)))) as IN'.
  pose proof (block_facts B (aa_MR API) (aa_laws API) L A mem md addr n 0 HM IN ltac:(lia))
    as (_ & BL0 & BL1 & _).
  change (txt ++ Z_to_bv 8 0 :: sl) with (txt ++ [Z_to_bv 8 0] ++ sl) in HB.
  rewrite (app_assoc txt [Z_to_bv 8 0] sl) in HB. apply bytes_at_app in HB. destruct HB as [HB0 _].
  assert (HB0' : bytes_at (ms_segs B) mem' addr (txt ++ [Z_to_bv 8 0])).
  { apply (rmid_bytes_block B API BW K sp Es Fs L A mem md L' A' mem' md' addr n addr _ R IN Hn NF HB0);
      [lia|rewrite length_app; cbn [length]; unfold n; lia|].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply (NE n i IN). unfold n. lia. }
  set (pad := (- (addr + n)) mod 8).
  assert (PR : forall i, 0 <= i < Z.of_nat (Z.to_nat pad) -> present mem' (addr + n + i)).
  { intros i Hi. apply (BSP L' A' mem' md' addr n (addr + n + i) M1 IN'). unfold pad in Hi.
    rewrite Z2Nat.id in Hi by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia. }
  destruct (p2_slack_bytes (ms_segs B) mem' (addr + n) (Z.to_nat pad) ltac:(lia)
    ltac:(rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia); pose proof (@YM05.alloc_ceiling_lt rc);
          pose proof (Z.mod_pos_bound (- (addr + n)) 8 ltac:(lia)); unfold pad; lia) PR) as (bs & BL & BB).
  exists (((addr, txt), bs) :: ks'). split; [cbn [map fst]; f_equal; exact E'|].
  constructor; [|exact F'].
  unfold p2_key_ok, key_addr, key_text, key_slack. cbn [fst snd].
  split; [exact IN'|]. split; [exact FR|].
  split.
  { change (txt ++ Z_to_bv 8 0 :: bs) with (txt ++ [Z_to_bv 8 0] ++ bs).
    rewrite (app_assoc txt [Z_to_bv 8 0] bs). apply bytes_at_app. split; [exact HB0'|].
    rewrite length_app. cbn [length]. replace (addr + Z.of_nat (length txt + 1)) with (addr + n) by (unfold n; lia).
    exact BB. }
  split; [exact NZ|]. split; [exact LEN|]. rewrite BL. fold n. fold pad.
  rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma p2_entry_rmid : forall rc fx B (API : AllocAPI B) K sp Es Fs L A mem md L' A' mem' md' e,
  @frame_allocator rc fx B API -> aa_MR API L A mem md -> rmid B API K sp Es Fs L A mem md L' A' mem' md' ->
  RelayRep.entry_ok (rc := rc) B L A mem e ->
  (forall q, In q (entry_blocks e) -> kept_block Es Fs L A q) ->
  exists e', p2_sbs e e' /\ RelayRep.entry_ok (rc := rc) B L' A' mem' e'.
Proof.
  intros rc fx B API K sp Es Fs L A mem md L' A' mem' md' e FA HM R
    (H1 & H2 & P1 & P2 & FD & CAP & UL & U6 & UZ & BUF & NH & HP & ND1 & ND2 & KS) HKB.
  assert (BW : blocks_writable B API) by (unfold frame_allocator in FA; tauto).
  assert (KIN : forall k, In k (re_keys e) -> In (key_addr k) (entry_blocks e)).
  { intros k Hk. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hk. }
  destruct (p2_keys_rmid rc fx B API K sp Es Fs L A mem md L' A' mem' md' (re_keys e) FA HM R KS
    (fun k Hk => HKB _ (KIN k Hk))) as (ks' & EK & FK).
  exists (RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) (re_hp e) (re_kh e)
    (re_pad2 e) ks' (re_U e) (re_junk e)).
  split; [unfold p2_sbs; cbn; repeat split; exact EK|].
  unfold RelayRep.entry_ok, re_nheld in *. cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2
    re_keys re_U re_junk]. rewrite (p2_fst_len _ _ EK).
  split; [exact H1|]. split; [exact H2|]. split; [exact P1|]. split; [exact P2|]. split; [exact FD|].
  split; [exact CAP|]. split; [exact UL|]. split; [exact U6|]. split; [exact UZ|].
  split.
  { destruct BUF as [Z0|(Hc & IN & FR & JL & RW)]; [left; exact Z0|right].
    assert (BI : In (re_buf e) (entry_blocks e)).
    { unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)). left. reflexivity. }
    destruct (HKB _ BI) as (NF & NE).
    split; [exact Hc|].
    split; [exact (proj1 (rmid_block B API BW K sp Es Fs L A mem md L' A' mem' md' _ _ 0 R IN Hc NF ltac:(lia)
      (NE _ 0 IN ltac:(lia))))|].
    split; [exact FR|]. split; [exact JL|].
    apply (rmid_rw_block B API BW K sp Es Fs L A mem md L' A' mem' md' _ _ _ _ R IN Hc NF RW);
      [lia|cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia|].
    intros i Hi. cbn [cells_size csize] in Hi. rewrite Nat.add_0_r, Z2Nat.id in Hi by lia. apply (NE _ i IN). lia. }
  split; [exact NH|].
  split.
  { destruct HP as [(H0 & HK0)|(IN & FR & L8 & K8 & PB)].
    - left. split; [exact H0|]. rewrite HK0 in EK. cbn in EK. destruct ks'; [reflexivity|discriminate].
    - right.
      destruct (p2_blk rc fx B API L A mem md _ _ 0 FA HM IN ltac:(lia)) as (_ & HP0 & _).
      assert (HI : In (re_hp e) (entry_blocks e)).
      { unfold entry_blocks. apply in_or_app. right. rewrite (proj2 (Z.eqb_neq (re_hp e) 0) ltac:(lia)).
        left. reflexivity. }
      destruct (HKB _ HI) as (NF & NE).
      split; [exact (proj1 (rmid_block B API BW K sp Es Fs L A mem md L' A' mem' md' _ _ 0 R IN ltac:(lia) NF
        ltac:(lia) (NE _ 0 IN ltac:(lia))))|].
      split; [exact FR|]. split; [exact L8|]. split; [exact K8|].
      rewrite (p2_fst_ptrs _ _ EK).
      apply (rmid_bytes_block B API BW K sp Es Fs L A mem md L' A' mem' md' _ _ _ _ R IN ltac:(lia) NF PB);
        [lia|rewrite slot_key_ptrs_length; lia|].
      intros i Hi. rewrite slot_key_ptrs_length in Hi. apply (NE _ i IN). lia. }
  split; [rewrite (p2_fst_addr _ _ EK); exact ND1|].
  split; [rewrite (p2_fst_text _ _ EK); exact ND2|].
  exact FK.
Qed.

Lemma p2_src_rmid : forall rc fx B (API : AllocAPI B) K sp Es Fs L A mem md L' A' mem' md' HA h,
  @frame_allocator rc fx B API -> ms_segs B = rsegs -> @YM05.alloc_ceiling rc <= sp - K ->
  aa_MR API L A mem md -> rmid B API K sp Es Fs L A mem md L' A' mem' md' ->
  src_at (rc := rc) B L A mem HA h ->
  (forall i, 0 <= i < 96 -> img_plain B (HA + i) /\ ~ Es (HA + i)) ->
  (forall q, In q (hs_blocks h) -> kept_block Es Fs L A q) ->
  src_at (rc := rc) B L' A' mem' HA h.
Proof.
  intros rc fx B API K sp Es Fs L A mem md L' A' mem' md' HA h FA SEG HK HM R S HL HB.
  assert (BW : blocks_writable B API) by (unfold frame_allocator in FA; tauto).
  assert (AX : AllocExtra B (aa_MR API)) by (unfold frame_allocator in FA; tauto).
  apply src_at_iff in S. destruct S as (SB & LE & LH & ND).
  apply src_at_iff.
  split.
  { apply (src_base_rmid B API AX BW K sp Es Fs L A mem md L' A' mem' md' HA h SEG HK HM R SB).
    - intros i Hi. apply HL. lia.
    - intros q [Hq|Hq]; apply HB; unfold hs_blocks; apply in_or_app; [left; exact Hq|].
      right. apply in_or_app. left. left. symmetry. exact Hq. }
  split.
  { apply (list_at_rmid B API AX BW K sp Es Fs L A mem md L' A' mem' md' (HA + 64) _ true SEG HK HM R LE).
    - intros i Hi. replace (HA + 64 + i) with (HA + (64 + i)) by lia. apply HL. lia.
    - intros q Hq. apply HB. unfold hs_blocks. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact Hq. }
  split; [|exact ND].
  apply (list_at_rmid B API AX BW K sp Es Fs L A mem md L' A' mem' md' (HA + 80) _ true SEG HK HM R LH).
  - intros i Hi. replace (HA + 80 + i) with (HA + (80 + i)) by lia. apply HL. lia.
  - intros q Hq. apply HB. unfold hs_blocks. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. right. exact Hq.
Qed.

Definition p2_ksum (G : list (list Z)) : Z :=
  fold_right (fun xl acc => xl + 5 + acc) 0 (map (fun x => Z.of_nat (length x)) G).

Lemma p2_ksum_app : forall G1 G2, p2_ksum (G1 ++ G2) = p2_ksum G1 + p2_ksum G2.
Proof. intros G1 G2. unfold p2_ksum. induction G1 as [|x G1 IH]; cbn [app map fold_right]; lia. Qed.

Lemma p2_ksum_nonneg : forall G, 0 <= p2_ksum G.
Proof. intros G. unfold p2_ksum. induction G as [|x G IH]; cbn [map fold_right]; lia. Qed.

Lemma p2_ksum_incl : forall A B, List.NoDup A -> incl A B -> p2_ksum A <= p2_ksum B.
Proof.
  induction A as [|a A IH]; intros B ND HI; [cbn; apply p2_ksum_nonneg|].
  apply List.NoDup_cons_iff in ND. destruct ND as [NA ND].
  destruct (in_split a B (HI a (or_introl eq_refl))) as (B1 & B2 & ->).
  assert (HI' : incl A (B1 ++ B2)).
  { intros y Hy. pose proof (HI y (or_intror Hy)) as Y. apply in_app_or in Y. apply in_or_app.
    destruct Y as [Y|[Y|Y]]; [left; exact Y| subst; contradiction|right; exact Y]. }
  pose proof (IH _ ND HI') as X. rewrite p2_ksum_app in X |- *.
  change (p2_ksum (a :: A)) with (Z.of_nat (length a) + 5 + p2_ksum A).
  change (p2_ksum (a :: B2)) with (Z.of_nat (length a) + 5 + p2_ksum B2). lia.
Qed.

Lemma p2_ksum_filter : forall (f : list Z -> bool) G, p2_ksum (List.filter f G) <= p2_ksum G.
Proof.
  intros f. induction G as [|x G IH]; [cbn; lia|]. cbn [List.filter].
  change (p2_ksum (x :: G)) with (Z.of_nat (length x) + 5 + p2_ksum G).
  destruct (f x); [change (p2_ksum (x :: List.filter f G)) with (Z.of_nat (length x) + 5 + p2_ksum (List.filter f G))|]; lia.
Qed.

Lemma p2_gesture_begin : forall l x, gesture l = Some (GBegin, x) -> (length x + 6 = length l)%nat.
Proof.
  intros l x H. unfold gesture in H.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l)); [|discriminate].
  destruct (last_space_from 0 l) as [j|] eqn:E; [|discriminate].
  destruct (Nat.ltb 13 j) eqn:J; [|discriminate].
  pose proof (last_space_lt l 0 j E) as LT.
  destruct (list_eqb (skipn (S j) l) W_BEGIN) eqn:W.
  - injection H as <-. unfold list_eqb in W.
    destruct (list_eq_dec Z.eq_dec (skipn (S j) l) W_BEGIN) as [Ew|]; [|discriminate].
    pose proof (f_equal (@length Z) Ew) as Lw. rewrite length_skipn in Lw. cbn in Lw.
    rewrite length_firstn. lia.
  - destruct (list_eqb (skipn (S j) l) W_END); discriminate.
Qed.

Lemma p2_ksum_upd : forall G l, p2_ksum (upd G l) <= p2_ksum G + Z.of_nat (length l) + 1.
Proof.
  intros G l. unfold upd. destruct (gesture l) as [[[|] x]|] eqn:EG.
  - pose proof (p2_gesture_begin l x EG) as LX. destruct (existsb (list_eqb x) G); [lia|].
    rewrite p2_ksum_app. change (p2_ksum [x]) with (Z.of_nat (length x) + 5 + 0). lia.
  - pose proof (p2_ksum_filter (fun y => negb (list_eqb x y)) G). lia.
  - lia.
Qed.

Lemma p2_ksum_upds : forall Ls G, p2_ksum (upds G Ls) <= p2_ksum G + Z.of_nat (length (with_nul Ls)).
Proof.
  unfold upds. induction Ls as [|l Ls IH]; intros G; cbn [fold_left]; [cbn; lia|].
  pose proof (IH (upd G l)) as X. pose proof (p2_ksum_upd G l) as Y.
  unfold with_nul in *. cbn [map concat]. rewrite length_app, length_app. cbn [length]. lia.
Qed.

Lemma p2_pair_cost : forall (e e' : rentry) (h h' : hsrc) (j : nat),
  re_skip e = hs_overlong h -> (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  (hs_overlong h = 0 \/ hs_overlong h = 1) -> Z.of_nat (length (re_U e)) = re_used e ->
  re_skip e' = hs_overlong h' -> (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) ->
  (hs_overlong h' = 0 \/ hs_overlong h' = 1) -> Z.of_nat (length (re_U e')) = re_used e' ->
  hs_state h' = feed (hs_state h) (bzs (pending_stream h)) -> hl_recs (hs_pending h') = [] ->
  NoDup (keys_texts (re_keys e')) ->
  same_set (keys_texts (re_keys e')) (upds (keys_texts (re_keys e)) (lines (hs_state h) (bzs (pending_stream h)))) ->
  pair_cost e' (h', j) <= pair_cost e (h, j).
Proof.
  intros e e' h h' j S1 W1 O1 U1 S2 W2 O2 U2 ST HP ND SS. unfold pair_cost. cbn [fst].
  assert (P0 : pending_stream h' = []) by (unfold pending_stream; rewrite HP; reflexivity).
  rewrite P0. cbn [length]. change (Z.of_nat 0) with 0.
  rewrite <- (hs_wcost e h S1 W1 O1 U1), <- (hs_wcost e' h' S2 W2 O2 U2), ST.
  pose proof (lines_bytes (bzs (pending_stream h)) (hs_state h)) as LB. rewrite bzs_length in LB.
  rewrite !RelayCap.keys_total_texts. fold (p2_ksum (keys_texts (re_keys e'))). fold (p2_ksum (keys_texts (re_keys e))).
  apply NoDup_ListNoDup in ND.
  pose proof (p2_ksum_incl _ _ ND (fun y Hy => proj1 (SS y) Hy)) as X.
  pose proof (p2_ksum_upds (lines (hs_state h) (bzs (pending_stream h))) (keys_texts (re_keys e))) as Y. lia.
Qed.

Lemma p2_cnt_cons : forall (a x : Z) l,
  count_occ Z.eq_dec (a :: l) x = ((if Z.eq_dec a x then 1 else 0) + count_occ Z.eq_dec l x)%nat.
Proof. intros a x l. cbn [count_occ]. destruct (Z.eq_dec a x); reflexivity. Qed.

Lemma p2_nd_cnt : forall (l : list Z), NoDup l <-> forall x, (count_occ Z.eq_dec l x <= 1)%nat.
Proof.
  intros l. split.
  - intros H. apply NoDup_ListNoDup in H. apply (NoDup_count_occ Z.eq_dec). exact H.
  - intros H. apply NoDup_ListNoDup. apply (NoDup_count_occ Z.eq_dec). exact H.
Qed.

Lemma p2_target_split : forall G OUT es hj i e h jj,
  nth_error es i = Some e -> nth_error hj i = Some (h, jj) ->
  forall x, count_occ Z.eq_dec (target_addrs G OUT es hj) x =
    (count_occ Z.eq_dec (G :: OUT :: entry_blocks e ++ hs_blocks h) x +
     count_occ Z.eq_dec (concat (map entry_blocks (firstn i es)) ++ concat (map entry_blocks (skipn (S i) es)) ++
       concat (map (fun p => hs_blocks (fst p)) (firstn i hj)) ++
       concat (map (fun p => hs_blocks (fst p)) (skipn (S i) hj))) x)%nat.
Proof.
  intros G OUT es hj i e h jj He Hh x.
  rewrite (split_at es i e (proj1 (nth_error_Some es i) ltac:(rewrite He; discriminate))) at 1.
  rewrite (split_at hj i (h, jj) (proj1 (nth_error_Some hj i) ltac:(rewrite Hh; discriminate))) at 1.
  rewrite (nth_error_nth es i e He), (nth_error_nth hj i (h, jj) Hh).
  unfold target_addrs. rewrite !map_app, !concat_app. cbn [map concat fst].
  rewrite !p2_cnt_cons, !count_occ_app. lia.
Qed.

Lemma p2_nodup_sub : forall G OUT es hj i e h jj,
  NoDup (target_addrs G OUT es hj) -> nth_error es i = Some e -> nth_error hj i = Some (h, jj) ->
  NoDup (G :: OUT :: entry_blocks e ++ hs_blocks h).
Proof.
  intros G OUT es hj i e h jj ND He Hh. apply p2_nd_cnt. intros x. apply p2_nd_cnt with (x := x) in ND.
  rewrite (p2_target_split G OUT es hj i e h jj He Hh x) in ND. lia.
Qed.

Lemma p2_f2_nth : forall {X Y} (R : X -> Y -> Prop) l1 l2 n y, Forall2 R l1 l2 -> nth_error l2 n = Some y ->
  exists x, nth_error l1 n = Some x /\ R x y.
Proof.
  intros X Y R l1 l2 n y H. revert n. induction H as [|a b l1 l2 Hab H IH]; intros [|n] Hn; cbn in Hn; try discriminate.
  - injection Hn as <-. exists a. split; [reflexivity|exact Hab].
  - exact (IH n Hn).
Qed.

Lemma p2_f2_nth_l : forall {X Y} (R : X -> Y -> Prop) l1 l2 n x, Forall2 R l1 l2 -> nth_error l1 n = Some x ->
  exists y, nth_error l2 n = Some y /\ R x y.
Proof.
  intros X Y R l1 l2 n x H. revert n. induction H as [|a b l1 l2 Hab H IH]; intros [|n] Hn; cbn in Hn; try discriminate.
  - injection Hn as <-. exists b. split; [reflexivity|exact Hab].
  - exact (IH n Hn).
Qed.

Lemma p2_pair_idx : forall rc B L A mem t es hj i e h jj,
  Forall2 (pair_ok (rc := rc) B L A mem t) es hj -> NoDup (map re_fd es) ->
  nth_error es i = Some e -> In (h, jj) hj -> hs_fd h = re_fd e -> nth_error hj i = Some (h, jj).
Proof.
  intros rc B L A mem t es hj i e h jj PA ND Hi Hin Hfd.
  destruct (In_nth_error hj (h, jj) Hin) as [i0 Hi0].
  destruct (p2_f2_nth _ _ _ _ _ PA Hi0) as (e0 & He0 & (_ & _ & Hfd0 & _)). cbn [fst] in Hfd0.
  apply NoDup_ListNoDup in ND.
  assert (EQ : i0 = i).
  { apply (proj1 (List.NoDup_nth_error (map re_fd es)) ND i0 i).
    - rewrite length_map. apply nth_error_Some. rewrite He0. discriminate.
    - rewrite !nth_error_map, He0, Hi. cbn. congruence. }
  subst i0. exact Hi0.
Qed.

Lemma p2_nth_seq4 : forall (f : nat -> Z) k, (k < 4)%nat -> nth k (map f (seq 0 4)) 0 = f k.
Proof. intros f k Hk. destruct k as [|[|[|[|k]]]]; [reflexivity..|lia]. Qed.

Definition p2_fsel (hj : list (hsrc * nat)) (i : nat) : option (hsrc * nat) := find (fun p => Nat.eqb (snd p) i) hj.

Lemma p2_fds : forall rc B L A mem t es hj, Forall2 (pair_ok (rc := rc) B L A mem t) es hj ->
  map (fun p => hs_fd (fst p)) hj = map re_fd es.
Proof.
  intros rc B L A mem t es hj H. induction H as [|e p es hj HP H IH]; [reflexivity|].
  cbn [map]. destruct HP as (_ & _ & FD & _). cbv zeta in FD. rewrite FD, IH. reflexivity.
Qed.

Lemma p2_fd_ne : forall rc B L A mem t es hj h1 j1 h2 j2,
  Forall2 (pair_ok (rc := rc) B L A mem t) es hj -> NoDup (map re_fd es) ->
  In (h1, j1) hj -> In (h2, j2) hj -> j1 <> j2 -> hs_fd h1 <> hs_fd h2.
Proof.
  intros rc B L A mem t es hj h1 j1 h2 j2 PA ND I1 I2 NJ EQ.
  rewrite <- (p2_fds rc B L A mem t es hj PA) in ND. apply NoDup_ListNoDup in ND.
  destruct (In_nth_error hj _ I1) as [k1 K1]. destruct (In_nth_error hj _ I2) as [k2 K2].
  assert (KE : k1 = k2).
  { apply (proj1 (List.NoDup_nth_error _) ND k1 k2).
    - rewrite length_map. apply nth_error_Some. rewrite K1. discriminate.
    - rewrite !nth_error_map, K1, K2. cbn. rewrite EQ. reflexivity. }
  subst k2. rewrite K1 in K2. injection K2 as _ E2. exact (NJ E2).
Qed.

Lemma p2_others : forall rc B L A mem t nfd G OUT es hj i e h jj,
  relay_at (rc := rc) B L A mem t nfd G OUT es hj -> nth_error es i = Some e -> nth_error hj i = Some (h, jj) ->
  exists fs os, others_at B mem jj (re_fd e) fs os.
Proof.
  intros rc B L A mem t nfd G OUT es hj i e h jj HREL He Hh.
  pose proof HREL as (_ & _ & _ & _ & NDF & _ & PA & NDH & ZH & _).
  destruct (p2_f2_nth _ _ _ _ _ PA Hh) as (e0 & He0 & (_ & _ & FD0 & _)). cbn [fst] in FD0.
  rewrite He in He0. injection He0 as <-.
  assert (HIN : In (h, jj) hj) by exact (nth_error_In hj i Hh).
  exists (map (fun k => match p2_fsel hj k with Some p => hs_fd (fst p) | None => 0 end) (seq 0 4)).
  exists (map (fun k => match p2_fsel hj k with Some p => hs_open (fst p) | None => 0 end) (seq 0 4)).
  split; [rewrite length_map, length_seq; reflexivity|]. split; [rewrite length_map, length_seq; reflexivity|].
  intros k Hk NK. rewrite !p2_nth_seq4 by exact Hk. cbv beta.
  destruct (p2_fsel hj k) as [[hk q]|] eqn:EF.
  - unfold p2_fsel in EF. apply find_some in EF. destruct EF as [INK EQK]. cbn [snd] in EQK. apply Nat.eqb_eq in EQK.
    subst q. destruct (pair_find _ _ _ _ _ (hk, k) PA INK) as [ek HPK].
    destruct HPK as (SRC & _). cbv zeta in SRC. cbn [fst snd] in SRC |- *.
    destruct SRC as (C1 & _ & _ & HO & FDR & _).
    split; [|split].
    + exact (proj1 (hg_cut _ _ _ [C4 (Z_to_bv 64 (hs_fd hk)); C4 (Z_to_bv 64 (hs_open hk))]
        [C4 (Z_to_bv 64 (hs_closed hk)); C4 (Z_to_bv 64 (hs_eintr hk))] C1)).
    + right. rewrite <- FD0. exact (p2_fd_ne rc B L A mem t es hj hk k h jj PA NDF INK HIN NK).
    + exact FDR.
  - assert (OF : slot_open hj k = false).
    { unfold slot_open. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X.
      destruct X as (q & HQ & HE). apply Nat.eqb_eq in HE. subst q. apply in_map_iff in HQ.
      destruct HQ as ([hq q] & EQ & HQ). cbn in EQ. subst q. unfold p2_fsel in EF.
      pose proof (find_none _ _ EF (hq, k) HQ) as X. cbn in X. rewrite Nat.eqb_refl in X. discriminate. }
    pose proof (ZH k Hk OF) as Z0. split; [|split; [left; reflexivity|lia]].
    assert (Z1 : rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat k)
        ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [CB 88 (nulbytes 88)])).
    { eapply rw_cells_retype; [exact Z0|cbn; tauto|reflexivity]. }
    exact (proj1 (hg_cut _ _ _ _ _ Z1)).
Qed.

Lemma p2_eb_len : forall rc B L A mem es, Forall (RelayRep.entry_ok (rc := rc) B L A mem) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  intros rc B L A mem es H. induction H as [|e es He H IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, (entry_size rc B L A mem e He), IH. lia.
Qed.

Lemma p2_table_split : forall rc B L A mem es tail G i e,
  Forall (RelayRep.entry_ok (rc := rc) B L A mem) es -> nth_error es i = Some e ->
  Z.of_nat (length tail) = 896 - 56 * Z.of_nat (length es) ->
  rw_cells (ms_segs B) mem G [CB 896 (concat (map entry_bytes es) ++ tail)] ->
  rw_cells (ms_segs B) mem G [CB (56 * i) (concat (map entry_bytes (firstn i es)));
    CB 56 (entry_bytes e); CB (896 - 56 * S i) (concat (map entry_bytes (skipn (S i) es)) ++ tail)].
Proof.
  intros rc B L A mem es tail G i e HF He TL TB.
  assert (Hi : (i < length es)%nat) by (apply nth_error_Some; rewrite He; discriminate).
  pose proof (split_at es i e Hi) as SP. rewrite (nth_error_nth es i e He) in SP.
  pose proof HF as HF'. rewrite SP in HF'. apply Forall_app in HF'. destruct HF' as [F1 F2].
  inversion F2 as [|? ? Fe F3]; subst.
  pose proof (p2_eb_len rc B L A mem _ F1) as L1. pose proof (p2_eb_len rc B L A mem _ F3) as L3.
  pose proof (entry_size rc B L A mem e Fe) as LE.
  rewrite length_firstn in L1. rewrite length_skipn in L3.
  eapply rw_cells_retype; [exact TB| |].
  - cbn [cells_wf cell_wf]. rewrite L1, LE, length_app, L3. split; [lia|]. split; [reflexivity|]. split; [lia|exact I].
  - assert (CE : concat (map entry_bytes es) = concat (map entry_bytes (firstn i es)) ++ entry_bytes e ++
        concat (map entry_bytes (skipn (S i) es))).
    { rewrite SP at 1. rewrite map_app, concat_app. reflexivity. }
    cbn [cells_bytes cbytes]. rewrite !app_nil_r, CE, !app_assoc. reflexivity.
Qed.

Lemma p2_drain_k : DRAIN_K = 8512.
Proof. reflexivity. Qed.

Lemma p2_cnl_k : CHECK_NO_LOSS_K = 8384.
Proof. reflexivity. Qed.

Lemma p2_combine_nth : forall {X Y} (l1 : list X) (l2 : list Y) n a b,
  nth_error l1 n = Some a -> nth_error l2 n = Some b -> In (a, b) (combine l1 l2).
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] [|n] a b H1 H2; cbn in *; try discriminate.
  - injection H1 as <-. injection H2 as <-. left. reflexivity.
  - right. exact (IH l2 n a b H1 H2).
Qed.

Lemma p2_nth_forall : forall {X} (P : X -> Prop) l n x, Forall P l -> nth_error l n = Some x -> P x.
Proof. intros X P l n x H Hn. rewrite Forall_forall in H. exact (H x (nth_error_In l n Hn)). Qed.

Ltac lia2 :=
  repeat match goal with
  | H : _ \/ _ |- _ => clear H
  | H : ?P -> ?Q |- _ => match type of P with Prop => match type of Q with Prop => clear H end end
  | H : context [Z.max _ _] |- _ => clear H
  | H : context [Z.min _ _] |- _ => clear H
  | H : context [Z.modulo _ _] |- _ => clear H
  | H : context [Z.div _ _] |- _ => clear H
  end; lia.

Lemma p2_pair_sbs : forall rc B L A mem L' A' mem' t e e' p,
  pair_ok (rc := rc) B L A mem t e p -> p2_sbs e e' ->
  src_at (rc := rc) B L' A' mem' (G_S + SRC_SIZE * Z.of_nat (snd p)) (fst p) ->
  pair_ok (rc := rc) B L' A' mem' t e' p.
Proof.
  intros rc B L A mem L' A' mem' t e e' p HP SB S'. unfold pair_ok in *. cbv zeta in *.
  destruct HP as (S & J & FD & EO & SS & REST).
  destruct SB as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  split; [exact S'|]. split; [exact J|]. split; [rewrite A1; exact FD|].
  split; [rewrite A2, A3, A12; exact EO|]. split; [rewrite (p2_fst_texts _ _ A11); exact SS|]. exact REST.
Qed.

Lemma p2_pairs_rmid : forall rc fx B (API : AllocAPI B) K sp Es Fs L A mem md L' A' mem' md' t es hj,
  @frame_allocator rc fx B API -> ms_segs B = rsegs -> @YM05.alloc_ceiling rc <= sp - K ->
  aa_MR API L A mem md -> rmid B API K sp Es Fs L A mem md L' A' mem' md' ->
  Forall2 (pair_ok (rc := rc) B L A mem t) es hj -> Forall (RelayRep.entry_ok (rc := rc) B L A mem) es ->
  (forall q, In q (concat (map entry_blocks es)) -> kept_block Es Fs L A q) ->
  (forall q, In q (concat (map (fun p => hs_blocks (fst p)) hj)) -> kept_block Es Fs L A q) ->
  (forall p i, In p hj -> 0 <= i < 96 ->
     img_plain B (G_S + SRC_SIZE * Z.of_nat (snd p) + i) /\ ~ Es (G_S + SRC_SIZE * Z.of_nat (snd p) + i)) ->
  exists es', Forall2 p2_sbs es es' /\ Forall (RelayRep.entry_ok (rc := rc) B L' A' mem') es' /\
    Forall2 (pair_ok (rc := rc) B L' A' mem' t) es' hj.
Proof.
  intros rc fx B API K sp Es Fs L A mem md L' A' mem' md' t es hj FA SEG HK HM R PA.
  induction PA as [|e p es hj HP PA IH]; intros HES KE KH KS.
  - exists []. split; [constructor|]. split; constructor.
  - inversion HES as [|? ? He HES']; subst.
    destruct (p2_entry_rmid rc fx B API K sp Es Fs L A mem md L' A' mem' md' e FA HM R He
      (fun q Hq => KE q (in_or_app _ _ _ (or_introl Hq)))) as (e' & SB & EO').
    destruct p as [h j]. pose proof HP as (SRC & _). cbv zeta in SRC. cbn [fst snd] in SRC.
    assert (SRC' : src_at (rc := rc) B L' A' mem' (G_S + SRC_SIZE * Z.of_nat j) h).
    { apply (p2_src_rmid rc fx B API K sp Es Fs L A mem md L' A' mem' md' _ h FA SEG HK HM R SRC).
      - intros k Hk. exact (KS (h, j) k (or_introl eq_refl) Hk).
      - intros q Hq. apply KH. cbn [map concat fst]. apply in_or_app. left. exact Hq. }
    destruct (IH HES' (fun q Hq => KE q (in_or_app _ _ _ (or_intror Hq)))
      (fun q Hq => KH q (in_or_app _ _ _ (or_intror Hq))) (fun p0 k Hp Hk => KS p0 k (or_intror Hp) Hk))
      as (es' & F1 & F2 & F3).
    exists (e' :: es'). split; [constructor; assumption|]. split; [constructor; assumption|].
    constructor; [exact (p2_pair_sbs rc B L A mem L' A' mem' t e e' (h, j) HP SB SRC')|exact F3].
Qed.

Lemma p2_cost_cons : forall x b y d, slot_cost (x :: b) (y :: d) = pair_cost x y + slot_cost b d.
Proof. reflexivity. Qed.

Lemma p2_cost_app : forall a c x y b d, length a = length c ->
  slot_cost (a ++ x :: b) (c ++ y :: d) = slot_cost a c + pair_cost x y + slot_cost b d.
Proof.
  induction a as [|a0 a IH]; intros [|c0 c] x y b d HL; cbn [length] in HL; try discriminate.
  - cbn [app]. rewrite p2_cost_cons. change (slot_cost [] []) with 0. lia.
  - cbn [app]. rewrite !p2_cost_cons, (IH c x y b d ltac:(lia)). lia.
Qed.

Lemma p2_cost_sbs : forall l l' hj, Forall2 p2_sbs l l' -> slot_cost l' hj = slot_cost l hj.
Proof.
  intros l l' hj H. revert hj. induction H as [|e e' l l' HS H IH]; intros [|p hj]; try reflexivity.
  rewrite !p2_cost_cons, (p2_sbs_cost e e' p HS), IH. reflexivity.
Qed.

Lemma p2_sbs_maps : forall l l', Forall2 p2_sbs l l' ->
  map entry_blocks l' = map entry_blocks l /\ map entry_bytes l' = map entry_bytes l /\
  map re_fd l' = map re_fd l /\ length l' = length l.
Proof.
  intros l l' H. induction H as [|e e' l l' HS H (M1 & M2 & M3 & M4)]; [repeat split|].
  cbn [map length]. rewrite (p2_sbs_blocks e e' HS), (p2_sbs_bytes e e' HS), M1, M2, M3, M4.
  rewrite (proj1 HS). repeat split.
Qed.

Lemma p2_lines_len : forall st d, Z.of_nat (length (lines st d)) <= wcost st + Z.of_nat (length d).
Proof.
  intros st d. pose proof (lines_bytes d st) as LB. pose proof (lines_count (lines st d)) as LC.
  pose proof (wcost_nonneg (feed st d)). lia.
Qed.

Lemma p2_nozero : forall U : list byte, ~ In (Z_to_bv 8 0) U -> nozero (bzs U).
Proof.
  intros U H. unfold nozero, bzs. apply Forall_map. apply Forall_forall. intros b Hb E.
  apply H. replace b with (Z_to_bv 8 0) in Hb; [exact Hb|]. apply bz_inj. rewrite E, bz_lit by lia. reflexivity.
Qed.

Lemma p2_fin_no : forall live mx NO CAP rc B L A mem e h HA,
  RelayRep.entry_ok (rc := rc) B L A mem e -> src_at (rc := rc) B L A mem HA h ->
  re_skip e = hs_overlong h -> (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  ds_no (drain_fin live mx NO CAP e h) =
    NO + Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h))))).
Proof.
  intros live mx NO CAP rc B L A mem e h HA EO S SK WU.
  destruct EO as (_ & H2 & _ & _ & _ & CAP3 & UL & U6 & UZ & _).
  destruct S as (_ & _ & _ & _ & _ & LP & _ & PEND & _).
  apply relay_remove_b_aux.rma_fin_no.
  - unfold J1, hs_state. cbn [ls_k ls_w]. rewrite SK. split; [reflexivity|]. split.
    + intros X. apply WU. destruct H2 as [E0|E1]; [exact E0|]. rewrite <- SK, E1 in X. discriminate.
    + split; [|exact (p2_nozero _ UZ)]. rewrite bzs_length. unfold LINE_LIMIT.
      assert (LU : Z.of_nat (length (re_U e)) <= 6000) by (rewrite UL; exact U6).
      apply Nat2Z.inj_le. change (Z.of_nat 6000) with 6000. exact LU.
  - unfold relay_remove_b_aux.rma_pok, drain_init. cbn [ds_off ds_pend].
    destruct LP as (_ & _ & _ & _ & _ & FR).
    destruct PEND as [(E0 & O0)|(r & rs & E1 & O1)].
    + rewrite E0. cbn [map]. split; [lia|exact I].
    + rewrite E1 in FR |- *. cbn [map]. split; [lia|]. split; [rewrite bzs_length; lia|].
      inversion FR as [|? ? _ FR']; subst. apply Forall_map. eapply Forall_impl; [|exact FR'].
      intros r0 (_ & _ & _ & _ & X). cbv beta. rewrite bzs_length. apply X. reflexivity.
  - destruct CAP3 as [C|[C|C]]; [left|right|right]; lia.
Qed.

Lemma p2_lb_pos : forall rc B L A mem LA l lines, list_at (rc := rc) B L A mem LA l lines ->
  forall q, In q (list_blocks l) -> exists m, 0 < m /\ In (q, m) (blocks L A).
Proof.
  intros rc B L A mem LA l lines (_ & _ & AR & _ & _ & FR) q Hq. unfold list_blocks in Hq.
  apply in_app_or in Hq. destruct Hq as [Hq|Hq].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [C|C]; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct AR as [(C0 & _)|(Cp & IN & _)]; [lia|]. exists (16 * hl_cap l). split; [lia|exact IN].
  - apply in_map_iff in Hq. destruct Hq as (r & <- & Hr). rewrite Forall_forall in FR.
    destruct (FR r Hr) as (IN & _). exists (Z.of_nat (length (snd r)) + 1). split; [lia|exact IN].
Qed.

Lemma p2_hb_pos : forall rc B L A mem HA h, src_at (rc := rc) B L A mem HA h ->
  forall q, In q (hs_blocks h) -> exists m, 0 < m /\ In (q, m) (blocks L A).
Proof.
  intros rc B L A mem HA h (_ & _ & _ & _ & _ & LP & _ & _ & _ & _ & PIN & _ & _ & _ & _ & LE & LH & _) q Hq.
  unfold hs_blocks in Hq. apply in_app_or in Hq. destruct Hq as [Hq|Hq]; [exact (p2_lb_pos _ _ _ _ _ _ _ _ LP q Hq)|].
  apply in_app_or in Hq. destruct Hq as [[<-|[]]|Hq]; [exists 6000; split; [lia|exact PIN]|].
  apply in_app_or in Hq. destruct Hq as [Hq|Hq]; [exact (p2_lb_pos _ _ _ _ _ _ _ _ LE q Hq)|].
  exact (p2_lb_pos _ _ _ _ _ _ _ _ LH q Hq).
Qed.

Lemma p2_eb_pos : forall rc B L A mem e, RelayRep.entry_ok (rc := rc) B L A mem e ->
  forall q, In q (entry_blocks e) -> exists m, 0 < m /\ In (q, m) (blocks L A).
Proof.
  intros rc B L A mem e (_ & _ & _ & _ & _ & _ & _ & _ & _ & BUF & _ & HP & _ & _ & KS) q Hq.
  unfold entry_blocks in Hq. apply in_app_or in Hq. destruct Hq as [Hq|Hq].
  - destruct (Z.eqb_spec (re_cap e) 0) as [C|C]; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct BUF as [(C0 & _)|(Cp & IN & _)]; [lia|]. exists (re_cap e). split; [lia|exact IN].
  - apply in_app_or in Hq. destruct Hq as [Hq|Hq].
    + destruct (Z.eqb_spec (re_hp e) 0) as [C|C]; [destruct Hq|]. destruct Hq as [<-|[]].
      destruct HP as [(C0 & _)|(IN & _ & _ & K8 & _)]; [lia|]. exists (re_kh e). split; [lia|exact IN].
    + apply in_map_iff in Hq. destruct Hq as (k & <- & Hk). rewrite Forall_forall in KS.
      destruct (KS k Hk) as (IN & _). exists (Z.of_nat (length (key_text k)) + 1). split; [lia|exact IN].
Qed.

Lemma p2_outW : forall SP x lo hi, ~ outside [(SP - 96, SP); (lo, hi)] x -> (SP - 96 <= x < SP) \/ (lo <= x < hi).
Proof. intros SP x lo hi H. cbn [outside] in H. lia. Qed.

Lemma p2_bytes_nil : forall segs m a, 0 <= a < 2 ^ 64 -> bytes_at segs m a [].
Proof. intros segs m a Ha. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Lemma p2_rw_bytes1 : forall segs m a b, rw_cells segs m a [C1 b] -> bytes_at segs m a [b].
Proof. intros segs m a b ((_ & BY) & _). cbn [cells_bytes cbytes] in BY. exact BY. Qed.

Lemma p2_lb_v : forall l, hl_cap l <> 0 -> In (hl_v l) (list_blocks l).
Proof. intros l C. unfold list_blocks. rewrite (proj2 (Z.eqb_neq _ _) C). left. reflexivity. Qed.

Lemma p2_lb_recs : forall l q, In q (map fst (hl_recs l)) -> In q (list_blocks l).
Proof. intros l q H. unfold list_blocks. apply in_or_app. right. exact H. Qed.

Lemma p2_hb_exp : forall h q, In q (list_blocks (hs_expected h)) -> In q (hs_blocks h).
Proof. intros h q H. unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma p2_hb_held : forall h q, In q (list_blocks (hs_held h)) -> In q (hs_blocks h).
Proof. intros h q H. unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H. Qed.

Lemma p2_hb_pend : forall h q, In q (list_blocks (hs_pending h)) -> In q (hs_blocks h).
Proof. intros h q H. unfold hs_blocks. apply in_or_app. left. exact H. Qed.

Lemma p2_hb_part : forall h, In (hs_partial h) (hs_blocks h).
Proof. intros h. unfold hs_blocks. apply in_or_app. right. left. reflexivity. Qed.

Lemma p2_forall_sub : forall {X} (P : X -> Prop) n l, Forall P l -> Forall P (firstn n l) /\ Forall P (skipn n l).
Proof. intros X P n l H. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. exact H. Qed.

Definition p2_oth (es : list rentry) (hj : list (hsrc * nat)) (i : nat) : list Z :=
  concat (map entry_blocks (firstn i es)) ++ concat (map entry_blocks (skipn (S i) es)) ++
  concat (map (fun p => hs_blocks (fst p)) (firstn i hj)) ++ concat (map (fun p => hs_blocks (fst p)) (skipn (S i) hj)).

Lemma p2_oth_cnt : forall G OUT es hj i e h jj x,
  nth_error es i = Some e -> nth_error hj i = Some (h, jj) ->
  count_occ Z.eq_dec (target_addrs G OUT es hj) x =
    (count_occ Z.eq_dec (G :: OUT :: entry_blocks e ++ hs_blocks h) x + count_occ Z.eq_dec (p2_oth es hj i) x)%nat.
Proof. intros G OUT es hj i e h jj x He Hh. exact (p2_target_split G OUT es hj i e h jj He Hh x). Qed.

Lemma p2_oth_out : forall G OUT es hj i e h jj x,
  NoDup (target_addrs G OUT es hj) -> nth_error es i = Some e -> nth_error hj i = Some (h, jj) ->
  In x (p2_oth es hj i) -> ~ In x (G :: OUT :: entry_blocks e ++ hs_blocks h) /\ In x (target_addrs G OUT es hj).
Proof.
  intros G OUT es hj i e h jj x ND He Hh Hx. pose proof (p2_oth_cnt G OUT es hj i e h jj x He Hh) as C.
  apply p2_nd_cnt with (x := x) in ND. apply (count_occ_In Z.eq_dec) in Hx. split.
  - intros HX. apply (count_occ_In Z.eq_dec) in HX. lia.
  - apply (count_occ_In Z.eq_dec). lia.
Qed.

Lemma p2_TA_cases : forall G OUT es hj i e h jj x,
  nth_error es i = Some e -> nth_error hj i = Some (h, jj) -> In x (target_addrs G OUT es hj) ->
  In x (G :: OUT :: entry_blocks e ++ hs_blocks h) \/ In x (p2_oth es hj i).
Proof.
  intros G OUT es hj i e h jj x He Hh Hx. pose proof (p2_oth_cnt G OUT es hj i e h jj x He Hh) as C.
  apply (count_occ_In Z.eq_dec) in Hx.
  destruct (Nat.eq_dec (count_occ Z.eq_dec (G :: OUT :: entry_blocks e ++ hs_blocks h) x) 0) as [Z0|Z0].
  - right. apply (count_occ_In Z.eq_dec). lia.
  - left. apply (count_occ_In Z.eq_dec). lia.
Qed.

Lemma p2_oth_nd : forall G OUT es hj i e h jj, NoDup (target_addrs G OUT es hj) ->
  nth_error es i = Some e -> nth_error hj i = Some (h, jj) ->
  forall x, (count_occ Z.eq_dec (p2_oth es hj i) x <= 1)%nat.
Proof.
  intros G OUT es hj i e h jj ND He Hh x. pose proof (p2_oth_cnt G OUT es hj i e h jj x He Hh) as C.
  apply p2_nd_cnt with (x := x) in ND. lia.
Qed.

Lemma p2_nd_join : forall G OUT es hj i e h jj,
  nth_error es i = Some e -> nth_error hj i = Some (h, jj) ->
  NoDup (G :: OUT :: entry_blocks e ++ hs_blocks h) -> (forall x, (count_occ Z.eq_dec (p2_oth es hj i) x <= 1)%nat) ->
  (forall x, In x (p2_oth es hj i) -> ~ In x (G :: OUT :: entry_blocks e ++ hs_blocks h)) ->
  NoDup (target_addrs G OUT es hj).
Proof.
  intros G OUT es hj i e h jj He Hh N1 N2 D. apply p2_nd_cnt. intros x.
  rewrite (p2_oth_cnt G OUT es hj i e h jj x He Hh). apply p2_nd_cnt with (x := x) in N1. pose proof (N2 x) as N2x.
  destruct (Nat.eq_dec (count_occ Z.eq_dec (p2_oth es hj i) x) 0) as [Z0|Z0]; [lia|].
  assert (HI : In x (p2_oth es hj i)) by (apply (count_occ_In Z.eq_dec); lia).
  pose proof (D x HI) as NX. rewrite (count_occ_not_In Z.eq_dec) in NX. lia.
Qed.

Lemma p2_nd_split : forall (a b : Z) l1 l2, NoDup (a :: b :: l1 ++ l2) ->
  a <> b /\ ~ In a (l1 ++ l2) /\ ~ In b (l1 ++ l2) /\ NoDup l1 /\ NoDup l2 /\ (forall q, In q l1 -> ~ In q l2).
Proof.
  intros a b l1 l2 ND. apply NoDup_ListNoDup in ND.
  inversion ND as [|? ? Na ND1]; subst. inversion ND1 as [|? ? Nb ND2]; subst.
  split; [intros <-; apply Na; left; reflexivity|]. split; [intros X; apply Na; right; exact X|]. split; [exact Nb|].
  pose proof (proj1 (NoDup_count_occ Z.eq_dec _) ND2) as C.
  split; [apply NoDup_ListNoDup, (NoDup_count_occ Z.eq_dec); intros x; specialize (C x); rewrite count_occ_app in C; lia|].
  split; [apply NoDup_ListNoDup, (NoDup_count_occ Z.eq_dec); intros x; specialize (C x); rewrite count_occ_app in C; lia|].
  intros q H1 H2. specialize (C q). rewrite count_occ_app in C. apply (count_occ_In Z.eq_dec) in H1, H2. lia.
Qed.

Lemma p2_firstn_app : forall {X} (l1 l2 : list X) x, firstn (length l1) (l1 ++ x :: l2) = l1 /\
  skipn (S (length l1)) (l1 ++ x :: l2) = l2 /\ nth_error (l1 ++ x :: l2) (length l1) = Some x.
Proof.
  intros X l1 l2 x. split; [apply firstn_len_app|].
  split; [|apply p2_nth].
  rewrite <- (skipn_skipn 1 (length l1)), skipn_len_app. reflexivity.
Qed.

Lemma p2_oth_in : forall G OUT es hj i e h jj x, nth_error es i = Some e -> nth_error hj i = Some (h, jj) ->
  In x (p2_oth es hj i) -> In x (target_addrs G OUT es hj).
Proof.
  intros G OUT es hj i e h jj x He Hh Hx. pose proof (p2_oth_cnt G OUT es hj i e h jj x He Hh) as C.
  apply (count_occ_In Z.eq_dec) in Hx. apply (count_occ_In Z.eq_dec). lia.
Qed.

Lemma p2_mid_in : forall G OUT es hj i e h jj x, nth_error es i = Some e -> nth_error hj i = Some (h, jj) ->
  In x (G :: OUT :: entry_blocks e ++ hs_blocks h) -> In x (target_addrs G OUT es hj).
Proof.
  intros G OUT es hj i e h jj x He Hh Hx. pose proof (p2_oth_cnt G OUT es hj i e h jj x He Hh) as C.
  apply (count_occ_In Z.eq_dec) in Hx. apply (count_occ_In Z.eq_dec). lia.
Qed.

Lemma p2_len_firstn : forall {X} (l : list X) i, (i < length l)%nat -> length (firstn i l) = i.
Proof. intros X l i H. rewrite length_firstn. lia. Qed.

Lemma p2_repl_facts : forall {X} (l l' : list X) i y, length l' = i ->
  firstn i (l' ++ y :: l) = l' /\ skipn (S i) (l' ++ y :: l) = l /\ nth_error (l' ++ y :: l) i = Some y.
Proof. intros X l l' i y <-. exact (p2_firstn_app l' l y). Qed.

Lemma p2_oth_repl : forall es hj i pre' post' e' p', (i < length es)%nat -> (i < length hj)%nat ->
  Forall2 p2_sbs (firstn i es) pre' -> Forall2 p2_sbs (skipn (S i) es) post' ->
  p2_oth (pre' ++ e' :: post') (firstn i hj ++ p' :: skipn (S i) hj) i = p2_oth es hj i.
Proof.
  intros es hj i pre' post' e' p' Hes Hhj S1 S2.
  destruct (p2_sbs_maps _ _ S1) as (M1 & _ & _ & L1). destruct (p2_sbs_maps _ _ S2) as (M2 & _ & _ & _).
  rewrite (p2_len_firstn es i Hes) in L1.
  destruct (p2_repl_facts post' pre' i e' L1) as (F1 & F2 & _).
  destruct (p2_repl_facts (skipn (S i) hj) (firstn i hj) i p' (p2_len_firstn hj i Hhj)) as (F3 & F4 & _).
  unfold p2_oth. rewrite F1, F2, F3, F4, M1, M2. reflexivity.
Qed.

Lemma p2_nodup_fst : forall {X Y} (l : list (X * Y)) x a b, List.NoDup (map fst l) -> In (x, a) l -> In (x, b) l ->
  a = b.
Proof.
  intros X Y l. induction l as [|[y c] l IH]; intros x a b ND Ha Hb; [destruct Ha|].
  cbn [map fst] in ND. inversion ND as [|z l' Hn Hl]; subst.
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - injection Ea as E1 E2. injection Eb as E3 E4. congruence.
  - injection Ea as E1 E2. subst. exfalso. apply Hn. exact (in_map fst _ (x, b) Hb).
  - injection Eb as E3 E4. subst. exfalso. apply Hn. exact (in_map fst _ (x, a) Ha).
  - exact (IH x a b Hl Ha Hb).
Qed.

Lemma p2_block_size : forall rc fx B (API : AllocAPI B) L A mem md q m m',
  @frame_allocator rc fx B API -> aa_MR API L A mem md -> In (q, m) (blocks L A) -> In (q, m') (blocks L A) -> m = m'.
Proof.
  intros rc fx B API L A mem md q m m' FA HM H1 H2.
  assert (BN : blocks_nodup B API) by (unfold frame_allocator in FA; tauto).
  pose proof (BN L A mem md HM) as ND. apply NoDup_ListNoDup in ND. exact (p2_nodup_fst _ q m m' ND H1 H2).
Qed.

Lemma p2_cs : forall r, ((r =? 2) || (r =? 3) || (r =? 4) || (r =? 8) || (r =? 9) || ((18 <=? r) && (r <=? 27)))%bool = true ->
  callee_saved r.
Proof.
  intros r H. unfold callee_saved. repeat rewrite orb_true_iff in H. rewrite andb_true_iff in H.
  rewrite !Z.eqb_eq, !Z.leb_le in H. lia.
Qed.
