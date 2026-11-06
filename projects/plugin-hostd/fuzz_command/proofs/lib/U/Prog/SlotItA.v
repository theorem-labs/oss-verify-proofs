From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require KindBGlue BlocksNodup.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import AllocSI AllocGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU SlotSpec SlotGlue SlotRuns SlotCallees SlotIter SlotEnd SlotItBase SlotItSt verbs_receive_c send_message_c CommandB VerbsB CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Slot SlotInv SlotRec RecTail.
Import ListNotations.
Local Open Scope Z_scope.

(* The loop head 0x140fc of message m to the entry of the message handler (0x14444, returning to 0x141c4): the
   header of the message at cursor (p, n) decoded, g_rec.refuse and g_rec.code set (the recorder R0), g_rec.state
   and g_rec.host_settings in s2 and s3; then the handler's run on the message's bytes (stA). *)

Lemma it_not_out1 : forall lo hi a, ~ Frame.outside [(lo, hi)] a -> lo <= a < hi.
Proof. intros lo hi a H. cbn in H. lia. Qed.

Section A.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : Slot.frame_given_u B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (SlotInv.FB S).

(* The guard words and the GNU_RELRO bytes the checks read. *)
Lemma it_cmd : forall fx L A regs mem md, CF fx L A regs mem md -> cmd_mem B mem.
Proof.
  intros fx L A regs mem md (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RO & GI & _).
  assert (SEGS : ms_segs B = rsegs) by (eapply it_SEGS; eassumption).
  destruct (it_vrt B API LS SH SK ra empty FG fx L A mem md HM GI) as (can & _ & _ & _ & VG).
  destruct (it_FA B API LS SH SK ra empty FG fx)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GRW & _).
  pose proof FG as FG'. fg_destruct FG'.
  unfold cmd_mem. split; [rewrite SEGS; exact RO|]. split; [exact GI|]. split; [exists can; exact VG|].
  intros i Hi. destruct (GRW L A mem md i HM Hi) as [_ W]. rewrite F7 in W. exact W.
Qed.

(* The entry blocks: no duplicates, at most 64 of them with at most 2^28 bytes (the entry bound b). *)
Lemma it_E : forall fx : FPState,
  List.NoDup (blocks L0 A0) /\ Z.of_nat (length (blocks L0 A0)) <= 64 /\ SlotInv.bsum (blocks L0 A0) <= 2 ^ 28.
Proof.
  intros fx. pose proof PRE as ((HM0 & _) & _ & _ & RES0 & ROOM0 & _).
  pose proof FG as FG'. fg_destruct FG'.
  destruct (F29 b n0 ROOM0) as (B1 & B2 & B3).
  destruct RES0 as (_ & _ & _ & _ & _ & _ & N1 & N2 & _).
  pose proof (SlotInv.nblocks_blocks L0 A0). pose proof (SlotInv.ubytes_blocks L0 A0).
  split; [exact (it_NODUP B API LS SH SK ra empty FG fx L0 A0 mem0 md0 HM0) | lia].
Qed.

Lemma it_tb_range : forall (L : layout) A, WF A -> 0 <= nblocks A /\ 0 <= ubytes A.
Proof.
  intros L A HW. rewrite (SlotInv.nblocks_blocks L A), (SlotInv.ubytes_blocks L A).
  pose proof (SlotInv.bsum_nonneg _ (SlotInv.blocks_nonneg L A HW)). lia.
Qed.

(* Room for a call: the live blocks are the entry blocks, the recorder's O and at most 3 blocks X of the
   message. *)
Lemma it_room : forall (fx : FPState) L A mem md O X, aa_MR (API rc) L A mem md -> WF A -> SlotInv.eblocks mem0 L0 A0 L A mem ->
  (forall pn, In pn (blocks L A) -> In pn (blocks L0 A0) \/ In pn O \/ In pn X) ->
  (length O <= SlotInv.O_MAX)%nat -> (forall pn, In pn O -> 0 <= snd pn <= LMAX + 2) ->
  (length X <= 3)%nat -> (forall pn, In pn X -> 0 <= snd pn <= 2 ^ 16) ->
  forall b2, sb_cap b2 = CAPMAX -> 0 <= sb_live b2 <= nblocks A + 200 -> 0 <= sb_bytes b2 <= ubytes A + 2 ^ 22 ->
  forall r, 0 <= r <= 2 ^ 22 -> room_slots b2 r.
Proof.
  intros fx L A mem md O X HM HW EB HB HO HOs HX HXs b2 Hc Hl Hb r Hr.
  destruct (it_E fx) as (E1 & E2 & E3).
  apply (SlotInv.room_tb L A (blocks L0 A0) O X b2 HW (it_NODUP B API LS SH SK ra empty FG fx L A mem md HM) E1);
    try assumption.
  - intros [a k] H. exact (proj1 (EB a k H)).
  - intros pn H. destruct (HB pn H) as [H1|[H1|H1]]; [left; exact H1 | right; apply in_or_app; tauto | right; apply in_or_app; tauto].
Qed.

Lemma it_fst_nodup : forall (fx : FPState) L A mem md, aa_MR (API rc) L A mem md -> List.NoDup (map fst (blocks L A)).
Proof.
  intros fx L A mem md HM. destruct (it_FA B API LS SH SK ra empty FG fx) as (_ & _ & _ & _ & _ & _ & _ & _ & H & _).
  exact (proj1 (stdpp.base.NoDup_ListNoDup _) (H L A mem md HM)).
Qed.

Lemma it_fst_eq : forall (l : list (Z * Z)) a k k', List.NoDup (map fst l) -> In (a, k) l -> In (a, k') l -> k = k'.
Proof.
  induction l as [|[a0 k0] l IH]; intros a k k' ND H1 H2; [destruct H1|].
  cbn [map fst] in ND. apply NoDup_cons_iff in ND as [NI ND].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - congruence.
  - injection E1 as <- <-. exfalso. apply NI. apply in_map_iff. exists (a0, k'). split; [reflexivity | exact H2].
  - injection E2 as <- <-. exfalso. apply NI. apply in_map_iff. exists (a0, k). split; [reflexivity | exact H1].
  - exact (IH a k k' ND H1 H2).
Qed.

(* A block's bytes lie below the allocation ceiling, outside the image (0x10000 .. 0x55000). *)
Lemma it_blk_out : forall (fx : FPState) L A mem md a k i, aa_MR (API rc) L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  ~ (0x10000 <= a + i < 0x55000) /\ 4096 <= a /\ a + k <= alloc_ceiling.
Proof.
  intros fx L A mem md a k i HM Hin Hi.
  assert (AX : AllocExtra B (aa_MR (API rc))) by exact (it_AX B API LS SH SK ra empty FG fx).
  assert (SEGS : ms_segs B = rsegs) by (eapply it_SEGS; eassumption).
  destruct (KindB.block_facts B _ (aa_laws (API rc)) L A mem md a k i HM Hin Hi) as (_ & Q1 & Q2 & _).
  split; [|lia]. intros Hx.
  unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & E & Hq). injection E as Ea Ek. subst a k'.
  exact (ax_blocks_img AX L A mem md q k i HM Hq Hi (send_message.sm_img_iv B _ SEGS Hx)).
Qed.

Lemma it_vrw_G : forall a, vr_writes a -> 0x33ff0 <= a < 0x343ec.
Proof.
  intros a H. unfold vr_writes in H.
  unfold RecInvU.G_REC, CommandModel.G_REC, REC_SIZE, RecInvU.REC_SC, SC_SIZE, VerbsB.G_QUIT, CommandModel.G_QUIT in *.
  lia.
Qed.

(* The locals of the frame (FB .. FB + 56) survive a call made at the frame base. *)
Lemma it_frame_cells : forall fx L A regs mem md K (E : Z -> Prop) L' A' mem' md' a0 cs,
  CF fx L A regs mem md -> aa_MR (API rc) L' A' mem' md' ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
     ~ scratch_k B K regs a -> ~ E a ->
     mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)) ->
  (forall a, E a -> a < alloc_ceiling) ->
  FB <= a0 -> a0 + Z.of_nat (cells_size cs) <= FB + 56 ->
  rw_cells rsegs mem a0 cs -> rw_cells rsegs mem' a0 cs.
Proof.
  intros fx L A regs mem md K E L' A' mem' md' a0 cs HCF HM' HF HE H1 H2 HC.
  pose proof HCF as (HM & _ & _ & _ & _ & R2 & _).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  assert (SP : spZ regs = FB) by (eapply it_spz; eassumption).
  assert (EV : errno_addr B = 0x3441c) by (eapply it_errno; eassumption).
  pose proof alloc_ceiling_val as AC.
  apply (KindB.rw_cells_transfer rsegs mem mem' _ _ HC). intros i Hi.
  assert (Ha : alloc_ceiling <= a0 + i < 2 ^ 64) by (unfold SlotInv.FB, SLOT_STACK in *; lia).
  destruct (HF (a0 + i) (or_introl Ha)) as [E1 W1].
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws (API rc)) L A mem md _ HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws (API rc)) L' A' mem' md' _ HM' Ho). lia.
  - unfold scratch_k. rewrite SP, EV. lia.
  - intros Hx. pose proof (HE _ Hx). lia.
  - split; [exact E1 | tauto].
Qed.

Definition atSM (m p n : Z) (R0 : rstate) (c : config) : Prop :=
  exists (fx : FPState) L A regs mem md O q,
    c = mkCfg (@mkst fx regs (Z_to_bv 64 0x14444) mem (seg_rom rsegs)) md /\
    CF fx L A regs mem md /\ SlotInv.rcap A /\ SlotInv.RF L0 A0 L A mem R0 O q /\ (length O <= SlotInv.O_MAX)%nat /\
    (r_refuse R0 <> 0 -> declared (r_code R0) = true) /\
    getr regs 1 = Z_to_bv 64 0x141c4 /\ getr regs 10 = Z_to_bv 64 (m_src p n) /\
    getr regs 11 = Z_to_bv 64 (m_len p0 pl p n) /\
    LR p0 n0 pl m p n regs mem /\
    getr regs 18 = Z_to_bv 64 (r_state R0) /\ getr regs 19 = Z_to_bv 64 (r_host R0) /\
    rw_cells rsegs mem FB (LOC1 (n - hdr_n n)) /\ (exists jw, rw_cells rsegs mem (FB + 24) [CB 32 jw]).

Lemma ia_not_out2 : forall lo1 hi1 lo2 hi2 a, ~ Frame.outside [(lo1, hi1); (lo2, hi2)] a ->
  lo1 <= a < hi1 \/ lo2 <= a < hi2.
Proof. intros lo1 hi1 lo2 hi2 a H. cbn in H. lia. Qed.

Lemma ia_head : forall m c, head_at B (API rc) S rg mem0 md0 L0 A0 p0 n0 m c ->
  SR rsegs c (fun c' => exists p n R0, atSM m p n R0 c').
Proof.
  intros m c (fx & p & n & L & A & regs & mem & md & R & O & q & -> & HI).
  destruct HI as (HCF & HRF & HRC & HOL & H23 & H18 & H9 & H24 & H25 & H27 & H12 & H13 & H14 &
    (jsv & jw & LC0 & LC1) & Hm & Hn & Hp & Hpn).
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRF as (REP & SPILL & QB & Hq & ENO & BLK).
  assert (SEGS : ms_segs B = rsegs) by (eapply it_SEGS; eassumption).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  pose proof alloc_ceiling_val as AC.
  destruct (it_model B API S rg mem0 md0 L0 A0 fx L A regs mem md HCF) as [Hh Hl].
  assert (Hn0 : 0 < n0) by lia.
  destruct (it_inblk B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0)
    as (_ & _ & Hp04 & Hpac & HL & _).
  pose proof (it_in_bytes B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0
     (p - p0) (hdr_n n) ltac:(lia) ltac:(unfold hdr_n; lia) ltac:(unfold hdr_n; lia)) as HB.
  replace (p0 + (p - p0)) with p in HB by lia.
  change (firstn (Z.to_nat (hdr_n n)) (skipn (Z.to_nat (p - p0)) pl)) with (m_hdr p0 pl p n) in HB.
  pose proof (m_hdr_len p0 n0 pl p n Hn Hp Hpn HL) as HHL.
  destruct (it_rep_parts L A mem R O REP) as [(G0 & G1 & G2 & G3 & G4) (X1 & X2 & X3 & X4 & X5 & X6)].
  assert (GRC : rw_cells rsegs mem G_REC [CB 8 (le4 (Z_to_bv 64 (r_refuse R)) ++ le4 (Z_to_bv 64 (r_code R)))]).
  { split; [split|].
    - split; [cbn [cell_wf]; rewrite length_app, !length_le4; reflexivity | exact Logic.I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
      + unfold OFF_REFUSE in X1. rewrite Z.add_0_r in X1. exact X1.
      + rewrite length_le4. exact X2.
    - cbn [cells_size csize]. apply SlotRec.g_wr_at; unfold G_REC; lia. }
  assert (SPV : bv_unsigned (reg_get regs 2) = FB).
  { change (reg_get regs 2) with (getr regs 2). rewrite R2. apply unsigned_lit.
    unfold SlotInv.FB, SLOT_STACK in *. lia. }
  pose proof (KindB.rw_cells_normalize rsegs _ _ _ RO LC0) as LC0n.
  pose proof (KindB.rw_cells_normalize rsegs _ _ _ RO GRC) as GRCn.
  eapply (@sr_run fx regs (Z_to_bv 64 0x140fc) mem md _ _ Hh Hl RO).
  { unfold Regs6ss.mkR_of.
    assert (E9 : reg_get regs 9 = Z_to_bv 64 n) by exact H9.
    assert (E12 : reg_get regs 12 = Z_to_bv 64 1) by exact H12.
    assert (E13 : reg_get regs 13 = Z_to_bv 64 58) by exact H13.
    assert (E14 : reg_get regs 14 = Z_to_bv 64 G_REC) by exact H14.
    assert (E18 : reg_get regs 18 = Z_to_bv 64 p) by exact H18.
    assert (E23 : reg_get regs 23 = Z_to_bv 64 m) by exact H23.
    assert (E24 : reg_get regs 24 = Z_to_bv 64 MASK) by exact H24.
    assert (E25 : reg_get regs 25 = Z_to_bv 64 32) by exact H25.
    assert (E27 : reg_get regs 27 = Z_to_bv 64 (2 ^ 64 - 1)) by exact H27.
    rewrite E9, E12, E13, E14, E18, E23, E24, E25, E27.
    eapply run_head_ok.
    - apply mem_inv_normalize.
    - rewrite SPV. unfold SlotInv.FB, SLOT_STACK, IMG_END in *. lia.
    - rewrite SPV. unfold SlotInv.FB in *. lia.
    - lia.
    - lia.
    - lia.
    - apply bytes_at_normalize; [exact RO | exact HB].
    - exact HHL.
    - rewrite SPV. apply LC0n. intros i Hi. apply ro_addr_hi. unfold LOC0 in Hi. cbn in Hi.
      unfold SlotInv.FB, SLOT_STACK in *. lia.
    - apply GRCn. intros i Hi. cbn in Hi. apply se_g_not_ro. unfold G_REC. lia.
    - apply bytes_at_normalize; [exact RO | exact X4].
    - apply bytes_at_normalize; [exact RO | exact X5]. }
  { intros s0 (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
    do 5 eexists. reflexivity. }
  intros R' F' pc' fc' m0' regs2 mem2
    (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI & RCC & RLC)
    REL ROS GR.
  injection E as ER EF Epc Efc Em. subst R' F' pc' fc' m0'.
  rewrite SPV in MU, RLC.
  apply SR_ret.
  pose proof (mem_rel_normalize rsegs mem RO) as REL0.
  assert (MU2 : munch [(G_REC, G_REC + 8); (FB + 16, FB + 24)] mem mem2)
    by exact (munch_rel rsegs _ _ _ _ _ REL0 REL ROS MU).
  assert (WM2 : wmono rsegs mem mem2) by exact (wmono_rel rsegs _ _ _ _ REL0 REL ROS WM).
  assert (RO2 : ro_agree rsegs mem2) by exact (ro_agree_same rsegs _ _ RO ROS).
  pose proof (KindB.rw_cells_of_rel rsegs _ _ _ _ REL RCC) as RCC2.
  pose proof (KindB.rw_cells_of_rel rsegs _ _ _ _ REL RLC) as RLC2.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (G_REC <= a < G_REC + 8) -> ~ (FB + 16 <= a < FB + 24) ->
     mbyte rsegs mem2 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem2 a)).
  { intros a Ha Hx1 Hx2.
    assert (Ho : Frame.outside [(G_REC, G_REC + 8); (FB + 16, FB + 24)] a)
      by (cbn; split; [exact Hx1 | split; [exact Hx2 | exact Logic.I]]).
    split; [exact (KindB.munch_mbyte rsegs _ _ _ a MU2 Ha Ho) | exact (KindB.munch_writable rsegs _ _ _ a MU2 Ha Ho)]. }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (eapply it_AX; eassumption).
  assert (GFREE : forall a, in_globals SlotInv.G_cmd a -> in_img B a /\ ~ static_owned B a /\
    ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4))
    by (eapply it_GFREE; eassumption).
  assert (CF2 : CF (mkFP fp_regs fp_csr) L A regs2 mem2 md).
  { apply (it_cf_run B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx _ L A regs mem md
             [(G_REC, G_REC + 8); (FB + 16, FB + 24)] mem2 regs2 HCF MU2 WM2 RO2).
    - intros a Ha Hx. apply ia_not_out2 in Hx. destruct Hx as [Hx|Hx].
      + right. left. apply se_g_of. unfold G_REC in Hx. lia.
      + left. unfold SlotInv.FB, SLOT_STACK in *. lia.
    - intros p1 n1 i Hin Hi Hx. exfalso. apply ia_not_out2 in Hx.
      assert (Hb : In (ptr_addr L p1, n1) (blocks L A))
        by (unfold blocks; apply in_map_iff; exists (p1, n1); split; [reflexivity | exact Hin]).
      destruct (KindB.block_facts B _ (aa_laws (API rc)) L A mem md _ n1 i M Hb Hi) as (_ & Q1 & Q2 & _).
      destruct Hx as [Hx|Hx].
      + apply (ax_blocks_img AX L A mem md p1 n1 i M Hin Hi).
        unfold G_REC in Hx.
        exact (proj1 (GFREE (ptr_addr L p1 + i) (se_g_of (ptr_addr L p1 + i) ltac:(lia)))).
      + unfold SlotInv.FB, SLOT_STACK in *. lia.
    - exact FZ.
    - rewrite GR. reflexivity.
    - rewrite GR. reflexivity.
    - rewrite GR. reflexivity. }
  assert (Hrf : -2^31 <= msg_rf (m_hdr p0 pl p n) < 2^31).
  { unfold msg_rf. pose proof (Z.mod_pos_bound (hbyte (m_hdr p0 pl p n) 0) 2). lia. }
  assert (Hk : (Z.to_nat ((hbyte (m_hdr p0 pl p n) 0 / 2) mod 58) < 58)%nat).
  { pose proof (Z.mod_pos_bound (hbyte (m_hdr p0 pl p n) 0 / 2) 58). lia. }
  destruct (SlotRec.codes_declared _ Hk) as [DCD Hcd].
  destruct RCC2 as [[_ RB] _]. cbn [cells_bytes cbytes] in RB. rewrite app_nil_r in RB.
  apply bytes_at_app in RB as [RB1 RB2]. rewrite length_le4 in RB2.
  assert (HBo : forall pn, In pn O -> 0 <= fst pn /\ fst pn + snd pn <= alloc_ceiling).
  { intros [q1 k1] Hin. destruct (it_rec_blk rsegs L A mem R O (q1, k1) REP Hin) as [Hb Hk1]. cbn [fst snd] in *.
    destruct (KindB.block_facts B _ (aa_laws (API rc)) L A mem md q1 k1 0 M Hb ltac:(lia)) as (_ & Q1 & Q2 & _).
    lia. }
  assert (KLO : forall a, 0 <= a < alloc_ceiling -> ~ (0x34028 <= a < 0x34028 + 8) -> mbyte rsegs mem2 a = mbyte rsegs mem a).
  { intros a Ha Hx. pose proof alloc_ceiling_lt as ACL.
    apply (K2 a); [lia | unfold G_REC; lia | unfold SlotInv.FB, SLOT_STACK in *; lia]. }
  pose proof (it_set_rc_lo L A mem mem2 R O (msg_rf (m_hdr p0 pl p n)) (msg_cd (m_hdr p0 pl p n)) REP Hrf Hcd RB1 RB2
    KLO HBo) as REP2.
  exists p, n.
  eexists. exists (mkFP fp_regs fp_csr), L, A, regs2, mem2, md, O, q.
  split; [reflexivity|]. split; [exact CF2|]. split; [exact HRC|].
  split.
  { refine (conj REP2 (conj _ (conj _ (conj Hq (conj ENO BLK))))).
    - cbn [r_spill]. exact SPILL.
    - apply (KindB.bytes_at_transfer rsegs mem mem2 _ _ QB). intros i Hi. rewrite length_le4 in Hi.
      apply K2; unfold G_QUIT, G_REC, SlotInv.FB, SLOT_STACK in *; lia. }
  split; [exact HOL|].
  split; [intros _; exact DCD|].
  split; [rewrite GR; reflexivity|].
  split; [rewrite GR; reflexivity|].
  split; [rewrite GR; reflexivity|].
  split.
  { unfold LR. do 8 (split; [rewrite GR; reflexivity|]). lia. }
  split; [rewrite GR; reflexivity|].
  split; [rewrite GR; reflexivity|].
  split; [exact RLC2|].
  exists jw.
  apply (KindB.rw_cells_transfer rsegs mem mem2 _ _ LC1). intros i Hi. cbn in Hi.
  destruct (K2 (FB + 24 + i)) as [E1 W1]; [unfold SlotInv.FB, SLOT_STACK in *; lia | unfold G_REC, SlotInv.FB, SLOT_STACK in *; lia | lia |].
  split; [exact E1 | tauto].
Qed.

Ltac pres P H r := exact (eq_trans (P r ltac:(unfold callee_saved; lia)) H).

(* The message handler on the message's bytes: the recorder holds its run on R0, the harness facts hold. *)
Lemma ia_send : (forall fx : FPState, @send_message_contract fx rc B (API rc)) -> harness_props ->
  forall m p n R0 c, atSM m p n R0 c -> SR rsegs c (stA B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0).
Proof.
  intros SMC HPR m p n R0 c
    (fx & L & A & regs & mem & md & O & q & -> & HCF & HRC & HRF & HOL & DCL & G1 & G10 & G11 & HLR & G18 & G19 &
     LC0 & (jw & LC1)).
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRF as (REP & SPILL & QB & Hq & ENO & BLK).
  pose proof HLR as (L8 & L9 & L23 & L22 & L26 & L24 & L25 & L27 & Hm & Hn & Hp & Hpn).
  assert (SEGS : ms_segs B = rsegs) by (eapply it_SEGS; eassumption).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  assert (TS : S <= TASK_SIZE) by (eapply it_TS; eassumption).
  assert (SP : spZ regs = FB) by (eapply it_spz; eassumption).
  assert (EV : errno_addr B = 0x3441c) by (eapply it_errno; eassumption).
  pose proof alloc_ceiling_val as AC.
  assert (Hn0 : 0 < n0) by lia.
  destruct (it_inblk B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0)
    as (IB & IB0 & Hp04 & Hpac & HL & _).
  pose proof (m_len_range p0 pl p n Hn) as [HL1 HL2].
  pose proof (m_D_len p0 n0 pl p n Hn Hp Hpn HL) as HDL.
  assert (HSRC : 0 <= m_src p n - p0) by (unfold m_src, hdr_n; lia).
  pose proof (it_in_bytes B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0
     (m_src p n - p0) (m_len p0 pl p n) HSRC ltac:(lia) ltac:(unfold m_src in *; lia)) as HD.
  replace (p0 + (m_src p n - p0)) with (m_src p n) in HD by lia.
  change (firstn (Z.to_nat (m_len p0 pl p n)) (skipn (Z.to_nat (m_src p n - p0)) pl)) with (m_D p0 pl p n) in HD.
  pose proof (it_cmd fx L A regs mem md HCF) as CMD.
  destruct (it_vrt B API LS SH SK ra empty FG fx L A mem md M GIm) as (can & VT).
  assert (PREK : call_pre_t B (API rc) SM_K L A regs mem md).
  { split.
    - apply (it_pre B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx L A regs mem md SM_K HCF).
      + rewrite G1. apply YK0s.ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
      + unfold SM_K, SEND_MESSAGE_FRAME, VR_K, SLOT_STACK. lia.
    - rewrite SP. unfold SlotInv.FB. lia. }
  assert (QOUT : outside B L A SM_K regs G_QUIT 4).
  { intros i Hi. split.
    - apply (it_GNOWN B API LS SH SK ra empty FG fx L A mem md _ M). apply se_g_of. unfold G_QUIT. lia.
    - unfold scratch_k. rewrite SP, EV.
      unfold SlotInv.FB, SLOT_STACK, G_QUIT, SM_K, SEND_MESSAGE_FRAME, VR_K in *. lia. }
  assert (RSL : forall pn, In pn O -> 0 <= snd pn <= LMAX + 2).
  { intros pn Hin. pose proof (it_rec_blk rsegs L A mem R0 O pn REP Hin). lia. }
  assert (ROOM : room_slots (sb_up (SlotInv.tb A) SM_PEAK SM_PEAKB) VR_REQ).
  { pose proof (it_tb_range L A Wf) as [T1 T2].
    apply (it_room fx L A mem md O [] M Wf EB
             (fun pn H => match BLK pn H with or_introl H1 => or_introl H1 | or_intror H1 => or_intror (or_introl H1) end)
             HOL RSL ltac:(cbn; lia) (fun pn H => False_ind _ H)).
    - reflexivity.
    - unfold sb_up, SlotInv.tb, SM_PEAK. cbn. lia.
    - unfold sb_up, SlotInv.tb, SM_PEAKB. cbn. lia.
    - unfold VR_REQ. lia. }
  assert (H10 : m_len p0 pl p n <> 0 -> 4096 <= m_src p n /\ m_src p n + m_len p0 pl p n <= 2 ^ 64 /\
      in_live L A O (m_src p n) (m_len p0 pl p n) /\
      forall i, 0 <= i < m_len p0 pl p n -> ~ vr_writes (m_src p n + i) /\ ~ scratch_k B SM_K regs (m_src p n + i)).
  { intros _. unfold m_src in *. split; [lia|]. split; [lia|]. split.
    - exists p0, n0. split; [exact IB|]. split; [exact (ENO p0 n0 IB0)|]. lia.
    - intros i Hi. destruct (it_blk_out fx L A mem md p0 n0 (p + hdr_n n - p0 + i) M IB ltac:(lia)) as (NO & _ & _).
      split.
      + intros Hw. pose proof (it_vrw_G _ Hw). apply NO. lia.
      + unfold scratch_k. rewrite SP, EV. unfold SlotInv.FB, SLOT_STACK, SM_K, SEND_MESSAGE_FRAME, VR_K in *.
        intros [Hx|Hx]; [lia | apply NO; lia]. }
  pose proof (SMC fx) as SM. unfold send_message_contract in SM.
  specialize (SM L A regs mem md (SlotInv.tb A) R0 O (m_src p n) (m_len p0 pl p n) q (m_D p0 pl p n) can).
  rewrite SEGS in SM.
  specialize (SM eq_refl PREK CMD FZ G10 G11 (send_message.sm_le_of_bytes B mem _ _ SEGS HD) HDL ltac:(lia) H10 REP DCL
    (send_message.sm_le_of_bytes B mem _ _ SEGS QB)
    (fun i Hi => SlotRec.g_writable mem (G_QUIT + i) ltac:(unfold G_QUIT; lia)) QOUT VT
    (SlotInv.res_tb L A Wf HRC) ROOM).
  unfold SEND_MESSAGE in SM.
  eapply SR_bind; [exact SM|]. clear SM.
  intros c1 (fx1 & L1 & A1 & regs1 & mem1 & md1 & O1 & b1 & -> & FZ1 & RGN1 & POST & CMD1 & VR & DLE1 & BLK1 & STAY1 &
    NOTO1 & KEPT1 & INIT1 & (can1 & VT1) & RES1 & CAP1).
  destruct POST as (M1 & W1 & Bd1 & LLE1 & PA1 & PRES & (vm1 & Hmd1) & FRAME & BYTES & SCRW).
  destruct (vr_run (rec_clear R0) (m_D p0 pl p n)) as [[R1 x] quit] eqn:EVR.
  destruct VR as (REP1 & QL1).
  pose proof (SlotRec.vr_keep R0 (m_D p0 pl p n)) as VK. rewrite EVR in VK. destruct VK as (VK1 & VK2 & VK3).
  destruct (SlotRec.rep_dedup rsegs L1 A1 mem1 R1 O1 REP1) as (O2 & O2E & O2L & REP2).
  pose proof CMD1 as (RO1 & GI1 & _). rewrite SEGS in RO1.
  pose proof FRAME as FRAMEr. rewrite SEGS in FRAMEr.
  apply SR_ret.
  assert (EB1 : SlotInv.eblocks mem0 L0 A0 L1 A1 mem1).
  { intros a k Hin. destruct (EB a k Hin) as [Hb Hk]. split.
    - exact (STAY1 (a, k) Hb (ENO a k Hin)).
    - intros i Hi. rewrite <- (Hk i Hi).
      assert (NOB : ~ owned_by O a).
      { intros (k' & Hk'). apply (ENO a k Hin). apply in_map_iff. exists (a, k'). split; [reflexivity | exact Hk']. }
      pose proof (KEPT1 a k i Hb NOB Hi) as KK. rewrite SEGS in KK. exact KK. }
  assert (CF1 : CF fx1 L1 A1 regs1 mem1 md1).
  { apply (it_cf_call B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx fx1 SM_K L A regs mem md
             vr_writes L1 A1 regs1 mem1 md1 regs1 HCF M1 W1 Bd1 (INIT1 I) PRES (ex_intro _ vm1 Hmd1)).
    - exact FRAME.
    - exact SCRW.
    - unfold SlotInv.FB, SM_K, SEND_MESSAGE_FRAME, VR_K, SLOT_STACK. lia.
    - unfold SM_K, SEND_MESSAGE_FRAME, VR_K. lia.
    - intros a Ha. left. apply se_g_of. exact (it_vrw_G a Ha).
    - exact RO1.
    - exact GI1.
    - exact EB1.
    - exact FZ1.
    - intros r. reflexivity. }
  exists fx1, L1, A1, regs1, mem1, md1, O2, R1, x, quit.
  split; [rewrite G1; reflexivity|].
  split; [exact CF1|].
  split; [exists b1; split; [exact RES1 | rewrite CAP1; reflexivity]|].
  split; [exact EVR|].
  split.
  { unfold RFX. split; [exact REP2|]. split; [rewrite VK3; exact SPILL|].
    split.
    { apply (send_message.sm_bytes_of_le B mem1 _ _ SEGS); [unfold G_QUIT; lia | rewrite length_le4; unfold G_QUIT; lia |].
      exact QL1. }
    split; [unfold qv; destruct quit; lia|].
    split.
    - intros a k Hin Ha. apply in_map_iff in Ha as ([a' k'] & Ea & Hk'). cbn in Ea. subst a'.
      apply O2E in Hk'. destruct (it_rec_blk rsegs L1 A1 mem1 R1 O1 (a, k') REP1 Hk') as [Hb' _].
      destruct (EB1 a k Hin) as [Hb1 _].
      pose proof (it_fst_eq _ a k k' (it_fst_nodup fx1 L1 A1 mem1 md1 M1) Hb1 Hb') as Ek. subst k'.
      destruct (EB a k Hin) as [Hb _].
      exact (NOTO1 (a, k) Hb (ENO a k Hin) Hk').
    - split.
      + intros pn Hpb. destruct (BLK1 pn Hpb) as [[Hp1 Hn1]|Hp1].
        * destruct (BLK pn Hp1) as [H|H]; [left; exact H | contradiction].
        * right. left. apply O2E. exact Hp1.
      + split; [intros pn []|]. unfold SlotInv.O_MAX. exact O2L. }
  split.
  { unfold LR.
    split; [pres PRES L8 8|]. split; [pres PRES L9 9|]. split; [pres PRES L23 23|]. split; [pres PRES L22 22|].
    split; [pres PRES L26 26|]. split; [pres PRES L24 24|]. split; [pres PRES L25 25|]. split; [pres PRES L27 27|].
    lia. }
  split; [pres PRES G18 18|].
  split; [pres PRES G19 19|].
  split.
  { apply (it_frame_cells fx L A regs mem md SM_K vr_writes L1 A1 mem1 md1 FB _ HCF M1 FRAMEr).
    - intros a Ha. pose proof (it_vrw_G a Ha). lia.
    - lia.
    - unfold LOC1. cbn. lia.
    - exact LC0. }
  split.
  { exists jw. apply (it_frame_cells fx L A regs mem md SM_K vr_writes L1 A1 mem1 md1 (FB + 24) _ HCF M1 FRAMEr).
    - intros a Ha. pose proof (it_vrw_G a Ha). lia.
    - lia.
    - cbn. lia.
    - exact LC1. }
  destruct (it_rep_parts L A mem R0 O REP) as [_ (_ & _ & _ & _ & _ & X6)].
  split.
  { apply HPR; [| lia | lia | exact DCL].
    apply Nat2Z.inj_le. rewrite HDL. change (Z.of_nat (Init.Nat.of_num_uint _)) with 8192. lia. }
  split; [exact DCL | lia].
Qed.

End A.
