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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU SlotSpec SlotGlue SlotRuns SlotCallees SlotIter SlotEnd SlotItBase SlotItSt verbs_receive_c send_message_c CommandB VerbsB CommandModel SlotItA SlotItE strnlen_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Slot SlotInv SlotRec RecTail RecAnsB SlotWords RecAns.
Import ListNotations.
Local Open Scope Z_scope.

(* From stA (the message handler returned, pc 0x141c4) to the third malloc's return (pc 0x14200): the length of
   the message's line (strnlen), then the three blocks text, copy (L0 + 1 bytes) and the pointer array. *)

Section B.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : Slot.frame_given_u B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (SlotInv.FB S).

(* A new block (res, sz) is not among the blocks before the call. *)
Lemma ib_new : forall (fx : FPState) L' A' mem' md' b1 b2 res sz k, aa_MR (API rc) L' A' mem' md' ->
  blocks L' A' = b1 ++ (res, sz) :: b2 -> In (res, k) (b1 ++ b2) -> False.
Proof.
  intros fx L' A' mem' md' b1 b2 res sz k HM E Hin.
  pose proof (it_fst_nodup B API LS SH SK ra empty FG fx L' A' mem' md' HM) as ND.
  pose proof (it_NODUP B API LS SH SK ra empty FG fx L' A' mem' md' HM) as ND2.
  assert (H1 : In (res, k) (blocks L' A')) by (rewrite E; exact (RecAnsB.in_mid_inv b1 b2 _ _ Hin)).
  assert (H2 : In (res, sz) (blocks L' A')) by (rewrite E; apply in_or_app; right; left; reflexivity).
  pose proof (it_fst_eq _ _ _ _ ND H1 H2) as ->.
  rewrite E in ND2. exact (NoDup_remove_2 _ _ _ ND2 Hin).
Qed.

(* malloc(sz) at the frame base, returning to ret: the new block joins the message's blocks X. *)
Lemma ib_malloc : forall fx L A regs mem md R O q X sz ret (K : config -> Prop),
  CF fx L A regs mem md -> SlotInv.rcap A -> RFX L0 A0 L A mem R O q X ->
  (length X <= 2)%nat -> (forall pn, In pn X -> 0 <= snd pn <= 2 ^ 16) -> 0 <= sz <= 2 ^ 16 ->
  getr regs 10 = Z_to_bv 64 sz -> getr regs 1 = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
  (forall fx' L' A' regs' mem' md' res, CF fx' L' A' regs' mem' md' -> SlotInv.rcap A' ->
     RFX L0 A0 L' A' mem' R O q (X ++ [(res, sz)]) -> ~ In res (map fst X) -> res mod 16 = 0 ->
     regs_preserved regs regs' -> getr regs' 10 = Z_to_bv 64 res ->
     (forall a cs, FB <= a -> a + Z.of_nat (cells_size cs) <= FB + 56 -> rw_cells rsegs mem a cs ->
        rw_cells rsegs mem' a cs) ->
     SR rsegs (mkCfg (@mkst fx' regs' (Z_to_bv 64 ret) mem' (seg_rom rsegs)) md') K) ->
  SR rsegs (mkCfg (@mkst fx regs (Z_to_bv 64 0x18c10) mem (seg_rom rsegs)) md) K.
Proof.
  intros fx L A regs mem md R O q X sz ret K HCF HRC HRX HXl HXs Hsz G10 G1 Hr2 Hr KC.
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRX as (REP & SPILL & QB & Hq & ENO & BLK & XC & HOL).
  assert (SEGS : ms_segs B = rsegs) by (eapply it_SEGS; eassumption).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  pose proof alloc_ceiling_val as AC.
  assert (SP : spZ regs = FB) by (eapply it_spz; eassumption).
  destruct (it_FA B API LS SH SK ra empty FG fx)
    as (MALLOC & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AX & GNOWN & RNOWN).
  pose proof FG as FG'. fg_destruct FG'.
  assert (PREC : call_pre B (aa_MR (API rc)) L A regs mem md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR (API rc)) L A regs mem md)).
    apply (it_pre B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx L A regs mem md ALLOC_STACK HCF).
    - rewrite G1. apply YK0s.ret_ok_even. rewrite unsigned_lit by lia. exact Hr2.
    - unfold ALLOC_STACK, SLOT_STACK. lia. }
  assert (RSL : forall pn, In pn O -> 0 <= snd pn <= LMAX + 2).
  { intros pn Hin. pose proof (it_rec_blk rsegs L A mem R O pn REP Hin). lia. }
  assert (ROOM : room_slots (SlotInv.tb A) sz).
  { pose proof (it_tb_range L A Wf) as [T1 T2].
    apply (it_room B API LS SH SK ra empty rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A mem md O X M Wf EB BLK HOL RSL
             ltac:(lia) HXs); [reflexivity | unfold SlotInv.tb; cbn; lia | unfold SlotInv.tb; cbn; lia | lia]. }
  pose proof (MALLOC L A regs mem md sz (SlotInv.tb A) PREC ltac:(rewrite SEGS; exact RO) G10
    (SlotInv.res_tb L A Wf HRC) ROOM) as ML.
  rewrite SEGS, F2 in ML.
  eapply SR_bind; [exact ML|]. clear ML.
  intros c1 (L1 & A1 & regs1 & mem1 & md1 & res & -> & POST & R10 & RNZ & R16 & FRESH & (b1 & b2 & E1 & E2) & KEPT &
    RO1 & GK & UK & INIT & RGN & RES1).
  destruct POST as (M1 & W1 & Bd1 & LLE1 & PA1 & PRES & (vm1 & Hmd1) & FRAME & BYTES & SCRW).
  pose proof FRAME as FRAMEr. rewrite SEGS in FRAMEr.
  assert (OLD : forall pn, In pn (blocks L A) -> In pn (blocks L1 A1)).
  { intros pn Hp. rewrite E1. rewrite E2 in Hp. exact (RecAnsB.in_mid_inv b1 b2 _ _ Hp). }
  assert (NOLD : forall k, ~ In (res, k) (blocks L A)).
  { intros k Hk. rewrite E2 in Hk. exact (ib_new fx L1 A1 mem1 md1 b1 b2 res sz k M1 E1 Hk). }
  assert (EB1 : SlotInv.eblocks mem0 L0 A0 L1 A1 mem1).
  { intros a k0 Hin. destruct (EB a k0 Hin) as [Hb Hk]. split; [exact (OLD _ Hb)|].
    intros i Hi. rewrite <- (Hk i Hi). pose proof (KEPT a k0 i Hb (fun H => H) Hi) as KK. rewrite SEGS in KK. exact KK. }
  assert (GI1 : G_img_c B frame_RELRO mem1).
  { intros a Ha. destruct (F26 a Ha) as (Hi & Hs & Hc & He).
    destruct (FRAME a (or_intror Hi)) as [E3 _].
    - exact (RNOWN L A mem md a M Ha).
    - exact (RNOWN L1 A1 mem1 md1 a M1 Ha).
    - unfold scratch_k. rewrite SP. pose proof (KindB.in_img_low B SEGS a Hi). unfold SlotInv.FB, ALLOC_STACK, SLOT_STACK in *.
      intros [Hx|Hx]; [lia | exact (He Hx)].
    - intros [].
    - rewrite E3. exact (GIm a Ha). }
  assert (CF1 : CF fx L1 A1 regs1 mem1 md1).
  { apply (it_cf_call B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx fx ALLOC_STACK L A regs mem md
             (fun _ => False) L1 A1 regs1 mem1 md1 regs1 HCF M1 W1 Bd1 INIT PRES (ex_intro _ vm1 Hmd1) FRAME SCRW).
    - unfold SlotInv.FB, ALLOC_STACK, SLOT_STACK. lia.
    - unfold ALLOC_STACK. lia.
    - intros a [].
    - rewrite <- SEGS. exact RO1.
    - exact GI1.
    - exact EB1.
    - exact FZ.
    - intros r. reflexivity. }
  assert (RX1 : RFX L0 A0 L1 A1 mem1 R O q (X ++ [(res, sz)])).
  { apply (it_rfx_move L0 A0 L A mem R O q X L1 A1 mem1 (X ++ [(res, sz)]) HRX).
    - intros a Ha. destruct (F25 a (se_g_of a Ha)) as (Hi & Hs & Hc & He).
      destruct (FRAMEr a (or_intror Hi)) as [E3 W3].
      + exact (GNOWN L A mem md a M (se_g_of a Ha)).
      + exact (GNOWN L1 A1 mem1 md1 a M1 (se_g_of a Ha)).
      + unfold scratch_k. rewrite SP. unfold SlotInv.FB, ALLOC_STACK, SLOT_STACK in *.
        intros [Hx|Hx]; [lia | exact (He Hx)].
      + intros [].
      + split; [exact E3 | tauto].
    - intros p1 k1 i Hin Hi. destruct (it_rec_blk rsegs L A mem R O (p1, k1) REP Hin) as [Hb _].
      pose proof (KEPT p1 k1 i Hb (fun H => H) Hi) as KK. rewrite SEGS in KK. exact KK.
    - intros pn Hin. exact (OLD _ (proj1 (it_rec_blk rsegs L A mem R O pn REP Hin))).
    - intros pn Hp. rewrite E1 in Hp. destruct (SlotInv.zz_dec pn (res, sz)) as [->|Hne].
      + right. right. apply in_or_app. right. left. reflexivity.
      + assert (Hp0 : In pn (blocks L A)) by (rewrite E2; exact (RecAnsB.in_mid_other b1 b2 _ _ Hp Hne)).
        destruct (BLK pn Hp0) as [H|[H|H]]; [left; exact H | right; left; exact H | right; right; apply in_or_app; left; exact H].
    - intros pn Hin. apply in_app_or in Hin as [Hin|[<-|[]]].
      + destruct (XC pn Hin) as (Hb & H0 & HO). split; [exact (OLD _ Hb) | split; [exact H0 | exact HO]].
      + split; [rewrite E1; apply in_or_app; right; left; reflexivity|]. split.
        * intros H0. destruct (EB _ _ H0) as [Hb _]. exact (NOLD sz Hb).
        * intros Ho. apply in_map_iff in Ho as ([a k] & Ea & Hk). cbn in Ea. subst a.
          exact (NOLD k (proj1 (it_rec_blk rsegs L A mem R O (res, k) REP Hk))). }
  rewrite G1, SEGS.
  apply (KC fx L1 A1 regs1 mem1 md1 res CF1).
  - exists (sb_malloc (SlotInv.tb A) sz). split; [exact RES1 | reflexivity].
  - exact RX1.
  - intros Hx. apply in_map_iff in Hx as ([a k] & Ea & Hk). cbn in Ea. subst a.
    exact (NOLD k (proj1 (XC _ Hk))).
  - exact R16.
  - exact PRES.
  - exact R10.
  - intros a cs Ha Hb HC.
    apply (it_frame_cells B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx L A regs mem md
             ALLOC_STACK _ L1 A1 mem1 md1 a cs HCF M1 FRAMEr); [|exact Ha|exact Hb|exact HC].
    intros a' [].
Qed.

(* A Kind A run that writes only the slot's stack below the saved registers. *)
Lemma ib_stack_move : forall fx fx' L A regs mem md R O q X W mem' regs',
  CF fx L A regs mem md -> RFX L0 A0 L A mem R O q X ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Frame.outside W a -> S - SLOT_STACK <= a < FB + 56) ->
  frm_zero (@fp_csr fx') -> getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  CF fx' L A regs' mem' md /\ RFX L0 A0 L A mem' R O q X /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - SLOT_STACK <= a < FB + 56) ->
     mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
Proof.
  intros fx fx' L A regs mem md R O q X W mem' regs' HCF HRX MU WM RO' HW FZ H2 H3 H4.
  pose proof HCF as (M & _).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  pose proof alloc_ceiling_val as AC.
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (S - SLOT_STACK <= a < FB + 56) ->
     mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Ha Hx. destruct (SlotInv.classic_outside W a) as [Ho|Ho]; [|exfalso; exact (Hx (HW a Ha Ho))].
    split; [exact (KindB.munch_mbyte rsegs _ _ _ a MU Ha Ho) | exact (KindB.munch_writable rsegs _ _ _ a MU Ha Ho)]. }
  split; [|split; [|exact K]].
  - apply (it_cf_run B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx fx' L A regs mem md W mem'
             regs' HCF MU WM RO'); [| | exact FZ | exact H2 | exact H3 | exact H4].
    + intros a Ha Hx. left. exact (HW a Ha Hx).
    + intros p1 n1 i Hin Hi Hx. exfalso.
      assert (Hb : In (ptr_addr L p1, n1) (blocks L A))
        by (unfold blocks; apply in_map_iff; exists (p1, n1); split; [reflexivity | exact Hin]).
      destruct (KindB.block_facts B _ (aa_laws (API rc)) L A mem md _ n1 i M Hb Hi) as (_ & _ & Q2 & _).
      pose proof (KindB.block_facts B _ (aa_laws (API rc)) L A mem md _ n1 i M Hb Hi) as (_ & Q1 & _).
      pose proof (HW (ptr_addr L p1 + i) ltac:(lia) Hx). unfold SlotInv.FB, SLOT_STACK in *. lia.
  - apply (it_rfx_move L0 A0 L A mem R O q X L A mem' X HRX).
    + intros a Ha. destruct (K a ltac:(lia) ltac:(unfold SlotInv.FB, SLOT_STACK in *; lia)) as [E W']. split; [exact E | tauto].
    + intros p1 k1 i Hin Hi. destruct HRX as (REP & _). destruct (it_rec_blk rsegs L A mem R O (p1, k1) REP Hin) as [Hb Hk].
      destruct (KindB.block_facts B _ (aa_laws (API rc)) L A mem md p1 k1 i M Hb Hi) as (_ & Q1 & Q2 & _).
      exact (proj1 (K (p1 + i) ltac:(lia) ltac:(unfold SlotInv.FB, SLOT_STACK in *; lia))).
    + intros pn H. exact (proj1 (it_rec_blk rsegs L A mem R O pn (proj1 HRX) H)).
    + exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HRX)))))).
    + exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRX))))))).
Qed.

Lemma LR_pres : forall m p n regs regs' mem mem', LR p0 n0 pl m p n regs mem -> regs_preserved regs regs' ->
  LR p0 n0 pl m p n regs' mem'.
Proof.
  intros m p n regs regs' mem mem' (L8 & L9 & L23 & L22 & L26 & L24 & L25 & L27 & RNG) P. unfold LR.
  split; [exact (eq_trans (P 8 ltac:(unfold callee_saved; lia)) L8)|].
  split; [exact (eq_trans (P 9 ltac:(unfold callee_saved; lia)) L9)|].
  split; [exact (eq_trans (P 23 ltac:(unfold callee_saved; lia)) L23)|].
  split; [exact (eq_trans (P 22 ltac:(unfold callee_saved; lia)) L22)|].
  split; [exact (eq_trans (P 26 ltac:(unfold callee_saved; lia)) L26)|].
  split; [exact (eq_trans (P 24 ltac:(unfold callee_saved; lia)) L24)|].
  split; [exact (eq_trans (P 25 ltac:(unfold callee_saved; lia)) L25)|].
  split; [exact (eq_trans (P 27 ltac:(unfold callee_saved; lia)) L27)|].
  exact RNG.
Qed.

Lemma LR_raw : forall m p n regs regs' R mem mem', LR p0 n0 pl m p n regs mem -> (forall r, getr regs' r = getr R r) ->
  getr R 8 = getr regs 8 -> getr R 9 = getr regs 9 -> getr R 23 = getr regs 23 -> getr R 22 = getr regs 22 ->
  getr R 26 = getr regs 26 -> getr R 24 = getr regs 24 -> getr R 25 = getr regs 25 -> getr R 27 = getr regs 27 ->
  LR p0 n0 pl m p n regs' mem'.
Proof.
  intros m p n regs regs' R mem mem' (L8 & L9 & L23 & L22 & L26 & L24 & L25 & L27 & RNG) GR H8 H9 H23 H22 H26 H24 H25
    H27. unfold LR.
  rewrite !GR, H8, H9, H23, H22, H26, H24, H25, H27. tauto.
Qed.

Lemma ib_out1 : forall lo hi a, a < lo \/ hi <= a -> Frame.outside [(lo, hi)] a.
Proof. intros lo hi a H. cbn. split; [lia | exact Logic.I]. Qed.

Lemma ib_cells_munch : forall W mem mem' a cs, rw_cells rsegs mem a cs -> munch W mem mem' -> 0 <= a ->
  a + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> Frame.outside W (a + i)) -> rw_cells rsegs mem' a cs.
Proof.
  intros W mem mem' a cs HC MU H0 H1 HO. apply (KindB.rw_cells_transfer rsegs mem mem' a cs HC). intros i Hi.
  split; [exact (KindB.munch_mbyte rsegs W mem mem' (a + i) MU ltac:(lia) (HO i Hi))|].
  intros Hw. exact (proj1 (KindB.munch_writable rsegs W mem mem' (a + i) MU ltac:(lia) (HO i Hi)) Hw).
Qed.

Lemma ib_cells_eq : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W Bt] Wr] W' E. split; [split; [exact W' | rewrite E; exact Bt]|].
  rewrite <- (Cells.cells_bytes_length cs' W'), E, (Cells.cells_bytes_length cs W). exact Wr.
Qed.

Lemma ib_cells_app : forall m A cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] R1] [[W2 B2] R2]. split; [split|].
  - apply Cells.cells_wf_app. tauto.
  - rewrite Cells.cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite (Cells.cells_bytes_length cs1 W1). exact B2.
  - rewrite Cells.cells_size_app, Nat2Z.inj_add.
    apply (proj2 (SlotWords.sw_wr_at_split m A (Z.of_nat (cells_size cs1)) (Z.of_nat (cells_size cs2)) ltac:(lia)
      ltac:(lia))).
    split; [exact R1 | exact R2].
Qed.

(* [CB (8 + k) j] at A is [CB 8] at A and [CB k] at A + 8. *)
Lemma ib_cb_split8 : forall m A (k : nat) j, rw_cells rsegs m A [CB (8 + k) j] ->
  rw_cells rsegs m A [CB 8 (firstn 8 j)] /\ rw_cells rsegs m (A + 8) [CB k (skipn 8 j)].
Proof.
  intros m A k j H. pose proof H as [[[Hl _] _] _]. cbn [cell_wf] in Hl.
  assert (H' : rw_cells rsegs m A ([CB 8 (firstn 8 j)] ++ [CB k (skipn 8 j)])).
  { apply (ib_cells_eq m A _ _ H).
    - cbn. rewrite length_firstn, length_skipn. split; [lia|]. split; [lia | exact Logic.I].
    - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. apply firstn_skipn. }
  apply RecAns.rw_cells_app_split in H' as [H1 H2]. split; [exact H1 | exact H2].
Qed.

Ltac pv P H r := exact (eq_trans (P r ltac:(unfold callee_saved; lia)) H).

(* The length of the message's line: strnlen of the message. *)
Definition LW (p n : Z) : Z := strnlen_res (m_len p0 pl p n) (m_D p0 pl p n).

Lemma LW_range : forall p n, 0 < n -> p0 <= p -> p + n = p0 + n0 -> Z.of_nat (length pl) = n0 ->
  0 <= LW p n <= m_len p0 pl p n.
Proof.
  intros p n Hn Hp Hpn HL. unfold LW.
  rewrite (SlotRec.strnlen_upto0 _ _ (m_D_len p0 n0 pl p n Hn Hp Hpn HL)).
  pose proof (m_D_len p0 n0 pl p n Hn Hp Hpn HL) as HD.
  assert (E : Verbs.upto0 (m_D p0 pl p n) = firstn (length (Verbs.upto0 (m_D p0 pl p n))) (m_D p0 pl p n))
    by (unfold Verbs.upto0; apply SlotWords.sw_upto_prefix).
  apply (f_equal (@length byte)) in E. rewrite length_firstn in E. lia.
Qed.

(* After the third malloc returned (pc 0x14200): text and copy (LW + 1 bytes) and the pointer array of the line
   are the message's blocks; text and copy stored at FB + 24, FB + 32; s4 = LW, s5 = LW + 1, a0 = arr. *)
Definition stB (m p n : Z) (R0 : rstate) (c : config) : Prop :=
  exists (fx : FPState) L A regs mem md O R1 x quit text copy arr jw,
    c = mkCfg (@mkst fx regs (Z_to_bv 64 0x14200) mem (seg_rom rsegs)) md /\
    CF fx L A regs mem md /\ SlotInv.rcap A /\
    vr_run (rec_clear R0) (m_D p0 pl p n) = (R1, x, quit) /\
    RFX L0 A0 L A mem R1 O (qv quit) [(text, LW p n + 1); (copy, LW p n + 1); (arr, arr_size (LW p n))] /\
    text <> copy /\ text <> arr /\ copy <> arr /\ text mod 16 = 0 /\ copy mod 16 = 0 /\ arr mod 16 = 0 /\
    LR p0 n0 pl m p n regs mem /\
    getr regs 10 = Z_to_bv 64 arr /\ getr regs 18 = Z_to_bv 64 (r_state R0) /\
    getr regs 19 = Z_to_bv 64 (r_host R0) /\ getr regs 20 = Z_to_bv 64 (LW p n) /\
    getr regs 21 = Z_to_bv 64 (LW p n + 1) /\
    rw_cells rsegs mem FB (LOC1 (n - hdr_n n)) /\
    rw_cells rsegs mem (FB + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw] /\
    msg_props R0 (m_D p0 pl p n) /\
    (r_refuse R0 <> 0 -> declared (r_code R0) = true) /\ 0 <= r_state R0 < 2 ^ 64 /\ 0 <= r_host R0 < 2 ^ 64.

Lemma ib_seg : strnlen_contract -> forall m p n R0 c, stA B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  SR rsegs c (stB m p n R0).
Proof.
  intros SNL m p n R0 c
    (fx & L & A & regs & mem & md & O & R1 & x & quit & -> & HCF & HRC & EVR & HRX & HLR & G18 & G19 &
     LC0 & (jw & LC1) & MP & DCL & HSB & HHB).
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HLR as (L8 & L9 & L23 & L22 & L26 & L24 & L25 & L27 & Hm & Hn & Hp & Hpn).
  assert (SEGS : ms_segs B = rsegs) by (eapply it_SEGS; eassumption).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  assert (TS : S <= TASK_SIZE) by (eapply it_TS; eassumption).
  pose proof alloc_ceiling_val as AC.
  assert (Hn0 : 0 < n0) by lia.
  destruct (it_inblk B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0)
    as (IB & IB0 & Hp04 & Hpac & HL & _).
  pose proof (m_len_range p0 pl p n Hn) as [HL1 HL2].
  pose proof (m_D_len p0 n0 pl p n Hn Hp Hpn HL) as HDL.
  pose proof (LW_range p n Hn Hp Hpn HL) as LWR.
  assert (HSRC : 0 <= m_src p n - p0) by (unfold m_src, hdr_n; lia).
  pose proof (it_in_bytes B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0
     (m_src p n - p0) (m_len p0 pl p n) HSRC ltac:(lia) ltac:(unfold m_src in *; lia)) as HD.
  replace (p0 + (m_src p n - p0)) with (m_src p n) in HD by lia.
  change (firstn (Z.to_nat (m_len p0 pl p n)) (skipn (Z.to_nat (m_src p n - p0)) pl)) with (m_D p0 pl p n) in HD.
  destruct (it_model B API S rg mem0 md0 L0 A0 fx L A regs mem md HCF) as [Hh Hl].
  (* to strnlen's entry *)
  eapply (@sr_raw fx regs (Z_to_bv 64 0x141c4) mem md _ _ Hh Hl).
  { unfold Regs6ss.mkR_of. apply run_g_strnlen_ok. }
  { intros s0 ->. do 5 eexists. reflexivity. }
  intros R_1 F1 pc1 fc1 m1 regs1 E GR1. injection E as -> -> -> -> ->.
  assert (P1 : regs_preserved regs regs1) by (eapply pres_mkR; exact GR1).
  pose proof (ie_cf_regs B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx (mkFP fp_regs fp_csr) L A
    regs mem md regs1 HCF (P1 2 ltac:(unfold callee_saved; lia)) (P1 3 ltac:(unfold callee_saved; lia))
    (P1 4 ltac:(unfold callee_saved; lia)) FZ) as CF1.
  destruct (it_model B API S rg mem0 md0 L0 A0 _ L A regs1 mem md CF1) as [Hh1 Hl1].
  assert (SPV1 : bv_unsigned (reg_get regs1 2) = FB).
  { assert (E2 : getr regs1 2 = getr regs 2) by exact (P1 2 ltac:(unfold callee_saved; lia)).
    change (reg_get regs1 2) with (getr regs1 2). rewrite E2, R2. apply unsigned_lit.
    unfold SlotInv.FB, SLOT_STACK in *. lia. }
  (* strnlen *)
  eapply (@sr_run (mkFP fp_regs fp_csr) regs1 (Z_to_bv 64 0x21110) mem md _ _ Hh1 Hl1 RO).
  { unfold Regs6ss.mkR_of.
    assert (E10 : reg_get regs1 10 = Z_to_bv 64 (m_src p n))
      by (change (reg_get regs1 10) with (getr regs1 10); rewrite GR1; exact L8).
    assert (E11 : reg_get regs1 11 = Z_to_bv 64 (m_len p0 pl p n))
      by (change (reg_get regs1 11) with (getr regs1 11); rewrite GR1; exact L9).
    rewrite E10, E11.
    eapply SNL with (lo := S - SLOT_STACK) (buf := m_D p0 pl p n).
    - apply bytes_at_normalize; [exact RO | exact HD].
    - unfold memchr_ok. destruct (find_byte 0 _); lia.
    - unfold m_src, hdr_n in *. lia.
    - lia.
    - rewrite SPV1. apply RecAns.stk_normalize; [unfold SLOT_STACK in *; lia | unfold SlotInv.FB in *; lia |].
      intros a Ha. apply SW. left. rewrite RG2. unfold SlotInv.FB in *. lia.
    - rewrite SPV1. unfold SlotInv.FB, SLOT_STACK in *. lia.
    - left. rewrite SPV1, HDL. unfold m_src, hdr_n, SlotInv.FB, SLOT_STACK in *. lia.
    - apply mem_inv_normalize. }
  { intros s0 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
    do 5 eexists. reflexivity. }
  intros R_2 F2 pc2 fc2 m2 regs2 mem2
    (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI & STK & BS)
    REL ROS GR2.
  injection E as -> -> -> -> ->.
  pose proof (mem_rel_normalize rsegs mem RO) as REL0.
  rewrite SPV1 in MU.
  assert (MU2 : munch [(FB - 32, FB)] mem mem2) by exact (munch_rel rsegs _ _ _ _ _ REL0 REL ROS MU).
  assert (WM2 : wmono rsegs mem mem2) by exact (wmono_rel rsegs _ _ _ _ REL0 REL ROS WM).
  assert (RO2 : ro_agree rsegs mem2) by exact (ro_agree_same rsegs _ _ RO ROS).
  assert (P2 : regs_preserved regs1 regs2) by (eapply pres_mkR; exact GR2).
  assert (HW2 : forall a, 0 <= a < 2 ^ 64 -> ~ Frame.outside [(FB - 32, FB)] a -> S - SLOT_STACK <= a < FB + 56).
  { intros a Ha Hx. apply it_not_out1 in Hx. unfold SlotInv.FB, SLOT_STACK in *. lia. }
  destruct (ib_stack_move _ (mkFP fp_regs fp_csr) L A regs1 mem md R1 O (qv quit) [] _ mem2 regs2 CF1 HRX MU2 WM2 RO2
    HW2 FZ (P2 2 ltac:(unfold callee_saved; lia)) (P2 3 ltac:(unfold callee_saved; lia))
    (P2 4 ltac:(unfold callee_saved; lia))) as (CF2 & RX2 & _).
  assert (LC0b : rw_cells rsegs mem2 FB (LOC1 (n - hdr_n n))).
  { apply (ib_cells_munch _ mem mem2 FB _ LC0 MU2); [unfold SlotInv.FB, SLOT_STACK in *; lia |
      unfold LOC1; cbn; unfold SlotInv.FB in *; lia |].
    intros i Hi. apply ib_out1. lia. }
  assert (LC1b : rw_cells rsegs mem2 (FB + 24) [CB 32 jw]).
  { apply (ib_cells_munch _ mem mem2 (FB + 24) _ LC1 MU2); [unfold SlotInv.FB, SLOT_STACK in *; lia |
      cbn; unfold SlotInv.FB in *; lia |].
    intros i Hi. apply ib_out1. cbn in Hi. lia. }
  pose proof (LR_pres m p n regs regs1 mem mem HLR P1) as HLR1.
  pose proof (LR_pres m p n regs1 regs2 mem mem2 HLR1 P2) as HLR2.
  assert (X18_2 : getr regs2 18 = Z_to_bv 64 (r_state R0)).
  { assert (X : getr regs1 18 = Z_to_bv 64 (r_state R0)) by pv P1 G18 18. pv P2 X 18. }
  assert (X19_2 : getr regs2 19 = Z_to_bv 64 (r_host R0)).
  { assert (X : getr regs1 19 = Z_to_bv 64 (r_host R0)) by pv P1 G19 19. pv P2 X 19. }
  (* to the first malloc *)
  destruct (it_model B API S rg mem0 md0 L0 A0 _ L A regs2 mem2 md CF2) as [Hh2 Hl2].
  assert (E1' : reg_get regs1 1 = Z_to_bv 64 0x141d0)
    by (change (reg_get regs1 1) with (getr regs1 1); rewrite GR1; reflexivity).
  rewrite E1', (se_ret_pc 0x141d0 eq_refl).
  assert (A10 : getr regs2 10 = Z_to_bv 64 (LW p n)) by (rewrite GR2; reflexivity).
  assert (U10 : bv_unsigned (reg_get regs2 10) = LW p n)
    by (change (reg_get regs2 10) with (getr regs2 10); rewrite A10; apply unsigned_lit; lia).
  eapply (@sr_raw _ regs2 (Z_to_bv 64 0x141d0) mem2 md _ _ Hh2 Hl2).
  { unfold Regs6ss.mkR_of. apply run_g_m0_ok. rewrite U10. lia. }
  { intros s0 ->. do 5 eexists. reflexivity. }
  intros R_3 F3 pc3 fc3 m3 regs3 E GR3. injection E as -> -> -> -> ->.
  pose proof CF2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FZ2).
  pose proof (ie_cf_regs B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 _ (mkFP fp_regs fp_csr) L A
    regs2 mem2 md regs3 CF2 ltac:(rewrite GR3; reflexivity) ltac:(rewrite GR3; reflexivity)
    ltac:(rewrite GR3; reflexivity) FZ2) as CF3.
  assert (HLR3 : LR p0 n0 pl m p n regs3 mem2)
    by (apply (LR_raw m p n regs2 regs3 _ mem2 mem2 HLR2 GR3); reflexivity).
  assert (X18_3 : getr regs3 18 = Z_to_bv 64 (r_state R0)) by (rewrite GR3; exact X18_2).
  assert (X19_3 : getr regs3 19 = Z_to_bv 64 (r_host R0)) by (rewrite GR3; exact X19_2).
  assert (X21_3 : getr regs3 21 = Z_to_bv 64 (LW p n + 1)).
  { transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs2 10) + 1)); [rewrite GR3; reflexivity | rewrite U10; reflexivity]. }
  assert (X20_3 : getr regs3 20 = Z_to_bv 64 (LW p n)) by (rewrite GR3; exact A10).
  (* malloc text *)
  apply (ib_malloc _ L A regs3 mem2 md R1 O (qv quit) [] (LW p n + 1) 0x141e0 _ CF3 HRC RX2).
  { cbn. lia. }
  { intros pn []. }
  { lia. }
  { transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs2 10) + 1)); [rewrite GR3; reflexivity | rewrite U10; reflexivity]. }
  { rewrite GR3. reflexivity. }
  { reflexivity. }
  { lia. }
  intros fx4 L4 A4 regs4 mem4 md4 text CF4 RC4 RX4 _ T16 P4 G10_4 CK4.
  pose proof CF4 as (M4 & _ & _ & _ & _ & R2_4 & _ & _ & _ & _ & _ & RO4 & _ & _ & FZ4).
  destruct (it_model B API S rg mem0 md0 L0 A0 fx4 L4 A4 regs4 mem4 md4 CF4) as [Hh4 Hl4].
  assert (LC0c : rw_cells rsegs mem4 FB (LOC1 (n - hdr_n n))) by (apply CK4; [lia | unfold LOC1; cbn; lia | exact LC0b]).
  assert (LC1c : rw_cells rsegs mem4 (FB + 24) [CB (8 + 24) jw]) by (apply CK4; [lia | cbn; lia | exact LC1b]).
  destruct (ib_cb_split8 mem4 (FB + 24) 24 jw LC1c) as [LCx LCy].
  replace (FB + 24 + 8) with (FB + 32) in LCy by lia.
  assert (SPV4 : bv_unsigned (reg_get regs4 2) = FB).
  { change (reg_get regs4 2) with (getr regs4 2). rewrite R2_4. apply unsigned_lit.
    unfold SlotInv.FB, SLOT_STACK in *. lia. }
  (* to the second malloc *)
  eapply (@sr_run fx4 regs4 (Z_to_bv 64 0x141e0) mem4 md4 _ _ Hh4 Hl4 RO4).
  { unfold Regs6ss.mkR_of. eapply run_g_m1_ok.
    - apply mem_inv_normalize.
    - rewrite SPV4. unfold SlotInv.FB, SLOT_STACK, IMG_END in *. lia.
    - rewrite SPV4. unfold SlotInv.FB in *. lia.
    - rewrite SPV4. apply (KindB.rw_cells_normalize rsegs _ _ _ RO4 LCx). intros i Hi. apply ro_addr_hi. cbn in Hi.
      unfold SlotInv.FB, SLOT_STACK in *. lia. }
  { intros s0 (mq & -> & _). do 5 eexists. reflexivity. }
  intros R_5 F5 pc5 fc5 m5 regs5 mem5 (m5' & E & MUa & WMa & MIa & RCa) RELa ROSa GR5. injection E as -> -> -> -> ->.
  rewrite SPV4 in MUa, RCa.
  pose proof (mem_rel_normalize rsegs mem4 RO4) as REL4.
  assert (MU5 : munch [(FB + 24, FB + 32)] mem4 mem5) by exact (munch_rel rsegs _ _ _ _ _ REL4 RELa ROSa MUa).
  assert (WM5 : wmono rsegs mem4 mem5) by exact (wmono_rel rsegs _ _ _ _ REL4 RELa ROSa WMa).
  assert (RO5 : ro_agree rsegs mem5) by exact (ro_agree_same rsegs _ _ RO4 ROSa).
  pose proof (KindB.rw_cells_of_rel rsegs _ _ _ _ RELa RCa) as RC5.
  change (reg_get regs4 10) with (getr regs4 10) in RC5. rewrite G10_4 in RC5.
  assert (HW5 : forall a, 0 <= a < 2 ^ 64 -> ~ Frame.outside [(FB + 24, FB + 32)] a -> S - SLOT_STACK <= a < FB + 56).
  { intros a Ha Hx. apply it_not_out1 in Hx. unfold SlotInv.FB, SLOT_STACK in *. lia. }
  destruct (ib_stack_move fx4 (mkFP fp_regs fp_csr) L4 A4 regs4 mem4 md4 R1 O (qv quit) _ _ mem5 regs5 CF4 RX4 MU5 WM5 RO5
    HW5 FZ4 ltac:(rewrite GR5; reflexivity) ltac:(rewrite GR5; reflexivity) ltac:(rewrite GR5; reflexivity))
    as (CF5 & RX5 & _).
  assert (LC0d : rw_cells rsegs mem5 FB (LOC1 (n - hdr_n n))).
  { apply (ib_cells_munch _ mem4 mem5 FB _ LC0c MU5); [unfold SlotInv.FB, SLOT_STACK in *; lia |
      unfold LOC1; cbn; unfold SlotInv.FB in *; lia |].
    intros i Hi. apply ib_out1. unfold LOC1 in Hi. cbn in Hi. lia. }
  assert (LCy' : rw_cells rsegs mem5 (FB + 32) [CB (8 + 16) (skipn 8 jw)]).
  { apply (ib_cells_munch _ mem4 mem5 (FB + 32) _ LCy MU5); [unfold SlotInv.FB, SLOT_STACK in *; lia |
      cbn; unfold SlotInv.FB in *; lia |].
    intros i Hi. apply ib_out1. cbn in Hi. lia. }
  pose proof (LR_pres m p n regs3 regs4 mem2 mem4 HLR3 P4) as HLR4.
  assert (HLR5 : LR p0 n0 pl m p n regs5 mem5) by (apply (LR_raw m p n regs4 regs5 _ mem4 mem5 HLR4 GR5); reflexivity).
  assert (X18_5 : getr regs5 18 = Z_to_bv 64 (r_state R0)).
  { assert (X : getr regs4 18 = Z_to_bv 64 (r_state R0)) by pv P4 X18_3 18. rewrite GR5. exact X. }
  assert (X19_5 : getr regs5 19 = Z_to_bv 64 (r_host R0)).
  { assert (X : getr regs4 19 = Z_to_bv 64 (r_host R0)) by pv P4 X19_3 19. rewrite GR5. exact X. }
  assert (X21_4 : getr regs4 21 = Z_to_bv 64 (LW p n + 1)) by pv P4 X21_3 21.
  assert (X21_5 : getr regs5 21 = Z_to_bv 64 (LW p n + 1)) by (rewrite GR5; exact X21_4).
  assert (X20_5 : getr regs5 20 = Z_to_bv 64 (LW p n)).
  { assert (X : getr regs4 20 = Z_to_bv 64 (LW p n)) by pv P4 X20_3 20. rewrite GR5. exact X. }
  (* malloc copy *)
  apply (ib_malloc _ L4 A4 regs5 mem5 md4 R1 O (qv quit) [(text, LW p n + 1)] (LW p n + 1) 0x141ec _ CF5 RC4 RX5).
  { cbn. lia. }
  { intros pn [<-|[]]. cbn. lia. }
  { lia. }
  { rewrite GR5. exact X21_4. }
  { rewrite GR5. reflexivity. }
  { reflexivity. }
  { lia. }
  intros fx6 L6 A6 regs6 mem6 md6 copy CF6 RC6 RX6 NC C16 P6 G10_6 CK6.
  pose proof CF6 as (M6 & _ & _ & _ & _ & R2_6 & _ & _ & _ & _ & _ & RO6 & _ & _ & FZ6).
  destruct (it_model B API S rg mem0 md0 L0 A0 fx6 L6 A6 regs6 mem6 md6 CF6) as [Hh6 Hl6].
  assert (LC0e : rw_cells rsegs mem6 FB (LOC1 (n - hdr_n n))) by (apply CK6; [lia | unfold LOC1; cbn; lia | exact LC0d]).
  assert (LCt : rw_cells rsegs mem6 (FB + 24) [C8 (Z_to_bv 64 text)]) by (apply CK6; [lia | cbn; lia | exact RC5]).
  assert (LCy2 : rw_cells rsegs mem6 (FB + 32) [CB (8 + 16) (skipn 8 jw)]) by (apply CK6; [lia | cbn; lia | exact LCy']).
  destruct (ib_cb_split8 mem6 (FB + 32) 16 (skipn 8 jw) LCy2) as [LCz LCw].
  replace (FB + 32 + 8) with (FB + 40) in LCw by lia.
  assert (SPV6 : bv_unsigned (reg_get regs6 2) = FB).
  { change (reg_get regs6 2) with (getr regs6 2). rewrite R2_6. apply unsigned_lit.
    unfold SlotInv.FB, SLOT_STACK in *. lia. }
  pose proof (LR_pres m p n regs5 regs6 mem5 mem6 HLR5 P6) as HLR6.
  assert (X20_6 : getr regs6 20 = Z_to_bv 64 (LW p n)) by pv P6 X20_5 20.
  assert (X21_6 : getr regs6 21 = Z_to_bv 64 (LW p n + 1)) by pv P6 X21_5 21.
  assert (X18_6 : getr regs6 18 = Z_to_bv 64 (r_state R0)) by pv P6 X18_5 18.
  assert (X19_6 : getr regs6 19 = Z_to_bv 64 (r_host R0)) by pv P6 X19_5 19.
  (* to the third malloc *)
  eapply (@sr_run fx6 regs6 (Z_to_bv 64 0x141ec) mem6 md6 _ _ Hh6 Hl6 RO6).
  { unfold Regs6ss.mkR_of.
    assert (E20 : reg_get regs6 20 = Z_to_bv 64 (LW p n)) by exact X20_6.
    rewrite E20. eapply run_g_m2_ok.
    - apply mem_inv_normalize.
    - rewrite SPV6. unfold SlotInv.FB, SLOT_STACK, IMG_END in *. lia.
    - rewrite SPV6. unfold SlotInv.FB in *. lia.
    - lia.
    - rewrite SPV6. apply (KindB.rw_cells_normalize rsegs _ _ _ RO6 LCz). intros i Hi. apply ro_addr_hi. cbn in Hi.
      unfold SlotInv.FB, SLOT_STACK in *. lia. }
  { intros s0 (aq & mq & -> & _). do 5 eexists. reflexivity. }
  intros R_7 F7 pc7 fc7 m7 regs7 mem7 (a0' & m7' & E & Ea0 & MUb & WMb & MIb & RCb) RELb ROSb GR7.
  injection E as -> -> -> -> ->.
  rewrite SPV6 in MUb, RCb.
  pose proof (mem_rel_normalize rsegs mem6 RO6) as REL6.
  assert (MU7 : munch [(FB + 32, FB + 40)] mem6 mem7) by exact (munch_rel rsegs _ _ _ _ _ REL6 RELb ROSb MUb).
  assert (WM7 : wmono rsegs mem6 mem7) by exact (wmono_rel rsegs _ _ _ _ REL6 RELb ROSb WMb).
  assert (RO7 : ro_agree rsegs mem7) by exact (ro_agree_same rsegs _ _ RO6 ROSb).
  pose proof (KindB.rw_cells_of_rel rsegs _ _ _ _ RELb RCb) as RC7.
  change (reg_get regs6 10) with (getr regs6 10) in RC7. rewrite G10_6 in RC7.
  assert (HW7 : forall a, 0 <= a < 2 ^ 64 -> ~ Frame.outside [(FB + 32, FB + 40)] a -> S - SLOT_STACK <= a < FB + 56).
  { intros a Ha Hx. apply it_not_out1 in Hx. unfold SlotInv.FB, SLOT_STACK in *. lia. }
  destruct (ib_stack_move fx6 (mkFP fp_regs fp_csr) L6 A6 regs6 mem6 md6 R1 O (qv quit) _ _ mem7 regs7 CF6 RX6 MU7 WM7 RO7
    HW7 FZ6 ltac:(rewrite GR7; reflexivity) ltac:(rewrite GR7; reflexivity) ltac:(rewrite GR7; reflexivity))
    as (CF7 & RX7 & _).
  assert (LC0f : rw_cells rsegs mem7 FB (LOC1 (n - hdr_n n))).
  { apply (ib_cells_munch _ mem6 mem7 FB _ LC0e MU7); [unfold SlotInv.FB, SLOT_STACK in *; lia |
      unfold LOC1; cbn; unfold SlotInv.FB in *; lia |].
    intros i Hi. apply ib_out1. unfold LOC1 in Hi. cbn in Hi. lia. }
  assert (LCt' : rw_cells rsegs mem7 (FB + 24) [C8 (Z_to_bv 64 text)]).
  { apply (ib_cells_munch _ mem6 mem7 (FB + 24) _ LCt MU7); [unfold SlotInv.FB, SLOT_STACK in *; lia |
      cbn; unfold SlotInv.FB in *; lia |].
    intros i Hi. apply ib_out1. cbn in Hi. lia. }
  assert (LCw' : rw_cells rsegs mem7 (FB + 40) [CB 16 (skipn 8 (skipn 8 jw))]).
  { apply (ib_cells_munch _ mem6 mem7 (FB + 40) _ LCw MU7); [unfold SlotInv.FB, SLOT_STACK in *; lia |
      cbn; unfold SlotInv.FB in *; lia |].
    intros i Hi. apply ib_out1. cbn in Hi. lia. }
  assert (HLR7 : LR p0 n0 pl m p n regs7 mem7) by (apply (LR_raw m p n regs6 regs7 _ mem6 mem7 HLR6 GR7); reflexivity).
  assert (X18_7 : getr regs7 18 = Z_to_bv 64 (r_state R0)) by (rewrite GR7; exact X18_6).
  assert (X19_7 : getr regs7 19 = Z_to_bv 64 (r_host R0)) by (rewrite GR7; exact X19_6).
  assert (X20_7 : getr regs7 20 = Z_to_bv 64 (LW p n)) by (rewrite GR7; reflexivity).
  assert (X21_7 : getr regs7 21 = Z_to_bv 64 (LW p n + 1)) by (rewrite GR7; exact X21_6).
  assert (ASZ : 0 <= arr_size (LW p n) <= 2 ^ 16).
  { unfold arr_size. pose proof (Z.div_pos (LW p n) 2 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (LW p n) 2 (LW p n) ltac:(lia) ltac:(lia)). lia. }
  (* malloc the pointer array *)
  apply (ib_malloc _ L6 A6 regs7 mem7 md6 R1 O (qv quit) [(text, LW p n + 1); (copy, LW p n + 1)] (arr_size (LW p n))
           0x14200 _ CF7 RC6 RX7).
  { cbn. lia. }
  { intros pn [<-|[<-|[]]]; cbn; lia. }
  { exact ASZ. }
  { rewrite GR7. exact Ea0. }
  { rewrite GR7. reflexivity. }
  { reflexivity. }
  { lia. }
  intros fx8 Ly A8 regs8 mem8 md8 arr CF8 RC8 RX8 NA A16 P8 G10_8 CK8.
  apply SR_ret.
  assert (LC0g : rw_cells rsegs mem8 FB (LOC1 (n - hdr_n n))) by (apply CK8; [lia | unfold LOC1; cbn; lia | exact LC0f]).
  assert (LCW : rw_cells rsegs mem8 (FB + 24)
                  [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 (skipn 8 (skipn 8 jw))]).
  { apply CK8; [lia | cbn; lia |].
    apply (ib_cells_app mem7 (FB + 24) [C8 (Z_to_bv 64 text)] [C8 (Z_to_bv 64 copy); CB 16 (skipn 8 (skipn 8 jw))] LCt').
    replace (FB + 24 + Z.of_nat (cells_size [C8 (Z_to_bv 64 text)])) with (FB + 32) by (cbn; lia).
    apply (ib_cells_app mem7 (FB + 32) [C8 (Z_to_bv 64 copy)] [CB 16 (skipn 8 (skipn 8 jw))] RC7).
    replace (FB + 32 + Z.of_nat (cells_size [C8 (Z_to_bv 64 copy)])) with (FB + 40) by (cbn; lia).
    exact LCw'. }
  cbn [map fst In] in NC, NA.
  exists fx8, Ly, A8, regs8, mem8, md8, O, R1, x, quit, text, copy, arr, (skipn 8 (skipn 8 jw)).
  split; [reflexivity|]. split; [exact CF8|]. split; [exact RC8|]. split; [exact EVR|]. split; [exact RX8|].
  split; [intros E; apply NC; left; congruence|].
  split; [intros E; apply NA; left; congruence|].
  split; [intros E; apply NA; right; left; congruence|].
  split; [exact T16|]. split; [exact C16|]. split; [exact A16|].
  split; [exact (LR_pres m p n regs7 regs8 mem7 mem8 HLR7 P8)|].
  split; [exact G10_8|].
  split; [pv P8 X18_7 18|]. split; [pv P8 X19_7 19|]. split; [pv P8 X20_7 20|]. split; [pv P8 X21_7 21|].
  split; [exact LC0g|]. split; [exact LCW|]. split; [exact MP|]. split; [exact DCL|]. split; [exact HSB | exact HHB].
Qed.

End B.
