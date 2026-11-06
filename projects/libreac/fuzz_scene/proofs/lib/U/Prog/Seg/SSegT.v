From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Cells.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0 Contract FrameAPI MemNorm.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require SceneTU.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require memcpy_c bcmp_c reac_ctrl_build_scene_step_c check_step_c.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require Import SInv STac SGlue SCut SMid.
Import ListNotations.
Open Scope Z_scope.

(* Segment T: from 0x151b4 (a0 = again) the 343-step rebuild of the body into again and the compare run to the
   free of again (ra 0x15294). *)

Lemma st_win : forall g body nb again lo hi y,
  In (lo, hi) [(g_S g - 9280, g_S g); (again, again + 8904)] -> lo <= y < hi ->
  kreg g [(body, nb); (again, 8904)] y \/ g_S g - 104 <= y < g_S g.
Proof.
  intros g body nb again lo hi y Hin Hy. cbn [In] in Hin.
  destruct Hin as [Ew|[Ew|[]]]; injection Ew as <- <-.
  - destruct (Z_lt_le_dec y (g_S g - 104)) as [Hl|Hl]; [left; left; unfold SLOT_K, SLOT_STACK; lia | right; lia].
  - left. right. exists again, 8904. split; [right; left; reflexivity | lia].
Qed.

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FREE : free_contract B (APIf rc).
Hypothesis BUILD : reac_ctrl_build_scene_step_c.reac_ctrl_build_scene_step_contract.
Hypothesis CHECK : check_step_c.check_step_contract.
Hypothesis MEMC : memcpy_c.memcpy_contract.
Hypothesis BCMP : bcmp_c.bcmp_contract.

Lemma st_blk_raw : forall g km hb L A regs mem md a k,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (a, k) hb -> 0 <= k ->
  bytes_at rsegs mem a (ss_rd_list mem a (Z.to_nat k)) /\ Z.of_nat (length (ss_rd_list mem a (Z.to_nat k))) = k.
Proof.
  intros g km hb L A regs mem md a k HF HP Hin Hk.
  destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md a k HF HP Hin) as (HB & H4 & Hc & _).
  pose proof alloc_ceiling_value as HAC.
  rewrite ss_rd_list_len. split; [|lia].
  split; [lia|]. rewrite ?ss_rd_list_len. split; [lia|].
  intros i Hi. rewrite ?ss_rd_list_len in Hi. rewrite ss_rd_list_nth by exact Hi.
  destruct (HB (Z.of_nat i) ltac:(lia)) as (_ & (b & Hb) & _).
  unfold mrd, wa. rewrite Hb. reflexivity.
Qed.

Lemma st_hb2_disj : forall g km body nb again L A regs mem md,
  FR B APIf ra empty g km [(body, nb); (again, 8904)] L A regs mem md ->
  Permutation (blocks L A) ([(body, nb); (again, 8904)] ++ blocks (g_L g) (g_A g)) ->
  ranges_disjoint (body, nb) (again, 8904).
Proof.
  intros g km body nb again L A regs mem md HF HP.
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  pose proof (mr_blocks_disjoint B _ (aa_laws (APIf rc)) L A mem md HMR) as Hpw.
  pose proof (ss_pw_perm ranges_disjoint ltac:(intros u v; unfold ranges_disjoint; lia) _ _ HP Hpw) as Hpw'.
  destruct Hpw' as [H1 _]. apply H1. left. reflexivity.
Qed.

Lemma st_norm_eq : forall (m : word -> option byte) x, ~ in_img B x -> 0 <= x < 2 ^ 64 ->
  normalize rsegs m (wa x) = m (wa x).
Proof.
  intros m x Hni Hx. unfold normalize, Mem.ro_addr. rewrite wa_unsigned by exact Hx.
  rewrite (ss_noimg_fs B APIf ra empty FF x Hni). reflexivity.
Qed.

Lemma st_blk_u8 : forall g km hb L A regs mem md a k,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (a, k) hb -> 0 <= k ->
  (bytes_at rsegs (normalize rsegs mem) a (ss_rd_list mem a (Z.to_nat k)) /\
   wr_at rsegs (normalize rsegs mem) a (Z.of_nat (length (ss_rd_list mem a (Z.to_nat k))))) /\
  Z.of_nat (length (ss_rd_list mem a (Z.to_nat k))) = k.
Proof.
  intros g km hb L A regs mem md a k HF HP Hin Hk.
  destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md a k HF HP Hin) as (HB & H4 & Hc & _).
  pose proof alloc_ceiling_value as HAC.
  rewrite !ss_rd_list_len. split; [|lia].
  split.
  - split; [lia|]. rewrite ?ss_rd_list_len. split; [lia|].
    intros i Hi. rewrite ?ss_rd_list_len in Hi. rewrite ss_rd_list_nth by exact Hi.
    destruct (HB (Z.of_nat i) ltac:(lia)) as (_ & (b & Hb) & Hni).
    unfold mrd. rewrite (st_norm_eq mem (a + Z.of_nat i) Hni ltac:(lia)). unfold wa. rewrite Hb. reflexivity.
  - split; [lia|]. split; [lia|]. intros i Hi.
    destruct (HB i ltac:(lia)) as (_ & (b & Hb) & Hni).
    unfold wview. rewrite (st_norm_eq mem (a + i) Hni ltac:(lia)). unfold wa. rewrite Hb. discriminate.
Qed.

Lemma seg_T : Hcut B APIf ra (Inv_K15294 B APIf ra empty) -> Hcut B APIf ra (Inv_K151b4 B APIf ra empty).
Proof.
  intros HX g c (body & again & HC).
  eapply (cut_open B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (H10 & H9 & H8 & HN & Q16 & (bb & Lbb & HBB) & (macb & Lmac & HMAC)).
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  pose proof (ss_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (_ & HIH & H8k & HfS & HSc & HS47 & HSK & Hsp).
  unfold IMG_HI in HIH.
  pose proof HF as (HGV & _ & _ & _ & Hsv & _ & HMI & _).
  pose proof HGV as (Hn0 & _ & _ & HS16 & _).
  pose proof alloc_ceiling_value as HAC.
  unfold MI in HMI. rewrite SEG in HMI.
  assert (Hnb : nbG g = 8904) by (unfold nbG; rewrite HN; reflexivity).
  assert (Hbin : In (body, nbG g) [(body, nbG g); (again, 8904)]) by (left; reflexivity).
  assert (Hain : In (again, 8904) [(body, nbG g); (again, 8904)]) by (right; left; reflexivity).
  destruct (ss_hb_blk B APIf ra empty FF g _ _ L A regs mem md body (nbG g) HF HP Hbin) as (_ & Hb4 & Hbc & _).
  destruct (ss_hb_blk B APIf ra empty FF g _ _ L A regs mem md again 8904 HF HP Hain) as (_ & Ha4 & Hac & _).
  destruct (st_blk_u8 g _ _ L A regs mem md again 8904 HF HP Hain ltac:(lia))
    as ((HBa & HWa) & HLa).
  assert (IB : in_hb [(body, nbG g); (again, 8904)] (body + 8903)) by (exists body, (nbG g); split; [exact Hbin | lia]).
  assert (IA : in_hb [(body, nbG g); (again, 8904)] (again + 8903)) by (exists again, 8904; split; [exact Hain | lia]).
  destruct (ss_hb_low B APIf ra empty FF g _ _ L A regs mem md (body + 8903) HF HP IB) as (_ & H2b).
  destruct (ss_hb_low B APIf ra empty FF g _ _ L A regs mem md (again + 8903) HF HP IA) as (_ & H2a).
  unfold SLOT_K, SLOT_STACK in H2b, H2a.
  pose proof (st_hb2_disj g _ body (nbG g) again L A regs mem md HF HP) as HDJ.
  unfold ranges_disjoint in HDJ. cbn [fst snd] in HDJ. rewrite Hnb in HDJ.
  assert (Ubd : bv_unsigned (getr regs 9) = body) by (rewrite H9; apply unsigned_lit; lia).
  assert (Uag : bv_unsigned (getr regs 10) = again) by (rewrite H10; apply unsigned_lit; lia).
  assert (Usp : bv_unsigned (getr regs 2) = g_S g - 9072)
    by (rewrite Hsp; unfold fsp, SLOT_FRAME; apply unsigned_lit; lia).
  pose proof (ss_fr_stk B APIf ra empty FF g _ _ L A regs mem md HF) as HSTK.
  unfold SLOT_K, SLOT_STACK in HSTK.
  change (Z.to_nat 8904) with 8904%nat in HBa, HWa, HLa.
  assert (RWA : rw_cells rsegs (normalize rsegs mem) (bv_unsigned (getr regs 10))
                  [Cells.CB 8904 (ss_rd_list mem again 8904)]).
  { rewrite Uag. split.
    - split; [cbn [Cells.cells_wf Cells.cell_wf]; rewrite ss_rd_list_len; split; [reflexivity | exact I]|].
      cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r. exact HBa.
    - cbn [Cells.cells_size Cells.csize]. rewrite Nat.add_0_r. exact HWa. }
  assert (HBn : bytes_at rsegs (normalize rsegs mem) (bv_unsigned (getr regs 9)) bb)
    by (rewrite Ubd; apply bytes_at_normalize; [exact HMI | exact HBB]).
  assert (Lbb' : length bb = 8904%nat) by (apply Nat2Z.inj; rewrite Lbb; reflexivity).
  assert (HSVn : bytes_at rsegs (normalize rsegs mem) (g_S g - 104) (saved_bytes ra g))
    by (apply bytes_at_normalize; [exact HMI | exact Hsv]).
  assert (Lsv : length (saved_bytes ra g) = 104%nat)
    by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
  assert (HMACn : bytes_at rsegs (normalize rsegs mem) (g_S g - 110) macb)
    by (apply bytes_at_normalize; [exact HMI | exact HMAC]).
  assert (Q16n : bytes_at rsegs (normalize rsegs mem) (bv_unsigned (getr regs 2) + 16) (le8 (Z_to_bv 64 8904))).
  { rewrite Usp. replace (g_S g - 9072 + 16) with (fsp g + 16) by (unfold fsp, SLOT_FRAME; lia).
    apply bytes_at_normalize; [exact HMI | exact Q16]. }
  assert (Flo : 0x52000 <= g_S g - 65536) by lia.
  assert (Flo2 : g_S g - 65536 + 9280 <= g_S g) by lia.
  assert (Fag : bv_unsigned (getr regs 10) <> 0) by lia.
  assert (Fbd : bv_unsigned (getr regs 9) <> 0) by lia.
  assert (FDA : bv_unsigned (getr regs 10) + 8904 <= g_S g - 65536 \/ g_S g <= bv_unsigned (getr regs 10))
    by (left; lia).
  assert (FDB : bv_unsigned (getr regs 9) + 8904 <= g_S g - 65536 \/ g_S g <= bv_unsigned (getr regs 9))
    by (left; lia).
  assert (FDAB : bv_unsigned (getr regs 10) + 8904 <= bv_unsigned (getr regs 9) \/
                 bv_unsigned (getr regs 9) + 8904 <= bv_unsigned (getr regs 10)) by lia.
  set (Q := SceneTU.QT (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 10) (getr regs 9) fp_regs fp_csr
              (normalize rsegs mem) (g_S g - 65536) (g_S g) bb (saved_bytes ra g) macb).
  apply (sm_mid B APIf ra empty FF g 2 [(body, nbG g); (again, 8904)] L A regs mem md (Z_to_bv 64 0x151b4) Q
    (Post B APIf ra g) HF HP).
  - rewrite ss_mkR_of.
    exact (SceneTU.scene_T_x (getr regs 1) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 10)
      (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17)
      (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
      (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)
      (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 9) fp_regs fp_csr (normalize rsegs mem)
      (g_S g - 65536) (g_S g) bb (saved_bytes ra g) macb (ss_rd_list mem again 8904)
      BUILD CHECK MEMC BCMP Usp HS16 HSTK Flo Flo2 Fag Fbd (mem_inv_normalize rsegs mem) RWA HBn Lbb' HSVn Lsv
      HMACn Lmac Q16n FDA FDB FDAB).
  - intros ms HQ.
    destruct HQ as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18
      & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m' & E & Ex1 & Ex2 & Ex3
      & Ex4 & Ex8 & Ex9 & Ex10 & MU & WM & _ & _ & _ & SV' & _).
    rewrite Uag in MU.
    do 3 eexists. split; [exact E|].
    split; [exists [(g_S g - 9280, g_S g); (again, again + 8904)]; split; [exact MU|];
            split; [exact WM | exact (st_win g body (nbG g) again)]|].
    split; [exact SV'|]. split; [exact Ex2|]. split; [exact Ex3 | exact Ex4].
  - intros R pc' m0' regs' m' HQ Hx Hrel HF'.
    destruct HQ as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18
      & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m'' & E & Ex1 & Ex2 & Ex3
      & Ex4 & Ex8 & Ex9 & Ex10 & MU & WM & MI' & ST' & BB' & SV' & MB' & Q16').
    injection E as ER Epc Em. subst R pc' m0'.
    assert (G1 : getr regs' 1 = Z_to_bv 64 0x15294) by (rewrite (ss_getr_eqv _ _ 1 Hx); exact Ex1).
    assert (G10 : getr regs' 10 = Z_to_bv 64 again)
      by (rewrite (ss_getr_eqv _ _ 10 Hx); transitivity (getr regs 10); [exact Ex10 | exact H10]).
    assert (G9 : getr regs' 9 = Z_to_bv 64 body)
      by (rewrite (ss_getr_eqv _ _ 9 Hx); transitivity (getr regs 9); [exact Ex9 | exact H9]).
    assert (G8 : getr regs' 8 = Z_to_bv 64 (nG g))
      by (rewrite (ss_getr_eqv _ _ 8 Hx); transitivity (getr regs 8); [exact Ex8 | exact H8]).
    rewrite <- (ss_free_pc B APIf ra empty FF).
    apply (ss_free_step B APIf ra empty FF FREE g 2 [(body, nbG g)] again 8904 [] L A regs' m' md _ HF' HP).
    + unfold MMAP_THRESHOLD. lia.
    + rewrite G1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + exact G10.
    + intros L2 A2 regs2 mem2 md2 HF2 HP2 RP2 FRM2.
      rewrite G1. apply HX. exists body, L2, A2, regs2, mem2, md2. split; [reflexivity|].
      split; [exact HF2|]. split; [exact HP2|].
      assert (KEEPF : forall a bs, fsp g <= a -> a + Z.of_nat (length bs) <= g_S g ->
                        bytes_at rsegs m'' a bs -> bytes_at rsegs mem2 a bs).
      { intros a bs Ha Hb HB. apply (proj2 (bytes_at_rel rsegs m' m'' a bs Hrel)) in HB.
        apply (ss_bytes_mbyte rsegs m' mem2); [|exact HB]. intros i Hi. rewrite <- SEG. apply FRM2. lia. }
      rewrite Usp in Q16'.
      split; [transitivity (getr regs' 9); [exact (RP2 9 ltac:(unfold callee_saved; lia)) | exact G9]|].
      split; [transitivity (getr regs' 8); [exact (RP2 8 ltac:(unfold callee_saved; lia)) | exact G8]|].
      split; [exact HN|].
      split.
      { unfold q64. replace (fsp g + 16) with (g_S g - 9072 + 16) by (unfold fsp, SLOT_FRAME; lia).
        apply KEEPF; [unfold fsp, SLOT_FRAME; lia | rewrite length_le8; lia | exact Q16']. }
      split.
      * destruct (st_blk_raw g 2 [(body, nbG g)] L2 A2 regs2 mem2 md2 body (nbG g) HF2 HP2
          ltac:(left; reflexivity) ltac:(lia)) as (HR & HRL).
        exists (ss_rd_list mem2 body (Z.to_nat (nbG g))). split; [rewrite HRL; exact Hnb | exact HR].
      * exists macb. split; [exact Lmac|].
        apply KEEPF; [unfold fsp, SLOT_FRAME; lia | rewrite Lmac; lia | exact MB'].
Qed.

End T.
