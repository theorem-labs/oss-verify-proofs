From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Cells.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import memcpy_c memset_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import reac_ctrl_scene_set_mac_c reac_ctrl_scene_build_c.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require SceneDU.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0 Contract FrameAPI MemNorm.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.SegCF Require Import CInv CTac.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require Import SInv STac SGlue SCut SMid.
Import ListNotations.
Open Scope Z_scope.

(* Segment D: 0x152a0 (a0 = before, just returned from malloc) runs scene_D_x to the call free(before) at
   0x16928 with ra 0x15450; free returns to 0x15450 with body still allocated. *)

Lemma sd_rd_bytes : forall (mem : word -> option byte) a k,
  0 <= a -> a + k <= 2 ^ 64 -> 0 <= k ->
  (forall i, 0 <= i < k -> present mem (a + i)) ->
  bytes_at rsegs mem a (ss_rd_list mem a (Z.to_nat k)).
Proof.
  intros mem a k H0 H1 Hk HP. split; [exact H0|].
  split; [rewrite ss_rd_list_len, Z2Nat.id by lia; lia|].
  intros i Hi. rewrite ss_rd_list_len in Hi. rewrite ss_rd_list_nth by exact Hi.
  pose proof (proj1 (Nat2Z.inj_lt _ _) Hi) as Hi'. rewrite Z2Nat.id in Hi' by lia.
  destruct (HP (Z.of_nat i) ltac:(lia)) as (b & Eb).
  unfold Mem.mrd, Mem.wa. rewrite Eb. reflexivity.
Qed.

Section D.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FREE : free_contract_cf B (APIf rc).
Hypothesis MEMC : memcpy_contract.
Hypothesis MEMS : memset_contract.
Hypothesis BCMPc : bcmp_contract.
Hypothesis SETMAC : reac_ctrl_scene_set_mac_contract.
Hypothesis SBUILD : reac_ctrl_scene_build_contract.

Lemma sd_rw_blk : forall g km hb L A regs mem md a k bs,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (a, k) hb ->
  Z.of_nat (length bs) = k -> bytes_at rsegs mem a bs ->
  Step.rw_cells rsegs (normalize rsegs mem) a [Cells.CB (Z.to_nat k) bs].
Proof.
  intros g km hb L A regs mem md a k bs HF HP Hin Hl HB. subst k.
  destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md a _ HF HP Hin) as (HW & H4 & Hc & _).
  destruct (ss_fr_bnd B APIf ra empty FF g km hb L A regs mem md HF) as (_ & _ & _ & _ & HRO).
  pose proof (@alloc_ceiling_lt rc) as HAC.
  split.
  - split.
    + cbn [Cells.cells_wf Cells.cell_wf]. split; [rewrite Nat2Z.id; reflexivity | exact I].
    + cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r. exact (bytes_at_normalize rsegs mem a bs HRO HB).
  - cbn [Cells.cells_size Cells.csize]. rewrite Nat.add_0_r, Nat2Z.id.
    apply (wr_at_norm rsegs mem (normalize rsegs mem) a _ (mem_rel_normalize rsegs mem HRO)).
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (HW i Hi) as (W & _ & _).
      rewrite (ss_segs B APIf ra empty FF) in W. exact W.
    + intros i Hi. destruct (HW i Hi) as (_ & _ & NI).
      unfold Mem.ro_addr. rewrite wa_unsigned by lia. rewrite (ss_noimg_fs B APIf ra empty FF _ NI). reflexivity.
Qed.

Lemma sd_disj : forall g km a1 k1 a2 k2 L A regs mem md,
  FR B APIf ra empty g km [(a1, k1); (a2, k2)] L A regs mem md ->
  Permutation (blocks L A) ([(a1, k1); (a2, k2)] ++ blocks (g_L g) (g_A g)) ->
  a1 + k1 <= a2 \/ a2 + k2 <= a1.
Proof.
  intros g km a1 k1 a2 k2 L A regs mem md HF HP.
  pose proof (mr_blocks_disjoint B _ (aa_laws (APIf rc)) L A mem md (FR_MR B APIf ra empty _ _ _ _ _ _ _ _ HF))
    as Hpw.
  pose proof (ss_pw_perm ranges_disjoint ltac:(intros u v; unfold ranges_disjoint; lia) _ _ HP Hpw) as Hpw'.
  destruct Hpw' as (H1 & _).
  specialize (H1 (a2, k2) (or_introl eq_refl)). unfold ranges_disjoint in H1. cbn [fst snd] in H1. exact H1.
Qed.

Lemma seg_D_cf : Hcut_cf B APIf ra (Inv_K15450 B APIf ra empty) -> Hcut_cf B APIf ra (Inv_K152a0 B APIf ra empty).
Proof.
  intros HX g c HCAP (body & before & km & Hkm & HC).
  eapply (cut_open_cf B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (H10 & H9 & H8 & (bb & Hbb & HBB) & (macb & Hlen & HMB)).
  pose proof HF as (_ & _ & _ & _ & HSV & _).
  pose proof (ss_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (_ & HIH & H8k & HfS & _ & HS47 & HSK & Hsp).
  unfold IMG_HI in HIH.
  pose proof (ss_fr_stk B APIf ra empty FF g _ _ L A regs mem md HF) as STN.
  destruct (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (_ & _ & _ & _ & HRO).
  pose proof (@alloc_ceiling_lt rc) as HAC.
  pose proof (nbG_range g) as Hnb. pose proof (nG_range g) as Hn.
  set (hb := [(body, nbG g); (before, nbG g)]).
  assert (InB : In (body, nbG g) hb) by (unfold hb; left; reflexivity).
  assert (InF : In (before, nbG g) hb) by (unfold hb; right; left; reflexivity).
  destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md body _ HF HP InB) as (HWB & B4 & Bc & _).
  destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md before _ HF HP InF) as (HWF & F4 & Fc & _).
  assert (LB : in_hb hb (body + nbG g - 1)) by (exists body, (nbG g); split; [exact InB | lia]).
  apply (ss_hb_low B APIf ra empty FF g km hb L A regs mem md _ HF HP) in LB as (_ & LBh).
  assert (LF : in_hb hb (before + nbG g - 1)) by (exists before, (nbG g); split; [exact InF | lia]).
  apply (ss_hb_low B APIf ra empty FF g km hb L A regs mem md _ HF HP) in LF as (_ & LFh).
  pose proof (sd_disj g km body (nbG g) before (nbG g) L A regs mem md HF HP) as DJ.
  assert (UB : bv_unsigned (Z_to_bv 64 body) = body) by (apply unsigned_lit; lia).
  assert (UF : bv_unsigned (Z_to_bv 64 before) = before) by (apply unsigned_lit; lia).
  assert (RWB : Step.rw_cells rsegs (normalize rsegs mem) body [Cells.CB (Z.to_nat (nbG g)) bb])
    by exact (sd_rw_blk g km hb L A regs mem md body (nbG g) bb HF HP InB Hbb HBB).
  assert (RWF : Step.rw_cells rsegs (normalize rsegs mem) before
                  [Cells.CB (Z.to_nat (nbG g)) (ss_rd_list mem before (Z.to_nat (nbG g)))]).
  { apply (sd_rw_blk g km hb L A regs mem md before (nbG g) _ HF HP InF).
    - rewrite ss_rd_list_len, Z2Nat.id by lia. reflexivity.
    - apply sd_rd_bytes; [lia | lia | lia |]. intros i Hi. exact (proj1 (proj2 (HWF i Hi))). }
  apply (sm_mid_cf B APIf ra empty FF g km hb L A regs mem md (Z_to_bv 64 0x152a0)
    (SceneDU.QD (Z_to_bv 64 (fsp g)) (getr regs 3) (getr regs 4) (Z_to_bv 64 body) (Z_to_bv 64 before)
       fp_regs fp_csr (normalize rsegs mem) (g_S g - 65536) (g_S g) (nbG g) (saved_bytes ra g))
    (Post B APIf ra g) HF HP).
  - rewrite ss_mkR_of. rewrite Hsp, H9, H10, H8.
    apply SceneDU.scene_D_x with (n := nG g) (bb := bb) (jb := ss_rd_list mem before (Z.to_nat (nbG g)))
      (macb := macb).
    + exact MEMC.
    + exact MEMS.
    + exact BCMPc.
    + exact SETMAC.
    + exact SBUILD.
    + rewrite unsigned_lit by lia. lia.
    + replace (g_S g - 65536) with (g_S g - SLOT_K) by lia. exact STN.
    + lia.
    + rewrite UF. lia.
    + rewrite UB. lia.
    + apply unsigned_lit. lia.
    + lia.
    + reflexivity.
    + apply mem_inv_normalize.
    + rewrite UB. exact RWB.
    + rewrite UF. exact RWF.
    + exact (bytes_at_normalize rsegs mem _ _ HRO HMB).
    + exact Hlen.
    + exact (bytes_at_normalize rsegs mem _ _ HRO HSV).
    + unfold saved_bytes. rewrite !length_app, !length_le8. reflexivity.
    + rewrite UB, UF. exact DJ.
    + rewrite UB. left. lia.
    + rewrite UF. left. lia.
  - intros ms HQ.
    destruct HQ as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 &
      x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m2 & -> & E1 & E2 & E3 &
      E4 & E9 & E10 & MU & WM & _ & _ & SV).
    do 3 eexists. split; [reflexivity|].
    split.
    { eexists. split; [exact MU|]. split; [exact WM|].
      intros lo hi y Hin Hy. rewrite UB, UF in Hin. unfold kreg, in_hb.
      cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E; intros; subst lo hi.
      - destruct (Z_lt_dec y (g_S g - 104)) as [Hl|Hl]; [left; left; lia | right; lia].
      - left; right. exists body, (nbG g). split; [exact InB | lia].
      - left; right. exists before, (nbG g). split; [exact InF | lia]. }
    split; [exact SV|].
    split; [rewrite E2, Hsp; reflexivity|].
    split; [rewrite E3; reflexivity | rewrite E4; reflexivity].
  - intros R pc' m0' regs' m' HQ XR _ HF'.
    destruct HQ as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 &
      x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m2 & E & E1 & E2 & E3 &
      E4 & E9 & E10 & _).
    injection E; intros; subst.
    assert (G1 : getr regs' 1 = Z_to_bv 64 0x15450) by (rewrite (ss_getr_x _ _ 1 XR) by reflexivity; reflexivity).
    assert (G9 : getr regs' 9 = Z_to_bv 64 body) by (rewrite (ss_getr_x _ _ 9 XR) by reflexivity; reflexivity).
    assert (G10 : getr regs' 10 = Z_to_bv 64 before)
      by (rewrite (ss_getr_x _ _ 10 XR) by reflexivity; reflexivity).
    rewrite <- (ss_free_pc B APIf ra empty FF).
    apply (ss_free_step_cf B APIf ra empty FF FREE g km [(body, nbG g)] before (nbG g) [] L A regs' m' md _ HF' HP).
    + unfold MMAP_THRESHOLD. lia.
    + rewrite G1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + exact G10.
    + intros L' A' regs2 mem2 md2 HF2 HP2 RP2 _.
      rewrite G1. apply HX; [exact HCAP|]. exists body, km. exists L', A', regs2, mem2, md2. split; [reflexivity|].
      split; [exact HF2|]. split; [exact HP2|].
      pose proof (ss_CSeq_pres _ _ RP2) as CS. ss_cs CS 9. exact G9.
Qed.

End D.
