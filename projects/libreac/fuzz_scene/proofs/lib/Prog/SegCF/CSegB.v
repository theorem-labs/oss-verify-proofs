From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Arr.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0 Contract FrameAPI MemNorm.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require SegBX SceneB.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneRun.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require memset_c reac_ctrl_build_scene_step_c check_step_c.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.SegCF Require Import CInv CTac.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg Require Import SInv STac SGlue SCut SMid.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

(* Segment B: from 0x14fa4 (a0 = body) the body fill, the scene step build and check run to the second malloc
   call (ra 0x15100, transfer path) or to 0x151dc. *)

Section B.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MALLOC : malloc_contract_cf B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Hypothesis MSET : memset_c.memset_contract.
Hypothesis BUILD : reac_ctrl_build_scene_step_c.reac_ctrl_build_scene_step_contract.
Hypothesis CHECK : check_step_c.check_step_contract.

Lemma sb_norm_eq : forall (m : word -> option byte) x, ~ in_img B x -> 0 <= x < 2 ^ 64 ->
  normalize rsegs m (wa x) = m (wa x).
Proof.
  intros m x Hni Hx. unfold normalize, Mem.ro_addr. rewrite wa_unsigned by exact Hx.
  rewrite (ss_noimg_fs B APIf ra empty FF x Hni). reflexivity.
Qed.

Lemma sb_blk_u8 : forall g km hb L A regs mem md a k,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (a, k) hb -> 0 <= k ->
  Arr.u8arr rsegs (normalize rsegs mem) a (ss_rd_list mem a (Z.to_nat k)) /\
  Z.of_nat (length (ss_rd_list mem a (Z.to_nat k))) = k.
Proof.
  intros g km hb L A regs mem md a k HF HP Hin Hk.
  destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md a k HF HP Hin) as (HB & H4 & Hc & _).
  pose proof alloc_ceiling_value as HAC.
  rewrite ss_rd_list_len. split; [|lia].
  split.
  - split; [lia|]. rewrite ss_rd_list_len. split; [lia|].
    intros i Hi. rewrite ?ss_rd_list_len in Hi. rewrite ss_rd_list_nth by exact Hi.
    destruct (HB (Z.of_nat i) ltac:(lia)) as (_ & (b & Hb) & Hni).
    unfold mrd. rewrite (sb_norm_eq mem (a + Z.of_nat i) Hni ltac:(lia)). unfold wa. rewrite Hb. reflexivity.
  - split; [lia|]. rewrite ?ss_rd_list_len. split; [lia|]. intros i Hi.
    destruct (HB i ltac:(lia)) as (_ & (b & Hb) & Hni).
    unfold wview. rewrite (sb_norm_eq mem (a + i) Hni ltac:(lia)). unfold wa. rewrite Hb. discriminate.
Qed.

Lemma sb_empty : empty = 0x30220.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
  exact H.
Qed.

(* The input block (or the empty input at empty) against a slot heap block, the frame and the bytes after the
   11 header bytes. *)
Lemma sb_input : forall g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  bytes_at rsegs (normalize rsegs mem) (g_p g + cG g) (skipn 11 (g_in g)) /\
  0 <= g_p g /\ g_p g + g_n g <= alloc_ceiling /\
  (forall a k, In (a, k) hb -> 1 <= k -> g_p g + g_n g <= a \/ a + k <= g_p g + cG g).
Proof.
  intros g km hb L A regs mem md HF HP.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _ & _ & _ & _ & _ & _ & HB0 & _).
  pose proof HGV as (Hn & Hnp & Hblk & _).
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  pose proof alloc_ceiling_value as HAC.
  pose proof sb_empty as HE.
  unfold MI in HMI. rewrite SEG in HMI.
  assert (Hc : 0 <= cG g <= 11 /\ cG g <= g_n g) by (unfold cG, cE, lenZ, g_n in *; lia).
  destruct Hnp as [[H0 Hp]|[H0 Hp]].
  - assert (Hnil : g_in g = []) by (unfold g_n in H0; destruct (g_in g); [reflexivity | cbn in H0; lia]).
    assert (Hc0 : cG g = 0) by (unfold cG, cE, lenZ; rewrite Hnil; reflexivity).
    rewrite Hnil, Hc0, Hp, HE. rewrite H0. split; [|split; [lia | split; [lia|]]].
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    + intros a k Hin Hk.
      destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md a k HF HP Hin) as (HB & _).
      destruct (Z_le_dec (0x30220 + 0) a) as [L1|L1]; [left; lia|].
      destruct (Z_le_dec (a + k) (0x30220 + 0)) as [L2|L2]; [right; lia|].
      exfalso. destruct (HB (0x30220 - a) ltac:(lia)) as (_ & _ & Hni). apply Hni.
      replace (a + (0x30220 - a)) with 0x30220 by lia. apply (ss_img_hi B APIf ra empty FF). lia.
  - assert (Hb : In (g_p g, g_n g) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hp).
    destruct (ss_blk_facts B APIf ra empty FF L A mem md (g_p g) (g_n g) 0 HMR Hb ltac:(lia))
      as (_ & H4 & Hcl & _).
    split; [|split; [lia | split; [lia|]]].
    + apply bytes_at_normalize; [exact HMI|].
      split; [lia|]. split.
      { rewrite length_skipn. unfold cG, cE, lenZ, g_n in *. lia. }
      intros i Hi. rewrite length_skipn in Hi.
      assert (Hc11 : cG g = 11) by (unfold cG, cE, lenZ, g_n in *; lia).
      rewrite Hc11. rewrite nth_error_skipn.
      pose proof (HB0 (g_p g) (g_n g) (11 + Z.of_nat i) Hp ltac:(unfold g_n; lia)) as E1.
      pose proof (Hblk (11 + Z.of_nat i) ltac:(unfold g_n in *; lia)) as E2.
      rewrite SEG in E1, E2. rewrite E2 in E1.
      replace (Z.to_nat (11 + Z.of_nat i)) with (11 + i)%nat in E1 by lia.
      unfold mrd, wa. unfold mbyte in E1.
      replace (g_p g + 11 + Z.of_nat i) with (g_p g + (11 + Z.of_nat i)) by lia. exact E1.
    + intros a k Hin Hk.
      destruct (Z_le_dec (g_p g + g_n g) a) as [L1|L1]; [left; exact L1|].
      destruct (Z_le_dec (a + k) (g_p g)) as [L2|L2]; [right; lia|].
      exfalso.
      destruct (ss_b0_facts B APIf ra empty FF L A mem md hb _ (g_p g) (g_n g) (Z.max a (g_p g) - g_p g) HMR HP Hp
        ltac:(lia)) as (_ & _ & Hnh).
      apply Hnh. exists a, k. split; [exact Hin | lia].
Qed.

Lemma sb_got : forall g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  bytes_at rsegs (normalize rsegs mem) 0x1ef60 (le8 (Z_to_bv 64 SegBX.TADDR)).
Proof.
  intros g km hb L A regs mem md HF.
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & Hrel & _).
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  unfold MI in HMI. rewrite SEG in HMI. unfold relro, G_img_c in Hrel. rewrite SEG in Hrel.
  apply bytes_at_normalize; [exact HMI|].
  assert (CHK : ss_rel_chk 0x1ef60 (le8 (Z_to_bv 64 SegBX.TADDR)) = true) by (vm_compute; reflexivity).
  split; [lia|]. split; [rewrite length_le8; lia|].
  intros i Hi. rewrite length_le8 in Hi.
  rewrite <- (ss_rel_chk_ok _ _ CHK i Hi).
  pose proof (Hrel (0x1ef60 + Z.of_nat i) ltac:(exists 0x1eee8, 168; split; [left; reflexivity | lia])) as E.
  unfold mbyte in E. unfold mrd, wa. exact E.
Qed.

Lemma sb_win : forall g body nb lo hi y, In (lo, hi) [(g_S g - 9296, g_S g); (body, body + nb)] -> lo <= y < hi ->
  kreg g [(body, nb)] y \/ g_S g - 104 <= y < g_S g.
Proof.
  intros g body nb lo hi y Hin Hy. cbn [In] in Hin.
  destruct Hin as [Ew|[Ew|[]]]; injection Ew as <- <-.
  - destruct (Z_lt_le_dec y (g_S g - 104)) as [Hl|Hl]; [left; left; unfold SLOT_K, SLOT_STACK; lia | right; lia].
  - left. right. exists body, nb. split; [left; reflexivity | lia].
Qed.

Lemma seg_B_cf : Hcut_cf B APIf ra (Inv_K15100 B APIf ra empty) -> Hcut_cf B APIf ra (Inv_K151dc B APIf ra empty) ->
  Hcut_cf B APIf ra (Inv_K14fa4 B APIf ra empty).
Proof.
  intros HXa HXb g c HCAP (body & HC).
  eapply (cut_open_cf B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (H10 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & (macb & Lmac & HMAC)).
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  pose proof (ss_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (_ & HIH & H8k & HfS & HSc & HS47 & HSK & Hsp).
  unfold IMG_HI in HIH.
  pose proof HF as (HGV & _ & _ & _ & Hsv & _ & HMI & _).
  pose proof HGV as (Hn0 & _ & _ & HS16 & _).
  pose proof alloc_ceiling_value as HAC.
  unfold MI in HMI. rewrite SEG in HMI.
  pose proof (nbG_range g) as Hnb. pose proof (nG_range g) as HnG.
  pose proof (gbz_range (g_in g) 0) as Hg0. pose proof (gbz_range (g_in g) 3) as Hg3.
  pose proof (gbz_range (g_in g) 4) as Hg4.
  assert (Hbin : In (body, nbG g) [(body, nbG g)]) by (left; reflexivity).
  destruct (ss_hb_blk B APIf ra empty FF g _ _ L A regs mem md body (nbG g) HF HP Hbin) as (_ & Hb4 & Hbc & _).
  destruct (sb_blk_u8 g _ _ L A regs mem md body (nbG g) HF HP Hbin ltac:(lia)) as (HU8 & HL8).
  destruct (sb_input g _ _ L A regs mem md HF HP) as (HIN & Hp0 & Hpc & HDJ).
  assert (Hc : 0 <= cG g <= 11 /\ cG g <= g_n g) by (unfold cG, cE, lenZ, g_n in *; lia).
  assert (Hlo : body + nbG g <= g_S g - 65536).
  { destruct (ss_hb_low B APIf ra empty FF g _ _ L A regs mem md (body + nbG g - 1) HF HP
      (ss_hb_in1 body (nbG g) (body + nbG g - 1) ltac:(lia))) as (_ & H2). unfold SLOT_K, SLOT_STACK in H2. lia. }
  assert (Ubd : bv_unsigned (getr regs 10) = body) by (rewrite H10; apply unsigned_lit; lia).
  assert (Usp : bv_unsigned (getr regs 2) = g_S g - 9072) by (rewrite Hsp; unfold fsp, SLOT_FRAME; apply unsigned_lit; lia).
  assert (Us2 : bv_unsigned (getr regs 18) = SegBX.nbE (nG g))
    by (change (SegBX.nbE (nG g)) with (nbG g); rewrite H18; apply unsigned_lit; lia).
  assert (Us3 : bv_unsigned (getr regs 19) = g_p g + cG g) by (rewrite H19; apply unsigned_lit; lia).
  assert (Us6 : bv_unsigned (getr regs 22) = g_n g - cG g) by (rewrite H22; apply unsigned_lit; lia).
  assert (Us8 : bv_unsigned (getr regs 24) = nG g) by (rewrite H24; apply unsigned_lit; lia).
  assert (Lin : Z.of_nat (length (skipn 11 (g_in g))) = g_n g - cG g)
    by (rewrite length_skipn; unfold cG, cE, lenZ, g_n in *; lia).
  assert (Ev : (gbz (g_in g) 3 + 256 * gbz (g_in g) 4) / 256 = gbz (g_in g) 4)
    by (Z.div_mod_to_equations; lia).
  assert (HSVn : bytes_at rsegs (normalize rsegs mem) (g_S g - 104) (saved_bytes ra g))
    by (apply bytes_at_normalize; [exact HMI | exact Hsv]).
  assert (HMACn : bytes_at rsegs (normalize rsegs mem) (g_S g - 110) macb)
    by (apply bytes_at_normalize; [exact HMI | exact HMAC]).
  pose proof (ss_fr_stk B APIf ra empty FF g _ _ L A regs mem md HF) as HSTK.
  unfold SLOT_K, SLOT_STACK in HSTK.
  set (Q := fun ms =>
    SceneB.QBa (getr regs 3) (getr regs 4) fp_regs fp_csr (normalize rsegs mem) (g_S g - 65536) (g_S g)
      (getr regs 10) (SegBX.nbE (nG g)) (nG g) (g_p g + cG g) (skipn 11 (g_in g)) (saved_bytes ra g) macb
      (getr regs 2) ms \/
    SceneB.QBb (getr regs 3) (getr regs 4) fp_regs fp_csr (normalize rsegs mem) (g_S g - 65536) (g_S g)
      (getr regs 10) (SegBX.nbE (nG g)) (nG g) (g_p g + cG g) (skipn 11 (g_in g)) (saved_bytes ra g) macb
      (getr regs 2) ms).
  apply (sm_mid_cf B APIf ra empty FF g 1 [(body, nbG g)] L A regs mem md (Z_to_bv 64 0x14fa4) Q
    (Post B APIf ra g) HF HP).
  - rewrite ss_mkR_of. rewrite H20, H21, H23.
    replace (Z_to_bv 64 (stG g)) with (Z_to_bv 64 (SegBX.sx16 (gbz (g_in g) 3 + 256 * gbz (g_in g) 4)))
      by reflexivity.
    replace (Z_to_bv 64 (s7G g))
      with (Z_to_bv 64 (SegBX.sx16 (256 * ((gbz (g_in g) 3 + 256 * gbz (g_in g) 4) / 256))))
      by (rewrite Ev; reflexivity).
    assert (F3 : g_S g < 2 ^ 64) by lia.
    assert (F5 : g_S g - 65536 + 9296 <= g_S g) by lia.
    assert (F6 : bv_unsigned (getr regs 10) <> 0) by lia.
    assert (F8 : Arr.u8arr rsegs (normalize rsegs mem) (bv_unsigned (getr regs 10)) (ss_rd_list mem body (Z.to_nat (nbG g))))
      by (rewrite Ubd; exact HU8).
    assert (F9 : bv_unsigned (getr regs 10) + SegBX.nbE (nG g) <= g_S g - 65536) by (rewrite Ubd; exact Hlo).
    assert (F14 : 0 <= nG g < 65536) by lia.
    assert (F15 : 0 <= flG g < 256) by (unfold flG; lia).
    assert (F16 : 0 <= gbz (g_in g) 3 + 256 * gbz (g_in g) 4 < 65536) by lia.
    assert (F19 : g_p g + cG g + (g_n g - cG g) <= bv_unsigned (getr regs 10) \/
                  bv_unsigned (getr regs 10) + SegBX.nbE (nG g) <= g_p g + cG g).
    { rewrite Ubd. destruct (HDJ body (nbG g) Hbin ltac:(lia)) as [Hd|Hd]; [left; lia | right; exact Hd]. }
    assert (F20 : g_p g + cG g + (g_n g - cG g) <= g_S g - 65536 \/ g_S g <= g_p g + cG g) by (left; lia).
    exact (SceneB.scene_B_x (getr regs 3) (getr regs 4) fp_regs fp_csr MSET BUILD CHECK
      (getr regs 1) (getr regs 2) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9)
      (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16)
      (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 22) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)
      (normalize rsegs mem) (g_S g) (g_S g - 65536) (nG g) (g_n g - cG g) (g_p g + cG g) (flG g)
      (gbz (g_in g) 3 + 256 * gbz (g_in g) 4)
      (ss_rd_list mem body (Z.to_nat (nbG g))) (skipn 11 (g_in g)) (saved_bytes ra g) macb
      Usp HS16 F3 HSTK F5 F6 HL8 F8 F9 Us2 Us3 Us6 Us8 F14 F15 F16 HIN Lin F19 F20 HSVn HMACn
      (sb_got g _ _ L A regs mem md HF) (mem_inv_normalize rsegs mem)).
  - intros ms [HQ|HQ].
    + destruct HQ as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18
        & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m' & bb & E & Ex1 & Ex2 & Ex3
        & Ex4 & Ex9 & Ex10 & Hn & Hnbq & Q8 & Q16 & MU & WM & _ & _ & SV' & _).
      rewrite Ubd in MU. change (SegBX.nbE (nG g)) with (nbG g) in MU.
      do 3 eexists. split; [exact E|].
      split; [exists [(g_S g - 9296, g_S g); (body, body + nbG g)]; split; [exact MU|];
              split; [exact WM | exact (sb_win g body (nbG g))]|].
      split; [exact SV'|]. split; [exact Ex2|]. split; [exact Ex3 | exact Ex4].
    + destruct HQ as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18
        & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m' & bb & E & Ex2 & Ex3 & Ex4
        & Ex9 & Ex18 & Ex24 & MU & WM & _ & _ & SV' & _).
      rewrite Ubd in MU. change (SegBX.nbE (nG g)) with (nbG g) in MU.
      do 3 eexists. split; [exact E|].
      split; [exists [(g_S g - 9296, g_S g); (body, body + nbG g)]; split; [exact MU|];
              split; [exact WM | exact (sb_win g body (nbG g))]|].
      split; [exact SV'|]. split; [exact Ex2|]. split; [exact Ex3 | exact Ex4].
  - intros R pc' m0' regs' m' HQ Hx Hrel HF'.
    destruct HQ as [HQ|HQ].
    + destruct HQ as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18
        & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m'' & bb & E & Ex1 & Ex2 & Ex3
        & Ex4 & Ex9 & Ex10 & Hn & Hnbq & Q8 & Q16 & MU & WM & MI' & ST' & SV' & MB' & IN' & Lbb & BB' & WR').
      injection E as ER Epc Em. subst R pc' m0'.
      assert (G1 : getr regs' 1 = Z_to_bv 64 0x15100) by (rewrite (ss_getr_eqv _ _ 1 Hx); exact Ex1).
      assert (G10 : getr regs' 10 = Z_to_bv 64 8904) by (rewrite (ss_getr_eqv _ _ 10 Hx); exact Ex10).
      assert (G9 : getr regs' 9 = Z_to_bv 64 body)
        by (rewrite (ss_getr_eqv _ _ 9 Hx); transitivity (getr regs 10); [exact Ex9 | exact H10]).
      rewrite Hnbq in Q8. rewrite Hn in Q16.
      rewrite <- (ss_malloc_pc B APIf ra empty FF).
      apply (ss_malloc_step_cf B APIf ra empty FF MALLOC LIMLAW g HCAP 1 [(body, nbG g)] L A regs' m' md 8904 _ HF' HP).
      * cbn. lia.
      * unfold hb_bytes. cbn. lia.
      * lia.
      * rewrite G1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
      * exact G10.
      * intros L2 A2 regs2 mem2 md2 res HF2 HP2 RP2 R10 Hr0 FRM2 HBM2.
        rewrite G1. apply HXa; [exact HCAP|]. exists body, res, L2, A2, regs2, mem2, md2. split; [reflexivity|].
        split; [exact HF2|]. split; [exact HP2|].
        assert (KEEPF : forall a bs, fsp g <= a -> a + Z.of_nat (length bs) <= g_S g ->
                          bytes_at rsegs m'' a bs -> bytes_at rsegs mem2 a bs).
        { intros a bs Ha Hb HB. apply (proj2 (bytes_at_rel rsegs m' m'' a bs Hrel)) in HB.
          apply (ss_bytes_mbyte rsegs m' mem2); [|exact HB]. intros i Hi. rewrite <- SEG. apply FRM2. lia. }
        split; [exact R10|].
        split; [transitivity (getr regs' 9); [exact (RP2 9 ltac:(unfold callee_saved; lia)) | exact G9]|].
        split; [exact Hn|].
        split.
        { unfold q64. replace (fsp g + 8) with (g_S g - 9064) by (unfold fsp, SLOT_FRAME; lia).
          apply KEEPF; [unfold fsp, SLOT_FRAME; lia | rewrite length_le8; lia | exact Q8]. }
        split.
        { unfold q64. replace (fsp g + 16) with (g_S g - 9056) by (unfold fsp, SLOT_FRAME; lia).
          apply KEEPF; [unfold fsp, SLOT_FRAME; lia | rewrite length_le8; lia | exact Q16]. }
        split.
        -- exists bb. split; [rewrite Lbb; exact Hnbq|].
           apply (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel)) in BB'. rewrite Ubd in BB'.
           apply (ss_bytes_mbyte rsegs m' mem2); [|exact BB'].
           intros i Hi. rewrite <- SEG. apply (HBM2 body (nbG g) i); [left; reflexivity|].
           rewrite Lbb in Hi. change (SegBX.nbE (nG g)) with (nbG g) in Hi. lia.
        -- exists macb. split; [exact Lmac|].
           apply KEEPF; [unfold fsp, SLOT_FRAME; lia | rewrite Lmac; lia | exact MB'].
    + destruct HQ as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18
        & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m'' & bb & E & Ex2 & Ex3 & Ex4
        & Ex9 & Ex18 & Ex24 & MU & WM & MI' & ST' & SV' & MB' & IN' & Lbb & BB' & WR').
      injection E as ER Epc Em. subst R pc' m0'.
      apply HXb; [exact HCAP|]. exists body, 1. split; [left; reflexivity|].
      exists L, A, regs', m', md. split; [reflexivity|]. split; [exact HF'|]. split; [exact HP|].
      split; [rewrite (ss_getr_eqv _ _ 9 Hx); transitivity (getr regs 10); [exact Ex9 | exact H10]|].
      split; [rewrite (ss_getr_eqv _ _ 18 Hx); exact Ex18|].
      split; [rewrite (ss_getr_eqv _ _ 24 Hx); exact Ex24|].
      split.
      * exists bb. split; [exact Lbb|]. apply (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel)). rewrite <- Ubd. exact BB'.
      * exists macb. split; [exact Lmac|]. apply (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel)). exact MB'.
Qed.

End B.
