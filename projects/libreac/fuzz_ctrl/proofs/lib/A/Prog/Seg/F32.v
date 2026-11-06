(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its numbers changed; 2046 of its 2082 lines of code are new or changed and 360 lines of the source are left out. *)
(* Segment F32 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x827d8-0x82858 with the side blocks
   0x82a20-0x82a28 and 0x82a74-0x82a7c (plan-asan section 2 row F32, call CAT@0x82858).
   rule 24: no function proved.
   v1.9 STATUS (2026-10-28): UNVERIFIED.  No build without probes has checked this file on v1.9.0.  It closed only
   in an ITERATION-ONLY build on the v1.9 bytes (FACTS 0bfe9aa0d452) with probes in Seg/Tac_slot.v and
   Seg/Tac_fsfree.v.  It waits for Seg/Tac_slot.v / Tac_fsfree.v re-fit to the regenerated Contract.v and FrameAPI.v.

   Cuts: the official SlotInv.v bodies (a working branch, push 11B and later).  Two entries (F31 reaches
   both): Inv_A827d8_at (the bcmp result, classify = Some e; FLS) and Inv_A82800_at (the join, entered from 0x82798
   when classify is not Some; FLS).  Two exits: Inv_A828c8_at (t_rowsel = false, memory unchanged; FLS, s8 still
   holds the kind) and Inv_A8285c_at (t_rowsel = true, after the catalogue call; FLSX by flsx_of_fls, since
   `ld s8,40(s1)` at 0x8284c overwrote the kind with fr + 32).  Every body ends with LT (IFS of turn j + 1), which
   this segment hands on unchanged.  FLS's record part is guarded by `50 <= flen g j`: on the entry 0x827d8 it
   follows from classify = Some e, at the join from k = 9 (f32_k_big); the k <> 9 arm does not read it.

     0x827d8  beqz a0,82bf4   -- NOT taken: a0 = 0 iff q.src = our (F31's iff) and classify = Some e says
                                 q.src <> our (RcClassifyLib.classify_some's cl_eq6 clause).
     0x827dc-0x827ec          -- a0 = [A+152] | [A+280], andi 1, beqz NOT taken: [A+152] = tfill,
                                 [A+280] = sum_ok (FLS) and classify = Some e gives sum_ok or tfill (TF).
     0x827f0-0x827fc          -- a0 = the 4 bytes at fr + 528 (the classify event e; [A+160] = fr + 528 is FLSI's),
                                 bgeu a0,6 NOT taken (0 <= e <= 5 from classify_some).
     0x82800  bne s8,9        -- k <> 9: to 0x828c8 (t_rowsel = false).
     0x82804-0x82818          -- the instrumented check of the byte at phi + 16: the code loads the shadow byte
                                 at (phi+16 >> 3) + K; when it is 0 the check passes at once, else the side block
                                 0x82a20 compares (phi+16) mod 8 with it and falls to 0x8281c.  phi is addressable
                                 for len >= 50 bytes (HB, FLS's 50 <= len), so the error path at 0x82cf4 is not
                                 reached.  The same for phi + 17 (side block 0x82a74, error path 0x82d14).
     0x8281c-0x82844          -- the two byte tests (205, 234): a mismatch goes to 0x828c8 (rowsel = false).
     0x82848  sb zero,4(s3)   -- the shadow byte of the count variable [fr+32, fr+40) is set to 0 (in scope).
     0x8284c-0x82850          -- s8 = [A+40] = fr + 32 (FLSI); the count is cleared.
     0x82858  jal reac_box_catalogue(fr + 32) -> 0x8285c with a0 = BOX_CATALOGUE and [fr+32] = 11.

   The catalogue contract is the Section Hypothesis CATC; the run is a Lib.Exec.evt (the contract's level) and is
   closed with Seg/Tac_b5.v's sl_run_lib.  It needs no mem_inv (its mem_inv clause is a conditional
   the proof does not use); ro_agree after the run is kept because the write set is above the image.  FRA moves
   across the catalogue path with f32_fra_w, ENT with Tac_slot.ent_store and ent_mat; the window and frame
   placement come from SlotInv's fra_win / fra_frame / fra_app. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcClassify RcClassifyLib
  RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 is the plain one here; the slot's
   cuts (ENT reads the FP state) are stated with the image-A one, which this alias names. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module CATc := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module ULF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.

(* The kernel compares cl_bsum fr with blocksum (skipn 18 fr) slowly unless cl_bsum is unfolded first (as in the
   ubsan Tac_b8m). *)
#[local] Strategy expand [cl_bsum].

(* ================= model facts of turn j (image-A twins of the ubsan Tac_b8m / Tac_b8c lemmas) ============== *)

Lemma f32_bz_range : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma f32_fL_nonneg : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb.
  pose proof (f32_bz_range (nthb inp (Z.to_nat c))). pose proof (f32_bz_range (nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma f32_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fc]. unfold c0, nlen. lia.
  - change (fc inp (S j)) with (f_next inp (fc inp j)). pose proof (f32_fL_nonneg inp (fc inp j)).
    unfold f_next, f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma f32_t_facts : forall inp j,
  0 <= t_c inp j <= nlen inp /\ t_left inp j = nlen inp - t_c inp j /\
  0 <= t_h inp j <= t_left inp j /\ 0 <= t_len inp j <= t_left inp j - t_h inp j /\
  t_body inp j = t_c inp j + t_h inp j.
Proof.
  intros inp j. pose proof (f32_fc_range inp j) as R. pose proof (f32_fL_nonneg inp (fc inp j)) as L.
  unfold t_c, t_left, t_h, t_len, t_body. unfold f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma f32_phi_length : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (f32_t_facts inp j) as (R & EL & (H1 & H2) & (H3 & H4) & EB).
  unfold t_phi, f_phi. rewrite length_firstn, length_skipn.
  change (f_len inp (fc inp j)) with (t_len inp j). change (f_body inp (fc inp j)) with (t_body inp j).
  unfold nlen in *. lia.
Qed.

Lemma f32_k_range : forall inp j, 0 <= t_k inp j <= 13.
Proof. intros inp j. unfold t_k. apply ctrlparse_kind_range. Qed.

Lemma f32_k_big : forall inp j, t_k inp j <> 0 -> 50 <= t_len inp j.
Proof.
  intros inp j K. destruct (Z_le_gt_dec 50 (t_len inp j)) as [H|H]; [exact H|].
  exfalso. apply K. unfold t_k. apply ctrlparse_none. intros (HC & _ & _). lia.
Qed.

Lemma f32_fr50_firstn : forall bs, (50 <= length bs)%nat -> fr50 bs = firstn 50 bs.
Proof.
  intros bs H. unfold fr50. rewrite firstn_app.
  replace (50 - length bs)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma f32_g_nth : forall inp j i, 50 <= t_len inp j -> (i < 50)%nat ->
  nth i (t_g inp j) cp_z = nth i (t_phi inp j) cp_z.
Proof.
  intros inp j i H Hi. unfold t_g. rewrite f32_fr50_firstn by (rewrite f32_phi_length; lia).
  rewrite nth_firstn. destruct (Nat.ltb_spec i 50); [reflexivity | lia].
Qed.

Lemma f32_cls_e : forall inp j e, t_cls inp j = Some e ->
  0 <= e <= 5 /\ t_k inp j <> 0 /\ 50 <= t_len inp j.
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (classify_some _ _ _ _ H) as (K & HN & _ & _ & _ & He).
  split; [exact He|]. split; [exact K | exact HN].
Qed.

Lemma f32_struct_src : forall fr k,
  firstn 6 (skipn 4 (cp_struct fr k)) = [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11].
Proof. intros fr k. unfold cp_struct. destruct (cp_rec fr), (k =? 6); reflexivity. Qed.

Lemma f32_cl_eq6_refl : forall xs, cl_eq6 xs xs = true.
Proof. intros xs. unfold cl_eq6. apply forallb_forall. intros i _. apply Z.eqb_refl. Qed.

Lemma f32_cls_src : forall inp j e, t_cls inp j = Some e ->
  firstn 6 (skipn 4 (t_B inp j)) <> OUR inp.
Proof.
  intros inp j e H E. unfold t_cls in H.
  destruct (classify_some _ _ _ _ H) as (K & HN & _ & EQ6 & _ & _).
  assert (HB : t_B inp j = cp_struct (t_g inp j) (t_k inp j)).
  { unfold t_B, t_k. exact (proj2 (cl_hdr _ _ K)). }
  rewrite HB, f32_struct_src in E.
  assert (C : cl_eq6 (skipn 6 (t_g inp j)) (OUR inp) = true).
  { rewrite <- cl_eq6_src. rewrite E. apply f32_cl_eq6_refl. }
  rewrite EQ6 in C. discriminate C.
Qed.

Lemma f32_cls_TF : forall inp j e, t_cls inp j = Some e ->
  t_sum_ok inp j = true \/ t_tfill inp j = true.
Proof.
  intros inp j e H.
  pose proof (f32_cls_e inp j e H) as (_ & _ & HN).
  assert (HBig : t_big inp j = true) by (unfold t_big; apply Z.leb_le; exact HN).
  unfold t_cls in H. destruct (classify_some _ _ _ _ H) as (_ & _ & _ & _ & KB & _).
  destruct KB as [K1|B0].
  - right. unfold t_tfill. rewrite HBig.
    assert (HF : fst (ctrlparse (t_len inp j) (t_g inp j)) = 1) by exact K1.
    apply ctrlparse_filler in HF. destruct HF as (_ & E16 & E17).
    rewrite E16, E17. reflexivity.
  - left. unfold t_sum_ok. rewrite HBig. unfold cl_bsum in B0. rewrite B0. reflexivity.
Qed.

Lemma f32_rowsel_k : forall inp j, t_k inp j <> 9 -> t_rowsel inp j = false.
Proof.
  intros inp j K. unfold t_rowsel. rewrite (proj2 (Z.eqb_neq _ _) K). reflexivity.
Qed.

Lemma f32_rowsel_16 : forall inp j, t_k inp j = 9 ->
  bv_unsigned (nth 16 (t_phi inp j) cp_z) <> 205 -> t_rowsel inp j = false.
Proof.
  intros inp j K H16.
  assert (HN : 50 <= t_len inp j) by (apply f32_k_big; lia).
  unfold t_rowsel. rewrite K. unfold cp_v, cp_b. rewrite (f32_g_nth inp j 16 HN ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq _ _) H16). rewrite andb_false_r. reflexivity.
Qed.

Lemma f32_rowsel_17 : forall inp j, t_k inp j = 9 ->
  bv_unsigned (nth 17 (t_phi inp j) cp_z) <> 234 -> t_rowsel inp j = false.
Proof.
  intros inp j K H17.
  assert (HN : 50 <= t_len inp j) by (apply f32_k_big; lia).
  unfold t_rowsel. rewrite K. unfold cp_v, cp_b. rewrite (f32_g_nth inp j 17 HN ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq _ _) H17). rewrite andb_false_r. reflexivity.
Qed.

Lemma f32_rowsel_true : forall inp j, t_k inp j = 9 ->
  bv_unsigned (nth 16 (t_phi inp j) cp_z) = 205 -> bv_unsigned (nth 17 (t_phi inp j) cp_z) = 234 ->
  t_rowsel inp j = true.
Proof.
  intros inp j K H16 H17.
  assert (HN : 50 <= t_len inp j) by (apply f32_k_big; lia).
  unfold t_rowsel. rewrite K. unfold cp_v, cp_b.
  rewrite (f32_g_nth inp j 16 HN ltac:(lia)), (f32_g_nth inp j 17 HN ltac:(lia)).
  rewrite H16, H17. reflexivity.
Qed.

(* ========================= byte / engine helpers ========================= *)

Lemma f32_firstn1 : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof.
  induction bs as [|x bs IH]; intros k d H; cbn [length] in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma f32_byte_lit : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma f32_rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn [length]; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH. cbn [firstn] in HH. exact HH.
Qed.

Lemma f32_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

Lemma f32_rd4 : forall m a bs, bytes_at rsegs m a bs -> length bs = 4%nat ->
  ov_read_bytes rsegs m (wa a) 4 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 4 H ltac:(lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

Lemma f32_rd_nth : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi. rewrite <- (f32_firstn1 bs i (Z_to_bv 8 0)) by lia.
  exact (bytes_at_ov_read rsegs m a bs i 1 H ltac:(lia)).
Qed.

Lemma f32_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma f32_eqb_zxb : forall (b : byte) c, 0 <= c < 2 ^ 64 ->
  bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. pose proof (f32_bz_range b) as Hb. unfold bz in Hb.
  unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma f32_lts_lit : forall x y, -2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_lit by lia. reflexivity. Qed.

Lemma f32_ltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma f32_rw1 : forall m a b, bytes_at rsegs m a [b] -> wview rsegs m (wa a) <> None ->
  rw_cells rsegs m a [C1 b].
Proof.
  intros m a b H Hw. pose proof H as (H0 & H1 & _). split.
  - split; [split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
  - split; [lia|]. split; [cbn [cells_size csize]; cbn [length] in H1; lia|].
    intros i Hi. cbn [cells_size csize] in Hi. replace i with 0 by lia. rewrite Z.add_0_r. exact Hw.
Qed.

Lemma f32_ba_nth : forall m A bs i, bytes_at rsegs m A bs -> (i < length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat i) [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m A bs i (H0 & HL & H) Hi.
  split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. destruct k as [|k]; [|lia].
  cbn [Z.of_nat nth_error]. rewrite Z.add_0_r, (H i Hi).
  apply nth_error_nth'. exact Hi.
Qed.

Lemma f32_shadow_in : forall fr i, fr mod 8 = 0 -> 0 <= i < 8 -> shadow_addr (fr + 32 + i) = Sfr fr + 4.
Proof.
  intros fr i H8 Hi. unfold Sfr, shadow_addr.
  assert (E : (fr + 32 + i) / 8 = fr / 8 + 4) by (Z.div_mod_to_equations; lia).
  lia.
Qed.

Lemma f32_shadow_eq_inv : forall fr a, fr mod 8 = 0 -> shadow_addr a = Sfr fr + 4 -> fr + 32 <= a < fr + 40.
Proof.
  intros fr a H8 E. unfold Sfr, shadow_addr in E. Z.div_mod_to_equations. lia.
Qed.

Lemma f32_mrd_munch : forall W m m' x, munch W m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  mrd rsegs m' (wa x) = mrd rsegs m (wa x).
Proof.
  intros W m m' x MU Hx Ho. unfold mrd. rewrite (MU (wa x)); [reflexivity|].
  rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma f32_addr_keep : forall m m' p n, addressable m p n ->
  (forall a, p <= a < p + n -> mrd rsegs m' (wa (shadow_addr a)) = mrd rsegs m (wa (shadow_addr a))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & Hn & Hend & HA) HK. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (HA i Hi) as (Happ & b & Hb & Hok).
  split; [exact Happ|]. exists b. split; [|exact Hok]. rewrite (HK (p + i) ltac:(lia)). exact Hb.
Qed.

Lemma f32_reg_eq : forall (regs : bvmap 5 word) (r : bv 5) a b,
  getr regs r = Z_to_bv 64 a -> getr regs r = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros regs r a b Ha Hb Ra Rb.
  assert (E : Z_to_bv 64 a = Z_to_bv 64 b) by congruence.
  apply (f_equal (bv_unsigned (n := 64))) in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

(* rg is equality after Z_to_bv 64: two values of one register agree mod 2^64 (from the F29 segment file). *)
Lemma rg_mod : forall regs r a b, rg regs r a -> rg regs r b -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof.
  unfold rg. intros regs r a b Ha Hb. rewrite Ha in Hb. apply (f_equal bv_unsigned) in Hb.
  rewrite !Z_to_bv_unsigned in Hb. exact Hb.
Qed.

(* A value of s1 within 416 bytes of the spill base A (both read through rg) is A. *)
Lemma f32_rg_near : forall (regs : bvmap 5 word) (r : bv 5) a b, rg regs r a -> rg regs r b ->
  416 <= a -> a + 416 <= 2 ^ 64 -> -400 <= b -> b + 8 <= 2 ^ 64 -> b = a.
Proof.
  intros regs r a b Ha Hb H1 H2 H3 H4.
  pose proof (rg_mod regs r b a Hb Ha) as E. rewrite (Z.mod_small a) in E by lia.
  pose proof (Z.div_mod b (2 ^ 64) ltac:(lia)) as D. rewrite E in D. lia.
Qed.

(* The image's registered globals lie below the image top GT. *)
Lemma f32_AG_low : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & len & Hil & Hr). unfold AF.frame_AG in Hil. cbn in Hil. unfold AC.GT.
  repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]).
  destruct Hil.
Qed.

Lemma f32_ub8 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof.
  intros v Hv. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma f32_zxb8 : forall v, 0 <= v < 256 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zxb. f_equal. apply f32_ub8. lia. Qed.

Lemma f32_sxb_eq : forall b : byte, sxb b = Z_to_bv 64 (bv_signed b).
Proof. intros b. reflexivity. Qed.

(* A branch arm the facts in context exclude (the ubsan b8c_bad, with the signed compare added). *)
Ltac f32_bad HC :=
  exfalso;
  try unfold sxb in HC; try unfold zxb in HC;
  rewrite ?f32_ub8 in HC by lia;
  first [ congruence
        | discriminate HC
        | (rewrite ?f32_eqb_zxb, ?f32_eqb_lit, ?f32_lts_lit, ?f32_ltu_lit in HC by lia; cbn [negb] in HC;
           first [ (apply Bool.negb_true_iff in HC;
                    first [apply Z.eqb_neq in HC | apply Z.ltb_ge in HC]; lia)
                 | (apply Bool.negb_false_iff in HC;
                    first [apply Z.eqb_eq in HC | apply Z.ltb_lt in HC]; lia)
                 | (apply Z.eqb_eq in HC; lia) | (apply Z.eqb_neq in HC; lia)
                 | (apply Z.ltb_lt in HC; lia) | (apply Z.ltb_ge in HC; lia) ])
        | (zify_cond HC; rewrite ?unsigned_lit in HC by lia; lia)
        | (vm_compute in HC; discriminate HC) ].
Ltac f32_nt := let H := fresh "HC" in first [ if_cases H; [f32_bad H | clear H] | idtac ].
Ltac f32_tk := let H := fresh "HC" in first [ if_cases H; [clear H | f32_bad H] | idtac ].

(* ---- Pure helpers taken from the F29 segment file (a working branch, same slot): byte lists, the shadow
   arithmetic of a 32-aligned frame, and the side stack's base word. *)

Lemma ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma ba_some : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa (a + i)) = Some b.
Proof.
  intros m a bs i (_ & _ & H) Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma sh_frame : forall fr y k, 0 <= fr -> fr mod 8 = 0 -> 0 <= y -> shadow_addr y = shadow_addr fr + k ->
  fr + 8 * k <= y < fr + 8 * k + 8.
Proof. unfold shadow_addr. intros fr y k H0 H8 Hy E. Z.div_mod_to_equations. lia. Qed.

Lemma in_shadow_bnd : forall x, in_shadow x -> LOWMEM_END <= x < HIGHMEM_BEG.
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros; lia. Qed.

Lemma addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW. exact Hi.
Qed.

(* A word_mem witness and the le8 word at the same address agree mod 2^64. *)
Lemma wm_uniq : forall m x v (w : word), word_mem rsegs m x v -> bytes_at rsegs m x (le8 w) ->
  v mod 2 ^ 64 = bv_unsigned w.
Proof.
  intros m x v w Hv Hw.
  pose proof Hw as (Hx0 & Hx1 & _). rewrite length_le8 in Hx1. change (Z.of_nat 8) with 8 in Hx1.
  assert (Hv' : word_mem rsegs m x (v mod 2 ^ 64)).
  { intros k Hk. rewrite (Hv k Hk). f_equal. f_equal. unfold le_byte.
    change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
  pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(lia)) as Hr.
  pose proof (word_mem_le8 rsegs m x (v mod 2 ^ 64) Hv' Hr Hx0 ltac:(lia)) as H8.
  pose proof (fl_le8_eq [] m m x _ _ H8 Hw (munch_refl [] m) (fun _ _ => I)) as E.
  apply (f_equal bv_unsigned) in E. rewrite unsigned_lit in E by lia. exact E.
Qed.

Lemma in_fs_range : forall m a (w : word), AC.a_in_fs AC.ASYMS m a -> bytes_at rsegs m RT_TP (le8 w) ->
  bv_unsigned w + AC.FS_SIZE <= 2 ^ 64 -> 0 <= a < 2 ^ 64 -> bv_unsigned w <= a < bv_unsigned w + AC.FS_SIZE.
Proof.
  intros m a w (b & Hbr & Hb & Hab) Hw Hsz Ha.
  change (AC.as_tp AC.ASYMS) with RT_TP in Hb.
  pose proof (wm_uniq m RT_TP b w Hb Hw) as E.
  pose proof (Z.div_mod b (2 ^ 64) ltac:(lia)) as D. rewrite E in D.
  pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
  unfold AC.FS_SIZE in *. lia.
Qed.

Lemma fs_meta_ge : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [[c [Hc Hr]] | [c [jj [Hc [Hj Heq]]]]]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. pose proof (a_fs_flag_range FS c jj Hc Hj). lia.
Qed.

(* Every segment of the image ends at or below GT, so a read-only address is below GT (F37's f37_ro_lo, with
   Tac_slot.img_tops_ok's bound). *)
Local Definition f32_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Local Lemma f32_rsegs_low : f32_tops rsegs AC.GT = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma f32_find_below : forall segs top x n s,
  f32_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold f32_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma f32_ro_lo : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < AC.GT.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (f32_find_below rsegs AC.GT (bv_unsigned a) 1 s f32_rsegs_low E ltac:(lia)) as [L|L];
    [exact L | discriminate L].
Qed.

(* The catalogue path's write set W = [sp - 16, sp) ++ [S(fr) + 4] ++ [fr + 32, fr + 40) misses the shadow byte of
   every app byte x outside the count variable: S(fr) + 4 is the shadow byte of [fr + 32, fr + 40) alone (fr is
   8-aligned), a shadow byte is below HIGHMEM_BEG <= sp - 16, and it is never app memory. *)
Lemma f32_sh_outW : forall fr sp x,
  fr mod 8 = 0 -> HIGHMEM_BEG <= sp - 16 -> (forall y, fr <= y < fr + 3136 -> app_mem y) ->
  app_mem x -> ~ (fr + 32 <= x < fr + 40) ->
  outside [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] (shadow_addr x).
Proof.
  intros fr sp x H8 Hsp Happ Hx Hn.
  pose proof (shadow_of_app x Hx) as Hs. pose proof (in_shadow_bnd _ Hs) as Hb.
  cbn [outside]. split; [lia|]. split; [|split; [|exact I]].
  - intros [H1 H2]. apply Hn. apply (f32_shadow_eq_inv fr x H8). lia.
  - intros [H1 H2]. exact (app_not_shadow (shadow_addr x) (Happ (shadow_addr x) ltac:(lia)) Hs).
Qed.

(* ---- The official bundles (SlotInv.v FLSH / FLSI / FLS / FLSX / LK / LT) across this segment's register changes
   (registers 9, 18, 21-25 kept) and across the catalogue path's write set (the spill base A and everything above
   it, the record bytes at Phi, out[] at fr + 2624, the frame records and the harness block are outside W). *)

Lemma f32_spill_regs : forall regs regs' m off v,
  getr regs' 9 = getr regs 9 -> spill regs m off v -> spill regs' m off v.
Proof.
  intros regs regs' m off v E (A & HA & Hq). exists A. split; [unfold rg in *; rewrite E; exact HA | exact Hq].
Qed.

Lemma f32_flsi_regs : forall g j fr regs regs' m,
  getr regs' 9 = getr regs 9 -> FLSI g j fr regs m -> FLSI g j fr regs' m.
Proof.
  intros g j fr regs regs' m E
    (((S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & Ha & Hb & Hp & P1 & P2 & P3 & P4 & P5) & S128 & Hs & S144 & Ha17) &
     S216 & S224 & S248 & HIN & (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & Ca & Cb & C9 & C10 & C11 & C12)).
  pose proof (f32_spill_regs regs regs' m) as T. unfold FLSI, FLSH, PRO, FLC.
  split.
  { split.
    { split; [exact (T _ _ E S1)|]. split; [exact (T _ _ E S2)|]. split; [exact (T _ _ E S3)|].
      split; [exact (T _ _ E S4)|]. split; [exact (T _ _ E S5)|]. split; [exact (T _ _ E S6)|].
      split; [exact (T _ _ E S7)|]. split; [exact (T _ _ E S8)|]. split; [exact Ha|]. split; [exact Hb|].
      split; [exact Hp|]. split; [exact (T _ _ E P1)|]. split; [exact (T _ _ E P2)|].
      split; [exact (T _ _ E P3)|]. split; [exact (T _ _ E P4) | exact (T _ _ E P5)]. }
    split; [exact (T _ _ E S128)|]. split; [exact Hs|]. split; [exact (T _ _ E S144) | exact Ha17]. }
  split; [exact (T _ _ E S216)|]. split; [exact (T _ _ E S224)|]. split; [exact (T _ _ E S248)|].
  split; [exact HIN|].
  split; [exact (T _ _ E C1)|]. split; [exact (T _ _ E C2)|]. split; [exact (T _ _ E C3)|].
  split; [exact (T _ _ E C4)|]. split; [exact (T _ _ E C5)|]. split; [exact (T _ _ E C6)|].
  split; [exact (T _ _ E C7)|]. split; [exact (T _ _ E C8)|]. split; [exact Ca|]. split; [exact Cb|].
  split; [exact (T _ _ E C9)|]. split; [exact (T _ _ E C10)|].
  split; [exact (T _ _ E C11) | exact (T _ _ E C12)].
Qed.

Lemma f32_lk_regs : forall g fr j regs regs' m,
  getr regs' 21 = getr regs 21 -> LK g fr j regs m -> LK g fr j regs' m.
Proof.
  intros g fr j regs regs' m E (Hj & H21 & HO). split; [exact Hj|].
  split; [unfold rg in *; rewrite E; exact H21 | exact HO].
Qed.

Lemma f32_flsx_regs : forall g j phi fr regs regs' m,
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  FLSX g j phi fr regs m -> FLSX g j phi fr regs' m.
Proof.
  intros g j phi fr regs regs' m E9 E18 E22 E23 E25 (HI & H18 & H22 & H23 & H25 & Hrec & H152 & H280).
  unfold FLSX.
  split; [exact (f32_flsi_regs g j fr regs regs' m E9 HI)|].
  split; [unfold rg in *; rewrite E18; exact H18|]. split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E23; exact H23|]. split; [unfold rg in *; rewrite E25; exact H25|].
  split; [exact Hrec|].
  split; [exact (f32_spill_regs regs regs' m _ _ E9 H152) | exact (f32_spill_regs regs regs' m _ _ E9 H280)].
Qed.

Lemma f32_fls_of_flsx : forall g j phi fr regs m,
  FLSX g j phi fr regs m -> rg regs 24 (t_k (g_in g) j) -> FLS g j phi fr regs m.
Proof.
  intros g j phi fr regs m (HI & H18 & H22 & H23 & H25 & Hrec & H152 & H280) H24.
  unfold FLS.
  split; [exact HI|]. split; [exact H18|]. split; [exact H22|]. split; [exact H23|]. split; [exact H24|].
  split; [exact H25|]. split; [exact Hrec|]. split; [exact H152 | exact H280].
Qed.

Lemma f32_fls_regs : forall g j phi fr regs regs' m,
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
  FLS g j phi fr regs m -> FLS g j phi fr regs' m.
Proof.
  intros g j phi fr regs regs' m E9 E18 E22 E23 E24 E25 H.
  apply f32_fls_of_flsx.
  - exact (f32_flsx_regs g j phi fr regs regs' m E9 E18 E22 E23 E25 (flsx_of_fls g j phi fr regs m H)).
  - destruct H as (_ & _ & _ & _ & H24 & _). unfold rg in *. rewrite E24. exact H24.
Qed.

Lemma f32_spill_mem : forall regs regs' m m' W off v A,
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off <= 400 ->
  getr regs' 9 = getr regs 9 -> munch W m m' -> (forall x, A <= x -> outside W x) ->
  spill regs m off v -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v A HA H1 H2 Hoff E MU HW (A' & HA' & Hq).
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  assert (EA : A' = A) by (apply (f32_rg_near regs 9 A A' HA HA'); lia).
  subst A'. exists A. split; [unfold rg in *; rewrite E; exact HA|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. apply HW. lia.
Qed.

Lemma f32_flsi_mem : forall g j fr regs regs' m m' W A,
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> munch W m m' -> (forall x, A <= x -> outside W x) ->
  addressable m' (fr + 2624) 6 -> stk rsegs m' fr (fr + 3136) -> addressable m' (fr + 2691) 17 -> f1_IN g m' ->
  addressable m' (fragb fr) 72 -> addressable m' (fr + 2688) 38 ->
  FLSI g j fr regs m -> FLSI g j fr regs' m'.
Proof.
  intros g j fr regs regs' m m' W A HA H1 H2 E MU HW Ha' Hs' Ha17' HIN' Hfb' H38'
    (((S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _ & _ & _ & P1 & P2 & P3 & P4 & P5) & S128 & _ & S144 & _) &
     S216 & S224 & S248 & _ & (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _ & _ & C9 & C10 & C11 & C12)).
  pose proof HIN' as (HinH' & Hinad' & Hinb').
  pose proof (fun off v (Hoff : 0 <= off <= 400) => f32_spill_mem regs regs' m m' W off v A HA H1 H2 Hoff E MU HW)
    as T.
  unfold FLSI, FLSH, PRO, FLC.
  split.
  { split.
    { split; [exact (T 40 _ ltac:(lia) S1)|]. split; [exact (T 120 _ ltac:(lia) S2)|].
      split; [exact (T 136 _ ltac:(lia) S3)|]. split; [exact (T 160 _ ltac:(lia) S4)|].
      split; [exact (T 168 _ ltac:(lia) S5)|]. split; [exact (T 176 _ ltac:(lia) S6)|].
      split; [exact (T 208 _ ltac:(lia) S7)|]. split; [exact (T 248 _ ltac:(lia) S8)|].
      split; [exact Ha'|]. split; [exact Hinb'|].
      split; [intros Hn; split; [exact (HinH' Hn) | exact Hinad']|].
      split; [exact (T 184 _ ltac:(lia) P1)|]. split; [exact (T 256 _ ltac:(lia) P2)|].
      split; [exact (T 264 _ ltac:(lia) P3)|].
      split; [exact (T 272 _ ltac:(lia) P4) | exact (T 32 _ ltac:(lia) P5)]. }
    split; [exact (T 128 _ ltac:(lia) S128)|]. split; [exact Hs'|].
    split; [exact (T 144 _ ltac:(lia) S144) | exact Ha17']. }
  split; [exact (T 216 _ ltac:(lia) S216)|]. split; [exact (T 224 _ ltac:(lia) S224)|].
  split; [exact (T 248 _ ltac:(lia) S248)|]. split; [exact HIN'|].
  split; [exact (T 256 _ ltac:(lia) C1)|]. split; [exact (T 184 _ ltac:(lia) C2)|].
  split; [exact (T 192 _ ltac:(lia) C3)|]. split; [exact (T 80 _ ltac:(lia) C4)|].
  split; [exact (T 88 _ ltac:(lia) C5)|]. split; [exact (T 96 _ ltac:(lia) C6)|].
  split; [exact (T 272 _ ltac:(lia) C7)|]. split; [exact (T 264 _ ltac:(lia) C8)|].
  split; [exact Hfb'|]. split; [exact H38'|].
  split; [exact (T 72 _ ltac:(lia) C9)|]. split; [exact (T 64 _ ltac:(lia) C10)|].
  split; [exact (T 56 _ ltac:(lia) C11) | exact (T 48 _ ltac:(lia) C12)].
Qed.

Lemma f32_lk_mem : forall g fr j regs regs' m m' W,
  getr regs' 21 = getr regs 21 -> munch W m m' ->
  (forall x, fr + 2624 <= x < fr + 2630 -> outside W x) ->
  LK g fr j regs m -> LK g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W E MU HW (Hj & H21 & HO). split; [exact Hj|].
  split; [unfold rg in *; rewrite E; exact H21|].
  unfold OURb in *. eapply fl_bytes; [exact HO | exact MU |].
  intros x Hx. apply HW. unfold OUR in Hx. rewrite length_map, length_seq in Hx. lia.
Qed.

Lemma f32_flsx_mem : forall g j phi fr regs regs' m m' W A,
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  munch W m m' -> (forall x, A <= x -> outside W x) ->
  (forall x, phi <= x < phi + flen g j -> outside W x) ->
  FLSI g j fr regs' m' -> FLSX g j phi fr regs m -> FLSX g j phi fr regs' m'.
Proof.
  intros g j phi fr regs regs' m m' W A HA H1 H2 E9 E18 E22 E23 E25 MU HW HWp HI'
    (_ & H18 & H22 & H23 & H25 & Hrec & H152 & H280).
  pose proof (f32_phi_length (g_in g) j) as Lp.
  unfold FLSX.
  split; [exact HI'|].
  split; [unfold rg in *; rewrite E18; exact H18|]. split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E23; exact H23|]. split; [unfold rg in *; rewrite E25; exact H25|].
  split.
  { intros Hl. destruct (Hrec Hl) as (Hp0 & Hp1 & Hg & Hph & Hpl).
    assert (Lg : length (t_g (g_in g) j) = 50%nat).
    { unfold flen in Hl. unfold t_g. rewrite f32_fr50_firstn by (rewrite f32_phi_length; lia).
      rewrite length_firstn, f32_phi_length. lia. }
    split; [exact Hp0|]. split; [exact Hp1|].
    split; [eapply fl_bytes; [exact Hg | exact MU |]; rewrite Lg; intros x Hx; apply HWp; lia|].
    split; [eapply fl_bytes; [exact Hph | exact MU |]; rewrite Lp; intros x Hx; apply HWp; unfold flen in *; lia|].
    exact Hpl. }
  split; [exact (f32_spill_mem regs regs' m m' W 152 _ A HA H1 H2 ltac:(lia) E9 MU HW H152)|].
  exact (f32_spill_mem regs regs' m m' W 280 _ A HA H1 H2 ltac:(lia) E9 MU HW H280).
Qed.

(* ---- The hand-on bundle LT (SlotInv.v: IFS g fr (S j), the frame records and, v1.9 FSb, the first fragment's
   spills [A+104] / [A+112] and body bytes at fr + 2880 of turn j + 1).  The frame records lie at fr + 2688
   (38 bytes) and fr + 2768 (72 bytes): every turn keeps their lengths (ING_length for the identity record, the four
   fg_next cases for the fragment state), so they lie inside the frame; the body is at most 23 bytes. *)

Lemma f32_rp_id_len : forall idb len g, length idb = ID_SIZE -> length (rp_id idb len g) = ID_SIZE.
Proof.
  intros idb len g H. unfold rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply ING_length; exact H | exact H].
Qed.

Lemma f32_fg_id_len : forall idb len st g, length idb = ID_SIZE -> length (fg_id idb len st g) = ID_SIZE.
Proof.
  intros idb len st g H. unfold fg_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply ING_length; exact H | exact H].
Qed.

Lemma f32_tID_length : forall inp j, length (t_ID inp j) = ID_SIZE.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  cbn [fst_at]. unfold turn. cbv beta zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; apply f32_fg_id_len, f32_rp_id_len; exact IH.
Qed.

Lemma f32_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_st len st g) = 72%nat.
Proof.
  intros len st g HL HG. unfold fg_st, fcls. cbn [fg_class Z.eqb orb].
  destruct (fg_fr len g) eqn:Efr; cbn [negb fg_next]; [|exact HL].
  assert (Hn : 1 <= fg_n g <= 22).
  { unfold fg_fr in Efr. apply andb_prop in Efr as [Efr _]. apply andb_prop in Efr as [Efr E22].
    apply andb_prop in Efr as [_ E1]. apply Z.leb_le in E22. apply Z.leb_le in E1. lia. }
  destruct (bat g 19 =? 1); cbn [fg_next].
  - unfold fg_first, fg_body. rewrite !length_app, length_skipn, HL. cbn [length].
    rewrite !rf_bsl_length by lia. lia.
  - destruct (negb (fg_keep st g)) eqn:Ek; cbn [fg_next].
    + apply rf_clear_length. exact HL.
    + assert (HT : fg_T st g <= 64).
      { unfold fg_keep in Ek. apply negb_false_iff in Ek. apply andb_prop in Ek as [_ Ek].
        apply Z.leb_le in Ek. exact Ek. }
      destruct (negb (fg_close st g)); cbn [fg_next]; apply rf_clear_length; apply rf_fg_join_length;
        assumption.
Qed.

Lemma f32_tFG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH]; [reflexivity|].
  assert (HG : length (t_g inp j) = 50%nat).
  { unfold t_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. }
  cbn [fst_at]. unfold turn. cbv beta zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; apply f32_fg_st_len; assumption.
Qed.

(* v1.9 FSb: the first fragment's body is at most the 23 bytes block[9 ..] of a 50-byte record (fs0's is empty),
   so it lies in [fr + 2880, fr + 2915), the 35 bytes FSb makes addressable.  (F29's fs_body_len.) *)
Lemma f32_fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  assert (HG : length (t_g inp j) = 50%nat).
  { unfold t_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. }
  cbn [fst_at]. unfold turn. cbv beta zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn, HG. lia.
Qed.

Lemma f32_lt_regs : forall g fr j regs regs' m,
  getr regs' 9 = getr regs 9 -> LT g fr j regs m -> LT g fr j regs' m.
Proof.
  intros g fr j regs regs' m E (HID & HFG & (Q104 & Q112 & Qbody & Qad & HFI)).
  pose proof (f32_spill_regs regs regs' m) as T. unfold LT, IFS, FSj, FSb.
  split; [exact HID|]. split; [exact HFG|].
  split; [exact (T _ _ E Q104)|]. split; [exact (T _ _ E Q112)|].
  split; [exact Qbody|]. split; [exact Qad | exact HFI].
Qed.

Lemma f32_f1in_mem : forall g m m' W,
  munch W m m' ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W (shadow_addr x)) ->
  f1_IN g m -> f1_IN g m'.
Proof.
  intros g m m' W MU HW HWs (Hin & Had & Hb). split; [exact Hin|]. split.
  - apply (addr_keep W m m' _ _ Had MU). intros i Hi. apply HWs. lia.
  - eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply HW. unfold g_n, nlen. lia.
Qed.

Lemma f32_lt_mem : forall g fr j regs regs' m m' W A,
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> munch W m m' -> (forall x, A <= x -> outside W x) ->
  (forall x, fr + 2688 <= x < fr + 2840 -> outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x /\ outside W (shadow_addr x)) ->
  LT g fr j regs m -> LT g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W A HA H1 H2 E MU HW HWr HWb
    ((HID & Hidok) & (HFG & Hfgok) & (Q104 & Q112 & Qbody & Qad & HFI)).
  pose proof (fun off v (Hoff : 0 <= off <= 400) => f32_spill_mem regs regs' m m' W off v A HA H1 H2 Hoff E MU HW)
    as T.
  pose proof (f32_tID_length (g_in g) (S j)) as LID. pose proof (f32_tFG_length (g_in g) (S j)) as LFG.
  unfold ID_SIZE in LID.
  unfold LT, IFS, IDj, FGj, IDb, FGb, FSj, FSb.
  split.
  { split; [|exact Hidok]. unfold IDBe in *. eapply fl_bytes; [exact HID | exact MU |].
    rewrite LID. intros x Hx. apply HWr. lia. }
  split.
  { split; [|exact Hfgok]. unfold FGBe in *. eapply fl_bytes; [exact HFG | exact MU |].
    rewrite LFG. intros x Hx. apply HWr. lia. }
  split; [exact (T 104 _ ltac:(lia) Q104)|]. split; [exact (T 112 _ ltac:(lia) Q112)|].
  split.
  { eapply fl_bytes; [exact Qbody | exact MU |]. pose proof (f32_fs_body_len (g_in g) (S j)) as LB.
    intros x Hx. exact (proj1 (HWb x ltac:(lia))). }
  split; [|exact HFI].
  apply (addr_keep W m m' _ _ Qad MU). intros i Hi. exact (proj2 (HWb (fr + 2880 + i) ltac:(lia))).
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CATC : CATc.reac_box_catalogue_contract.

(* FRA across this segment's write set W = the catalogue's 16-byte window below sp, the one frame shadow byte
   S(fr) + 4 and the count variable [fr + 32, fr + 40).  RT by RT_meta_write (a shadow byte is rewritten, every
   shadow byte is still readable); AH and stklo from the caller; the 392 shadow bytes are rebuilt from shadow_rw
   mem'; the S-anchored stack window is backed again (the callee's window by its stk result, the count variable by
   its new bytes, every other byte of it is outside W); ro_agree, the side arm's FakeStack record and every other
   FRA cell are outside W by the address bounds (the image is below GT <= fr, the shadow is below HIGHMEM_BEG <=
   stklo < sp - 16, the FakeStack is below stklo, the frame header is apart from the window by fra_frame, the spill
   base A and the saved registers are at or above sp and above the frame); an addressable byte outside the frame
   (a registered global, a byte of the slot window) keeps its shadow byte, since S(fr) + 4 is the shadow byte of
   the count variable alone (f32_sh_outW). *)
Lemma f32_fra_w : forall g fr hb regs regs' mem mem' md spv,
  FRA B APIf ra g fr hb regs mem md ->
  AC.aspZ regs = spv ->
  munch [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] mem mem' ->
  wmono rsegs mem mem' ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  shadow_rw mem' ->
  stk rsegs mem' (spv - FN_STACK) spv ->
  bytes_at rsegs mem' (fr + 32) (le8 (Z_to_bv 64 11)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md spv HFRA Hasp MU WM HAH' HSTK HSW' HWIN HBA
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hplace & _ & _ & _).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWAd &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (Esp : spv = sp) by (rewrite <- Hasp; exact Haspz).
  clear Hasp. subst spv.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAE : APPMEM_END = 140737488355328) by reflexivity.
  assert (HLE : LOWMEM_END = 2147450880) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold AC.GT in HGT.
  assert (Hwin0 : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (Hpl : fr + 3136 <= sp - 16 \/ sp <= fr).
  { destruct (Hplace 16 ltac:(lia)) as [H|H]; rewrite Haspz in H; [left | right]; lia. }
  assert (Hhi0 : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  assert (HW16 : HIGHMEM_BEG <= sp - 16) by lia.
  (* the frame's shadow bytes *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (Hin4 : in_shadow (Sfr fr + 4)) by (apply HshIS; lia).
  pose proof (in_shadow_bnd _ Hin4) as HS4b.
  pose proof (in_shadow_bnd _ (HshIS (Sfr fr) ltac:(lia))) as HS0b.
  pose proof (in_shadow_bnd _ (HshIS (Sfr fr + 391) ltac:(lia))) as HS379b.
  assert (Hmeta4 : Sfr fr + 4 < fr \/ fr + 3136 <= Sfr fr + 4).
  { apply (app_ivl_meta fr (fr + 3136)); [exact Happ | exact Hin4]. }
  (* outside W for the classes of addresses FRA reads *)
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1.
    assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. cbn [outside]. repeat split; try exact I; lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  assert (HWfr : forall x, fr <= x < fr + 24 ->
                   outside [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] x).
  { intros x Hx. cbn [outside]. repeat split; try exact I; lia. }
  assert (HWA : forall x, A <= x ->
                  outside [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] x).
  { intros x Hx. cbn [outside]. repeat split; try exact I; lia. }
  (* the image's read-only bytes are below GT <= fr *)
  assert (HRO : ro_agree rsegs mem').
  { intros a Ha. pose proof (f32_ro_lo a Ha) as Hlo. pose proof (bv_unsigned_in_range 64 a) as Ha64.
    change (bv_modulus 64) with (2 ^ 64) in Ha64. unfold AC.GT in Hlo.
    assert (E : mrd rsegs mem' a = mrd rsegs mem a).
    { unfold mrd. rewrite (MU a); [reflexivity|]. cbn [outside]. repeat split; try exact I; lia. }
    rewrite E. exact (Hro a Ha). }
  (* an addressable byte outside the frame keeps its shadow byte *)
  assert (Hkeep1 : forall a, addressable mem a 1 -> ~ (fr <= a < fr + 3136) -> addressable mem' a 1).
  { intros a Ha Hnf. apply (addr_keep _ mem mem' a 1 Ha MU). intros i Hi.
    replace (a + i) with a by lia.
    apply (f32_sh_outW fr sp a Hfr8 HW16 Happ (addr1_app mem a Ha)). lia. }
  (* RT *)
  assert (HRT' : AsanRTInv.RT sp mem' md).
  { eapply (AsanRTInv.RT_meta_write sp sp mem mem' md md); [exact HRT | exact MU | exact WM | | ].
    - unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [left; lia | exact I].
    - intros a Ha. destruct (HSW' a Ha) as (_ & b & Hb). exists b. exact Hb. }
  exists A, sp, s5.
  split; [exact HRT'|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfrz [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfrz|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo2 | exact Hhi2]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * apply (fsrec_munch_lo APIf (hb ++ g_H g) mem mem' md _ fr Hrec HAH (proj1 (fr_munch_ul _ _ _) MU)).
          -- intros x Hx. apply (proj2 (fr_outside_lib _ _)). cbn [outside].
             repeat split; try exact I; lia.
          -- intros x Hx Hnb Hlo. apply (proj2 (fr_outside_lib _ _)). cbn [outside].
             split; [lia|].
             split; [intros Hc; apply (app_not_shadow x Hx); replace x with (Sfr fr + 4) by lia; exact Hin4|].
             split; [lia | exact I]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWfr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWfr. lia. }
  split.
  { assert (HSTKsh : stk rsegs mem' (Sfr fr) (Sfr fr + 392)).
    { split; [lia|]. split; [lia|]. intros a Ha. exact (HSW' a (HshIS a Ha)). }
    destruct (stk_bytes rsegs mem' (Sfr fr) (Sfr fr + 392) HSTKsh ltac:(lia)) as (sh' & Hl' & Hb').
    exists sh'. split; [exact Hb'|]. rewrite Hl'. replace (Sfr fr + 392 - Sfr fr) with 392 by lia.
    reflexivity. }
  split.
  { destruct Hwin as (Hw0 & Hw1 & Hwv). split; [exact Hw0|]. split; [exact Hw1|].
    intros a Ha. destruct (Hwv a Ha) as (Hwa & b & Hb). split; [exact (WM _ Hwa)|].
    assert (Hcnt : fr + 32 <= a < fr + 40 -> exists b', mrd rsegs mem' (wa a) = Some b').
    { intros Hc. replace a with (fr + 32 + (a - (fr + 32))) by lia.
      apply (ba_some mem' (fr + 32) (le8 (Z_to_bv 64 11))); [exact HBA | rewrite length_le8; change (Z.of_nat 8) with 8; lia]. }
    assert (Hout : ~ (sp - 16 <= a < sp) -> ~ (fr + 32 <= a < fr + 40) ->
                   exists b', mrd rsegs mem' (wa a) = Some b').
    { intros N1 N2. exists b. rewrite (f32_mrd_munch _ mem mem' a MU ltac:(lia)); [exact Hb|].
      cbn [outside]. split; [exact N1|]. split; [lia|]. split; [exact N2 | exact I]. }
    destruct (Z_le_gt_dec (sp - 16) a) as [L3|L3]; [destruct (Z_lt_ge_dec a sp) as [L4|L4]|].
    - destruct HWIN as (_ & _ & HW). exact (proj2 (HW a ltac:(lia))).
    - destruct (Z_le_gt_dec (fr + 32) a) as [L1|L1]; [destruct (Z_lt_ge_dec a (fr + 40)) as [L2|L2]|];
        [apply Hcnt; lia | apply Hout; lia | apply Hout; lia].
    - destruct (Z_le_gt_dec (fr + 32) a) as [L1|L1]; [destruct (Z_lt_ge_dec a (fr + 40)) as [L2|L2]|];
        [apply Hcnt; lia | apply Hout; lia | apply Hout; lia]. }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWA. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn [length] in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split.
  { intros a Hin. apply Hkeep1; [exact (HAG a Hin)|].
    pose proof (f32_AG_low a Hin) as Hl. unfold AC.GT in Hl. lia. }
  split; [intros a H1 H2; exact (Hkeep1 a (HWAd a H1 H2) H2)|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* ===================== the machine runs ===================== *)

(* 0x827d8 -> 0x82800: the three branches to 0x82bf4 are not taken. *)
Lemma f32_evt_a :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (A EV tf so ev : Z),
    x9 = Z_to_bv 64 A -> 0 <= A -> A + 288 <= 2 ^ 64 ->
    bv_eqb x10 (Z_to_bv 64 0) = false ->
    ov_read_bytes rsegs m (wa (A + 152)) 8 = Some (le8 (Z_to_bv 64 tf)) -> (tf = 0 \/ tf = 1) ->
    ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 so)) -> (so = 0 \/ so = 1) ->
    ~ (tf = 0 /\ so = 0) ->
    ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 EV)) -> 0 <= EV -> EV + 4 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa EV) 4 = Some (le4 (Z_to_bv 64 ev)) -> 0 <= ev <= 5 ->
    LE.evt rsegs
      (fun ms' => exists y10 y11,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                       x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x827d8) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m A EV tf so ev E9 HA0 HA1 Hne R152 Htf R280 Hso Hnz R160 HE0 HE1 Rev Hev.
  subst x9.
  assert (Hev' : ev = 0 \/ ev = 1 \/ ev = 2 \/ ev = 3 \/ ev = 4 \/ ev = 5) by lia.
  destruct Htf as [->| ->]; destruct Hso as [->| ->];
    try (exfalso; apply Hnz; split; reflexivity);
    destruct Hev' as [->|[->|[->|[->|[->| ->]]]]];
    (step; f32_nt; step; step; step; step; step; f32_nt; step; step; step; step; f32_nt;
     apply evt_done; eexists; eexists; reflexivity).
Qed.

(* 0x82800 with k <> 9: the branch to 0x828c8 is taken. *)
Lemma f32_evt_n :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (k : Z),
    x24 = Z_to_bv 64 k -> 0 <= k <= 13 -> k <> 9 ->
    LE.evt rsegs
      (fun ms' => exists y10,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                       x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m k E24 Hk Hk9. subst x24.
  assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/
                k = 10 \/ k = 11 \/ k = 12 \/ k = 13) by lia.
  destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
    (step; step; f32_tk; apply evt_done; eexists; reflexivity).
Qed.

(* 0x82808 -> 0x8281c: the instrumented check of the byte at phi + 16 (side block 0x82a20, error path 0x82cf4). *)
Lemma f32_chk16 :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (phi : Z) (b : byte),
    x23 = Z_to_bv 64 phi -> x26 = Z_to_bv 64 ASAN_K -> 0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 16) 3 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ (phi + 16) mod 8 < bv_signed b <= 7) ->
    LE.evt rsegs
      (fun ms' => exists y11 y12,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (phi + 16)) y11 y12 x13 x14 x15 x16 x17 x18 x19
                       x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 0x8281c) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82808) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m phi b E23 E26 Hp0 Hp1 R16 Hok. subst x23 x26.
  assert (HS : 0 <= Z.shiftr (phi + 16) 3 < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  pose proof (sbyte_range b) as Hsb.
  destruct Hok as [H0 | Hlt].
  - rewrite (byte_s0 b H0) in R16.
    step. rewrite ?(MState.unsigned_lit phi) by lia.
    step. rewrite ?(MState.unsigned_lit (phi + 16)) by lia.
    step. rewrite ?(MState.unsigned_lit (Z.shiftr (phi + 16) 3)) by lia.
    rewrite ?(MState.unsigned_lit ASAN_K) by (unfold ASAN_K; lia).
    step. step. f32_nt.
    apply evt_done. eexists; eexists; reflexivity.
  - step. rewrite ?(MState.unsigned_lit phi) by lia.
    step. rewrite ?(MState.unsigned_lit (phi + 16)) by lia.
    step. rewrite ?(MState.unsigned_lit (Z.shiftr (phi + 16) 3)) by lia.
    rewrite ?(MState.unsigned_lit ASAN_K) by (unfold ASAN_K; lia).
    step. step. f32_tk.
    step. rewrite ?(MState.unsigned_lit (phi + 16)) by lia. rewrite ?(land7 (phi + 16)) by lia.
    step. f32_nt. step.
    apply evt_done. eexists; eexists; reflexivity.
Qed.

(* 0x82828 -> 0x8283c: the same check for the byte at phi + 17 (side block 0x82a74, error path 0x82d14). *)
Lemma f32_chk17 :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (phi : Z) (b : byte),
    x23 = Z_to_bv 64 phi -> x26 = Z_to_bv 64 ASAN_K -> 0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 17) 3 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ (phi + 17) mod 8 < bv_signed b <= 7) ->
    LE.evt rsegs
      (fun ms' => exists y11 y12,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (phi + 17)) y11 y12 x13 x14 x15 x16 x17 x18 x19
                       x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 0x8283c) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82828) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m phi b E23 E26 Hp0 Hp1 R17 Hok. subst x23 x26.
  assert (HS : 0 <= Z.shiftr (phi + 17) 3 < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  pose proof (sbyte_range b) as Hsb.
  destruct Hok as [H0 | Hlt].
  - rewrite (byte_s0 b H0) in R17.
    step. rewrite ?(MState.unsigned_lit phi) by lia.
    step. rewrite ?(MState.unsigned_lit (phi + 17)) by lia.
    step. rewrite ?(MState.unsigned_lit (Z.shiftr (phi + 17) 3)) by lia.
    rewrite ?(MState.unsigned_lit ASAN_K) by (unfold ASAN_K; lia).
    step. step. f32_nt.
    apply evt_done. eexists; eexists; reflexivity.
  - step. rewrite ?(MState.unsigned_lit phi) by lia.
    step. rewrite ?(MState.unsigned_lit (phi + 17)) by lia.
    step. rewrite ?(MState.unsigned_lit (Z.shiftr (phi + 17) 3)) by lia.
    rewrite ?(MState.unsigned_lit ASAN_K) by (unfold ASAN_K; lia).
    step. step. f32_tk.
    step. rewrite ?(MState.unsigned_lit (phi + 17)) by lia. rewrite ?(land7 (phi + 17)) by lia.
    step. f32_nt. step.
    apply evt_done. eexists; eexists; reflexivity.
Qed.

Lemma f32_shadow_rng : forall x, in_shadow x -> LOWMEM_END <= x < HIGHMEM_BEG.
Proof.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros x [H|H]; lia.
Qed.

(* 0x82800 with k = 9: the two byte tests, then either 0x828c8 or the catalogue call and 0x8285c. *)
Lemma f32_evt_m :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (Asp fr phi spv lo v16 v17 : Z) (b16 b17 b4 : byte) (junk : list byte),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 Asp -> x19 = Z_to_bv 64 (Sfr fr) ->
    x23 = Z_to_bv 64 phi -> x24 = Z_to_bv 64 9 -> x26 = Z_to_bv 64 ASAN_K ->
    0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 16) 3 + ASAN_K)) 1 = Some [b16] ->
    (bv_signed b16 = 0 \/ (phi + 16) mod 8 < bv_signed b16 <= 7) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 17) 3 + ASAN_K)) 1 = Some [b17] ->
    (bv_signed b17 = 0 \/ (phi + 17) mod 8 < bv_signed b17 <= 7) ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [Z_to_bv 8 v16] -> 0 <= v16 < 256 ->
    ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [Z_to_bv 8 v17] -> 0 <= v17 < 256 ->
    ro_cells rsegs m (Asp + 40) [C8 (Z_to_bv 64 (fr + 32))] ->
    rw_cells rsegs m (Sfr fr + 4) [C1 b4] -> rw_cells rsegs m (fr + 32) [CB 8 junk] ->
    0 <= fr -> fr mod 8 = 0 -> 6283264 <= fr -> fr + 3136 <= Asp -> Asp + 48 <= 2 ^ 64 ->
    ASAN_K <= Sfr fr -> Sfr fr + 5 <= lo -> 6283264 <= lo -> HIGHMEM_BEG <= lo ->
    lo + 16 <= spv -> spv <= Asp -> spv < 2 ^ 64 ->
    (fr + 3136 <= lo \/ spv <= fr) ->
    (Sfr fr + 5 <= fr + 32 \/ fr + 40 <= Sfr fr + 4) ->
    stk rsegs m lo spv ->
    (forall a, fr + 32 <= a < fr + 40 -> app_mem a) ->
    asan_cells m -> shadow_rw m ->
    LE.evt rsegs
      (fun ms' =>
         (exists y10 y11 y12,
            ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                          x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fcs None m (seg_rom rsegs)
            /\ (v16 <> 205 \/ v17 <> 234))
         \/ (exists y11 y12 m',
            ms' = MS (mkR (Z_to_bv 64 0x8285c) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 CATc.BOX_CATALOGUE) y11 y12
                          x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (fr + 32)) x25 x26 x27 x28
                          x29 x30 x31) Fr (Z_to_bv 64 0x8285c) fcs None m' (seg_rom rsegs)
            /\ v16 = 205 /\ v17 = 234
            /\ munch [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] m m'
            /\ wmono rsegs m m' /\ stk rsegs m' lo spv
            /\ bytes_at rsegs m' (fr + 32) (le8 (Z_to_bv 64 11))
            /\ mrd rsegs m' (wa (Sfr fr + 4)) = Some (Z_to_bv 8 0)))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m Asp fr phi spv lo v16 v17 b16 b17 b4 junk
    E2 E9 E19 E23 E24 E26 Hp0 Hp1 R16s Hok16 R17s Hok17 R16b Hv16 R17b Hv17
    RA40 RW4 RWfr Hfr0 Hfr8 HGT HfrA HAb HSfr0 HSlo HloG HloH Hlosp HspA HspB Hdw Hd4 HST Happ HAC HSW.
  subst x2 x9 x19 x23 x24 x26.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  step. step. f32_nt.
  eapply evt_cut;
    [ eapply (f32_chk16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi b16);
      [reflexivity | reflexivity | lia | lia | exact R16s | exact Hok16]
    | intros ms1 (y11 & y12 & ->) ].
  step. rewrite ?(f32_zxb8 v16) by lia.
  step. step.
  destruct (Z.eq_dec v16 205) as [Ev16 | Nv16].
  2: { f32_tk. apply evt_done. left. do 3 eexists. split; [reflexivity|]. left. exact Nv16. }
  subst v16. f32_nt.
  eapply evt_cut;
    [ eapply (f32_chk17 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi b17);
      [reflexivity | reflexivity | lia | lia | exact R17s | exact Hok17]
    | intros ms2 (y11' & y12' & ->) ].
  step. rewrite ?(f32_zxb8 v17) by lia.
  step. step.
  destruct (Z.eq_dec v17 234) as [Ev17 | Nv17].
  2: { f32_tk. apply evt_done. left. do 3 eexists. split; [reflexivity|]. right. exact Nv17. }
  subst v17. f32_nt.
  (* the two stores and the catalogue call *)
  pose proof (munch_refl [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct Hd4 as [Hd4 | Hd4];
  (rewrite ?(MState.unsigned_lit (Sfr fr)) by lia;
   step;
   change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]; mem_after_store;
   rewrite ?(MState.unsigned_lit Asp) by lia;
   step;
   rewrite ?(MState.unsigned_lit (fr + 32)) by lia;
   step; step; step;
   eapply evt_cut;
   [ eapply CATC with (c := fr + 32) (lo := lo);
     [ reflexivity
     | rewrite ?(MState.unsigned_lit spv) by lia; exact HST
     | rewrite ?(MState.unsigned_lit spv) by lia; unfold CATc.REAC_BOX_CATALOGUE_FRAME; lia
     | eapply (asan_cells_kept _ m); [exact HAC | exact MU |
         unfold RT_LO, RT_HI; cbn [disjoint_from]; repeat split; try exact I; left; lia]
     | intros x Hx; pose proof (f32_shadow_rng x Hx) as Hxr;
       destruct (Z.eq_dec x (Sfr fr + 4)) as [Ex | Nx];
       [ subst x; split;
         [ apply WM; exact (proj1 (HSW _ Hx))
         | destruct RW4 as ((_ & Hb4') & _); cbn [cells_bytes cbytes] in Hb4';
           rewrite app_nil_r in Hb4'; destruct Hb4' as (_ & _ & Hb4'');
           pose proof (Hb4'' 0%nat ltac:(cbn [length]; lia)) as Hm4; cbn [Z.of_nat nth_error] in Hm4;
           rewrite Z.add_0_r in Hm4; exists (Z_to_bv 8 0); exact Hm4 ]
       | destruct (HSW x Hx) as (Hw & bx & Hbx); split; [apply WM; exact Hw|];
         exists bx; rewrite (f32_mrd_munch _ m _ x MU ltac:(unfold LOWMEM_END, HIGHMEM_BEG in Hxr; lia));
         [ exact Hbx
         | cbn [outside]; split; [lia|]; split; [lia|]; split; [|exact I];
           intros [Hc1 Hc2]; exact (app_not_shadow x (Happ x ltac:(lia)) Hx) ] ]
     | intros x Hx; rewrite ?(MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; cbn [outside];
       destruct Hx as [Hx | [Hx | Hx]];
       [ unfold GOT_CELL_K in Hx; repeat split; try exact I; lia
       | unfold CELL_K in Hx; repeat split; try exact I; lia
       | pose proof (f32_shadow_rng x Hx) as Hxr;
         split; [lia|]; split; [|exact I];
         intros [Hc1 Hc2]; exact (app_not_shadow x (Happ x ltac:(lia)) Hx) ]
     | right; split; [Z.div_mod_to_equations; lia|];
       split; [exact (proj2 RWfr)|];
       split;
       [ rewrite ?(MState.unsigned_lit spv) by lia; unfold CATc.REAC_BOX_CATALOGUE_FRAME;
         destruct Hdw as [Hq|Hq]; [left; lia | right; lia]
       | pose proof (Happ (fr + 39) ltac:(lia)) as Hae;
         unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hae;
         split; [lia|]; split; [lia|]; split; [unfold APPMEM_END; lia|];
         intros i Hi; split; [apply Happ; lia|];
         exists (Z_to_bv 8 0); split;
         [ rewrite (f32_shadow_in fr i Hfr8 ltac:(lia));
           destruct RW4 as ((_ & Hb4') & _); cbn [cells_bytes cbytes] in Hb4';
           rewrite app_nil_r in Hb4'; destruct Hb4' as (_ & _ & Hb4'');
           pose proof (Hb4'' 0%nat ltac:(cbn [length]; lia)) as Hm4; cbn [Z.of_nat nth_error] in Hm4;
           rewrite Z.add_0_r in Hm4; exact Hm4
         | left; vm_compute; reflexivity ] ] ]
   | intros ms3 (a1' & a2' & m' & Ems & MUc & WMc & MIc & STc & BAc);
     subst ms3;
     replace (ret_pc (Z_to_bv 64 0x8285c)) with (Z_to_bv 64 0x8285c)
       by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]);
     replace (fr + 32 =? 0) with false in BAc by (symmetry; apply Z.eqb_neq; lia);
     apply evt_done; right; exists a1', a2', m'; split; [reflexivity|];
     split; [reflexivity|]; split; [reflexivity|];
     split;
     [ eapply munch_trans; [exact MU|];
       eapply munch_weaken; [| exact MUc];
       unfold sub_fp; intros z Hz; cbn [outside] in *;
       rewrite ?(MState.unsigned_lit spv) in Hz by lia;
       rewrite ?(MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; repeat split; try exact I; lia
     | split; [eapply wmono_trans; [exact WM | exact WMc]|];
       split; [rewrite ?(MState.unsigned_lit spv) in STc by lia; exact STc|];
       split; [exact BAc|];
       destruct RW4 as ((_ & Hb4') & _); cbn [cells_bytes cbytes] in Hb4';
       rewrite app_nil_r in Hb4'; destruct Hb4' as (_ & _ & Hb4'');
       pose proof (Hb4'' 0%nat ltac:(cbn [length]; lia)) as Hm4; cbn [Z.of_nat nth_error] in Hm4;
       rewrite Z.add_0_r in Hm4;
       rewrite (f32_mrd_munch _ _ m' (Sfr fr + 4) MUc ltac:(lia));
       [ exact Hm4
       | rewrite ?(MState.unsigned_lit spv) by lia; cbn [outside];
         unfold CATc.REAC_BOX_CATALOGUE_FRAME; split; [lia|]; split; [lia|exact I] ] ] ]).
Qed.


Local Notation STKLO mem md := (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
Local Notation STKHI mem md := (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
Local Notation OWNED H mem md := (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md).

(* The frame's place (from the F29 segment file, a working branch): the side stack FS is the word at tp, below
   the real stack; the frame is on the real stack (at or above stklo) or inside FS. *)
Lemma fra_loc : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists FS, (exists w : word, bytes_at rsegs mem RT_TP (le8 w) /\ bv_unsigned w = FS) /\
    AC.GT <= FS /\ FS + AC.FS_SIZE <= STKLO mem md /\ (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    HIGHMEM_BEG <= STKLO mem md /\
    0 <= fr /\ AC.GT <= fr /\ (forall a, fr <= a < fr + 3136 -> app_mem a) /\
    ((STKLO mem md <= fr /\ fr + 3136 <= APPMEM_END) \/ (FS <= fr /\ fr + 3136 <= FS + AC.FS_SIZE)).
Proof.
  intros g fr hb regs mem md HFRA.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Hfrapp).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof Hwin as (Hw0 & Hw1 & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (RT_fs_cells _ _ _ HRT) as (_ & _ & _ & _ & (FSw & HFSw & HFok) & _).
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
  assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw)).
  { change (AC.as_tp AC.ASYMS) with RT_TP. exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ mem md (bv_unsigned FSw) HAH Hwm HFSr)
    as (HGT & HFSlo & _ & HFSapp).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof Hhdr1 as (Hfr0 & Hfr8 & _). rewrite length_le8 in Hfr8. change (Z.of_nat 8) with 8 in Hfr8.
  exists (bv_unsigned FSw).
  split; [exists FSw; split; [exact HFSw | reflexivity]|].
  split; [exact HGT|]. split; [exact HFSlo|]. split; [exact HFSapp|]. split; [exact Hhi|].
  split; [exact Hfr0|]. split; [exact HGTfr|]. split; [exact Hfrapp|].
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal fr ltac:(lia)) as R1. pose proof (Hreal (fr + 3135) ltac:(lia)) as R2.
    left. lia.
  - assert (HFS1 : bv_unsigned FSw + AC.FS_SIZE <= 2 ^ 64) by (unfold AC.FS_SIZE in *; lia).
    pose proof (in_fs_range mem fr FSw (Hfs fr ltac:(lia)) HFSw HFS1 ltac:(lia)) as F1.
    assert (Hin : forall a, fr <= a < fr + 3136 -> bv_unsigned FSw <= a < bv_unsigned FSw + AC.FS_SIZE).
    { intros a Ha. apply (in_fs_range mem a FSw (Hfs a Ha) HFSw HFS1).
      unfold AF.SLOT_STACK, AC.FS_SIZE in *. lia. }
    pose proof (Hin (fr + 3135) ltac:(lia)) as F2.
    right. lia.
Qed.

(* A byte of a live heap block is not a frame byte (from the F29 segment file). *)
Lemma fra_blk : forall g fr hb regs mem md p n a, FRA B APIf ra g fr hb regs mem md ->
  In (p, n) (hb ++ g_H g) -> p <= a < p + n -> fr <= a < fr + 3136 -> False.
Proof.
  intros g fr hb regs mem md p n a HFRA Hin Ha Hfa.
  pose proof FRAME_BYTES_val as HFBv.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfA & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md p n HAH Hin) as (_ & _ & Hend & _ & Hall).
  destruct (Hall a Ha) as (_ & _ & _ & _ & Hnfs).
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal a Hfa). lia.
  - exact (Hnfs (Hfs a Hfa)).
Qed.

(* ===================== the segment lemma ===================== *)

Lemma seg_F32 : forall j : nat,
  Hat B APIf ra (Inv_A828c8_at B APIf ra) j -> Hat B APIf ra (Inv_A8285c_at B APIf ra) j ->
  Hat B APIf ra (Inv_A827d8_at B APIf ra) j /\ Hat B APIf ra (Inv_A82800_at B APIf ra) j.
Proof.
  intros j H81c H7b0.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  assert (Hjoin : Hat B APIf ra (Inv_A82800_at B APIf ra) j).
  { intros g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLS & HLT).
    subst c. rewrite SEGS.
    pose proof HFLS as (_ & Hs2 & Hs6r & Hs7 & Hs8 & Hs9r & Hrec & H152 & H280).
    destruct (Z.eq_dec (t_k (g_in g) j) 9) as [Ek|Ek].
    2: { (* k <> 9: the branch at 0x82804 is taken; the record part of FLS is not read *)
      pose proof HFRA as (_ & _ & _ & _ & _ & _ & _ & Hhalt & _).
      apply (@sl_run_lib fx regs (Z_to_bv 64 0x82800) mem md
        (fun R pc' mem' => pc' = Z_to_bv 64 0x828c8 /\ mem' = mem /\
           getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
           getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
           getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
           getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
           getr R 26 = getr regs 26)
        (Post B APIf ra g)).
      - exact Hhalt.
      - eapply LE.evt_mono.
        + unfold Regs6ss.mkR_of.
          eapply f32_evt_n with (k := t_k (g_in g) j);
            [ unfold rg in Hs8; exact Hs8 | apply f32_k_range | exact Ek ].
        + intros ms' (y10 & ->). eexists _, _, _. split; [reflexivity|].
          do 14 (split; [reflexivity|]). reflexivity.
      - intros R pc' mem' regs' md'
          (Hpc & Hm & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E21 & E22 & E23 & E24 & E25 & E26) Hreg Hmat.
        subst pc' mem'.
        assert (HIe : Inv_A828c8_at B APIf ra g j
                        (mkCfg (mkst regs' (Z_to_bv 64 0x828c8) mem (seg_rom rsegs)) md')).
        { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
          split.
          { apply (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA);
              [ rewrite Hreg; exact E2 | rewrite Hreg; exact E3 | rewrite Hreg; exact E4
              | rewrite Hreg; exact E8 | rewrite Hreg; exact E9 | rewrite Hreg; exact E19
              | rewrite Hreg; exact E26 | exact Hmat ]. }
          split; [exact (ent_mat APIf g _ mem md md' HENT Hmat)|].
          split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
          split; [apply (f32_flsi_regs g j fr regs); [rewrite Hreg; exact E9 | exact HFLSI]|].
          split; [apply (f32_lk_regs g fr j regs); [rewrite Hreg; exact E21 | exact HLK]|].
          split; [apply (f32_fls_regs g j phi fr regs); try (rewrite Hreg; assumption); exact HFLS|].
          split; [exact (f32_rowsel_k (g_in g) j Ek)|].
          apply (f32_lt_regs g fr j regs); [rewrite Hreg; exact E9 | exact HLT]. }
        pose proof (H81c g _ HIe) as HSR. rewrite SEGS in HSR. exact HSR. }
    (* k = 9: the row arm reads the record, so 50 <= len_j (f32_k_big) and FLS's record part holds *)
    assert (Hl50 : 50 <= flen g j) by (unfold flen; apply f32_k_big; lia).
    destruct (Hrec Hl50) as (Hp0 & Hp1 & Htg & Hph & Hphl).
    pose proof HFLSI as (((Hsp40 & _ & _ & _ & _ & _ & _ & _ & Had2624 & _) & _ & Hstkfr & _ & Had2691) &
      _ & _ & _ & HIN & HFLC).
    pose proof HFLC as (_ & _ & _ & _ & _ & _ & _ & _ & Hadfb & Had2688 & _).
    (* FLS's 50 <= len_j: the block's a_size is its length *)
    assert (Hsz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
    rewrite Hsz in HFRA, HENT.
    pose proof (fra_win B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hlosp & HSTKw).
    pose proof (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hplace & _ & HFSb & _).
    pose proof (fra_app B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (HGTfr & Hfrapp).
    pose proof (fra_loc g fr (hb1 phi (flen g j)) regs mem md HFRA)
      as (FS & (FSw & HFSw & EFS) & HGTFS & HFSlo & HFSapp & Hhi & Hfr0 & _ & _ & Hfrloc).
    pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo &
      Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5v & HAm & HAS & Hspa & HfrA & HA416 & HS4 & HAPP &
      Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAd &
      HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
    rewrite Haspz in Hlosp, HSTKw, Hplace.
    assert (HFN : FN_STACK = 1044480) by reflexivity.
    assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
    pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
    pose proof Hwin as (Hw0 & Hw1 & _).
    assert (HAb : 416 <= A /\ A + 416 <= 2 ^ 64) by (unfold HIGHMEM_BEG in Hhi; lia).
    assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
    assert (HspE : sp <= APPMEM_END) by lia.
    assert (HspH : HIGHMEM_BEG + FN_STACK <= sp) by lia.
    assert (HW16 : HIGHMEM_BEG <= sp - 16) by lia.
    assert (Hshf : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
    { intros x Hx.
      assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
      { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
      pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hin)) as His.
      replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
      unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
    assert (Hin4 : in_shadow (Sfr fr + 4)) by (apply Hshf; lia).
    pose proof (in_shadow_bnd _ Hin4) as Hrng4.
    assert (Hsh0 : shadow_addr (fr + 32) = Sfr fr + 4).
    { pose proof (f32_shadow_in fr 0 Hfr8 ltac:(lia)) as HH. rewrite Z.add_0_r in HH. exact HH. }
    assert (HSfr0 : ASAN_K <= Sfr fr)
      by (unfold Sfr, shadow_addr; unfold AC.GT in HGTfr; revert HGTfr; clear; Z.div_mod_to_equations; lia).
    (* the frame is apart from the stack window and from the frame shadow byte *)
    assert (Hpl16 : fr + 3136 <= sp - 16 \/ sp <= fr).
    { destruct (Hplace 16 ltac:(lia)) as [H|H]; [left | right]; lia. }
    assert (HplF : fr + 3136 <= sp - FN_STACK \/ sp <= fr).
    { destruct (Hplace FN_STACK ltac:(lia)) as [H|H]; [left | right]; lia. }
    assert (HWfrm : forall x, fr <= x < fr + 3136 -> ~ (sp - 16 <= x < sp)).
    { destruct Hpl16 as [Hq|Hq]; intros x Hx; lia. }
    assert (HWsh : forall x, app_mem x -> ~ (Sfr fr + 4 <= x < Sfr fr + 5)).
    { intros x Hx Hc. apply (app_not_shadow x Hx). replace x with (Sfr fr + 4) by lia. exact Hin4. }
    pose proof HHB as (Hphinz & Hphiad).
    rewrite Hsz in Hphiad.
    pose proof Hphiad as (Hphi0 & _ & Hphiend & _).
    pose proof (f32_phi_length (g_in g) j) as Hplen.
    assert (Hkbig : 50 <= t_len (g_in g) j) by exact Hl50.
    destruct Hsp40 as (Asp & HrA & Hq40).
    pose proof Hq40 as (Hq40a & Hq40b & _). rewrite length_le8 in Hq40b.
    change (Z.of_nat 8) with 8 in Hq40b.
    assert (EAsp : Asp = A) by (apply (f32_rg_near regs 9 A Asp Hr9 HrA); lia).
    subst Asp.
    (* the shadow bytes of phi + 16 and phi + 17 *)
    destruct (meta_byte mem (phi + 16) 1
                (addressable_sub mem phi (flen g j) 16 1 Hphiad ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia))
      as (b16 & Rc16 & Hok16 & Hin16).
    destruct (meta_byte mem (phi + 17) 1
                (addressable_sub mem phi (flen g j) 17 1 Hphiad ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia))
      as (b17 & Rc17 & Hok17 & Hin17).
    assert (R16s : ov_read_bytes rsegs mem (wa (Z.shiftr (phi + 16) 3 + ASAN_K)) 1 = Some [b16]).
    { apply f32_rd1. destruct Rc16 as (_ & Hb). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      exact Hb. }
    assert (R17s : ov_read_bytes rsegs mem (wa (Z.shiftr (phi + 17) 3 + ASAN_K)) 1 = Some [b17]).
    { apply f32_rd1. destruct Rc17 as (_ & Hb). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      exact Hb. }
    assert (Hok16' : bv_signed b16 = 0 \/ (phi + 16) mod 8 < bv_signed b16 <= 7)
      by (destruct Hok16 as [H|H]; [left; exact H | right; lia]).
    assert (Hok17' : bv_signed b17 = 0 \/ (phi + 17) mod 8 < bv_signed b17 <= 7)
      by (destruct Hok17 as [H|H]; [left; exact H | right; lia]).
    (* the two record bytes *)
    assert (R16b : ov_read_bytes rsegs mem (wa (phi + 16)) 1
                   = Some [Z_to_bv 8 (bv_unsigned (nth 16 (t_phi (g_in g) j) (Z_to_bv 8 0)))]).
    { rewrite f32_byte_lit.
      pose proof (f32_rd_nth mem phi (t_phi (g_in g) j) 16 Hph ltac:(rewrite Hplen; lia)) as HH.
      change (Z.of_nat 16) with 16 in HH. exact HH. }
    assert (R17b : ov_read_bytes rsegs mem (wa (phi + 17)) 1
                   = Some [Z_to_bv 8 (bv_unsigned (nth 17 (t_phi (g_in g) j) (Z_to_bv 8 0)))]).
    { rewrite f32_byte_lit.
      pose proof (f32_rd_nth mem phi (t_phi (g_in g) j) 17 Hph ltac:(rewrite Hplen; lia)) as HH.
      change (Z.of_nat 17) with 17 in HH. exact HH. }
    (* the cells of the two stores *)
    destruct Hsh as (sh & Hshb & Hshl).
    assert (RW4 : rw_cells rsegs mem (Sfr fr + 4) [C1 (nth 4 sh (Z_to_bv 8 0))]).
    { apply f32_rw1.
      - pose proof (f32_ba_nth mem (Sfr fr) sh 4 Hshb ltac:(lia)) as HB4.
        change (Z.of_nat 4) with 4 in HB4. exact HB4.
      - exact (proj1 (RT_shadow_rw _ _ _ HRT _ Hin4)). }
    assert (HST40 : stk rsegs mem fr (fr + 40))
      by (destruct (stk_split rsegs mem fr (fr + 40) (fr + 3136) Hstkfr ltac:(lia)) as (H1 & _); exact H1).
    destruct (stk_carve rsegs mem fr (fr + 40) 8 HST40 ltac:(lia)) as (_ & junk & RWfr0).
    assert (RWfr : rw_cells rsegs mem (fr + 32) [CB 8 junk])
      by (replace (fr + 32) with (fr + 40 - Z.of_nat 8) by lia; exact RWfr0).
    assert (RA40 : ro_cells rsegs mem (A + 40) [C8 (Z_to_bv 64 (fr + 32))]) by (apply ro_c8; exact Hq40).
    pose proof HRT as (HAC0 & HSW0 & _).
    assert (Hd4 : Sfr fr + 5 <= fr + 32 \/ fr + 40 <= Sfr fr + 4).
    { destruct (app_ivl_meta fr (fr + 3136) (Sfr fr + 4) Hfrapp Hin4) as [Hq|Hq];
        [left; lia | right; lia]. }
    apply (@sl_run_lib fx regs (Z_to_bv 64 0x82800) mem md
      (fun R pc' mem' =>
        (pc' = Z_to_bv 64 0x828c8 /\ mem' = mem /\ t_rowsel (g_in g) j = false /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
          getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
          getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
          getr R 26 = getr regs 26)
        \/ (pc' = Z_to_bv 64 0x8285c /\ t_rowsel (g_in g) j = true /\
          munch [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] mem mem' /\
          wmono rsegs mem mem' /\ stk rsegs mem' (sp - FN_STACK) sp /\
          bytes_at rsegs mem' (fr + 32) (le8 (Z_to_bv 64 11)) /\
          mrd rsegs mem' (wa (Sfr fr + 4)) = Some (Z_to_bv 8 0) /\
          getr R 10 = Z_to_bv 64 CATc.BOX_CATALOGUE /\ getr R 24 = Z_to_bv 64 (fr + 32) /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
          getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
          getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26))
      (Post B APIf ra g)).
    - exact Hhalt.
    - eapply LE.evt_mono.
      + unfold Regs6ss.mkR_of.
        eapply f32_evt_m with (Asp := A) (fr := fr) (phi := phi) (spv := sp) (lo := sp - FN_STACK)
          (b16 := b16) (b17 := b17) (b4 := nth 4 sh (Z_to_bv 8 0)) (junk := junk).
        * exact Hr2.
        * unfold rg in Hr9; exact Hr9.
        * unfold rg in Hr19; exact Hr19.
        * unfold rg in Hs7; exact Hs7.
        * unfold rg in Hs8; rewrite Ek in Hs8; exact Hs8.
        * unfold rg in Hr26; exact Hr26.
        * lia.
        * unfold APPMEM_END in Hphiend; lia.
        * exact R16s.
        * exact Hok16'.
        * exact R17s.
        * exact Hok17'.
        * exact R16b.
        * exact (f32_bz_range _).
        * exact R17b.
        * exact (f32_bz_range _).
        * exact RA40.
        * exact RW4.
        * exact RWfr.
        * unfold AC.GT in HGTfr; lia.
        * exact Hfr8.
        * unfold AC.GT in HGTfr; exact HGTfr.
        * exact HfrA.
        * lia.
        * exact HSfr0.
        * lia.
        * unfold HIGHMEM_BEG in *; lia.
        * lia.
        * lia.
        * exact Hspa.
        * lia.
        * exact HplF.
        * exact Hd4.
        * exact HSTKw.
        * intros a Ha; apply Hfrapp; lia.
        * exact HAC0.
        * exact HSW0.
      + intros ms' [ (y10 & y11 & y12 & Ems & Hbad)
                   | (y11 & y12 & m' & Ems & Ev16 & Ev17 & MUc & WMc & STc & BAc & MRc) ].
        * subst ms'. eexists _, _, _. split; [reflexivity|]. left.
          split; [reflexivity|]. split; [reflexivity|].
          split; [destruct Hbad as [Hb|Hb];
                  [ exact (f32_rowsel_16 (g_in g) j Ek Hb) | exact (f32_rowsel_17 (g_in g) j Ek Hb) ]|].
          do 12 (split; [reflexivity|]). reflexivity.
        * subst ms'. eexists _, _, _. split; [reflexivity|]. right.
          split; [reflexivity|].
          split; [exact (f32_rowsel_true (g_in g) j Ek Ev16 Ev17)|].
          split; [exact MUc|]. split; [exact WMc|]. split; [exact STc|].
          split; [exact BAc|]. split; [exact MRc|].
          do 13 (split; [reflexivity|]). reflexivity.
    - intros R pc' mem' regs' md'
        [ (Hpc & Hm & Hrow & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E21 & E22 & E23 & E24 & E25 & E26)
        | (Hpc & Hrow & MUc & WMc & STc & BAc & MRc & E10 & E24 & E2 & E3 & E4 & E8 & E9 & E18 & E19 &
           E21 & E22 & E23 & E25 & E26) ] Hreg Hmat.
      + (* the row is not selected: 0x828c8, memory unchanged *)
        subst pc' mem'.
        assert (HIe : Inv_A828c8_at B APIf ra g j
                        (mkCfg (mkst regs' (Z_to_bv 64 0x828c8) mem (seg_rom rsegs)) md')).
        { exists phi, regs', mem, md', fr. rewrite SEGS, Hsz. split; [reflexivity|].
          split.
          { apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs regs' mem md md' HFRA);
              [ rewrite Hreg; exact E2 | rewrite Hreg; exact E3 | rewrite Hreg; exact E4
              | rewrite Hreg; exact E8 | rewrite Hreg; exact E9 | rewrite Hreg; exact E19
              | rewrite Hreg; exact E26 | exact Hmat ]. }
          split; [exact (ent_mat APIf g _ mem md md' HENT Hmat)|].
          split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
          split; [apply (f32_flsi_regs g j fr regs); [rewrite Hreg; exact E9 | exact HFLSI]|].
          split; [apply (f32_lk_regs g fr j regs); [rewrite Hreg; exact E21 | exact HLK]|].
          split; [apply (f32_fls_regs g j phi fr regs); try (rewrite Hreg; assumption); exact HFLS|].
          split; [exact Hrow|].
          apply (f32_lt_regs g fr j regs); [rewrite Hreg; exact E9 | exact HLT]. }
        pose proof (H81c g _ HIe) as HSR. rewrite SEGS in HSR. exact HSR.
      + (* the catalogue returned: 0x8285c *)
        subst pc'.
        assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
        assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
        assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
        assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
        assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
        assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
        assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
        assert (F21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
        assert (F22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
        assert (F23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact E23).
        assert (F25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
        assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
        assert (F10 : getr regs' 10 = Z_to_bv 64 CATc.BOX_CATALOGUE) by (rewrite Hreg; exact E10).
        assert (F24 : getr regs' 24 = Z_to_bv 64 (fr + 32)) by (rewrite Hreg; exact E24).
        (* bytes outside the write set are the bytes of mem *)
        assert (Hkeep : forall q, 0 <= q < 2 ^ 64 -> ~ (sp - 16 <= q < sp) ->
                          ~ (Sfr fr + 4 <= q < Sfr fr + 5) -> ~ (fr + 32 <= q < fr + 40) ->
                          mbyte rsegs mem' q = mbyte rsegs mem q).
        { intros q Hq N1 N2 N3.
          change (mbyte rsegs mem' q) with (mrd rsegs mem' (wa q)).
          change (mbyte rsegs mem q) with (mrd rsegs mem (wa q)).
          apply (f32_mrd_munch _ mem mem' q MUc Hq).
          cbn [outside]. split; [exact N1|]. split; [exact N2|]. split; [exact N3 | exact I]. }
        (* every byte the run wrote is present again *)
        assert (HpresM : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                          exists b, mbyte rsegs mem' q = Some b).
        { intros q Hq Hp.
          destruct (Z_le_gt_dec (fr + 32) q) as [H1|H1]; [destruct (Z_lt_ge_dec q (fr + 40)) as [H2|H2]|].
          - replace q with (fr + 32 + (q - (fr + 32))) by lia.
            apply (ba_some mem' (fr + 32) (le8 (Z_to_bv 64 11)));
              [exact BAc | rewrite length_le8; change (Z.of_nat 8) with 8; lia].
          - destruct (Z.eq_dec q (Sfr fr + 4)) as [->|Hne]; [exists (Z_to_bv 8 0); exact MRc|].
            destruct (Z_le_gt_dec (sp - FN_STACK) q) as [H3|H3];
              [destruct (Z_lt_ge_dec q sp) as [H4|H4]|].
            + exact (proj2 (proj2 (proj2 STc) q ltac:(lia))).
            + rewrite (Hkeep q ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact Hp.
            + rewrite (Hkeep q ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact Hp.
          - destruct (Z.eq_dec q (Sfr fr + 4)) as [->|Hne]; [exists (Z_to_bv 8 0); exact MRc|].
            destruct (Z_le_gt_dec (sp - FN_STACK) q) as [H3|H3];
              [destruct (Z_lt_ge_dec q sp) as [H4|H4]|].
            + exact (proj2 (proj2 (proj2 STc) q ltac:(lia))).
            + rewrite (Hkeep q ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact Hp.
            + rewrite (Hkeep q ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact Hp. }
        assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
          by (intros a Ha Hw; exact (WMc (Z_to_bv 64 a) Hw)).
        (* the heap invariant, the runtime's own bytes and the stack bounds across the write set *)
        assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem' md /\
                       (forall q, OWNED (hb1 phi (flen g j) ++ g_H g) mem' md q <->
                                  OWNED (hb1 phi (flen g j) ++ g_H g) mem md q) /\
                       STKLO mem' md = STKLO mem md /\ STKHI mem' md = STKHI mem md).
        { destruct Hfrloc as [[Hlo Hhi'] | [Hlo Hhi']].
          - assert (Hst : forall a, 0 <= a < 2 ^ 64 ->
                      ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g) (STKLO mem md) a ->
                      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
            { intros a Ha Hns. apply MUc. rewrite MState.unsigned_lit by lia. cbn [outside].
              split; [|split; [|split; [|exact I]]].
              - intros [Hc1 Hc2]. apply Hns. right; left.
                unfold AF.SLOT_STACK, APPMEM_END in *; lia.
              - intros [Hc1 Hc2]. apply Hns. right; right; right. exists (fr + 32).
                split; [lia|]. right; left. unfold APPMEM_END in *; lia.
              - intros [Hc1 Hc2]. apply Hns. right; left. unfold APPMEM_END in *; lia. }
            exact (AC.a_laws_store _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem mem' md HAH Hst HwmL).
          - pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
            rewrite EFS in HFSr.
            assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
            { change (AC.as_tp AC.ASYMS) with RT_TP. rewrite <- EFS.
              exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
            assert (Hfsz : FS + AC.FS_SIZE <= 2 ^ 64)
              by (unfold AF.SLOT_STACK, APPMEM_END in *; lia).
            assert (Hmeta : forall q, fs_meta FS q -> outside
                              [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] q).
            { intros q Hq. pose proof (fs_meta_ge FS q Hq) as Hq1.
              pose proof (fs_meta_below FS q Hq) as Hq2.
              pose proof (HFSb FS Hwm HFSr) as Hq3.
              assert (Happq : app_mem q) by (apply HFSapp; unfold AC.FS_SIZE in *; lia).
              cbn [outside]. split; [|split; [|split; [|exact I]]].
              - intros [Hc1 Hc2]. unfold AC.FS_SIZE in *. lia.
              - exact (HWsh q Happq).
              - intros [Hc1 Hc2]. lia. }
            assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                      ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g) (STKLO mem md) q ->
                      ~ (FS <= q < FS + AC.FS_SIZE) ->
                      ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
                      mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
            { intros q Hq Hns Hnf Hnsh. apply MUc. rewrite MState.unsigned_lit by lia. cbn [outside].
              split; [|split; [|split; [|exact I]]].
              - intros [Hc1 Hc2]. apply Hns. right; left.
                unfold AF.SLOT_STACK, APPMEM_END in *; lia.
              - intros [Hc1 Hc2]. apply Hnsh. exists (fr + 32).
                split; [unfold AC.FS_SIZE in *; lia | lia].
              - intros [Hc1 Hc2]. apply Hnf. unfold AC.FS_SIZE in *; lia. }
            exact (a_fs_ok_store_AH AC.ASYMS _ _ _ _
                     [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)]
                     (hb1 phi (flen g j) ++ g_H g) mem mem' md FS LAWS HAH Hwm HFSr Hfsz MUc
                     (fun q _ Hw => WMc _ Hw) (fun q Hq Hp => HpresM q Hq Hp) Hmeta Hagree). }
        destruct HAHS as (HAH' & HOWN & HSTK' & HSTKHI').
        (* shadow_rw after the run *)
        assert (HSW' : shadow_rw mem').
        { intros x Hx. pose proof (in_shadow_bnd _ Hx) as Hxr.
          destruct (Z.eq_dec x (Sfr fr + 4)) as [->|Hne].
          - split; [apply WMc; exact (proj1 (HSW0 _ Hx)) | exists (Z_to_bv 8 0); exact MRc].
          - destruct (HSW0 x Hx) as (Hw & bx & Hbx). split; [apply WMc; exact Hw|].
            exists bx. rewrite (f32_mrd_munch _ mem mem' x MUc ltac:(unfold LOWMEM_END, HIGHMEM_BEG in Hxr; lia)); [exact Hbx|].
            cbn [outside]. split; [unfold HIGHMEM_BEG in *; lia|].
            split; [lia|]. split; [|exact I].
            intros [Hc1 Hc2]. exact (app_not_shadow x (Hfrapp x ltac:(lia)) Hx). }
        (* FRA and ENT across the write set and the lazy pages *)
        assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md)
          by exact (f32_fra_w g fr (hb1 phi (flen g j)) regs regs' mem mem' md sp HFRA Haspz
                      MUc WMc HAH' HSTK' HSW' STc BAc F2 F3 F4 F8 F9 F19 F26).
        assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md')
          by (apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs' regs' mem' md md' HFRA');
              try reflexivity; exact Hmat).
        assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md).
        { apply (ent_store B APIf ra g fr (hb1 phi (flen g j)) regs mem mem' md
                   [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] HENT HFRA
                   (proj1 (fr_munch_ul _ _ _) MUc)).
          - intros x Hx.
            destruct (Z.eq_dec x (Sfr fr + 4)) as [->|N4]; [right; right; right; lia|].
            destruct (Z_le_gt_dec (fr + 32) x) as [L3|L3];
              [destruct (Z_lt_ge_dec x (fr + 40)) as [L4|L4]|];
              [right; right; left; lia | |];
              (destruct (Z_le_gt_dec (sp - 16) x) as [L1|L1];
                 [destruct (Z_lt_ge_dec x sp) as [L2|L2]|];
                 [ right; left; lia
                 | left; cbn [ULF.outside]; repeat split; try exact I; lia
                 | left; cbn [ULF.outside]; repeat split; try exact I; lia ]).
          - exact HSTK'.
          - exact HSTKHI'.
          - intros a _ Ho. exact (proj2 (HOWN a) Ho). }
        pose proof (ent_mat APIf g _ mem' md md' HENT' Hmat) as HENT''.
        (* the block's bytes and its shadow bytes are apart from the write set *)
        assert (Hblkfr : forall x, phi <= x < phi + flen g j -> ~ (fr <= x < fr + 3136)).
        { intros x Hx Hc.
          exact (fra_blk g fr (hb1 phi (flen g j)) regs mem md phi (flen g j) x HFRA
                   ltac:(left; reflexivity) Hx Hc). }
        assert (Hblkapp : forall x, phi <= x < phi + flen g j -> app_mem x).
        { intros x Hx. replace x with (phi + (x - phi)) by lia.
          exact (proj1 (proj2 (proj2 (proj2 Hphiad)) (x - phi) ltac:(lia))). }
        assert (Hblkstk : phi + flen g j <= STKLO mem md).
        { destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem md phi (flen g j) HAH
                      ltac:(left; reflexivity)) as (_ & _ & Hend & _). exact Hend. }
        assert (HblkW : forall x, phi <= x < phi + flen g j -> outside
                          [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] x).
        { intros x Hx. cbn [outside]. split; [|split; [|split; [|exact I]]].
          - intros [Hc1 Hc2]. lia.
          - exact (HWsh x (Hblkapp x Hx)).
          - intros [Hc1 Hc2]. exact (Hblkfr x Hx ltac:(lia)). }
        (* the spill base and everything above it is apart from the write set *)
        assert (HWA_ : forall x, A <= x -> outside
                         [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] x).
        { intros x Hx. cbn [outside]. repeat split; try exact I; lia. }
        (* the exit cut's bundles *)
        assert (HHB' : HB mem' phi (flen g j)).
        { split; [exact Hphinz|]. rewrite Hsz.
          apply (addr_keep _ mem mem' phi (flen g j) Hphiad MUc). intros i Hi.
          apply (f32_sh_outW fr sp (phi + i) Hfr8 HW16 Hfrapp (Hblkapp (phi + i) ltac:(lia))).
          intros Hc. exact (Hblkfr (phi + i) ltac:(lia) ltac:(lia)). }
        assert (Had' : addressable mem' (fr + 2624) 6).
        { apply (addr_keep _ mem mem' (fr + 2624) 6 Had2624 MUc). intros i Hi.
          apply (f32_sh_outW fr sp (fr + 2624 + i) Hfr8 HW16 Hfrapp (Hfrapp (fr + 2624 + i) ltac:(lia))). lia. }
        assert (Had2691' : addressable mem' (fr + 2691) 17).
        { apply (addr_keep _ mem mem' (fr + 2691) 17 Had2691 MUc). intros i Hi.
          apply (f32_sh_outW fr sp (fr + 2691 + i) Hfr8 HW16 Hfrapp (Hfrapp (fr + 2691 + i) ltac:(lia))). lia. }
        (* FLSI's FLC: the 72 bytes at fragb fr = fr + 2768 and the 38 bytes at fr + 2688 lie in the frame, off the
           count variable *)
        assert (Hadfb' : addressable mem' (fragb fr) 72).
        { apply (addr_keep _ mem mem' (fragb fr) 72 Hadfb MUc). intros i Hi. unfold fragb.
          apply (f32_sh_outW fr sp (fr + 2768 + i) Hfr8 HW16 Hfrapp (Hfrapp (fr + 2768 + i) ltac:(lia))). lia. }
        assert (Had2688' : addressable mem' (fr + 2688) 38).
        { apply (addr_keep _ mem mem' (fr + 2688) 38 Had2688 MUc). intros i Hi.
          apply (f32_sh_outW fr sp (fr + 2688 + i) Hfr8 HW16 Hfrapp (Hfrapp (fr + 2688 + i) ltac:(lia))). lia. }
        assert (Hstk' : stk rsegs mem' fr (fr + 3136)).
        { destruct Hstkfr as (L1 & L2 & HS). split; [exact L1|]. split; [exact L2|].
          intros a Ha. destruct (HS a Ha) as (Hw & bb & Hb). split; [apply WMc; exact Hw|].
          destruct (Z_le_gt_dec (fr + 32) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (fr + 40)) as [H2|H2]|].
          - replace a with (fr + 32 + (a - (fr + 32))) by lia.
            apply (ba_some mem' (fr + 32) (le8 (Z_to_bv 64 11)));
              [exact BAc | rewrite length_le8; change (Z.of_nat 8) with 8; lia].
          - exists bb. rewrite (f32_mrd_munch _ mem mem' a MUc ltac:(unfold AC.GT in HGTfr; lia));
              [exact Hb|].
            cbn [outside]. split; [exact (HWfrm a Ha)|].
            split; [exact (HWsh a (Hfrapp a Ha))|]. split; [lia | exact I].
          - exists bb. rewrite (f32_mrd_munch _ mem mem' a MUc ltac:(unfold AC.GT in HGTfr; lia));
              [exact Hb|].
            cbn [outside]. split; [exact (HWfrm a Ha)|].
            split; [exact (HWsh a (Hfrapp a Ha))|]. split; [lia | exact I]. }
        (* FLSI's harness input block f1_IN: a live entry block (when it is not empty), below stklo and off the
           frame *)
        pose proof HIN as (HinH0 & Hinad & _).
        assert (Hpapp : forall x, g_p g <= x < g_p g + g_n g -> app_mem x).
        { intros x Hx. replace x with (g_p g + (x - g_p g)) by lia.
          exact (proj1 (proj2 (proj2 (proj2 Hinad)) (x - g_p g) ltac:(lia))). }
        assert (Hpblk : forall x, g_p g <= x < g_p g + g_n g ->
                          g_p g + g_n g <= STKLO mem md /\ ~ (fr <= x < fr + 3136)).
        { intros x Hx.
          assert (HinH : In (g_p g, g_n g) (hb1 phi (flen g j) ++ g_H g))
            by (apply in_or_app; right; apply HinH0; lia).
          destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md (g_p g) (g_n g) HAH HinH) as (_ & _ & HpEnd & _).
          split; [exact HpEnd|].
          intros Hc. exact (fra_blk g fr (hb1 phi (flen g j)) regs mem md (g_p g) (g_n g) x HFRA HinH Hx Hc). }
        assert (HIN' : f1_IN g mem').
        { apply (f32_f1in_mem g mem mem' _ MUc); [ | | exact HIN].
          - intros x Hx. destruct (Hpblk x Hx) as (HpEnd & Hpfr).
            cbn [outside]. split; [lia|]. split; [exact (HWsh x (Hpapp x Hx))|].
            split; [intros [Hc1 Hc2]; exact (Hpfr ltac:(lia)) | exact I].
          - intros x Hx. destruct (Hpblk x Hx) as (_ & Hpfr).
            apply (f32_sh_outW fr sp x Hfr8 HW16 Hfrapp (Hpapp x Hx)).
            intros Hc. exact (Hpfr ltac:(lia)). }
        pose proof (f32_flsi_mem g j fr regs regs' mem mem' _ A Hr9 (proj1 HAb) (proj2 HAb) F9 MUc HWA_
                      Had' Hstk' Had2691' HIN' Hadfb' Had2688' HFLSI) as HFLSI'.
        assert (HLK' : LK g fr j regs' mem').
        { apply (f32_lk_mem g fr j regs regs' mem mem' _ F21 MUc); [|exact HLK].
          intros x Hx. cbn [outside]. split; [exact (HWfrm x ltac:(lia))|].
          split; [exact (HWsh x (Hfrapp x ltac:(lia)))|]. split; [lia | exact I]. }
        pose proof (f32_flsx_mem g j phi fr regs regs' mem mem' _ A Hr9 (proj1 HAb) (proj2 HAb)
                      F9 F18 F22 F23 F25 MUc HWA_ HblkW HFLSI' (flsx_of_fls g j phi fr regs mem HFLS)) as HFLSX'.
        (* LT: the frame records lie inside the frame and the first-fragment spills above A *)
        assert (HWr : forall x, fr + 2688 <= x < fr + 2840 -> outside
                        [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] x).
        { intros x Hx. cbn [outside]. split; [exact (HWfrm x ltac:(lia))|].
          split; [exact (HWsh x (Hfrapp x ltac:(lia)))|]. split; [lia | exact I]. }
        assert (HWb : forall x, fr + 2880 <= x < fr + 2915 ->
                        outside [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] x /\
                        outside [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] (shadow_addr x)).
        { intros x Hx. split.
          - cbn [outside]. split; [exact (HWfrm x ltac:(lia))|].
            split; [exact (HWsh x (Hfrapp x ltac:(lia)))|]. split; [lia | exact I].
          - apply (f32_sh_outW fr sp x Hfr8 HW16 Hfrapp (Hfrapp x ltac:(lia))). lia. }
        pose proof (f32_lt_mem g fr j regs regs' mem mem' _ A Hr9 (proj1 HAb) (proj2 HAb) F9 MUc HWA_ HWr HWb
                      HLT) as HLT'.
        assert (HIe : Inv_A8285c_at B APIf ra g j
                        (mkCfg (mkst regs' (Z_to_bv 64 0x8285c) mem' (seg_rom rsegs)) md')).
        { exists phi, regs', mem', md', fr. rewrite SEGS, Hsz. split; [reflexivity|].
          split; [exact HFRA''|]. split; [exact HENT''|].
          split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB'|]. split; [exact HFLSI'|].
          split; [exact HLK'|]. split; [exact HFLSX'|]. split; [exact Hrow|].
          split; [unfold rg; exact F10|]. split; [unfold rg; exact F24|].
          split; [unfold q64; exact BAc | exact HLT']. }
        pose proof (H7b0 g _ HIe) as HSR. rewrite SEGS in HSR. exact HSR. }
  split; [| exact Hjoin].
  (* the 0x827d8 entry: the three branches to 0x82bf4 are not taken, then the join *)
  intros g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLS &
    Hcls & Hiff & Hev & HLT).
  pose proof HFLS as (_ & _ & _ & _ & _ & _ & _ & H152 & H280).
  pose proof HFLSI as (((_ & _ & _ & H160 & _) & _) & _).
  subst c. rewrite SEGS.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo &
    Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5v & HAm & HAS & Hspa & HfrA & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAd &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  (* a0 <> 0, TF and the classify event *)
  assert (Hcls' : exists e, t_cls (g_in g) j = Some e)
    by (destruct (t_cls (g_in g) j) as [e|]; [exists e; reflexivity | exfalso; apply Hcls; reflexivity]).
  destruct Hcls' as (e & Ecl).
  pose proof (f32_cls_e (g_in g) j e Ecl) as (He5 & Hk0 & Hlen50).
  pose proof (f32_cls_src (g_in g) j e Ecl) as Hsrc.
  pose proof (f32_cls_TF (g_in g) j e Ecl) as HTF.
  assert (Hne : bv_eqb (getr regs 10) (Z_to_bv 64 0) = false).
  { apply Bool.not_true_iff_false. intros HC. apply bv_eqb_eq in HC.
    exact (Hsrc (proj1 Hiff HC)). }
  destruct H152 as (A1 & HrA1 & Hq152).
  destruct H280 as (A2 & HrA2 & Hq280).
  destruct H160 as (A3 & HrA3 & Hq160).
  assert (HAb : 416 <= A /\ A + 416 <= 2 ^ 64).
  { pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ mem md HAH)
      as Hhi8.
    pose proof Hwin as (Hw0 & Hw1 & _).
    unfold HIGHMEM_BEG in Hhi8. unfold AF.SLOT_STACK in *. lia. }
  assert (HA1 : A1 = A).
  { pose proof Hq152 as (Hb0 & Hb & _). rewrite length_le8 in Hb. change (Z.of_nat 8) with 8 in Hb.
    apply (f32_rg_near regs 9 A A1 Hr9 HrA1); lia. }
  assert (HA2 : A2 = A).
  { pose proof Hq280 as (Hb0 & Hb & _). rewrite length_le8 in Hb. change (Z.of_nat 8) with 8 in Hb.
    apply (f32_rg_near regs 9 A A2 Hr9 HrA2); lia. }
  assert (HA3 : A3 = A).
  { pose proof Hq160 as (Hb0 & Hb & _). rewrite length_le8 in Hb. change (Z.of_nat 8) with 8 in Hb.
    apply (f32_rg_near regs 9 A A3 Hr9 HrA3); lia. }
  subst A1 A2 A3.
  pose proof (Hev e Ecl) as Hu32.
  pose proof Hq160 as (Hq160a & Hq160b & _). rewrite length_le8 in Hq160b.
  change (Z.of_nat 8) with 8 in Hq160b.
  pose proof Hu32 as (Hu32a & Hu32b & _). rewrite length_le4 in Hu32b.
  change (Z.of_nat 4) with 4 in Hu32b.
  apply (@sl_run_lib fx regs (Z_to_bv 64 0x827d8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x82800 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26)
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    + unfold Regs6ss.mkR_of.
      eapply f32_evt_a with (A := A) (EV := fr + 528) (tf := b2z (t_tfill (g_in g) j))
        (so := b2z (t_sum_ok (g_in g) j)) (ev := e).
      * unfold rg in Hr9; exact Hr9.
      * lia.
      * pose proof Hq280 as (_ & Hb & _). rewrite length_le8 in Hb. change (Z.of_nat 8) with 8 in Hb. lia.
      * exact Hne.
      * apply f32_rd8; [exact Hq152 | apply length_le8].
      * unfold b2z; destruct (t_tfill (g_in g) j); [right | left]; reflexivity.
      * apply f32_rd8; [exact Hq280 | apply length_le8].
      * unfold b2z; destruct (t_sum_ok (g_in g) j); [right | left]; reflexivity.
      * intros (Htf0 & Hso0). unfold b2z in Htf0, Hso0.
        destruct HTF as [Hs|Ht];
          [ rewrite Hs in Hso0; discriminate | rewrite Ht in Htf0; discriminate ].
      * apply f32_rd8; [exact Hq160 | apply length_le8].
      * lia.
      * lia.
      * apply f32_rd4; [exact Hu32 | apply length_le4].
      * lia.
    + intros ms' (y10 & y11 & ->). eexists _, _, _. split; [reflexivity|].
      do 14 (split; [reflexivity|]). reflexivity.
  - intros R pc' mem' regs' md'
      (Hpc & Hm & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E21 & E22 & E23 & E24 & E25 & E26) Hreg Hmat.
    subst pc' mem'.
    assert (HIj : Inv_A82800_at B APIf ra g j
                    (mkCfg (mkst regs' (Z_to_bv 64 0x82800) mem (seg_rom rsegs)) md')).
    { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA);
          [ rewrite Hreg; exact E2 | rewrite Hreg; exact E3 | rewrite Hreg; exact E4
          | rewrite Hreg; exact E8 | rewrite Hreg; exact E9 | rewrite Hreg; exact E19
          | rewrite Hreg; exact E26 | exact Hmat ]. }
      split; [exact (ent_mat APIf g _ mem md md' HENT Hmat)|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [apply (f32_flsi_regs g j fr regs); [rewrite Hreg; exact E9 | exact HFLSI]|].
      split; [apply (f32_lk_regs g fr j regs); [rewrite Hreg; exact E21 | exact HLK]|].
      split; [apply (f32_fls_regs g j phi fr regs); try (rewrite Hreg; assumption); exact HFLS|].
      apply (f32_lt_regs g fr j regs); [rewrite Hreg; exact E9 | exact HLT]. }
    pose proof (Hjoin g _ HIj) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.
End S.

(* ===================== route (C): the narrowed twins (reac_box_catalogue_contract_on) ===================== *)

(* Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery) and its 10:34Z amendment): the shadow bytes
   f32_fra_w needs present in mem' through its shadow_rw premise.  Its proof needs the whole shadow of mem' (FRA's RT
   by RT_meta_write, the frame's 392 shadow bytes); every shadow byte outside the write set W keeps mem's byte, which
   FRA's own RT on mem holds (AsanRTInv.RT_shadow_rw), so the premise is needed only for the shadow byte inside W:
   S(fr) + 4, the one the segment stores into (sb zero,4(s3) with s3 = S(fr); the catalogue's window [sp - 16, sp)
   and the count variable [fr + 32, fr + 40) are app memory).  It reads no other shadow byte through it. *)
Definition f32_fra_w_shadow_R (fr : Z) : Z -> Prop := fun a => Sfr fr + 4 <= a < Sfr fr + 5.

(* The Section S above stays as it is: its lemmas take CATc.reac_box_catalogue_contract (Hypothesis CATC).  Its two
   shadow-carrying lemmas get their twins here: f32_fra_w_on (no callee; FF only) and f32_evt_m_on (under the
   catalogue's narrowed contract).  seg_F32 gets no twin: no image-A stage cites a Seg cut-to-cut lemma (a Theorem Labs lane
   11:36Z, L3-recipe.md section 4b (a working note, not in this delivery)). *)
Section S_on.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* Route (C): the catalogue's narrowed contract (reac_box_catalogue_c.v); f32_evt_m_on uses it. *)
Hypothesis CATC_on : CATc.reac_box_catalogue_contract_on.

(* Route (C): f32_fra_w under the region premise shadow_rw_on (f32_fra_w_shadow_R fr) mem'.  No callee; f32_fra_w
   stays as it is (every old line unchanged), and this twin carries its own proof: f32_fra_w's, with shadow_rw mem'
   rebuilt first from RT on mem and the region (HSW' below). *)
Lemma f32_fra_w_on : forall g fr hb regs regs' mem mem' md spv,
  FRA B APIf ra g fr hb regs mem md ->
  AC.aspZ regs = spv ->
  munch [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] mem mem' ->
  wmono rsegs mem mem' ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  SRO.shadow_rw_on (f32_fra_w_shadow_R fr) mem' ->
  stk rsegs mem' (spv - FN_STACK) spv ->
  bytes_at rsegs mem' (fr + 32) (le8 (Z_to_bv 64 11)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md spv HFRA Hasp MU WM HAH' HSTK HSWR HWIN HBA
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hplace & _ & _ & _).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWAd &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (Esp : spv = sp) by (rewrite <- Hasp; exact Haspz).
  clear Hasp. subst spv.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAE : APPMEM_END = 140737488355328) by reflexivity.
  assert (HLE : LOWMEM_END = 2147450880) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold AC.GT in HGT.
  assert (Hwin0 : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (Hpl : fr + 3136 <= sp - 16 \/ sp <= fr).
  { destruct (Hplace 16 ltac:(lia)) as [H|H]; rewrite Haspz in H; [left | right]; lia. }
  assert (Hhi0 : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  assert (HW16 : HIGHMEM_BEG <= sp - 16) by lia.
  (* the frame's shadow bytes *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (Hin4 : in_shadow (Sfr fr + 4)) by (apply HshIS; lia).
  pose proof (in_shadow_bnd _ Hin4) as HS4b.
  pose proof (in_shadow_bnd _ (HshIS (Sfr fr) ltac:(lia))) as HS0b.
  pose proof (in_shadow_bnd _ (HshIS (Sfr fr + 391) ltac:(lia))) as HS379b.
  assert (Hmeta4 : Sfr fr + 4 < fr \/ fr + 3136 <= Sfr fr + 4).
  { apply (app_ivl_meta fr (fr + 3136)); [exact Happ | exact Hin4]. }
  (* Route (C): the whole shadow of mem' again, from RT on mem (AsanRTInv.RT_shadow_rw, form item 3) and the region
     premise.  The segment stored into S(fr) + 4 alone (f32_fra_w_shadow_R fr); every other shadow byte is outside W
     (the window [sp - 16, sp) is above HIGHMEM_BEG, the count variable is app memory), so mem' keeps mem's byte, and
     wmono keeps it writable.  The rest is f32_fra_w's proof. *)
  assert (HSW' : shadow_rw mem').
  { intros a Ha. pose proof (in_shadow_bnd a Ha) as Hab.
    destruct (Z_le_dec (Sfr fr + 4) a) as [L1|L1]; [destruct (Z_lt_dec a (Sfr fr + 5)) as [L2|L2]|];
      [exact (HSWR a (conj L1 L2) Ha) | |];
      (destruct (AsanRTInv.RT_shadow_rw _ _ _ HRT a Ha) as (Hw & b & Hb); split; [exact (WM _ Hw)|];
       exists b; rewrite (f32_mrd_munch _ mem mem' a MU ltac:(lia)); [exact Hb|];
       cbn [outside]; split; [lia|]; split; [lia|];
       split; [intros Hc; exact (app_not_shadow a (Happ a ltac:(lia)) Ha) | exact I]). }
  (* outside W for the classes of addresses FRA reads *)
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1.
    assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. cbn [outside]. repeat split; try exact I; lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  assert (HWfr : forall x, fr <= x < fr + 24 ->
                   outside [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] x).
  { intros x Hx. cbn [outside]. repeat split; try exact I; lia. }
  assert (HWA : forall x, A <= x ->
                  outside [(sp - 16, sp); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] x).
  { intros x Hx. cbn [outside]. repeat split; try exact I; lia. }
  (* the image's read-only bytes are below GT <= fr *)
  assert (HRO : ro_agree rsegs mem').
  { intros a Ha. pose proof (f32_ro_lo a Ha) as Hlo. pose proof (bv_unsigned_in_range 64 a) as Ha64.
    change (bv_modulus 64) with (2 ^ 64) in Ha64. unfold AC.GT in Hlo.
    assert (E : mrd rsegs mem' a = mrd rsegs mem a).
    { unfold mrd. rewrite (MU a); [reflexivity|]. cbn [outside]. repeat split; try exact I; lia. }
    rewrite E. exact (Hro a Ha). }
  (* an addressable byte outside the frame keeps its shadow byte *)
  assert (Hkeep1 : forall a, addressable mem a 1 -> ~ (fr <= a < fr + 3136) -> addressable mem' a 1).
  { intros a Ha Hnf. apply (addr_keep _ mem mem' a 1 Ha MU). intros i Hi.
    replace (a + i) with a by lia.
    apply (f32_sh_outW fr sp a Hfr8 HW16 Happ (addr1_app mem a Ha)). lia. }
  (* RT *)
  assert (HRT' : AsanRTInv.RT sp mem' md).
  { eapply (AsanRTInv.RT_meta_write sp sp mem mem' md md); [exact HRT | exact MU | exact WM | | ].
    - unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [left; lia | exact I].
    - intros a Ha. destruct (HSW' a Ha) as (_ & b & Hb). exists b. exact Hb. }
  exists A, sp, s5.
  split; [exact HRT'|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfrz [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfrz|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo2 | exact Hhi2]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * apply (fsrec_munch_lo APIf (hb ++ g_H g) mem mem' md _ fr Hrec HAH (proj1 (fr_munch_ul _ _ _) MU)).
          -- intros x Hx. apply (proj2 (fr_outside_lib _ _)). cbn [outside].
             repeat split; try exact I; lia.
          -- intros x Hx Hnb Hlo. apply (proj2 (fr_outside_lib _ _)). cbn [outside].
             split; [lia|].
             split; [intros Hc; apply (app_not_shadow x Hx); replace x with (Sfr fr + 4) by lia; exact Hin4|].
             split; [lia | exact I]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWfr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWfr. lia. }
  split.
  { assert (HSTKsh : stk rsegs mem' (Sfr fr) (Sfr fr + 392)).
    { split; [lia|]. split; [lia|]. intros a Ha. exact (HSW' a (HshIS a Ha)). }
    destruct (stk_bytes rsegs mem' (Sfr fr) (Sfr fr + 392) HSTKsh ltac:(lia)) as (sh' & Hl' & Hb').
    exists sh'. split; [exact Hb'|]. rewrite Hl'. replace (Sfr fr + 392 - Sfr fr) with 392 by lia.
    reflexivity. }
  split.
  { destruct Hwin as (Hw0 & Hw1 & Hwv). split; [exact Hw0|]. split; [exact Hw1|].
    intros a Ha. destruct (Hwv a Ha) as (Hwa & b & Hb). split; [exact (WM _ Hwa)|].
    assert (Hcnt : fr + 32 <= a < fr + 40 -> exists b', mrd rsegs mem' (wa a) = Some b').
    { intros Hc. replace a with (fr + 32 + (a - (fr + 32))) by lia.
      apply (ba_some mem' (fr + 32) (le8 (Z_to_bv 64 11))); [exact HBA | rewrite length_le8; change (Z.of_nat 8) with 8; lia]. }
    assert (Hout : ~ (sp - 16 <= a < sp) -> ~ (fr + 32 <= a < fr + 40) ->
                   exists b', mrd rsegs mem' (wa a) = Some b').
    { intros N1 N2. exists b. rewrite (f32_mrd_munch _ mem mem' a MU ltac:(lia)); [exact Hb|].
      cbn [outside]. split; [exact N1|]. split; [lia|]. split; [exact N2 | exact I]. }
    destruct (Z_le_gt_dec (sp - 16) a) as [L3|L3]; [destruct (Z_lt_ge_dec a sp) as [L4|L4]|].
    - destruct HWIN as (_ & _ & HW). exact (proj2 (HW a ltac:(lia))).
    - destruct (Z_le_gt_dec (fr + 32) a) as [L1|L1]; [destruct (Z_lt_ge_dec a (fr + 40)) as [L2|L2]|];
        [apply Hcnt; lia | apply Hout; lia | apply Hout; lia].
    - destruct (Z_le_gt_dec (fr + 32) a) as [L1|L1]; [destruct (Z_lt_ge_dec a (fr + 40)) as [L2|L2]|];
        [apply Hcnt; lia | apply Hout; lia | apply Hout; lia]. }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWA. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn [length] in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split.
  { intros a Hin. apply Hkeep1; [exact (HAG a Hin)|].
    pose proof (f32_AG_low a Hin) as Hl. unfold AC.GT in Hl. lia. }
  split; [intros a H1 H2; exact (Hkeep1 a (HWAd a H1 H2) H2)|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* Route (C): f32_evt_m's run under the catalogue's narrowed contract CATc.reac_box_catalogue_contract_on
   (reac_box_catalogue_c.v, a working branch d68c95046c8), whose shadow_rw premise is dropped.  f32_evt_m used
   its premise `shadow_rw m` only to give the callee `shadow_rw` on the post-store memory (its catalogue bullet);
   the run itself reads its two shadow bytes (phi + 16, phi + 17) through the ov_read_bytes premises, stores S(fr) + 4
   through rw_cells (Sfr fr + 4), and the callee's asan_cells through asan_cells_kept.  Under the narrowed contract
   the proof never uses the premise, so it is DROPPED (no region); the post states no shadow_rw.  The statement is
   f32_evt_m's with `shadow_rw m ->` removed; the proof is f32_evt_m's without that bullet. *)
Lemma f32_evt_m_on :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (Asp fr phi spv lo v16 v17 : Z) (b16 b17 b4 : byte) (junk : list byte),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 Asp -> x19 = Z_to_bv 64 (Sfr fr) ->
    x23 = Z_to_bv 64 phi -> x24 = Z_to_bv 64 9 -> x26 = Z_to_bv 64 ASAN_K ->
    0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 16) 3 + ASAN_K)) 1 = Some [b16] ->
    (bv_signed b16 = 0 \/ (phi + 16) mod 8 < bv_signed b16 <= 7) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 17) 3 + ASAN_K)) 1 = Some [b17] ->
    (bv_signed b17 = 0 \/ (phi + 17) mod 8 < bv_signed b17 <= 7) ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [Z_to_bv 8 v16] -> 0 <= v16 < 256 ->
    ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [Z_to_bv 8 v17] -> 0 <= v17 < 256 ->
    ro_cells rsegs m (Asp + 40) [C8 (Z_to_bv 64 (fr + 32))] ->
    rw_cells rsegs m (Sfr fr + 4) [C1 b4] -> rw_cells rsegs m (fr + 32) [CB 8 junk] ->
    0 <= fr -> fr mod 8 = 0 -> 6283264 <= fr -> fr + 3136 <= Asp -> Asp + 48 <= 2 ^ 64 ->
    ASAN_K <= Sfr fr -> Sfr fr + 5 <= lo -> 6283264 <= lo -> HIGHMEM_BEG <= lo ->
    lo + 16 <= spv -> spv <= Asp -> spv < 2 ^ 64 ->
    (fr + 3136 <= lo \/ spv <= fr) ->
    (Sfr fr + 5 <= fr + 32 \/ fr + 40 <= Sfr fr + 4) ->
    stk rsegs m lo spv ->
    (forall a, fr + 32 <= a < fr + 40 -> app_mem a) ->
    asan_cells m ->
    LE.evt rsegs
      (fun ms' =>
         (exists y10 y11 y12,
            ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                          x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fcs None m (seg_rom rsegs)
            /\ (v16 <> 205 \/ v17 <> 234))
         \/ (exists y11 y12 m',
            ms' = MS (mkR (Z_to_bv 64 0x8285c) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 CATc.BOX_CATALOGUE) y11 y12
                          x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (fr + 32)) x25 x26 x27 x28
                          x29 x30 x31) Fr (Z_to_bv 64 0x8285c) fcs None m' (seg_rom rsegs)
            /\ v16 = 205 /\ v17 = 234
            /\ munch [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] m m'
            /\ wmono rsegs m m' /\ stk rsegs m' lo spv
            /\ bytes_at rsegs m' (fr + 32) (le8 (Z_to_bv 64 11))
            /\ mrd rsegs m' (wa (Sfr fr + 4)) = Some (Z_to_bv 8 0)))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m Asp fr phi spv lo v16 v17 b16 b17 b4 junk
    E2 E9 E19 E23 E24 E26 Hp0 Hp1 R16s Hok16 R17s Hok17 R16b Hv16 R17b Hv17
    RA40 RW4 RWfr Hfr0 Hfr8 HGT HfrA HAb HSfr0 HSlo HloG HloH Hlosp HspA HspB Hdw Hd4 HST Happ HAC.
  subst x2 x9 x19 x23 x24 x26.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  step. step. f32_nt.
  eapply evt_cut;
    [ eapply (f32_chk16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi b16);
      [reflexivity | reflexivity | lia | lia | exact R16s | exact Hok16]
    | intros ms1 (y11 & y12 & ->) ].
  step. rewrite ?(f32_zxb8 v16) by lia.
  step. step.
  destruct (Z.eq_dec v16 205) as [Ev16 | Nv16].
  2: { f32_tk. apply evt_done. left. do 3 eexists. split; [reflexivity|]. left. exact Nv16. }
  subst v16. f32_nt.
  eapply evt_cut;
    [ eapply (f32_chk17 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi b17);
      [reflexivity | reflexivity | lia | lia | exact R17s | exact Hok17]
    | intros ms2 (y11' & y12' & ->) ].
  step. rewrite ?(f32_zxb8 v17) by lia.
  step. step.
  destruct (Z.eq_dec v17 234) as [Ev17 | Nv17].
  2: { f32_tk. apply evt_done. left. do 3 eexists. split; [reflexivity|]. right. exact Nv17. }
  subst v17. f32_nt.
  (* the two stores and the catalogue call *)
  pose proof (munch_refl [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct Hd4 as [Hd4 | Hd4];
  (rewrite ?(MState.unsigned_lit (Sfr fr)) by lia;
   step;
   change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]; mem_after_store;
   rewrite ?(MState.unsigned_lit Asp) by lia;
   step;
   rewrite ?(MState.unsigned_lit (fr + 32)) by lia;
   step; step; step;
   eapply evt_cut;
   [ eapply CATC_on with (c := fr + 32) (lo := lo);
     [ reflexivity
     | rewrite ?(MState.unsigned_lit spv) by lia; exact HST
     | rewrite ?(MState.unsigned_lit spv) by lia; unfold CATc.REAC_BOX_CATALOGUE_FRAME; lia
     | eapply (asan_cells_kept _ m); [exact HAC | exact MU |
         unfold RT_LO, RT_HI; cbn [disjoint_from]; repeat split; try exact I; left; lia]
     | intros x Hx; rewrite ?(MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; cbn [outside];
       destruct Hx as [Hx | [Hx | Hx]];
       [ unfold GOT_CELL_K in Hx; repeat split; try exact I; lia
       | unfold CELL_K in Hx; repeat split; try exact I; lia
       | pose proof (f32_shadow_rng x Hx) as Hxr;
         split; [lia|]; split; [|exact I];
         intros [Hc1 Hc2]; exact (app_not_shadow x (Happ x ltac:(lia)) Hx) ]
     | right; split; [Z.div_mod_to_equations; lia|];
       split; [exact (proj2 RWfr)|];
       split;
       [ rewrite ?(MState.unsigned_lit spv) by lia; unfold CATc.REAC_BOX_CATALOGUE_FRAME;
         destruct Hdw as [Hq|Hq]; [left; lia | right; lia]
       | pose proof (Happ (fr + 39) ltac:(lia)) as Hae;
         unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hae;
         split; [lia|]; split; [lia|]; split; [unfold APPMEM_END; lia|];
         intros i Hi; split; [apply Happ; lia|];
         exists (Z_to_bv 8 0); split;
         [ rewrite (f32_shadow_in fr i Hfr8 ltac:(lia));
           destruct RW4 as ((_ & Hb4') & _); cbn [cells_bytes cbytes] in Hb4';
           rewrite app_nil_r in Hb4'; destruct Hb4' as (_ & _ & Hb4'');
           pose proof (Hb4'' 0%nat ltac:(cbn [length]; lia)) as Hm4; cbn [Z.of_nat nth_error] in Hm4;
           rewrite Z.add_0_r in Hm4; exact Hm4
         | left; vm_compute; reflexivity ] ] ]
   | intros ms3 (a1' & a2' & m' & Ems & MUc & WMc & MIc & STc & BAc);
     subst ms3;
     replace (ret_pc (Z_to_bv 64 0x8285c)) with (Z_to_bv 64 0x8285c)
       by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]);
     replace (fr + 32 =? 0) with false in BAc by (symmetry; apply Z.eqb_neq; lia);
     apply evt_done; right; exists a1', a2', m'; split; [reflexivity|];
     split; [reflexivity|]; split; [reflexivity|];
     split;
     [ eapply munch_trans; [exact MU|];
       eapply munch_weaken; [| exact MUc];
       unfold sub_fp; intros z Hz; cbn [outside] in *;
       rewrite ?(MState.unsigned_lit spv) in Hz by lia;
       rewrite ?(MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; repeat split; try exact I; lia
     | split; [eapply wmono_trans; [exact WM | exact WMc]|];
       split; [rewrite ?(MState.unsigned_lit spv) in STc by lia; exact STc|];
       split; [exact BAc|];
       destruct RW4 as ((_ & Hb4') & _); cbn [cells_bytes cbytes] in Hb4';
       rewrite app_nil_r in Hb4'; destruct Hb4' as (_ & _ & Hb4'');
       pose proof (Hb4'' 0%nat ltac:(cbn [length]; lia)) as Hm4; cbn [Z.of_nat nth_error] in Hm4;
       rewrite Z.add_0_r in Hm4;
       rewrite (f32_mrd_munch _ _ m' (Sfr fr + 4) MUc ltac:(lia));
       [ exact Hm4
       | rewrite ?(MState.unsigned_lit spv) by lia; cbn [outside];
         unfold CATc.REAC_BOX_CATALOGUE_FRAME; split; [lia|]; split; [lia|exact I] ] ] ]).
Qed.

End S_on.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
