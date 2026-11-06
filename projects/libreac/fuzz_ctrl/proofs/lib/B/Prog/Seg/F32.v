(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 1535 of its 1667 lines of code are new or changed and 879 lines of the source are left out. *)
(* Segment F32 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the range
   0x82b38-0x82bc8 (slot-plan-asan-ubsan section 2 row F32, call CAT@0x82bc8, twin C03). Image-B port of the
   image-A segment 0x827d8-0x8285c.

     0x82b38 beqz a0,82fa4      a0 = the bcmp result of F31: not taken, the source field differs from our[]
     0x82b3c ld a0,184(s1)      [A+184] = the type-filler flag
     0x82b40 or a0,a0,s9        s9 = the block-sum flag
     0x82b44 andi a0,a0,1
     0x82b48 beqz a0,82fa4      not taken: classify = Some e gives k = 1 (type filler) or block sum 0
     0x82b4c ld a0,192(s1)      [A+192] = fr+528, the classify event word
     0x82b50 lw a0,0(a0)        a0 = e
     0x82b54 li a1,5
     0x82b58 bltu a1,a0,82fa4   not taken: 0 <= e <= 5
     0x82b5c li a0,9            (also the target of F31's bnez at 0x82af8, classify = None)
     0x82b60 bne s8,a0,82c90    s8 = k: taken when k <> 9
     0x82b64 beqz s2,82fa0      T67: not taken, Phi <> 0
     0x82b68 li a0,-17; 0x82b6c bltu a0,s2,82fa0    T68: not taken, Phi + 16 does not wrap
     0x82b70 addi a0,s2,16
     0x82b74-0x82b80            the instrumented check of the byte Phi+16: the shadow byte at ((Phi+16) >> 3) +
                                0x7fff8000 is 0 (the granule lies inside the addressable block HB(Phi), len >= 50),
                                so the branch to the error path 0x82dbc (whose `bge a2,a1` goes to the call of
                                __asan_report_load1 at 0x830ac) is not taken
     0x82b84 lbu a0,0(a0); 0x82b88 li a1,205; 0x82b8c bne a0,a1,82c90   taken when Phi[16] <> 0xcd
     0x82b90 li a0,-18; 0x82b94 bltu a0,s2,82fa0    T69: not taken, Phi + 17 does not wrap
     0x82b98-0x82ba8            the instrumented check of the byte Phi+17 (error path 0x82e10, whose `bge a2,a1`
                                goes to the call of __asan_report_load1 at 0x830c4, not taken)
     0x82bac lbu a0,0(a0); 0x82bb0 li a1,234; 0x82bb4 bne a0,a1,82c90   taken when Phi[17] <> 0xea
     0x82bb8 sb zero,4(s3)      s3 = S(fr): the shadow byte of the granule [fr+32, fr+40) becomes 0 (the count
                                variable comes into scope and is marked usable)
     0x82bbc ld s7,160(s1)      [A+160] = fr+32, the count variable
     0x82bc0 sd zero,0(s7)      the count variable is zeroed
     0x82bc4 mv a0,s7
     0x82bc8 jal reac_box_catalogue      returns to 0x82bcc with a0 = T = 0x9f620 and the count 11 at fr+32

   Entry cuts: the official Inv_B82b38_at (seg_F32) and the official Inv_B82b5c_at (seg_F32_af8: 0x82b5c, the
   target of F31's bnez at 0x82af8, lies in this range). Exits: the official Inv_B82bcc_at (F33's entry, through
   reac_box_catalogue) and the official Inv_B82c90_at at 0x82c90 (the target of the three `bne`s; the official
   Inv_B82ca0_at is one basic block further, after the reac_box_catalogue_match call of 0x82c9c, which belongs to
   the F36 range of the plan, where Seg/F36.v's seg_F36_c2c composes it). Phi off the side stack (the c2c cut's
   ~ a_in_fs) comes from FRA's live block (Phi, a_size len), which has at least one byte (f32_notfs). FTK, FTURN
   (with the Phi bytes) and IFS g fr (S j) pass through: FTK is [A+184] = tfill, s6 = 1, s8 = k, [A+272] = k and
   s9 = sum_ok, IFS includes the local `first` [fr+2880, fr+2920); the segment writes none of their registers or
   bytes.

   The segment's memory writes are the shadow byte S(fr)+4 and the 8 bytes at fr+32, plus the callee's own
   [sp-16, sp) and its 8 bytes at fr+32: FRA moves across them by the local f32_fra_run (the image-A twin used
   Tac_slot's sl_fr_meta, which does not allow the callee's window below sp) and ENT (the cuts' entry-state
   relation) by Tac_slot's ent_store, then ent_mat across the model step; LK (with the frame-loop set FLI) moves
   by Tac_ro.lk_keep. No cut carries mem_inv: ro_agree on the new memory comes from Tac_slot's sl_ro_keep (the
   writes are above GT). The callee contract is a Section Hypothesis (reac_box_catalogue_contract,
   lib/B/Prog/reac_box_catalogue_c.v). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcClassify RcClassifyLib RcKind RcModel
  RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Import ListNotations.
(* The short name YK11 can resolve to lib/Reusable/YK11.v (loaded by lib.Prog's RcParse chain); this file's
   registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are (as in Seg/F30.v). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module CATc := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_box_catalogue_c.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module RC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassify.
Module RCL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassifyLib.
Module RM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcModel.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.

(* ========================= model facts ========================= *)

Lemma f32_inb_nonneg : forall inp c, 0 <= inb inp c.
Proof. intros inp c. unfold inb, RIM.bz. apply (proj1 (bv_unsigned_in_range _ _)). Qed.

(* The frame cursor c_j stays in [0, n]. *)
Lemma f32_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH]; cbn [fc].
  - unfold c0, nlen. lia.
  - pose proof (f32_inb_nonneg inp (fc inp j)) as I1. pose proof (f32_inb_nonneg inp (fc inp j + 1)) as I2.
    unfold f_next, f_body, f_len, f_h, f_L, f_left, nlen in *.
    destruct (2 <=? Z.of_nat (length inp) - fc inp j); lia.
Qed.

(* Phi's byte list is the whole frame: its length is len_j. *)
Lemma f32_phi_len : forall inp j, Z.of_nat (length (t_phi inp j)) = t_len inp j.
Proof.
  intros inp j. pose proof (f32_fc_range inp j) as Hc.
  pose proof (f32_inb_nonneg inp (fc inp j)) as I1. pose proof (f32_inb_nonneg inp (fc inp j + 1)) as I2.
  unfold t_phi, t_len, f_phi, f_len, f_body, f_h, f_L, f_left, nlen in *.
  rewrite length_firstn, length_skipn.
  destruct (2 <=? Z.of_nat (length inp) - fc inp j); lia.
Qed.

(* With len >= 50 the frame's first 50 bytes need no padding. *)
Lemma f32_tg : forall inp j, 50 <= t_len inp j -> t_g inp j = firstn 50 (t_phi inp j).
Proof.
  intros inp j H. pose proof (f32_phi_len inp j) as HL.
  unfold t_g, fr50. rewrite firstn_app. replace (50 - length (t_phi inp j))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma f32_nth_firstn : forall n (l : list byte) k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  induction n as [|n IH]; intros l k d H; [lia|].
  destruct l as [|x l]; cbn.
  - destruct k; reflexivity.
  - destruct k as [|k]; [reflexivity|]. apply IH. lia.
Qed.

Lemma f32_fs1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l RP.cp_z].
Proof.
  induction l as [|x l IH]; intros [|k] H; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

(* The parse kind is one of the 14 kinds. *)
Lemma f32_kind_range : forall fr, 0 <= RP.cp_kind fr <= 13.
Proof.
  intros fr. unfold RP.cp_kind, RcKind.KL1.
  repeat (match goal with |- context [if ?b then _ else _] =>
            lazymatch b with true => fail | false => fail | _ => destruct b end end; cbv iota).
  all: lia.
Qed.

Lemma f32_k_range : forall inp j, 0 <= t_k inp j <= 13.
Proof.
  intros inp j. unfold t_k, RP.ctrlparse.
  destruct (RP.cp_hdr (t_len inp j) (t_g inp j)); cbn [fst]; [apply f32_kind_range | lia].
Qed.

Lemma f32_k9_len : forall inp j, t_k inp j = 9 -> 50 <= t_len inp j.
Proof.
  intros inp j H. unfold t_k in H.
  destruct (RCL.cl_hdr (t_len inp j) (t_g inp j)) as [H50 _]; [rewrite H; discriminate | exact H50].
Qed.

Lemma f32_kind1 : forall fr, RP.cp_kind fr = 1 -> RP.cp_type fr 0 0 = true.
Proof.
  intros fr. unfold RP.cp_kind, RcKind.KL1.
  destruct (RP.cp_type fr 0 0); [intros; reflexivity|]. cbv iota.
  repeat (match goal with |- context [if ?b then _ else _] =>
            lazymatch b with true => fail | false => fail | _ => destruct b end end; cbv iota).
  all: intros H; discriminate H.
Qed.

Lemma f32_eq6_refl : forall l, RC.cl_eq6 l l = true.
Proof. intros l. unfold RC.cl_eq6. cbn [seq forallb]. rewrite !Z.eqb_refl. reflexivity. Qed.

(* The classify output record (as Seg/F31.v's f31_cls_B / f31_cp_b / f31_struct_src). *)
Lemma f32_cls_B : forall inp j e, t_cls inp j = Some e -> t_B inp j = RP.cp_struct (t_g inp j) (t_k inp j).
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (RCL.classify_some _ _ _ _ H) as (K & _).
  destruct (RCL.cl_hdr _ _ K) as [_ HB]. exact HB.
Qed.

Lemma f32_cp_b : forall fr i v, RP.cp_v fr i = v -> 0 <= v < 256 -> RP.cp_b fr i = Z_to_bv 8 v.
Proof.
  intros fr i v E Hv. apply bv_eq. unfold RP.cp_v in E. rewrite E. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small; lia.
Qed.

Lemma f32_struct_src : forall fr k,
  firstn 6 (skipn 4 (RP.cp_struct fr k)) =
  [RP.cp_b fr 6; RP.cp_b fr 7; RP.cp_b fr 8; RP.cp_b fr 9; RP.cp_b fr 10; RP.cp_b fr 11].
Proof. intros fr k. unfold RP.cp_struct. destruct (RP.cp_rec fr), (k =? 6); reflexivity. Qed.

(* classify = Some e (C1.8 of the classify model): the source field of the classify output differs from our[], the
   type-filler flag or the block-sum flag is set, and 0 <= e <= 5. *)
Lemma f32_cls : forall inp j e, t_cls inp j = Some e ->
  firstn 6 (skipn 4 (t_B inp j)) <> OUR inp /\ (t_tfill inp j = true \/ t_sum_ok inp j = true) /\ 0 <= e <= 5.
Proof.
  intros inp j e H. pose proof (f32_cls_B inp j e H) as HB. unfold t_cls in H.
  destruct (RCL.classify_some _ _ _ _ H) as (Hk & H50 & _ & Heq6 & Hks & He).
  assert (Hbig : t_big inp j = true) by (unfold t_big; apply Z.leb_le; exact H50).
  split; [|split; [|exact He]].
  - rewrite HB, f32_struct_src. intros E.
    pose proof (RCL.cl_eq6_src (t_g inp j) (OUR inp)) as Hs.
    rewrite E, Heq6, f32_eq6_refl in Hs. discriminate Hs.
  - destruct Hks as [K1|K0].
    + left. revert K1. unfold RP.ctrlparse.
      destruct (RP.cp_hdr (t_len inp j) (t_g inp j)); cbn [fst]; intros K1; [|discriminate K1].
      pose proof (f32_kind1 _ K1) as T. unfold RP.cp_type in T.
      apply andb_prop in T as [T1 T2]. unfold t_tfill. rewrite Hbig, T1, T2. reflexivity.
    + (* The kernel's conversion of RC.cl_bsum against RcModel.blocksum diverges in the direction
         blocksum -> cl_bsum, so the bridge is stated with cl_bsum on the left and K0 is rewritten by it. *)
      right. assert (Hb : RC.cl_bsum (t_g inp j) = RM.blocksum (skipn 18 (t_g inp j))) by reflexivity.
      rewrite Hb in K0. unfold t_sum_ok. rewrite Hbig, K0. reflexivity.
Qed.

(* ========================= bit-vector and memory helpers ========================= *)

Lemma f32_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma f32_ltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

(* `bltu aX,s2` with aX a negative literal: the left operand is read modulo 2^64. *)
Lemma f32_ltu_wrap : forall x y, 0 <= y < 2 ^ 64 -> y <= x mod 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hy Hxy. unfold bv_ltu. rewrite MState.unsigned_lit_wrap, (MState.unsigned_lit y) by lia.
  apply Z.ltb_ge. lia.
Qed.

(* The two UBSan checks `li aX,-17 / -18; bltu aX,s2` (T68, T69): not taken when Phi + 17 / 18 <= 2^64. *)
Lemma f32_ltu_m17 : forall y, 0 <= y -> y + 17 <= 2 ^ 64 -> bv_ltu (Z_to_bv 64 (-17)) (Z_to_bv 64 y) = false.
Proof.
  intros y H1 H2. apply f32_ltu_wrap; [lia|].
  replace ((-17) mod 2 ^ 64) with (2 ^ 64 - 17) by reflexivity. lia.
Qed.

Lemma f32_ltu_m18 : forall y, 0 <= y -> y + 18 <= 2 ^ 64 -> bv_ltu (Z_to_bv 64 (-18)) (Z_to_bv 64 y) = false.
Proof.
  intros y H1 H2. apply f32_ltu_wrap; [lia|].
  replace ((-18) mod 2 ^ 64) with (2 ^ 64 - 18) by reflexivity. lia.
Qed.

Lemma f32_rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.

Lemma f32_rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H.
  pose proof (bytes_at_ov_read rsegs m a (le8 v) 0 8 H ltac:(rewrite length_le8; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH.
Qed.

Lemma f32_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H.
  pose proof (bytes_at_ov_read rsegs m a (le4 v) 0 4 H ltac:(rewrite length_le4; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by (rewrite length_le4; lia). exact HH.
Qed.

(* Two addresses in different 8-byte granules have different shadow bytes. *)
Lemma f32_gran_ne : forall x y, 0 <= x -> 0 <= y -> y mod 8 = 0 -> ~ (y <= x < y + 8) -> x / 8 <> y / 8.
Proof. intros x y Hx Hy Hm Hn E. apply Hn. Z.div_mod_to_equations. lia. Qed.

(* A byte whose shadow byte is one of the frame's 392 lies in the frame (fr is 32-aligned, 3136 = 8 * 392). *)
Lemma f32_sh_frame : forall fr a, fr mod 32 = 0 -> 0 <= a -> Sfr fr <= shadow_addr a < Sfr fr + FRAME_SHADOW ->
  fr <= a < fr + FRAME_BYTES.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr a Hm Ha Hc. unfold Sfr, shadow_addr in Hc. Z.div_mod_to_equations. lia.
Qed.

(* A byte of an addressable block: its granule's shadow byte is 0 (AsanRTFacts.meta8 on the granule start). *)
Lemma f32_sh : forall m p L o, addressable m p (AC.a_size L) -> 7 <= o -> o + 8 <= L ->
  bytes_at rsegs m (Z.shiftr (p + o) 3 + ASAN_K) [Z_to_bv 8 0].
Proof.
  intros m p L o HA Ho HL.
  pose proof HA as (Hp0 & _ & _ & _).
  pose proof (Z.mod_pos_bound (p + o) 8 ltac:(lia)) as Hr.
  assert (H8 : addressable m (p + (o - (p + o) mod 8)) 8)
    by (apply (addressable_sub m p (AC.a_size L)); [exact HA | lia | lia | unfold AC.a_size; lia]).
  destruct (meta8 m _ H8) as [[_ RB] _].
  assert (E : Z.shiftr (p + (o - (p + o) mod 8)) 3 = Z.shiftr (p + o) 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    replace (p + (o - (p + o) mod 8)) with ((p + o) / 8 * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite E in RB. exact RB.
Qed.

(* mrd is unchanged outside a run's write set. *)
Lemma f32_mrd_munch : forall W m m' x, munch W m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  mrd rsegs m' (wa x) = mrd rsegs m (wa x).
Proof.
  intros W m m' x MU Hx Ho. unfold mrd.
  rewrite (MU (wa x) ltac:(rewrite Mem.wa_unsigned by lia; exact Ho)). reflexivity.
Qed.

(* ADDR-KEEP for a run that may write shadow bytes: the block stays addressable when its own shadow bytes are
   outside the write set. *)
Lemma f32_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HW.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok).
  split; [exact Hap|]. exists b. split; [|exact Hok].
  rewrite (f32_mrd_munch W m m' (shadow_addr (p + i)) MU); [exact Hb| |exact (HW i Hi)].
  pose proof (shadow_of_app (p + i) Hap) as His. pose proof (in_shadow_range _ His). lia.
Qed.

(* The runtime's own cells survive a run that writes nothing below 6283264 (= AC.GT). *)
Lemma f32_cells_keep : forall W m m', asan_cells m -> munch W m m' ->
  (forall x, 0 <= x < 6283264 -> outside W x) -> asan_cells m'.
Proof.
  intros W m m' H MU HW.
  unfold asan_cells, CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND,
    GOT_HIEND, MIDBEG, GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, REAL_MEMSET, GOT_REAL_MEMSET in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat split;
    (eapply fl_bytes; [eassumption | exact MU |]);
    (try rewrite length_le8); (try rewrite length_le4); cbn [length]; intros x Hx; apply HW; lia.
Qed.

(* ========================= the machine runs ========================= *)

(* 0x82b38 -> 0x82b5c: the three branches to the abort pair 0x82fa4 are not taken (a0 <> 0 from the bcmp of F31,
   the type-filler / block-sum flag is 1, the event word is at most 5). The run reads [A+184] (the type-filler
   flag; s9 holds the block-sum flag), [A+192] and the 4 bytes of the event word; it writes no memory. *)
Lemma f32e_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (A tf sm E e : Z),
    s1 = Z_to_bv 64 A -> s9 = Z_to_bv 64 sm -> bv_eqb a0 (Z_to_bv 64 0) = false ->
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= E -> E + 4 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 184) (le8 (Z_to_bv 64 tf)) ->
    bytes_at rsegs m (A + 192) (le8 (Z_to_bv 64 E)) ->
    bytes_at rsegs m E (le4 (Z_to_bv 64 e)) ->
    (tf = 0 \/ tf = 1) -> (sm = 0 \/ sm = 1) -> (tf = 1 \/ sm = 1) -> 0 <= e <= 5 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 5) a2 a3 a4 a5 a6 a7 s2 s3 s4
                              s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b38) fcr None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m A tf sm E e -> -> H0 HA0 HA1 HE0 HE1 H184 H192 HEv Htf Hsm Hor He.
  pose proof (f32_rd8 m (A + 184) (Z_to_bv 64 tf) H184) as R184.
  pose proof (f32_rd8 m (A + 192) (Z_to_bv 64 E) H192) as R192.
  pose proof (f32_rd4 m E (Z_to_bv 64 e) HEv) as RE.
  destruct Htf as [Etf|Etf]; destruct Hsm as [Esm|Esm]; subst tf; subst sm;
    try (exfalso; destruct Hor as [Hc|Hc]; discriminate Hc).
  all: (* 0x82b38 beqz a0: not taken *)
       step; rewrite H0; cbv iota;
       (* 0x82b3c ld a0,184(s1); 0x82b40 or a0,a0,s9; 0x82b44 andi a0,a0,1 *)
       step; step; step;
       (* 0x82b48 beqz a0: not taken *)
       step; if_false;
       (* 0x82b4c ld a0,192(s1); 0x82b50 lw a0,0(a0) *)
       step; step;
       rewrite (RCL.cl_sx32 e) by lia;
       (* 0x82b54 li a1,5; 0x82b58 bltu a1,a0: not taken *)
       step; step;
       rewrite (f32_ltu_lit 5 e) by lia; if_false;
       apply evt_done; reflexivity.
Qed.

(* 0x82b5c with s8 = k <> 9: `bne s8,a0` is taken to 0x82c90. *)
Lemma f32n_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (k : Z),
    s8 = Z_to_bv 64 k -> 0 <= k < 2 ^ 64 -> k <> 9 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 9) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                              (Z_to_bv 64 k) s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c90) fcr None m
                           (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  intros. subst s8. step. step.
  rewrite (f32_eqb_lit k 9) by lia. if_true.
  apply evt_done. reflexivity.
Qed.

(* 0x82b5c with k = 9 and Phi[16] <> 0xcd: the two UBSan checks and the instrumented check of Phi+16 pass, and
   `bne a0,a1` at 0x82b8c is taken to 0x82c90. The run reads the byte Phi+16 and its shadow byte. *)
Lemma f32m1_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (phi : Z) (b16 : byte),
    s2 = Z_to_bv 64 phi -> s8 = Z_to_bv 64 9 -> s10 = Z_to_bv 64 ASAN_K ->
    0 < phi -> phi + 50 <= APPMEM_END ->
    bytes_at rsegs m (Z.shiftr (phi + 16) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 16) [b16] -> bv_unsigned b16 <> 205 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (zxb b16) (Z_to_bv 64 205) a2 a3 a4 a5 a6 a7 s2 s3 s4
                              s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c90) fcr None m
                           (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m phi b16 -> -> -> Hp0 Hp1 Hsh Hb Hne.
  unfold APPMEM_END in Hp1.
  pose proof (f32_rd1 m _ _ Hsh) as RDsh. pose proof (f32_rd1 m _ _ Hb) as RDb.
  pose proof (bv_unsigned_in_range 8 b16) as Rb. unfold bv_modulus in Rb.
  change (2 ^ Z.of_N 8) with 256 in Rb.
  (* 0x82b5c li a0,9; 0x82b60 bne s8,a0: not taken *)
  step. step. rewrite (f32_eqb_lit 9 9) by lia. if_false.
  (* 0x82b64 beqz s2 (T67): not taken *)
  step. rewrite (f32_eqb_lit phi 0) by lia. if_false.
  (* 0x82b68 li a0,-17; 0x82b6c bltu a0,s2 (T68): not taken *)
  step. step. rewrite (f32_ltu_m17 phi) by lia. cbv iota.
  (* 0x82b70 addi a0,s2,16; 0x82b74 srli; 0x82b78 add; 0x82b7c lb; 0x82b80 bnez: not taken (the shadow byte is
     0, so the error path 0x82dbc and its call of __asan_report_load1 at 0x830ac are not reached) *)
  step. step. rewrite (MState.unsigned_lit (phi + 16)) by lia.
  step. step. step. if_false.
  (* 0x82b84 lbu a0,0(a0); 0x82b88 li a1,205; 0x82b8c bne a0,a1: taken *)
  step. step. step.
  unfold zxb. rewrite (f32_eqb_lit (bv_unsigned b16) 205) by lia. if_true.
  apply evt_done. reflexivity.
Qed.

(* 0x82b5c with k = 9, Phi[16] = 0xcd and Phi[17] <> 0xea: `bne a0,a1` at 0x82bb4 is taken to 0x82c90. *)
Lemma f32m2_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (phi : Z) (b17 : byte),
    s2 = Z_to_bv 64 phi -> s8 = Z_to_bv 64 9 -> s10 = Z_to_bv 64 ASAN_K ->
    0 < phi -> phi + 50 <= APPMEM_END ->
    bytes_at rsegs m (Z.shiftr (phi + 16) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 16) [Z_to_bv 8 205] ->
    bytes_at rsegs m (Z.shiftr (phi + 17) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 17) [b17] -> bv_unsigned b17 <> 234 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (zxb b17) (Z_to_bv 64 234) a2 a3 a4 a5 a6 a7 s2 s3 s4
                              s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c90) fcr None m
                           (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m phi b17 -> -> -> Hp0 Hp1 Hsh16 Hb16 Hsh17 Hb17 Hne.
  unfold APPMEM_END in Hp1.
  pose proof (f32_rd1 m _ _ Hsh16) as RDsh16. pose proof (f32_rd1 m _ _ Hb16) as RDb16.
  pose proof (f32_rd1 m _ _ Hsh17) as RDsh17. pose proof (f32_rd1 m _ _ Hb17) as RDb17.
  pose proof (bv_unsigned_in_range 8 b17) as Rb. unfold bv_modulus in Rb.
  change (2 ^ Z.of_N 8) with 256 in Rb.
  step. step. rewrite (f32_eqb_lit 9 9) by lia. if_false.
  step. rewrite (f32_eqb_lit phi 0) by lia. if_false.
  step. step. rewrite (f32_ltu_m17 phi) by lia. cbv iota.
  step. step. rewrite (MState.unsigned_lit (phi + 16)) by lia.
  step. step. step. if_false.
  (* 0x82b84 lbu a0,0(a0); 0x82b88 li a1,205; 0x82b8c bne a0,a1: not taken *)
  step. step. step. rewrite (RCL.cl_zxb_eqb (Z_to_bv 8 205) 205) by lia. if_false.
  (* 0x82b90 li a0,-18; 0x82b94 bltu a0,s2 (T69): not taken *)
  step. step. rewrite (f32_ltu_m18 phi) by lia. cbv iota.
  (* 0x82b98 addi a0,s2,17; 0x82b9c srli; 0x82ba0 add; 0x82ba4 lb; 0x82ba8 bnez: not taken (the shadow byte is
     0, so the error path 0x82e10 and its call of __asan_report_load1 at 0x830c4 are not reached) *)
  step. step. rewrite (MState.unsigned_lit (phi + 17)) by lia.
  step. step. step. if_false.
  (* 0x82bac lbu a0,0(a0); 0x82bb0 li a1,234; 0x82bb4 bne a0,a1: taken *)
  step. step. step.
  unfold zxb. rewrite (f32_eqb_lit (bv_unsigned b17) 234) by lia. if_true.
  apply evt_done. reflexivity.
Qed.

(* The registered globals and the RELRO range lie in the image, below AC.GT = 0x5fe000 (checked over the list). *)
Lemma f32_glob_bound : forall G a,
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 6283264)) G = true -> in_globals G a -> 0 <= a < 6283264.
Proof.
  intros G a Hb (lo & len & Hin & Hr).
  rewrite forallb_forall in Hb. pose proof (Hb _ Hin) as H. cbn [fst snd] in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma f32_AG_bound : forall a, in_globals AF.frame_AG a -> 0 <= a < 6283264.
Proof. intros a Ha. exact (f32_glob_bound AF.frame_AG a ltac:(vm_compute; reflexivity) Ha). Qed.

Lemma f32_RELRO_bound : forall a, in_globals AF.frame_RELRO a -> 0 <= a < 6283264.
Proof. intros a Ha. exact (f32_glob_bound AF.frame_RELRO a ltac:(vm_compute; reflexivity) Ha). Qed.

Lemma f32_store_ok : forall m a n (jn : nat), wr_at rsegs m a n -> Z.of_nat jn <= n ->
  store_ok rsegs m (wa a) jn = true.
Proof.
  intros m a n jn H Hj. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  apply (wr_at_store_ok rsegs m a n 0 jn); [exact H | lia | lia].
Qed.

(* An app byte and a shadow byte are never the same address. *)
Lemma f32_app_shadow_ne : forall x y, app_mem x -> in_shadow y -> x <> y.
Proof. intros x y Hx Hy E. subst y. exact (app_not_shadow x Hx Hy). Qed.

(* The frame's shadow range [S(fr), S(fr) + 392) lies in the shadow map. *)
Lemma f32_frsh_shadow : forall fr x, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr x Happ Hx.
  assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
  { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
  pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
  replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
  unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia.
Qed.

(* 0x82b5c -> 0x82bcc with k = 9, Phi[16] = 0xcd and Phi[17] = 0xea: the two instrumented checks pass, the shadow
   byte of the granule [fr+32, fr+40) is set to 0 (the count variable is marked usable), the count variable is
   zeroed, and reac_box_catalogue runs. Touched ranges: it reads the bytes Phi+16, Phi+17 and their shadow bytes,
   the spill [A+160, A+168), and writes the shadow byte S(fr)+4, the 8 bytes [fr+32, fr+40) and the callee's own
   stack window [sp-16, sp). *)
Lemma f32c_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fcr : bv 32) (m : word -> option byte) (A fr phi lo spv : Z),
    CATc.reac_box_catalogue_contract ->
    s1 = Z_to_bv 64 A -> s2 = Z_to_bv 64 phi -> s3 = Z_to_bv 64 (Sfr fr) -> s8 = Z_to_bv 64 9 ->
    s10 = Z_to_bv 64 ASAN_K -> sp = Z_to_bv 64 spv ->
    0 < phi -> phi + 50 <= APPMEM_END -> 0 <= A -> A + 448 <= 2 ^ 64 ->
    AC.GT <= fr -> fr mod 32 = 0 -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    HIGHMEM_BEG <= lo -> lo + 16 <= spv -> spv <= APPMEM_END -> spv <= A ->
    (fr + FRAME_BYTES <= spv - 16 \/ spv <= fr) ->
    bytes_at rsegs m (Z.shiftr (phi + 16) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 16) [Z_to_bv 8 205] ->
    bytes_at rsegs m (Z.shiftr (phi + 17) 3 + ASAN_K) [Z_to_bv 8 0] ->
    bytes_at rsegs m (phi + 17) [Z_to_bv 8 234] ->
    bytes_at rsegs m (A + 160) (le8 (Z_to_bv 64 (fr + 32))) ->
    wr_at rsegs m (fr + 32) 8 -> wr_at rsegs m (Sfr fr + 4) 1 ->
    stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CATc.BOX_CATALOGUE) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4
                       s5 s6 (Z_to_bv 64 (fr + 32)) s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x82bcc) fcr None m' (seg_rom rsegs)
         /\ munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] m m'
         /\ wmono rsegs m m' /\ stk rsegs m' lo spv
         /\ bytes_at rsegs m' (fr + 32) (le8 (Z_to_bv 64 11))
         /\ (forall a, in_shadow a -> exists b, mrd rsegs m' (wa a) = Some b)
         /\ (forall bs, bytes_at rsegs m (Sfr fr) bs -> length bs = Z.to_nat FRAME_SHADOW ->
               exists bs', bytes_at rsegs m' (Sfr fr) bs' /\ length bs' = Z.to_nat FRAME_SHADOW))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82b5c) fcr None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcr m A fr phi lo spv HCAT -> -> -> -> -> -> Hp0 Hp1 HA0 HA1 HGT Hfm Happ Hlo Hlo16 Hspe HAsp Hdisj
    Hsh16 Hb16 Hsh17 Hb17 H160 HWR8 HWR1 HST HAC HSW.
  unfold APPMEM_END in Hp1, Hspe. unfold AC.GT in HGT. unfold HIGHMEM_BEG in Hlo.
  pose proof (f32_rd1 m _ _ Hsh16) as RDsh16. pose proof (f32_rd1 m _ _ Hb16) as RDb16.
  pose proof (f32_rd1 m _ _ Hsh17) as RDsh17. pose proof (f32_rd1 m _ _ Hb17) as RDb17.
  pose proof (f32_rd8 m _ _ H160) as RD160.
  (* the frame's bytes and the shadow byte of the count variable *)
  assert (Hc8 : forall a, fr + 32 <= a < fr + 40 -> app_mem a) by (intros a Ha; apply Happ; lia).
  assert (Hcapp : app_mem (fr + 32)) by (apply Hc8; lia).
  assert (Hshc : shadow_addr (fr + 32) = Sfr fr + 4)
    by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
  assert (HshIS : in_shadow (Sfr fr + 4)) by (rewrite <- Hshc; apply shadow_of_app; exact Hcapp).
  assert (HshB : 2147450880 <= Sfr fr + 4 < 17594333495296)
    by (pose proof HshIS as Hs;
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs; lia).
  assert (Hfrb : fr + FRAME_BYTES <= 140737488355328)
    by (pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha;
        unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha; lia).
  (* the three branch targets of the mismatch paths are not taken here *)
  step. step. rewrite (f32_eqb_lit 9 9) by lia. if_false.
  step. rewrite (f32_eqb_lit phi 0) by lia. if_false.
  step. step. rewrite (f32_ltu_m17 phi) by lia. cbv iota.
  step. step. rewrite (MState.unsigned_lit (phi + 16)) by lia.
  step. step. step. if_false.
  step. step. step. rewrite (RCL.cl_zxb_eqb (Z_to_bv 8 205) 205) by lia. if_false.
  step. step. rewrite (f32_ltu_m18 phi) by lia. cbv iota.
  step. step. rewrite (MState.unsigned_lit (phi + 17)) by lia.
  step. step. step. if_false.
  step. step. step. rewrite (RCL.cl_zxb_eqb (Z_to_bv 8 234) 234) by lia. if_false.
  (* 0x82bb8 sb zero,4(s3): the shadow byte of [fr+32, fr+40) becomes 0 *)
  pose proof (f32_store_ok m (Sfr fr + 4) 1 1%nat HWR1 ltac:(cbn; lia)) as ST1.
  step.
  match goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      replace bs with [Z_to_bv 8 0] by (vm_compute; reflexivity)
  end.
  set (m1 := write_to_mem m (Z_to_bv 64 (Sfr fr + 4)) [Z_to_bv 8 0]) in *.
  assert (MU1 : munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] m m1).
  { unfold m1. apply (munch_write _ m m (Sfr fr + 4) [Z_to_bv 8 0] (munch_refl _ m));
      [lia | cbn [length]; lia | cbn [inside length]; lia]. }
  assert (WM1 : wmono rsegs m m1) by (unfold m1; apply (wmono_write rsegs m m); apply wmono_refl).
  assert (HB1 : bytes_at rsegs m1 (Sfr fr + 4) [Z_to_bv 8 0])
    by (unfold m1; apply bytes_at_write_same; cbn [length]; lia).
  assert (ST1' : stk rsegs m1 lo spv)
    by (unfold m1; apply (stk_write rsegs m lo spv (Sfr fr + 4) [Z_to_bv 8 0] HST); cbn [length]; lia).
  assert (WR81 : wr_at rsegs m1 (fr + 32) 8) by (unfold m1; apply wr_at_write; exact HWR8).
  (* 0x82bbc ld s7,160(s1): the count variable's address *)
  assert (RD160' : ov_read_bytes rsegs m1 (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 (fr + 32)))).
  { apply f32_rd8. unfold m1. apply (bytes_at_write_other rsegs m (Sfr fr + 4) [Z_to_bv 8 0]);
      [exact H160 | lia | cbn [length]; lia | cbn [length]; rewrite length_le8;
       unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in *; lia]. }
  step.
  (* 0x82bc0 sd zero,0(s7): the count variable is zeroed *)
  pose proof (f32_store_ok m1 (fr + 32) 8 8%nat WR81 ltac:(cbn; lia)) as ST2.
  step.
  match goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      replace bs with (le8 (Z_to_bv 64 0)) by (vm_compute; reflexivity)
  end.
  set (m2 := write_to_mem m1 (Z_to_bv 64 (fr + 32)) (le8 (Z_to_bv 64 0))) in *.
  assert (MU2 : munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] m m2).
  { unfold m2. apply (munch_write _ m m1 (fr + 32) (le8 (Z_to_bv 64 0)) MU1);
      [lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]. }
  assert (WM2 : wmono rsegs m m2) by (unfold m2; apply (wmono_write rsegs m m1); exact WM1).
  assert (ST2' : stk rsegs m2 lo spv)
    by (unfold m2; apply (stk_write rsegs m1 lo spv (fr + 32) (le8 (Z_to_bv 64 0)) ST1');
        [lia | rewrite length_le8; lia]).
  assert (WR82 : wr_at rsegs m2 (fr + 32) 8) by (unfold m2; apply wr_at_write; exact WR81).
  assert (HB2 : bytes_at rsegs m2 (Sfr fr + 4) [Z_to_bv 8 0]).
  { unfold m2. apply (bytes_at_write_other rsegs m1 (fr + 32) (le8 (Z_to_bv 64 0)));
      [exact HB1 | lia | rewrite length_le8; lia |
       cbn [length]; rewrite length_le8;
       unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in *; lia]. }
  (* the premises of the catalogue contract on the memory after the two stores *)
  assert (HoutW2 : forall x, 0 <= x < 6283264 ->
            outside [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] x).
  { intros x Hx. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (HAC2 : asan_cells m2) by (apply (f32_cells_keep _ m m2 HAC MU2 HoutW2)).
  assert (HmrdW : forall x, 0 <= x < 2 ^ 64 ->
            ~ (Sfr fr + 4 <= x < Sfr fr + 5) -> ~ (fr + 32 <= x < fr + 40) -> ~ (spv - 16 <= x < spv) ->
            mrd rsegs m2 (wa x) = mrd rsegs m (wa x)).
  { intros x Hx H1 H2 H3. apply (f32_mrd_munch _ m m2 x MU2 Hx).
    cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (HSW2 : shadow_rw m2).
  { intros a Hin. split; [apply WM2, (proj1 (HSW a Hin))|].
    destruct (Z.eq_dec a (Sfr fr + 4)) as [->|Hne].
    - exists (Z_to_bv 8 0). destruct HB2 as (_ & _ & HB2b). pose proof (HB2b 0%nat ltac:(cbn; lia)) as HH.
      cbn [Z.of_nat nth_error] in HH. rewrite Z.add_0_r in HH. exact HH.
    - destruct (HSW a Hin) as (_ & b & Hb). exists b. rewrite HmrdW; [exact Hb | | lia | | ].
      + pose proof (in_shadow_range a Hin). lia.
      + intros Hc. exact (app_not_shadow a (Hc8 a Hc) Hin).
      + intros Hc. apply (app_not_shadow a); [|exact Hin].
        unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
  assert (HADR : addressable m2 (fr + 32) 8).
  { split; [lia|]. split; [lia|].
    split; [pose proof (Happ (fr + 39) ltac:(lia)) as Ha;
            unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha |- *; lia|].
    intros i Hi. split; [apply Hc8; lia|].
    exists (Z_to_bv 8 0). split.
    - replace (shadow_addr (fr + 32 + i)) with (Sfr fr + 4).
      + destruct HB2 as (_ & _ & HB2b). pose proof (HB2b 0%nat ltac:(cbn; lia)) as HH.
        cbn [Z.of_nat nth_error] in HH. rewrite Z.add_0_r in HH. exact HH.
      + unfold Sfr, shadow_addr. replace (fr + 32 + i) with (fr + 4 * 8 + i) by lia.
        replace (fr + 4 * 8 + i) with ((fr / 8 + 4) * 8 + i) by (Z.div_mod_to_equations; lia).
        rewrite Z.div_add_l by lia. rewrite (Z.div_small i 8) by lia. lia.
    - unfold shadow_ok. left. reflexivity. }
  (* 0x82bc4 mv a0,s7; 0x82bc8 jal reac_box_catalogue *)
  step. step.
  unfold CATc.reac_box_catalogue_contract, CATc.REAC_BOX_CATALOGUE, CATc.REAC_BOX_CATALOGUE_FRAME,
    CATc.BOX_CATALOGUE in HCAT.
  eapply evt_cut.
  { eapply HCAT with (c := fr + 32) (lo := lo).
    - reflexivity.
    - rewrite MState.unsigned_lit by lia. exact ST2'.
    - rewrite MState.unsigned_lit by lia. lia.
    - exact HAC2.
    - exact HSW2.
    - intros x Hx. rewrite MState.unsigned_lit by lia. cbn [outside].
      unfold GOT_CELL_K, CELL_K in Hx.
      split; [|split; [|exact I]].
      + destruct Hx as [Hx|[Hx|Hx]]; [lia | lia |].
        pose proof (in_shadow_range x Hx). intros Hc.
        apply (app_not_shadow x); [|exact Hx]. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
      + destruct Hx as [Hx|[Hx|Hx]]; [lia | lia |].
        intros Hc. exact (app_not_shadow x (Hc8 x ltac:(lia)) Hx).
    - right. split; [Z.div_mod_to_equations; lia|].
      split; [exact WR82|].
      split; [rewrite MState.unsigned_lit by lia; lia | exact HADR]. }
  intros ms' (a1' & a2' & m3 & Ems & MU3 & WM3 & MI3 & ST3 & HCb).
  subst ms'.
  rewrite MState.unsigned_lit in MU3, ST3 by lia.
  replace (fr + 32 =? 0) with false in HCb by (symmetry; apply Z.eqb_neq; lia).
  match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] =>
      replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z)
        by (symmetry; apply ret_pc_even; [clear; lia | reflexivity])
  end.
  (* compose the two write sets *)
  assert (MUall : munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (spv - 16, spv)] m m3).
  { apply (munch_trans _ m m2 m3 MU2).
    apply (munch_weaken [(spv - 16, spv); (fr + 32, fr + 32 + 8)]); [|exact MU3].
    intros x Hx. cbn [outside] in Hx |- *. split; [lia|]. split; [lia | exact I]. }
  assert (WMall : wmono rsegs m m3) by (apply (wmono_trans rsegs m m2 m3 WM2 WM3)).
  assert (HmrdW3 : forall x, 0 <= x < 2 ^ 64 ->
            ~ (Sfr fr + 4 <= x < Sfr fr + 5) -> ~ (fr + 32 <= x < fr + 40) -> ~ (spv - 16 <= x < spv) ->
            mrd rsegs m3 (wa x) = mrd rsegs m (wa x)).
  { intros x Hx H1 H2 H3. apply (f32_mrd_munch _ m m3 x MUall Hx).
    cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  apply evt_done. cbv beta.
  eexists _, _, _, m3. split; [reflexivity|].
  split; [exact MUall|]. split; [exact WMall|].
  split; [exact ST3|].
  split; [exact HCb|].
  split.
  { intros a Hin. destruct (Z.eq_dec a (Sfr fr + 4)) as [->|Hne].
    - destruct (in_shadow_range (Sfr fr + 4) Hin) as (Hr0 & Hr1).
      assert (Hb : exists b, mrd rsegs m2 (wa (Sfr fr + 4)) = Some b).
      { exists (Z_to_bv 8 0). destruct HB2 as (_ & _ & HB2b). pose proof (HB2b 0%nat ltac:(cbn; lia)) as HH.
        cbn [Z.of_nat nth_error] in HH. rewrite Z.add_0_r in HH. exact HH. }
      destruct Hb as (b & Hb). exists b.
      rewrite (f32_mrd_munch _ m2 m3 (Sfr fr + 4) MU3); [exact Hb | lia |].
      cbn [outside]. split; [|split; [|exact I]].
      + intros Hc. apply (app_not_shadow (Sfr fr + 4)); [|exact Hin].
        unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
      + intros Hc. assert (Hc' : fr + 32 <= Sfr fr + 4 < fr + 40) by lia.
        exact (app_not_shadow (Sfr fr + 4) (Hc8 _ Hc') Hin).
    - destruct (HSW a Hin) as (_ & b & Hb). exists b.
      rewrite HmrdW3; [exact Hb | | lia | |].
      + pose proof (in_shadow_range a Hin). lia.
      + intros Hc. exact (app_not_shadow a (Hc8 a Hc) Hin).
      + intros Hc. apply (app_not_shadow a); [|exact Hin].
        unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
  { intros bs Hbs Hl. change (Z.to_nat FRAME_SHADOW) with 392%nat in Hl |- *.
    exists (upd_bytes bs 4 [Z_to_bv 8 0]).
    split; [|rewrite upd_bytes_length; [exact Hl | cbn [length]; lia]].
    assert (Hin1 : bytes_at rsegs m1 (Sfr fr) (upd_bytes bs 4 [Z_to_bv 8 0])).
    { unfold m1. replace (Sfr fr + 4) with (Sfr fr + 4) by lia.
      apply (bytes_at_write_inside rsegs m (Sfr fr) bs 4 [Z_to_bv 8 0] Hbs); [lia | cbn [length]; lia]. }
    assert (Hlen' : length (upd_bytes bs 4 [Z_to_bv 8 0]) = 392%nat)
      by (rewrite upd_bytes_length; [exact Hl | cbn [length]; lia]).
    assert (Hin2 : bytes_at rsegs m2 (Sfr fr) (upd_bytes bs 4 [Z_to_bv 8 0])).
    { unfold m2. apply (bytes_at_write_other rsegs m1 (fr + 32) (le8 (Z_to_bv 64 0)));
        [exact Hin1 | lia | rewrite length_le8; lia |
         rewrite Hlen', length_le8;
         pose proof (f32_frsh_shadow fr (Sfr fr) Happ ltac:(lia)) as Hs0;
         pose proof (f32_frsh_shadow fr (Sfr fr + 391) Happ ltac:(lia)) as Hs1;
         unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
           APPMEM_END in Hs0, Hs1, Hcapp |- *; lia]. }
    eapply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 32, fr + 32 + 8)] m2 m3);
      [exact Hin2 | exact MU3 |].
    rewrite Hlen'. cbn [disjoint_from].
    pose proof (f32_frsh_shadow fr (Sfr fr) Happ ltac:(lia)) as Hs0.
    pose proof (f32_frsh_shadow fr (Sfr fr + 391) Happ ltac:(lia)) as Hs1.
    unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END
      in Hs0, Hs1, Hcapp |- *.
    split; [lia|]. split; [lia | exact I]. }
Qed.

(* The word at an address is unique: two values that read as the same 8 bytes are equal. *)
Lemma f32_word_mem_det : forall m a v1 v2, 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 W1 W2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (W1 k Hk) as E1. pose proof (W2 k Hk) as E2.
    assert (Eb : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal bv_unsigned) in Eb. rewrite !kb_byte_unsigned in Eb. exact Eb. }
  rewrite (kb_le8_digits v1 H1), (kb_le8_digits v2 H2).
  rewrite !Hb by lia. reflexivity.
Qed.

(* bytes_at sub-range. *)
Lemma f32_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
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

(* A spilled word at s1 + off read at the FRA spill base A (the existential base of `spill` is A). *)
Lemma f32_spill : forall regs m off v A, spill regs m off v -> rg regs 9 A ->
  0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  unfold rg in HA, HA'. rewrite HA in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1.
  assert (E : A' = A).
  { apply (f_equal bv_unsigned) in HA'. rewrite !unsigned_lit_wrap in HA'.
    rewrite (Z.mod_small A) in HA' by lia. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* bytes_at moves to a memory that agrees with the old one on the bytes' own range. *)
Lemma f32_ba_eq : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mrd rsegs m' (wa x) = mrd rsegs m (wa x)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [lia|]. split; [lia|].
  intros i Hi. exact (eq_trans (HK (a + Z.of_nat i) ltac:(lia)) (H i Hi)).
Qed.

(* IFS moves to a memory that keeps the two frame records [fr + 2688, fr + 2840) and the local `first`
   [fr + 2880, fr + 2920) byte for byte, and keeps `first` addressable (v1.9.0: FSb is `first`, not spills). *)
Lemma f32_IFS_tr : forall g fr j regs regs' m m',
  IFS g fr j regs m ->
  (forall x, fr + 2688 <= x < fr + 2920 -> mrd rsegs m' (wa x) = mrd rsegs m (wa x)) ->
  (addressable m (fr + 2880) 40 -> addressable m' (fr + 2880) 40) ->
  IFS g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' HIFS HK HA.
  pose proof HIFS as (_ & _ & _ & _ & _ & Hfst & _).
  apply (Tac_ro.ifs_keep g fr j regs regs' m m' HIFS).
  - intros HID. apply (f32_ba_eq _ _ _ _ HID). rewrite Tac_ro.tr_ID_length. intros x Hx. apply HK. lia.
  - intros HFG. apply (f32_ba_eq _ _ _ _ HFG). rewrite Tac_ro.tr_FG_length. intros x Hx. apply HK. lia.
  - intros a bs Ha Hl Hb. apply (f32_ba_eq _ _ _ _ Hb). intros x Hx. apply HK. lia.
  - exact (HA Hfst).
Qed.

Section F32.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* reac_box_catalogue (0x84dec): the function returns the catalogue's base 0x9f620 and writes the count 11 to the
   8 bytes at its argument; it writes only those bytes and its own 16 stack bytes below sp. *)
Hypothesis HCAT : CATc.reac_box_catalogue_contract.

(* The one place of this file that uses the lazy-model bridge (AsanLift.evt_SR_canon_lazy): the runs of this
   segment are Lib.Exec runs, because the reac_box_catalogue contract is stated with Lib.Exec.evt. *)
Lemma f32_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* A live block ends below stklo and none of its bytes is in the side stack: the two facts of SlotInv's lw_blocks
   (Contract.a_laws_blocks) this file reads, with lwb_byte's per-byte list taken apart once here. *)
Lemma f32_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ _ Hle _ Hall].
  split; [exact Hle|]. intros a Ha. destruct (Hall a Ha) as (_ & _ & _ & _ & Hnfs). exact Hnfs.
Qed.

(* The allocator's heap invariant, the runtime's owned set and the two stack bounds survive this segment's writes:
   the frame variable [fr+32, fr+40) and its shadow byte are the frame's own bytes (the real-stack arm: inside
   [stklo, APPMEM_END); the side-stack arm: inside the side stack, so the FakeStack law applies), and the callee's
   window [sp-16, sp) lies in the slot's stack window, which is above stklo in both arms. The owned set and stkhi
   are what Tac_slot's ent_store asks for. *)
Lemma f32_ah_move : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md ->
  munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (AC.aspZ regs - 16, AC.aspZ regs)] mem mem' ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  (forall a, 0 <= a < 2 ^ 64 -> (exists b, mbyte rsegs mem a = Some b) ->
     (exists b, mbyte rsegs mem' a = Some b)) ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> AC.GT <= fr ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr hb regs mem mem' md HFRA MU HWM HMB Happ HGT.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Hspz : AC.aspZ regs = sp) by exact Haspz.
  assert (Hcapp : app_mem (fr + 32)) by (apply Happ; lia).
  assert (Hshc : shadow_addr (fr + 32) = Sfr fr + 4)
    by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
  assert (HstkW : forall x, sp - 16 <= x < sp ->
                    AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END) by (intros x Hx; lia).
  destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5fr [Hfsb [Hfs Hrec]]]].
  - (* the real-stack arm: the frame is the function's own stack frame, above stklo *)
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
      cbn [outside]. split; [|split; [|split; [|exact I]]].
      - intros Hc. apply Hns. unfold AC.a_store_ok. right; right; right.
        exists (fr + 32). split; [rewrite Hshc; lia|]. right; left. exact (Hreal (fr + 32) ltac:(lia)).
      - intros Hc. apply Hns. unfold AC.a_store_ok. right; left. exact (Hreal a ltac:(lia)).
      - intros Hc. apply Hns. unfold AC.a_store_ok. right; left. rewrite Hspz in Hc. exact (HstkW a Hc). }
    destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH HstoreC HWM)
      as [HAH' Hown' HSTKeq HSTKHIeq].
    split; [exact HAH'|]. split; [exact Hown'|]. split; [exact HSTKeq | exact HSTKHIeq].
  - (* the side-stack arm: the frame is a fake frame on the runtime's side stack for frames *)
    destruct (Hfs (fr + 32) ltac:(lia)) as (FS & HFSr & HFSw & HFSlo & HFShi).
    destruct (lw_fs_place (APIf rc) (hb ++ g_H g) mem md FS HAH HFSw HFSr)
      as [HGTfs HFSstk HFSmod HFSapp].
    assert (HFSfr : FS + 6328320 <= fr) by (apply (Hfsb FS HFSw HFSr)).
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FS <= a < FS + AC.FS_SIZE) ->
      ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by lia.
      cbn [outside]. split; [|split; [|split; [|exact I]]].
      - intros Hc. apply Hnsh. exists (fr + 32). split; [lia|]. rewrite Hshc. lia.
      - intros Hc. apply Hnf. destruct (Hfs a ltac:(lia)) as (FS' & HFSr' & HFSw' & HFSlo' & HFShi').
        assert (FS' = FS)
          by exact (f32_word_mem_det mem (AC.as_tp AC.ASYMS) FS' FS HFSr' HFSr HFSw' HFSw).
        subst FS'. lia.
      - intros Hc. apply Hns. unfold AC.a_store_ok. right; left. rewrite Hspz in Hc. exact (HstkW a Hc). }
    assert (Hmeta : forall q, fs_meta FS q -> outside [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40);
                                                       (AC.aspZ regs - 16, AC.aspZ regs)] q).
    { intros q Hq. pose proof (fs_meta_below FS q Hq) as Hqlo.
      assert (HqFS : FS <= q).
      { unfold fs_meta in Hq.
        destruct Hq as [Hq | [Hq | [ (cc & Hcc & Hr) | (cc & jj & Hcc & Hjj & Heq) ]]];
          [lia | lia | unfold AC.a_fs_hint in Hr; lia |
           subst q; pose proof (a_fs_flag_range FS cc jj Hcc Hjj); lia]. }
      cbn [outside]. split; [|split; [|split; [|exact I]]].
      - intros Hc. apply (app_not_shadow q (HFSapp q ltac:(unfold AC.FS_SIZE; lia))).
        assert (Hq4 : q = Sfr fr + 4) by lia. rewrite Hq4, <- Hshc. apply shadow_of_app. exact Hcapp.
      - lia.
      - rewrite Hspz. unfold AC.FS_SIZE in *. lia. }
    assert (HFS64 : FS + AC.FS_SIZE <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
    destruct (a_fs_ok_store_AH _ _ _ _ _ _ (hb ++ g_H g) mem mem' md FS LAWS HAH HFSw HFSr HFS64 MU HWM HMB
                Hmeta HstoreC)
      as (HAH' & Hown' & HSTKeq & HSTKHIeq).
    split; [exact HAH'|]. split; [exact Hown'|]. split; [exact HSTKeq | exact HSTKHIeq].
Qed.

(* FRA moves across this segment's writes. Tac_slot's sl_fr_meta allows only the frame body and the frame's 392
   shadow bytes; this segment also writes the callee's 16 stack bytes below sp, so the window is a premise (as in
   F31's f31_stk_run) and the "kept" premise excludes [sp-16, sp) too. The side arm's frame record FSREC moves by
   Tac_slot's fsrec_keep_app_lo (every app byte the run writes outside the frame is in [sp-16, sp), above stklo);
   the slot window outside the frame stays addressable byte by byte (its shadow bytes are outside the frame's 392,
   so outside W by the "kept" premise). *)
Lemma f32_fra_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> AC.GT <= fr ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  HIGHMEM_BEG + 16 <= AC.aspZ regs ->
  (fr + FRAME_BYTES <= AC.aspZ regs - 16 \/ AC.aspZ regs <= fr) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (fr + 24 <= x < fr + FRAME_BYTES) -> ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) ->
     ~ (AC.aspZ regs - 16 <= x < AC.aspZ regs) -> outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> forall x, A + 336 <= x < A + 344 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> forall x, A + 40 <= x < A + 56 -> outside W x) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK Happ Hgt Hshnew HWIN' HAG' HshR
    Hsphi Hfrsp HWkept HWspill HWsaved HWsel E2 E3 E4 E8 E9 E19 E26.
  unfold AC.GT in Hgt. unfold HIGHMEM_BEG in Hsphi.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (Hub : fr + FRAME_BYTES <= 140737488355328).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. destruct Ha as [Ha|Ha]; lia. }
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x)
    by (intros x Hx; exact (f32_frsh_shadow fr x Happ Hx)).
  assert (KBout : forall x, app_mem x -> ~ (fr + 24 <= x < fr + FRAME_BYTES) ->
                    ~ (AC.aspZ regs - 16 <= x < AC.aspZ regs) -> outside W x).
  { intros x Hap Hnb Hns. apply HWkept.
    - unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hap; destruct Hap; lia.
    - exact Hnb.
    - intro Hin380. exact (app_not_shadow x Hap (HshIS x Hin380)).
    - exact Hns. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1.
    assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by (unfold APPMEM_END in *; lia).
      apply KBout; [unfold app_mem, LOWMEM_END; left; lia | lia | rewrite Haspz; lia]. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - pose proof (f32_RELRO_bound a Hin). lia.
    - pose proof (f32_RELRO_bound a Hin). lia. }
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
    rewrite length_le8. intros x Hx. exact (HWspill A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr40 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + eapply fsrec_keep_app_lo with (W := W); [exact Hrec | exact HAH | exact MU |].
        intros x Hap Hlo Hnf. apply KBout; [exact Hap | lia | lia]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply KBout; [apply Happ; lia | lia | rewrite Haspz; lia]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply KBout; [apply Happ; lia | lia | rewrite Haspz; lia]. }
  split; [exact Hshnew|].
  split; [exact HWIN'|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split.
  { intros a H1 H2. pose proof (HWA a H1 H2) as Ha1. pose proof Ha1 as (Ha0 & _).
    apply (addr1_munch W mem mem' a MU); [|exact Ha1].
    pose proof (shadow_of_app a (addr1_app mem a Ha1)) as His.
    pose proof (in_shadow_range _ His) as Hr.
    apply HWkept; [lia | | |].
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [apply Happ; lia | exact His].
    - intros Hc. apply H2. exact (f32_sh_frame fr a Hfrm Ha0 Hc).
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact His].
      unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. unfold APPMEM_END in HAPP. lia. }
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  (* the input block: app memory below stklo (so below the callee's window [sp-16, sp)) and apart from the frame
     (fra_in_apart); its shadow bytes are shadow bytes of no frame byte *)
  apply (fra_in_keep_sh g mem mem' W Hinb Hinblk MU).
  intros x Hx. destruct (Hinap x Hx) as (Hxa & Hxlo & Hxf & _).
  assert (Hx0 : 0 <= x < APPMEM_END)
    by (unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hxa |- *; lia).
  pose proof (shadow_of_app x Hxa) as Hxs.
  pose proof (in_shadow_range _ Hxs) as Hxr.
  unfold FN_STACK in Hwlo.
  split.
  - apply HWkept; [unfold APPMEM_END in Hx0; lia | lia | |].
    + intros Hc. exact (app_not_shadow x Hxa (HshIS x Hc)).
    + lia.
  - apply HWkept; [lia | | |].
    + intros Hc. apply (app_not_shadow (shadow_addr x)); [apply Happ; lia | exact Hxs].
    + intros Hc. exact (Hxf (f32_sh_frame fr x Hfrm ltac:(lia) Hc)).
    + intros Hc. apply (app_not_shadow (shadow_addr x)); [|exact Hxs].
      unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. unfold APPMEM_END in HAPP. lia.
Qed.

(* ===================== the cut states ===================== *)

(* Phi is not a side-stack byte: the cut's live block (Phi, a_size len) has at least one byte, and no live block
   byte is in the side stack (Contract.a_laws_blocks). *)
Lemma f32_notfs : forall g fr phi len regs mem md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size len)) regs mem md -> ~ AC.a_in_fs AC.ASYMS mem phi.
Proof.
  intros g fr phi len regs mem md HFRA.
  destruct HFRA as (A & sp & s5 & HRT & HAH & _).
  assert (Hin : In (phi, AC.a_size len) (hb1 phi (AC.a_size len) ++ g_H g))
    by (apply in_or_app; left; unfold hb1; left; reflexivity).
  destruct (f32_blocks _ mem md phi (AC.a_size len) HAH Hin) as (_ & Hnfs).
  exact (Hnfs phi ltac:(unfold AC.a_size; pose proof (Z.le_max_r len 1); lia)).
Qed.

(* A stack range stays a stack range when every byte of it is still readable. *)
Lemma f32_stk_keep : forall mem mem' lo hi,
  stk rsegs mem lo hi -> wmono rsegs mem mem' ->
  (forall x, lo <= x < hi -> exists b, mrd rsegs mem' (wa x) = Some b) -> stk rsegs mem' lo hi.
Proof.
  intros mem mem' lo hi (H0 & H1 & H) WM HM.
  split; [exact H0|]. split; [exact H1|].
  intros a Ha. split; [apply WM, (proj1 (H a Ha)) | exact (HM a Ha)].
Qed.

(* The exit cut at 0x82c90 (official Inv_B82c90_at) from the entry state: no memory is written on the three mismatch
   paths, which write a0 / a1 only. *)
Lemma f32_c2c_cut : forall g j phi fr regs regs' mem md md',
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md ->
  AsanLift.mat_le md md' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 24 = getr regs 24 ->
  getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
  getr regs' 25 = getr regs 25 -> getr regs' 22 = getr regs 22 ->
  g_n g < 2 ^ 26 -> (j <= 255)%nat -> HB mem phi (flen g j) -> LK g fr j regs mem ->
  PT32 g j phi fr regs mem -> t_want_m (g_in g) j = 0 ->
  FTK g j fr regs mem -> FTURN g j phi regs mem -> IFS g fr (S j) regs mem ->
  Inv_B82c90_at B APIf ra g j (mkCfg (mkst regs' (Z_to_bv 64 0x82c90) mem (seg_rom rsegs)) md').
Proof.
  intros g j phi fr regs regs' mem md md' HFRA HENT Hmat E2 E3 E4 E8 E9 E18 E19 E20 E24 E26 E27 E25 E22
    Hgn Hj HHB HLK HPT Hwm HFTK HFT HIFS.
  pose proof (proj1 FF) as SEGS.
  pose proof (f32_notfs g fr phi (flen g j) regs mem md HFRA) as HNFS.
  pose proof HPT as (Hr18 & Hr24 & Hr20 & Hs152 & Hs312 & Hphi & Hplen & Hs160 & Hfstk).
  pose proof HLK as (Hj255 & Hs240 & HOUR & HFLI).
  pose proof HFTK as (Hs184 & Hr22 & _ & Hs272 & Hr25).
  pose proof HFT as (Hs224 & Hs232 & Hphi' & Hplen').
  assert (Hsp9 : forall off v, spill regs mem off v -> spill regs' mem off v).
  { intros off v (A' & HA' & Hq). exists A'. split; [|exact Hq]. unfold rg in *. rewrite E9. exact HA'. }
  exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
  split.
  { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem md md' HFRA);
      assumption. }
  split; [eapply ent_mat; [exact HENT | exact Hmat]|].
  split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
  split.
  { pose proof (Tac_ro.fli_mem g fr regs mem HFLI) as (Fad & Fstk & Frad & Ffrg & Fknt & Ffst).
    eapply Tac_ro.lk_keep;
      [exact HLK | | exact Fad | exact Fstk | exact Frad | exact Ffrg | exact Fknt | exact Ffst | exact HOUR |].
    - unfold rg in *. rewrite E27. exact (proj1 HFLI).
    - intros off v _ Hs. exact (Hsp9 off v Hs). }
  split; [exact Hwm|].
  split; [exact HNFS|].
  split.
  { split; [unfold rg in *; rewrite E18; exact Hr18|].
    split; [unfold rg in *; rewrite E24; exact Hr24|].
    split; [unfold rg in *; rewrite E20; exact Hr20|].
    split; [apply Hsp9; exact Hs152|].
    split; [apply Hsp9; exact Hs312|].
    split; [exact Hphi|]. split; [exact Hplen|].
    split; [apply Hsp9; exact Hs160|].
    exact Hfstk. }
  split.
  { split; [apply Hsp9; exact Hs184|].
    split; [unfold rg in *; rewrite E22; exact Hr22|].
    split; [unfold rg in *; rewrite E24; exact Hr24|].
    split; [apply Hsp9; exact Hs272 | unfold rg in *; rewrite E25; exact Hr25]. }
  split.
  { split; [apply Hsp9; exact Hs224|]. split; [apply Hsp9; exact Hs232|].
    split; [exact Hphi' | exact Hplen']. }
  exact (f32_IFS_tr g fr (S j) regs regs' mem mem HIFS (fun x _ => eq_refl) (fun X => X)).
Qed.

(* ===================== the segment lemmas ===================== *)

(* 0x82b5c (F31's second exit, the classify = None arm) is inside this segment's range, so this file discharges it
   too: from 0x82b5c the run reaches either 0x82c90 (k <> 9, or the type bytes are not cd ea) or 0x82bcc (through
   reac_box_catalogue). *)
Lemma seg_F32_af8 : forall j,
  Hat B APIf ra (Inv_B82bcc_at B APIf ra) j -> Hat B APIf ra (Inv_B82c90_at B APIf ra) j ->
  Hat B APIf ra (Inv_B82b5c_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j H68 Hc2c g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & HFTK & HPT & HFT &
                    HIFS).
  subst c. rewrite SEGS.
  pose proof HPT as (Hr18 & Hr24 & Hr20 & Hs152 & Hs312 & Hphi & Hplen & Hs160 & Hfstk).
  pose proof HLK as (Hj255 & Hs240 & HOUR & HFLI).
  destruct (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGT & Hfapp).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)
    as Hstkhi.
  destruct (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hdisj & _ & _ & _).
  assert (HSb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof (f32_k_range (g_in g) j) as Hkr.
  destruct (Z.eq_dec (t_k (g_in g) j) 9) as [Ek|Ek]; [|].
  2: { (* k <> 9: `bne s8,a0` at 0x82b60 is taken to 0x82c90 *)
    assert (Hwm : t_want_m (g_in g) j = 0).
    { unfold t_want_m, t_rowsel. replace (t_k (g_in g) j =? 9) with false
        by (symmetry; apply Z.eqb_neq; exact Ek). reflexivity. }
    apply (f32_run_lib regs (Z_to_bv 64 0x82b5c) mem md
      (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82c90 /\ mem' = mem /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
         getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 24 = getr regs 24 /\
         getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
         getr R0 25 = getr regs 25 /\ getr R0 22 = getr regs 22)
      (Post B APIf ra g)).
    - exact Hhalt.
    - eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of. apply (f32n_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ mem (t_k (g_in g) j)); [unfold rg in Hr24; exact Hr24 | lia | exact Ek]. }
      { intros ms' E. eexists _, _, _. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|].
        repeat split;
          first [ reflexivity
                | unfold rg in *; symmetry;
                  first [ exact Hr2 | exact Hr9 | exact Hr18 | exact Hr19 | exact Hr20 | exact Hr26
                        | exact Hr24 ] ]. }
    - intros R0 pc' mem' regs' md'
        (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E24 & E26 & E27 & E25 & E22) Hreg Hmat.
      subst pc' mem'.
      pose proof (f32_c2c_cut g j phi fr regs regs' mem md md' HFRA HENT Hmat
        ltac:(rewrite Hreg; exact E2) ltac:(rewrite Hreg; exact E3) ltac:(rewrite Hreg; exact E4)
        ltac:(rewrite Hreg; exact E8) ltac:(rewrite Hreg; exact E9) ltac:(rewrite Hreg; exact E18)
        ltac:(rewrite Hreg; exact E19) ltac:(rewrite Hreg; exact E20) ltac:(rewrite Hreg; exact E24)
        ltac:(rewrite Hreg; exact E26) ltac:(rewrite Hreg; exact E27) ltac:(rewrite Hreg; exact E25)
        ltac:(rewrite Hreg; exact E22) Hgn Hj HHB HLK HPT Hwm HFTK HFT HIFS) as HIexit.
      pose proof (Hc2c g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR. }
  (* k = 9: the frame is at least 50 bytes long and the two type bytes are read *)
  assert (Hlen50 : 50 <= flen g j) by (unfold flen; apply f32_k9_len; exact Ek).
  assert (Hr24k : getr regs 24 = Z_to_bv 64 9) by (unfold rg in Hr24; rewrite Hr24, Ek; reflexivity).
  pose proof HHB as (Hphi0 & HAd).
  pose proof HAd as (Hp0 & _ & Hpe & _). unfold AC.a_size in Hpe. rewrite Z.max_l in Hpe by lia.
  assert (Hphipos : 0 < phi) by lia.
  assert (Hphi50 : phi + 50 <= APPMEM_END) by lia.
  pose proof (f32_sh mem phi (flen g j) 16 HAd ltac:(lia) ltac:(lia)) as Hsh16.
  pose proof (f32_sh mem phi (flen g j) 17 HAd ltac:(lia) ltac:(lia)) as Hsh17.
  assert (Hplen' : Z.of_nat (length (t_phi (g_in g) j)) = flen g j)
    by (unfold flen; apply f32_phi_len).
  assert (Hgt : t_g (g_in g) j = firstn 50 (t_phi (g_in g) j))
    by (apply f32_tg; unfold flen in Hlen50; exact Hlen50).
  assert (Hb16 : bytes_at rsegs mem (phi + 16) [RP.cp_b (t_g (g_in g) j) 16]).
  { pose proof (f32_ba_sub mem phi (t_phi (g_in g) j) 16 1 Hphi ltac:(lia)) as H16.
    rewrite (f32_fs1 (t_phi (g_in g) j) 16) in H16 by lia.
    replace (phi + Z.of_nat 16) with (phi + 16) in H16 by lia.
    unfold RP.cp_b. rewrite Hgt, f32_nth_firstn by lia. exact H16. }
  assert (Hb17 : bytes_at rsegs mem (phi + 17) [RP.cp_b (t_g (g_in g) j) 17]).
  { pose proof (f32_ba_sub mem phi (t_phi (g_in g) j) 17 1 Hphi ltac:(lia)) as H17.
    rewrite (f32_fs1 (t_phi (g_in g) j) 17) in H17 by lia.
    replace (phi + Z.of_nat 17) with (phi + 17) in H17 by lia.
    unfold RP.cp_b. rewrite Hgt, f32_nth_firstn by lia. exact H17. }
  destruct (Z.eq_dec (RP.cp_v (t_g (g_in g) j) 16) 205) as [E16|E16]; [|].
  2: { (* Phi[16] <> 0xcd: `bne a0,a1` at 0x82b8c is taken to 0x82c90 *)
    assert (Hwm : t_want_m (g_in g) j = 0).
    { unfold t_want_m, t_rowsel. replace (RP.cp_v (t_g (g_in g) j) 16 =? 205) with false
        by (symmetry; apply Z.eqb_neq; exact E16).
      rewrite andb_false_r. reflexivity. }
    apply (f32_run_lib regs (Z_to_bv 64 0x82b5c) mem md
      (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82c90 /\ mem' = mem /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
         getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 24 = getr regs 24 /\
         getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
         getr R0 25 = getr regs 25 /\ getr R0 22 = getr regs 22)
      (Post B APIf ra g)).
    - exact Hhalt.
    - eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of.
        apply (f32m1_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ mem phi (RP.cp_b (t_g (g_in g) j) 16));
          [ unfold rg in Hr18; exact Hr18
          | exact Hr24k
          | unfold rg in Hr26; exact Hr26
          | lia | lia | exact Hsh16 | exact Hb16 | unfold RP.cp_v in E16; exact E16 ]. }
      { intros ms' E. eexists _, _, _. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|].
        repeat split;
          first [ reflexivity
                | unfold rg in *; symmetry;
                  first [ exact Hr2 | exact Hr9 | exact Hr18 | exact Hr19 | exact Hr20 | exact Hr26
                        | exact Hr24 | exact Hr24k ] ]. }
    - intros R0 pc' mem' regs' md'
        (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E24 & E26 & E27 & E25 & E22) Hreg Hmat.
      subst pc' mem'.
      pose proof (f32_c2c_cut g j phi fr regs regs' mem md md' HFRA HENT Hmat
        ltac:(rewrite Hreg; exact E2) ltac:(rewrite Hreg; exact E3) ltac:(rewrite Hreg; exact E4)
        ltac:(rewrite Hreg; exact E8) ltac:(rewrite Hreg; exact E9) ltac:(rewrite Hreg; exact E18)
        ltac:(rewrite Hreg; exact E19) ltac:(rewrite Hreg; exact E20) ltac:(rewrite Hreg; exact E24)
        ltac:(rewrite Hreg; exact E26) ltac:(rewrite Hreg; exact E27) ltac:(rewrite Hreg; exact E25)
        ltac:(rewrite Hreg; exact E22) Hgn Hj HHB HLK HPT Hwm HFTK HFT HIFS) as HIexit.
      pose proof (Hc2c g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR. }
  assert (Eb16 : RP.cp_b (t_g (g_in g) j) 16 = Z_to_bv 8 205)
    by (apply (f32_cp_b _ 16 205 E16); lia).
  destruct (Z.eq_dec (RP.cp_v (t_g (g_in g) j) 17) 234) as [E17|E17]; [|].
  2: { (* Phi[17] <> 0xea: `bne a0,a1` at 0x82bb4 is taken to 0x82c90 *)
    assert (Hwm : t_want_m (g_in g) j = 0).
    { unfold t_want_m, t_rowsel. replace (RP.cp_v (t_g (g_in g) j) 17 =? 234) with false
        by (symmetry; apply Z.eqb_neq; exact E17).
      rewrite andb_false_r. reflexivity. }
    apply (f32_run_lib regs (Z_to_bv 64 0x82b5c) mem md
      (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82c90 /\ mem' = mem /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
         getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 24 = getr regs 24 /\
         getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
         getr R0 25 = getr regs 25 /\ getr R0 22 = getr regs 22)
      (Post B APIf ra g)).
    - exact Hhalt.
    - eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of.
        apply (f32m2_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ mem phi (RP.cp_b (t_g (g_in g) j) 17));
          [ unfold rg in Hr18; exact Hr18
          | exact Hr24k
          | unfold rg in Hr26; exact Hr26
          | lia | lia | exact Hsh16 | rewrite <- Eb16; exact Hb16 | exact Hsh17 | exact Hb17
          | unfold RP.cp_v in E17; exact E17 ]. }
      { intros ms' E. eexists _, _, _. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|].
        repeat split;
          first [ reflexivity
                | unfold rg in *; symmetry;
                  first [ exact Hr2 | exact Hr9 | exact Hr18 | exact Hr19 | exact Hr20 | exact Hr26
                        | exact Hr24 | exact Hr24k ] ]. }
    - intros R0 pc' mem' regs' md'
        (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E24 & E26 & E27 & E25 & E22) Hreg Hmat.
      subst pc' mem'.
      pose proof (f32_c2c_cut g j phi fr regs regs' mem md md' HFRA HENT Hmat
        ltac:(rewrite Hreg; exact E2) ltac:(rewrite Hreg; exact E3) ltac:(rewrite Hreg; exact E4)
        ltac:(rewrite Hreg; exact E8) ltac:(rewrite Hreg; exact E9) ltac:(rewrite Hreg; exact E18)
        ltac:(rewrite Hreg; exact E19) ltac:(rewrite Hreg; exact E20) ltac:(rewrite Hreg; exact E24)
        ltac:(rewrite Hreg; exact E26) ltac:(rewrite Hreg; exact E27) ltac:(rewrite Hreg; exact E25)
        ltac:(rewrite Hreg; exact E22) Hgn Hj HHB HLK HPT Hwm HFTK HFT HIFS) as HIexit.
      pose proof (Hc2c g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR. }
  (* k = 9, Phi[16] = 0xcd, Phi[17] = 0xea: the catalogue runs and the row loop is entered at 0x82bcc *)
  assert (Eb17 : RP.cp_b (t_g (g_in g) j) 17 = Z_to_bv 8 234)
    by (apply (f32_cp_b _ 17 234 E17); lia).
  assert (Hrow : t_rowsel (g_in g) j = true).
  { unfold t_rowsel. rewrite Ek, E16, E17. reflexivity. }
  assert (Hbig : t_big (g_in g) j = true)
    by (unfold t_big; apply Z.leb_le; unfold flen in Hlen50; exact Hlen50).
  assert (Hs312' : spill regs mem 312 (phi + 18)) by (rewrite Hbig in Hs312; exact Hs312).
  (* the frame's bytes and the stack window *)
  assert (HGTz : 6283264 <= fr) by (unfold AC.GT in HGT; lia).
  assert (Hfrb : fr + FRAME_BYTES <= 140737488355328).
  { pose proof (Hfapp (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. lia. }
  assert (Hlo16 : g_S g - AF.SLOT_STACK + 16 <= sp) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hhilo : HIGHMEM_BEG <= g_S g - AF.SLOT_STACK) by lia.
  assert (HspE : sp <= APPMEM_END) by lia.
  destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin ltac:(lia)) as (HSlo & HShi).
  assert (HdisjK : fr + FRAME_BYTES <= sp - 16 \/ sp <= fr).
  { destruct (Hdisj 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [HD|HD];
      [left | right]; rewrite Haspz in HD; lia. }
  assert (HWR8 : wr_at rsegs mem (fr + 32) 8).
  { destruct Hfstk as (Hf0 & Hf1 & Hf). split; [lia|]. split; [lia|].
    intros i Hi. exact (proj1 (Hf (fr + 32 + i) ltac:(lia))). }
  assert (Hshc : shadow_addr (fr + 32) = Sfr fr + 4)
    by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
  assert (HshIS4 : in_shadow (Sfr fr + 4))
    by (rewrite <- Hshc; apply shadow_of_app; apply Hfapp; lia).
  assert (HWR1 : wr_at rsegs mem (Sfr fr + 4) 1).
  { pose proof (AsanRTInv.RT_shadow_rw sp mem md HRT (Sfr fr + 4) HshIS4) as (Hw & _).
    pose proof (in_shadow_range _ HshIS4) as Hr.
    split; [lia|]. split; [lia|]. intros i Hi. replace (Sfr fr + 4 + i) with (Sfr fr + 4) by lia. exact Hw. }
  assert (Q160 : q64 mem (A + 160) (fr + 32)) by (apply (f32_spill regs mem 160 _ A Hs160 Hr9); lia).
  assert (Hasz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
  apply (f32_run_lib regs (Z_to_bv 64 0x82b5c) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82bcc /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 24 = getr regs 24 /\
       getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
       getr R0 25 = getr regs 25 /\ getr R0 22 = getr regs 22 /\
       getr R0 10 = Z_to_bv 64 CATc.BOX_CATALOGUE /\
       getr R0 23 = Z_to_bv 64 (fr + 32) /\
       munch [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (sp - 16, sp)] mem mem' /\
       wmono rsegs mem mem' /\ stk rsegs mem' (g_S g - AF.SLOT_STACK) sp /\
       bytes_at rsegs mem' (fr + 32) (le8 (Z_to_bv 64 11)) /\
       (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) /\
       (forall bs, bytes_at rsegs mem (Sfr fr) bs -> length bs = Z.to_nat FRAME_SHADOW ->
          exists bs', bytes_at rsegs mem' (Sfr fr) bs' /\ length bs' = Z.to_nat FRAME_SHADOW))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      apply (f32c_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ mem A fr phi (g_S g - AF.SLOT_STACK) sp HCAT);
        [ unfold rg in Hr9; exact Hr9
        | unfold rg in Hr18; exact Hr18
        | unfold rg in Hr19; exact Hr19
        | exact Hr24k
        | unfold rg in Hr26; exact Hr26
        | exact Hr2
        | lia | lia | lia | lia | exact HGT | exact Hfrm | exact Hfapp
        | exact Hhilo | exact Hlo16 | exact HspE | exact Hspa | exact HdisjK
        | exact Hsh16 | rewrite <- Eb16; exact Hb16 | exact Hsh17 | rewrite <- Eb17; exact Hb17
        | exact Q160 | exact HWR8 | exact HWR1 | exact HSlo
        | exact (AsanRTInv.RT_cells sp mem md HRT) | exact (AsanRTInv.RT_shadow_rw sp mem md HRT) ]. }
    { intros ms' (ra' & a1' & a2' & m3 & E & MU & WM & ST3 & HCb & HshR & Hsh392).
      eexists _, (Z_to_bv 64 0x82bcc), m3. split; [exact E|].
      repeat (split; [first [ reflexivity
                            | unfold rg in *; symmetry;
                              first [ exact Hr2 | exact Hr9 | exact Hr18 | exact Hr19 | exact Hr20
                                    | exact Hr26 | exact Hr24k ] ] | ]).
      split; [exact MU|]. split; [exact WM|]. split; [exact ST3|].
      split; [exact HCb|]. split; [exact HshR | exact Hsh392]. }
  - intros R0 pc' mem3 regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E24 & E26 & E27 & E25 & E22 & E10 & E23 &
       MU & WM & ST3 & HCb & HshR & Hsh392) Hreg Hmat.
    subst pc'.
    set (W3 := [(Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40); (sp - 16, sp)]) in *.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact E27).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 CATc.BOX_CATALOGUE) by (rewrite Hreg; exact E10).
    assert (Fr23 : getr regs' 23 = Z_to_bv 64 (fr + 32)) by (rewrite Hreg; exact E23).
    (* the heap block is apart from the frame in both frame arms *)
    assert (HinPhi : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
      by (apply in_or_app; left; unfold hb1; left; reflexivity).
    assert (Hblk : forall a, phi <= a < phi + flen g j -> ~ (fr <= a < fr + FRAME_BYTES)).
    { intros a Ha Hc.
      destruct (f32_blocks (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
                  (AC.a_size (flen g j)) HAH HinPhi) as (Hle & Hb).
      rewrite Hasz in Hle, Hb.
      destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5fr [Hfsb [Hfs Hrec]]]].
      - pose proof (Hreal a Hc) as Hr. lia.
      - exact (Hb a Ha (Hfs a Hc)). }
    assert (Hphib : phi + flen g j <= g_S g - AF.SLOT_STACK).
    { destruct (f32_blocks (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
                  (AC.a_size (flen g j)) HAH HinPhi) as (Hle & _).
      rewrite Hasz in Hle. lia. }
    (* A range whose bytes all miss the frame lies before the frame variable or after it. *)
    assert (Hfrapart : forall x n, 0 < n -> (forall y, x <= y < x + n -> ~ (fr <= y < fr + FRAME_BYTES)) ->
              (x + n <= fr + 32 \/ fr + 40 <= x)).
    { intros x n Hn Hnf.
      destruct (Z_le_gt_dec (x + n) (fr + 32)) as [HL|HR]; [left; lia|].
      destruct (Z_le_gt_dec (fr + 40) x) as [HL2|HR2]; [right; lia|].
      exfalso. destruct (Z_le_gt_dec x (fr + 32)) as [HA|HB].
      - assert (Hy1 : x <= fr + 32 < x + n) by lia.
        assert (Hy2 : fr <= fr + 32 < fr + FRAME_BYTES) by lia.
        exact (Hnf (fr + 32) Hy1 Hy2).
      - assert (Hy1 : x <= x < x + n) by lia.
        assert (Hy2 : fr <= x < fr + FRAME_BYTES) by lia.
        exact (Hnf x Hy1 Hy2). }
    assert (Hblksh : forall i, 0 <= i < AC.a_size (flen g j) -> outside W3 (shadow_addr (phi + i))).
    { intros i Hi. unfold AC.a_size in Hi. rewrite Z.max_l in Hi by lia.
      assert (Hi' : 0 <= i < AC.a_size (flen g j))
        by (unfold AC.a_size; rewrite Z.max_l by lia; lia).
      destruct (proj2 (proj2 (proj2 HAd)) i Hi') as (Hap & _).
      pose proof (shadow_of_app (phi + i) Hap) as His.
      unfold W3. cbn [outside]. split; [|split; [|split; [|exact I]]].
      - intros Hc. assert (Hq : shadow_addr (phi + i) = Sfr fr + 4) by lia.
        rewrite <- Hshc in Hq. unfold shadow_addr in Hq.
        apply (f32_gran_ne (phi + i) (fr + 32)); [lia | lia | Z.div_mod_to_equations; lia | | lia].
        intros Hin. assert (Ha1 : phi <= phi + i < phi + flen g j) by lia.
        assert (Ha2 : fr <= phi + i < fr + FRAME_BYTES) by lia.
        exact (Hblk (phi + i) Ha1 Ha2).
      - intros Hc. assert (Hc' : fr <= shadow_addr (phi + i) < fr + FRAME_BYTES) by lia.
        exact (app_not_shadow (shadow_addr (phi + i)) (Hfapp _ Hc') His).
      - intros Hc. apply (app_not_shadow (shadow_addr (phi + i))); [|exact His].
        unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia. }
    assert (HHB3 : HB mem3 phi (flen g j)).
    { split; [exact Hphi0|]. apply (f32_addr_keep W3 mem mem3 phi _ HAd MU Hblksh). }
    (* the memory facts the cut needs, transported by the write set *)
    assert (Hout : forall x, 0 <= x < 2 ^ 64 -> ~ (Sfr fr + 4 <= x < Sfr fr + 5) ->
              ~ (fr + 32 <= x < fr + 40) -> ~ (sp - 16 <= x < sp) -> outside W3 x).
    { intros x Hx H1 H2 H3. unfold W3. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (Hmunch_eq : forall x, 0 <= x < 2 ^ 64 -> ~ (Sfr fr + 4 <= x < Sfr fr + 5) ->
              ~ (fr + 32 <= x < fr + 40) -> ~ (sp - 16 <= x < sp) ->
              mem3 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx H1 H2 H3. apply MU. rewrite MState.unsigned_lit by lia. apply Hout; lia. }
    assert (Hphiapp : forall y, phi <= y < phi + flen g j -> app_mem y).
    { intros y Hy.
      assert (Hi : 0 <= y - phi < AC.a_size (flen g j))
        by (unfold AC.a_size; rewrite Z.max_l by lia; lia).
      destruct (proj2 (proj2 (proj2 HAd)) (y - phi) Hi) as (Hap & _).
      replace (phi + (y - phi)) with y in Hap by lia. exact Hap. }
    (* A byte list of app bytes, apart from the frame variable and from the callee's window, is kept: its
       shadow byte is not among the written bytes because the shadow map is not app memory. *)
    assert (Hkeep : forall a bs, bytes_at rsegs mem a bs -> 0 <= a ->
              a + Z.of_nat (length bs) <= 2 ^ 64 ->
              (forall y, a <= y < a + Z.of_nat (length bs) -> app_mem y) ->
              (a + Z.of_nat (length bs) <= fr + 32 \/ fr + 40 <= a) ->
              (a + Z.of_nat (length bs) <= sp - 16 \/ sp <= a) ->
              bytes_at rsegs mem3 a bs).
    { intros a bs Hb Ha0 Ha1 Happ' D2 D3. eapply fl_bytes; [exact Hb | exact MU |].
      intros x Hx. apply Hout; [lia | | lia | lia].
      intros Hc. assert (Hx4 : x = Sfr fr + 4) by lia.
      pose proof (Happ' x Hx) as Hxa. rewrite Hx4 in Hxa.
      exact (app_not_shadow (Sfr fr + 4) Hxa HshIS4). }
    assert (Hshlo : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG /\ LOWMEM_END <= Sfr fr).
    { pose proof (f32_frsh_shadow fr (Sfr fr) Hfapp ltac:(lia)) as Hs0.
      pose proof (f32_frsh_shadow fr (Sfr fr + FRAME_SHADOW - 1) Hfapp ltac:(lia)) as Hs1.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs0, Hs1 |- *. lia. }
    assert (Hfrapp32 : app_mem (fr + 32)) by (apply Hfapp; lia).
    assert (Hspapp : HIGHMEM_BEG <= sp - 16) by lia.
    assert (Happ_out : forall x, app_mem x -> ~ (fr + 32 <= x < fr + 40) -> ~ (sp - 16 <= x < sp) ->
              outside W3 x).
    { intros x Hxa H2 H3. apply Hout; [ | | exact H2 | exact H3].
      - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa. lia.
      - intros Hc. assert (Hx4 : x = Sfr fr + 4) by lia. rewrite Hx4 in Hxa.
        exact (app_not_shadow _ Hxa HshIS4). }
    assert (Hfr_out : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 32 <= x < fr + 40) -> outside W3 x).
    { intros x Hx Hn. apply Happ_out; [apply Hfapp; exact Hx | exact Hn |].
      destruct HdisjK as [HD|HD]; lia. }
    assert (Hwin_out : forall x, sp <= x < g_S g -> ~ (fr + 32 <= x < fr + 40) -> outside W3 x).
    { intros x Hx Hn. apply Happ_out; [ | exact Hn | lia].
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. right. lia. }
    (* FRA on the new memory *)
    assert (HroM : ro_agree rsegs mem3).
    { apply (sl_ro_keep W3 mem mem3 Hro MU). intros x Hx.
      destruct Hshlo as (_ & Hl). unfold AC.GT in Hx. unfold LOWMEM_END in Hl. unfold HIGHMEM_BEG in Hspapp.
      assert (H1 : 0 <= x < 2 ^ 64) by lia.
      assert (H2 : ~ (Sfr fr + 4 <= x < Sfr fr + 5)) by lia.
      assert (H3 : ~ (fr + 32 <= x < fr + 40)) by lia.
      assert (H4 : ~ (sp - 16 <= x < sp)) by lia.
      exact (Hout x H1 H2 H3 H4). }
    assert (Hmbmono : forall a, 0 <= a < 2 ^ 64 -> (exists b, mbyte rsegs mem a = Some b) ->
              (exists b, mbyte rsegs mem3 a = Some b)).
    { intros a Ha Hb.
      destruct (Z.eq_dec a (Sfr fr + 4)) as [->|Hne1].
      { destruct (HshR (Sfr fr + 4) HshIS4) as (b & Hb'). exists b. unfold mbyte. exact Hb'. }
      destruct (Z_le_gt_dec (fr + 32) a) as [Hge|Hlt];
        [destruct (Z_lt_ge_dec a (fr + 40)) as [Hlt2|Hge2]|].
      - destruct HCb as (_ & _ & HCbb).
        pose proof (HCbb (Z.to_nat (a - (fr + 32))) ltac:(rewrite length_le8; lia)) as HH.
        rewrite Z2Nat.id in HH by lia. replace (fr + 32 + (a - (fr + 32))) with a in HH by lia.
        destruct (nth_error (le8 (Z_to_bv 64 11)) (Z.to_nat (a - (fr + 32)))) as [b|] eqn:En.
        + exists b. unfold mbyte. exact HH.
        + exfalso. apply nth_error_None in En. rewrite length_le8 in En. lia.
      - destruct (Z_le_gt_dec (sp - 16) a) as [Hge3|Hlt3];
          [destruct (Z_lt_ge_dec a sp) as [Hlt4|Hge4]|].
        + destruct ST3 as (_ & _ & HST3). destruct (HST3 a ltac:(lia)) as (_ & b & Hb').
          exists b. unfold mbyte. exact Hb'.
        + destruct Hb as (b & Hb). exists b. unfold mbyte in *.
          rewrite Hmunch_eq by lia. exact Hb.
        + destruct Hb as (b & Hb). exists b. unfold mbyte in *.
          rewrite Hmunch_eq by lia. exact Hb.
      - destruct (Z_le_gt_dec (sp - 16) a) as [Hge3|Hlt3];
          [destruct (Z_lt_ge_dec a sp) as [Hlt4|Hge4]|].
        + destruct ST3 as (_ & _ & HST3). destruct (HST3 a ltac:(lia)) as (_ & b & Hb').
          exists b. unfold mbyte. exact Hb'.
        + destruct Hb as (b & Hb). exists b. unfold mbyte in *.
          rewrite Hmunch_eq by lia. exact Hb.
        + destruct Hb as (b & Hb). exists b. unfold mbyte in *.
          rewrite Hmunch_eq by lia. exact Hb. }
    destruct (f32_ah_move g fr (hb1 phi (AC.a_size (flen g j))) regs mem mem3 md HFRA
      ltac:(rewrite Haspz; exact MU)
      ltac:(intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)) Hmbmono Hfapp HGT)
      as (HAH3 & HOWN3 & HSTK3 & HSTKHI3).
    assert (Hrtdj : rt_disjoint W3).
    { unfold W3, rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN in *.
      unfold Sfr, shadow_addr, ASAN_K, HIGHMEM_BEG in *. cbn [disjoint_from].
      repeat split; first [left; Z.div_mod_to_equations; lia | right; Z.div_mod_to_equations; lia | exact I]. }
    assert (HAG3 : forall a, in_globals AF.frame_AG a -> addressable mem3 a 1).
    { intros a Hin. pose proof (f32_AG_bound a Hin) as Hab. pose proof (HAG a Hin) as HAa.
      apply (f32_addr_keep W3 mem mem3 a 1 HAa MU). intros i Hi.
      destruct (proj2 (proj2 (proj2 HAa)) i Hi) as (Hap & _).
      pose proof (shadow_of_app (a + i) Hap) as His.
      unfold W3. cbn [outside]. split; [|split; [|split; [|exact I]]].
      - intros Hc. exfalso.
        assert (Hq : (a + i) / 8 = fr / 8 + 4) by (unfold Sfr, shadow_addr in Hc; lia).
        revert Hq. Z.div_mod_to_equations. lia.
      - intros Hc. assert (Hc' : fr <= shadow_addr (a + i) < fr + FRAME_BYTES) by lia.
        exact (app_not_shadow (shadow_addr (a + i)) (Hfapp _ Hc') His).
      - intros Hc. apply (app_not_shadow (shadow_addr (a + i))); [|exact His].
        unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia. }
    assert (HWIN3 : stk rsegs mem3 (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (f32_stk_keep mem mem3 _ _ Hwin WM). intros x Hx.
      destruct (Z_le_gt_dec (g_S g - AF.SLOT_STACK) x) as [_|Hc]; [|lia].
      destruct (Z_lt_ge_dec x sp) as [Hlt|Hge].
      - destruct ST3 as (_ & _ & HST3). destruct (HST3 x ltac:(lia)) as (_ & b & Hb'). exists b. exact Hb'.
      - destruct (Z_le_gt_dec (fr + 32) x) as [Hge2|Hlt2];
          [destruct (Z_lt_ge_dec x (fr + 40)) as [Hlt3|Hge3]|].
        + destruct HCb as (_ & _ & HCbb).
          pose proof (HCbb (Z.to_nat (x - (fr + 32))) ltac:(rewrite length_le8; lia)) as HH.
          rewrite Z2Nat.id in HH by lia. replace (fr + 32 + (x - (fr + 32))) with x in HH by lia.
          destruct (nth_error (le8 (Z_to_bv 64 11)) (Z.to_nat (x - (fr + 32)))) as [b|] eqn:En.
          * exists b. exact HH.
          * exfalso. apply nth_error_None in En. rewrite length_le8 in En. lia.
        + destruct Hwin as (_ & _ & Hw). destruct (Hw x ltac:(lia)) as (_ & b & Hb). exists b.
          assert (Hxo : outside W3 x) by (apply Hwin_out; lia).
          assert (Hx64 : 0 <= x < 2 ^ 64) by lia.
          rewrite (f32_mrd_munch W3 mem mem3 x MU Hx64 Hxo). exact Hb.
        + destruct Hwin as (_ & _ & Hw). destruct (Hw x ltac:(lia)) as (_ & b & Hb). exists b.
          assert (Hxo : outside W3 x) by (apply Hwin_out; lia).
          assert (Hx64 : 0 <= x < 2 ^ 64) by lia.
          rewrite (f32_mrd_munch W3 mem mem3 x MU Hx64 Hxo). exact Hb. }
    assert (Hshnew : exists sh, bytes_at rsegs mem3 (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
    { destruct Hshf as (sh & Hsh & Hl). exact (Hsh392 sh Hsh Hl). }
    assert (HFRA3 : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem3 md).
    { apply (f32_fra_run g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem3 md W3 HFRA MU WM HroM Hrtdj
        HAH3 HSTK3 Hfapp HGT Hshnew HWIN3 HAG3 HshR);
        [ rewrite Haspz; lia
        | rewrite Haspz; exact HdisjK
        | intros x Hx H1 H2 H3; apply Hout; [lia | lia | lia | rewrite Haspz in H3; lia]
        | intros A' HA' HA'r x Hx; apply Hout; unfold rg in Hr9; rewrite Hr9 in HA';
          assert (A' = A) by (apply (f_equal bv_unsigned) in HA'; rewrite !MState.unsigned_lit in HA' by lia; lia);
          subst A'; lia
        | intros x Hx; apply Hout; lia
        | intros A' HA' HA'r x Hx; apply Hout; unfold rg in Hr9; rewrite Hr9 in HA';
          assert (A' = A) by (apply (f_equal bv_unsigned) in HA'; rewrite !MState.unsigned_lit in HA' by lia; lia);
          subst A'; lia
        | exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 ]. }
    assert (HFRA3' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem3 md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' regs' mem3 md md' HFRA3);
          try reflexivity; exact Hmat).
    (* ENT crosses the same write (Tac_slot's ent_store): each written byte is the frame's shadow byte S(fr)+4,
       a frame byte, or a byte of the slot window below S; the stack bounds and the owned set come from
       f32_ah_move. *)
    assert (HENT3 : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem3 md).
    { eapply ent_store with (W := W3) (fr := fr) (regs := regs);
        [ exact HENT | exact HFRA | exact MU | | exact HSTK3 | exact HSTKHI3
        | intros a Hia Ho; exact (proj2 (HOWN3 a) Ho) ].
      intros x Hx.
      destruct (Z.eq_dec x (Sfr fr + 4)) as [Ex|Ex]; [right; right; right; lia|].
      destruct (Z_le_gt_dec (fr + 32) x) as [D1|D1]; [destruct (Z_lt_ge_dec x (fr + 40)) as [D2|D2]|].
      - right; right; left. lia.
      - destruct (Z_le_gt_dec (sp - 16) x) as [D3|D3]; [destruct (Z_lt_ge_dec x sp) as [D4|D4]|].
        + right; left. lia.
        + left. apply Hout; lia.
        + left. apply Hout; lia.
      - destruct (Z_le_gt_dec (sp - 16) x) as [D3|D3]; [destruct (Z_lt_ge_dec x sp) as [D4|D4]|].
        + right; left. lia.
        + left. apply Hout; lia.
        + left. apply Hout; lia. }
    assert (HENT3' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem3 md')
      by (eapply ent_mat; [exact HENT3 | exact Hmat]).
    (* the spills and frame bytes the exit cut carries *)
    assert (Hsp9 : forall off v, spill regs mem off v -> 0 <= off <= 440 -> spill regs' mem3 off v).
    { intros off v Hs Hoff. pose proof (f32_spill regs mem off v A Hs Hr9 ltac:(lia) ltac:(lia) Hoff) as Hq.
      exists A. split; [unfold rg in *; rewrite Fr9; exact Hr9|].
      unfold q64 in *. apply Hkeep;
        [ exact Hq | lia | rewrite length_le8; lia
        | rewrite length_le8; intros y Hy; unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia
        | rewrite length_le8; lia | rewrite length_le8; lia ]. }
    (* the frame's stack facts on the new memory (PT32 and FLI carry them) *)
    assert (Hfstk3 : stk rsegs mem3 fr (fr + FRAME_BYTES)).
    { apply (f32_stk_keep mem mem3 _ _ Hfstk WM). intros x Hx.
      destruct (Z_le_gt_dec (fr + 32) x) as [Hge2|Hlt2];
        [destruct (Z_lt_ge_dec x (fr + 40)) as [Hlt3|Hge3]|].
      - destruct HCb as (_ & _ & HCbb).
        pose proof (HCbb (Z.to_nat (x - (fr + 32))) ltac:(rewrite length_le8; lia)) as HH.
        rewrite Z2Nat.id in HH by lia. replace (fr + 32 + (x - (fr + 32))) with x in HH by lia.
        destruct (nth_error (le8 (Z_to_bv 64 11)) (Z.to_nat (x - (fr + 32)))) as [b|] eqn:En.
        + exists b. exact HH.
        + exfalso. apply nth_error_None in En. rewrite length_le8 in En. lia.
      - destruct Hfstk as (_ & _ & Hf). destruct (Hf x ltac:(lia)) as (_ & b & Hb). exists b.
        assert (Hxo : outside W3 x) by (apply Hfr_out; lia).
        assert (Hx64 : 0 <= x < 2 ^ 64) by lia.
        rewrite (f32_mrd_munch W3 mem mem3 x MU Hx64 Hxo). exact Hb.
      - destruct Hfstk as (_ & _ & Hf). destruct (Hf x ltac:(lia)) as (_ & b & Hb). exists b.
        assert (Hxo : outside W3 x) by (apply Hfr_out; lia).
        assert (Hx64 : 0 <= x < 2 ^ 64) by lia.
        rewrite (f32_mrd_munch W3 mem mem3 x MU Hx64 Hxo). exact Hb. }
    (* An addressable range apart from the frame variable stays addressable: its shadow bytes are not S(fr)+4
       (a different granule) and are not app memory. *)
    assert (Hfr32 : (fr + 32) mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
    assert (HaddrK : forall p n, addressable mem p n ->
              (forall i, 0 <= i < n -> ~ (fr + 32 <= p + i < fr + 40)) -> addressable mem3 p n).
    { intros p n Hp Hn. apply (f32_addr_keep W3 mem mem3 p n Hp MU). intros i Hi.
      destruct (proj2 (proj2 (proj2 Hp)) i Hi) as (Hap & _).
      pose proof (shadow_of_app (p + i) Hap) as His. pose proof Hp as (Hpp0 & _).
      pose proof (in_shadow_range _ His) as Hsr.
      apply Hout.
      - lia.
      - intros Hc. assert (Hq : shadow_addr (p + i) = shadow_addr (fr + 32)) by lia.
        unfold shadow_addr in Hq.
        apply (f32_gran_ne (p + i) (fr + 32));
          [lia | lia | exact Hfr32 | intros Hc2; apply (Hn i Hi); lia | lia].
      - intros Hc. apply (app_not_shadow (shadow_addr (p + i))); [apply Hfapp; lia | exact His].
      - intros Hc. apply (app_not_shadow (shadow_addr (p + i))); [|exact His].
        unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia. }
    assert (Hphi3 : bytes_at rsegs mem3 phi (t_phi (g_in g) j)).
    { apply Hkeep;
        [ exact Hphi | lia | rewrite Hplen'; lia
        | rewrite Hplen'; intros y Hy; apply Hphiapp; lia
        | rewrite Hplen'; apply Hfrapart; [lia | exact Hblk]
        | rewrite Hplen'; left; lia ]. }
    assert (HIexit : Inv_B82bcc_at B APIf ra g j
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82bcc) mem3 (seg_rom rsegs)) md')).
    { exists phi, regs', mem3, md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA3'|].
      split; [exact HENT3'|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB3|].
      split.
      { pose proof (Tac_ro.fli_mem g fr regs mem HFLI) as (Fad & _ & Frad & Ffrg & (Fkb & Fka) & Ffst).
        assert (HL : length KNC.kind_name_bytes = 112%nat) by reflexivity.
        eapply Tac_ro.lk_keep; [exact HLK | | | | | | | | |].
        - unfold rg in *. rewrite Fr27. exact (proj1 HFLI).
        - apply HaddrK; [exact Fad | intros i Hi; lia].
        - exact Hfstk3.
        - apply HaddrK; [exact Frad | intros i Hi; lia].
        - apply HaddrK; [exact Ffrg | intros i Hi; unfold fragb; lia].
        - (* the kind-name table (image data below GT): apart from the frame and the callee's window *)
          unfold KNT. split.
          + apply Hkeep;
              [ exact Fkb | unfold KNC.KIND_NAME; lia | rewrite HL; unfold KNC.KIND_NAME; lia
              | rewrite HL; intros y Hy; clear - Hy; unfold app_mem, LOWMEM_END, KNC.KIND_NAME in *; left; lia
              | rewrite HL; left; clear - HGTz; unfold KNC.KIND_NAME; lia
              | rewrite HL; left; clear - Hspapp; unfold KNC.KIND_NAME, HIGHMEM_BEG in *; lia ].
          + apply HaddrK; [exact Fka | intros i Hi; clear - Hi HGTz; unfold KNC.KIND_NAME; lia].
        - (* the local `first` [fr+2880, fr+2920): apart from the frame variable [fr+32, fr+40) *)
          apply HaddrK; [exact Ffst | intros i Hi; lia].
        - unfold OURb in *. apply Hkeep;
            [ exact HOUR | lia | rewrite OUR_length; lia
            | rewrite OUR_length; intros y Hy; apply Hfapp; lia
            | rewrite OUR_length; lia | rewrite OUR_length; lia ].
        - intros off v Ho Hs. apply Hsp9; [exact Hs | lia]. }
      split.
      { destruct HFTK as (S184 & H22 & H24 & S272 & H25).
        split; [apply Hsp9; [exact S184 | lia]|].
        split; [unfold rg in *; rewrite Fr22; exact H22|].
        split; [unfold rg in *; rewrite Fr24; exact H24|].
        split; [apply Hsp9; [exact S272 | lia] | unfold rg in *; rewrite Fr25; exact H25]. }
      split; [exact Hrow|].
      split; [unfold rg; rewrite Fr10; reflexivity|].
      split; [unfold rg; rewrite Fr23; reflexivity|].
      split; [unfold q64; exact HCb|].
      split; [unfold rg in *; rewrite Fr18; exact Hr18|].
      split; [unfold rg in *; rewrite Fr20; exact Hr20|].
      split; [apply Hsp9; [exact Hs152 | lia]|].
      split; [exact Hphi3|].
      split; [exact Hplen|].
      split; [apply Hsp9; [exact Hs160 | lia]|].
      split; [exact Hfstk3|].
      split; [apply Hsp9; [exact Hs312' | lia]|].
      split.
      { destruct HFT as (S224 & S232 & _ & _).
        split; [apply Hsp9; [exact S224 | lia]|]. split; [apply Hsp9; [exact S232 | lia]|].
        split; [exact Hphi3 | exact Hplen]. }
      apply (f32_IFS_tr g fr (S j) regs regs' mem mem3 HIFS).
      - intros x Hx. assert (Hxo : outside W3 x) by (apply Hfr_out; lia).
        exact (f32_mrd_munch W3 mem mem3 x MU ltac:(lia) Hxo).
      - intros Had. apply HaddrK; [exact Had | intros i Hi; lia]. }
    pose proof (H68 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

(* The 0x82b38 entry (the bcmp wrapper's return, F31's first exit): the three checks are not taken and the run falls
   through to 0x82b5c, where seg_F32_af8 takes over. *)
Lemma seg_F32_ad4 : forall j,
  Hat B APIf ra (Inv_B82bcc_at B APIf ra) j -> Hat B APIf ra (Inv_B82c90_at B APIf ra) j ->
  Hat B APIf ra (Inv_B82b38_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros j H68 Hc2c g c HInv.
  pose proof (seg_F32_af8 j H68 Hc2c) as Haf8.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & HFTK & Hcls & Hiff &
    Hs184 & Hr25 & Hs192 & Hev & HPT & HFT & HIFS).
  subst c. rewrite SEGS.
  pose proof HPT as (Hr18 & Hr24 & Hr20 & Hs152 & Hs312 & Hphi & Hplen & Hs160 & Hfstk).
  destruct (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGT & Hfapp).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  (* the classify result: the source field is not our address, a flag is set, the event word is at most 5 *)
  assert (HSb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  destruct (t_cls (g_in g) j) as [e|] eqn:Ecl; [| exfalso; apply Hcls; reflexivity].
  destruct (f32_cls (g_in g) j e Ecl) as (Hsrc & Hflag & He).
  assert (Ha0 : bv_eqb (getr regs 10) (Z_to_bv 64 0) = false).
  { apply Bool.not_true_iff_false. intros HC. apply bv_eqb_eq in HC.
    exact (Hsrc (proj1 Hiff HC)). }
  assert (Q184 : q64 mem (A + 184) (b2z (t_tfill (g_in g) j)))
    by (apply (f32_spill regs mem 184 _ A Hs184 Hr9); lia).
  assert (Q192 : q64 mem (A + 192) (fr + 528)) by (apply (f32_spill regs mem 192 _ A Hs192 Hr9); lia).
  assert (Hevw : u32 mem (fr + 528) e) by (apply Hev; first [reflexivity | exact Ecl]).
  assert (Hfrb : fr + FRAME_BYTES <= 140737488355328).
  { pose proof (Hfapp (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. lia. }
  assert (HA0 : 0 <= A) by lia.
  assert (HA1 : A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HE0 : 0 <= fr + 528) by (unfold AC.GT in *; lia).
  assert (HE1 : fr + 528 + 4 <= 2 ^ 64) by lia.
  apply (f32_run_lib regs (Z_to_bv 64 0x82b38) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82b5c /\ mem' = mem /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 24 = getr regs 24 /\
       getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
       getr R0 25 = getr regs 25 /\ getr R0 22 = getr regs 22)
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      apply (f32e_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ mem A (b2z (t_tfill (g_in g) j)) (b2z (t_sum_ok (g_in g) j)) (fr + 528) e);
        [ unfold rg in Hr9; exact Hr9
        | unfold rg in Hr25; exact Hr25
        | exact Ha0
        | exact HA0 | exact HA1 | exact HE0 | exact HE1
        | exact Q184 | exact Q192 | exact Hevw
        | unfold b2z; destruct (t_tfill (g_in g) j); [right | left]; reflexivity
        | unfold b2z; destruct (t_sum_ok (g_in g) j); [right | left]; reflexivity
        | unfold b2z; destruct Hflag as [Hf|Hf]; rewrite Hf; [left | right]; reflexivity
        | lia ]. }
    { intros ms' E. eexists _, _, _. split; [exact E|].
      split; [reflexivity|]. split; [reflexivity|]. repeat split; reflexivity. }
  - intros R0 pc' mem' regs' md'
      (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E24 & E26 & E27 & E25 & E22) Hreg Hmat.
    subst pc' mem'.
    assert (Hsp9 : forall off v, spill regs mem off v -> spill regs' mem off v).
    { intros off v (A' & HA' & Hq). exists A'. split; [|exact Hq]. unfold rg in *.
      rewrite Hreg, E9. exact HA'. }
    assert (HIexit : Inv_B82b5c_at B APIf ra g j
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82b5c) mem (seg_rom rsegs)) md')).
    { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem md md' HFRA);
          rewrite ?Hreg; assumption. }
      split; [eapply ent_mat; [exact HENT | exact Hmat]|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
      split.
      { pose proof HLK as (Hj255 & Hs240 & HOUR & HFLI).
        pose proof (Tac_ro.fli_mem g fr regs mem HFLI) as (Fad & Fstk & Frad & Ffrg & Fknt & Ffst).
        eapply Tac_ro.lk_keep;
          [exact HLK | | exact Fad | exact Fstk | exact Frad | exact Ffrg | exact Fknt | exact Ffst | exact HOUR |].
        - unfold rg in *. rewrite Hreg, E27. exact (proj1 HFLI).
        - intros off v _ Hs. exact (Hsp9 off v Hs). }
      split.
      { destruct HFTK as (S184 & H22 & H24 & S272 & H25).
        split; [apply Hsp9; exact S184|].
        split; [unfold rg in *; rewrite Hreg, E22; exact H22|].
        split; [unfold rg in *; rewrite Hreg, E24; exact H24|].
        split; [apply Hsp9; exact S272 | unfold rg in *; rewrite Hreg, E25; exact H25]. }
      split.
      { split; [unfold rg in *; rewrite Hreg, E18; exact Hr18|].
        split; [unfold rg in *; rewrite Hreg, E24; exact Hr24|].
        split; [unfold rg in *; rewrite Hreg, E20; exact Hr20|].
        split; [apply Hsp9; exact Hs152|].
        split; [apply Hsp9; exact Hs312|].
        split; [exact Hphi|]. split; [exact Hplen|].
        split; [apply Hsp9; exact Hs160|].
        exact Hfstk. }
      split.
      { destruct HFT as (S224 & S232 & Hb & Hl).
        split; [apply Hsp9; exact S224|]. split; [apply Hsp9; exact S232|]. split; [exact Hb | exact Hl]. }
      exact (f32_IFS_tr g fr (S j) regs regs' mem mem HIFS (fun x _ => eq_refl) (fun X => X)). }
    pose proof (Haf8 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

(* S_F32 (forms-asan-ubsan-v190.md): both entries of the segment, 0x82b38 and 0x82b5c, from F33's entry cut and the
   0x82c90 cut. *)
Lemma seg_F32 : forall j : nat,
  Hat B APIf ra (Inv_B82bcc_at B APIf ra) j -> Hat B APIf ra (Inv_B82c90_at B APIf ra) j ->
  Hat B APIf ra (Inv_B82b38_at B APIf ra) j /\ Hat B APIf ra (Inv_B82b5c_at B APIf ra) j.
Proof.
  intros j H68 Hc2c. split; [exact (seg_F32_ad4 j H68 Hc2c) | exact (seg_F32_af8 j H68 Hc2c)].
Qed.

End F32.
