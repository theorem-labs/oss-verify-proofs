(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module names changed; 371 of its 411 lines of code are new or changed and 356 lines of the source are left out. *)
(* Segment F28b of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): the check_ports post-loop checks
   0x826d4-0x8274c, the slow block of the instrumented check 0x82a8c-0x82a94 and the error
   path entry 0x82d1c (not reached). Entry cut Inv_A826d4_at, exit cut Inv_A82750_at (official SlotInv.v cuts;
   the exit's FLS / LT come from B7K, push 12, by B7Cuts.b7_a826a4).

   The block reads the three ports words at t2 = fr + 128 (PORTS with t_rp = 0), the byte first at [A+120] = fr + 160
   (FIRSTb), loads s9 = [A+176] = fr + 64 (B7SPL), and takes none of the seven branches to 0x82bf4: in_ch and
   out_ch | unk are multiples of 4, first = the first code >= 4, 4 n_empty + unk + in_ch + out_ch = 48 (addw),
   in_ch = 4 n_in, out_ch = 4 n_out and headamp_base = 16 blk[7] (the plain twin's Q06, its branch lemmas q06_c80 ..
   q06_c86 and Tac_b7's ports facts C5.6-C5.8, copied here with a b7_ prefix). Before the 1-byte load of blk[7] at
   phi + 25 the code loads the shadow byte k at ((phi + 25) >> 3) + ASAN_K and continues when k = 0 or
   (phi + 25) mod 8 < k (the slow block 0x82a8c); the byte is addressable (HB(phi), flen >= 50), so the branch to
   the error path 0x82d1c is not taken. No memory is written, so FRA moves by sl_fra_move and the entry relation
   ENT (push 5c) by ent_mat alone. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot B7Cuts.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.

(* ---- The ports facts of C5.6-C5.8 (plain twin Tac_b7.v; pbs = the first 20 bytes of the block phi + 18) ---- *)

Lemma b7_decl_same : forall bs, RcLeaf.decl bs = RcPorts.pu_decl bs.
Proof. intros bs. reflexivity. Qed.

Lemma b7_nunk_nonneg : forall bs k, 0 <= RcPorts.pu_nunk bs k.
Proof. intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|]. destruct (4 <=? _); lia. Qed.

Lemma b7_nunk_le : forall bs k, RcPorts.pu_nunk bs k <= Z.of_nat k.
Proof. intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|]. destruct (4 <=? _); lia. Qed.

Lemma b7_cnt_range : forall f bs k, 0 <= RcLeaf.cnt f bs k <= Z.of_nat k.
Proof. intros f bs k. induction k as [|k IH]; cbn [RcLeaf.cnt]; [lia|]. destruct (f _); lia. Qed.

(* C5.6: every code is in exactly one of {00, 02}, {01}, {03}, >= 4. *)
Lemma b7_codes_sum : forall bs k,
  RcLeaf.cnt RcLeaf.is_in bs k + RcLeaf.cnt RcLeaf.is_out bs k + RcLeaf.cnt is_empty bs k +
  RcPorts.pu_nunk bs k = Z.of_nat k.
Proof.
  intros bs k. induction k as [|k IH]; cbn [RcLeaf.cnt RcPorts.pu_nunk]; [reflexivity|].
  unfold RcPorts.rc_u8. fold (RcLeaf.bt bs (8 + k)).
  pose proof (bv_unsigned_in_range 8 (nth (8 + k) bs (Z_to_bv 8 0))) as R. unfold RcLeaf.bt.
  set (c := bv_unsigned (nth (8 + k) bs (Z_to_bv 8 0))) in *.
  assert (E : (if RcLeaf.is_in c then 1 else 0) + (if RcLeaf.is_out c then 1 else 0) +
              (if is_empty c then 1 else 0) + (if 4 <=? c then 1 else 0) = 1).
  { unfold RcLeaf.is_in, RcLeaf.is_out, is_empty.
    destruct (Z.eqb_spec c 0); destruct (Z.eqb_spec c 1); destruct (Z.eqb_spec c 2); destruct (Z.eqb_spec c 3);
      destruct (Z.leb_spec 4 c); cbn [orb]; lia. }
  lia.
Qed.

Lemma b7_unk_rp0 : forall inp j, t_rp inp j = 0 -> 0 <= t_unk inp j <= 48 /\ RcPorts.pu_decl (t_pbs inp j) = true.
Proof.
  intros inp j H. unfold t_rp, t_unk in *. rewrite <- b7_decl_same.
  destruct (RcLeaf.decl (t_pbs inp j)); [|discriminate H].
  pose proof (b7_nunk_nonneg (t_pbs inp j) 12). pose proof (b7_nunk_le (t_pbs inp j) 12).
  change (Z.of_nat 12) with 12 in *. split; [lia | reflexivity].
Qed.

(* C5.5 / C5.7: the first unknown code is 0 exactly when there is none, and is a byte. *)
Lemma b7_first_spec : forall bs k,
  (RcPorts.pu_first bs k = 0 <-> RcPorts.pu_nunk bs k = 0) /\ 0 <= RcPorts.pu_first bs k < 256.
Proof.
  intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_first RcPorts.pu_nunk]; [lia|].
  pose proof (b7_nunk_nonneg bs k).
  pose proof (bv_unsigned_in_range 8 (nth (8 + k) bs (Z_to_bv 8 0))) as R. unfold RcPorts.rc_u8.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  set (c := bv_unsigned (nth (8 + k) bs (Z_to_bv 8 0))) in *.
  destruct IH as [IH1 IH2].
  destruct (Z.eqb_spec (RcPorts.pu_nunk bs k) 0); destruct (Z.leb_spec 4 c); cbn [andb]; lia.
Qed.

(* C5.8: headamp_base reads blk[7] = Phi[25]; blk and pbs share their first 20 bytes. *)
Lemma b7_blk_pbs : forall inp j k, (k < 20)%nat ->
  nth k (t_blk inp j) (Z_to_bv 8 0) = nth k (t_pbs inp j) (Z_to_bv 8 0).
Proof.
  intros inp j k Hk. unfold t_blk, t_pbs, RcFrag.bsl.
  change (Z.to_nat 32) with 32%nat. change (Z.to_nat 20) with 20%nat.
  rewrite !nth_firstn. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (k <? 20)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.

Lemma b7_blk_length : forall inp j, length (t_blk inp j) = 32%nat.
Proof.
  intros inp j. unfold t_blk, t_g, RcFrag.bsl. rewrite length_firstn, length_skipn, fr50_length. reflexivity.
Qed.

(* The count facts in the cut's own vocabulary (n_in, n_out, bt), proved over an abstract block so the segment
   proof only instantiates them. *)
Lemma b7_n_in_range : forall bs, 0 <= RcLeaf.n_in bs <= 12.
Proof.
  intros bs. unfold RcLeaf.n_in. pose proof (b7_cnt_range RcLeaf.is_in bs 12) as H.
  change (Z.of_nat 12) with 12 in H. exact H.
Qed.

Lemma b7_n_out_range : forall bs, 0 <= RcLeaf.n_out bs <= 12.
Proof.
  intros bs. unfold RcLeaf.n_out. pose proof (b7_cnt_range RcLeaf.is_out bs 12) as H.
  change (Z.of_nat 12) with 12 in H. exact H.
Qed.

Lemma b7_emp_range : forall bs, 0 <= RcLeaf.cnt is_empty bs 12 <= 12.
Proof.
  intros bs. pose proof (b7_cnt_range is_empty bs 12) as H. change (Z.of_nat 12) with 12 in H. exact H.
Qed.

Lemma b7_nu_range : forall bs, 0 <= RcPorts.pu_nunk bs 12 <= 12.
Proof.
  intros bs. pose proof (b7_nunk_nonneg bs 12) as H0. pose proof (b7_nunk_le bs 12) as H1.
  change (Z.of_nat 12) with 12 in H1. lia.
Qed.

Lemma b7_pf_range : forall bs, 0 <= RcPorts.pu_first bs 12 < 256.
Proof. intros bs. exact (proj2 (b7_first_spec bs 12)). Qed.

Lemma b7_sum12 : forall bs,
  RcLeaf.n_in bs + RcLeaf.n_out bs + RcLeaf.cnt is_empty bs 12 + RcPorts.pu_nunk bs 12 = 12.
Proof.
  intros bs. unfold RcLeaf.n_in, RcLeaf.n_out. pose proof (b7_codes_sum bs 12) as H.
  change (Z.of_nat 12) with 12 in H. exact H.
Qed.

Lemma b7_hb : forall bs, 16 * RcLeaf.bt bs 7 = 16 * bv_unsigned (nth 7 bs (Z_to_bv 8 0)).
Proof. intros bs. reflexivity. Qed.

(* ---- Bit-vector helpers (plain twin Tac_b7.v) ---- *)

Lemma b7_all : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall u, 0 <= u < 256 -> P u = true.
Proof.
  intros P H u Hu. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat u).
  split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

Lemma b7_sx32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite MState.unsigned_lit by lia.
  rewrite bv_swrap_small; [reflexivity | change (bv_half_modulus 32) with (2 ^ 31); lia].
Qed.

Lemma b7_land4 : forall x, 0 <= x -> Z.land (4 * x) 3 = 0.
Proof.
  intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.

Lemma b7_uzxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply MState.unsigned_lit. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma b7_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  exact R.
Qed.

(* ---- The seven branches to 0x82bf4 (plain twin Q06.v, q06_c80 .. q06_c86) ---- *)

(* 0x826dc: in_ch & 3 = 0. *)
Lemma b7_c80 : forall nin, 0 <= nin <= 12 ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (sx32 (Z_to_bv 64 (4 * nin)))) 3)) (Z_to_bv 64 0)) = false.
Proof.
  intros nin H. rewrite b7_sx32 by lia. rewrite MState.unsigned_lit by lia. rewrite b7_land4 by lia.
  rewrite bv_eqb_refl. reflexivity.
Qed.

(* 0x826ec: (out_ch | unk) & 3 = 0. *)
Lemma b7_c81 : forall nout nu, 0 <= nout <= 12 -> 0 <= nu <= 12 ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 (Z_to_bv 64 (4 * nout))))
                                                                    (bv_unsigned (Z_to_bv 64 (4 * nu)))))) 3))
               (Z_to_bv 64 0)) = false.
Proof.
  intros nout nu H1 H2. rewrite b7_sx32 by lia.
  rewrite (MState.unsigned_lit (4 * nout)) by lia. rewrite (MState.unsigned_lit (4 * nu)) by lia.
  rewrite (MState.unsigned_lit (Z.lor (4 * nout) (4 * nu))) by (apply zr_lor; unfold inr64; lia).
  rewrite Z.land_lor_distr_l, !b7_land4 by lia. rewrite bv_eqb_refl. reflexivity.
Qed.

(* 0x826fc: the byte first read back equals zext.b of the first code >= 4. *)
Lemma b7_c82 : forall pf, 0 <= pf < 256 ->
  negb (bv_eqb (zxb (Z_to_bv 8 pf)) (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 pf)) 255))) = false.
Proof.
  intros pf H.
  pose proof (b7_all (fun pf => Bool.eqb (negb (bv_eqb (zxb (Z_to_bv 8 pf))
                                     (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 pf)) 255)))) false)
                ltac:(vm_compute; reflexivity) pf H) as E.
  cbv beta in E. apply Bool.eqb_prop in E. exact E.
Qed.

(* 0x82718: 4 n_empty + unk + in_ch + out_ch = 48 (addw). *)
Lemma b7_c83 : forall nin nout nemp nu, 0 <= nin <= 12 -> 0 <= nout <= 12 -> 0 <= nemp <= 12 -> 0 <= nu <= 12 ->
  nin + nout + nemp + nu = 12 ->
  negb (bv_eqb
          (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 nemp)) 2)) +
                                    bv_unsigned (Z_to_bv 64 (4 * nu + bv_unsigned (sx32 (Z_to_bv 64 (4 * nin))) +
                                                              bv_unsigned (sx32 (Z_to_bv 64 (4 * nout))))))))
          (Z_to_bv 64 48)) = false.
Proof.
  intros nin nout nemp nu H1 H2 H3 H4 H5. rewrite !b7_sx32 by lia.
  rewrite (MState.unsigned_lit nemp) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  rewrite (MState.unsigned_lit (4 * nin)) by lia. rewrite (MState.unsigned_lit (4 * nout)) by lia.
  rewrite (MState.unsigned_lit (nemp * 4)) by lia.
  rewrite (MState.unsigned_lit (4 * nu + 4 * nin + 4 * nout)) by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  replace (nemp * 4 + (4 * nu + 4 * nin + 4 * nout)) with 48 by lia.
  rewrite bv_eqb_refl. reflexivity.
Qed.

(* 0x82720, 0x82728: a port width against 4 times its count. *)
Lemma b7_c84 : forall n, 0 <= n <= 12 ->
  negb (bv_eqb (sx32 (Z_to_bv 64 (4 * n))) (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 2)))) =
  false.
Proof.
  intros n H. rewrite b7_sx32 by lia. rewrite MState.unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 2) with 4. rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  replace (n * 4) with (4 * n) by lia. rewrite bv_eqb_refl. reflexivity.
Qed.

(* 0x8274c: headamp_base = 16 blk[7]. *)
Lemma b7_c86 : forall b : byte,
  negb (bv_eqb (sx32 (Z_to_bv 64 (16 * bv_unsigned b))) (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 4))) = false.
Proof.
  intros b. pose proof (b7_byte_range b) as R. rewrite b7_sx32 by lia. rewrite b7_uzxb.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. replace (bv_unsigned b * 16) with (16 * bv_unsigned b) by lia.
  rewrite bv_eqb_refl. reflexivity.
Qed.

(* ---- Memory reads in the form the UL `step` consumes ---- *)

Lemma f28b_rd : forall m a bs, bytes_at rsegs m a bs ->
  ov_read_bytes rsegs m (ULMem.wa a) (length bs) = Some bs.
Proof.
  intros m a bs H.
  pose proof (ULMem.bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all in HH. exact HH.
Qed.

Lemma f28b_rd1 : forall m a bs k d, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (ULMem.wa (a + Z.of_nat k)) 1 = Some [nth k bs d].
Proof.
  intros m a bs k d H Hk.
  pose proof (ULMem.bytes_at_ov_read rsegs m a bs k 1 H ltac:(lia)) as HH. rewrite HH. f_equal.
  clear H HH. revert k Hk. induction bs as [|b bs IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(* The cell facts of the cuts as reads, proved once over abstract values (so the segment proof only instantiates
   them). *)
Lemma f28b_rd4 : forall m a v, u32 m a v -> ov_read_bytes rsegs m (ULMem.wa a) 4 = Some (le4 (Z_to_bv 64 v)).
Proof. intros m a v H. exact (f28b_rd m a (le4 (Z_to_bv 64 v)) H). Qed.

Lemma f28b_rd8 : forall m a v, q64 m a v -> ov_read_bytes rsegs m (ULMem.wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof. intros m a v H. exact (f28b_rd m a (le8 (Z_to_bv 64 v)) H). Qed.

Lemma f28b_rdb : forall m a v, b8 m a v -> ov_read_bytes rsegs m (ULMem.wa a) 1 = Some [Z_to_bv 8 v].
Proof. intros m a v H. exact (f28b_rd m a [Z_to_bv 8 v] H). Qed.

(* blk[7] = pbs[7], read at phi + 25 (from B7K's block fact, stated with the cut's own bytes_at). *)
Lemma f28b_blk7 : forall m phi inp j, LMem.bytes_at rsegs m (phi + 18) (t_blk inp j) ->
  ov_read_bytes rsegs m (ULMem.wa (phi + 25)) 1 = Some [nth 7 (t_pbs inp j) (Z_to_bv 8 0)].
Proof.
  intros m phi inp j H.
  pose proof (f28b_rd1 m (phi + 18) (t_blk inp j) 7 (Z_to_bv 8 0) H ltac:(rewrite b7_blk_length; lia)) as R.
  rewrite (b7_blk_pbs inp j 7 ltac:(lia)) in R.
  replace (phi + 18 + Z.of_nat 7) with (phi + 25) in R by lia. exact R.
Qed.

(* The instrumented 1-byte check of an addressable byte X: the shadow byte b is readable at (X >> 3) + ASAN_K and
   passes the check (b = 0, or X mod 8 < b) (F17's f17_shadow). *)
Lemma f28b_shadow : forall m X, addressable m X 1 ->
  exists b : byte, ov_read_bytes rsegs m (ULMem.wa (Z.shiftr X 3 + ASAN_K)) 1 = Some [b]
    /\ (bv_signed b = 0 \/ X mod 8 < bv_signed b) /\ -128 <= bv_signed b < 128.
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & IS).
  exists b. split; [| split].
  - pose proof (cells_at_read rsegs m (Z.shiftr X 3 + ASAN_K) [C1 b] 0%nat (C1 b) RO eq_refl) as H.
    cbn [csize cbytes] in H. rewrite Z.add_0_r in H. exact H.
  - destruct OK as [H|H]; [left; exact H | right; lia].
  - pose proof (sbyte_range b); lia.
Qed.

(* A spill read through s1 = A (FRA's spill base, 0 <= A, A + off < 2^64). *)
Lemma f28b_spill : forall regs m A off v, rg regs 9 A -> 0 <= A -> 0 <= off -> A + off < 2 ^ 64 ->
  spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v HA HA0 Hoff HAo (A' & HA' & Hq).
  assert (E : A' = A).
  { unfold rg in HA, HA'. rewrite HA in HA'. apply (f_equal bv_unsigned) in HA'.
    rewrite !MState.unsigned_lit_wrap in HA'.
    pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

Lemma f28b_spill_move : forall regs regs' m off v, getr regs' 9 = getr regs 9 -> spill regs m off v ->
  spill regs' m off v.
Proof. intros regs regs' m off v E (A & HA & Hq). exists A. split; [unfold rg in *; rewrite E; exact HA | exact Hq]. Qed.

(* mkR_of regs is definitionally the explicit 31-slot register map (F20). *)
Lemma f28b_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot `getr regs r` to its carried value, from H : rg regs r v (F20). *)
Ltac subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* A branch to 0x82bf4 shown not taken: its condition is false by pf. *)
Ltac brf pf :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; pf); cbv_concl_iota
  end.

(* The instrumented check bnez convergence (F17's converge): the fast path (shadow byte = 0) and the slow block
   0x82a8c (`andi a3,a0,7; bge a3,a2,errpath; j 0x82744`, the bge not taken from X mod 8 < b) rejoin at 0x82744 with
   only the scratch register a3 changed. Leaves the goal `evt .. 0x82744` for an arbitrary a3. *)
Ltac converge scratch Xe b OK BD :=
  match goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
      let Gc := fresh "Gc" in
      enough (Gc : forall rr, evt segs Q (MS (bvmap_set scratch rr R) F cont fc rv m ro)) by
        (let K0 := fresh "K0" in
         destruct (Z.eqb_spec (bv_signed b) 0) as [K0|K0];
         [ match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (unfold sxb; rewrite K0; vm_compute; reflexivity) end;
           cbv_concl_iota;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end
         | let Hmb := fresh "Hmb" in let Hlt := fresh "Hlt" in
           pose proof (Z.mod_pos_bound Xe 8 ltac:(lia)) as Hmb;
           assert (Hlt : Xe mod 8 < bv_signed b) by (destruct OK as [HH|HH]; [exfalso; apply K0; exact HH | lia]);
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold sxb; rewrite bv_eqb_lit by lia;
               replace (bv_signed b =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
           cbv_concl_iota; step; step;
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (rewrite (MState.unsigned_lit Xe) by lia;
               rewrite land7 by lia; rewrite lts_sxb by lia;
               replace (Xe mod 8 <? bv_signed b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) end;
           cbv_concl_iota; step;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end ])
  end; intro.

(* The state at 0x82750: memory unchanged, the FRA registers (2, 3, 4, 8, 9, 19, 26) and the B7K registers
   (18, 21, 22, 23, 24) kept, s9 = fr + 64. *)
Definition f28b_K (regs : bvmap 5 word) (fr : Z) (mem : word -> option byte)
    (R : bvmap 5 word) (pc' : word) (mem' : word -> option byte) : Prop :=
  pc' = Z_to_bv 64 0x82750 /\ mem' = mem /\
  getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
  getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
  getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
  getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\
  getr R 25 = Z_to_bv 64 (fr + 64).

Section F28b.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The run 0x826d4 -> 0x82750 over abstract values: nin = n_in, nout = n_out, nemp = n_empty, nu = n_unk,
   pf = the first code >= 4, hb = headamp_base, b7 = blk[7], b25 = the shadow byte of phi + 25. hb is a separate
   variable tied to b7 by a Z equation, so that the segment proof instantiates every read premise syntactically:
   a conversion inside a `u32` / `le4` term (a bit-vector record with its proof field, four times over) makes the
   kernel check of the segment's proof term take minutes. *)
Lemma f28b_run : forall (regs : bvmap 5 word) (mem : word -> option byte)
    (fr A phi nin nout nemp nu pf hb : Z) (b7 b25 : byte),
  rg regs 7 (fr + 128) -> rg regs 20 (4 * nu) -> rg regs 9 A -> rg regs 13 nemp -> rg regs 12 nin ->
  rg regs 11 nout -> rg regs 17 pf -> rg regs 22 (phi + 18) -> rg regs 26 ASAN_K ->
  0 <= nin <= 12 -> 0 <= nout <= 12 -> 0 <= nemp <= 12 -> 0 <= nu <= 12 -> nin + nout + nemp + nu = 12 ->
  0 <= pf < 256 -> 0 < phi -> phi + 50 <= 2 ^ 64 -> hb = 16 * bv_unsigned b7 ->
  ov_read_bytes rsegs mem (ULMem.wa (fr + 128)) 4 = Some (le4 (Z_to_bv 64 (4 * nin))) ->
  ov_read_bytes rsegs mem (ULMem.wa (fr + 132)) 4 = Some (le4 (Z_to_bv 64 (4 * nout))) ->
  ov_read_bytes rsegs mem (ULMem.wa (fr + 136)) 4 = Some (le4 (Z_to_bv 64 hb)) ->
  ov_read_bytes rsegs mem (ULMem.wa (A + 120)) 8 = Some (le8 (Z_to_bv 64 (fr + 160))) ->
  ov_read_bytes rsegs mem (ULMem.wa (fr + 160)) 1 = Some [Z_to_bv 8 pf] ->
  ov_read_bytes rsegs mem (ULMem.wa (A + 176)) 8 = Some (le8 (Z_to_bv 64 (fr + 64))) ->
  ov_read_bytes rsegs mem (ULMem.wa (Z.shiftr (phi + 25) 3 + ASAN_K)) 1 = Some [b25] ->
  (bv_signed b25 = 0 \/ (phi + 25) mod 8 < bv_signed b25) -> -128 <= bv_signed b25 < 128 ->
  ov_read_bytes rsegs mem (ULMem.wa (phi + 25)) 1 = Some [b7] ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
                                  f28b_K regs fr mem R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x826d4) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem fr A phi nin nout nemp nu pf hb b7 b25 Ht2 Hs4 Hs1 Ha3 Ha2 Ha1 Ha7 Hs6 Hs10
    Rin Rout Remp Rnu Hsum Rpf Hphi0 Hphi50 Ehb R0 R4 R8 R120 RFI R176 RSH OK25 BD25 R25.
  subst hb.
  unfold f28b_K. rewrite f28b_mkR_of_expand.
  subst_slot Ht2. subst_slot Hs4. subst_slot Hs1. subst_slot Ha3. subst_slot Ha2. subst_slot Ha1.
  subst_slot Ha7. subst_slot Hs6. subst_slot Hs10.
  (* 0x826d4 lw a0,0(t2) ; andi a4,a0,3 ; bnez a4 (in_ch & 3 = 0) *)
  step. step. step. brf ltac:(exact (b7_c80 nin Rin)).
  (* 0x826e0 lw a4,4(t2) ; or a5,a4,s4 ; andi a5,a5,3 ; bnez a5 ((out_ch | unk) & 3 = 0) *)
  step. step. step. step. brf ltac:(exact (b7_c81 nout nu Rout Rnu)).
  (* 0x826f0 ld a5,120(s1) ; lbu a5,0(a5) ; zext.b a6,a7 ; bne a5,a6 (first) *)
  step. step. step. step. brf ltac:(exact (b7_c82 pf Rpf)).
  (* 0x82700 slli a3 ; add s4 ; add s4 ; addw a3 ; ld s9,176(s1) ; li a5,48 ; bne a3,a5 (sum = 48) *)
  step. step. step. step. step. step. step. brf ltac:(exact (b7_c83 nin nout nemp nu Rin Rout Remp Rnu Hsum)).
  (* 0x8271c slliw a2 ; bne a0,a2 (in_ch = 4 n_in) *)
  step. step. brf ltac:(exact (b7_c84 nin Rin)).
  (* 0x82724 slliw a0,a1 ; bne a4,a0 (out_ch = 4 n_out) *)
  step. step. brf ltac:(exact (b7_c84 nout Rout)).
  (* 0x8272c addi a0,s6,7 ; srli a1,a0,3 ; add a1,a1,s10 ; lb a2,0(a1) ; lw a1,8(t2) ; bnez a2 *)
  step. step. step.
  rewrite (MState.unsigned_lit (phi + 25)) by lia.
  step. step. step.
  converge (Z_to_bv 5 13) (phi + 25) b25 OK25 BD25.
  (* 0x82744 lbu a0,0(a0) ; slli a0,a0,4 ; bne a1,a0 (headamp_base = 16 blk[7]) *)
  step. step. step. brf ltac:(exact (b7_c86 b7)).
  finish. all: simp_regs; try reflexivity.
Qed.

(* From the state at 0x82750 to the exit cut Inv_A82750_at: FRA by sl_fra_move (no memory write), ENT by ent_mat,
   FLSI by b7_flsi_regs, B7K by b7_B7K_regs, s9 = fr + 64, and the body by b7_a826a4. *)
Lemma f28b_cont : forall j g phi regs mem md fr,
  Hat B APIf ra (Inv_A82750_at B APIf ra) j ->
  FRA B APIf ra g fr (hb1 phi (flen g j)) regs mem md -> ENT APIf g (hb1 phi (flen g j)) mem md ->
  g_n g < 2 ^ 26 -> (j <= 255)%nat ->
  HB mem phi (flen g j) -> FLSI g j fr regs mem -> B7K g j phi fr regs mem ->
  forall R pc' mem' regs' md', f28b_K regs fr mem R pc' mem' -> (forall r, getr regs' r = getr R r) ->
  AsanLift.mat_le md md' ->
  SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') (Post B APIf ra g).
Proof.
  intros j g phi regs mem md fr Hexit HFRA HENT Hgn Hj HHB HFLSI HK R pc' mem' regs'' md'
    (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E19 & E21 & E22 & E23 & E24 & E26 & E18 & E25) Hreg Hmat.
  pose proof (proj1 FF) as SEGS.
  pose proof (b7_asize_flen g j phi fr regs mem HK) as Hasz.
  subst pc' mem'. rewrite <- SEGS. apply Hexit.
  unfold Inv_A82750_at.
  exists phi, regs'', mem, md', fr.
  rewrite ?Hasz.
  split; [reflexivity|].
  split.
  { apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs regs'' mem md md' HFRA);
      [ rewrite Hreg; exact E2 | rewrite Hreg; exact E3 | rewrite Hreg; exact E4
      | rewrite Hreg; exact E8 | rewrite Hreg; exact E9 | rewrite Hreg; exact E19
      | rewrite Hreg; exact E26 | exact Hmat ]. }
  split; [exact (ent_mat APIf g (hb1 phi (flen g j)) mem md md' HENT Hmat)|].
  split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
  assert (HFLSI' : FLSI g j fr regs'' mem)
    by (apply (b7_flsi_regs g j fr regs regs'' mem HFLSI); rewrite Hreg; exact E9).
  split; [exact HFLSI'|].
  apply (b7_a826a4 g j phi fr regs'' mem HFLSI').
  - apply (b7_B7K_regs g j phi fr regs regs'' mem HK); rewrite Hreg; assumption.
  - unfold rg. rewrite Hreg. exact E25.
Qed.

Lemma seg_F28b : forall j : nat,
  Hat B APIf ra (Inv_A82750_at B APIf ra) j -> Hat B APIf ra (Inv_A826d4_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HK &
    Hrp & Hunk0 & Hs4 & Ht2 & HPO & HFI & Ha2 & Ha1 & Ha3 & Ha7). subst c.
  rewrite SEGS.
  pose proof (b7_asize_flen g j phi fr regs mem HK) as Hasz.
  rewrite Hasz in HFRA, HENT.
  pose proof HK as (HLK & H23 & H22 & Hphi0 & Hphi50 & Hfl & Hblk & Hsp280 & H24 & H18 & H152 & Hg & Hph & Hlen &
    HLT & Hsp136 & Hsp120 & Hsp176).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hrest).
  (* the spill base A: 0 <= sp <= A and A + 312 <= 2^64 *)
  assert (Hsp0 : 0 <= sp).
  { unfold AC.aspZ in Haspz. pose proof (bv_unsigned_in_range 64 (getr regs 2)). lia. }
  assert (HAhi : A + 312 <= 2 ^ 64).
  { pose proof Hspill as (_ & Hq & _). rewrite length_le8 in Hq. change (Z.of_nat 8) with 8 in Hq. lia. }
  pose proof (f28b_spill regs mem A 120 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) Hsp120) as Q120.
  pose proof (f28b_spill regs mem A 176 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) Hsp176) as Q176.
  (* The model facts: t_rp = 0, so unk = 4 n_unk and first = the first code >= 4; the three ports words. Every
     fact keeps the cut's own terms (n_in, n_out, bt) and reaches f28b_run unchanged, so each premise is
     instantiated syntactically: a conversion inside a `u32` / `le4` term, or a `destruct` of the applied
     conjunction `proj1 HPO Hrp`, makes the kernel check of this proof term take minutes. *)
  pose proof (proj2 (b7_unk_rp0 (g_in g) j Hrp)) as Ed.
  assert (Hs4' : rg regs 20 (4 * RcPorts.pu_nunk (t_pbs (g_in g) j) 12)).
  { unfold t_unk in Hs4. rewrite Ed in Hs4. exact Hs4. }
  assert (HFI' : b8 mem (fr + 160) (RcPorts.pu_first (t_pbs (g_in g) j) 12)).
  { unfold FIRSTb, t_first in HFI. rewrite Ed in HFI. exact HFI. }
  pose proof (proj1 (proj1 HPO Hrp)) as P0.
  pose proof (proj1 (proj2 (proj1 HPO Hrp))) as P4.
  pose proof (proj2 (proj2 (proj1 HPO Hrp))) as P8.
  (* the instrumented check of blk[7] = phi + 25: addressable from HB(phi), flen >= 50 *)
  assert (Had25 : addressable mem (phi + 25) 1).
  { destruct HHB as (_ & HAd). apply (addressable_sub mem phi (AC.a_size (flen g j)) 25 1 HAd); unfold AC.a_size; lia. }
  destruct (f28b_shadow mem (phi + 25) Had25) as (b25 & HRsh & OK25 & BD25).
  apply (sl_run regs (Z_to_bv 64 0x826d4) mem md (f28b_K regs fr mem) (Post B APIf ra g)).
  - exact Hhalt.
  - exact (f28b_run regs mem fr A phi _ _ _ _ _ _ (nth 7 (t_pbs (g_in g) j) (Z_to_bv 8 0)) b25
             Ht2 Hs4' Hr9 Ha3 Ha2 Ha1 Ha7 H22 Hr26
             (b7_n_in_range _) (b7_n_out_range _) (b7_emp_range _) (b7_nu_range _) (b7_sum12 _) (b7_pf_range _)
             Hphi0 Hphi50 (b7_hb _)
             (f28b_rd4 mem _ _ P0) (f28b_rd4 mem _ _ P4) (f28b_rd4 mem _ _ P8)
             (f28b_rd8 mem _ _ Q120) (f28b_rdb mem _ _ HFI') (f28b_rd8 mem _ _ Q176)
             HRsh OK25 BD25 (f28b_blk7 mem phi (g_in g) j Hblk)).
  - exact (f28b_cont j g phi regs mem md fr Hexit HFRA HENT Hgn Hj HHB HFLSI HK).
Qed.

End F28b.
