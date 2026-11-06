(* Helpers of seg_F05 (batch u4) of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): the block-sum loop over Φ[18..49]
   (psum, the byte reads, AF9's room value and the branch tactics, ported from a working branch Tac_u2m:
   u2_psum_S, u2_psum_rng, u2_zxb_u, u2_first1, u2_fr50_eq, u2_rd_blk, u2_room, u2_cond), one-byte reads of Φ's
   first 50 bytes, the seqz / snez / or values, and the len >= 50 model facts of turn j (is_8819, sum_ok, TF,
   struct P5.1: k = 0 exactly when not is_8819). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_u4.
Import ListNotations.
Open Scope Z_scope.

(* ---- The block sum ---- *)

Lemma u4b_psum_S : forall bs i,
  RcModel.psum bs (S i) = RcModel.psum bs i + bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof. reflexivity. Qed.

Lemma u4b_psum_rng : forall bs i, 0 <= RcModel.psum bs i <= 255 * Z.of_nat i.
Proof.
  intros bs i. induction i as [|i IH]; cbn [RcModel.psum]; [lia|].
  pose proof (u4_byte_rng (nth i bs (Z_to_bv 8 0))). lia.
Qed.

Lemma u4b_zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply MState.unsigned_lit. pose proof (u4_byte_rng b). lia. Qed.

Lemma u4b_first1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma u4b_fr50_eq : forall bs, (50 <= length bs)%nat -> fr50 bs = firstn 50 bs.
Proof.
  intros bs H. unfold fr50. rewrite firstn_app. replace (50 - length bs)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

(* Byte j of the block X = bytes 18 .. 49 of a frame's first 50 bytes, read from the frame in memory. *)
Lemma u4b_rd_blk : forall m phi F j, bytes_at rsegs m phi F -> (50 <= length F)%nat -> (j < 32)%nat ->
  ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j (skipn 18 (fr50 F)) (Z_to_bv 8 0)].
Proof.
  intros m phi F j HB HL Hj. rewrite <- Z.add_assoc.
  rewrite (bytes_at_read rsegs m phi F (18 + Z.of_nat j) 1 HB) by lia.
  replace (Z.to_nat (18 + Z.of_nat j)) with (18 + j)%nat by lia.
  rewrite (u4b_first1 F (18 + j) (Z_to_bv 8 0)) by lia.
  rewrite nth_skipn. rewrite (u4b_fr50_eq F HL). rewrite nth_firstn.
  destruct (Nat.ltb_spec (18 + j) 50); [reflexivity | lia].
Qed.

(* Byte i (i < 50) of a frame's first 50 bytes. *)
Lemma u4b_rd : forall m phi F (i : Z), bytes_at rsegs m phi F -> (50 <= length F)%nat -> 0 <= i < 50 ->
  ov_read_bytes rsegs m (wa (phi + i)) 1 = Some [RcParse.cp_b (fr50 F) (Z.to_nat i)].
Proof.
  intros m phi F i HB HL Hi.
  rewrite (bytes_at_read rsegs m phi F i 1 HB) by lia.
  rewrite (u4b_first1 F (Z.to_nat i) RcParse.cp_z) by lia.
  unfold RcParse.cp_b. rewrite (u4b_fr50_eq F HL). rewrite nth_firstn.
  destruct (Nat.ltb_spec (Z.to_nat i) 50); [reflexivity | lia].
Qed.

(* AF9's room value: `li a1,-18; sub a2,a1,s7; sltiu a3,a2,-17; neg a3,a3; and a2,a3,a2` with s7 = Φ (v1.9; v1.8
   had Φ in s6) gives a2 = 2^64 - 18 - Φ when Φ + 18 does not wrap. *)
Lemma u4b_room : forall phi, 0 <= phi -> phi + 18 < 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_sltiu (Z_to_bv 64 (18446744073709551598 -
      bv_unsigned (Z_to_bv 64 phi))) (-17))))) (bv_unsigned (Z_to_bv 64 (18446744073709551598 -
      bv_unsigned (Z_to_bv 64 phi))))) = Z_to_bv 64 (18446744073709551598 - phi).
Proof.
  intros phi H0 H1.
  unfold v_sltiu.
  rewrite (MState.unsigned_lit phi) by lia.
  rewrite (MState.unsigned_lit (18446744073709551598 - phi)) by lia.
  replace (bv_wrap 64 (-17)) with 18446744073709551599 by (vm_compute; reflexivity).
  rewrite (proj2 (Z.ltb_lt (18446744073709551598 - phi) 18446744073709551599)) by lia.
  cbv beta iota.
  rewrite (MState.unsigned_lit 1) by lia.
  replace (bv_unsigned (Z_to_bv 64 (0 - 1))) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* ---- seqz, snez, or, zext.b ---- *)

Lemma u4b_seqz : forall x, 0 <= x < 2 ^ 64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 (b2z (x =? 0)).
Proof.
  intros x Hx. unfold v_sltiu. rewrite (MState.unsigned_lit x) by lia.
  replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity).
  destruct (Z.eqb_spec x 0) as [->|E]; [reflexivity|].
  rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity.
Qed.

Lemma u4b_seqz_b : forall b : byte, v_sltiu (zxb b) 1 = Z_to_bv 64 (b2z (bv_unsigned b =? 0)).
Proof. intros b. unfold zxb. apply u4b_seqz. pose proof (u4_byte_rng b). lia. Qed.

(* `addi a0,a0,-c; seqz s1,a0` on a byte x: s1 = (x = c). *)
Lemma u4b_seqz_add : forall x c, 0 <= x < 256 -> 0 < c < 256 ->
  v_sltiu (Z_to_bv 64 (x + - c)) 1 = Z_to_bv 64 (b2z (x =? c)).
Proof.
  intros x c Hx Hc. unfold v_sltiu. rewrite MState.unsigned_lit_wrap.
  replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity).
  destruct (Z.eqb_spec x c) as [E|E].
  - replace (x + - c) with 0 by lia. reflexivity.
  - assert (H1 : 1 <= (x + - c) mod 2 ^ 64).
    { destruct (Z_lt_le_dec (x + - c) 0) as [L|L].
      - rewrite <- (Z_mod_plus_full (x + - c) 1 (2 ^ 64)). rewrite Z.mod_small by lia. lia.
      - rewrite Z.mod_small by lia. lia. }
    rewrite (proj2 (Z.ltb_ge _ 1) H1). reflexivity.
Qed.

Lemma u4b_lor_b2z : forall p q : bool,
  Z.lor (bv_unsigned (Z_to_bv 64 (b2z p))) (bv_unsigned (Z_to_bv 64 (b2z q))) = b2z (p || q).
Proof. intros p q. destruct p, q; vm_compute; reflexivity. Qed.

Lemma u4b_land255 : forall x, 0 <= x < 2 ^ 64 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 255 = x mod 256.
Proof.
  intros x Hx. rewrite MState.unsigned_lit by lia. change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

(* ---- Branch conditions ---- *)

Lemma u4b_bne_eq : forall (b : byte) v, 0 <= v < 2 ^ 64 -> bv_unsigned b = v ->
  negb (bv_eqb (zxb b) (Z_to_bv 64 v)) = false.
Proof.
  intros b v Hv E. pose proof (u4_byte_rng b) as Hb. unfold bv_eqb, zxb.
  rewrite !MState.unsigned_lit by lia. rewrite E, Z.eqb_refl. reflexivity.
Qed.

Lemma u4b_bne_neq : forall (b : byte) v, 0 <= v < 2 ^ 64 -> bv_unsigned b <> v ->
  negb (bv_eqb (zxb b) (Z_to_bv 64 v)) = true.
Proof.
  intros b v Hv E. pose proof (u4_byte_rng b) as Hb. unfold bv_eqb, zxb.
  rewrite !MState.unsigned_lit by lia. rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity.
Qed.

(* #42: `snez a0,s9; bne a0,s3` (v1.9; v1.8 s8 / s1) with s9 = k and s3 = e is not taken when (k <> 0) = e. *)
Lemma u4b_bne_snez : forall k e, 0 <= k < 2 ^ 64 -> (k =? 0) = negb e ->
  negb (bv_eqb (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 k)) (Z_to_bv 64 (b2z e))) = false.
Proof.
  intros k e Hk H. unfold v_sltu, c_ltu, bv_ltu. rewrite !MState.unsigned_lit by lia.
  destruct e; cbn [negb] in H.
  - apply Z.eqb_neq in H. rewrite (proj2 (Z.ltb_lt 0 k)) by lia. cbv iota. rewrite bv_eqb_refl. reflexivity.
  - apply Z.eqb_eq in H. subst k. rewrite Z.ltb_irrefl. cbv iota. rewrite bv_eqb_refl. reflexivity.
Qed.

(* A branch decided by unsigned or equality comparisons on Z_to_bv 64 z with z in range. *)
Ltac u4b_cond := unfold_cond; fold_lit_ux; rewrite ?MState.unsigned_lit by lia; solve_cond_rec.
Ltac u4b_if_false :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota | symmetry; u4b_cond]
  end.
Ltac u4b_if_true :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota | symmetry; u4b_cond]
  end.

(* ---- The len >= 50 model facts of turn j ---- *)

Lemma u4b_model : forall inp j, 50 <= t_len inp j ->
  t_big inp j = true /\
  t_8819 inp j = (RcParse.cp_v (t_g inp j) 12 =? 0x88) && (RcParse.cp_v (t_g inp j) 13 =? 0x19) /\
  t_sum_ok inp j = (RcModel.psum (skipn 18 (t_g inp j)) 32 mod 256 =? 0) /\
  t_TF inp j = (RcModel.psum (skipn 18 (t_g inp j)) 32 mod 256 =? 0) ||
               ((RcParse.cp_v (t_g inp j) 16 =? 0) && (RcParse.cp_v (t_g inp j) 17 =? 0)) /\
  (t_k inp j =? 0) = negb ((RcParse.cp_v (t_g inp j) 12 =? 0x88) && (RcParse.cp_v (t_g inp j) 13 =? 0x19)).
Proof.
  intros inp j H.
  assert (Hb : t_big inp j = true) by (unfold t_big; apply Z.leb_le; exact H).
  split; [exact Hb|].
  unfold t_TF, t_8819, t_sum_ok, t_tfill. rewrite Hb. cbn [andb]. unfold RcModel.blocksum.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  unfold t_k.
  destruct (Z.eqb_spec (RcParse.cp_v (t_g inp j) 12) 0x88) as [E12|E12];
    destruct (Z.eqb_spec (RcParse.cp_v (t_g inp j) 13) 0x19) as [E13|E13]; cbn [andb negb].
  - apply Z.eqb_neq. intros E. apply RcParse.ctrlparse_none in E. apply E. tauto.
  - apply Z.eqb_eq. apply RcParse.ctrlparse_none. intros (_ & _ & X). exact (E13 X).
  - apply Z.eqb_eq. apply RcParse.ctrlparse_none. intros (_ & X & _). exact (E12 X).
  - apply Z.eqb_eq. apply RcParse.ctrlparse_none. intros (_ & X & _). exact (E12 X).
Qed.
