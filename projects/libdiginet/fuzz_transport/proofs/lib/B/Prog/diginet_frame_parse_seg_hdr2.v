(* Proof of fp_hdr2_stmt (diginet_frame_parse_segs.v): the run of diginet_frame_parse in fuzz_frame.asan-ubsan
   from the return of the first rd32 call (FP_RD1R 0x82234, a0 = rd32's result sx32 of the send counter) to the
   second rd32 call (`jal` 0x8258c at 0x82258, ra = FP_RD2R 0x8225c), stepped with StepF's step. It stores the low
   32 bits of a0 at f + 20 and sets a0 = buf + 22. Those 32 bits are the bytes le4 of fr_send b, since
   be32 b 18 < 2^32 (fpbhdr2_be32_range, fpbhdr2_le4_sx32).
   The store follows the check of its shadow byte k at ((f + 20) >> 3) + ASAN_K: the addressable premise of f
   gives k = 0 or (f + 20) mod 8 + 3 < k (fpbhdr1_shk), so the check passes, directly or through the compare of
   its slow path (0x824b4 `andi a3,a1,7; addi a3,a3,3; blt a3,a2`), and errpath_store4 (0x824c4) is not reached.
   The UBSan branch to the unimp word 0x82428 at 0x82250 (`bltu` of 2^64 - 9 against s3 = buf + 14) is not
   taken, by fp_body_pre's buf + length b <= 2^47.
   The store writes only [f, f + 64); the shadow bytes of buf and f lie outside it, so the addressable facts and
   the bytes of buf hold at the new memory (the helpers of diginet_frame_parse_seg_hdr1.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_segs
  diginet_frame_parse_seg_hdr1.
Import ListNotations.
Open Scope Z_scope.

(* ---- the send counter: the bytes of rd32's sign-extended result ---- *)

(* be32 is a 32-bit value. *)
Lemma fpbhdr2_be32_range : forall l i, 0 <= be32 l i < 2^32.
Proof.
  intros l i. unfold be32, at8, bz.
  pose proof (byte_range (nth i l (b8 0))).
  pose proof (byte_range (nth (S i) l (b8 0))).
  pose proof (byte_range (nth (S (S i)) l (b8 0))).
  pose proof (byte_range (nth (S (S (S i))) l (b8 0))).
  lia.
Qed.

(* `sw` stores the low 32 bits of the register: for a 32-bit v, those of sx32 v are the bytes of v. *)
Lemma fpbhdr2_le4_sx32 : forall v, 0 <= v < 2^32 -> le4 (sx32 (Z_to_bv 64 v)) = le4 (Z_to_bv 64 v).
Proof.
  intros v Hv. unfold le4, sx32.
  rewrite (unsigned_lit v) by lia. rewrite unsigned_lit_wrap.
  rewrite (Z_to_le_bytes_mod 4 _ 64) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 v) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 v 32) by (cbn; lia).
  f_equal. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.

Theorem fp_hdr2_holds : fp_hdr2_stmt.
Proof.
  unfold fp_hdr2_stmt.
  intros RNG ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf f b fj LFJ PRE.
  destruct PRE as (FC0 & Hb0 & Hb1 & Hf0 & Hf1 & BB & HC & CS & DJ & ADB & ADF & RB & RF & RSB & RSF).
  pose proof (fr_code_ok b FC0) as (L30 & ET & N16 & NL).
  assert (SR : 0 <= fr_send b < 2^32) by (unfold fr_send; apply fpbhdr2_be32_range).
  fp_lits.
  (* the shadow byte of the 4-byte store at f + 20, on m, and its footprint *)
  destruct (fpbhdr1_shk m f 64 20 4 ADF ltac:(lia) ltac:(lia) ltac:(lia)) as (AP20 & k20 & MK20 & SK20).
  pose proof (fpbhdr1_shrng RNG f 64 20 ltac:(lia) RSF) as RS20.
  (* f and buf as the words in s0 and s2 *)
  assert (Uf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (Ub : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  set (wF := Z_to_bv 64 f) in *. set (wB := Z_to_bv 64 buf) in *. clearbody wF wB.
  subst f buf.
  unfold fp_hdr1_cells in HC. unfold ASAN_K in *.
  pose proof (Z.mod_pos_bound (bv_unsigned wF + 20) 8 ltac:(lia)) as MB20.
  pose proof (munch_refl [(bv_unsigned wF, bv_unsigned wF + 64)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x82234 addi a1, s0, 20; 0x82238 srli a2, a1, 3; 0x8223c add a2, a2, s5; 0x82240 lb a2: the shadow byte
     of f + 20 *)
  step. fpbhdr1_gen wF 20 w20 U20.
  step. gen_shr w20 g20 G20. rewrite U20 in G20.
  step. gen_addi g20 h20 H20.
  fpbhdr1_shload h20 k20 MK20 AP20 RS20.
  (* 0x82244 bnez a2; slow path 0x824b4 andi a3, a1, 7; addi a3, a3, 3; blt a3, a2 back to 0x82248 *)
  fpbhdr1_merge 13 0x8b3f0 x1.
  { step. fpbhdr1_bnez SK20; [apply K | do 3 step; fpbhdr1_slow U20; apply K]. }
  (* 0x82248 li a2, -9; 0x8224c sw a0, 0(a1): the low 32 bits of rd32's result, the send counter, at f + 20 *)
  step.
  fpbhdr1_hs w20 U20 20 4%nat.
  step. clear HS. rewrite (fpbhdr2_le4_sx32 _ SR). fpbhdr1_store 20%nat.
  (* 0x82250 bltu a2, s3: UBSan, taken when 2^64 - 9 < buf + 14 *)
  step. if_cases HU; [fpbhdr1_ub HU|].
  (* 0x82254 addi a0, s2, 22; 0x82258 jal rd32 *)
  step. step.
  (* at rd32: the 64 bytes at f hold fp_hdr2_cells *)
  apply evtF_done. hnf.
  do 8 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  unfold fp_body_pre.
  split; [exact FC0|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact BB|].
  split.
  { eapply fpbhdr1_cells_ext; [exact HC|]. unfold fp_hdr2_cells. rewrite ?skipn_skipn. cbn [Nat.add].
    reflexivity. }
  split; [reflexivity|]. split; [exact DJ|].
  split; [exact (fpbhdr1_addr_tp _ _ _ _ _ MU ADF ADB)|].
  split; [exact (fpbhdr1_addr_tp _ _ _ _ _ MU ADF ADF)|].
  split; [exact RB|]. split; [exact RF|]. split; [exact RSB | exact RSF].
Qed.
