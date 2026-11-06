(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C7 ECH_AKit ECH_AsKit AsWalk ECH_AC14_bio2buf_seg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import N6_tac.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ALD_R1 : Z := 0x51a540.   (* [comment removed for export] *)
Definition ALD_R2 : Z := 0x51a568.   (* [comment removed for export] *)
Definition ALD_R3 : Z := 0x51a58c.   (* [comment removed for export] *)
Definition ALD_RD : Z := 0x51a5a8.   (* [comment removed for export] *)
Definition ALD_RC : Z := 0x51a604.   (* [comment removed for export] *)
Definition ALD_FAIL : Z := 0x51a3c8. (* [comment removed for export] *)
Definition ALD_RF : Z := 0x51a3e0.   (* [comment removed for export] *)
Definition ALD_R595 : Z := 0x51a3f8. (* [comment removed for export] *)
Definition ALD_OK : Z := 0x51a60c.   (* [comment removed for export] *)
Definition ALD_RN : Z := 0x51a5cc.   (* [comment removed for export] *)
Definition OSSL_ECH_MAX_ECHCONFIG_LEN : Z := 1500.

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.

  (* [comment removed for export] *)
  Lemma ald_seg1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb : Z),
      s2 = Z_to_bv 64 mb -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ARP_R3) fc None m (seg_rom asegs)).
  Proof.
    intros until mb. intros S2 MI. subst s2. unfold ARP_R3, ALD_R1, P_BIO_eof.
    step. step. if_lit. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg2_eof :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb e : Z),
      s2 = Z_to_bv 64 mb -> 0 < e < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_RD) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_R1) fc None m (seg_rom asegs)).
  Proof.
    intros until e. intros S2 ER MI. subst s2. unfold ALD_R1, ALD_RD, P_BIO_eof.
    step. br. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg2_grow :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A rbp K : Z),
      0 <= K -> K + 1024 < 2^63 -> 0 <= rbp -> rbp + 8 < 2^64 ->
      rw_cells asegs m rbp [C8 (wz 512)] -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 (K + 1024)) (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 128) a4 a5 a6 a7
                       s2 s3 s4 s5 (Z_to_bv 64 K) s7 s8 (Z_to_bv 64 rbp) (Z_to_bv 64 A) (Z_to_bv 64 ARP_FILE) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_realloc) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 K) s7 s8 (Z_to_bv 64 rbp) (Z_to_bv 64 A) (Z_to_bv 64 ARP_FILE) t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_R1) fc None m (seg_rom asegs)).
  Proof.
    intros until K. intros K0 K1 R0 R1 RB MI. unfold ALD_R1, ALD_R2, P_CRYPTO_realloc, ARP_FILE. unfold wz in RB.
    step. if_lit.
    st1. step. step. if_lit.
    zstep. step. step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg3 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb A' K : Z),
      s2 = Z_to_bv 64 mb -> 0 < A' < 2^64 -> 0 <= K -> A' + K + 1024 < 2^64 ->
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_R3) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 (Z_to_bv 64 A') (Z_to_bv 64 (- (K + 512))) (Z_to_bv 64 (A' + K)) s7 (Z_to_bv 64 (A' + K + 512)) s9 (Z_to_bv 64 (K + 512)) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (- K)) (Z_to_bv 64 K) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_R2) fc None m (seg_rom asegs)).
  Proof.
    intros until K. intros S2 AR K0 K1 MI. subst s2. unfold ALD_R2, ALD_R3, P_BIO_eof.
    step. br.
    step. zstep. zstep. zstep. zstep. step. step. step.
    replace (- K + -512) with (- (K + 512)) by lia.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg4 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb c : Z),
      s2 = Z_to_bv 64 mb -> 2 <= c <= 32 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ARP_R3) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) s8 (Z_to_bv 64 512) s9 a4 a5 a6 a7
                       s2 s3 s4 s5 s10 (Z_to_bv 64 (c - 1)) s8 s9 s4 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_read_ex) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 c) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_R3) fc None m (seg_rom asegs)).
  Proof.
    intros until c. intros S2 CR MI. subst s2. unfold ALD_R3, ARP_R3, P_BIO_read_ex.
    step. step. step. if_lit.
    zstep. rewrite swrap32_small by lia. replace (c + -1) with (c - 1) by lia.
    step. br.
    step. step. step. step. step. step.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg4_cap :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb : Z),
      s2 = Z_to_bv 64 mb -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_RC) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s10 (Z_to_bv 64 0) s8 s9 s4 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 1) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_R3) fc None m (seg_rom asegs)).
  Proof.
    intros until mb. intros S2 MI. subst s2. unfold ALD_R3, ALD_RC, P_BIO_eof.
    step. step. step. if_lit.
    zstep. step. if_lit.
    step. step. step. step.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_segc1 :
    forall (rax s0w a1 a2 a3 a4 a5 a6 a7 s4 s5 t0 t1 t2 t3 t4 t5 t6 gp tp : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff st mb A e shf s9v s11v : Z) (j0 j1 j2 j3 j4 : list byte),
      0 < e < 2^64 -> 0 <= q -> q + 432 <= 2^64 ->
      rw_cells asegs m q (arp_slotsQ j0 j1 j2 j3 j4 st ff) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ALD_FAIL) (Z_to_bv 64 q) gp tp t0 t1 t2
                       s0w (Z_to_bv 64 q) (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 mb) (Z_to_bv 64 shf) s4 s5 (Z_to_bv 64 ff) (Z_to_bv 64 ff)
                       (Z_to_bv 64 0) (Z_to_bv 64 s9v) (Z_to_bv 64 A) (Z_to_bv 64 s11v) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m1 (seg_rom asegs)
          /\ munch [(q, q + 312)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 q [CB 16 j0; CB 168 j1; C8 (wz 0); C8 (wz st); C8 (wz ff); C8 (wz ff); C8 (wz ASHB); CB 8 j3; C8 (wz ff); CB 72 j4])
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 mb) (Z_to_bv 64 shf) s4 s5 (Z_to_bv 64 ff) (Z_to_bv 64 ff)
                 (Z_to_bv 64 0) (Z_to_bv 64 s9v) (Z_to_bv 64 A) (Z_to_bv 64 s11v) t3 t4 t5 t6)
            F (Z_to_bv 64 ARP_R2) fc None m (seg_rom asegs)).
  Proof.
    intros until j4. intros ER Q1 Q2 SL MI. unfold ARP_R2, ALD_FAIL, P_BIO_eof. unfold ASHB in *.
    pose proof (munch_refl [(q, q + 312)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold arp_slotsQ, wz in SL.
    st1. step. br. step. step. step.
    apply evt_done. eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    unfold wz. exact SL.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_segf :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_RF) sp gp tp t0 t1 t2 s0 s1 s10 (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 140) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_FAIL) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI. unfold ALD_FAIL, ALD_RF, P_CRYPTO_free, ARP_FILE.
    step. step. step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_segc2 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_RF) sp gp tp t0 t1 t2 s0 s1 s4 (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 140) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s4 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_RC) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI. unfold ALD_RC.
    step. step. apply ald_segf. exact MI.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg5 :
    forall (rax s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 gp tp : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff : Z) (pre : list cell) (c216 : cell) (j3 j4 : list byte)
           (sa : list byte) (sb : byte) (sc sd se : list byte) (sr : byte) (sg : list byte),
      0 <= q -> q + 432 <= 2^64 -> AIMG_TOP <= ff -> ff + 4096 <= aceil -> aapp ff 4096 -> aceil <= q ->
      cells_size pre = 200%nat -> csize c216 = 8%nat ->
      rw_cells asegs m q (pre ++ [C8 (wz ff); C8 (wz ff); c216; CB 8 j3; C8 (wz ff); CB 72 j4]) ->
      rw_cells asegs m (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sd se sr sg) ->
      mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ALD_R595) (Z_to_bv 64 q) gp tp t0 t1 t2
                       s0w (Z_to_bv 64 q) (Z_to_bv 64 (-8)) a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 (Z_to_bv 64 ff) (Z_to_bv 64 ff) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom asegs)
          /\ munch [(Z.shiftr ff 3 + ASHB + 280, Z.shiftr ff 3 + ASHB + 281)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 q (pre ++ [C8 (wz ff); C8 (wz ff); c216; CB 8 j3; C8 (wz ff); CB 72 j4])
          /\ rw_cells asegs m1 (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sd se (b8 0xf8) sg))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_RF) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros Q1 Q2 FF1 FF2 AAP CQ SZP SZC SL SHC MI. unfold ALD_RF, ALD_R595, P_ERR_new. unfold ASHB in *.
    acb. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO, ALOWSH_LO in *.
    assert (SHR : Z.shiftr ff 3 = ff / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    pose proof (munch_refl [(Z.shiftr ff 3 + 2147450880 + 280, Z.shiftr ff 3 + 2147450880 + 281)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SL. destruct SL as [SLP SL]. rewrite SZP in SL. change (Z.of_nat 200) with 200 in SL.
    unfold arp_fshadow, wz in *.
    (* [comment removed for export] *)
    st1. st1. step. st1.
    (* [comment removed for export] *)
    step. step.
    apply evt_done. eexists _. split; [reflexivity|].
    replace (Z.shiftr ff 3 + 2147451160) with (Z.shiftr ff 3 + 2147450880 + 280) by lia. replace (Z.shiftr ff 3 + 2147451161) with (Z.shiftr ff 3 + 2147450880 + 281) by lia.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [| exact SHC].
    apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact SLP|]. rewrite SZP. change (Z.of_nat 200) with 200. exact SL.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_segE_ok :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e rbp n K ff : Z) (sa : list byte) (sb : byte) (sc sd se : list byte) (sr : byte) (sg : list byte),
      0 < e < 2^64 -> 0 <= n <= 512 -> 0 <= K < 2^62 -> n + K < OSSL_ECH_MAX_ECHCONFIG_LEN -> 0 <= rbp -> rbp + 8 < 2^64 ->
      AIMG_TOP <= ff -> ff + 4096 <= aceil -> aapp ff 4096 -> (rbp + 8 <= Z.shiftr ff 3 + ASHB \/ Z.shiftr ff 3 + ASHB + 512 <= rbp) ->
      rw_cells asegs m rbp [C8 (wz n)] -> rw_cells asegs m (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sd se sr sg) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-8)) (Z_to_bv 64 OSSL_ECH_MAX_ECHCONFIG_LEN) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (n + K)) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 (Z_to_bv 64 K) s7 (Z_to_bv 64 n) (Z_to_bv 64 rbp) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ALD_OK) fc None m1 (seg_rom asegs)
          /\ munch [(Z.shiftr ff 3 + ASHB + 280, Z.shiftr ff 3 + ASHB + 281)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 rbp [C8 (wz n)]
          /\ rw_cells asegs m1 (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sd se (b8 0xf8) sg))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 (Z_to_bv 64 K) s7 s8 (Z_to_bv 64 rbp) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_RD) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros ER NR KR GATE R0 R1 FF1 FF2 AAP DJ RB SHC MI. unfold ALD_RD, ALD_OK, OSSL_ECH_MAX_ECHCONFIG_LEN in *. unfold ASHB in *.
    acb. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO, ALOWSH_LO in *.
    assert (SHR : Z.shiftr ff 3 = ff / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    pose proof (munch_refl [(Z.shiftr ff 3 + 2147450880 + 280, Z.shiftr ff 3 + 2147450880 + 281)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold arp_fshadow, wz in *.
    (* [comment removed for export] *)
    step. br. st1. step. zstep. step. st1.
    step. if_cases K2; zify_cond K2; [| kill K2]. clear K2.
    apply evt_done. eexists _. split; [reflexivity|].
    replace (Z.shiftr ff 3 + 2147451160) with (Z.shiftr ff 3 + 2147450880 + 280) by lia. replace (Z.shiftr ff 3 + 2147451161) with (Z.shiftr ff 3 + 2147450880 + 281) by lia.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact RB| exact SHC].
  Qed.

  (* [comment removed for export] *)
  Lemma ald_segE_big :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e rbp n K ff : Z) (sa : list byte) (sb : byte) (sc sd se : list byte) (sr : byte) (sg : list byte),
      0 < e < 2^64 -> 0 <= n <= 512 -> 0 <= K < 2^62 -> OSSL_ECH_MAX_ECHCONFIG_LEN <= n + K -> 0 <= rbp -> rbp + 8 < 2^64 ->
      AIMG_TOP <= ff -> ff + 4096 <= aceil -> aapp ff 4096 -> (rbp + 8 <= Z.shiftr ff 3 + ASHB \/ Z.shiftr ff 3 + ASHB + 512 <= rbp) ->
      rw_cells asegs m rbp [C8 (wz n)] -> rw_cells asegs m (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sd se sr sg) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ALD_RN) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-8)) (Z_to_bv 64 OSSL_ECH_MAX_ECHCONFIG_LEN) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (n + K)) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 (Z_to_bv 64 K) s7 (Z_to_bv 64 n) (Z_to_bv 64 rbp) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom asegs)
          /\ munch [(Z.shiftr ff 3 + ASHB + 280, Z.shiftr ff 3 + ASHB + 281)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 rbp [C8 (wz n)]
          /\ rw_cells asegs m1 (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sd se (b8 0xf8) sg))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 (Z_to_bv 64 K) s7 s8 (Z_to_bv 64 rbp) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_RD) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros ER NR KR GATE R0 R1 FF1 FF2 AAP DJ RB SHC MI. unfold ALD_RD, ALD_RN, P_ERR_new, OSSL_ECH_MAX_ECHCONFIG_LEN in *. unfold ASHB in *.
    acb. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO, ALOWSH_LO in *.
    assert (SHR : Z.shiftr ff 3 = ff / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    pose proof (munch_refl [(Z.shiftr ff 3 + 2147450880 + 280, Z.shiftr ff 3 + 2147450880 + 281)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold arp_fshadow, wz in *.
    step. br. st1. step. zstep. step. st1.
    step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
    step. step.
    apply evt_done. eexists _. split; [reflexivity|].
    replace (Z.shiftr ff 3 + 2147451160) with (Z.shiftr ff 3 + 2147450880 + 280) by lia. replace (Z.shiftr ff 3 + 2147451161) with (Z.shiftr ff 3 + 2147450880 + 281) by lia.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact RB| exact SHC].
  Qed.
End S.
