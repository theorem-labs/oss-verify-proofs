(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C7 ECH_AKit ECH_AsKit AsWalk ECH_AC14_bio2buf_seg.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ALD_R1 : Z := 0x5533c0.   (* [comment removed for export] *)
Definition ALD_R2 : Z := 0x5533ec.   (* [comment removed for export] *)
Definition ALD_R3 : Z := 0x553424.   (* [comment removed for export] *)
Definition ALD_RD : Z := 0x55343c.   (* [comment removed for export] *)
Definition ALD_RC : Z := 0x55322c.   (* [comment removed for export] *)
Definition ALD_FAIL : Z := 0x55322c. (* [comment removed for export] *)
Definition ALD_RF : Z := 0x553248.   (* [comment removed for export] *)
Definition ALD_R595 : Z := 0x553260. (* [comment removed for export] *)
Definition ALD_OK : Z := 0x5534bc.   (* [comment removed for export] *)
Definition ALD_RN : Z := 0x553460.   (* [comment removed for export] *)
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
      s6 = Z_to_bv 64 mb -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ARP_R3) fc None m (seg_rom asegs)).
  Proof.
    intros until mb. intros S6 MI. subst s6. unfold ARP_R3, ALD_R1, P_BIO_eof.
    go. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg2_eof :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb e : Z),
      s6 = Z_to_bv 64 mb -> 0 < e < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_RD) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_R1) fc None m (seg_rom asegs)).
  Proof.
    intros until e. intros S6 ER MI. subst s6. unfold ALD_R1, ALD_RD, P_BIO_eof.
    go. br. go. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg2_grow :
    forall (rax gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A rbp K q : Z),
      0 <= K -> K + 1024 < 2^63 -> 0 <= rbp -> rbp + 8 < 2^64 -> 0 <= q -> q + 192 < 2^64 ->
      rw_cells asegs m rbp [C8 (wz 512)] -> rw_cells asegs m (q + 168) [C8 (wz ARP_FILE)] -> rw_cells asegs m (q + 184) [C8 (wz A)] ->
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_R2) (Z_to_bv 64 q) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 A) (Z_to_bv 64 (K + 1024)) (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 128) a4 a5 a6 a7
                       (Z_to_bv 64 512) s3 s4 s5 s6 (Z_to_bv 64 (K + 1024)) s8 (Z_to_bv 64 rbp) (Z_to_bv 64 A) (Z_to_bv 64 K) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_realloc) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 512) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 rbp) s10 (Z_to_bv 64 K) t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_R1) fc None m (seg_rom asegs)).
  Proof.
    intros until q. intros K0 K1 R0 R1 Q0 Q1 RB RF RA MI. unfold ALD_R1, ALD_R2, P_CRYPTO_realloc, ARP_FILE in *. unfold wz in RB, RF, RA.
    go. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg3 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s8 s9 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb A' K : Z),
      s6 = Z_to_bv 64 mb -> 0 < A' < 2^64 -> 0 <= K -> A' + K + 1024 < 2^64 ->
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_R3) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb) (Z_to_bv 64 (A' + K + 1024)) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 512) s3 (Z_to_bv 64 A') (Z_to_bv 64 (- (K + 512))) s6 (Z_to_bv 64 (A' + K + 512)) s8 s9 s10 (Z_to_bv 64 (K + 512)) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 512) s3 s4 (Z_to_bv 64 (- K)) s6 (Z_to_bv 64 (K + 1024)) s8 s9 s10 (Z_to_bv 64 K) t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_R2) fc None m (seg_rom asegs)).
  Proof.
    intros until K. intros S6 AR K0 K1 MI. subst s6. unfold ALD_R2, ALD_R3, P_BIO_eof.
    go. br. go. rewrite zb_lxor_ones by lia. go. step.
    replace (- K + -512) with (- (K + 512)) by lia.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg4 :
    forall (rax gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 v : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb c q : Z),
      s6 = Z_to_bv 64 mb -> 2 <= c <= 32 -> 0 <= q -> q + 192 < 2^64 ->
      rw_cells asegs m (q + 184) [C8 v] -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARP_R3) (Z_to_bv 64 q) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 mb) s7 (Z_to_bv 64 512) s9 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (c - 1)) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_read_ex) fc None m1 (seg_rom asegs)
          /\ munch [(q + 184, q + 192)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (q + 184) [C8 s4])
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 c) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_R3) fc None m (seg_rom asegs)).
  Proof.
    intros until q. intros S6 CR Q0 Q1 RS MI. subst s6. unfold ALD_R3, ARP_R3, P_BIO_read_ex.
    pose proof (munch_refl [(q + 184, q + 192)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. rewrite swrap32_small by lia. replace (c + -1) with (c - 1) by lia. br. go. step.
    apply evt_done. eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact RS.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg4_cap :
    forall (rax gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 v : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb q : Z),
      s6 = Z_to_bv 64 mb -> 0 <= q -> q + 192 < 2^64 ->
      rw_cells asegs m (q + 184) [C8 v] -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ALD_RC) (Z_to_bv 64 q) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 (Z_to_bv 64 0) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m1 (seg_rom asegs)
          /\ munch [(q + 184, q + 192)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (q + 184) [C8 s4])
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 1) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_R3) fc None m (seg_rom asegs)).
  Proof.
    intros until q. intros S6 Q0 Q1 RS MI. subst s6. unfold ALD_R3, ALD_RC, P_BIO_eof.
    pose proof (munch_refl [(q + 184, q + 192)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. step.
    apply evt_done. eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact RS.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_segc1 :
    forall (rax s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 gp tp : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff st mb e s10v : Z) (j0 j1 j2 j3 j4 : list byte),
      0 < e < 2^64 -> 0 <= q -> q + 448 <= 2^64 ->
      rw_cells asegs m q (arp_slotsQ j0 j1 j2 j3 j4 st ff) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ALD_FAIL) (Z_to_bv 64 q) gp tp t0 t1 t2
                       s0w (Z_to_bv 64 q) (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 (Z_to_bv 64 mb) s7 s8 s9 (Z_to_bv 64 s10v) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m1 (seg_rom asegs)
          /\ munch [(q, q + 344)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 q [CB 16 j0; CB 128 j1; C8 (wz (Z.shiftr ff 3 + ASHB + 10)); C8 (wz ff); C8 (wz s10v); CB 8 (skipn 8 j2); C8 (wz ASHB); CB 32 j3; C8 (wz ff); CB 120 j4])
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 (Z_to_bv 64 mb) s7 s8 s9 (Z_to_bv 64 s10v) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ARP_R2) fc None m (seg_rom asegs)).
  Proof.
    intros until j4. intros ER Q1 Q2 SL MI. unfold ARP_R2, ALD_FAIL, P_BIO_eof. unfold ASHB in *.
    pose proof (munch_refl [(q, q + 344)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold arp_slotsQ, wz in SL.
    go. br. go. step.
    apply evt_done. eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    unfold wz, ASHB in *. rewrite <- Z.add_assoc in SL. exact SL.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_segf :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ALD_RF) sp gp tp t0 t1 t2 s0 s1 s4 (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 140) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s4 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_FAIL) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI. unfold ALD_FAIL, ALD_RF, P_CRYPTO_free, ARP_FILE.
    go. step. apply evt_done. reflexivity.
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
    intros until m. intros MI. replace ALD_RC with ALD_FAIL by reflexivity.
    apply ald_segf. exact MI.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_seg5 :
    forall (rax s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 gp tp : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff : Z) (pre : list cell)
           (sa : list byte) (sb : byte) (sc : list byte) (sb2 sc2 : byte) (sd se : list byte) (sr : byte) (sg : list byte),
      0 <= q -> q + 448 <= 2^64 -> AIMG_TOP <= ff -> ff + 4096 <= aceil -> aapp ff 4096 -> aceil <= q ->
      cells_size pre = 152%nat ->
      rw_cells asegs m q (pre ++ [C8 (wz ff); C8 (wz ff)]) ->
      rw_cells asegs m (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sb2 sc2 sd se sr sg) ->
      mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ALD_R595) (Z_to_bv 64 q) gp tp t0 t1 t2
                       s0w (Z_to_bv 64 q) (Z_to_bv 64 (-8)) a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 s6 s7 (Z_to_bv 64 ff) s9 (Z_to_bv 64 ff) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom asegs)
          /\ munch [(Z.shiftr ff 3 + ASHB + 282, Z.shiftr ff 3 + ASHB + 283)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 q (pre ++ [C8 (wz ff); C8 (wz ff)])
          /\ rw_cells asegs m1 (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sb2 sc2 sd se (b8 0xf8) sg))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_RF) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros Q1 Q2 FF1 FF2 AAP CQ SZP SL SHC MI. unfold ALD_RF, ALD_R595, P_ERR_new.
    pose proof (munch_refl [(Z.shiftr ff 3 + ASHB + 282, Z.shiftr ff 3 + ASHB + 283)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ASHB in *.
    acb. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO, ALOWSH_LO in *.
    assert (SHR : Z.shiftr ff 3 = ff / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SL. destruct SL as [SLP SL]. rewrite SZP in SL. change (Z.of_nat 152) with 152 in SL.
    unfold arp_fshadow, wz in *.
    (* [comment removed for export] *)
    go.
    (* [comment removed for export] *)
    step.
    apply evt_done. eexists _. split; [reflexivity|].
    match goal with |- munch [(Z.shiftr ff 3 + ?x, Z.shiftr ff 3 + ?y)] _ _ /\ _ =>
      replace (Z.shiftr ff 3 + x) with (Z.shiftr ff 3 + ASHB + 282) by (unfold ASHB; lia);
      replace (Z.shiftr ff 3 + y) with (Z.shiftr ff 3 + ASHB + 283) by (unfold ASHB; lia) end.
    unfold ASHB.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [| exact SHC].
    apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact SLP|]. rewrite SZP. change (Z.of_nat 152) with 152. exact SL.
  Qed.

  (* [comment removed for export] *)
  Lemma ald_segE_ok :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e rbp n K ff : Z) (sa : list byte) (sb : byte) (sc : list byte) (sb2 sc2 : byte) (sd se : list byte) (sr : byte) (sg : list byte),
      0 < e < 2^64 -> 0 <= n <= 512 -> 0 <= K < 2^62 -> n + K < OSSL_ECH_MAX_ECHCONFIG_LEN -> 0 <= rbp -> rbp + 8 < 2^64 ->
      AIMG_TOP <= ff -> ff + 4096 <= aceil -> aapp ff 4096 -> (rbp + 8 <= Z.shiftr ff 3 + ASHB \/ Z.shiftr ff 3 + ASHB + 512 <= rbp) ->
      rw_cells asegs m rbp [C8 (wz n)] -> rw_cells asegs m (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sb2 sc2 sd se sr sg) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-8)) (Z_to_bv 64 (OSSL_ECH_MAX_ECHCONFIG_LEN - 1)) a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 (Z_to_bv 64 (n + K)) (Z_to_bv 64 n) s8 (Z_to_bv 64 rbp) s10 (Z_to_bv 64 K) t3 t4 t5 t6)
                   F (Z_to_bv 64 ALD_OK) fc None m1 (seg_rom asegs)
          /\ munch [(Z.shiftr ff 3 + ASHB + 282, Z.shiftr ff 3 + ASHB + 283)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 rbp [C8 (wz n)]
          /\ rw_cells asegs m1 (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sb2 sc2 sd se (b8 0xf8) sg))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 s6 s7 s8 (Z_to_bv 64 rbp) s10 (Z_to_bv 64 K) t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_RD) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros ER NR KR GATE R0 R1 FF1 FF2 AAP DJ RB SHC MI. unfold ALD_RD, ALD_OK, OSSL_ECH_MAX_ECHCONFIG_LEN in *.
    pose proof (munch_refl [(Z.shiftr ff 3 + ASHB + 282, Z.shiftr ff 3 + ASHB + 283)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ASHB in *.
    acb. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO, ALOWSH_LO in *.
    assert (SHR : Z.shiftr ff 3 = ff / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    unfold arp_fshadow, wz in *.
    (* [comment removed for export] *)
    go. br. go. br. go_to ALD_OK.
    apply evt_done. eexists _. split; [reflexivity|].
    match goal with |- munch [(Z.shiftr ff 3 + ?x, Z.shiftr ff 3 + ?y)] _ _ /\ _ =>
      replace (Z.shiftr ff 3 + x) with (Z.shiftr ff 3 + ASHB + 282) by (unfold ASHB; lia);
      replace (Z.shiftr ff 3 + y) with (Z.shiftr ff 3 + ASHB + 283) by (unfold ASHB; lia) end.
    unfold ASHB.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact RB| exact SHC].
  Qed.

  (* [comment removed for export] *)
  Lemma ald_segE_big :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e rbp n K ff : Z) (sa : list byte) (sb : byte) (sc : list byte) (sb2 sc2 : byte) (sd se : list byte) (sr : byte) (sg : list byte),
      0 < e < 2^64 -> 0 <= n <= 512 -> 0 <= K < 2^62 -> OSSL_ECH_MAX_ECHCONFIG_LEN <= n + K -> 0 <= rbp -> rbp + 8 < 2^64 ->
      AIMG_TOP <= ff -> ff + 4096 <= aceil -> aapp ff 4096 -> (rbp + 8 <= Z.shiftr ff 3 + ASHB \/ Z.shiftr ff 3 + ASHB + 512 <= rbp) ->
      rw_cells asegs m rbp [C8 (wz n)] -> rw_cells asegs m (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sb2 sc2 sd se sr sg) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ALD_RN) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-8)) (Z_to_bv 64 (OSSL_ECH_MAX_ECHCONFIG_LEN - 1)) a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 (Z_to_bv 64 (n + K)) (Z_to_bv 64 n) s8 (Z_to_bv 64 rbp) s10 (Z_to_bv 64 K) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom asegs)
          /\ munch [(Z.shiftr ff 3 + ASHB + 282, Z.shiftr ff 3 + ASHB + 283)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 rbp [C8 (wz n)]
          /\ rw_cells asegs m1 (Z.shiftr ff 3 + ASHB) (arp_fshadow sa sb sc sb2 sc2 sd se (b8 0xf8) sg))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4 s5 s6 s7 s8 (Z_to_bv 64 rbp) s10 (Z_to_bv 64 K) t3 t4 t5 t6)
            F (Z_to_bv 64 ALD_RD) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros ER NR KR GATE R0 R1 FF1 FF2 AAP DJ RB SHC MI. unfold ALD_RD, ALD_RN, P_ERR_new, OSSL_ECH_MAX_ECHCONFIG_LEN in *.
    pose proof (munch_refl [(Z.shiftr ff 3 + ASHB + 282, Z.shiftr ff 3 + ASHB + 283)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ASHB in *.
    acb. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO, ALOWSH_LO in *.
    assert (SHR : Z.shiftr ff 3 = ff / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    unfold arp_fshadow, wz in *.
    go. br. go. br. go. step.
    apply evt_done. eexists _. split; [reflexivity|].
    match goal with |- munch [(Z.shiftr ff 3 + ?x, Z.shiftr ff 3 + ?y)] _ _ /\ _ =>
      replace (Z.shiftr ff 3 + x) with (Z.shiftr ff 3 + ASHB + 282) by (unfold ASHB; lia);
      replace (Z.shiftr ff 3 + y) with (Z.shiftr ff 3 + ASHB + 283) by (unfold ASHB; lia) end.
    unfold ASHB.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact RB| exact SHC].
  Qed.
End S.
