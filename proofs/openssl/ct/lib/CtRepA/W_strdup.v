(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApLogic.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA AsStruct RtCallA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Definition CRYPTO_STRDUP : Z := 0x203dd0.
Definition RA_SD_STRLEN : Z := 0x203e04.
Definition RA_SD_MALLOC : Z := 0x203e18.
Definition RA_SD_MEMCPY : Z := 0x203e2c.
(* [comment removed for export] *)
Definition CRYPTO_STRDUP_STACK : Z := 48 + CRYPTO_MALLOC_STACK.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma strlen_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo s : Z) (str slack : list byte) (bsrc : block),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  In bsrc (OW ++ LB) -> blk_addr bsrc <= s -> s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= blk_addr bsrc + blk_size bsrc ->
  bytes_at ctasegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^40 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  a0 = wz s ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz e_strlen) fc None m (seg_rom ctasegs))))
            (ASTA RT Σ PMc (icall_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (Z.of_nat (length str))) Σ OW LB lo 0 0 m (fun _ => True))).
Proof.
  intros until bsrc. intros HEAP ST CEIL LO SPT SP16 MI -> INS S1 S2 HS NONUL HN PAD ->.
  unfold MallocRep.wz in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bsrc HEAP INS) as (BS0 & _ & _ & BSC & _).
  eapply cps_conseq; [ eapply (rc_strlen RT (@ar_RC AR) Σ PMc) with (s := s) (str := str) (slack := slack) (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - exact HS.
  - exact NONUL.
  - exact HN.
  - exact PAD.
  - unfold BnHeapA.ACEIL in *. lia.
  - left. unfold BnHeapA.ACEIL in *. lia.
  - exact (blk_checked_src Σ OW LB m sp lo bsrc s (Z.of_nat (length str) + 1) HEAP INS S1 ltac:(lia) CEIL).
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | unfold USTACK_TOP; lia | exact SP16].
  - intros c Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & _).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold icall_post, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split. { eapply AH_same_ex; [exact HEAP| exact ART2| exact WM2| exact PRES| right; right; lia]. }
    split; [exact WM2|].
    split; [pose proof (AH_frames _ _ _ _ HEAP) as HF; eapply (AH_agree_ex _ _ _ _ _ _ _ _ _ HEAP); rewrite <- HF; exact PRES |].
    exact I.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition strdup_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (lo : Z) (m : mem) (strb : list byte)
    (p : bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' A,
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres LB OW (bv_unsigned sp) m m'
    /\ rt_credit RT Σ - mcost (zlength strb + 1) <= rt_credit RT Σ'
    /\ ablock_range A (zlength strb + 1) /\ AHEAP Σ' ((p, A, zlength strb + 1) :: OW) LB m' /\ acc ctasegs m' A (zlength strb + 1)
    /\ rw_cells ctasegs m' A [CB (S (length strb)) (strb ++ [Z_to_bv 8 0])].

Lemma rw_cells_of_bytes : forall m A bs, bytes_at ctasegs m A bs -> wr_at ctasegs m A (Z.of_nat (length bs)) -> rw_cells ctasegs m A [CB (length bs) bs].
Proof.
  intros m A bs HB HW. split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]|].
  cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact HW.
Qed.

(* [comment removed for export] *)

End WithRT.
