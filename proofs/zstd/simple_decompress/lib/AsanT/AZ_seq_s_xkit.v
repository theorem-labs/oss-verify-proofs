(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_lkit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqd_mcpy_post (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPz D n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPz - MEMCPY_STACK_A, SPz); (D, D + n)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPz /\ stk bsegs m' D (D + n).

Lemma sqd_mcpy_spec : zd_memcpyZ_stmtA ->
  forall (RNG : footprint) (D S n SPz : Z) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem) lo,
  stk bsegs m D (D + n) -> rdbl bsegs m S (S + n) -> (S + n <= D \/ D + n <= S) -> 0 <= n <= 2^40 ->
  stk bsegs m lo SPz -> lo <= SPz - MEMCPY_STACK_A -> SPz < 2^47 ->
  (S + n <= SPz - MEMCPY_STACK_A \/ SPz <= S) -> (D + n <= lo \/ SPz <= D) ->
  app_blk S (S + n) -> aro RNG m S n -> ahull RNG m S n -> app_blk D (D + n) -> aro RNG m D n -> ahull RNG m D n ->
  art m -> astk RNG lo SPz -> mem_inv bsegs m ->
  evtF bsegs RNG (sqd_mcpy_post RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPz D n lo m)
    (MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 APZD_MEMCPY) fc None m (seg_rom bsegs)).
Proof.
  intros MCP RNG D S n SPz ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         STD RDS SEP Hn STK LO SPT SS SD ABS AOS AHS ABD AOD AHD ART AST MI.
  destruct (rdbl_bytes bsegs m S (S + n) RDS ltac:(lia)) as (src & LS & BS). replace (S + n - S) with n in LS by lia.
  destruct (stk_carve bsegs m D (D + n) (Z.to_nat n) STD ltac:(lia)) as [_ (junk & DJ)].
  replace (D + n - Z.of_nat (Z.to_nat n)) with D in DJ by lia.
  unfold zd_memcpyZ_stmtA in MCP.
  eapply evtF_mono.
  - eapply (MCP RNG D S n SPz ra gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo src junk);
      [ exact BS | exact LS | exact DJ | exact SEP | exact Hn | exact STK | exact LO | exact SPT | exact SS | exact SD
      | exact ABS | exact AOS | exact AHS | exact ABD | exact AOD | exact AHD | exact ART | exact AST | exact MI
      | reflexivity | reflexivity | reflexivity ].
  - intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & STK' & DST' & _).
    do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    pose proof (stk_of_rw_cells bsegs _ _ _ DST') as X. cbn [cells_size csize] in X.
    lazymatch type of X with stk _ _ _ ?h => replace h with (D + n) in X by (clear - Hn; lia) end. exact X.
Qed.


(* [comment removed for export] *)
Lemma sqd_aregU_trF : forall RNG (m m' : amem) FF X n,
  aregU RNG m X n -> munch [(FF, FF + 256)] m m' -> 0 <= X -> 0 < n -> X + n <= 2^47 ->
  (FF + 256 <= 2147446784 \/ 17594333495296 <= FF) -> 0 <= FF -> aregU RNG m' X n.
Proof.
  intros RNG m m' FF X n (B & U & R1 & R2) MU X0 Hn Xn FB F0. split; [exact B|]. split; [| split; [exact R1 | exact R2]].
  eapply unp_tr; [exact U | exact MU |]. pose proof (shspan_bounds X n X0 Hn Xn) as (S1 & S2 & S3).
  cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div in *. unfold ASHOFF in *. clear - S1 S2 S3 FB F0 Xn X0 Hn. Z.div_mod_to_equations. lia.
Qed.
Lemma sqd_aregU_trF0 : forall RNG (m m' : amem) FF X n,
  aregU RNG m X n -> munch [(FF, FF + 256)] m m' -> 0 <= X -> 0 <= n -> X + n <= 2^47 ->
  (FF + 256 <= 2147446784 \/ 17594333495296 <= FF) -> 0 <= FF -> aregU RNG m' X n.
Proof.
  intros RNG m m' FF X n A MU X0 Hn Xn FB F0. destruct (Z.eq_dec n 0) as [E|NZ].
  - subst n. destruct A as (B & U & R1 & R2). split; [exact B|]. split; [| split; [exact R1 | exact R2]].
    destruct U as (U1 & U2 & _). split; [exact U1|]. split; [exact U2|]. intros G HG. exfalso. clear - HG. lia.
  - eapply sqd_aregU_trF; [exact A | exact MU | exact X0 | clear - Hn NZ; lia | exact Xn | exact FB | exact F0].
Qed.
Lemma sqd_ahull_tr : forall RNG (m m' : amem) X n, ahull RNG m X n -> wmono bsegs m m' -> ahull RNG m' X n.
Proof.
  intros RNG m m' X n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W0 & R) WM. exists RLO, RHI.
  do 6 (split; [assumption|]). split; [eapply wr_at_transport; [exact W0 | exact WM] | exact R].
Qed.
Lemma sqd_art_trF : forall (m m' : amem) FF, art m -> munch [(FF, FF + 256)] m m' -> wmono bsegs m m' -> 6443008 <= FF -> art m'.
Proof.
  intros m m' FF (G1 & G2 & G3 & G4 & G5 & G6) MU WM HF.
  assert (TC : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= 6443008 -> rw_cells bsegs m' A cs).
  { intros A cs H HA. eapply rw_cells_transport; [exact H | exact MU | exact WM | cbn [disjoint_from]; split; [clear - HA HF; lia | exact I]]. }
  unfold art. split; [apply TC; [exact G1 | cbn; clear; lia]|]. split; [apply TC; [exact G2 | cbn; clear; lia]|].
  split; [apply TC; [exact G3 | cbn; clear; lia]|]. split; [apply TC; [exact G4 | cbn; clear; lia]|].
  split; [apply TC; [exact G5 | cbn; clear; lia]|]. apply TC; [exact G6 | cbn; clear; lia].
Qed.

Lemma sqd_dctx_cells_tr : forall W (m1 m2 : amem) A cs,
  rw_cells bsegs m1 A cs -> munch W m1 m2 -> wmono bsegs m1 m2 -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells bsegs m2 A cs.
Proof. intros W m1 m2 A cs H MU WM D. eapply rw_cells_transport; [exact H | exact MU | exact WM | exact D]. Qed.


Lemma bytes_at_sh2 : forall (m : amem) A A1 (l0 l1 : list byte) b0 b1,
  l0 = [b0] -> l1 = [b1] -> rdn bsegs m (wa A) 1 = Some l0 -> rdn bsegs m (wa A1) 1 = Some l1 ->
  A1 = A + 1 -> 0 <= A -> A + 2 <= 2^64 -> bytes_at bsegs m A [b0; b1].
Proof.
  intros m A A1 l0 l1 b0 b1 -> -> H0 H1 -> HA HB. split; [exact HA|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|i]]; [ | | lia].
  - rewrite Z.add_0_r. unfold mrd. cbn [rdn] in H0. cbn [nth_error].
    destruct (m (wa A)) as [b|]; [congruence|]. destruct (seg_rom bsegs (wa A)) as [b|]; congruence.
  - change (A + Z.of_nat 1) with (A + 1). unfold mrd. cbn [rdn] in H1. cbn [nth_error].
    destruct (m (wa (A + 1))) as [b|]; [congruence|]. destruct (seg_rom bsegs (wa (A + 1))) as [b|]; congruence.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_sh1 : forall (m : amem) A (l0 : list byte) b0,
  l0 = [b0] -> rdn bsegs m (wa A) 1 = Some l0 -> 0 <= A -> A + 1 <= 2^64 -> bytes_at bsegs m A [b0].
Proof.
  intros m A l0 b0 -> H0 HA HB. split; [exact HA|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. destruct i as [|i]; [ | lia].
  rewrite Z.add_0_r. unfold mrd. cbn [rdn] in H0. cbn [nth_error].
  destruct (m (wa A)) as [b|]; [congruence|]. destruct (seg_rom bsegs (wa A)) as [b|]; congruence.
Qed.

(* [comment removed for export] *)
Lemma sqs_loc_shadow : forall RNG (m : amem) DCTX D8, areg RNG m DCTX 95992 -> DCTX = 8 * D8 ->
  rdn bsegs m (wa (2147450880 + D8 + 3796)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof.
  intros RNG m DCTX D8 AD ED8. destruct (AD ltac:(clear; lia)) as (_ & UD & _).
  assert (Z0 : m (wa (shad (DCTX + 30368))) = Some (Z_to_bv 8 0)) by (eapply (unp_shadow_zero m DCTX 95992); [exact UD | clear; lia | clear - ED8; Z.div_mod_to_equations; lia]).
  rewrite shad_div in Z0. unfold ASHOFF in Z0. replace ((DCTX + 30368) / 8) with (D8 + 3796) in Z0 by (clear - ED8; Z.div_mod_to_equations; lia).
  cbn [rdn]. replace (2147450880 + D8 + 3796) with (2147450880 + (D8 + 3796)) by lia. rewrite Z0. reflexivity.
Qed.

End CANSEC1.
