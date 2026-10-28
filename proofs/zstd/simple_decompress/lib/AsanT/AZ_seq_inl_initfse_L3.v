(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable AsanEmbed.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_kx AZ_globals AZ_globalsR AZ_huf_iface AZ_seq_bit_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
Ltac kx_pull ::= kx_pull1; kx_pull1.
Ltac kx_lia ::= kx_bv_ranges; solve [kx_lia_pruned].

Section CANSEC1. Context {rc : runConstT}.

Definition SQ_INL_INITFSE_L3_ENTRY : Z := 0x8a4b0.
Definition SQ_INL_INITFSE_L3_EXIT : Z := 0x8a648.

Definition sq_inl_initfse_L3_post (ra sp gp tp t0 t2 s0 s4 s6 s9 s10 a6 t3 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (FRB BD T SEQ n B tl TP NS P224 P232 : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a7 s11 t4 t5 m' cw' bc' jpad' ptr' st,
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 SBITMASK) t2 s0 (Z_to_bv 64 FRB) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 ASHOFF) (Z_to_bv 64 SEQ) s4 (Z_to_bv 64 BD) s6 (Z_to_bv 64 TP) (Z_to_bv 64 NS) s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 SQ_INL_INITFSE_L3_EXIT) fc None m' (seg_rom bsegs)
    /\ munch [(BD, BD + 40); (BD + 72, BD + 88); (FRB + 136, FRB + 152); (FRB + 176, FRB + 208); (FRB + 272, FRB + 280); (FRB + 296, FRB + 304)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' BD (sbd_cells cw' bc' jpad' ptr' SEQ)
    /\ rw_cells bsegs m' (BD + 72) [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (T + 8))]
    /\ rw_cells bsegs m' (FRB + 136) [C8 (Z_to_bv 64 (NS - 1)); C8 s6]
    /\ rw_cells bsegs m' (FRB + 176) [C8 (Z_to_bv 64 NS); C8 t6; C8 (Z_to_bv 64 TP); C8 s9]
    /\ rw_cells bsegs m' (FRB + 272) [C8 (Z_to_bv 64 (T + 8))]
    /\ rw_cells bsegs m' (FRB + 296) [C8 (Z_to_bv 64 SBITMASK)]
    /\ a0 = Z_to_bv 64 P232 /\ a1 = Z_to_bv 64 (NS - 1) /\ s11 = Z_to_bv 64 (P232 - P224) /\ t4 = Z_to_bv 64 st /\ t5 = Z_to_bv 64 (T + 8)
    /\ 0 <= st < 2^tl /\ 0 <= bc' <= B + 9 /\ bit_okS SEQ n bc' ptr'.

Definition sq_inl_initfse_L3_stmt_if (CND : Z -> Z -> Z -> Z -> Z -> Prop) : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t2 s0 a2 a3 a4 a5 a6 a7 s4 s6 s9 s10 s11 t3 t4 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (FRB BD T SEQ B bc ptr TP NS P224 P232 : Z)
         (cw st0 tb0 c136 c144 c176 c184 c192 c200 c272 c296 : word) (jpad sqb : list byte)
         (k : seq_kind) (t : seq_table),
  rw_cells bsegs m BD (sbd_cells cw bc jpad ptr SEQ) -> rw_cells bsegs m (BD + 72) [C8 st0; C8 tb0] ->
  rw_cells bsegs m (FRB + 136) [C8 c136; C8 c144] -> rw_cells bsegs m (FRB + 176) [C8 c176; C8 c184; C8 c192; C8 c200] ->
  rw_cells bsegs m (FRB + 224) [C8 (Z_to_bv 64 P224); C8 (Z_to_bv 64 P232)] ->
  rw_cells bsegs m (FRB + 272) [C8 c272] -> rw_cells bsegs m (FRB + 296) [C8 c296] ->
  bytes_at bsegs m T (map (Z_to_bv 8) (seq_table_bytes t)) -> seq_table_ok k t ->
  bytes_at bsegs m SEQ sqb ->
  4096 <= BD -> BD + 88 < 2^47 -> 4096 <= T -> T + 8 * (1 + 2^(st_log t)) < 2^47 ->
  4096 <= SEQ -> SEQ + Z.of_nat (length sqb) < 2^47 -> 1 <= Z.of_nat (length sqb) ->
  4096 <= FRB -> FRB + 304 < 2^47 -> KHIGH <= FRB -> 4096 <= TP -> TP + 24 < 2^47 ->
  1 <= NS < 2^31 -> 0 <= P224 < 2^64 -> 0 <= P232 < 2^64 ->
  BD mod 8 = 0 -> T mod 4 = 0 -> FRB mod 8 = 0 ->
  (BD + 88 <= SEQ \/ SEQ + Z.of_nat (length sqb) <= BD) -> (BD + 88 <= T \/ T + 8 * (1 + 2^(st_log t)) <= BD) ->
  (BD + 88 <= FRB + 136 \/ FRB + 304 <= BD) -> (FRB + 304 <= SEQ \/ SEQ + Z.of_nat (length sqb) <= FRB + 136) ->
  (FRB + 304 <= T \/ T + 8 * (1 + 2^(st_log t)) <= FRB + 136) ->
  0 <= bc <= B -> B <= 82 -> bit_okS SEQ (Z.of_nat (length sqb)) bc ptr ->
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> app_blk (BD + 72) (BD + 88) -> aro RNG m (BD + 72) 16 ->
  app_blk (FRB + 136) (FRB + 152) -> rng RNG (FRB + 136) 16 -> app_blk (FRB + 176) (FRB + 208) -> rng RNG (FRB + 176) 32 ->
  rng RNG (FRB + 224) 16 -> app_blk (FRB + 272) (FRB + 280) -> rng RNG (FRB + 272) 8 ->
  app_blk (FRB + 296) (FRB + 304) -> rng RNG (FRB + 296) 8 ->
  aro RNG m SEQ (Z.of_nat (length sqb)) -> aro RNG m T (8 * (1 + 2^(st_log t))) -> aro_client RNG m ->
  art m -> mem_inv bsegs m ->
  CND bc (st_log t) ptr SEQ (Z.of_nat (length sqb)) ->
  evtF bsegs RNG (sq_inl_initfse_L3_post ra sp gp tp t0 t2 s0 s4 s6 s9 s10 a6 t3 t6 F fc FRB BD T SEQ (Z.of_nat (length sqb)) B (st_log t) TP NS P224 P232 m)
      (MS (mkR ra sp gp tp t0 (Z_to_bv 64 SBITMASK) t2 s0 (Z_to_bv 64 FRB) (Z_to_bv 64 (T + 4)) (Z_to_bv 64 (SEQ + 8)) a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 ASHOFF) (Z_to_bv 64 SEQ) s4 (Z_to_bv 64 BD) s6 (Z_to_bv 64 TP) (Z_to_bv 64 NS) s9 s10 s11 t3 t4 (Z_to_bv 64 T) t6)
          F (Z_to_bv 64 SQ_INL_INITFSE_L3_ENTRY) fc None m (seg_rom bsegs)).

Definition sq_inl_initfse_L3_stmt : Prop := sq_inl_initfse_L3_stmt_if (fun _ _ _ _ _ => True).

Ltac sq_inl_initfse_L3_close :=
  apply evtF_done; unfold sq_inl_initfse_L3_post, sbd_cells;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [match goal with H : rw_cells _ _ ?B (C8 _ :: C4 _ :: _) |- rw_cells _ _ ?B2 _ => constr_eq B B2; exact H end|];
  do 5 (split; [match goal with H : rw_cells _ _ ?S _ |- rw_cells _ _ ?S2 _ => constr_eq S S2; exact H end|]);
  do 5 (split; [first [reflexivity | (unfold SBITMASK; reflexivity) | (f_equal; lia) | idtac]|]);
  split; [apply sland_mask_lt; lia|]; split; [lia|]; unfold bit_okS; intros; lia.

Lemma sq_inl_initfse_L3_c1 : sq_inl_initfse_L3_stmt_if (fun bc tl ptr SEQ n => 65 <= bc + tl).
Proof.
  unfold sq_inl_initfse_L3_stmt_if, SQ_INL_INITFSE_L3_ENTRY. intros until t.
  intros HBD HST HF1 HF2 HFR HF3 HF4 TB OK SQB R1 R2 R3 R4 R5 R5b R6 R7 R8 RFH R9 R10 R11 R12 R13 A1 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5 RB RBB IB APB AROB APS AROST APF1 RGF1 APF2 RGF2 RGFR APF3 RGF3 APF4 RGF4 AROS AROT ACL ART MI C. cbv beta in C. unfold KHIGH in RFH.
  pose proof (seq_rdn_log bsegs m T k t TB OK) as RL. pose proof (seq_tl_range k t OK) as RT.
  remember (st_log t) as tl eqn:Etl.
  pose proof (sbitmask_know m tl MI ltac:(clear - RT; lia)) as BK. unfold SBITMASK in BK. change (0x22180) with 139648 in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROST as (UST & RGST & RGSTS). destruct AROS as (US & RGS & RGSS). destruct AROT as (UT & RGT & RGTS).
  pose proof (aro_client_at RNG m 139648 128 ACL ltac:(cbn [ACLIENT_RO In]; tauto)) as (UM & RGM & RGMS).
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (SPB2 : BD + 88 <= 0x7fff8000 \/ 0x10007fff8000 <= BD + 72) by (unfold app_blk, KLOW, KHIGH, KEND in APS; clear - APS; lia).
  assert (FRBB1 : FRB + 152 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 136) by (unfold app_blk, KLOW, KHIGH, KEND in APF1; clear - APF1; lia).
  assert (FRBB2 : FRB + 208 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 176) by (unfold app_blk, KLOW, KHIGH, KEND in APF2; clear - APF2; lia).
  assert (FRBB3 : FRB + 280 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 272) by (unfold app_blk, KLOW, KHIGH, KEND in APF3; clear - APF3; lia).
  assert (FRBB4 : FRB + 304 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 296) by (unfold app_blk, KLOW, KHIGH, KEND in APF4; clear - APF4; lia).
  assert (MU : munch [(BD, BD + 40); (BD + 72, BD + 88); (FRB + 136, FRB + 152); (FRB + 176, FRB + 208); (FRB + 272, FRB + 280); (FRB + 296, FRB + 304)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (RG : 4096 <= BD < 2^47 /\ 4096 <= SEQ < 2^47 /\ 4096 <= SEQ + n < 2^47) by lia.
  assert (T16 : 16 <= 8 * (1 + 2^tl)) by (clear - RP; lia).
  assert (UT16 : unpoisoned m T (T + 16)) by (eapply unpoisoned_sub; [exact UT | lia | clear - T16; lia]).
  assert (RGT16 : rng RNG T 16) by (eapply rng_sub'; [exact RGT | clear - T16; lia]).
  assert (RGTS16 : rng RNG (shad T) (shspan T 16))
    by (pose proof (shspan_sub T (8 * (1 + 2^tl)) T 16 ltac:(lia) ltac:(lia) ltac:(clear - T16; lia)) as [SS1 SS2];
        eapply rng_sub'; [exact RGTS | split; [exact SS1 | exact SS2]]).
  clear UT RGT RGTS.
  unfold sbd_cells in HBD. unfold bit_okS in IB.
  clear TB ACL APB APS APF1 APF2 APF3 APF4.
  unfold SBITMASK.
  hide DJ1. hide DJ2. hide DJ3. hide DJ4. hide DJ5.

  kx_autoFLAx [KAUnp BD 40; KAUnp (BD + 72) 16; KAUnp SEQ n; KAUnp T 16; KAUnp 139648 128; KAApp BD 40; KAApp (BD + 72) 16; KAApp (FRB + 136) 16; KAApp (FRB + 176) 32; KAApp (FRB + 272) 8; KAApp (FRB + 296) 8] [SQ_INL_INITFSE_L3_EXIT] 400%nat
      [KZRange bc 0 82; KZRange (bc + tl) 65 91; KZRange n 1 (2^47);
       KZRange BD 4096 (2^47 - 88); KZRange FRB 4096 (2^47 - 304); KZRange TP 4096 (2^47 - 24); KZRange NS 1 (2^31 - 1); KZRange P224 0 (2^64 - 1); KZRange P232 0 (2^64 - 1); KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4; KZAlign FRB 8;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 72) 16; KZWr (FRB + 136) 16; KZWr (FRB + 176) 32; KZWr (FRB + 272) 8; KZWr (FRB + 296) 8;
       KZDisj BD 40 (BD + 72) 16; KZDisj BD 40 (FRB + 136) 16; KZDisj BD 40 (FRB + 176) 32; KZDisj BD 40 (FRB + 272) 8; KZDisj BD 40 (FRB + 296) 8; KZDisj (BD + 72) 16 (FRB + 136) 16; KZDisj (BD + 72) 16 (FRB + 176) 32; KZDisj (BD + 72) 16 (FRB + 272) 8; KZDisj (BD + 72) 16 (FRB + 296) 8; KZDisj (FRB + 136) 16 (FRB + 176) 32; KZDisj (FRB + 136) 16 (FRB + 272) 8; KZDisj (FRB + 136) 16 (FRB + 296) 8; KZDisj (FRB + 176) 32 (FRB + 272) 8; KZDisj (FRB + 176) 32 (FRB + 296) 8; KZDisj (FRB + 272) 8 (FRB + 296) 8; KZDisj BD 40 SEQ n; KZDisj BD 40 T 16; KZDisj BD 40 (FRB + 224) 16; KZDisj (BD + 72) 16 SEQ n; KZDisj (BD + 72) 16 T 16; KZDisj (BD + 72) 16 (FRB + 224) 16; KZDisj (FRB + 136) 16 SEQ n; KZDisj (FRB + 136) 16 T 16; KZDisj (FRB + 136) 16 (FRB + 224) 16; KZDisj (FRB + 176) 32 SEQ n; KZDisj (FRB + 176) 32 T 16; KZDisj (FRB + 176) 32 (FRB + 224) 16; KZDisj (FRB + 272) 8 SEQ n; KZDisj (FRB + 272) 8 T 16; KZDisj (FRB + 272) 8 (FRB + 224) 16; KZDisj (FRB + 296) 8 SEQ n; KZDisj (FRB + 296) 8 T 16; KZDisj (FRB + 296) 8 (FRB + 224) 16]
      [(SEQ, n); (BD, 40); (BD + 72, 16); (FRB + 136, 16); (FRB + 176, 32); (FRB + 272, 8); (FRB + 296, 8); (FRB + 224, 16)] [(BD, 40); (BD + 72, 16); (FRB + 136, 16); (FRB + 176, 32); (FRB + 272, 8); (FRB + 296, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGST | kx_acc RGB | kx_acc RGS | kx_acc RGT16 | kx_acc RGM | kx_acc RGF1 | kx_acc RGF2 | kx_acc RGF3 | kx_acc RGF4 | kx_acc RGFR | kx_acc RGBS | kx_acc RGSS | kx_acc RGTS16 | kx_acc RGMS | kx_acc RGSTS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => try kx_side_pre;
            lazymatch goal with |- _ /\ _ /\ (?A + _ <= ?B \/ _) =>
              let X := base_of A in let Y := base_of B in unhide_related X Y;
              repeat match goal with H : hidden _ |- _ => clear H end; repeat split; lia end end).
  all: unhide.
  all: kx_mem.
  all: kx_abs.
  all: kx_mkR_fold.
  all: sq_inl_initfse_L3_close.
Qed.

Lemma sq_inl_initfse_L3_c2 : sq_inl_initfse_L3_stmt_if (fun bc tl ptr SEQ n => bc + tl <= 64 /\ ptr = SEQ).
Proof.
  unfold sq_inl_initfse_L3_stmt_if, SQ_INL_INITFSE_L3_ENTRY. intros until t.
  intros HBD HST HF1 HF2 HFR HF3 HF4 TB OK SQB R1 R2 R3 R4 R5 R5b R6 R7 R8 RFH R9 R10 R11 R12 R13 A1 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5 RB RBB IB APB AROB APS AROST APF1 RGF1 APF2 RGF2 RGFR APF3 RGF3 APF4 RGF4 AROS AROT ACL ART MI C. cbv beta in C. unfold KHIGH in RFH.
  pose proof (seq_rdn_log bsegs m T k t TB OK) as RL. pose proof (seq_tl_range k t OK) as RT.
  remember (st_log t) as tl eqn:Etl.
  pose proof (sbitmask_know m tl MI ltac:(clear - RT; lia)) as BK. unfold SBITMASK in BK. change (0x22180) with 139648 in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROST as (UST & RGST & RGSTS). destruct AROS as (US & RGS & RGSS). destruct AROT as (UT & RGT & RGTS).
  pose proof (aro_client_at RNG m 139648 128 ACL ltac:(cbn [ACLIENT_RO In]; tauto)) as (UM & RGM & RGMS).
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (SPB2 : BD + 88 <= 0x7fff8000 \/ 0x10007fff8000 <= BD + 72) by (unfold app_blk, KLOW, KHIGH, KEND in APS; clear - APS; lia).
  assert (FRBB1 : FRB + 152 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 136) by (unfold app_blk, KLOW, KHIGH, KEND in APF1; clear - APF1; lia).
  assert (FRBB2 : FRB + 208 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 176) by (unfold app_blk, KLOW, KHIGH, KEND in APF2; clear - APF2; lia).
  assert (FRBB3 : FRB + 280 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 272) by (unfold app_blk, KLOW, KHIGH, KEND in APF3; clear - APF3; lia).
  assert (FRBB4 : FRB + 304 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 296) by (unfold app_blk, KLOW, KHIGH, KEND in APF4; clear - APF4; lia).
  assert (MU : munch [(BD, BD + 40); (BD + 72, BD + 88); (FRB + 136, FRB + 152); (FRB + 176, FRB + 208); (FRB + 272, FRB + 280); (FRB + 296, FRB + 304)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (RG : 4096 <= BD < 2^47 /\ 4096 <= SEQ < 2^47 /\ 4096 <= SEQ + n < 2^47) by lia.
  assert (T16 : 16 <= 8 * (1 + 2^tl)) by (clear - RP; lia).
  assert (UT16 : unpoisoned m T (T + 16)) by (eapply unpoisoned_sub; [exact UT | lia | clear - T16; lia]).
  assert (RGT16 : rng RNG T 16) by (eapply rng_sub'; [exact RGT | clear - T16; lia]).
  assert (RGTS16 : rng RNG (shad T) (shspan T 16))
    by (pose proof (shspan_sub T (8 * (1 + 2^tl)) T 16 ltac:(lia) ltac:(lia) ltac:(clear - T16; lia)) as [SS1 SS2];
        eapply rng_sub'; [exact RGTS | split; [exact SS1 | exact SS2]]).
  clear UT RGT RGTS.
  unfold sbd_cells in HBD. unfold bit_okS in IB.
  clear TB ACL APB APS APF1 APF2 APF3 APF4.
  unfold SBITMASK.
  hide DJ1. hide DJ2. hide DJ3. hide DJ4. hide DJ5.
    destruct C as (C1 & C2). subst ptr.
  kx_autoFLAx [KAUnp BD 40; KAUnp (BD + 72) 16; KAUnp SEQ n; KAUnp T 16; KAUnp 139648 128; KAApp BD 40; KAApp (BD + 72) 16; KAApp (FRB + 136) 16; KAApp (FRB + 176) 32; KAApp (FRB + 272) 8; KAApp (FRB + 296) 8] [SQ_INL_INITFSE_L3_EXIT] 400%nat
      [KZRange bc 0 64; KZRange (bc + tl) 0 64; KZRange n 1 (2^47);
       KZRange BD 4096 (2^47 - 88); KZRange FRB 4096 (2^47 - 304); KZRange TP 4096 (2^47 - 24); KZRange NS 1 (2^31 - 1); KZRange P224 0 (2^64 - 1); KZRange P232 0 (2^64 - 1); KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4; KZAlign FRB 8;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 72) 16; KZWr (FRB + 136) 16; KZWr (FRB + 176) 32; KZWr (FRB + 272) 8; KZWr (FRB + 296) 8;
       KZDisj BD 40 (BD + 72) 16; KZDisj BD 40 (FRB + 136) 16; KZDisj BD 40 (FRB + 176) 32; KZDisj BD 40 (FRB + 272) 8; KZDisj BD 40 (FRB + 296) 8; KZDisj (BD + 72) 16 (FRB + 136) 16; KZDisj (BD + 72) 16 (FRB + 176) 32; KZDisj (BD + 72) 16 (FRB + 272) 8; KZDisj (BD + 72) 16 (FRB + 296) 8; KZDisj (FRB + 136) 16 (FRB + 176) 32; KZDisj (FRB + 136) 16 (FRB + 272) 8; KZDisj (FRB + 136) 16 (FRB + 296) 8; KZDisj (FRB + 176) 32 (FRB + 272) 8; KZDisj (FRB + 176) 32 (FRB + 296) 8; KZDisj (FRB + 272) 8 (FRB + 296) 8; KZDisj BD 40 SEQ n; KZDisj BD 40 T 16; KZDisj BD 40 (FRB + 224) 16; KZDisj (BD + 72) 16 SEQ n; KZDisj (BD + 72) 16 T 16; KZDisj (BD + 72) 16 (FRB + 224) 16; KZDisj (FRB + 136) 16 SEQ n; KZDisj (FRB + 136) 16 T 16; KZDisj (FRB + 136) 16 (FRB + 224) 16; KZDisj (FRB + 176) 32 SEQ n; KZDisj (FRB + 176) 32 T 16; KZDisj (FRB + 176) 32 (FRB + 224) 16; KZDisj (FRB + 272) 8 SEQ n; KZDisj (FRB + 272) 8 T 16; KZDisj (FRB + 272) 8 (FRB + 224) 16; KZDisj (FRB + 296) 8 SEQ n; KZDisj (FRB + 296) 8 T 16; KZDisj (FRB + 296) 8 (FRB + 224) 16]
      [(SEQ, n); (BD, 40); (BD + 72, 16); (FRB + 136, 16); (FRB + 176, 32); (FRB + 272, 8); (FRB + 296, 8); (FRB + 224, 16)] [(BD, 40); (BD + 72, 16); (FRB + 136, 16); (FRB + 176, 32); (FRB + 272, 8); (FRB + 296, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGST | kx_acc RGB | kx_acc RGS | kx_acc RGT16 | kx_acc RGM | kx_acc RGF1 | kx_acc RGF2 | kx_acc RGF3 | kx_acc RGF4 | kx_acc RGFR | kx_acc RGBS | kx_acc RGSS | kx_acc RGTS16 | kx_acc RGMS | kx_acc RGSTS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => try kx_side_pre;
            lazymatch goal with |- _ /\ _ /\ (?A + _ <= ?B \/ _) =>
              let X := base_of A in let Y := base_of B in unhide_related X Y;
              repeat match goal with H : hidden _ |- _ => clear H end; repeat split; lia end end).
  all: unhide.
  all: kx_mem.
  all: kx_abs.
  all: kx_mkR_fold.
  all: sq_inl_initfse_L3_close.
Qed.

Lemma sq_inl_initfse_L3_c3 : sq_inl_initfse_L3_stmt_if (fun bc tl ptr SEQ n => bc + tl <= 64 /\ 8 <= n /\ SEQ + 8 <= ptr <= SEQ + n - 8).
Proof.
  unfold sq_inl_initfse_L3_stmt_if, SQ_INL_INITFSE_L3_ENTRY. intros until t.
  intros HBD HST HF1 HF2 HFR HF3 HF4 TB OK SQB R1 R2 R3 R4 R5 R5b R6 R7 R8 RFH R9 R10 R11 R12 R13 A1 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5 RB RBB IB APB AROB APS AROST APF1 RGF1 APF2 RGF2 RGFR APF3 RGF3 APF4 RGF4 AROS AROT ACL ART MI C. cbv beta in C. unfold KHIGH in RFH.
  pose proof (seq_rdn_log bsegs m T k t TB OK) as RL. pose proof (seq_tl_range k t OK) as RT.
  remember (st_log t) as tl eqn:Etl.
  pose proof (sbitmask_know m tl MI ltac:(clear - RT; lia)) as BK. unfold SBITMASK in BK. change (0x22180) with 139648 in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROST as (UST & RGST & RGSTS). destruct AROS as (US & RGS & RGSS). destruct AROT as (UT & RGT & RGTS).
  pose proof (aro_client_at RNG m 139648 128 ACL ltac:(cbn [ACLIENT_RO In]; tauto)) as (UM & RGM & RGMS).
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (SPB2 : BD + 88 <= 0x7fff8000 \/ 0x10007fff8000 <= BD + 72) by (unfold app_blk, KLOW, KHIGH, KEND in APS; clear - APS; lia).
  assert (FRBB1 : FRB + 152 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 136) by (unfold app_blk, KLOW, KHIGH, KEND in APF1; clear - APF1; lia).
  assert (FRBB2 : FRB + 208 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 176) by (unfold app_blk, KLOW, KHIGH, KEND in APF2; clear - APF2; lia).
  assert (FRBB3 : FRB + 280 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 272) by (unfold app_blk, KLOW, KHIGH, KEND in APF3; clear - APF3; lia).
  assert (FRBB4 : FRB + 304 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 296) by (unfold app_blk, KLOW, KHIGH, KEND in APF4; clear - APF4; lia).
  assert (MU : munch [(BD, BD + 40); (BD + 72, BD + 88); (FRB + 136, FRB + 152); (FRB + 176, FRB + 208); (FRB + 272, FRB + 280); (FRB + 296, FRB + 304)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (RG : 4096 <= BD < 2^47 /\ 4096 <= SEQ < 2^47 /\ 4096 <= SEQ + n < 2^47) by lia.
  assert (T16 : 16 <= 8 * (1 + 2^tl)) by (clear - RP; lia).
  assert (UT16 : unpoisoned m T (T + 16)) by (eapply unpoisoned_sub; [exact UT | lia | clear - T16; lia]).
  assert (RGT16 : rng RNG T 16) by (eapply rng_sub'; [exact RGT | clear - T16; lia]).
  assert (RGTS16 : rng RNG (shad T) (shspan T 16))
    by (pose proof (shspan_sub T (8 * (1 + 2^tl)) T 16 ltac:(lia) ltac:(lia) ltac:(clear - T16; lia)) as [SS1 SS2];
        eapply rng_sub'; [exact RGTS | split; [exact SS1 | exact SS2]]).
  clear UT RGT RGTS.
  unfold sbd_cells in HBD. unfold bit_okS in IB.
  clear TB ACL APB APS APF1 APF2 APF3 APF4.
  unfold SBITMASK.
  hide DJ1. hide DJ2. hide DJ3. hide DJ4. hide DJ5.
    destruct C as (C1 & C2 & C3).
  assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
    by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SEQ); clear - C1 C3 RB RT; lia).
  destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4).
  assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc.
  kx_autoFLAx [KAUnp BD 40; KAUnp (BD + 72) 16; KAUnp SEQ n; KAUnp T 16; KAUnp 139648 128; KAApp BD 40; KAApp (BD + 72) 16; KAApp (FRB + 136) 16; KAApp (FRB + 176) 32; KAApp (FRB + 272) 8; KAApp (FRB + 296) 8] [SQ_INL_INITFSE_L3_EXIT] 400%nat
      [KZRange n 16 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
       KZRange BD 4096 (2^47 - 88); KZRange FRB 4096 (2^47 - 304); KZRange TP 4096 (2^47 - 24); KZRange NS 1 (2^31 - 1); KZRange P224 0 (2^64 - 1); KZRange P232 0 (2^64 - 1); KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4; KZAlign FRB 8;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 72) 16; KZWr (FRB + 136) 16; KZWr (FRB + 176) 32; KZWr (FRB + 272) 8; KZWr (FRB + 296) 8;
       KZDisj BD 40 (BD + 72) 16; KZDisj BD 40 (FRB + 136) 16; KZDisj BD 40 (FRB + 176) 32; KZDisj BD 40 (FRB + 272) 8; KZDisj BD 40 (FRB + 296) 8; KZDisj (BD + 72) 16 (FRB + 136) 16; KZDisj (BD + 72) 16 (FRB + 176) 32; KZDisj (BD + 72) 16 (FRB + 272) 8; KZDisj (BD + 72) 16 (FRB + 296) 8; KZDisj (FRB + 136) 16 (FRB + 176) 32; KZDisj (FRB + 136) 16 (FRB + 272) 8; KZDisj (FRB + 136) 16 (FRB + 296) 8; KZDisj (FRB + 176) 32 (FRB + 272) 8; KZDisj (FRB + 176) 32 (FRB + 296) 8; KZDisj (FRB + 272) 8 (FRB + 296) 8; KZDisj BD 40 SEQ n; KZDisj BD 40 T 16; KZDisj BD 40 (FRB + 224) 16; KZDisj (BD + 72) 16 SEQ n; KZDisj (BD + 72) 16 T 16; KZDisj (BD + 72) 16 (FRB + 224) 16; KZDisj (FRB + 136) 16 SEQ n; KZDisj (FRB + 136) 16 T 16; KZDisj (FRB + 136) 16 (FRB + 224) 16; KZDisj (FRB + 176) 32 SEQ n; KZDisj (FRB + 176) 32 T 16; KZDisj (FRB + 176) 32 (FRB + 224) 16; KZDisj (FRB + 272) 8 SEQ n; KZDisj (FRB + 272) 8 T 16; KZDisj (FRB + 272) 8 (FRB + 224) 16; KZDisj (FRB + 296) 8 SEQ n; KZDisj (FRB + 296) 8 T 16; KZDisj (FRB + 296) 8 (FRB + 224) 16]
      [(SEQ, n); (BD, 40); (BD + 72, 16); (FRB + 136, 16); (FRB + 176, 32); (FRB + 272, 8); (FRB + 296, 8); (FRB + 224, 16)] [(BD, 40); (BD + 72, 16); (FRB + 136, 16); (FRB + 176, 32); (FRB + 272, 8); (FRB + 296, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGST | kx_acc RGB | kx_acc RGS | kx_acc RGT16 | kx_acc RGM | kx_acc RGF1 | kx_acc RGF2 | kx_acc RGF3 | kx_acc RGF4 | kx_acc RGFR | kx_acc RGBS | kx_acc RGSS | kx_acc RGTS16 | kx_acc RGMS | kx_acc RGSTS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => try kx_side_pre;
            lazymatch goal with |- _ /\ _ /\ (?A + _ <= ?B \/ _) =>
              let X := base_of A in let Y := base_of B in unhide_related X Y;
              repeat match goal with H : hidden _ |- _ => clear H end; repeat split; lia end end).
  all: unhide.
  all: kx_mem.
  all: kx_abs.
  all: kx_mkR_fold.
  all: sq_inl_initfse_L3_close.
Qed.

Lemma sq_inl_initfse_L3_c4 : sq_inl_initfse_L3_stmt_if (fun bc tl ptr SEQ n => bc + tl <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8 /\ (bc + tl) / 8 <= ptr - SEQ).
Proof.
  unfold sq_inl_initfse_L3_stmt_if, SQ_INL_INITFSE_L3_ENTRY. intros until t.
  intros HBD HST HF1 HF2 HFR HF3 HF4 TB OK SQB R1 R2 R3 R4 R5 R5b R6 R7 R8 RFH R9 R10 R11 R12 R13 A1 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5 RB RBB IB APB AROB APS AROST APF1 RGF1 APF2 RGF2 RGFR APF3 RGF3 APF4 RGF4 AROS AROT ACL ART MI C. cbv beta in C. unfold KHIGH in RFH.
  pose proof (seq_rdn_log bsegs m T k t TB OK) as RL. pose proof (seq_tl_range k t OK) as RT.
  remember (st_log t) as tl eqn:Etl.
  pose proof (sbitmask_know m tl MI ltac:(clear - RT; lia)) as BK. unfold SBITMASK in BK. change (0x22180) with 139648 in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROST as (UST & RGST & RGSTS). destruct AROS as (US & RGS & RGSS). destruct AROT as (UT & RGT & RGTS).
  pose proof (aro_client_at RNG m 139648 128 ACL ltac:(cbn [ACLIENT_RO In]; tauto)) as (UM & RGM & RGMS).
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (SPB2 : BD + 88 <= 0x7fff8000 \/ 0x10007fff8000 <= BD + 72) by (unfold app_blk, KLOW, KHIGH, KEND in APS; clear - APS; lia).
  assert (FRBB1 : FRB + 152 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 136) by (unfold app_blk, KLOW, KHIGH, KEND in APF1; clear - APF1; lia).
  assert (FRBB2 : FRB + 208 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 176) by (unfold app_blk, KLOW, KHIGH, KEND in APF2; clear - APF2; lia).
  assert (FRBB3 : FRB + 280 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 272) by (unfold app_blk, KLOW, KHIGH, KEND in APF3; clear - APF3; lia).
  assert (FRBB4 : FRB + 304 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 296) by (unfold app_blk, KLOW, KHIGH, KEND in APF4; clear - APF4; lia).
  assert (MU : munch [(BD, BD + 40); (BD + 72, BD + 88); (FRB + 136, FRB + 152); (FRB + 176, FRB + 208); (FRB + 272, FRB + 280); (FRB + 296, FRB + 304)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (RG : 4096 <= BD < 2^47 /\ 4096 <= SEQ < 2^47 /\ 4096 <= SEQ + n < 2^47) by lia.
  assert (T16 : 16 <= 8 * (1 + 2^tl)) by (clear - RP; lia).
  assert (UT16 : unpoisoned m T (T + 16)) by (eapply unpoisoned_sub; [exact UT | lia | clear - T16; lia]).
  assert (RGT16 : rng RNG T 16) by (eapply rng_sub'; [exact RGT | clear - T16; lia]).
  assert (RGTS16 : rng RNG (shad T) (shspan T 16))
    by (pose proof (shspan_sub T (8 * (1 + 2^tl)) T 16 ltac:(lia) ltac:(lia) ltac:(clear - T16; lia)) as [SS1 SS2];
        eapply rng_sub'; [exact RGTS | split; [exact SS1 | exact SS2]]).
  clear UT RGT RGTS.
  unfold sbd_cells in HBD. unfold bit_okS in IB.
  clear TB ACL APB APS APF1 APF2 APF3 APF4.
  unfold SBITMASK.
  hide DJ1. hide DJ2. hide DJ3. hide DJ4. hide DJ5.
    destruct C as (C1 & C2 & C3 & C4 & QD).
  assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n /\ q <= d)
    by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SEQ); clear - C1 C3 C4 QD RB RT; lia).
  clear QD. destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4 & QD).
  assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc.
  kx_autoFLAx [KAUnp BD 40; KAUnp (BD + 72) 16; KAUnp SEQ n; KAUnp T 16; KAUnp 139648 128; KAApp BD 40; KAApp (BD + 72) 16; KAApp (FRB + 136) 16; KAApp (FRB + 176) 32; KAApp (FRB + 272) 8; KAApp (FRB + 296) 8] [SQ_INL_INITFSE_L3_EXIT] 400%nat
      [KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
       KZRange BD 4096 (2^47 - 88); KZRange FRB 4096 (2^47 - 304); KZRange TP 4096 (2^47 - 24); KZRange NS 1 (2^31 - 1); KZRange P224 0 (2^64 - 1); KZRange P232 0 (2^64 - 1); KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4; KZAlign FRB 8;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 72) 16; KZWr (FRB + 136) 16; KZWr (FRB + 176) 32; KZWr (FRB + 272) 8; KZWr (FRB + 296) 8;
       KZDisj BD 40 (BD + 72) 16; KZDisj BD 40 (FRB + 136) 16; KZDisj BD 40 (FRB + 176) 32; KZDisj BD 40 (FRB + 272) 8; KZDisj BD 40 (FRB + 296) 8; KZDisj (BD + 72) 16 (FRB + 136) 16; KZDisj (BD + 72) 16 (FRB + 176) 32; KZDisj (BD + 72) 16 (FRB + 272) 8; KZDisj (BD + 72) 16 (FRB + 296) 8; KZDisj (FRB + 136) 16 (FRB + 176) 32; KZDisj (FRB + 136) 16 (FRB + 272) 8; KZDisj (FRB + 136) 16 (FRB + 296) 8; KZDisj (FRB + 176) 32 (FRB + 272) 8; KZDisj (FRB + 176) 32 (FRB + 296) 8; KZDisj (FRB + 272) 8 (FRB + 296) 8; KZDisj BD 40 SEQ n; KZDisj BD 40 T 16; KZDisj BD 40 (FRB + 224) 16; KZDisj (BD + 72) 16 SEQ n; KZDisj (BD + 72) 16 T 16; KZDisj (BD + 72) 16 (FRB + 224) 16; KZDisj (FRB + 136) 16 SEQ n; KZDisj (FRB + 136) 16 T 16; KZDisj (FRB + 136) 16 (FRB + 224) 16; KZDisj (FRB + 176) 32 SEQ n; KZDisj (FRB + 176) 32 T 16; KZDisj (FRB + 176) 32 (FRB + 224) 16; KZDisj (FRB + 272) 8 SEQ n; KZDisj (FRB + 272) 8 T 16; KZDisj (FRB + 272) 8 (FRB + 224) 16; KZDisj (FRB + 296) 8 SEQ n; KZDisj (FRB + 296) 8 T 16; KZDisj (FRB + 296) 8 (FRB + 224) 16]
      [(SEQ, n); (BD, 40); (BD + 72, 16); (FRB + 136, 16); (FRB + 176, 32); (FRB + 272, 8); (FRB + 296, 8); (FRB + 224, 16)] [(BD, 40); (BD + 72, 16); (FRB + 136, 16); (FRB + 176, 32); (FRB + 272, 8); (FRB + 296, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGST | kx_acc RGB | kx_acc RGS | kx_acc RGT16 | kx_acc RGM | kx_acc RGF1 | kx_acc RGF2 | kx_acc RGF3 | kx_acc RGF4 | kx_acc RGFR | kx_acc RGBS | kx_acc RGSS | kx_acc RGTS16 | kx_acc RGMS | kx_acc RGSTS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => try kx_side_pre;
            lazymatch goal with |- _ /\ _ /\ (?A + _ <= ?B \/ _) =>
              let X := base_of A in let Y := base_of B in unhide_related X Y;
              repeat match goal with H : hidden _ |- _ => clear H end; repeat split; lia end end).
  all: unhide.
  all: kx_mem.
  all: kx_abs.
  all: kx_mkR_fold.
  all: sq_inl_initfse_L3_close.
Qed.

Lemma sq_inl_initfse_L3_c5 : sq_inl_initfse_L3_stmt_if (fun bc tl ptr SEQ n => bc + tl <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8 /\ ptr - SEQ < (bc + tl) / 8).
Proof.
  unfold sq_inl_initfse_L3_stmt_if, SQ_INL_INITFSE_L3_ENTRY. intros until t.
  intros HBD HST HF1 HF2 HFR HF3 HF4 TB OK SQB R1 R2 R3 R4 R5 R5b R6 R7 R8 RFH R9 R10 R11 R12 R13 A1 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5 RB RBB IB APB AROB APS AROST APF1 RGF1 APF2 RGF2 RGFR APF3 RGF3 APF4 RGF4 AROS AROT ACL ART MI C. cbv beta in C. unfold KHIGH in RFH.
  pose proof (seq_rdn_log bsegs m T k t TB OK) as RL. pose proof (seq_tl_range k t OK) as RT.
  remember (st_log t) as tl eqn:Etl.
  pose proof (sbitmask_know m tl MI ltac:(clear - RT; lia)) as BK. unfold SBITMASK in BK. change (0x22180) with 139648 in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROST as (UST & RGST & RGSTS). destruct AROS as (US & RGS & RGSS). destruct AROT as (UT & RGT & RGTS).
  pose proof (aro_client_at RNG m 139648 128 ACL ltac:(cbn [ACLIENT_RO In]; tauto)) as (UM & RGM & RGMS).
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (SPB2 : BD + 88 <= 0x7fff8000 \/ 0x10007fff8000 <= BD + 72) by (unfold app_blk, KLOW, KHIGH, KEND in APS; clear - APS; lia).
  assert (FRBB1 : FRB + 152 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 136) by (unfold app_blk, KLOW, KHIGH, KEND in APF1; clear - APF1; lia).
  assert (FRBB2 : FRB + 208 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 176) by (unfold app_blk, KLOW, KHIGH, KEND in APF2; clear - APF2; lia).
  assert (FRBB3 : FRB + 280 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 272) by (unfold app_blk, KLOW, KHIGH, KEND in APF3; clear - APF3; lia).
  assert (FRBB4 : FRB + 304 <= 0x7fff8000 \/ 0x10007fff8000 <= FRB + 296) by (unfold app_blk, KLOW, KHIGH, KEND in APF4; clear - APF4; lia).
  assert (MU : munch [(BD, BD + 40); (BD + 72, BD + 88); (FRB + 136, FRB + 152); (FRB + 176, FRB + 208); (FRB + 272, FRB + 280); (FRB + 296, FRB + 304)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (RG : 4096 <= BD < 2^47 /\ 4096 <= SEQ < 2^47 /\ 4096 <= SEQ + n < 2^47) by lia.
  assert (T16 : 16 <= 8 * (1 + 2^tl)) by (clear - RP; lia).
  assert (UT16 : unpoisoned m T (T + 16)) by (eapply unpoisoned_sub; [exact UT | lia | clear - T16; lia]).
  assert (RGT16 : rng RNG T 16) by (eapply rng_sub'; [exact RGT | clear - T16; lia]).
  assert (RGTS16 : rng RNG (shad T) (shspan T 16))
    by (pose proof (shspan_sub T (8 * (1 + 2^tl)) T 16 ltac:(lia) ltac:(lia) ltac:(clear - T16; lia)) as [SS1 SS2];
        eapply rng_sub'; [exact RGTS | split; [exact SS1 | exact SS2]]).
  clear UT RGT RGTS.
  unfold sbd_cells in HBD. unfold bit_okS in IB.
  clear TB ACL APB APS APF1 APF2 APF3 APF4.
  unfold SBITMASK.
  hide DJ1. hide DJ2. hide DJ3. hide DJ4. hide DJ5.
    destruct C as (C1 & C2 & C3 & C4 & QD).
  assert (QR : exists q r d, bc + tl = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n /\ d < q)
    by (exists ((bc + tl) / 8), ((bc + tl) mod 8), (ptr - SEQ); clear - C1 C3 C4 QD RB RT; lia).
  clear QD. destruct QR as (q & r & d & EQ & -> & Q1 & Q2 & Q3 & Q4 & QD).
  assert (EB : bc = 8 * q + r - tl) by (clear - EQ; lia). subst bc.
  kx_autoFLAx [KAUnp BD 40; KAUnp (BD + 72) 16; KAUnp SEQ n; KAUnp T 16; KAUnp 139648 128; KAApp BD 40; KAApp (BD + 72) 16; KAApp (FRB + 136) 16; KAApp (FRB + 176) 32; KAApp (FRB + 272) 8; KAApp (FRB + 296) 8] [SQ_INL_INITFSE_L3_EXIT] 400%nat
      [KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange (8 * q + r - tl) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
       KZRange BD 4096 (2^47 - 88); KZRange FRB 4096 (2^47 - 304); KZRange TP 4096 (2^47 - 24); KZRange NS 1 (2^31 - 1); KZRange P224 0 (2^64 - 1); KZRange P232 0 (2^64 - 1); KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign T 4; KZAlign FRB 8;
       KZWord (T + 4) 4 tl; KZWord (139648 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr (BD + 72) 16; KZWr (FRB + 136) 16; KZWr (FRB + 176) 32; KZWr (FRB + 272) 8; KZWr (FRB + 296) 8;
       KZDisj BD 40 (BD + 72) 16; KZDisj BD 40 (FRB + 136) 16; KZDisj BD 40 (FRB + 176) 32; KZDisj BD 40 (FRB + 272) 8; KZDisj BD 40 (FRB + 296) 8; KZDisj (BD + 72) 16 (FRB + 136) 16; KZDisj (BD + 72) 16 (FRB + 176) 32; KZDisj (BD + 72) 16 (FRB + 272) 8; KZDisj (BD + 72) 16 (FRB + 296) 8; KZDisj (FRB + 136) 16 (FRB + 176) 32; KZDisj (FRB + 136) 16 (FRB + 272) 8; KZDisj (FRB + 136) 16 (FRB + 296) 8; KZDisj (FRB + 176) 32 (FRB + 272) 8; KZDisj (FRB + 176) 32 (FRB + 296) 8; KZDisj (FRB + 272) 8 (FRB + 296) 8; KZDisj BD 40 SEQ n; KZDisj BD 40 T 16; KZDisj BD 40 (FRB + 224) 16; KZDisj (BD + 72) 16 SEQ n; KZDisj (BD + 72) 16 T 16; KZDisj (BD + 72) 16 (FRB + 224) 16; KZDisj (FRB + 136) 16 SEQ n; KZDisj (FRB + 136) 16 T 16; KZDisj (FRB + 136) 16 (FRB + 224) 16; KZDisj (FRB + 176) 32 SEQ n; KZDisj (FRB + 176) 32 T 16; KZDisj (FRB + 176) 32 (FRB + 224) 16; KZDisj (FRB + 272) 8 SEQ n; KZDisj (FRB + 272) 8 T 16; KZDisj (FRB + 272) 8 (FRB + 224) 16; KZDisj (FRB + 296) 8 SEQ n; KZDisj (FRB + 296) 8 T 16; KZDisj (FRB + 296) 8 (FRB + 224) 16]
      [(SEQ, n); (BD, 40); (BD + 72, 16); (FRB + 136, 16); (FRB + 176, 32); (FRB + 272, 8); (FRB + 296, 8); (FRB + 224, 16)] [(BD, 40); (BD + 72, 16); (FRB + 136, 16); (FRB + 176, 32); (FRB + 272, 8); (FRB + 296, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGST | kx_acc RGB | kx_acc RGS | kx_acc RGT16 | kx_acc RGM | kx_acc RGF1 | kx_acc RGF2 | kx_acc RGF3 | kx_acc RGF4 | kx_acc RGFR | kx_acc RGBS | kx_acc RGSS | kx_acc RGTS16 | kx_acc RGMS | kx_acc RGSTS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => try kx_side_pre;
            lazymatch goal with |- _ /\ _ /\ (?A + _ <= ?B \/ _) =>
              let X := base_of A in let Y := base_of B in unhide_related X Y;
              repeat match goal with H : hidden _ |- _ => clear H end; repeat split; lia end end).
  all: unhide.
  all: kx_mem.
  all: kx_abs.
  all: kx_mkR_fold.
  all: sq_inl_initfse_L3_close.
Qed.

Theorem sq_inl_initfse_L3_proof : sq_inl_initfse_L3_stmt.
Proof.
  unfold sq_inl_initfse_L3_stmt, sq_inl_initfse_L3_stmt_if. intros until t.
  intros HBD HST HF1 HF2 HFR HF3 HF4 TB OK SQB R1 R2 R3 R4 R5 R5b R6 R7 R8 RFH R9 R10 R11 R12 R13 A1 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5 RB RBB IB APB AROB APS AROST APF1 RGF1 APF2 RGF2 RGFR APF3 RGF3 APF4 RGF4 AROS AROT ACL ART MI _.
  pose proof (seq_tl_range k t OK) as RT.
  assert (CASES : 65 <= bc + st_log t \/ (bc + st_log t <= 64 /\ ptr = SEQ) \/
                  (bc + st_log t <= 64 /\ 8 <= Z.of_nat (length sqb) /\ SEQ + 8 <= ptr <= SEQ + Z.of_nat (length sqb) - 8) \/
                  (bc + st_log t <= 64 /\ 8 <= Z.of_nat (length sqb) /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + Z.of_nat (length sqb) - 8 /\ (bc + st_log t) / 8 <= ptr - SEQ) \/
                  (bc + st_log t <= 64 /\ 8 <= Z.of_nat (length sqb) /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + Z.of_nat (length sqb) - 8 /\ ptr - SEQ < (bc + st_log t) / 8)).
  { unfold bit_okS in IB. clear - IB RT RB.
    destruct (Z_le_gt_dec (bc + st_log t) 64) as [Bq|Bq]; [|left; lia]. destruct (IB ltac:(lia)) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec (SEQ + 8) ptr); [right; right; left; lia|]. destruct (Z.eq_dec ptr SEQ); [right; left; lia|].
    destruct (Z_le_gt_dec ((bc + st_log t) / 8) (ptr - SEQ)); [right; right; right; left; lia | right; right; right; right; lia]. }
  destruct CASES as [C|[C|[C|[C|C]]]];
    [ eapply sq_inl_initfse_L3_c1 | eapply sq_inl_initfse_L3_c2 | eapply sq_inl_initfse_L3_c3 | eapply sq_inl_initfse_L3_c4 | eapply sq_inl_initfse_L3_c5 ]; try eassumption; exact C.
Qed.
End CANSEC1.
