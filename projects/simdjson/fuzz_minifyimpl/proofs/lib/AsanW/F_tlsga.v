(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase F_tryinit F_aunwind.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AKit FsKit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AFSDESC : Z := 0x167e48.      (* [comment removed for export] *)
Definition AREAL_TLSGA : Z := 0x168f50.  (* [comment removed for export] *)
Definition ATLSGA : Z := 0x15a0e8.       (* [comment removed for export] *)
Definition ADTLSF : Z := 0x99ec8.        (* [comment removed for export] *)
Definition ATLSGA_ICPT : Z := 0x73f48.   (* [comment removed for export] *)
Definition ADTV : Z := 0x6a4e08.         (* [comment removed for export] *)
Definition ADTLSV : Z := 0x6a4df0.       (* [comment removed for export] *)
Definition AVERB : Z := 0x1ffe58.        (* [comment removed for export] *)
Definition ACF137 : Z := 0x201f71.       (* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma musl_tlsga_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (fsw : word),
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)] ->
  rw_cells asegs m (ATP - 8) [C8 (Z_to_bv 64 ADTV); C8 fsw] ->
  rw_cells asegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))] ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => exists a1' a2',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AFSDESC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA) fc None m (seg_rom asegs)).
Proof.
  intros until fsw. intros -> DESC DTVP DTV1 RIMG.
  unfold AFSDESC, ATP, ADTV, ATLSGA in *. lit_in DTVP; lit_in DTV1.
  do 9 zstep. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dtls_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma dtls_fast_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo B v : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AFSDESC ->
  rt_got m ->
  rw_cells asegs m ACF137 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0x167068 [C8 (Z_to_bv 64 AVERB)] ->
  rw_cells asegs m AVERB [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)] ->
  rw_cells asegs m 0x167e58 [C8 (Z_to_bv 64 8)] ->
  rw_cells asegs m ADTLSV [C8 (Z_to_bv 64 B)] ->
  rw_cells asegs m (B + 24) [C8 (Z_to_bv 64 v)] ->
  iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->            (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG B 4096 ->
  evtF asegs RNG (dtls_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADTLSF) fc None m (seg_rom asegs)).
Proof.
  intros until v. intros MI ST LO CEIL -> -> G50 CF GB0 VERB DESC G08 DV BD BLO BHI V RIMG RSTK RB. destruct BLO as [BLO _].   (* [comment removed for export] *)
  unfold GOT_CFLAGS, ACFLAGS, ACF137, AVERB, AFSDESC, ADTLSV, ADTLSF, ATP, AIMG_HI in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 144%nat ST.
  do 14 zstep.                              (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep; lits.                       (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|].   (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. if_cases K3; zify_cond K3; [exfalso; clear - K3 V BHI; lia|].      (* [comment removed for export] *)
  zstep. if_cases K4; zify_cond K4; [| exfalso; clear - K4 BLO; lia].      (* [comment removed for export] *)
  zstep. if_cases K5; zify_cond K5; [exfalso; clear - K5 BLO; lia|].        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep. if_cases K6; zify_cond K6; [| exfalso; clear - K6; lia].   (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases K7; zify_cond K7; [exfalso; clear - K7 V; lia|].          (* [comment removed for export] *)
  do 16 zstep.                              (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tlsga_cells (m : amem) (t B v : Z) (fsw : word) : Prop :=
     rw_cells asegs m AREAL_TLSGA [C8 (Z_to_bv 64 ATLSGA)]
  /\ rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]
  /\ rw_cells asegs m (ATP - 8) [C8 (Z_to_bv 64 ADTV); C8 fsw]
  /\ rw_cells asegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))]
  /\ rt_got m
  /\ rw_cells asegs m ACF137 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x167068 [C8 (Z_to_bv 64 AVERB)]
  /\ rw_cells asegs m AVERB [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x167e58 [C8 (Z_to_bv 64 8)]
  /\ rw_cells asegs m ADTLSV [C8 (Z_to_bv 64 B)]
  /\ rw_cells asegs m (B + 24) [C8 (Z_to_bv 64 v)]
  /\ (exists tb te : word, rw_cells asegs m (t + 48) [C8 tb; C8 te]).

Definition tlsga_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma tlsga_icpt_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo ctx t B v : Z) (fsw : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AFSDESC ->
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v fsw ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->     (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  evtF asegs RNG (tlsga_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom asegs)).
Proof.
  intros until fsw. intros MI ST LO CEIL TP A0 INI TI TK T88 TSD CT
         (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48))
         C0 C1 T0 T1 BLO BHI V RIMG RSTK RCTX RT RB.
  subst a0.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ATLSGA_ICPT, ATLSGA in *.
  lit_in DTVP; lit_in DTV1.
  carve_frame 32%nat ST.
  do 5 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. call_sp tryinit_spec;
    first [exact MI| exact ST| exact INI| exact RIMG| unfold KHIGH; lia| solve_rng | idtac].
  rename PC into ST. clear POST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI1 end.
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  callp musl_tlsga_spec; first [exact TP| exact DESC| exact DTVP| exact DTV1| exact RIMG| idtac].
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  box RT; box RB.
  zstep. call_sp get_current_thread_spec;
    first [exact ST| exact MI1| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| exact RIMG| exact RCTX
          | atop_facts; lia| solve_rng | idtac].
  unbox RT; unbox RB. rename POST into ST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 T0; lia|].        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. call_sp dtls_fast_spec;
    first [exact MI2| exact ST| exact TP| reflexivity| exact G50| exact CF| exact GB0| exact VERB| exact DESC
          | exact G08| exact DV| exact BD| exact RIMG| exact RB| exact BLO| unfold AIMG_HI; lia| solve_rng | idtac].
  rename POST into ST.
  do 7 zstep.                               (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). subst tp. finish.
Qed.
End CANSEC2.
(* [comment removed for export] *)
