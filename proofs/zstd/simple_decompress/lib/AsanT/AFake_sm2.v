(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase F_tryinit F_aunwind F_tlsga F_m2s_b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit FsKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition ASTKMALLOC2 : Z := 0x3f190.

(* [comment removed for export] *)
Definition sm2_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs + 16, fs + 24); (flag, flag + 1); (F + 24, F + 32); (F + 248, F + 256); (shad F, shad F + 32)].

Definition sm2_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h flag F : Z) (h0 h1 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm2_W (bv_unsigned sp) fs flag F) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' fs [C8 h0; C8 h1; C8 (Z_to_bv 64 (h + 1)); CB 64 hs]
    /\ rw_cells bsegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' (F + 24) [C8 sp]
    /\ rw_cells bsegs m' (F + 248) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma stack_malloc2_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j24 j248 sh0 sh1 sh2 sh3 h0 h1 : word) (hs : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->     (* [comment removed for export] *)
  (* [comment removed for export] *)
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->            (* [comment removed for export] *)
  rw_cells bsegs m fs [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  pos = Z.land h 4095 -> flag = fs + 28672 + pos -> F = fs + 2134016 + pos * 256 ->
  rw_cells bsegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 248) [C8 j248] ->
  rw_cells bsegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3] ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm2_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h flag F h0 h1 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom bsegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.   (* [comment removed for export] *)
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm2_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm2_W in MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC2 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 32 <= fs \/ fs + 11571200 <= shad F).   (* [comment removed for export] *)
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  box RCTX; box RT; box RB.   (* [comment removed for export] *)
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].   (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].      (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep; lits.                              (* [comment removed for export] *)
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].      (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  do 9 zstep.                               (* [comment removed for export] *)
  zstep. rewrite <- POS.                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (fs + 28672 + pos)] => replace (fs + 28672 + pos) with flag by lia end.
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].      (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (2097152 + Z.shiftl pos 8))] =>
    replace (fs + 36864 + (2097152 + Z.shiftl pos 8)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia) end.
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)   (* [comment removed for export] *)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  assert (RSF : rng RNG (shad F) 32).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
  do 6 zstep.                               (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
