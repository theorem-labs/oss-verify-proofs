(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase F_tryinit F_aunwind F_tlsga F_m2s_b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AKit FsKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition ASTKMALLOC0 : Z := 0x3cc38.

(* [comment removed for export] *)
Definition sm0_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs, fs + 8); (flag, flag + 1); (F + 24, F + 32); (F + 56, F + 64); (shad F, shad F + 8)].

Definition sm0_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h flag F : Z) (h1 h2 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm0_W (bv_unsigned sp) fs flag F) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' fs [C8 (Z_to_bv 64 (h + 1)); C8 h1; C8 h2; CB 64 hs]
    /\ rw_cells bsegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' (F + 24) [C8 sp]
    /\ rw_cells bsegs m' (F + 56) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0)].

Lemma stack_malloc0_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h pos flag F : Z) (j24 j56 sh0 h1 h2 : word) (hs : list byte),
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
  rw_cells bsegs m fs [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  pos = Z.land h 16383 -> flag = fs + 4096 + pos -> F = fs + 36864 + pos * 64 ->
  rw_cells bsegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 56) [C8 j56] ->
  rw_cells bsegs m (shad F) [C8 sh0] ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm0_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h flag F h1 h2 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs)).
Proof.
intros until hs.
intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY C0 C1 T0 T1 BLO BHI V
FLO FHI FAL HNT HB LOG NGC POS FLAG FF FL0 F24 F56 SH0
RIMG RSTK RCTX RT RB RFS RSH.
pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
pose proof (munch_refl (sm0_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm0_W in MU. pose proof (wmono_refl bsegs m) as WM.
assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC0 in *.
lit_in DTVP; lit_in DTV1.
assert (PB : 0 <= pos < 16384).
{ subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (SHD : shad F + 8 <= fs \/ fs + 11571200 <= shad F).
{ pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
carve_frame 32%nat ST.
do 5 zstep.
zstep.
zstep. zstep.
zstep.
zstep.
box RCTX; box RT; box RB.
call_sp tlsga_icpt_spec;
first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
| (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
| exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
| lia | solve_rng | idtac ].
unbox RCTX; unbox RT; unbox RB.
rename POST into ST. unfold ATP.
lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
zstep.
zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].
zstep; rewrite zxb_lit by lia.
zstep.
zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].
zstep. zstep. zstep.
zstep; lits.
zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].
zstep. zstep.
zstep.
zstep. zstep. zstep. zstep.
zstep. zstep.
zstep. zstep.
zstep. rewrite <- POS.
zstep.
match goal with |- context [Z_to_bv 64 (fs + 4096 + pos)] => replace (fs + 4096 + pos) with flag by lia end.
zstep; rewrite zxb_lit by lia.
zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
zstep. zstep. zstep.
zstep.
zstep.
zstep.
zstep. zstep.
zstep.
match goal with |- context [Z_to_bv 64 (fs + 36864 + Z.shiftl pos 6)] =>
replace (fs + 36864 + Z.shiftl pos 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia) end.
zstep. zstep.
zstep.
zstep. call m2sb_spec;
first [ eassumption
| (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
| idtac ].
rewrite unsigned_lit by lia.
zstep. zstep. zstep.
assert (RSF : rng RNG (shad F) 8).
{ eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
zstep.
do 6 zstep.
lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
