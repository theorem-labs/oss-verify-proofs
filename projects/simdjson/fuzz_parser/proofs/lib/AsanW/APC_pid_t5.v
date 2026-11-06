(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface I_asan_memset AU_rt AH_memcpy0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import ShadowTac APC_kit APC_kit2 APC_kit3 APC_kit4 APC_docalloc APC_setcap APC_setdepth APC_active APC_create APC_dtor APC_memcmp APC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2Lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import APC_pid0 APC_pid1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.


(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac tlia ::= tlia_u.
Local Ltac lia3 ::= lia3_u.
Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable rng_fs : alayout -> footprint -> Prop.

Section T.
  Hypothesis ONTA : opnew_nt_stmtA AI.
  Hypothesis ODA : opdelete_arr_stmtA AI.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis PARSE : parse_stmtA AI rng_fs.
  Hypothesis RFSM : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Variable (L : alayout).
  Variable (RNG : footprint).
  Variable (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Variable (F : bvmap 5 word).
  Variable (fc : bv 32).
  Variable (m : amem).
  Variable (s : APS).
  Variable (LB : list ablock).
  Variable (lo : Z).
  Variable (rstk : region).
  Variable (data : list Z).
  Variable (D P R : Z).
  Variable (jr : list byte).
  Variable (trR : list Z).
  Variable (LBK : boxed (∀ b : ablock, In b LB → (∃ (p : AsanCtrl.aptr) (A n : Z), b = HB p A n) ∨ ∃ cls FA FN : Z, b = {| ab_kind := ABFake cls; ab_addr := FA; ab_size := FN |} ∧ cls ≠ 5 ∧ cls ≠ 4)).
  Variable (PAY : boxed (payload_atA LB D data)).
  Variable (DAT : bytes_at asegs m D (map (Z_to_bv 8) data)).
  Variable (DB : Forall (λ c : Z, 0 <= c < 256) data).
  Variable (D16 : D mod 16 = 0).
  Let len : Z := zlength data.
  Variable (DL : len < 2 ^ 26).
  Variable (CI0 : client_img m).
  Variable (CSH : client_sh m).
  Variable (fcls FA FN : Z).
  Variable (INF : In {| ab_kind := ABFake fcls; ab_addr := FA; ab_size := FN |} LB).
  Variable (FKH : FA <= P).
  Variable (FK2 : P + 80 <= FA + FN).
  Variable (FKB : ablk FA (FA + FN)).
  Variable (RP : P + 80 <= R).
  Variable (R8 : R mod 8 = 0).
  Variable (P8 : P mod 8 = 0).
  Variable (RSPR : bv_unsigned sp + 16 <= R).
  Variable (RHI : R + 24 <= r_hi rstk).
  Variable (R47 : R + 24 <= 2 ^ 47).
  Variable (LOA : ATOP + 4096 <= lo).
  Variable (LOS : lo <= bv_unsigned sp - (112 + (32 + (416 + 8192)))).
  Variable (RCL : rclean m rstk).
  Variable (RCL1 : r_lo rstk <= lo).
  Variable (RCL2 : bv_unsigned sp <= r_hi rstk).
  Variable (RCL3 : ATOP <= r_rlo rstk).
  Variable (RRNG : rng RNG (shad (r_rlo rstk)) (shad (r_rhi rstk) - shad (r_rlo rstk))).
  Variable (STOP : bv_unsigned sp + 16 < al_top L).
  Variable (SP16 : bv_unsigned sp mod 16 = 0).
  Variable (FZ : frm0 fc).
  Variable (TP : tp = Z_to_bv 64 ATP).
  Variable (HUL : HU L).
  Variable (RFS : rng_fs L RNG).
  Variable (AOK : aps_ok L s).
  Variable (RSP : 0 <= bv_unsigned sp < 2 ^ 64).
  Variable (H : 140735332483072 <= ATOP <= 140737479966720).
  Variable (FK1 : FA <= R).
  Variable (FKB1 : 6705152 <= FA).
  Variable (FKB2 : 0 <= FA).
  Variable (FKB3 : FA + FN <= ATOP).
  Variable (FKB4 : FA + FN + 8 <= 2 ^ 47).
  Variable (bF : Z).
  Variable (bFr : 0 <= bF <= 1).
  Variable (bFhi : FA + FN <= 2147446784 + bF * 140737479966720).
  Variable (bFlo : 17594333495296 * bF <= FA).
  Variable (LY1 : al_bot L + 8388608 = al_top L).
  Variable (LY2 : al_top L mod 4096 = 0).
  Variable (LY3 : al_top L <= 2 ^ 47).
  Variable (LEN0 : 0 <= len).
  Variable (CAPR : 32 <= CAP len < 2 ^ 26 + 32).
  Variable (PR0 : 0 <= R).
  Variable (SB : 2147450880 <= (P + 8) ≫ 3 + 2147450880 ∧ (P + 8) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB0 : 2147450880 <= (P + 24) ≫ 3 + 2147450880 ∧ (P + 24) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB1 : 2147450880 <= (P + 32) ≫ 3 + 2147450880 ∧ (P + 32) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB2 : 2147450880 <= (P + 40) ≫ 3 + 2147450880 ∧ (P + 40) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB3 : 2147450880 <= (P + 48) ≫ 3 + 2147450880 ∧ (P + 48) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB4 : 2147450880 <= (P + 56) ≫ 3 + 2147450880 ∧ (P + 56) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB5 : 2147450880 <= (P + 64) ≫ 3 + 2147450880 ∧ (P + 64) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB6 : 2147450880 <= (P + 72) ≫ 3 + 2147450880 ∧ (P + 72) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB7 : 2147450880 <= R ≫ 3 + 2147450880 ∧ R ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB8 : 2147450880 <= (R + 8) ≫ 3 + 2147450880 ∧ (R + 8) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB9 : 2147450880 <= (R + 16) ≫ 3 + 2147450880 ∧ (R + 16) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (RS0 : rng RNG ((P + 24) ≫ 3 + 2147450880) 1).
  Variable (RS1 : rng RNG ((P + 32) ≫ 3 + 2147450880) 1).
  Variable (RS2 : rng RNG ((P + 40) ≫ 3 + 2147450880) 1).
  Variable (RS3 : rng RNG ((P + 48) ≫ 3 + 2147450880) 1).
  Variable (RS7 : boxed (rng RNG (R ≫ 3 + 2147450880) 1)).
  Variable (RS8 : boxed (rng RNG ((R + 8) ≫ 3 + 2147450880) 1)).
  Variable (RS9 : boxed (rng RNG ((R + 16) ≫ 3 + 2147450880) 1)).
  Variable (junk : list byte).
  Variable (K1 : CAP len <= 4294967295).
  Variable (K2 : 0 < CAP len).
  Variable (psb ptp : AsanCtrl.aptr).
  Variable (SBA TPA : Z).
  Variable (BRS : ablock_range SBA (SB_BYTES len)).
  Variable (BRT : ablock_range TPA (TAPE_BYTES len)).
  Variable (FWF : Forall wfar2 (apid_W P R)).
  Variable (HUM : In [AMALLOC_PC; AOPNEW_RET] (al_U L)).
  Variable (pim psi poc pia : AsanCtrl.aptr).
  Variable (s2' : APS).
  Variable (RNG2 : footprint).
  Variable (w0' w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 : word).
  Variable (AIM ASI AOC AIA : Z).
  Variable (p1 p2 pad : list byte).
  Variable (BRM : ablock_range AIM 96).
  Variable (BRI : ablock_range ASI (SIDX_BYTES len)).
  Variable (BRO : ablock_range AOC (8 * 1024)).
  Variable (BRA : ablock_range AIA 1024).
  Variable (BRM1 : 6705152 <= AIM).
  Variable (BRM2 : 0 <= 96).
  Variable (BRM3 : AIM + 96 <= ATOP).
  Variable (BRM4 : AIM mod 16 = 0).
  Variable (BRI1 : 6705152 <= ASI).
  Variable (BRI2 : 0 <= SIDX_BYTES len).
  Variable (BRI3 : ASI + SIDX_BYTES len <= ATOP).
  Variable (BRI4 : ASI mod 16 = 0).
  Variable (BRO1 : 6705152 <= AOC).
  Variable (BRO2 : 0 <= 8 * 1024).
  Variable (BRO3 : AOC + 8 * 1024 <= ATOP).
  Variable (BRO4 : AOC mod 16 = 0).
  Variable (BRA1 : 6705152 <= AIA).
  Variable (BRA2 : 0 <= 1024).
  Variable (BRA3 : AIA + 1024 <= ATOP).
  Variable (BRA4 : AIA mod 16 = 0).
  Variable (BRS1 : 6705152 <= SBA).
  Variable (BRS2 : 0 <= SB_BYTES len).
  Variable (BRS3 : SBA + SB_BYTES len <= ATOP).
  Variable (BRS4 : SBA mod 16 = 0).
  Variable (BRT1 : 6705152 <= TPA).
  Variable (BRT2 : 0 <= TAPE_BYTES len).
  Variable (BRT3 : TPA + TAPE_BYTES len <= ATOP).
  Variable (BRT4 : TPA mod 16 = 0).
  Variable (DJMF : AIM + 96 <= FA ∨ FA + FN <= AIM).
  Variable (KC : len <= 1048512).
  Variable (SZC : 0 < COPY_BYTES len <= AREQMAX).
  Variable (pcp : AsanCtrl.aptr).
  Variable (s3' : APS).
  Variable (RNG3 : footprint).
  Variable (x0 x1 x2 e1 e2 e3 e4 e5 e6 e7 x3 x4 x5 x6 : word).
  Variable (ACP : Z).
  Variable (jcp : list byte).
  Variable (BRC : ablock_range ACP (len + 64)).
  Variable (RC1 : rng RNG3 ACP (len + 64)).
  Variable (RC2 : rng RNG3 (shad ACP) (shlen (len + 64 + 7))).
  Variable (BRC1 : 6705152 <= ACP).
  Variable (BRC2 : 0 <= len + 64).
  Variable (BRC3 : ACP + (len + 64) <= ATOP).
  Variable (BRC4 : ACP mod 16 = 0).
  Variable (bC : Z).
  Variable (bCr : 0 <= bC <= 1).
  Variable (bChi : ACP + (len + 64) <= 2147446784 + bC * 140737479966720).
  Variable (bClo : 17594333495296 * bC <= ACP).
  Variable (INM : In (HB pim AIM 96) (HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
  Variable (RSTK3 : rng RNG3 lo (al_top L - lo)).
  Variable (RI3 : rng_aimg RNG3).
  Variable (RISH3 : rng_aimg_sh RNG3).
  Variable (RPR3 : rng RNG3 R 24).
  Variable (RPP3 : rng RNG3 P 80).
  Variable (RS_8 : rng RNG3 ((P + 8) ≫ 3 + 2147450880) 1).
  Variable (RS_64 : rng RNG3 ((P + 64) ≫ 3 + 2147450880) 1).
  Variable (FPL13 : fp_le RNG RNG3).
  Variable (ARS13 : aps_rest s3' = aps_rest s).
  Variable (INC : In (HB pcp ACP (len + 64)) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
  Variable (z0 z1 z2 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 : word).
  Variable (m1 : amem).
  Variable (RS_72 : rng RNG3 ((P + 72) ≫ 3 + 2147450880) 1).
  Variable (h0 h1 h2 i1 i2 i3 i4 i5 i6 i7 h3 h4 h5 h6 ra' x0' x1' x2' y0' y1' y2' y3' y4' y5' y6' y7' x3' x4' x5' x6' : word).
  Variable (m0 : amem).
  Variable (INM' : In (HB pim AIM 96) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
  Variable (RS_56 : rng RNG3 ((P + 56) ≫ 3 + 2147450880) 1).
  Variable (bM : Z).
  Variable (bMr : 0 <= bM <= 1).
  Variable (bMhi : AIM + 96 <= 2147446784 + bM * 140737479966720).
  Variable (bMlo : 17594333495296 * bM <= AIM).
  Variable (SBM0 : 2147450880 <= AIM ≫ 3 + 2147450880 ∧ AIM ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SBM48 : 2147450880 <= (AIM + 48) ≫ 3 + 2147450880 ∧ (AIM + 48) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (ZD : zlength (strip_bom data) <= len ∧ len - 3 <= zlength (strip_bom data)).
  Variable (SZ1 : 4 * len + 36 <= SIDX_BYTES len).
  Variable (SZ2 : TAPE_BYTES len mod 8 = 0).
  Variable (SZ3 : 8 * (len + 3) <= TAPE_BYTES len <= 2 ^ 27).
  Variable (SZ4 : 5 * len + 182 <= 3 * SB_BYTES len).
  Variable (SZ5 : len + 60 <= SB_BYTES len <= 2 ^ 24).
  Variable (ND7 : List.NoDup [pim; psi; pcp; ptp; psb; poc; pia]).
  Variable (NF5 : ∀ FA' FN' : Z, ¬ In {| ab_kind := ABFake 5; ab_addr := FA'; ab_size := FN' |} (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
  Variable (RSHR3 : rng RNG3 (R ≫ 3 + 2147450880) ((R + 24) ≫ 3 + 2147450880 - (R ≫ 3 + 2147450880))).
  Variable (RSHP3 : rng RNG3 (P ≫ 3 + 2147450880) ((P + 80) ≫ 3 + 2147450880 - (P ≫ 3 + 2147450880))).
  Variable (RSD : rng RNG3 ((P + 24) ≫ 3 + 2147450880) 2).
  Variable (RDOC : rng RNG3 (P + 24) 16).
  Variable (INT7 : In (HB ptp TPA (TAPE_BYTES len)) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
  Variable (INS7 : In (HB psb SBA (SB_BYTES len)) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
  Variable (INO7 : In (HB poc AOC (8 * 1024)) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
  Variable (INA7 : In (HB pia AIA 1024) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
  Variable (INI7 : In (HB psi ASI (SIDX_BYTES len)) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
  Variable (jtp jsb joc jia : list byte).
  Variable (RRNG3 : rng RNG3 (shad (r_rlo rstk)) (shad (r_rhi rstk) - shad (r_rlo rstk))).
  Variable (USP3 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112).
  Variable (s4' : APS).
  Variable (RNG4 : footprint).
  Variable (FPL4 : fp_le RNG3 RNG4).
  Variable (q0' q1' q2' z0' z1' z2' z3' z4' z5' z6' z7' q3' q4' q5' q6' : word).
  Variable (F16 : bvmap 5 word).
  Variable (fc16 : bv 32).
  Variable (m16 : amem).
  Variable (FZ16 : frm0 fc16).
  Variable (MI16 : mem_inv asegs m16).
  Variable (ST16 : stk asegs m16 lo (bv_unsigned sp + -112)).
  Variable (ARS4 : aps_rest s4' = aps_rest s3').
  Variable (AH16 : AHEAP AI L RNG4 (aps_m s4') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m16).
  Variable (INF7 : In {| ab_kind := ABFake fcls; ab_addr := FA; ab_size := FN |} (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
  Variable (bI : Z).
  Variable (bIr : 0 <= bI <= 1).
  Variable (bIhi : ASI + SIDX_BYTES len <= 2147446784 + bI * 140737479966720).
  Variable (bIlo : 17594333495296 * bI <= ASI).
  Variable (bT : Z).
  Variable (bTr : 0 <= bT <= 1).
  Variable (bThi : TPA + TAPE_BYTES len <= 2147446784 + bT * 140737479966720).
  Variable (bTlo : 17594333495296 * bT <= TPA).
  Variable (bS : Z).
  Variable (bSr : 0 <= bS <= 1).
  Variable (bShi : SBA + SB_BYTES len <= 2147446784 + bS * 140737479966720).
  Variable (bSlo : 17594333495296 * bS <= SBA).
  Variable (bO : Z).
  Variable (bOr : 0 <= bO <= 1).
  Variable (bOhi : AOC + 8 * 1024 <= 2147446784 + bO * 140737479966720).
  Variable (bOlo : 17594333495296 * bO <= AOC).
  Variable (bA : Z).
  Variable (bAr : 0 <= bA <= 1).
  Variable (bAhi : AIA + 1024 <= 2147446784 + bA * 140737479966720).
  Variable (bAlo : 17594333495296 * bA <= AIA).
  Variable (FR : rw_cells asegs m16 (bv_unsigned sp + -112) [C8 (Z_to_bv 64 (P + 24)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Variable (PR : rw_cells asegs m16 R [CB 24 jr]).
  Variable (SC7 : rw_cells asegs m16 (R ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC8 : rw_cells asegs m16 ((R + 8) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC9 : rw_cells asegs m16 ((R + 16) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (DST4 : rw_cells asegs m16 (P + 8) [C8 (Z_to_bv 64 AIM)]).
  Variable (DOCa : rw_cells asegs m16 (P + 24) [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)]).
  Variable (PCP : rw_cells asegs m16 (P + 64) [C8 (Z_to_bv 64 ACP); C8 (Z_to_bv 64 len)]).
  Variable (O0 : rw_cells asegs m16 AIM [C8 (Z_to_bv 64 1064784)]).
  Variable (O16 : rw_cells asegs m16 (AIM + 16) [C8 (Z_to_bv 64 ASI)]).
  Variable (O56a : rw_cells asegs m16 (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)]).
  Variable (PW16 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m16).
  Variable (CS116 : client_static1 m16).
  Lemma apid_t5 :
    implMA RNG4 (mret ((psb, ptp).1, (psb, ptp).2, (pim, psi, poc, pia), Some pcp)) s4' (apid_post AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB len lo P R m) (MS (mkR (Z_to_bv 64 614332) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp q0' q1' q2' (Z_to_bv 64 R) (Z_to_bv 64 ((P + 64) ≫ 3 + 2147450880)) z0' z1' z2' z3' z4' z5' z6' z7' (Z_to_bv 64 (zlength (strip_bom data))) (Z_to_bv 64 (ACP + (len - zlength (strip_bom data)))) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) ≫ 3 + 2147450880)) q3' q4' q5' q6') F16 (ret_pc (Z_to_bv 64 614332)) fc16 None m16 (seg_rom asegs)).

  Proof using All.
    apply implMA_ret. retlit.
    pose proof (fp_le_trans _ _ _ FPL13 FPL4) as FPL14. assert (ARS14 : aps_rest s4' = aps_rest s) by (rewrite ARS4; exact ARS13).
    pose proof (rng_fp_le _ _ _ _ FPL4 RSTK3) as RSTK4. pose proof (rng_fp_le _ _ _ _ FPL4 RPR3) as RPR4.
    pose proof (rng_fp_le _ _ _ _ FPL4 RI3) as RI4.
    unbox RS7. unbox RS8. unbox RS9.
    pose proof (rng_fp_le _ _ _ _ FPL14 RS7) as RS_R. pose proof (rng_fp_le _ _ _ _ FPL14 RS8) as RS_R8. pose proof (rng_fp_le _ _ _ _ FPL14 RS9) as RS_R16.
    clear RS7 RS8 RS9.
    assert (INF8 : In (mkABlock (ABFake fcls) FA FN) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                     :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (do 7 right; exact INF).
    (* [comment removed for export] *)
    ltac2:(only_rng []). zstep. unhide_rng.
    if_cases KZ.
    - (* [comment removed for export] *)
      pose proof (rw_cells_split_CB asegs _ R [] 24 jr [] [8%nat; 8%nat; 4%nat; 4%nat] PR ltac:(reflexivity)) as SPL. cbn [app mk_CB_cells] in SPL.
      destruct (rw_cells_cut asegs _ R _ 1 SPL) as [PRa SPL1]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PRa, SPL1.
      destruct (rw_cells_cut asegs _ _ _ 1 SPL1) as [PRb SPL2]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PRb, SPL2.
      destruct (rw_cells_cut asegs _ _ _ 1 SPL2) as [PRc PRd]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PRc, PRd.
      replace (R + 8 + 8) with (R + 16) in PRc, PRd by lia. clear SPL SPL1 SPL2 PR.
      change (Z.of_nat 8) with 8 in PRb. change (Z.of_nat 4) with 4 in PRd. replace (R + 16 + 4) with (R + 20) in PRd by lia.
      pose proof (munch_refl [(R, R + 20)] m16) as MU17. pose proof (wmono_refl asegs m16) as WM17.
      park_memA m16. unfold parkedA in SC7, SC8, SC9, PRa, PRb, PRc, FR.
      ltac2:(hide_arith [@LOS; @LOA; @RSP; @STOP; @LY3; @SP16; @RP; @RSPR; @R47; @PR0; @R8; @FK1; @FKH; @FK2; @FKB3; @SB7; @SB8; @SB9; @bFr; @bFhi; @bFlo]).
      ltac2:(only_rng [@RS_R]). Time do 4 astep. unhide_rng.
      ltac2:(only_rng [@RPR4]). Time do 1 astep. unhide_rng.
      ltac2:(only_rng [@RS_R8]). Time do 5 astep. unhide_rng.
      ltac2:(only_rng [@RPR4]). Time do 2 astep. unhide_rng.
      ltac2:(only_rng [@RS_R16]). Time do 5 astep. unhide_rng.
      ltac2:(only_rng [@RPR4]). Time do 2 astep. unhide_rng.
      ltac2:(only_rng [@RSTK4]). Time do 15 astep. unhide_rng.
      unhide_arith. unparkA.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m17 eqn:EM17 end. clear EM17.
      Time trmC MU17 WM17 ltac:(fun _ => prnB).
      assert (AH17 : AHEAP AI L RNG4 (aps_m s4') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                                                  :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m17)
        by (eapply (AI_frame AI); [exact AH16| exact MU17| exact WM17|];
            apply Forall_cons; [first [ (left; left; cbn; prnB; lia) | (right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF8| cbn; prnB; lia]) ]| apply Forall_nil]).
      assert (PW17 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m17).
      { eapply aheap_pres_W_trans; [exact PW16|]. eapply aheap_pres_W_of_munch; [exact MU17| exact WM17|].
        intros a Ha Hc Hx. unfold apid_W in Hx. cbn [app outside] in Hx |- *. clear - Hx. lia. }
      pose proof (client_static1_munch32 _ _ _ CS116 MU17 WM17 ltac:(apply Forall_cons; [first [ (eapply wfar_ablk; [exact FKB| prnB; lia| prnB; lia]) | (apply wfar_high; prnB; lia) ]| apply Forall_nil])) as CS117.
      clear AH16 PW16 CS116 MU17 WM17.
      release_frame FR ST16 (bv_unsigned sp).
      apply evtF_done.
      unfold apid_post. split; [exact FPL14|].
      do 15 eexists. exists F16, fc16. eexists. split; [reflexivity|].
      split; [exact FZ16|]. split; [eassumption|]. split; [exact ST16|]. split; [exact (stk_slot4 _ _ _ _ _ _ PRa PRb PRc PRd eq_refl eq_refl eq_refl eq_refl)|].
      split; [exact PW17|]. split; [exact ARS14|]. split; [exact CS117|].
      exists SBA, TPA, AIM, ASI, AOC, AIA, ACP.
      split; [unfold apid_blocks, acopy_blk, asix_blks, ISARR_BYTES, OC_BYTES, MAX_DEPTH, IMPL_BYTES, COPY_BYTES, PADDING; cbn [app]; exact AH17|].
      destruct (rw_cells_cut asegs _ _ _ 1 PCP) as [PCPa _]. cbn [firstn] in PCPa.
      split; [exact DST4|]. split; [exact DOCa|]. split; [exact PCPa|]. split; [unfold AVTAB_DOM; exact O0|]. split; [exact O16| exact O56a].
    - (* [comment removed for export] *)
      ltac2:(only_rng []). Time do 6 astep. unhide_rng.
      (* [comment removed for export] *)
      assert (RC16 : rclean m16 rstk).
      { eapply (rclean_W AI _ _ _ _ _ _ RCL PW16 RCL3). intros a Ha. unfold apid_W, client_wr. cbn [app outside].
        pose proof RCL as ((_ & (H1 & H2 & H3 & H4 & H5 & H6) & _ & _) & _). unfold KEND in H6. pose proof atop_range as AR.
        rewrite !shad_div in Ha. unfold ASHOFF in Ha.
        clear - Ha H1 H2 H3 H4 H5 H6 AR RCL3 FK1 FKH FK2 FKB3 FKB2 RP RSPR LOA LOS PR0 bFr bFhi bFlo. Z.div_mod_to_equations. lia. }
      destruct RC16 as [(UNP16 & HL16 & WRH6 & APP16) _].
      pose proof (client_rt_of_aheap AI _ _ _ _ _ AH16) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
      pose proof (rw_cells_split_CB asegs _ R [] 24 jr [] [16%nat; 8%nat] PR ltac:(reflexivity)) as SPL. cbn [app mk_CB_cells] in SPL.
      destruct (rw_cells_cut asegs _ R _ 1 SPL) as [PR16 PR8]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PR16, PR8.
      change (Z.of_nat 16) with 16 in PR8. clear SPL PR.
      pose proof (unpoisoned_two _ R R8 PR0 ltac:(prnB; lia) SC7 SC8) as UPR.
      pose proof (rng_fp_le _ _ _ _ FPL14 RRNG) as RGH4.
      assert (APR : app_blk R (R + 16)) by (eapply app_blk_sub; [exact APP16| clear - RCL1 LOS LOA RSPR; lia| lia| clear - RHI; lia]).
      assert (HL64 : r_rlo rstk <= R /\ R + 16 <= r_rhi rstk /\ r_rlo rstk mod 64 = 0 /\ r_rhi rstk mod 64 = 0 /\ 0 <= r_rlo rstk /\ r_rhi rstk <= KEND)
        by (destruct HL16 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6); clear - Q1 Q2 Q3 Q4 Q5 Q6 RCL1 LOS LOA RSPR RHI; repeat split; lia).
      assert (UR : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; clear - PR0 R47; lia).
      assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; clear - LOS LOA RSP; lia).
      assert (U16 : bv_unsigned (Z_to_bv 64 16) = 16) by reflexivity. assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
      assert (RSM : rng RNG4 lo (bv_unsigned sp + -112 - lo)) by (eapply rng_sub'; [exact RSTK4| clear - LOS LOA RSP STOP LY3; lia]).
      assert (RRM : rng RNG4 R 16) by (eapply rng_sub'; [exact RPR4| clear - PR0; lia]).
      eapply evtF_cut.
      { eapply (asan_memset_spec RNG4) with (lo := lo) (RLO2 := r_rlo rstk) (RHI2 := r_rhi rstk) (junk := firstn 16 jr);
          rewrite ?UR, ?USP, ?U16, ?U0;
          first [ eassumption | exact PR16 | (unfold KHIGH; clear - LOA; lia) | (right; clear - RSPR; lia) | (clear - LOS; lia) ]. }
      cbv beta. intros ms17 (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m17 & -> & MU17 & WM17 & MI17 & ST17 & SET17).
      rewrite ?UR, ?USP, ?U16 in MU17. rewrite ?UR, ?USP, ?U16 in ST17. rewrite ?UR, ?USP, ?U16 in SET17. retlit.
      Time trmC MU17 WM17 ltac:(fun _ => prnB).
      assert (AH17 : AHEAP AI L RNG4 (aps_m s4') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                                                  :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m17)
        by (eapply (AI_frame AI); [exact AH16| exact MU17| exact WM17|];
            apply Forall_cons; [left; left; cbn; prnB; lia|];
            apply Forall_cons; [first [ (left; left; cbn; prnB; lia) | (right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF8| cbn; prnB; lia]) ]| apply Forall_nil]).
      assert (PW17 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m17).
      { eapply aheap_pres_W_trans; [exact PW16|]. eapply aheap_pres_W_of_munch; [exact MU17| exact WM17|].
        intros a Ha Hc Hx. unfold apid_W in Hx. cbn [app outside] in Hx |- *.
        pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH17 (fun b Hb => or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror Hb))))))) Hc) as Ha'.
        clear - Hx Ha' LOA LOS. lia. }
      pose proof (client_static1_munch32 _ _ _ CS116 MU17 WM17
                    ltac:(apply Forall_cons; [apply wfar_high; prnB; lia| apply Forall_cons; [first [ (eapply wfar_ablk; [exact FKB| prnB; lia| prnB; lia]) | (apply wfar_high; prnB; lia) ]| apply Forall_nil]])) as CS117.
      clear AH16 PW16 CS116 MU17 WM17 GOT RIC REAL SHB SUA INI LAY UPR RGH4 WRH6 APR HL64 RSM RRM PR16 UNP16 HL16 APP16.
      (* [comment removed for export] *)
      pose proof (munch_refl [(R + 16, R + 20)] m17) as MU18. pose proof (wmono_refl asegs m17) as WM18.
      pose proof (rw_cells_split_CB asegs _ (R + 16) [] 8 _ [] [4%nat; 4%nat] PR8 ltac:(reflexivity)) as SPL. cbn [app mk_CB_cells] in SPL.
      destruct (rw_cells_cut asegs _ (R + 16) _ 1 SPL) as [PR16a PR20]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PR16a, PR20.
      try replace (R + 16 + Z.of_nat 4) with (R + 20) in PR20 by lia. try replace (R + 16 + 4) with (R + 20) in PR20 by lia.
      clear SPL PR8.
      park_memA m17. unfold parkedA in SC9, PR16a, FR.
      ltac2:(hide_arith [@LOS; @LOA; @RSP; @STOP; @LY3; @SP16; @RP; @RSPR; @R47; @PR0; @R8; @FK1; @FKH; @FK2; @FKB3; @SB9; @bFr; @bFhi; @bFlo]).
      ltac2:(only_rng [@RS_R16]). Time do 4 astep. unhide_rng.
      ltac2:(only_rng [@RPR4]). Time do 2 astep. unhide_rng.
      ltac2:(only_rng [@RSTK4]). Time do 15 astep. unhide_rng.
      unhide_arith. unparkA.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m18 eqn:EM18 end. clear EM18.
      Time trmC MU18 WM18 ltac:(fun _ => prnB).
      assert (AH18 : AHEAP AI L RNG4 (aps_m s4') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                                                  :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m18)
        by (eapply (AI_frame AI); [exact AH17| exact MU18| exact WM18|];
            apply Forall_cons; [first [ (left; left; cbn; prnB; lia) | (right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF8| cbn; prnB; lia]) ]| apply Forall_nil]).
      assert (PW18 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m18).
      { eapply aheap_pres_W_trans; [exact PW17|]. eapply aheap_pres_W_of_munch; [exact MU18| exact WM18|].
        intros a Ha Hc Hx. unfold apid_W in Hx. cbn [app outside] in Hx |- *. clear - Hx. lia. }
      pose proof (client_static1_munch32 _ _ _ CS117 MU18 WM18 ltac:(apply Forall_cons; [first [ (eapply wfar_ablk; [exact FKB| prnB; lia| prnB; lia]) | (apply wfar_high; prnB; lia) ]| apply Forall_nil])) as CS118.
      clear AH17 PW17 CS117 MU18 WM18.
      release_frame FR ST17 (bv_unsigned sp).
      apply evtF_done.
      unfold apid_post. split; [exact FPL14|].
      do 15 eexists. exists F16, fc16. eexists. split; [reflexivity|].
      split; [exact FZ16|]. split; [eassumption|]. split; [exact ST17|]. split; [exact (stk_slot3 _ _ _ _ _ SET17 PR16a PR20 eq_refl eq_refl eq_refl)|].
      split; [exact PW18|]. split; [exact ARS14|]. split; [exact CS118|].
      exists SBA, TPA, AIM, ASI, AOC, AIA, ACP.
      split; [unfold apid_blocks, acopy_blk, asix_blks, ISARR_BYTES, OC_BYTES, MAX_DEPTH, IMPL_BYTES, COPY_BYTES, PADDING; cbn [app]; exact AH18|].
      destruct (rw_cells_cut asegs _ _ _ 1 PCP) as [PCPa _]. cbn [firstn] in PCPa.
      split; [exact DST4|]. split; [exact DOCa|]. split; [exact PCPa|]. split; [unfold AVTAB_DOM; exact O0|]. split; [exact O16| exact O56a].
  Qed.
End T.
End S.
End CANSEC1.
