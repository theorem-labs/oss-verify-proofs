(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface I_asan_memset AU_rt AH_memcpy0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import ShadowTac APC_kit APC_kit2 APC_kit3 APC_kit4 APC_docalloc APC_setcap APC_setdepth APC_active APC_create APC_dtor APC_memcmp APC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import A2Lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_pid0 APC_pid1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_pid_t5.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import LiaTier0U.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_bkit.
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
  Variable (DAT : bytes_at bsegs m D (map (Z_to_bv 8) data)).
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
  Variable (RSHR : boxed (rng RNG (R ≫ 3 + 2147450880) ((R + 24) ≫ 3 + 2147450880 - (R ≫ 3 + 2147450880)))).
  Variable (RSHP : boxed (rng RNG (P ≫ 3 + 2147450880) ((P + 80) ≫ 3 + 2147450880 - (P ≫ 3 + 2147450880)))).
  Variable (RSPR : bv_unsigned sp + 16 <= R).
  Variable (RHI : R + 24 <= r_hi rstk).
  Variable (LOA : ATOP + 4096 <= lo).
  Variable (LOS : lo <= bv_unsigned sp - (112 + (32 + (448 + 8192)))).
  Variable (RCL : rclean m rstk).
  Variable (RCL1 : r_lo rstk <= lo).
  Variable (RCL2 : bv_unsigned sp <= r_hi rstk).
  Variable (RCL3 : ATOP <= r_rlo rstk).
  Variable (RRNG : boxed (rrng RNG rstk)).
  Variable (STOP : bv_unsigned sp + 16 < al_top L).
  Variable (SP16 : bv_unsigned sp mod 16 = 0).
  Variable (FZ : frm0 fc).
  Variable (TP : tp = Z_to_bv 64 ATP).
  Variable (HUL : HU L).
  Variable (UCR : boxed (uchain m (al_top L) AFREE_PC (bv_unsigned sp + -112) R (Nat.pred UDEPTH) trR)).
  Variable (TRR : (length trR ≤ 27)%nat).
  Variable (RFS : rng_fs L RNG).
  Variable (AOK : aps_ok L s).
  Variable (AFR : AFRESH (aps_m s)).
  Variable (DKW : dk (aps_m s) < DWMAX).
  Variable (PRO : boxed (rw_cells bsegs m R [CB 24 jr])).
  Variable (RSP : 0 <= bv_unsigned sp < 2 ^ 64).
  Variable (H : 140735332483072 <= ATOP <= 140737479966720).
  Variable (FK1 : FA <= R).
  Variable (FKB1 : 6754304 <= FA).
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
  Variable (R47 : R + 24 <= 2 ^ 47).
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
  Variable (RS4 : boxed (rng RNG ((P + 56) ≫ 3 + 2147450880) 1)).
  Variable (RS7 : boxed (rng RNG (R ≫ 3 + 2147450880) 1)).
  Variable (RS8 : boxed (rng RNG ((R + 8) ≫ 3 + 2147450880) 1)).
  Variable (RS9 : boxed (rng RNG ((R + 16) ≫ 3 + 2147450880) 1)).
  Variable (junk : list byte).
  Variable (K1 : CAP len <= 4294967295).
  Variable (K2 : 0 < CAP len).
  Variable (psb ptp : AsanCtrl.aptr).
  Variable (s1' : APS).
  Variable (SBA TPA : Z).
  Variable (BRS : ablock_range SBA (SB_BYTES len)).
  Variable (BRT : ablock_range TPA (TAPE_BYTES len)).
  Variable (AFR1 : AFRESH (aps_m s1')).
  Variable (DK1 : dk (aps_m s1') < DWMAX).
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
  Variable (AFR2 : AFRESH (aps_m s2')).
  Variable (DK2 : dk (aps_m s2') < DWMAX).
  Variable (BRM1 : 6754304 <= AIM).
  Variable (BRM2 : 0 <= 96).
  Variable (BRM3 : AIM + 96 <= ATOP).
  Variable (BRM4 : AIM mod 16 = 0).
  Variable (BRI1 : 6754304 <= ASI).
  Variable (BRI2 : 0 <= SIDX_BYTES len).
  Variable (BRI3 : ASI + SIDX_BYTES len <= ATOP).
  Variable (BRI4 : ASI mod 16 = 0).
  Variable (BRO1 : 6754304 <= AOC).
  Variable (BRO2 : 0 <= 8 * 1024).
  Variable (BRO3 : AOC + 8 * 1024 <= ATOP).
  Variable (BRO4 : AOC mod 16 = 0).
  Variable (BRA1 : 6754304 <= AIA).
  Variable (BRA2 : 0 <= 1024).
  Variable (BRA3 : AIA + 1024 <= ATOP).
  Variable (BRA4 : AIA mod 16 = 0).
  Variable (BRS1 : 6754304 <= SBA).
  Variable (BRS2 : 0 <= SB_BYTES len).
  Variable (BRS3 : SBA + SB_BYTES len <= ATOP).
  Variable (BRS4 : SBA mod 16 = 0).
  Variable (BRT1 : 6754304 <= TPA).
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
  Variable (AFR3 : AFRESH (aps_m s3')).
  Variable (DK3 : dk (aps_m s3') < DWMAX).
  Variable (BRC1 : 6754304 <= ACP).
  Variable (BRC2 : 0 <= len + 64).
  Variable (BRC3 : ACP + (len + 64) <= ATOP).
  Variable (BRC4 : ACP mod 16 = 0).
  Variable (bC : Z).
  Variable (bCr : 0 <= bC <= 1).
  Variable (bChi : ACP + (len + 64) <= 2147446784 + bC * 140737479966720).
  Variable (bClo : 17594333495296 * bC <= ACP).
  Variable (DJM : ACP + (len + 64) <= AIM ∨ AIM + 96 <= ACP).
  Variable (DJF : ACP + (len + 64) <= FA ∨ FA + FN <= ACP).
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
  Variable (h0 h1 h2 i1 i2 i3 i4 i5 i6 i7 h3 h4 h5 h6 ra' x0' x1' x2' b1' y0' y1' y2' y3' y4' y5' y6' y7' x3' x4' x5' x6' : word).
  Variable (m14 : amem).
  Variable (MI14 : mem_inv bsegs m14).
  Variable (ST14 : stk bsegs m14 lo (bv_unsigned sp + -112)).
  Variable (SC5 : rw_cells bsegs m14 ((P + 64) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (FR : rw_cells bsegs m14 (bv_unsigned sp + -112) [C8 (Z_to_bv 64 (P + 24)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Variable (SC6 : rw_cells bsegs m14 ((P + 72) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (PCP : rw_cells bsegs m14 (P + 64) [C8 (Z_to_bv 64 ACP); C8 (Z_to_bv 64 len)]).
  Variable (DST4 : rw_cells bsegs m14 (P + 8) [C8 (Z_to_bv 64 AIM)]).
  Variable (OBJ4 : rw_cells bsegs m14 AIM [C8 (Z_to_bv 64 AVTAB_DOM); C4 (Z_to_bv 64 0); CB 4 p1; C8 (Z_to_bv 64 ASI); C4 (Z_to_bv 64 0); CB 4 p2; C8 (Z_to_bv 64 (CAP len)); C8 (Z_to_bv 64 1024); C2 (Z_to_bv 64 0); CB 6 pad; C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  Variable (DOC2 : rw_cells bsegs m14 (P + 24) [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA); C8 (Z_to_bv 64 (CAP len))]).
  Variable (PMAX : rw_cells bsegs m14 (P + 48) [C8 (Z_to_bv 64 4294967295); C1 (Z_to_bv 8 0)]).
  Variable (PR : rw_cells bsegs m14 R [CB 24 jr]).
  Variable (SC : rw_cells bsegs m14 ((P + 8) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC0 : rw_cells bsegs m14 ((P + 24) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC1 : rw_cells bsegs m14 ((P + 32) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC2 : rw_cells bsegs m14 ((P + 40) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC3 : rw_cells bsegs m14 ((P + 48) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC4 : rw_cells bsegs m14 ((P + 56) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC7 : rw_cells bsegs m14 (R ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC8 : rw_cells bsegs m14 ((R + 8) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC9 : rw_cells bsegs m14 ((R + 16) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SET10 : rw_cells bsegs m14 (ACP + len) [CB (Z.to_nat 64) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 64))]).
  Variable (CPY12 : rw_cells bsegs m14 ACP [CB (Z.to_nat len) (map (Z_to_bv 8) data)]).
  Variable (AH14 : AHEAP AI L RNG3 (aps_m s3') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m14).
  Variable (PW14 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m14).
  Variable (CS114 : client_static1 m14).
  Lemma apid_t4 :
    evtF bsegs RNG3 (λ ms' : machine_state, implMA RNG3 (parse_impl amalloc_M afree_M (new_handlerA AAllocAsan) data;;; mret ((psb, ptp).1, (psb, ptp).2, (pim, psi, poc, pia), Some pcp)) s3' (apid_post AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB len lo P R m) ms') (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x0' x1' x2' (Z_to_bv 64 R) b1' y0' y1' y2' y3' y4' y5' y6' y7' (Z_to_bv 64 (zlength (strip_bom data))) (Z_to_bv 64 (ACP + (len - zlength (strip_bom data)))) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) ≫ 3 + 2147450880)) x3' x4' x5' x6') F (Z_to_bv 64 613708) fc None m14 (seg_rom bsegs)).
  Proof using All.
    (* [comment removed for export] *)
    assert (INM' : In (HB pim AIM 96) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                                         :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (right; exact INM).
    pose proof (client_img_W AI IMG_CI _ _ _ _ _ _ _ _ _ CI0 PW14 FWF AH14 MI14) as CI14.
    pose proof (client_sh_W AI IMG_CI _ _ _ _ _ CSH PW14 FWF) as CSH14.
    pose proof CI14 as (_ & _ & VTD14 & _). unfold AVTAB_DOM, vtab_dom_cells in VTD14.
    pose proof (client_sh_cell m14 0x10f6d0 CSH14 ltac:(unfold client_sh_addrs; repeat (first [left; reflexivity| right]))) as SHV. change (Z.shiftr 0x10f6d0 3 + 2147450880) with 2147589850 in SHV.
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ (AIM + 48) AH14 INM' ltac:(prnB; lia) ltac:(prnB; lia) ltac:(prnB; Z.div_mod_to_equations; lia)) as (SM48 & RSM48).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ AIM AH14 INM' ltac:(prnB; lia) ltac:(prnB; lia) ltac:(prnB; Z.div_mod_to_equations; lia)) as (SM0 & RSM0).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH14 INM') as (_ & _ & RIM & _).
    destruct (aimpl_split _ _ _ _ _ _ _ _ _ OBJ4) as (O0 & O8 & O12 & O16 & O24 & O28 & O32 & O40 & O48 & O49 & O50 & O56). clear OBJ4.
    unbox RS4. pose proof (rng_fp_le _ _ _ _ FPL13 RS4) as RS_56. clear RS4.
    band_ind (proj1 BRM) bM.
    pose proof (blk_shx_bounds AIM ltac:(prnB; lia) ltac:(prnB; lia)) as SBM0.
    pose proof (blk_shx_bounds (AIM + 48) ltac:(prnB; lia) ltac:(prnB; lia)) as SBM48.
    (* [comment removed for export] *)
    park_memA m14. unfold parkedA in SC4, SC, DST4, PMAX, SM48.
    ltac2:(hide_arith [@LOS; @LOA; @RSP; @STOP; @LY3; @SP16; @RP; @RSPR; @R47; @PR0; @P8; @FK1; @FKH; @FK2; @FKB3; @SB; @SB4; @BRM1; @BRM2; @BRM3; @BRM4;
                       @bFr; @bFhi; @bFlo; @bMr; @bMhi; @bMlo; @DJMF; @SBM0; @SBM48]).
    ltac2:(only_rng [@RS_56]). Time do 5 astep. unhide_rng.
    (* [comment removed for export] *)
    ltac2:(only_rng [@RPR3; @RPP3]). Time do 3 astep. unhide_rng.
    ltac2:(only_rng [@RS_8]). Time do 2 astep. unhide_rng.
    ltac2:(only_rng [@RPR3; @RPP3]). Time do 1 astep. unhide_rng.
    (* [comment removed for export] *)
    ltac2:(only_rng []). zstep. if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by lia; lia|].
    do 2 zstep. if_cases KA; zify_cond KA; [exfalso; exact (KA (land7_of_mod16 AIM BRM4))|]. unhide_rng.
    ltac2:(only_rng [@RSM48]). Time do 5 astep. unhide_rng.
    unhide_arith. unparkA.
    (* [comment removed for export] *)
    pose proof (munch_refl [(AIM + 48, AIM + 49)] m14) as MU15. pose proof (wmono_refl bsegs m14) as WM15.
    park_memA m14. unfold parkedA in O48.
    ltac2:(hide_arith [@BRM1; @BRM2; @BRM3; @BRM4; @bMr; @bMhi; @bMlo; @SBM0; @SBM48]).
    ltac2:(only_rng [@RIM]). Time zstep. unhide_rng.
    unhide_arith. unparkA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m15 eqn:EM15 end. clear EM15.
    Time trmC MU15 WM15 ltac:(fun _ => prnB).
    (* [comment removed for export] *)
    unfold AVTAB_DOM in O0.
    park_memA m15. unfold parkedA in SM0, O0, SHV, VTD14.
    ltac2:(hide_arith [@BRM1; @BRM2; @BRM3; @BRM4; @bMr; @bMhi; @bMlo; @SBM0; @SBM48]).
    ltac2:(only_rng [@RSM0]). Time do 4 astep. unhide_rng.
    ltac2:(only_rng [@RIM]). Time do 1 astep. unhide_rng.
    ltac2:(only_rng [@RISH3]). Time do 4 astep. unhide_rng.
    ltac2:(only_rng [@RI3]). Time do 1 astep. unhide_rng.
    ltac2:(only_rng []). Time do 4 astep. unhide_rng.
    unhide_arith. unparkA.
    assert (AH15 : AHEAP AI L RNG3 (aps_m s3') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                                                :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m15)
      by (eapply (AI_frame AI); [exact AH14| exact MU15| exact WM15|
          apply Forall_cons; [right; left; exists (HB pim AIM 96); split; [exact INM'| cbn; prnB; lia]| apply Forall_nil]]).
    assert (PW15 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m15).
    { eapply aheap_pres_W_trans; [exact PW14|]. eapply aheap_pres_W_of_munch; [exact MU15| exact WM15|].
      intros a Ha Hc Hx. cbn [outside] in Hx |- *.
      pose proof (mid_blk_not_client AI _ _ _ [HB pcp ACP (len + 64); HB pia AIA 1024; HB poc AOC (8 * 1024); HB psi ASI (SIDX_BYTES len);
                    HB pim AIM 96; HB ptp TPA (TAPE_BYTES len); HB psb SBA (SB_BYTES len)] LB _ pim AIM 96 (bv_unsigned sp) a AH15
                    ltac:(do 4 right; left; reflexivity) ltac:(prnB; lia) Hc) as NM.
      clear - Hx NM. lia. }
    pose proof (client_static1_munch32 _ _ _ CS114 MU15 WM15 ltac:(apply Forall_cons; [eapply wfar_ablk; [exact (proj1 BRM)| prnB; lia| prnB; lia]| apply Forall_nil])) as CS115.
    clear AH14 PW14 CS114 MU15 WM15 CI14 CSH14 VTD14 SHV SM48 RSM48 SM0 RSM0 RIM. try drop_mem m14.
    (* [comment removed for export] *)
    apply evtF_done.
    (* [comment removed for export] *)
    assert (ZD : zlength (strip_bom data) <= len /\ len - 3 <= zlength (strip_bom data))
      by (destruct (zlength_strip_bom data) as [E|E]; rewrite E; unfold len; clear; lia).
    destruct (pid_sizesA len ltac:(clear - KC LEN0; lia)) as (SZ1 & SZ2 & SZ3 & SZ4 & SZ5).
    pose proof (sidx_40 len ltac:(clear - KC LEN0; lia)) as SZ6.
    assert (ND7 : List.NoDup [pim; psi; pcp; ptp; psb; poc; pia]).
    { pose proof (AI_hb_ids AI _ _ _ _ _ AH15) as ND. cbn [hb_ids flat_map ab_kind app] in ND. exact (nodup7_permA _ _ _ _ _ _ _ _ ND). }
    assert (NF5 : forall FA' FN', ~ In (mkABlock (ABFake 5) FA' FN') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024)
                     :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
    { intros FA' FN' Hin. unbox LBK. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [discriminate|]).
      destruct (LBK _ Hin) as [(p0 & A0 & n0 & E0)|(c0 & F0 & N0 & E0 & C0)]; [discriminate| injection E0 as E1 _ _; clear - E1 C0; lia]. }
    assert (NF4 : forall FA' FN', ~ In (mkABlock (ABFake 4) FA' FN') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024)
                     :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)).
    { intros FA' FN' Hin. unbox LBK. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [discriminate|]).
      destruct (LBK _ Hin) as [(p0 & A0 & n0 & E0)|(c0 & F0 & N0 & E0 & C0)]; [discriminate| injection E0 as E1 _ _; clear - E1 C0; lia]. }
    assert (BUF15 : bytes_at bsegs m15 (ACP + (len - zlength (strip_bom data))) (s1buf (strip_bom data))).
    { apply buf_stripA. eapply copy_s1bufA; [exact CPY12| | reflexivity| reflexivity]. unfold len. exact SET10. }
    assert (O40' : rw_cells bsegs m15 (AIM + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
    { apply (rw_cells_app_join bsegs _ _ [C8 (Z_to_bv 64 MAX_DEPTH)] [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]); [exact O40|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (AIM + 40 + 8) with (AIM + 48) by lia.
      apply (rw_cells_app_join bsegs _ _ [C1 (Z_to_bv 8 0)] [C1 (Z_to_bv 8 0)]); [exact O48|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (AIM + 48 + 1) with (AIM + 49) by lia. exact O49. }
    destruct (rw_cells_cut bsegs _ _ _ 2 DOC2) as [DOCa _]. cbn [firstn] in DOCa.
    assert (SHD : rw_cells bsegs m15 (Z.shiftr (P + 24) 3 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
    { apply (rw_cells_app_join bsegs _ _ [C1 (Z_to_bv 8 0)] [C1 (Z_to_bv 8 0)]); [exact SC0|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      replace (Z.shiftr (P + 24) 3 + 2147450880 + 1) with (Z.shiftr (P + 32) 3 + 2147450880); [exact SC1|].
      rewrite !Z.shiftr_div_pow2 by (prnB; lia). change (2 ^ 3) with 8. clear - P8. Z.div_mod_to_equations. lia. }
    unbox RSHR. pose proof (rng_fp_le _ _ _ _ FPL13 RSHR) as RSHR3. clear RSHR.
    unbox RSHP. pose proof (rng_fp_le _ _ _ _ FPL13 RSHP) as RSHP3. clear RSHP.
    assert (RSD : rng RNG3 (Z.shiftr (P + 24) 3 + 2147450880) 2).
    { eapply rng_sub'; [exact RSHP3|]. rewrite !Z.shiftr_div_pow2 by (prnB; lia). change (2 ^ 3) with 8. clear - P8 PR0 FKB2 FKH. Z.div_mod_to_equations. lia. }
    assert (RDOC : rng RNG3 (P + 24) 16) by (eapply rng_sub'; [exact RPP3| clear - PR0; lia]).
    (* [comment removed for export] *)
    assert (INT7 : In (HB ptp TPA (TAPE_BYTES len)) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                     :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (do 5 right; left; reflexivity).
    assert (INS7 : In (HB psb SBA (SB_BYTES len)) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                     :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (do 6 right; left; reflexivity).
    assert (INO7 : In (HB poc AOC (8 * 1024)) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                     :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (do 2 right; left; reflexivity).
    assert (INA7 : In (HB pia AIA 1024) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                     :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (do 1 right; left; reflexivity).
    assert (INI7 : In (HB psi ASI (SIDX_BYTES len)) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                     :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (do 3 right; left; reflexivity).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH15 INT7) as (_ & _ & _ & _ & _ & WT & _).
    destruct (rw_cells_of_wr_at bsegs m15 TPA (TAPE_BYTES len) WT (no_image_asan TPA _ ltac:(prnB; lia)) ltac:(prnB; lia)) as (jtp & _ & JT). clear WT.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH15 INS7) as (_ & _ & _ & _ & _ & WS & _).
    destruct (rw_cells_of_wr_at bsegs m15 SBA (SB_BYTES len) WS (no_image_asan SBA _ ltac:(prnB; lia)) ltac:(prnB; lia)) as (jsb & _ & JS). clear WS.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH15 INO7) as (_ & _ & _ & _ & _ & WO & _).
    destruct (rw_cells_of_wr_at bsegs m15 AOC (8 * 1024) WO (no_image_asan AOC _ ltac:(prnB; lia)) ltac:(prnB; lia)) as (joc & _ & JO). clear WO.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH15 INA7) as (_ & _ & _ & _ & _ & WA & _).
    destruct (rw_cells_of_wr_at bsegs m15 AIA 1024 WA (no_image_asan AIA _ ltac:(prnB; lia)) ltac:(prnB; lia)) as (jia & _ & JA). clear WA.
    pose proof (client_img_W AI IMG_CI _ _ _ _ _ _ _ _ _ CI0 PW15 FWF AH15 ltac:(eassumption)) as CI15.
    pose proof (client_sh_W AI IMG_CI _ _ _ _ _ CSH PW15 FWF) as CSH15.
    assert (RC15 : rclean m15 rstk).
    { eapply (rclean_W AI _ _ _ _ _ _ RCL PW15 RCL3). intros a Ha. unfold apid_W, client_wr. cbn [app outside].
      pose proof RCL as ((_ & (H1 & H2 & H3 & H4 & H5 & H6) & _ & _) & _). unfold KEND in H6. pose proof atop_range as AR.
      rewrite !shad_div in Ha. unfold ASHOFF in Ha. clear - Ha H1 H2 H3 H4 H5 H6 AR RCL3 FK1 FKH FK2 FKB3 FKB2 RP RSPR LOA LOS PR0 bFr bFhi bFlo. Z.div_mod_to_equations. lia. }
    unbox RRNG. unfold rrng in RRNG. pose proof (rng_fp_le _ _ _ _ FPL13 RRNG) as RRNG3.
    unbox UCR. unbox PRO.
    assert (UC15 : uchain m15 (al_top L) AFREE_PC (bv_unsigned sp + -112) R (Nat.pred UDEPTH) trR).
    { replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia.
      eapply (uchain_keepR m m15 _ _ _ R _ _ jr UCR); [| exact PRO | exact PR | clear - PR0 FK1 FKB1; unfold AIMG_HI in *; lia | clear - R47; lia].
      intros a Ha Hr.
      assert (HA : 0 <= a < 2 ^ 64 /\ bv_unsigned sp <= a < 2 ^ 47) by (clear - Ha RSPR LY3 RSP; lia).
      destruct (PW15 a ltac:(clear - HA; lia) ltac:(left; clear - HA; lia)) as [E _]; [| exact E].
      unfold apid_W, client_wr. cbn [app outside]. clear - Ha Hr HA FK2 FKB3 LOA LOS H. lia. }
    assert (USP3 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; clear - LOS LOA RSP; lia).
    eapply implMA_bind.
    { idtac "PARSECALL". pose proof PARSE as PS. unfold parse_stmtA in PS. cbv zeta in PS.
      Time eapply PS with (lo := lo) (rstk := rstk) (data := data) (tr0 := trR) (pim := pim) (psi := psi) (pcp := pcp) (ptp := ptp) (psb := psb)
        (poc := poc) (pia := pia) (THIS := AIM) (ASI := ASI) (ACP := ACP) (TPA := TPA) (SBA := SBA) (AOC := AOC) (AIA := AIA) (DOC := P + 24)
        (BUF := ACP + (len - zlength (strip_bom data))) (nim := 96) (nsi := SIDX_BYTES len) (ncp := len + 64) (ntp := TAPE_BYTES len)
        (nsb := SB_BYTES len) (noc := 8 * 1024) (nia := 1024) (x8 := Z_to_bv 64 0) (x24 := Z_to_bv 64 0) (x72 := Z_to_bv 64 0)
        (x80 := Z_to_bv 64 0) (x88 := Z_to_bv 64 0) (jtp := jtp) (jsb := jsb) (joc := joc) (jia := jia);
        try reflexivity; rewrite ?USP3;
        first [ eassumption | exact ND7 | exact NF5 | exact NF4 | exact BUF15 | exact (Forall_strip_bom _ _ DB) | exact O40' | exact IMG_CI
                  | exact (RFSM _ _ _ FPL13 RFS) | (eapply aps_ok_rest; [exact ARS13| exact AOK])
                  | (exists fcls, FA, FN; split; [do 7 right; exact INF| split; [clear - FKH; lia| split; [clear - FK2; lia| exact FKB]]])
                  | (rewrite (unsigned_lit R) by (clear - PR0 R47; lia); exact UC15)
                  | (right; rewrite (unsigned_lit R) by (clear - PR0 R47; lia); clear - RSPR; lia)
                  | (cbn [length]; lia) | (rewrite unsigned_lit by lia; lia) | (rewrite unsigned_lit by lia; unfold AFREE_PC; lia)
                  | (unfold APARSE_STACK, STAGE2_STACK_A; clear - LOS; lia) | (clear - RCL2; lia) | (clear - STOP; lia) | (clear - SP16; lia)
                  | (clear - ZD SZ1 SZ2 SZ3 SZ4 SZ5 SZ6 KC LEN0 P8; lia) ]. }
    cbv beta. intros [] s4' RNG4 ms16 (FPL4 & q0' & q1' & q2' & z0' & z1' & z2' & z3' & z4' & z5' & z6' & z7' & q3' & q4' & q5' & q6' & F16 & fc16 & m16
                                       & -> & A064 & FZ16 & MI16 & ST16 & PWP & ARS4 & AH16).
    rewrite ?USP3 in ST16. rewrite ?USP3 in PWP.
    (* [comment removed for export] *)
    destruct (rw_cells_cut bsegs _ _ _ 2 O56) as [O56a _]. cbn [firstn] in O56a. clear O56.
    Local Ltac tclr H := try clear H.
    tclr O8. tclr O12. tclr O24. tclr O28. tclr O32. tclr O40'. tclr O40. tclr O48. tclr O49. tclr O50. tclr CPY12. tclr SET10. tclr BUF15.
    tclr JT. tclr JS. tclr JO. tclr JA. tclr SHD. tclr SC0. tclr SC1. tclr SC2. tclr SC3. tclr SC4. tclr SC5. tclr SC6. tclr SC. tclr PMAX.
    tclr SM48. tclr SM0. tclr SHV. tclr VTD14.
    assert (INF7 : In (mkABlock (ABFake fcls) FA FN) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                     :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (do 7 right; exact INF).
    band_ind (proj1 BRI) bI. band_ind (proj1 BRT) bT. band_ind (proj1 BRS) bS. band_ind (proj1 BRO) bO. band_ind (proj1 BRA) bA.
    pose proof (nodup7A _ _ _ _ _ _ _ ND7) as (N12 & N13 & N14 & N15 & N16 & N17 & _).
    Local Ltac djb AH H1 H2 := let X := fresh "X" in
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH H1 H2 ltac:(first [discriminate| intros E; injection E; intros; congruence])) as X;
      cbn [ab_addr ab_size] in X; exact X.
    assert (DJIF : ASI + SIDX_BYTES len <= FA \/ FA + FN <= ASI) by djb AH16 INI7 INF7.
    assert (DJTF : TPA + TAPE_BYTES len <= FA \/ FA + FN <= TPA) by djb AH16 INT7 INF7.
    assert (DJSF : SBA + SB_BYTES len <= FA \/ FA + FN <= SBA) by djb AH16 INS7 INF7.
    assert (DJOF : AOC + 8 * 1024 <= FA \/ FA + FN <= AOC) by djb AH16 INO7 INF7.
    assert (DJAF : AIA + 1024 <= FA \/ FA + FN <= AIA) by djb AH16 INA7 INF7.
    assert (DJIM : ASI + SIDX_BYTES len <= AIM \/ AIM + 96 <= ASI) by djb AH16 INI7 INM'.
    assert (DJTM : TPA + TAPE_BYTES len <= AIM \/ AIM + 96 <= TPA) by djb AH16 INT7 INM'.
    assert (DJSM : SBA + SB_BYTES len <= AIM \/ AIM + 96 <= SBA) by djb AH16 INS7 INM'.
    assert (DJOM : AOC + 8 * 1024 <= AIM \/ AIM + 96 <= AOC) by djb AH16 INO7 INM'.
    assert (DJAM : AIA + 1024 <= AIM \/ AIM + 96 <= AIA) by djb AH16 INA7 INM'.
    Local Ltac blk Ha DJF bXr bXhi bXlo BRX1 BRX3 DJXM :=
      first [ (revert Ha; clear - LOA LOS STOP LY3 RSP BRX3 RSPR; lia)
            | (revert Ha; clear - FK1 FK2 FKH RP PR0 R8 P8 DJF; lia)
            | (revert Ha; clear - SB7 SB8 SB9 bXr bXhi bXlo BRX1 BRX3; lia)
            | (revert Ha; clear - BRM1 BRM3 DJXM; lia) ].
    Local Ltac aimp Ha DJMF bMr bMhi bMlo :=
      first [ (left; first [ (revert Ha; clear - LOA LOS STOP LY3 RSP BRM3 RSPR; lia) | (revert Ha; clear - FK1 FK2 FKH RP PR0 R8 P8 DJMF; lia)
                           | (revert Ha; clear - SB7 SB8 SB9 bMr bMhi bMlo BRM1 BRM3; lia) ])
            | (right; left; revert Ha; clear; lia) | (right; right; left; revert Ha; clear; lia) | (right; right; right; revert Ha; clear; lia) ].
    idtac "TPW".
    lazymatch type of FR with rw_cells bsegs ?mo ?A ?cs =>
      assert (TFR : rw_cells bsegs m16 A cs)
        by (eapply aheap_pres_W_rw_cells; [exact PWP| exact FR| acrC INF7 IMG_CI ltac:(fun _ => prnB)|];
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
            apply (parse_win_out _ _ _ _ _ _ _ _ _ _ (SIDX_BYTES len));
            [ clear - SZ1 ZD; lia | aimp Ha DJMF bMr bMhi bMlo
            | blk Ha DJIF bIr bIhi bIlo BRI1 BRI3 DJIM | blk Ha DJTF bTr bThi bTlo BRT1 BRT3 DJTM | blk Ha DJSF bSr bShi bSlo BRS1 BRS3 DJSM
            | blk Ha DJOF bOr bOhi bOlo BRO1 BRO3 DJOM | blk Ha DJAF bAr bAhi bAlo BRA1 BRA3 DJAM ])
    end. clear FR. rename TFR into FR.
    lazymatch type of PR with rw_cells bsegs ?mo ?A ?cs =>
      assert (TPR : rw_cells bsegs m16 A cs)
        by (eapply aheap_pres_W_rw_cells; [exact PWP| exact PR| acrC INF7 IMG_CI ltac:(fun _ => prnB)|];
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
            apply (parse_win_out _ _ _ _ _ _ _ _ _ _ (SIDX_BYTES len));
            [ clear - SZ1 ZD; lia | aimp Ha DJMF bMr bMhi bMlo
            | blk Ha DJIF bIr bIhi bIlo BRI1 BRI3 DJIM | blk Ha DJTF bTr bThi bTlo BRT1 BRT3 DJTM | blk Ha DJSF bSr bShi bSlo BRS1 BRS3 DJSM
            | blk Ha DJOF bOr bOhi bOlo BRO1 BRO3 DJOM | blk Ha DJAF bAr bAhi bAlo BRA1 BRA3 DJAM ])
    end. clear PR. rename TPR into PR.
    lazymatch type of SC7 with rw_cells bsegs ?mo ?A ?cs =>
      assert (TSC7 : rw_cells bsegs m16 A cs)
        by (eapply aheap_pres_W_rw_cells; [exact PWP| exact SC7| acrC INF7 IMG_CI ltac:(fun _ => prnB)|];
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
            apply (parse_win_out _ _ _ _ _ _ _ _ _ _ (SIDX_BYTES len));
            [ clear - SZ1 ZD; lia | aimp Ha DJMF bMr bMhi bMlo
            | blk Ha DJIF bIr bIhi bIlo BRI1 BRI3 DJIM | blk Ha DJTF bTr bThi bTlo BRT1 BRT3 DJTM | blk Ha DJSF bSr bShi bSlo BRS1 BRS3 DJSM
            | blk Ha DJOF bOr bOhi bOlo BRO1 BRO3 DJOM | blk Ha DJAF bAr bAhi bAlo BRA1 BRA3 DJAM ])
    end. clear SC7. rename TSC7 into SC7.
    lazymatch type of SC8 with rw_cells bsegs ?mo ?A ?cs =>
      assert (TSC8 : rw_cells bsegs m16 A cs)
        by (eapply aheap_pres_W_rw_cells; [exact PWP| exact SC8| acrC INF7 IMG_CI ltac:(fun _ => prnB)|];
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
            apply (parse_win_out _ _ _ _ _ _ _ _ _ _ (SIDX_BYTES len));
            [ clear - SZ1 ZD; lia | aimp Ha DJMF bMr bMhi bMlo
            | blk Ha DJIF bIr bIhi bIlo BRI1 BRI3 DJIM | blk Ha DJTF bTr bThi bTlo BRT1 BRT3 DJTM | blk Ha DJSF bSr bShi bSlo BRS1 BRS3 DJSM
            | blk Ha DJOF bOr bOhi bOlo BRO1 BRO3 DJOM | blk Ha DJAF bAr bAhi bAlo BRA1 BRA3 DJAM ])
    end. clear SC8. rename TSC8 into SC8.
    lazymatch type of SC9 with rw_cells bsegs ?mo ?A ?cs =>
      assert (TSC9 : rw_cells bsegs m16 A cs)
        by (eapply aheap_pres_W_rw_cells; [exact PWP| exact SC9| acrC INF7 IMG_CI ltac:(fun _ => prnB)|];
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
            apply (parse_win_out _ _ _ _ _ _ _ _ _ _ (SIDX_BYTES len));
            [ clear - SZ1 ZD; lia | aimp Ha DJMF bMr bMhi bMlo
            | blk Ha DJIF bIr bIhi bIlo BRI1 BRI3 DJIM | blk Ha DJTF bTr bThi bTlo BRT1 BRT3 DJTM | blk Ha DJSF bSr bShi bSlo BRS1 BRS3 DJSM
            | blk Ha DJOF bOr bOhi bOlo BRO1 BRO3 DJOM | blk Ha DJAF bAr bAhi bAlo BRA1 BRA3 DJAM ])
    end. clear SC9. rename TSC9 into SC9.
    lazymatch type of DST4 with rw_cells bsegs ?mo ?A ?cs =>
      assert (TDST4 : rw_cells bsegs m16 A cs)
        by (eapply aheap_pres_W_rw_cells; [exact PWP| exact DST4| acrC INF7 IMG_CI ltac:(fun _ => prnB)|];
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
            apply (parse_win_out _ _ _ _ _ _ _ _ _ _ (SIDX_BYTES len));
            [ clear - SZ1 ZD; lia | aimp Ha DJMF bMr bMhi bMlo
            | blk Ha DJIF bIr bIhi bIlo BRI1 BRI3 DJIM | blk Ha DJTF bTr bThi bTlo BRT1 BRT3 DJTM | blk Ha DJSF bSr bShi bSlo BRS1 BRS3 DJSM
            | blk Ha DJOF bOr bOhi bOlo BRO1 BRO3 DJOM | blk Ha DJAF bAr bAhi bAlo BRA1 BRA3 DJAM ])
    end. clear DST4. rename TDST4 into DST4.
    lazymatch type of DOCa with rw_cells bsegs ?mo ?A ?cs =>
      assert (TDOCa : rw_cells bsegs m16 A cs)
        by (eapply aheap_pres_W_rw_cells; [exact PWP| exact DOCa| acrC INF7 IMG_CI ltac:(fun _ => prnB)|];
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
            apply (parse_win_out _ _ _ _ _ _ _ _ _ _ (SIDX_BYTES len));
            [ clear - SZ1 ZD; lia | aimp Ha DJMF bMr bMhi bMlo
            | blk Ha DJIF bIr bIhi bIlo BRI1 BRI3 DJIM | blk Ha DJTF bTr bThi bTlo BRT1 BRT3 DJTM | blk Ha DJSF bSr bShi bSlo BRS1 BRS3 DJSM
            | blk Ha DJOF bOr bOhi bOlo BRO1 BRO3 DJOM | blk Ha DJAF bAr bAhi bAlo BRA1 BRA3 DJAM ])
    end. clear DOCa. rename TDOCa into DOCa.
    lazymatch type of PCP with rw_cells bsegs ?mo ?A ?cs =>
      assert (TPCP : rw_cells bsegs m16 A cs)
        by (eapply aheap_pres_W_rw_cells; [exact PWP| exact PCP| acrC INF7 IMG_CI ltac:(fun _ => prnB)|];
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
            apply (parse_win_out _ _ _ _ _ _ _ _ _ _ (SIDX_BYTES len));
            [ clear - SZ1 ZD; lia | aimp Ha DJMF bMr bMhi bMlo
            | blk Ha DJIF bIr bIhi bIlo BRI1 BRI3 DJIM | blk Ha DJTF bTr bThi bTlo BRT1 BRT3 DJTM | blk Ha DJSF bSr bShi bSlo BRS1 BRS3 DJSM
            | blk Ha DJOF bOr bOhi bOlo BRO1 BRO3 DJOM | blk Ha DJAF bAr bAhi bAlo BRA1 BRA3 DJAM ])
    end. clear PCP. rename TPCP into PCP.
    lazymatch type of O0 with rw_cells bsegs ?mo ?A ?cs =>
      assert (TO0 : rw_cells bsegs m16 A cs)
        by (eapply aheap_pres_W_rw_cells; [exact PWP| exact O0| acrC INF7 IMG_CI ltac:(fun _ => prnB)|];
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
            apply (parse_win_out _ _ _ _ _ _ _ _ _ _ (SIDX_BYTES len));
            [ clear - SZ1 ZD; lia | aimp Ha DJMF bMr bMhi bMlo
            | blk Ha DJIF bIr bIhi bIlo BRI1 BRI3 DJIM | blk Ha DJTF bTr bThi bTlo BRT1 BRT3 DJTM | blk Ha DJSF bSr bShi bSlo BRS1 BRS3 DJSM
            | blk Ha DJOF bOr bOhi bOlo BRO1 BRO3 DJOM | blk Ha DJAF bAr bAhi bAlo BRA1 BRA3 DJAM ])
    end. clear O0. rename TO0 into O0.
    lazymatch type of O16 with rw_cells bsegs ?mo ?A ?cs =>
      assert (TO16 : rw_cells bsegs m16 A cs)
        by (eapply aheap_pres_W_rw_cells; [exact PWP| exact O16| acrC INF7 IMG_CI ltac:(fun _ => prnB)|];
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
            apply (parse_win_out _ _ _ _ _ _ _ _ _ _ (SIDX_BYTES len));
            [ clear - SZ1 ZD; lia | aimp Ha DJMF bMr bMhi bMlo
            | blk Ha DJIF bIr bIhi bIlo BRI1 BRI3 DJIM | blk Ha DJTF bTr bThi bTlo BRT1 BRT3 DJTM | blk Ha DJSF bSr bShi bSlo BRS1 BRS3 DJSM
            | blk Ha DJOF bOr bOhi bOlo BRO1 BRO3 DJOM | blk Ha DJAF bAr bAhi bAlo BRA1 BRA3 DJAM ])
    end. clear O16. rename TO16 into O16.
    lazymatch type of O56a with rw_cells bsegs ?mo ?A ?cs =>
      assert (TO56a : rw_cells bsegs m16 A cs)
        by (eapply aheap_pres_W_rw_cells; [exact PWP| exact O56a| acrC INF7 IMG_CI ltac:(fun _ => prnB)|];
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
            apply (parse_win_out _ _ _ _ _ _ _ _ _ _ (SIDX_BYTES len));
            [ clear - SZ1 ZD; lia | aimp Ha DJMF bMr bMhi bMlo
            | blk Ha DJIF bIr bIhi bIlo BRI1 BRI3 DJIM | blk Ha DJTF bTr bThi bTlo BRT1 BRT3 DJTM | blk Ha DJSF bSr bShi bSlo BRS1 BRS3 DJSM
            | blk Ha DJOF bOr bOhi bOlo BRO1 BRO3 DJOM | blk Ha DJAF bAr bAhi bAlo BRA1 BRA3 DJAM ])
    end. clear O56a. rename TO56a into O56a.
    idtac "TPWEND".

    assert (PW16 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m16).
    { eapply aheap_pres_W_trans; [exact PW15|]. intros a Ha Hc Hx.
      assert (HcL : aclient_addr CI (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                     :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) (bv_unsigned sp + -112) a)
        by (eapply aclient_addr_mono_sp; [eapply aclient_addr_mono_lb; [exact Hc| intros b Hb; do 7 right; exact Hb]| clear; lia]).
      Local Ltac nmb AH Hc p A n := let NM := fresh "NM" in
        pose proof (mid_blk_not_client AI _ _ _ [HB pcp ACP (len + 64); HB pia AIA 1024; HB poc AOC (8 * 1024); HB psi ASI (SIDX_BYTES len);
                    HB pim AIM 96; HB ptp TPA (TAPE_BYTES len); HB psb SBA (SB_BYTES len)] LB _ p A n (bv_unsigned sp) _ AH
                    ltac:(repeat (first [left; reflexivity| right])) ltac:(prnB; lia) Hc) as NM.
      nmb AH15 Hc pia AIA 1024. nmb AH15 Hc poc AOC (8 * 1024). nmb AH15 Hc psi ASI (SIDX_BYTES len). nmb AH15 Hc pim AIM 96.
      nmb AH15 Hc ptp TPA (TAPE_BYTES len). nmb AH15 Hc psb SBA (SB_BYTES len).
      apply PWP; [exact Ha| exact HcL|]. unfold parse_winA. cbn [outside].
      clear - NM NM0 NM1 NM2 NM3 NM4 ZD LEN0 SZ1. lia. }
    pose proof (client_static1_W AI IMG_CI _ _ _ _ _ PWP
                  ltac:(unfold parse_winA; repeat (apply Forall_cons; [cbn [fst snd]; right; prnB; lia|]); apply Forall_nil) CS115) as CS116.
    clear PWP PW15 CS115 AH15. try drop_mem m15.
    clear DJIF DJTF DJSF DJOF DJAF DJIM DJTM DJSM DJOM DJAM DJM DJF N12 N13 N14 N15 N16 N17.
    exact (apid_t5 AI rng_fs ONTA ODA IMG_CI PARSE RFSM L RNG ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo rstk data D P R jr trR LBK PAY DAT DB
       D16 DL CI0 CSH fcls FA FN INF FKH FK2 FKB RP R8 P8 RSPR RHI LOA LOS RCL RCL1 RCL2 RCL3 RRNG STOP SP16 FZ TP HUL UCR TRR RFS AOK AFR DKW PRO RSP H
       FK1 FKB1 FKB2 FKB3 FKB4 bF bFr bFhi bFlo LY1 LY2 LY3 LEN0 CAPR R47 PR0 SB SB0 SB1 SB2 SB3 SB4 SB5 SB6 SB7 SB8 SB9 RS0 RS1 RS2 RS3 RS7 RS8 RS9 junk
       K1 K2 psb ptp s1' SBA TPA BRS BRT AFR1 DK1 FWF HUM pim psi poc pia s2' RNG2 w0' w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 AIM ASI AOC AIA p1 p2 pad
       BRM BRI BRO BRA AFR2 DK2 BRM1 BRM2 BRM3 BRM4 BRI1 BRI2 BRI3 BRI4 BRO1 BRO2 BRO3 BRO4 BRA1 BRA2 BRA3 BRA4 BRS1 BRS2 BRS3 BRS4 BRT1 BRT2 BRT3 BRT4
       DJMF KC SZC pcp s3' RNG3 x0 x1 x2 e1 e2 e3 e4 e5 e6 e7 x3 x4 x5 x6 ACP jcp BRC RC1 RC2 AFR3 DK3 BRC1 BRC2 BRC3 BRC4 bC bCr bChi bClo INM RSTK3 RI3
       RISH3 RPR3 RPP3 RS_8 RS_64 FPL13 ARS13 INC z0 z1 z2 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 m1 RS_72 h0 h1 h2 i1 i2 i3 i4 i5 i6 i7 h3 h4 h5 h6 ra' x0' x1'
       x2' b1' y0' y1' y2' y3' y4' y5' y6' y7' x3' x4' x5' x6' m0 INM' RS_56 bM bMr bMhi bMlo SBM0 SBM48 KN KA ZD SZ1 SZ2 SZ3 SZ4 SZ5 SZ6 ND7 NF5 NF4
       RSHR3 RSHP3 RSD RDOC INT7 INS7 INO7 INA7 INI7 jtp jsb joc jia RRNG3 USP3 s4' RNG4 FPL4 q0' q1' q2' z0' z1' z2' z3' z4' z5' z6' z7' q3' q4' q5' q6'
       F16 fc16 m16 A064 FZ16 MI16 ST16 ARS4 AH16 INF7 bI bIr bIhi bIlo bT bTr bThi bTlo bS bSr bShi bSlo bO bOr bOhi bOlo bA bAr bAhi bAlo FR PR SC7 SC8
       SC9 DST4 DOCa PCP O0 O16 O56a PW16 CS116).
  Qed.
End T.
End S.
End CANSEC1.
