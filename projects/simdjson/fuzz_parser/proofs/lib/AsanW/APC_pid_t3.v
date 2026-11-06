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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import APC_pid_t4.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
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
  Variable (RSHR : boxed (rng RNG (R ≫ 3 + 2147450880) ((R + 24) ≫ 3 + 2147450880 - (R ≫ 3 + 2147450880)))).
  Variable (RSHP : boxed (rng RNG (P ≫ 3 + 2147450880) ((P + 80) ≫ 3 + 2147450880 - (P ≫ 3 + 2147450880)))).
  Variable (RSPR : bv_unsigned sp + 16 <= R).
  Variable (RHI : R + 24 <= r_hi rstk).
  Variable (R47 : R + 24 <= 2 ^ 47).
  Variable (LOA : ATOP + 4096 <= lo).
  Variable (LOS : lo <= bv_unsigned sp - (112 + (32 + (416 + 8192)))).
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
  Variable (UCR : boxed (uchain m (al_top L) AFREE_PC (bv_unsigned sp - 112) R (Nat.pred UDEPTH) trR)).
  Variable (TRR : (length trR <= 27)%nat).
  Variable (PRO : boxed (rw_cells asegs m R [CB 24 jr])).
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
  Variable (RS4 : boxed (rng RNG ((P + 56) ≫ 3 + 2147450880) 1)).
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
  Variable (h0 h1 h2 i1 i2 i3 i4 i5 i6 i7 h3 h4 h5 h6 : word).
  Variable (m12 : amem).
  Variable (MI12 : mem_inv asegs m12).
  Variable (ST12 : stk asegs m12 lo (bv_unsigned sp + -112)).
  Variable (CPY12 : rw_cells asegs m12 ACP [CB (Z.to_nat len) (map (Z_to_bv 8) data)]).
  Variable (SET10 : rw_cells asegs m12 (ACP + len) [CB (Z.to_nat 64) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 64))]).
  Variable (SC9 : rw_cells asegs m12 ((R + 16) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC8 : rw_cells asegs m12 ((R + 8) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC7 : rw_cells asegs m12 (R ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC4 : rw_cells asegs m12 ((P + 56) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC3 : rw_cells asegs m12 ((P + 48) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC2 : rw_cells asegs m12 ((P + 40) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC1 : rw_cells asegs m12 ((P + 32) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC0 : rw_cells asegs m12 ((P + 24) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC : rw_cells asegs m12 ((P + 8) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (PR : rw_cells asegs m12 R [CB 24 jr]).
  Variable (PMAX : rw_cells asegs m12 (P + 48) [C8 (Z_to_bv 64 4294967295); C1 (Z_to_bv 8 0)]).
  Variable (DOC2 : rw_cells asegs m12 (P + 24) [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA); C8 (Z_to_bv 64 (CAP len))]).
  Variable (OBJ4 : rw_cells asegs m12 AIM [C8 (Z_to_bv 64 AVTAB_DOM); C4 (Z_to_bv 64 0); CB 4 p1; C8 (Z_to_bv 64 ASI); C4 (Z_to_bv 64 0); CB 4 p2; C8 (Z_to_bv 64 (CAP len)); C8 (Z_to_bv 64 1024); C2 (Z_to_bv 64 0); CB 6 pad; C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  Variable (DST4 : rw_cells asegs m12 (P + 8) [C8 (Z_to_bv 64 AIM)]).
  Variable (PCP : rw_cells asegs m12 (P + 64) [C8 (Z_to_bv 64 ACP); C8 (Z_to_bv 64 len)]).
  Variable (SC6 : rw_cells asegs m12 ((P + 72) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (FR : rw_cells asegs m12 (bv_unsigned sp + -112) [C8 (Z_to_bv 64 (P + 24)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Variable (SC5 : rw_cells asegs m12 ((P + 64) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (AH12 : AHEAP AI L RNG3 (aps_m s3') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m12).
  Variable (PW12 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m12).
  Variable (CS112 : client_static1 m12).
  Variable (AFR3 : AFRESH (aps_m s3')).
  Variable (DK3 : dk (aps_m s3') < DWMAX).
  Lemma apid_t3 :
    evtF asegs RNG3 (λ ms' : machine_state, implMA RNG3 (parse_impl amalloc_M afree_M (new_handlerA AAllocAsan) data;;; mret ((psb, ptp).1, (psb, ptp).2, (pim, psi, poc, pia), Some pcp)) s3' (apid_post AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB len lo P R m) ms') (MS (mkR (Z_to_bv 64 614172) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp h0 h1 h2 (Z_to_bv 64 R) (Z_to_bv 64 ((P + 64) ≫ 3 + 2147450880)) (Z_to_bv 64 ACP) i1 i2 i3 i4 i5 i6 i7 (Z_to_bv 64 len) (Z_to_bv 64 D) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) ≫ 3 + 2147450880)) h3 h4 h5 h6) F (Z_to_bv 64 614172) fc None m12 (seg_rom asegs)).

  Proof using All.
    (* [comment removed for export] *)
    pose proof (client_img_W AI IMG_CI _ _ _ _ _ _ _ _ _ CI0 PW12 FWF AH12 MI12) as CI12.
    pose proof (client_img_x _ CI12) as (RMC & FMIN & BOMS & CTS & ISH).
    pose proof (rt_flags_of_aheap AI _ _ _ _ _ AH12) as FLG.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH12) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
    unfold rt_real_mc, rt_flags, rt_bom_sh, AREAL_MC, AMCFLAGS, ABOM in RMC, FLG, BOMS. change (shad 0x22ec0) with 2147468760 in BOMS.
    clear FMIN CTS ISH SUA.
    Time eapply (evtF_cut asegs RNG3 (fun x => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : amem),
        x = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 R) (Z_to_bv 64 ((P + 64) ≫ 3 + 2147450880))
                a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (zlength (strip_bom data))) (Z_to_bv 64 (ACP + (len - zlength (strip_bom data))))
                (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
                (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) ≫ 3 + 2147450880)) t3' t4' t5' t6') F (Z_to_bv 64 0x95f48) fc None m' (seg_rom asegs)
        /\ munch [(lo, bv_unsigned sp + -112)] m12 m' /\ wmono asegs m12 m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -112))).
    { Time (park_memA m12; unfold parkedA in PCP).
      ltac2:(hide_arith [@LOS; @LOA; @RSP; @STOP; @LY3; @SP16; @RP; @RSPR; @R47; @PR0; @P8; @FK1; @FKH; @FK2; @FKB3; @LEN0; @DL; @KC]).
      ltac2:(only_rng [@RPR3; @RPP3]).
      do 3 zstep.
      unhide_rng. unhide_arith. unparkA.
      if_cases K3; zify_cond K3.
      - (* [comment removed for export] *)
        assert (SBD : strip_bom data = data) by (apply strip_bom_short; unfold len, zlength in K3; clear - K3; lia).
        rewrite SBD. replace (ACP + (len - zlength data)) with ACP by (unfold len; clear; lia).
        apply evtF_done. Time (do 17 eexists; split; [reflexivity|]). split; [apply munch_refl|]. split; [apply wmono_refl|]. split; eassumption.
      - (* [comment removed for export] *)
        destruct (list3 data ltac:(unfold len, zlength in K3; clear - K3; lia)) as (q0 & q1 & q2 & r & EDATA).
        pose proof DB as DB'. rewrite EDATA in DB'. apply Forall_cons_iff in DB' as [XB0 DB']. apply Forall_cons_iff in DB' as [XB1 DB'].
        apply Forall_cons_iff in DB' as [XB2 _].
        assert (RL : zlength r = len - 3) by (unfold len; rewrite EDATA; unfold zlength; cbn [length]; clear; lia).
        pose proof (proj2 (proj1 CPY12)) as BC. cbn [cells_bytes cbytes] in BC. rewrite app_nil_r in BC. rewrite EDATA in BC. cbn [map] in BC.
        change (Z_to_bv 8 q0 :: Z_to_bv 8 q1 :: Z_to_bv 8 q2 :: map (Z_to_bv 8) r)
          with ([Z_to_bv 8 q0; Z_to_bv 8 q1; Z_to_bv 8 q2] ++ map (Z_to_bv 8) r) in BC.
        apply bytes_at_app_split in BC as [B1 _].
        assert (B2 : bytes_at asegs m12 0x22ee0 [Z_to_bv 8 239; Z_to_bv 8 187; Z_to_bv 8 191]).
        { pose proof (ro_cells_image asegs m12 0x22ee0 [Z_to_bv 8 239; Z_to_bv 8 187; Z_to_bv 8 191] MI12 ltac:(vm_compute; reflexivity)
                        ltac:(lia) ltac:(cbn; lia)) as RC. destruct RC as [_ RC]. cbn [cells_bytes cbytes app] in RC. exact RC. }
        destruct (blk_window_facts AI _ _ _ _ _ _ _ _ ACP 3 AH12 INC ltac:(lia) ltac:(prnB; lia) ltac:(lia)) as (APC3 & UNP3 & RC3 & (RLO1 & RHI1 & HU1 & WH1 & RH1)).
        assert (WHB : wr_at asegs m12 (shad 0x22ec0) (shad 0x22f00 - shad 0x22ec0)) by (change (shad 0x22ec0) with 2147468760; exact (proj2 BOMS)).
        assert (RHB : rng RNG3 (shad 0x22ec0) (shad 0x22f00 - shad 0x22ec0))
          by (change (shad 0x22ec0) with 2147468760; change (shad 0x22f00) with 2147468768; eapply rng_sub'; [exact RISH3| lia]).
        assert (RB3 : rng RNG3 0x22ee0 3) by (eapply rng_sub'; [exact RI3| lia]).
        assert (UNB : unpoisoned m12 0x22ee0 0x22ee3) by (apply unpoisoned_bom; unfold rt_bom_sh, ABOM; change (shad 0x22ec0) with 2147468760; exact BOMS).
        assert (APB : app_blk 0x22ee0 (0x22ee0 + 3)) by (unfold app_blk, KLOW, KHIGH, KEND; lia).
        assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; clear - LOS LOA RSP; lia).
        assert (UCP : bv_unsigned (Z_to_bv 64 ACP) = ACP) by (apply unsigned_lit; prnB; lia).
        assert (RSM : rng RNG3 lo (bv_unsigned sp + -112 - lo)) by (eapply rng_sub'; [exact RSTK3| clear - LOS LOA RSP STOP LY3; lia]).
        park_memA m12. unfold parkedA in FR.
        ltac2:(hide_arith [@LOS; @LOA; @RSP; @STOP; @LY3; @SP16; @LEN0; @DL; @K3]).
        Time steps_to 0x55828. zstep.
        unhide_arith. unparkA.
        eapply evtF_cut.
        { Time eapply bcmp_icpt_spec.
          Time eapply (mc_pre_i RNG3 _ _ lo _ _ _ [Z_to_bv 8 q0; Z_to_bv 8 q1; Z_to_bv 8 q2] [Z_to_bv 8 239; Z_to_bv 8 187; Z_to_bv 8 191]
                            RLO1 RHI1 0x22ec0 0x22f00); rewrite ?USP, ?UCP, ?(unsigned_lit 3), ?(unsigned_lit 0x22ee0) by lia;
            first [ eassumption | reflexivity | (unfold KHIGH; clear - LOA; lia) | (clear - LOS; lia) | (left; prnB; lia) | (left; clear - LOA; lia)
                      | (unfold KEND; lia) ]. }
        cbv beta. intros ms13 (k0 & k1 & k2 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & k3 & k4 & k5 & k6 & m13 & -> & MU13 & WM13 & MI13 & ST13).
        rewrite ?USP in MU13. rewrite ?USP in ST13. retlit.
        pose proof (memcmp_res_bound [Z_to_bv 8 q0; Z_to_bv 8 q1; Z_to_bv 8 q2] [Z_to_bv 8 239; Z_to_bv 8 187; Z_to_bv 8 191]) as MRB.
        pose proof (bom_res q0 q1 q2 XB0 XB1 XB2) as BR.
        assert (MU13' : munch [(lo, bv_unsigned sp + -112)] m12 m13)
          by (eapply munch_weaken; [| exact MU13]; intros x Hx; cbn [outside] in *; clear - Hx LOS; lia).
        destruct (Z.eq_dec (memcmp_res [Z_to_bv 8 q0; Z_to_bv 8 q1; Z_to_bv 8 q2] [Z_to_bv 8 239; Z_to_bv 8 187; Z_to_bv 8 191]) 0) as [EZ|NZ].
        + (* [comment removed for export] *)
          rewrite EZ. apply BR in EZ as (-> & -> & ->).
          assert (SBY : strip_bom data = r) by (rewrite EDATA; reflexivity).
          do 3 astep.
          apply evtF_done. rewrite SBY. replace (ACP + (len - zlength r)) with (ACP + 3) by (clear - RL; lia).
          replace (zlength r) with (len + -3) by (clear - RL; lia).
          Time (do 17 eexists; split; [reflexivity|]). split; [exact MU13'|]. split; [exact WM13|]. split; eassumption.
        + (* [comment removed for export] *)
          assert (SBN : strip_bom data = data).
          { rewrite EDATA, strip_bom_3. destruct (Z.eqb_spec q0 239), (Z.eqb_spec q1 187), (Z.eqb_spec q2 191); cbn [andb]; try reflexivity.
            exfalso. apply NZ. apply BR. auto. }
          pose proof (res_nonzero_reg _ MRB NZ) as NZR.
          remember (memcmp_res [Z_to_bv 8 q0; Z_to_bv 8 q1; Z_to_bv 8 q2] [Z_to_bv 8 239; Z_to_bv 8 187; Z_to_bv 8 191]) as res eqn:ERES.
          ltac2:(only_rng []). zstep. unhide_rng.
          if_cases KB; [| exfalso; unfold bv_eqb in KB; change (bv_unsigned (Z_to_bv 64 0)) with 0 in KB;
                          apply negb_false_iff, Z.eqb_eq in KB; exact (NZR KB)].
          apply evtF_done. rewrite SBN. replace (ACP + (len - zlength data)) with ACP by (unfold len; clear; lia).
          Time (do 17 eexists; split; [reflexivity|]). split; [exact MU13'|]. split; [exact WM13|]. split; eassumption. }
    cbv beta. intros ms14 (ra' & x0' & x1' & x2' & y0' & y1' & y2' & y3' & y4' & y5' & y6' & y7' & x3' & x4' & x5' & x6' & m14 & -> & MU14 & WM14 & MI14 & ST14).
    clear GOT RIC REAL SHB INI LAY FLG RMC BOMS CI12.
    Time trmC MU14 WM14 ltac:(fun _ => prnB).
    assert (AH14 : AHEAP AI L RNG3 (aps_m s3') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                                                :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m14)
      by (eapply (AI_frame AI); [exact AH12| exact MU14| exact WM14| apply Forall_cons; [left; left; cbn; prnB; lia| apply Forall_nil]]).
    assert (PW14 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m14).
    { eapply aheap_pres_W_trans; [exact PW12|]. eapply aheap_pres_W_of_munch; [exact MU14| exact WM14|].
      intros a Ha Hc Hx. cbn [outside] in Hx |- *.
      pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH14 (fun b Hb => or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror Hb))))))) Hc) as Ha'.
      clear - Ha' LOA LOS. lia. }
    pose proof (client_static1_munch32 _ _ _ CS112 MU14 WM14 ltac:(apply Forall_cons; [apply wfar_high; prnB; lia| apply Forall_nil])) as CS114.
    clear AH12 PW12 CS112 MU14 WM14. try drop_mem m12.
    exact (apid_t4 AI rng_fs ONTA ODA IMG_CI PARSE RFSM L RNG ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo rstk data D P R jr trR LBK PAY DAT DB D16
       DL CI0 CSH fcls FA FN INF FKH FK2 FKB RP R8 P8 RSHR RSHP RSPR RHI R47 LOA LOS RCL RCL1 RCL2 RCL3 RRNG STOP SP16 FZ TP HUL UCR TRR PRO RFS AOK RSP H FK1 FKB1
       FKB2 FKB3 FKB4 bF bFr bFhi bFlo LY1 LY2 LY3 LEN0 CAPR PR0 SB SB0 SB1 SB2 SB3 SB4 SB5 SB6 SB7 SB8 SB9 RS0 RS1 RS2 RS3 RS4 RS7 RS8 RS9 junk K1 K2 psb
       ptp SBA TPA BRS BRT FWF HUM pim psi poc pia s2' RNG2 w0' w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 AIM ASI AOC AIA p1 p2 pad BRM BRI BRO BRA BRM1 BRM2
       BRM3 BRM4 BRI1 BRI2 BRI3 BRI4 BRO1 BRO2 BRO3 BRO4 BRA1 BRA2 BRA3 BRA4 BRS1 BRS2 BRS3 BRS4 BRT1 BRT2 BRT3 BRT4 DJMF KC SZC pcp s3' RNG3 x0 x1 x2 e1
       e2 e3 e4 e5 e6 e7 x3 x4 x5 x6 ACP jcp BRC RC1 RC2 BRC1 BRC2 BRC3 BRC4 bC bCr bChi bClo DJM DJF INM RSTK3 RI3 RISH3 RPR3 RPP3 RS_8 RS_64 FPL13 ARS13 INC
       z0 z1 z2 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 m1 RS_72 h0 h1 h2 i1 i2 i3 i4 i5 i6 i7 h3 h4 h5 h6 ra' x0' x1' x2' y0' y1' y2' y3' y4' y5' y6' y7' x3'
       x4' x5' x6' m14 MI14 ST14 SC5 FR SC6 PCP DST4 OBJ4 DOC2 PMAX PR SC SC0 SC1 SC2 SC3 SC4 SC7 SC8 SC9 SET10 CPY12 AH14 PW14 CS114 AFR3 DK3).
  Qed.
End T.
End S.
End CANSEC1.
