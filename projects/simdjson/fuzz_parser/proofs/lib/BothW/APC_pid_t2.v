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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_pid0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_pid_t3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_mpres.
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
  Variable (RS6 : boxed (rng RNG ((P + 72) ≫ 3 + 2147450880) 1)).
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
  Variable (m5 : amem).
  Variable (MI4 : mem_inv bsegs m5).
  Variable (ST4 : stk bsegs m5 lo (bv_unsigned sp + -112)).
  Variable (AIM ASI AOC AIA : Z).
  Variable (p1 p2 pad : list byte).
  Variable (BRM : ablock_range AIM 96).
  Variable (BRI : ablock_range ASI (SIDX_BYTES len)).
  Variable (BRO : ablock_range AOC (8 * 1024)).
  Variable (BRA : ablock_range AIA 1024).
  Variable (AFR2 : AFRESH (aps_m s2')).
  Variable (DK2 : dk (aps_m s2') < DWMAX).
  Variable (PCP : rw_cells bsegs m5 (P + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  Variable (SC5 : rw_cells bsegs m5 ((P + 64) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (RSTK2 : rng RNG2 lo (al_top L - lo)).
  Variable (RI2 : rng_aimg RNG2).
  Variable (RISH2 : rng_aimg_sh RNG2).
  Variable (RPR2 : rng RNG2 R 24).
  Variable (RPP2 : rng RNG2 P 80).
  Variable (RS_8 : rng RNG2 ((P + 8) ≫ 3 + 2147450880) 1).
  Variable (RS_64 : rng RNG2 ((P + 64) ≫ 3 + 2147450880) 1).
  Variable (FR : rw_cells bsegs m5 (bv_unsigned sp + -112) [C8 (Z_to_bv 64 (P + 24)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
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
  Variable (SC9 : rw_cells bsegs m5 ((R + 16) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC8 : rw_cells bsegs m5 ((R + 8) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC7 : rw_cells bsegs m5 (R ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC6 : rw_cells bsegs m5 ((P + 72) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC4 : rw_cells bsegs m5 ((P + 56) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC3 : rw_cells bsegs m5 ((P + 48) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC2 : rw_cells bsegs m5 ((P + 40) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC1 : rw_cells bsegs m5 ((P + 32) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC0 : rw_cells bsegs m5 ((P + 24) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC : rw_cells bsegs m5 ((P + 8) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (PR : rw_cells bsegs m5 R [CB 24 jr]).
  Variable (PMAX : rw_cells bsegs m5 (P + 48) [C8 (Z_to_bv 64 4294967295); C1 (Z_to_bv 8 0)]).
  Variable (DOC2 : rw_cells bsegs m5 (P + 24) [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA); C8 (Z_to_bv 64 (CAP len))]).
  Variable (OBJ4 : rw_cells bsegs m5 AIM [C8 (Z_to_bv 64 AVTAB_DOM); C4 (Z_to_bv 64 0); CB 4 p1; C8 (Z_to_bv 64 ASI); C4 (Z_to_bv 64 0); CB 4 p2; C8 (Z_to_bv 64 (CAP len)); C8 (Z_to_bv 64 1024); C2 (Z_to_bv 64 0); CB 6 pad; C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  Variable (DST4 : rw_cells bsegs m5 (P + 8) [C8 (Z_to_bv 64 AIM)]).
  Variable (AH5 : AHEAP AI L RNG2 (aps_m s2') (HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m5).
  Variable (PW5 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m5).
  Variable (CS15 : client_static1 m5).
  Variable (FPL12 : fp_le RNG RNG2).
  Variable (ARS12 : aps_rest s2' = aps_rest s).
  Lemma apid_t2 :
    evtF bsegs RNG2 (λ ms' : machine_state, implMA RNG2 (lb <- padded_alloc amalloc_M (new_handlerA AAllocAsan) len;; match lb with | Some _ => parse_impl amalloc_M afree_M (new_handlerA AAllocAsan) data | None => mret () end;;; mret ((psb, ptp).1, (psb, ptp).2, (pim, psi, poc, pia), lb)) s2' (apid_post AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB len lo P R m) ms') (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some w6) TEmpty) (Some d5) TEmpty) (Some w2) (TNode TEmpty (Some (Z_to_bv 64 (P + 72))) TEmpty)) (Some gp) (TNode (TNode TEmpty (Some (Z_to_bv 64 D)) TEmpty) (Some (Z_to_bv 64 64)) (TNode TEmpty (Some (Z_to_bv 64 ((P + 8) ≫ 3 + 2147450880))) TEmpty))) (Some (Z_to_bv 64 614288)) (TNode (TNode (TNode TEmpty (Some d7) TEmpty) (Some (Z_to_bv 64 ((P + 64) ≫ 3 + 2147450880))) (TNode TEmpty (Some (Z_to_bv 64 (P + 24))) TEmpty)) (Some w0') (TNode (TNode TEmpty (Some (Z_to_bv 64 P)) TEmpty) (Some d3) (TNode TEmpty (Some w4) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some d6) TEmpty) (Some (Z_to_bv 64 R)) (TNode TEmpty (Some (Z_to_bv 64 0)) TEmpty)) (Some tp) (TNode (TNode TEmpty (Some (Z_to_bv 64 (P + 8))) TEmpty) (Some d2) (TNode TEmpty (Some w3) TEmpty))) (Some (Z_to_bv 64 (bv_unsigned sp + -112))) (TNode (TNode (TNode TEmpty (Some (Z_to_bv 64 len)) TEmpty) (Some (Z_to_bv 64 1048512)) (TNode TEmpty (Some (Z_to_bv 64 2147450880)) TEmpty)) (Some w1) (TNode (TNode TEmpty (Some (Z_to_bv 64 (P + 64))) TEmpty) (Some d4) (TNode TEmpty (Some w5) TEmpty))))) F (Z_to_bv 64 613424) fc None m5 (seg_rom bsegs)).
  Proof using All.
    assert (DJMF : AIM + 96 <= FA \/ FA + FN <= AIM)
      by (pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH5 (ltac:(do 3 right; left; reflexivity)) (ltac:(do 6 right; exact INF)) ltac:(discriminate)) as X;
          cbn in X; exact X).
    zstep. if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      pose proof (munch_refl [(P + 64, P + 72)] m5) as MU6. pose proof (wmono_refl bsegs m5) as WM6.
      park_memA m5. unfold parkedA in SC5, PCP.
      boxm RI2. boxm RISH2.
      ltac2:(hide_arith [@LOS; @LOA; @RSP; @STOP; @LY3; @SP16; @RP; @RSPR; @R47; @PR0; @P8; @FK1; @FKH; @FK2; @FKB3; @SB5; @KC; @bFr; @bFhi; @bFlo]).
      (* [comment removed for export] *)
      Time steps_to 0x95ef4. zstep. if_cases KR0; zify_cond KR0; [exfalso; rewrite ?unsigned_lit in KR0 by lia; lia|].
      Time steps_to 0x65ce8.
      unhide_arith. unbox RI2. unbox RISH2. unparkA.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m6 eqn:EM6 end. clear EM6.
      Time trmC MU6 WM6 ltac:(fun _ => prnA).
      assert (AH6 : AHEAP AI L RNG2 (aps_m s2') (HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96
                                                :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m6)
        by (eapply (AI_frame AI); [exact AH5| exact MU6| exact WM6|];
            apply Forall_cons; [first [ (left; left; cbn; prnA; lia) | (right; left; exists (mkABlock (ABFake fcls) FA FN); split; [do 6 right; exact INF| cbn; prnA; lia]) ]| apply Forall_nil]).
      assert (PW6 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m6).
      { eapply aheap_pres_W_trans; [exact PW5|]. eapply aheap_pres_W_of_munch; [exact MU6| exact WM6|].
        intros a Ha Hc Hx. unfold apid_W in Hx. cbn [app outside] in Hx |- *. clear - Hx. lia. }
      pose proof (client_static1_munch32 _ _ _ CS15 MU6 WM6 ltac:(apply Forall_cons; [first [ (eapply wfar_ablk; [exact FKB| prnA; lia| prnA; lia]) | (apply wfar_high; prnA; lia) ]| apply Forall_nil])) as CS16.
      clear AH5 PW5 CS15.
      (* [comment removed for export] *)
      assert (RC6 : rclean m6 rstk).
      { eapply (rclean_W AI _ _ _ _ _ _ RCL PW6 RCL3). intros a Ha. unfold apid_W, client_wr. cbn [app outside].
        pose proof RCL as ((_ & (H1 & H2 & H3 & H4 & H5 & H6) & _ & _) & _). unfold KEND in H6. pose proof atop_range as AR.
        rewrite !shad_div in Ha. unfold ASHOFF in Ha.
        clear - Ha H1 H2 H3 H4 H5 H6 AR RCL3 FK1 FKH FK2 FKB3 FKB2 RP RSPR LOA LOS PR0 bFr bFhi bFlo. Z.div_mod_to_equations. lia. }
      destruct RC6 as [(UNP6 & HL6 & WRH6 & APP6) _].
      pose proof (client_rt_of_aheap AI _ _ _ _ _ AH6) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
      pose proof (rw_cells_split_CB bsegs _ R [] 24 jr [] [16%nat; 8%nat] PR ltac:(reflexivity)) as SPL. cbn [app mk_CB_cells] in SPL.
      destruct (rw_cells_cut bsegs _ R _ 1 SPL) as [PR16 PR8]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PR16, PR8.
      clear SPL PR.
      pose proof (unpoisoned_two _ R R8 PR0 ltac:(prnA; lia) SC7 SC8) as UPR.
      unbox RRNG. unfold rrng in RRNG. pose proof (rng_fp_le _ _ _ _ FPL12 RRNG) as RGH2.
      assert (APR : app_blk R (R + 16)) by (eapply app_blk_sub; [exact APP6| clear - RCL1 LOS LOA RSPR; lia| lia| clear - RHI; lia]).
      assert (HL64 : r_rlo rstk <= R /\ R + 16 <= r_rhi rstk /\ r_rlo rstk mod 64 = 0 /\ r_rhi rstk mod 64 = 0 /\ 0 <= r_rlo rstk /\ r_rhi rstk <= KEND)
        by (destruct HL6 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6); clear - Q1 Q2 Q3 Q4 Q5 Q6 RCL1 LOS LOA RSPR RHI; repeat split; lia).
      assert (UR : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; clear - PR0 R47; lia).
      assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; clear - LOS LOA RSP; lia).
      assert (U16 : bv_unsigned (Z_to_bv 64 16) = 16) by reflexivity. assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
      assert (RSM : rng RNG2 lo (bv_unsigned sp + -112 - lo)) by (eapply rng_sub'; [exact RSTK2| clear - LOS LOA RSP STOP LY3; lia]).
      assert (RRM : rng RNG2 R 16) by (eapply rng_sub'; [exact RPR2| clear - PR0; lia]).
      eapply evtF_cut.
      { eapply (asan_memset_spec RNG2) with (lo := lo) (RLO2 := r_rlo rstk) (RHI2 := r_rhi rstk) (junk := firstn 16 jr);
          rewrite ?UR, ?USP, ?U16, ?U0;
          first [ eassumption | exact PR16 | (unfold KHIGH; clear - LOA; lia) | (right; clear - RSPR; lia) | (clear - LOS; lia) ]. }
      cbv beta. intros ms7 (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m7 & -> & MU7 & WM7 & MI7 & ST7 & SET7).
      rewrite ?UR, ?USP, ?U16 in MU7. rewrite ?UR, ?USP, ?U16 in ST7. rewrite ?UR, ?USP, ?U16 in SET7. retlit.
      Time trmC MU7 WM7 ltac:(fun _ => prnA).
      assert (AH7 : AHEAP AI L RNG2 (aps_m s2') (HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96
                                                :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m7)
        by (eapply (AI_frame AI); [exact AH6| exact MU7| exact WM7|];
            apply Forall_cons; [left; left; cbn; prnA; lia|];
            apply Forall_cons; [first [ (left; left; cbn; prnA; lia) | (right; left; exists (mkABlock (ABFake fcls) FA FN); split; [do 6 right; exact INF| cbn; prnA; lia]) ]| apply Forall_nil]).
      assert (PW7 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m7).
      { eapply aheap_pres_W_trans; [exact PW6|]. eapply aheap_pres_W_of_munch; [exact MU7| exact WM7|].
        intros a Ha Hc Hx. unfold apid_W in Hx. cbn [app outside] in Hx |- *.
        pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH7 (fun b Hb => or_intror (or_intror (or_intror (or_intror (or_intror (or_intror Hb)))))) Hc) as Ha'.
        clear - Hx Ha' LOA LOS. lia. }
      pose proof (client_static1_munch32 _ _ _ CS16 MU7 WM7
                    ltac:(apply Forall_cons; [apply wfar_high; prnA; lia| apply Forall_cons; [first [ (eapply wfar_ablk; [exact FKB| prnA; lia| prnA; lia]) | (apply wfar_high; prnA; lia) ]| apply Forall_nil]])) as CS17.
      clear AH6 PW6 CS16 MU7 WM7 GOT RIC REAL SHB SUA INI LAY UPR RGH2 WRH6 APR HL64 RSM RRM PR16 UNP6 HL6 APP6.
      (* [comment removed for export] *)
      unbox RS9. pose proof (rng_fp_le _ _ _ _ FPL12 RS9) as RS_R16. clear RS9.
      pose proof (munch_refl [(R + 16, R + 20)] m7) as MU8. pose proof (wmono_refl bsegs m7) as WM8.
      pose proof (rw_cells_split_CB bsegs _ (R + 16) [] 8 _ [] [4%nat; 4%nat] PR8 ltac:(reflexivity)) as SPL. cbn [app mk_CB_cells] in SPL.
      destruct (rw_cells_cut bsegs _ (R + 16) _ 1 SPL) as [PR16a PR20]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PR16a, PR20.
      try replace (R + 16 + Z.of_nat 4) with (R + 20) in PR20 by lia. try replace (R + 16 + 4) with (R + 20) in PR20 by lia.
      clear SPL PR8.
      park_memA m7. unfold parkedA in SC9, PR16a, FR.
      boxm RI2. boxm RISH2. boxm RS_8. boxm RS_64.
      ltac2:(hide_arith [@LOS; @LOA; @RSP; @STOP; @LY3; @SP16; @RP; @RSPR; @R47; @PR0; @R8; @FK1; @FKH; @FK2; @FKB3; @SB9; @bFr; @bFhi; @bFlo]).
      boxm RSTK2.
      Time do 7 astep.
      unbox RSTK2. boxm RPR2. boxm RPP2. boxm RS_R16.
      Time do 15 astep.
      unbox RPR2. unbox RPP2. unbox RS_R16.
      unhide_arith. unbox RI2. unbox RISH2. unbox RS_8. unbox RS_64. unparkA.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m8 eqn:EM8 end. clear EM8.
      Time trmC MU8 WM8 ltac:(fun _ => prnA).
      assert (AH8 : AHEAP AI L RNG2 (aps_m s2') (HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96
                                                :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m8)
        by (eapply (AI_frame AI); [exact AH7| exact MU8| exact WM8|];
            apply Forall_cons; [first [ (left; left; cbn; prnA; lia) | (right; left; exists (mkABlock (ABFake fcls) FA FN); split; [do 6 right; exact INF| cbn; prnA; lia]) ]| apply Forall_nil]).
      assert (PW8 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m8).
      { eapply aheap_pres_W_trans; [exact PW7|]. eapply aheap_pres_W_of_munch; [exact MU8| exact WM8|].
        intros a Ha Hc Hx. unfold apid_W in Hx. cbn [app outside] in Hx |- *. clear - Hx. lia. }
      pose proof (client_static1_munch32 _ _ _ CS17 MU8 WM8 ltac:(apply Forall_cons; [first [ (eapply wfar_ablk; [exact FKB| prnA; lia| prnA; lia]) | (apply wfar_high; prnA; lia) ]| apply Forall_nil])) as CS18.
      clear AH7 PW7 CS17 MU8 WM8.
      release_frame FR ST7 (bv_unsigned sp).
      apply evtF_done.
      unfold HarnessP.padded_alloc. replace (copy_made len) with false
        by (unfold copy_made, COPY_BYTES, PADDING, COPY_LIMIT; symmetry; apply Z.leb_gt; clear - KC; lia).
      apply implMA_retb. cbv beta iota. apply implMA_retb. apply implMA_ret. apply evtF_done.
      destruct (aimpl_post_cells _ _ _ _ _ _ _ _ _ OBJ4) as (OB0 & OB16 & OB56).
      destruct (rw_cells_cut bsegs _ _ _ 2 DOC2) as [DOCa _]. cbn [firstn] in DOCa.
      destruct (rw_cells_cut bsegs _ _ _ 1 PCP) as [PCPa _]. cbn [firstn] in PCPa.
      unfold apid_post. split; [exact FPL12|].
      do 15 eexists. exists F, fc. eexists. split; [reflexivity|].
      split; [exact FZ|]. split; [eassumption|]. split; [exact ST7|]. split; [exact (stk_slot3 _ _ _ _ _ SET7 PR16a PR20 eq_refl eq_refl eq_refl)|].
      split; [exists 2; split; [lia| exact PR16a]|].   (* [comment removed for export] *)
      split; [exact PW8|]. split; [exact ARS12|]. split; [exact CS18|].
      exists SBA, TPA, AIM, ASI, AOC, AIA, 0.
      split; [unfold apid_blocks, acopy_blk, asix_blks, ISARR_BYTES, OC_BYTES, MAX_DEPTH, IMPL_BYTES; cbn [app]; exact AH8|].
      split; [exact DST4|]. split; [exact DOCa|]. split; [exact PCPa|]. split; [exact OB0|]. split; [exact OB16| exact OB56].
    - (* [comment removed for export] *)
      assert (SZC : 0 < COPY_BYTES len <= AREQMAX) by (unfold COPY_BYTES, PADDING, AREQMAX in *; clear - KC LEN0; lia).
      pose proof (got_nothrow_of_aheap AI _ _ _ _ _ AH5 ltac:(eassumption)) as GNT. unfold AGOT_NOTHROW, ANOTHROW in GNT.
      park_memA m5. unfold parkedA in GNT.
      boxm RISH2. boxm RPR2. boxm RPP2. boxm RS_64. boxm RS_8.
      Time steps_to 0xee5e0.
      unbox RISH2. unbox RPR2. unbox RPP2. unbox RS_64. unbox RS_8. unparkA. clear GNT.
      apply evtF_done.
      unfold HarnessP.padded_alloc. replace (copy_made len) with true
        by (unfold copy_made, COPY_BYTES, PADDING, COPY_LIMIT; symmetry; apply Z.leb_le; clear - KC; lia).
      eapply implMA_map_some.
      { eapply implMA_leaves; [| exact (opnew_dk (COPY_BYTES len) s2')].
        pose proof (proj2 ONTA) as ONT2. unfold opnew_nt_stmtA_at in ONT2.
        assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; clear - LOS LOA RSP; lia).
        eapply ONT2 with (lo := lo) (n := COPY_BYTES len); try reflexivity; rewrite ?USP;
          first [ exact AH5 | exact TP | exact HUM | eassumption | (unfold COPY_BYTES, PADDING; reflexivity)
                | (unfold OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; clear - LOS; lia) | (clear - STOP; lia)
                | (clear - SP16; lia) | (eapply aps_ok_rest; [exact ARS12| exact AOK]) | (eapply rng_sub'; [exact RSTK2| clear - RSP LOS LOA STOP LY3; lia]) ]. }
      cbv beta. intros pcp s3' RNG3 ms4
        [(FPL3 & x0 & x1 & x2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m9 & ACP & jcp & -> & MI9 & ST9 & HPR9 & ARS3 & BRC & AH9 & BLKC & RC1 & RC2) DKS3].
      destruct DKS3 as (DF3 & _ & _). destruct (DF3 AFR2) as [AFR3 DKB3]. assert (DK3 : dk (aps_m s3') < DWMAX) by (clear - DK2 DKB3; lia). clear DF3 DKB3.
      rewrite ?unsigned_lit in ST9 by (clear - LOS LOA RSP; lia). rewrite ?unsigned_lit in HPR9 by (clear - LOS LOA RSP; lia). retlit.
      pose proof (ablock_range_lin _ _ BRC) as (BRC1 & BRC2 & BRC3 & BRC4).
      unfold COPY_BYTES, PADDING in BRC, BRC2, BRC3, BLKC, AH9, RC1, RC2.
      band_ind (proj1 BRC) bC.
      assert (DJM : ACP + (len + 64) <= AIM \/ AIM + 96 <= ACP)
        by (pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ (HB pim AIM 96) AH9 ltac:(do 3 right; left; reflexivity)) as X; cbn in X; exact X).
      assert (DJF : ACP + (len + 64) <= FA \/ FA + FN <= ACP)
        by (pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ (mkABlock (ABFake fcls) FA FN) AH9 ltac:(do 6 right; exact INF)) as X; cbn in X; exact X).
      (* [comment removed for export] *)
      assert (INM : In (HB pim AIM 96) (HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96
                                         :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (do 3 right; left; reflexivity).
      assert (INF6 : In (mkABlock (ABFake fcls) FA FN) (HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96
                                         :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (do 6 right; exact INF).
      Time trpC HPR9 INF6 IMG_CI ltac:(fun _ => prnA).
      assert (PW9 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m9).
      { eapply aheap_pres_W_trans; [exact PW5|]. eapply aheap_pres_W_of_pres.
        eapply aheap_pres_weaken; [exact HPR9| prnA; lia| intros b Hb; do 6 right; exact Hb]. }
      pose proof (client_static1_pres AI IMG_CI _ _ _ _ HPR9 CS15) as CS19.
      clear HPR9 PW5 CS15 AH5.
      cbv beta iota. apply implMA_from_evtF.
      pose proof (rng_fp_le _ _ _ _ FPL3 RSTK2) as RSTK3. pose proof (rng_fp_le _ _ _ _ FPL3 RI2) as RI3. pose proof (rng_fp_le _ _ _ _ FPL3 RISH2) as RISH3.
      pose proof (rng_fp_le _ _ _ _ FPL3 RPR2) as RPR3. pose proof (rng_fp_le _ _ _ _ FPL3 RPP2) as RPP3. pose proof (rng_fp_le _ _ _ _ FPL3 RS_8) as RS_8'. pose proof (rng_fp_le _ _ _ _ FPL3 RS_64) as RS_64'.
      pose proof (fp_le_trans _ _ _ FPL12 FPL3) as FPL13. assert (ARS13 : aps_rest s3' = aps_rest s) by (rewrite ARS3; exact ARS12).
      clear RSTK2 RI2 RISH2 RPR2 RPP2 RS_8 RS_64 FPL12 FPL3 ARS12 ARS3. rename RS_8' into RS_8. rename RS_64' into RS_64.
      (* [comment removed for export] *)
      assert (INC : In (HB pcp ACP (len + 64)) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                                                :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (left; reflexivity).
      destruct (blk_window_facts AI _ _ _ _ _ _ _ _ (ACP + len) 64 AH9 INC ltac:(prnA; lia) ltac:(prnA; lia) ltac:(lia))
        as (APC & UNPC & RWC & (RLOC & RHIC & HUC & WHC & RHC)).
      pose proof (rw_cells_split_CB bsegs _ ACP [] (Z.to_nat (len + 64)) jcp [] [Z.to_nat len; 64%nat] BLKC ltac:(cbn; clear - LEN0; lia)) as SPL.
      cbn [app mk_CB_cells] in SPL. destruct (rw_cells_cut bsegs _ ACP _ 1 SPL) as [CPA CPB].
      cbn [firstn skipn cells_size csize] in CPA, CPB. rewrite ?Nat.add_0_r in CPB. rewrite Z2Nat.id in CPB by lia. clear SPL BLKC.
      park_memA m9. unfold parkedA in CPB.
      boxm RPR3. boxm RPP3. boxm RS_8. boxm RS_64.
      zstep. if_cases KN; zify_cond KN; [exfalso; clear - KN BRC1; lia| clear KN].
      (* [comment removed for export] *)
      Time steps_to 0x95c50. zstep. if_cases KO; zify_cond KO; [exfalso; rewrite lxor_ones64 in KO by lia; lia| clear KO].
      Time steps_to 0x65ce8.
      unbox RPR3. unbox RPP3. unbox RS_8. unbox RS_64.
      pose proof (client_rt_of_aheap AI _ _ _ _ _ AH9) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
      assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; clear - LOS LOA RSP; lia).
      assert (UCL : bv_unsigned (Z_to_bv 64 (ACP + len)) = ACP + len) by (apply unsigned_lit; prnA; lia).
      assert (U64 : bv_unsigned (Z_to_bv 64 64) = 64) by reflexivity. assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
      assert (RSM : rng RNG3 lo (bv_unsigned sp + -112 - lo)) by (eapply rng_sub'; [exact RSTK3| clear - LOS LOA RSP STOP LY3; lia]).
      eapply evtF_cut.
      { eapply (asan_memset_spec RNG3) with (lo := lo) (RLO2 := RLOC) (RHI2 := RHIC);
          rewrite ?USP, ?UCL, ?U64, ?U0;
          first [ eassumption | (unfold KHIGH; clear - LOA; lia) | (left; prnA; lia) | (clear - LOS; lia) ]. }
      cbv beta. intros ms10 (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m10 & -> & MU10 & WM10 & MI10 & ST10 & SET10).
      rewrite ?USP, ?UCL, ?U64, ?U0 in MU10. rewrite ?USP, ?UCL, ?U64, ?U0 in ST10. rewrite ?USP, ?UCL, ?U64, ?U0 in SET10. retlit.
      unparkA. clear CPB APC UNPC RWC RLOC RHIC HUC WHC RHC GOT RIC REAL SHB SUA INI LAY RSM.
      Time trmC MU10 WM10 ltac:(fun _ => prnA).
      assert (AH10 : AHEAP AI L RNG3 (aps_m s3') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                                                  :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m10)
        by (eapply (AI_frame AI); [exact AH9| exact MU10| exact WM10|];
            apply Forall_cons; [left; left; cbn; prnA; lia|];
            apply Forall_cons; [right; left; exists (HB pcp ACP (len + 64)); split; [left; reflexivity| cbn; prnA; lia]| apply Forall_nil]).
      assert (PW10 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m10).
      { eapply aheap_pres_W_trans; [exact PW9|]. eapply aheap_pres_W_of_munch; [exact MU10| exact WM10|].
        intros a Ha Hc Hx. unfold apid_W in Hx. cbn [app outside] in Hx |- *.
        assert (HcL : aclient_addr CI (HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96
                                        :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) (bv_unsigned sp) a)
          by (eapply aclient_addr_mono_lb; [exact Hc| intros b Hb; do 6 right; exact Hb]).
        pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH9 ltac:(prnA; lia) HcL) as NF.
        pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH9 (fun b Hb => or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror Hb))))))) Hc) as Ha'.
        clear - Hx Ha' NF LOA LOS LEN0. lia. }
      pose proof (client_static1_munch32 _ _ _ CS19 MU10 WM10
                    ltac:(apply Forall_cons; [apply wfar_high; prnA; lia| apply Forall_cons; [eapply wfar_ablk; [exact (proj1 BRC)| prnA; lia| prnA; lia]| apply Forall_nil]])) as CS110.
      clear AH9 PW9 CS19 MU10 WM10.
      (* [comment removed for export] *)
      unbox RS6. pose proof (rng_fp_le _ _ _ _ FPL13 RS6) as RS_72. clear RS6.
      pose proof (munch_refl [(P + 64, P + 80)] m10) as MU11. pose proof (wmono_refl bsegs m10) as WM11.
      park_memA m10. unfold parkedA in SC5, SC6, PCP, FR.
      boxm RI3. boxm RISH3. boxm RS_8.
      Time steps_to 0x95ce4.
      zstep. if_cases KN2; zify_cond KN2; [exfalso; clear - KN2 BRC1; lia| clear KN2].
      Time steps_to 0x6584c.
      unbox RI3. unbox RISH3. unbox RS_8. unparkA.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m11 eqn:EM11 end. clear EM11.
      Time trmC MU11 WM11 ltac:(fun _ => prnA).
      assert (AH11 : AHEAP AI L RNG3 (aps_m s3') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                                                  :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m11)
        by (eapply (AI_frame AI); [exact AH10| exact MU11| exact WM11|];
            apply Forall_cons; [first [ (left; left; cbn; prnA; lia) | (right; left; exists (mkABlock (ABFake fcls) FA FN); split; [do 7 right; exact INF| cbn; prnA; lia]) ]| apply Forall_nil]).
      assert (PW11 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m11).
      { eapply aheap_pres_W_trans; [exact PW10|]. eapply aheap_pres_W_of_munch; [exact MU11| exact WM11|].
        intros a Ha Hc Hx. unfold apid_W in Hx. cbn [app outside] in Hx |- *. clear - Hx. lia. }
      pose proof (client_static1_munch32 _ _ _ CS110 MU11 WM11 ltac:(apply Forall_cons; [first [ (eapply wfar_ablk; [exact FKB| prnA; lia| prnA; lia]) | (apply wfar_high; prnA; lia) ]| apply Forall_nil])) as CS111.
      clear AH10 PW10 CS110 MU11 WM11.
      pose proof (client_rt_of_aheap AI _ _ _ _ _ AH11) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
      assert (UCP : bv_unsigned (Z_to_bv 64 ACP) = ACP) by (apply unsigned_lit; prnA; lia).
      assert (UD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; unbox PAY; destruct PAY as [(pp & Hpp & _)|(_ & ->)];
                                                      [pose proof (AI_block_bounds AI _ _ _ _ _ _ AH11 (ltac:(do 7 right; exact Hpp))) as BB; cbn in BB; clear - BB; unfold AIMG_HI in BB; lia
                                                      | unfold AEMPTY; lia]).
      assert (UL : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; clear - DL LEN0; lia).
      assert (RSM : rng RNG3 lo (bv_unsigned sp + -112 - lo)) by (eapply rng_sub'; [exact RSTK3| clear - LOS LOA RSP STOP LY3; lia]).
      eapply evtF_cut.
      { destruct (Z_gt_le_dec len 0) as [LP|LZ].
        - (* [comment removed for export] *)
          unbox PAY. destruct PAY as [(pp & INP & _)|(E0 & _)]; [| exfalso; assert (ZL0 : zlength data = 0) by (rewrite E0; reflexivity); unfold len in LP; clear - ZL0 LP; lia].
          assert (INP' : In (HB pp D len) (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                                           :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (do 7 right; exact INP).
          destruct (blk_window_facts AI _ _ _ _ _ _ _ _ D len AH11 INP' ltac:(lia) ltac:(lia) ltac:(lia)) as (APS & UNS & RDS & (RLOS & RHIS & HUS & WHS & RHS)).
          destruct (blk_window_facts AI _ _ _ _ _ _ _ _ ACP len AH11 INC ltac:(lia) ltac:(prnA; lia) ltac:(lia)) as (APD & UND & RDD & (RLOD & RHID & HUD & WHD & RHD)).
          pose proof (AI_block_bounds AI _ _ _ _ _ _ AH11 INP') as BBP. cbn [ab_addr ab_size] in BBP.
          assert (DJP : D + len <= ACP \/ ACP + (len + 64) <= D).
          { pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ (HB pp D len) AH11 ltac:(do 6 right; exact INP)) as X. cbn in X. clear - X. lia. }
          assert (DJQ : D + len <= FA \/ FA + FN <= D).
          { pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH11 INP' (ltac:(do 7 right; exact INF)) ltac:(discriminate)) as X. cbn in X. clear - X. lia. }
          assert (DAT11 : bytes_at bsegs m11 D (map (Z_to_bv 8) data)).
          { eapply (aheap_pres_W_bytes_at CI _ _ _ _ _ _ _ PW11 DAT).
            - right; left. exists (HB pp D len). split; [exact INP|]. cbn. rewrite length_map. unfold len, zlength. lia.
            - intros a Ha. rewrite length_map in Ha. unfold apid_W, client_wr. cbn [app outside].
              assert (Ha' : D <= a < D + len) by (unfold len, zlength; lia). clear - Ha' DJQ FK1 FKH FK2 RP RSPR LOA LOS BBP. unfold AIMG_HI in BBP. lia. }
          pose proof (asan_memcpy_proof RNG3) as MC. unfold asan_memcpy_stmt in MC. cbv zeta in MC.
          eapply MC with (lo := lo) (RLO1 := RLOS) (RHI1 := RHIS) (RLO2 := RLOD) (RHI2 := RHID);
            rewrite ?USP, ?UCP, ?UD, ?UL;
            first [ eassumption | (rewrite length_map; unfold len, zlength; rewrite Nat2Z.id; reflexivity) | (unfold AMEMCPY_STACK; clear - LOS; lia) | (unfold KHIGH; clear - LOA; lia)
                      | (clear - DJP; lia) | (left; clear - BBP LOS LOA; unfold AMEMCPY_STACK; lia) | (left; prnA; lia) | (clear - DL; lia) ].
        - (* [comment removed for export] *)
          assert (ED : data = []) by (destruct data as [|c0 dr]; [reflexivity| exfalso; unfold len, zlength in LZ; cbn [length] in LZ; clear - LZ; lia]).
          rewrite ED. cbn [map].
          unbox PAY. destruct PAY as [(pp & INP & LPP)|(_ & HD)]; [exfalso; unfold len, zlength in LPP, LZ; lia|].
          eapply asan_memcpy0_spec; rewrite ?USP, ?UCP, ?UD;
            first [ eassumption | (unfold AMEMCPY_STACK; clear - LOS; lia) | (unfold KHIGH; clear - LOA; lia)
                      | (f_equal; unfold len; rewrite ED; reflexivity) | (clear - D16; Z.div_mod_to_equations; lia)
                      | (clear - BRC4; Z.div_mod_to_equations; lia) | (clear - HD BRC1; unfold AEMPTY, AIMG_HI in *; lia) ]. }
      cbv beta. intros ms12 (h0 & h1 & h2 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & h3 & h4 & h5 & h6 & m12 & -> & MU12 & WM12 & MI12 & ST12 & CPY12 & DAT12).
      rewrite ?USP, ?UCP, ?UD, ?UL in MU12. rewrite ?USP, ?UCP, ?UD, ?UL in ST12. rewrite ?USP, ?UCP, ?UD, ?UL in CPY12. rewrite ?USP, ?UCP, ?UD, ?UL in DAT12. retlit.
      Time trmC MU12 WM12 ltac:(fun _ => prnA).
      assert (AH12 : AHEAP AI L RNG3 (aps_m s3') (HB pcp ACP (len + 64) :: HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len)
                                                  :: HB pim AIM 96 :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m12)
        by (eapply (AI_frame AI); [exact AH11| exact MU12| exact WM12|];
            apply Forall_cons; [left; left; cbn; prnA; lia|];
            apply Forall_cons; [right; left; exists (HB pcp ACP (len + 64)); split; [left; reflexivity| cbn; prnA; lia]| apply Forall_nil]).
      assert (PW12 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m12).
      { eapply aheap_pres_W_trans; [exact PW11|]. eapply aheap_pres_W_of_munch; [exact MU12| exact WM12|].
        intros a Ha Hc Hx. unfold apid_W in Hx. cbn [app outside] in Hx |- *.
        assert (HcL : aclient_addr CI (HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96
                                        :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) (bv_unsigned sp) a)
          by (eapply aclient_addr_mono_lb; [exact Hc| intros b Hb; do 6 right; exact Hb]).
        pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH11 ltac:(prnA; lia) HcL) as NF.
        pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH11 (fun b Hb => or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror Hb))))))) Hc) as Ha'.
        clear - Hx Ha' NF LOA LOS LEN0. lia. }
      pose proof (client_static1_munch32 _ _ _ CS111 MU12 WM12
                    ltac:(apply Forall_cons; [apply wfar_high; prnA; lia| apply Forall_cons; [eapply wfar_ablk; [exact (proj1 BRC)| prnA; lia| prnA; lia]| apply Forall_nil]])) as CS112.
      clear AH11 PW11 CS111 MU12 WM12 DAT12 GOT RIC REAL SHB SUA INI LAY RSM UD UCP UL USP UCL U64 U0 INF6.
      try drop_mem m9. try drop_mem m10. try drop_mem m11. try drop_mem m5.
      exact (apid_t3 AI rng_fs ONTA ODA IMG_CI PARSE RFSM L RNG ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo rstk data D P R jr trR LBK PAY DAT DB
       D16 DL CI0 CSH fcls FA FN INF FKH FK2 FKB RP R8 P8 RSHR RSHP RSPR RHI LOA LOS RCL RCL1 RCL2 RCL3 RRNG STOP SP16 FZ TP HUL UCR TRR RFS AOK AFR DKW
       PRO RSP H FK1 FKB1 FKB2 FKB3 FKB4 bF bFr bFhi bFlo LY1 LY2 LY3 LEN0 CAPR R47 PR0 SB SB0 SB1 SB2 SB3 SB4 SB5 SB6 SB7 SB8 SB9 RS0 RS1 RS2 RS3 RS4 RS7
       RS8 RS9 junk K1 K2 psb ptp s1' SBA TPA BRS BRT AFR1 DK1 FWF HUM pim psi poc pia s2' RNG2 w0' w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 AIM ASI AOC AIA
       p1 p2 pad BRM BRI BRO BRA AFR2 DK2 BRM1 BRM2 BRM3 BRM4 BRI1 BRI2 BRI3 BRI4 BRO1 BRO2 BRO3 BRO4 BRA1 BRA2 BRA3 BRA4 BRS1 BRS2 BRS3 BRS4 BRT1 BRT2
       BRT3 BRT4 DJMF KC SZC pcp s3' RNG3 x0 x1 x2 e1 e2 e3 e4 e5 e6 e7 x3 x4 x5 x6 ACP jcp BRC RC1 RC2 AFR3 DK3 BRC1 BRC2 BRC3 BRC4 bC bCr bChi bClo DJM
       DJF INM RSTK3 RI3 RISH3 RPR3 RPP3 RS_8 RS_64 FPL13 ARS13 INC z0 z1 z2 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 m1 RS_72 h0 h1 h2 i1 i2 i3 i4 i5 i6 i7 h3 h4
       h5 h6 m12 MI12 ST12 CPY12 SET10 SC9 SC8 SC7 SC4 SC3 SC2 SC1 SC0 SC PR PMAX DOC2 OBJ4 DST4 PCP SC6 FR SC5 AH12 PW12 CS112).
  Qed.
End T.
End S.
End CANSEC1.
