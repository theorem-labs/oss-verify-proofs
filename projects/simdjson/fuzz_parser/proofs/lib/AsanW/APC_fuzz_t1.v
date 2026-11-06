(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree StrFun.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface I_asan_memset AU_rt AH_memcpy0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import ShadowTac APC_kit APC_kit2 APC_kit3 APC_kit4 APC_dtor APC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2Lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import APC_pid0 APC_pid1 APC_pid APC_fuzz0 APC_mpres.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import LiaTier0U.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
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
Variable fflag : alayout -> Z -> Z -> Z.

Section T.
  Hypothesis ONTA : opnew_nt_stmtA AI.
  Hypothesis ODA : opdelete_arr_stmtA AI.
  Hypothesis OD : opdelete_stmtA AI.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis PARSE : parse_stmtA AI rng_fs.
  Hypothesis RFSM : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis SM2 : stack_malloc_2_stmt AI fflag rng_fs.
  Hypothesis FAKE_FLAG : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges CI (fflag L cls F).
  Hypothesis FAKE_RELEASE : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).

  Variable (L : alayout).
  Variable (RNG : footprint).
  Variable (sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Variable (F : bvmap 5 word).
  Variable (fc : bv 32).
  Variable (m : amem).
  Variable (s : APS).
  Variable (LB : list ablock).
  Variable (D : Z).
  Variable (payload : list Z).
  Variable (lo : Z).
  Variable (rstk : region).
  Variable (m0 : amem).
  Variable (AH : AHEAP AI L RNG (aps_m s) LB m).
  Variable (LBK : ∀ b : ablock, In b LB → ∃ (p : AsanCtrl.aptr) (A n : Z), b = HB p A n).
  Variable (PAY : payload_atA LB D payload).
  Variable (DAT : bytes_at asegs m D (map (Z_to_bv 8) payload)).
  Variable (DB : Forall (λ c : Z, 0 <= c < 256) payload).
  Variable (D16 : D mod 16 = 0).
  Variable (DL : zlength payload < 2 ^ 26).
  Variable (LOA : ATOP + 4096 <= lo).
  Variable (LOS : lo <= bv_unsigned sp - 16384).
  Variable (SP0 : bv_unsigned sp + 208 = al_sp0 L).
  Variable (SP16 : bv_unsigned sp mod 16 = 0).
  Variable (RCL1 : r_lo rstk <= lo).
  Variable (RCL2 : bv_unsigned sp <= r_hi rstk).
  Variable (RCL3 : ATOP <= r_rlo rstk).
  Variable (FZ : frm0 fc).
  Variable (TP : tp = Z_to_bv 64 ATP).
  Variable (HUL : HU L).
  Variable (RSTK : rng RNG lo (al_top L - lo)).
  Variable (RI : rng_aimg RNG).
  Variable (RISH : rng_aimg_sh RNG).
  Variable (RFS : rng_fs L RNG).
  Variable (RRNG : rrng RNG rstk).
  Variable (AOK : aps_ok L s).
  Variable (RSP : 0 <= bv_unsigned sp < 2 ^ 64).
  Variable (STKW0 : boxed (wr_at asegs m (bv_unsigned sp) (al_top L - bv_unsigned sp))).
  Variable (ATR : 140735332483072 <= ATOP <= 140737479966720).
  Variable (LY1 : al_bot L + 8388608 = al_top L).
  Variable (LY2 : al_top L mod 4096 = 0).
  Variable (LY3 : al_top L <= 2 ^ 47).
  Variable (HTOP : bv_unsigned sp + 16 <= al_top L < bv_unsigned sp + 48 + 4096).
  Variable (junk : list byte).
  Variable (FWL : Forall wfar [(lo, bv_unsigned sp)]).
  Variable (SA : Z).
  Variable (SAB : bv_unsigned sp - 144 <= SA <= bv_unsigned sp - 128 ∧ SA mod 32 = 0).
  Variable (USA : bv_unsigned (Z_to_bv 64 SA) = SA).
  Variable (FF : Z).
  Variable (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word).
  Variable (m1 : amem).
  Variable (j0 j1 j2 : word).
  Variable (jk : list byte).
  Variable (m3 m4 : amem).
  Variable (MI1 : mem_inv asegs m4).
  Variable (STL1 : stk asegs m4 lo SA).
  Variable (F256 : FF mod 256 = 0).
  Variable (FBLK : ablk FF (FF + 256)).
  Variable (FTOP : FF + 256 <= ATOP).
  Variable (RF : rng RNG FF 256).
  Variable (RFSH : rng RNG (FF ≫ 3 + 2147450880) 32).
  Variable (FNC : ∀ a : Z, aclient_addr CI LB (bv_unsigned (Z_to_bv 64 SA)) a → a < shad FF ∨ shad FF + 32 <= a).
  Variable (FB1 : 6705152 <= FF).
  Variable (FB2 : 0 <= FF).
  Variable (FB3 : FF + 256 <= ATOP).
  Variable (FB4 : FF + 256 + 8 <= 2 ^ 47).
  Variable (bF : Z).
  Variable (bFr : 0 <= bF <= 1).
  Variable (bFhi : FF + 256 <= 2147446784 + bF * 140737479966720).
  Variable (bFlo : 17594333495296 * bF <= FF).
  Variable (AWF : awin FF 0).
  Variable (STG1 : stk asegs m4 SA (SA + 16)).
  Variable (STG2 : stk asegs m4 (SA + 48) (bv_unsigned sp + -80)).
  Variable (jF jr : list byte).
  Variable (SFB : 2147450880 <= FF ≫ 3 + 2147450880 ∧ FF ≫ 3 + 2147450880 + 32 <= 17594333495296).
  Variable (FS8 : FF ≫ 3 * 8 = FF).
  Variable (FRF : rw_cells asegs m4 (SA + 16) [C8 (Z_to_bv 64 FF)]).
  Variable (FSH' : rw_cells asegs m4 (FF ≫ 3 + 2147450880) [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  Variable (FC : rw_cells asegs m4 FF [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 96791); C8 (Z_to_bv 64 612444); CB 8 (take 8 jk); C1 (Z_to_bv 8 0); CB 7 (take 7 (drop 9 jk)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 (take 3 (drop 1 (drop 15 (drop 9 jk)))); C4 (Z_to_bv 64 12); CB 192 (drop 7 (drop 1 (drop 15 (drop 9 jk)))); C8 (Z_to_bv 64 (fflag L 2 FF))]).
  Variable (FRR : rw_cells asegs m4 (SA + 24) [CB 24 jr]).
  Variable (FRS : rw_cells asegs m4 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 (Z_to_bv 64 (zlength payload)); C8 (Z_to_bv 64 ATRUN_RET)]).
  Variable (FW2 : Forall wfar [(SA + 16, SA + 24); (FF, FF + 256); (FF ≫ 3 + 2147450880, FF ≫ 3 + 2147450880 + 32)]).
  Variable (CI4 : client_img m4).
  Variable (CSH4 : client_sh m4).
  Variable (CST4 : client_static s LB m4).
  Variable (RCL4 : rclean m4 rstk).
  Variable (AH4 : AHEAP AI L RNG (aps_m s) ({| ab_kind := ABFake 2; ab_addr := FF; ab_size := 256 |} :: LB) m4).
  Variable (PW4 : aheap_pres_W CI LB (bv_unsigned sp) client_wr m m4).
  Variable (AFR : AFRESH (aps_m s)).
  Variable (DKF0 : dk (aps_m s) <= DKF).
  Lemma afuzz_t1 :
    evtF asegs RNG (λ ms' : machine_state, implMA RNG (b <- parse_into_doc (amalloc AAllocAsan) (afree AAllocAsan) (new_handlerA AAllocAsan) payload;; parser_dtor (afree AAllocAsan) b;;; mret 0) s (λ (a : Z) (s' : APS) (RNG' : footprint) (ms'0 : machine_state), DK 8 s s' → fuzz_oneU_postW AI L RNG (Z_to_bv 64 ATRUN_RET) sp gp tp (Z_to_bv 64 (zlength payload)) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m a s' RNG' ms'0) ms') (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some u6) TEmpty) (Some b5) TEmpty) (Some u2) (TNode TEmpty (Some (Z_to_bv 64 (FF ≫ 3 + 2147450880))) TEmpty)) (Some gp) (TNode (TNode TEmpty (Some (Z_to_bv 64 (zlength payload))) TEmpty) (Some (Z_to_bv 64 0)) (TNode TEmpty (Some s11) TEmpty))) (Some (Z_to_bv 64 612776)) (TNode (TNode (TNode TEmpty (Some b7) TEmpty) (Some (Z_to_bv 64 SA)) (TNode TEmpty (Some s9) TEmpty)) (Some u0) (TNode (TNode TEmpty (Some (Z_to_bv 64 (FF + 32))) TEmpty) (Some b3) (TNode TEmpty (Some u4) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some b6) TEmpty) (Some sp) (TNode TEmpty (Some (Z_to_bv 64 FF)) TEmpty)) (Some tp) (TNode (TNode TEmpty (Some (Z_to_bv 64 D)) TEmpty) (Some (Z_to_bv 64 24)) (TNode TEmpty (Some u3) TEmpty))) (Some (Z_to_bv 64 SA)) (TNode (TNode (TNode TEmpty (Some (Z_to_bv 64 FF)) TEmpty) (Some (Z_to_bv 64 (FF + 56))) (TNode TEmpty (Some s10) TEmpty)) (Some u1) (TNode (TNode TEmpty (Some (Z_to_bv 64 (FF + 56))) TEmpty) (Some b4) (TNode TEmpty (Some u5) TEmpty))))) F (Z_to_bv 64 417604) fc None m4 (seg_rom asegs)).

  Proof using All.
    pose proof (proj1 CST4) as CL0. (* [comment removed for export] *)
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH4) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
    (* [comment removed for export] *)
    destruct (rw_cells_app_split asegs _ _ [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 96791); C8 (Z_to_bv 64 612444); CB 8 _; C1 (Z_to_bv 8 0); CB 7 _;
                C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 _; C4 (Z_to_bv 64 12)] _ FC) as [FCa FCr]. clear FC.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FCr.
    destruct (rw_cells_app_split asegs _ _ [CB 192 _] _ FCr) as [FCb FCc]. clear FCr.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FCc. replace (FF + 56 + 192) with (FF + 248) in FCc by lia.
    pose proof (rw_cells_split_CB asegs _ (FF + 56) [] 192 _ [] [24%nat; 8%nat; 8%nat; 16%nat; 136%nat] FCb ltac:(reflexivity)) as SPL.
    cbn [app mk_CB_cells] in SPL. clear FCb.
    destruct (rw_cells_cut asegs _ _ _ 1 SPL) as [P24 SPL1]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in P24, SPL1.
    destruct (rw_cells_cut asegs _ _ _ 2 SPL1) as [P80 SPL2]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in P80, SPL2.
    destruct (rw_cells_cut asegs _ _ _ 1 SPL2) as [P96 P112]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in P96, P112.
    clear SPL SPL1 SPL2.
    replace (FF + 56 + 24) with (FF + 80) in P80 by lia. replace (FF + 56 + 24 + 16) with (FF + 96) in P96, P112 by lia.
    replace (FF + 96 + 16) with (FF + 112) in P112 by lia.
    (* [comment removed for export] *)
    assert (SHF : shad FF = FF ≫ 3 + 2147450880) by (unfold shad, ASHOFF; lia).
    assert (SHF128 : shad (FF + 128) - shad FF = 16) by (rewrite !shad_div; clear - F256 FB2; Z.div_mod_to_equations; lia).
    assert (WSH4 : wr_at asegs m4 (shad FF) (shad (FF + 128) - shad FF)) by (rewrite SHF128, SHF; exact (rw_cells_wr_at _ _ _ _ 16 FSH' ltac:(cbn; lia))).
    assert (RSH16 : rng RNG (shad FF) (shad (FF + 128) - shad FF)) by (rewrite SHF128, SHF; eapply rng_sub'; [exact RFSH| lia]).
    Local Ltac ushad3 FSH := intros i Hi;
      match goal with |- _ (wa (?b + ?k + i)) = _ => replace (b + k + i) with (b + (k + i)) by lia end;
      eapply (cells_byteF _ _ _ _ _ FSH); [| lia| lia];
      assert (Hi' : i = 0 \/ i = 1 \/ i = 2) by lia; destruct Hi' as [-> | [-> | ->]]; reflexivity.
    Local Ltac ushad2 FSH := intros i Hi;
      match goal with |- _ (wa (?b + ?k + i)) = _ => replace (b + k + i) with (b + (k + i)) by lia end;
      eapply (cells_byteF _ _ _ _ _ FSH); [| lia| lia];
      assert (Hi' : i = 0 \/ i = 1) by lia; destruct Hi' as [-> | ->]; reflexivity.
    assert (U56 : unpoisoned m4 (FF + 56) (FF + 56 + 24)).
    { eapply (unpoisoned_of_zeroF m4 (FF + 56) (FF + 56 + 24) (FF ≫ 3 + 2147450880 + 7)); [lia| lia| lia| unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - F256 FB2; Z.div_mod_to_equations; lia|].
      replace ((FF + 56 + 24 + 7) / 8 - (FF + 56) / 8) with 3 by (clear - F256 FB2; Z.div_mod_to_equations; lia). ushad3 FSH'. }
    assert (UF56 : bv_unsigned (Z_to_bv 64 (FF + 56)) = FF + 56) by (apply unsigned_lit; lia).
    assert (U24 : bv_unsigned (Z_to_bv 64 24) = 24) by reflexivity. assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    eapply evtF_cut.
    { eapply (asan_memset_spec RNG) with (lo := lo) (RLO2 := FF) (RHI2 := FF + 128);
        rewrite ?UF56, ?USA, ?U24, ?U0;
        first [ exact P24 | eassumption | (unfold KHIGH; clear - LOA ATR; lia) | (left; clear - FB3 LOA; lia) | (clear - LOS SAB; lia)
              | (apply ablk_app_blk; [eapply ablk_sub; [exact FBLK| lia| lia]| lia]) | (clear; lia)
              | (repeat split; clear - F256 FB2 FB4; unfold KEND; Z.div_mod_to_equations; lia)
              | (eapply rng_sub'; [exact RSTK| clear - LOA LOS SAB HTOP; lia]) | (eapply rng_sub'; [exact RF| lia]) ]. }
    cbv beta. intros ms5 (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & SET5).
    rewrite ?UF56, ?USA, ?U24 in MU5. rewrite ?USA in ST5. rewrite ?UF56, ?U24, ?U0 in SET5. retlit.
    change (Z.to_nat 24) with 24%nat in SET5. change (0 mod 256) with 0 in SET5.
    (* [comment removed for export] *)
    Local Ltac post_memset mn X n AHo MU WM PWo CIo CSHo CSTo RCLo AHn PWn CIn CSHn CSTn RCLn :=
      assert (AHn : AHEAP AI L RNG (aps_m s) (mkABlock (ABFake 2) FF 256 :: LB) mn)
        by (eapply (AI_frame AI); [exact AHo| exact MU| exact WM|];
            apply Forall_cons; [left; left; cbn; clear - LOA LOS SAB ATR HTOP LY3; lia|];
            apply Forall_cons; [right; left; exists (mkABlock (ABFake 2) FF 256); split; [left; reflexivity| cbn; lia]| apply Forall_nil]);
      assert (PWn : aheap_pres_W CI LB (bv_unsigned sp) client_wr m mn)
        by (eapply aheap_pres_W_trans; [exact PWo|]; eapply aheap_pres_W_of_munch; [exact MU| exact WM|]; intros a Ha Hc Hx; cbn [outside];
            pose proof (fresh_fake_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AHo FBLK ltac:(lia) Hc) as NF;
            pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as Ha';
            clear - NF Ha' SAB LOA LOS RSP ATR; repeat split; try exact I; lia);
      assert (FWn : Forall wfar [(SA - 2208, SA); (X, X + n)])
        by (apply Forall_cons; [apply wfar_high; lia| apply Forall_cons; [eapply wfar_ablk; [exact FBLK| lia| lia]| apply Forall_nil]]);
      pose proof (client_img_munch32 _ _ _ CIo MU WM FWn) as CIn; pose proof (client_sh_munch32 _ _ _ CSHo MU FWn) as CSHn;
      pose proof (client_static_munch32 _ _ _ _ _ CSTo MU WM FWn) as CSTn;
      assert (RCLn : rclean mn rstk)
        by (eapply (rclean_munchF _ _ _ _ RCLo MU WM); pose proof RCLo as ((_ & (H1 & H2 & H3 & H4 & H5 & H6) & _ & _) & _);
            rewrite !shad_div; unfold ASHOFF, KEND in *; cbn [disjoint_from];
            clear - H1 H2 H3 H4 H5 H6 RCL3 FB1 FB2 FB3 bFr bFhi bFlo ATR SAB LOA LOS RSP; Z.div_mod_to_equations; lia);
      clear AHo PWo CIo CSHo CSTo RCLo FWn.
    clear P24. Time trmB MU5 WM5.
    assert (AH5 : AHEAP AI L RNG (aps_m s) (mkABlock (ABFake 2) FF 256 :: LB) m5).
    { eapply (AI_frame AI); [exact AH4| exact MU5| exact WM5|].
      apply Forall_cons; [left; left; cbn; clear - LOA LOS SAB ATR HTOP LY3; lia|].
      apply Forall_cons; [right; left; exists (mkABlock (ABFake 2) FF 256); split; [left; reflexivity| cbn; lia]| apply Forall_nil]. }
    idtac "AH5".
    assert (PW5 : aheap_pres_W CI LB (bv_unsigned sp) client_wr m m5).
    { eapply aheap_pres_W_trans; [exact PW4|]. eapply aheap_pres_W_of_munch; [exact MU5| exact WM5|]. intros a Ha Hc Hx. cbn [outside].
      pose proof (fresh_fake_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH4 FBLK ltac:(lia) Hc) as NF.
      pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as Ha'.
      clear - NF Ha' SAB LOA LOS RSP ATR. repeat split; try exact I; lia. }
    idtac "PW5".
    assert (FW5 : Forall wfar [(SA - 2208, SA); (FF + 56, FF + 56 + 24)])
      by (apply Forall_cons; [apply wfar_high; lia| apply Forall_cons; [eapply wfar_ablk; [exact FBLK| lia| lia]| apply Forall_nil]]).
    pose proof (client_img_munch32 _ _ _ CI4 MU5 WM5 FW5) as CI5. pose proof (client_sh_munch32 _ _ _ CSH4 MU5 FW5) as CSH5.
    pose proof (client_static_munch32 _ _ _ _ _ CST4 MU5 WM5 FW5) as CST5.
    idtac "CST5".
    assert (RCL5 : rclean m5 rstk).
    { eapply (rclean_munchF _ _ _ _ RCL4 MU5 WM5). pose proof RCL4 as ((_ & (H1 & H2 & H3 & H4 & H5 & H6) & _ & _) & _).
      rewrite !shad_div. unfold ASHOFF, KEND in *. cbn [disjoint_from].
      clear - H1 H2 H3 H4 H5 H6 RCL3 FB1 FB2 FB3 bFr bFhi bFlo ATR SAB LOA LOS RSP. Z.div_mod_to_equations. lia. }
    clear AH4 PW4 CI4 CSH4 CST4 RCL4 FW5.
    clear MU5 WM5 GOT RIC REAL SHB SUA INI LAY.
    (* [comment removed for export] *)
    pose proof (munch_refl [(FF + 80, FF + 96)] m5) as MU6. pose proof (wmono_refl asegs m5) as WM6.
    park_memA m5. unfold parkedA in P80.
    Time steps_to 0x65f44.
    unparkA. Time trmB MU6 WM6.
    assert (AH6 : AHEAP AI L RNG (aps_m s) (mkABlock (ABFake 2) FF 256 :: LB) m6).
    { eapply (AI_frame AI); [exact AH5| exact MU6| exact WM6|].
      apply Forall_cons; [right; left; exists (mkABlock (ABFake 2) FF 256); split; [left; reflexivity| cbn; lia]| apply Forall_nil]. }
    assert (PW6 : aheap_pres_W CI LB (bv_unsigned sp) client_wr m m6).
    { eapply aheap_pres_W_trans; [exact PW5|]. eapply aheap_pres_W_of_munch; [exact MU6| exact WM6|]. intros a Ha Hc Hx. cbn [outside].
      pose proof (fresh_fake_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH5 FBLK ltac:(lia) Hc) as NF.
      clear - NF. repeat split; try exact I; lia. }
    assert (FW6 : Forall wfar [(FF + 80, FF + 96)]) by (apply Forall_cons; [eapply wfar_ablk; [exact FBLK| lia| lia]| apply Forall_nil]).
    pose proof (client_img_munch32 _ _ _ CI5 MU6 WM6 FW6) as CI6. pose proof (client_sh_munch32 _ _ _ CSH5 MU6 FW6) as CSH6.
    pose proof (client_static_munch32 _ _ _ _ _ CST5 MU6 WM6 FW6) as CST6.
    assert (RCL6 : rclean m6 rstk).
    { eapply (rclean_munchF _ _ _ _ RCL5 MU6 WM6). pose proof RCL5 as ((_ & (H1 & H2 & H3 & H4 & H5 & H6) & _ & _) & _).
      rewrite !shad_div. unfold ASHOFF, KEND in *. cbn [disjoint_from].
      clear - H1 H2 H3 H4 H5 H6 RCL3 FB1 FB2 FB3 bFr bFhi bFlo ATR SAB LOA LOS RSP. Z.div_mod_to_equations. lia. }
    clear AH5 PW5 CI5 CSH5 CST5 RCL5 FW6 MU6 WM6.
    (* [comment removed for export] *)
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH6) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
    assert (WSH6 : wr_at asegs m6 (shad FF) (shad (FF + 128) - shad FF)) by (rewrite SHF128, SHF; exact (rw_cells_wr_at _ _ _ _ 16 FSH' ltac:(cbn; lia))).
    assert (U96 : unpoisoned m6 (FF + 96) (FF + 96 + 16)).
    { eapply (unpoisoned_of_zeroF m6 (FF + 96) (FF + 96 + 16) (FF ≫ 3 + 2147450880 + 12)); [lia| lia| lia| unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - F256 FB2; Z.div_mod_to_equations; lia|].
      replace ((FF + 96 + 16 + 7) / 8 - (FF + 96) / 8) with 2 by (clear - F256 FB2; Z.div_mod_to_equations; lia). ushad2 FSH'. }
    assert (UF96 : bv_unsigned (Z_to_bv 64 (FF + 96)) = FF + 96) by (apply unsigned_lit; lia).
    assert (U16 : bv_unsigned (Z_to_bv 64 16) = 16) by reflexivity.
    eapply evtF_cut.
    { eapply (asan_memset_spec RNG) with (lo := lo) (RLO2 := FF) (RHI2 := FF + 128);
        rewrite ?UF96, ?USA, ?U16, ?U0;
        first [ exact P96 | eassumption | (unfold KHIGH; clear - LOA ATR; lia) | (left; clear - FB3 LOA; lia) | (clear - LOS SAB; lia)
              | (apply ablk_app_blk; [eapply ablk_sub; [exact FBLK| lia| lia]| lia]) | (clear; lia)
              | (repeat split; clear - F256 FB2 FB4; unfold KEND; Z.div_mod_to_equations; lia)
              | (eapply rng_sub'; [exact RSTK| clear - LOA LOS SAB HTOP; lia]) | (eapply rng_sub'; [exact RF| lia]) ]. }
    cbv beta. intros ms7 (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m7 & -> & MU7 & WM7 & MI7 & ST7 & SET7).
    rewrite ?UF96, ?USA, ?U16 in MU7. rewrite ?USA in ST7. rewrite ?UF96, ?U16, ?U0 in SET7. retlit.
    change (Z.to_nat 16) with 16%nat in SET7. change (0 mod 256) with 0 in SET7.
    clear P96. Time trmB MU7 WM7.
    post_memset m7 (FF + 96) 16 AH6 MU7 WM7 PW6 CI6 CSH6 CST6 RCL6 AH7 PW7 CI7 CSH7 CST7 RCL7.
    clear MU7 WM7 GOT RIC REAL SHB SUA INI LAY.
    (* [comment removed for export] *)
    Time steps_to 0x95d34.
    (* [comment removed for export] *)
    destruct (rw_cells_app_split asegs _ _ [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 96791); C8 (Z_to_bv 64 612444); CB 8 _; C1 (Z_to_bv 8 0); CB 7 _] _ FCa)
      as [_ FCa2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FCa2.
    destruct (rw_cells_cut asegs _ _ _ 1 FCa2) as [PIM _]. cbn [firstn] in PIM. replace (FF + 40) with (FF + 32 + 8) in PIM by lia. clear FCa2.
    assert (PDOC : rw_cells asegs m7 (FF + 32 + 24) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
      by (replace (FF + 32 + 24) with (FF + 56) by lia; eapply rw_cells_recast; [exact SET5| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]).
    destruct (rw_cells_cut asegs _ _ _ 2 P80) as [PMAX _]. cbn [firstn] in PMAX. replace (FF + 80) with (FF + 32 + 48) in PMAX by lia. clear P80.
    assert (PCP : rw_cells asegs m7 (FF + 32 + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
      by (replace (FF + 32 + 64) with (FF + 96) by lia; eapply rw_cells_recast; [exact SET7| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]).
    (* [comment removed for export] *)
    pose proof FSH' as FSHk.
    destruct (rw_cells_app_split asegs _ _ [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
                C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601)] _ FSH') as [_ FSHb].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FSHb.
    destruct (rw_cells_app_split asegs _ _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] _ FSHb) as [FSHp _]. clear FSHb.
    assert (SHP : rw_cells asegs m7 (shx (FF + 32)) [CB 10 (repeat (Z_to_bv 8 0) 10)]).
    { replace (shx (FF + 32)) with (FF ≫ 3 + 2147450880 + 4)
        by (unfold shx, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - F256 FB2; Z.div_mod_to_equations; lia).
      eapply rw_cells_recast; [exact FSHp| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. }
    clear FSHp.
    assert (SHR : rw_cells asegs m7 (shx (SA + 24)) [CB 3 (repeat (Z_to_bv 8 0) 3)]).
    { unfold shx, ASHOFF. exact (shadow_cells_of_rclean m7 rstk (SA + 24) 3 RCL7 ltac:(lia) ltac:(lia) ltac:(clear - SAB; Z.div_mod_to_equations; lia) ltac:(lia)). }
    assert (RPR : rng RNG (SA + 24) 24) by (eapply rng_sub'; [exact RSTK| clear - LOA LOS SAB HTOP; lia]).
    pose proof RRNG as RRNG'. unfold rrng in RRNG'. pose proof RCL7 as ((_ & (H1 & H2 & H3 & H4 & H5 & H6) & _ & _) & _).
    assert (RSHR : rng RNG (shx (SA + 24)) (shx (SA + 24 + 24) - shx (SA + 24))).
    { eapply rng_sub'; [exact RRNG'|]. rewrite !shad_div. unfold shx, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - H1 H2 RCL1 RCL2 LOS SAB. Z.div_mod_to_equations. lia. }
    assert (RPP : rng RNG (FF + 32) 80) by (eapply rng_sub'; [exact RF| lia]).
    assert (RSHP : rng RNG (shx (FF + 32)) (shx (FF + 32 + 80) - shx (FF + 32))).
    { eapply rng_sub'; [exact RFSH|]. unfold shx, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - F256 FB2. Z.div_mod_to_equations. lia. }
    clear H1 H2 H3 H4 H5 H6 RRNG'.
    (* [comment removed for export] *)
    assert (WST : wr_at asegs m7 (SA - 112 - 16) (al_top L - (SA - 112 - 16))).
    { unbox STKW0. assert (WH : wr_at asegs m7 (bv_unsigned sp) (al_top L - bv_unsigned sp)).
      { eapply (aheap_pres_W_wr_at CI _ _ _ _ _ _ _ PW7 STKW0); [left; left; clear - HTOP LY3; lia|].
        intros a Ha. cbn [client_wr outside]. clear - Ha LOA LOS ATR. lia. }
      pose proof (wr_at_of_stkF _ _ _ (SA - 128) 128 ST7 ltac:(clear - LOA LOS SAB; lia) ltac:(lia) ltac:(lia)) as W1.
      pose proof (wr_at_of_stkF _ _ _ SA 16 STG1 ltac:(lia) ltac:(lia) ltac:(lia)) as W2.
      pose proof (rw_cells_wr_at _ _ _ _ 8 FRF ltac:(cbn; lia)) as W3.
      pose proof (rw_cells_wr_at _ _ _ _ 24 FRR ltac:(cbn; lia)) as W4.
      pose proof (wr_at_of_stkF _ _ _ (SA + 48) (bv_unsigned sp + -80 - (SA + 48)) STG2 ltac:(lia) ltac:(lia) ltac:(clear - SAB; lia)) as W5.
      pose proof (rw_cells_wr_at _ _ _ _ 80 FRS ltac:(cbn; lia)) as W6.
      pose proof (wr_at_joinF _ _ _ _ _ W1 W2 ltac:(lia) ltac:(lia) ltac:(lia)) as J1.
      pose proof (wr_at_joinF _ _ _ _ _ J1 W3 ltac:(lia) ltac:(lia) ltac:(lia)) as J2.
      pose proof (wr_at_joinF _ _ _ _ _ J2 W4 ltac:(lia) ltac:(lia) ltac:(lia)) as J3.
      pose proof (wr_at_joinF _ _ _ _ _ J3 W5 ltac:(lia) ltac:(lia) ltac:(clear - SAB; lia)) as J4.
      pose proof (wr_at_joinF _ _ _ _ _ J4 W6 ltac:(lia) ltac:(clear - SAB; lia) ltac:(lia)) as J5.
      pose proof (wr_at_joinF _ _ _ _ _ J5 WH ltac:(lia) ltac:(clear - SAB; lia) ltac:(clear - HTOP; lia)) as J6.
      replace (SA - 112 - 16) with (SA - 128) by lia. eapply wr_at_subF; [exact J6| lia| clear - SAB HTOP; lia| clear - SAB HTOP; lia]. }
    destruct (uchain_exists m7 (al_top L) AFREE_PC (Nat.pred UDEPTH) (SA - 112) (SA + 24) ltac:(clear - LOA LOS SAB ATR; lia) LY3 WST) as (trR & UCR).
    pose proof (uchain_length _ _ _ _ _ _ _ UCR) as TRR. unfold UDEPTH in TRR. cbn in TRR.
    (* [comment removed for export] *)
    assert (DAT7 : bytes_at asegs m7 D (map (Z_to_bv 8) payload)).
    { destruct PAY as [(p & Hp & Hl)|(E1 & E2)].
      - eapply (aheap_pres_W_bytes_at CI _ _ _ _ _ _ _ PW7 DAT).
        + right; left. exists (HB p D (zlength payload)). split; [exact Hp|]. cbn. rewrite length_map. unfold zlength. lia.
        + intros a Ha. rewrite length_map in Ha. pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hp) as BB. cbn [ab_addr ab_size] in BB.
          unfold AIMG_HI in BB. cbn [client_wr outside]. unfold zlength in BB. clear - Ha BB. lia.
      - subst payload D. destruct DAT as (B0 & B1 & _). split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia. }
    apply evtF_done.
    pose proof (apid_proof AI rng_fs ONTA ODA IMG_CI PARSE RFSM) as PID. unfold apid_stmt in PID.
    eapply implMA_bind.
    { Time eapply PID with (L := L) (RNG := RNG) (s := s) (LB := mkABlock (ABFake 2) FF 256 :: LB) (lo := lo) (rstk := rstk)
          (data := payload) (D := D) (P := FF + 32) (R := SA + 24) (jr := jr) (trR := trR);
        rewrite ?USA;
        first [ eassumption
              | (intros b [<-|Hb]; [right; exists 2, FF, 256; split; [reflexivity| split; discriminate]| left; exact (LBK b Hb)])
              | (destruct PAY as [(p & Hp & Hl)|(E1 & E2)]; [left; exists p; split; [right; exact Hp| exact Hl]| right; split; assumption])
              | (exists 2, FF, 256; split; [left; reflexivity| split; [lia| split; [lia| exact FBLK]]])
              | (unfold APID_STACK, APARSE_STACK, STAGE2_STACK_A; clear - LOS SAB; lia)
              | (clear - DKF0; unfold DKF, DWMAX in *; lia)
              | reflexivity | (f_equal; lia)
              | (clear - SAB LOA LOS RCL2 HTOP LY3 FB3 ATR; lia)
              | (clear - SAB; Z.div_mod_to_equations; lia) | (clear - F256; Z.div_mod_to_equations; lia) ]. }
    cbv beta. intros r s1' RNG1 ms1 PO.
    destruct PO as (FPL1 & q0 & q1 & q2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & q3 & q4 & q5 & q6 & F8 & fc8 & m8 & -> & FZ8 & MI8 & ST8 & STR8 & PW8 & ARS8 & CS8
                    & (SBA & TPA & AIM & ASI & AOC & AIA & ACP & AH8 & O8 & O24 & O64 & VT & O16i & O56i)).
    rewrite ?USA in ST8, PW8. retlit.
    destruct r as [[[psb ptp] [[[pim psi] poc] pia]] lb].
    (* [comment removed for export] *)
    destruct (rw_cells_app_split asegs _ _ [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 96791); C8 (Z_to_bv 64 612444)] _ FCa) as [FH _]. clear FCa.
    Local Ltac zofnat := repeat match goal with |- context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v end.
    Local Ltac zofnatH H := repeat match type of H with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in H end.
    Local Ltac trWf PW H := eapply (aheap_pres_W_rw_cells CI _ _ _ _ _ _ _ PW H);
      [ first [ (left; left; cbn; clear - SAB LOA LOS HTOP LY3 ATR; lia)
              | (right; left; exists (mkABlock (ABFake 2) FF 256); split; [left; reflexivity| cbn; lia])
              | (right; right; right; right; exists 2, FF, 256; split; [left; reflexivity|]; cbn [fst snd cells_size csize Nat.add]; zofnat;
                 unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - F256 FB1; Z.div_mod_to_equations; lia) ]
      | intros a Ha; cbn [cells_size csize Nat.add] in Ha; zofnatH Ha; try (rewrite !Z.shiftr_div_pow2 in Ha by lia; change (2^3) with 8 in Ha);
        unfold apid_W, client_wr; cbn [app outside];
        clear - Ha SAB LOA LOS FB1 FB3 F256 ATR bFr bFhi bFlo; Z.div_mod_to_equations; repeat split; try exact I; lia ].
    assert (FRS8 : rw_cells asegs m8 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 (Z_to_bv 64 (zlength payload)); C8 (Z_to_bv 64 ATRUN_RET)])
      by (trWf PW8 FRS).
    assert (FRF8 : rw_cells asegs m8 (SA + 16) [C8 (Z_to_bv 64 FF)]) by (trWf PW8 FRF).
    assert (FH8 : rw_cells asegs m8 FF [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 96791); C8 (Z_to_bv 64 612444)]) by (trWf PW8 FH).
    assert (FCc8 : rw_cells asegs m8 (FF + 248) [C8 (Z_to_bv 64 (fflag L 2 FF))]) by (trWf PW8 FCc).
    lazymatch type of FSHk with rw_cells _ _ ?A ?cs => assert (FSH8 : rw_cells asegs m8 A cs) by (trWf PW8 FSHk) end.
    assert (SHP8 : rw_cells asegs m8 (Z.shiftr (FF + 32) 3 + 2147450880) [CB 10 (repeat (Z_to_bv 8 0) 10)]) by (unfold shx, ASHOFF in SHP; trWf PW8 SHP).
    pose proof (aheap_pres_W_stkF CI _ _ _ _ _ _ _ PW8 STG1 ltac:(lia) ltac:(clear - SAB HTOP LY3; lia) ltac:(intros a Ha; unfold apid_W, client_wr; cbn [app outside]; clear - Ha SAB LOA LOS FB1 FB3 ATR; repeat split; try exact I; lia)) as STG1'.
    pose proof (aheap_pres_W_stkF CI _ _ _ _ _ _ _ PW8 STG2 ltac:(lia) ltac:(clear - SAB HTOP LY3; lia) ltac:(intros a Ha; unfold apid_W, client_wr; cbn [app outside]; clear - Ha SAB LOA LOS FB1 FB3 ATR; repeat split; try exact I; lia)) as STG2'.
    assert (FWA : Forall wfar2 (apid_W (FF + 32) (SA + 24))).
    { unfold apid_W, client_wr, wfar2, KLS. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - SAB LOA LOS FB1 FB3 bFr bFhi bFlo ATR; lia. }
    pose proof (client_img_W AI IMG_CI _ _ _ _ _ _ _ _ _ CI7 PW8 FWA AH8 MI8) as CI8.
    pose proof (client_sh_W AI IMG_CI _ _ _ _ _ CSH7 PW8 FWA) as CSH8.
    clear FRS FRF FH FCc FSHk SHP STG1 STG2 FRR SHR ST7 CI7 CSH7 CST7 DAT7 PIM PDOC PMAX PCP SET5 SET7 FSH' UCR WST.
    (* [comment removed for export] *)
    pose proof (rng_fp_le _ _ _ _ FPL1 RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FPL1 RI) as RI1. pose proof (rng_fp_le _ _ _ _ FPL1 RISH) as RISH1.
    pose proof (rng_fp_le _ _ _ _ FPL1 RPP) as RPP1. pose proof (rng_fp_le _ _ _ _ FPL1 RSHP) as RSHP1.
    assert (RSHP10 : rng RNG1 (shx (FF + 32)) 10).
    { eapply rng_sub'; [exact RSHP1|]. unfold shx, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - F256 FB2. Z.div_mod_to_equations. lia. }
    apply implMA_from_evtF.
    do 2 zstep.
    apply evtF_done.
    unfold apid_blocks in AH8. rewrite <- app_assoc in AH8. cbn [snd] in O64.
    Local Ltac scr mm SH X j := let H := fresh "SCR" in
      assert (H : shc mm (X + 8 * j)) by (unfold shc, shx, ASHOFF; exact (shadow_cell_of_run mm X 10 j ltac:(clear - F256; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) SH));
      cbn [Z.mul] in H.
    scr m8 SHP8 (FF + 32) 1. scr m8 SHP8 (FF + 32) 3. scr m8 SHP8 (FF + 32) 4. scr m8 SHP8 (FF + 32) 8.
    replace (FF + 32 + 8 * 1) with (FF + 32 + 8) in SCR by lia. replace (FF + 32 + 8 * 3) with (FF + 32 + 24) in SCR0 by lia.
    replace (FF + 32 + 8 * 4) with (FF + 32 + 32) in SCR1 by lia. replace (FF + 32 + 8 * 8) with (FF + 32 + 64) in SCR2 by lia.
    (* [comment removed for export] *)
    assert (HTOP2 : bv_unsigned sp + 32 <= al_top L).
    { unfold al_top. rewrite <- SP0. unfold page_round_up_Z. change page_size with 4096. replace (bv_unsigned sp + 208 - 160) with (bv_unsigned sp + 48) by lia.
      clear. Z.div_mod_to_equations. lia. }
    pose proof FRS8 as FRSc. destruct (rw_cells_app_split asegs _ _ [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _ FRSc) as [_ FRT]. clear FRSc.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRT. replace (bv_unsigned sp + -80 + 64) with (bv_unsigned sp - 16) in FRT by lia.
    destruct (rw_cells_cut asegs _ _ _ 1 FRT) as [FRT1 FRT2]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRT1, FRT2.
    replace (bv_unsigned sp - 16 + 8) with (bv_unsigned sp - 8) in FRT2 by lia.
    pose proof (rw_cells_bytes_at _ _ _ _ FRT1) as BFP. pose proof (rw_cells_bytes_at _ _ _ _ FRT2) as BRA. cbn [cells_bytes cbytes] in BFP, BRA. rewrite app_nil_r in BFP, BRA.
    assert (UCD : uchain m8 (al_top L) AFREE_PC SA (bv_unsigned sp) UDEPTH [ATRUN_RET]).
    { change [ATRUN_RET] with ((if ATRUN_RET =? AFREE_PC then [] else [ATRUN_RET]) ++ []).
      eapply (uc_step m8 (al_top L) AFREE_PC SA (bv_unsigned sp) UDEPTH (zlength payload) ATRUN_RET []);
        [ lia | clear - HTOP2; lia | clear - SP16; Z.div_mod_to_equations; lia | unfold UDEPTH; lia | exact BFP | exact BRA | unfold ATRUN_RET; lia | unfold zlength in *; lia |].
      apply uc_stop. unfold zlength in *. clear - LOS LOA ATR DL. lia. }
    clear FRT FRT1 FRT2 BFP BRA.
    pose proof (apdtor_proof AI ODA OD IMG_CI) as PD. unfold apdtor_stmt in PD.
    eapply implMA_bind.
    { Time eapply PD with (L := L) (RNG := RNG1) (s := s1') (LB0 := mkABlock (ABFake 2) FF 256 :: LB) (lb := lb) (pia := pia) (poc := poc) (psi := psi)
          (pim := pim) (ptp := ptp) (psb := psb) (ACP := ACP) (AIA := AIA) (AOC := AOC) (ASI := ASI) (AIM := AIM) (TPA := TPA) (SBA := SBA)
          (lo := lo) (P := FF + 32) (tr := [ATRUN_RET]);
        rewrite ?USA;
        first [ eassumption
              | (unfold IMPL_BYTES; lia)
              | (replace ADTOR_STACK with 4160 by reflexivity; clear - LOS SAB; lia)
              | (exists 2, FF, 256; split; [left; reflexivity| split; [lia| split; [lia| exact FBLK]]])
              | (eapply (HU_in _ _ HUL); unfold HU_TRACES; repeat (first [left; reflexivity | right])) | (eapply aps_ok_rest; [exact ARS8| exact AOK])
              | reflexivity | (cbn [length]; lia) | (unfold ATRUN_RET, AFREE_PC; lia) | (rewrite unsigned_lit by lia; unfold AFREE_PC; lia)
              | (clear - SAB LOA LOS HTOP LY3 FB3 ATR; lia) | (clear - SAB; Z.div_mod_to_equations; lia) | (clear - F256; Z.div_mod_to_equations; lia) ]. }
    cbv beta. intros [] s2' RNG2 ms2 PO2.
    destruct PO2 as (FPL2 & v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m9 & -> & MI9 & ST9 & HPX9 & ARS9 & AH9).
    rewrite ?USA in ST9. rewrite ?USA in HPX9. retlit.
    (* [comment removed for export] *)
    Local Ltac trXf HPX H := eapply (aheap_pres_x_rw_cells CI _ _ _ _ _ _ _ _ HPX H);
      [ first [ (left; left; cbn; clear - SAB LOA LOS HTOP LY3 ATR; lia)
              | (right; left; exists (mkABlock (ABFake 2) FF 256); split; [left; reflexivity| cbn; lia])
              | (right; right; right; right; exists 2, FF, 256; split; [left; reflexivity|]; cbn [fst snd cells_size csize Nat.add]; zofnat;
                 unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - F256 FB1; Z.div_mod_to_equations; lia) ]
      | cbn [cells_size csize Nat.add]; zofnat; try (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8);
        clear - SAB LOA LOS FB1 FB3 F256 ATR bFr bFhi bFlo; Z.div_mod_to_equations; lia ].
    assert (FRS9 : rw_cells asegs m9 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 (Z_to_bv 64 (zlength payload)); C8 (Z_to_bv 64 ATRUN_RET)])
      by (trXf HPX9 FRS8).
    assert (FRF9 : rw_cells asegs m9 (SA + 16) [C8 (Z_to_bv 64 FF)]) by (trXf HPX9 FRF8).
    assert (FH9 : rw_cells asegs m9 FF [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 96791); C8 (Z_to_bv 64 612444)]) by (trXf HPX9 FH8).
    assert (FCc9 : rw_cells asegs m9 (FF + 248) [C8 (Z_to_bv 64 (fflag L 2 FF))]) by (trXf HPX9 FCc8).
    lazymatch type of FSH8 with rw_cells _ _ ?A ?cs => assert (FSH9 : rw_cells asegs m9 A cs) by (trXf HPX9 FSH8) end.
    pose proof (aheap_pres_x_stk CI _ _ _ _ _ _ _ _ HPX9 STG1' ltac:(lia) ltac:(clear - SAB HTOP LY3; lia) ltac:(right; lia)) as STG1''.
    pose proof (aheap_pres_x_stk CI _ _ _ _ _ _ _ _ HPX9 STG2' ltac:(lia) ltac:(clear - SAB HTOP LY3; lia) ltac:(right; clear - SAB LOA LOS FB3 ATR; lia)) as STG2''.
    pose proof (aheap_pres_x_stk CI _ _ _ _ _ _ _ _ HPX9 STR8 ltac:(lia) ltac:(clear - SAB HTOP LY3; lia) ltac:(right; clear - SAB LOA LOS FB3 ATR; lia)) as STR9.
    assert (WFP : wfar (FF + 32 + 8, FF + 32 + 8 + 64)) by (eapply wfar_ablk; [exact FBLK| lia| lia]).
    pose proof (client_img_pres_x AI IMG_CI _ _ _ _ _ _ _ _ _ _ HPX9 WFP CI8 AH9 MI9) as CI9.
    pose proof (client_sh_pres_x AI IMG_CI _ _ _ _ _ _ HPX9 WFP CSH8) as CSH9.
    pose proof (client_static1_pres_x AI IMG_CI _ _ _ _ _ _ HPX9 WFP CS8) as CS9.
    clear FRS8 FRF8 FH8 FCc8 FSH8 STG1' STG2' CI8 CSH8 CS8.
    (* [comment removed for export] *)
    apply implMA_ret.
    destruct (FAKE_FLAG _ _ _ _ _ _ _ _ AH9 (or_introl eq_refl)) as (FLC & RFL & FLB & FLT & FLD & FLCI).
    pose proof (ablk_lin _ _ FLB) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1. band_ind FLB bG.
    pose proof (rng_fp_le _ _ _ _ (fp_le_trans _ _ _ FPL1 FPL2) RFSH) as RFSH2. pose proof (rng_fp_le _ _ _ _ (fp_le_trans _ _ _ FPL1 FPL2) RF) as RF2.
    pose proof (munch_refl [(FF ≫ 3 + 2147450880, FF ≫ 3 + 2147450880 + 32); (FF, FF + 8)] m9) as MU10. pose proof (wmono_refl asegs m9) as WM10.
    park_memA m9. unfold parkedA in FH9, FCc9, FSH9.
    Local Ltac mem_after_store ::= mem_after_store_fast.
    set (FS := FF ≫ 3) in *. assert (EFS : FF ≫ 3 = FS) by reflexivity. clearbody FS.
    ltac2:(only_rng [@RFSH2; @RF2]). ltac2:(hide_arith [@SFB; @FS8; @FB1; @FB2; @FB3; @bFr; @bFhi; @bFlo]).
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    Time do 10 zstep.
    do 3 zstep.
    zstep. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia| clear KB].
    zstep. replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
    Time do 4 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells asegs mx (FS + 2147450880) _ |- _ =>
      pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK.
    Time do 27 zstep.
    zstep. (* [comment removed for export] *)
    unhide_rng. unhide_arith. unparkA. subst FS.
    (* [comment removed for export] *)
    pose proof (FLD _ (or_introl eq_refl)) as FLD0. cbn [ab_addr ab_size] in FLD0.
    Time trmB MU10 WM10.
    assert (AH11 : AHEAP AI L RNG2 (aps_m s2') (mkABlock (ABFake 2) FF 256 :: LB) m11).
    { eapply (AI_frame AI); [exact AH9| exact MU10| exact WM10|].
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - right; right. right; right. exists 2, FF, 256. split; [left; reflexivity|].
        cbn [fst snd]. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - F256 FB1. Z.div_mod_to_equations. lia.
      - right; left. exists (mkABlock (ABFake 2) FF 256). split; [left; reflexivity| cbn; lia]. }
    assert (FW10 : Forall wfar [(FF ≫ 3 + 2147450880, FF ≫ 3 + 2147450880 + 32); (FF, FF + 8)]).
    { apply Forall_cons; [apply wfar_shad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - FB1; Z.div_mod_to_equations; lia|].
      apply Forall_cons; [eapply wfar_ablk; [exact FBLK| lia| lia]| apply Forall_nil]. }
    pose proof (client_img_munch32 _ _ _ CI9 MU10 WM10 FW10) as CI11. pose proof (client_sh_munch32 _ _ _ CSH9 MU10 FW10) as CSH11.
    pose proof (client_static1_munch32 _ _ _ CS9 MU10 WM10 FW10) as CS11.
    (* [comment removed for export] *)
    assert (PWM : forall LB1 LB2 SP1 SP2 W1 W2 mx my, aheap_pres_W CI LB2 SP2 W2 mx my -> SP2 <= SP1 -> (forall b, In b LB1 -> In b LB2) ->
                  (forall a, aclient_addr CI LB1 SP1 a -> outside W1 a -> outside W2 a) -> aheap_pres_W CI LB1 SP1 W1 mx my).
    { intros LB1 LB2 SP1 SP2 W1 W2 mx my H HS HL HW a Ha Hc Ho. apply H; [exact Ha| | exact (HW a Hc Ho)].
      eapply aclient_addr_mono_sp; [eapply aclient_addr_mono_lb; [exact Hc| exact HL]| exact HS]. }
    assert (NFK : forall a, aclient_addr CI LB (bv_unsigned sp) a -> ~ (FF <= a < FF + 256)).
    { intros a Hc. exact (fresh_fake_not_client AI _ _ _ _ _ _ _ _ (bv_unsigned sp) a AH7 FBLK ltac:(clear - LOA LOS ATR; lia) Hc). }
    assert (PW11 : aheap_pres_W CI LB (bv_unsigned sp) client_wr m m11).
    { eapply aheap_pres_W_trans; [exact PW7|]. eapply aheap_pres_W_trans; [| eapply aheap_pres_W_trans].
      - eapply PWM; [exact PW8| clear - SAB; lia| intros b Hb; right; exact Hb|].
        intros a Hc Ho. cbn [app outside]. pose proof (NFK a Hc) as N1.
        pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH7 (fun b Hb => or_intror Hb) Hc) as Ha'.
        split; [clear - N1; lia| split; [clear - Ha' SAB LOA LOS ATR; lia| exact Ho]].
      - eapply (pres_W_of_x AI); [exact HPX9| clear - SAB; lia| intros b Hb; right; exact Hb|].
        intros a Hc Ho. pose proof (NFK a Hc) as N1. clear - N1. lia.
      - eapply aheap_pres_W_of_munch; [exact MU10| exact WM10|]. intros a Ha Hc Ho. cbn [outside].
        pose proof (NFK a Hc) as N1. pose proof (FNC a ltac:(rewrite USA; eapply aclient_addr_mono_sp; [exact Hc| clear - SAB; lia])) as NS.
        unfold shad, ASHOFF in NS. rewrite Z.add_comm in NS. clear - N1 NS. repeat split; try exact I; lia. }
    clear MU10 WM10 AH9 CI9 CSH9 CS9 PW7 PW8 HPX9 FW10.
    (* [comment removed for export] *)
    pose proof (munch_refl [(fflag L 2 FF, fflag L 2 FF + 1)] m11) as MU11. pose proof (wmono_refl asegs m11) as WM11.
    park_memA m11. unfold parkedA in FLC.
    ltac2:(only_rng [@RFL]).
    Time zstep.
    unhide_rng. unparkA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m12 eqn:EM12 end. clear EM12.
    pose proof (FAKE_RELEASE _ _ _ _ _ _ _ _ AH11) as AH12.
    rewrite <- (mem_eq_single m11 m12 (fflag L 2 FF) (Z_to_bv 8 0) ltac:(lia) ltac:(lia) MU11 (byte_of_c1 _ _ _ FLC ltac:(lia))) in AH12.
    Time trmB MU11 WM11.
    assert (FW11 : Forall wfar [(fflag L 2 FF, fflag L 2 FF + 1)]) by (apply Forall_cons; [eapply wfar_ablk; [exact FLB| lia| lia]| apply Forall_nil]).
    pose proof (client_img_munch32 _ _ _ CI11 MU11 WM11 FW11) as CI12. pose proof (client_sh_munch32 _ _ _ CSH11 MU11 FW11) as CSH12.
    pose proof (client_static1_munch32 _ _ _ CS11 MU11 WM11 FW11) as CS12.
    assert (PW12 : aheap_pres_W CI LB (bv_unsigned sp) client_wr m m12).
    { eapply aheap_pres_W_trans; [exact PW11|]. eapply aheap_pres_W_of_munch; [exact MU11| exact WM11|]. intros a Ha Hc Ho. cbn [outside]. split; [| exact I].
      destruct Hc as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
      - clear - X FL3 LOA LOS ATR. lia.
      - intros X'. apply FLCI. exists iv. split; [exact Hiv| lia].
      - pose proof (FLD b (or_intror Hb)). lia.
      - assert (A47 : 0 <= a' < 2^47).
        { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]];
            [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia| destruct (LBK _ Hb') as (p' & A'' & N' & E'); discriminate]. }
        rewrite shad_div. unfold ASHOFF. eapply (ablk_clear_band _ _ _ FLB). unfold KLS. clear - A47. Z.div_mod_to_equations. lia. }
    clear MU11 WM11 AH11 CI11 CSH11 CS11 PW11 FW11.
    (* [comment removed for export] *)
    pose proof (rng_fp_le _ _ _ _ FPL2 RSTK1) as RSTK2.
    ltac2:(only_rng [@RSTK2]).
    Time do 15 zstep.
    unhide_rng.
    apply evtF_done. cbv beta. intros (DFR & DCL & DRS).
    (* [comment removed for export] *)
    assert (S1 : stk asegs m12 lo (SA + 24)).
    { replace (SA + 24) with (SA + 16 + Z.of_nat (cells_size [C8 (Z_to_bv 64 FF)])) by (cbn; lia).
      eapply stk_release; [eapply stk_merge; [exact ST9| exact STG1''| lia]| exact FRF9| lia]. }
    pose proof (stk_merge asegs _ _ _ _ S1 STR9 ltac:(lia)) as S2. replace (SA + 24 + 24) with (SA + 48) in S2 by lia.
    pose proof (stk_merge asegs _ _ _ _ S2 STG2'' ltac:(clear - SAB LOA LOS; lia)) as S3.
    pose proof (stk_release asegs _ _ _ _ S3 FRS9 ltac:(clear - SAB LOA LOS; lia)) as S4. cbv [cells_size csize Nat.add] in S4.
    replace (bv_unsigned sp + -80 + Z.of_nat 80) with (bv_unsigned sp) in S4 by lia.
    (* [comment removed for export] *)
    assert (ASP : astk_shadow_pres (bv_unsigned sp) m m12).
    { intros a Ha. pose proof ATOP_al16 as AT16. rewrite !shad_div in Ha. unfold ASHOFF in Ha.
      rewrite <- (shad_unshad a).
      refine (proj1 (PW12 (shad (8 * (a - ASHOFF))) _ _ _)).
      - rewrite shad_unshad. unfold ASHOFF. clear - Ha RSP. lia.
      - right; right; right. exists (8 * (a - ASHOFF)). split; [| reflexivity]. left. unfold ASHOFF.
        clear - Ha AT16 HTOP LY3 ATR. Z.div_mod_to_equations. lia.
      - rewrite shad_unshad. unfold client_wr. cbn [outside]. unfold ASHOFF. clear - Ha ATR. Z.div_mod_to_equations. repeat split; try exact I; lia. }
    unfold fuzz_oneU_postW. split; [exact (fp_le_trans _ _ _ FPL1 FPL2)|].
    do 14 eexists. exists F8, fc8, m12, LB. split; [reflexivity|].
    split; [reflexivity|]. split; [exact MI9|]. split; [exact FZ8|]. split; [exact S4|].
    split; [exact (magree_of_pres_W AI _ _ _ _ _ PW12)|]. split; [exact ASP|]. split; [exact AH12|].
    split; [split; [exact CI12| exact CSH12]|].
    split; [split; [rewrite DCL; exact CL0| right; exact CS12]|].
    split; [exact DRS|]. split; [reflexivity|]. split; [exact DCL|].
    destruct (DFR AFR) as [AFR' DKR]. split; [exact AFR'| clear - DKR; lia].
  Qed.

End T.
End S.
End CANSEC1.
