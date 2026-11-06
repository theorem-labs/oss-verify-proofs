(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpya4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_WS7e8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Panhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_WSruy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Ha0ng.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Ha0ng.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Ha0ng.

Module A_Ha3dj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_VStbd A_Panhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_WSruy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Ha0ng.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Ha0ng.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Ha0ng.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_ImgLow OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Panhq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_WSruy.A_HKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Ha0ng.A_Ha5zr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Ha0ng.A_Haqjq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Ha0ng.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (data : Z) (inp : list byte) (SB N : Z) (T : TSet).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPLO : alloc_ceiling + 65536 + LIB_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis MI00 : mem_inv rsegs (aview A0 m0).
  Hypothesis ST00 : stk rsegs (aview A0 m0) (bv_unsigned sp - LIB_STACK) (bv_unsigned sp).
  Hypothesis STKSH00 : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64).
  Hypothesis FR00 : forall ff, a_frame A0 ff = None.
  Hypothesis LEN : Z.of_nat (length inp) < NMAX.
  Hypothesis INP : length inp <> 0%nat -> data <> 0 /\ a_live A0 data = Some (Z.of_nat (length inp)) /\ bytes_at rsegs (aview A0 m0) data inp.
  Hypothesis BUD : a_livebytes A0 + LIB_LIVE (Z.of_nat (length inp)) <= LIVE_MAX /\ a_nlive A0 + LIB_NLIVE <= NLIVE_MAX.
  Hypothesis SECC : LIB_SECC (Z.of_nat (length inp)) <= a_seccred A0.
  Hypothesis PRIMC : LIB_PRIM (Z.of_nat (length inp)) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (md' : Model) (A' : AS),
      alib_post sp m0 md0 A0 inp SB N m' md' A' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj TP (conj SP16 (conj SPLO (conj SPHI (conj AINV00 (conj MI00 (conj ST00 (conj STKSH00 (conj FR00 (conj LEN (conj INP (conj BUD
      (conj SECC (conj PRIMC K)))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    pose proof (zr_word ra) as RAR; unfold inr64 in RAR;
    unfold LIB_STACK in *.

  Local Ltac pose_T :=
    pose proof (seg_T ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 data inp SB N T
                  TP SP16 SPLO SPHI AINV00 MI00 ST00 STKSH00 FR00 LEN INP BUD SECC PRIMC K) as seg_T'.

  (* [comment removed for export] *)
  Local Ltac xfer_stack Hc CF AINV AV a n SPLO ACV D0 SPR :=
    lazymatch type of CF with cframe _ (owned ?A) (owned ?A') ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA A A' xsp win V Nn ma mb CF a) in Hc;
      [| exact (crange_stack (Clg:=Clg) (L:=LPA) A _ _ ma a n AINV ltac:(keeplia SPLO ACV D0) ltac:(keeplia SPR D0)
                 (rw_cells_mapped (Clg:=Clg) LPA _ _ _ Hc ltac:(off_image_solve LPA)))
       | cbn [SAVE Cells.cells_size Cells.csize Nat.add length]; split; [keeplia D0| intros i Hi X; refine (AV _ _ X); keeplia Hi D0] ]
    end.
  (* [comment removed for export] *)
  Local Ltac xfer_frame Hc CF AINV FF AV a CR FB SPLO ACV D0 :=
    lazymatch type of CF with cframe _ (owned ?A) (owned ?A') ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA A A' xsp win V Nn ma mb CF a) in Hc;
      [| eapply CR; [exact AINV| exact FF| clear; lia| rewrite fsize7; change (8192 / 8) with 1024; cbn [Cells.cells_size Cells.csize Nat.add length]; clear; lia| cbn; clear; lia]
       | cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia FB SPLO ACV D0| intros i Hi X; refine (AV _ _ X); keeplia Hi] ]
    end.
  (* [comment removed for export] *)
  Local Ltac xfer_stksh STKSH CF AINV AV SPLO ACV D0 :=
    lazymatch type of CF with cframe _ (owned ?A) (owned ?A') ?xsp ?win ?V ?Nn ?ma ?mb =>
      let X := fresh "STKSHx" in
      assert (X : stack_shadow LPA mb SB N (bv_unsigned sp - 12288) (bv_unsigned sp + 64));
      [ (let SSB := fresh "SSB" in let SSN := fresh "SSN" in let SSC := fresh "SSC" in let SST := fresh "SST" in let CRS := fresh "CRS" in
        (first [ pose proof (STKSH) as dR_1; dand6 dR_1 as SSB SSN _ _ SSC SST | pose proof STKSH as (SSB & SSN & _ & _ & SSC & SST) ]);
        pose proof (crange_stack_shadow (Clg:=Clg) LPA A _ _ SB N _ _ AINV STKSH ltac:(keeplia SPLO ACV)) as CRS;
        eapply stack_shadow_again; [exact STKSH| | reflexivity];
        apply (bytes_at_ccall LPA A A' xsp win V Nn ma mb CF SB);
        [ rewrite zeros_length, Z2Nat.id by exact SSN; exact CRS
        | rewrite zeros_length, Z2Nat.id by exact SSN; split;
          [ (let SHC8 := fresh "SHC8" in unfold kHighMemBeg in SST; pose proof sh_ceiling_ge as SHC8; keeplia SSC SST SHC8 SPLO ACV D0)
          | intros i Hi X; refine (AV _ _ X); keeplia Hi]
        | exact SSB ])
      | clear STKSH; rename X into STKSH ]
    end.
  (* [comment removed for export] *)
  Local Ltac xfer_data DAT CF AINV LD AV Dhi SPLO ACV D0 :=
    lazymatch type of CF with cframe _ (owned ?A) (owned ?A') ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (bytes_at_ccall LPA A A' xsp win V Nn ma mb CF data) in DAT;
      [| exact (crange_block (L:=LPA) A _ _ data _ data (Z.of_nat (length inp)) AINV LD ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))
       | split; [keeplia Dhi SPLO ACV D0| intros i Hi X; refine (AV _ _ X); keeplia Hi] ]
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 K SECC PRIMC BUD INP LEN FR00 STKSH00 ST00 MI00 AINV00 SPHI SPLO SP16 TP T A0 md0 m0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp ra"] Lemma blk_avoids : forall (A : AS) (m : mem) (md : Model) (ff : Z) (age : nat) (p n a : Z),
    ainv A m md -> a_frame A ff = Some (HCLASS, age) -> a_live A p = Some n ->
    a_live A data = Some (Z.of_nat (length inp)) -> p <> data ->
    sh alloc_ceiling <= SB -> SB + N <= kHighMemBeg ->
    newblk p n a ->
    ~ (bv_unsigned sp - LIB_STACK <= a < bv_unsigned sp \/ sh ff <= a < sh ff + 540 \/ ff <= a < ff + 24 \/ ff + 3056 <= a < ff + 3056 + 8
       \/ SB <= a < SB + N \/ data <= a < data + Z.of_nat (length inp)).
  Proof.
    touch_all. intros A m md ff age p n a AIx HF LP LD NE SSC SST X Ha. prelims.
    (first [ pose proof ((fframe_geom LPA A m md ff HCLASS age AIx HF)) as dR_2; dand5 dR_2 as _ _ FLO FHI _ | destruct (fframe_geom LPA A m md ff HCLASS age AIx HF) as (_ & _ & FLO & FHI & _) ]). rewrite fsize7 in FHI.
    (first [ pose proof ((as_frame_ok LPA A m md ff HCLASS age AIx HF)) as dR_3; dand3 dR_3 as _ AL _ | destruct (as_frame_ok LPA A m md ff HCLASS age AIx HF) as (_ & AL & _) ]). rewrite fsize7 in AL. change (Z.min 8192 4096) with 4096 in AL.
    assert (F8 : ff mod 8 = 0) by (clear - AL; Z.div_mod_to_equations; lia).
    (first [ pose proof ((app_lin LPA ff 8192 FLO)) as dR_4; dex2 dR_4 as ix sx; rename dR_4 into FB | pose proof ((app_lin LPA ff 8192 FLO)) as dR_4; dand3 dR_4 as ix sx FB | pose proof (app_lin LPA ff 8192 FLO) as (ix & sx & FB) ]). cbn [cl_image_lo cl_image_hi LPA] in FB. change ((8192 + 7) / 8) with 1024 in FB.
    (first [ pose proof ((live_geomP LPA A m md p n AIx LP)) as dR_5; dand5 dR_5 as Pn P16 Plo Phi _ | pose proof (live_geomP LPA A m md p n AIx LP) as (Pn & P16 & Plo & Phi & _) ]). unfold kHighMemBeg in Plo.
    (first [ pose proof ((app_lin LPA p n (proj1 Plo))) as dR_6; dex2 dR_6 as ixp sxp; rename dR_6 into PB | pose proof ((app_lin LPA p n (proj1 Plo))) as dR_6; dand3 dR_6 as ixp sxp PB | pose proof (app_lin LPA p n (proj1 Plo)) as (ixp & sxp & PB) ]). cbn [cl_image_lo cl_image_hi LPA] in PB.
    (first [ pose proof ((live_geomP LPA A m md data _ AIx LD)) as dR_7; dand5 dR_7 as _ _ Dlo Dhi _ | pose proof (live_geomP LPA A m md data _ AIx LD) as (_ & _ & Dlo & Dhi & _) ]). unfold kHighMemBeg in Dlo.
    (first [ pose proof ((app_lin LPA data _ (proj1 Dlo))) as dR_8; dex2 dR_8 as ixd sxd; rename dR_8 into DB | pose proof ((app_lin LPA data _ (proj1 Dlo))) as dR_8; dand3 dR_8 as ixd sxd DB | pose proof (app_lin LPA data _ (proj1 Dlo)) as (ixd & sxd & DB) ]). cbn [cl_image_lo cl_image_hi LPA] in DB.
    pose proof (as_frame_blk_disjoint LPA A m md ff HCLASS age p n AIx HF LP) as DJ. rewrite fsize7 in DJ.
    pose proof (as_live_disjoint LPA A m md p n data _ AIx LP LD NE) as DD.
    pose proof sh_ceiling_ge as SHC8. unfold kHighMemBeg in SST.
    unfold newblk, blk in X.
    clear - FHI FB F8 Pn P16 Phi PB Dhi DB DJ DD SHC8 SST SSC X Ha SPLO ACV. unfold sh, kShadowOffset in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AI16 INP inp data A0 m0 sp"] Lemma world_bytes_bound : forall H A v VEP vv tag q vr va vi wa n Nn,
    parsed_world H A v VEP vv tag q vr va vi wa n Nn -> 0 <= Nn -> world_bytes vr va vi <= 9 * Nn + 12408.
  Proof.
    intros H A v VEP vv tag q vr va vi wa n Nn PW N0.
    (first [ dand14 PW as _ _ _ _ _ _ _ _ _ VO (R1 & R2) _ HA HI | destruct PW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VO & (R1 & R2) & _ & HA & HI) ]).
    pose proof (proj1 (proj2 VO)) as VI. (first [ dand3 VI as Vsz Vlen _ | destruct VI as (Vsz & Vlen & _) ]).
    unfold world_bytes.
    assert (BA : match va with None => 0 | Some x => 40 + vb_size x end <= 40 + Nn + 4096).
    { destruct va as [x|]; [| lia]. (first [ dand4 HA as XO _ [X1 X2] _ | destruct HA as (XO & _ & [X1 X2] & _) ]). lia. }
    assert (BI : match vi with None => 0 | Some (x, _) => 40 + vb_size x end <= 40 + Nn + 4096).
    { destruct vi as [[x fi]|]; [| lia]. (first [ dand3 HI as XO [X1 X2] _ | destruct HI as (XO & [X1 X2] & _) ]). lia. }
    lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AI16 K SECC PRIMC BUD INP LEN FR00 STKSH00 ST00 MI00 AINV00 SPHI SPLO SP16 TP T N SB inp data A0 md0 m0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp sp ra"] Lemma nb_avoids : forall (A : AS) (m : mem) (md : Model) (ff : Z) (age : nat) (q k a : Z),
    ainv A m md -> a_frame A ff = Some (HCLASS, age) -> a_live A q = Some k ->
    newblk q k a -> ~ (ff <= a < ff + 8192 \/ sh ff <= a < sh ff + 1024 \/ 65536 <= a < 6332416).
  Proof.
    touch_all. intros A m md ff age q k a AIx HF LQ X Ha. prelims.
    (first [ pose proof ((fframe_geom LPA A m md ff HCLASS age AIx HF)) as dR_13; dand5 dR_13 as _ _ FLO FHI _ | destruct (fframe_geom LPA A m md ff HCLASS age AIx HF) as (_ & _ & FLO & FHI & _) ]). rewrite fsize7 in FHI.
    (first [ pose proof ((as_frame_ok LPA A m md ff HCLASS age AIx HF)) as dR_14; dand3 dR_14 as _ AL _ | destruct (as_frame_ok LPA A m md ff HCLASS age AIx HF) as (_ & AL & _) ]). rewrite fsize7 in AL. change (Z.min 8192 4096) with 4096 in AL.
    assert (F8 : ff mod 8 = 0) by (clear - AL; Z.div_mod_to_equations; lia).
    (first [ pose proof ((app_lin LPA ff 8192 FLO)) as dR_15; dex2 dR_15 as ix sx; rename dR_15 into FB | pose proof ((app_lin LPA ff 8192 FLO)) as dR_15; dand3 dR_15 as ix sx FB | pose proof (app_lin LPA ff 8192 FLO) as (ix & sx & FB) ]). cbn [cl_image_lo cl_image_hi LPA] in FB. change ((8192 + 7) / 8) with 1024 in FB.
    (first [ pose proof ((live_geomP LPA A m md q k AIx LQ)) as dR_16; dand5 dR_16 as Qn Q16 Qlo Qhi _ | pose proof (live_geomP LPA A m md q k AIx LQ) as (Qn & Q16 & Qlo & Qhi & _) ]). unfold kHighMemBeg in Qlo.
    (first [ pose proof ((app_lin LPA q k (proj1 Qlo))) as dR_17; dex2 dR_17 as ixq sxq; rename dR_17 into QB | pose proof ((app_lin LPA q k (proj1 Qlo))) as dR_17; dand3 dR_17 as ixq sxq QB | pose proof (app_lin LPA q k (proj1 Qlo)) as (ixq & sxq & QB) ]). cbn [cl_image_lo cl_image_hi LPA] in QB.
    pose proof (as_frame_blk_disjoint LPA A m md ff HCLASS age q k AIx HF LQ) as DJ. rewrite fsize7 in DJ.
    unfold newblk, blk in X.
    clear - FHI FB F8 Qn Q16 Qhi QB DJ X Ha ACV. unfold sh, kShadowOffset in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AI16 K SECC PRIMC BUD INP LEN FR00 STKSH00 ST00 MI00 AINV00 SPHI SPLO SP16 TP T N SB inp data A0 md0 m0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp sp ra"] Lemma blk2_avoids : forall (A : AS) (m : mem) (md : Model) (p n q k a : Z),
    ainv A m md -> a_live A p = Some n -> a_live A q = Some k -> p <> q ->
    newblk q k a -> ~ (p <= a < p + n).
  Proof.
    touch_all. intros A m md p n q k a AIx LP LQ NE X Ha. prelims.
    (first [ pose proof ((live_geomP LPA A m md p n AIx LP)) as dR_18; dand5 dR_18 as Pn P16 Plo Phi _ | pose proof (live_geomP LPA A m md p n AIx LP) as (Pn & P16 & Plo & Phi & _) ]). unfold kHighMemBeg in Plo.
    (first [ pose proof ((app_lin LPA p n (proj1 Plo))) as dR_19; dex2 dR_19 as ixp sxp; rename dR_19 into PB | pose proof ((app_lin LPA p n (proj1 Plo))) as dR_19; dand3 dR_19 as ixp sxp PB | pose proof (app_lin LPA p n (proj1 Plo)) as (ixp & sxp & PB) ]). cbn [cl_image_lo cl_image_hi LPA] in PB.
    (first [ pose proof ((live_geomP LPA A m md q k AIx LQ)) as dR_20; dand5 dR_20 as Qn Q16 Qlo Qhi _ | pose proof (live_geomP LPA A m md q k AIx LQ) as (Qn & Q16 & Qlo & Qhi & _) ]). unfold kHighMemBeg in Qlo.
    (first [ pose proof ((app_lin LPA q k (proj1 Qlo))) as dR_21; dex2 dR_21 as ixq sxq; rename dR_21 into QB | pose proof ((app_lin LPA q k (proj1 Qlo))) as dR_21; dand3 dR_21 as ixq sxq QB | pose proof (app_lin LPA q k (proj1 Qlo)) as (ixq & sxq & QB) ]). cbn [cl_image_lo cl_image_hi LPA] in QB.
    pose proof (as_live_disjoint LPA A m md q k p n AIx LQ LP (not_eq_sym NE)) as DD.
    unfold newblk, blk in X.
    clear - Pn Phi PB Qn Qhi QB DD X Ha ACV. unfold sh, kShadowOffset in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 K SECC PRIMC BUD INP LEN FR00 STKSH00 ST00 MI00 AINV00 SPHI SPLO SP16 TP"] Lemma seg_C : forall (A1 : AS) (mq : mem) (mdq : Model) (ff : Z) (d : Z) (N1 : Z -> Prop) (flags : Z)
      (xt0 xt1 xt2 a5 a6 a7 xt3 xt4 xt5 xt6 : word) (j0 j16 hdr bs jvl : list byte),
    let sp1 := bv_unsigned sp + -192 - d in let SHB := sh ff in let H := HENV ff in let v := aview A1 mq in
    ainv A1 mq mdq -> mem_inv rsegs v -> amd_frame md0 mdq ->
    a_frame A1 ff = Some (HCLASS, 0%nat) -> ff <> 0 -> (forall g, g <> ff -> a_frame A1 g = None) ->
    (forall p, a_live A1 p = a_live A0 p) -> a_livebytes A1 = a_livebytes A0 -> a_nlive A1 = a_nlive A0 ->
    a_tinycred A1 = a_tinycred A0 -> a_seccred A1 = a_seccred A0 -> a_primcred A1 = a_primcred A0 (* [comment removed for export] *) ->
    length inp <> 0%nat -> 0 <= flags < 16 ->
    ws0_obj LPA H v -> henv_ok LPA VIA H A1 v -> bytes_at rsegs v data inp ->
    0 <= d <= 16 -> sp1 mod 16 = 0 ->
    stk rsegs v (bv_unsigned sp - LIB_STACK) sp1 ->
    (* [comment removed for export] *)
    rw_cells rsegs v sp1 [CB 16 j0; C8 (Z_to_bv 64 (SHB + 4)); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 (SHB + 192)); C8 (Z_to_bv 64 (SHB + 394));
                         C8 (Z_to_bv 64 (Z.of_nat (length inp))); C8 (Z_to_bv 64 data);
                         CB 16 j16; C8 (Z_to_bv 64 ff)] ->
    stk rsegs v (sp1 + 88) (bv_unsigned sp + -104) ->
    rw_cells rsegs v (bv_unsigned sp + -104) (SAVE ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells rsegs v SHB [CB 540 bs] ->
    rw_cells rsegs v ff [CB 24 hdr] ->
    rw_cells rsegs v (h_vsbloc H) [CB 8 jvl] ->
    stack_shadow LPA v SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64) ->
    cframe LPA (owned A0) (owned A1) (bv_unsigned sp) LIB_STACK (HV ff) N1 (aview A0 m0) v ->
    (forall a, frm ff HCLASS a -> owned A0 a \/ (aview A0 m0 (Z_to_bv 64 a) = None /\ ~ in_image LPA a)) ->
    srealizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 0x873ac) (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1)
                                    (Z_to_bv 64 (h_vc H)) (Z_to_bv 64 (h_req H)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 flags) a5 a6 a7
                                    (Z_to_bv 64 ff) (Z_to_bv 64 SHB) (Z_to_bv 64 (h_resp H)) (Z_to_bv 64 (h_wrk H)) (Z_to_bv 64 (h_vc H))
                                    (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 flags) (Z_to_bv 64 2147450880) (Z_to_bv 64 (h_ws H)) (Z_to_bv 64 (h_req H))
                                    xt3 xt4 xt5 xt6)
                               F (Z_to_bv 64 VEP_Init_entry) fc None mq (seg_rom rsegs)) mdq) T.
  Proof.
    touch_all. intros until jvl. cbv zeta. intros AINV1 MI1 MDF1 FF1 FFNZ FR1 LIVE1 LB1 NL1 TC1 SC1 PC1 LENp FL WS0 HENV1 DAT D0 AL16 STlo SPILL STpad SAV SHC FFH VSBL STKSH1 CF01 FRM0.
    pose_T. prelims. unfold LIB_STACK in seg_T'.
    pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    (first [ pose proof ((fframe_geom LPA A1 mq mdq ff HCLASS 0%nat AINV1 FF1)) as dR_22; dand5 dR_22 as _ FS FLO FHI _ | destruct (fframe_geom LPA A1 mq mdq ff HCLASS 0%nat AINV1 FF1) as (_ & FS & FLO & FHI & _) ]).
    rewrite fsize7 in FS, FHI. change (Z.min 8192 4096) with 4096 in FS.
    (first [ pose proof ((app_lin LPA ff 8192 FLO)) as dR_23; dex2 dR_23 as ix sx; rename dR_23 into FB | pose proof ((app_lin LPA ff 8192 FLO)) as dR_23; dand3 dR_23 as ix sx FB | pose proof (app_lin LPA ff 8192 FLO) as (ix & sx & FB) ]). cbn [cl_image_lo cl_image_hi LPA] in FB. change ((8192 + 7) / 8) with 1024 in FB.
    (* [comment removed for export] *)
    (first [ pose proof ((INP LENp)) as dR_24; dand3 dR_24 as DNZ LD0 _ | destruct (INP LENp) as (DNZ & LD0 & _) ]).
    assert (LD1 : a_live A1 data = Some (Z.of_nat (length inp))) by (rewrite (LIVE1 data); exact LD0).
    (first [ pose proof ((live_geomP LPA A1 mq mdq data _ AINV1 LD1)) as dR_25; dand6 dR_25 as _ _ Dlo Dhi Dimg _ | pose proof (live_geomP LPA A1 mq mdq data _ AINV1 LD1) as (_ & _ & Dlo & Dhi & Dimg & _) ]). unfold kHighMemBeg in Dlo. all_app_facts.
    assert (N1p : 1 <= Z.of_nat (length inp)) by (clear - LENp; lia). unfold NMAX in LEN.
    (* [comment removed for export] *)
    pose proof BUD as [BL BN]. unfold LIB_LIVE, LIB_NLIVE in BL, BN. unfold LIB_SECC in SECC, SC1.
    assert (DIVF : 0 <= Z.of_nat (length inp) / 682).   (* [comment removed for export] *)
    { pose proof (Nat2Z.is_nonneg (length inp)) as NN. revert NN. generalize (Z.of_nat (length inp)). clear. intros n NN. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    eapply (VEP_Init_closed (HENV ff) flags (bv_unsigned sp - 12288) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mq mdq A1 T);
      [ exact AINV1 | exact MI1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact FL
      | exact WS0 | exact HENV1
      | rewrite LB1; keeplia BL N1p | rewrite NL1; keeplia BN
      | rewrite PC1; unfold LIB_PRIM in PRIMC; keeplia PRIMC (* [comment removed for export] *)
      | exact TP
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact AL16
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact STlo
      | keeplia SPLO ACV
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); unfold_stacks; keeplia SPLO D0 ACV | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A2 m2 md2. cbv zeta.
    intros AINV2 MI2 MDF2 ST2 HENV2 FRS2 TC2 SC2 PC2 OUT.   (* [comment removed for export] *)
    rewrite unsigned_lit in ST2, OUT by (keeplia SPR D0 SPLO ACV). unfold VEPINIT_STACK, PRINTF_STACK, VPRINTF_STACK, EXT_STACK, ASTK in OUT.
    replace (ret_pc (Z_to_bv 64 0x873ac)) with (Z_to_bv 64 0x873ac) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (as_minv LPA A2 _ _ AINV2) as [_ MH2].
    assert (FF2 : a_frame A2 ff = Some (HCLASS, 0%nat)) by (rewrite (FRS2 ff); exact FF1).
    assert (FR2 : forall g, g <> ff -> a_frame A2 g = None) by (intros g NE; rewrite (FRS2 g); exact (FR1 g NE)).
    (* [comment removed for export] *)
    set (PIECES := fun a => bv_unsigned sp - 12288 <= a < bv_unsigned sp \/ sh ff <= a < sh ff + 540 \/ ff <= a < ff + 24 \/ ff + 3056 <= a < ff + 3056 + 8
                            \/ SB <= a < SB + N \/ data <= a < data + Z.of_nat (length inp)).
    (first [ pose proof (STKSH1) as dR_26; dand6 dR_26 as _ SSN0 SSL0 SSH0 SSC0 SST0 | pose proof STKSH1 as (_ & SSN0 & SSL0 & SSH0 & SSC0 & SST0) ]). unfold kHighMemBeg in SST0. pose proof sh_ceiling_ge as SHC8.
    pose proof (as_frame_blk_disjoint LPA A1 mq mdq ff HCLASS 0%nat data _ AINV1 FF1 LD1) as DJD. rewrite fsize7 in DJD.
    (* [comment removed for export] *)
    rename OUT into OKC.
    - (* [comment removed for export] *)
      (first [ dex4 OKC as wa tag q b; dand18 OKC as RNZ WS1' S VEPO SNZ VSO LS1 LBb1 NSr NBr NSw NBw LWA1 LR1 LV2 LB2 NL2 CF2 | dand22 OKC as wa tag q b RNZ WS1' S VEPO SNZ VSO LS1 LBb1 NSr NBr NSw NBw LWA1 LR1 LV2 LB2 NL2 CF2 | destruct OKC as (wa & tag & q & b & RNZ & WS1' & S & VEPO & SNZ & VSO & LS1 & LBb1 & NSr & NBr & NSw & NBw & LWA1 & LR1 & LV2 & LB2 & NL2 & CF2) ]).
      lazymatch type of CF2 with cframe _ _ _ _ _ ?V _ _ _ =>
        assert (AV : forall a, PIECES a -> ~ V a)
          by (intros a Ha X; subst PIECES; cbv beta in Ha; unfold h_ws, h_wsbuf, h_vsbloc in *; cbn [h_ff] in *; keeplia Ha X FB SPLO ACV SSC0 SST0 SHC8 Dlo Dhi DJD) end.
      subst PIECES. cbv beta in AV.
      xfer_stack SPILL CF2 AINV1 AV (bv_unsigned sp + -192 - d) 88 SPLO ACV D0 SPR.
      xfer_stack SAV CF2 AINV1 AV (bv_unsigned sp + -104) 104 SPLO ACV D0 SPR.
      xfer_frame SHC CF2 AINV1 FF1 AV (sh ff) crange_fshadow FB SPLO ACV D0.
      xfer_frame FFH CF2 AINV1 FF1 AV ff crange_fframe FB SPLO ACV D0.
      unfold h_vsbloc in VSBL. cbn [h_ff] in VSBL.
      xfer_frame VSBL CF2 AINV1 FF1 AV (ff + 3056) crange_fframe FB SPLO ACV D0.
      lazymatch type of CF2 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
        apply (stk_ccall_any A1 A2 _ _ ma mb xsp win V Nn _ _ AINV1 CF2) in STpad; [| keeplia SPLO ACV D0 | intros a Ha X; refine (AV _ _ X); keeplia Ha D0] end.
      xfer_stksh STKSH1 CF2 AINV1 AV SPLO ACV D0.
      xfer_data DAT CF2 AINV1 LD1 AV Dhi SPLO ACV D0.
      assert (MP2 : mapped (aview A2 m2) (bv_unsigned sp - 12288) 12288).
      { pose proof (stk_release rsegs _ _ _ _ ST2 SPILL ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
        pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
        pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3. unfold SAVE in Y3. cbn [cells_size csize Nat.add] in Y3.
        eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
      lazymatch type of CF2 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
        pose proof (cframe_reframe LPA (owned A1) (owned A2) xsp win (bv_unsigned sp) 12288 V Nn ma mb CF2 ltac:(keeplia D0) ltac:(keeplia D0 SPR) MP2) as CF2';
        assert (V2N : forall a, V a -> N1 a \/ HV ff a)
          by (intros a X; right; right; left; unfold h_ws, h_wsbuf in X; cbn [h_ff] in X; rewrite fsize7; keeplia X);
        pose proof (cframe_seq LPA (owned A0) (owned A1) (owned A2) (bv_unsigned sp) 12288 12288 12288 (HV ff) N1 V Nn (HV ff) (fun a => N1 a \/ Nn a)
                    (aview A0 m0) ma mb CF01 CF2' ltac:(clear; lia) ltac:(clear; lia) MP2 ltac:(intros a X; exact X) V2N
                    ltac:(intros a [X|X]; [left; exact X| right; left; exact X])) as CF02;
        clear V2N CF2' CF2
      end.
      (* [comment removed for export] *)
      (first [ pose proof (VEPO) as dR_32; dand4 dR_32 as LVEP VEPC TAG8 PADS | pose proof VEPO as (LVEP & VEPC & TAG8 & PADS) ]).
      (first [ pose proof ((live_geomP LPA A2 m2 md2 r 312 AINV2 LVEP)) as dR_33; dand5 dR_33 as _ _ Rlo Rhi _ | pose proof (live_geomP LPA A2 m2 md2 r 312 AINV2 LVEP) as (_ & _ & Rlo & Rhi & _) ]). unfold kHighMemBeg in Rlo. all_app_facts.
      assert (LD2 : a_live A2 data = Some (Z.of_nat (length inp))).
      { rewrite (LV2 data); [exact LD1| | | |]; intros E; rewrite <- E in *;
          first [rewrite LD1 in LWA1; discriminate LWA1 | rewrite LD1 in LR1; discriminate LR1 | rewrite LD1 in LS1; discriminate LS1 | rewrite LD1 in LBb1; discriminate LBb1]. }
      (* [comment removed for export] *)
      ago AINV2. fold_cl_segs.
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (keeplia Rlo Rhi ACV); exact (RNZ KZ)|]. clear KZ.
      zstep. zstep. zstep. zstep. zstep.
      astop0 AINV2.
      lazymatch goal with AIq : ainv A2 ?mx ?mdx, SBq : same_but_materialized md2 ?mdx |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
        rename AIq into AINVb; rename SBq into SBMb; rename mx into m2b; rename mdx into md2b end.
      lazymatch goal with MIq : mem_inv _ (aview A2 m2b) |- _ => rename MIq into MIb end.
      assert (LF2 : lib_frames A2) by (intros g k age HG; destruct (Z.eq_dec g ff) as [->|NE]; [rewrite FF2 in HG; injection HG as <- _; unfold HCLASS; clear; lia| rewrite (FR2 g NE) in HG; discriminate HG]).
      assert (STKSHp : stack_shadow LPA (aview A2 m2b) SB N (bv_unsigned sp + -192 - d - PARSE_STACK - 64) (bv_unsigned sp + -192 - d + 64))
        by (eapply (stack_shadow_sub LPA); [exact STKSH1| unfold_stacks; keeplia D0| keeplia D0| keeplia SPLO ACV]).
      eapply (VEP_Parse_closed (HENV ff) r S b flags wa data inp tag q (bv_unsigned sp - 12288) SB N
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2b md2b A2 T);
        [ exact AINVb | exact MIb | reflexivity | reflexivity | reflexivity | exact FL
        | exact VEPO | exact SNZ | exact VSO | exact WS1'
        | split; [exact LD2| split; [exact DAT| split; [exact N1p| exact LEN]]]
        | exact HENV2
        | exact (not_eq_sym NSr) | exact (not_eq_sym NBr) | exact (not_eq_sym NSw) | exact (not_eq_sym NBw)
        | intros E; rewrite E in LD1; rewrite LD1 in LR1; discriminate LR1
        | intros E; rewrite E in LD1; rewrite LD1 in LS1; discriminate LS1
        | intros E; rewrite E in LD1; rewrite LD1 in LBb1; discriminate LBb1
        | intros E; rewrite E in LD1; rewrite LD1 in LWA1; discriminate LWA1
        | rewrite LB2, LB1; unfold PARSE_LIVE; keeplia BL N1p | rewrite NL2, NL1; unfold PARSE_NLIVE; keeplia BN
        | rewrite SC2, SC1; unfold PARSE_CRED; keeplia SECC DIVF
        | rewrite PC2, PC1; unfold LIB_PRIM, PARSE_PRIM, PRIM_ROOM, PPOT_CAP, PVB_MAX in *; keeplia PRIMC (* [comment removed for export] *)
        | exact LF2 | exact TP
        | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact AL16
        | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); keeplia SPHI D0
        | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact ST2
        | keeplia SPLO ACV
        | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); unfold_stacks; keeplia SPLO D0 ACV
        | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact STKSHp | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A3 m3 md3 vv3 tag3 q3 vr3 va vi nmk. cbv zeta.
      intros AINV3 MI3 MDF3 ST3 HENV3 PW EVS VERP WS13 DAT3 LKEEP3 PNEW FRS3 LB3 TC3 NL3 SC3 PC3 CF3.
      rewrite unsigned_lit in ST3, CF3 by (keeplia SPR D0 SPLO ACV). unfold PARSE_STACK, DOINCL_STACK, MARK_STACK, EMITC_STACK, EMITLEN_STACK, BCAT_STACK, PRINTF_STACK, VPRINTF_STACK, EXT_STACK, ASTK in CF3. match type of CF3 with context [Z.max ?a ?b] => let v := eval vm_compute in (Z.max a b) in change (Z.max a b) with v in CF3 end.
      replace (ret_pc (Z_to_bv 64 0x873c4)) with (Z_to_bv 64 0x873c4) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (as_minv LPA A3 _ _ AINV3) as [_ MH3].
      assert (FF3 : a_frame A3 ff = Some (HCLASS, 0%nat)) by (rewrite (FRS3 ff); exact FF2).
      assert (FR3 : forall g, g <> ff -> a_frame A3 g = None) by (intros g NE; rewrite (FRS3 g); exact (FR2 g NE)).
      assert (LD3 : a_live A3 data = Some (Z.of_nat (length inp))) by (apply LKEEP3; [exact LD2| intros E; rewrite E in LD1; rewrite LD1 in LBb1; discriminate LBb1]).
      (* [comment removed for export] *)
      lazymatch type of CF3 with cframe _ _ _ _ _ ?V _ _ _ =>
        assert (AV3 : forall a, (bv_unsigned sp - 12288 <= a < bv_unsigned sp \/ sh ff <= a < sh ff + 540 \/ ff <= a < ff + 24 \/ ff + 3056 <= a < ff + 3056 + 8
                                 \/ SB <= a < SB + N \/ data <= a < data + Z.of_nat (length inp)) -> ~ V a) end.
      { intros a Ha X. unfold parse_changed in X. destruct X as [X|[X|[X|X]]].
        - refine (blk_avoids A2 m2b md2b ff 0%nat r 312 a AINVb FF2 LVEP LD2 _ SSC0 SST0 (or_introl X) Ha).
          intros E; rewrite E in LR1; rewrite LD1 in LR1; discriminate LR1.
        - refine (blk_avoids A2 m2b md2b ff 0%nat S 40 a AINVb FF2 (proj1 (proj2 (proj2 VSO))) LD2 _ SSC0 SST0 (or_introl X) Ha).
          intros E; rewrite E in LS1; rewrite LD1 in LS1; discriminate LS1.
        - refine (blk_avoids A2 m2b md2b ff 0%nat b 16 a AINVb FF2 (proj1 (proj2 (proj2 (proj2 VSO)))) LD2 _ SSC0 SST0 X Ha).
          intros E; rewrite E in LBb1; rewrite LD1 in LBb1; discriminate LBb1.
        - unfold h_vsc in X. cbn [h_ff] in X. keeplia Ha X FB SPLO ACV SSC0 SST0 SHC8 Dlo Dhi DJD. }
      xfer_stack SPILL CF3 AINVb AV3 (bv_unsigned sp + -192 - d) 88 SPLO ACV D0 SPR.
      xfer_stack SAV CF3 AINVb AV3 (bv_unsigned sp + -104) 104 SPLO ACV D0 SPR.
      xfer_frame SHC CF3 AINVb FF2 AV3 (sh ff) crange_fshadow FB SPLO ACV D0.
      xfer_frame FFH CF3 AINVb FF2 AV3 ff crange_fframe FB SPLO ACV D0.
      xfer_frame VSBL CF3 AINVb FF2 AV3 (ff + 3056) crange_fframe FB SPLO ACV D0.
      lazymatch type of CF3 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
        apply (stk_ccall_any A2 A3 _ _ ma mb xsp win V Nn _ _ AINVb CF3) in STpad; [| keeplia SPLO ACV D0 | intros a Ha X; refine (AV3 _ _ X); keeplia Ha D0] end.
      xfer_stksh STKSH1 CF3 AINVb AV3 SPLO ACV D0.
      clear DAT STKSHp.
      assert (MP3 : mapped (aview A3 m3) (bv_unsigned sp - 12288) 12288).
      { pose proof (stk_release rsegs _ _ _ _ ST3 SPILL ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
        pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
        pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3. unfold SAVE in Y3. cbn [cells_size csize Nat.add] in Y3.
        eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
      lazymatch type of CF3 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
        lazymatch type of CF02 with cframe _ _ _ _ _ _ ?N2 _ _ =>
        pose proof (cframe_reframe LPA (owned A2) (owned A3) xsp win (bv_unsigned sp) 12288 V Nn ma mb CF3 ltac:(keeplia D0) ltac:(keeplia D0 SPR) MP3) as CF3';
        assert (V3N : forall a, V a -> N2 a \/ HV ff a)
          by (intros a X; unfold parse_changed in X; destruct X as [X|[X|[X|X]]];
              [ left; right; right; left; left; exact X
              | left; right; right; right; left; left; exact X
              | left; right; right; right; right; exact X
              | right; right; left; unfold h_vsc in X; cbn [h_ff] in X; rewrite fsize7; keeplia X ]);
        pose proof (cframe_seq LPA (owned A0) (owned A2) (owned A3) (bv_unsigned sp) 12288 12288 12288 (HV ff) N2 V Nn (HV ff) (fun a => N2 a \/ Nn a)
                    (aview A0 m0) (aview A2 m2b) mb CF02 CF3' ltac:(clear; lia) ltac:(clear; lia) MP3 ltac:(intros a X; exact X) V3N
                    ltac:(intros a [X|X]; [left; exact X| right; left; exact X])) as CF03;
        clear V3N CF3' CF3 CF02
      end end.
      (* [comment removed for export] *)
      ago AINV3. fold_cl_segs.
      zstep. zstep.
      astop0 AINV3.
      lazymatch goal with AIq : ainv A3 ?mx ?mdx, SBq : same_but_materialized md3 ?mdx |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
        rename AIq into AINVc; rename SBq into SBMc; rename mx into m3b; rename mdx into md3b end.
      lazymatch goal with MIq : mem_inv _ (aview A3 m3b) |- _ => rename MIq into MIc end.
      assert (LF3 : lib_frames A3) by (intros g k age HG; destruct (Z.eq_dec g ff) as [->|NE]; [rewrite FF3 in HG; injection HG as <- _; unfold HCLASS; clear; lia| rewrite (FR3 g NE) in HG; discriminate HG]).
      pose proof (world_bytes_bound _ _ _ _ _ _ _ _ _ _ _ _ _ PW ltac:(clear; lia)) as WBB.
      pose proof (world_nlive_nonneg va vi) as WNL.
      eapply (VEP_Finish_closed (HENV ff) r wa nmk (Z.of_nat (length inp)) data vv3 tag3 q3 vr3 va vi (bv_unsigned sp - 12288)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3b md3b A3 T);
        [ exact AINVc | exact MIc | reflexivity | exact PW | exact WS13 | exact HENV3
        | exact LD3 | keeplia N1p | exact VERP
        | intros E; rewrite E in LD1; rewrite LD1 in LR1; discriminate LR1
        | rewrite EVS; intros E; rewrite E in LD1; rewrite LD1 in LS1; discriminate LS1
        | intros X; destruct (PNEW data X) as [E|E]; [rewrite E in LD1; rewrite LD1 in LBb1; discriminate LBb1| rewrite LD2 in E; discriminate E]
        | rewrite LB3, LB2, LB1; unfold FIN_LIVE; keeplia BL N1p WBB
        | rewrite NL3, NL2, NL1; keeplia BN WNL
        | unfold FIN_CRED; unfold PARSE_CRED in SC3; rewrite SC2, SC1 in SC3; keeplia SECC DIVF SC3
        | rewrite PC2, PC1 in PC3; unfold LIB_PRIM, PARSE_PRIM, PRIM_ROOM, PPOT_CAP, PVB_MAX in *; keeplia PRIMC PC3 (* [comment removed for export] *)
        | apply lib_frames_young; exact LF3
        | exact TP
        | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact AL16
        | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact ST3
        | keeplia SPLO ACV
        | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); unfold_stacks; keeplia SPLO D0 ACV | ].
      intros t0''' t1''' t2''' a1''' a2''' a3''' a4''' a5''' a6''' a7''' t3''' t4''' t5''' t6''' r4 A4 m4 md4 vv4 vr4. cbv zeta.
      intros AINV4 MI4 MDF4 ST4 HENV4 VEPO4 WS14 ROUT LKEEP4 FA4 LB4 TC4 NL4 SC4 PC4 CF4.
      rewrite unsigned_lit in ST4, CF4 by (keeplia SPR D0 SPLO ACV).
      unfold VEPFIN_STACK, MARK_STACK, EMITC_STACK, EMITLEN_STACK, BCAT_STACK, EXT_STACK, ASTK in CF4.
      replace (ret_pc (Z_to_bv 64 0x873cc)) with (Z_to_bv 64 0x873cc) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (as_minv LPA A4 _ _ AINV4) as [_ MH4].
      destruct FA4 as [AG4 NN4]. (first [ pose proof ((AG4 ff HCLASS 0%nat FF3)) as dR_34; dex1 dR_34 as dd; destruct dR_34 as [FF4 Hdd] | pose proof ((AG4 ff HCLASS 0%nat FF3)) as dR_34; dand3 dR_34 as dd FF4 Hdd | destruct (AG4 ff HCLASS 0%nat FF3) as (dd & FF4 & Hdd) ]). unfold fbound, HCLASS in Hdd. cbn in Hdd.
      replace (0 + dd)%nat with 0%nat in FF4 by (clear - Hdd; lia).
      assert (FR4 : forall g, g <> ff -> a_frame A4 g = None) by (intros g NE; exact (NN4 g (FR3 g NE))).
      (* [comment removed for export] *)
      (first [ pose proof (PW) as dR_35; dand14 dR_35 as VEPO3 _ _ _ _ _ _ _ _ VSO3 _ _ HVA HVI | pose proof PW as (VEPO3 & _ & _ & _ & _ & _ & _ & _ & _ & VSO3 & _ & _ & HVA & HVI) ]).
      pose proof (proj1 (proj2 (proj2 VSO3))) as LS3. pose proof (proj1 (proj2 (proj2 (proj2 VSO3)))) as LBF3. rewrite EVS in LS3.
      assert (NDS : S <> data) by (intros E; rewrite E in LS1; rewrite LD1 in LS1; discriminate LS1).
      assert (NDR : r <> data) by (intros E; rewrite E in LR1; rewrite LD1 in LR1; discriminate LR1).
      assert (NDP : forall x, parse_blocks vv3 vr3 va vi x -> x <> data).
      { intros x PX E. subst x. destruct (PNEW data PX) as [E|E]; [rewrite E in LD1; rewrite LD1 in LBb1; discriminate LBb1| rewrite LD2 in E; discriminate E]. }
      assert (LD4 : a_live A4 data = Some (Z.of_nat (length inp))) by (apply LKEEP4; [exact LD3| rewrite EVS; exact (not_eq_sym NDS)| intros X; exact (NDP data X eq_refl)]).
      assert (FCB : forall a, finish_changed (HENV ff) r vv3 vr3 va vi a ->
                (h_vsc (HENV ff) + 1304 <= a < h_vsc (HENV ff) + 1320) \/ exists p n, a_live A3 p = Some n /\ p <> data /\ newblk p n a).
      { intros a X. unfold finish_changed, vsb_blocks in X. destruct X as [X|[[X|X]|[X|[X|X]]]].
        - right. exists r, 312. split; [exact (proj1 VEPO3)| split; [exact NDR| left; exact X]].
        - right. exists S, 40. split; [exact LS3| split; [exact NDS| rewrite EVS in X; exact X]].
        - right. exists (vb_buf vr3), (vb_size vr3). split; [exact LBF3| split; [apply NDP; left; reflexivity| exact X]].
        - destruct va as [x|]; [| destruct X]. destruct HVA as (XO & _). right.
          destruct X as [X|X].
          + exists (vv3 Fattr_vsb), 40. split; [exact (proj1 (proj2 (proj2 XO)))| split; [apply NDP; right; left; left; reflexivity| exact X]].
          + exists (vb_buf x), (vb_size x). split; [exact (proj1 (proj2 (proj2 (proj2 XO))))| split; [apply NDP; right; left; right; reflexivity| exact X]].
        - destruct vi as [[x fi]|]; [| destruct X]. destruct HVI as (XO & _). right.
          destruct X as [X|X].
          + exists (vv3 Finclude_src), 40. split; [exact (proj1 (proj2 (proj2 XO)))| split; [apply NDP; right; right; left; reflexivity| exact X]].
          + exists (vb_buf x), (vb_size x). split; [exact (proj1 (proj2 (proj2 (proj2 XO))))| split; [apply NDP; right; right; right; reflexivity| exact X]].
        - left. exact X. }
      lazymatch type of CF4 with cframe _ _ _ _ _ ?V _ _ _ =>
        assert (AV4 : forall a, (bv_unsigned sp - 12288 <= a < bv_unsigned sp \/ sh ff <= a < sh ff + 540 \/ ff <= a < ff + 24 \/ ff + 3056 <= a < ff + 3056 + 8
                                 \/ SB <= a < SB + N \/ data <= a < data + Z.of_nat (length inp)) -> ~ V a) end.
      { intros a Ha X. destruct (FCB a X) as [Y|(p & n & LP & NE & Y)].
        - unfold h_vsc in Y. cbn [h_ff] in Y. keeplia Ha Y FB SPLO ACV SSC0 SST0 SHC8 Dlo Dhi DJD.
        - exact (blk_avoids A3 m3b md3b ff 0%nat p n a AINVc FF3 LP LD3 NE SSC0 SST0 Y Ha). }
      clear FCB.
      xfer_stack SPILL CF4 AINVc AV4 (bv_unsigned sp + -192 - d) 88 SPLO ACV D0 SPR.
      xfer_stack SAV CF4 AINVc AV4 (bv_unsigned sp + -104) 104 SPLO ACV D0 SPR.
      xfer_frame SHC CF4 AINVc FF3 AV4 (sh ff) crange_fshadow FB SPLO ACV D0.
      xfer_frame FFH CF4 AINVc FF3 AV4 ff crange_fframe FB SPLO ACV D0.
      xfer_frame VSBL CF4 AINVc FF3 AV4 (ff + 3056) crange_fframe FB SPLO ACV D0.
      lazymatch type of CF4 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
        apply (stk_ccall_any A3 A4 _ _ ma mb xsp win V Nn _ _ AINVc CF4) in STpad; [| keeplia SPLO ACV D0 | intros a Ha X; refine (AV4 _ _ X); keeplia Ha D0] end.
      xfer_stksh STKSH1 CF4 AINVc AV4 SPLO ACV D0.
      clear DAT3.
      assert (MP4 : mapped (aview A4 m4) (bv_unsigned sp - 12288) 12288).
      { pose proof (stk_release rsegs _ _ _ _ ST4 SPILL ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
        pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
        pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3. unfold SAVE in Y3. cbn [cells_size csize Nat.add] in Y3.
        eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
      lazymatch type of CF4 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
        lazymatch type of CF03 with cframe _ _ _ _ _ _ ?N3 _ _ =>
        pose proof (cframe_reframe LPA (owned A3) (owned A4) xsp win (bv_unsigned sp) 12288 V Nn ma mb CF4 ltac:(keeplia D0) ltac:(keeplia D0 SPR) MP4) as CF4';
        assert (V4N : forall a, V a -> N3 a \/ HV ff a)
          by (intros a X; unfold finish_changed, vsb_blocks in X; destruct X as [X|[[X|X]|[X|[X|X]]]];
              [ left; left; right; right; left; left; exact X
              | left; left; right; right; right; left; rewrite <- EVS; exact X
              | left; right; left; exact X
              | left; right; right; left; destruct va as [x|]; [unfold vsb_blocks; exact X| destruct X]
              | left; right; right; right; destruct vi as [[x fi]|]; [unfold vsb_blocks; exact X| destruct X]
              | right; right; left; unfold h_vsc in X; cbn [h_ff] in X; rewrite fsize7; keeplia X ]);
        pose proof (cframe_seq LPA (owned A0) (owned A3) (owned A4) (bv_unsigned sp) 12288 12288 12288 (HV ff) N3 V Nn (HV ff) (fun a => N3 a \/ Nn a)
                    (aview A0 m0) (aview A3 m3b) mb CF03 CF4' ltac:(clear; lia) ltac:(clear; lia) MP4 ltac:(intros a X; exact X) V4N
                    ltac:(intros a [X|X]; [left; exact X| right; left; exact X])) as CF04;
        clear V4N CF4' CF4 CF03
      end end.
      (* [comment removed for export] *)
      assert (LIVEc4 : forall p n, a_live A0 p = Some n -> a_live A4 p = Some n).
      { intros p n Hp. assert (H1 : a_live A1 p = Some n) by (rewrite LIVE1; exact Hp).
        assert (H2 : a_live A2 p = Some n).
        { rewrite (LV2 p); [exact H1| | | |]; intros ->; [rewrite LWA1 in H1| rewrite LR1 in H1| rewrite LS1 in H1| rewrite LBb1 in H1]; discriminate H1. }
        assert (H3 : a_live A3 p = Some n) by (apply LKEEP3; [exact H2| intros ->; rewrite LBb1 in H1; discriminate H1]).
        apply LKEEP4; [exact H3| rewrite EVS; intros ->; rewrite LS1 in H1; discriminate H1
          | intros X; destruct (PNEW p X) as [->|E]; [rewrite LBb1 in H1; discriminate H1| rewrite H2 in E; discriminate E]]. }
      (first [ dand4 HENV4 as HF4 GLOB4 HOBJ4 HSH4 | destruct HENV4 as (HF4 & GLOB4 & HOBJ4 & HSH4) ]).
      (* [comment removed for export] *)
      pose proof (munch_refl [(ff + 3056, ff + 3056 + 8)] (aview A4 m4)) as MU4. pose proof (wmono_refl rsegs (aview A4 m4)) as WM4.
      assert (CFP4 : client_fp LPA A4 (aview A4 m4) [(ff + 3056, ff + 3056 + 8)]).
      { cbn. split; [| exact I]. right; right; left. exists ff, HCLASS, 0%nat. split; [exact FF4| rewrite fsize7; clear; lia]. }
      ago AINV4. fold_cl_segs.
      replace (h_req (HENV ff) + 640) with (ff + 3056) by (unfold h_req; cbn [h_ff]; clear; lia).
      zstep. zstep.
      destruct ROUT as [R40 | (R4NZ & ER4 & VSO4 & APART4 & BUF4)].
      + (* [comment removed for export] *)
        subst r4. zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity]. clear KZ.
        astop AINV4 MU4 WM4 CFP4.
        lazymatch goal with AIq : ainv A4 ?mx ?mdx, SBq : same_but_materialized md4 ?mdx |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
          rename AIq into AINVd; rename SBq into SBMd; rename mx into m4b; rename mdx into md4b end.
        lazymatch goal with MIq : mem_inv _ (aview A4 m4b) |- _ => rename MIq into MId end.
        (* [comment removed for export] *)
        assert (WS1d : ws1_obj LPA (HENV ff) A4 (aview A4 m4b) wa r)
          by (eapply (ws1_obj_munch LPA); [exact WS14| exact MU4| exact WM4| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [h_ff outside] in *;
              (first [ pose proof (WS14) as dR_37; dand8 dR_37 as _ _ _ _ _ _ LWA4 _ | pose proof WS14 as (_ & _ & _ & _ & _ & _ & LWA4 & _) ]);
              pose proof (as_frame_blk_disjoint LPA A4 m4 md4 ff HCLASS 0%nat wa 40 AINV4 FF4 LWA4) as DJW; rewrite fsize7 in DJW; keeplia Ha DJW]).
        assert (GLOBd : glob_ok LPA VIA (HENV ff) (aview A4 m4b))
          by (eapply (glob_ok_munch LPA); [exact GLOB4| exact MU4| exact WM4| intros a Ha; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha; unfold h_cp, h_vsc in Ha; cbn [h_ff outside] in *; keeplia Ha FB]).
        assert (HSHd : hshadow LPA (HENV ff) (aview A4 m4b))
          by (eapply (hshadow_munch LPA); [exact HSH4| exact MU4| eapply henv_geom_of_frame; [exact AINV4| exact HF4]| intros x Hx; cbn [h_ff outside] in *; unfold HFSIZE in Hx; change (8192 / 8) with 1024 in Hx; keeplia Hx FB]).
        (first [ pose proof (STKSH1) as dR_38; dand3 dR_38 as SSB4 SSN4 _ | pose proof STKSH1 as (SSB4 & SSN4 & _) ]).
        assert (SSBd : bytes_at rsegs (aview A4 m4b) SB (repeat (Z_to_bv 8 0) (Z.to_nat N)))
          by (eapply (bytes_at_munch LPA); [exact SSB4| exact MU4| rewrite repeat_length, Z2Nat.id by exact SSN4; intros a Ha; cbn [outside]; keeplia Ha FB SSC0 SST0 SHC8]).
        pose proof (stack_shadow_again _ _ SB N _ _ _ STKSH1 SSBd eq_refl) as STKSHd. clear SSBd SSB4.
        assert (MP4b : mapped (aview A4 m4b) (bv_unsigned sp - 12288) 12288).
        { pose proof (stk_release rsegs _ _ _ _ ST4 SPILL ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
          pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
          pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3. unfold SAVE in Y3. cbn [cells_size csize Nat.add] in Y3.
          eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
        lazymatch type of CF04 with cframe _ _ _ _ _ _ ?N4 _ _ =>
          pose proof (cframe_noalloc LPA (owned A4) (bv_unsigned sp) 12288 (HV ff) nowhere (aview A4 m4) (aview A4 m4b) _ MU4
                        ltac:(intros a Ha NO; cbn [outside] in NO; right; right; left; rewrite fsize7; keeplia Ha NO) MP4b ltac:(intros a X; destruct X)) as CFst;
          pose proof (cframe_seq LPA (owned A0) (owned A4) (owned A4) (bv_unsigned sp) 12288 12288 12288 (HV ff) N4 (HV ff) nowhere (HV ff) N4
                        (aview A0 m0) (aview A4 m4) (aview A4 m4b) CF04 CFst ltac:(clear; lia) ltac:(clear; lia) MP4b ltac:(intros a X; exact X)
                        ltac:(intros a X; right; exact X) ltac:(intros a X; left; exact X)) as CF04b;
          clear CFst CF04
        end.
        ago AINVd. fold_cl_segs.
        lazymatch type of SPILL with rw_cells _ ?mx ?Ax [?c0;?c1;?c2;?c3;?c4;?c5;?c6;?c7;?c8] =>
          pose proof (rw_cells_merge rsegs mx Ax [c0;c1] [c2] [c3;c4;c5;c6;c7;c8] SPILL) as SPa;
          pose proof (rw_cells_merge rsegs mx Ax [c0; c1; CB (cells_size [c2]) (cells_bytes [c2]); c3; c4] [c5;c6;c7;c8] [] SPa) as SPb;
          clear SPa SPILL; cbn [cells_size csize Nat.add cells_bytes cbytes app] in SPb end.
        lazymatch type of CF04b with cframe _ _ _ _ _ _ ?NK _ _ =>
        eapply (seg_T' A4 m4b md4b (Some (wa, r)) ff 0%nat d NK) end;
          [ exact AINVd | exact MId
          | eapply amd_frame_trans; [exact MDF1|]; eapply amd_frame_trans; [exact MDF2|]; eapply amd_frame_trans; [apply amd_frame_sbm; [exact SBMb| exact MH2]|];
            eapply amd_frame_trans; [exact MDF3|]; eapply amd_frame_trans; [apply amd_frame_sbm; [exact SBMc| exact MH3]|];
            eapply amd_frame_trans; [exact MDF4| apply amd_frame_sbm; [exact SBMd| exact MH4]]
          | exact FF4 | exact FFNZ | exact FR4
          | split; [exact WS1d|]; split; [rewrite <- (LIVE1 wa); exact LWA1|]; split; [rewrite <- (LIVE1 r); exact LR1|];
            split; [exact LIVEc4|]; split; [rewrite LB4, LB3, LB2, LB1; cbn [Z.eqb]; clear; lia|]; split; [rewrite NL4, NL3, NL2, NL1; cbn [Z.eqb]; clear - WNL; lia|];
            intros a X; cbv beta; left; left; right; destruct X as [X|X]; [left; exact X| right; left; exact X]
          | exact GLOBd | exact HSHd | rewrite TC4, TC3, TC2; exact TC1
          | unfold LIB_SECC; unfold FIN_CRED in SC4; unfold PARSE_CRED in SC3; rewrite SC2, SC1 in SC3; keeplia SECC DIVF SC3 SC4
          | rewrite PC2, PC1 in PC3; unfold LIB_PRIM, PARSE_PRIM, PRIM_ROOM, PPOT_CAP, PVB_MAX in *; keeplia PRIMC PC3 PC4 (* [comment removed for export] *)
          | exact D0 | exact AL16 | exact ST4 | exact SPb | exact STpad | exact SAV | exact SHC | exact FFH | exact STKSHd | exact CF04b | exact FRM0 ].
      + (* [comment removed for export] *)
        assert (ER4S : r4 = S) by (rewrite ER4, EVS; reflexivity).
        pose proof VSO4 as VSO4'. rewrite ER4S in VSO4'.
        pose proof (proj1 (proj2 (proj2 VSO4'))) as LS4. pose proof (proj1 (proj2 (proj2 (proj2 VSO4')))) as LBF4.
        (first [ pose proof ((live_geomP LPA A4 m4 md4 S 40 AINV4 LS4)) as dR_39; dand5 dR_39 as _ _ S4lo S4hi _ | pose proof (live_geomP LPA A4 m4 md4 S 40 AINV4 LS4) as (_ & _ & S4lo & S4hi & _) ]). unfold kHighMemBeg in S4lo. all_app_facts.
        (first [ pose proof ((live_geomP LPA A4 m4 md4 (vb_buf vr4) _ AINV4 LBF4)) as dR_40; dand5 dR_40 as _ _ B4lo B4hi _ | pose proof (live_geomP LPA A4 m4 md4 (vb_buf vr4) _ AINV4 LBF4) as (_ & _ & B4lo & B4hi & _) ]). unfold kHighMemBeg in B4lo. all_app_facts.
        pose proof (as_frame_blk_disjoint LPA A4 m4 md4 ff HCLASS 0%nat S 40 AINV4 FF4 LS4) as DJS4. rewrite fsize7 in DJS4.
        pose proof (as_frame_blk_disjoint LPA A4 m4 md4 ff HCLASS 0%nat (vb_buf vr4) _ AINV4 FF4 LBF4) as DJB4. rewrite fsize7 in DJB4.
        pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(keeplia S4lo) ltac:(clear; lia) ltac:(exact S4hi)) as SHS4. rewrite SHMAX_val in SHS4. change ((40 + 7) / 8) with 5 in SHS4.
        pose proof (proj1 (proj2 VSO4')) as VINV4. pose proof (proj1 VINV4) as Vsz4.
        pose proof (sh_boundL (Clg:=Clg) (vb_buf vr4) (vb_size vr4) ltac:(keeplia B4lo) ltac:(keeplia Vsz4) ltac:(exact B4hi)) as SHB4. rewrite SHMAX_val in SHB4.
        assert (NDB4 : vb_buf vr4 <> data).
        { destruct BUF4 as [PX|E]; [exact (NDP _ PX)| intros E2; rewrite E2 in E; rewrite LD3 in E; discriminate E]. }
        destruct (APART4 r ltac:(left; reflexivity)) as [NRS4 NRB4]. destruct (APART4 wa ltac:(right; left; reflexivity)) as [NWS4 NWB4]. rewrite ER4S in NRS4, NWS4.
        zstep. if_cases KZ; zify_cond KZ; [exfalso; apply SNZ; rewrite ER4S in KZ; rewrite ?unsigned_lit in KZ by (keeplia S4lo S4hi ACV); exact KZ|]. clear KZ.
        (* [comment removed for export] *)
        zstep. zstep.
        astop AINV4 MU4 WM4 CFP4.
        lazymatch goal with AIq : ainv A4 ?mx ?mdx, SBq : same_but_materialized md4 ?mdx |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
          rename AIq into AINVd; rename SBq into SBMd; rename mx into m4b; rename mdx into md4b end.
        lazymatch goal with MIq : mem_inv _ (aview A4 m4b) |- _ => rename MIq into MId end.
        assert (WS1d : ws1_obj LPA (HENV ff) A4 (aview A4 m4b) wa r)
          by (eapply (ws1_obj_munch LPA); [exact WS14| exact MU4| exact WM4| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [h_ff outside] in *;
              (first [ pose proof (WS14) as dR_41; dand8 dR_41 as _ _ _ _ _ _ LWA4 _ | pose proof WS14 as (_ & _ & _ & _ & _ & _ & LWA4 & _) ]);
              pose proof (as_frame_blk_disjoint LPA A4 m4 md4 ff HCLASS 0%nat wa 40 AINV4 FF4 LWA4) as DJW; rewrite fsize7 in DJW; keeplia Ha DJW]).
        assert (GLOBd : glob_ok LPA VIA (HENV ff) (aview A4 m4b))
          by (eapply (glob_ok_munch LPA); [exact GLOB4| exact MU4| exact WM4| intros a Ha; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha; unfold h_cp, h_vsc in Ha; cbn [h_ff outside] in *; keeplia Ha FB]).
        assert (HSHd : hshadow LPA (HENV ff) (aview A4 m4b))
          by (eapply (hshadow_munch LPA); [exact HSH4| exact MU4| eapply henv_geom_of_frame; [exact AINV4| exact HF4]| intros x Hx; cbn [h_ff outside] in *; unfold HFSIZE in Hx; change (8192 / 8) with 1024 in Hx; keeplia Hx FB]).
        (first [ pose proof (STKSH1) as dR_42; dand3 dR_42 as SSB4 SSN4 _ | pose proof STKSH1 as (SSB4 & SSN4 & _) ]).
        assert (SSBd : bytes_at rsegs (aview A4 m4b) SB (repeat (Z_to_bv 8 0) (Z.to_nat N)))
          by (eapply (bytes_at_munch LPA); [exact SSB4| exact MU4| rewrite repeat_length, Z2Nat.id by exact SSN4; intros a Ha; cbn [outside]; keeplia Ha FB SSC0 SST0 SHC8]).
        pose proof (stack_shadow_again _ _ SB N _ _ _ STKSH1 SSBd eq_refl) as STKSHd. clear SSBd SSB4.
        assert (VSOd : vsb_obj LPA A4 (aview A4 m4b) S vr4 true)
          by (eapply vsb_obj_munch; [exact VSO4'| exact MU4| exact WM4| intros a__ Ha__; cbn; keeplia Ha__ DJS4 DJB4 S4hi B4hi]).
        assert (MP4b : mapped (aview A4 m4b) (bv_unsigned sp - 12288) 12288).
        { pose proof (stk_release rsegs _ _ _ _ ST4 SPILL ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
          pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
          pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3. unfold SAVE in Y3. cbn [cells_size csize Nat.add] in Y3.
          eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
        lazymatch type of CF04 with cframe _ _ _ _ _ _ ?N4 _ _ =>
          pose proof (cframe_noalloc LPA (owned A4) (bv_unsigned sp) 12288 (HV ff) nowhere (aview A4 m4) (aview A4 m4b) _ MU4
                        ltac:(intros a Ha NO; cbn [outside] in NO; right; right; left; rewrite fsize7; keeplia Ha NO) MP4b ltac:(intros a X; destruct X)) as CFst;
          pose proof (cframe_seq LPA (owned A0) (owned A4) (owned A4) (bv_unsigned sp) 12288 12288 12288 (HV ff) N4 (HV ff) nowhere (HV ff) N4
                        (aview A0 m0) (aview A4 m4) (aview A4 m4b) CF04 CFst ltac:(clear; lia) ltac:(clear; lia) MP4b ltac:(intros a X; exact X)
                        ltac:(intros a X; right; exact X) ltac:(intros a X; left; exact X)) as CF04b;
          clear CFst CF04
        end.
        (first [ pose proof (HSHd) as dR_43; dand9 dR_43 as _ _ _ _ _ _ _ SHVL _ | pose proof HSHd as (_ & _ & _ & _ & _ & _ & _ & SHVL & _) ]). unfold h_vsbloc in SHVL. cbn [h_ff] in SHVL.
        (first [ pose proof ((as_frame_ok LPA A4 m4 md4 ff HCLASS 0%nat AINV4 FF4)) as dR_44; dand3 dR_44 as _ AL4 _ | destruct (as_frame_ok LPA A4 m4 md4 ff HCLASS 0%nat AINV4 FF4) as (_ & AL4 & _) ]). rewrite fsize7 in AL4. change (Z.min 8192 4096) with 4096 in AL4.
        eapply (VSB_destroy_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m4b md4b A4 (ff + 3056) S vr4 true (bv_unsigned sp - 12288) T);
          [ exact AINVd | exact MId | reflexivity
          | rewrite <- ER4S; exact VSBL
          | eapply (cobj_hframe LPA A4 _ _ (HENV ff) (ff + 3056) 8 (ff + 3056) 8);
            [exact HF4| cbn [h_ff]; clear; lia| unfold HOBJ_END; cbn [h_ff]; clear; lia| clear - AL4; Z.div_mod_to_equations; lia| clear; lia| clear; lia| exact SHVL]
          | clear - AL4; Z.div_mod_to_equations; lia
          | keeplia FB
          | exact VSOd | exact TP
          | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact AL16
          | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact ST4
          | keeplia SPLO ACV
          | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); unfold_stacks; keeplia SPLO D0 ACV | ].
        intros y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 A5 m5 md5. cbv zeta.
        intros AINV5 MI5 MDF5 FRS5 LB5 TC5 NL5 SC5 PC5 ST5 PS0 DS5 DB5 LV5 CF5.   (* [comment removed for export] *)
        rewrite unsigned_lit in ST5, CF5 by (keeplia SPR D0 SPLO ACV). unfold DESTROY_STACK, ASTK in CF5.
        replace (ret_pc (Z_to_bv 64 0x873e0)) with (Z_to_bv 64 0x873e0) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
        pose proof (as_minv LPA A5 _ _ AINV5) as [_ MH5].
        assert (FF5 : a_frame A5 ff = Some (HCLASS, 0%nat)) by (rewrite (FRS5 ff); exact FF4).
        assert (FR5 : forall g, g <> ff -> a_frame A5 g = None) by (intros g NE; rewrite (FRS5 g); exact (FR4 g NE)).
        lazymatch type of CF5 with cframe _ _ _ _ _ ?V _ _ _ =>
          assert (AV5 : forall a, (bv_unsigned sp - 12288 <= a < bv_unsigned sp \/ sh ff <= a < sh ff + 540 \/ ff <= a < ff + 24
                                   \/ SB <= a < SB + N \/ data <= a < data + Z.of_nat (length inp)) -> ~ V a);
          [ intros a Ha [X|[X|X]];
            [ refine (blk_avoids A4 m4b md4b ff 0%nat S 40 a AINVd FF4 LS4 LD4 NDS SSC0 SST0 X _); clear - Ha; tauto
            | refine (blk_avoids A4 m4b md4b ff 0%nat (vb_buf vr4) (vb_size vr4) a AINVd FF4 LBF4 LD4 NDB4 SSC0 SST0 X _); clear - Ha; tauto
            | keeplia Ha X FB SPLO ACV SSC0 SST0 SHC8 Dlo Dhi DJD ]
          | ];
          assert (AVH : forall a, (ff <= a < ff + 8192 \/ sh ff <= a < sh ff + 1024 \/ 65536 <= a < 6332416 \/ wa <= a < wa + 40) -> ~ (ff + 3056 <= a < ff + 3056 + 8) -> ~ V a);
          [ (first [ pose proof (WS1d) as dR_45; dand9 dR_45 as _ _ _ _ _ _ LWAd _ LRd | pose proof WS1d as (_ & _ & _ & _ & _ & _ & LWAd & _ & LRd) ]);
            pose proof (as_frame_blk_disjoint LPA A4 m4b md4b ff HCLASS 0%nat wa 40 AINVd FF4 LWAd) as DJWd; rewrite fsize7 in DJWd;
            intros a Ha NPS [X|[X|X]];
            [ destruct Ha as [Ha|[Ha|[Ha|Ha]]];
              [ exact (nb_avoids A4 m4b md4b ff 0%nat S 40 a AINVd FF4 LS4 X (or_introl Ha))
              | exact (nb_avoids A4 m4b md4b ff 0%nat S 40 a AINVd FF4 LS4 X (or_intror (or_introl Ha)))
              | exact (nb_avoids A4 m4b md4b ff 0%nat S 40 a AINVd FF4 LS4 X (or_intror (or_intror Ha)))
              | exact (blk2_avoids A4 m4b md4b wa 40 S 40 a AINVd LWAd LS4 (not_eq_sym NWS4) X Ha) ]
            | destruct Ha as [Ha|[Ha|[Ha|Ha]]];
              [ exact (nb_avoids A4 m4b md4b ff 0%nat _ _ a AINVd FF4 LBF4 X (or_introl Ha))
              | exact (nb_avoids A4 m4b md4b ff 0%nat _ _ a AINVd FF4 LBF4 X (or_intror (or_introl Ha)))
              | exact (nb_avoids A4 m4b md4b ff 0%nat _ _ a AINVd FF4 LBF4 X (or_intror (or_intror Ha)))
              | exact (blk2_avoids A4 m4b md4b wa 40 _ _ a AINVd LWAd LBF4 (not_eq_sym NWB4) X Ha) ]
            | exact (NPS X) ]
          | ]
        end.
        (* [comment removed for export] *)
        lazymatch type of CF5 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
          apply (rw_cells_ccall LPA A4 A5 xsp win V Nn ma mb CF5 (bv_unsigned sp + -192 - d)) in SPILL;
          [| exact (crange_stack (Clg:=Clg) (L:=LPA) A4 _ _ ma (bv_unsigned sp + -192 - d) 88 AINVd ltac:(keeplia SPLO ACV D0) ltac:(keeplia SPR D0)
                     (rw_cells_mapped (Clg:=Clg) LPA _ _ _ SPILL ltac:(off_image_solve LPA)))
           | cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia D0| intros i Hi X; refine (AV5 _ _ X); keeplia Hi D0] ];
          apply (rw_cells_ccall LPA A4 A5 xsp win V Nn ma mb CF5 (bv_unsigned sp + -104)) in SAV;
          [| exact (crange_stack (Clg:=Clg) (L:=LPA) A4 _ _ ma (bv_unsigned sp + -104) 104 AINVd ltac:(keeplia SPLO ACV) ltac:(keeplia SPR)
                     (rw_cells_mapped (Clg:=Clg) LPA _ _ _ SAV ltac:(off_image_solve LPA)))
           | cbn [SAVE Cells.cells_size Cells.csize Nat.add length]; split; [keeplia D0| intros i Hi X; refine (AV5 _ _ X); keeplia Hi D0] ];
          apply (rw_cells_ccall LPA A4 A5 xsp win V Nn ma mb CF5 (sh ff)) in SHC;
          [| eapply crange_fshadow; [exact AINVd| exact FF4| clear; lia| rewrite fsize7; change (8192 / 8) with 1024; cbn [Cells.cells_size Cells.csize Nat.add length]; clear; lia| cbn; clear; lia]
           | cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia FB SPLO ACV D0| intros i Hi X; refine (AV5 _ _ X); keeplia Hi] ];
          apply (rw_cells_ccall LPA A4 A5 xsp win V Nn ma mb CF5 ff) in FFH;
          [| eapply crange_fframe; [exact AINVd| exact FF4| clear; lia| rewrite fsize7; cbn [Cells.cells_size Cells.csize Nat.add length]; clear; lia| cbn; clear; lia]
           | cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia FB SPLO ACV D0| intros i Hi X; refine (AV5 _ _ X); keeplia Hi] ];
          apply (stk_ccall_any A4 A5 _ _ ma mb xsp win V Nn _ _ AINVd CF5) in STpad; [| keeplia SPLO ACV D0 | intros a Ha X; refine (AV5 _ _ X); keeplia Ha D0];
          assert (STKSH5 : stack_shadow LPA mb SB N (bv_unsigned sp - 12288) (bv_unsigned sp + 64));
          [ (first [ pose proof (STKSHd) as dR_46; dand6 dR_46 as SSB SSN _ _ SSC SST | pose proof STKSHd as (SSB & SSN & _ & _ & SSC & SST) ]);
            pose proof (crange_stack_shadow (Clg:=Clg) LPA A4 _ _ SB N _ _ AINVd STKSHd ltac:(keeplia SPLO ACV)) as CRS;
            eapply stack_shadow_again; [exact STKSHd| | reflexivity];
            apply (bytes_at_ccall LPA A4 A5 xsp win V Nn ma mb CF5 SB);
            [ rewrite zeros_length, Z2Nat.id by exact SSN; exact CRS
            | rewrite zeros_length, Z2Nat.id by exact SSN; split;
              [ unfold kHighMemBeg in SST; keeplia SSC SST SHC8 SPLO ACV D0
              | intros i Hi X; refine (AV5 _ _ X); keeplia Hi]
            | exact SSB ]
          | ];
          (* [comment removed for export] *)
          assert (GLOB5 : glob_ok LPA VIA (HENV ff) mb);
          [ eapply (glob_ok_acall (HENV ff) A4 A5); [exact AINVd| exact HF4| exact CF5| exact GLOBd| keeplia SPLO ACV D0|];
            intros a Ha; unfold h_cp, h_vsc in Ha; cbn [h_ff] in Ha;
            destruct Ha as [Ha|[Ha|[Ha|Ha]]];
            [ apply AVH; [right; right; left; keeplia Ha| keeplia Ha FB]
            | apply AVH; [right; right; left; keeplia Ha| keeplia Ha FB]
            | apply AVH; [left; keeplia Ha| keeplia Ha]
            | apply AVH; [left; keeplia Ha| keeplia Ha] ]
          | ];
          assert (HSH5 : hshadow LPA (HENV ff) mb);
          [ eapply (hshadow_ccall LPA A4 A5); [exact AINVd| exact HF4| exact CF5| exact HSHd| keeplia SPLO ACV D0|];
            intros x Hx; cbn [h_ff] in Hx; unfold HFSIZE in Hx; change (8192 / 8) with 1024 in Hx; apply AVH; [right; left; exact Hx| keeplia Hx FB]
          | ];
          assert (WS15 : ws1_obj LPA (HENV ff) A5 mb wa r);
          [ (first [ pose proof (WS1d) as dR_47; dand9 dR_47 as _ _ _ _ _ _ LWAd _ LRd | pose proof WS1d as (_ & _ & _ & _ & _ & _ & LWAd & _ & LRd) ]);
            eapply (ws1_obj_ccall LPA (HENV ff) A4 A5); [exact AINVd| exact HF4| exact CF5| exact WS1d| keeplia SPLO ACV D0
              | rewrite (LV5 wa (not_eq_sym NWS4) (not_eq_sym NWB4)); exact LWAd
              | rewrite (LV5 r (not_eq_sym NRS4) (not_eq_sym NRB4)); exact LRd |];
            intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [h_ff] in Ha;
            pose proof (as_frame_blk_disjoint LPA A4 m4b md4b ff HCLASS 0%nat wa 40 AINVd FF4 LWAd) as DJWd; rewrite fsize7 in DJWd;
            destruct Ha as [Ha|[Ha|Ha]];
            [ apply AVH; [left; keeplia Ha| keeplia Ha]
            | apply AVH; [left; keeplia Ha| keeplia Ha]
            | apply AVH; [right; right; right; exact Ha| keeplia Ha DJWd] ]
          | ]
        end.
        assert (MP5 : mapped (aview A5 m5) (bv_unsigned sp - 12288) 12288).
        { pose proof (stk_release rsegs _ _ _ _ ST5 SPILL ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
          pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
          pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3. unfold SAVE in Y3. cbn [cells_size csize Nat.add] in Y3.
          eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
        lazymatch type of CF5 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
          lazymatch type of CF04b with cframe _ _ _ _ _ _ ?N4 _ _ =>
          pose proof (cframe_reframe LPA (owned A4) (owned A5) xsp win (bv_unsigned sp) 12288 V Nn ma mb CF5 ltac:(keeplia D0) ltac:(keeplia D0 SPR) MP5) as CF5';
          assert (V5N : forall a, V a -> N4 a \/ HV ff a)
            by (intros a X; cbn beta; destruct X as [X|[X|X]];
                [ left; left; left; right; right; right; left; exact X
                | left; right; split; [exact R4NZ| unfold vsb_blocks; right; exact X]
                | right; right; left; rewrite fsize7; keeplia X ]);
          pose proof (cframe_seq LPA (owned A0) (owned A4) (owned A5) (bv_unsigned sp) 12288 12288 12288 (HV ff) N4 V Nn (HV ff) N4
                      (aview A0 m0) (aview A4 m4b) mb CF04b CF5' ltac:(clear; lia) ltac:(clear; lia) MP5 ltac:(intros a X; exact X) V5N
                      ltac:(intros a X; left; exact X)) as CF05;
          clear V5N CF5' CF5
        end end.
        (* [comment removed for export] *)
        assert (LIVEc5 : forall p n, a_live A0 p = Some n -> a_live A5 p = Some n).
        { intros p n Hp. assert (H1 : a_live A1 p = Some n) by (rewrite LIVE1; exact Hp).
          assert (H2 : a_live A2 p = Some n).
          { rewrite (LV2 p); [exact H1| | | |]; intros ->; [rewrite LWA1 in H1| rewrite LR1 in H1| rewrite LS1 in H1| rewrite LBb1 in H1]; discriminate H1. }
          assert (H3 : a_live A3 p = Some n) by (apply LKEEP3; [exact H2| intros ->; rewrite LBb1 in H1; discriminate H1]).
          rewrite (LV5 p); [exact (LIVEc4 p n Hp)| intros ->; rewrite LS1 in H1; discriminate H1|].
          intros ->. destruct BUF4 as [PX|E]; [| rewrite H3 in E; discriminate E].
          destruct (PNEW _ PX) as [E|E]; [rewrite E, LBb1 in H1; discriminate H1| rewrite H2 in E; discriminate E]. }
        (* [comment removed for export] *)
        ago AINV5. fold_cl_segs.
        lazymatch type of SPILL with rw_cells _ ?mx ?Ax [?c0;?c1;?c2;?c3;?c4;?c5;?c6;?c7;?c8] =>
          pose proof (rw_cells_merge rsegs mx Ax [c0;c1] [c2] [c3;c4;c5;c6;c7;c8] SPILL) as SPa;
          pose proof (rw_cells_merge rsegs mx Ax [c0; c1; CB (cells_size [c2]) (cells_bytes [c2]); c3; c4] [c5;c6;c7;c8] [] SPa) as SPb;
          clear SPa SPILL; cbn [cells_size csize Nat.add cells_bytes cbytes app] in SPb end.
        destruct (Z.eqb_spec S 0) as [ES0|_]; [exact (False_ind _ (SNZ ES0))|].
        rewrite ER4S in LB4, NL4. destruct (Z.eqb_spec S 0) as [ES0|_]; [exact (False_ind _ (SNZ ES0))|].
        lazymatch type of CF05 with cframe _ _ _ _ _ _ ?NK _ _ =>
        eapply (seg_T' A5 m5 md5 (Some (wa, r)) ff 0%nat d NK) end;
          [ exact AINV5 | exact MI5
          | eapply amd_frame_trans; [exact MDF1|]; eapply amd_frame_trans; [exact MDF2|]; eapply amd_frame_trans; [apply amd_frame_sbm; [exact SBMb| exact MH2]|];
            eapply amd_frame_trans; [exact MDF3|]; eapply amd_frame_trans; [apply amd_frame_sbm; [exact SBMc| exact MH3]|];
            eapply amd_frame_trans; [exact MDF4|]; eapply amd_frame_trans; [apply amd_frame_sbm; [exact SBMd| exact MH4]| exact MDF5]
          | exact FF5 | exact FFNZ | exact FR5
          | split; [exact WS15|]; split; [rewrite <- (LIVE1 wa); exact LWA1|]; split; [rewrite <- (LIVE1 r); exact LR1|];
            split; [exact LIVEc5|]; split; [rewrite LB5, LB4, LB3, LB2, LB1; clear; lia|]; split; [rewrite NL5, NL4, NL3, NL2, NL1; clear - WNL; lia|];
            intros a X; cbv beta; left; left; right; destruct X as [X|X]; [left; exact X| right; left; exact X]
          | exact GLOB5 | exact HSH5 | rewrite TC5, TC4, TC3, TC2; exact TC1
          | unfold LIB_SECC; rewrite SC5; unfold FIN_CRED in SC4; unfold PARSE_CRED in SC3; rewrite SC2, SC1 in SC3; keeplia SECC DIVF SC3 SC4
          | rewrite PC5; rewrite PC2, PC1 in PC3; unfold LIB_PRIM, PARSE_PRIM, PRIM_ROOM, PPOT_CAP, PVB_MAX in *; keeplia PRIMC PC3 PC4 (* [comment removed for export] *)
          | exact D0 | exact AL16 | exact ST5 | exact SPb | exact STpad | exact SAV | exact SHC | exact FFH | exact STKSH5 | exact CF05 | exact FRM0 ].
  Qed.
End S.
End A_Ha3dj.


Module A_Ha05e.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpya4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_WS7e8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Panhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_WSruy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Ha0ng.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Ha0ng.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Ha0ng.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_ImgLow OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_WS7e8.A_WSg84 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Panhq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_WSruy.A_HKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Ha0ng.A_Ha5zr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Ha0ng.A_Haqjq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Ha0ng OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Har9f.A_Ha3dj.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].
Ltac icall_consts_in H ::= unfold asan_memset_post, WS_Init_post, ASAN_MEMSET_STACK, WSINIT_STACK, ICPT_STACK, h_ws, h_wsbuf in H; cbn [h_ff] in H.

(* [comment removed for export] *)
Lemma img_ivl_bss_vsc {Clg : Ceiling} {AI : AsanAlloc LPA} : img_ivl (L:=LPA) 6189632 (6189632 + 8).
Proof. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. Qed.
Lemma img_ivl_bss_cp {Clg : Ceiling} {AI : AsanAlloc LPA} : img_ivl (L:=LPA) 6189664 (6189664 + 8).
Proof. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. Qed.

Lemma sh_addk : forall a d, a mod 8 = 0 -> d mod 8 = 0 -> sh (a + d) = sh a + d / 8.
Proof. intros a d Ha Hd. unfold sh, kShadowOffset. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma hshadow_of_zero {Clg : Ceiling} {AI : AsanAlloc LPA} : forall ff v, hsh_zero (sh ff) v -> ff mod 8 = 0 -> hshadow LPA (HENV ff) v.
Proof.
  intros ff v HZ AL. unfold hshadow, h_vsc, h_cp, h_req, h_resp, h_vc, h_wrk, h_ws, h_vsbloc, h_hd, h_wsbuf. cbn [h_ff cl_segs LPA].
  rewrite !sh_addk by (first [exact AL | reflexivity]).
  change (32 / 8) with 4. change (1536 / 8) with 192. change (2416 / 8) with 302. change (2512 / 8) with 314. change (2608 / 8) with 326.
  change (2720 / 8) with 340. change (2976 / 8) with 372. change (3056 / 8) with 382. change (3088 / 8) with 386. change (3152 / 8) with 394.
  change (shpat 1368) with (zb 171 ++ []). change (shpat 752) with (zb 94 ++ []). change (shpat 56) with (zb 7 ++ []).
  change (shpat 72) with (zb 9 ++ []). change (shpat 184) with (zb 23 ++ []). change (shpat 40) with (zb 5 ++ []).
  change (shpat 8) with (zb 1 ++ []). change (shpat 32) with (zb 4 ++ []). change (shpat 1024) with (zb 128 ++ []).
  rewrite !app_nil_r. exact HZ.
Qed.

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (data : Z) (inp : list byte) (SB N : Z) (T : TSet).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPLO : alloc_ceiling + 65536 + LIB_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis MI00 : mem_inv rsegs (aview A0 m0).
  Hypothesis ST00 : stk rsegs (aview A0 m0) (bv_unsigned sp - LIB_STACK) (bv_unsigned sp).
  Hypothesis STKSH00 : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64).
  Hypothesis FR00 : forall ff, a_frame A0 ff = None.
  Hypothesis LEN : Z.of_nat (length inp) < NMAX.
  Hypothesis INP : length inp <> 0%nat -> data <> 0 /\ a_live A0 data = Some (Z.of_nat (length inp)) /\ bytes_at rsegs (aview A0 m0) data inp.
  Hypothesis BUD : a_livebytes A0 + LIB_LIVE (Z.of_nat (length inp)) <= LIVE_MAX /\ a_nlive A0 + LIB_NLIVE <= NLIVE_MAX.
  Hypothesis SECC : LIB_SECC (Z.of_nat (length inp)) <= a_seccred A0.
  Hypothesis PRIMC : LIB_PRIM (Z.of_nat (length inp)) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (md' : Model) (A' : AS),
      alib_post sp m0 md0 A0 inp SB N m' md' A' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj TP (conj SP16 (conj SPLO (conj SPHI (conj AINV00 (conj MI00 (conj ST00 (conj STKSH00 (conj FR00 (conj LEN (conj INP (conj BUD
      (conj SECC (conj PRIMC K)))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    pose proof (zr_word ra) as RAR; unfold inr64 in RAR;
    unfold LIB_STACK in *.

  Local Ltac pose_C :=
    pose proof (seg_C ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 data inp SB N T
                  TP SP16 SPLO SPHI AINV00 MI00 ST00 STKSH00 FR00 LEN INP BUD SECC PRIMC K) as seg_C'.

  (* [comment removed for export] *)
  Local Ltac henv_now ff GLOB1 HSH1 HVIS1 CE1 CF3 HG SHA FB SPLO ACV GLOBc HSHc HVISc CEc :=
    lazymatch goal with MUq : munch ?W (aview ?A1 ?m1) ?vc, WMq : wmono _ (aview ?A1 ?m1) ?vc |- evt _ _ (MS _ _ _ _ _ ?vc _) =>
      assert (GLOBc : glob_ok LPA VIA (HENV ff) vc)
        by (eapply (glob_ok_munch LPA); [exact GLOB1| exact MUq| exact WMq|
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn [h_ff] in Ha__; cbn [outside]; keeplia Ha__ FB SPLO ACV]);
      assert (HSHc : hshadow LPA (HENV ff) vc)
        by (eapply (hshadow_munch LPA); [exact HSH1| exact MUq| exact HG|
              intros x__ Hx__; cbn [h_ff] in Hx__; unfold HFSIZE in Hx__; change (8192 / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ FB SPLO ACV]);
      assert (HVISc : hvis (HENV ff) vc)
        by (intros a__ Ha__; cbn [h_ff] in Ha__; unfold HOBJ_END in Ha__;
            pose proof (SHA a__ ltac:(keeplia Ha__)) as SB__; pose proof (Z.mod_pos_bound (sh a__) 8 ltac:(clear; lia)) as M8__;
            eapply mapped_munch; [exact MUq| keeplia SB__ M8__ FB| keeplia SB__ M8__ FB| intros i__ Hi__; cbn [outside]; keeplia SB__ M8__ Hi__ FB SPLO ACV
              | exact (HVIS1 a__ ltac:(cbn [h_ff]; unfold HOBJ_END; keeplia Ha__))]);
      pose proof (cenv_munch3 _ _ _ CE1 MUq CF3) as CEc
    end.

  (* [comment removed for export] *)
  Local Ltac hsh_now ff HSH1 HG FB SPLO ACV SHrq SHrs SHvc :=
    lazymatch goal with MUq : munch ?W (aview ?A1 ?m1) ?vc |- evt _ _ (MS _ _ _ _ _ ?vc _) =>
      let X := fresh "HSHc" in
      assert (X : hshadow LPA (HENV ff) vc)
        by (eapply (hshadow_munch LPA); [exact HSH1| exact MUq| exact HG|
              intros x__ Hx__; cbn [h_ff] in Hx__; unfold HFSIZE in Hx__; change (8192 / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ FB SPLO ACV]);
      try clear SHrq; try clear SHrs; try clear SHvc;
      (first [ pose proof (X) as dR_1; dand6 dR_1 as _ _ SHrq SHrs SHvc _ | pose proof X as (_ & _ & SHrq & SHrs & SHvc & _) ]); clear X;
      unfold h_req, h_resp, h_vc in SHrq, SHrs, SHvc; cbn [h_ff] in SHrq, SHrs, SHvc; fold_cl_segs;
      change (shpat 56) with (repeat (Z_to_bv 8 0) 7 ++ []) in SHrq; rewrite app_nil_r in SHrq;
      change (shpat 56) with (repeat (Z_to_bv 8 0) 7 ++ []) in SHrs; rewrite app_nil_r in SHrs;
      change (shpat 72) with (repeat (Z_to_bv 8 0) 9 ++ []) in SHvc; rewrite app_nil_r in SHvc
    end.

  (* [comment removed for export] *)
  Local Ltac chk0_rest SRC k :=
    shadow_addr SRC k; zstep;
    let K := fresh "KS" in
    zstep; if_cases K; zify_cond K;
    [ first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead | (exfalso; clear - K; lia) ]
    | first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead | (exfalso; clear - K; lia) ] ].

  (* [comment removed for export] *)
  Local Ltac memset_call TGT RQ CE1 CF3 STlo FB SPR D0 SPLO ACV :=
    lazymatch goal with MUq : munch ?W (aview ?A1 ?m1) ?vc |- evt _ _ (MS _ _ _ _ _ ?vc _) =>
      let AMC := fresh "AMC" in
      pose proof (asan_memset_cells_of_consts _ (proj1 (cenv_munch3 _ _ _ CE1 MUq CF3))) as AMC; fold_aview;
      icall asan_memset_spec by
        (rewrite ?unsigned_lit by (keeplia FB SPR D0 SPLO ACV);
         first [ exact TGT | exact AMC | exact STlo | assumption
               | (unfold ASAN_MEMSET_STACK; keeplia D0 SPLO ACV)
               | (left; keeplia FB SPLO ACV D0)
               | (right; first [ apply (range_ok_high_munch _ _ _ _ _ RQ MUq) ];
                  [ keeplia FB | clear; lia | keeplia FB
                  | repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; keeplia FB SPLO ACV ])
               | keeplia SPLO ACV
               | (clear; lia) ]);
      try clear AMC
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 K SECC PRIMC BUD INP LEN FR00 STKSH00 ST00 MI00 AINV00 SPHI SPLO SP16 TP"] Lemma seg_S : forall (A1 : AS) (m1 : mem) (md1 : Model) (ff : Z) (d : Z) (N1 : Z -> Prop) (flags : Z)
      (xra xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xs9 xt3 xt4 xt5 xt6 : word)
      (j0 j16 hdr bs jrq jrs jvc jwk jws jvl jhd jwb : list byte),
    let sp1 := bv_unsigned sp + -192 - d in let SHB := sh ff in let H := HENV ff in let v := aview A1 m1 in
    ainv A1 m1 md1 -> mem_inv rsegs v -> amd_frame md0 md1 ->
    a_frame A1 ff = Some (HCLASS, 0%nat) -> ff <> 0 -> (forall g, g <> ff -> a_frame A1 g = None) ->
    (forall p, a_live A1 p = a_live A0 p) -> a_livebytes A1 = a_livebytes A0 -> a_nlive A1 = a_nlive A0 ->
    a_tinycred A1 = a_tinycred A0 -> a_seccred A1 = a_seccred A0 -> a_primcred A1 = a_primcred A0 (* [comment removed for export] *) ->
    length inp <> 0%nat -> 0 <= flags < 16 ->
    glob_ok LPA VIA H v -> hshadow LPA H v -> bytes_at rsegs v data inp ->
    0 <= d <= 16 -> sp1 mod 16 = 0 ->
    stk rsegs v (bv_unsigned sp - LIB_STACK) sp1 ->
    (* [comment removed for export] *)
    rw_cells rsegs v sp1 [CB 24 j0; C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 (SHB + 192)); C8 (Z_to_bv 64 (SHB + 394));
                         C8 (Z_to_bv 64 (Z.of_nat (length inp))); C8 (Z_to_bv 64 data); CB 16 j16; C8 (Z_to_bv 64 ff)] ->
    stk rsegs v (sp1 + 88) (bv_unsigned sp + -104) ->
    rw_cells rsegs v (bv_unsigned sp + -104) (SAVE ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells rsegs v SHB [CB 540 bs] ->
    rw_cells rsegs v ff [CB 24 hdr] ->
    rw_cells rsegs v (ff + 2416) [CB 56 jrq] -> rw_cells rsegs v (ff + 2512) [CB 56 jrs] ->
    rw_cells rsegs v (ff + 2608) [CB 72 jvc] -> rw_cells rsegs v (ff + 2720) [CB 184 jwk] ->
    rw_cells rsegs v (ff + 2976) [CB 40 jws] -> rw_cells rsegs v (ff + 3056) [CB 8 jvl] ->
    rw_cells rsegs v (ff + 3088) [CB 32 jhd] -> rw_cells rsegs v (ff + 3152) [CB 32 jwb] ->
    stack_shadow LPA v SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64) ->
    cframe LPA (owned A0) (owned A1) (bv_unsigned sp) LIB_STACK (HV ff) N1 (aview A0 m0) v ->
    (forall a, frm ff HCLASS a -> owned A0 a \/ (aview A0 m0 (Z_to_bv 64 a) = None /\ ~ in_image LPA a)) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1)
                                    a0 a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 ff) (Z_to_bv 64 SHB) (Z_to_bv 64 2147450880) (Z_to_bv 64 (SHB + 192)) (Z_to_bv 64 (SHB + 4))
                                    (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 flags) xs9 (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 data)
                                    xt3 xt4 xt5 xt6)
                               F (Z_to_bv 64 0x8726c) fc None m1 (seg_rom rsegs)) md1) T.
  Proof.
    touch_all. intros until jwb. cbv zeta.
    intros AINV1 MI1 MDF1 FF1 FFNZ FR1 LIVE1 LB1 NL1 TC1 SC1 PC1 LENp FL GLOB1 HSH1 DAT D0 AL16 STlo SPILL STpad SAV SHC FFH
           REQ RESP VC WRK WS40 VSBJ HD32 WSB32 STKSH1 CF01 FRM0.
    pose_C. prelims.
    pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    (first [ pose proof ((fframe_geom LPA A1 m1 md1 ff HCLASS 0%nat AINV1 FF1)) as dR_2; dand5 dR_2 as _ FS FLO FHI _ | destruct (fframe_geom LPA A1 m1 md1 ff HCLASS 0%nat AINV1 FF1) as (_ & FS & FLO & FHI & _) ]).
    rewrite fsize7 in FS, FHI. change (Z.min 8192 4096) with 4096 in FS.
    (first [ pose proof ((app_lin LPA ff 8192 FLO)) as dR_3; dex2 dR_3 as ix sx; rename dR_3 into FB | pose proof ((app_lin LPA ff 8192 FLO)) as dR_3; dand3 dR_3 as ix sx FB | pose proof (app_lin LPA ff 8192 FLO) as (ix & sx & FB) ]). cbn [cl_image_lo cl_image_hi LPA] in FB. change ((8192 + 7) / 8) with 1024 in FB.
    (first [ pose proof ((as_frame_ok LPA A1 m1 md1 ff HCLASS 0%nat AINV1 FF1)) as dR_4; dand3 dR_4 as _ AL4 _ | destruct (as_frame_ok LPA A1 m1 md1 ff HCLASS 0%nat AINV1 FF1) as (_ & AL4 & _) ]). rewrite fsize7 in AL4. change (Z.min 8192 4096) with 4096 in AL4.
    assert (FF0 : 4096 <= ff) by (keeplia FB).
    assert (HF1 : hframe LPA A1 (HENV ff)) by (exists 0%nat; exact FF1).
    pose proof (henv_geom_of_frame LPA A1 m1 md1 (HENV ff) AINV1 HF1) as HG.
    pose proof (cenv_intro A1 m1 md1 AINV1) as CE1.
    pose proof (hvis_intro LPA A1 m1 md1 (HENV ff) AINV1 HF1) as HVIS1.
    assert (SHA : forall a, ff <= a < ff + 4176 -> sh ff <= sh a <= sh ff + 1023).
    { intros a Ha. unfold sh, kShadowOffset. clear - Ha AL4. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    (first [ pose proof ((INP LENp)) as dR_5; dand3 dR_5 as DNZ LD0 _ | destruct (INP LENp) as (DNZ & LD0 & _) ]).
    assert (LD1 : a_live A1 data = Some (Z.of_nat (length inp))) by (rewrite (LIVE1 data); exact LD0).
    (first [ pose proof ((live_geomP LPA A1 m1 md1 data _ AINV1 LD1)) as dR_6; dand6 dR_6 as _ _ Dlo Dhi Dimg _ | pose proof (live_geomP LPA A1 m1 md1 data _ AINV1 LD1) as (_ & _ & Dlo & Dhi & Dimg & _) ]). unfold kHighMemBeg in Dlo.
    pose proof (as_frame_blk_disjoint LPA A1 m1 md1 ff HCLASS 0%nat data _ AINV1 FF1 LD1) as DJD. rewrite fsize7 in DJD.
    (first [ pose proof (STKSH1) as dR_7; dand6 dR_7 as _ SSN0 SSL0 SSH0 SSC0 SST0 | pose proof STKSH1 as (_ & SSN0 & SSL0 & SSH0 & SSC0 & SST0) ]). unfold kHighMemBeg in SST0. pose proof sh_ceiling_ge as SHC8.
    (* [comment removed for export] *)
    assert (CF3 : Forall const_free_ivl3 [(bv_unsigned sp - 12288, bv_unsigned sp); (ff + 2416, ff + 4176)]).
    { repeat (apply Forall_cons); try apply Forall_nil.
      - apply const_free_ivl3_high. cbn [fst]. keeplia SPLO ACV.
      - apply (const_free_ivl3_app ff 8192); [exact FLO| clear; lia| clear; lia]. }
    (first [ pose proof (HSH1) as dR_8; dand7 dR_8 as _ _ SHrq1 SHrs1 SHvc1 SHwk1 _ | pose proof HSH1 as (_ & _ & SHrq1 & SHrs1 & SHvc1 & SHwk1 & _) ]).
    unfold h_req, h_resp, h_vc, h_wrk in SHrq1, SHrs1, SHvc1, SHwk1. cbn [h_ff] in SHrq1, SHrs1, SHvc1, SHwk1. fold_cl_segs.
    assert (RQrq : range_ok (aview A1 m1) (ff + 2416) 56).
    { eapply (shadowed_range_ok _ _ _ (ff + 2416) 56); [exact SHrq1| apply (hff_al8 (HENV ff) 2416 HG); reflexivity| keeplia FB| clear; lia| clear; lia| clear; lia
        | unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; keeplia FB
        | apply HVIS1; cbn [h_ff]; unfold HOBJ_END; clear; lia| apply HVIS1; cbn [h_ff]; unfold HOBJ_END; clear; lia]. }
    assert (RQrs : range_ok (aview A1 m1) (ff + 2512) 56).
    { eapply (shadowed_range_ok _ _ _ (ff + 2512) 56); [exact SHrs1| apply (hff_al8 (HENV ff) 2512 HG); reflexivity| keeplia FB| clear; lia| clear; lia| clear; lia
        | unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; keeplia FB
        | apply HVIS1; cbn [h_ff]; unfold HOBJ_END; clear; lia| apply HVIS1; cbn [h_ff]; unfold HOBJ_END; clear; lia]. }
    assert (RQvc : range_ok (aview A1 m1) (ff + 2608) 72).
    { eapply (shadowed_range_ok _ _ _ (ff + 2608) 72); [exact SHvc1| apply (hff_al8 (HENV ff) 2608 HG); reflexivity| keeplia FB| clear; lia| clear; lia| clear; lia
        | unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; keeplia FB
        | apply HVIS1; cbn [h_ff]; unfold HOBJ_END; clear; lia| apply HVIS1; cbn [h_ff]; unfold HOBJ_END; clear; lia]. }
    assert (RQwk : range_ok (aview A1 m1) (ff + 2720) 184).
    { eapply (shadowed_range_ok _ _ _ (ff + 2720) 184); [exact SHwk1| apply (hff_al8 (HENV ff) 2720 HG); reflexivity| keeplia FB| clear; lia| clear; lia| clear; lia
        | unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; keeplia FB
        | apply HVIS1; cbn [h_ff]; unfold HOBJ_END; clear; lia| apply HVIS1; cbn [h_ff]; unfold HOBJ_END; clear; lia]. }
    clear SHrq1 SHrs1 SHvc1 SHwk1.
    (* [comment removed for export] *)
    pose proof (hff_al8 (HENV ff) 2416 HG eq_refl) as ALrq. pose proof (hff_al8 (HENV ff) 2512 HG eq_refl) as ALrs.
    pose proof (hff_al8 (HENV ff) 2608 HG eq_refl) as ALvc. cbn [h_ff] in ALrq, ALrs, ALvc.
    (* [comment removed for export] *)
    assert (MP1 : mapped (aview A1 m1) (bv_unsigned sp - 12288) 12288).
    { pose proof (stk_release rsegs _ _ _ _ STlo SPILL ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
      pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
      pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3. unfold SAVE in Y3. cbn [cells_size csize Nat.add] in Y3.
      eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
    assert (CFP : client_fp LPA A1 (aview A1 m1) [(bv_unsigned sp - 12288, bv_unsigned sp); (ff + 2416, ff + 4176)]).
    { cbn. split; [left; split; [keeplia SPLO ACV| split; [keeplia SPR| replace (bv_unsigned sp - (bv_unsigned sp - 12288)) with 12288 by (clear; lia); exact MP1]]|].
      split; [| exact I]. right; right; left. first [ hotw_ex3 ff HCLASS (0%nat) | exists ff, HCLASS, 0%nat ]. split; [exact FF1| rewrite fsize7; clear; lia]. }
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB rsegs _ (ff + 3088) [] 32 jhd [] [16; 8; 8]%nat HD32 eq_refl) as HD3. clear HD32. cbn [mk_CB_cells app] in HD3.
    lazymatch type of HD3 with rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: nil) =>
      pose proof (proj1 (rw_cells_app rsegs mx (ff + 3088) [c0] [c1; c2]) HD3) as [HDa HDbc];
      cbn [cells_size csize Nat.add] in HDbc; change (Z.of_nat 16) with 16 in HDbc;
      replace (ff + 3088 + 16) with (ff + 3104) in HDbc by (clear; lia);
      pose proof (proj1 (rw_cells_app rsegs mx (ff + 3104) [c1] [c2]) HDbc) as [HDb HDc];
      cbn [cells_size csize Nat.add] in HDc; change (Z.of_nat 8) with 8 in HDc;
      replace (ff + 3104 + 8) with (ff + 3112) in HDc by (clear; lia) end.
    clear HD3 HDbc.
    (* [comment removed for export] *)
    hide DAT. hide SHC. hide FFH. hide FB.
    (* [comment removed for export] *)
    ago AINV1. fold_cl_segs.
    pose proof (munch_refl [(bv_unsigned sp - 12288, bv_unsigned sp); (ff + 2416, ff + 4176)] (aview A1 m1)) as MU.
    pose proof (wmono_refl rsegs (aview A1 m1)) as WM.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    do 11 zstep.
    unhide FB.
    henv_now ff GLOB1 HSH1 HVIS1 CE1 CF3 HG SHA FB SPLO ACV GLOBc HSHc HVISc CEc.
    hide FB.
    icall (WS_Init_ok (HENV ff) jws jwb (bv_unsigned sp - 12288)) by
      (rewrite ?unsigned_lit by (keeplia FHI FLO SPR D0 SPLO ACV);
       first [ reflexivity
             | exact WS40 | exact WSB32
             | exact GLOBc | exact HSHc | exact HVISc | exact HG | exact CEc | exact STlo
             | assumption
             | (unfold WSINIT_STACK, ICPT_STACK; keeplia D0 SPLO ACV)
             | keeplia SPLO ACV
             | (apply f_equal; cbn [h_ws h_wsbuf h_ff]; clear; lia) ]).
    try clear GLOBc. try clear HSHc. try clear HVISc. try clear CEc.
    lazymatch goal with X : ws0_obj _ _ ?vq |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into WS0c end.
    try lazymatch goal with X : glob_ok _ _ _ ?vq |- evt _ _ (MS _ _ _ _ _ ?vq _) => clear X end.
    lazymatch goal with X : stk _ ?vq (bv_unsigned sp - 12288) _ |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into STlo end.
    (* [comment removed for export] *)
    (first [ dex1 WS0c as wsid; dand3 WS0c as WSID WSC WEC | dand4 WS0c as wsid WSID WSC WEC | destruct WS0c as (wsid & WSID & WSC & WEC) ]). fold_cl_segs.
    unfold ws_cells, ws_rec_of, h_ws, h_wsbuf in WSC. cbn [ws_id ws_s ws_f ws_r ws_e h_ff] in WSC.
    unfold wsemu_cells, wsemu_WS0, h_wsbuf in WEC. cbn [we_len we_ws we_first we_last h_ff] in WEC.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    unhide FB. memset_call REQ RQrq CE1 CF3 STlo FB SPR D0 SPLO ACV. hide FB.
    lazymatch goal with X : rw_cells _ ?vq (ff + 2416) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into REQ end.
    lazymatch goal with X : stk _ ?vq (bv_unsigned sp - 12288) _ |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into STlo end.
    change (Z.to_nat 56) with 56%nat in REQ. change (0 mod 256) with 0 in REQ.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    unhide FB. hsh_now ff HSH1 HG FB SPLO ACV SHrq SHrs SHvc. hide FB.
    chk0_rest SHrq 8.
    (* [comment removed for export] *)
    zstep. zstep. try clear SHvc. try clear SHrs. try clear SHrq. zstep.
    zstep. if_cases KG; zify_cond KG.
    { exfalso. unhide FB. rewrite ?unsigned_lit in KG by (keeplia FB ACV). keeplia KG FB ACV. }
    clear KG.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    unhide FB. hsh_now ff HSH1 HG FB SPLO ACV SHrq SHrs SHvc. hide FB.
    shadow_chk0z SHrq 8.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    unhide FB. memset_call RESP RQrs CE1 CF3 STlo FB SPR D0 SPLO ACV. hide FB.
    lazymatch goal with X : rw_cells _ ?vq (ff + 2512) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into RESP end.
    lazymatch goal with X : stk _ ?vq (bv_unsigned sp - 12288) _ |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into STlo end.
    change (Z.to_nat 56) with 56%nat in RESP. change (0 mod 256) with 0 in RESP.
    (* [comment removed for export] *)
    zstep. zstep.
    unhide FB. hsh_now ff HSH1 HG FB SPLO ACV SHrq SHrs SHvc. hide FB.
    shadow_chk0z SHrs 8.
    (* [comment removed for export] *)
    zstep. zstep. try clear SHvc. try clear SHrs. try clear SHrq. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    unhide FB. memset_call WRK RQwk CE1 CF3 STlo FB SPR D0 SPLO ACV. hide FB.
    lazymatch goal with X : rw_cells _ ?vq (ff + 2720) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into WRK end.
    lazymatch goal with X : stk _ ?vq (bv_unsigned sp - 12288) _ |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into STlo end.
    change (Z.to_nat 184) with 184%nat in WRK. change (0 mod 256) with 0 in WRK.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    unhide FB. memset_call VC RQvc CE1 CF3 STlo FB SPR D0 SPLO ACV. hide FB.
    lazymatch goal with X : rw_cells _ ?vq (ff + 2608) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into VC end.
    lazymatch goal with X : stk _ ?vq (bv_unsigned sp - 12288) _ |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into STlo end.
    change (Z.to_nat 72) with 72%nat in VC. change (0 mod 256) with 0 in VC.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    unhide FB. hsh_now ff HSH1 HG FB SPLO ACV SHrq SHrs SHvc. hide FB.
    shadow_chk0z SHvc 8.
    (* [comment removed for export] *)
    try clear SHvc. try clear SHrs. try clear SHrq. zstep. zstep.
    unhide FB. hsh_now ff HSH1 HG FB SPLO ACV SHrq SHrs SHvc. hide FB.
    shadow_chk0z SHvc 8.
    (* [comment removed for export] *)
    try clear SHvc. try clear SHrs. try clear SHrq. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    try clear SHrq. try clear SHrs. try clear SHvc.
    (* [comment removed for export] *)
    unhide FB. unhide DAT. unhide SHC. unhide FFH.
    lazymatch goal with MUq : munch ?W (aview A1 m1) ?ve, WMq : wmono _ (aview A1 m1) ?ve |- evt _ _ (MS _ _ _ _ _ ?ve _) =>
      rename MUq into MUe; rename WMq into WMe;
      assert (DATe : bytes_at rsegs ve data inp)
        by (eapply (bytes_at_munch LPA); [exact DAT| exact MUe| intros a Ha; cbn [outside]; keeplia Ha Dhi DJD SPLO ACV FB]);
      assert (SHCe : rw_cells rsegs ve (sh ff) [CB 540 bs])
        by (eapply (rw_cells_munch LPA); [exact SHC| exact MUe| exact WMe| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; keeplia Ha FB SPLO ACV]);
      assert (FFHe : rw_cells rsegs ve ff [CB 24 hdr])
        by (eapply (rw_cells_munch LPA); [exact FFH| exact MUe| exact WMe| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; keeplia Ha FHI SPLO ACV]);
      assert (SSBe : bytes_at rsegs ve SB (repeat (Z_to_bv 8 0) (Z.to_nat N)))
        by (eapply (bytes_at_munch LPA); [exact (proj1 STKSH1)| exact MUe| rewrite repeat_length, Z2Nat.id by exact SSN0; intros a Ha; cbn [outside]; keeplia Ha FB SSC0 SST0 SHC8 SPLO ACV]);
      pose proof (stack_shadow_again _ _ SB N _ _ _ STKSH1 SSBe eq_refl) as STKSHe; clear SSBe;
      assert (GLOBe : glob_ok LPA VIA (HENV ff) ve)
        by (eapply (glob_ok_munch LPA); [exact GLOB1| exact MUe| exact WMe|
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn [h_ff] in Ha__; cbn [outside]; keeplia Ha__ FB SPLO ACV]);
      assert (HSHe : hshadow LPA (HENV ff) ve)
        by (eapply (hshadow_munch LPA); [exact HSH1| exact MUe| exact HG|
              intros x__ Hx__; cbn [h_ff] in Hx__; unfold HFSIZE in Hx__; change (8192 / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ FB SPLO ACV]);
      assert (MPe : mapped ve (bv_unsigned sp - 12288) 12288)
        by (pose proof (stk_release rsegs _ _ _ _ STlo SPILL ltac:(keeplia SPLO ACV D0)) as Y1; cbn [cells_size csize Nat.add] in Y1;
            pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2;
            pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3; unfold SAVE in Y3; cbn [cells_size csize Nat.add] in Y3;
            eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]);
      pose proof (cframe_noalloc LPA (owned A1) (bv_unsigned sp) 12288 (HV ff) nowhere (aview A1 m1) ve _ MUe
                    ltac:(intros a Ha NO;
                          assert (Y : bv_unsigned sp - 12288 <= a < bv_unsigned sp \/ ff + 2416 <= a < ff + 4176) by (clear - NO; cbn [outside] in NO; lia);
                          destruct Y as [Y|Y]; [left; exact Y| right; right; left; rewrite fsize7; clear - Y; lia])
                    MPe ltac:(intros a X; destruct X)) as CFst;
      pose proof (cframe_seq LPA (owned A0) (owned A1) (owned A1) (bv_unsigned sp) 12288 12288 12288 (HV ff) N1 (HV ff) nowhere (HV ff) N1
                    (aview A0 m0) (aview A1 m1) ve CF01 CFst ltac:(clear; lia) ltac:(clear; lia) MPe ltac:(intros a X; exact X)
                    ltac:(intros a X; right; exact X) ltac:(intros a X; left; exact X)) as CF0e;
      clear CFst
    end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?ve _) =>
      assert (HOBJe : hobj_ok LPA VIA (HENV ff) ve);
      [ apply (rw_cells_recast rsegs _ _ _ (wrk_cells (repeat (Z_to_bv 8 0) 28) (repeat (Z_to_bv 8 0) 144))) in WRK;
          [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity | vm_compute; reflexivity];
        apply (rw_cells_recast rsegs _ _ _ (http_cells 0 (repeat (Z_to_bv 8 0) 24) (ff + 2976) (repeat (Z_to_bv 8 0) 8) (repeat (Z_to_bv 8 0) 4))) in RESP;
          [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity | cbn [cells_bytes cbytes app http_cells]; reflexivity];
        eapply hobj_ok_intro; unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_ws; cbn [h_ff vi_url VIA];
        try exact VC; try exact WRK; try exact REQ; try exact RESP;
        try (replace (ff + 3088 + 16) with (ff + 3104) by (clear; lia); exact HDb);
        reflexivity
      | ];
      assert (WS0e : ws0_obj LPA (HENV ff) ve)
        by (eapply (ws0_obj_intro LPA (HENV ff) _ wsid WSID);
            [ unfold ws_cells, ws_rec_of, h_ws, h_wsbuf; cbn [ws_id ws_s ws_f ws_r ws_e h_ff]; exact WSC
            | unfold wsemu_cells, wsemu_WS0, h_wsbuf; cbn [we_len we_ws we_first we_last h_ff]; exact WEC ])
    end.
    astop AINV1 MUe WMe CFP.
    lazymatch goal with AIq : ainv A1 ?mx ?mdx, SBq : same_but_materialized md1 ?mdx |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
      rename AIq into AINVe; rename SBq into SBMe; rename mx into me; rename mdx into mde end.
    lazymatch goal with MIq : mem_inv _ (aview A1 me) |- _ => rename MIq into MIe end.
    eapply (seg_C' A1 me mde ff d N1 flags);
      [ exact AINVe | exact MIe
      | eapply amd_frame_trans; [exact MDF1| apply amd_frame_sbm; [exact SBMe| exact MH1]]
      | exact FF1 | exact FFNZ | exact FR1 | exact LIVE1 | exact LB1 | exact NL1 | exact TC1 | exact SC1 | exact PC1 (* [comment removed for export] *) | exact LENp | exact FL
      | exact WS0e
      | split; [exact HF1| split; [exact GLOBe| split; [exact HOBJe| exact HSHe]]]
      | exact DATe | exact D0 | exact AL16 | exact STlo | exact SPILL | exact STpad | exact SAV | exact SHCe | exact FFHe
      | exact VSBJ | exact STKSHe | exact CF0e | exact FRM0 ].
  Qed.
  Local Ltac pose_S :=
    pose proof seg_S as seg_S'.   (* [comment removed for export] *)
  Local Ltac pose_X :=
    pose proof (harness_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 data inp SB N T
                  TP SP16 SPLO SPHI AINV00 MI00 ST00 STKSH00 FR00 LEN INP BUD SECC PRIMC K) as seg_X'.

  (* [comment removed for export] *)
  Local Ltac chk_rest SRC k U :=
    shadow_addr SRC k;
    lazymatch goal with |- evt ?segs ?Q _ =>
      eapply (evt_cut segs _ Q);
      [ zstep;
        let K := fresh "KS" in
        zstep; if_cases K; zify_cond K;
        [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ]
        | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow U ] ]
      | let ms := fresh "ms" in let x := fresh "junk" in
        intros ms [x ->]; simp_regs ]
    end;
    shadow_cleanup.

  Local Ltac flag_bound :=
    repeat match goal with |- context [Z.b2z (?f ?a ?c)] => destruct (f a c) end;
    match goal with |- 0 <= ?e < 16 => let v := eval vm_compute in e in change e with v end; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 K SECC PRIMC BUD INP LEN FR00 STKSH00 ST00 MI00 AINV00 SPHI SPLO SP16 TP"] Lemma seg_BF : forall (A1 : AS) (m1 : mem) (md1 : Model) (ff : Z) (d : Z) (N1 : Z -> Prop)
      (xt0 xt1 xt2 a0 a1 a2 a3 a4 a5 a6 a7 xt3 xt4 xt5 xt6 wv wc : word)
      (j0 hdr bs jcnt jcp jrq jrs jvc jwk jws jvl jhd jwb : list byte),
    let sp1 := bv_unsigned sp + -192 - d in let SHB := sh ff in let H := HENV ff in let v := aview A1 m1 in
    ainv A1 m1 md1 -> mem_inv rsegs v -> amd_frame md0 md1 ->
    a_frame A1 ff = Some (HCLASS, 0%nat) -> ff <> 0 -> (forall g, g <> ff -> a_frame A1 g = None) ->
    (forall p, a_live A1 p = a_live A0 p) -> a_livebytes A1 = a_livebytes A0 -> a_nlive A1 = a_nlive A0 ->
    a_tinycred A1 = a_tinycred A0 -> a_seccred A1 = a_seccred A0 -> a_primcred A1 = a_primcred A0 (* [comment removed for export] *) ->
    hsh_zero SHB v -> (length inp <> 0%nat -> bytes_at rsegs v data inp) ->
    0 <= d <= 16 -> sp1 mod 16 = 0 ->
    stk rsegs v (bv_unsigned sp - LIB_STACK) sp1 ->
    rw_cells rsegs v sp1 [CB 80 j0; C8 (Z_to_bv 64 ff)] ->   (* [comment removed for export] *)
    stk rsegs v (sp1 + 88) (bv_unsigned sp + -104) ->
    rw_cells rsegs v (bv_unsigned sp + -104) (SAVE ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells rsegs v SHB [CB 540 bs] ->
    rw_cells rsegs v ff [CB 24 hdr] ->
    rw_cells rsegs v (vi_bss_vsc VIA) [C8 wv] -> rw_cells rsegs v (vi_bss_cp VIA) [C8 wc] ->
    rw_cells rsegs v (ff + 1336) [CB 16 jcnt] -> rw_cells rsegs v (ff + 1536) [CB 752 jcp] ->
    rw_cells rsegs v (ff + 2416) [CB 56 jrq] -> rw_cells rsegs v (ff + 2512) [CB 56 jrs] ->
    rw_cells rsegs v (ff + 2608) [CB 72 jvc] -> rw_cells rsegs v (ff + 2720) [CB 184 jwk] ->
    rw_cells rsegs v (ff + 2976) [CB 40 jws] -> rw_cells rsegs v (ff + 3056) [CB 8 jvl] ->
    rw_cells rsegs v (ff + 3088) [CB 32 jhd] -> rw_cells rsegs v (ff + 3152) [CB 32 jwb] ->
    stack_shadow LPA v SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64) ->
    cframe LPA (owned A0) (owned A1) (bv_unsigned sp) LIB_STACK (HV ff) N1 (aview A0 m0) v ->
    (forall a, frm ff HCLASS a -> owned A0 a \/ (aview A0 m0 (Z_to_bv 64 a) = None /\ ~ in_image LPA a)) ->
    srealizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 0x87150) (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 sp1)
                                    a0 a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 ff) (Z_to_bv 64 SHB) (Z_to_bv 64 (SHB + 394)) (Z_to_bv 64 (SHB + 192)) (Z_to_bv 64 (SHB + 4))
                                    (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 ff) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 data)
                                    xt3 xt4 xt5 xt6)
                               F (Z_to_bv 64 0x87150) fc None m1 (seg_rom rsegs)) md1) T.
  Proof.
    touch_all. intros until jwb. cbv zeta.
    intros AINV1 MI1 MDF1 FF1 FFNZ FR1 LIVE1 LB1 NL1 TC1 SC1 PC1 HSZ DATc D0 AL16 STlo SPILL STpad SAV SHC FFH
           BSSV BSSC CNT16 CP REQ RESP VC WRK WS40 VSBJ HD32 WSB32 STKSH1 CF01 FRM0.
    pose_S. pose_X. prelims.
    pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    (first [ pose proof ((fframe_geom LPA A1 m1 md1 ff HCLASS 0%nat AINV1 FF1)) as dR_10; dand5 dR_10 as _ FS FLO FHI _ | destruct (fframe_geom LPA A1 m1 md1 ff HCLASS 0%nat AINV1 FF1) as (_ & FS & FLO & FHI & _) ]).
    rewrite fsize7 in FS, FHI. change (Z.min 8192 4096) with 4096 in FS.
    (first [ pose proof ((app_lin LPA ff 8192 FLO)) as dR_11; dex2 dR_11 as ix sx; rename dR_11 into FB | pose proof ((app_lin LPA ff 8192 FLO)) as dR_11; dand3 dR_11 as ix sx FB | pose proof (app_lin LPA ff 8192 FLO) as (ix & sx & FB) ]). cbn [cl_image_lo cl_image_hi LPA] in FB. change ((8192 + 7) / 8) with 1024 in FB.
    (first [ pose proof ((as_frame_ok LPA A1 m1 md1 ff HCLASS 0%nat AINV1 FF1)) as dR_12; dand3 dR_12 as _ AL4 _ | destruct (as_frame_ok LPA A1 m1 md1 ff HCLASS 0%nat AINV1 FF1) as (_ & AL4 & _) ]). rewrite fsize7 in AL4. change (Z.min 8192 4096) with 4096 in AL4.
    assert (FF0 : 4096 <= ff) by (keeplia FB).
    assert (AL8 : ff mod 8 = 0) by (clear - AL4; Z.div_mod_to_equations; lia).
    assert (FIMG : ff + 8192 <= 65536 \/ 6332416 <= ff) by (keeplia FB).
    assert (HF1 : hframe LPA A1 (HENV ff)) by (exists 0%nat; exact FF1).
    pose proof (henv_geom_of_frame LPA A1 m1 md1 (HENV ff) AINV1 HF1) as HG.
    pose proof (cenv_intro A1 m1 md1 AINV1) as CE1.
    pose proof (hvis_intro LPA A1 m1 md1 (HENV ff) AINV1 HF1) as HVIS1.
    pose proof (hshadow_of_zero ff (aview A1 m1) HSZ AL8) as HSH1. clear HSZ.
    (first [ pose proof (STKSH1) as dR_13; dand6 dR_13 as _ SSN0 SSL0 SSH0 SSC0 SST0 | pose proof STKSH1 as (_ & SSN0 & SSL0 & SSH0 & SSC0 & SST0) ]). unfold kHighMemBeg in SST0. pose proof sh_ceiling_ge as SHC8.
    pose proof BUD as [BL BN]. unfold LIB_LIVE, LIB_NLIVE in BL, BN. unfold LIB_SECC in SECC.
    cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSSC.
    ago AINV1. fold_cl_segs.
    unfold NMAX in LEN.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ; try rewrite Z.mod_small in KZ by (keeplia LEN).
    { (* [comment removed for export] *)
      assert (LEN0 : length inp = 0%nat) by (keeplia KZ LEN).
      pose proof (munch_refl [(bv_unsigned sp - 12288, bv_unsigned sp); (sh ff, sh ff + 540); (ff, ff + 24)] (aview A1 m1)) as MUx.
      pose proof (wmono_refl rsegs (aview A1 m1)) as WMx.
      assert (MP1 : mapped (aview A1 m1) (bv_unsigned sp - 12288) 12288).
      { pose proof (stk_release rsegs _ _ _ _ STlo SPILL ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
        pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
        pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3. unfold SAVE in Y3. cbn [cells_size csize Nat.add] in Y3.
        eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
      assert (CFPx : client_fp LPA A1 (aview A1 m1) [(bv_unsigned sp - 12288, bv_unsigned sp); (sh ff, sh ff + 540); (ff, ff + 24)]).
      { cbn. split; [left; split; [keeplia SPLO ACV| split; [keeplia SPR| replace (bv_unsigned sp - (bv_unsigned sp - 12288)) with 12288 by (clear; lia); exact MP1]]|].
        split; [right; right; right; first [ hotw_ex3 ff HCLASS (0%nat) | exists ff, HCLASS, 0%nat ]; split; [exact FF1| rewrite fsize7; change (8192 / 8) with 1024; clear; lia]|].
        split; [| exact I]. right; right; left. first [ hotw_ex3 ff HCLASS (0%nat) | exists ff, HCLASS, 0%nat ]. split; [exact FF1| rewrite fsize7; clear; lia]. }
      pose proof (rw_cells_merge1 _ _ _ SPILL) as SPILL88. cbn [cells_size csize Nat.add cells_bytes cbytes app] in SPILL88.
      eapply (seg_X' A1 m1 md1 (aview A1 m1) ff 0%nat d N1);
        [ exact AINV1 | exact MDF1 | exact MUx | exact WMx | exact CFPx | exact MI1 | exact FF1 | exact FFNZ | exact FR1
        | intros p n Hp; rewrite (LIVE1 p); exact Hp
        | exact LB1 | exact NL1 | exact TC1
        | rewrite SC1, LEN0; unfold LIB_SECC; cbn; clear; lia
        | rewrite PC1, LEN0; unfold LIB_PRIM; cbn; clear; lia (* [comment removed for export] *)
        | exact D0 | exact AL16 | exact STlo | exact SPILL88 | exact STpad | exact SAV | exact SHC | exact FFH | exact STKSH1 | exact CF01 | exact FRM0 ]. }
    rename KZ into LENp'. assert (LENp : length inp <> 0%nat) by (keeplia LENp' LEN). clear LENp'.
    specialize (DATc LENp). rename DATc into DAT.
    (first [ pose proof ((INP LENp)) as dR_14; dand3 dR_14 as DNZ LD0 _ | destruct (INP LENp) as (DNZ & LD0 & _) ]).
    assert (LD1 : a_live A1 data = Some (Z.of_nat (length inp))) by (rewrite (LIVE1 data); exact LD0).
    (first [ pose proof ((live_geomP LPA A1 m1 md1 data _ AINV1 LD1)) as dR_15; dand6 dR_15 as _ D16 Dlo Dhi Dimg _ | pose proof (live_geomP LPA A1 m1 md1 data _ AINV1 LD1) as (_ & D16 & Dlo & Dhi & Dimg & _) ]). unfold kHighMemBeg in Dlo.
    (first [ pose proof ((app_lin LPA data _ (proj1 Dlo))) as dR_16; dex2 dR_16 as ixd sxd; rename dR_16 into DB | pose proof ((app_lin LPA data _ (proj1 Dlo))) as dR_16; dand3 dR_16 as ixd sxd DB | pose proof (app_lin LPA data _ (proj1 Dlo)) as (ixd & sxd & DB) ]). cbn [cl_image_lo cl_image_hi LPA] in DB.
    assert (DLO : 4096 <= data) by (keeplia DB).
    pose proof (as_frame_blk_disjoint LPA A1 m1 md1 ff HCLASS 0%nat data _ AINV1 FF1 LD1) as DJD. rewrite fsize7 in DJD.
    assert (D8 : data mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
    assert (N1p : 1 <= Z.of_nat (length inp)) by (clear - LENp; lia).
    pose proof (as_live_shadow LPA A1 m1 md1 data _ AINV1 LD1) as SHDs. fold_cl_segs. fold_aview. hide SHDs.
    (* [comment removed for export] *)
    assert (CF3 : Forall const_free_ivl3 [(bv_unsigned sp - 12288, bv_unsigned sp); (6189632, 6189632 + 8); (6189664, 6189664 + 8); (ff + 1536, ff + 2288)]).
    { repeat (apply Forall_cons); try apply Forall_nil.
      - apply const_free_ivl3_high. cbn [fst]. keeplia SPLO ACV.
      - apply const_free_ivl3_of2. apply const_free_ivl2_of. unfold const_free_ivl. cbn [fst snd]. clear; lia.
      - apply const_free_ivl3_of2. apply const_free_ivl2_of. unfold const_free_ivl. cbn [fst snd]. clear; lia.
      - apply (const_free_ivl3_app ff 8192); [exact FLO| clear; lia| clear; lia]. }
    (first [ pose proof (HSH1) as dR_17; dand3 dR_17 as _ SHcp1 _ | pose proof HSH1 as (_ & SHcp1 & _) ]). unfold h_cp in SHcp1. cbn [h_ff] in SHcp1. fold_cl_segs.
    assert (RQcp : range_ok (aview A1 m1) (ff + 1536) 752).
    { eapply (shadowed_range_ok _ _ _ (ff + 1536) 752); [exact SHcp1| apply (hff_al8 (HENV ff) 1536 HG); reflexivity| keeplia FB| clear; lia| clear; lia| clear; lia
        | unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; keeplia FB
        | apply HVIS1; cbn [h_ff]; unfold HOBJ_END; clear; lia| apply HVIS1; cbn [h_ff]; unfold HOBJ_END; clear; lia]. }
    clear SHcp1.
    assert (MP1 : mapped (aview A1 m1) (bv_unsigned sp - 12288) 12288).
    { pose proof (stk_release rsegs _ _ _ _ STlo SPILL ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
      pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
      pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3. unfold SAVE in Y3. cbn [cells_size csize Nat.add] in Y3.
      eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
    assert (CFPX : client_fpx A1 (aview A1 m1) [(bv_unsigned sp - 12288, bv_unsigned sp); (6189632, 6189632 + 8); (6189664, 6189664 + 8); (ff + 1536, ff + 2288)]).
    { cbn. split; [left; split; [keeplia SPLO ACV| split; [keeplia SPR| replace (bv_unsigned sp - (bv_unsigned sp - 12288)) with 12288 by (clear; lia); exact MP1]]|].
      split; [right; right; right; right; apply img_ivl_bss_vsc|].
      split; [right; right; right; right; apply img_ivl_bss_cp|].
      split; [| exact I]. right; right; left. first [ hotw_ex3 ff HCLASS (0%nat) | exists ff, HCLASS, 0%nat ]. split; [exact FF1| rewrite fsize7; clear; lia]. }
    pose proof (munch_refl [(bv_unsigned sp - 12288, bv_unsigned sp); (6189632, 6189632 + 8); (6189664, 6189664 + 8); (ff + 1536, ff + 2288)] (aview A1 m1)) as MU.
    pose proof (wmono_refl rsegs (aview A1 m1)) as WM.
    hide DAT. hide SHC. hide FFH. hide FB. hide DB.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KD; zify_cond KD. { exfalso. apply DNZ. rewrite ?unsigned_lit in KD by (keeplia Dlo Dhi ACV). exact KD. } clear KD.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    unhide FB.
    lazymatch goal with MUq : munch ?W (aview A1 m1) ?vc |- evt _ _ (MS _ _ _ _ _ ?vc _) =>
      pose proof (asan_memset_cells_of_consts _ (proj1 (cenv_munch3 _ _ _ CE1 MUq CF3))) as AMC; fold_aview;
      icall asan_memset_spec by
        (rewrite ?unsigned_lit by (keeplia FB SPR D0 SPLO ACV);
         first [ exact CP | exact AMC | exact STlo | assumption
               | (unfold ASAN_MEMSET_STACK; keeplia D0 SPLO ACV)
               | (left; keeplia FB SPLO ACV D0)
               | (right; first [ apply (range_ok_high_munch _ _ _ _ _ RQcp MUq) ];
                  [ keeplia FB | clear; lia | keeplia FB
                  | repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; keeplia FB SPLO ACV ])
               | keeplia SPLO ACV
               | (clear; lia) ]);
      try clear AMC
    end.
    hide FB.
    lazymatch goal with X : rw_cells _ ?vq (ff + 1536) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into CP end.
    lazymatch goal with X : stk _ ?vq (bv_unsigned sp - 12288) _ |- evt _ _ (MS _ _ _ _ _ ?vq _) => rename X into STlo end.
    change (Z.to_nat 752) with 752%nat in CP. change (0 mod 256) with 0 in CP.
    (* [comment removed for export] *)
    destruct inp as [|b0 inp1] eqn:EINP; [exact (False_ind _ (LENp eq_refl))|]. rewrite <- EINP in *.
    assert (NTH0 : nth_error inp 0 = Some b0) by (rewrite EINP; reflexivity).
    assert (NTH : forall i, (i < length inp)%nat -> exists b, nth_error inp i = Some b).
    { intros i Hi. destruct (nth_error inp i) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. exfalso; clear - Hi E; lia. }
    (* [comment removed for export] *)
    unhide DAT. unhide DB. unhide FB. unhide SHDs.
    lazymatch goal with MUq : munch ?W (aview A1 m1) ?vc |- evt _ _ (MS _ _ _ _ _ ?vc _) =>
      assert (DATc : bytes_at rsegs vc data inp)
        by (eapply (bytes_at_munch LPA); [exact DAT| exact MUq| intros a Ha; cbn [outside]; keeplia Ha Dlo Dhi DJD DB SPLO ACV FB]);
      assert (SHDc : bytes_at rsegs vc (sh data) (shpat (Z.of_nat (length inp))))
        by (eapply (bytes_at_munch LPA); [exact SHDs| exact MUq| rewrite shpat_length by (clear; lia); intros a Ha; cbn [outside]; keeplia Ha Dlo Dhi DB SPLO ACV FB])
    end.
    hide DAT. hide FB. hide DB. hide SHDs.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    chk_rest SHDc 1 11.
    (* [comment removed for export] *)
    zstep.
    try clear SHDc. try clear DATc.
    unhide DAT. unhide DB. unhide FB. unhide SHDs.
    lazymatch goal with MUq : munch ?W (aview A1 m1) ?vc |- evt _ _ (MS _ _ _ _ _ ?vc _) =>
      assert (DATc : bytes_at rsegs vc data inp)
        by (eapply (bytes_at_munch LPA); [exact DAT| exact MUq| intros a Ha; cbn [outside]; keeplia Ha Dlo Dhi DJD DB SPLO ACV FB]);
      assert (SHDc : bytes_at rsegs vc (sh data) (shpat (Z.of_nat (length inp))))
        by (eapply (bytes_at_munch LPA); [exact SHDs| exact MUq| rewrite shpat_length by (clear; lia); intros a Ha; cbn [outside]; keeplia Ha Dlo Dhi DB SPLO ACV FB])
    end.
    hide DAT. hide FB. hide DB. hide SHDs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?vc _) =>
      pose proof (u8ro_read rsegs vc data inp 0 b0 (wa data) DATc NTH0 ltac:(clear; lia) ltac:(unfold wa; apply f_equal; clear; lia)) as RD0 end.
    zstep. clear RD0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    try clear SHDc. try clear DATc.
    unhide DAT. unhide DB. unhide FB. unhide SHDs.
    lazymatch goal with MUq : munch ?W (aview A1 m1) ?vc |- evt _ _ (MS _ _ _ _ _ ?vc _) =>
      assert (DATc : bytes_at rsegs vc data inp)
        by (eapply (bytes_at_munch LPA); [exact DAT| exact MUq| intros a Ha; cbn [outside]; keeplia Ha Dlo Dhi DJD DB SPLO ACV FB]);
      assert (SHDc : bytes_at rsegs vc (sh data) (shpat (Z.of_nat (length inp))))
        by (eapply (bytes_at_munch LPA); [exact SHDs| exact MUq| rewrite shpat_length by (clear; lia); intros a Ha; cbn [outside]; keeplia Ha Dlo Dhi DB SPLO ACV FB])
    end.
    hide DAT. hide FB. hide DB. hide SHDs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (evt_cut rsegs (fun ms => exists (f : Z) (zs9 za0 za1 za2 zra zt0 zt1 zt2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word), 0 <= f < 16 /\ ms =
      MS (mkR zra (Z_to_bv 64 (bv_unsigned sp + -192 - d)) gp tp zt0 zt1 zt2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - d))
              za0 za1 za2 za3 za4 za5 za6 za7
              (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (sh ff + 192)) (Z_to_bv 64 (sh ff + 4))
              (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 f) zs9 (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 data) zt3 zt4 zt5 zt6)
         F (Z_to_bv 64 0x8726c) fc None mx (seg_rom rsegs)))
    end.
    { (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { apply evt_done. hot_eexists_k18. split; [|reflexivity]. flag_bound. }
      destruct (NTH 1%nat ltac:(keeplia K1 LENp LEN)) as [b1 NTH1].
      (* [comment removed for export] *)
      zstep. zstep. if_cases KG; zify_cond KG.
      { exfalso. rewrite ?unsigned_lit in KG by (keeplia Dlo Dhi ACV). keeplia KG Dlo Dhi ACV. }
      clear KG. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) =>
        pose proof (u8ro_read rsegs my data inp 1 b1 _ DATc NTH1 ltac:(clear; lia) eq_refl) as RD1 end.
      (* [comment removed for export] *)
      zstep. shadow_chk SHDc 1 12.
      (* [comment removed for export] *)
      zstep. clear RD1. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases K2; zify_cond K2.
      { apply evt_done. hot_eexists_k18. split; [|reflexivity]. flag_bound. }
      destruct (NTH 2%nat ltac:(keeplia K1 K2 LENp LEN)) as [b2 NTH2].
      (* [comment removed for export] *)
      zstep. zstep. if_cases KG; zify_cond KG.
      { exfalso. rewrite ?unsigned_lit in KG by (keeplia Dlo Dhi ACV). keeplia KG Dlo Dhi ACV. }
      clear KG. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) =>
        pose proof (u8ro_read rsegs my data inp 2 b2 _ DATc NTH2 ltac:(clear; lia) eq_refl) as RD2 end.
      (* [comment removed for export] *)
      zstep. shadow_chk SHDc 1 12.
      zstep. clear RD2. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases K3; zify_cond K3.
      { apply evt_done. hot_eexists_k18. split; [|reflexivity]. flag_bound. }
      destruct (NTH 3%nat ltac:(keeplia K1 K2 K3 LENp LEN)) as [b3 NTH3].
      (* [comment removed for export] *)
      zstep. zstep. if_cases KG; zify_cond KG.
      { exfalso. rewrite ?unsigned_lit in KG by (keeplia Dlo Dhi ACV). keeplia KG Dlo Dhi ACV. }
      clear KG. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) =>
        pose proof (u8ro_read rsegs my data inp 3 b3 _ DATc NTH3 ltac:(clear; lia) eq_refl) as RD3 end.
      (* [comment removed for export] *)
      zstep. shadow_chk SHDc 1 12.
      zstep. clear RD3. zstep. zstep. zstep. zstep.
      apply evt_done. hot_eexists_k18. split; [|reflexivity]. flag_bound. }
    (intros ms; intros (f & zs9 & za0 & za1 & za2 & zra & zt0 & zt1 & zt2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & FLf & ->)). try clear SHDc. try clear DATc.
    (* [comment removed for export] *)
    unhide FB. unhide DAT. unhide SHC. unhide FFH. unhide DB.
    lazymatch goal with MUq : munch ?W (aview A1 m1) ?ve, WMq : wmono _ (aview A1 m1) ?ve |- evt _ _ (MS _ _ _ _ _ ?ve _) =>
      rename MUq into MUe; rename WMq into WMe;
      assert (DATe : bytes_at rsegs ve data inp)
        by (eapply (bytes_at_munch LPA); [exact DAT| exact MUe| intros a Ha; cbn [outside]; keeplia Ha Dlo Dhi DJD DB SPLO ACV FB]);
      assert (SHCe : rw_cells rsegs ve (sh ff) [CB 540 bs])
        by (eapply (rw_cells_munch LPA); [exact SHC| exact MUe| exact WMe| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; keeplia Ha FB SPLO ACV]);
      assert (FFHe : rw_cells rsegs ve ff [CB 24 hdr])
        by (eapply (rw_cells_munch LPA); [exact FFH| exact MUe| exact WMe| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; keeplia Ha FB FHI SPLO ACV]);
      assert (SSBe : bytes_at rsegs ve SB (repeat (Z_to_bv 8 0) (Z.to_nat N)))
        by (eapply (bytes_at_munch LPA); [exact (proj1 STKSH1)| exact MUe| rewrite repeat_length, Z2Nat.id by exact SSN0; intros a Ha; cbn [outside]; keeplia Ha FB SSC0 SST0 SHC8 SPLO ACV]);
      pose proof (stack_shadow_again _ _ SB N _ _ _ STKSH1 SSBe eq_refl) as STKSHe; clear SSBe;
      assert (HSHe : hshadow LPA (HENV ff) ve)
        by (eapply (hshadow_munch LPA); [exact HSH1| exact MUe| exact HG|
              intros x__ Hx__; cbn [h_ff] in Hx__; unfold HFSIZE in Hx__; change (8192 / 8) with 1024 in Hx__; cbn [outside]; keeplia Hx__ FB SPLO ACV]);
      assert (MPe : mapped ve (bv_unsigned sp - 12288) 12288)
        by (pose proof (stk_release rsegs _ _ _ _ STlo SPILL ltac:(keeplia SPLO ACV D0)) as Y1; cbn [cells_size csize Nat.add] in Y1;
            pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2;
            pose proof (stk_release rsegs _ _ _ _ Y2 SAV ltac:(keeplia SPLO ACV D0)) as Y3; unfold SAVE in Y3; cbn [cells_size csize Nat.add] in Y3;
            eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]);
      pose proof (cframe_noalloc LPA (owned A1) (bv_unsigned sp) 12288 (HV ff) nowhere (aview A1 m1) ve _ MUe
                    ltac:(intros a Ha NO;
                          assert (Y : bv_unsigned sp - 12288 <= a < bv_unsigned sp \/ (6189632 <= a < 6189632 + 8 \/ 6189664 <= a < 6189664 + 8) \/ ff + 1536 <= a < ff + 2288)
                            by (clear - NO; cbn [outside] in NO; lia);
                          destruct Y as [Y|[Y|Y]]; [left; exact Y| right; left; unfold HBSSV; cbn [vi_bss_vsc vi_bss_cp VIA]; exact Y
                                                 | right; right; left; rewrite fsize7; clear - Y; lia])
                    MPe ltac:(intros a X; destruct X)) as CFst;
      pose proof (cframe_seq LPA (owned A0) (owned A1) (owned A1) (bv_unsigned sp) 12288 12288 12288 (HV ff) N1 (HV ff) nowhere (HV ff) N1
                    (aview A0 m0) (aview A1 m1) ve CF01 CFst ltac:(clear; lia) ltac:(clear; lia) MPe ltac:(intros a X; exact X)
                    ltac:(intros a X; right; exact X) ltac:(intros a X; left; exact X)) as CF0e;
      clear CFst;
      assert (GLOBe : glob_ok LPA VIA (HENV ff) ve)
        by (eapply glob_ok_intro; cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp; cbn [h_ff];
            [exact BSSV| exact BSSC| exact CP| replace (ff + 32 + 1304) with (ff + 1336) by (clear; lia); exact CNT16])
    end.
    astopx AINV1 MUe WMe CFPX.
    lazymatch goal with AIq : ainv A1 ?mx ?mdx, SBq : same_but_materialized md1 ?mdx |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
      rename AIq into AINVe; rename SBq into SBMe; rename mx into me; rename mdx into mde end.
    lazymatch goal with MIq : mem_inv _ (aview A1 me) |- _ => rename MIq into MIe end.
    eapply (seg_S' A1 me mde ff d N1 f);
      [ exact AINVe | exact MIe
      | eapply amd_frame_trans; [exact MDF1| apply amd_frame_sbm; [exact SBMe| exact MH1]]
      | exact FF1 | exact FFNZ | exact FR1 | exact LIVE1 | exact LB1 | exact NL1 | exact TC1 | exact SC1 | exact PC1 (* [comment removed for export] *) | exact LENp | exact FLf
      | exact GLOBe | exact HSHe | exact DATe | exact D0 | exact AL16 | exact STlo | exact SPILL | exact STpad | exact SAV | exact SHCe | exact FFHe
      | exact REQ | exact RESP | exact VC | exact WRK | exact WS40 | exact VSBJ | exact HD32 | exact WSB32
      | exact STKSHe | exact CF0e | exact FRM0 ].
  Qed.
End S.
End A_Ha05e.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_ImgLow OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_WS7e8.A_WSg84 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Panhq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_WSruy.A_HKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Ha0ng.A_Ha5zr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Ha0ng.A_Haqjq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Ha0ng OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Har9f.A_Ha3dj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Har9f.A_Ha05e.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].
Ltac icall_consts_in H ::= unfold asan_memset_post, WS_Init_post, ASAN_MEMSET_STACK, WSINIT_STACK, ICPT_STACK, h_ws, h_wsbuf in H; cbn [h_ff] in H.

Lemma mod16_of_mod32_h : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (data : Z) (inp : list byte) (SB N : Z) (T : TSet).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPLO : alloc_ceiling + 65536 + LIB_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis MI00 : mem_inv rsegs (aview A0 m0).
  Hypothesis ST00 : stk rsegs (aview A0 m0) (bv_unsigned sp - LIB_STACK) (bv_unsigned sp).
  Hypothesis STKSH00 : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64).
  Hypothesis FR00 : forall ff, a_frame A0 ff = None.
  Hypothesis LEN : Z.of_nat (length inp) < NMAX.
  Hypothesis INP : length inp <> 0%nat -> data <> 0 /\ a_live A0 data = Some (Z.of_nat (length inp)) /\ bytes_at rsegs (aview A0 m0) data inp.
  Hypothesis BUD : a_livebytes A0 + LIB_LIVE (Z.of_nat (length inp)) <= LIVE_MAX /\ a_nlive A0 + LIB_NLIVE <= NLIVE_MAX.
  Hypothesis SECC : LIB_SECC (Z.of_nat (length inp)) <= a_seccred A0.
  Hypothesis PRIMC : LIB_PRIM (Z.of_nat (length inp)) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (md' : Model) (A' : AS),
      alib_post sp m0 md0 A0 inp SB N m' md' A' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj TP (conj SP16 (conj SPLO (conj SPHI (conj AINV00 (conj MI00 (conj ST00 (conj STKSH00 (conj FR00 (conj LEN (conj INP (conj BUD
      (conj SECC (conj PRIMC K)))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    pose proof (zr_word ra) as RAR; unfold inr64 in RAR;
    unfold LIB_STACK in *.

  (* [comment removed for export] *)
  Local Ltac hpeel FR N :=
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A (?c :: ?cs) =>
        let X := fresh in
        pose proof (proj1 (rw_cells_app segs m A [c] cs) FR) as X; clear FR;
        destruct X as [N FR]; cbn [cells_size csize Nat.add] in FR;
        repeat match type of FR with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in FR end;
        repeat match type of FR with
        | rw_cells _ _ (?b + ?x + ?y) _ =>
            lazymatch x with Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac end;
            lazymatch y with Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac end;
            let s := eval vm_compute in (x + y)%Z in
            replace (b + x + y)%Z with (b + s)%Z in FR by (clear; lia)
        end;
        try (lazymatch type of N with rw_cells _ _ _ [CB _ ?bs] =>
               lazymatch bs with
               | firstn _ _ => let j := fresh "junk" in set (j := bs) in N; clearbody j
               | skipn _ _ => let j := fresh "junk" in set (j := bs) in N; clearbody j
               end end)
    end.

  (* [comment removed for export] *)
  Lemma rw_cells_mk_peel : forall segs m A s sizes bs,
    rw_cells segs m A (mk_CB_cells (s :: sizes) bs) ->
    rw_cells segs m A [CB s (firstn s bs)] /\ rw_cells segs m (A + Z.of_nat s) (mk_CB_cells sizes (skipn s bs)).
  Proof.
    intros segs m A s sizes bs H. cbn [mk_CB_cells] in H.
    destruct (proj1 (rw_cells_app segs m A [CB s (firstn s bs)] (mk_CB_cells sizes (skipn s bs))) H) as [H1 H2].
    cbn [cells_size csize] in H2. rewrite Nat.add_0_r in H2. exact (conj H1 H2).
  Qed.
  Local Ltac hpeelk FR N :=
    lazymatch type of FR with
    | rw_cells ?segs ?m ?A (mk_CB_cells (?s :: ?sizes) ?bs) =>
        let X := fresh in
        pose proof (rw_cells_mk_peel segs m A s sizes bs FR) as X; clear FR;
        destruct X as [N FR];
        (let j := fresh "junk" in set (j := firstn s bs) in N; clearbody j);
        (let j := fresh "junk" in set (j := skipn s bs) in FR; clearbody j);
        repeat match type of FR with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in FR end;
        repeat match type of FR with
        | rw_cells _ _ (?b + ?x + ?y) _ =>
            lazymatch x with Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac end;
            lazymatch y with Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac end;
            let s := eval vm_compute in (x + y)%Z in
            replace (b + x + y)%Z with (b + s)%Z in FR by (clear; lia)
        end
    end.

  Local Ltac pose_BF :=
    pose proof (seg_BF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 data inp SB N T
                  TP SP16 SPLO SPHI AINV00 MI00 ST00 STKSH00 FR00 LEN INP BUD SECC PRIMC K) as seg_BF'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 K SECC PRIMC BUD INP LEN FR00 STKSH00 ST00 MI00 AINV00 SPHI SPLO SP16 TP N SB A0 AI Clg"] Lemma harness_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 data) (Z_to_bv 64 (Z.of_nat (length inp))) a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 LIB_ENTRY) fc None m0 (seg_rom rsegs)) md0) T.
  Proof.
    touch_all. intros. pose_BF. prelims. unfold LIB_ENTRY.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH0].
    pose proof STKSH00 as (_ & SSN0 & SSL0 & SSH0 & SSC0 & SST0). unfold kHighMemBeg in SST0. pose proof sh_ceiling_ge as SHC8.
    unfold NMAX in LEN.
    (* [comment removed for export] *)
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE0.
    pose proof (map_cells_of_consts _ (proj1 CE0)) as MC. pose proof (uar_cells_of_consts _ (proj1 CE0)) as [UARG UARV]. fold_aview. open_map_cells MC.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 12288, bv_unsigned sp)] (aview A0 m0)) as MU.
    pose proof (wmono_refl rsegs (aview A0 m0)) as WM.
    assert (WMAP : mapped (aview A0 m0) (bv_unsigned sp - 12288) 12288)
      by (eapply (stk_mapped (L:=LPA)); [exact ST00| keeplia SPLO ACV| clear; lia| keeplia SPR]).
    assert (CFP : client_fp LPA A0 (aview A0 m0) [(bv_unsigned sp - 12288, bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [keeplia SPLO ACV|]. split; [keeplia SPR|].
      replace (bv_unsigned sp - (bv_unsigned sp - 12288)) with 12288 by (clear; lia). exact WMAP. }
    pose proof ST00 as ST.
    ago AINV00. fold_cl_segs.
    carve_frame 104%nat ST. rename FR into FRH. carve_frame 88%nat ST. rename FR into FR0.
    (* [comment removed for export] *)
    do 15 zstep.
    (* [comment removed for export] *)
    zstep. try replace (bv_unsigned sp + -192 + 192) with (bv_unsigned sp) by (clear; lia). try rewrite (Z_to_bv_bv_unsigned sp).
    (* [comment removed for export] *)
    zstep.
    assert (AL16a : (bv_unsigned sp + -192) mod 16 = 0).
    { pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(clear; lia)) as Dv. rewrite SP16, Z.add_0_r in Dv. rewrite Dv.
      replace (16 * (bv_unsigned sp / 16) + -192) with ((bv_unsigned sp / 16 - 12) * 16) by (clear; lia). apply Z_mod_mult. }
    (first [ pose proof ((land_align32_w (bv_unsigned sp + -192) ltac:(keeplia SPR SPLO ACV) AL16a)) as dR_1; dex1 dR_1 as d; dand3 dR_1 as Dd ELAND AL32 | pose proof ((land_align32_w (bv_unsigned sp + -192) ltac:(keeplia SPR SPLO ACV) AL16a)) as dR_1; dand4 dR_1 as d Dd ELAND AL32 | destruct (land_align32_w (bv_unsigned sp + -192) ltac:(keeplia SPR SPLO ACV) AL16a) as (d & Dd & ELAND & AL32) ]). clear AL16a.
    rewrite ELAND. clear ELAND. assert (D0 : 0 <= d <= 16) by (keeplia Dd). clear Dd.
    pose proof (mod16_of_mod32_h _ AL32) as AL16.
    (* [comment removed for export] *)
    release_frame FR0 ST (bv_unsigned sp + -104).
    destruct (stk_split rsegs _ (bv_unsigned sp - 12288) (bv_unsigned sp + -192 - d + 88) _ ST ltac:(keeplia D0 SPLO ACV)) as [STl STpad]. clear ST.
    destruct (stk_carve rsegs _ _ _ 88 STl ltac:(keeplia D0 SPLO ACV)) as [STlo [jp SCR]]. clear STl.
    change (Z.of_nat 88) with 88 in STlo, SCR.
    replace (bv_unsigned sp + -192 - d + 88 - 88) with (bv_unsigned sp + -192 - d) in STlo, SCR by (clear; lia).
    (* [comment removed for export] *)
    do 9 zstep.
    (* [comment removed for export] *)
    zstep. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). if_false.
    (* [comment removed for export] *)
    zstep. zstep. try rewrite (sx32_small 4320) by (clear; lia). zstep.
    (* [comment removed for export] *)
    astop AINV00 MU WM CFP. fold_cl_segs.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, SBq : same_but_materialized md0 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename SBq into SBMa; rename mq into ma; rename mdq into mda end.
    lazymatch goal with MIq : mem_inv _ (aview A0 ma) |- _ => rename MIq into MIa end.
    assert (MPW : mapped (aview A0 ma) (bv_unsigned sp + -192 - d - ASTK) ASTK)
      by (unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact STlo | keeplia SPLO ACV | keeplia SPLO ACV D0 | keeplia D0]).
    assert (MPa : mapped (aview A0 ma) (bv_unsigned sp - 12288) 12288).
    { pose proof (stk_release rsegs _ _ _ _ STlo SCR ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
      pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
      pose proof (stk_release rsegs _ _ _ _ Y2 FRH ltac:(keeplia SPLO ACV D0)) as Y3. cbn [cells_size csize Nat.add] in Y3.
      eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
    eapply smalloc7_acall;
      [ exact AINVa | exact MIa | reflexivity
      | intros g age Hg; rewrite FR00 in Hg; discriminate Hg
      | exact TP
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact AL16
      | rewrite unsigned_lit by (clear; lia); reflexivity
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); unfold ASTK; keeplia SPLO ACV D0
      | rewrite unsigned_lit by (keeplia SPR D0 SPLO ACV); exact MPW | ].
    clear MPW.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ff A1 mB mdB fj shj
           AINV1 MI1 MDF1 LV1 LB1 TC1 NL1 SC1 PC1 NZ FN FF1 AGE NONE GEOM LFJ FFC LSH SHC FRO.
    pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    replace (ret_pc (Z_to_bv 64 0x86d54)) with (Z_to_bv 64 0x86d54) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    (first [ dand5 GEOM as FAL FLO FHI SH0 SH1 | destruct GEOM as (FAL & FLO & FHI & SH0 & SH1) ]). pose proof SH1 as SH1n. rewrite SHMAX_val in SH1n.
    (first [ pose proof ((app_lin LPA ff 8192 FLO)) as dR_3; dex2 dR_3 as ix sx; rename dR_3 into FB | pose proof ((app_lin LPA ff 8192 FLO)) as dR_3; dand3 dR_3 as ix sx FB | pose proof (app_lin LPA ff 8192 FLO) as (ix & sx & FB) ]). cbn [cl_image_lo cl_image_hi LPA] in FB. change ((8192 + 7) / 8) with 1024 in FB.
    assert (FF0 : 4096 <= ff) by (keeplia FB).
    assert (FSH : ff + 8192 <= sh ff \/ sh ff + 1024 <= ff) by (keeplia FB).
    assert (FR1 : forall g, g <> ff -> a_frame A1 g = None) by (intros g NE; exact (NONE g NE (FR00 g))).
    pose proof (cframe_of_frame_ok LPA _ _ _ _ _ _ _ _ FRO) as CF1.
    rewrite unsigned_lit in CF1 by (keeplia SPR D0 SPLO ACV). unfold ASTK in CF1.
    (* [comment removed for export] *)
    assert (AV : forall a, bv_unsigned sp - 12288 <= a < bv_unsigned sp \/ SB <= a < SB + N -> ~ nowhere a) by (intros a _ X; exact X).
    assert (SSBa : bytes_at rsegs (aview A0 ma) SB (repeat (Z_to_bv 8 0) (Z.to_nat N)))
      by (eapply (bytes_at_munch LPA); [exact (proj1 STKSH00)| exact MU| rewrite repeat_length, Z2Nat.id by exact SSN0; intros a Ha; cbn [outside]; keeplia Ha SSC0 SST0 SHC8 SPLO ACV]).
    pose proof (stack_shadow_again _ _ SB N _ _ _ STKSH00 SSBa eq_refl) as STKSHa. clear SSBa.
    lazymatch type of CF1 with cframe _ _ _ ?xsp ?win ?V ?Nn ?va ?vb =>
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn va vb CF1 (bv_unsigned sp + -192 - d)) in SCR;
      [| exact (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ va (bv_unsigned sp + -192 - d) 88 AINVa ltac:(keeplia SPLO ACV D0) ltac:(keeplia SPR D0)
                 (rw_cells_mapped (Clg:=Clg) LPA _ _ _ SCR ltac:(off_image_solve LPA)))
       | cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia D0| intros i Hi X; exact X] ];
      apply (rw_cells_ccall LPA A0 A1 xsp win V Nn va vb CF1 (bv_unsigned sp + -104)) in FRH;
      [| exact (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ va (bv_unsigned sp + -104) 104 AINVa ltac:(keeplia SPLO ACV) ltac:(keeplia SPR)
                 (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRH ltac:(off_image_solve LPA)))
       | cbn [Cells.cells_size Cells.csize Nat.add length]; split; [keeplia D0| intros i Hi X; exact X] ];
      apply (stk_ccall_any A0 A1 _ _ va vb xsp win V Nn _ _ AINVa CF1) in STpad; [| keeplia SPLO ACV D0 | intros a Ha X; exact X];
      apply (stk_ccall_any A0 A1 _ _ va vb xsp win V Nn _ _ AINVa CF1) in STlo; [| keeplia SPLO ACV D0 | intros a Ha X; exact X];
      assert (STKSH1 : stack_shadow LPA vb SB N (bv_unsigned sp - 12288) (bv_unsigned sp + 64));
      [ pose proof (crange_stack_shadow (Clg:=Clg) LPA A0 _ _ SB N _ _ AINVa STKSHa ltac:(keeplia SPLO ACV)) as CRS;
        eapply stack_shadow_again; [exact STKSHa| | reflexivity];
        apply (bytes_at_ccall LPA A0 A1 xsp win V Nn va vb CF1 SB);
        [ rewrite zeros_length, Z2Nat.id by exact SSN0; exact CRS
        | rewrite zeros_length, Z2Nat.id by exact SSN0; split; [keeplia SSC0 SST0 SHC8 SPLO ACV D0| intros i Hi X; exact X]
        | exact (proj1 STKSHa) ]
      | ];
      clear STKSHa;
      assert (DATb : length inp <> 0%nat -> bytes_at rsegs vb data inp);
      [ intros LENp; (first [ pose proof ((INP LENp)) as dR_4; dand3 dR_4 as DNZ LD0 DAT0 | destruct (INP LENp) as (DNZ & LD0 & DAT0) ]);
        (first [ pose proof ((live_geomP LPA A0 m0 md0 data _ AINV00 LD0)) as dR_5; dand5 dR_5 as _ _ Dlo Dhi _ | pose proof (live_geomP LPA A0 m0 md0 data _ AINV00 LD0) as (_ & _ & Dlo & Dhi & _) ]); unfold kHighMemBeg in Dlo;
        assert (DATa : bytes_at rsegs va data inp)
          by (eapply (bytes_at_munch LPA); [exact DAT0| exact MU| intros a Ha; cbn [outside]; keeplia Ha Dhi SPLO ACV]);
        apply (bytes_at_ccall LPA A0 A1 xsp win V Nn va vb CF1 data) in DATa;
        [ exact DATa
        | exact (crange_block (L:=LPA) A0 _ _ data _ data (Z.of_nat (length inp)) AINVa LD0 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))
        | split; [keeplia Dhi SPLO ACV D0| intros i Hi X; exact X] ]
      | ]
    end.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB rsegs _ ff [] 8184 fj [] [24; 8160]%nat FFC eq_refl) as FF2. clear FFC. cbn [mk_CB_cells app] in FF2.
    lazymatch type of FF2 with rw_cells _ ?mx _ (?c0 :: ?c1 :: nil) =>
      pose proof (proj1 (rw_cells_app rsegs mx ff [c0] [c1]) FF2) as [FFH FREST];
      cbn [cells_size csize Nat.add] in FREST; change (Z.of_nat 24) with 24 in FREST end.
    clear FF2.
    pose proof (rw_cells_split_CB rsegs _ (sh ff) [] 1024 shj [] [540; 484]%nat SHC eq_refl) as SH2. clear SHC. cbn [mk_CB_cells app] in SH2.
    lazymatch type of SH2 with rw_cells _ ?mx _ (?c0 :: ?c1 :: nil) =>
      pose proof (proj1 (rw_cells_app rsegs mx (sh ff) [c0] [c1]) SH2) as [SHC SHREST];
      cbn [cells_size csize Nat.add] in SHREST; change (Z.of_nat 540) with 540 in SHREST end.
    clear SH2.
    (* [comment removed for export] *)
    assert (MPb : mapped (aview A1 mB) (bv_unsigned sp - 12288) 12288).
    { pose proof (stk_release rsegs _ _ _ _ STlo SCR ltac:(keeplia SPLO ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
      pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2.
      pose proof (stk_release rsegs _ _ _ _ Y2 FRH ltac:(keeplia SPLO ACV D0)) as Y3. cbn [cells_size csize Nat.add] in Y3.
      eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]. }
    pose proof (cframe_noalloc LPA (owned A0) (bv_unsigned sp) 12288 (HV ff) nowhere (aview A0 m0) (aview A0 ma) _ MU
                  ltac:(intros a Ha NO; left; clear - NO; cbn [outside] in NO; lia) MPa ltac:(intros a X; destruct X)) as CFs1.
    pose proof (cframe_reframe LPA (owned A0) (owned A1) _ _ (bv_unsigned sp) 12288 _ _ _ _ CF1 ltac:(keeplia D0) ltac:(keeplia D0 SPR) MPb) as CF1'.
    pose proof (cframe_seq LPA (owned A0) (owned A0) (owned A1) (bv_unsigned sp) 12288 12288 12288 (HV ff) nowhere nowhere (frm ff HCLASS) (HV ff) nowhere
                  (aview A0 m0) (aview A0 ma) (aview A1 mB) CFs1 CF1' ltac:(clear; lia) ltac:(clear; lia) MPb ltac:(intros a X; exact X)
                  ltac:(intros a X; destruct X) ltac:(intros a X; destruct X)) as CF0B.
    clear CFs1 CF1'.
    assert (FRM0 : forall a, frm ff HCLASS a -> owned A0 a \/ (aview A0 m0 (Z_to_bv 64 a) = None /\ ~ in_image LPA a)).
    { intros a Ha. (first [ dand5 FRO as _ _ _ F4 _ | destruct FRO as (_ & _ & _ & F4 & _) ]).
      assert (Ha' : 0 <= a < 2^64) by (unfold frm in Ha; rewrite fsize7 in Ha; change (8192 / 8) with 1024 in Ha; keeplia Ha FB).
      destruct (F4 a Ha' Ha) as [O|[X|[Nn HZ]]]; [left; exact O| destruct X|].
      right. split; [| exact (proj2 HZ)].
      try change (aview_of (ahull A0) ma) with (aview A0 ma) in Nn. try unfold wz in Nn.
      rewrite <- Nn. symmetry. apply MU. cbn [outside]. rewrite unsigned_lit by (clear - Ha'; lia). unfold frm in Ha. rewrite fsize7 in Ha. change (8192 / 8) with 1024 in Ha. keeplia Ha FB SPLO ACV. }
    clear CF1 FRO AV.
    (* [comment removed for export] *)
    assert (CF3 : Forall const_free_ivl3 [(bv_unsigned sp - 12288, bv_unsigned sp); (sh ff, sh ff + 540); (ff, ff + 24)]).
    { repeat (apply Forall_cons); try apply Forall_nil.
      - apply const_free_ivl3_high. cbn [fst]. keeplia SPLO ACV.
      - apply (const_free_ivl3_frame_shadow ff 8192 540 FLO); clear; [lia| change ((8192 + 7) / 8) with 1024; lia].
      - apply (const_free_ivl3_app ff 8192); [exact FLO| clear; lia| clear; lia]. }
    pose proof (app_shadow_const_free2 LPA ff 8192 540 FLO eq_refl eq_refl ltac:(clear; lia) ltac:(clear; change ((8192 + 7) / 8) with 1024; lia)) as CF2.
    pose proof (cenv_intro A1 mB mdB AINV1) as CE1.
    assert (CFP2 : client_fp LPA A1 (aview A1 mB) [(bv_unsigned sp - 12288, bv_unsigned sp); (sh ff, sh ff + 540); (ff, ff + 24)]).
    { cbn. split; [left; split; [keeplia SPLO ACV| split; [keeplia SPR| replace (bv_unsigned sp - (bv_unsigned sp - 12288)) with 12288 by (clear; lia); exact MPb]]|].
      split; [right; right; right; exists ff, HCLASS, 0%nat; split; [exact FF1| rewrite fsize7; change (8192 / 8) with 1024; clear; lia]|].
      split; [| exact I]. right; right; left. exists ff, HCLASS, 0%nat. split; [exact FF1| rewrite fsize7; clear; lia]. }
    hide FREST. hide SHREST. hide FB.
    ago AINV1. fold_cl_segs.
    pose proof (munch_refl [(bv_unsigned sp - 12288, bv_unsigned sp); (sh ff, sh ff + 540); (ff, ff + 24)] (aview A1 mB)) as MU2.
    pose proof (wmono_refl rsegs (aview A1 mB)) as WM2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KZ; zify_cond KZ; [| exfalso; rewrite ?unsigned_lit in KZ by (keeplia FF0 FHI ACV); exact (NZ KZ)]. clear KZ.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. try rewrite (sx32_small 1102416563) by (clear; lia). zstep. zstep.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. fix_neg. zstep. zstep.
    rewrite (shr3_div8 ff). replace (ff / 8 + 2147450880) with (sh ff) by (unfold sh, kShadowOffset; clear; lia).
    (* [comment removed for export] *)
    lazymatch goal with MUq : munch ?W (aview A1 mB) ?vc |- evt _ _ (MS _ _ _ _ _ ?vc _) =>
      pose proof (cenv_munch3 _ _ _ CE1 MUq CF3) as CEc end.
    unhide FB.
    icall (poison1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (sh ff) _)
      by (first [exact SHC | exact CEc | exact CF2 | assumption | keeplia FB | keeplia FB]).
    hide FB. try clear CEc.
    lazymatch goal with X : rw_cells _ ?mx (sh ff) [CB 540 ?b] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHC end.
    (* [comment removed for export] *)
    lazymatch goal with MUq : munch ?W (aview A1 mB) ?vc |- evt _ _ (MS _ _ _ _ _ ?vc _) =>
      pose proof (cenv_munch3 _ _ _ CE1 MUq CF3) as CEc end.
    unhide FB.
    icall (unpoison _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (sh ff) _)
      by (first [exact SHC | exact CEc | exact CF2 | assumption | keeplia FB | keeplia FB]).
    hide FB. try clear CEc.
    lazymatch goal with X : rw_cells _ ?mx (sh ff) [CB 540 ?b] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into SHC end.
    lazymatch goal with X : hsh_zero _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into HSZ end.
    (* [comment removed for export] *)
    unhide FREST. unhide SHREST. unhide FB.
    lazymatch goal with MUq : munch ?W (aview A1 mB) ?ve, WMq : wmono _ (aview A1 mB) ?ve |- evt _ _ (MS _ _ _ _ _ ?ve _) =>
      rename MUq into MUe; rename WMq into WMe;
      lazymatch type of FREST with rw_cells _ _ _ ?cs =>
        assert (FRESTe : rw_cells rsegs ve (ff + 24) cs)
          by (eapply (rw_cells_munch LPA); [exact FREST| exact MUe| exact WMe|
                intros a Ha; change (Z.of_nat (cells_size cs)) with 8160 in Ha; cbn [outside]; keeplia Ha FB FHI SPLO ACV]) end;
      clear FREST;
      assert (DATe : length inp <> 0%nat -> bytes_at rsegs ve data inp)
        by (intros LENp; specialize (DATb LENp); (first [ pose proof ((INP LENp)) as dR_7; dand3 dR_7 as DNZ LD0 _ | destruct (INP LENp) as (DNZ & LD0 & _) ]);
            assert (LD1 : a_live A1 data = Some (Z.of_nat (length inp))) by (rewrite (LV1 data); exact LD0);
            (first [ pose proof ((live_geomP LPA A1 mB mdB data _ AINV1 LD1)) as dR_8; dand5 dR_8 as _ _ Dlo Dhi _ | pose proof (live_geomP LPA A1 mB mdB data _ AINV1 LD1) as (_ & _ & Dlo & Dhi & _) ]); unfold kHighMemBeg in Dlo;
            (first [ pose proof ((app_lin LPA data _ (proj1 Dlo))) as dR_9; dex2 dR_9 as ixd sxd; rename dR_9 into DB | pose proof ((app_lin LPA data _ (proj1 Dlo))) as dR_9; dand3 dR_9 as ixd sxd DB | pose proof (app_lin LPA data _ (proj1 Dlo)) as (ixd & sxd & DB) ]); cbn [cl_image_lo cl_image_hi LPA] in DB;
            pose proof (as_frame_blk_disjoint LPA A1 mB mdB ff HCLASS 0%nat data _ AINV1 FF1 LD1) as DJD; rewrite fsize7 in DJD;
            eapply (bytes_at_munch LPA); [exact DATb| exact MUe| intros a Ha; cbn [outside]; keeplia Ha Dlo Dhi DJD DB FB SPLO ACV]);
      clear DATb;
      assert (SSBe : bytes_at rsegs ve SB (repeat (Z_to_bv 8 0) (Z.to_nat N)))
        by (eapply (bytes_at_munch LPA); [exact (proj1 STKSH1)| exact MUe| rewrite repeat_length, Z2Nat.id by exact SSN0; intros a Ha; cbn [outside]; keeplia Ha FB SSC0 SST0 SHC8 SPLO ACV]);
      pose proof (stack_shadow_again _ _ SB N _ _ _ STKSH1 SSBe eq_refl) as STKSHe; clear SSBe STKSH1;
      assert (MPe : mapped ve (bv_unsigned sp - 12288) 12288)
        by (pose proof (stk_release rsegs _ _ _ _ STlo SCR ltac:(keeplia SPLO ACV D0)) as Y1; cbn [cells_size csize Nat.add] in Y1;
            pose proof (stk_merge rsegs _ _ _ _ Y1 STpad ltac:(keeplia SPLO ACV D0)) as Y2;
            pose proof (stk_release rsegs _ _ _ _ Y2 FRH ltac:(keeplia SPLO ACV D0)) as Y3; cbn [cells_size csize Nat.add] in Y3;
            eapply (stk_mapped (L:=LPA)); [exact Y3| keeplia SPLO ACV| clear; lia| keeplia SPR]);
      pose proof (cframe_noalloc LPA (owned A1) (bv_unsigned sp) 12288 (HV ff) nowhere (aview A1 mB) ve _ MUe
                    ltac:(intros a Ha NO;
                          assert (Y : bv_unsigned sp - 12288 <= a < bv_unsigned sp \/ sh ff <= a < sh ff + 540 \/ ff <= a < ff + 24) by (clear - NO; cbn [outside] in NO; lia);
                          destruct Y as [Y|[Y|Y]]; [left; exact Y| right; right; right; rewrite fsize7; change (8192 / 8) with 1024; clear - Y; lia
                                                 | right; right; left; rewrite fsize7; clear - Y; lia])
                    MPe ltac:(intros a X; destruct X)) as CFst;
      pose proof (cframe_seq LPA (owned A0) (owned A1) (owned A1) (bv_unsigned sp) 12288 12288 12288 (HV ff) nowhere (HV ff) nowhere (HV ff) nowhere
                    (aview A0 m0) (aview A1 mB) ve CF0B CFst ltac:(clear; lia) ltac:(clear; lia) MPe ltac:(intros a X; exact X)
                    ltac:(intros a X; right; exact X) ltac:(intros a X; destruct X)) as CF0e;
      clear CFst CF0B
    end.
    (* [comment removed for export] *)
    apply rw_cells_merge1 in FFH. cbn [cells_size csize Nat.add cells_bytes cbytes app] in FFH.
    apply (rw_cells_split_CB rsegs _ (ff + 24) [] 8160 _ [] [8; Z.to_nat 1304; 16; 184; 752; 128; 56; 40; 56; 40; 72; 40; 184; 72; 40; 40; 8; 24; 32; 32; 32; Z.to_nat 992; Z.to_nat 4008]%nat) in FRESTe; (* [comment removed for export] *)
      [| reflexivity].
    cbn [app] in FRESTe. rewrite app_nil_r in FRESTe.
    hpeelk FRESTe Fpad24. hpeelk FRESTe Fvsclo. hpeelk FRESTe CNT16. hpeelk FRESTe Fvschi. hpeelk FRESTe CP. hpeelk FRESTe Fg2288.
    hpeelk FRESTe REQ. hpeelk FRESTe Fg2472. hpeelk FRESTe RESP. hpeelk FRESTe Fg2568. hpeelk FRESTe VC. hpeelk FRESTe Fg2680.
    hpeelk FRESTe WRK. hpeelk FRESTe Fg2904. hpeelk FRESTe WS40. hpeelk FRESTe Fg3016. hpeelk FRESTe VSBJ. hpeelk FRESTe Fg3064.
    hpeelk FRESTe HD32. hpeelk FRESTe Fg3120. hpeelk FRESTe WSB32. hpeelk FRESTe Fwsbrest.
    clear Fpad24 Fvsclo Fvschi Fg2288 Fg2472 Fg2568 Fg2680 Fg2904 Fg3016 Fg3064 Fg3120 Fwsbrest FRESTe.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?ve _) =>
      destruct (rw_C8_any ve 6189632 ltac:(clear; lia) ltac:(clear; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [wv BSSV];
      destruct (rw_C8_any ve 6189664 ltac:(clear; lia) ltac:(clear; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [wc BSSC] end.
    astop AINV1 MUe WMe CFP2.
    lazymatch goal with AIq : ainv A1 ?mx ?mdx, SBq : same_but_materialized mdB ?mdx |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
      rename AIq into AINVe; rename SBq into SBMe; rename mx into me; rename mdx into mde end.
    lazymatch goal with MIq : mem_inv _ (aview A1 me) |- _ => rename MIq into MIe end.
    eapply (seg_BF' A1 me mde ff d nowhere);
      [ exact AINVe | exact MIe
      | eapply amd_frame_trans; [apply amd_frame_sbm; [exact SBMa| exact MH0]|]; eapply amd_frame_trans; [exact MDF1| apply amd_frame_sbm; [exact SBMe| exact MH1]]
      | exact FF1 | exact NZ | exact FR1 | exact LV1 | exact LB1 | exact NL1 | exact TC1 | exact SC1 | exact PC1 (* [comment removed for export] *)
      | exact HSZ | exact DATe | exact D0 | exact AL16 | exact STlo | exact SCR | exact STpad | exact FRH | exact SHC | exact FFH
      | cbn [vi_bss_vsc VIA]; exact BSSV | cbn [vi_bss_cp VIA]; exact BSSC
      | exact CNT16 | exact CP | exact REQ | exact RESP | exact VC | exact WRK | exact WS40 | exact VSBJ | exact HD32 | exact WSB32
      | exact STKSHe | exact CF0e | exact FRM0 ].
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem alib_call_ok_proved {Clg : Ceiling} {AI : AsanAlloc LPA} {AI16 : AsanAlloc16} : alib_call_ok.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A data inp SB N T PRE K.
  destruct PRE as [Ea0 Ea1 TP SP16 SPLO SPHI AINV MI ST STKSH ERR BV BC FR LEN INP BUD SECC PRIMC].   (* [comment removed for export] *) subst a0 a1.
  exact (harness_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A data inp SB N T
           TP SP16 SPLO SPHI AINV MI ST STKSH FR LEN INP BUD SECC PRIMC K t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Qed.
