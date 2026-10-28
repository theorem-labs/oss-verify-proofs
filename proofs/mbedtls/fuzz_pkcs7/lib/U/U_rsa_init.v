(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_rsa_init () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"].


Definition U_RSA_INIT : Z := 0x2ac30.
Notation RSA_INIT_STACK := 16 (only parsing).

Definition rsa_init_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_rsa_init ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O15.O14.O13.O12.R10.R?.R>.O11.O10.R=.R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(8.O15.)O4.(9.(2.&40.))R1.(:.O16.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.O3.(10.O3.+>8.))(<.(=.$>.$>.)(?.$>.$>.(11.(12.&40.O14.)+10.)(12.&40.O14.))(13.(=.$>.$>.))))O1.R1.)(4.(14.O16.O1.R1.)(4.(15.O16.R1.)(4.(16.O16.R1.O3.(<.$17.(18.#>8.(19.(2.&8.)(1:.&8.=)#>8.))(13.$17.)))(1;.O16.R1.O2.(12.&40.O14.)))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rsa_init_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A lo : Z) (junk : list byte),
  rw_cells segs m A [CB 232 junk] -> A mod 8 = 0 -> 0 < A ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSA_INIT_STACK -> alloc_ceiling <= lo -> bv_unsigned sp mod 16 = 0 ->
  (A + 232 <= lo \/ bv_unsigned sp <= A) ->
  mem_inv segs m -> bv_unsigned ra mod 2 = 0 ->
  a0 = Z_to_bv 64 A ->
  evt segs (rsa_init_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Theorem U_rsa_init_spec {L : heap_layout} : rsa_init_stmt usegs U_RSA_INIT.
Proof.
  unfold rsa_init_stmt, U_RSA_INIT. intros until junk. intros CH AL A0 ST LO ACL SPA DA MI RA ->.
  pose proof (rw_cells_bound _ _ _ _ CH) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
  carve_frame 16%nat ST.
  pose proof (munch_refl [(A, A + 232); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 7 zstep.
  pose proof U_memset_spec as SP. unfold memset_stmt in SP.
  eapply evt_cut; [eapply SP; rewrite ?unsigned_lit by lia; [eassumption| eassumption] |].
  cbv beta. intros ms' PO. unfold memset_post in PO. rewrite !unsigned_lit in PO by lia.
  ddestruct PO as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & MU' & WM' & MI' & CH').
  replace (ret_pc (Z_to_bv 64 0x2ac4c)) with (Z_to_bv 64 0x2ac4c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  apply (rw_cells_transport usegs [(A, A + 232)] m1 m' _ _) in FR; [| exact MU'| exact WM'| cbn; repeat split; try exact I; lia].
  apply (stk_transport_disjoint usegs [(A, A + 232)] m1 m' _ _) in ST; [| exact MU'| exact WM'| cbn; repeat split; try exact I; lia].
  assert (MU2 : munch [(A, A + 232); (bv_unsigned sp - 16, bv_unsigned sp)] m m') by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU']; intros a Ha; cbn in Ha |- *; lia]).
  assert (WM2 : wmono usegs m m') by (eapply wmono_trans; [exact WM| exact WM']).
  clear MU WM MU' WM' CH MI SP.
  zstep; if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
  zstep. zstep; if_cases K2; zify_cond K2.
  { exfalso. change 7 with (Z.ones 3) in K2. rewrite Z.land_ones in K2 by lia. change (2 ^ 3) with 8 in K2. lia. }
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold rsa_init_post. deexists 16.
  split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact MI'|].
  split; [exact CH'| exact ST].
Qed.
