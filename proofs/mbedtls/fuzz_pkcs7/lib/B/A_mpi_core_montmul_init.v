(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_montmul_init.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_mpi_core_montmul_init () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_MONTMUL_INIT_STACK_A"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_core_montmul_init_postA"].


Definition A_MPI_CORE_MONTMUL_INIT : Z := 0xa5414.
Definition MPI_CORE_MONTMUL_INIT_STACK_A : Z := 16.

Definition mpi_core_montmul_init_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_montmul_init ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O14.O13.O12.O11.R10.R?.R>.O10.O?.R=.R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(8.O14.)O3.(9.(2.&40.))R1.(:.O15.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.O13.)$12.)(11.&40.O13.))(13.(=.$>.$>.)))O1.R1.)(4.(14.O15.O1.R1.)(4.(15.O15.R1.)(16.O15.R1.O2.(11.&40.O13.))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_montmul_init_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_montmul_init ()) "PCS,P,$>.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(17.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PN,$>.Plo,$>.Pns,(18.(2.&40.))P,(19.O3.R4.R3.(1:.R1.))P,(1;.+1.(1<.(1=.(2.&40.)R2.)))P,(5.$>.(1>.R5.+4.)=)P,(1?.=R6.)P,(15.O3.R8.)P,(20.O2.)P,(21.O2.R2<.)P,(22.O3.O2.R;.)P,(23.O3.O2.R2>.R<.R;.+4.)P,(16.O3.R=.R;.(11.&40.R2=.))P,(1;.R<.(10.(11.&40.R2>.)$12.))P,(5.$>.(1>.(11.&40.R2?.)+10.)=)P,(24.R32.R>.(10.(11.&40.R30.)R>.))P,(25.(1;.(26.R10.(27.+4.(1<.(1=.(2.&40.)R>.))))(10.(11.&40.R31.)$12.))(1;.(11.&40.R31.)R10.))P,(5.(2.&40.)R2:.(28.&40.R11.))(29.O3.O2.R35.(2:.O3.R34.R33.R32.R31.R2=.R2<.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R15.R14.R11.R13.)(6.(7.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(28.&40.O1.)R14.(9.(2.&40.))R13.(:.O3.)))")
(* [comment removed for export] *).

Local Ltac ifF := lazymatch goal with |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
  replace c with false; [cbv iota | symmetry; unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec] end.

Lemma A_mpi_core_montmul_init_spec : forall AL, asan_img_ok AL -> mpi_core_montmul_init_stmtA asegs AL A_MPI_CORE_MONTMUL_INIT.
Proof.
  intros AL IMG. unfold mpi_core_montmul_init_stmtA, A_MPI_CORE_MONTMUL_INIT.
  intros until ns. intros HN LN ALN NZN MI ALWF CSOK ABS ON ST LO SPA SCS SN ->.
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  unfold MPI_CORE_MONTMUL_INIT_STACK_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (u32ro_bound _ _ _ _ HN) as NB. pose proof (proj1 ST) as LO0.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  zstep. zstep.
  assert (NL3 : Z.land N 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact ALN).
  zstep. first [ifF | idtac]. zstep. rewrite ?NL3. zstep. first [ifF | idtac]. clear NL3.
  pose proof (abase_got _ _ _ ABS) as GOT. pose proof (abase_gsb _ _ _ ABS) as GSB. rewrite (proj1 IMG) in GOT.
  (* [comment removed for export] *)
  zstep. zstep. zstep. clear GOT GSB.
  (* [comment removed for export] *)
  zstep. zstep. shadow_chk ON N 4.
  rd HN 0.
  vstep 11%positive. vstep 11%positive. vstep 11%positive. vstep 11%positive. vstep 12%positive. zstep.
  vstep 12%positive. vstep 11%positive. vstep 12%positive. vstep 13%positive. vstep 11%positive. vstep 10%positive.
  vstep 10%positive. vstep 10%positive.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  finish.
  all: match goal with |- ?g => idtac "LEFT:" g end.
Qed.
