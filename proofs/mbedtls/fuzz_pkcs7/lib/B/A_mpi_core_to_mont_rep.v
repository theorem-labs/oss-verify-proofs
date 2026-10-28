(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_montmul.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_mpi_core_montmul.
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
Ltac2 gd_tbl_A_mpi_core_to_mont_rep () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_montmul.MPI_CORE_MONTMUL_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_montmul.mpi_core_montmul_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_montmul.A_ASAN_MEMSET_MM"; "mpi_core_to_mont_rep_stmtA"; "A_MPI_CORE_TO_MONT_REP"].


Definition A_MPI_CORE_TO_MONT_REP : Z := 0x0a66b4.   (* [comment removed for export] *)

Definition mpi_core_to_mont_rep_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_to_mont_rep ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))PX,$6.PA,$6.PRR,$6.PN,$6.Pan,$6.PT,$6.Plo,$6.Pxs,(1.(3.&40.))Pys,(1.(3.&40.))Prs,(1.(3.&40.))Pns,(1.(3.&40.))Pts,(1.(3.&40.))P,(7.O4.O3.O2.R31.R30.R2?.R=.)P,(8.O4.R>.R=.R6.)P,(9.O4.R?.R=.(:.R6.))P,(9.O4.R10.R=.(:.R6.))P,(9.O4.R11.R=.(:.R6.))P,(8.O4.R12.R<.R6.)P,(;.(<.+1.R>.)(<.R>.+1387.))P,(<.R?.(=.(>.(3.&40.)R<.)))P,(<.R10.(=.(>.(3.&40.)R<.)))P,(<.R11.(=.(>.(3.&40.)R<.)))P,(<.R12.(=.(>.(3.&40.)R<.)))P,(<.(?.(10.+2.R13.)+1.)(=.(>.(3.&40.)R<.)))P,(11.(<.(?.R18.(10.+4.(=.(>.(3.&40.)R11.))))R13.)(<.(?.R13.(10.+4.(=.(>.(3.&40.)R=.))))R18.))P,(11.(<.(?.R18.(10.+4.(=.(>.(3.&40.)R11.))))R14.)(<.(?.R14.(10.+4.(=.(>.(3.&40.)R>.))))R18.))P,(11.(<.(?.R18.(10.+4.(=.(>.(3.&40.)R11.))))R15.)(<.(?.R15.(10.+4.(=.(>.(3.&40.)R?.))))R18.))P,(11.(<.(?.R18.(10.+4.(=.(>.(3.&40.)R11.))))R16.)(<.(?.R16.(10.+4.(=.(>.(3.&40.)R10.))))R18.))P,(11.(<.(?.R19.(10.+4.(=.(>.(3.&40.)R12.))))R1<.)(<.(?.R1<.(10.+4.(=.(>.(3.&40.)R15.))))R19.))P,(12.$6.(13.R1=.+4.)=)P,(12.$6.(13.R1=.+4.)=)P,(12.$6.(13.R1=.+4.)=)P,(12.$6.(13.R1=.+4.)=)P,(12.$6.(13.R1<.+4.)=)P,(14.=R22.)P,(14.=R22.)P,(14.=R22.)P,(14.=R22.)P,(14.=R21.)P,(14.(?.R27.(10.+4.(=.(>.(3.&40.)R20.))))(15.+2.+40.))P,(14.(?.R27.(10.+4.(=.(>.(3.&40.)R20.))))(15.+2.+40.))P,(14.(?.R27.(10.+4.(=.(>.(3.&40.)R20.))))(15.+2.+40.))P,(14.(?.R27.(10.+4.(=.(>.(3.&40.)R20.))))(15.+2.+40.))P,(14.(?.R26.(10.+4.(=.(>.(3.&40.)R20.))))(15.+2.+40.))P,(16.O4.R2=.R26.(17.&40.R4=.))P,(<.(18.O3.)R27.)P,(<.R28.(19.(19.(17.&40.R4?.)$1:.)(1;.O3.)))P,(<.(17.&40.R50.)(1<.O4.O3.O2.R54.))P,(12.$6.(13.(17.&40.R51.)+10.)=)P,(11.(<.(?.R31.(10.+4.(=.(>.(3.&40.)R2:.))))R2;.)(<.(17.&40.R52.)R31.))P,(11.(<.(?.R31.(10.+4.(=.(>.(3.&40.)R2:.))))R2<.)(<.(17.&40.R53.)R31.))P,(11.(<.(?.R31.(10.+4.(=.(>.(3.&40.)R2:.))))R2=.)(<.(17.&40.R54.)R31.))P,(11.(<.(?.R31.(10.+4.(=.(>.(3.&40.)R2:.))))R2>.)(<.(17.&40.R55.)R31.))P,(11.(<.(?.R30.(10.+4.(=.(>.(3.&40.)R2:.))))R2?.)(<.(17.&40.R56.)R30.))P,(1=.(1>.O3.)(1?.$2.R5:.(20.R59.))(18.O3.)(1<.O4.O3.O2.R5;.)R36.(10.+4.R32.))P,(1=.(1>.O3.)(1?.$2.R5;.(20.R5:.))(18.O3.)(1<.O4.O3.O2.R5<.)R32.(10.+4.(?.(10.+2.R33.)+1.)))P,(21.O4.R39.)P,(12.$6.(13.(17.&40.R5;.)+2.)=)P,(22.O4.(23.O3.)(24.O4.O3.O2.R5?.)R3;.R3:.(10.+4.R36.))P,(22.O4.(23.O3.)(24.O4.O3.O2.R60.)R3<.R3:.(10.+4.R37.))P,(22.O4.(23.O3.)(24.O4.O3.O2.R61.)R3=.R3:.(10.+4.R38.))P,(22.O4.(23.O3.)(24.O4.O3.O2.R62.)R3>.R3:.(10.+4.R39.))P,(22.O4.(23.O3.)(24.O4.O3.O2.R63.)R3?.R39.(10.+4.(?.(10.+2.R3:.)+1.)))P,(12.(3.&40.)R58.(25.&40.R3?.))P,(12.(3.&40.)R58.(25.&40.R3?.))P,(12.(3.&40.)R58.(25.&40.R3>.))P,(12.(3.&40.)R58.(25.&40.R3>.))P,(12.(3.&40.)R57.(25.&40.R41.))P,(12.(3.&40.)R57.(25.&40.R3?.))(26.O4.(23.O3.)(24.O4.O3.O2.R6:.)(27.O4.O3.O2.R6:.R69.R68.R67.R66.R65.R64.R60.R5?.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R48.R47.R45.R41.R40.R3>.R3:.R3?.R46.)(28.(29.R67.R66.R65.R64.R63.R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.)R48.(25.&40.O1.)R47.(2:.(3.&40.))R46.(2;.O4.)))")
(* [comment removed for export] *).

Lemma A_mpi_core_to_mont_rep_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_to_mont_rep ()) "PR,$2<.PHIA,(2=.$2>.R1.)P,(2?.(23.R2.))P,(12.$6.(30.R3.)$31.)P,(<.=(1;.R4.))(32.$2>.R5.R4.$33.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG AMS NEED0. unfold mpi_core_to_mont_rep_stmtA, A_MPI_CORE_TO_MONT_REP.
  intros until ts. intros HH HX HA HR HN HT Han LX LA LR LN LT D1 D2 D3 D4 D5 AL1 AL2 AL3 AL4 AL5 NZ1 NZ2 NZ3 NZ4 NZ5 T1 T2 T3 T4 T5
         ST LOS LO TOP SPA S1 S2 S3 S4 S5 CWX CWT MI RA OX OA ORR ON OT -> -> -> -> -> ->.
  pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  pose proof (A_mpi_core_montmul_spec R HIA IMG AMS NEED0) as SP. unfold mpi_core_montmul_stmtA, A_MPI_CORE_MONTMUL in SP.
  eapply SP with (B := RR) (bn := an) (zs := rs) (ys := ys) (ns := ns); try reflexivity; try eassumption; try lia.
Qed.
