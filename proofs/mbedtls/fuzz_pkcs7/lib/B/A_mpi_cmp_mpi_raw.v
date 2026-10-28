(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_mpi_cmp_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
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
Ltac2 gd_tbl_A_mpi_cmp_mpi_raw () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_mpi.mpi_cmp_postA"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Definition mpi_cmp_mpi_raw_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi_raw ()) "PCS,P,$0.SpPra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))Plo,$0.PX,$0.PP,$0.Pn,$0.Psg,$0.Pxs,(4.(1.&40.))Ppad,(1.&40.)PY,$0.PQ,$0.Pn',$0.Psg',$0.Pys,(4.(1.&40.))Ppad',(1.&40.)P,(5.O3.R>.R<.(6.$7.(8.(9.&40.R;.))(6.$7.(:.(9.&40.R9.))(6.$7.(:.(9.&40.R:.))(6.$7.(;.R7.)(<.$7.))))))P,(=.O3.R?.R<.(>.R9.))P,(?.$0.(10.(11.(1.&40.)R:.))R<.)P,(12.(13.=R=.)(13.R=.+2710.))P,(14.(?.$0.R=.+1.)(?.$0.R=.-1.))P,(14.(?.$0.R?.=)(12.(15.=R10.)(?.$0.(16.R10.+4.)=)))P,(?.$0.(16.R12.+8.)=)P,(15.=R13.)P,(5.O3.R16.R>.(6.$7.(8.(9.&40.R=.))(6.$7.(:.(9.&40.R;.))(6.$7.(:.(9.&40.R<.))(6.$7.(;.R9.)(<.$7.))))))P,(=.O3.R17.R>.(>.R;.))P,(?.$0.(10.(11.(1.&40.)R<.))R>.)P,(12.(13.=R?.)(13.R?.+2710.))P,(14.(?.$0.R?.+1.)(?.$0.R?.-1.))P,(14.(?.$0.R11.=)(12.(15.=R12.)(?.$0.(16.R12.+4.)=)))P,(?.$0.(16.R14.+8.)=)P,(15.=R15.)P,(17.O3.R1>.)P,(18.O2.)P,(19.O2.R42.)P,(1:.O3.O2.R21.)P,(1;.O3.O2.R44.R22.R20.+10.)P,(1;.O3.O2.R45.R23.R1;.+10.)P,P,(13.+1.R20.)(1;.O3.O2.R47.R25.R22.(1<.+4.R21.))P,P,(13.+1.R1;.)(1;.O3.O2.R48.R26.R1=.(1<.+4.R1<.))P,(1=.O3.R26.R25.(1>.&40.R46.))P,(13.=R26.)P,(13.R27.(1?.(1>.&40.R48.)+10.))P,(?.$0.(16.(1>.&40.R49.)+10.)=)P,(20.R4<.R29.(1?.(1>.&40.R4:.)R29.))P,(14.(13.(21.R29.+10.)R2:.)(13.(1>.&40.R4;.)R29.))P,(14.(13.(21.R24.+10.)R2;.)(13.(1>.&40.R4<.)R24.))P,P,(13.+1.R29.)(14.(13.(21.R2;.(1<.+4.R2:.))R2=.)(13.(1>.&40.R4>.)R2;.))P,P,(13.+1.R24.)(14.(13.(21.R26.(1<.+4.R25.))R2>.)(13.(1>.&40.R4?.)R26.))P,(?.(1.&40.)R47.(9.&40.R2=.))P,(?.(1.&40.)R47.(9.&40.R28.))(22.O3.O2.R53.(23.O3.R52.R51.R50.R4?.R4;.R4:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R33.R32.(24.(1?.(1<.R2<.(25.R2;.R2=.))(1<.R26.(25.R25.R27.))))R30.R31.)(26.(27.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R33.(9.&40.O1.)R32.(28.(1.&40.))R31.(29.O3.)))")
(* [comment removed for export] *).

Theorem A_mpi_cmp_mpi_raw_spec : forall AL, asan_img_ok AL -> mpi_cmp_mpi_raw_stmtA asegs AL A_MPI_CMP_MPI_E.
Proof.
  intros AL IMG. unfold mpi_cmp_mpi_raw_stmtA, A_MPI_CMP_MPI_E. intros until pad'.
  intros CX BX LX NX SX PBX ALX X0 CY BY LY NY SY PBY ALY Y0 MI ALWF CSOK AB OX OY OP OQ ST LO0 SLO SPA SCS XS YS PS QS -> ->.
  pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  pose proof (rw_cells_bound _ _ _ _ CX) as ABX. pose proof (rw_cells_bound _ _ _ _ CY) as ABY. cbn [cells_size csize Nat.add] in ABX, ABY.
  pose proof (bytes_at_bound _ _ _ _ BX) as PBB. rewrite u32s_length in PBB.
  pose proof (bytes_at_bound _ _ _ _ BY) as QBB. rewrite u32s_length in QBB.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  zstep. zstep.
  eapply b_main; try eassumption; try reflexivity.
  all: try (clear - ABX; lia).
  all: try (clear - ABY; lia).
  all: try (clear - NX LX PBB PBX; lia).
  all: try (clear - NY LY QBB PBY; lia).
  all: try (intros N1; destruct (PS N1); [left| right]; assumption).
  all: try (intros N1; destruct (QS N1); [left| right]; assumption).
  all: try (intros N1; eapply (aobj_munch asegs AL CS CSOK [(lo, bv_unsigned sp)] m);
            [unfold w_client; apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]
            | exact MU | first [exact (OP N1) | exact (OQ N1)]]).
  all: match goal with |- ?g => idtac "CMPRAW-LEFT:" g end.
Qed.
