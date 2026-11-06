(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX MpiCoreAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg A_mpi_cmp_mpi A_mpi_cmp_int.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_cmp_int_z0 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.LibA.AShadow.al_wf"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "OSSVerify.KrLib.LibA.AShadow.abase"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "OSSVerify.KrLib.A.A_mpi_cmp_mpi.mpi_cmp_postA"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].


(* [comment removed for export] *)
Definition mpi_cmp_int_z0_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_int_z0 ()) "PCS,P,$0.SpPra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))PX,$0.PP,$0.Psg,$0.Ppad,(1.&40.)Plo,$0.P,(4.O3.R6.R5.(5.R4.(6.&40.R3.)=R2.))P,(7.$0.(8.R6.+8.)=)P,(9.=R7.)P,(:.(;.R8.+10.)(<.+2.+40.))P,(=.O3.R:.)P,(>.O2.)P,(?.O2.R2>.)P,(10.O3.O2.R=.)P,(11.O3.O2.R30.R>.R=.+10.)P,(12.O3.R?.R:.(13.&40.R2?.))P,(:.=R;.)P,(:.R<.(14.(13.&40.R31.)+10.))P,(7.$0.(8.(13.&40.R32.)+10.)=)P,(15.R35.R>.(14.(13.&40.R33.)R>.))P,(16.(:.(;.R13.+10.)R?.)(:.(13.&40.R34.)R13.))P,(7.(1.&40.)R2=.(6.&40.R14.))P,(7.(1.&40.)R2=.(6.&40.=))(17.O3.O2.R39.(18.O3.R38.R37.R36.R35.R31.R30.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R19.R18.=R12.R17.)(19.(1:.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(6.&40.O1.)R18.(1;.(1.&40.))R17.(1<.O3.)))")
(* [comment removed for export] *).

Theorem A_mpi_cmp_int_z0_spec : forall AL, asan_img_ok AL -> mpi_cmp_int_z0_stmtA asegs AL A_MPI_CMP_INT_E.
Proof.
  intros AL IMG. unfold mpi_cmp_int_z0_stmtA, A_MPI_CMP_INT_E. intros until lo. intros CX XAL X0 XB MI ALWF CSOK AB OX ST LO0 SLO SPA SCS DA -> ->.
  pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  unfold mpi_cells in CX.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  zstep. zstep.
  (* [comment removed for export] *)
  pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
  zstep. zstep. zstep. clear GOT GSB.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  shadow_chk OX (X + 10) 2.
  (* [comment removed for export] *)
  zstep. change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  zstep.
  zstep; try (if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]).
  (* [comment removed for export] *)
  zstep; try (if_cases K1; zify_cond K1; [exfalso; cbv in K1; lia|]).
  zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evtA_done. unfold mpi_cmp_postA. deexists 15.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
  all: match goal with |- ?g => idtac "Z0-LEFT:" g end.
Qed.
