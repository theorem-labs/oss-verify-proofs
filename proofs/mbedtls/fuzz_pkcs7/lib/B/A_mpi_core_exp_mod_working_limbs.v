(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_exp_mod_working_limbs.
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
Ltac2 gd_tbl_A_mpi_core_exp_mod_working_limbs () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_core_exp_mod_working_limbs.mpi_core_exp_mod_working_limbs_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "mpi_core_exp_mod_working_limbs_stmtA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "A_MPI_CORE_EXP_MOD_WORKING_LIMBS"].


Definition A_MPI_CORE_EXP_MOD_WORKING_LIMBS : Z := 0x0a5e08.

Definition mpi_core_exp_mod_working_limbs_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod_working_limbs ()) "PCS,P,$0.SpPra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))Pan,$0.Pen,$0.P,(4.(5.=R2.)(5.R2.+2710.))P,(4.(5.=R2.)(5.R2.+2710.))P,(6.O3.R5.)P,(7.O2.)P,(8.O2.R29.)P,(9.(1.&40.)R20.(:.&40.R7.))P,(9.(1.&40.)R20.(:.&40.R7.))(;.O3.O2.R2<.(<.O3.R2;.R2:.R29.R28.R24.R23.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R<.R;.R9.R8.R:.)(=.(>.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(:.&40.O1.)R;.(?.(1.&40.))R:.(10.O3.)))")
(* [comment removed for export] *).

Lemma A_mpi_core_exp_mod_working_limbs_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod_working_limbs ()) "PAL,$11.P,(12.R1.)(13.$14.R2.$15.)")
(* [comment removed for export] *).
Proof.
  intros AL IMG. unfold mpi_core_exp_mod_working_limbs_stmtA, A_MPI_CORE_EXP_MOD_WORKING_LIMBS.
  intros until en. intros Han Hen MI ALWF CSOK -> ->.
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
  zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  all: repeat (lazymatch goal with |- evtA _ _ _ _ (MS _ _ (ret_pc _) _ _ _ _) => fail | _ => zstep end).
  all: finish; unfold exp_mod_working_limbs, exp_mod_welem;
       first [ replace (79 <? 32 * en) with false by (symmetry; apply Z.ltb_ge; lia)
             | replace (79 <? 32 * en) with true by (symmetry; apply Z.ltb_lt; lia) ];
       f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; lia.
Qed.
