(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_int P_asn1_empty.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg A_asn1_get_tag_stmt A_asn1_get_int_loops.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_asn1_empty () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.LibA.AShadow.al_wf"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "OSSVerify.KrLib.LibA.AShadow.abase"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ALazy.crange"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "asn1_empty_postA"].


Notation ASN1_EMPTY_STACK_A := 16 (only parsing).

Definition asn1_empty_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
    : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_empty ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O14.O13.O12.O11.R?.R>.R=.O10.O?.(8.&40.-60.)R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(9.O14.)O3.(:.(2.&40.))R1.(;.O15.)))(4.(<.(=.(>.$?.$?.)(10.$?.$?.(11.(12.&40.O13.)+10.)(12.&40.O13.))(13.(>.$?.$?.)))O2.R1.)(4.(14.O15.O2.R1.)(4.(15.O15.R1.)(16.O15.R1.O1.(12.&40.O13.)))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition asn1_empty_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_empty ()) "PCS,P,$?.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(17.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$?.Pp,$?.Plo,$?.P,(18.O3.R4.R3.(=.$19.(1:.(8.&40.R2.))(13.$19.)))P,(4.(1;.=R3.)(1<.R3.(1=.+2.+40.)))P,(5.$?.(1>.R5.+8.)=)P,(1<.=R6.)P,(1?.(1;.(12.&40.R28.)R7.)(1;.(20.R7.+8.)R5.))P,(16.O3.R9.R6.(12.&40.R29.))P,(1;.R7.(11.(12.&40.R2:.)+10.))P,(1;.+1000.R8.)P,(5.$?.(1>.(12.&40.R2<.)+10.)=)P,(15.O3.R=.)P,(5.$?.(1>.(12.&40.R2?.)+2.)=)P,(21.O2.)P,(22.O2.R32.)P,(23.O3.O2.R11.)P,(24.O3.O2.R34.R12.R11.+8.)P,(25.R35.R10.(11.(12.&40.R33.)R10.))P,(5.(2.&40.)R2<.(8.&40.R13.))P,(5.(2.&40.)R2<.(8.&40.R13.))(26.O3.O2.R38.(27.O3.R37.R36.R35.R34.R30.R2?.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R18.R17.R16.R13.)(6.(7.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(8.&40.O1.)R17.(:.(2.&40.))R16.(;.O3.)))")
(* [comment removed for export] *).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.

  #[using="IMG"] Lemma A_asn1_get_tag_empty_walk : asn1_empty_stmtA asegs AL A_ASN1_GET_TAG.
  Proof.
    unfold asn1_empty_stmtA, A_ASN1_GET_TAG.
    intros until lo; intros HPP PB AL1 NZ DJ ST SLO LO4 SPA MI RA ALWF CSOK AB OPP SCS -> ->.
    pose proof (rw_cells_bound _ _ _ _ HPP) as PPB; cbn [cells_size csize Nat.add] in PPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof ALWF as ALWF'; unfold al_wf in ALWF'.
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    assert (LO0 : 0 <= lo) by lia.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU; pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    rewrite Z.sub_diag. zstep.
    try (if_cases K; zify_cond K; [ exfalso; cbn in *; lia |]).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    finish; try eassumption; try lia.
    all: match goal with |- ?g => idtac "TAGE-LEFT:" g end.
  Qed.

  #[using="IMG"] Lemma A_asn1_get_int_empty_walk : asn1_empty_stmtA asegs AL A_ASN1_GET_INT.
  Proof.
    unfold asn1_empty_stmtA, A_ASN1_GET_INT.
    intros until lo; intros HPP PB AL1 NZ DJ ST SLO LO4 SPA MI RA ALWF CSOK AB OPP SCS -> ->.
    pose proof (rw_cells_bound _ _ _ _ HPP) as PPB; cbn [cells_size csize Nat.add] in PPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof ALWF as ALWF'; unfold al_wf in ALWF'.
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    assert (LO0 : 0 <= lo) by lia.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU; pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    carve_frame 16%nat ST.
    zstep. zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    zstep. zstep. zstep. clear GOT GSB. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    rewrite Z.sub_diag. zstep.
    try (if_cases K; zify_cond K; [ exfalso; cbn in *; lia |]).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    finish; try eassumption; try lia.
    all: match goal with |- ?g => idtac "INTE-LEFT:" g end.
  Qed.
End Walk.

Lemma A_asn1_get_tag_empty : forall AL, asan_img_ok AL -> asn1_empty_stmtA asegs AL A_ASN1_GET_TAG.
Proof. exact A_asn1_get_tag_empty_walk. Qed.
Lemma A_asn1_get_int_empty : forall AL, asan_img_ok AL -> asn1_empty_stmtA asegs AL A_ASN1_GET_INT.
Proof. exact A_asn1_get_int_empty_walk. Qed.
