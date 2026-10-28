(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX Image Statics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_oidv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_oid () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.P.P_oid.MBEDTLS_ERR_OID_NOT_FOUND"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_bcmp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "oid_lookup1_postA"; "oid_lookup2_postA"; "RocqVerifyHarness.AgentSubmission.P.P_oidv.oid_vres"; "oid_lookup1v_postA"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "oid_lookup1v_stmtA"; "oid_lookup1_stmtA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_gsb"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.AGSB"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memcmp_i"; "A_WRAP_BCMP"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_shadow_ok"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_cs"].


Definition A_WRAP_BCMP : Z := 0x58704.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition oid_lookup1_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (EXT lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_oid ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.(2.&40.)Lv,(2.&40.)(5.(6.$0.R13.(7.(8.O15.O14.O13.O12.R12.R11.R10.O11.O10.R?.R>.R=.R<.R;.R:.R9.R8.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R7.R6.R5.R4.)O5.(9.O15.)O4.(:.(2.&40.))R3.(;.O1;.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O3.(10.O3.+4.))(=.(>.$4.$4.)(?.$4.$4.O2.(11.&40.O14.))(12.(>.$4.$4.))))O1.R3.)(5.(13.O1;.O1.R3.)(5.(14.O1;.R3.)(5.(6.(2.&40.)R?.(15.&40.R2.))(5.(16.(6.$4.R2.=)(6.$4.R2.$17.))(5.(18.O1;.R3.O3.(=.$19.(1:.R1.)(12.$19.)))(5.(1;.O1;.R3.O2.(11.&40.O14.))(1<.O1;.O1:.O19.O18.O17.O16.R3.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition oid_lookup1_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY STACK : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_oid ()) "Ph,(1=.O5.O4.O3.)PLB,(1>.$1?.)PLF,(1>.$1?.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))POID,$4.PEXT,$4.PP,$4.PLEN,$4.Plo,$4.Ptg,(2.&40.)Ppd,(2.&40.)Pv0,(2.&40.)Pxs,(1>.(2.&8.))P,(1<.O5.O4.O3.R2>.R2=.R2<.R:.)P,(18.O5.R;.R:.(21.R5.R4.R7.R8.))P,(22.O5.R<.R9.R3.)P,(6.$4.(23.(24.(2.&8.)R4.))R9.)P,(18.O5.R>.R<.(=.$19.(1:.R6.)(12.$19.)))P,(16.(25.(10.R=.+4.)R>.)(25.(10.R>.+18.)R=.))P,(16.(25.(10.R>.+4.)R=.)(25.(10.R=.R<.)R>.))P,(6.$4.(26.R10.+8.)=)P,(6.$4.(26.R10.+4.)=)P,(27.=R12.)P,(27.=R12.)P,(27.=R12.)P,(1;.O5.R16.R11.(11.&40.R36.))P,(25.(28.O4.)R12.)P,(25.R13.(29.(29.(11.&40.R38.)O1.)(2:.O4.)))P,(25.(11.&40.R39.)(2;.O5.O4.O3.R3=.))P,(6.$4.(26.(11.&40.R3:.)+10.)=)P,(16.(25.(10.R1:.+18.)R16.)(25.(11.&40.R3;.)R1:.))P,(16.(25.(10.R1:.+4.)R17.)(25.(11.&40.R3<.)R1:.))P,(16.(25.(10.R1:.R19.)R18.)(25.(11.&40.R3=.)R1:.))P,(25.(10.(10.R1;.R1:.)+8.)(2<.+2.+2?.))P,(2=.(2>.O4.)(2?.$1?.R42.(30.R41.))(28.O4.)(2;.O5.O4.O3.R43.)R1=.+4.)P,(14.O5.R20.)P,(31.O5.(32.O4.)(33.O5.O4.O3.R45.)R21.R20.+18.)P,(31.O5.(32.O4.)(33.O5.O4.O3.R46.)R22.R1?.R1>.)P,(31.O5.(32.O4.)(33.O5.O4.O3.R47.)R23.R21.+4.)P,(6.(2.&40.)R3<.(15.&40.R23.))P,(6.(2.&40.)R3<.(15.&40.R23.))(34.O5.(32.O4.)(33.O5.O4.O3.R4:.)(35.O5.O4.O3.R4:.R49.R48.R47.R46.R45.R44.R40.R3?.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R28.R27.R24.R21.R26.)(7.(8.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.)R28.(15.&40.O2.)R27.(:.(2.&40.))R26.(;.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition oid_lookup2_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E1 E2 lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_oid ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.(2.&40.)Lv1,(2.&40.)(1.(2.&40.)Lv2,(2.&40.)(5.(6.$0.R14.(7.(8.O16.O15.O14.O13.R13.R12.R11.O12.O11.R10.R?.R>.R=.R<.R;.R:.R9.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R8.R7.R6.R5.)O6.(9.O16.)O5.(:.(2.&40.))R4.(;.O1<.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O4.(10.O4.+4.))(=.(>.$4.$4.)(?.$4.$4.O3.(10.O3.+4.))(=.(>.$4.$4.)(?.$4.$4.O2.(11.&40.O15.))(12.(>.$4.$4.)))))O1.R4.)(5.(13.O1<.O1.R4.)(5.(14.O1<.R4.)(5.(6.(2.&40.)R10.(15.&40.R3.))(5.(16.(6.$4.R3.=)(6.$4.R3.$17.))(5.(18.O1<.R4.O4.(=.$19.(1:.R2.)(12.$19.)))(5.(18.O1<.R4.O3.(=.$19.(1:.R1.)(12.$19.)))(5.(1;.O1<.R4.O2.(11.&40.O15.))(1<.O1<.O1;.O1:.O19.O18.O17.R4.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition oid_lookup2_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY STACK : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_oid ()) "Ph,(1=.O5.O4.O3.)PLB,(1>.$1?.)PLF,(1>.$1?.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))POID,$4.PE1,$4.PE2,$4.PP,$4.PLEN,$4.Plo,$4.Ptg,(2.&40.)Ppd,(2.&40.)Pv1,(2.&40.)Pv2,(2.&40.)Pxs,(1>.(2.&8.))P,(1<.O5.O4.O3.R30.R2?.R2>.R<.)P,(18.O5.R=.R<.(21.R6.R5.R8.R9.))P,(22.O5.R>.R:.R3.)P,(6.$4.(23.(24.(2.&8.)R4.))R:.)P,(18.O5.R10.R>.(=.$19.(1:.R7.)(12.$19.)))P,(18.O5.R11.R>.(=.$19.(1:.R7.)(12.$19.)))P,(16.(25.(10.R10.+4.)R11.)(25.(10.R11.+18.)R10.))P,(16.(25.(10.R11.+4.)R?.)(25.(10.R?.R>.)R11.))P,(16.(25.(10.R11.+4.)R13.)(25.(10.R13.+18.)R11.))P,(16.(25.(10.R12.+4.)R11.)(25.(10.R11.R10.)R12.))P,(16.(25.(10.R14.+4.)R13.)(25.(10.R13.+4.)R14.))P,(6.$4.(26.R16.+8.)=)P,(6.$4.(26.R16.+4.)=)P,(6.$4.(26.R16.+4.)=)P,(27.=R19.)P,(27.=R19.)P,(27.=R19.)P,(27.=R19.)P,(1;.O5.R1>.R18.(11.&40.R3>.))P,(25.(28.O4.)R19.)P,(25.R1:.(29.(29.(11.&40.R40.)O1.)(2:.O4.)))P,(25.(11.&40.R41.)(2;.O5.O4.O3.R45.))P,(6.$4.(26.(11.&40.R42.)+10.)=)P,(16.(25.(10.R22.+18.)R1=.)(25.(11.&40.R43.)R22.))P,(16.(25.(10.R22.+4.)R1>.)(25.(11.&40.R44.)R22.))P,(16.(25.(10.R22.+4.)R1?.)(25.(11.&40.R45.)R22.))P,(16.(25.(10.R22.R21.)R20.)(25.(11.&40.R46.)R22.))P,(25.(10.(10.R23.R22.)+8.)(2<.+2.+2?.))P,(2=.(2>.O4.)(2?.$1?.R4;.(30.R4:.))(28.O4.)(2;.O5.O4.O3.R4<.)R26.+4.)P,(2=.(2>.O4.)(2?.$1?.R4<.(30.R4;.))(28.O4.)(2;.O5.O4.O3.R4=.)R26.+4.)P,(14.O5.R2:.)P,(31.O5.(32.O4.)(33.O5.O4.O3.R4?.)R2;.R2:.+18.)P,(31.O5.(32.O4.)(33.O5.O4.O3.R50.)R2<.R28.R27.)P,(31.O5.(32.O4.)(33.O5.O4.O3.R51.)R2=.R2;.+4.)P,(31.O5.(32.O4.)(33.O5.O4.O3.R52.)R2>.R2;.+4.)P,(6.(2.&40.)R47.(15.&40.R2>.))P,(6.(2.&40.)R47.(15.&40.R2>.))P,(6.(2.&40.)R47.(15.&40.R2>.))(34.O5.(32.O4.)(33.O5.O4.O3.R56.)(36.O5.O4.O3.R56.R55.R54.R53.R52.R51.R50.R4<.R4;.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R34.R33.R30.R2?.R2<.R32.)(7.(8.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.)R34.(15.&40.O2.)R33.(:.(2.&40.))R32.(;.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition oid_lookup1v_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (EXT lo : Z) (v0 : word) (VALS : list Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_oid ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.(2.&40.)Lv,(2.&40.)(5.(6.$0.R13.(7.(8.O17.O16.O15.O14.R12.R11.R10.O13.O12.R?.R>.R=.R<.R;.R:.R9.R8.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R7.R6.R5.R4.)O7.(9.O17.)O6.(:.(2.&40.))R3.(;.O1=.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+4.))(=.(>.$4.$4.)(?.$4.$4.O4.(11.&40.O16.))(12.(>.$4.$4.))))O1.R3.)(5.(13.O1=.O1.R3.)(5.(14.O1=.R3.)(5.(6.(2.&40.)R?.(15.&40.R2.))(5.(16.(6.$4.R2.=)(6.$4.R2.$17.))(5.(18.O1=.R3.O5.(=.$19.(1:.R1.)(12.$19.)))(5.(37.R2.R1.O3.O2.)(5.(1;.O1=.R3.O4.(11.&40.O16.))(1<.O1=.O1<.O1;.O1:.O19.O18.R3.))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition oid_lookup1v_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY STACK : Z) (VALS : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_oid ()) "Ph,(1=.O6.O5.O4.)PLB,(1>.$1?.)PLF,(1>.$1?.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))POID,$4.PEXT,$4.PP,$4.PLEN,$4.Plo,$4.Ptg,(2.&40.)Ppd,(2.&40.)Pv0,(2.&40.)Pxs,(1>.(2.&8.))P,(1<.O6.O5.O4.R2>.R2=.R2<.R:.)P,(18.O6.R;.R:.(21.R5.R4.R7.R8.))P,(22.O6.R<.R9.R3.)P,(6.$4.(23.(24.(2.&8.)R4.))R9.)P,(18.O6.R>.R<.(=.$19.(1:.R6.)(12.$19.)))P,(16.(25.(10.R=.+4.)R>.)(25.(10.R>.+18.)R=.))P,(16.(25.(10.R>.+4.)R=.)(25.(10.R=.R<.)R>.))P,(6.$4.(26.R10.+8.)=)P,(6.$4.(26.R10.+4.)=)P,(27.=R12.)P,(27.=R12.)P,(27.=R12.)P,(1;.O6.R16.R11.(11.&40.R36.))P,(25.(28.O5.)R12.)P,(25.R13.(29.(29.(11.&40.R38.)O2.)(2:.O5.)))P,(25.(11.&40.R39.)(2;.O6.O5.O4.R3=.))P,(6.$4.(26.(11.&40.R3:.)+10.)=)P,(16.(25.(10.R1:.+18.)R16.)(25.(11.&40.R3;.)R1:.))P,(16.(25.(10.R1:.+4.)R17.)(25.(11.&40.R3<.)R1:.))P,(16.(25.(10.R1:.R19.)R18.)(25.(11.&40.R3=.)R1:.))P,(25.(10.(10.R1;.R1:.)+8.)(2<.+2.+2?.))P,(2=.(2>.O5.)(2?.$1?.R42.(30.R41.))(28.O5.)(2;.O6.O5.O4.R43.)R1=.+4.)P,(14.O6.R20.)P,(31.O6.(32.O5.)(33.O6.O5.O4.R45.)R21.R20.+18.)P,(31.O6.(32.O5.)(33.O6.O5.O4.R46.)R22.R1?.R1>.)P,(31.O6.(32.O5.)(33.O6.O5.O4.R47.)R23.R21.+4.)P,(6.(2.&40.)R3<.(15.&40.R23.))P,(6.(2.&40.)R3<.(15.&40.R23.))(34.O6.(32.O5.)(33.O6.O5.O4.R4:.)(38.O6.O5.O4.R4:.R49.R48.R47.R46.R45.R44.R40.R3?.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R28.R27.R24.R21.R1>.O1.R26.)(7.(8.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.)R28.(15.&40.O3.)R27.(:.(2.&40.))R26.(;.O6.)))")
(* [comment removed for export] *).

Lemma oid_lookup1v_weakenA : ltac2:(CDefT.buildp (gd_tbl_A_oid ()) "Psegs,(1>.$39.)PR,$3:.PHIA,(3;.R2.R1.)PENTRY,$4.PSTACK,$4.PVALS,(1>.$4.)P,(3<.R6.R5.R4.R3.R2.R1.)(3=.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros segs R HIA ENTRY STACK VALS H. unfold oid_lookup1_stmtA. intros.
  eapply evtA_mono; [eapply H; eassumption|].
  intros ms' PO. unfold oid_lookup1v_postA in PO. unfold oid_lookup1_postA.
  ddestruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & r & v & E & MU & WM & MI & A0 & HR & HX & _ & ST & HH).
  dexists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', r, v.
  repeat match goal with |- _ /\ _ => split end. all: assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition oid_rt_hyps (R : art_layout) (HIA : artA asegs R) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_oid ()) "(5.(3>.(32.O2.))(5.(6.$4.(3?.(32.O2.))$40.)(5.(6.$4.(41.O2.)$42.)(5.Pm,P,(2.&40.)(3.(2.&8.))P,(43.O2.R1.)(44.R2.)(5.(25.=(2:.O2.))Ph,(1=.$45.O2.O1.)PLB,(1>.$1?.)PLF,(1>.$1?.)Pm,P,(2.&40.)(3.(2.&8.))P,(1<.$45.O2.O1.R4.R3.R2.R1.)(46.$45.(32.O2.)R2.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma hcs_img_cs : ltac2:(CDefT.buildp (gd_tbl_A_oid ()) "PR,$3:.PHIA,(3;.$45.R1.)Ph,(1=.$45.R2.R1.)P,(3>.(32.R3.))P,(6.$4.(3?.(32.R4.))$40.)(47.(33.$45.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  (intros R HIA h dd_H; ddestruct dd_H as (G & LO & HI & _); intros GSB). eapply img_cs_of; [exact LO | exact HI | exact G | exact GSB |].
  intros a n H1 H2 H3 H4. eapply (hcs_img asegs R HIA h); assumption.
Qed.

Ltac solve_in := lazymatch goal with |- In _ _ => cbn; repeat (first [ left; reflexivity | right ]) end.

(* [comment removed for export] *)
Tactic Notation "ro_str_at" constr(mx) constr(A) constr(n) "as" ident(RO) :=
  let bs := eval vm_compute in (match image_bytes asegs A n with Some bs => bs | None => [] end) in
  match goal with MI : mem_inv asegs mx |- _ =>
    pose proof (ro_image_bytes_at asegs mx A bs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO end.
Tactic Notation "ro_str" constr(A) constr(n) "as" ident(RO) :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => ro_str_at mx A n as RO end.

(* [comment removed for export] *)
Tactic Notation "img_aobj_at" constr(mx) constr(A) constr(n) "as" ident(OA) :=
  match goal with ICS : img_cs ?CS, ISH : (forall h LB LF m, HM _ _ _ h LB LF m -> img_shadow_ok _ _ m), HH : HM _ _ _ _ _ _ mx |- _ =>
    pose proof (aobj_img asegs _ CS mx A n ICS (ISH _ _ _ _ HH) ltac:(vm_compute; reflexivity)) as OA end.
Tactic Notation "img_aobj" constr(A) constr(n) "as" ident(OA) :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => img_aobj_at mx A n as OA end.

(* [comment removed for export] *)
Tactic Notation "tbl_cells_at" constr(mx) constr(A) constr(n) "as" ident(TB) :=
  let bs := eval vm_compute in (match image_bytes asegs A n with Some bs => bs | None => [] end) in
  match goal with RTC : (forall m, arl_rtc _ m -> asan_rtc m), HH : HM _ ?R ?HIA ?h ?LB ?LF mx |- _ =>
    pose proof (asan_rtc_const mx A bs (RTC mx (hm_rtc asegs R HIA h LB LF mx HH))
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as TB;
    cbn [length] in TB end.
Tactic Notation "tbl_cells" constr(A) constr(n) "as" ident(TB) :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => tbl_cells_at mx A n as TB end.

(* [comment removed for export] *)
Ltac pcleanA :=
  repeat match goal with
         | H : _ <-> _ |- _ => clear H
         | H : bv_unsigned ?x <> 0 |- _ => is_var x; clear H; try clear x
         | H : bv_unsigned ?x = 0 |- _ => is_var x; clear H; try clear x
         end.

(* [comment removed for export] *)
Tactic Notation "bcmpA" constr(SPB) constr(spf) constr(RODATA) constr(len) constr(HXS) :=
  let RO := fresh "RO" in let ORO := fresh "ORO" in
  let nn := eval vm_compute in (Z.to_nat len) in
  zstep; (* [comment removed for export] *)
  ro_str RODATA nn as RO; img_aobj RODATA len as ORO;
  lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of HXS with bytes_at _ mx ?qq ?qqs =>
    lazymatch goal with HH : HM _ _ _ ?hh ?lb ?lf mx |- _ =>
    lazymatch goal with STK : stk _ mx ?lo0 _ |- _ =>
      callxA_sp spf
        (eapply SPB with (h := hh) (LB := lb) (LF := lf) (P := RODATA) (Q := qq) (n := len) (lo := lo0) (qs := qqs);
         rewrite ?(unsigned_lit spf) by plia;
         first [ exact RO | exact HXS | exact ORO | eassumption | reflexivity | plia
               | match goal with H : aobj _ _ _ _ _ _ |- aobj _ _ _ _ _ _ => eapply aobj_sub; [exact H | plia | plia] end
               | match goal with H : crange _ _ _ |- crange _ _ _ => eapply crange_sub; [exact H | plia | plia] end
               | pose proof (@alloc_ceiling_bounds _); pose proof (@alloc_ceiling_pos _); plia                       (* [comment removed for export] *)
               | match goal with |- ?g => idtac "BCMP-SIDE:" g end ])
    end end end
  end;
  try clear RO ORO.
