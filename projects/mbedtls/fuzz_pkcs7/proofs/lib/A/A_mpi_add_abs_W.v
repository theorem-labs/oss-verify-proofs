(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_add_abs_W P_mpi_add_abs_C.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_journey A_mpi_core_add A_mpi_copy.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_add_abs_W () : Init.string Init.list := ["OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.A.A_mpi_opnd.opnd_atA"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_writableA"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.Spec.Rep.LNull"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.LibA.ARt.arl_tp"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_aobjA"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.hcs"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.A.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "OSSVerify.KrLib.LibA.ARt.havol"; "add_abs_PHI"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.A.A_alloc_lib.uw_obj"; "OSSVerify.KrLib.LibA.ARt.hfr"; "add_abs_FR"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpi_binop_postA"; "OSSVerify.KrLib.P.P_mpi_addsub.add_abs_R"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.A.A_mpi_journey.XJA"; "WA.AA_FRAME_A"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "WA.AA_VAL_A"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "WA.AA_POST_A"; "OSSVerify.KrLib.A.A_mpi_journey.BJA"; "OSSVerify.KrLib.Spec.Rep.limbs_val"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "WA.aaV1"; "WA.aaF1"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.A.A_mpi_journey.JBA"; "WA.K1A_stmt"; "WA.aaM"; "WA.aaV0"; "WA.aaF0"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "WA.opnd2A"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_ADD_ABS"].


Definition A_WRAP_CALLOC_AA : Z := 0x68f10.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMCPY_AA : Z := 0x67848.    (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Definition add_abs_PHI (dX dA dB : mpd) : Z := grow_PHI (md_n dA) + 3 * grow_PHI (Z.max (md_n dA) (md_n dB) + 2).
Definition add_abs_FR (d : Z) : Z := calls_FR 8 d.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mpi_add_abs_stmtA_o (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PdA,$7.PdB,$7.Plo,$8.Pd,$8.P,(9.O4.O3.O2.R2;.R2:.R29.R7.)P,(:.O4.O3.O2.R2<.R7.)P,(;.O4.R9.R2<.R7.)P,(;.O4.R:.R2=.R7.)P,(<.O4.O3.R2=.R;.R2>.(=.&40.R2;.)R7.)P,(>.R:.R9.)P,(>.R;.R9.)P,(>.R;.R:.)P,(?.(10.$11.(12.R=.)$13.))P,(14.R>.R=.R;.(=.&40.R30.))P,(14.R?.R=.R<.(=.&40.R31.))P,(15.(16.O3.)(17.$2.R35.(18.R34.))R=.(19.R?.)+10.)P,P,(10.$11.(12.R10.)$1:.)(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(1;.R11.)(1<.+4.(1=.R11.)))P,(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(19.R10.)+10.)P,P,(10.$11.(12.R11.)$1:.)(15.(16.O3.)(17.$2.R39.(18.R38.))R11.(1;.R12.)(1<.+4.(1=.R12.)))P,(1>.O3.R39.R38.(=.&40.R36.)(1?.O4.O3.O2.R3:.)R14.)P,P,(?.(10.$11.(12.R15.)$20.))(21.(22.(23.(1;.R16.)(1<.+4.(1=.R16.)))R13.)(22.(=.&40.R38.)(1;.R16.)))P,(24.O4.R18.R13.(=.&40.R38.))P,(22.(25.O3.)R14.)P,(22.R15.(26.(26.(=.&40.R3:.)+>0.)(27.O3.)))P,(22.(=.&40.R3;.)(1?.O4.O3.O2.R3?.))P,(10.$8.(28.(=.&40.R3<.)+10.)=)P,(10.(3.&40.)R3;.(29.&40.(2:.O3.)))P,(2;.O4.R1>.)P,(10.$8.(28.(=.&40.R40.)+2.)=)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R44.)R20.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R45.)R21.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R46.)R22.R1>.)P,P,(?.(10.$8.(19.R20.)(19.R21.)))P,(10.$11.(12.R21.)$13.)(10.$2?.(30.(1;.R22.)(1<.+4.(1=.R22.)))$31.)P,P,(10.$11.(12.R21.)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.R23.))))(10.$2?.(34.O4.(35.(23.(1;.R24.)R2.)))$31.)(10.$2?.(30.(1;.R23.)(1<.+4.(1=.R23.)))$31.)P,P,(10.$11.(12.R21.)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.R23.))))(10.$2?.(34.O4.(35.(23.(1;.R24.)R2.)))$31.)(10.$2?.(30.(1;.R23.)(1<.+4.(1=.R23.)))$31.)P,(22.(23.(36.O4.O3.O2.R4:.)(37.R24.R23.R22.))$38.)P,(39.O4.R27.(25.O3.)(3:.O4.O3.O2.R4;.)(=.&40.R41.)(=.&40.R47.)R21.)P,(3;.O3.(19.R26.)+10.R22.)P,(3;.O3.(19.R26.)+10.R23.)P,(3;.O3.(19.R26.)+10.R24.)P,(22.(23.(3<.O4.O3.O2.R4?.)(3=.R25.))$3>.)P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))(3?.O4.(40.O4.O3.O2.R50.R4?.R4>.R4=.R49.R48.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R31.R30.R53.R52.R51.R2=.(41.R52.R2=.R2<.R2;.)(37.R2=.R2<.R2;.)(3=.R29.)R2:.R2?.R2>.)(42.(43.(44.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.)R31.(29.&40.O1.)R30.(45.(3.&40.))R2?.(46.O4.))R2>.))")
(* [comment removed for export] *).

Definition mpi_add_abs_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PdA,$7.PdB,$7.Plo,$8.Pd,$8.P,(9.O4.O3.O2.R2;.R2:.R29.R7.)P,(:.O4.O3.O2.R2<.R7.)P,(;.O4.R9.R2<.R7.)P,(;.O4.R:.R2=.R7.)P,(;.O4.R;.R2>.R7.)P,(>.R:.R9.)P,(>.R;.R9.)P,(>.R;.R:.)P,(?.(10.$11.(12.R=.)$13.))P,(14.R>.R=.R;.(=.&40.R30.))P,(14.R?.R=.R<.(=.&40.R31.))P,(15.(16.O3.)(17.$2.R35.(18.R34.))R=.(19.R?.)+10.)P,P,(10.$11.(12.R10.)$1:.)(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(1;.R11.)(1<.+4.(1=.R11.)))P,(15.(16.O3.)(17.$2.R37.(18.R36.))R?.(19.R10.)+10.)P,P,(10.$11.(12.R11.)$1:.)(15.(16.O3.)(17.$2.R39.(18.R38.))R11.(1;.R12.)(1<.+4.(1=.R12.)))P,(1>.O3.R39.R38.(=.&40.R36.)(1?.O4.O3.O2.R3:.)R14.)P,P,(?.(10.$11.(12.R15.)$20.))(21.(22.(23.(1;.R16.)(1<.+4.(1=.R16.)))R13.)(22.(=.&40.R38.)(1;.R16.)))P,(24.O4.R18.R13.(=.&40.R38.))P,(22.(25.O3.)R14.)P,(22.R15.(26.(26.(=.&40.R3:.)+>0.)(27.O3.)))P,(22.(=.&40.R3;.)(1?.O4.O3.O2.R3?.))P,(10.$8.(28.(=.&40.R3<.)+10.)=)P,(10.(3.&40.)R3;.(29.&40.(2:.O3.)))P,(2;.O4.R1>.)P,(10.$8.(28.(=.&40.R40.)+2.)=)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R44.)R20.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R45.)R21.R1>.)P,(2<.O4.(2=.O3.)(2>.O4.O3.O2.R46.)R22.R1>.)P,P,(?.(10.$8.(19.R20.)(19.R21.)))P,(10.$11.(12.R21.)$13.)(10.$2?.(30.(1;.R22.)(1<.+4.(1=.R22.)))$31.)P,P,(10.$11.(12.R21.)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.R23.))))(10.$2?.(34.O4.(35.(23.(1;.R24.)R2.)))$31.)(10.$2?.(30.(1;.R23.)(1<.+4.(1=.R23.)))$31.)P,P,(10.$11.(12.R21.)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.R23.))))(10.$2?.(34.O4.(35.(23.(1;.R24.)R2.)))$31.)(10.$2?.(30.(1;.R23.)(1<.+4.(1=.R23.)))$31.)P,(22.(23.(36.O4.O3.O2.R4:.)(37.R24.R23.R22.))$38.)P,(39.O4.R27.(25.O3.)(3:.O4.O3.O2.R4;.)(=.&40.R41.)(=.&40.R47.)R21.)P,(3;.O3.(19.R26.)+10.R22.)P,(3;.O3.(19.R26.)+10.R23.)P,(3;.O3.(19.R26.)+10.R24.)P,(22.(23.(3<.O4.O3.O2.R4?.)(3=.R25.))$3>.)P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))P,(10.(3.&40.)R44.(29.&40.(19.R2:.)))(3?.O4.(40.O4.O3.O2.R50.R4?.R4>.R4=.R49.R48.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R31.R30.R53.R52.R51.R2=.(41.R52.R2=.R2<.R2;.)(37.R2=.R2<.R2;.)(3=.R29.)R2:.R2?.R2>.)(42.(43.(44.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.)R31.(29.&40.O1.)R30.(45.(3.&40.))R2?.(46.O4.))R2>.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition aa_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition aa_frame96 (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) : list cell :=
  [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section WA.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Hypothesis C24T : c24_transition.   (* [comment removed for export] *)
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_AA.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_AA.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (lo d : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition AA_FRAME_A := aa_frame96 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10.
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  (* [comment removed for export] *)
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis D0 : 0 <= d.

  Definition AA_POST_A := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "(40.$47.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(41.VLB,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(37.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(3=.Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).
  Definition AA_VAL_A := mpd_abs dA + mpd_abs dB.

  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -96)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A []).

  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0@L19687428440.138L25465666776.138L28125529944.138L29025845208.138L29428324939.5  L29762660275.138L31686769240.138L35663928186.7  L36180290948.1  L52253708504.138L60098763854.3  L60511538335.138L60692334296.138L61601561944.138L62505661912.138L64270350808.138L65178513496.138L947156799.137  Q15643598972.138Q18366170748.138Q18378508831.138Q21879891999.138Q24389844383.138Q27585188988.138Q27906956191.138Q30415318815.138Q31271277308.138Q32655747964.138Q33918012703.138Q36425601695.138Q3830178207.138 Q39939305631.138Q41152143740.138Q44648563964.138Q4533800828.138 Q51235551740.138Q52101417212.138Q59257011708.138Q59842863100.138Q60511538335.138Q66521824799.138Q9843086111.138 00000700>00E00L00^00e00l01A01E01L01V02002702>02E02L02S02Z02a02h03;03N03a03h04;04N04U04\04o05B05U05h05o06606=06D06K06R06Y06l07?07RS2ra2spS2ra2spS2ra2spS2ra2spS1R2lo3LOS3ALO3ACPS2ra2spS2ra2spS1R3HIA1h2sp2lo3TOP1HS2spS2ra2spS1R2lo3LOSS1R2ra2sp2lo5NEEDR3SLO3SPRS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2sp2loS2sp2loS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS2sp2loS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS2sp2loS2sp2loS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS2sp2loS2sp2loS2sp2loS2sp2loS2sp2loS2sp2loS2sp2loS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLOS1R2sp2lo5NEEDR3SLO". (* [comment removed for export] *)
  #[using="IMG JC"] Lemma aa_ret : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pr,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0',(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R21.R20.R1?.R1>.R1=.R1<.)P,(21.(32.(10.$8.R1<.=)(32.(10.$8.(4<.R1=.)$4=.)(10.$8.(4>.R1=.)+1.)))(10.$8.R1<.$4?.))P,(22.R23.(37.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(22.R23.(3=.Vd,))(50.$47.(51.$47.VR,VHIA,R23.Vmo,)$52.(43.(44.R1>.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R1=.R1<.R1;.R1:.R19.R18.(29.&40.R1?.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.Vs11,R8.R7.R6.R5.)VF,(29.&40.+9=>64.)Vfc,(45.(3.&40.))R21.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold AA_FRAME_A, aa_frame96 in FR1. replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep.
    do 12 zstep.
    zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold AA_POST_A.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC); [exact J| | exact HK9| exact MF9| exact HV| exact HF].
    split; [exact HR|]. split; [exact AD1|]. split; [exact PD1|]. split; [exact FRS1| exact NM1].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG JC"] Lemma aa_ret0 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0',(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R21.R20.R1?.R1>.R1=.R1<.)P,(10.$8.(4<.R1=.)$4=.)P,(10.$8.(4>.R1>.)+1.)P,(22.R24.(37.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(22.R24.(3=.Vd,))(50.$47.(51.$47.VR,VHIA,R24.Vmo,)$52.(43.(44.R20.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.Vs11,R9.R8.R7.R6.)VF,(29.&40.+9=>60.)Vfc,(45.(3.&40.))R22.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J HV HS BV BF. basic_factsA hc.
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep. eapply aa_ret; [exact J| left; split; [reflexivity| split; [exact HV| exact HS]]| exact BV| exact BF].
  Qed.

  (* [comment removed for export] *)
  #[using="IMG JC"] Lemma aa_retm16 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0',(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R21.R20.R1?.R1>.R1=.R1<.)P,(22.R22.(37.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(22.R22.(3=.Vd,))(50.$47.(51.$47.VR,VHIA,R22.Vmo,)$52.(43.(44.R1>.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.Vs11,R7.R6.R5.R4.)VF,(29.&40.+9=;:<.)Vfc,(45.(3.&40.))R20.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J BV BF. basic_factsA hc.
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep. zstep. eapply aa_ret; [exact J| right; reflexivity| exact BV| exact BF].
  Qed.
  Hypothesis BUD : havol asegs R HIA h + add_abs_PHI dX dA dB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + add_abs_FR d <= FR_MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 224 - arl_need_rt R.
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).
  Local Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Local Notation SH10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Local Notation SHE E := (Z_to_bv 64 (Z.shiftr E 3 + al_sb AL)).
  Local Notation XJ1 An cnt := (XJA asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A [(An, 4 * cnt)]).
  Local Notation FB0 := (FBA asegs R LB LF dX lo).
  Local Notation XD0 := (XDA asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A).
  Local Notation JBE dE := (JBA asegs R HIA LB LF m dX sp lo dE).
  Local Notation BJE dE := (BJA asegs R HIA LF sp dE).
  (* [comment removed for export] *)
  Definition aaM : Z := Z.max (md_n dA) (md_n dB).
  Definition aaV0 : Z := grow_PHI (md_n dA).
  Definition aaV1 : Z := grow_PHI (md_n dA) + grow_PHI (aaM + 2).
  Definition aaF0 : Z := calls_FR 2 d.                     (* [comment removed for export] *)
  Definition aaF1 : Z := calls_FR 2 d + calls_FR 2 d.
  Local Ltac xa_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1.

  (* [comment removed for export] *)
  Definition K1A_stmt (dE : mpd) (j : Z) (vv : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R18.R17.R16.R15.R14.R13.)P,(53.$47.VR,VHIA,VLF,Vsp,O3.R17.R16.R15.R14.)P,(10.$11.(12.R15.)$1:.)P,(22.O2.(1=.R16.))P,(10.$8.(4>.R17.)+1.)P,(10.$8.(54.(55.R18.))O1.)P,(22.R1>.$56.)P,(22.R1>.$57.)(50.$47.(51.$47.VR,VHIA,R1>.Vmo,)$52.(43.(44.R1:.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R19.R18.R17.(29.&40.VX,)(29.&40.(23.VX,+:.))R16.R15.R14.R13.R12.R11.R10.R?.(29.&40.O2.)(29.&40.(19.O3.))R>.(29.&40.(58.(2=.VR,)))(29.&40.(23.(1<.+4.O2.)+4.))(29.&40.(23.(59.(23.VX,+:.)+3.)(58.(2=.VR,))))(29.&40.(59.VX,+3.))(29.&40.(23.(59.(19.O3.)+3.)(58.(2=.VR,))))R=.Vs11,R<.R;.R:.R9.)VF,(29.&40.+9=<44.)Vfc,(45.(3.&40.))R1<.(46.$47.)))")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "04G0@C17025492443.266C17025492443.267C17025492443.268C53526081063.269C53526081063.270C53526081063.271D21361708665.206D22466435734.272D24976250634.228D24976250634.303D27965255826.298D34348047352.204D34348047352.206D34352354649.292D34352354649.294D34352354649.299D376593230.272  D37969448224.293D37969448224.300D50797141399.228D50797141399.229D50797141399.303D52014138856.228D52014138856.229D52014138856.303D59228252318.303D60109446735.272D62155808737.229D62155808737.303D7340709316.272 D8414535367.298 D939044794.272  K1329197271.269 K1329197271.270 K1329197271.271 K2612272047.268 K2612272047.272 K32761642720.268K32761642720.272K38856059124.304K61206821897.229K61206821897.303K61206821897.304K6379668000.266 K6379668000.267 K6379668000.268 K7412424035.272 L10947173192.14 L12755534717.11 L12755534717.9  L1342025005.3   L14051382136.11 L14748712526.19 L14751320984.1  L14760987928.8  L15649680808.1  L16473205958.7  L16473494895.4  L17585880332.15 L18826226759.8  L18929185109.35 L19277739793.9  L20803911415.2  L2166243551.4   L21845917352.35 L21847519070.3  L21848002076.19 L21860433226.8  L22479292268.1  L23100341967.216L23100341967.221L23100341967.254L23100341967.287L23615739305.3  L24313534829.3  L24313585860.4  L24313813357.8  L25044269509.2  L25046775673.253L25047280258.241L2607826517.4   L26950159893.14 L27214106967.5  L27481632834.8  L27481632834.9  L27966909654.1  L28655862141.3  L29059042772.8  L29211043776.6  L31060952619.9  L31325970818.4  L32756788865.4  L32761511569.8  L34222569270.300L34412813842.37 L34424803280.3  L35298821793.4  L35655538624.7  L35655538630.7  L35663928186.7  L35697213963.5  L35975126990.5  L36180290948.1  L37969005188.5  L381020265.6    L38235734261.1  L38546189747.8  L38868673902.3  L38868673902.5  L39172636981.0  L39436426759.7  L40294887048.3  L40449602357.4  L41112120439.37 L41114184771.35 L41116237108.1  L41389564045.12 L42601251809.7  L43625157983.1  L43631939593.37 L43878034250.5  L45270628691.35 L46061234176.4  L46160487540.221L46160487540.242L46160487540.288L46380960401.4  L46756382136.216L46948640662.37 L48154966246.216L49578233423.221L49578233423.287L49579218529.37 L49807695752.8  L5098421631.4   L5098421631.5   L51211863758.10 L5261871668.3   L52707865424.1  L547707976.3    L57258774030.15 L59308633593.3  L59308972243.3  L60098763854.3  L61212928741.14 L61564783896.35 L62018535662.1  L62112453655.206L62935018273.0  L63070224179.4  L63070715826.19 L63074667748.10 L63074930482.37 L63442736301.15 L6384586821.2   L64811930313.12 L64934269637.2  L66661851587.4  L67601363691.1  L7400112281.3   L7429484350.35  L8414648675.5   L9951453048.13  O17025492443.266O17025492443.267O17025492443.268O22987107037.268O22987107037.272O32329373691.272O37539299629.266O37539299629.267O37539299629.268O41427663046.271O45218884275.268O45218884275.272O53526081063.269O53526081063.270O53526081063.271P1329197271.269 P1329197271.270 P1329197271.271 P38856059124.229P38856059124.304P40437264079.266P40437264079.267P40437264079.268P57246471156.271P6379668000.266 P6379668000.267 P6379668000.268 P7412424035.272 Q12370813529.221Q12370813529.226Q12370813529.265Q12370813529.300Q17205055869.299Q17205141463.225Q17207432298.220Q17207432298.264Q22466435734.272Q24974040330.228Q24974040330.303Q26207421841.225Q26207421841.251Q26207721832.226Q26207721832.252Q26207721832.301Q26207967338.223Q26207967338.264Q26207967338.298Q26209519061.300Q26209835253.249Q31651985788.300Q31653536963.264Q31654082872.225Q31654082872.251Q37623358517.225Q37623376543.299Q37625261960.220Q37625261960.264Q376593230.272  Q38248387216.272Q39212284437.226Q39212284437.252Q39212284437.301Q42081808994.226Q42081808994.301Q42250421143.193Q42250421143.289Q42250505353.252Q42252699699.271Q42252699701.175Q43879899724.272Q43925228937.226Q43925228937.252Q43925228937.301Q52016320488.228Q52016320488.302Q52016320488.303Q5483308162.299 Q5483358760.225 Q5485126037.220 Q5485126037.264 Q5485174314.221 Q5485174314.226 Q5485174314.265 Q5485174314.300 Q6027349519.228 Q6027349519.229 Q6027349519.302 Q6027349519.303 Q60511567613.226Q60511567613.252Q60511567613.301Q60697995187.226Q60697995187.252Q60697995187.301Q6143569392.221 Q6143569392.226 Q6143569392.265 Q6143569392.300 Q62157788641.228Q62157788641.302Q62965564504.227Q62965564504.301Q62965564504.302Q63442345212.298Q68317669980.295Q68317669980.296Q68317669980.297Q68330333437.205Q7891539809.226 Q7891539809.300 Q8880503606.223 Q8880503606.298 Q8882895785.249 Q9538787269.223 Q9538787269.298 Q9540589402.249 00000100200300400500600L01901c02Z03B03C03D03E03F03G04M04N04O05[06e08A08k09S0:J0:K0;A0;i0<`0<a0<b0=`0=a0=b0=c0>T0?E0@?0A90A:0B90CI0DN0DO0DP0DQ0DR0DY0DZ0D[0D\0E<0EL0EM0EN0EQ0Ef0Eg0Eh0F>0F]0G90G:0GJ0Gf0Gg0H=0H>0HB0H[0I40IS0J;0JE0JR0JS0JT0J]0KD0L50L60L70LG0LH0LI0LM0LN0Lf0M70MS0M^0M_0N30N[0No0O00O;0OV0P10PF0PX0Pi0Pm0Pn0Q?0QC0QT0QU0QV0QW0Qm0R00R10RC0RU0RV0RW0Rd0Re0SG0SN0Sm0T50TU0UI0V80V90WT0XM0XN0Xg0YO0Z<0Z=0ZJ0Z[0Z\0Zf0Zi0[30[40[?0[J0[T0[U0\O0\R0\h0\i0\j0]<0]=0]U0]V0]W0]o0^80^H0^M0^N0_;0_<0_=0_>0_?0_@0_A0_B0_C0_D0_E0_F0_G0_H0_I0_J0_K0_L0_M0_N0_O0_P0_Q0`O0aM0bK0cP0cQ0cR0cS0cT0d40dT0e:0ei0fA0fN0f[0fj0gH0gf0hM0hZ0i70iD0ia0j90jF0jU0jm0kE0kb0l:0lI0lV0m30m@0mX0me0n40nZ0o80oE0ob10:10M10k11Z12T13V14P15?15`15m16J16b17C17m18T18l19919F19U19b19o1:>1:V1;41;S1<:1<d1<o1=J1=`1>01>P1>k1?81?E1?T1?l1@K1A51AO1B41BY1CQ1CR1CS1CT1CU1Ch1DF1DS1Dk1EH1ES1Ei1FDFFFFFFS2ra2sp1X3xs02Ea2zs2xsS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4SLEN4DLENS2ra2sp1X3xs02Ea2zs1j2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLENFFFFFS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2X03SPR2E02An3An02N12P04Fcnt4SLEN4DLENFFS1R2ra2sp1X3xs02lo4SLO22Ea2zs1j2xs5NEEDR3LOS2X03SPR2E02An3An02HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22Ea2zs2xs5NEEDR3LOS2X03SPR2E02An3An02HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22Ea2zs1j3nXc3pXc2xs5NEEDR3LOS2X03SPR2E02An3An02P04ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs1j2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stFS1R2ra2sp1X3xs02lo2Ea2zs1j3nXc3pXc2xs3LOS2An4SLEN4DLENS2ra2sp1X3xs02Ea2zs2xs2An2HB5Ha_st5Hl_stS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLEN2HB5Ha_st5Hl_stFFS1R3HIA2ra2sp1X3xs02lo2Ea2zs1j3nXc3pXc2xs2h22An4TOP24SLEN4DLENFFFS3xs02pE2zs1j3nXc3pXc2xs4LEN12An2N14SLEN4DLEN3SEPS3xs02pE2zs1j3nXc3pXc2xs4LEN12An2N14SLEN4DLEN3SEPS1R2sp3xs02lo2zs1j3nXc3pXc2xs3LOS3ALO4LEN12N12PC4SLEN4DLENS1R2sp3xs02lo2zs1j3nXc3pXc2xs3LOS3ALO4LEN12N12PC4SLEN4DLENFS1R2sp1X3xs02lo4SLO22pE2zs1j2xs5NEEDR3FSZ3DSX2HB5Ha_st5Hl_st2AnS1R2sp1X3xs02lo4SLO22pE2zs1j3nXc2xs5NEEDR3FSZ3DSX4LEN12An2N14ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO22pE2zs1j3nXc2xs5NEEDR3FSZ3DSX4ZLEN2HB5Ha_st5Hl_stFFFFS2sp2loFFFS2dA2dB2nE1j1v3nXc3CNT2EM2BV3NR1S2sp3nXc3SPR3NR1FFS1jS2nE1j3nXc3CNT2An3A47FFS2nE2pE1j3nXc3CNT2An1HS2sp2dA2dB2nE1j3nXc3CNT3SPR3NRES2dA2dB2nE1j1v3nXc3CNT2EM2BVFS3nXc2xs4LEN12N1S1R2sp2dA2dB2lo4SLO23NRM3SPRFS1R2sp2lo4SLO23NRA3SPRFS2AnS2ra2sp1X3xs02Ea2zs2xs2AnS2ra2sp1X3xs02Ea2zs2xs2AnS2ra2sp1X3xs02Ea2zs1j3pXc2xs2AnS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLENS1R3HIA2hcS3nXc3pXc3P47FFS3nXc3NR1S2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs3NR12AnS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs3NR12An4SLEN4DLENFFS1R3HIA1h2sp3TOPFFS2spFS2Ea2nE1j3nXc3CNT2An3ESAS2nE1j3nXc3CNT2AnS2dA2dB2nE1j1v3nXc3CNT2EM2BVS1d2D01f2BFFS2sp2lo3nXc3pXc4XLScS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLENS1R2sp2dA2dB2lo4SLO2FS1d2D01f2BFS1R3HIA2sp2lo2h24TOP25HTOP2S1R3HIA2sp2lo2h44TOP45HTOP4S1R3HIA1h2sp2lo3TOP1HS2nE1j3nXc3CNT3NRES2nE1j3nXc3CNT2N1S2spFS2nE1j3nXc3CNT2AnS2loS2sp2lo2nE2pE3EL5FFSS1R3nXc3pXc2N12P02PC1HS1XFS2sp2dA2dB3SPA3SPRS2sp2dA2dB3SPA3SPRFFS2sp2lo2Ea2ESFS2sp2dA2dB2nE1j3nXc3CNT3SPR3NRE2N1S2sp2loS2sp2dA2dB2nE1j3nXc3CNT3SPR3NR1S1d1f2BFS2ra2sp1X3xs02Ea2zs2xs2X03X162AnS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2X03X162An4SLEN4DLENS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2X03X162An4ZLENFS1R2ra2sp1X2nX3xs02lo4SLO22Ea2nE2zs1j3nXc2xs3CNT5NEEDR3LOS2X03LEN3ALO3SPR2E02An3An03AnC3NM1S1R3HIA1h2sp2dA2dB3BUD2nE1j1v3nXc3CNT2EM2BV3SPR2h22N13HV1FS2ra2sp1X3xs02Ea2zs2xs2AnS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2An4ZLENS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2BF3SPR2h24HFR1FS3nXc2xs4LEN1S2nE1j3nXc3CNT2N1FS1X2X03X16S1jS1R3HIA2h2FS2An3An02KZS3pXc2KP2P0S1R2lo3LOSFS1R3HIA1h2sp2dA2dB3BUD2nE1j1v2hc3nXc3CNT2EM2BV3SPR3NR13HV1S1RS2ra2sp1X3xs02Ea2zs2xsSFS1R3HIA2sp2h24TOP2FS1R3HIA2sp2dA2dB2h24TOP2FFS2lo2nE1j3nXc3CNT2An3FloS3nXc3NR1S3nXc3pXc2An3SEPS3nXcFS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2hc2BF3SPR4HFR1FFFFFFFFFFFFFFFFFFFFFFS1R2sp3xs02lo2zs1j3nXc2xs3LOS3ALO2An3AnC2N14Fcnt3Flo4SLEN4DLENS1R2sp3xs02lo2zs1j3nXc2xs3LOS3ALO2An3AnC2N14Fcnt3Flo4SLEN4DLENS1R2sp3xs02lo2zs1j3nXc2xs3LOS3ALO2An3AnC2N14Fcnt3Flo4SLEN4DLENS1R2sp3xs02lo4SLO22zs1j3nXc2xs5NEEDR3LOS3ALO2An3AnC2N14Fcnt4SLEN4DLENFFFFS2ra2sp1X3xs02Ea2zs2xs2X03XAL2AnS2ra2sp1X3xs02Ea2zs2xs2X03XAL2AnS2ra2sp1X3xs02Ea2zs1j3pXc2xs2X03XAL2AnS2ra2sp1X3xs02Ea2zs1j3nXc3pXc2xs2X03XAL2An4ZLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xsS1X3xs02zs2xsS1X3xs02zs1j2xsS3xs02zs1j3nXc2xs2An4SLEN4DLENS1X3xs02zs1j2xs2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs4ZLEN2HB5Ha_st5Hl_stS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4SLEN4DLENS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4SLEN4DLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xsS1X3xs02zs1j2xsS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs1j3nXc2xs4SLEN4DLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs1j2xsS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4SLEN4DLENS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xsS1X3xs02zs1j2xsS3xs02zs1j3nXc2xs2An2N14Fcnt4SLEN4DLENS3xs02lo2zs1j3nXc2xs4SLEN4DLENS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4SLEN4DLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xs2X02HBS1X3xs02zs1j3nXc2xs2X04ZLEN2HBS1R2sp3xs02lo4SLO22zs2xs5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO22zs1j3nXc2xs5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22zs1j3nXc2xs5NEEDR3LOS4SP643ALO3ACP2N14SLEN4DLENS1R2sp3xs02lo4SLO22zs1j3nXc2xs5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22zs2xs5NEEDR3LOS4SP643ALO3ACPS2sp3xs02lo2zs1j3nXc2xs4SLEN4DLENS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4SLEN4DLENS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs1j2xs2HB5Ha_st5Hl_st2AnS1X3xs02zs1j3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs4ZLEN2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xsS1X3xs02zs2xsS1X3xs02zs1j2xsS1X3xs02zs2xsS1X3xs02zs2xsS1X3xs02zs1j2xsS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs1j2xs2HB5Ha_st5Hl_stS1X3xs02zs2xs2An2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs4ZLEN2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS3xs02zs2xsS3xs02zs1j3nXc2xs4SLEN4DLENS3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xs2X0S1X3xs02zs1j3nXc2xs2X04SLEN4DLENS1X3xs02zs1j3nXc2xs2X04ZLENS1X3xs02zs2xsS1X3xs02zs2xsS1X3xs02zs1j2xsS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs2xs2An2HB5Ha_st5Hl_stS1X3xs02zs1j3nXc2xs2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02zs2xs3X162HB5Ha_stS1X3xs02zs1j3nXc2xs3X164ZLEN2HB5Ha_stS1X3xs02zs1j3nXc2xs3X164ZLEN2HB5Ha_stS1R2sp3xs02lo4SLO22zs1j3nXc3pXc2xs5NEEDR3LOS3ALO2PC4ZLENFFFFS1X3xs02zs2xs2X02HBS1X3xs02zs1j3nXc2xs2X04ZLEN2HBS1X3xs02zs2xsS1X3xs02zs1j3nXc2xs4ZLENS1X3xs02zs1j3nXc2xs4SLEN4DLENS3xs02zs2xsS3xs02zs1j3nXc2xs4ZLENS3xs02zs1j3nXc2xs4SLEN4DLEN". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2"] Lemma aa_G1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "PdE,$7.Pj,$8.Pvv,$8.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(5:.$47.VR,VHIA,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,R1;.)P,(5;.R1<.R1;.R1:.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R1:.R19.R18.R17.R16.R15.)P,(53.$47.VR,VHIA,VLF,Vsp,R1>.R19.R18.R17.R16.)P,(32.(33.(1=.R17.)R1>.)(22.R1>.(1=.R1?.)))P,(22.(1=.R20.)$5<.)P,(10.$8.(4>.R19.)+1.)P,(10.$8.(54.(55.R1:.))R20.)P,(22.R20.$5=.)P,(22.R20.$5>.)(50.$47.(51.$47.VR,VHIA,R20.Vmo,)$52.(43.(44.R1<.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R1;.R1:.R19.(29.&40.VX,)(29.&40.(23.VX,+:.))R18.R17.R16.R15.R14.R13.R12.R11.(29.&40.R24.)(29.&40.(19.R25.))R10.(29.&40.(58.(2=.VR,)))(29.&40.(23.(1<.+4.R24.)+4.))(29.&40.(23.(59.(23.VX,+:.)+3.)(58.(2=.VR,))))(29.&40.(59.VX,+3.))(29.&40.(23.(59.(19.R25.)+3.)(58.(2=.VR,))))R?.Vs11,R>.R=.R<.R;.)VF,(29.&40.+9=;=4.)Vfc,(45.(3.&40.))R1>.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros DBJ K1 J B CNT EM SG1 HVV BV BF. jc_open. unfold K1A_stmt in K1.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    xa_open J.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' sg.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC dE DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    destruct dE as [Ea sE nE pE zs padE ownE]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in ST1, FR1 by (clear; lia).
    replace (Z_to_bv 64 429840) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (cnt := j) (sz := 4) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; try eassumption; try reflexivity.
      all: try (apply c24_of_transition; exact C24T).   (* [comment removed for export] *)
      all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
      all: try (rewrite HT1; clear - TOP; lia).
      all: unfold aaV0, aaF0, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
           clear - CNT EM NR1 NR NRE LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP; try lia.
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2. clear MU WM.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof ST2 as ST2'.
    assert (HP2' : presA asegs R LBc LF (bv_unsigned sp - 96) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m2).
    { eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2, HT1; exact TOP).
    destruct CASES as [[Er HH2] | (An & Er & A16 & HFRA & HAS & HH2 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - (* [comment removed for export] *)
      pose proof (xa_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep.
      eapply aa_retm16; [exact J2| |].
      + unfold aaV0, aaM, add_abs_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT EM NRE NR1. lia.
      + unfold aaF0, add_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      replace (j * 4) with (4 * j) in HFRA, HAS, HH2, HNEW, HV2 by (clear; lia).
      destruct (xa_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ An j J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW
                  ltac:(cbn [md_n]; clear - CNT NRE; lia)) as [J2 F2].
      pose proof (bja_transport _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ _ J B HP2' MI2 HCS2 HH2 ltac:(intros b Hb; right; exact Hb)) as B2.
      dpose HFRA as (An0 & AnC & AnD & HAP).
      clear J B. try clear MI1; try clear ST1; try clear STc; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1; try clear CX1; try clear OWN0; try clear OWN1;
      xa_open J2.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2 & OWN0 & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold mpi_cells in CX2.
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH1) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - An0 AnC H; lia); clear - KZ An0; lia|]. clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KP; zify_cond KP.
      + (* [comment removed for export] *)
        assert (EO : own = LNull).
        { destruct own; [reflexivity| | exfalso; exact (NS1 eq_refl)]. exfalso.
          ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & _ & _ & _ & P0 & PC & _).
          rewrite Z.mod_small in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H N1; lia). clear - KP P0; lia. }
        subst own. ddestruct (OWN0 eq_refl) as (EP & EN & EL). clear OWN1 KP.
        pose proof (xga_null _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J2 F2 eq_refl) as D2.
        pose proof (xda_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ D2) as CW5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CW5. rewrite <- HT1 in CW5.
        clear MU WM. pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
        (* [comment removed for export] *)
        shadow_chk OX1 (X + 10) 2.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        pose proof (xda_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ D2 MU WM MI1 CX2 HH1 OX1) as J5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
        pose proof (bja_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ _ D2 B2 MU WM) as B5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in B5.
        eapply K1; [exact J5| exact B5| reflexivity| cbn [md_n]; clear; lia| reflexivity| | |].
        * cbn [md_limbs]. rewrite limbs_val_repeat0. rewrite EL in HVV. cbn [limbs_val] in HVV. exact HVV.
        * unfold aaV0, aaV1, aaM, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT EM. lia.
        * unfold aaF0, aaF1, calls_FR, fr_charge in *. clear - BF D0. lia.
      + (* [comment removed for export] *)
        assert (EO : own = LHeap).
        { destruct own; [| reflexivity| exfalso; exact (NS1 eq_refl)]. exfalso. apply KP. rewrite (proj1 (OWN0 eq_refl)). reflexivity. }
        subst own. ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1 KP.
        pose proof (XLS1 ltac:(discriminate)) as XLSc. pose proof (XP1 eq_refl) as XPc.
        pose proof F2 as [Ffr Ffr0 Fal Fnew Fnewc Fap Farr Flen Fcnt FXS Flo]. cbn [md_n] in Fcnt.
        destruct (xga_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J2 F2 eq_refl)
          as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _ & OA & OP' & _ & A47 & INA & INP).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP, OA, OP', A47, INA, INP.
        rewrite firstn_length in DST, DLEN. rewrite repeat_length in DST, DLEN.
        replace (Init.Nat.min (Z.to_nat nXc) (Z.to_nat j)) with (Z.to_nat nXc) in DST, DLEN by (clear - CNT N1; lia).
        (* [comment removed for export] *)
        shadow_chk OX1 (X + 10) 2.
        zstep.
        replace (zx16 (Z_to_bv 64 nXc)) with (Z_to_bv 64 nXc)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
        zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
        pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_AA) as SPC. unfold A_ASAN_MEMCPY_AA in SPC.
        apply (u8arr_of_rw_cells asegs) in DST.
        (* [comment removed for export] *)
        clear MU WM. pose proof (munch_refl [(An, An + 4 * nXc); (lo, bv_unsigned sp + -96)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
        acallxA_sp (bv_unsigned sp + -96)
          (eapply SPC with (h := h2) (LB := (An, 4 * j) :: LBc) (LF := LF) (DST := An) (SRC := pXc) (n := 4 * nXc) (lo := lo)
                            (ss := u32s xs);
           rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia;
           try eassumption; try reflexivity;
           first [ left; rewrite AMC; reflexivity
                 | rewrite u32s_length, firstn_length, repeat_length; clear - N1 CNT; lia
                 | rewrite u32s_length; clear - LEN1 N1; lia
                 | eapply aobj_sub; [exact OA| clear; lia| clear - CNT N1; lia]
                 | right; clear - SEP; lia
                 | left; clear - Flo CNT N1 SLO2 NEEDR; lia
                 | clear - XLSc SLO2 NEEDR; lia
                 | right; clear - A47 CNT N1; lia
                 | right; clear - P47; lia
                 | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
                 | eapply client_wrange_block; [apply in_or_app; left; left; reflexivity| clear; lia| clear - CNT N1; lia]
                 | f_equal; clear; lia
                 | clear - NR1 N1 CNT LOS SLO SLO2 NEEDR NRA TOP2 SPA SPR; lia
                 | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ]).
        clear SPC.
        all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        match goal with H : u8arr asegs m3 An (u32s xs) |- _ => rename H into HPA end.
        match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
        match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
        match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
        match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 X 16 |- _ => rename H into OX3 end.
        pose proof ST3 as ST3'.
        apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
        replace (4 * length xs)%nat with (Z.to_nat (4 * nXc)) in HPA by (clear - LEN1 N1; lia).
        destruct (xga_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m3 J2 F2 eq_refl MU WM MI3 ST3' HPA HH3 OX3) as [J3 F3].
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J3, F3.
        pose proof (bja_fb_apart _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ J2 F2 B2) as [ESA ELA].
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ESA, ELA.
        pose proof (bja_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 J2 B2 MU WM
                      ltac:(unfold w_client; apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [eapply aobj_crange; exact OA| clear; lia| clear - CNT N1; lia]|];
                            apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]| apply Forall_nil])
                      ltac:(cbn; split; [clear - ESA CNT N1; lia|]; split; [clear - ES SLO2 NEEDR; lia| exact I])
                      ltac:(intros BN; cbn; split; [pose proof (ELA BN); clear - H CNT N1; lia|]; split; [ddestruct (OWNE1 BN) as (_ & _ & _ & _ & EL5 & _); clear - EL5 SLO2 NEEDR; lia| exact I])) as B3.
        clear J2 F2 B2 OA OP' SBY SLEN DLEN INA INP.
        try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. xa_open J3. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
        try clear CX2. pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J3) as (_ & _ & _ & _ & CX3 & _ & _).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
        (* [comment removed for export] *)
        clear MU WM. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        zstep. zstep. zstep.
        replace (zx16 (Z_to_bv 64 nXc)) with (Z_to_bv 64 nXc)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
        zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
        destruct (xga_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB & ZN1).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ZIN, ZCH, ZLEN, ZB.
        pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
        eapply aevtA_call.
        { intros mo3 [HK3 MF3].
          eapply SPZ with (h := h2) (LB := (An, 4 * j) :: LBc) (LF := LF) (buf := pXc) (len := 4 * nXc) (lo := lo) (d := d) (junk := u32s xs);
            rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; try eassumption; try reflexivity.
          all: try (right; split; [exact ZIN | rewrite <- ZLEN; exact ZCH]).
          all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
          all: try (f_equal; clear; lia).
          all: unfold aaV0, aaF0, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
               clear - CNT EM NR1 NR NRE N1 LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP TOP2; try lia.
          all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
        clear SPZ.
        (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
        destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
        rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in PO by qlia.
        ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
          replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
        match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
        presA_transport HP4.
        pose proof ST4 as ST4'.
        assert (HP4' : presA asegs R (lb_remove pXc ((An, 4 * j) :: LBc)) LF (bv_unsigned sp - 96) (arl_stklo R) (hstkhi asegs R HIA h2)
                         [(pXc, pXc + 4 * nXc)] m3 m4).
        { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
        pose proof (xga_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 eq_refl MI4 ST4' HP4' HT4 HS4 HF4 HCS4 HV4 HFR4 HH4) as D4.
        pose proof (bja_zfree _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 B3 eq_refl HP4' MI4 HCS4 HH4) as B4.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in D4, B4.
        assert (HT4h : htop asegs R HIA h4 = htop asegs R HIA h) by (rewrite HT4; exact HT1).
        apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
        clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
        clear CSOK SB64 SCS0 SCS HTOP2.
        pose proof (hcs_ok asegs R HIA h4) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h4) as SCS0.
        assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
        try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. clear J3 F3 B3 HP4 HP4'. try clear ZCH; try clear ZB; try clear XARR; try clear OP; try clear HH2.
        pose proof D4 as [DMI DST4 DFR DHM DHT DHS DHF DHCS DHV DHFR DCX DSG DSUB DKEEP DGONE DNEW DAPART DARR DLEN4 DCNT DXS DPRES DFRESH DAL DOX DLO DNM].
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in DCX, DOX, DHM. unfold mpi_cells in DCX.
        pose proof (hm_top asegs R HIA h4 _ LF m4 DHM) as HTOP4.
        assert (SCS : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP4 HTOP4; lia]).
        pose proof (xda_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ D4) as CW5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CW5.
        rewrite <- HT4h in CW5.
        pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
        (* [comment removed for export] *)
        shadow_chk DOX (X + 10) 2.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
        pose proof (xda_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ D4 MU WM MI5 DCX DHM DOX) as J5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
        pose proof (bja_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ _ D4 B4 MU WM) as B5.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in B5.
        eapply K1; [exact J5| exact B5| reflexivity| cbn [md_n]; clear; lia| reflexivity| | |].
        * cbn [md_limbs]. rewrite skipn_repeat, limbs_val_app_zeros. exact HVV.
        * unfold aaV0, aaV1, aaM, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT EM. lia.
        * unfold aaF0, aaF1, calls_FR, fr_charge in *. clear - BF D0. lia.
    all: match goal with |- ?g => idtac "G1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Hypothesis VALM : AA_VAL_A < 2 ^ (32 * (aaM + 1)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04T0@C17025492443.246C17025492443.247C17025492443.248C40893063684.290C53526081063.249C53526081063.250C53526081063.251D17975678776.252D21361708665.198D22466435734.252D24976250634.282D27965255826.276D34348047352.195D34348047352.198D34352354649.270D34352354649.272D34352354649.277D37969448224.271D37969448224.278D37981848449.196D50797141399.282D52014138856.282D59228252318.282D60109446735.252D61815348395.289D62155808737.282D6762693186.289 D7340709316.252 D8414535367.276 D939044794.252  K1329197271.249 K1329197271.250 K1329197271.251 K23468015258.290K2612272047.248 K2612272047.252 K32761642720.248K32761642720.252K38856059124.283K52322685826.290K61206821897.282K61206821897.283K6379668000.246 K6379668000.247 K6379668000.248 K7412424035.252 L10559054258.4  L10947173192.14 L11656196980.1  L12416934887.5  L12755534717.8  L12755534717.9  L12905641847.4  L1342025005.2   L14051382092.8  L16473205958.5  L16473494895.4  L17585880332.13 L17703443598.3  L17830241467.3  L18587013051.13 L20630580640.10 L20803911415.2  L21073294716.9  L21086251255.8  L21297056158.4  L21847519070.3  L21860237213.17 L21860433226.8  L21860695708.32 L22479292268.1  L23100341967.222L23100341967.235L23100341967.269L23100341967.275L23455462144.3  L23615739305.3  L24313534829.3  L24313585860.4  L24313813357.6  L24799912036.4  L25119086869.34 L25132156744.1  L25138051168.17 L25138248375.8  L25142208316.1  L25232169794.9  L25654434199.198L2607826517.4   L26228513507.2  L26660323117.1  L26673455472.32 L27214106967.5  L27572020408.8  L27747017808.5  L27835269521.2  L27836715734.223L27837255469.234L27966909654.1  L28655862141.3  L28671776394.4  L30483066123.4  L31325970818.4  L32027975233.0  L32754825233.4  L32761511569.8  L34412813842.34 L34424803280.3  L35655538624.7  L35655538630.7  L35663928186.7  L36180290948.1  L37969005188.5  L38235734261.1  L38868673902.4  L39172636981.0  L40294887048.3  L40449602357.4  L4079695450.2   L41112120439.32 L41112120439.34 L41116237108.1  L43343741601.15 L43878034250.5  L44196988417.11 L44611170703.5  L4482322106.10  L46160487540.224L46160487540.270L46380960401.4  L46756382136.222L46948640662.34 L48154966246.222L48823579041.0  L49150310671.4  L49578233423.269L49579218529.34 L51216332057.10 L52318461464.3  L5261871668.3   L53314392638.2  L53404598366.8  L547707976.3    L54817154178.3  L55190826961.274L55191156004.277L57258774030.15 L59308632307.3  L59308633593.3  L60098763854.3  L61212928741.14 L61562785068.32 L62018535662.1  L63070224179.10 L63070224179.4  L63074471475.17 L63074930482.34 L63286672054.278L63440801702.15 L63654471873.2  L6384586821.2   L63849440564.1  L65496508708.4  L66581468868.32 L66661851587.4  L67180826602.3  L67180826602.4  L67725245073.2  L7400112281.3   L7419031306.32  L7704260991.4   L8414648675.5   L8890516472.1   O17025492443.246O17025492443.247O17025492443.248O22987107037.248O22987107037.252O32329373691.252O37539299629.246O37539299629.247O37539299629.248O41427663046.251O45218884275.248O45218884275.252O53526081063.249O53526081063.250O53526081063.251P1329197271.249 P1329197271.250 P1329197271.251 P23468015258.290P38856059124.283P40437264079.246P40437264079.247P40437264079.248P43347971899.290P57246471156.251P6379668000.246 P6379668000.247 P6379668000.248 P7412424035.252 Q10203249998.285Q11801279589.289Q12370813529.230Q12370813529.243Q12370813529.279Q12370813529.283Q17205055869.278Q17207432298.229Q17207432298.242Q17207432298.282Q17975678776.252Q22466435734.252Q22642964918.288Q24974040330.282Q26207421841.231Q26207721832.232Q26207721832.280Q26207967338.229Q26207967338.242Q26207967338.277Q26209519061.279Q26295627581.285Q31651985788.279Q31653536963.242Q31654082872.231Q37623376543.278Q37625261960.229Q37625261960.242Q37625261960.282Q38248387216.252Q39212284437.232Q39212284437.280Q42081808994.280Q42250421143.185Q42250421143.267Q42250505353.232Q42252699699.249Q42252699701.167Q43879899724.252Q43925228937.232Q43925228937.280Q49291908042.285Q49306541890.287Q49861398996.230Q49861398996.283Q50458135125.285Q52016320488.281Q52016320488.282Q52582070103.282Q5483308162.278 Q5485126037.229 Q5485126037.242 Q5485126037.282 Q5485174314.230 Q5485174314.243 Q5485174314.279 Q5485174314.283 Q59703481013.230Q6027349519.281 Q6027349519.282 Q60511567613.232Q60511567613.280Q60697995187.232Q60697995187.280Q6143569392.230 Q6143569392.243 Q6143569392.279 Q6143569392.283 Q61813135019.289Q61815603366.285Q61819782235.285Q62157788641.281Q62965564504.280Q62965564504.281Q63442345212.276Q6762438223.285 Q6764644418.289 Q6775036594.285 Q6775086905.282 Q6775135803.285 Q68317669980.273Q68317669980.274Q68317669980.275Q68330333437.197Q7891539809.279 Q8880503606.229 Q8880503606.277 Q8943555749.282 Q9538787269.229 Q9538787269.277 00000100200300400500600700W00n01N02802S02T02U02V02W02X02Y02Z02[03d04N04O05805S06=06h06i06j07[07\07]07^07_08J09509l0:c0:d0;B0<L0=H0=I0=J0=K0=L0=S0=Z0=^0=n0=o0>00>?0>@0>V0>a0>b0>c0>j0?10?20?@0?A0?B0?C0?R0?S0?i0?j0@F0@J0@j0A@0A[0B60B70BA0BM0BN0BO0B^0C60C70CF0CG0CH0Cf0D=0D>0DE0DF0DW0Dg0Dh0E30E;0Ec0FA0FE0FF0FU0F`0Fk0Fl0Fm0G@0GT0GU0H00HK0H`0Hd0He0Hi0Hj0Hk0Hn0Ho0I60IH0IZ0I[0I\0Ic0Id0J30J40J[0K=0K>0L00L_0MX0MY0MZ0N50Nb0Nc0Nd0Nn0O50OK0OU0O]0PQ0QE0QF0QQ0Q\0Qf0Qg0RW0RZ0R[0R\0Rn0SF0Sa0Sb0Si0Sj0Sk0T:0TO0T^0Te0U10U90U:0Ug0Uh0Ui0Um0Un0Uo0V00V10V20V30V40V50V60V70V80V90V:0V;0V<0V=0V>0V?0V@0VA0Vc0WE0Wg0X]0Y[0Y\0Y]0Y^0Y_0Z20ZE0Zo0[L0[n0\P0\b0]90]F0]X0^00^H0^_0_@0_W0_n0`@0`W0`d0a60aH0aX0aj0b70bN0b`0c70cD0cV0cn0dE0dW0do0e^0fR0gN0hB0i10iL0ic0j50jV0k=0k>0k?0kR0l60lW0lj0m<0mS0m`0n20nI0nV0nh0o:0o;0o\10@10U10e11?11T11k12812J12\12o13B13U14914X15715i16A16Y17117I17a17b17c17d17e18=18T18f19619K19[FFFFFFFS2ra2sp1X3xs02xs2jn2An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jnS2ra2sp1X3xs02xs2jn2An4SLEN4DLENS2ra2sp1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs2jn2An4ZLENFFFFFFFFS1R2ra2sp1X3xs02lo4SLO22xs2jn5NEEDR3LOS2X03SPR2An3An04ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stFS1R2ra2sp1X3xs02lo2xs2jn3LOS2An4SLEN4DLENS2ra2sp1X3xs02xs2jn2An4ZLENS2ra2sp1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs2jn2X03SPR4LEN12An3An04ZLENFFS1R3HIA2ra2sp1X3xs02lo2xs2jn2h22An4TOP24SLEN4DLENFFFFS3xs02xs3pXc2jn2JM4LEN12N12An4SLEN4DLEN3SEPS3xs02xs3pXc2jn2JM4LEN12N12An4SLEN4DLEN3SEPS1R2sp3xs02lo2xs3pXc2jn2JM3LOS3ALO4LEN12N12PC4SLEN4DLENS1R2sp3xs02lo2xs3pXc2jn2JM3LOS3ALO4LEN12N12PC4SLEN4DLENFS1X3xs02xs2jn4LEN12An3FXS4ZLENS1R2sp1X3xs02lo4SLO22xs2jn2JM5NEEDR3FSZ3DSX4LEN12N12An4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO22xs2jn5NEEDR3FSZ3DSX4ZLEN2HB5Ha_st5Hl_stFFFFS2jn2AnS2sp2loS2jnS1X2jn2N12An3FXSFFS2xs2jn4LEN12N1FS2dA2dB1v2jn2JM2BV3NR1S2jn2An3A47FFS2jn2N1S2jn2N1FS2lo2jn2An3FloFFFS2xs2jn4LEN12N1FS1R2sp2lo4SLO23NRA3SPRFS1R2sp2dA2dB2lo4SLO23NRM3SPRS2AnS2ra2sp1X3xs02xs2jn2An4SLEN4DLENS2ra2sp1X3xs02xs2jn2AnS2ra2sp1X3xs02xs2jn2An4ZLENS2ra2sp1X3xs02xs2jn2An4ZLENFS1R3HIA2hcS3pXc2jn3P47FFS2xs2jn4LEN12N1S2sp2dA2dB2jn3CNT3SPR2N1FS2sp2jn3CNT3SPRFFS1R2sp2lo4SLO22jn5NEEDR2An3FloS2ra2sp1X3xs02xs3pXc2jnFS2jn2N1FS2sp2dA2dB2jn3NR1S1R3HIA1h2sp3TOPFS2xs2jn3HVVS2jn3NR1S2ra2sp1X3xs02xs2jn3CNT3NR12An4SLEN4DLENS2ra2sp1X3xs02xs2jn3CNT3NR12AnS2spFS2xs2jn4LEN12N1S1d2D01f2BFS1d2D01f2BFSFS2sp2lo3pXc2jn4XLScS1R2sp2dA2dB2lo4SLO2FS1R3HIA2sp2lo2h24TOP25HTOP2S1R3HIA2sp2lo2h44TOP45HTOP4S1R3HIA1h2sp2lo3TOP1HS2spFS2loFSS1XFS2jn2AnS2sp2dA2dB3SPA3SPRS2sp2dA2dB3SPA3SPRFFS2sp2loFS2jn2N12An1a2NOFS2ra2sp1X3xs02xs2jn2X03X162An4SLEN4DLENS2ra2sp1X3xs02xs2jn2X03X162An4ZLENFS2ra2sp1X3xs02xs2jn2X03SPR2N12An3An04SLEN4DLEN3A47S1R3HIA1h2sp2dA2dB3BUD1v2jn2JM2BV3SPR2N12h23HV1S2ra2sp1X3xs02xs3pXc2jn2X03SPR2N12P03P472An3An04SLEN4DLENSFS2ra2sp1X3xs02xs2jn2An4ZLENS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2BF3SPR2h24HFR1FFS1X2X03X16S2jn2AnS2dA2dB1v2jn2JM2BV3NR1S1R3HIA2h2S2jn3CNTS2ra2sp1X3xs02xs2jn2X03SPR4LEN12An3An03A474ZLEN4LEN5S2ra2sp1X3xs02xs2jn2X03SPR4LEN12An3An03A474ZLEN4LEN5FS3pXc2P02KPS2An3An02KZS1R2lo3LOSFS1R3HIA1h2sp2dA2dB3BUD1v2hc2jn2JM2BV3SPR3NR13HV1S1RFFS1R3HIA2sp2h24TOP2S1R3HIA2sp2dA2dB2h24TOP2S2ra2sp1X3xs02xs2jn2An4ZLENFS2jn2N1FFS2xs2jn4LEN12N1S2sp2dA2dB2jn3CNT3SPRS3pXc2jn2An3SEPS2jn2N1S2xs2jn4LEN1S2jn3NR1FS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2hc2BF3SPR4HFR1FFS2jnFFFFFFFFFFFFFFFFFFFFS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2An3Flo4ZLEN3AC5S1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2N12An3AnC3Flo4SLEN4DLENFFFFS3xs02xs2jn2An4ZLENS3xs02xs2jn2An4ZLENS2ra2sp1X3xs02xs2jn2X03XAL2N12An4SLEN4DLENS2ra2sp1X3xs02xs2jn2X03XAL2AnS2ra2sp1X3xs02xs2jn2X03XAL2An4ZLENS2ra2sp1X3xs02xs2jn2X03XAL2An4ZLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS3xs02xs2jn2An4SLEN4DLENS3xs02xs2jn2An4SLEN4DLENS3xs02xs2jn2An3A474ZLENS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4ZLENS3xs02xs2jn4ZLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jnS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS3xs02lo2xs2jn4SLEN4DLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn2X04ZLEN2HBS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP2N14SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACPS2sp3xs02lo2xs2jn4SLEN4DLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS3xs02xs2jn4LEN12An3An04ZLEN4LEN5S3xs02xs2jn4LEN12An3An04ZLEN4LEN55HBarrFFS3xs02xs2jn2An4ZLENS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS3xs02xs2jn2An4ZLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4ZLENFS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS3xs02xs2jn4SLEN4DLENS3xs02xs2jn4ZLENS1X3xs02xs2jn2X04SLEN4DLENS1X3xs02xs2jn2X04ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4ZLENS3xs02xs2jn2An4ZLENS3xs02xs2jn2An4ZLENS3xs02xs2jn2An4ZLENS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn3X164ZLEN2HB5Ha_stS1X3xs02xs2jn3X164ZLEN2HB5Ha_stS1R2sp3xs02lo4SLO22xs3pXc2jn5NEEDR3LOS3ALO2PC4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENFFFFS1X3xs02xs2jn2X04ZLEN2HBS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS3xs02xs2jn4ZLENS3xs02xs2jn4SLEN4DLENS3xs02xs2jn4ZLEN". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2"] Lemma aa_G3 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pxs,(1.(3.&40.))PpXc,$8.Pjn,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R1;.R1:.R19.R18.R17.(48.VX,+1.R14.R15.R16.VpadX,$1:.))P,(22.(23.R15.+1.)+2710.)P,(22.R16.$5<.)P,(10.$8.(23.(54.R19.)(5?.+2.(1<.+20.R17.)))$4=.)P,(22.R1?.$56.)P,(22.R1?.$57.)(50.$47.(51.$47.VR,VHIA,R1?.Vmo,)$52.(43.(44.R19.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R18.R17.R16.(29.&40.VX,)(29.&40.(23.VX,+:.))R15.R14.(29.&40.+1.)R13.R12.R11.R10.R?.(29.&40.R1:.)R>.R=.(29.&40.(58.(2=.VR,)))(29.&40.(23.(1<.+4.R1:.)+4.))(29.&40.(23.(59.(23.VX,+:.)+3.)(58.(2=.VR,))))(29.&40.(23.(59.VX,+3.)(58.(2=.VR,))))R<.R;.Vs11,R:.R9.R8.R7.)VF,(29.&40.+9=<:0.)Vfc,(45.(3.&40.))R1=.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J CNT JM HVV BV BF. jc_open.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    xa_open J. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc. pose proof (XP1 eq_refl) as XPc.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in ST1, FR1 by (clear; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 (jn + 1)) with (Z_to_bv 64 (jn + 1)) by reflexivity.
    replace (Z_to_bv 64 429840) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (cnt := jn + 1) (sz := 4) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; try eassumption; try reflexivity.
      all: try (apply c24_of_transition; exact C24T).   (* [comment removed for export] *)
      all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
      all: try (rewrite HT1; clear - TOP; lia).
      all: try (f_equal; clear; lia).
      all: unfold aaV1, aaF1, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
           clear - CNT JM NR1 NR LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP; try lia.
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2. clear MU WM.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof ST2 as ST2'.
    assert (HP2' : presA asegs R LBc LF (bv_unsigned sp - 96) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m2).
    { eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2, HT1; exact TOP).
    destruct CASES as [[Er HH2] | (An & Er & A16 & HFRA & HAS & HH2 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - (* [comment removed for export] *)
      pose proof (xa_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep.
      eapply aa_retm16; [exact J2| |].
      + unfold aaV1, aaM, add_abs_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT JM NR1. lia.
      + unfold aaF1, add_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      replace ((jn + 1) * 4) with (4 * (jn + 1)) in HFRA, HAS, HH2, HNEW, HV2 by (clear; lia).
      destruct (xa_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ An (jn + 1) J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW
                  ltac:(cbn [md_n]; clear - CNT NR1; lia)) as [J2 F2].
      dpose HFRA as (An0 & AnC & AnD & HAP).
      clear J. try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. try clear STc; try clear CX1.
      xa_open J2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2 & _ & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2, OWN1. unfold mpi_cells in CX2.
      try clear XIN; try clear XPAL; try clear XARR; try clear PI; try clear OP. ddestruct (OWN1 ltac:(discriminate)) as (_ & _ & XIN & _ & XARR & _ & _ & _ & OP & _). clear OWN1.
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH1) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      pose proof F2 as [Ffr Ffr0 Fal Fnew Fnewc Fap Farr Flen Fcnt FXS Flo]. cbn [md_n] in Fcnt.
      destruct (xga_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J2 F2 eq_refl)
        as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _ & OA & OP' & _ & A47 & INA & INP).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP, OA, OP', A47, INA, INP.
      rewrite firstn_length in DST, DLEN. rewrite repeat_length in DST, DLEN.
      replace (Init.Nat.min (Z.to_nat jn) (Z.to_nat (jn + 1))) with (Z.to_nat jn) in DST, DLEN by (clear - CNT N1; lia).
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - An0 AnC H; lia); clear - KZ An0; lia|]. clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KP; zify_cond KP; [exfalso; first [rewrite Z.mod_small in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H N1; lia) | idtac]; clear - KP P0; lia|]. clear KP.
      (* [comment removed for export] *)
      shadow_chk OX1 (X + 10) 2.
      zstep.
      replace (zx16 (Z_to_bv 64 jn)) with (Z_to_bv 64 jn)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
      zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
      pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_AA) as SPC. unfold A_ASAN_MEMCPY_AA in SPC.
      apply (u8arr_of_rw_cells asegs) in DST.
      clear MU WM. pose proof (munch_refl [(An, An + 4 * jn); (lo, bv_unsigned sp + -96)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      acallxA_sp (bv_unsigned sp + -96)
        (eapply SPC with (h := h2) (LB := (An, 4 * (jn + 1)) :: LBc) (LF := LF) (DST := An) (SRC := pXc) (n := 4 * jn) (lo := lo)
                          (ss := u32s xs);
         rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia;
         try eassumption; try reflexivity;
         first [ left; rewrite AMC; reflexivity
               | rewrite u32s_length, firstn_length, repeat_length; clear - N1 CNT; lia
               | rewrite u32s_length; clear - LEN1 N1; lia
               | eapply aobj_sub; [exact OA| clear; lia| clear - CNT N1; lia]
               | right; clear - SEP; lia
               | left; clear - Flo CNT N1 SLO2 NEEDR; lia
               | clear - XLSc SLO2 NEEDR; lia
               | right; clear - A47 CNT N1; lia
               | right; clear - P47; lia
               | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
               | eapply client_wrange_block; [apply in_or_app; left; left; reflexivity| clear; lia| clear - CNT N1; lia]
               | f_equal; clear; lia
               | clear - NR1 N1 CNT LOS SLO SLO2 NEEDR NRA TOP2 SPA SPR; lia
               | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ]).
      clear SPC.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : u8arr asegs m3 An (u32s xs) |- _ => rename H into HPA end.
      match goal with H : stk asegs m3 lo (bv_unsigned sp + -96) |- _ => rename H into ST3 end.
      match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
      match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
      match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 X 16 |- _ => rename H into OX3 end.
      pose proof ST3 as ST3'.
      apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
      replace (4 * length xs)%nat with (Z.to_nat (4 * jn)) in HPA by (clear - LEN1 N1; lia).
      destruct (xga_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m3 J2 F2 eq_refl MU WM MI3 ST3' HPA HH3 OX3) as [J3 F3].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J3, F3.
      clear J2 F2 OA OP' SBY SLEN DLEN INA INP.
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. xa_open J3. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      try clear CX2. pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J3) as (_ & _ & _ & _ & CX3 & _ & _).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
      (* [comment removed for export] *)
      clear MU WM. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      zstep. zstep. zstep.
      replace (zx16 (Z_to_bv 64 jn)) with (Z_to_bv 64 jn)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
      zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
      destruct (xga_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB & ZN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ZIN, ZCH, ZLEN, ZB.
      pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
      eapply aevtA_call.
      { intros mo3 [HK3 MF3].
        eapply SPZ with (h := h2) (LB := (An, 4 * (jn + 1)) :: LBc) (LF := LF) (buf := pXc) (len := 4 * jn) (lo := lo) (d := d) (junk := u32s xs);
          rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; try eassumption; try reflexivity.
        all: try (right; split; [exact ZIN | rewrite <- ZLEN; exact ZCH]).
        all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
        all: try (f_equal; clear; lia).
        all: unfold aaV1, aaF1, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
             clear - CNT JM NR1 NR N1 LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP TOP2; try lia.
        all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
      clear SPZ.
      (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
      destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in PO by qlia.
      ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
      match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
      presA_transport HP4.
      pose proof ST4 as ST4'.
      assert (HP4' : presA asegs R (lb_remove pXc ((An, 4 * (jn + 1)) :: LBc)) LF (bv_unsigned sp - 96) (arl_stklo R) (hstkhi asegs R HIA h2)
                       [(pXc, pXc + 4 * jn)] m3 m4).
      { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
      pose proof (xga_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 eq_refl MI4 ST4' HP4' HT4 HS4 HF4 HCS4 HV4 HFR4 HH4) as D4.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in D4.
      assert (HT4h : htop asegs R HIA h4 = htop asegs R HIA h) by (rewrite HT4; exact HT1).
      assert (HS4h : hstkhi asegs R HIA h4 = hstkhi asegs R HIA h) by (rewrite HS4; exact HS1).
      apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
      clear CSOK SB64 SCS0 SCS HTOP2.
      pose proof (hcs_ok asegs R HIA h4) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h4) as SCS0.
      assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. clear J3 F3 HP4 HP4'. try clear ZCH; try clear ZB; try clear XARR; try clear OP; try clear HH2.
      pose proof D4 as [DMI DST4 DFR DHM DHT DHS DHF DHCS DHV DHFR DCX DSG DSUB DKEEP DGONE DNEW DAPART DARR DLEN4 DCNT DXS DPRES DFRESH DAL DOX DLO DNM].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in DCX, DOX, DHM, DARR, DLEN4. unfold mpi_cells in DCX.
      pose proof (hm_top asegs R HIA h4 _ LF m4 DHM) as HTOP4.
      assert (SCS : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP4 HTOP4; lia]).
      pose proof (xda_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ D4) as CW5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CW5.
      rewrite <- HT4h in CW5.
      pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      (* [comment removed for export] *)
      zstep.
      shadow_chk DOX (X + 10) 2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
      pose proof (xda_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ D4 MU WM MI5 DCX DHM DOX) as J5.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5. rewrite skipn_repeat in J5.
      replace (Z.to_nat (jn + 1) - Z.to_nat jn)%nat with 1%nat in J5 by (clear - CNT N1; lia). cbn [repeat] in J5.
      clear D4 DST4 DFR DHT DHS DHF DHCS DHV DHFR DSG DSUB DKEEP DGONE DNEW DAPART DLEN4 DCNT DXS DPRES DFRESH DAL DLO DNM CW5.
      try clear DMI; try clear DARR; try clear DCX; try clear DOX; try clear DHM.
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1.
      xa_open J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J5) as (_ & LEN5 & _ & _ & CX5 & _ & OWN5).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX5, LEN5, OWN5. unfold mpi_cells in CX5.
      ddestruct (OWN5 ltac:(discriminate)) as (_ & _ & AIN & _ & AARR & _ & AC5 & _ & OA5 & _). clear OWN5.
      assert (CWA : client_wrange L (((An, 4 * (jn + 1)) :: lb_remove pXc LBc) ++ fdata LF) (arl_stklo R) (htop asegs R HIA h4) An (4 * (jn + 1)))
        by (eapply client_wrange_block; [left; reflexivity| clear; lia| clear; lia]).
      assert (NTH : nth_error (xs ++ [Z_to_bv 64 0]) (Z.to_nat jn) = Some (Z_to_bv 64 0)).
      { rewrite nth_error_app2 by (clear - LEN1 N1; lia). replace (Z.to_nat jn - length xs)%nat with 0%nat by (clear - LEN1 N1; lia). reflexivity. }
      clear MU WM. pose proof (munch_refl [(An + 4 * jn, An + 4 * jn + 4)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 (An + (4 * jn + 4) + -4)) with (Z_to_bv 64 (An + 4 * jn)) by (f_equal; clear; lia).
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OA5 (An + 4 * jn) 4.
      (* [comment removed for export] *)
      pose proof (u32arr_read asegs m5 An (xs ++ [Z_to_bv 64 0]) jn (Z_to_bv 64 0) _ AARR NTH ltac:(clear - N1; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD.
      (* [comment removed for export] *)
      zstep.
      pose proof (u32arr_store_ok asegs m5 An (xs ++ [Z_to_bv 64 0]) jn _ AARR ltac:(rewrite length_app; cbn [length]; clear - LEN1 N1; lia) ltac:(f_equal; clear; lia)) as SOKw.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
        pose proof (u32arr_write asegs m5 An (xs ++ [Z_to_bv 64 0]) jn vv AARR ltac:(rewrite length_app; cbn [length]; clear - LEN1 N1; lia)) as AARR' end.
      store_done.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo _ |- _ => rename H into ST6 end.
      match goal with H : HM asegs R HIA h4 _ LF m6 |- _ => rename H into HH6 end.
      assert (HW6 : forall a, ~ outside [(An + 4 * jn, An + 4 * jn + 4)] a -> (LHeap = LHeap /\ An <= a < An + 4 * (jn + 1)) \/ lo <= a < bv_unsigned sp - 96).
      { intros a NO. left. split; [reflexivity|]. cbn [outside] in NO. clear - NO N1. lia. }
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J5 MU WM MI6 ST6 HH6 HW6
                    ltac:(cbn; split; [clear - Flo SLO2 NEEDR N1; lia| exact I]) ltac:(cbn; split; [clear - FXS N1; lia| exact I]) AARR'
                    ltac:(rewrite upd_length; reflexivity)) as J6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
      (* [comment removed for export] *)
      zstep.
      eapply aa_ret0; [exact J6| | reflexivity| |].
      * unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_upd by (rewrite length_app; cbn [length]; clear - LEN1 N1; lia).
        rewrite (limb32_w32_nth _ _ _ NTH).
        change (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 0)) + 1))) mod 2 ^ 32)
          with (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 0)) + 1)))).
        rewrite w32_incr. unfold w32. rewrite (unsigned_lit 0) by (clear; lia).
        change ((0 mod 2 ^ 32 + 1) mod 2 ^ 32) with 1. change (0 mod 2 ^ 32) with 0.
        rewrite limbs_val_app. cbn [limbs_val]. rewrite ?(unsigned_lit 0) by (clear; lia). change (0 mod 2 ^ 32) with 0.
        replace (Z.of_nat (Z.to_nat jn)) with jn by (clear - N1; lia). rewrite LEN1. clear - HVV. lia.
      * unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT JM NR1. lia.
      * unfold aaF1, add_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    all: match goal with |- ?g => idtac "G3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04O0@C17025492443.246C17025492443.247C17025492443.248C40893063684.288C53526081063.249C53526081063.250C53526081063.251D17975678776.252D21361708665.199D22466435734.252D24976250634.280D27965255826.276D34348047352.196D34348047352.199D34352354649.270D34352354649.272D34352354649.277D37969448224.271D37969448224.278D37981848449.197D50797141399.280D52014138856.280D59228252318.280D60109446735.252D61815348395.287D62155808737.280D6762693186.287 D7340709316.252 D8414535367.276 D939044794.252  K1329197271.249 K1329197271.250 K1329197271.251 K23468015258.288K2612272047.248 K2612272047.252 K32761642720.248K32761642720.252K38856059124.281K52322685826.288K61206821897.280K61206821897.281K6379668000.246 K6379668000.247 K6379668000.248 K7412424035.252 L10559054258.4  L10947173192.14 L11656196980.1  L12416934887.5  L12755534717.8  L12755534717.9  L12905641847.4  L1342025005.2   L14051382092.8  L15198982830.3  L16473205958.5  L16473494895.4  L17437327158.278L17585880332.13 L17703443598.3  L17830241467.3  L18587013051.13 L20630580640.10 L20803911415.2  L21073294716.9  L21086251255.8  L21297056158.4  L21847519070.3  L21860237213.17 L21860433226.8  L21860695708.32 L22479292268.1  L23100341967.223L23100341967.235L23100341967.267L23100341967.273L23455462144.3  L23615739305.3  L24313534829.3  L24313585860.4  L24313813357.6  L24799912036.4  L25119086869.34 L25132156744.1  L25138051168.17 L25138248375.8  L25142208316.1  L25232169794.9  L2607826517.4   L26228513507.2  L26660323117.1  L26673455472.32 L27214106967.5  L27572020408.8  L27747017808.5  L27835269521.2  L27835396370.223L27837255469.234L27966909654.1  L28655862141.3  L28671776394.4  L30483066123.4  L31325970818.4  L32027975233.0  L32754825233.4  L32761511569.8  L34412813842.34 L34424803280.3  L35655538624.7  L35655538630.7  L35663928186.7  L36180290948.1  L37969005188.5  L38235734261.1  L38868673902.4  L39172636981.0  L39188636933.0  L40294887048.3  L40449602357.4  L41112120439.32 L41112120439.34 L41116237108.1  L43343741601.15 L43878034250.5  L44196988417.11 L44611170703.5  L4482322106.10  L46380960401.4  L46756382136.223L46948640662.34 L48154966246.223L49150310671.4  L49578233423.267L49579218529.34 L51216332057.10 L51751604631.199L52318461464.3  L5261871668.3   L53314392638.2  L53404598366.8  L547707976.3    L54817154178.3  L55190826961.272L55191156004.275L57258774030.15 L59107603233.0  L59308632307.3  L59308633593.3  L60098763854.3  L61212928741.14 L61562785068.32 L62018535662.1  L63070224179.10 L63070224179.4  L63074471475.17 L63074930482.34 L63440801702.15 L63654471873.2  L6384586821.2   L63849440564.1  L65496508708.4  L66581468868.32 L66661851587.4  L67180826602.3  L67180826602.4  L67725245073.2  L7400112281.3   L7419031306.32  L7704260991.4   L8414648675.5   L8890516472.1   O17025492443.246O17025492443.247O17025492443.248O22987107037.248O22987107037.252O32329373691.252O37539299629.246O37539299629.247O37539299629.248O41427663046.251O45218884275.248O45218884275.252O53526081063.249O53526081063.250O53526081063.251P1329197271.249 P1329197271.250 P1329197271.251 P23468015258.288P38856059124.281P40437264079.246P40437264079.247P40437264079.248P43347971899.288P57246471156.251P6379668000.246 P6379668000.247 P6379668000.248 P7412424035.252 Q10203249998.283Q11801279589.287Q12370813529.231Q12370813529.243Q12370813529.277Q12370813529.281Q17205055869.276Q17207432298.230Q17207432298.242Q17207432298.280Q17975678776.252Q22466435734.252Q22642964918.286Q24416901192.231Q24418772599.277Q24418818504.232Q24418818504.278Q24974040330.280Q26207967338.242Q26207967338.277Q26209773141.231Q26295627581.283Q29201240740.231Q29203049627.277Q31651666684.231Q31653536963.242Q31653536963.277Q36081244985.232Q36081244985.278Q37623376543.276Q37625261960.230Q37625261960.242Q37625261960.280Q38248387216.252Q42081808994.278Q42250421143.186Q42250421143.267Q42250505353.232Q42252699699.249Q42252699701.168Q42766971027.232Q43879899724.252Q46720892458.232Q49291908042.283Q49306541890.285Q49861398996.231Q49861398996.281Q50458135125.283Q52016320488.279Q52016320488.280Q52582070103.280Q5483308162.276 Q5485126037.230 Q5485126037.242 Q5485126037.280 Q5485174314.231 Q5485174314.243 Q5485174314.277 Q5485174314.281 Q56512145356.232Q56512145356.278Q59703481013.231Q6027349519.279 Q6027349519.280 Q6143569392.231 Q6143569392.243 Q6143569392.277 Q6143569392.281 Q61813135019.287Q61815603366.283Q61819782235.283Q62157788641.279Q62965564504.278Q62965564504.279Q63442345212.276Q6762438223.283 Q6764644418.287 Q6775036594.283 Q6775086905.280 Q6775135803.283 Q68317669980.273Q68317669980.274Q68317669980.275Q68330333437.198Q7891539809.277 Q8943555749.280 00000100200300400500600700W00n01N02802S02T02U02V02W02X02Y02Z02[03d04N04O05805S06=06h06i06j07[07\07]07^07_08J09509l0:c0:d0;B0<L0=H0=I0=J0=K0=L0=S0=Z0=^0=n0=o0>00>?0>@0>V0>_0>j0>k0?F0?G0?N0?U0?V0?d0?e0?f0?g0@60@70@M0@N0@j0@n0AN0Ad0B?0BZ0B[0Be0C10C20C30CB0CZ0C[0Cj0Ck0Cl0DJ0DK0DR0DS0Dd0E40E50E@0EH0F00FN0FR0FS0Fb0Fm0G80G90G:0GM0Ga0Gb0H=0HX0Hm0I10I20I60I70I80I90I<0I=0IO0Ia0Ib0Ic0Ij0Ik0J:0J;0J<0Jn0K]0LV0LW0M20M_0M`0N70N80NB0NI0N_0Ni0O10Oe0PY0PZ0P[0Pf0Q10Q;0Q<0Ql0Qo0R00R10RC0R[0R\0Rc0Rd0Re0S40SI0SX0S_0Sk0T30T40Ta0Tb0Tc0Tg0Th0Ti0Tj0Tk0Tl0Tm0Tn0To0U00U10U20U30U40U50U60U70U80U90U:0U;0U]0V?0Va0WW0XU0XV0XW0XX0XY0Xl0Y?0Yi0ZF0Zh0[J0[\0\30\@0\R0\j0]B0]Y0^00^B0^Y0^k0_L0_Y0_k0`B0`R0`i0a;0aR0a_0b10bH0bZ0bl0cC0cP0cb0d:0dR0eA0f50g10ge0hT0hU0i00i10iR0j90j:0j;0jN0k20kS0kf0l80lO0l\0ln0mE0mR0md0n60nk0o`0oa10B10f11=11J11\11n12A12T12g13K13j14I15;15S15k16C16[17317417517617717O17_FFFFFFFS2ra2sp1X3xs02xs2jn2An4SLEN4DLENS2ra2sp1X3xs02xs3pXc2jnS2ra2sp1X3xs02xs2jn2An4SLEN4DLENS2ra2sp1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs2jn2An4ZLENFFFFFFFFS1R2ra2sp1X3xs02lo4SLO22xs2jn5NEEDR3LOS2X03SPR2An3An04ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stFS1R2ra2sp1X3xs02lo2xs2jn3LOS2An4SLEN4DLENS2ra2sp1X3xs02xs2jn2An4ZLENS2ra2sp1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs2jn2X03SPR4LEN12An3An04ZLENFFS1R3HIA2ra2sp1X3xs02lo2xs2jn2h22An4TOP24SLEN4DLENFFFFS3xs02xs3pXc2jn2JM4LEN12N12An4SLEN4DLEN3SEPS3xs02xs3pXc2jn2JM4LEN12N12An4SLEN4DLEN3SEPS1R2sp3xs02lo2xs3pXc2jn2JM3LOS3ALO4LEN12N12PC4SLEN4DLENS1R2sp3xs02lo2xs3pXc2jn2JM3LOS3ALO4LEN12N12PC4SLEN4DLENFS1X3xs02xs2jn4LEN12An3FXS4ZLENS1R2sp1X3xs02lo4SLO22xs2jn2JM5NEEDR3FSZ3DSX4LEN12N12An4ZLEN2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO22xs2jn5NEEDR3FSZ3DSX4ZLEN2HB5Ha_st5Hl_stFFFFS2jn2AnS2sp2loS2jnS1X2jn2N12An3FXSFFS2xs2jn4LEN12N1FS2dA2dB1v2jn2JM2BV3NR1S1R1X3XALS2jn2An3A47FS2ra2sp1X3xs02xs2jn2An4ZLENFS2jn2N1S2jn2N1FS2lo2jn2An3FloFFFS2xs2jn4LEN12N1FS1R2sp2lo4SLO23NRA3SPRFS1R2sp2dA2dB2lo4SLO23NRM3SPRS2AnS2ra2sp1X3xs02xs2jn2An4SLEN4DLENS2ra2sp1X3xs02xs2jn2AnS2ra2sp1X3xs02xs2jn2An4ZLENS2ra2sp1X3xs02xs2jn2An4ZLENFS1R3HIA2hcS3pXc2jn3P47FFS2xs2jn4LEN12N1S2sp2dA2dB2jn3CNT3SPR2N1FS2sp2jn3CNT3SPRFFS1R2sp2lo4SLO22jn5NEEDR2An3FloFS2jn2N1FS2sp2dA2dB2jn3NR1S1R3HIA1h2sp3TOPFS2xs2jn3HVVS2jn3NR1S2ra2sp1X3xs02xs2jn3CNT3NR12An4SLEN4DLENS2ra2sp1X3xs02xs2jn3CNT3NR12AnS2spFS2xs2jn4LEN12N1S1d2D01f2BFS1d2D01f2BFSFS2sp2lo3pXc2jn4XLScS1R2sp2dA2dB2lo4SLO2FS1R3HIA2sp2lo2h24TOP25HTOP2S1R3HIA2sp2lo2h44TOP45HTOP4S1R3HIA1h2sp2lo3TOP1HS2spFS2loFSSS1XFS2sp2dA2dB3SPA3SPRS2sp2dA2dB3SPA3SPRFFS2sp2loFS2jn2N12An1a2NOFFS2ra2sp1X3xs02xs2jn2X03SPR2N12An3An04SLEN4DLEN3A47S1R3HIA1h2sp2dA2dB3BUD1v2jn2JM2BV3SPR2N12h23HV1S2ra2sp1X3xs02xs3pXc2jn2X03SPR2N12P03P472An3An04SLEN4DLENFS2ra2sp1X3xs02xs2jn2An4ZLENS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2BF3SPR2h24HFR1FS2ra2sp1X3xs02xs3pXc2jnFS1X2X03X16S2jn2AnS2dA2dB1v2jn2JM2BV3NR1S1R3HIA2h2S2jn3CNTS2ra2sp1X3xs02xs2jn2X03SPR4LEN12An3An03A474ZLEN4LEN5S2ra2sp1X3xs02xs2jn2X03SPR4LEN12An3An03A474ZLEN4LEN5FSS3pXc2P02KPS2An3An02KZS1R2lo3LOSFS1R3HIA1h2sp2dA2dB3BUD1v2hc2jn2JM2BV3SPR3NR13HV1S1RFFS1R3HIA2sp2h24TOP2S1R3HIA2sp2dA2dB2h24TOP2FS2jn2N1FFS2xs2jn4LEN12N1S2sp2dA2dB2jn3CNT3SPRS3pXc2jn2An3SEPS2jn2N1S2xs2jn4LEN1S2jn3NR1FS1R3HIA1h2sp2dA2dB1d2D04BUDF1f2hc2BF3SPR4HFR1FFS2jnFFFFFFFFFFFFFFFFFFFFS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS2sp3xs02lo2xs2jn2An3Flo4SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2An3Flo4ZLEN3AC5S1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS3ALO2N12An3AnC3Flo4SLEN4DLENFFFFS3xs02xs2jn2An4ZLENS3xs02xs2jn2An4ZLENS2ra2sp1X3xs02xs2jn2X03XAL2N12An4SLEN4DLENS2ra2sp1X3xs02xs2jn2X03XAL2AnS2ra2sp1X3xs02xs2jn2X03XAL2An4ZLENS2ra2sp1X3xs02xs2jn2X03XAL2An4ZLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS3xs02xs2jn2An4SLEN4DLENS3xs02xs2jn2An4SLEN4DLENS3xs02xs2jn2An3A474ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS3xs02lo2xs2jn4SLEN4DLENS1X3xs02xs2jn2X04ZLEN2HBS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP2N14SLEN4DLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACP4ZLENS1R2sp3xs02lo4SLO22xs2jn5NEEDR3LOS4SP643ALO3ACPFS2sp3xs02lo2xs2jn4SLEN4DLENFS3xs02xs2jn4LEN12An3An04ZLEN4LEN5S3xs02xs2jn4LEN12An3An04ZLEN4LEN55HBarrFFS3xs02xs2jn2An4ZLENS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS3xs02xs2jn2An4ZLENS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4ZLENS2ra2sp1X3xs02xs2jn2JM2X03XAL3SPR2N12An3An04SLEN4DLENS2ra2sp1X3xs02xs2jn2JM2X03XAL3SPR4LEN12N12An3An04ZLENFS1X3xs02xs2jn4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn4SLEN4DLENS1X3xs02xs2jnS1X3xs02xs2jn4ZLENS1X3xs02xs2jn4ZLENS3xs02xs2jn2An4ZLENS3xs02xs2jn2An4ZLENS3xs02xs2jn2An4ZLENS1X3xs02xs2jn2An4ZLEN2HB5Ha_st5Hl_stS1X3xs02xs2jn3X164ZLEN2HB5Ha_stS1X3xs02xs2jn3X164ZLEN2HB5Ha_stS1R2sp3xs02lo4SLO22xs3pXc2jn5NEEDR3LOS3ALO2PC4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENS3xs02xs2jn4LEN12An4ZLENFFFFS1X3xs02xs2jn2X04ZLEN2HBS3xs02xs2jn4ZLEN". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2"] Lemma aa_G2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pxs,(1.(3.&40.))PpXc,$8.Pjn,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R1<.R1;.R1:.R19.R18.(48.VX,+1.R15.R16.R17.VpadX,$1:.))P,(22.(23.R16.+1.)+2710.)P,(22.R17.$5<.)P,(10.$8.(23.(54.R1:.)(5?.+2.(1<.+20.R18.)))$4=.)P,(22.R20.$56.)P,(22.R20.$57.)(50.$47.(51.$47.VR,VHIA,R20.Vmo,)$52.(43.(44.R1:.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R19.R18.R17.(29.&40.VX,)(29.&40.(23.VX,+:.))R16.R15.R14.R13.R12.R11.R10.R?.(29.&40.(23.R1;.+1.))R>.R=.(29.&40.(58.(2=.VR,)))(29.&40.(1<.+4.R1;.))(29.&40.(23.(59.(23.VX,+:.)+3.)(58.(2=.VR,))))(29.&40.(23.(59.VX,+3.)(58.(2=.VR,))))R<.R;.Vs11,R:.R9.R8.R7.)VF,(29.&40.+9==88.)Vfc,(45.(3.&40.))R1>.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J CNT JM HVV BV BF. jc_open.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    xa_open J. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc. pose proof (XP1 eq_refl) as XPc.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in ST1, FR1 by (clear; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 429840) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (cnt := jn + 1) (sz := 4) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; try eassumption; try reflexivity.
      all: try (apply c24_of_transition; exact C24T).   (* [comment removed for export] *)
      all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
      all: try (rewrite HT1; clear - TOP; lia).
      all: try (f_equal; clear; lia).
      all: unfold aaV1, aaF1, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
           clear - CNT JM NR1 NR LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP; try lia.
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2. clear MU WM.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof ST2 as ST2'.
    assert (HP2' : presA asegs R LBc LF (bv_unsigned sp - 96) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m2).
    { eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2, HT1; exact TOP).
    destruct CASES as [[Er HH2] | (An & Er & A16 & HFRA & HAS & HH2 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - (* [comment removed for export] *)
      pose proof (xa_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep.
      eapply aa_retm16; [exact J2| |].
      + unfold aaV1, aaM, add_abs_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT JM NR1. lia.
      + unfold aaF1, add_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      replace ((jn + 1) * 4) with (4 * (jn + 1)) in HFRA, HAS, HH2, HNEW, HV2 by (clear; lia).
      destruct (xa_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ An (jn + 1) J MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW
                  ltac:(cbn [md_n]; clear - CNT NR1; lia)) as [J2 F2].
      dpose HFRA as (An0 & AnC & AnD & HAP).
      clear J. try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. try clear STc; try clear CX1.
      xa_open J2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2 & _ & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2, OWN1. unfold mpi_cells in CX2.
      try clear XIN; try clear XPAL; try clear XARR; try clear PI; try clear OP. ddestruct (OWN1 ltac:(discriminate)) as (_ & _ & XIN & _ & XARR & _ & _ & _ & OP & _). clear OWN1.
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH1) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      pose proof F2 as [Ffr Ffr0 Fal Fnew Fnewc Fap Farr Flen Fcnt FXS Flo]. cbn [md_n] in Fcnt.
      destruct (xga_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J2 F2 eq_refl)
        as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _ & OA & OP' & _ & A47 & INA & INP).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP, OA, OP', A47, INA, INP.
      rewrite firstn_length in DST, DLEN. rewrite repeat_length in DST, DLEN.
      replace (Init.Nat.min (Z.to_nat jn) (Z.to_nat (jn + 1))) with (Z.to_nat jn) in DST, DLEN by (clear - CNT N1; lia).
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - An0 AnC H; lia); clear - KZ An0; lia|]. clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KP; zify_cond KP; [exfalso; first [rewrite Z.mod_small in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H N1; lia) | idtac]; clear - KP P0; lia|]. clear KP.
      (* [comment removed for export] *)
      assert (E10 : Z.shiftr (X + 10) 3 + al_sb AL = Z.shiftr X 3 + al_sb AL + 1)
        by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - XAL; lia).
      rewrite E10. zstep. zstep.
      zstep.
      replace (zx16 (Z_to_bv 64 jn)) with (Z_to_bv 64 jn)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
      zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
      pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_AA) as SPC. unfold A_ASAN_MEMCPY_AA in SPC.
      apply (u8arr_of_rw_cells asegs) in DST.
      clear MU WM. pose proof (munch_refl [(An, An + 4 * jn); (lo, bv_unsigned sp + -96)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      acallxA_sp (bv_unsigned sp + -96)
        (eapply SPC with (h := h2) (LB := (An, 4 * (jn + 1)) :: LBc) (LF := LF) (DST := An) (SRC := pXc) (n := 4 * jn) (lo := lo)
                          (ss := u32s xs);
         rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia;
         try eassumption; try reflexivity;
         first [ left; rewrite AMC; reflexivity
               | rewrite u32s_length, firstn_length, repeat_length; clear - N1 CNT; lia
               | rewrite u32s_length; clear - LEN1 N1; lia
               | eapply aobj_sub; [exact OA| clear; lia| clear - CNT N1; lia]
               | right; clear - SEP; lia
               | left; clear - Flo CNT N1 SLO2 NEEDR; lia
               | clear - XLSc SLO2 NEEDR; lia
               | right; clear - A47 CNT N1; lia
               | right; clear - P47; lia
               | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
               | eapply client_wrange_block; [apply in_or_app; left; left; reflexivity| clear; lia| clear - CNT N1; lia]
               | f_equal; clear; lia
               | clear - NR1 N1 CNT LOS SLO SLO2 NEEDR NRA TOP2 SPA SPR; lia
               | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ]).
      clear SPC.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : u8arr asegs m3 An (u32s xs) |- _ => rename H into HPA end.
      match goal with H : stk asegs m3 lo (bv_unsigned sp + -96) |- _ => rename H into ST3 end.
      match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
      match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
      match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 X 16 |- _ => rename H into OX3 end.
      pose proof ST3 as ST3'.
      apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
      replace (4 * length xs)%nat with (Z.to_nat (4 * jn)) in HPA by (clear - LEN1 N1; lia).
      destruct (xga_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ m3 J2 F2 eq_refl MU WM MI3 ST3' HPA HH3 OX3) as [J3 F3].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J3, F3.
      clear J2 F2 OA OP' SBY SLEN DLEN INA INP.
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. xa_open J3. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      try clear CX2. pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J3) as (_ & _ & _ & _ & CX3 & _ & _).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
      (* [comment removed for export] *)
      clear MU WM. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      zstep. zstep. zstep.
      replace (zx16 (Z_to_bv 64 jn)) with (Z_to_bv 64 jn)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
      zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
      destruct (xga_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB & ZN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ZIN, ZCH, ZLEN, ZB.
      pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
      eapply aevtA_call.
      { intros mo3 [HK3 MF3].
        eapply SPZ with (h := h2) (LB := (An, 4 * (jn + 1)) :: LBc) (LF := LF) (buf := pXc) (len := 4 * jn) (lo := lo) (d := d) (junk := u32s xs);
          rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; try eassumption; try reflexivity.
        all: try (right; split; [exact ZIN | rewrite <- ZLEN; exact ZCH]).
        all: try (eapply (uw_obj_uwc asegs R); [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear - X0 X16; lia]).
        all: try (f_equal; clear; lia).
        all: unfold aaV1, aaF1, aaM, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
             clear - CNT JM NR1 NR N1 LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP TOP2; try lia.
        all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
      clear SPZ.
      (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
      destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in PO by qlia.
      ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
      match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
      presA_transport HP4.
      pose proof ST4 as ST4'.
      assert (HP4' : presA asegs R (lb_remove pXc ((An, 4 * (jn + 1)) :: LBc)) LF (bv_unsigned sp - 96) (arl_stklo R) (hstkhi asegs R HIA h2)
                       [(pXc, pXc + 4 * jn)] m3 m4).
      { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
      pose proof (xga_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 eq_refl MI4 ST4' HP4' HT4 HS4 HF4 HCS4 HV4 HFR4 HH4) as D4.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in D4.
      assert (HT4h : htop asegs R HIA h4 = htop asegs R HIA h) by (rewrite HT4; exact HT1).
      assert (HS4h : hstkhi asegs R HIA h4 = hstkhi asegs R HIA h) by (rewrite HS4; exact HS1).
      apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
      clear CSOK SB64 SCS0 SCS HTOP2.
      pose proof (hcs_ok asegs R HIA h4) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h4) as SCS0.
      assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. clear J3 F3 HP4 HP4'. try clear ZCH; try clear ZB; try clear XARR; try clear OP; try clear HH2.
      pose proof D4 as [DMI DST4 DFR DHM DHT DHS DHF DHCS DHV DHFR DCX DSG DSUB DKEEP DGONE DNEW DAPART DARR DLEN4 DCNT DXS DPRES DFRESH DAL DOX DLO DNM].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in DCX, DOX, DHM, DARR, DLEN4. unfold mpi_cells in DCX.
      pose proof (hm_top asegs R HIA h4 _ LF m4 DHM) as HTOP4.
      assert (SCS : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP4 HTOP4; lia]).
      pose proof (xda_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ D4) as CW5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CW5.
      rewrite <- HT4h in CW5.
      pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      (* [comment removed for export] *)
      rewrite ?E10. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
      pose proof (xda_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ _ _ D4 MU WM MI5 DCX DHM DOX) as J5.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5. rewrite skipn_repeat in J5.
      replace (Z.to_nat (jn + 1) - Z.to_nat jn)%nat with 1%nat in J5 by (clear - CNT N1; lia). cbn [repeat] in J5.
      clear D4 DST4 DFR DHT DHS DHF DHCS DHV DHFR DSG DSUB DKEEP DGONE DNEW DAPART DLEN4 DCNT DXS DPRES DFRESH DAL DLO DNM CW5.
      try clear DMI; try clear DARR; try clear DCX; try clear DOX; try clear DHM.
      try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1.
      xa_open J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J5) as (_ & LEN5 & _ & _ & CX5 & _ & OWN5).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX5, LEN5, OWN5. unfold mpi_cells in CX5.
      ddestruct (OWN5 ltac:(discriminate)) as (_ & _ & AIN & _ & AARR & _ & AC5 & _ & OA5 & _). clear OWN5.
      assert (CWA : client_wrange L (((An, 4 * (jn + 1)) :: lb_remove pXc LBc) ++ fdata LF) (arl_stklo R) (htop asegs R HIA h4) An (4 * (jn + 1)))
        by (eapply client_wrange_block; [left; reflexivity| clear; lia| clear; lia]).
      assert (NTH : nth_error (xs ++ [Z_to_bv 64 0]) (Z.to_nat jn) = Some (Z_to_bv 64 0)).
      { rewrite nth_error_app2 by (clear - LEN1 N1; lia). replace (Z.to_nat jn - length xs)%nat with 0%nat by (clear - LEN1 N1; lia). reflexivity. }
      clear MU WM. pose proof (munch_refl [(An + 4 * jn, An + 4 * jn + 4)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OA5 (An + 4 * jn) 4.
      (* [comment removed for export] *)
      zstep.
      pose proof (u32arr_read asegs m5 An (xs ++ [Z_to_bv 64 0]) jn (Z_to_bv 64 0) _ AARR NTH ltac:(clear - N1; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD.
      (* [comment removed for export] *)
      zstep. zstep.
      pose proof (u32arr_store_ok asegs m5 An (xs ++ [Z_to_bv 64 0]) jn _ AARR ltac:(rewrite length_app; cbn [length]; clear - LEN1 N1; lia) ltac:(f_equal; clear; lia)) as SOKw.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
        pose proof (u32arr_write asegs m5 An (xs ++ [Z_to_bv 64 0]) jn vv AARR ltac:(rewrite length_app; cbn [length]; clear - LEN1 N1; lia)) as AARR' end.
      store_done.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo _ |- _ => rename H into ST6 end.
      match goal with H : HM asegs R HIA h4 _ LF m6 |- _ => rename H into HH6 end.
      assert (HW6 : forall a, ~ outside [(An + 4 * jn, An + 4 * jn + 4)] a -> (LHeap = LHeap /\ An <= a < An + 4 * (jn + 1)) \/ lo <= a < bv_unsigned sp - 96).
      { intros a NO. left. split; [reflexivity|]. cbn [outside] in NO. clear - NO N1. lia. }
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J5 MU WM MI6 ST6 HH6 HW6
                    ltac:(cbn; split; [clear - Flo SLO2 NEEDR N1; lia| exact I]) ltac:(cbn; split; [clear - FXS N1; lia| exact I]) AARR'
                    ltac:(rewrite upd_length; reflexivity)) as J6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      eapply aa_ret; [exact J6| left; split; [reflexivity| split; [| reflexivity]]| |].
      * unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_upd by (rewrite length_app; cbn [length]; clear - LEN1 N1; lia).
        rewrite (limb32_w32_nth _ _ _ NTH).
        change (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 0)) + 1))) mod 2 ^ 32)
          with (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 0)) + 1)))).
        rewrite w32_incr. unfold w32. rewrite (unsigned_lit 0) by (clear; lia).
        change ((0 mod 2 ^ 32 + 1) mod 2 ^ 32) with 1. change (0 mod 2 ^ 32) with 0.
        rewrite limbs_val_app. cbn [limbs_val]. rewrite ?(unsigned_lit 0) by (clear; lia). change (0 mod 2 ^ 32) with 0.
        replace (Z.of_nat (Z.to_nat jn)) with jn by (clear - N1; lia). rewrite LEN1. clear - HVV. lia.
      * unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT JM NR1. lia.
      * unfold aaF1, add_abs_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    all: match goal with |- ?g => idtac "G2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01O0@C11264064775.181D33619324555.180D8561475640.180 K46334092739.181K65977458927.181K68539399608.181L11030354103.6  L12074844306.11 L12515801992.3  L13604857769.4  L14518907549.3  L14948330784.177L15198982830.3  L15663651505.3  L15840915687.5  L17848125779.1  L20859654516.1  L27742581695.6  L29526146055.2  L2970692150.2   L29763661393.2  L29765672528.165L29765672528.167L29765672786.163L29765672786.165L32076862224.4  L35663928186.7  L39188636933.0  L41074412576.165L41074420074.168L41416003690.6  L42470618843.182L42633816569.1  L43092657406.3  L44015168660.3  L45116040196.165L45116040196.167L45116040325.164L45116040325.166L46323497533.3  L51267807018.15 L5775036390.2   L57930138456.3  L5800431574.6   L58609956177.2  L58636003124.1  L59308628179.5  L59308628433.4  L59308975210.7  L59310648043.7  L60098763854.3  L61553859661.6  L61827434946.163L61827434946.165L65528204888.4  L65971322641.3  L67417882581.7  L68550025798.15 L7207588064.1   L8328083279.7   L9570690066.2   P46334092739.181Q11801279589.180Q20962640553.173Q20964724257.178Q24418818504.168Q24418818504.170Q24419214967.167Q24419214967.169Q26207754346.167Q26207754346.169Q26295627581.173Q29203131547.167Q29203131547.169Q31653749955.167Q31653749955.169Q32494403506.170Q33606497915.175Q33619063430.176Q33621337227.180Q36081244985.168Q36081244985.170Q42766971027.168Q42766971027.170Q50458135125.173Q56512145356.168Q56512145356.170Q60196163333.179Q61218916524.173Q8561220661.176 Q8563657272.180 Q8565397704.175 Q8565759041.173 Q8565809916.170 Q8943627034.170 00000100c01R01S02<03703=03d03m04804@04A04J04S04]04`04c04o05605=05D05c06D06c07D07O07d07e08Y09M09N09m0:20::0:;0:\0;?0;k0<Y0<Z0=00=70=?0=R0=Y0=\0=g0>20>A0>X0>b0?50?a0@O0@Z0@[0A00A10A40AH0AN0AO0Af0BD0Bb0C30CF0CW0Cj0D;0DN0D_0E00EC0ET0Eg0FE0Fc0GA0Ga0H20HE0HF0HG0H\0IK0J<0JX0K60KQ0Kn0LI0Ld0M?0MPFS2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR1w2P02JM2K0S2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR1w2P02JMFS1X3xs01k2xs3pXc1N1J2Hk2HJ1w2N13XPc2JM2K0S1R2sp3xs02lo4SLO21k2xs3pXc1N1J2Hk5NEEDR3LOS3ALO1w2N12PC2K0S1J2GTS1R2sp2lo4SLO23pXc1N1J2HJ5NEEDR4XLSc2K0S1w2WR2NZS1N1J2HJ2K0S1N1J2HJFS1R1X3XALS1w2WR2KBS1k1N1J2HkS1JS1JS2xs1J3HVV1wS3pXc1JS3pXc1NS1N3NR1S2ra2sp1X3xs02xs3pXc1N1J2Hk3NR1S2ra2sp1X3xs01k2xs3pXc1N1J2Hk3NR1S2ra2sp1X3xs02xs3pXc1N1J2Hk3NR1S2ra2sp1X3xs01k2xs3pXc1N1J2Hk3NR1S1N1J2HJ2K0S1R3HIA1h2sp2lo3TOP1HSS2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR2P03P472JM2K0S2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR2P03P472JM2K0SS2ra2sp1X3xs01k2xs3pXc1N1J2Hk1wS3pXcS1N1J2HJSS2ra2sp1X3xs02xs3pXc1N1J2Hk2HJ2K1S2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2K1S2ra2sp1X3xs02xs3pXc1N1J2Hk2HJ2X03SPR2P03P47S2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR2P03P47FS2dA2dB1v1N1J2HJ2BV2JMS3pXc1JS1N1J2HJS2xs1N1J2HJ4LEN12K0S1N3NR1S1JS1N1J2Hk2K0S1N1J2K02K2S2xs1J2VN2VM2PGS2xs1N1J2HJ4LEN12K03NTHS1R2lo3LOSS2xs1N1J2HJ4LEN12K0S2ra2sp1X3xs02xs3pXc1N1J2Hk2HJ2X03SPR2P03P47S2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03SPR2P03P47S1d2D01f2BFFS1X3pXc1N1J2HJ3XPc2K0FS1JS3pXc1N1J2HJ2K01a2NOS1N2K1FS3xs01k2xs3pXc1N1J2Hk1wS3xs01k2xs3pXc1N1J2Hk2HJ2P02JMS3xs01k2xs3pXc1N1J2Hk2HJ2P02JMS1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkS1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkS1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkS3xs01k2xs1N1J2HkS1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkS1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkS3xs01k2xs3pXc1N1J2Hk2HJ2JM2K0S3xs01k2xs3pXc1N1J2Hk2HJ2JM2K0S3xs01k2xs3pXc1N1J2Hk2HJ2JM2K0S3xs01k2xs3pXc1N1J2Hk2HJ1w2JM2K0S1X3xs02xs1N1J2HkS1X3xs01k2xs1N1J2HkFFS3xs01k2xs3pXc1N1J2HkS2ra2sp1X3xs02xs3pXc1N1J2Hk2HJ2X03XAL3SPR2P02JMS2ra2sp1X3xs01k2xs3pXc1N1J2Hk2HJ2X03XAL3SPR2P02JMS3xs01k2xs3pXc1N1J2Hk3P472K0S3xs01k2xs3pXc1N1J2Hk2HJ2JM2K0S3xs01k2xs3pXc1N1J2Hk2HJ2JMS3xs01k2xs3pXc1N1J2Hk2HJ1w2JMS3xs01k2xs3pXc1N1J2Hk2HJ2JMS3xs01k2xs3pXc1N1J2Hk2HJ2JMS3xs01k2xs3pXc1N1J2Hk2HJ2JMS3xs01k2xs1N1J2Hk". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_LOOP : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pk,$60.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pxs,(1.(3.&40.))PpXc,$8.PN,$8.PJ,$8.Pr2,(3.&40.)Pr10,(3.&40.)Pr24,(3.&40.)Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(22.(26.R17.R16.)(61.R1?.))P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R1?.R1>.R1=.R1<.R1;.(48.VX,+1.R18.R19.R1:.VpadX,$1:.))P,(32.(22.+1.R18.)(22.R18.R19.))P,(10.$8.(23.(54.R1<.)(5?.+2.(1<.+20.R19.)))$4=.)P,(22.R22.$56.)P,(22.R22.$57.)P,(10.(3.&40.)R1;.(29.&40.(23.R1<.+1.)))P,(10.(3.&40.)R1;.(29.&40.(26.(23.R1?.(1<.+4.R1=.))+4.)))P,(10.(3.&40.)R1;.(29.&40.(1<.+4.R1>.)))(50.$47.(51.$47.VR,VHIA,R25.Vmo,)$52.(43.(44.R1;.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R1:.R19.R18.(29.&40.VX,)(29.&40.(23.VX,+:.))R1=.R17.R16.R15.R14.R13.R12.R11.R1>.R10.R?.(29.&40.(58.(2=.VR,)))R1<.(29.&40.(23.(59.(23.VX,+:.)+3.)(58.(2=.VR,))))(29.&40.(23.(59.VX,+3.)(58.(2=.VR,))))(29.&40.+2710.)R>.Vs11,R=.R<.R;.R:.)VF,(29.&40.+9==64.)Vfc,(45.(3.&40.))R23.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hk J0 HJ HVV BV BF -> -> ->.
    all: jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
         cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    all: basic_factsA hc.
    all: pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    all: pose proof J0 as JX; xa_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    all: ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47); clear OWN0 OWN1.
    all: pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc; unfold mpi_cells in CX1.
    all: pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    all: assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    all: pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    all: pose proof (munch_refl [(pXc + 4 * J, pXc + 4 * J + 4)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    all: assert (E10 : Z.shiftr (X + 10) 3 + al_sb AL = Z.shiftr X 3 + al_sb AL + 1)
           by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - XAL; lia).
    (* [comment removed for export] *)
    all: assert (JM : J <= aaM) by
      (pose proof (limbs_val_nonneg xs) as VN; pose proof VALM as VM; rewrite <- HVV in VM;
       destruct (Z_le_gt_dec J aaM) as [|GT]; [assumption| exfalso];
       assert (PG : 2 ^ (32 * (aaM + 1)) <= 2 ^ (32 * J)) by (apply Z.pow_le_mono_r; clear - GT HJ; lia); clear - PG VN VM; lia).
    (* [comment removed for export] *)
    all: rewrite E10; zstep; zstep; zstep.
    all: replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    (* [comment removed for export] *)
    all: zstep; replace (Z_to_bv 64 (J + 1 + -1)) with (Z_to_bv 64 J) by (f_equal; clear; lia).
    all: zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - NR1 HJ; lia).
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *) eapply aa_retm16; [exact J0| clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia]. }
      zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 K0; lia|].
      assert (EJ : J = N) by (clear - K0 HJ; lia). subst J.
      rewrite <- E10. eapply aa_G2; [exact J0| clear - K1; lia| exact JM| exact HVV| exact BV| exact BF].
    - (* [comment removed for export] *) exfalso. clear - K0 Hk HJ. lia.
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *) eapply aa_retm16; [exact J0| clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia]. }
      zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 K0; lia|].
      assert (EJ : J = N) by (clear - K0 HJ; lia). subst J.
      rewrite <- E10. eapply aa_G2; [exact J0| clear - K1; lia| exact JM| exact HVV| exact BV| exact BF].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep.
      replace (Z_to_bv 64 (pXc + 4 * J - 4 + 4)) with (Z_to_bv 64 (pXc + 4 * J)) by (f_equal; clear; lia).
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OP (pXc + 4 * J) 4.
      (* [comment removed for export] *)
      zstep.
      destruct (nth_error xs (Z.to_nat J)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LEN1 K0 HJ; lia].
      pose proof (u32arr_read asegs mc pXc xs J w _ XARR NTH ltac:(clear - HJ; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD.
      (* [comment removed for export] *)
      zstep. zstep.
      assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
        by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
      pose proof (u32arr_store_ok asegs mc pXc xs J _ XARR ltac:(clear - HJ K0 LEN1; lia) ltac:(f_equal; clear; lia)) as SOKw.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
        pose proof (u32arr_write asegs mc pXc xs J vv XARR ltac:(clear - HJ K0 LEN1; lia)) as XARR' end.
      store_done.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo _ |- _ => rename H into ST6 end.
      match goal with H : HM asegs R HIA hc _ LF m6 |- _ => rename H into HH6 end.
      assert (HW6 : forall a, ~ outside [(pXc + 4 * J, pXc + 4 * J + 4)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 96).
      { intros a NO. left. split; [reflexivity|]. cbn [outside] in NO. clear - NO HJ K0. lia. }
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6 HH6 HW6
                    ltac:(cbn; split; [clear - XLSc SLO2 NEEDR HJ K0; lia| exact I]) ltac:(cbn; split; [clear - XPc HJ K0; lia| exact I]) XARR'
                    ltac:(rewrite upd_length; reflexivity)) as J6.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
      pose proof (limb32_w32_nth xs (Z.to_nat J) w NTH) as LW. pose proof (w32_range w) as WR.
      assert (LVU : limbs_val (upd xs (Z.to_nat J) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))))
                    = limbs_val xs + 2 ^ (32 * J) * ((w32 w + 1) mod 2 ^ 32 - w32 w)).
      { rewrite limbs_val_upd by (clear - HJ K0 LEN1; lia).
        change (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))) mod 2 ^ 32) with (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1)))).
        rewrite w32_incr, LW. replace (Z.of_nat (Z.to_nat J)) with J by (clear - HJ; lia). reflexivity. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases KB; zify_cond KB; rewrite incr_mod64 in KB.
      + (* [comment removed for export] *)
        apply (proj1 (sxz_zero_iff _ ltac:(clear; apply Z.mod_pos_bound; lia))) in KB.
        rewrite <- E10. eapply (IH _ _ _ _ _ _ _ N (J + 1)); [clear - Hk K0; lia| exact J6| clear - HJ K0; lia| | exact BV| exact BF| f_equal; clear; lia| f_equal; clear; lia| f_equal; clear; lia].
        rewrite LVU, KB. replace (32 * (J + 1)) with (32 * J + 32) by (clear; lia). rewrite Z.pow_add_r by (clear - HJ; lia).
        assert (w32 w = 2 ^ 32 - 1) by (clear - KB WR; lia). clear - HVV H. nia.
      + (* [comment removed for export] *)
        assert (NZ : (w32 w + 1) mod 2 ^ 32 <> 0) by (intros E; apply KB; rewrite E; reflexivity).
        zstep.
        eapply aa_ret; [exact J6| | clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia].
        left. split; [reflexivity|]. split; [| reflexivity].
        unfold mpd_val. cbn [md_sg md_limbs]. rewrite LVU. rewrite Z.mod_small by (clear - WR NZ; lia). clear - HVV. lia.
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00m0@C11264064775.176D16239083480.175D33619324555.175K46334092739.176K65977458927.176K68539399608.176L12070384199.10 L12515719056.3  L12616134508.2  L14948330784.172L15663651505.3  L16539540349.3  L17027684244.1  L24178789648.3  L27742581695.6  L2970692150.2   L35663928186.7  L39846883059.1  L41074406303.160L41074420074.163L41416003690.6  L41652918740.1  L42470618843.177L42633816569.1  L43021235637.5  L44015168660.3  L45272757598.3  L46160492556.172L46322969181.3  L46950334807.6  L51267807018.15 L59308975210.7  L59310648043.6  L60098763854.3  L6027026214.2   L62785188115.3  L65071520974.5  L65528204888.4  L65971842929.3  L67416084352.6  L67663008344.3  L68550554150.15 L8328083279.6   P46334092739.176Q11801279589.175Q16226248488.170Q16226608033.168Q16226640547.165Q16237098456.175Q16238814165.171Q26295627581.168Q32494403597.165Q33606497915.170Q33619063430.171Q33621337227.175Q50458135125.168Q60196163333.174Q61218916524.168Q7974808257.173 Q7981049417.168 Q8943604901.165 00000100[01E01F01g02]03A03J03Q03R03[03c03f03k04704>04S04V05B05n05o06206J06O06_06`06h07G07H07N07d08308G08Q08X08`09009;09<09N09V09W09h09i0:90:O0:e0;;0;S0;i0<30<I0<_0=50=M0=[0>20>H0>a0?:0?DFS2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR1w2P02JMS2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR1w2P02JMFS1X3xs02xs3pXc1N1j2HJ1w2N13XPc2JMS1R2sp3xs02lo4SLO22xs3pXc1N1j2HJ5NEEDR3LOS3ALO1w2N12PCS1R2sp2lo4SLO23pXc1N1j2HJ5NEEDR4XLScS1w2WR2KBS3pXc1jFS1w2WR2KBS1N1j2HJS1jS1N1jS2xs1j3HVV1wS3pXc1NS1R3HIA1h2sp2lo3TOP1HS1jS2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR2P03P472JMS2ra2sp1X3xs02xs3pXc1N1j2HJ2X03SPR2P03P472JMSS1jS2ra2sp1X3xs02xs3pXc1j1wS3pXcS2xs1N1j2HJ4LEN1SS1N1j2HJS2ra2sp1X3xs02xs3pXc1j2X03X161wFS1j2GTS2dA2dB1v1N1j2HJ2BV2JMS2xs1j2VN2VM2PGS2xs1N1j2HJ4LEN13NTHS1R2lo3LOSS3pXc1jS1N1j2HJS2xs1N1j2HJ4LEN1S1d2D01f2BFFS1X3pXc1N1j2HJ3XPcS1N1j2HJFS3pXc1N1j2HJ1a2NOFS3xs02xs3pXc1j1wS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ1w2JMS3xs02xs3pXc1N1j2HJ2JMS3xs02xs1jS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ1w2JMS3xs02xs3pXc1jS3xs02xs3pXc1N1j2HJ3P47S3xs02xs3pXc1N1j2HJ2JMS3xs02xs3pXc1N1j2HJ2P02JMS3xs02xs3pXc1N1j2HJ2P02JMS3xs02xs1j". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_ITER1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pxs,(1.(3.&40.))PpXc,$8.PN,$8.Pj,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R1;.R1:.R19.R18.R17.(48.VX,+1.R14.R15.R16.VpadX,$1:.))P,(32.(22.+1.R14.)(33.R14.R15.))P,(10.$8.(23.(54.R18.)(5?.+2.(1<.+20.R15.)))$4=.)P,(22.R1>.$56.)P,(22.R1>.$57.)(50.$47.(51.$47.VR,VHIA,R1>.Vmo,)$52.(43.(44.R17.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R16.R15.R14.(29.&40.VX,)(29.&40.(23.VX,+:.))R13.R12.(29.&40.+1.)R11.R10.R?.R>.R=.(29.&40.R18.)R<.(29.&40.R1:.)(29.&40.(58.(2=.VR,)))(29.&40.(23.(1<.+4.R18.)+4.))(29.&40.(23.(59.(23.VX,+:.)+3.)(58.(2=.VR,))))(29.&40.(23.(59.VX,+3.)(58.(2=.VR,))))R;.R:.Vs11,R9.R8.R7.R6.)VF,(29.&40.+9==28.)Vfc,(45.(3.&40.))R1<.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 HJ HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J0 as JX; xa_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47); clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc; unfold mpi_cells in CX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl [(pXc + 4 * j, pXc + 4 * j + 4)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    assert (JM : j <= aaM).
    { pose proof (limbs_val_nonneg xs) as VN; pose proof VALM as VM; rewrite <- HVV in VM.
      destruct (Z_le_gt_dec j aaM) as [|GT]; [assumption| exfalso].
      assert (PG : 2 ^ (32 * (aaM + 1)) <= 2 ^ (32 * j)) by (apply Z.pow_le_mono_r; clear - GT HJ; lia). clear - PG VN VM; lia. }
    (* [comment removed for export] *)
    zstep. zstep.
    replace (Z_to_bv 64 (pXc + (4 * j + 4) + -4)) with (Z_to_bv 64 (pXc + 4 * j)) by (f_equal; clear; lia).
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OP (pXc + 4 * j) 4.
    (* [comment removed for export] *)
    destruct (nth_error xs (Z.to_nat j)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LEN1 HJ; lia].
    pose proof (u32arr_read asegs mc pXc xs j w _ XARR NTH ltac:(clear - HJ; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    zstep.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    pose proof (u32arr_store_ok asegs mc pXc xs j _ XARR ltac:(clear - HJ LEN1; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs mc pXc xs j vv XARR ltac:(clear - HJ LEN1; lia)) as XARR' end.
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo _ |- _ => rename H into ST6 end.
    match goal with H : HM asegs R HIA hc _ LF m6 |- _ => rename H into HH6 end.
    assert (HW6 : forall a, ~ outside [(pXc + 4 * j, pXc + 4 * j + 4)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 96).
    { intros a NO. left. split; [reflexivity|]. cbn [outside] in NO. clear - NO HJ. lia. }
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6 HH6 HW6
                  ltac:(cbn; split; [clear - XLSc SLO2 NEEDR HJ; lia| exact I]) ltac:(cbn; split; [clear - XPc HJ; lia| exact I]) XARR'
                  ltac:(rewrite upd_length; reflexivity)) as J6.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
    pose proof (limb32_w32_nth xs (Z.to_nat j) w NTH) as LW. pose proof (w32_range w) as WR.
    assert (LVU : limbs_val (upd xs (Z.to_nat j) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))))
                  = limbs_val xs + 2 ^ (32 * j) * ((w32 w + 1) mod 2 ^ 32 - w32 w)).
    { rewrite limbs_val_upd by (clear - HJ LEN1; lia).
      change (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))) mod 2 ^ 32) with (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1)))).
      rewrite w32_incr, LW. replace (Z.of_nat (Z.to_nat j)) with j by (clear - HJ; lia). reflexivity. }
    (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB; rewrite incr_mod64, bv_unsigned_sx32 in KB; fold (w32 w) in KB.
    - (* [comment removed for export] *)
      apply (proj1 (sxz_le_iff _ _ (w32_range w) ltac:(clear; apply Z.mod_pos_bound; lia))) in KB.
      eapply aa_ret0; [exact J6| | reflexivity| clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia].
      unfold mpd_val. cbn [md_sg md_limbs]. rewrite LVU. rewrite Z.mod_small by (clear - WR KB; lia). clear - HVV. lia.
    - (* [comment removed for export] *)
      apply (proj1 (sxz_lt_iff _ _ ltac:(clear; apply Z.mod_pos_bound; lia) (w32_range w))) in KB.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      eapply (aa_LOOP (Z.to_nat (N - (j + 1))) _ _ _ _ _ _ _ N (j + 1));
        [clear - HJ; lia| exact J6| clear - HJ; lia| | exact BV| exact BF| f_equal; clear; lia| f_equal; clear; lia| f_equal; clear; lia].
      rewrite LVU. replace (32 * (j + 1)) with (32 * j + 32) by (clear; lia). rewrite Z.pow_add_r by (clear - HJ; lia).
      assert (w32 w = 2 ^ 32 - 1) by (clear - KB WR; lia). assert ((w32 w + 1) mod 2 ^ 32 = 0) by (rewrite H; reflexivity). clear - HVV H H0. nia.
    all: match goal with |- ?g => idtac "ITER1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0@L20955340085.162L22550422114.3  L22704838960.4  L29763661393.2  L29765672528.163L29765672786.162L32954672962.162L35963164448.5  L46160487540.162L51267939251.14 L51267939251.15 L55345850227.162L55784711535.5  L58609956177.2  L59308628433.2  L60208222901.4  L65528204888.4  L9570690066.3   Q26207421841.164Q26207721832.165Q26207967338.162Q31654082872.164Q39212284437.165Q43925228937.165Q60511567613.165Q60697995187.165Q8880503606.162 Q9538787269.162 00000100:00E00L00l01H02402>02[02o03E03`03l04304904D04O04Y04e05105=05I05U05a05k06:06F06PFS1c2HC2KCS1N1j2HJ2K0S1N3NR1S2ra2sp1X3xs02xs3pXc1N2K22HJ3NR1S2ra2sp1X3xs02xs3pXc1N1j3NR1S2ra2sp1X3xs02xs3pXc1N1j2HJ2JM2X03SPR2P03P47S2xs1j3HVVS2ra2sp1X3xs02xs3pXc1j2X03X16S2dA2dB1v1N2JM2HJ2BVS2dA2dB1v1N1j2HJ2JM2BVS2ra2sp1X3xs02xs3pXc1j1c2HCS2xs1j3HVV1NS1N3NR1S1N2K2S1N1j2HJ2K0S1d2D01f2BFS1N3NR12K1S1X3xs02xs1jS1X3xs02xs1jS1X3xs02xs1jS1X3xs02xs1jS1X3xs02xs1jS1X3xs02xs1jS3xs02xs1jS1X3xs02xs1j2X0S1X3xs02xs1jS3xs02xs1j". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_FIRST : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pxs,(1.(3.&40.))PpXc,$8.PN,$8.Pj,$8.Pc,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R1<.R1;.R1:.R19.R18.(48.VX,+1.R15.R16.R17.VpadX,$1:.))P,(32.(22.+1.R15.)(22.R15.R16.))P,(32.(22.=R15.)(22.R15.+1.))P,(22.R17.$5<.)P,(10.$8.(23.(54.R1;.)(1<.R17.(5?.+2.(1<.+20.R18.))))$4=.)P,(22.R21.$56.)P,(22.R21.$57.)(50.$47.(51.$47.VR,VHIA,R21.Vmo,)$52.(43.(44.R19.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R18.R17.R16.(29.&40.VX,)(29.&40.(23.VX,+:.))(29.&40.R1:.)R15.R14.R13.R12.R11.R10.R?.(29.&40.R1;.)R>.(29.&40.R1=.)(29.&40.(58.(2=.VR,)))(29.&40.(23.(1<.+4.R1;.)+4.))(29.&40.(23.(59.(23.VX,+:.)+3.)(58.(2=.VR,))))(29.&40.(23.(59.VX,+3.)(58.(2=.VR,))))R=.R<.Vs11,R;.R:.R9.R8.)VF,(29.&40.+9=<70.)Vfc,(45.(3.&40.))R1?.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 HJ HC JM HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J0 as JX; xa_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47); clear OWN0 OWN1.
    unfold mpi_cells in CX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by (clear - HC; lia).
    { eapply aa_ret0; [exact J0| | reflexivity| clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia].
      unfold mpd_val. cbn [md_sg md_limbs]. rewrite KC in HVV. clear - HVV. lia. }
    assert (EC : c = 1) by (clear - KC HC; lia). subst c. clear KC HC.
    (* [comment removed for export] *)
    zstep. shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - NR1 HJ; lia).
    { (* [comment removed for export] *)
      eapply aa_ITER1; [exact J0| clear - K0 HJ; lia| clear - HVV; lia| exact BV| exact BF]. }
    assert (EJ : j = N) by (clear - K0 HJ; lia). subst j.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      eapply aa_retm16; [exact J0| clear - BV JM HJ; unfold aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia]. }
    (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by (clear - NR1; lia); clear - K2; lia|].
    eapply aa_G3; [exact J0| clear - K1 NR1; lia| exact JM| clear - HVV; lia| exact BV| exact BF].
    all: match goal with |- ?g => idtac "FIRST-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L15528730518.60L45272754978.60L59549403627.60L9132507695.60 00000J00_01401IS2ra2xs3xs'2zs1j1c4Hlen2HvS2ra2xs3xs'1j2Hj4HlenS2ra2xs3xs'1j2Hl4HlenS2ra2xs3xs'1j2Hl4Hlen". (* [comment removed for export] *)
  #[using="ra dA dB"] Lemma limbs_val_core_addA : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pxs,(1.(3.&40.))Pxs',(1.(3.&40.))Pzs,(1.(3.&40.))Pj,$8.Pc,$8.P,(22.=R2.)P,(22.R3.(61.(62.(3.&40.)R6.)))P,(10.$60.(62.(3.&40.)R6.)(62.(3.&40.)R7.))P,(10.(1.(3.&40.))(63.(3.&40.)(64.R5.)R7.)(63.(3.&40.)(64.R5.)R8.))P,(10.$8.(23.(65.R8.R6.)(1<.R5.(5?.+2.(1<.+20.R6.))))(23.(65.R9.R6.)(65.R7.R6.)))(10.$8.(23.(54.R9.)(1<.R6.(5?.+2.(1<.+20.R7.))))(23.(54.R:.)(65.R8.R7.)))")
(* [comment removed for export] *).
  Proof.
    intros xs xs' zs j c Hj Hl Hlen Hs Hv.
    rewrite (limbs_val_split xs j), (limbs_val_split xs' j) by lia. rewrite Hs. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition opnd2A (dE : mpd) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) : Prop :=
    (JBE dE /\ BJE dE hc LBc mc dXc) \/ dE = dXc.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02<0@C24112444547.200D10576698754.201D17444351834.201D22752211978.204D30202740417.201D30213615715.204D38874475859.204D42633159082.201D42643779336.204D62012212072.204K11420089551.200K25384422162.202K28284592895.199K41585169438.199K45908760803.203K45908760803.205K52581815936.201K61717199003.201L11379748202.3  L11416546478.3  L14183750181.16 L14183782691.14 L16399517397.15 L16399549907.16 L17813258712.7  L17815712639.11 L17815810169.13 L17898023708.8  L23100341967.179L23643762344.6  L23853643285.1  L25399627235.15 L2617640871.5   L2695949673.2   L28029610798.11 L28270437390.4  L2975768925.2   L35663928186.7  L36147132693.8  L36147476882.8  L36149152565.14 L36149250099.16 L36180290948.1  L38235734261.1  L38291463909.8  L38297951381.10 L41114152401.6  L41114660182.5  L41116278007.12 L41117966897.179L41128898453.2  L41580512891.2  L42633816569.1  L43878034250.5  L45272757598.3  L45558987916.9  L45913639042.4  L45916029979.4  L47797436189.12 L49206922459.2  L4952274081.0   L52182933129.12 L52189551865.8  L52189667041.8  L52592168972.2  L53709971128.6  L54434634207.10 L54473544495.13 L5865530840.11  L59310763475.6  L59378981895.1  L59549313838.11 L59553535406.5  L60098763854.3  L60283674290.11 L60451539393.3  L61576705368.7  L61711433322.3  L64201493914.6  L66151427842.16 L66151427842.17 L68455774684.7  L68458302331.12 L68458334333.13 L9289747104.13  L9289845158.11  O14737164687.202O24112444547.200O27573497883.199O31435371494.202O35105909750.201O43419437345.201O43841349487.203O43841349487.205O54539614568.199P11385514907.202P11420089551.200P41585169438.199P45908760803.203P45908760803.205P52581815936.201Q12370813529.187Q14460600349.209Q15148415212.187Q17207432298.186Q18347242623.208Q22752211978.209Q23773721554.206Q23773721554.207Q23773721554.208Q30213615715.209Q3477013320.186 Q37625261960.186Q38874475859.209Q39314530340.187Q42252534531.187Q42630719017.209Q42643779336.209Q4511369453.187 Q45875552310.209Q46978751216.187Q46978803023.186Q47588311916.205Q47588311916.206Q47588311916.207Q47588311916.208Q5485126037.186 Q5485174314.187 Q59703481013.187Q6143569392.187 Q61889752670.207Q61889752670.208Q62701122256.186Q64443693026.187Q64835987202.187Q9285269895.209 Q9827600259.205 Q9827600259.206 Q9827600259.207 Q9827600259.208 00000101@02N02O03U04Q04R05;05X06706807207a07b07c07d07e08a08b08c08d08e08f08g08h08i08j08k09H09Z09^09_09k09l0:A0:B0:I0:^0:_0:`0:a0:b0:f0:j0:k0;R0;S0;_0;`0<=0<>0<?0<D0<K0<S0<k0<l0<m0<n0<o0=00=10=20=P0=Q0=e0>I0>M0>_0?40?80?K0?[0?e0@I0@S0@m0@n0A;0A[0A\0A]0A^0A_0A`0Aa0Ab0Ac0Ad0Ae0Af0Ag0Ah0Ai0Aj0Ak0Al0Am0An0Ao0B00BT0BU0CI0CV0CW0CX0CY0CZ0C[0D70DE0DR0DS0DT0EC0ED0ES0ET0EU0Ec0F10F20F30F40F50FB0FO0FP0F]0F^0F_0Fm0G;0G<0G=0G>0G?0G@0GAFS1R2ra2sp1X3xs02lo4SLO22Ea2pE1j3pXc2xs2zs5NEEDR3LOS2X03SPR3EP03E0'2P04xs6l4LEN6S1R3HIA1h2ra2sp1X3xs02Ea2pE1j2hc3pXc2xs2zs3TOP2X03SPR3EP03E0'3HT12P04xs6l4LEN6FS2ra2sp1X3xs02Ea2pE1j1N3pXc2xs2zs2HJ2JM2X03SPR3EP03E0'2N12P04xs6l4LEN6S2ra2sp1X3xs02Ea2pE1j1N3pXc2xs2zs2HJ2JM2X03SPR3EP03E0'2N12P0FS2ra2sp1X3xs02Ea2pE1j3pXc2xs2zs4xs6l4LEN6S2ra2sp1X3xs02Ea2pE3pXc2xs2zsS1R2ra2sp1X3xs02Ea2pE3pXc2xs2zsFS1R2sp3xs02lo4SLO21j1N3pXc2xs2zs2HJ2JM5NEEDR3LOS3ALO2N12PCS1R2sp3xs02lo1j1N3pXc2xs2zs2HJ2JM3LOS3ALO2N12PCFFFFS2sp1X3xs02lo1j1N3pXc2xs2zs2HJ2JM3x142N13XPc2x23x153x164POSTFFFFFFFFFFS2ra2sp1X3xs02Ea2pE3pXc2xs2zsS1X1j1N3pXc2HJ3XPcS2spFS1j1N3pXc2HJFS2nE1j2xs2zs3HJE4LENZFS1N3pXcS1R3HIA1h2sp2lo3TOP1HFFFFS2spS2loFS1R2sp2lo4SLO21N3pXc2xs5NEEDR4LEN14XLScFS2sp3SPA3SPRFS2ra2sp1X3xs02Ea2pE3pXc2xs2zsFFS3pXcS2sp2loS1j1N2HJS1j2xs2zs3HVV1c4xs6l3LVCFFFFSFFS1R2sp2lo4SLO22pE2zs5NEEDR3ESKFS1R2sp2lo4SLO25NEEDRS1R2sp2lo4SLO21j1N3pXc2HJ5NEEDR4XLScS2spS1j1N2xs2zs2HJ3NR1S2dE1j3dXc2HJ3HJE3EZ0S2pES1j1N2xs2zs2HJ4LEN1S1j1N2xs2HJ4LEN1S1R2lo3LOSS1R2sp2lo4SLO21j1N3pXc2HJ5NEEDR1a2NOS2dE3dXc1HS1R2sp1X2lo4SLO25NEEDR3DSXFS2nE2pE1j3HJES3dXc2r04XPAL1q1r1H2H02q02H43pXcFFFFFFFFFFFFFFFFFFFFFS2ra2sp1X3xs02Ea2pE3pXc2xs2zs2X03XALFS2ra2sp1X3xs02Ea2pE3pXc2xs2zs2X03SPR3EP03E0'4EAL'2P0S1X3xs02xs2zsFFFFFS3xs01j1N3pXc2xs2zs2HJ2JM2N1S3xs02Ea2xs2zsS1X3xs02xs2zsFFS1R2sp3xs02lo4SLO22xs2zs5NEEDR3LOS4SP643ALO3ACPFS3xs03pXc2xs2zsFFS3xs02Ea2xs2zsS3xs02Ea2xs2zsFFFFS1X3xs02xs2zsS1X3xs02xs2zsFS1X3xs02xs2zsFFS3xs02Ea2xs2zsS3xs02Ea2xs2zsFFFFFF". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_CALL : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "PdE,$7.Pj,$8.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R18.R17.R16.R15.R14.R13.)P,(66.R1;.R17.R16.R15.R14.)P,(10.$11.(12.R15.)$1:.)P,(32.(22.+1.R1<.)(22.R1<.(1=.R16.)))P,(22.R1=.(1=.R1>.))P,(22.R1>.$5<.)P,(10.$8.(4>.R19.)+1.)P,(10.$8.(23.(54.(55.R1:.))(65.(55.R21.)R20.))$4=.)P,(22.R20.$56.)P,(22.R20.$57.)(50.$47.(51.$47.VR,VHIA,R20.Vmo,)$52.(43.(44.R1<.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R1;.R1:.R19.(29.&40.VX,)(29.&40.(23.VX,+:.))R18.R17.R16.R15.R14.R13.R12.R11.(29.&40.R23.)(29.&40.(19.R24.))R10.(29.&40.(58.(2=.VR,)))(29.&40.(23.(1<.+4.R23.)+4.))(29.&40.(23.(59.(23.VX,+:.)+3.)(58.(2=.VR,))))(29.&40.(59.VX,+3.))(29.&40.(23.(59.(19.R24.)+3.)(58.(2=.VR,))))R?.Vs11,R>.R=.R<.R;.)VF,(29.&40.+9=<44.)Vfc,(45.(3.&40.))R1>.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 OPD EO HJ HJE JM SG1 HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    (* [comment removed for export] *)
    assert (EF : exists zs, md_limbs dE = zs /\ bytes_at asegs mc (md_p dE) (u32s zs) /\ Z.of_nat (length zs) = md_n dE
                 /\ ((md_p dE = md_p dXc /\ zs = md_limbs dXc) \/ md_p dE + 4 * Z.of_nat (length zs) <= md_p dXc \/ md_p dXc + 4 * Z.of_nat (length (md_limbs dXc)) <= md_p dE)
                 /\ md_p dE mod 4 = 0 /\ 0 < md_p dE /\ (md_p dE + 4 * Z.of_nat (length zs) <= lo \/ bv_unsigned sp <= md_p dE)
                 /\ rw_cells asegs mc (md_addr dE) (mpi_cells (md_p dE) (Z_to_bv 64 (md_sg dE)) (md_n dE) (md_pad dE))
                 /\ aobj asegs AL (hcs asegs R HIA hc) mc (md_addr dE) 16
                 /\ aobj asegs AL (hcs asegs R HIA hc) mc (md_p dE) (4 * md_n dE)
                 /\ 0 < md_addr dE /\ md_addr dE + 16 <= 2 ^ 64 /\ md_addr dE mod 8 = 0 /\ (md_addr dE + 16 <= lo \/ bv_unsigned sp <= md_addr dE)).
    { ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
      destruct OPD as [[DBJ B]| ->].
      - pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
        assert (EN : md_own dE <> LNull) by (intros C; destruct (OWNE0 C) as [_ EZ0]; clear - HJ HJE EZ0; lia).
        ddestruct (OWNE1 EN) as (_ & EP0 & EPAL & EBY & ESK & _).
        pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B)) as [(CE & _) _].
        exists (md_limbs dE). split; [reflexivity|]. split; [exact EBY|]. split; [exact LENE|].
        split; [right; rewrite LENE, LEN1; pose proof (bj_sepL _ _ _ _ _ _ _ _ _ _ B EO EN); clear - H; lia|].
        split; [exact EPAL|]. split; [exact EP0|]. split; [rewrite LENE; exact ESK|]. split; [exact CE|].
        split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)|]. split; [exact (bj_aobjL _ _ _ _ _ _ _ _ _ _ B EN)|].
        split; [exact E0|]. split; [exact E16|]. split; [exact EAL| exact ES].
      - pose proof (xa_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as ADc. pose proof (xa_pad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as PDc. rewrite ADc, PDc.
        exists (md_limbs dXc). split; [reflexivity|]. split; [apply u32arr_ro; exact XARR|]. split; [exact LEN1|].
        split; [left; split; reflexivity|]. split; [clear - XPAL; Z.div_mod_to_equations; lia|]. split; [exact P0|].
        split; [rewrite LEN1; exact (xa_XLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0 ltac:(rewrite EO; discriminate))|].
        split; [exact CX1|]. split; [exact (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0)|]. split; [exact OP|].
        split; [exact X0|]. split; [exact X16|]. split; [exact XAL| exact DSX]. }
    ddestruct EF as (zs & EZ & EBY & LENZ & SEPZ & EPAL & EP0 & ESK & CE & OE & OEL & E0' & E16' & EAL' & ES'). rewrite EZ in HVV.
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' sg own.
    destruct dE as [Ea sE nE pE zs0 padE ownE]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst zs0.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1 OPD.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc. unfold mpi_cells in CX1, CE.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * j); (bv_unsigned sp + -96 - MPI_CORE_ADD_STACK_A, bv_unsigned sp + -96)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (A_mpi_core_add_spec AL IMG) as SPC. unfold mpi_core_add_stmtA, A_MPI_CORE_ADD in SPC.
    acallxA_sp (bv_unsigned sp + -96)
      (eapply SPC with (X := pXc) (A := pXc) (B := pE) (n := j) (lo := lo) (xs := xs) (ys := xs) (zs := zs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia;
       try eassumption; try reflexivity;
       first [ apply u32arr_ro; exact XARR
             | left; split; reflexivity
             | clear - HJ HJE LEN1 LENZ N1 NR1; lia
             | clear - XPAL; Z.div_mod_to_equations; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear - HJ N1; lia]
             | eapply aobj_sub; [exact OEL| clear; lia| clear - HJ HJE; lia]
             | unfold MPI_CORE_ADD_STACK_A; clear - SLO2 NEEDR LOS; lia
             | clear - SPA SPR LOSP; lia
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
             | unfold MPI_CORE_ADD_STACK_A; left; rewrite LEN1; clear - XLSc SLO2 NEEDR; lia
             | unfold MPI_CORE_ADD_STACK_A; clear - XLSc LEN1 SLO2 NEEDR; lia
             | unfold MPI_CORE_ADD_STACK_A; clear - ESK SLO2 NEEDR; lia
             | match goal with |- ?g => idtac "CADD-PRE-LEFT:" g end ]).
    clear SPC.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-CADD-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo (bv_unsigned sp + -96) |- _ => rename H into ST6 end.
    match goal with H : u32arr asegs m6 pXc ?l, H2 : length ?l = length xs |- _ => rename H into XARR6; rename H2 into LEN6; rename l into xs6l end.
    match goal with H : lval xs6l j + ?cc * 2 ^ (32 * j) = _, H2 : 0 <= ?cc <= 1, H3 : skipn _ xs6l = _ |- _ => rename H into LV6; rename H2 into HC6; rename H3 into SK6; rename cc into c end.
    (* [comment removed for export] *)
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HH6. cbn [app] in HH6.
    apply (hm_munch asegs R HIA hc LBc LF [(pXc, pXc + 4 * j); (bv_unsigned sp + -96 - MPI_CORE_ADD_STACK_A, bv_unsigned sp + -96)] mc m6) in HH6;
      [| exact MU| exact WM| unfold MPI_CORE_ADD_STACK_A; solve_w_writable].
    pose proof ST6 as ST6'.
    assert (HW6 : forall a, ~ outside [(pXc, pXc + 4 * j); (bv_unsigned sp + -96 - MPI_CORE_ADD_STACK_A, bv_unsigned sp + -96)] a ->
                  (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 96).
    { intros a NO. cbn [outside] in NO. unfold MPI_CORE_ADD_STACK_A in NO.
      assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 96) by (clear - NO HJ SLO2 NEEDR; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6
                  ltac:(cbn; unfold MPI_CORE_ADD_STACK_A; split; [clear - XLSc SLO2 NEEDR HJ; lia| split; [clear; lia| exact I]])
                  ltac:(cbn; unfold MPI_CORE_ADD_STACK_A; split; [clear - XPc HJ; lia| split; [clear - DSX SLO2 NEEDR; lia| exact I]]) XARR6
                  ltac:(exact LEN6)) as J6.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
    subst x2.
    eapply aa_FIRST; [exact J6| exact HJ| exact HC6| exact JM| | exact BV| exact BF].
    pose proof (limbs_val_core_addA xs xs6l zs j c ltac:(clear - HJ; lia) ltac:(clear - HJ LEN1; lia) LEN6 SK6 LV6) as LVC. clear - LVC HVV. lia.
    all: match goal with |- ?g => idtac "CALL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00O0@L13642871129.5  L14679198811.6  L20447459013.4  L20851361989.6  L27038138034.3  L27243017426.5  L32954672833.162L32954672962.165L36618624197.2  L46160478397.162L46160487540.165L48662239157.5  L51269834902.12 L5260339702.164 L55408706463.3  L58293195749.2  L59308546259.6  L59308628179.4  L65448092613.2  L65450267334.165L65530246509.5  Q26207421841.166Q26207721832.167Q26207774294.164Q31654082872.166Q39212284437.167Q43925228937.167Q60511567613.167Q60697995187.167Q8880817418.164 Q9538464249.164 00000@00R00\00h01101A01i02E02N02f03>03H03X04004904?04R04_04h05=05L05W05b05m06806C06N06W06e070079S2dE1j3dXc2HJ2K0S2dA2dB2dE1j2HJ2EMS1f2BF3F01S2dE1j2HJ2EMS2dE1j2HJS2dE1j3dXc2HJ2K0S2ra2sp1X3xs02dE1j3dXc2HJ2EM2X03SPR4NE10S2ra2sp1X3xs02dE1j3dXc2HJ2K1S3dXc3NR1S2ra2sp1X3xs03dXc2X03X16S2ra2sp1X3xs03dXc2X03X16S1v2BV3V01S2dA2dB1v2BV3V01S2ra2sp1X3xs03dXc2X03X16S2dE1j2HJS1d2D0S2dE1j3dXc2HJ2K02N0S1j3dXc2HJ2K0S3dXc3NR1S2ra2sp1X3xs03dXc3NR1S1d2D01f2BF3F01S1X3xs03dXcS1X3xs03dXcS1X3xs03dXcS1X3xs03dXcS1X3xs03dXcS1X3xs03dXcS3xs03dXcS1X3xs03dXc2X0S1X3xs03dXcS3xs03dXc". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_J1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "PdE,$7.Pj,$8.Pvv,$8.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R1;.R1:.R19.R18.R17.R16.)P,(66.R1?.R1:.R19.R18.R17.)P,(32.(22.+1.R1?.)(22.R1?.(1=.R20.)))P,(22.(1=.R21.)$5<.)P,(10.$8.(4>.R1:.)+1.)P,(10.$8.(54.(55.R1;.))R21.)P,(10.$8.(23.R22.(65.(55.R24.)R23.))$4=.)P,(22.R22.$5=.)P,(22.R22.$5>.)(50.$47.(51.$47.VR,VHIA,R22.Vmo,)$52.(43.(44.R1>.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R1=.R1<.R1;.(29.&40.VX,)R1:.R19.R18.R17.R16.R15.R14.R13.R12.(29.&40.R26.)(29.&40.(19.R27.))R11.(29.&40.(58.(2=.VR,)))(29.&40.(23.(1<.+4.R26.)+4.))R10.R?.(29.&40.(23.(59.(19.R27.)+3.)(58.(2=.VR,))))R>.Vs11,R=.R<.R;.R:.)VF,(29.&40.+9=;:0.)Vfc,(45.(3.&40.))R20.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 OPD HJ EM SG1 HVv HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold mpi_cells in CX1.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    assert (NE10 : 0 <= md_n dE <= 10000).
    { destruct OPD as [[DBJ B]| EQ]; [pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & _ & NRE & _); exact NRE| rewrite EQ; exact NR1]. }
    assert (V01 : aaV0 <= aaV1) by (clear - EM HJ; unfold aaV0, aaV1, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia).
    assert (F01 : aaF0 <= aaF1) by (clear - D0; unfold aaF0, aaF1, calls_FR, fr_charge in *; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K1; zify_cond K1; rewrite ?Z.mod_small in K1 by (clear - HJ NE10; lia).
    2: { (* [comment removed for export] *) eapply aa_retm16; [exact J0| clear - BV V01; unfold aaV0, aaV1, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF F01 D0; unfold aaF1, add_abs_FR, calls_FR, fr_charge in *; lia]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep. replace (zx16 (Z_to_bv 64 (md_n dXc))) with (Z_to_bv 64 (md_n dXc)) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?Z.mod_small in K0 by (clear - HJ NE10 NR1; lia).
    - (* [comment removed for export] *)
      assert (EO : md_own dXc = LHeap).
      { destruct (md_own dXc) eqn:E; [| reflexivity| exfalso; exact (NS1 eq_refl)]. exfalso. destruct (OWN0 eq_refl) as [_ [N0 _]]. clear - N0 K0 HJ. lia. }
      replace (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)) with SH10 by reflexivity.
      eapply aa_CALL; [exact J0| exact OPD| exact EO| clear - HJ K0; lia| clear - HJ; lia| clear - HJ EM; lia| exact SG1| rewrite HVv; exact HVV| clear - BV V01; lia| clear - BF F01; lia].
    - (* [comment removed for export] *)
      destruct OPD as [[DBJ B]| EQ]; [| exfalso; subst dE; clear - K0 HJ; lia].
      eapply aa_G1; [exact DBJ| | exact J0| exact B| clear - K0 HJ; lia| exact EM| exact SG1| exact HVv| exact BV| exact BF].
      unfold K1A_stmt. intros. eapply aa_CALL; try eassumption; [left; split; assumption| | clear - HJ; lia| clear - HJ EM; lia|].
      + split; [clear - HJ; lia| assumption].
      + match goal with H : limbs_val _ = vv |- _ => rewrite H; exact HVV end.
    all: match goal with |- ?g => idtac "J1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L5386298158.5300000;S2ra2zs1n1H". (* [comment removed for export] *)
  #[using="ra dA dB"] Lemma lval_fullA : forall zs n, Z.of_nat (length zs) = n -> lval zs n = limbs_val zs.
  Proof. intros zs n H. unfold lval. replace (Z.to_nat n) with (length zs) by lia. rewrite firstn_all. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0@L15428237971.2  L21041645149.3  L21631969095.2  L31009716740.6  L32761824045.1  L42608597650.1  L51267939251.14 L52803347089.146L54425651213.3  L55661584084.148L59308583409.4  L59310648043.6  L60008970178.5  L65528204888.4  L780814420.5    L8929159528.142 L8941817250.139 Q17047075571.145Q2183115807.143 Q22043167663.143Q22743580764.145Q26295627581.143Q27197462532.140Q27210147641.143Q35463703583.140Q50458135125.143Q8956258970.140 00000600>00D00S00V00Y00n01H01Q02B02N02c02o03:03F04904l05I05a06B06_06n07K07h08E08W08fS2dE1rS1k1r2HkS2zs1rS2zs2vv3HVV3ZA'S1rS1rS2dA2dB2dE1v2EM2HR2BVS2ra2sp1X3xs01k2dE2zs1r2HkS2dE1r2HRS2ra2sp1X3xs01k2dE2zs1r2Hk4LENZ2EM2HR2X03SPR4NE10S2dE1r2Hk2HRS2dE2zs1r4LENZ2HR3NTHS2dE1r2HR2K2S1d2D01f2BFS2dE1r2HR2K2S2ra2sp1X3xs01k2dE2zs1r2Hk4LENZ2EM3EP02HR2X03SPR2EBS2ra2sp1X3xs01k2dE2zs1r2Hk4LENZ2EM3EP02HR2X03SPR2EBS3xs01k2dE2zs1r2Hk4LENZ2EM2HRS3xs01k2dE2zs1r2Hk2EM2HRS3xs01k2dE2zs1r2Hk4LENZ2EM3EP02HRS3xs01k2dE2zs1r2Hk4LENZ2EM2HRS3xs01k2zs1r2HkS3xs01k2dE2zs1r2Hk4LENZ2EM2HRS3xs01k2dE2zs1r2Hk4LENZ2EM2HRS3xs01k2dE2zs1r2Hk4LENZ2EM2HRS3xs01k2dE2zs1r2HkS3xs01k2zs1r2Hk". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_SCANLOOP : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pk,$60.PdE,$7.Pzs,(1.(3.&40.))Pvv,$8.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pr,$8.Pr2,(3.&40.)Pr24,(3.&40.)Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(22.R15.(61.R1?.))P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R1<.R1;.R1:.R19.R18.R17.)P,(66.R20.R1;.R1:.R19.R18.)P,(10.$8.(4>.R19.)+1.)P,(10.(1.(3.&40.))(55.R22.)R21.)P,(67.$47.R1<.(1;.R23.)(68.R22.))P,(10.$8.(61.(62.(3.&40.)R23.))(1=.R24.))P,(22.(1=.R25.)$5<.)P,(33.=(1;.R26.))P,(69.$47.(2=.VR,)(2>.$47.VR,VHIA,R22.)R20.(1;.R27.)(1<.+4.(1=.R27.)))P,(32.(22.+1.R1?.)(22.R1?.(1=.R28.)))P,(10.$8.(65.R28.R20.)(54.R28.))P,(10.$8.(54.(55.R22.))R28.)P,(10.$8.(23.R29.(54.R2:.))$4=.)P,(22.R29.$5=.)P,(22.R29.$5>.)P,(10.(3.&40.)R24.(29.&40.R25.))P,(10.(3.&40.)R24.(29.&40.(23.(1<.+4.R26.)+4.)))(50.$47.(51.$47.VR,VHIA,R2;.Vmo,)$52.(43.(44.R24.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R23.R22.R21.(29.&40.VX,)R20.R1?.(29.&40.(1;.R30.))(29.&40.(26.(1;.R30.)+4.))(29.&40.+4.)R1>.R1=.R1<.R1;.R26.(29.&40.(19.R30.))R1:.(29.&40.(58.(2=.VR,)))R25.R19.R18.(29.&40.(23.(59.(19.R30.)+3.)(58.(2=.VR,))))R17.Vs11,R16.R15.R14.R13.)VF,(29.&40.+9=;5<.)Vfc,(45.(3.&40.))R29.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hk J0 OPD SG1 EZ EBY LENZ EM EP0 OEL HR ZA HVv HVV BV BF -> ->; [exfalso; clear - Hk HR; lia|].
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MI1.
    pose proof (u32ro_bound _ _ _ _ EBY) as EB.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    assert (NE10 : 0 <= md_n dE <= 10000).
    { destruct OPD as [[DBJ B]| EQ]; [pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (_ & _ & _ & _ & NRE & _); exact NRE
      | rewrite EQ; pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (_ & _ & NR1 & _); exact NR1]. }
    (* [comment removed for export] *)
    zstep. zstep.
    replace (Z_to_bv 64 (md_p dE + (4 * r + 4) + -8)) with (Z_to_bv 64 (md_p dE + 4 * (r - 1))) by (f_equal; clear; lia).
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OEL (md_p dE + 4 * (r - 1)) 4.
    (* [comment removed for export] *)
    zstep.
    destruct (nth_error zs (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ HR; lia].
    pose proof (u32ro_read asegs mc (md_p dE) zs (r - 1) w _ EBY NTH ltac:(clear - HR; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (limb32_w32_nth zs (Z.to_nat (r - 1)) w NTH) as LW. pose proof (w32_range w) as WR.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite bv_unsigned_sx32 in K0; fold (w32 w) in K0.
    - (* [comment removed for export] *)
      eapply aa_J1; [exact J0| exact OPD| exact HR| exact EM| exact SG1| exact HVv| rewrite EZ, ZA; exact HVV| exact BV| exact BF].
    - (* [comment removed for export] *)
      apply (proj1 (sxz_zero_iff _ WR)) in K0.
      assert (ZA' : lval zs (r - 1) = limbs_val zs).
      { rewrite <- ZA. replace r with (r - 1 + 1) at 2 by (clear; lia). rewrite (lval_succ zs (r - 1)) by (clear - HR; lia). rewrite LW, K0. clear; lia. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply (IH _ _ _ _ _ _ _ _ _ (r - 1)); try eassumption; [clear - Hk; lia| clear - HR K2 NE10; lia| f_equal; clear; lia| f_equal; clear; lia].
      + (* [comment removed for export] *)
        assert (r = 1) as -> by (clear - K2 HR NE10; lia). change (1 - 1) with 0 in ZA'. rewrite lval_0 in ZA'.
        zstep.
        eapply aa_ret0; [exact J0| | exact SG1| |].
        * unfold mpd_val. rewrite SG1, HVv. clear - HVV ZA'. lia.
        * clear - BV EM HR; unfold aaV0, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia.
        * clear - BF D0; unfold aaF0, add_abs_FR, calls_FR, fr_charge in *; lia.
    all: match goal with |- ?g => idtac "SCANLOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01L0@D24976250634.169D50797141399.169D52014138856.169K61206821897.169L1164172544.1   L23100341967.177L29074096193.161L29074168500.164L33085536913.2  L35006717247.3  L35663928186.7  L35839507041.2  L35963164448.4  L36683892759.1  L37070357933.2  L39172636981.0  L39397715809.2  L39399726678.185L39403987028.192L41117966897.193L44822572454.2  L46160487540.168L46160821889.165L47182164405.4  L49584625515.2  L49639216613.182L49639411472.185L51269970326.14 L51269970338.14 L52527267900.192L5262002619.176 L59308546259.3  L59308628179.4  L59310763475.3  L59833689021.3  L60098763854.3  L61212928741.14 L61929812114.168L61931729563.176L61931815313.2  L64182719253.2  L65482851406.1  L65528204888.4  Q12370813529.180Q15148415212.200Q17205389788.179Q22285631880.166Q22285648010.163Q22286196081.165Q24974040330.168Q26207721832.170Q26207967338.167Q26209519061.169Q2656781204.188 Q2656862870.191 Q2658344491.190 Q31651985788.169Q3489202933.199 Q37623042622.179Q39212284437.166Q39212284437.170Q39212284437.191Q39314530340.200Q42081808994.166Q42951517552.188Q43925228937.170Q45029911549.191Q46978751216.200Q46990992626.199Q47243923986.180Q4926406185.166 Q52016320488.168Q54253886744.165Q5483109411.179 Q5485174314.180 Q56761401107.166Q6027349519.169 Q60511567613.166Q60511567613.170Q60511567613.191Q60697995187.170Q6143569392.180 Q62704923501.199Q62965564504.167Q63231501142.163Q64443693026.200Q67099234674.190Q67530527544.191Q8880503606.167 Q9538787269.163 Q9538787269.167 Q9538787269.188 00000O01I01h02^02a03303J03a03h04204G04O04W04[04c04d04l05I05i06B06H06_07607A07G07d08A08V08l09L09e09n0:G0:R0:W0:a0:b0;80;P0;W0;_0;b0;m0<F0=10=;0=E0=O0=Y0>20><0>F0>P0>^0>l0?:0?D0?R0?\0?f0@00@>0@?0@O0@]0@g0A50AC0AQ0AR0A\0B50B?0BI0BS0B`0C90CA0CI0CT0Ca0Ck0D90DP0DZ0Dh0E60EG0EQ0EY0Ea0ElS2ra2sp1X3xs02xs2HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22xs5NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO21p2xs5NEEDR3FSZ3DSX2HB5Ha_st5Hl_stS1XS2ra2sp1X3xs01p2xsS2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S1n3NR1S1X2Ea3SXBS1R3HIA1h2sp2lo3TOP1HS2nE3NRES2xs3HVVS2nES2nE3NE1SS2nE3NRES2ra2sp1X3xs02Ea2nE2zs2xs3NRES2ra2sp1X3xs02Ea2nE2pE2zs2xs3NRES2ra2sp1X3xs02Ea2pE2zs2xsS1n2N1S2ra2sp1X3xs02xs2X03X16S2ra2sp1X3xs02xs2X03X16S1X2nE2pE1HS1n2N1S2ra2sp1X3xs02Ea2zs2xs2E03E16S2ra2sp1X3xs02Ea2zs2xs2E03E16S2dA2dB1v1n2EM2BV3NR1S2dA2dB2nE1v2EM2BV3NRES2ra2sp1X3xs02Ea2pE2zs2xs2E03E16S2ra2sp1X3xs01p2xs2X03X16S1n2K02N0S2nE2zs4LENE2K01n2xs4LEN1S2nE2K03EZ0S3HVVS1R2lo3LOSFS2ra2sp1X3xs01n2xs3NR1S2ra2sp1X3xs01n1p2xs3NR1S1n3NR1S2nE3NE1S1nS1d2D01f2BFS2ra2sp1X3xs01p2xs2X03XALS2ra2sp1X3xs02Ea2pE2zs2xs2X03SPR2E03EAL3EP0S1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xs2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xsS1X3xs02xsS3xs02Ea2zs2xsS3xs02Ea2zs2xsS3xs02Ea2zs2xsS1X3xs02xsS3xs02Ea2zs2xsS1X3xs02xsS1X3xs02xsS1X3xs02xsS3xs02Ea2zs2xsFS1X3xs02xs2X02HBS3xs02Ea2zs2xsS1X3xs02xsS3xs02Ea2zs2xsS3xs02Ea2zs2xsS3xs02Ea2zs2xsFS1X3xs02xsS1X3xs02xs2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xs2X0S1X3xs02xs2HB5Ha_st5Hl_stS3xs02xsS3xs02xsS3xs02zs2xsS1X3xs02xs2X0S1X3xs02xsS3xs02Ea2zs2xsS1X3xs02xs3X162HB5Ha_stS1X3xs02xsS3xs02Ea2zs2xsS3xs02Ea2zs2xsS3xs02Ea2zs2xs2E0S1X3xs02xsS3xs02xsS3xs02xsS3xs02zs2xs". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM"] Lemma aa_SCAN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "PdE,$7.Pv,$8.Pf,$8.Phc,(0.$47.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))PdXc,$7.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs4,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxs10,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(49.$47.VR,VHIA,Vh,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$4:.(4;.$2.)R1>.R1=.R1<.R1;.R1:.R19.)P,(66.R20.R1=.R1<.R1;.R1:.)P,(22.(1=.R21.)$5<.)P,(10.$8.(23.(54.(55.R1<.))(54.(55.R22.)))$4=.)P,(22.R22.$5=.)P,(22.R22.$5>.)(50.$47.(51.$47.VR,VHIA,R22.Vmo,)$52.(43.(44.R1>.(29.&40.(23.(=.&40.Vsp,)-60.))Vgp,Vtp,R1=.R1<.R1;.(29.&40.VX,)R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.(29.&40.(19.R25.))R10.(29.&40.(58.(2=.VR,)))R?.R>.R=.R<.R;.Vs11,R:.R9.R8.R7.)VF,(29.&40.+9=;00.)Vfc,(45.(3.&40.))R20.(46.$47.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 OPD EM HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg n p xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    unfold mpi_cells in CX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as CWX. cbn [md_addr] in CWX. rewrite <- HT1 in CWX.
    pose proof (munch_refl [(X, X + 16)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX1 (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : HM asegs R HIA hc LBc LF m2 |- _ => rename H into HH2 end.
    match goal with H : aobj asegs AL (hcs asegs R HIA hc) m2 X 16 |- _ => rename H into OX2 end.
    match goal with H : rw_cells asegs m2 X _ |- _ => rename H into CX2 end.
    pose proof (xa_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ 1 J0 MU WM MI2 CX2 ltac:(left; reflexivity) HH2 OX2) as J2.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J2.
    destruct OPD as [[DBJ B]|EQ].
    - (* [comment removed for export] *)
      destruct dE as [Ea sE nE pE zs padE ownE]. pose proof (jb_OB _ _ _ _ _ _ _ _ _ _ DBJ) as (OB1 & OB2 & OB3 & OB4 & OB5). pose proof (jb_SXB _ _ _ _ _ _ _ _ _ _ DBJ) as SXB.
      pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (bja_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 J0 B MU WM
                    ltac:(unfold w_client; apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX2| apply Forall_nil])
                    ltac:(cbn; split; [clear - SXB; lia| exact I]) ltac:(intros EN; cbn; split; [pose proof (OB1 EN); clear - H; lia| exact I])) as B2.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in B2.
      assert (B2' : BJE (mkMPD Ea sE nE pE zs padE ownE) hc LBc m2 (mkMPD X 1 n p xs padX own)) by (destruct B2 as [b1 b2 b3 b4 b5]; constructor; assumption).
      clear B2. rename B2' into B2.
      pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B2)) as [(CE2 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CE2. unfold mpi_cells in CE2.
      pose proof (bj_aobj _ _ _ _ _ _ _ _ _ _ B2) as OE2. cbn [md_addr] in OE2.
      clear MU WM B J0 JX. try clear CX1; try clear OX1. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OE2 (Ea + 10) 2.
      (* [comment removed for export] *)
      zstep. replace (zx16 (Z_to_bv 64 nE)) with (Z_to_bv 64 nE) by (unfold zx16; rewrite !unsigned_lit by (clear - NRE; lia); rewrite Z.mod_small by (clear - NRE; lia); reflexivity).
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; rewrite ?Z.mod_small in K0 by (clear - NRE; lia).
      { (* [comment removed for export] *)
        eapply aa_ret0; [exact J2| | reflexivity| clear - BV EM NRE; unfold aaV0, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF0, add_abs_FR, calls_FR, fr_charge in *; lia].
        unfold mpd_val. cbn [md_sg md_limbs].
        destruct zs; [cbn [limbs_val] in HVV; clear - HVV; lia| exfalso; cbn [length] in LENE; clear - LENE K0; lia]. }
      assert (EN : ownE <> LNull) by (intros C; destruct (OWNE0 C) as [_ EZ0]; clear - K0 EZ0; lia).
      ddestruct (OWNE1 EN) as (NE1 & EP0 & EPAL & _ & ESK & _).
      pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B2) as (_ & _ & _ & _ & _ & _ & _ & OWNE2). ddestruct (OWNE2 EN) as (_ & _ & _ & EBY2 & _).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in EBY2.
      pose proof (bj_aobjL _ _ _ _ _ _ _ _ _ _ B2 EN) as OEL2. cbn [md_p md_n] in OEL2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep.
      eapply (aa_SCANLOOP (Z.to_nat nE) (mkMPD Ea sE nE pE zs padE ownE) zs) with (r := nE); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        [clear - NE1; lia| exact J2| left; split; [exact DBJ| exact B2]| reflexivity| reflexivity| exact EBY2| exact LENE| exact EM| exact EP0| exact OEL2
        | clear - NE1; lia| apply lval_fullA; exact LENE| reflexivity| exact HVV| exact BV| exact BF| f_equal; clear; lia| f_equal; clear; lia].
    - (* [comment removed for export] *)
      subst dE. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2' & OWN2 & OWN2'). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2', OWN2, OWN2'. unfold mpi_cells in CX2'.
      pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2) as OX2'. cbn [md_addr] in OX2'.
      clear MU WM J0 JX. try clear CX1; try clear OX1. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OX2' (X + 10) 2.
      zstep. replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
      zstep. if_cases K0; zify_cond K0; rewrite ?Z.mod_small in K0 by (clear - NR1; lia).
      { eapply aa_ret0; [exact J2| | reflexivity| clear - BV EM NR1; unfold aaV0, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; lia| clear - BF D0; unfold aaF0, add_abs_FR, calls_FR, fr_charge in *; lia].
        unfold mpd_val. cbn [md_sg md_limbs].
        destruct xs; [cbn [limbs_val] in HVV |- *; clear - HVV; lia| exfalso; cbn [length] in LEN1; clear - LEN1 K0; lia]. }
      assert (ON : own <> LNull) by (intros C; destruct (OWN2 C) as [_ [N0 _]]; clear - K0 N0; lia).
      ddestruct (OWN2' ON) as (EO & N1 & XIN & XPAL & ARR2 & P0 & PC & PI & OP2 & P47). subst own.
      zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep.
      eapply (aa_SCANLOOP (Z.to_nat n) (mkMPD X 1 n p xs padX LHeap) xs) with (r := n); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        [clear - N1; lia| exact J2| right; reflexivity| reflexivity| reflexivity| apply u32arr_ro; exact ARR2| exact LEN1| exact EM| exact P0| exact OP2
        | clear - N1; lia| apply lval_fullA; exact LEN1| reflexivity| exact HVV| exact BV| exact BF| f_equal; clear; lia| f_equal; clear; lia].
    all: match goal with |- ?g => idtac "SCAN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308579668.400000=S1X2Ea3SXE2H5". (* [comment removed for export] *)
  #[using="IMG"] Lemma mk_JBd : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "PdE,$7.Pm1,P,(3.&40.)(5.(3.&8.))P,(<.$47.VR,VLF,Vm,VLB,(=.&40.Vsp,)R2.)P,(14.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R3.Vlo,(=.&40.Vsp,))P,(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(19.R4.)+10.)P,P,(10.$11.(12.R5.)$1:.)(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(1;.R6.)(1<.+4.(1=.R6.)))P,(21.(22.(23.VX,+10.)(19.R6.))(22.(23.(19.R6.)+10.)VX,))P,P,(10.$11.(12.R7.)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.R9.))))(10.$2?.(34.$47.(35.(23.(1;.R:.)R2.)))$31.)(10.$2?.(30.(1;.R9.)(1<.+4.(1=.R9.)))$31.)P,(69.$47.(2=.VR,)(2>.$47.VR,VHIA,Vh,)R7.(19.R8.)+10.)P,P,(10.$11.(12.R9.)$13.)(69.$47.(2=.VR,)(2>.$47.VR,VHIA,Vh,)R9.(1;.R:.)(1<.+4.(1=.R:.)))P,(9.$47.VR,VHIA,Vh,VLB,VLF,R9.)P,(<.$47.VR,VLF,R:.VLB,(=.&40.Vsp,)R;.)(32.(5:.$47.VR,VHIA,VLB,VLF,Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,R<.)(53.$47.VR,VHIA,VLF,Vsp,R<.Vh,VLB,R;.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))")
(* [comment removed for export] *).
  Proof.
    intros dE m1; intros ME OE CRE CREL SXE IE OEs OEl HM1 ME1. dpose OE as (OE1 & OE2 & OE3 & OE4 & OE5).
    destruct dE as [Ea sE nE pE zs0 padE ownE].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    split.
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption.
      intros EO RO hc LBc mc HMc. eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HMc| exact (IE EO RO)].
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      + exact ME1.
      + exact OE2.
      + intros EOX EN. destruct OE3 as [C|[C|[C|C]]]; [exfalso; injection C; intros; clear - SXE H5; lia| exfalso; exact (C EOX)| exfalso; exact (EN C)| exact C].
      + exact OEs.
      + intros EN. pose proof (opnd_viewA _ _ _ _ _ _ _ ME1) as [(_ & _ & _ & _ & _ & OW) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OW.
        destruct ownE; [exfalso; exact (EN eq_refl)| |].
        * ddestruct OW as (_ & EIN & _). eapply hm_aobj_block; [exact HM1| exact EIN].
        * exact (OEl eq_refl).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis COPY : mpi_copy_stmtA asegs R HIA A_MPI_COPY.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02`0@D10492578459.223D11157215372.219D11157215372.220D11157215372.221D11157215372.224D11157215372.225D11157215372.226D11157215372.227D1227298075.219 D1227298075.225 D1503938095.222 D21367999998.225D34354337919.217D35881667587.165D35881667587.166D43120647727.219D43120647727.220D43120647727.221D43120647727.224D43120647727.225D43120647727.226D43120647727.227D51255084822.166D53615092884.218D53615092884.224D61949433775.165D61949433775.166K14554379081.165K14554379081.166K68206801384.165K68206801384.166L11075936116.153L14550820926.2  L14714826937.3  L15282565064.2  L16017091139.5  L17097338356.153L17305750384.4  L19431261630.4  L19687428440.153L19945316590.2  L23124392564.153L23459206846.172L23459206846.173L24026950640.22 L24714629722.14 L25465666776.153L26479207440.3  L26983617546.4  L27213746373.22 L28125529944.153L29010569984.213L29025845208.153L29135309044.153L29762660275.153L3070335905.4   L31686769240.153L31743414849.8  L31743414976.8  L31755912410.7  L34456472569.2  L35161367924.153L35653441506.7  L36180999398.161L37742778000.225L40834179097.172L40834179097.173L41114184774.22 L41172169716.153L42479632545.4  L43059266230.159L43671330526.3  L43679985268.152L44778233891.3  L44807604259.22 L5065130740.153 L50786303024.2  L52253708504.153L5259987632.173 L5259987632.174 L5262094874.172 L5262094874.173 L5262098304.171 L53617338766.7  L55720577396.153L59308628433.4  L59308632561.1  L59314955108.4  L60098763854.3  L60692334296.153L60860973994.5  L61601561944.153L61747685364.153L62042415875.153L62505661912.152L62998362800.22 L64270350808.153L64491265552.2  L6482734895.4   L65178513496.153L66988777498.171L66990871850.173L66990871850.174L67758486644.153L68211501598.2  L7695952367.7   L8303040740.2   P24721069904.225Q10333294960.180Q15643324129.161Q18365925601.162Q18378753154.162Q18694078840.181Q18694180728.182Q21800401414.180Q21879645826.162Q24328806760.181Q24329039720.182Q24389563138.162Q24721069904.225Q25160350961.180Q25513505925.164Q25513505925.165Q25662327983.182Q25662554799.181Q27584944865.162Q27907200258.162Q30415036802.162Q31228739884.182Q31228907308.181Q31271525473.162Q31396957457.180Q32655500769.162Q33918256002.162Q35014402586.182Q35014503450.181Q35715139857.180Q36425882626.162Q36426122721.180Q3830427394.162 Q39517585209.165Q39939554818.162Q41152393185.162Q4141071397.180 Q42250699284.225Q42250699542.190Q44648843873.162Q4533518817.162 Q49698585326.163Q49698585326.164Q50299420301.182Q50299646093.181Q51235796833.162Q52101170785.162Q53969792887.182Q53969822071.181Q53972118266.180Q55780705378.164Q55780705378.165Q59256763233.162Q59843137889.162Q60511257090.162Q61802108972.182Q61802206764.181Q63856323923.162Q63856323923.163Q6414620453.180 Q64255452024.182Q64255683960.181Q64333403626.163Q66522067074.162Q67528989526.165Q67528989526.166Q68319848314.220Q68319848314.221Q9843367298.161 00000100200300S00T00U00V01601701801901T01U02K03c03d04D04E04F04G04g04h06706806907D08m09i0;D0<@0=[0>60>70>A0>H0>\0?70?C0?Q0?l0@30@N0@l0AJ0Ai0Aj0BE0BO0B[0C10CL0CM0Ch0DC0D^0Dj0EE0Eb0F?0FY0F`0G;0GS0Gn0HI0Hf0IC0IU0J00J<0J_0Jg0KB0KJ0K^0L90L?0LZ0M<0M^0N@0Nb0OD0OM0Oh0P50P90PF0PP0Pk0Po0QJ0Qe0R@0R[0S;0SV0S\0Sj0TE0Tc0UA0U_0V:0V;0VI0VR0WU0WV0Wo0XH0Xf0Y@0YZ0Y[0Z90Z:0Z;0ZY0ZZ0[40[_0\i0\j0\k0]D0]b0^@0^[0_60_O0_b0`;0`Y0a40aO0aP0an0ao0bM0c>0c\0d50d60dm0ed0f=0fV0g:0g^0g_0g`0h90hR0hm0iH0ic0jS0k^0l70lP0ln0lo0m00mI0mb0n<0n=0n>0nW0o50oe11411511611TFFFS2ra2sp1X3xs02dA2dB3ABD3BBD1x2HxFFFS2ra2sp1X3xs02dA2dB3ABD3BBD1x2HxFFFS2ra2sp1X3xs02dA2dB3ABD3BBDFS1R3HIA1h2ra2sp1X3xs02dA2dB3TOP3ABD3BBD2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs02dA2dB3TOP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10FS2ra2sp1X3xs02dA2dB3ABD3BBD1x2HxFFFS2ra2sp1X3xs02dA2dB3ABD3BBD1x2HxFS1R2ra2sp3s101X3xs02dA2dB2lo4SLO25NEEDR3LOS2X03SPR2A02B03ABD3BBD2HB5Ha_st5Hl_stFFS1R2ra2sp1X3xs02dA2dB2lo4SLO25NEEDR3LOS2X03SPR2A02B03ABD3BBD2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02dA2dB2lo4SLO25NEEDR3LOS2X03SPR2A02B03ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S1R2ra2sp3xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OA42HB5Ha_st5Hl_stS1R2sp2s03xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OA42HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10S1R2ra2sp3xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OB42HB5Ha_st5Hl_stS1R2sp2s03xs02dA2dB2lo4SLO25NEEDR3ABD3BBD3OB42HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10S2ra2sp1X3xs02dA2dB3ABD3BBDFS1X2dA3KAXS2dA2dBS1R2sp2lo4SLO25NEEDRS2ra2sp1X3xs02dA2dB3ABD3BBDS2sp2dA2lo1HS2sp2dA2lo3OA4S2ra2sp1X3xs02dA2dB3ABD3BBDS2sp2loS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB2A03ABD3BBDS2ra2sp1X3xs02dA2dB2A03ABD3BBDS1R3HIA1h2sp2dA2dB3BUD3SPR4NRA'FS2ra2sp1X3xs02dA2dB3ABD3BBDS1X2dB3KXBS2dA2A01a2HaS1R3HIA1h2sp2dA2dB3TOPS2ra2sp1X3xs02dA2dB3ABD3BBDFS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2dA2dB4NRA'S2ra2sp1X3xs02dA2dB3ABD3BBDS1X2sX2nX2pX3xs04padX4ownX2dAS1X2sX2nX2pX3xs04padX4ownX2dBS1X2sX2nX2pX3xs04padX4ownXS2dA2dBS2ra2sp1X3xs02dA2dB3ABD3BBDS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS1R2ra2sp1X3xs02dA2dB3ABD3BBDS1R2ra2sp1X3xs02dA2dB3ABD3BBDS2sp2dA2dB3SPA3SPRS2ra2sp1X3xs02dA2dB3ABD3BBDS2sp2dB2lo1HS2ra2sp1X3xs02dA2dB2lo4LOSP3ABD3BBDS1X2dA1DS2ra2sp1X3xs02dA2dB3ABD3BBDS1X2dB1DS1R2sp2dA2dB2lo4SLO2S2ra2sp1X3xs02dA2dB3ABD3BBDS1d2D0S2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB2X03X163ABD3BBDS2ra2sp1X3xs02dA2dB2X03X163ABD3BBDS2ra2sp1X3xs02dA2dB2X03X163ABD3BBDS2ra2sp1X3xs02dA2dB2X03X163ABD3BBDS2ra2sp1X3xs02dA2dB2X03X163ABD3BBDS2sp2dA1HS2ra2sp1X3xs02dA2dB3ABD3BBDS1X2dB3KXB2K2S2KRS1X2dA1D1E2dBS1R2lo3LOSS2ra2sp1X3xs02dA2dB3ABD3BBDS2spS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDS1R3HIA1h2sp2dA2dB1d2D04BUDF3SPRS2ra2sp1X3xs02dA2dB3ABD3BBDS1d2D0S2sp2dB2lo3OB4S2ra2sp1X3xs02dA2dB3ABD3BBDS2ra2sp1X3xs02dA2dB2B03ABD3BBDS2ra2sp1X3xs02dA2dB2B03ABD3BBDS2ra2sp1X3xs02dA2dB2B03ABD3BBDS2ra2sp1X3xs02dA2dB3ABD3BBDFS2sp2dA2lo3OA4S2dA4NRA'S1R2sp1X3xs02dA2dB2lo4SLO25NEEDR3FSZ3DSX3ABD3BBD3OA43OB43KXB3KAX2K2FS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB4IMG'3ABD3BBDS1R3xs02dA2dB4IMG'3ABD3BBDFS2sp3xs02dA2dB2lo4LOSP3ABD3BBDFFS2sp3xs02dA2dB2lo4LOSP3ABD3BBDFS1R3xs02dA2dB4IMG'3ABD3BBDS2ra2sp3xs02dA2dB2lo3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10FFS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS3xs02dA2dB3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDFS2sp3xs02dA2dB2lo4LOSP3ABD3BBDFS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3s103xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_stS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDFS1R2sp3xs02dA2dB2lo4SLO25NEEDR3LOS4SP643ALO3ACP3ABD3BBDS1R2sp3xs02dA2dB2lo4SLO25NEEDR3LOS4SP643ALO3ACP3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB4SP643ABD3BBD2HB5Ha_stS2sp3xs02dA2dB4SP643ABD3BBD2HB5Ha_stFFS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS1R3xs02dA2dB5ALWF'3ABD3BBDS2ra2sp3xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo3ABD3BBDS2sp3xs02dA2dB2lo4LOSP3ABD3BBDFFS2sp3xs02dA2dB3ABD3BBD2HBS2sp3xs02dA2dB3ABD3BBD2HBS1R3xs02dA2dB4IMG'3ABD3BBDFFS2sp3xs02dA2dB3ABD3BBD2HBS2sp3xs02dA2dB2lo4LOSP3ABD3BBDS2ra2sp3xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_stS2sp2s03xs02dA2dB2lo4LOSP3ABD3BBD2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s10FFS2sp3xs02dA2dB2lo4LOSP3ABD3BBD". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC JC TPV UWX D0 BUD BUDF SLO2 VALM COPY"] Lemma aa_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_abs_W ()) "Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(:.$47.VR,VHIA,Vh,Vmo,)P,(;.$47.Vm,VLB,VdA,)P,(<.$47.VR,VLF,Vm,VLB,(=.&40.Vsp,)VdB,)P,(>.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)P,(>.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdB,)P,(>.VdA,VdB,)P,(14.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,Vlo,(=.&40.Vsp,))P,(14.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdB,Vlo,(=.&40.Vsp,))P,(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(19.VdA,)+10.)P,P,(10.$11.(12.VdA,)$1:.)(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(1;.VdA,)(1<.+4.(1=.VdA,)))P,(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(19.VdB,)+10.)P,P,(10.$11.(12.VdB,)$1:.)(15.(16.VR,)(17.$2.VLB,(18.VLF,))Vlo,(1;.VdB,)(1<.+4.(1=.VdB,)))P,(24.$47.Vm,Vlo,(=.&40.Vsp,))P,(2;.$47.Vm,)P,(2<.$47.(2=.VR,)(2>.$47.VR,VHIA,Vh,)Vm,(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(2<.$47.(2=.VR,)(2>.$47.VR,VHIA,Vh,)Vm,VdA,)P,(2<.$47.(2=.VR,)(2>.$47.VR,VHIA,Vh,)Vm,VdB,)P,P,(?.(10.$8.(19.VdA,)(19.(48.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))))P,(10.$11.(12.VdA,)$13.)(10.$2?.(30.(1;.VdA,)(1<.+4.(1=.VdA,)))$31.)P,P,(10.$11.(12.VdA,)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.VdA,))))(10.$2?.(34.$47.(35.(23.(1;.VdA,)R2.)))$31.)(10.$2?.(30.(1;.VdA,)(1<.+4.(1=.VdA,)))$31.)P,P,(10.$11.(12.VdB,)$13.)P,Pi,$8.P,(32.(22.=R1.)(33.R1.(1<.+4.(1=.VdB,))))(10.$2?.(34.$47.(35.(23.(1;.VdB,)R2.)))$31.)(10.$2?.(30.(1;.VdB,)(1<.+4.(1=.VdB,)))$31.)(3?.$47.$52.(42.(43.(44.Vra,Vsp,Vgp,Vtp,R20.R1?.R1>.Vs0,Vs1,(29.&40.VX,)(29.&40.(19.VdA,))(29.&40.(19.VdB,))R1=.R1<.R1;.R1:.R19.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R18.R17.R16.R15.)VF,(29.&40.$6:.)Vfc,(45.(3.&40.))Vm,(46.$47.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK MA0 MB0 SXA SXB SAB OA OB CRA CRAL CRB CRBL ST MI OXA OAA OBA IA1 IA2 IB2. unfold A_MPI_ADD_ABS.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 96 AA_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof MA0 as [(CA0 & AAL & A0 & LENA & NRA' & OWNA) SGA]. pose proof (opnd_viewA _ _ _ _ _ _ _ MB0) as [(CB0 & BAL & B0 & LENB & NRB & OWNB) SGB]. unfold MPI_MAX_LIMBS in NRA', NRB.
    pose proof (rw_cells_bound _ _ _ _ CA0) as ABD. pose proof (rw_cells_bound _ _ _ _ CB0) as BBD. unfold mpi_cells in ABD, BBD. cbn [cells_size csize Nat.add] in ABD, BBD.
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof OXA as [OX _]. pose proof OAA as [OAs OAl]. pose proof OBA as [OBs OBl]. cbn [md_addr] in OX.
    pose proof SXA as SXA0. unfold mpd_sep in SXA, SXB, SAB. cbn [md_addr] in SXA, SXB, SAB.
    assert (VAL : AA_VAL_A = limbs_val (md_limbs dA) + limbs_val (md_limbs dB)) by (unfold AA_VAL_A, mpd_abs; reflexivity).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 96%nat ST.
    (* [comment removed for export] *)
    do 13 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    change (rw_cells asegs m1 (bv_unsigned sp + -96) AA_FRAME_A) in FR.
    pose proof ST as ST1.
    pose proof (xa_start _ _ _ _ _ _ _ _ _ _ _ _ JC m1 HH MI ST1 FR OX MU WM) as J0.
    (* [comment removed for export] *)
    assert (MA1 : mpd_at asegs m1 LB dA).
    { eapply mpd_at_munch_any; [exact MA0| exact MU| exact WM| cbn; split; [clear - OA4; lia| exact I]|].
      intros ON. cbn. split; [destruct (OA5 ON); clear - H; lia| exact I]. }
    assert (MB1 : opnd_atA asegs R LF m1 LB (bv_unsigned sp) dB).
    { eapply opnd_atA_munch_any; [exact MB0| exact MU| exact WM| cbn; split; [clear - OB4; lia| exact I]|].
      intros ON. cbn. split; [destruct (OB5 ON); clear - H; lia| exact I]. }
    assert (WC0 : w_client (hcs asegs R HIA h) [(lo, bv_unsigned sp)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]. }
    assert (OAl1 : md_own dA = LStatic -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dA) (4 * md_n dA)) by (intros E; eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact (OAl E)]).
    assert (OBl1 : md_own dB = LStatic -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dB) (4 * md_n dB)) by (intros E; eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact (OBl E)]).
    (* [comment removed for export] *)
    assert (IDA : md_addr dA = X -> dA = dX) by (intros E; destruct SXA as [E'|D]; [symmetry; exact E'| exfalso; clear - D E; lia]).
    assert (IDB : md_addr dB = X -> dB = dX) by (intros E; destruct SXB as [E'|D]; [symmetry; exact E'| exfalso; clear - D E; lia]).
    pose proof (opnd_atA_mpd asegs R LF m LB (bv_unsigned sp) dA MA0) as MA0o. pose proof (opnd_atA_mpd asegs R LF m1 LB (bv_unsigned sp) dA MA1) as MA1o.
    assert (JBA : md_addr dA <> X -> JBE dA /\ BJE dA h LB m1 dX).
    { intros NE. eapply mk_JBd; try eassumption. all: try (intros EO RO; exact (IA2 EO RO)).
      all: destruct SXA as [E|D]; [exfalso; apply NE; rewrite <- E; reflexivity| clear - D; lia]. }
    assert (JBB : md_addr dB <> X -> JBE dB /\ BJE dB h LB m1 dX).
    { intros NE. eapply mk_JBd; try eassumption. all: try (intros EO RO; exact (IB2 EO RO)).
      all: destruct SXB as [E|D]; [exfalso; apply NE; rewrite <- E; reflexivity| clear - D; lia]. }
    assert (BV0 : 0 <= aaV0) by (unfold aaV0, grow_PHI; unfold AVOL_CALL; clear - NRA'; lia).
    assert (BF0 : 0 <= aaF0) by (unfold aaF0, calls_FR, fr_charge; clear - D0; lia).
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases KXB; zify_cond KXB; rewrite ?Z.mod_small in KXB by (clear - BBD X16 X0; lia).
    - (* [comment removed for export] *)
      pose proof (IDB (eq_sym KXB)) as EDB.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KAX; zify_cond KAX; rewrite ?Z.mod_small in KAX by (clear - ABD X16 X0; lia).
      + (* [comment removed for export] *)
        pose proof (IDA KAX) as EDA. rewrite KAX.
        eapply aa_SCAN with (dE := dX); [exact J0| right; reflexivity| unfold aaM; rewrite <- EDA; clear; lia| | exact BV0| exact BF0].
        rewrite VAL, ?EDA, ?EDB. clear; lia.
      + (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by (clear - BBD X16 X0; lia); [| exfalso; clear - K2 KXB; lia].
        destruct (JBA ltac:(clear - KAX; lia)) as [DBJ B].
        eapply aa_SCAN with (dE := dA); [exact J0| left; split; [exact DBJ| exact B]| unfold aaM; clear; lia| | exact BV0| exact BF0].
        rewrite VAL, ?EDB. clear; lia.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases KAX; zify_cond KAX; rewrite ?Z.mod_small in KAX by (clear - ABD X16 X0; lia).
      + (* [comment removed for export] *)
        pose proof (IDA KAX) as EDA.
        destruct (JBB ltac:(clear - KXB; lia)) as [DBJ B].
        eapply aa_SCAN with (dE := dB); [exact J0| left; split; [exact DBJ| exact B]| unfold aaM; clear; lia| | exact BV0| exact BF0].
        rewrite VAL, ?EDA. clear; lia.
      + (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by (clear - BBD X16 X0; lia); [exfalso; clear - K2 KXB; lia|].
        zstep. zstep.
        destruct (JBB ltac:(clear - KXB; lia)) as [DBJ B].
        pose proof (xa_X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MX1.
        destruct XW as [CW DXP].
        clear MU WM.
        assert (CSEP : P_mpi_copy.copy_sep dX dA lo (bv_unsigned sp + -96)).
        { unfold P_mpi_copy.copy_sep. split; [exact OA1|]. split; [exact OA2|]. split; [exact OA3|]. split; [clear - OA4 SLO2 NEEDR; lia|].
          split; [intros AN; destruct (OA5 AN); [left; assumption| right; clear - H SLO2 NEEDR; lia]| intros a Ha; clear - Ha A0; lia]. }
        eapply aevtA_call.
        { intros mo1 [HK1 MF1]. pose proof COPY as CP. unfold mpi_copy_stmtA, mpi_copy_stmtA_gen in CP.
          eapply CP with (h := h) (LB := LB) (LF := LF) (dX := dX) (dY := dA) (lo := lo) (d := d);
            rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; try eassumption; try reflexivity.
          all: try (unfold P_mpi_copy.copy_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; split; [exact OA1|]; split; [exact OA2|]; split; [exact OA3|];
                    split; [clear - OA4 SLO2 NEEDR; lia| intros AN; destruct (OA5 AN); [left; assumption| right; clear - H SLO2 NEEDR; lia]]).
          all: try (split; [eapply client_wrange_sp_mono; [| exact CW]; clear - SLO2 NEEDR; lia| exact DXP]).
          all: try (rewrite unsigned_lit by (clear; lia); reflexivity).
          all: try (intros EO; apply IA1; [cbn [md_addr]; clear - KAX; lia| exact EO]).
          all: unfold copy_PHI, copy_FR, add_abs_PHI, add_abs_FR, grow_PHI, calls_FR, fr_charge in *; unfold AVOL_CALL in *;
               clear - LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF D0 LOSP TOP NRA' NRB; try lia.
          all: match goal with |- ?g => idtac "COPY-PRE-LEFT:" g end. }
        (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
        ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
        injection E as E1 E2. subst ms' mo'.
        rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
          replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
        presA_transport HP2.
        pose proof ST2 as ST2'.
        unfold P_mpi_copy.copy_R in CR. ddestruct CR as (CR1 & CAD & CPD & CFR).
        assert (BK : binop_keep LB dX dX2).
        { split; [exact CAD|]. split; [exact CPD|]. split; [exact CFR|]. destruct CR1 as [(_ & _ & Bn & _)|(_ & En & _)]; [exact Bn| rewrite En; apply Z.le_refl]. }
        pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -96) (copy_PHI dA) (copy_FR d) J0 ltac:(clear - SLO2 NEEDR; lia)
                      ltac:(unfold copy_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA'; lia) ltac:(unfold copy_FR, calls_FR, fr_charge; clear - D0; lia)
                      MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
        pose proof (bja_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ (bv_unsigned sp + -96) J0 B ltac:(clear - SLO2 NEEDR; lia) MI2 HP2 HCS2 HH2 MX2 OUT2 FRA2) as B1.
        apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
        clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
        pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
        (* [comment removed for export] *)
        zstep. zstep. if_cases KR; zify_cond KR.
        * (* [comment removed for export] *)
          destruct CR1 as [(-> & _)|(-> & _)]; [exfalso; apply KR; reflexivity|].
          eapply aa_ret; [exact J1| right; reflexivity| unfold copy_PHI, aaV0, add_abs_PHI, aaM, grow_PHI in *; unfold AVOL_CALL in *; clear - NRA' NRB; lia
                         | unfold copy_FR, add_abs_FR, calls_FR, fr_charge in *; clear - D0; lia].
        * destruct CR1 as [(-> & CV & CN)|(-> & _)]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
          eapply aa_SCAN with (dE := dB); [exact J1| left; split; [exact DBJ| exact B1]| unfold aaM; clear; lia| | unfold copy_PHI, aaV0; apply Z.le_refl| unfold copy_FR, aaF0; apply Z.le_refl].
          rewrite VAL. pose proof (mpd_val_abs dX2 (proj2 MX2)) as VX. pose proof (mpd_val_abs dA SGA) as VA. unfold mpd_abs in VX, VA.
          rewrite <- VX, CV, VA. reflexivity.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WA.


(* [comment removed for export] *)
