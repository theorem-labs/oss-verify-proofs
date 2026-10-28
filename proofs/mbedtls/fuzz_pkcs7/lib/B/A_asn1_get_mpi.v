(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX HeapIface Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_mpi_addsub P_mpi_read_binary P_asn1_get_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_alloc_lib A_mpi_read_binary_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import LxConv_getlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P02a873925e9ace9d 0 5 0 1 29 1 34 1 40 1 41 1P03881b8a7b383eee 0 2 0 1 1 1P0aec0fbcc4723a6e 0 3 0 1 37 1 44 1P0b769c1f87a680d6 0 2 0 1 30 1P0bc2e43d3baba714 0 2 0 1 2 1P0e7092ee1a9b319d 0 2 0 1 2 1P10e38161c3581116 0 4 0 1 29 1 34 1 41 1P15e4544370488ba9 0 2 0 1 1 1P1964722cbab38625 0 4 0 1 31 1 36 1 43 1P1988f1afd9789b3d 0 2 0 1 31 1P1c17594ae087d5f6 2 40 0 6 0 8 1 8 41 8 47 8 52 8 53 8 0 4 0 8 2 8 52 8 53 8P21f2b9dff192b802 0 2 0 1 30 1P236a0ef13a164693 0 2 0 1 31 1P279284114fd4d6fd 0 4 0 1 31 1 36 1 43 1P27a32f0249be1ab0 0 4 0 1 38 1 42 1 45 1P2ca776b7bb72b5e4 0 4 0 1 29 1 34 1 41 1P2e93149910df3ec7 0 3 0 1 35 1 42 1P2ec1b00e9217ba86 0 4 0 1 35 1 39 1 42 1P318c2ca965b591d5 0 2 0 1 31 1P33c264f53eeb0477 0 2 0 1 1 1P348a6b285a737a65 0 2 0 1 31 1P36408e381912e889 0 2 0 1 2 1P399bc17ef34587cb 0 3 0 1 38 1 45 1P3a6a35e0481deaa6 0 3 0 1 35 1 42 1P3a6e012493458a64 0 4 0 1 32 1 37 1 44 1P3b06a82ffe0da40f 0 2 0 1 30 1P3f1fb0ded1f06539 0 3 0 1 37 1 44 1N012be8a9a96617a1N01d020d04d8efc32N04d2b79c710aa513N055992265d483e5aN09dc0e28cff969ceN0a56f04183d9e864N0a93ce4b9315a600N0b75f5e2e9086b7dN0be10a1bb3df5750N0cc871fa5a18affbN0f4e37f16743a03aN10657cc13006f949N1d9acb8f9d25558dN1e3e320af53a448bN1e94b87c3ddad92aN2224eb66c6daec89N2244d095e7f0e8ceN25da8dcdb62e437aN2a34b77022b3f983N2e261f70bfa5cc4eN308b63c184073940N31885415416909d2N3322c46556448182N367b1e2c3ad343b9N387bbb9c6c99020eN3a4b9f46be72b348N3c180fd757207b79N3d1af28ad748f9c0N3d30ca18163d8aceN3d61e3fe07787d2eN3eb677f5c20852ad"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_asn1_get_mpi () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.MPI_RB_PHI"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.MPI_RB_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpi_read_binary_stmtA"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "asn1_get_mpi_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Walk.hdr_facts"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.le"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.J1Q"; "Walk.FAILQ"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "asn1_get_mpi_stmtA"; "A_ASN1_GET_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.A_MPI_READ_BINARY"].


Definition A_ASN1_GET_MPI : Z := 0x099e78.
Notation ASN1_GET_MPI_STACK_A := 240 (only parsing).   (* [comment removed for export] *)

Definition asn1_get_mpi_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP P END : Z) (dX : mpd) (lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O20.O1?.O1>.)Lh',(5.O20.O1?.O1>.)(1.(6.$7.)LLB',(6.$7.)(1.$8.LdX',$8.(1.$9.Lr,$9.(1.$9.Lp',$9.(:.(;.$0.R16.(<.(=.(>.O1:.O19.O18.O17.R15.R14.R13.O16.O15.(?.&40.R2.)R12.R11.R10.R?.R>.R=.R<.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R;.R:.R9.R8.)O:.(10.O1:.)O9.(11.(2.&40.))R7.(12.O20.))R6.))(:.(13.O20.R7.)(:.(14.O20.R7.O4.(15.&40.O19.))(:.(16.O1.R6.)(:.(17.O20.O1?.(18.O1<.O5.)O1;.(15.&40.O19.)(19.O1?.)(1:.O20.O1?.O1>.O1=.)(1;.(1<.$9.$9.)(1=.$9.$9.O8.(1>.O8.+8.))(1;.(1<.$9.$9.)(1=.$9.$9.(1?.O5.)(1>.(1?.O5.)+10.))(20.(1<.$9.$9.))))O2.R7.)(:.(;.$9.(21.O20.O1?.O1>.R5.)(21.O20.O1?.O1>.O1=.))(:.(;.$9.(1:.O20.O1?.O1>.R5.)(1:.O20.O1?.O1>.O1=.))(:.(;.$9.(22.O20.O1?.O1>.R5.)(22.O20.O1?.O1>.O1=.))(:.(23.O20.O1?.O1>.R5.R6.)(:.Px,$9.P,(24.O20.O1?.O1>.O1=.R1.)(24.O20.O1?.O1>.R7.R2.)(:.(25.(26.O20.O1?.O1>.R5.)(1>.(26.O20.O1?.O1>.O1=.)(27.(28.O6.O7.))))(:.(25.(29.O20.O1?.O1>.R5.)(1>.(29.O20.O1?.O1>.O1=.)(2:.O3.)))(:.(2;.O20.O1?.O1>.R5.R4.O1;.R7.)(:.(2<.O20.R7.R4.R3.)(:.(2=.O1<.O5.R4.R3.)(:.(2>.O20.R7.O8.(1;.$2?.(30.(?.&40.R1.))(20.$2?.)))(:.(:.(25.O7.R1.)(25.R1.O6.))(:.(:.(31.-7?.R2.)(25.R2.=))(:.P,(;.$9.R2.=)(:.(25.(1>.O7.+2.)R2.)(;.$9.(32.R4.)+1.))Pb,$7.P,(33.$7.R1.(34.R4.))(35.(33.$7.R2.(34.O5.))(36.O1?.(18.O1<.O5.)O1;.(37.$9.$9.R2.)(38.$9.$9.R2.)))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_mpi_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY RB : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi ()) "P,(39.O5.O4.O3.O1.)Ph,(5.O5.O4.O3.)PLB,(6.$7.)PLF,(6.$7.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PPP,$9.PP,$9.PEND,$9.PBUF,$9.Pbs,(6.(2.&8.))PdX,$8.Plo,$9.Pd,$9.P,(2;.O5.O4.O3.R2>.R2=.R2<.R:.)P,(23.O5.O4.O3.R2?.R:.)P,(2>.O5.R<.R:.(1;.$2?.(30.(?.&40.R9.))(20.$2?.)))P,(3;.O5.R=.R8.R7.)P,(25.R9.R;.)P,(25.R<.R;.)P,(25.R<.(1>.R;.(3<.(3=.(2.&8.)R:.))))P,(31.(1>.R<.(3<.(3=.(2.&8.)R;.)))(3>.+2.+3?.))P,(25.(1>.(1>.R=.(3<.(3=.(2.&8.)R<.)))+8.)(3>.+2.+2?.))P,(2<.O5.R13.R36.R<.)P,(3?.(;.$40.(41.R=.)$42.))P,(43.(44.O4.)(45.$7.R38.(46.R37.))(15.&40.R35.)(21.O5.O4.O3.R39.)R>.)P,(35.(25.(1>.R14.+8.)R11.)(25.(1>.R11.(3<.(3=.(2.&8.)R10.)))R14.))P,(35.(25.(1>.R15.+8.)(1?.R10.))(25.(1>.(1?.R10.)+10.)R15.))P,P,(;.$40.(41.R11.)$47.)(35.(25.(1>.R17.+8.)(48.R12.))(25.(1>.(48.R12.)(49.+4.(4:.R12.)))R17.))P,(35.(25.(1>.R14.(3<.(3=.(2.&8.)R13.)))(1?.R12.))(25.(1>.(1?.R12.)+10.)R14.))P,P,(;.$40.(41.R13.)$47.)(35.(25.(1>.R16.(3<.(3=.(2.&8.)R15.)))(48.R14.))(25.(1>.(48.R14.)(49.+4.(4:.R14.)))R16.))P,(;.$9.(4;.R19.+8.)=)P,(31.=R1:.)P,(31.=R18.)P,(14.O5.R1>.R16.(15.&40.R3>.))P,(25.(19.O4.)R17.)P,(25.R18.(28.(28.(15.&40.R40.)+?0.)(4<.O4.)))P,(25.(15.&40.R41.)(21.O5.O4.O3.R45.))P,(;.$9.(4;.(15.&40.R42.)+10.)=)P,(35.(25.(1>.R21.+8.)R1;.)(25.(15.&40.R43.)R21.))P,(35.(25.(1>.R1?.(3<.(3=.(2.&8.)R1>.)))R1<.)(25.(15.&40.R44.)R1?.))P,(4=.(44.O4.)(45.$7.R48.(46.R47.))R1=.(21.O5.O4.O3.R49.)R23.+8.)P,(4>.(44.O4.)(45.$7.R49.(46.R48.))R1>.R21.(3<.(3=.(2.&8.)R20.)))P,(;.(2.&40.)R45.(?.&40.(4?.O4.)))P,(13.O5.R28.)P,(50.O5.(51.O4.)(24.O5.O4.O3.R4=.)R29.R27.+8.)P,(50.O5.(51.O4.)(24.O5.O4.O3.R4>.)R2:.(1?.R23.)+10.)P,(50.O5.(51.O4.)(24.O5.O4.O3.R4?.)R2;.R26.(3<.(3=.(2.&8.)R25.)))P,(50.O5.(51.O4.)(24.O5.O4.O3.R50.)R2<.(28.(15.&40.R4<.)+28.)+8.)P,(25.(1>.(26.O5.O4.O3.R51.)(27.(28.R29.R2:.)))$52.)P,(53.O4.(1?.R27.)+10.R25.)P,(25.(1>.(29.O5.O4.O3.R53.)(2:.R26.))$54.)P,(;.(2.&40.)R48.(?.&40.R2>.))P,(;.(2.&40.)R48.(?.&40.R2=.))P,(;.(2.&40.)R48.(?.&40.(1?.R2;.)))(55.O5.(56.O5.O4.O3.R57.R56.R55.R54.R53.R52.R51.R4=.R4<.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R35.R34.R31.R30.R2?.R2<.R2;.R2:.R33.R32.)(<.(=.(>.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.)R35.(?.&40.O2.)R34.(11.(2.&40.))R33.(12.O5.))R32.))")
(* [comment removed for export] *).

(* [comment removed for export] *)


From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x99f80]).
Local Ltac zchk_new ::= constr:([0x99f38; 0x99f3c; 0x99f40; 0x99f44; 0x99f48]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis HRB : mpi_read_binary_stmtA asegs R HIA A_MPI_READ_BINARY.
  Hypothesis NEED0 : 0 <= arl_need_rt R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32)
            (PP P END BUF lo : Z) (bs : list byte) (dX : mpd).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis B47 : BUF + Z.of_nat (length bs) + 8 <= 2^47.
  Hypothesis HNS : md_own dX <> LStatic.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis DX1 : PP + 8 <= md_addr dX \/ md_addr dX + 16 <= PP.
  Hypothesis DX2 : md_own dX = LHeap -> PP + 8 <= md_p dX \/ md_p dX + 4 * md_n dX <= PP.
  Hypothesis DX3 : BUF + Z.of_nat (length bs) <= md_addr dX \/ md_addr dX + 16 <= BUF.
  Hypothesis DX4 : md_own dX = LHeap -> BUF + Z.of_nat (length bs) <= md_p dX \/ md_p dX + 4 * md_n dX <= BUF.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SPL : lo <= bv_unsigned sp - 240 - arl_need_rt R.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis DSX : md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX.
  Hypothesis XB : 0 < md_addr dX /\ md_addr dX + 16 <= 2^64.
  Hypothesis CWPP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CRBUF : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis HWR : mpd_writable L (LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis TOPHI : bv_unsigned sp <= hstkhi asegs R HIA h.    (* [comment removed for export] *)
  Variable d : Z.
  Hypothesis XUW : uw_obj R (md_addr dX) 16 d.                  (* [comment removed for export] *)

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPHI; lia]).

  Notation SHPP := (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)).
  Notation FRAME := [C8 s2; C8 s1; C8 s0; C8 ra].
  Notation WH := [(lo, bv_unsigned sp); (PP, PP + 8)].

  Definition RET1Q (m0 : mem) (ms : machine_state) : Prop :=
    exists (x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word) (m' : mem) (r p : Z),
      ms = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ rw_cells asegs m' PP [C8 (Z_to_bv 64 p)] /\ -127 < r < 0 /\ P <= p <= END
      /\ stk asegs m' lo (bv_unsigned sp) /\ mem_inv asegs m' /\ munch WH m0 m' /\ wmono asegs m0 m'.

  Definition CALL1Q (m0 : mem) (ms : machine_state) : Prop :=
    exists (x5 x6 x7 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word) (m' : mem) (p1 len : Z) (junk : list byte),
      ms = MS (mkR (Z_to_bv 64 0x99f24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7
                   (Z_to_bv 64 PP) (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 p1) (Z_to_bv 64 len)
                   xa3 xa4 xa5 xa6 xa7 SHPP s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x9d308) fc None m' (seg_rom asegs)
      /\ rw_cells asegs m' PP [C8 (Z_to_bv 64 p1)]
      /\ rw_cells asegs m' (bv_unsigned sp + -48) (CB 8 junk :: C8 (Z_to_bv 64 len) :: FRAME)
      /\ P + 2 <= p1 /\ 0 <= len /\ p1 + len <= END
      /\ bytes_at asegs m' BUF bs /\ stk asegs m' lo (bv_unsigned sp + -48) /\ mem_inv asegs m'
      /\ aobj asegs AL CS m' PP 8 /\ aobj asegs AL CS m' (md_addr dX) 16 /\ aobj asegs AL CS m' BUF (Z.of_nat (length bs))
      /\ munch WH m0 m' /\ wmono asegs m0 m'.

  #[local] Ltac lx_pins_hook ::= try lx_pin1 XUW; try lx_pin1 d; try lx_pin1 TPV; try lx_pin1 HWR; try lx_pin1 CRBUF; try lx_pin1 CWPP; try lx_pin1 XB; try lx_pin1 DSX; try lx_pin1 TOP; try lx_pin1 DX4; try lx_pin1 DX3; try lx_pin1 DX2; try lx_pin1 DX1; try lx_pin1 HNS; try lx_pin1 HRB.
  Lemma run1_walk : forall (m : mem) (a3 a4 a5 a6 a7 : word),
    rw_cells asegs m PP [C8 (Z_to_bv 64 P)] -> bytes_at asegs m BUF bs ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m -> abase asegs AL m ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m (md_addr dX) 16 -> aobj asegs AL CS m BUF (Z.of_nat (length bs)) ->
    aobj asegs AL CS m (bv_unsigned sp - 40) 8 ->
    evtA asegs AL CS (fun ms => RET1Q m ms \/ CALL1Q m ms)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 (md_addr dX)) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 A_ASN1_GET_MPI) fc None m (seg_rom asegs)).
  Proof.
    intros m a3 a4 a5 a6 a7 HPP HBUF ST MI AB OPP OX OBUF OLEN.
    rt_facts.
    pose proof (munch_refl WH m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB asegs m (bv_unsigned sp + -48) [] 48 junk [] [8; 8; 32]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    cb8_to_c8 FR [CB 8 (firstn 8 junk)].
    lazymatch type of FR with rw_cells _ _ _ (_ :: C8 ?w :: _) => rewrite <- (Z_to_bv_bv_unsigned w) in FR end.
    pose proof (sums_getlen_ok AL IMG) as LXSUMS.
    unfold A_ASN1_GET_MPI.
    lx_pre.
    lx_run_tac (PLANS [0x9d308; 0x99f80] [(0x99ed0, DJoin)] 300%N [SUM_getlenA]).
    lx_tree.
    all: lxu_chk_leaves 0x99f80.
    all: lazymatch goal with
         | |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => apply evtA_done; cbv beta; left; unfold RET1Q; lx_post_body
         | |- context [MS _ _ (Z_to_bv 64 0x9d308) _ _ _ (seg_rom _)] => try lx_rejoin; apply evtA_done; cbv beta; right; unfold CALL1Q; lx_post_body
         | |- _ => idtac
         end.
    all: try lx_app.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308587409.700000CS2dX1A1n2AP1a2Ha2Hr". (* [comment removed for export] *)
  Lemma client_wrange_keep : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi ()) "PSPx,$9.PTOPx,$9.PA,$9.Pn,$9.P,(4=.(44.VR,)(45.$7.VLB,(46.VLF,))R4.R3.R2.R1.)P,P,(;.$40.(41.VdX,)$47.)(35.(25.(1>.R4.R3.)(48.VdX,))(25.(1>.(48.VdX,)(49.+4.(4:.VdX,)))R4.))(4=.(44.VR,)(45.$7.(18.VLB,VdX,)(46.VLF,))R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros SPx TOPx A n CW AP a Ha. destruct (CW a Ha) as [Hs|[Hd|(b & Hb & Hr)]]; [left; exact Hs| right; left; exact Hd| right; right].
    exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
    apply In_mpd_keep_intro; [exact Hb|]. unfold mpd_blk. destruct (md_own dX) eqn:EO; [intros []| | intros []].
    intros [E|[]]. subst b. cbn in Hr. specialize (AP eq_refl). clear - Hr AP Ha. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Notation W := [(PP, PP + 8); (md_addr dX, md_addr dX + 16)].
  Notation POST := (asn1_get_mpi_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP P END dX lo d).

  Hypothesis XLB : md_own dX = LHeap -> md_p dX + 4 * md_n dX <= alloc_ceiling /\ 0 < md_p dX.

  Lemma run2_walk : forall (m m5 m2 : mem) (mo mo1 mo2 : Model) (h2 : HST asegs R HIA) (LB2 : list blk) (dX2 : mpd)
      (r p1 : Z) (ibs junk : list byte) x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    presW asegs R HIA h (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) W m m5 ->
    P + 2 <= p1 <= END -> Z.of_nat (length ibs) <= END - p1 ->
    rw_cells asegs m5 PP [C8 (Z_to_bv 64 p1)] ->
    rw_cells asegs m5 (bv_unsigned sp + -48) (CB 8 junk :: C8 (Z_to_bv 64 (Z.of_nat (length ibs))) :: FRAME) ->
    aobj asegs AL (hcs asegs R HIA h) m5 PP 8 ->
    mo_frame mo mo1 ->
    mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -48) -> mo_frame mo1 mo2 ->
    presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp + -48) (arl_stklo R) (hstkhi asegs R HIA h)
      [(md_addr dX, md_addr dX + 16)] m5 m2 ->
    htop asegs R HIA h2 = htop asegs R HIA h -> hstkhi asegs R HIA h2 = hstkhi asegs R HIA h ->
    hflag asegs R HIA h2 = hflag asegs R HIA h -> HK asegs R HIA h2 mo2 ->
    (forall x, hcs asegs R HIA h x -> hcs asegs R HIA h2 x) ->
    havol asegs R HIA h2 <= havol asegs R HIA h + MPI_RB_PHI (Z.of_nat (length ibs)) ->
    hfr asegs R HIA h2 <= hfr asegs R HIA h + MPI_RB_FR d ->
    HM asegs R HIA h2 LB2 LF m2 -> mpd_at asegs m2 LB2 dX2 -> mpd_out LB dX LB2 dX2 ->
    (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) ->
    (r = 0 -> md_sg dX2 = 1 /\ md_n dX2 = chars_to_limbs (Z.of_nat (length ibs))) ->
    (forall b : blk, In b (mpd_blk dX2) -> In b (mpd_blk dX) \/ fresh_apart R (mpd_keep LB dX) LF (fst b) (snd b)) ->
    aevtS asegs (POST m mo)
      (mkCfg (MS (mkR (Z_to_bv 64 0x99f24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7
                      (Z_to_bv 64 PP) (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7 SHPP s3
                      s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x99f24) fc None m2 (seg_rom asegs)) mo2).
  Proof.
    intros until x31. intros PW Hp1 KC HPP5 FR5 OPP5 MF1 MI2 ST2 MF2 HP2 HT2 HS2 HF2 HK2 HCS2 HV2 HFR2 HH2 HX2 HOUT Hr Hr0 HFRESH.
    rt_facts.
    assert (CWPPk : client_wrange L (mpd_keep LB dX ++ fdata LF) lo (htop asegs R HIA h) PP 8) by (apply client_wrange_keep; [exact CWPP| exact DX2]).
    apply (presA_rw_cells asegs R _ _ _ _ _ _ _ _ _ _ HP2) in FR5;
      [| apply client_range_stack; simpl_sizes; clear; lia | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - DSX XB SPR SPL NEED0; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ _ _ _ _ HP2) in HPP5;
      [| simpl_sizes; eapply client_range_wsep; [exact CWPPk| intros b Hb; exact Hb| clear - DS1; lia]
       | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - DX1; lia ].
    presA_transport HP2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OPP5) as OPP2.
    assert (SCS2 : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS2| exact SCS]).
    pose proof (hcs_ok asegs R HIA h2) as CSOK2.
    assert (CW2 : client_wrange L (LB2 ++ fdata LF) lo (htop asegs R HIA h2) PP 8).
    { rewrite HT2. eapply client_wrange_mono; [exact CWPPk|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff.
      destruct Hb as [Hb|Hb]; [left; eapply mpd_keep_out; [exact HOUT| exact Hb]| right; exact Hb]. }
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
    pose proof (munch_refl [(lo, bv_unsigned sp); (PP, PP + 8)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    assert (P1R : 0 < p1 /\ p1 + Z.of_nat (length ibs) < 2 ^ 63) by (clear - Hp1 KC B1 B2 B3 B4 NZ3; lia).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    release_frame FR5 ST2 (bv_unsigned sp).
    pose proof HOUT as HOUT'. flat constr:(HOUT') 3%nat. flclear HOUT'. intros HA2 HNS2 _.
    assert (HX9 : mpd_at asegs m9 LB2 dX2).
    { eapply mpd_at_munch; [exact HX2| exact HNS2| exact MU2| exact WM2| |]; cbn [disjoint_from].
      - rewrite HA2. clear - DSX DX1 XB. lia.
      - intros HO. split; [| split; [| exact I]].
        + flat constr:(HX2) 2%nat. flclear HX2. intros FLt1 _. flat constr:(FLt1) 6%nat. flclear FLt1. intros _ _ _ HL _ HOWN. rewrite HO in HOWN. flat constr:(HOWN) 3%nat. flclear HOWN. intros Hn1 HIN2 _.
          destruct (HFRESH _ ltac:(unfold mpd_blk; rewrite HO; left; reflexivity)) as [HOLD | HFR].
          * unfold mpd_blk in HOLD. destruct (md_own dX) eqn:EO; [destruct HOLD| | destruct HOLD].
            destruct HOLD as [E|[]]. injection E as E1 E2. pose proof (XLB eq_refl) as XL. clear - E1 E2 XL ALO LOS Hn1. nia.
          * flat constr:(HFR) 3%nat. flclear HFR. intros F0 F1 _. cbn in F0, F1. clear - F0 F1 ALO LOS. lia.
        + destruct (HFRESH _ ltac:(unfold mpd_blk; rewrite HO; left; reflexivity)) as [HOLD | HFR].
          * unfold mpd_blk in HOLD. destruct (md_own dX) eqn:EO; [destruct HOLD| | destruct HOLD].
            destruct HOLD as [E|[]]. injection E as E1 E2. pose proof (DX2 eq_refl) as D. clear - E1 E2 D. nia.
          * eapply (fresh_apart_client R (mpd_keep LB dX) LF lo PP 8 _ _ HFR); [| clear; lia| | clear - ALO LOS; lia].
            -- eapply client_range_inside; [exact CWPPk| intros b Hb; exact Hb| clear; lia| clear; lia].
            -- flat constr:(HX2) 2%nat. flclear HX2. intros FLt2 _. flat constr:(FLt2) 6%nat. flclear FLt2. intros _ _ _ HL' _ HOWN'. rewrite HO in HOWN'. cbn. clear - HOWN'. lia. }
    apply aevtA_done. intros mo9 [HK9 MF9].
    do 14 eexists. exists m9, mo9, h2, LB2, dX2, r, (Z.of_nat (length ibs) + p1).
    split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [exact MF9|].
    split; [eapply presW_presA; eassumption|].
    split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
    split; [exact HCS2|].
    split; [eapply Z.le_trans; [exact HV2|]; apply Zplus_le_compat_l; apply MPI_RB_PHI_mono; clear - KC Hp1; lia|].
    split; [exact HFR2|].
    split; [assumption|]. split; [exact HX9|]. split; [exact HOUT|].
    split; [assumption|]. split; [clear - KC Hp1; lia|].
    split; [unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr; lia|].
    split; [intros R0; split; [clear - Hp1; lia| exact (proj1 (Hr0 R0))]|].
    exact HFRESH.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "03V0@D10651634317.131D10651634317.136D21329468335.116D21329468335.117D23379772182.117D28498761192.182D35881667587.116D35881667587.117D4451634193.182 D46805379688.131D46805379688.136D60098909036.131D60098909036.136D60109196847.182D64317730251.131D64317730251.136K12226132804.116K12226132804.117K30474232799.182K44164039966.116K44164039966.117L10649519402.1  L11326150134.11 L11328261952.6  L11423978205.12 L11803635331.9  L12222146976.2  L12414522636.0  L1429900444.1   L15756354262.4  L16087790284.35 L1685717371.0   L17701970480.1  L19201215546.35 L21765854580.108L21887662552.107L21887662552.129L21887662552.132L21887662552.173L22706556809.4  L23884779055.35 L24109380644.4  L27775132660.108L28757711097.5  L29428324939.5  L30478119227.2  L30504326418.4  L33510041944.108L33510041944.129L33510041944.132L33510041944.173L33808426644.35 L34290115814.112L35655473017.6  L35698097162.180L35992000370.3  L38770711634.35 L39332637397.0  L397962399.4    L39935459111.179L39939634581.134L39941749543.137L40834179097.110L41202929119.128L41202929119.129L41202929119.172L41562522427.133L41562522427.136L41562522430.178L41942189128.1  L4233398364.6   L43059266230.110L44168742175.3  L44252307114.8  L45288738383.35 L4959706922.35  L5261466405.8   L52634178206.6  L53271535775.172L54748384003.108L57392807047.37 L57777220325.11 L57777299826.2  L58805056528.7  L58807005955.9  L59309005011.1  L59309005011.3  L60098763854.3  L61565418556.127L62018535662.1  L62031154087.11 L62031154087.9  L64180445855.128L66083662040.108L66083662040.129L66083662040.132L66083662040.173L68297591230.8  L7465097271.2   L8187829678.35  L8603509526.35  L8840328354.9   L9716869748.107 L9817085104.127 L9962237875.108 L9962237875.129 L9962237875.132 L9962237875.173 P48652884198.172Q10478161754.117Q10649498890.134Q10649498890.135Q10649498890.179Q10649604031.134Q10649715752.133Q10651634312.178Q10651634317.131Q10651634317.136Q13732762037.178Q13735187586.134Q13735272213.133Q1461511394.115 Q14633614404.115Q15641193412.137Q15643272566.134Q15643324129.112Q15647485892.179Q15756125040.131Q15756125040.136Q17013132514.131Q17013132514.136Q17701933584.134Q17701933584.135Q17701933584.179Q18694146040.115Q20414272036.116Q20414272036.117Q20414272036.182Q20568046174.115Q21798041355.115Q22712450012.116Q22712450012.117Q23512175082.114Q24665950363.116Q24665950363.117Q25157988860.115Q25513505925.115Q25513505925.116Q25662358575.115Q26611046992.115Q27668705378.115Q27668705378.116Q28496781288.181Q28498761192.182Q28689862499.131Q28689862499.136Q31135243771.131Q31135243771.136Q31228709292.115Q31394594844.115Q32653238468.137Q32655289974.134Q32655500769.113Q32659530948.179Q32681824661.116Q32681824661.117Q32681824661.182Q33185036414.115Q35014437530.115Q35717497884.115Q35765334355.113Q35765334355.114Q37216054521.179Q3830244501.134 Q3830427394.113 Q3832293927.137 Q3834392103.179 Q3867248849.172 Q39600066516.134Q39600066516.135Q39935459111.179Q39939554818.113Q39939634581.134Q39941749543.137Q40267031658.173Q41934512048.173Q4451634193.182 Q4453582353.181 Q44648628726.134Q44648843873.113Q44650778436.137Q44652874564.179Q45353818935.178Q45355799959.133Q45355851264.134Q4639722776.134 Q4639722776.135 Q46805379688.131Q46805379688.136Q49698585326.114Q49698585326.115Q50846839876.131Q50846839876.136Q51223443012.179Q51233927748.137Q51235796833.113Q51236011254.134Q5294666208.173 Q53969758199.115Q60741299470.131Q60741299470.136Q61556549392.180Q61847600945.134Q61847600945.135Q61847600945.179Q62016014964.173Q6416456232.115 Q64255486968.115Q66522020629.134Q66522067074.113Q66524132775.137Q66534617511.179Q67426116409.116Q68548810730.115Q7190686615.164 Q7193124917.144 Q9839205543.179 Q9841301671.137 Q9843367298.112 Q9843414549.134 00000:00D01;02502l03L04404b05B05L05V05i06<06e07>07W08F09;09n0:^0;T0;X0<00<E0<k0=E0=F0=G0=K0=Y0>00>10>50>m0?70?A0?K0?U0?c0@10@i0A70AA0AP0Ab0Ac0B50B?0BI0BS0Ba0CM0CW0Cl0D:0DE0EG0EH0EV0Fl0H>0IL0IX0Ib0Il0J:0JD0JN0J\0J`0K20L@0LA0LY0MG0M[0N80NL0NZ0Nd0OZ0Od0Ok0P@0P_0Pc0Pl0Q60Qg0Qj0RB0RZ0SK0SU0S_0Si0T70TI0TO0TP0U<0UY0Uc0VT0V^0Vh0W20W@0WU0XE0XL0XS0X^0Xe0Xl0Y70Y>0YE0YP0YW0Y^0Y_0Y`0Yj0Z40Z>0ZL0Z]0Zn0[50[<0[C0[J0[U0[`0\K0]<0]_0]`0]a0^:0^Y0^c0_S0`F0`Q0`m0aO0aP0aQ0b90bd0cA0c^0d40dJ0dK0dL0dX0d\0df0e00e:0eH0eI0eJ0ej0ek0f70f80fB0fL0f^0g40gJ0g`0h:0hX0hY0hZ0i40iJ0i`0j60jF0jQ0jn0kK0kU0k_0ki0l70lB0lI0lP0lQ0lR0lY0l`0m40mH0mR0m\0mj0n40n>0nH0nI0nU0n_0ni0oA0oW0om10G10Q10\10]11311I11_12912a12b13L14614P14f15<15RS2sp2PP2bsS2sp2PP2bsS1R5NEED02ra2sp2PP2lo2bs3PPB3LOS3SPL3SPR2HB5Ha_st5Hl_stS1R5NEED02sp2s02PP2lo2bs3PPB3LOS3SPL3SPR2HB5Ha_st5Hl_st2s1S1R5NEED02sp2s22PP2lo2bs3PPB3LOS3SPL3SPR2HB5Ha_st5Hl_stS2sp2PP2bs2p13ibs2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2PP2bs3TOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s02PP2bs3TOP2HB5Ha_st5Hl_st2s12s2S2sp2PP2bs2p13ibs2HB5Ha_st5Hl_stS2sp2PP2bsS2sp2PP2bsS1R2sp2PP2lo2bs3LOSS1R2sp2PP2lo2bs3LOSS1R2sp2PP2lo2bs3LOS2p13ibs2HB5Ha_st5Hl_stS1R3HIA1h2sp2PP2lo2bs3TOPS1R3HIA1h2sp2PP2lo2bs3TOPS1R5NEED02ra2sp2PP2lo2bs3SPL3DS12HB5Ha_st5Hl_stS1R5NEED02sp2s02PP2lo2bs3SPL3DS12HB5Ha_st5Hl_st2s12s2S1R5NEED02sp2PP2lo2bs3SPL3DS12p13ibs2HB5Ha_st5Hl_stS1R5NEED02ra2sp3BUF2lo2bs3SPL3DS32HB5Ha_st5Hl_stS1R5NEED02sp2s03BUF2lo2bs3SPL3DS32HB5Ha_st5Hl_st2s12s2S2PPS1P3END3BUF2bs2B12p13Hp1S1P3END3BUF2B12p13Hp1S1P3END3BUF2bs2B12B32p12Lw3Hp12KC1a2HaS1R5NEED02sp2lo2dX3SPL3DSXFSS2spS1R2lo3LOS3ALOS1R3HIA1h2sp2bs3TOP3ibsSS2PPS2sp1P3END3BUF2bs2dX2B12B33DX33SPR2p12Lw3Hp12KC3ibs4LENIS2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS2PP2dX3x212HxS2sp1P3END3BUF2lo2bs2B12B33DS33SPR2p12Lw3Hp12KC3ibs4LENIS1P3END2p13Hp1S2sp2PP2bsS1R3HIA1h1d3FR0S1R2lo3LOS3ALO3ACPFS2m23LB23dX25HOWN'S2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS2sp3END3BUF2bs2B33B473SPR2p12Lw2KC3ibs4LENIS2sp2PP2bsS1R3HIA1h2sp2lo5TOPHIS2sp2PP2bs3ibsS2PP2dX3DX1S1R5NEED02sp1P3END3BUF2lo2bs2B13NZ33LOS3SPL3ALO3ACP3SPR2p13Hp13ibsSS2sp2PP2lo3DS1S1R5NEED02sp2PP1P3END3BUF2lo2bs2dX2B12B32D23DX13DX33PPB3SPL3DS13DS33DSX3SPR2p13ibs3Hp1S1R5NEED02sp2PP1P3END3BUF2lo2bs2dX2B12B32D23DX13DX33PPB3SPL3DS13DS33DSX3SPR2p13Hp1S1R5NEED02sp2PP1P3END3BUF2lo2bs2dX2B12B22B32D23DX13DX33PPB3SPL3DS13DS33DSX3SPRS1R2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS2spS1R3HIA1h1P3END2B2S1R5NEED02sp2PP1P3END3BUF2lo2bs2dX2B12B22B32D23DX13DX33PPB3SPL3DS13DS33DSX3SPRFS1R2sp2lo3LOS3ALO3dX22F1S1R5NEED02sp2lo2bs3LOS3SPL3SPA3ALO3ACP3SPR3ibsS1R2sp2lo2bs3SPL3ibsS1P3END2p13ibs2Lw3Hp12KC4LENIS1P3END2p12Lw3Hp12KCS2sp2PP2bs3ibsS2sp2PP2bsS2sp1P3END3BUF2bs2dX2B12B33SPR2p12Lw3Hp12KC3ibs4LENI1HS2bs2Lw2LRS2Lw2LRS2sp2PP2lo2dX3DX13DSXS1R2sp2PP2lo2dX3DX23LOS3XLB3ALOS2R0S1r2Hr2R0S1R2lo3LOSS2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2p13Hp1S1RS3END3BUF2bs2B32p12Lw2KCS3END3BUF2bs2B32p12Lw2KCS2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2p13Hp1S2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS1P3END2p13ibs3Hp1S1r2HrFS2sp3END3BUF2bs2B33B473SPR2p12Lw2KC3ibs4LENIS1P3END2p13ibs2Lw3Hp12KC4LENIS2sp2PP2bsS2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2p13Hp1S2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS2sp2PP2lo2bs3DS13ibsS1R5NEED02sp2s22lo2bs3LOS3SPL3ALO2HB5Ha_st5Hl_stS2PP2bsS2PP2bsS2PP2bs3ibsS2PP2bsS2PP2bsS2PP2bs3ibsS2PP2bsS2PP2bsS2PP2bs3ibsS2PP2bsS2PP2bsFFS2sp2lo2bsS2sp2lo2bsS2sp2lo2bsS2sp2lo2bs3ibsS1R2lo2bs3LOS3ALOS1R2lo2bs3LOS3ALOS2PP2bsS2PP2bsS2PP2bsS2PP2bsS2PP2bs3ibsS1R2bs4IMG'S1R5NEED02ra2sp2PP2lo2bs3SPL2HB5Ha_st5Hl_stS1R5NEED02sp2s02PP2lo2bs3SPL2HB5Ha_st5Hl_st2s12s2S2sp2PP2lo2bs2p13ibs2HB5Ha_st5Hl_stFFS2ra2sp2bs2HB5Ha_st5Hl_stS2sp2s02bs2HB5Ha_st5Hl_st2s12s2S2sp2bs2HBS1R5NEED02ra2sp2lo2bs3LOS3SPL3ALO2HB5Ha_st5Hl_stS1R5NEED02sp2s02lo2bs3LOS3SPL3ALO2HB5Ha_st5Hl_st2s1S1R2bs4IMG'S2ra2sp2lo2bs2HB5Ha_st5Hl_stS2sp2s02lo2bs2HB5Ha_st5Hl_st2s12s2FFS1R5NEED02ra2sp2lo2bs3SPL2HB5Ha_st5Hl_stS1R5NEED02sp2s02lo2bs3SPL2HB5Ha_st5Hl_st2s1S2PP2bs2p13ibs2HB5Ha_st5Hl_stS2PP2bs2p13ibs2HB5Ha_st5Hl_stS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLFFS1R2bs5ALWF'S2bsS2sp2lo2bsS2sp2lo2bsS2sp2lo2bsS2sp2lo2bs3ibsFFS2PP2bs2dX2p13ibs2HB5Ha_st5Hl_stFS1R2bs5ALWF'FS2sp2bs2HBS2sp2bs2HBS2PP2bs3PPB3ibs2HBS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPL3ibsS1R5NEED02sp2lo2bs3LOS3SPL3ibsFFS1R5NEED02sp2lo2bs3SPL3ibsS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R3HIA1h2bs3ibsS2sp2bs3ibsS2PP2bs2p13ibs2HB5Ha_st5Hl_stS2PP2bs2p13ibs2HB5Ha_st5Hl_stS2sp2lo2bsS2sp2lo2bsS2sp2lo2bsS2sp2lo2bs3ibsS2PP2bs3ibsS2PP2bsS2PP2bsFFS2PP2bsS2PP2bsS2sp2bs3SPR2HB5Ha_stS2sp2bs3SPR2HB5Ha_stS2sp2lo2bsS2sp2lo2bsS2sp2lo2bs3ibsS2sp2lo2bsS2sp2lo2bsS2sp2lo2bsFS1R2bs5ALWF'S2PP2bs2dXS2PP2bs2dXS2PP2bs3PPB3ibs2HB5Ha_stS2sp2PP2bs3PPB3AL13SPRS2sp2PP2bs3PPB3AL13SPRS2sp2PP2bs3PPB3AL13SPR3ibsS1R2bs3ibsS1R2bs4IMG'FS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPL3ibsS1R5NEED02sp2s22lo2bs3SPL2HB5Ha_st5Hl_stFS1R5NEED02sp2lo2bs3LOS3SPL3ALO3ACP3SPR3ibsS1R5NEED02sp2lo2bs3LOS3SPL3ALO3ACP3SPR3ibsS1R5NEED02sp2lo2bs3SPL3ibsS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPL". (* [comment removed for export] *)
  Lemma main_walk : forall (m : mem) (mo : Model) (a3 a4 a5 a6 a7 : word),
    HM asegs R HIA h LB LF m -> HK asegs R HIA h mo ->
    rw_cells asegs m PP [C8 (Z_to_bv 64 P)] -> bytes_at asegs m BUF bs -> mpd_at asegs m LB dX ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m (md_addr dX) 16 -> aobj asegs AL CS m BUF (Z.of_nat (length bs)) ->
    aobj asegs AL CS m (bv_unsigned sp - 40) 8 ->
    havol asegs R HIA h + MPI_RB_PHI (END - P) <= AVOL_MAX ->
    hfr asegs R HIA h + MPI_RB_FR d <= FR_MAX ->
    aevtS asegs (POST m mo)
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 (md_addr dX)) a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 A_ASN1_GET_MPI) fc None m (seg_rom asegs)) mo).
  Proof.
    intros m mo a3 a4 a5 a6 a7 HH HKmo HPP HBUF HX ST MI OPP OX OBUF OLEN BUD BUDF.
    pose proof (MPI_RB_FR_nonneg d (uw_obj_nonneg _ _ _ _ XUW)) as FR0.
    rt_facts.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (presW_sub_blocks asegs R HIA h LB (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) W m m
                  (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) W HH ltac:(clear; lia)) (In_mpd_keep LB dX)) as PW.
    pose proof (wlow_sub_blocks R LB (mpd_keep LB dX) LF (hm_wlow asegs R HIA h LB LF m HH) (In_mpd_keep LB dX)) as WL.
    eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
      [ eapply run1_walk; eassumption | intros y Hy; exact Hy | ].
    intros ms' [HF | HC].
    - destruct HF as (x5 & x6 & x7 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m5 & r & p & -> & HPP5 & Hr & Hp
                      & ST5 & MI5 & MU5 & WM5).
      assert (HX5 : mpd_at asegs m5 LB dX).
      { eapply mpd_at_munch; [exact HX| exact HNS| exact MU5| exact WM5| |]; cbn [disjoint_from].
        - clear - DSX DX1 XB. lia.
        - intros HO. specialize (DX2 HO). specialize (XLB HO). clear - DX2 XLB ALO LOS. lia. }
      transport_after_callA asegs m m5 MU5.
      apply aevtA_done. intros mo9 [HK9 MF9].
      do 14 eexists. exists m5, mo9, h, LB, dX, r, p.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      split; [eapply presW_presA; eassumption|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HK9|].
      split; [intros y Hy; exact Hy|].
      split; [unfold MPI_RB_PHI, AVOL_CALL; clear - B2; lia|].
      split; [clear - FR0; lia|].
      split; [assumption|]. split; [exact HX5|]. split; [apply mpd_out_refl; exact HNS|].
      split; [assumption|]. split; [exact Hp|]. split; [clear - Hr; lia|].
      split; [intros R0; exfalso; clear - Hr R0; lia|].
      intros b Hb; left; exact Hb.
    - destruct HC as (x5 & x6 & x7 & xa3 & xa4 & xa5 & xa6 & xa7 & x28 & x29 & x30 & x31 & m5 & p1 & len & junk & -> & HPP5 & FR5
                      & Hp1 & Hlen0 & Hlen & HBUF5 & ST5 & MI5 & OPP5 & OX5 & OBUF5 & MU5 & WM5).
      assert (HX5 : mpd_at asegs m5 LB dX).
      { eapply mpd_at_munch; [exact HX| exact HNS| exact MU5| exact WM5| |]; cbn [disjoint_from].
        - clear - DSX DX1 XB. lia.
        - intros HO. specialize (DX2 HO). specialize (XLB HO). clear - DX2 XLB ALO LOS. lia. }
      transport_after_callA asegs m m5 MU5.
      set (ibs := firstn (Z.to_nat len) (skipn (Z.to_nat (p1 - BUF)) bs)).
      assert (LENI : Z.of_nat (length ibs) = len) by (subst ibs; apply bytes_at_sub_length; clear - Hp1 Hlen0 Hlen B1 B2 B3; lia).
      assert (HIB : bytes_at asegs m5 p1 ibs) by (subst ibs; eapply bytes_at_sub; [exact HBUF5| clear - Hp1 B1; lia| clear - Hlen0; lia| clear - Hp1 Hlen B3; lia]).
      assert (OIB : aobj asegs AL CS m5 p1 (Z.of_nat (length ibs))).
      { rewrite LENI. eapply aobj_sub; [exact OBUF5| clear - Hp1 B1; lia| clear - Hp1 Hlen B3; lia]. }
      assert (HWR' : mpd_writable L (LB ++ fdata LF) (bv_unsigned sp + -48) (htop asegs R HIA h) dX)
        by (eapply mpd_writable_sp_mono; [exact HWR| clear; lia]).
      assert (CRI : client_range L (LB ++ fdata LF) lo p1 (Z.of_nat (length ibs))) by (rewrite LENI; intros a Ha; apply CRBUF; clear - Ha Hp1 Hlen B1 B3; lia).
      assert (BUDI : havol asegs R HIA h + MPI_RB_PHI (Z.of_nat (length ibs)) <= AVOL_MAX).
      { rewrite LENI. eapply Z.le_trans; [| exact BUD]. apply Zplus_le_compat_l. apply MPI_RB_PHI_mono. clear - Hlen0 Hlen Hp1; lia. }
      clearbody ibs. subst len. clear HBUF5 OBUF5.
      pose proof HRB as SG. unfold mpi_read_binary_stmtA, A_MPI_READ_BINARY in SG.
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply SG with (h := h) (LB := LB) (LF := LF) (dX := dX) (B := p1) (ibs := ibs) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by qlia; try eassumption; try reflexivity.
        all: clear - Hp1 Hlen0 Hlen B1 B2 B3 B4 B47 NZ3 TOP SPL NEED0 SPA SPR LOS ALO ACP DS3 DX3 DX4 BUDF;
             first [lia | intros HO; pose proof (DX4 HO); lia | Z.div_mod_to_equations; lia | match goal with |- ?g => idtac "RB-PRE-LEFT:" g end]. }
      clear SG.
      intros ms' mo' (mo1 & [HK1 MF1] & PO).
      destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
      injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by qlia.
      flat constr:(PO) 17%nat. flclear PO. intros MI2 ST2 MF2 HP2 HT2 HS2 HF2 HK2 HCS2 HV2 HFR2 HH2 HX2 HOUT Hr Hr0 HFRESH.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      eapply (run2_walk m m5); try eassumption; clear - Hp1 Hlen0 Hlen; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L31036732193.95L32795199445.97L34628186967.7 L34632568438.9 L41353889562.99L42760023526.96L59315317366.12L59315317366.7 L59964710235.93L63860231421.95L68428645371.8 L68544371040.6 L68548764737.4 00000[01401M01g02d03503^04204I04Z04l05;05IS1R3HIA1h2sp2PP2bs3NZ13TOP3PPB3ALO3ACP4HTOPS1R2sp2PP2bs2dX3PPB2H02HCS1R2dX2lo3LOS3ALO3DHI3D2'S1R2dX2lo3LOS3ALO1B1j2Hr1HS1R5NEED02sp2PP2bs2lo3NZ13LOS3SLO3PPB3ALO3ACP2Bx2jx2fb3Hr22HCS2sp2PP2bs2dX3PPBS1R3HIA5NEED01h2sp2dX2lo3LOS3SLO3ALO2A01SS1R3HIA1h2sp2dX2Hs1SS2sp2PP2bs2dX3PPB3HP01BS2sp2PP2bs2dX3PPBS2FB1n2Bx2jx2E12E2S1R2dX1B1j2Hr1HS1R2dX3DHI3D2'". (* [comment removed for export] *)
Lemma A_asn1_get_mpi_spec : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi ()) "PR,$63.PHIA,(64.$57.R1.)P,(65.(51.R2.))P,(25.=(4<.R3.))(66.$57.R4.R3.$67.$68.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG NEED0 HRB. unfold A_ASN1_GET_MPI.
  intros until d. intros HH HK HPP HBUF B1 B2 B3 B4 B47 HX HNS HWR D2 DX1 DX2 DX3 DX4 AL1 NZ1 NZ3 ST LOS SLO TOP SPA DS1 DS3
         CWPP CRBUF TPV MI OPP OX OBUF OLEN BUD XUW BUDF -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
  pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
  flat constr:((hm_apart asegs R HIA h LB LF m HH)) 2%nat. intros HBR _. rewrite Forall_forall in HBR.
  pose proof (art_data_lo asegs R HIA) as DHI.
  assert (XB : 0 < md_addr dX /\ md_addr dX + 16 <= 2^64).
  { flat constr:(HX) 2%nat. flclear HX. intros FLt3 _. flat constr:(FLt3) 4%nat. flclear FLt3. intros HR _ HP0 _. pose proof (rw_cells_bound _ _ _ _ HR) as B. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in B. lia. }
  (* [comment removed for export] *)
  assert (HL : forall Bx jx, In (Bx, jx) LB \/ In (Bx, jx) (fdata LF) -> Bx + jx <= @alloc_ceiling (arl_L R)).
  { intros Bx jx [Hx|Hx].
    - destruct (HBR (Bx, jx) ltac:(apply in_app_iff; left; exact Hx)) as (_ & _ & HC & _). exact HC.
    - assert (HXf : exists fb, In fb LF /\ fst fb <= Bx /\ Bx + jx <= fst fb + snd fb).
      { clear - Hx. induction LF as [|[FB n] rr IH]; cbn in Hx; [destruct Hx|].
        destruct Hx as [E|[E|Hx]].
        - injection E as E1 E2. exists (FB, n). split; [left; reflexivity| cbn; lia].
        - injection E as E1 E2. exists (FB, n). split; [left; reflexivity| cbn; lia].
        - flat constr:((IH Hx)) 3%nat. intros fb H1 H2. exists fb. split; [right; exact H1| exact H2]. }
      flat constr:(HXf) 3%nat. flclear HXf. intros fb Hfb Hr2.
      destruct (HBR fb ltac:(apply in_app_iff; right; exact Hfb)) as (_ & _ & HC & _). lia. }
  (* [comment removed for export] *)
  assert (DSX : md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX).
  { flat constr:(HWR) 3%nat. intros CW _ _.
    destruct (Z_le_gt_dec (bv_unsigned sp) (md_addr dX)) as [Hs|Hs]; [right; exact Hs| left].
    assert (A0 : md_addr dX < @alloc_ceiling (arl_L R)).
    { destruct (CW (md_addr dX) ltac:(lia)) as [S|[[[D1 D2'] DNS]|(b & Hb & Hr)]]; [exfalso; clear - S Hs; lia| clear - D2' DHI; lia|].
      destruct b as [B j]. cbn in Hr. apply in_app_iff in Hb. pose proof (HL B j Hb). clear - H Hr. lia. }
    destruct (CW (md_addr dX + 15) ltac:(lia)) as [S|[[[D1 D2'] DNS]|(b & Hb & Hr)]].
    - exfalso. clear - S A0 ALO LOS SLO NEED0. lia.
    - clear - D2' DHI ALO LOS. lia.
    - destruct b as [B j]. cbn in Hr. apply in_app_iff in Hb. pose proof (HL B j Hb). clear - H Hr ALO LOS. lia. }
  assert (XLB : md_own dX = LHeap -> md_p dX + 4 * md_n dX <= @alloc_ceiling (arl_L R) /\ 0 < md_p dX).
  { intros HO. flat constr:(HX) 2%nat. flclear HX. intros FLt4 _. flat constr:(FLt4) 6%nat. flclear FLt4. intros _ _ _ _ _ HOWN. rewrite HO in HOWN. flat constr:(HOWN) 3%nat. flclear HOWN. intros _ HIN _.
    destruct (HBR _ ltac:(apply in_app_iff; left; exact HIN)) as (H0 & _ & HC & _). cbn in H0, HC. lia. }
  eapply main_walk; try eassumption; try lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
