(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX HeapIface Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_mpi_addsub P_mpi_read_binary P_asn1_get_mpi.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg A_alloc_lib A_mpi_read_binary_stmt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_mpi_read_binary_stmt_c24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_asn1_get_mpi.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxATac LxARt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P02a873925e9ace9d 0 5 0 1 29 1 34 1 40 1 41 1P03881b8a7b383eee 0 2 0 1 1 1P0aec0fbcc4723a6e 0 3 0 1 37 1 44 1P0b769c1f87a680d6 0 2 0 1 30 1P0bc2e43d3baba714 0 2 0 1 2 1P0e7092ee1a9b319d 0 2 0 1 2 1P10e38161c3581116 0 4 0 1 29 1 34 1 41 1P15e4544370488ba9 0 2 0 1 1 1P1964722cbab38625 0 4 0 1 31 1 36 1 43 1P1988f1afd9789b3d 0 2 0 1 31 1P1c17594ae087d5f6 2 40 0 6 0 8 1 8 41 8 47 8 52 8 53 8 0 4 0 8 2 8 52 8 53 8P21f2b9dff192b802 0 2 0 1 30 1P236a0ef13a164693 0 2 0 1 31 1P279284114fd4d6fd 0 4 0 1 31 1 36 1 43 1P27a32f0249be1ab0 0 4 0 1 38 1 42 1 45 1P2ca776b7bb72b5e4 0 4 0 1 29 1 34 1 41 1P2e93149910df3ec7 0 3 0 1 35 1 42 1P2ec1b00e9217ba86 0 4 0 1 35 1 39 1 42 1P318c2ca965b591d5 0 2 0 1 31 1P33c264f53eeb0477 0 2 0 1 1 1P348a6b285a737a65 0 2 0 1 31 1P36408e381912e889 0 2 0 1 2 1P399bc17ef34587cb 0 3 0 1 38 1 45 1P3a6a35e0481deaa6 0 3 0 1 35 1 42 1P3a6e012493458a64 0 4 0 1 32 1 37 1 44 1P3b06a82ffe0da40f 0 2 0 1 30 1P3f1fb0ded1f06539 0 3 0 1 37 1 44 1N012be8a9a96617a1N01d020d04d8efc32N04d2b79c710aa513N055992265d483e5aN09dc0e28cff969ceN0a56f04183d9e864N0a93ce4b9315a600N0b75f5e2e9086b7dN0be10a1bb3df5750N0cc871fa5a18affbN0f4e37f16743a03aN10657cc13006f949N1d9acb8f9d25558dN1e3e320af53a448bN1e94b87c3ddad92aN2224eb66c6daec89N2244d095e7f0e8ceN25da8dcdb62e437aN2a34b77022b3f983N2e261f70bfa5cc4eN308b63c184073940N31885415416909d2N3322c46556448182N367b1e2c3ad343b9N387bbb9c6c99020eN3a4b9f46be72b348N3c180fd757207b79N3d1af28ad748f9c0N3d30ca18163d8aceN3d61e3fe07787d2eN3eb677f5c20852ad"%lxh.
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
Ltac2 gd_tbl_A_asn1_get_mpi_c24 () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.LibA.ARt.presA"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.mpd_keep"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.LibA.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.MPI_RB_PHI"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.LibA.ARt.hfr"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.MPI_RB_FR"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.MpiVal.mpd_out"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.LibA.ACnt24.cnt24"; "Stdlib.ZArith.BinInt.Z.div"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt_c24.mpi_read_binary_stmtA_c"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.P.P_mpi_addsub.mpd_writable"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "OSSVerify.KrLib.Lib.HeapIface.client_wrange"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibA.ARt.arl_tp"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.A.A_alloc_lib.uw_obj"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "C24_GET_MPI_c"; "OSSVerify.KrLib.LibA.ACnt24.C24MAX"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "asn1_get_mpi_postA_c"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Walk.hdr_facts"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.le"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "Walk.J1Q"; "Walk.FAILQ"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "asn1_get_mpi_stmtA_c"; "OSSVerify.KrLib.A.A_asn1_get_mpi.A_ASN1_GET_MPI"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.A_MPI_READ_BINARY"].


Notation ASN1_GET_MPI_STACK_A := 224 (only parsing).   (* [comment removed for export] *)

Definition C24_GET_MPI_c : Z := 1.

Definition asn1_get_mpi_postA_c (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP P END : Z) (dX : mpd) (lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi_c24 ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O20.O1?.O1>.)Lh',(5.O20.O1?.O1>.)(1.(6.$7.)LLB',(6.$7.)(1.$8.LdX',$8.(1.$9.Lr,$9.(1.$9.Lp',$9.(:.(;.$0.R16.(<.(=.(>.O1:.O19.O18.O17.R15.R14.R13.O16.O15.(?.&40.R2.)R12.R11.R10.R?.R>.R=.R<.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R;.R:.R9.R8.)O:.(10.O1:.)O9.(11.(2.&40.))R7.(12.O20.))R6.))(:.(13.O20.R7.)(:.(14.O20.R7.O4.(15.&40.O19.))(:.(16.O1.R6.)(:.(17.O20.O1?.(18.O1<.O5.)O1;.(15.&40.O19.)(19.O1?.)(1:.O20.O1?.O1>.O1=.)(1;.(1<.$9.$9.)(1=.$9.$9.O8.(1>.O8.+8.))(1;.(1<.$9.$9.)(1=.$9.$9.(1?.O5.)(1>.(1?.O5.)+10.))(20.(1<.$9.$9.))))O2.R7.)(:.(;.$9.(21.O20.O1?.O1>.R5.)(21.O20.O1?.O1>.O1=.))(:.(;.$9.(1:.O20.O1?.O1>.R5.)(1:.O20.O1?.O1>.O1=.))(:.(;.$9.(22.O20.O1?.O1>.R5.)(22.O20.O1?.O1>.O1=.))(:.(23.O20.O1?.O1>.R5.R6.)(:.Px,$9.P,(24.O20.O1?.O1>.O1=.R1.)(24.O20.O1?.O1>.R7.R2.)(:.(25.(26.O20.O1?.O1>.R5.)(1>.(26.O20.O1?.O1>.O1=.)(27.(28.O6.O7.))))(:.(25.(29.O20.O1?.O1>.R5.)(1>.(29.O20.O1?.O1>.O1=.)(2:.O3.)))(:.(2;.O20.O1?.O1>.R5.R4.O1;.R7.)(:.(2<.O20.R7.R4.R3.)(:.(2=.O1<.O5.R4.R3.)(:.(2>.O20.R7.O8.(1;.$2?.(30.(?.&40.R1.))(20.$2?.)))(:.(:.(25.O7.R1.)(25.R1.O6.))(:.(:.(31.-7?.R2.)(25.R2.=))(:.P,(;.$9.R2.=)(:.(25.(1>.O7.+2.)R2.)(;.$9.(32.R4.)+1.))(:.Pb,$7.P,(33.$7.R1.(34.R4.))(35.(33.$7.R2.(34.O5.))(36.O1?.(18.O1<.O5.)O1;.(37.$9.$9.R2.)(38.$9.$9.R2.)))(25.(39.R4.)(1>.(39.O1<.)(3:.(28.R1.O7.)+1701.))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

Definition asn1_get_mpi_stmtA_c (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY RB : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi_c24 ()) "P,(3;.O5.O4.O3.O1.)Ph,(5.O5.O4.O3.)PLB,(6.$7.)PLF,(6.$7.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PPP,$9.PP,$9.PEND,$9.PBUF,$9.Pbs,(6.(2.&8.))PdX,$8.Plo,$9.Pd,$9.P,(2;.O5.O4.O3.R2>.R2=.R2<.R:.)P,(23.O5.O4.O3.R2?.R:.)P,(2>.O5.R<.R:.(1;.$2?.(30.(?.&40.R9.))(20.$2?.)))P,(3=.O5.R=.R8.R7.)P,(25.R9.R;.)P,(25.R<.R;.)P,(25.R<.(1>.R;.(3>.(3?.(2.&8.)R:.))))P,(31.(1>.R<.(3>.(3?.(2.&8.)R;.)))(40.+2.+3?.))P,(25.(1>.(1>.R=.(3>.(3?.(2.&8.)R<.)))+8.)(40.+2.+2?.))P,(2<.O5.R13.R36.R<.)P,(41.(;.$42.(43.R=.)$44.))P,(45.(46.O4.)(47.$7.R38.(48.R37.))(15.&40.R35.)(21.O5.O4.O3.R39.)R>.)P,(35.(25.(1>.R14.+8.)R11.)(25.(1>.R11.(3>.(3?.(2.&8.)R10.)))R14.))P,(35.(25.(1>.R15.+8.)(1?.R10.))(25.(1>.(1?.R10.)+10.)R15.))P,P,(;.$42.(43.R11.)$49.)(35.(25.(1>.R17.+8.)(4:.R12.))(25.(1>.(4:.R12.)(4;.+4.(4<.R12.)))R17.))P,(35.(25.(1>.R14.(3>.(3?.(2.&8.)R13.)))(1?.R12.))(25.(1>.(1?.R12.)+10.)R14.))P,P,(;.$42.(43.R13.)$49.)(35.(25.(1>.R16.(3>.(3?.(2.&8.)R15.)))(4:.R14.))(25.(1>.(4:.R14.)(4;.+4.(4<.R14.)))R16.))P,(;.$9.(4=.R19.+8.)=)P,(31.=R1:.)P,(31.=R18.)P,(14.O5.R1>.R16.(15.&40.R3>.))P,(25.(19.O4.)R17.)P,(25.R18.(28.(28.(15.&40.R40.)+>0.)(4>.O4.)))P,(25.(15.&40.R41.)(21.O5.O4.O3.R45.))P,(;.$9.(4=.(15.&40.R42.)+10.)=)P,(35.(25.(1>.R21.+8.)R1;.)(25.(15.&40.R43.)R21.))P,(35.(25.(1>.R1?.(3>.(3?.(2.&8.)R1>.)))R1<.)(25.(15.&40.R44.)R1?.))P,(4?.(46.O4.)(47.$7.R48.(48.R47.))R1=.(21.O5.O4.O3.R49.)R23.+8.)P,(50.(46.O4.)(47.$7.R49.(48.R48.))R1>.R21.(3>.(3?.(2.&8.)R20.)))P,(;.(2.&40.)R45.(?.&40.(51.O4.)))P,(13.O5.R28.)P,(52.O5.(53.O4.)(24.O5.O4.O3.R4=.)R29.R27.+8.)P,(52.O5.(53.O4.)(24.O5.O4.O3.R4>.)R2:.(1?.R23.)+10.)P,(52.O5.(53.O4.)(24.O5.O4.O3.R4?.)R2;.R26.(3>.(3?.(2.&8.)R25.)))P,(25.(1>.(26.O5.O4.O3.R50.)(27.(28.R28.R29.)))$54.)P,(55.O4.(1?.R26.)+10.R24.)P,(25.(1>.(29.O5.O4.O3.R52.)(2:.R25.))$56.)P,(25.(1>.(39.R52.)$57.)$58.)P,(;.(2.&40.)R48.(?.&40.R2>.))P,(;.(2.&40.)R48.(?.&40.R2=.))P,(;.(2.&40.)R48.(?.&40.(1?.R2;.)))(59.O5.(5:.O5.O4.O3.R57.R56.R55.R54.R53.R52.R51.R4=.R4<.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R35.R34.R31.R30.R2?.R2<.R2;.R2:.R33.R32.)(<.(=.(>.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.)R35.(?.&40.O2.)R34.(11.(2.&40.))R33.(12.O5.))R32.))")
(* [comment removed for export] *).

(* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis HRB : mpi_read_binary_stmtA_c asegs R HIA A_MPI_READ_BINARY.
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
  Hypothesis SPL : lo <= bv_unsigned sp - 224 - arl_need_rt R.
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
  Hypothesis C24H : cnt24 LB + C24_GET_MPI_c <= C24MAX.     (* [comment removed for export] *)

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

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHPP := (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)).
  Notation FRAME := [C8 s2; C8 s1; C8 s0; C8 ra].
  Notation WH := [(lo, bv_unsigned sp); (PP, PP + 8)].

  (* [comment removed for export] *)
  Definition hdr_facts (mm m' : mem) (p : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi_c24 ()) "(:.(2>.$5;.O2.VPP,(1;.$2?.(30.(?.&40.O1.))(20.$2?.)))(:.(3=.$5;.O2.VBUF,Vbs,)(:.(2>.$5;.O2.(1>.(15.&40.Vsp,)-20.)(1;.$2?.(30.Vs2,)(1;.$2?.(30.Vs1,)(1;.$2?.(30.Vs0,)(1;.$2?.(30.Vra,)(20.$2?.))))))(:.(14.$5;.O2.Vlo,(1>.(15.&40.Vsp,)-20.))(:.(13.$5;.O2.)(:.(52.$5;.(53.VR,)(24.$5;.VR,VHIA,Vh,)O2.VPP,+8.)(:.(52.$5;.(53.VR,)(24.$5;.VR,VHIA,Vh,)O2.(1?.VdX,)+10.)(:.(52.$5;.(53.VR,)(24.$5;.VR,VHIA,Vh,)O2.VBUF,(3>.(3?.(2.&8.)Vbs,)))(:.(5<.(1;.(1<.$9.$9.)(1=.$9.$9.Vlo,(15.&40.Vsp,))(1;.(1<.$9.$9.)(1=.$9.$9.VPP,(1>.VPP,+8.))(20.(1<.$9.$9.))))O3.O2.)(5=.$5;.O3.O2.))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition FAILQ (mm : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi_c24 ()) "Lms',$5>.(1.(2.&40.)Lx5,(2.&40.)(1.(2.&40.)Lx6,(2.&40.)(1.(2.&40.)Lx7,(2.&40.)(1.(2.&40.)Lx8,(2.&40.)(1.(2.&40.)Lx9,(2.&40.)(1.(2.&40.)Lx10,(2.&40.)(1.(2.&40.)Lx11,(2.&40.)(1.(2.&40.)Lx12,(2.&40.)(1.(2.&40.)Lx14,(2.&40.)(1.(2.&40.)Lx15,(2.&40.)(1.(2.&40.)Lx16,(2.&40.)(1.(2.&40.)Lx17,(2.&40.)(1.(2.&40.)Lx28,(2.&40.)(1.(2.&40.)Lx29,(2.&40.)(1.(2.&40.)Lx30,(2.&40.)(1.(2.&40.)Lx31,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$9.Lr,$9.(1.$9.Lp,$9.(:.(;.$5>.R14.(=.(>.Vra,(?.&40.(1>.(15.&40.Vsp,)-20.))Vgp,Vtp,R13.R12.R11.R10.R?.R>.R=.R<.(?.&40.R2.)R;.R:.R9.R8.(?.&40.(1>.(5?.VPP,+3.)(60.(53.VR,))))Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(?.&40.+99938.)Vfc,(11.(2.&40.))R3.(12.$5;.)))(:.(:.(31.-7?.R2.)(31.R2.=))(:.(:.(25.VP,R1.)(25.R1.VEND,))(61.O1.R3.R1.)))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition J1Q (mm : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi_c24 ()) "Lms',$5>.(1.(2.&40.)Lx5,(2.&40.)(1.(2.&40.)Lx6,(2.&40.)(1.(2.&40.)Lx7,(2.&40.)(1.(2.&40.)Lx9,(2.&40.)(1.(2.&40.)Lx14,(2.&40.)(1.(2.&40.)Lx15,(2.&40.)(1.(2.&40.)Lx16,(2.&40.)(1.(2.&40.)Lx17,(2.&40.)(1.(2.&40.)Lx28,(2.&40.)(1.(2.&40.)Lx29,(2.&40.)(1.(2.&40.)Lx30,(2.&40.)(1.(2.&40.)Lx31,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$9.Lp1,$9.(1.(2.&40.)LLw,(2.&40.)(:.(;.$5>.R10.(=.(>.Vra,(?.&40.(1>.(15.&40.Vsp,)-20.))Vgp,Vtp,R?.R>.R=.R1.R<.(?.&40.VPP,)(?.&40.VEND,)(?.&40.(1?.VdX,))(?.&40.-60.)R;.R:.R9.R8.(?.&40.(1>.(5?.VPP,+3.)(60.(53.VR,))))Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(?.&40.+998>8.)Vfc,(11.(2.&40.))R3.(12.$5;.)))(:.(:.(25.(1>.VP,+2.)R2.)(25.R2.VEND,))(61.O1.R3.R2.))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 C24H; try lx_pin1 XUW; try lx_pin1 d; try lx_pin1 TPV; try lx_pin1 HWR; try lx_pin1 CRBUF; try lx_pin1 CWPP; try lx_pin1 XB; try lx_pin1 DSX; try lx_pin1 DS3; try lx_pin1 TOP; try lx_pin1 SPA; try lx_pin1 NZ1; try lx_pin1 DX4; try lx_pin1 DX3; try lx_pin1 DX2; try lx_pin1 DX1; try lx_pin1 HNS; try lx_pin1 B4; try lx_pin1 B2; try lx_pin1 bs; try lx_pin1 lo; try lx_pin1 BUF; try lx_pin1 t6; try lx_pin1 t5; try lx_pin1 t4; try lx_pin1 t3; try lx_pin1 s2; try lx_pin1 s0; try lx_pin1 t2; try lx_pin1 t1; try lx_pin1 t0; try lx_pin1 sp; try lx_pin1 LF; try lx_pin1 LB; try lx_pin1 h; try lx_pin1 HRB; try lx_pin1 HIA; try lx_pin1 R.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L11091995449.93L17807771876.74L21187612063.74L26703942547.74L29303082658.93L29428324939.5 L35655473017.6 L53005458999.74L58256283600.95L60098763854.3 L62336676465.7400000X01D01l02[03C03U03j04R06H06R07:S2PP3END2bs1j3cur2Hj5Hstop4lxHn5lxHn02H9S2PP3END2bs3PPB1j3cur2Hj5Hstop4lxHn5lxHn02H9S2PP3END2bs1j3cur2Hj5Hstop4lxHn5lxHn02H9S2PP1P3END2bs1j3cur2Hj4Hcur5Hstop4lxHn5lxHn02H9S2PP3END2bs1j3cur2Hj5Hstop4lxHn5lxHn02H9S1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo5TOPHIS2PP3END2bs1j3cur2Hj5Hstop4lxHn5lxHn02H9S1R3HIA1h2ra2sp2gp2tp2s12s32s42s52s62s72s82s93s103s111F2fc2PP3END2bs2dX3cur2Lw2x52x62x73x283x293x303x312m02mm2Hj5HstopS1R2lo3LOSS2PP3END2bs1j3cur2Hj5Hstop4lxHn5lxHn02H9". (* [comment removed for export] *)
  #[using="TOPHI DS1 SPL LOS NZ3 AL1 PPB D2 B47 B3 B1 NEED0 IMG"]
  Lemma loop1_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi_c24 ()) "Pj,$62.Pcur,$9.PLw,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))P,(:.(63.#1.R<.)(63.R<.#4.))P,(25.(1>.VP,+2.)R<.)P,(25.(1>.R=.(3>.R>.))VEND,)P,(61.R5.R4.R>.)(64.$5;.(53.VR,)(24.$5;.VR,VHIA,Vh,)(65.R6.)(=.(>.Vra,(?.&40.(1>.(15.&40.Vsp,)-20.))Vgp,Vtp,R=.R<.R;.R>.Vs1,(?.&40.VPP,)(?.&40.VEND,)(?.&40.(1?.VdX,))(?.&40.-60.)(?.&40.(1>.R?.+1.))(?.&40.R?.)(?.&40.(60.(53.VR,)))(?.&40.(3>.R10.))(?.&40.(1>.(5?.VPP,+3.)(60.(53.VR,))))Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(?.&40.+9998<.)Vfc,(11.(2.&40.))R5.(12.$5;.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  induction j as [|j IH]; intros cur Lw x5 x6 x7 x28 x29 x30 x31 m0 mm Hj Hcur Hstop
    (HPP & HBUF & FR & ST & MI & OPP & OX & OBUF & MU & WM); [lia|].
  rt_facts.
  try (pose proof (munch_refl W mm) as MU). try (pose proof (wmono_refl asegs mm) as WM).   (* [comment removed for export] *)
  lx_pre. lxr_path. lxr_abase. lxr_pose.   (* [comment removed for export] *)
  lx_pre. lx_run_tac (PLAN [0x0998e8; 0x09998c; 0x09d20c] [(0x9988c, DJoin); (0x998c0, DJoin); (0x998e0, DJoin); (0x99998, DJoin)] 143%N).
  lx_tree.
  all: lxr_leaf; lx_carry.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => first [ match goal with H : munch _ _ mx |- _ => rename H into MU end | idtac ]; first [ match goal with H : wmono _ _ mx |- _ => rename H into WM end | idtac ] end).
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0x9998c) _ _ _ (seg_rom _)] => lx_apply IH | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0x998e8) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: match goal with |- ?g => idtac "lxw loop1_walk: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac hdr_fail mcur r p :=
    apply evtA_done; left; unfold FAILQ; do 16 eexists; exists mcur, r, p;
    split; [reflexivity|]; split; [| split; [| unfold hdr_facts; repeat (lazymatch goal with |- _ /\ _ => split end); assumption]].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02H0@K30474232799.106K30474232799.114K30474232799.118K44164039966.106K44164039966.114K44164039966.118L11668954808.94 L11668962290.91 L11670651223.90 L12550742471.103L12551142084.101L12551142087.106L16070426553.111L16070426553.114L16108054177.108L16110144372.98 L16605321107.91 L1804587928.93  L21991189007.93 L21993419083.95 L24150417681.101L27079381994.114L29428324939.5  L30478119227.2  L30803094856.105L35347804779.104L35655473017.6  L39929847471.114L41202929119.105L41202929119.109L41202929119.91 L41202929119.97 L42815144887.4  L42815156885.4  L44168742175.3  L46860861783.90 L47940674131.3  L49921901157.4  L50091493243.99 L50091499700.102L50091499700.107L50091501498.96 L508980326.103  L52753478851.4  L53271535775.105L53271535775.109L53271535775.97 L53792479276.4  L5548785062.2   L60098763854.3  L63152446533.108L64438461917.10 L6958177821.11  L9814875959.90  L9817098198.96  Q10649498890.103Q10649498890.111Q10649498890.115Q10649498890.97 Q10649605966.102Q10651570095.96 Q10651703251.110Q10651703773.114Q10732447889.102Q13074342371.110Q13074443200.110Q13074443201.113Q13076419398.105Q13076443006.108Q13076443006.113Q13732697234.96 Q13733085920.114Q13733088494.110Q13735185523.102Q15063504633.108Q15063504633.113Q15930096381.100Q15930096381.108Q15930096381.113Q17701933584.103Q17701933584.111Q17701933584.115Q17701933584.97 Q1954359180.100 Q20414272036.106Q20414272036.114Q20414272036.118Q21027042243.108Q21027042243.113Q21028779900.113Q21028779901.110Q2215932912.97  Q23733024212.102Q23735521236.97 Q23735546217.100Q24782519217.112Q28496781288.105Q28496781288.113Q28496781288.117Q30485177150.113Q30485177151.110Q31407341477.110Q31409376512.105Q32871135979.108Q32871135979.113Q37216054521.103Q37216054521.111Q37216054521.115Q37343932385.102Q37345667932.100Q39600066516.103Q39600066516.111Q39600066516.115Q39600066516.97 Q42812894818.114Q4347736924.114 Q43608320047.105Q43608320682.97 Q43610462858.110Q4453582353.105 Q4453582353.113 Q4453582353.117 Q45353748076.110Q45353748578.114Q45353885200.96 Q45355845361.102Q4639722776.103 Q4639722776.111 Q4639722776.115 Q4639722776.97  Q47832358507.111Q49921682489.111Q49923780528.114Q5257172243.108 Q5257172243.113 Q52753442471.102Q56288992540.108Q56288992540.113Q56290924962.110Q56290924963.113Q57351519894.100Q60929927345.102Q61556549392.104Q61556549392.112Q61556549392.116Q61778999419.100Q61781458118.102Q61847600945.103Q61847600945.111Q61847600945.115Q61847600945.97 Q62641111670.10000000^01L02:02Y03803W04D05105^06106D06W06g07707M08:08g09I09\09o0:Q0;i0<;0<<0<=0<G0<\0<h0=20=<0=F0=P0=Q0=R0=S0=a0=d0=n0>[0?H0@50@b0A20A<0AF0AP0AZ0Ad0Ak0B50BE0Be0CF0D30D`0Dg0Dn0E50E<0EC0EJ0EQ0EX0El0F90FF0FS0F`0Fm0G:0GA0GH0GO0GV0Gj0H>0HB0HF0HJ0HQ0HX0H_0Hf0I70IU0J30JQ0JR0JS0JT0JU0Ji0K60KC0KP0K]0L50LM0Le0M90MM0Ma0N50NF0NW0Ne0O30OA0OB0OC0OD0OE0OF0OG0OK0O_0Oc0Og0Ok0PC0P[0Q30Q:0QA0QH0QO0QP0QQ0QR0QS0QW0Qd0R10R70R=0RJ0RK0RL0RM0RN0Rb0Rf0S:0SN0Sb0Sc0Sd0T:0TP0Tf0U<0UBS1R5NEED02sp2PP1P2lo2bs3SPL3DS12HB5Ha_st5Hl_stS1R5NEED02sp2PP1P2lo2bs3SPL3DS12HB5Ha_st5Hl_stS1R5NEED02sp2PP1P2lo2bs3SPL3DS12HB5Ha_st5Hl_stS2PP1P3BUF2bs2D22HB5Ha_st5Hl_stS2PP1P3BUF2bs2D22HB5Ha_st5Hl_stS2PP1P3BUF2bs2D22HB5Ha_st5Hl_stS2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2K0S2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2K0S2sp2PP1P3END3BUF2bs2B12B22B33B473PPB3NZ33SPRS2sp2PP1P3BUF2bs2B1S2sp2PP1P3BUF2bs2B1S2sp2PP1P3BUF2bs2B1S2sp2PP1P3BUF2bsS2sp2PP1P3BUF2bsS2sp2PP1P3END2bs2K02K3S2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2K0S2sp2PP1P3END3BUF2bs2B12B22B33B473PPB3NZ33SPRS2sp2PP1P3END3BUF2bs2B33PPB3SPR2K0S2sp2PP1P3BUF2bs2B1S2sp2PP1P3BUF2bs2B1S2sp2PP1P3END3BUF2bs2B33PPB3SPR2K1S1R5NEED02sp2PP1P3END3BUF2lo2bs2dX2B12B32D23DX13DX33PPB3SPL3DS13DS33DSX3SPR2K12nn2HN3KgeS1R2lo3LOS3ALO3ACPFFS2sp2PP2bsS1R3HIA1h2sp2lo5TOPHIS2sp2PP1P2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bsSSFS2sp2PP2bs3PPBS1PS1P3END2E2S2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2K1S2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2K1S2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2K1S2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2K0S2sp2PP1P3BUF2bsS1P3END2B2S2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2b12nn2KnS2nn2HNS1R2lo3LOSS2sp2PP2bs2nn2NRS1P3END2bs2B21K3BUF2B12B32B43NZ3S1P3END2bs2K02K23BUF2B12B32B43NZ3S2sp2PP1P3END3BUF2bs2B12B22B33B473PPB3NZ33SPRS2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2K0S2PP2bsS2PP2bsS2PP2bsS2PP2bsS2PP2bsS2PP2bsS2PP2bsS2PP2bsS1P3END3BUF2bs2B32K0S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S2PP2bsS2PP2bsS2PP2bsS2PP2bsS1P3END3BUF2bs2B32K1S1P3END3BUF2bs2B32K1S2bsS2bsS2bsS2PP2bsS2PP2bsS2PP2bsS2PP2bsS1P3BUF2bs2B13NZ3S2sp2PP1P2lo2bs2HB5Ha_st5Hl_stS2sp2PP1P2lo2bs2HB5Ha_st5Hl_stS2sp2PP1P2lo2bs2HB5Ha_st5Hl_stFFFFS1P3END3BUF2bs2B32K0S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3BUF2bs2B1S1P3END2bs2K1S2PP1P2bs2HB5Ha_st5Hl_stS2PP1P2bs2HB5Ha_st5Hl_stS2PP1P2bs2HB5Ha_st5Hl_stS1P3END3BUF2bs2B32K1S1P3END3BUF2bs2B32K1S1P3END3BUF2bs2B32K1S1P3END3BUF2bs2B32K1S1P3BUF2bs2B13NZ3S1P3BUF2bs2B13NZ3S2PP2bs3PPB2HBS2PP2bs3PPB2HBS2PP2bs3PPB2HBFFFFFFS2bsS1P3END2bs2nn2HN3KgeS2bsS2bsS2bsS2PP1P2bs2HB5Ha_st5Hl_stS2PP1P2bs2HB5Ha_st5Hl_stS2PP1P2bs2HB5Ha_st5Hl_stS2PP2bsS2PP2bsS2PP2bsS2PP2bsFFFFS2bsS1P3END2bs2K0S1P3END2bs2K0S1P2bsS1P2bsS1P3END2bs2B2FFFFS1P3END3BUF2bs2B32K0S2bsS2PP2bs3PPB2HB5Ha_stS2PP2bs3PPB2HB5Ha_stS2PP2bs3PPB2HB5Ha_stFFS2sp2PP2bs3PPB3AL13SPRS2sp2PP2bs3PPB3AL13SPRS2sp2PP2bs3PPB3AL13SPRS2sp2PP2bs3PPB3AL13SPRS1P2bs". (* [comment removed for export] *)
  Lemma hdr_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi_c24 ()) "Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px17,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))P,(61.R1.R1.VP,)(64.$5;.(53.VR,)(24.$5;.VR,VHIA,Vh,)Lms',$5>.(35.(66.R3.R1.)(65.R3.R1.))(=.(>.Vra,(?.&40.(1>.(15.&40.Vsp,)-20.))Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(?.&40.VPP,)(?.&40.VEND,)(?.&40.(1?.VdX,))R6.R5.R4.(?.&40.(60.(53.VR,)))R3.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(?.&40.+99860.)Vfc,(11.(2.&40.))R2.(12.$5;.)))")
(* [comment removed for export] *).
  Proof.
    intros x13 x14 x15 x17 mm (HPP & HBUF & FR & ST & MI & OPP & OX & OBUF & MU & WM). rt_facts.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K.
    { assert (EP : END = P) by (apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; clear - K B1 B2 B3 B4 NZ3; lia).
      hdr_fail mm (-96) P; clear - B2 EP; lia. }
    clear K1.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk1 OBUF P.
    (* [comment removed for export] *)
    get_byte bs (P - BUF) b0 NB0. read_at HBUF NB0 (P - BUF) RD0.
    zstep. clear RD0. zstep.
    zstep. if_cases Kt; zify_cond Kt.
    { zstep. hdr_fail mm (-98) P; qlia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    zstep. if_cases K2; zify_cond K2.
    { assert (E2 : END = P + 1) by (apply Bool.andb_false_iff in K2; destruct K2 as [K2|K2]; apply Z.ltb_ge in K2; clear - K2 K0 B1 B2 B3 B4 NZ3; lia).
      hdr_fail m1 (-96) (P + 1); clear - B2 E2; lia. }
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk1 OBUF (P + 1).
    (* [comment removed for export] *)
    get_byte bs (P + 1 - BUF) b1 NB1. read_at HBUF NB1 (P + 1 - BUF) RD1.
    zstep. clear RD1. zstep. if_cases Ksg; zify_cond Ksg.
    { (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. if_cases Kn; zify_cond Kn.
      2:{ (* [comment removed for export] *)
        zstep. zstep. hdr_fail m1 (-100) (P + 1); qlia. }
      pose proof (land_127_range (bv_unsigned (sxb b1))) as NR.
      set (nn := Z.land (Z.land (bv_unsigned (sxb b1)) 255) 127) in *.
      assert (HN : 1 <= nn <= 4) by (clear -NR Kn; apply longform_n; [exact NR|]; lia). clearbody nn. clear Kn.
      (* [comment removed for export] *)
      zstep. if_cases Kge; zify_cond Kge.
      { hdr_fail m1 (-96) (P + 1); qlia. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      apply (evtA_mono asegs AL CS (J1Q mm)); [| intros ms' HJ; right; exact HJ].
      replace (Z_to_bv 64 nn) with (Z_to_bv 64 (Z.of_nat (Z.to_nat nn))) by (f_equal; lia).
      replace (Z_to_bv 64 (P + 3)) with (Z_to_bv 64 (P + 2 + 1)) by (f_equal; lia).
      eapply (loop1_walk (Z.to_nat nn) (P + 2)); [clear - HN; lia| clear - B1; lia| qlia|].
      unfold hdr_facts. repeat (lazymatch goal with |- _ /\ _ => split end); assumption. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    shadow_chk1 OBUF (P + 1).
    (* [comment removed for export] *)
    read_at HBUF NB1 (P + 1 - BUF) RD2. zstep. clear RD2.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    apply evtA_done. right. unfold J1Q. do 12 eexists. exists m9, (P + 2). eexists.
    split; [reflexivity|]. split; [qlia|]. unfold hdr_facts. repeat (lazymatch goal with |- _ /\ _ => split end); assumption.
    all: match goal with |- ?g => idtac "HDR-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308587409.700000CS2dX1A1n2AP1a2Ha2Hr". (* [comment removed for export] *)
  Lemma client_wrange_keep : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi_c24 ()) "PSPx,$9.PTOPx,$9.PA,$9.Pn,$9.P,(4?.(46.VR,)(47.$7.VLB,(48.VLF,))R4.R3.R2.R1.)P,P,(;.$42.(43.VdX,)$49.)(35.(25.(1>.R4.R3.)(4:.VdX,))(25.(1>.(4:.VdX,)(4;.+4.(4<.VdX,)))R4.))(4?.(46.VR,)(47.$7.(18.VLB,VdX,)(48.VLF,))R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros SPx TOPx A n CW AP a Ha. destruct (CW a Ha) as [Hs|[Hd|(b & Hb & Hr)]]; [left; exact Hs| right; left; exact Hd| right; right].
    exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
    apply In_mpd_keep_intro; [exact Hb|]. unfold mpd_blk. destruct (md_own dX) eqn:EO; [intros []| | intros []].
    intros [E|[]]. subst b. cbn in Hr. specialize (AP eq_refl). clear - Hr AP Ha. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308587409.700000CS2dX1A1n2AP1a2Ha2Hr". (* [comment removed for export] *)
  Lemma client_range_keep : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi_c24 ()) "PSPx,$9.PA,$9.Pn,$9.P,(50.(46.VR,)(47.$7.VLB,(48.VLF,))R3.R2.R1.)P,P,(;.$42.(43.VdX,)$49.)(35.(25.(1>.R4.R3.)(4:.VdX,))(25.(1>.(4:.VdX,)(4;.+4.(4<.VdX,)))R4.))(50.(46.VR,)(47.$7.(18.VLB,VdX,)(48.VLF,))R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros SPx A n CR AP a Ha. destruct (CR a Ha) as [Hs|[Hd|(b & Hb & Hr)]]; [left; exact Hs| right; left; exact Hd| right; right].
    exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
    apply In_mpd_keep_intro; [exact Hb|]. unfold mpd_blk. destruct (md_own dX) eqn:EO; [intros []| | intros []].
    intros [E|[]]. subst b. cbn in Hr. specialize (AP eq_refl). clear - Hr AP Ha. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Notation W := [(PP, PP + 8); (md_addr dX, md_addr dX + 16)].
  Notation POST := (asn1_get_mpi_postA_c asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP P END dX lo d).

  Hypothesis XLB : md_own dX = LHeap -> md_p dX + 4 * md_n dX <= alloc_ceiling /\ 0 < md_p dX.

  Local Ltac2 Set LiaOrc.tbl := fun () => "03^0@D10651634317.132D10651634317.137D21329468335.117D21329468335.118D23379772182.118D28498761192.184D35881667587.117D35881667587.118D4451634193.184 D46805379688.132D46805379688.137D60098909036.132D60098909036.137D60109196847.184D64317730251.132D64317730251.137K12226132804.117K12226132804.118K30474232799.184K44164039966.117K44164039966.118L10649519402.1  L11326150134.11 L11328261952.6  L11423978205.12 L11803635331.9  L12222146976.2  L12414522636.0  L1429900444.1   L14886007918.10 L14886007918.9  L15280506777.4  L15756354262.4  L16087790284.35 L1685717371.0   L16959327509.10 L17701970480.1  L19201215546.35 L21765854580.109L21887662552.108L21887662552.130L21887662552.133L21887662552.175L22706556809.4  L23884779055.35 L24109380644.4  L27775132660.109L28757711097.5  L29428324939.5  L30478119227.2  L30504326418.4  L31131013238.9  L33510041944.109L33510041944.130L33510041944.133L33510041944.175L33808426644.35 L34290115814.113L35655473017.6  L35693901974.182L35992000370.3  L36400902985.4  L38770711634.35 L39332637397.0  L397962399.4    L39935459111.181L39939634581.135L39941749543.138L40834179097.111L41202929119.129L41202929119.130L41202929119.174L41562522427.134L41562522427.137L41562522430.180L41942189128.1  L4233398364.6   L43059266230.111L44168742175.3  L44252307114.8  L45288738383.35 L4959706922.35  L51508673957.0  L5261466405.8   L52634178206.6  L53271535775.174L54748384003.109L57392807047.37 L57777220325.11 L57777299826.2  L58805056528.7  L58807005955.9  L59309005011.1  L59309005011.3  L60098763854.3  L61565418556.128L62018535662.1  L62031154087.11 L62031154087.9  L64180445855.129L66083662040.109L66083662040.130L66083662040.133L66083662040.175L67092310858.4  L68297591230.8  L7465097271.2   L8187829678.35  L8603509526.35  L8840328354.9   L9716869748.108 L9817085104.128 L9962237875.109 L9962237875.130 L9962237875.133 L9962237875.175 P48648690810.174Q10478161754.118Q10649498890.135Q10649498890.136Q10649498890.181Q10649604031.135Q10649715752.134Q10651634312.180Q10651634317.132Q10651634317.137Q13732762037.180Q13735187586.135Q13735272213.134Q1461511394.116 Q14633614404.116Q15641193412.138Q15643272566.135Q15643324129.113Q15647485892.181Q15756125040.132Q15756125040.137Q17013132514.132Q17013132514.137Q17701933584.135Q17701933584.136Q17701933584.181Q18694146040.116Q20414272036.117Q20414272036.118Q20414272036.184Q20568046174.116Q21798041355.116Q22712450012.117Q22712450012.118Q23512175082.115Q24665950363.117Q24665950363.118Q25157988860.116Q25513505925.116Q25513505925.117Q25662358575.116Q26611046992.116Q27668705378.116Q27668705378.117Q28496781288.183Q28498761192.184Q28689862499.132Q28689862499.137Q31135243771.132Q31135243771.137Q31228709292.116Q31394594844.116Q32653238468.138Q32655289974.135Q32655500769.114Q32659530948.181Q32681824661.117Q32681824661.118Q32681824661.184Q33185036414.116Q35014437530.116Q35717497884.116Q35765334355.114Q35765334355.115Q37216054521.181Q3830244501.135 Q3830427394.114 Q3832293927.138 Q3834392103.181 Q3871444045.174 Q39600066516.135Q39600066516.136Q39935459111.181Q39939554818.114Q39939634581.135Q39941749543.138Q40271225078.175Q41930316588.175Q4451634193.184 Q4453582353.183 Q44648628726.135Q44648843873.114Q44650778436.138Q44652874564.181Q45353818935.180Q45355799959.134Q45355851264.135Q4639722776.135 Q4639722776.136 Q46805379688.132Q46805379688.137Q49698585326.115Q49698585326.116Q50846839876.132Q50846839876.137Q51223443012.181Q51233927748.138Q51235796833.114Q51236011254.135Q5298861436.175 Q53969758199.116Q60741299470.132Q60741299470.137Q61556549392.182Q61847600945.135Q61847600945.136Q61847600945.181Q62011821800.175Q6416456232.116 Q64255486968.116Q66522020629.135Q66522067074.114Q66524132775.138Q66534617511.181Q67426116409.117Q68548810730.116Q7190686615.165 Q7193124917.145 Q9839205543.181 Q9841301671.138 Q9843367298.113 Q9843414549.135 00000:00D01;02502l03L04404b05B05L05V05i06<06e07>07W08F09;09n0:^0;T0;X0<00<E0<k0=E0=F0=G0=K0=m0>L0>X0>f0?=0?>0?[0?_0@W0@a0@k0A50A?0AM0A[0BS0Ba0Bk0C:0CL0CM0C_0D10D;0DE0DO0D]0EI0ES0Eh0F60FA0FO0GQ0GR0G`0I60JH0KV0Kb0Kl0L60LD0LN0LX0Lf0Lj0M<0NJ0NK0Nc0OQ0Oe0Of0PC0PW0Pe0Po0Qe0Qo0R60RK0Rj0Rn0S70SA0T20T50TM0Te0UV0U`0Uj0V40VB0VP0Vb0Vh0Vi0WU0X20X<0Xm0Y70YA0YK0YY0Yn0Z^0Ze0Zl0[70[>0[E0[P0[W0[^0[i0\00\70\80\90\C0\M0\W0\e0]60]G0]N0]U0]\0]c0]n0^90^d0_U0`80`90`:0`S0a20a<0al0b_0bj0cF0ch0ci0cj0dR0e=0eZ0f70fM0fc0fd0fe0g10g50g?0gI0gS0ga0gb0gc0hC0hD0hP0hQ0h[0he0i70iM0ic0j90jS0k10k20k30kM0kc0l90lO0l_0lj0mG0md0mn0n80nB0nP0n[0nb0ni0nj0nk0o20o90oM0oa0ok10510C10M10W10a10b10n11811B11Z12012F12`12j13513613L13b14814R15:15;15e16O16i17?17U17kS2sp2PP2bsS2sp2PP2bsS1R5NEED02ra2sp2PP2lo2bs3PPB3LOS3SPL3SPR2HB5Ha_st5Hl_stS1R5NEED02sp2s02PP2lo2bs3PPB3LOS3SPL3SPR2HB5Ha_st5Hl_st2s1S1R5NEED02sp2s22PP2lo2bs3PPB3LOS3SPL3SPR2HB5Ha_st5Hl_stS2sp2PP2bs2p13ibs2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2PP2bs3TOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s02PP2bs3TOP2HB5Ha_st5Hl_st2s12s2S2sp2PP2bs2p13ibs2HB5Ha_st5Hl_stS2sp2PP2bsS2sp2PP2bsS1R2sp2PP2lo2bs3LOSS1R2sp2PP2lo2bs3LOSS1R2sp2PP2lo2bs3LOS2p13ibs2HB5Ha_st5Hl_stS1R3HIA1h2sp2PP2lo2bs3TOPS1R3HIA1h2sp2PP2lo2bs3TOPS1R5NEED02ra2sp2PP2lo2bs3SPL3DS12HB5Ha_st5Hl_stS1R5NEED02sp2s02PP2lo2bs3SPL3DS12HB5Ha_st5Hl_st2s12s2S1R5NEED02sp2PP2lo2bs3SPL3DS12p13ibs2HB5Ha_st5Hl_stS1R5NEED02ra2sp3BUF2lo2bs3SPL3DS32HB5Ha_st5Hl_stS1R5NEED02sp2s03BUF2lo2bs3SPL3DS32HB5Ha_st5Hl_st2s12s2S2PPS1P3END3BUF2bs2B12p13Hp1S1P3END3BUF2B12p13Hp1S1P3END3BUF2bs2B12B32p12Lw3Hp12KC1a2HaS1R5NEED02sp2lo2dX3SPL3DSXFSS2spS2LB1P2p13ibs2Lw3LB24HCNT2WR2W02DDS2LB1P2p13ibs2Lw3LB24HCNT2WR2DDS1P3END1p2HpS1R2lo3LOS3ALOS1R3HIA1h2sp2bs3TOP3ibsSS1P3END2p13ibs2Lw3Hp14LENI2W1S2PPS2sp1P3END3BUF2bs2dX2B12B33DX33SPR2p12Lw3Hp12KC3ibs4LENIS2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS2PP2dX3x212HxS2sp1P3END3BUF2lo2bs2B12B33DS33SPR2p12Lw3Hp12KC3ibs4LENIS1P3END2p13Hp1S2sp2PP2bsS1R3HIA1h1d3FR0S1R2lo3LOS3ALO3ACPFS2m23LB23dX25HOWN'S1P3END2p13ibs3Hp1S2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS2sp3END3BUF2bs2B33B473SPR2p12Lw2KC3ibs4LENIS2sp2PP2bsS1R3HIA1h2sp2lo5TOPHIS2sp2PP2bs3ibsS2PP2dX3DX1S1P3END2p13Hp1S1R5NEED02sp1P3END3BUF2lo2bs2B13NZ33LOS3SPL3ALO3ACP3SPR2p13Hp13ibsSS2sp2PP2lo3DS1S1R5NEED02sp2PP1P3END3BUF2lo2bs2dX2B12B32D23DX13DX33PPB3SPL3DS13DS33DSX3SPR2p13ibs3Hp1S1R5NEED02sp2PP1P3END3BUF2lo2bs2dX2B12B32D23DX13DX33PPB3SPL3DS13DS33DSX3SPR2p13Hp1S1R5NEED02sp2PP1P3END3BUF2lo2bs2dX2B12B22B32D23DX13DX33PPB3SPL3DS13DS33DSX3SPRS1R2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS2spS1R3HIA1h1P3END2B2S1R5NEED02sp2PP1P3END3BUF2lo2bs2dX2B12B22B32D23DX13DX33PPB3SPL3DS13DS33DSX3SPRFS1R2sp2lo3LOS3ALO3dX22F1S1R5NEED02sp2lo2bs3LOS3SPL3SPA3ALO3ACP3SPR3ibsS1R2sp2lo2bs3SPL3ibsSS1P3END2p13ibs2Lw3Hp12KC4LENIS1P3END2p12Lw3Hp12KCS2sp2PP2bs3ibsS2sp2PP2bsS2sp1P3END3BUF2bs2dX2B12B33SPR2p12Lw3Hp12KC3ibs4LENI1HS2bs2Lw2LRS2Lw2LRS2sp2PP2lo2dX3DX13DSXS1R2sp2PP2lo2dX3DX23LOS3XLB3ALOS2R0S1r2Hr2R0S1R2lo3LOSS2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2p13Hp1S1RS3END3BUF2bs2B32p12Lw2KCS3END3BUF2bs2B32p12Lw2KCS2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2p13Hp1S2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS2LB1P1p2DP2p1S1P3END2p13ibs3Hp1S1r2HrFS2sp3END3BUF2bs2B33B473SPR2p12Lw2KC3ibs4LENIS1P3END2p13ibs2Lw3Hp12KC4LENIS2sp2PP2bsS2sp2PP1P3END3BUF2bs2B12B33B473PPB3NZ33SPR2p13Hp1S2sp2PP2bsS2sp2PP2bsS2sp2PP2bsS2sp2PP2bs3ibsS2sp2PP2lo2bs3DS13ibsS1R5NEED02sp2s22lo2bs3LOS3SPL3ALO2HB5Ha_st5Hl_stS2PP2bsS2PP2bsS2PP2bs3ibsS2PP2bsS2PP2bsS2PP2bs3ibsS2PP2bsS2PP2bsS2PP2bs3ibsS2PP2bsS2PP2bsFFS2sp2lo2bsS2sp2lo2bsS2sp2lo2bsS2sp2lo2bs3ibsS1R2lo2bs3LOS3ALOS1R2lo2bs3LOS3ALOS2PP2bsS2PP2bsS2PP2bsS2PP2bsS2PP2bs3ibsS1R2bs4IMG'S1R5NEED02ra2sp2PP2lo2bs3SPL2HB5Ha_st5Hl_stS1R5NEED02sp2s02PP2lo2bs3SPL2HB5Ha_st5Hl_st2s12s2S2sp2PP2lo2bs2p13ibs2HB5Ha_st5Hl_stFFS2ra2sp2bs2HB5Ha_st5Hl_stS2sp2s02bs2HB5Ha_st5Hl_st2s12s2S2sp2bs2HBS1R5NEED02ra2sp2lo2bs3LOS3SPL3ALO2HB5Ha_st5Hl_stS1R5NEED02sp2s02lo2bs3LOS3SPL3ALO2HB5Ha_st5Hl_st2s1S1R2bs4IMG'S2ra2sp2lo2bs2HB5Ha_st5Hl_stS2sp2s02lo2bs2HB5Ha_st5Hl_st2s12s2FFS1R5NEED02ra2sp2lo2bs3SPL2HB5Ha_st5Hl_stS1R5NEED02sp2s02lo2bs3SPL2HB5Ha_st5Hl_st2s1S2PP2bs2p13ibs2HB5Ha_st5Hl_stS2PP2bs2p13ibs2HB5Ha_st5Hl_stS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLFFS1R2bs5ALWF'S2bsS2sp2lo2bsS2sp2lo2bsS2sp2lo2bsS2sp2lo2bs3ibsFFS2PP2bs2dX2p13ibs2HB5Ha_st5Hl_stFS1R2bs5ALWF'FS2sp2bs2HBS2sp2bs2HBS2PP2bs3PPB3ibs2HBS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPL3ibsS1R5NEED02sp2lo2bs3LOS3SPL3ibsFFS1R5NEED02sp2lo2bs3SPL3ibsS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R3HIA1h2bs3ibsS2sp2bs3ibsS2PP2bs2p13ibs2HB5Ha_st5Hl_stS2PP2bs2p13ibs2HB5Ha_st5Hl_stS2sp2lo2bsS2sp2lo2bsS2sp2lo2bsS2sp2lo2bs3ibsS2PP2bs3ibsS2PP2bsS2PP2bsFFS2PP2bsS2PP2bsS2sp2bs3SPR2HB5Ha_stS2sp2bs3SPR2HB5Ha_stS2sp2lo2bsS2sp2lo2bsS2sp2lo2bs3ibsS2sp2lo2bsS2sp2lo2bsS2sp2lo2bsFS1R2bs5ALWF'S2PP2bs2dXS2PP2bs2dXS2PP2bs3PPB3ibs2HB5Ha_stS2sp2PP2bs3PPB3AL13SPRS2sp2PP2bs3PPB3AL13SPRS2sp2PP2bs3PPB3AL13SPR3ibsS1R2bs3ibsS1R2bs4IMG'FS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPL3ibsS1R5NEED02sp2s22lo2bs3SPL2HB5Ha_st5Hl_stFS1R5NEED02sp2lo2bs3LOS3SPL3ALO3ACP3SPR3ibsS1R5NEED02sp2lo2bs3LOS3SPL3ALO3ACP3SPR3ibsS1R5NEED02sp2lo2bs3SPL3ibsS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPLS1R5NEED02sp2lo2bs3SPL". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi_c24 ()) "Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)P,(2;.$5;.VR,VHIA,Vh,VLB,VLF,R7.)P,(23.$5;.VR,VHIA,Vh,R7.)P,(2>.$5;.R9.VPP,(1;.$2?.(30.(?.&40.VP,))(20.$2?.)))P,(3=.$5;.R:.VBUF,Vbs,)P,(2<.$5;.R;.VLB,VdX,)P,(14.$5;.R<.Vlo,(15.&40.Vsp,))P,(13.$5;.R=.)P,(52.$5;.(53.VR,)(24.$5;.VR,VHIA,Vh,)R>.VPP,+8.)P,(52.$5;.(53.VR,)(24.$5;.VR,VHIA,Vh,)R?.(1?.VdX,)+10.)P,(52.$5;.(53.VR,)(24.$5;.VR,VHIA,Vh,)R10.VBUF,(3>.(3?.(2.&8.)Vbs,)))P,(25.(1>.(26.$5;.VR,VHIA,Vh,)(27.(28.VEND,VP,)))$54.)P,(25.(1>.(29.$5;.VR,VHIA,Vh,)(2:.Vd,))$56.)(59.$5;.(5:.$5;.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VdX,Vlo,Vd,R13.R12.)(<.(=.(>.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(?.&40.VPP,)(?.&40.VEND,)(?.&40.(1?.VdX,))R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(?.&40.+99840.)Vfc,(11.(2.&40.))R13.(12.$5;.))R12.))")
(* [comment removed for export] *).
  Proof.
    intros m mo a3 a4 a5 a6 a7 HH HKmo HPP HBUF HX ST MI OPP OX OBUF BUD BUDF.
    pose proof (MPI_RB_FR_nonneg d (uw_obj_nonneg _ _ _ _ XUW)) as FR0.
    pose proof (conj HH I) as HH0. pose proof (conj HX I) as HX0. rt_facts.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (presW_sub_blocks asegs R HIA h LB (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) W m m
                  (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) W HH ltac:(clear; lia)) (In_mpd_keep LB dX)) as PW.
    pose proof (wlow_sub_blocks R LB (mpd_keep LB dX) LF (hm_wlow asegs R HIA h LB LF m HH) (In_mpd_keep LB dX)) as WL.
    pose proof (munch_refl [(lo, bv_unsigned sp); (PP, PP + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
      [ eapply hdr_walk; unfold hdr_facts; repeat (lazymatch goal with |- _ /\ _ => split end); try eassumption;
        [ apply munch_refl | apply wmono_refl ]
      | intros y Hy; exact Hy | ].
    intros ms' [HF | HJ].
    - (* [comment removed for export] *)
      destruct HF as (x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m5 & r & p & -> & Hr & Hp
                      & HPP5 & HBUF5 & FR5 & ST5 & MI5 & OPP5 & OX5 & OBUF5 & MU5 & WM5).
      clear HPP HBUF FR ST MI OPP OX OBUF.
      transport_after_callA asegs m1 m5 MU5.
      assert (HX5 : mpd_at asegs m5 LB dX).
      { eapply mpd_at_munch; [exact (proj1 HX0)| exact HNS| eapply munch_trans; [exact MU| exact MU5]| eapply wmono_trans; [exact WM| exact WM5]| |];
          cbn [disjoint_from].
        - clear - DSX DX1 XB. lia.
        - intros HO. specialize (DX2 HO). specialize (XLB HO). clear - DX2 XLB ALO LOS. lia. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      release_frame FR5 ST5 (bv_unsigned sp).
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
      split; [intros b Hb; left; exact Hb|]. (match goal with |- cnt24 _ <= cnt24 _ + ?q / 5889 => let DP := fresh "DP" in assert (DP : 0 <= q / 5889) by (apply Z.div_pos; [first [clear - Hp; lia | clear - Hp1; lia | clear - Hp Hp1; lia]| clear; lia]); clear - DP; lia end).
    - (* [comment removed for export] *)
      destruct HJ as (x5 & x6 & x7 & x9 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m5 & p1 & Lw & -> & Hp1
                      & HPP5 & HBUF5 & FR5 & ST5 & MI5 & OPP5 & OX5 & OBUF5 & MU5 & WM5).
      clear HPP HBUF FR ST MI OPP OX OBUF.
      transport_after_callA asegs m1 m5 MU5.
      assert (HX5 : mpd_at asegs m5 LB dX).
      { eapply mpd_at_munch; [exact (proj1 HX0)| exact HNS| eapply munch_trans; [exact MU| exact MU5]| eapply wmono_trans; [exact WM| exact WM5]| |];
          cbn [disjoint_from].
        - clear - DSX DX1 XB. lia.
        - intros HO. specialize (DX2 HO). specialize (XLB HO). clear - DX2 XLB ALO LOS. lia. }
      pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      zstep. if_cases KC; zify_cond KC.
      { (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        release_frame FR5 ST5 (bv_unsigned sp).
        apply aevtA_done. intros mo9 [HK9 MF9].
        do 14 eexists. exists m5, mo9, h, LB, dX, (-96), p1.
        split; [reflexivity|].
        split; [assumption|]. split; [assumption|]. split; [exact MF9|].
        split; [eapply presW_presA; eassumption|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HK9|].
        split; [intros y Hy; exact Hy|].
        split; [unfold MPI_RB_PHI, AVOL_CALL; clear - B2; lia|].
        split; [clear - FR0; lia|].
        split; [assumption|]. split; [exact HX5|]. split; [apply mpd_out_refl; exact HNS|].
        split; [assumption|]. split; [clear - Hp1; lia|]. split; [clear; lia|].
        split; [intros R0; exfalso; clear - R0; lia|].
        split; [intros b Hb; left; exact Hb|]. (match goal with |- cnt24 _ <= cnt24 _ + ?q / 5889 => let DP := fresh "DP" in assert (DP : 0 <= q / 5889) by (apply Z.div_pos; [first [clear - Hp; lia | clear - Hp1; lia | clear - Hp Hp1; lia]| clear; lia]); clear - DP; lia end). }
      rewrite ?unsigned_lit in KC by qlia.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      set (ibs := firstn (Z.to_nat (bv_unsigned Lw)) (skipn (Z.to_nat (p1 - BUF)) bs)).
      assert (LENI : Z.of_nat (length ibs) = bv_unsigned Lw) by (subst ibs; apply bytes_at_sub_length; clear - Hp1 KC B1 B3 LR; lia).
      assert (HIB : bytes_at asegs m5 p1 ibs) by (subst ibs; eapply bytes_at_sub; [exact HBUF5| clear - Hp1 B1; lia| clear - LR; lia| clear - Hp1 KC B3; lia]).
      assert (OIB : aobj asegs AL CS m5 p1 (Z.of_nat (length ibs))).
      { rewrite LENI. eapply aobj_sub; [exact OBUF5| clear - Hp1 B1; lia| clear - Hp1 KC B3; lia]. }
      assert (HWR' : mpd_writable L (LB ++ fdata LF) (bv_unsigned sp + -32) (htop asegs R HIA h) dX)
        by (eapply mpd_writable_sp_mono; [exact HWR| clear; lia]).
      assert (CRI : client_range L (LB ++ fdata LF) lo p1 (Z.of_nat (length ibs))) by (rewrite LENI; intros a Ha; apply CRBUF; clear - Ha Hp1 KC B1 B3; lia).
      assert (CWPPk : client_wrange L (mpd_keep LB dX ++ fdata LF) lo (htop asegs R HIA h) PP 8) by (apply client_wrange_keep; [exact CWPP| exact DX2]).
      assert (BUDI : havol asegs R HIA h + MPI_RB_PHI (Z.of_nat (length ibs)) <= AVOL_MAX).
      { rewrite LENI. eapply Z.le_trans; [| exact BUD]. apply Zplus_le_compat_l. apply MPI_RB_PHI_mono. clear - KC Hp1; lia. }
      replace Lw with (Z_to_bv 64 (Z.of_nat (length ibs))) by (rewrite LENI; apply Z_to_bv_bv_unsigned).
      clearbody ibs. clear HBUF5 OBUF5.
      pose proof HRB as SP. unfold mpi_read_binary_stmtA_c, A_MPI_READ_BINARY in SP.
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply SP with (h := h) (LB := LB) (LF := LF) (dX := dX) (B := p1) (ibs := ibs) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by qlia; try eassumption; try reflexivity.
        all: clear - Hp1 KC B1 B3 B4 B47 NZ3 LENI LR TOP SPL NEED0 SPA SPR LOS ALO ACP DS3 DX3 DX4 BUDF;
             first [lia | intros HO; pose proof (DX4 HO); lia | Z.div_mod_to_equations; lia | match goal with |- ?g => idtac "RB-PRE-LEFT:" g end]. }
      clear SP.
      intros ms' mo' (mo1 & [HK1 MF1] & PO).
      destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
      injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by qlia.
      flat constr:(PO) 18%nat. flclear PO. intros MI2 ST2 MF2 HP2 HT2 HS2 HF2 HK2 HCS2 HV2 HFR2 HH2 HX2 HOUT Hr Hr0 HFRESH HCNT.
      rewrite LENI in HCNT.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
      match type of HH2 with HM _ _ _ ?hh ?LBB _ _ => rename hh into h2; rename LBB into LB2 end.
      match type of HX2 with mpd_at _ _ _ ?d => rename d into dX2 end.
      match type of Hr with ?rr = 0 \/ _ => rename rr into r end.
      clear MI5 OX5 OIB HIB CRI HWR' HX5.
      (* [comment removed for export] *)
      apply (presA_rw_cells asegs R _ _ _ _ _ _ _ _ _ _ HP2) in FR5;
        [| apply client_range_stack; simpl_sizes; clear; lia | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - DSX XB SPR SPL NEED0; lia ].
      apply (presA_rw_cells asegs R _ _ _ _ _ _ _ _ _ _ HP2) in HPP5;
        [| simpl_sizes; eapply client_range_wsep; [exact CWPPk| intros b Hb; exact Hb| clear - DS1; lia]
         | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - DX1; lia ].
      presA_transport HP2.
      (* [comment removed for export] *)
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
      (* [comment removed for export] *)
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OPP5) as OPP2.
      assert (SCS2 : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS2| exact SCS]).
      pose proof (hcs_ok asegs R HIA h2) as CSOK2.
      assert (CW2 : client_wrange L (LB2 ++ fdata LF) lo (htop asegs R HIA h2) PP 8).
      { rewrite HT2. eapply client_wrange_mono; [exact CWPPk|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff.
        destruct Hb as [Hb|Hb]; [left; eapply mpd_keep_out; [exact HOUT| exact Hb]| right; exact Hb]. }
      assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
      pose proof (munch_refl [(lo, bv_unsigned sp); (PP, PP + 8)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      release_frame FR5 ST2 (bv_unsigned sp).
      pose proof HOUT as HOUT'. flat constr:(HOUT') 3%nat. flclear HOUT'. intros HA2 HNS2 _.
      assert (HX9 : mpd_at asegs m9 LB2 dX2).
      { eapply mpd_at_munch; [exact HX2| exact HNS2| exact MU2| exact WM2| |]; cbn [disjoint_from].
        - rewrite HA2. clear - DSX DX1 XB. lia.
        - intros HO. split; [| split; [| exact I]].
          + (* [comment removed for export] *)
            flat constr:(HX2) 2%nat. flclear HX2. intros FLt1 _. flat constr:(FLt1) 6%nat. flclear FLt1. intros _ _ _ HL _ HOWN. rewrite HO in HOWN. flat constr:(HOWN) 3%nat. flclear HOWN. intros Hn1 HIN2 _.
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
      do 14 eexists. exists m9, mo9, h2, LB2, dX2, r, (p1 + Z.of_nat (length ibs)).
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [exact MF9|].
      split; [eapply presW_presA; eassumption|].
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|].
      split; [exact HCS2|].
      split; [eapply Z.le_trans; [exact HV2|]; apply Zplus_le_compat_l; apply MPI_RB_PHI_mono; clear - KC Hp1 LENI; lia|].
      split; [exact HFR2|].
      split; [assumption|]. split; [exact HX9|]. split; [exact HOUT|].
      split; [assumption|]. split; [clear - KC Hp1 LENI LR; lia|].
      split; [unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr; lia|].
      split; [intros R0; split; [clear - Hp1 LENI LR; lia| exact (proj1 (Hr0 R0))]|].
      split; [exact HFRESH|]. (pose proof (w24_range (4 * chars_to_limbs (bv_unsigned Lw))) as WR; destruct (Z.eq_dec (w24 (4 * chars_to_limbs (bv_unsigned Lw))) 1) as [W1|W0]; [ apply w24_ctl in W1; match goal with |- cnt24 _ <= cnt24 _ + ?q / 5889 => assert (DD : 1 <= q / 5889) by (apply Z.div_le_lower_bound; [clear; lia| clear - W1 Hp1 LENI LR KC; lia]) end; clear - DD HCNT WR; lia | match goal with |- cnt24 _ <= cnt24 _ + ?q / 5889 => assert (DD : 0 <= q / 5889) by (apply Z.div_pos; [clear - Hp1 LENI LR KC; lia| clear; lia]) end; clear - DD HCNT WR W0; lia ]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00=0@L31036732193.96 L32795199445.98 L34628186967.7  L34632568438.9  L41353889562.100L42760023526.97 L59315317366.12 L59315317366.7  L59964710235.94 L63860231421.96 L68428645371.8  L68544371040.6  L68548764737.4  00000[01401M01g02d03503^04204I04Z04l05;05IS1R3HIA1h2sp2PP2bs3NZ13TOP3PPB3ALO3ACP4HTOPS1R2sp2PP2bs2dX3PPB2H02HCS1R2dX2lo3LOS3ALO3DHI3D2'S1R2dX2lo3LOS3ALO1B1j2Hr1HS1R5NEED02sp2PP2bs2lo3NZ13LOS3SLO3PPB3ALO3ACP2Bx2jx2fb3Hr22HCS2sp2PP2bs2dX3PPBS1R3HIA5NEED01h2sp2dX2lo3LOS3SLO3ALO2A01SS1R3HIA1h2sp2dX2Hs1SS2sp2PP2bs2dX3PPB3HP01BS2sp2PP2bs2dX3PPBS2FB1n2Bx2jx2E12E2S1R2dX1B1j2Hr1HS1R2dX3DHI3D2'". (* [comment removed for export] *)
Lemma A_asn1_get_mpi_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_mpi_c24 ()) "PR,$67.PHIA,(68.$5;.R1.)P,(69.(53.R2.))P,(25.=(4>.R3.))(6:.$5;.R4.R3.$6;.$6<.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG NEED0 HRB. unfold A_ASN1_GET_MPI.
  intros until d. intros HH HK HPP HBUF B1 B2 B3 B4 B47 HX HNS HWR D2 DX1 DX2 DX3 DX4 AL1 NZ1 NZ3 ST LOS SLO TOP SPA DS1 DS3
         CWPP CRBUF TPV MI OPP OX OBUF BUD XUW BUDF C24H -> -> ->.
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
