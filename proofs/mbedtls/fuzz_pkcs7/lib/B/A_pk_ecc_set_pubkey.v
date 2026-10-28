(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_ecp_check_pubkey P_ecp_point_read_binary.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_copy A_ecp_check_pubkey_c24 A_frame_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
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
Ltac2 gd_tbl_A_pk_ecc_set_pubkey () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_A"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_B"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.grp_imgA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.grp_nle"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_h"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_X"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_G"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Y"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_pt"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "pk_set_pubkey_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "pk_set_pubkey_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mkKP"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_mpds"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_point_read_binary.pt_dis"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_dy_sz"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_blocks"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_KEYPAIR_SIZE"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_init"; "grp_factsA"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.mc_okA"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_check_pubkey.bad_point_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.arl_need_ecp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "C24_PK_SET_PUBKEY"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.check_pubkey_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.check_pubkey_FRn"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "pk_ecc_set_pubkey_postA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_check_pubkey_c24.A_BAD_POINTS"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_point_read_binary_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_POINT_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_MUL_COUNT"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_check_pubkey_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_CHECK_PUBKEY"; "pk_ecc_set_pubkey_stmtA"; "A_PK_ECC_SET_PUBKEY"].


Definition A_PK_ECC_SET_PUBKEY : Z := 0x0da558.     (* [comment removed for export] *)
(* [comment removed for export] *)
Notation PK_ECC_SET_PUBKEY_STACK_A := 1536 (only parsing).
Definition pk_set_pubkey_PHI (N len : Z) : Z := point_read_PHIn N len + check_pubkey_PHIn (ecp_dy_sz N).
Definition pk_set_pubkey_FR (N d : Z) : Z := point_read_FRn N 0 + check_pubkey_FRn (ecp_dy_sz N) d.
(* [comment removed for export] *)
Definition C24_PK_SET_PUBKEY : Z := Z.max C24_ECP_POINT_READ (C24_ECP_CHECK_PUBKEY + 3).

(* [comment removed for export] *)
Definition grp_factsA (g : ecp_grp) (N : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_pubkey ()) "(0.(1.$2.(3.(4.O2.))+1.)(0.(1.$2.(3.(5.O2.))+1.)(0.(1.$2.(3.(6.O2.))+1.)(0.(7.+1.(8.(4.O2.)))(0.(7.(9.(4.O2.))+1387.)(0.(:.O2.)(0.(;.O2.O1.)(0.(7.=O1.)(<.(0.(1.$2.(=.O2.)+1.)(0.(>.(1.$2.(?.(10.(11.O2.)))=))(>.(1.$2.(?.(12.(11.O2.)))=))))(0.(1.$2.(=.O2.)+2.)(0.(>.(1.$2.(?.(10.(11.O2.)))=))(1.$2.(?.(12.(11.O2.)))=))))))))))))")
(* [comment removed for export] *).

Definition pk_ecc_set_pubkey_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs R HIA) (LB LF : list blk) (PKA info C : Z) (g : ecp_grp) (dd : mpd) (MC N LEN lo d : Z) (m : mem) (mo : Model)
    : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_pubkey ()) "Lc,$13.(14.(15.&40.)Lt0,(15.&40.)(14.(15.&40.)Lt1,(15.&40.)(14.(15.&40.)Lt2,(15.&40.)(14.(15.&40.)La1,(15.&40.)(14.(15.&40.)La2,(15.&40.)(14.(15.&40.)La3,(15.&40.)(14.(15.&40.)La4,(15.&40.)(14.(15.&40.)La5,(15.&40.)(14.(15.&40.)La6,(15.&40.)(14.(15.&40.)La7,(15.&40.)(14.(15.&40.)Lt3,(15.&40.)(14.(15.&40.)Lt4,(15.&40.)(14.(15.&40.)Lt5,(15.&40.)(14.(15.&40.)Lt6,(15.&40.)(14.P,(15.&40.)(16.(15.&8.))Lm',P,(15.&40.)(16.(15.&8.))(14.$17.Lmo',$17.(14.(18.O25.O24.O23.)Lh',(18.O25.O24.O23.)(14.(19.$1:.)LLB',(19.$1:.)(14.$1;.LQ',$1;.(14.$2.Lr,$2.(14.(15.&40.)Lcnt',(15.&40.)(0.(1.$13.R16.(1<.(1=.(1>.O21.O20.O1?.O1>.R15.R14.R13.O1=.O1<.(1?.&40.R2.)R12.R11.R10.R?.R>.R=.R<.O1;.O1:.O19.O18.O17.O16.O15.O14.O13.O12.R;.R:.R9.R8.)O11.(20.O21.)O10.(21.(15.&40.))R7.(22.O25.))R6.))(0.(0.(23.(24.(25.+2.+1?.))R2.)(7.R2.=))(0.(26.O25.R7.)(0.(27.O25.R7.O4.(28.&40.O20.))(0.(29.O1.R6.)(0.(2:.O25.O24.O>.O=.(28.&40.O20.)(2;.O24.)(2<.O25.O24.O23.O?.)(2=.(2>.$2.$2.)(2?.$2.$2.(30.O:.+=0.)(30.(30.O:.+=0.)+30.))(2=.(2>.$2.$2.)(2?.$2.$2.O7.(30.O7.+8.))(31.(2>.$2.$2.))))O2.R7.)(0.(1.$2.(32.O25.O24.O23.R5.)(32.O25.O24.O23.O?.))(0.(1.$2.(2<.O25.O24.O23.R5.)(2<.O25.O24.O23.O?.))(0.(1.$2.(33.O25.O24.O23.R5.)(33.O25.O24.O23.O?.))(0.(34.O25.O24.O23.R5.R6.)(0.Px,$2.P,(35.O25.O24.O23.O?.R1.)(35.O25.O24.O23.R7.R2.)(0.(7.(36.O25.O24.O23.R5.)(30.(36.O25.O24.O23.O?.)(37.O6.O5.)))(0.(7.(38.O25.O24.O23.R5.)(30.(38.O25.O24.O23.O?.)(39.O6.O3.)))(0.(3:.O25.O24.O23.R5.R4.O=.R7.)(0.(3;.O25.O22.R7.R4.O:.(3<.O9.O8.R3.))(0.(3=.$3>.Le,$3>.(<.(1.$2.(3.R1.)+1.)(1.$2.(3.R1.)-1.))(3?.R3.))(0.(40.R3.)(0.P,(1.$2.R2.=)(3=.$3>.Le,$3>.(7.(9.R1.)(41.O6.))(3?.R4.))(0.Pb,$1:.P,(42.$1:.R1.O>.)(42.$1:.R2.R6.)(0.Pb,$1:.P,(42.$1:.R1.R5.)(<.(42.$1:.R2.O>.)(42.$1:.R2.(43.R5.)))(0.Pb,$1:.P,(42.$1:.R1.(43.R4.))(0.(>.(42.$1:.R2.O>.))(44.O24.O>.O=.(45.$2.$2.R2.)(46.$2.$2.R2.)))(0.(47.O25.R7.O<.(2=.$48.(49.(1?.&40.O;.))(2=.$48.(49.(1?.&40.O:.))(31.$48.))))(47.O25.R7.O7.(2=.$48.(49.R1.)(31.$48.))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pk_ecc_set_pubkey_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (ENTRY MC BP : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_pubkey ()) "Ph,(18.O7.O6.O5.)PLB,(19.$1:.)PLF,(19.$1:.)Pra,(15.&40.)Psp,(15.&40.)Pgp,(15.&40.)Ptp,(15.&40.)Pt0,(15.&40.)Pt1,(15.&40.)Pt2,(15.&40.)Ps0,(15.&40.)Ps1,(15.&40.)Pa0,(15.&40.)Pa1,(15.&40.)Pa2,(15.&40.)Pa3,(15.&40.)Pa4,(15.&40.)Pa5,(15.&40.)Pa6,(15.&40.)Pa7,(15.&40.)Ps2,(15.&40.)Ps3,(15.&40.)Ps4,(15.&40.)Ps5,(15.&40.)Ps6,(15.&40.)Ps7,(15.&40.)Ps8,(15.&40.)Ps9,(15.&40.)Ps10,(15.&40.)Ps11,(15.&40.)Pt3,(15.&40.)Pt4,(15.&40.)Pt5,(15.&40.)Pt6,(15.&40.)PF,(4:.&5.(15.&40.))Pfc,(15.&20.)Pm,P,(15.&40.)(16.(15.&8.))Pmo,$17.PPKA,$2.Pinfo,$2.PC,$2.PB,$2.Pbs,(19.(15.&8.))Pg,$4;.Ppd,(15.&40.)PqX,(15.&40.)PqY,(15.&40.)PqZ,(15.&40.)Pcnt,(15.&40.)Pbp1,$3>.Pbp2,$3>.PN,$2.Plo,$2.Pd,$2.Pslo,$2.P,(3:.O7.O6.O5.R37.R36.R35.R13.)P,(34.O7.O6.O5.R38.R13.)P,(4<.(4=.(4>.$1:.R37.)#4.)#200.)P,(47.O7.R16.R14.(2=.$48.(49.(1?.&40.R13.))(2=.$48.(49.(1?.&40.R12.))(31.$48.))))P,(1.$2.(4?.R15.+8.)=)P,(23.=R16.)P,(50.O7.(51.O6.)(35.O7.O6.O5.R3=.)R19.R17.+10.)P,(52.(53.O6.)(54.$1:.R3=.(55.R3<.))R:.R18.+10.)P,(<.(7.(30.R19.+10.)R;.)(7.(28.&40.R3;.)R19.))P,(<.(7.(30.R1:.+10.)R18.)(7.(30.R18.$56.)R1:.))P,(<.(7.(30.O2.+8.)R1;.)(7.(30.R1;.+10.)O2.))P,(3;.O7.O4.R1>.R41.R1:.(3<.R17.(57.(30.R1:.+<0.)R16.)(58.(30.R1:.+=0.)R15.R14.R13.)))P,(42.(2>.$2.$2.)(2?.$2.$2.R1;.$56.)R42.)P,(59.R19.R11.)P,(5:.O7.R21.R1<.R1;.)P,(23.=R1=.)P,(7.(30.(30.R1>.(5;.(4>.(15.&8.)R1=.)))+8.)(25.+2.+2?.))P,(52.(53.O6.)(54.$1:.R47.(55.R46.))R14.R1?.(5;.(4>.(15.&8.)R1>.)))P,(<.(7.(30.R20.(5;.(4>.(15.&8.)R1?.)))R15.)(7.(28.&40.R45.)R20.))P,(<.(7.(30.R21.(5;.(4>.(15.&8.)R20.)))R22.)(7.(30.R22.$56.)R21.))P,(<.(7.(30.O2.+8.)R22.)(7.(30.R22.(5;.(4>.(15.&8.)R21.)))O2.))P,(<.(1.$2.(5;.(4>.(15.&8.)R22.))=)(50.O7.(51.O6.)(35.O7.O6.O5.R4<.)R28.R23.(5;.(4>.(15.&8.)R22.))))P,(47.O7.R29.O2.(2=.$48.(49.R1=.)(31.$48.)))P,(5<.O6.O2.)P,(<.(7.(30.O2.+8.)R27.)(7.(30.R27.$56.)O2.))P,(5=.O7.R2<.R4?.O1.R1?.)P,(5=.O7.R2=.R50.(30.O1.+20.)R1?.)P,(5>.R21.)P,(5>.R21.)P,(1.$5?.(60.O1.+10.)$61.)P,(1.$5?.(60.(30.O1.+20.)+10.)$61.)P,(<.(7.(30.O2.+8.)O1.)(7.(30.O1.+30.)O2.))P,(27.O7.R33.R23.(28.&40.R53.))P,(7.(2;.O6.)R24.)P,(7.R25.(62.(62.(28.&40.R55.)+600.)(63.O6.)))P,(64.O7.(51.O6.)R36.R24.(28.&40.R56.))P,(7.(2;.O6.)R25.)P,(7.R26.R28.)P,(7.(28.&40.R59.)(32.O7.O6.O5.R5=.))P,(1.$2.(4?.(28.&40.R5:.)+10.)=)P,(1.(15.&40.)R59.(1?.&40.(65.O6.)))P,(26.O7.R3<.)P,(1.$2.(4?.(28.&40.R5>.)+2.)=)P,(66.$2.(67.(2>.$2.$2.)$2.(45.$2.$2.)R61.))P,(7.(30.(36.O7.O6.O5.R63.)(37.R30.(5;.(4>.(15.&8.)R39.))))$68.)P,(69.O7.R40.(2;.O6.)(2<.O7.O6.O5.R64.)(28.&40.R5:.)(28.&40.R60.)R2?.)P,(7.(30.(38.O7.O6.O5.R65.)(39.R32.R30.))$6:.)P,(7.(30.(6;.R65.)$6<.)$6=.)P,(7.=(6>.(41.R34.)))P,(7.=(6?.(41.R35.)R33.))P,Pe,$3>.P,(42.$3>.R1.(70.R3?.))P,(1.$71.(72.R2.)$73.)(>.(1.$2.(?.R3.)R44.))P,(1.(15.&40.)R5>.(1?.&40.R44.))P,(1.(15.&40.)R5>.(1?.&40.R42.))P,(1.(15.&40.)R5>.(1?.&40.(5;.(4>.(15.&8.)R42.))))(74.O7.(75.O7.O6.O5.O4.R6:.R69.R68.R67.R63.R62.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4;.R4:.R6=.R6<.R6;.R47.R46.R45.R42.(57.(30.R45.+<0.)R41.)O2.R3:.(5;.(4>.(15.&8.)R43.))R39.R38.R49.R48.)(1<.(1=.(1>.R6:.R69.R68.R67.R66.R65.R64.R63.R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.)R4;.(1?.&40.O3.)R4:.(21.(15.&40.))R49.(22.O7.))R48.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L36134086745.2L47909269.3   L56470958949.400000600>00JS1a2HaS1A1i2HiS2bp2LL1i2Hi". (* [comment removed for export] *)
Lemma bad_point_any_mem : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_pubkey ()) "PR,$76.PHIA,(77.$78.R1.)Ph,(18.$78.R2.R1.)Phk,(18.$78.R3.R2.)PLB,(19.$1:.)PLF,(19.$1:.)PLBk,(19.$1:.)PLFk,(19.$1:.)Pm,P,(15.&40.)(16.(15.&8.))Pmk,P,(15.&40.)(16.(15.&8.))PA,$2.Pbp,$3>.P,Pm0,P,(15.&40.)(16.(15.&8.))P,(79.R=.R1.)(7:.R2.)P,(3:.$78.R=.R<.R;.R9.R8.R5.)P,(3:.$78.R>.R=.R;.R8.R7.R5.)P,(26.$78.R7.)P,(26.$78.R7.)P,(5=.$78.R9.R=.R7.R6.)P,(<.(1.$2.R8.$7;.)(1.$2.R8.(30.$7;.+20.)))(5=.$78.R:.R=.R9.R8.)")
(* [comment removed for export] *).
Proof.
  (intros R HIA h hk LB LF LBk LFk m mk A bp RTCL HH HHk MI MIk dd_H; ddestruct dd_H as (MB & EA & EO & SG); intros HA).
  destruct (RTCL m (hm_rtc asegs R HIA h LB LF m HH)) as [_ PR0]. destruct (RTCL mk (hm_rtc asegs R HIA hk LBk LFk mk HHk)) as [_ PRk].
  assert (PRI : forall a, A <= a < A + 16 -> rtc_prist a).
  { intros a Ha. unfold rtc_prist. eapply (in_ranges_b_sound rtc_pristine A_BAD_POINTS (A_BAD_POINTS + 48)); [vm_compute; reflexivity|].
    unfold A_BAD_POINTS in *. destruct HA as [-> | ->]; clear - Ha; lia. }
  destruct MB as [(CX & AL8 & POS & LL & NR & OW) SGN]. rewrite EO in OW. ddestruct OW as (N1 & P4 & P0 & PB & PRO).
  split; [| split; [exact EA| split; [exact EO| exact SG]]].
  split; [| exact SGN]. split.
  - eapply ck_rw_cells_same; [exact CX|]. unfold mpi_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    intros i Hi. rewrite EA. assert (HAi : A <= A + i < A + 16) by (clear - Hi; lia). rewrite (PRk (A + i) (PRI (A + i) HAi)), (PR0 (A + i) (PRI (A + i) HAi)). reflexivity.
  - split; [exact AL8|]. split; [exact POS|]. split; [exact LL|]. split; [exact NR|]. rewrite EO.
    split; [exact N1|]. split; [exact P4|]. split; [exact P0|]. split; [| exact PRO].
    eapply MpiFacts.static_limbs_any_mem; [exact MI| exact MIk| exact PB|]. rewrite u32s_length. intros i Hi. apply PRO. clear - Hi LL. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x0da5f0]).
Local Ltac zchk_new ::= constr:([0x0da568; 0x0da570; 0x0da574; 0x0da578; 0x0da5a0; 0x0da5a4; 0x0da5a8]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
Section WalkSP.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis RTCL : forall m, arl_rtc R m -> asan_rtc m.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Variable MT : list modp_ent.
  Hypothesis HPRB : ecp_point_read_binary_stmtA asegs R HIA MT A_ECP_POINT_READ_BINARY A_MUL_COUNT.
  Hypothesis HCPK : ecp_check_pubkey_stmtA asegs R HIA MT A_ECP_CHECK_PUBKEY A_MUL_COUNT A_BAD_POINTS.

  Local Ltac2 Set LiaOrc.tbl := fun () => "02`0@D21329468335.155D21329468335.156D35881667587.155D35881667587.156K15589905402.155K15589905402.156K64113782398.155K64113782398.156L12384449689.27 L1429900444.1   L14624175251.9  L15601980411.3  L15756355153.5  L1603158936.2   L16088298306.27 L1685717371.0   L21580243985.4  L21765854580.144L21887662552.143L21887662552.227L21887662552.228L22313785456.27 L22328826999.22 L22725724074.7  L22929875509.8  L23177638786.9  L23179735426.9  L23785117501.5  L24711474703.1  L24897784206.27 L25069434269.5  L25539402469.5  L25966757048.7  L26879113011.6  L26892418956.1  L27180976466.2  L27514306081.0  L27775132660.144L28009036723.13 L29010569222.226L31021792691.6  L31707989633.22 L31974651076.6  L32550613799.5  L33238509327.1  L33510041944.144L33510041944.227L33510041944.228L34290115814.151L35362472812.0  L35617777616.8  L35653441506.7  L35655538624.10 L3600419235.22  L37335576760.5  L37622536980.27 L37624864531.22 L39280637297.0  L39935298845.238L39939636484.237L39941780610.6  L40281191306.3  L40834179097.144L41562197561.6  L41562522430.236L41562522430.237L41942189128.1  L42350410676.4  L42733965476.27 L43059266230.149L43154573232.236L43551719215.0  L45288820673.27 L47232154693.27 L47760128357.7  L5248022362.1   L53388521588.7  L53419693873.3  L53735577720.143L56857443872.8  L5687117712.1   L58504191197.22 L59654577821.10 L60098763854.3  L60991393927.1  L61583536353.27 L62018535662.1  L62037160523.8  L63207038851.4  L63918187566.1  L64116126217.2  L64173436825.27 L6450286553.1   L64788204432.1  L65368606304.3  L66083662040.144L66083662040.227L66083662040.228L66151426447.10 L66151427842.16 L66597727309.2  L66610753222.8  L66617044166.8  L696052593.2    L7193141396.10  L7237223214.1   L7338849128.6   L8129703265.1   L8603099800.27  L9716869748.143 L9782311734.7   P27192773590.155P27192773590.156P5674272020.155 P5674272020.156 P64783223060.155P64783223060.156Q10883745538.152Q15643274727.237Q15643324129.151Q15647596030.238Q18696258664.152Q21800154267.152Q22712450012.155Q22712450012.156Q24665950363.155Q24665950363.156Q25160069740.152Q25513505925.154Q25513505925.155Q25664473023.152Q27668705378.154Q27668705378.155Q31226595900.152Q31396709260.152Q32655288039.237Q32655500769.152Q32659609342.238Q35016517898.152Q35715385228.152Q35765334355.152Q35765334355.153Q36169027261.152Q3830246404.237 Q3830427394.152 Q3834567709.238 Q41638316336.152Q42439443119.155Q42439443119.156Q49238979661.152Q49698585326.153Q49698585326.154Q51223282814.238Q51235796833.152Q51236009063.237Q53440817419.153Q53441140777.152Q53971870823.152Q54520642575.153Q59321350679.155Q59321350679.156Q59865321072.155Q59865321072.156Q63116570093.153Q6414342584.152 Q64253372520.152Q64683667846.155Q64683667846.156Q66522018692.237Q66522067074.152Q66534720413.238Q67528989526.155Q67528989526.156Q9839095453.238 Q9843367298.151 Q9843416708.237 00001502@03403n04o06307208408A08E08a08b09009809K09L09[0:40:M0:f0;?0;L0;V0;k0<D0<`0==0=D0=G0=V0=]0>00>I0>Z0>^0>_0>`0?90?I0?J0?_0@70@D0@Q0@T0@m0AF0A_0B80B90BS0Bk0CK0CX0Ce0D20D<0D=0Do0Ea0F80FA0F\0G10GJ0Gc0Gg0H60HF0I80IQ0IR0J=0JX0Jl0Jo0K90KB0K_0L?0L@0LX0M:0MD0MG0MW0MZ0N90N@0NC0ND0N_0Nb0Nc0Nl0OE0O^0P70PG0Pa0Pj0QF0Qa0Qi0RP0RS0Ri0Rl0S90SR0Sj0U30V?0WD0XL0YQ0ZY0Zl0[E0[^0\70\P0\Q0]90]d0^e0_i0`B0`m0a[0a\0bU0cQ0cl0d?0dX0e10eJ0ee0ef0f?0fX0fY0g@0gg0hN0ha0iT0jJ0jK0jn0kQ0kj0lC0l\0lo0mB0m]0n00n10n20n30n40nY0o20o310011011W12>12e13^14Z15A15h16OS1R3NS12LF2ra2sp3PKA2bs2lo3LFB3NZP3LOS3SLO3SPR3NES3PKB2HB5Ha_st5Hl_stS1R3NS12LF2ra2sp2s03PKA2bs2lo3LFB3NZP3LOS3SLO3SPR3NES3PKB2HB5Ha_st5Hl_st2s1S1R3HIA1h2LF2ra2sp3PKA2bs3LFB3TOP3PKB2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp2s03PKA2bs3LFB3TOP3PKB2HB5Ha_st5Hl_st2s1S1R5NEEDR2LF2ra2sp3PKA1B2bs2lo3LFB3DSB3SLO3NER3PKB2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2s03PKA1B2bs2lo3LFB3DSB3SLO3NER3PKB2HB5Ha_st5Hl_st2s1S1R5NEEDR2LF2ra2sp3PKA2bs2lo3LFB3DSP3SLO3NER3PKB2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2s03PKA2bs2lo3LFB3DSP3SLO3NER3PKB2HB5Ha_st5Hl_st2s1S2sp1B2bs3B47S2spS1R1C2lo3CAC4STKC3MCB1a1k2HkFS1R2lo3LOS3ALOS2LF3LFBS1R3HIA1h2sp2bs3TOPSS3PKA1C3DPC3DPMS2LF2ra2sp3PKA2bs3LFB3PKBS2LF2ra2sp3PKA2bs3LFB3PKBS2LF2ra2sp3PKA2bs3LFB3PKBS2LF2ra2sp3PKA2bs3LFB3PKBS2sp1C2bs3DMCS2sp1C3DMCS1R2sp2lo4STKC1a1k2HkS1R3HIA1h2bs1N3BUD2h23HV2S1R3HIA1h2bs1N2h23HV22h33HV3S1R3HIA1h1N1d2h24HFR22h34HFR3S1C3DMCS1CS2sp1C1B2bs3DBCS1C3DMCS2sp3PKA2lo3DSP3PKBS1R3HIA1h2bs1N3BUD6CKPHI0S1g1N2G12G22G32N0S2spFSS2LF2ra2sp3PKA2bs3LFB3PKBS1R1C3ACV2C03CACFS1R3HIA1h2sp3TOP4HTOPS1R2sp1C2lo3SPR3CAC4STKCS1R1C3ALO3CACS1R1C3ALO3CACS1CS2LF2ra2sp3PKA2bs3LFB3PKBS2LF2ra2sp3PKA2bs3LFB3PKBS2LF2ra2sp3PKA2bs3LFB3PKBS2LF2ra2sp3PKA2bs3LFB3PKBSS1R3HIA1h1N1d4BUDF2h24HFR2S1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA1h2sp2lo3TOP2h23HT25HTOP2S1R2sp2lo3SLOS1R1C3ALO3CACS2sp1C2bs3DMCS2sp1C3DMCSS1R3NS12LF2ra2sp3PKA2bs2lo3LFB3NZP3SLO3SPR3NES3PKBS1R3NS12LF2ra2sp3PKA2bs2lo3LFB3NZP3SLO3SPR3NES3PKBS1R5NEEDR2sp2lo3SLO3NERS1R3HIA1hS1R2LF2ra2sp3PKA2bs3LFB3PKBS1R2sp2lo2M24STKC3DHCS2LF2ra2sp3PKA2bs3LFB3PKBS2LF2ra2sp3PKA2bs3LFB3PKBS2spS2sp3PKA2lo3DSPS1R2sp2bs2lo3SLOS1R3NS12LF2ra2sp3PKA2bs2lo3LFB3NZP3SLO3SPR3NES3PKBS2LF2ra2sp3PKA2bs3LFB3PKBSS1R5NEEDR2sp2bs2lo3SLO3SPA3ACV3SPR3NER4STKCS1R2sp1C2bs2lo3SPR3CAC4STKCS1R3HIA1h2sp2lo1a2HaS1CS1R2M23DHCS1R1C3CACS2LF2ra2sp3PKA2bs3LFB3NZP3PKBS1R5NEEDR2sp2lo3slo3SLO4SLO23NERFS1R2sp1C2lo3SPR3CAC4STKCS1R3HIA5NEEDR1h2sp2lo3SLO3NER1a2HaS1R2lo3LOSS1CS2sp1B2bs2lo3DSBS1RS1R5NEEDR2sp2lo3LOS3SLO3SPR3NERS1C1e1KS1CFS1R2sp1C2bs2lo3SPR3CAC4STKCS1CFS1R1C3CACS2LF2ra2sp3PKA2bs3LFB3PKBS2LF2ra2sp3PKA2bs3LFB3PKBS2LF2ra2sp3PKA2bs3LFB3PKBS1r2RR2r02KT1q1HS2sp2r03SPA1q1r1H2H02q02H4S3PKA3DPMS1R3HIA1h2bs1N6CKPHI02h23HV2S1R3HIA1h1N1d5CKFR02h24HFR2S2sp3SPRS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3SPR3NERS1CS2LB4C24H3LB22Q22C12C3S1aS2sp1B2bs3B47S2LF2ra2sp3PKA2bs3LFB3PKBS1R3HIA1h1N1d4BUDF5CKFR0S1R3NS12LF2ra2sp3PKA2bs2lo3LFB3LOS3SLO3EHI3ALO3ACV3NES3PKB2HB5Ha_st5Hl_stS1R3NS12LF2sp2s03PKA2bs2lo3LFB3LOS3SLO3EHI3ALO3ACV3NES3PKB2HB5Ha_st5Hl_st2s1S1R3NS12LF2ra2sp3PKA2bs2lo3LFB3LOS3SLO3ALO3ACV3NES3PKB2HB5Ha_st5Hl_stS1R3NS12LF2sp2s03PKA2bs2lo3LFB3LOS3SLO3ALO3ACV3NES3PKB2HB5Ha_st5Hl_st2s1S1R3NS12LF2ra2sp3PKA2bs2lo3LFB3LOS3SLO3ALO3ACV3NES3PKB2HB5Ha_st5Hl_stS1R3NS12LF2sp2s03PKA2bs2lo3LFB3LOS3SLO3ALO3ACV3NES3PKB2HB5Ha_st5Hl_st2s1S2LF3PKA2bs3LFB3PKBS2LF2sp3PKA2bs2lo3LFB3PKBS2LF2sp3PKA2bs2lo3LFB3PKBS2LF2sp3PKA2bs2lo3LFB3PKBS1R2LF3PKA2bs3LFB3EHI3PKBFS2LF2ra2sp3PKA2bs3LFB3PKB2HB5Ha_st5Hl_stS2LF2sp2s03PKA2bs3LFB3PKB2HB5Ha_st5Hl_st2s1S1R3NS12LF2ra2sp3PKA2bs2lo3LFB3LOS3SLO3ALO3NES3PKB2HB5Ha_st5Hl_stS1R3NS12LF2sp2s03PKA2bs2lo3LFB3LOS3SLO3ALO3NES3PKB2HB5Ha_st5Hl_st2s1S1R2LF3PKA2bs3LFB3EHI3PKBS2LF2ra2sp3PKA2bs2lo3LFB3PKB2HB5Ha_st5Hl_stS2LF2sp2s03PKA2bs2lo3LFB3PKB2HB5Ha_st5Hl_st2s1FS1R3NS12LF2ra2sp3PKA2bs2lo3LFB3SLO3NES3PKB2HB5Ha_st5Hl_stS1R3NS12LF2sp2s03PKA2bs2lo3LFB3SLO3NES3PKB2HB5Ha_st5Hl_st2s1S1R2LF3PKA2bs3LFB5ALWF'3PKBS2LF3PKA2bs3LFB3PKBS2LF2sp3PKA2bs2lo3LFB3PKBS2LF2sp3PKA2bs2lo3LFB3PKBS2LF2sp3PKA2bs2lo3LFB3PKBS1R2LF3PKA2bs3LFB5ALWF'3PKBFS2LF2sp3PKA2bs3LFB3PKB2HBS2LF2sp3PKA2bs3LFB3PKB2HBFS1R3NS12LF2sp3PKA2bs2lo3LFB3SLO3NES3PKBS1R3NS12LF2sp3PKA2bs2lo3LFB3SLO3NES3PKBS1R3NS12LF2sp3PKA2bs2lo3LFB3SLO3NES3PKBS2LF3PKA2bs3LFB3PKBS1R2LF2ra2sp3PKA2bs3slo3LFB4SLO13PKB2HB5Ha_st5Hl_stS1R2LF2sp2s03PKA2bs3slo3LFB4SLO13PKB2HB5Ha_st5Hl_st2s1FS2LF2sp3PKA2bs3LFB3SPR3PKB2HB5Ha_stS2LF2sp3PKA2bs3LFB3SPR3PKB2HB5Ha_stS2LF2sp3PKA2bs2lo3LFB3PKBS2LF2sp3PKA2bs2lo3LFB3PKBS2LF2sp3PKA2bs2lo3LFB3PKBS2LF3PKA2bs3LFB3PKBS2LF3PKA2bs3LFB3PKBS1R2LF3PKA2bs3LFB5ALWF'3PKBS2LF3PKA2bs3LFB3PKBFFFFS2LF2ra2sp3PKA2bs3LFB3ALP3NZP3SPR3PKBS1R2LF3PKA2bs3LFB3ELO3PKBFS1R3HIA1h2LF2ra2sp3PKA2bs3slo3LFB3TOP4HTOP3PKB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2s03PKA2bs3slo3LFB3TOP4HTOP3PKB2HB5Ha_st5Hl_st2s1S1R3NS12LF2sp3PKA2bs2lo3LFB3SLO3NES3PKBS1R3NS12LF2sp3PKA2bs2lo3LFB3SLO3NES3PKBS1R3NS12LF2sp3PKA2bs2lo3LFB3SLO3NES3PKBS1R3NS12LF2ra2sp3PKA2bs2lo3LFB3SLO3NES3PKB2HB5Ha_st5Hl_stS1R3NS12LF2sp2s03PKA2bs2lo3LFB3SLO3NES3PKB2HB5Ha_st5Hl_st2s1S1R3NS12LF2sp3PKA2bs2lo3LFB3SLO3NES3PKBS1R3NS12LF2sp3PKA2bs2lo3LFB3SLO3NES3PKBS1R3NS12LF2sp3PKA2bs2lo3LFB3SLO3NES3PKB". (* [comment removed for export] *)
  #[using="IMG NEEDR NS1 RTCL HND HPRB HCPK"] Theorem A_pk_ecc_set_pubkey_spec_s : pk_ecc_set_pubkey_stmtA asegs R HIA MT A_PK_ECC_SET_PUBKEY A_MUL_COUNT A_BAD_POINTS.
  Proof.
    unfold pk_ecc_set_pubkey_stmtA, A_PK_ECC_SET_PUBKEY.
    intros until slo. intros HH HK0 LFB HPKA ALP NZP OPKA CRP DSP DPC DPM KP INC GF HBS B0 B47 CRB DSB DBC DBM OBS CNT MCOK DMC
           BP1 BP2 IM1 IM2 NZ1 NZ2 DBP ST LOS SLO SS SLO1 SLO2 TOP SPA TPV MI RA ND BUD UW BUDF C24H CKPHI0 CKFR0 GNC A0 A1 A2.
    subst a0 a1 a2. unfold ECP_KEYPAIR_SIZE in *.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (arl_need_ecp_rt R) as NER. pose proof (arl_need_ecp_smalloc R) as NES.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HBR HAP]. rewrite Forall_forall in HBR.
    destruct (HBR _ ltac:(apply in_app_iff; left; exact INC)) as (C0 & _ & CAC & _). cbn [fst snd] in C0, CAC.
    dpose KP as (HG & ED & MD & FD & HQ & FQ). cbn [kp_grp kp_d kp_Q] in HG, ED, MD, FD, HQ, FQ.
    assert (CAL : C mod 8 = 0) by (destruct HG as (_ & CAL & _); exact CAL).
    pose proof (rw_cells_bound _ _ _ _ HPKA) as PKB. cbn [cells_size csize Nat.add] in PKB.
    ddestruct IMG' as (EGOT & ELO & EHI).
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB. pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite EGOT in GOT.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    pose proof (conj HH (conj MI (conj HPKA (conj HBS (conj CNT (conj SS UW)))))) as BOX.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_MUL_COUNT in CNT.
    (* [comment removed for export] *)
    zstep. carve_frame 32%nat ST. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with M : mem_inv asegs m1 |- _ => rename M into MI1 end.
    match goal with W : wmono asegs m m1 |- _ => rename W into WM1 end.
    match goal with S : stk asegs m1 lo _ |- _ => rename S into ST1 end.
    match goal with H : HM asegs R HIA h LB LF m1 |- _ => rename H into HH1 end.
    match goal with H : sshad asegs AL m1 _ _ |- _ => rename H into SS1 end.
    ddestruct BOX as (HH0 & MI0 & HPKA0 & HBS0 & CNT0 & SS0 & UW0).
    assert (STKC : alloc_ceiling <= lo) by (clear - ACV ALO LOS; lia).
    assert (DJ : forall a k, a + k <= alloc_ceiling -> disjoint_from [(lo, bv_unsigned sp)] a k).
    { intros a k Hk. cbn. clear - Hk STKC. lia. }
    assert (GIN : forall e, In e (grp_mpds g) -> md_own e = LHeap -> In (md_p e, 4 * md_n e) LB /\ 1 <= md_n e).
    { intros e He O. ddestruct HG as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & _).
      assert (MDe : mpdr_at asegs m LB e) by (unfold grp_mpds, pt_mpds in He; cbn in He; destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption).
      ddestruct MDe as (_ & _ & _ & _ & _ & OW). rewrite O in OW. ddestruct OW as (N1 & EIN & _). split; [exact EIN| exact N1]. }
    assert (GCE : forall e, In e (grp_mpds g) -> md_own e = LHeap -> md_p e + 4 * md_n e <= alloc_ceiling).
    { intros e He O. destruct (GIN e He O) as [EIN _]. destruct (HBR _ ltac:(apply in_app_iff; left; exact EIN)) as (_ & _ & K & _). exact K. }
    assert (HG1 : ecp_group_at asegs MT m1 LB C g).
    { eapply ecp_group_at_munch; [exact HG| exact MU| exact WM1| exact MI0| exact MI1| apply DJ; clear - CAC; lia|].
      intros e He O. apply DJ. exact (GCE e He O). }
    assert (HQ1 : ecp_point_at asegs m1 LB (C + 208) (pt_init (C + 208) qX qY qZ)).
    { eapply ecp_point_at_munch; [exact HQ| exact MU| exact WM1| exact MI0| exact MI1| apply DJ; clear - CAC; lia|].
      cbn. intros e [<-|[<-|[<-|[]]]]; cbn; intros; discriminate. }
    assert (CNT1 : rw_cells asegs m1 A_MUL_COUNT [C8 cnt]).
    { eapply rw_cells_transport; [exact CNT0| exact MU| exact WM1|]. cbn. ddestruct MCOK as (_ & M2 & _). pose proof (art_data_lo asegs R HIA) as DHC. clear - M2 DHC STKC. lia. }
    assert (SPR1 : 0 <= bv_unsigned sp + -32 < 2^64) by (clear - SLO LOS ALO ACV SPR NEEDR NER; lia).
    dpose GF as (SGP & SGA & SGB & VP & NP5 & GIMG & GNLE & N0 & GKIND).
    pose proof (hm_aobj_block asegs R HIA h LB LF m1 C 256 HH1 INC) as OC1.
    assert (SS1' : sshad asegs AL m1 slo (bv_unsigned sp + -32)).
    { destruct (sshad_split asegs AL m1 slo (bv_unsigned sp + -32) (bv_unsigned sp) SS1 ltac:(clear - SLO SLO2 NER NEEDR; lia) ltac:(clear - SPA; Z.div_mod_to_equations; lia)) as [K _]. exact K. }
    assert (OBS1 : Z.of_nat (length bs) = 0 \/ aobj asegs AL (hcs asegs R HIA h) m1 B (Z.of_nat (length bs))).
    { destruct OBS as [E|O]; [left; exact E| right].
      eapply (aobj_munch asegs AL _ CSOK [(lo, bv_unsigned sp)] m m1); [constructor; [cbn [fst snd]; exact SCS| constructor]| exact MU| exact O]. }
    (* [comment removed for export] *)
    pose proof HPRB as SPR'. unfold ecp_point_read_binary_stmtA, A_ECP_POINT_READ_BINARY in SPR'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPR' with (h := h) (LB := LB) (LF := LF) (G := C) (Q := C + 208) (g := g) (p := pt_init (C + 208) qX qY qZ) (B := B) (bs := bs)
                       (N := N) (lo := lo) (d := 0) (slo := slo) (cnt := cnt);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by exact SPR1; rewrite ?(unsigned_lit C) by (clear - C0 CAC ACV ALO SPR LOS SLO NER NEEDR; lia);
        first [ exact HH1 | exact HK1 | exact LFB | exact HG1 | exact HQ1 | exact CNT1 | exact MCOK | exact ST1 | exact LOS | exact SS1' | exact SLO1
              | exact TPV | exact MI1 | exact GIMG | exact B0 | exact CRB | exact DBM | exact OBS1 | eassumption | reflexivity
              | lazymatch goal with
                | |- md_sg (g_P g) = 1 \/ _ => left; exact SGP
                | |- md_n (g_P g) <= N => exact (proj1 GNLE)
                | |- md_p (pt_X (g_G g)) <> 0 -> md_p (pt_Y (g_G g)) <> 0 -> _ =>
                    intros HX HY; destruct GKIND as [(K1 & _ & _)|(_ & _ & K2)]; [| exfalso; exact (HY K2)];
                    repeat (split; [assumption|]); exact GNLE
                | |- client_range _ _ _ C 192 => eapply client_range_block; [apply in_app_iff; left; exact INC| clear; lia| clear; lia]
                | |- client_wrange _ _ _ _ (C + 208) 48 => eapply client_wrange_block; [apply in_app_iff; left; exact INC| clear; lia| clear; lia]
                | |- aobj _ _ _ _ C 192 => eapply aobj_sub; [exact OC1| clear; lia| clear; lia]
                | |- aobj _ _ _ _ (C + 208) 48 => eapply aobj_sub; [exact OC1| clear; lia| clear; lia]
                | |- uw_obj _ _ _ _ => left; split; [clear - CAC ACV ALO; lia| clear; lia]
                | |- Forall (fun e => md_own e = LNull) _ => cbn; repeat constructor
                | |- Forall (fun e => md_sg e = 1 \/ md_sg e = -1) _ => cbn; repeat (constructor; [left; reflexivity|]); constructor
                | |- md_p (pt_X (g_G g)) <> 0 -> C + 208 + 48 <= C \/ _ => intros _; right; clear; lia
                | |- md_p (pt_X (g_G g)) <> 0 -> forall e, _ =>
                    intros _ e He O; destruct (GIN e He O) as [EIN N1];
                    pose proof (blocks_apart_in2 (LB ++ LF) (md_p e) (4 * md_n e) C 256 HAP ltac:(apply in_app_iff; left; exact EIN) ltac:(apply in_app_iff; left; exact INC) (GNC e He O)) as K;
                    clear - K N1; lia
                | |- uwc _ _ _ _ _ _ _ => apply uwc_data; [clear; lia| clear - C0 CAC ACV ALO; lia]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold pk_set_pubkey_PHI in BUD; clear - BUD CKPHI0; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold pk_set_pubkey_FR in BUDF; clear - BUDF CKFR0; lia
                | |- cnt24 LB + _ <= C24MAX => unfold C24_PK_SET_PUBKEY in C24H; clear - C24H; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- _ => clear - SLO SLO2 LOS NER NEEDR TOP SPA SPR CAC C0 ACV ALO DMC DBC DSB B47 B0 STKC; first [lia | Z.div_mod_to_equations; lia]
                end
              | match goal with |- ?gl => idtac "PRB-LEFT:" gl end ]. }
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    unfold ecp_point_read_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & Q2 & r & cnt2
                    & E2 & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & HQ2 & FQ2 & SGQ2 & DISQ2 & SZQ2 & INC2 & OUT2 & FRS2 & HG2 & CNT2 & NOG2 & RR).
    injection E2 as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, HP2 by exact SPR1.
    assert (MCB : A_MUL_COUNT + 8 <= alloc_ceiling).
    { ddestruct MCOK as (_ & M2 & _). pose proof (art_data_lo asegs R HIA) as DHC. clear - M2 DHC STKC ACV ALO. lia. }
    assert (DJW : forall a k, lo <= a -> disjoint_from [(C + 208, C + 208 + 48); (A_MUL_COUNT, A_MUL_COUNT + 8)] a k).
    { intros a k Hk. cbn. clear - Hk STKC CAC MCB. lia. }
    (* [comment removed for export] *)
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in FR; [| apply client_range_stack; clear; lia| apply DJW; clear - SLO NER NEEDR; lia].
    assert (HPKA1 : rw_cells asegs m1 PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)]).
    { eapply rw_cells_transport; [exact HPKA0| exact MU| exact WM1|]. cbn. cbn [cells_size csize Nat.add] in PKB. clear - DSP PKB. lia. }
    assert (HPKA2 : rw_cells asegs m2 PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)]).
    { eapply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2); [exact HPKA1| |].
      - eapply client_range_sep; [exact CRP| intros b Hb; exact Hb| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - DSP; lia].
      - cbn. clear - DPC DPM. lia. }
    assert (SS2 : sshad asegs AL m2 slo (bv_unsigned sp)).
    { eapply (presA_sshad asegs R); [exact HP2| exact SS1| exact SLO1| clear - HTOP TOP; lia]. }
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW0) as D0.
    assert (UW2 : uwc asegs m2 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_presA R); [exact HP2| | clear; lia| intros a Ha; eapply (disjoint_outside _ a 1); [apply DJW; clear - Ha SLO NER NEEDR; lia| clear; lia]| clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NER NEEDR; lia].
      eapply uwc_munch; [exact UW0| exact MU| clear - SPR; lia| (apply hstkhi_le64; clear - LOS SLO SPR NER NEEDR; lia)| intros a Ha; cbn [outside fst snd]; split; [clear - Ha; lia| exact I]]. }
    assert (HPX : presA asegs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(C + 208, C + 208 + 48); (A_MUL_COUNT, A_MUL_COUNT + 8)] m m2).
    { eapply presA_trans.
      - eapply presA_weaken; [exact (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PRES)| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I].
      - eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    assert (KP2 : ecp_keypair_at asegs MT m2 LB2 C (mkKP g (mpd_init (C + 192) pd) Q2)).
    { split; [exact HG2|]. split; [exact ED|]. split; [| split; [exact FD| split; [exact HQ2| exact FQ2]]]. cbn [kp_d].
      ddestruct MD as (MDc & MDal & MDpos & _). apply mpdr_at_init; [| exact MDal| exact MDpos].
      pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m m2 _ _ HPX MDc) as K. cbn [md_addr mpd_init] in K. apply K.
      - eapply client_range_block; [apply in_app_iff; left; exact INC| clear; lia| cbn; clear; lia].
      - cbn. clear - CAC MCB DMC. lia. }
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear CSOK SB64 SCS0 SCS. 
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (hcs_stack asegs R HIA h2) as SCS0. pose proof (hm_top asegs R HIA h2 LB2 LF m2 HH2) as HTOP2.
    assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP2 HT2 HS2; lia]).
    clear MU WM1 PRES.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT.
    2: { (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      release_frame FR ST2 (bv_unsigned sp).
      zstep.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold pk_ecc_set_pubkey_postA.
      deexists 14. dexists m2, mo9, h2, LB2, Q2, r, cnt2.
      split; [reflexivity|]. split; [exact RR|].
      split; [exact MI2|]. split; [assumption|]. split; [exact MF9|]. split; [exact HPX|].
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|]. split; [exact HCS2|].
      split; [unfold pk_set_pubkey_PHI; clear - HV2 CKPHI0; lia|]. split; [unfold pk_set_pubkey_FR; clear - HFR2 CKFR0; lia|].
      split; [exact HH2|]. split; [exact KP2|]. split; [exact SGQ2|]. split; [exact DISQ2|]. split; [exact SZQ2|].
      split; [exact INC2|]. split; [exact OUT2|]. split; [exact FRS2|]. split; [exact HPKA2| exact CNT2]. }
    (* [comment removed for export] *)
    assert (R0 : r = 0) by (clear - KT RR; Z.div_mod_to_equations; lia). subst r. clear KT.
    pose proof (SZQ2 eq_refl) as SZQ.
    pose proof (hm_aobj_block asegs R HIA h2 LB2 LF m2 C 256 HH2 (INC2 _ INC)) as OC2.
    assert (C24K : cnt24 LB2 + C24_ECP_CHECK_PUBKEY <= C24MAX).
    { pose proof (HND _ _ _ _ HH2) as ND2.
      assert (INCL : incl LB2 (pt_blocks Q2 ++ LB)) by (intros b Hb; apply in_or_app; destruct (OUT2 b Hb) as [K|K]; [right; exact K| left; exact K]).
      pose proof (cnt24_incl _ _ (NoDup_map_inv fst LB2 ND2) INCL) as C1. rewrite cnt24_app in C1.
      assert (C3 : cnt24 (pt_blocks Q2) <= 3).
      { etransitivity; [apply cnt24_le_length|]. unfold pt_blocks, pt_mpds, mpd_blk. cbn [flat_map].
        destruct (md_own (pt_X Q2)), (md_own (pt_Y Q2)), (md_own (pt_Z Q2)); cbn; clear; lia. }
      unfold C24_PK_SET_PUBKEY in C24H. clear - C1 C3 C24H. lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST2 (bv_unsigned sp).
    zstep.
    pose proof HCPK as SPC. unfold ecp_check_pubkey_stmtA, A_ECP_CHECK_PUBKEY in SPC.
    eapply aevtA_call.
    { intros mo3 [HK3 MF3].
      eapply SPC with (h := h2) (LB := LB2) (LF := LF) (G := C) (Q := C + 208) (g := g) (p := Q2) (cnt := cnt2) (bp1 := bp1) (bp2 := bp2)
                      (N := ecp_dy_sz N) (lo := lo) (d := d) (slo := slo);
        first [ exact HH2 | exact HK3 | exact HG2 | exact HQ2 | exact FQ2 | exact SGQ2 | exact SZQ | exact CNT2 | exact MCOK | exact IM1 | exact IM2 | exact NZ1 | exact NZ2 | exact DBP
              | exact LOS | exact SS2 | exact SLO1 | exact SLO2 | exact SPA | exact TPV | exact MI2 | exact RA | exact SGP | exact SGA | exact SGB | exact VP | exact GIMG | exact C24K
              | reflexivity
              | lazymatch goal with
                | |- (length LF + 3 <= 512)%nat => clear - LFB; lia
                | |- (g_h g = 1 /\ _) \/ _ => destruct GKIND as [K|(K1 & _ & K2)]; [left; exact K| right; split; assumption]
                | |- grp_nle g _ => ddestruct GNLE as (G1 & G2 & G3); unfold grp_nle, ecp_dy_sz, ecp_sz; clear - G1 G2 G3 N0; lia
                | |- client_range _ _ _ C 192 => eapply client_range_block; [apply in_app_iff; left; apply INC2; exact INC| clear; lia| clear; lia]
                | |- client_range _ _ _ (C + 208) 48 => eapply client_range_block; [apply in_app_iff; left; apply INC2; exact INC| clear; lia| clear; lia]
                | |- aobj _ _ _ _ C 192 => eapply aobj_sub; [exact OC2| clear; lia| clear; lia]
                | |- aobj _ _ _ _ (C + 208) 48 => eapply aobj_sub; [exact OC2| clear; lia| clear; lia]
                | |- uw_obj _ _ _ _ => left; split; [clear - CAC ACV ALO; lia| exact D0]
                | |- bad_point_ok _ _ _ A_BAD_POINTS _ =>
                    eapply (bad_point_any_mem R HIA h h2 LB LF LB2 LF m m2); [exact RTCL| exact HH0| exact HH2| exact MI0| exact MI2| exact BP1| left; reflexivity]
                | |- bad_point_ok _ _ _ (A_BAD_POINTS + 32) _ =>
                    eapply (bad_point_any_mem R HIA h h2 LB LF LB2 LF m m2); [exact RTCL| exact HH0| exact HH2| exact MI0| exact MI2| exact BP2| right; reflexivity]
                | |- stk _ _ _ _ => assumption
                | |- bv_unsigned sp <= htop _ _ _ _ => rewrite HT2; exact TOP
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold pk_set_pubkey_PHI in BUD; clear - BUD HV2; lia
                | |- uwc _ _ _ _ _ _ _ => rewrite HS2; exact UW2
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold pk_set_pubkey_FR in BUDF; clear - BUDF HFR2; lia
                | |- _ => clear - SLO SLO2 LOS NER NEEDR TOP SPA SPR CAC C0 ACV ALO DMC STKC MCB; first [lia | Z.div_mod_to_equations; lia]
                end
              | match goal with |- ?gl => idtac "CPK-LEFT:" gl end ]. }
    cbv beta. (intros ms' mo' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)). apply aevtS_now. unfold ecp_check_postA in PO.
    ddestruct PO as (z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m3 & mo4 & h3 & LB3 & r3 & cnt3
                    & E3 & MI3 & ST3 & MF4 & HP3 & HT3 & HS3 & HF3 & HK4 & HCS3 & HV3 & HFR3 & HH3 & LBEQ & HG3 & HQ3 & CNT3 & RR3).
    rewrite HS2 in HP3.
    unfold pk_ecc_set_pubkey_postA. dexists z0, z1, z2, za1, za2, za3, za4, za5, za6, za7, z3, z4, z5, z6, m3, mo4, h3, LB3, Q2, r3, cnt3.
    split; [exact E3|]. split; [exact RR3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact (mo_frame_trans _ _ _ MF3 MF4)|].
    split.
    { eapply presA_trans; [exact HPX|].
      eapply presA_weaken; [exact HP3| intros b Hb; apply INC2; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
      intros y Hy. cbn [outside fst snd] in Hy |- *. clear - Hy. tauto. }
    split; [rewrite HT3; exact HT2|]. split; [rewrite HS3; exact HS2|]. split; [rewrite HF3; exact HF2|]. split; [exact HK4|].
    split; [intros x Hx; apply HCS3, HCS2, Hx|].
    split; [unfold pk_set_pubkey_PHI; clear - HV2 HV3; lia|]. split; [unfold pk_set_pubkey_FR; clear - HFR2 HFR3; lia|].
    split; [exact HH3|].
    split.
    { ddestruct KP2 as (_ & _ & MD2 & _). cbn [kp_d] in MD2.
      split; [exact HG3|]. split; [exact ED|]. split; [| split; [exact FD| split; [exact HQ3| exact FQ2]]]. cbn [kp_d].
      ddestruct MD2 as (MDc & MDal & MDpos & _). apply mpdr_at_init; [| exact MDal| exact MDpos].
      pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3 MDc) as K. cbn [md_addr mpd_init] in K. apply K.
      - eapply client_range_block; [apply in_app_iff; left; apply INC2; exact INC| clear; lia| cbn; clear; lia].
      - cbn. clear - CAC MCB DMC. lia. }
    split; [exact SGQ2|]. split; [exact DISQ2|]. split; [intros _; exact SZQ|].
    split; [intros b Hb; apply LBEQ, INC2, Hb|]. split; [intros b Hb; apply OUT2, LBEQ, Hb|]. split; [exact FRS2|].
    split; [| exact CNT3].
    eapply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3); [exact HPKA2| |].
    - eapply client_range_sep; [exact CRP| | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; exact DSP].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply INC2; exact Hb| right; exact Hb].
    - cbn. clear - DPM. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WalkSP.

Theorem A_pk_ecc_set_pubkey_spec : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_pubkey ()) "PR,$76.PHIA,(77.$78.R1.)PMT,(19.$7<.)P,(7=.(51.R3.))P,(7.=(7>.R4.))P,(7.=(7?.R5.))P,Pm,P,(15.&40.)(16.(15.&8.))P,(79.R7.R1.)(7:.R2.)P,Ph,(18.$78.R7.R6.)PLB,(19.$1:.)PLF,(19.$1:.)Pm,P,(15.&40.)(16.(15.&8.))P,(3:.$78.R;.R:.R4.R3.R2.R1.)(66.$2.(67.(2>.$2.$2.)$2.(45.$2.$2.)R4.))P,(80.$78.R8.R7.R6.$81.$82.)P,(83.$78.R9.R8.R7.$84.$82.$7;.)(85.$78.R:.R9.R8.$86.$82.$7;.)")
(* [comment removed for export] *).
Proof. intros. eapply A_pk_ecc_set_pubkey_spec_s; eassumption. Qed.
