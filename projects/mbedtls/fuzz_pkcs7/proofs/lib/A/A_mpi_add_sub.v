(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_journey
     A_mpi_add_abs_W A_mpi_sub_abs.
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
Ltac2 gd_tbl_A_mpi_add_sub () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.A.AImg.asegs"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sgn"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.P.P_mpi_cmp.SIGF"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.A.AImgGlobals.img_norz"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpi_binop_postA"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.P.P_mpi_addsub.add_sub_mpi_R"; "add_sub_PHI"; "add_sub_FR"; "OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.A.A_mpi_journey.XJA"; "WAS.AS_FRAME_A"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "WAS.AS_VAL_A"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "WAS.AS_POST_A"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Spec.MpiVal.mpd_abs"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.A.A_mpi_opnd.opnd_atA"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_aobjA"; "OSSVerify.KrLib.LibA.ARt.hcs"; "WAS.at1"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_ADD_SUB_MPI"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_writableA"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.Spec.Rep.LNull"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "OSSVerify.KrLib.LibA.ARt.arl_tp"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.A.A_alloc_lib.uw_obj"; "OSSVerify.KrLib.LibA.ARt.hfr"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CmpWalkA.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (raj sp' gp tp t2 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (X Aa pA nA : Z) (ys : list word) (sAw padA : word).
  Variables (Ba pB nB : Z) (zs : list word) (sBw padB : word).
  Hypothesis CEA : rw_cells asegs m Aa [C8 (Z_to_bv 64 pA); C2 sAw; C2 (Z_to_bv 64 nA); C4 padA].
  Hypothesis HA : bytes_at asegs m pA (u32s ys).
  Hypothesis LA : Z.of_nat (length ys) = nA.
  Hypothesis HnA : 0 <= nA <= 10000.
  Hypothesis ABD : 0 <= Aa /\ Aa + 16 <= 2^64.
  Hypothesis PAB : nA = 0 \/ 0 < pA /\ pA mod 4 = 0.
  Hypothesis ALA : Aa mod 8 = 0.
  Hypothesis OAS : aobj asegs AL CS m Aa 16.
  Hypothesis OAL : 1 <= nA -> aobj asegs AL CS m pA (4 * nA).
  Hypothesis PABB : 0 <= pA /\ pA + 4 * nA <= 2^64.
  Hypothesis CEB : rw_cells asegs m Ba [C8 (Z_to_bv 64 pB); C2 sBw; C2 (Z_to_bv 64 nB); C4 padB].
  Hypothesis HB : bytes_at asegs m pB (u32s zs).
  Hypothesis LB_ : Z.of_nat (length zs) = nB.
  Hypothesis HnB : 0 <= nB <= 10000.
  Hypothesis BBD : 0 <= Ba /\ Ba + 16 <= 2^64.
  Hypothesis PBB : nB = 0 \/ 0 < pB /\ pB mod 4 = 0.
  Hypothesis ALB : Ba mod 8 = 0.
  Hypothesis OBS : aobj asegs AL CS m Ba 16.
  Hypothesis OBL : 1 <= nB -> aobj asegs AL CS m pB (4 * nB).
  Hypothesis PBBB : 0 <= pB /\ pB + 4 * nB <= 2^64.
  Hypothesis MI : mem_inv asegs m.

  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHAa := (Z_to_bv 64 (Z.shiftr Aa 3 + al_sb AL)).
  Notation SHBa := (Z_to_bv 64 (Z.shiftr Ba 3 + al_sb AL)).

  (* [comment removed for export] *)
  Definition cmpw_postA (c : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Lms',$0.(1.(2.&40.)Ly0,(2.&40.)(1.(2.&40.)Ly1,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lw,(2.&40.)(1.$3.Lpc,$3.(4.(5.$0.R;.(6.(7.Vraj,Vsp',Vgp,Vtp,R:.R9.Vt2,(8.&40.VX,)(8.&40.(9.VAL,))R8.(8.&40.VAa,)(8.&40.VBa,)R7.R6.R5.R4.R3.R2.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.R1.)Vfc,(:.(2.&40.))Vm,(;.$<.)))(=.(4.(5.$3.R1.+9>598.)(=.(4.(5.$3.O1.+1.)(5.(2.&40.)R2.Vs2v,))(4.(5.$3.O1.=)(5.(2.&40.)R2.(8.&40.+1.)))))(4.(5.$3.R1.+9>5:<.)(4.(5.$3.O1.-1.)(5.(2.&40.)R2.Vs2v,)))))))))))))))")
(* [comment removed for export] *).

  Let CMP := Z.sgn (lval ys nA - lval zs nB).
  Let POST := cmpw_postA CMP.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Local Ltac done_at := apply evtA_done; subst POST; unfold cmpw_postA; deexists 10; split; [reflexivity|].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0130?L11014201954.11L11014201954.12L11014202083.11L11099433098.2 L14559281462.3 L16256852529.91L1966108301.11 L21734020596.3 L21743477688.1 L23355682316.11L23917405863.3 L25572164514.12L28082334664.88L28084074302.91L29010565666.77L35193647827.5 L36571201320.0 L38538042510.91L38540248044.94L54425655282.3 L54425655405.4 L56840611386.1 L59308546259.3 L59308551419.8 L59308551544.8 L59308628179.4 L59435147825.89L64709271574.2 L66151418440.3 L68009313513.5 Q10558331632.93Q10558798004.92Q10869101314.96Q12540582640.91Q14488277007.93Q15157415951.91Q15282990891.92Q16331225058.91Q18803472354.93Q19475995813.93Q26295627581.93Q26295627581.96Q26710966465.93Q26710966465.95Q26713475008.90Q32577269584.91Q33229631312.93Q35195261215.90Q3604969708.91 Q36868470712.95Q36886229090.96Q37692421331.90Q39400329406.93Q43320303283.92Q46622226668.93Q49024560195.95Q50458135125.93Q50458135125.96Q52823721877.95Q52823721878.93Q52825981699.96Q60160662256.91Q60162712396.90Q6630548121.93 Q68395763019.90Q8945554086.90 Q8945570098.93 00000>00L00Z00`00j01N01m02602902X02`03B04:05205_05m05n06k07h08008808;08L08c09<09G09k0:10::0:I0:d0;?0;e0;f0;g0;h0<C0<^0=90=]0>50>M0>k0?I0?g0?h0?i0@J0A60AX0B;0BV0C80CS0DH0Di0ED0E_0F=0F[0G90GT0Go0HR0Hm0IE0I]S1k1r2Hk2wx2wyS1k1r2Hk2wx2wyS1k1r2Hk2wx2wyS2pA1rS2nB1r3Rn'S2Aa2pA2nA2ys2Ba2pB2nB2zs3CMP1k1r2HkS2ys2zs1k1r2Hk2wx2wy3LXr3LYr2K1S2nA1r2RnS1rS2ys2zs1k1r2Hk2wx2wy3LXr3LYr2K2S1k1r2HkS2ys2zs1k1r2Hk2wx2wy3LXr3LYr2K12K2S2Aa2pA2nA2ys2Ba2pB2nB2zs3ABD4PABB3BBD4PBBB1k1r2Hk2Rn2PPS2Aa2pA2nA2ys2Ba2pB2nB2zs3ABD4PABB3BBD4PBBB1k1r2Hk2Rn2PPS2Aa2pA2nA2ys2Ba2zs3ABD4PABB3BBD1k1r2Hk2Hr2RnS2nA1k1r2Hk2RnSS2Aa2pA2nA2ys2Ba2pB2nB2zs3ABD4PABB3BBD4PBBB1k1r2Hk3Rn'3N1'2QPS2Aa2pA2nA2ys2Ba2pB2nB2zs3ABD4PABB3BBD4PBBB1k1r2Hk3Rn'3N1'2QPS1k1r2HkS1k1r2HkS1rS2nA2N12N02nB3N1'S2nA2ys2LA1k1r2Hk2Rn2NXS2nB2zs3LB_1k1r2Hk3Rn'2NYS1k1r2Hk2K0S2Aa2pA2nA2ys2Ba2pB2nB2zs3CMP1k1r2HkS2pB1rS1r2Hk2HrS2nB1k1r2Hk3Rn'S2nA2ys2Ba2nB2zs3CMP1k1r2HkS2nA2ys2Ba2nB2zs3CMP1k1r2HkS2nA2ys2pB2nB2zs3CMP1k1r2Hk3Rn'2HT3N1'FFFS2nA2ys2Ba2nB2zs3CMP1k1r2HkS2Aa2nA2ys2nB2zs3CMP1k1r2HkS2nA2ys2Ba2nB2zs3CMP1k1r2HkS2pA2nA2ys2nB2zs3CMP1k1r2Hk2Rn2HT2N1S2nA2ys2nB2zs3CMP1k1r2HkS2nA2ys2nB2zs3CMP1k1r2HkS2pA2nA2ys2nB2zs3CMP1k1r2Hk2HTS2pA2nA2ys2nB2zs3CMP1k1r2Hk2HTS2pA2nA2ys2nB2zs3CMP1k1r2Hk2HTFFS2pA2nA2ys2nB2zs3CMP1k1r2Hk2Rn2HTS2Aa2pA2nA2ys2Ba2pB2nB2zs3ABD3ALA3CMP1k1r2HkS2nA2ys2pB2nB2zs3CMP1k1r2Hk3Rn'2HTS2nA2ys2pB2nB2zs4PBBB3CMP1k1r2Hk2HTS2Aa2nA2ys2nB2zs3CMP1k1r2HkS2nA2ys2pB2nB2zs3CMP1k1r2Hk3Rn'2HTS2nA2ys2Ba2nB2zs3CMP1k1r2HkS2Aa2pA2nA2ys2Ba2pB2nB2zs3ABD3BBD3ALB4PBBB3CMP1k1r2HkS2pA2nA2ys2nB2zs3CMP1k1r2Hk2Rn2HTS2pA2nA2ys2nB2zs3CMP1k1r2HkS2nA2ys2pB2nB2zs3CMP1k1r2HkS2nA2ys2pB2nB2zs3CMP1k1r2Hk2HTS2nA2ys2pB2nB2zs3CMP1k1r2Hk2HTS2nA2ys2pB2nB2zs3CMP1k1r2Hk2HTS2Aa2nA2ys2nB2zs3CMP1k1r2HkS2Aa2nA2ys2nB2zs3CMP1k1r2HkS2pA2nA2ys2nB2zs4PABB3CMP1k1r2Hk2HTS2Aa2nA2ys2nB2zs3CMP1k1r2HkS2nA2ys2nB2zs3CMP1k1r2HkS2nA2ys2nB2zs3CMP1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK pA sAw padA pB sBw padB CEA HA LA ABD PAB ALA OAS OAL PABB CEB HB LB_ BBD PBB ALB OBS OBL PBBB"] Lemma c_loop3 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pk,$>.Pr,$3.Pw14,(2.&40.)Pw15,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxa0,(2.&40.)Pxa3,(2.&40.)P,(5.$>.(?.R7.)R8.)P,(10.=R8.)P,(10.R9.VnA,)P,(10.R:.VnB,)P,(5.$3.VCMP,(11.(12.(13.Vys,R;.)(13.Vzs,R;.))))P,(5.(2.&40.)R;.(8.&40.(14.R<.+1.)))P,(5.(2.&40.)R;.(8.&40.(12.(15.+4.R=.)+4.)))(16.$<.VAL,VCS,VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,R;.R:.Vt2,(8.&40.VX,)(8.&40.(9.VAL,))R9.(8.&40.VAa,)(8.&40.VBa,)R8.R=.R<.(8.&40.(14.(17.VAa,+3.)(9.VAL,)))(8.&40.(14.(17.VBa,+3.)(9.VAL,)))Vs2v,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+9>618.)Vfc,(:.(2.&40.))Vm,(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w14 w15 xt0 xt1 xa0 xa3 Hk Hr Rn Rn' HT -> ->; al_facts.
    - assert (r = 0) as -> by (clear - Hk Hr; lia).
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      done_at. left. split; [reflexivity|]. right. split; [| reflexivity]. rewrite HT, !lval_0. reflexivity.
    - zstep. zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - Hk Hr Rn HnA; lia); clear - K0 Hk; lia|]. clear K0.
      destruct (nth_error ys (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX Rn LA Hk; lia].
      destruct (nth_error zs (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; exfalso; clear - NY Rn' LB_ Hk; lia].
      assert (N1 : 1 <= nA) by (clear - Hk Rn; lia). assert (N1' : 1 <= nB) by (clear - Hk Rn'; lia).
      pose proof (OAL N1) as OPn. pose proof (OBL N1') as OQn.
      destruct PAB as [N0|[PP PAL]]; [exfalso; clear - N0 N1; lia|]. destruct PBB as [N0|[QP QAL]]; [exfalso; clear - N0 N1'; lia|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OPn (pA + (4 * r - 4)) 4.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      pose proof (u32ro_read asegs m pA ys (r - 1) wx _ HA NX ltac:(clear - Hk Hr; lia) eq_refl) as RDX.
      replace (pA + 4 * (r - 1)) with (pA + (4 * r - 4)) in RDX by (clear; lia).
      zstep. zstep. shadow_chk OQn (pB + (4 * r - 4)) 4.
      clear RDX.
      (* [comment removed for export] *)
      pose proof (u32ro_read asegs m pB zs (r - 1) wy _ HB NY ltac:(clear - Hk Hr; lia) eq_refl) as RDY.
      replace (pB + 4 * (r - 1)) with (pB + (4 * r - 4)) in RDY by (clear; lia).
      zstep. clear RDY.
      pose proof (limb32_of_read ys r wx NX) as LXr. pose proof (limb32_of_read zs r wy NY) as LYr.
      pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(clear; lia)) as Bx.
      pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(clear; lia)) as By.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
      + apply (proj1 (sxz_lt_iff _ _ By Bx)) in K1.
        done_at. left. split; [reflexivity|]. left. split; [| reflexivity]. rewrite HT. apply (cmp_step_gt ys zs r); clear - K1 LXr LYr Hk Hr; lia.
      + apply (proj1 (sxz_le_iff _ _ Bx By)) in K1.
        (* [comment removed for export] *)
        zstep. zstep. if_cases K2; zify_cond K2; rewrite ?bv_unsigned_sx32 in K2.
        * apply (proj1 (sxz_le_iff _ _ By Bx)) in K2.
          eapply (IH (r - 1)); [clear - Hk; lia| clear - Hk; lia| clear - Rn; lia| clear - Rn'; lia| rewrite HT; apply (cmp_step_eq ys zs r); clear - K1 K2 LXr LYr Hk Hr; lia| f_equal; clear; lia| f_equal; clear; lia].
        * apply (proj1 (sxz_lt_iff _ _ Bx By)) in K2.
          (* [comment removed for export] *)
          zstep.
          done_at. right. split; [reflexivity|]. split; [| reflexivity]. rewrite HT. apply (cmp_step_lt ys zs r); clear - K2 LXr LYr Hk Hr; lia.
    all: match goal with |- ?g => idtac "LOOP3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0?L10351590514.3 L10357722005.79L10907032063.3 L13149012510.5 L2011573810.5  L23444480699.3 L27601760771.4 L32954672704.82L32954672833.81L39172636981.0 L44872450572.3 L45272779239.3 L51166956437.79L51196083649.1 L63517917270.3 L66253296149.79L66253710909.81L66253711036.8200000900L00T00d01401=01H01o02V02W02_02h03;03>03G03l04S05:S2nA1i2I1S2Aa2ys2Ba2zs3BBD1iS1i1j2K2S2nA2ys2nB2zs2LTS2nA2ys2nB2zs2LTS2nA1i2I1S1i1j2K12K2S2Aa2ys2Ba2pB2nB2zs3ABD3BBD4PBBB1i1j2J1S2Aa2ys2Ba2pB2nB2zs3ABD3BBD4PBBB1i1j2J1SS1i1j2K1S2nB1j2J1S2Aa2ys2Ba2zs3ABD1iS1iS2nB1i2J1S2Aa2pA2nA2ys2Ba2zs3ABD4PABB3BBD1i2I1S2Aa2pA2nA2ys2Ba2zs3ABD4PABB3BBD1i1j2I1S2Aa2pA2nA2ys2Ba2zs3ABD4PABB3BBD1i1j2I1". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK pA sAw padA pB sBw padB CEA HA LA ABD PAB ALA OAS OAL PABB CEB HB LB_ BBD PBB ALB OBS OBL PBBB"] Lemma c_decide : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pi,$3.Pj,$3.Pxt0,(2.&40.)Pxt1,(2.&40.)Pxa0,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)P,(18.Vys,VnA,R8.)P,(18.Vzs,VnB,R8.)(16.$<.VAL,VCS,VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,R8.R7.Vt2,(8.&40.VX,)(8.&40.(9.VAL,))R6.(8.&40.VAa,)(8.&40.VBa,)(8.&40.R:.)(8.&40.R9.)R5.R4.R3.Vs2v,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+9>594.)Vfc,(:.(2.&40.))Vm,(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros i j xt0 xt1 xa0 xa5 xa6 xa7 SX SY. al_facts. dpose SX as (I1 & I2 & I3). dpose SY as (J1 & J2 & J3).
    pose proof (lval_range ys i ltac:(clear - I1; lia)) as RX. pose proof (lval_range zs j ltac:(clear - J1; lia)) as RY.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - I1 J1 HnA HnB; lia).
    2:{ (* [comment removed for export] *)
        done_at. left. split; [reflexivity|]. left. split; [| reflexivity]. unfold CMP. apply Z.sgn_pos.
        pose proof (SIGF_lt ys nA i zs nB j SX SY ltac:(clear - K1; lia)) as LT. clear - LT. lia. }
    (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - I1 J1 HnA HnB; lia).
    2:{ (* [comment removed for export] *)
        done_at. right. split; [reflexivity|]. split; [| reflexivity]. unfold CMP. apply Z.sgn_neg.
        pose proof (SIGF_lt zs nB j ys nA i SY SX ltac:(clear - K2; lia)) as LT. clear - LT. lia. }
    assert (j = i) as -> by (clear - K1 K2; lia). clear K1 K2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    eapply (c_loop3 (Z.to_nat i) i); [reflexivity| clear - I1; lia| clear - I1; lia| clear - J1; lia| | f_equal; clear; lia| f_equal; clear; lia].
    unfold CMP. rewrite I2, J2. reflexivity.
    all: match goal with |- ?g => idtac "DECIDE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L11014210082.3 L13036769295.4 L23917405863.3 L23970764156.89L27579353874.4 L31326834835.4 L36571201320.0 L37985911552.2 L38540224293.83L38540248044.86L54425655405.3 L59308546259.3 L59308551544.6 L59308587409.4 L59904662719.2 L64709271574.2 L64930767917.4 L66607628735.3 L68007316146.3 Q10869101314.88Q26295627581.88Q36868470712.88Q36886229090.88Q39398648597.85Q50458135125.88Q52823721877.88Q52825981699.88Q52826012733.85Q8943594137.85 00000900E00M01=01>01J01K01Q02;02e02n03903L03X03`03f04204;04D04b05:05X06;06Y07407R08008N08fS2nB1r2HrS2nB1r2Hr2K2S1k1r2HkS2Aa2ys2Ba2pB2nB2zs3ABD3BBD4PBBB1k1r2Hk2Hr2QP2wyFS2nB1r2Hr2K2SS2pB1rS2Aa2ys2Ba2pB2nB2zs3ABD3BBD4PBBB1k1r2Hk2HrS2Aa2ys2Ba2pB2nB2zs3ABD3BBD4PBBB1k1r2Hk2HrS2nB1r2HrS2nB3N1'2N0S2nB2zs3LB_1r2Hr2NYS2nB1r2Hk2HrS2nB3HnBS2pB1rS2nB1r2Hr2K2S2nB1r2HrS2nB1r2HrS2nA2ys2pB2nB2zs3CMP1k1r2Hk2HrS2nA2ys2nB2zs3CMP1k1r2HkS2nA2ys2pB2nB2zs3CMP1k1r2Hk2HrS2nA2ys2pB2nB2zs4PBBB3CMP1k1r2Hk2HrS2nA2ys2pB2nB2zs3CMP1k1r2Hk2HrS2nA2ys2pB2nB2zs3CMP1k1r2HkS2nA2ys2pB2nB2zs3CMP1k1r2Hk2HrS2nA2ys2pB2nB2zs3CMP1k1r2Hk2HrS2nA2ys2pB2nB2zs3CMP1k1r2Hk2HrS2nA2ys2nB2zs3CMP1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK pA sAw padA sBw padB CEA HA LA ABD PAB ALA OAS OAL PABB CEB HB LB_ HnB BBD PBB ALB OBS OBL PBBB"] Lemma c_loop2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pk,$>.Pi,$3.Pr,$3.Pw,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)P,(5.$>.(?.R6.)R8.)P,(4.(10.+1.R7.)(10.R7.VnB,))P,(18.Vys,VnA,R9.)P,(5.$3.(13.Vzs,VnB,)(13.Vzs,R9.))P,(5.(2.&40.)R9.(8.&40.(14.VpB,(12.(15.+4.R:.)+4.))))(16.$<.VAL,VCS,VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,R9.R8.Vt2,(8.&40.VX,)(8.&40.(9.VAL,))R:.(8.&40.VAa,)(8.&40.VBa,)(8.&40.R<.)(8.&40.R;.)R:.R7.R6.Vs2v,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+9>558.)Vfc,(:.(2.&40.))Vm,(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i r w xt0 xt1 xa6 xa7 Hk Hr SX INV ->; [exfalso; clear - Hk Hr; lia|]. al_facts.
    assert (N1' : 1 <= nB) by (clear - Hr; lia). pose proof (OBL N1') as OQn.
    destruct PBB as [N0|[QP QAL]]; [exfalso; clear - N0 N1'; lia|].
    destruct (nth_error zs (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; exfalso; clear - NY Hr LB_; lia].
    dpose SX as (I1 & _ & _).
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OQn (pB + (4 * r - 4)) 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs m pB zs (r - 1) wy _ HB NY ltac:(clear - Hr; lia) eq_refl) as RDY.
    replace (pB + 4 * (r - 1)) with (pB + (4 * r - 4)) in RDY by (clear; lia).
    zstep. clear RDY. pose proof (limb32_of_read zs r wy NY) as LYr.
    pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(clear; lia)) as By.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - (* [comment removed for export] *)
      assert (NZ : limb32 zs (Z.to_nat (r - 1)) <> 0) by (rewrite LYr; intros E; apply K1; rewrite E; reflexivity).
      apply c_decide; [exact SX|]. split; [clear - Hr; lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [clear - Hr; lia| exact NZ].
    - (* [comment removed for export] *) apply (proj1 (sxz_zero_iff _ By)) in K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - Hr HnB; lia).
      + eapply (IH i (r - 1)); [clear - Hk; lia| clear - Hr K2; lia| exact SX| rewrite INV; apply lval_drop_zero; [clear - Hr; lia| rewrite LYr; exact K1]| f_equal; clear; lia].
      + (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; clear - K2 Hr; lia).
        apply c_decide; [exact SX|]. split; [clear - HnB; lia|]. split; [| left; reflexivity].
        rewrite INV, (lval_drop_zero zs r) by (first [clear - Hr; lia | rewrite LYr; exact K1]). replace (r - 1) with 0 by (clear - K2 Hr; lia). reflexivity.
    all: match goal with |- ?g => idtac "LOOP2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L10359834498.79L16256852529.80L37988080496.2 L39172636981.0 L43662869054.79L43665079170.77L47219663280.2 L50136544034.2 L56381107161.74L56381132560.77L59904662719.2 L65775916289.3 Q10558331632.82Q10560447308.81Q15280256211.81Q18787540591.78Q18788156054.79Q18788187560.76Q18803472354.82Q25961452344.79Q27526241100.76Q28640013309.79Q39212284437.79Q43322869067.81Q46622226668.82Q52486639926.78Q60511567613.79Q9538497017.76 00000D00^00e00f01=01Q01Y01`02102B02J02U02i03=03Q03e04904M04a05905M05a06506I07407H07Y07jS2Aa2ys2Ba2pB2zs3BBDS2Aa2nA2ys2Ba2pB2nB2zs3CMPS2pB2nBSS2Aa2ys2Ba2pB2nB2zs3HnBS2Aa2ys2Ba2nB2zs3HnBS2nB3HnBS2nB2K0S2Aa2ys2Ba2zs3BBDS2Aa2ys2Ba2zs3BBDS2nB3HnBS2nB3HnB2K0S2nA2ys2Ba2nB2zs3CMPS2nA2ys2Ba2nB2zs3CMPS2nA2ys2Ba2nB2zs3CMPS2nA2ys2Ba2nB2zs3CMPS2nA2ys2Ba2nB2zs3CMPS2nA2ys2Ba2nB2zs3CMPS2nA2ys2Ba2nB2zs3CMPS2nA2ys2Ba2nB2zs3BBD3CMPS2nA2ys2Ba2nB2zs3CMPS2nA2ys2Ba2nB2zs3CMPS2nA2ys2Ba2nB2zs3CMPS2nA2ys2Ba2nB2zs3CMPS2Aa2nA2ys2Ba2pB2nB2zs3ABD3BBD3ALB4PBBB3CMPS2nA2ys2Ba2nB2zs3CMPS2nA2ys2nB2zs3CMPS2nA2ys2nB2zs3CMP". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK pA sAw padA pB sBw padB CEA HA LA ABD PAB ALA OAS OAL PABB CEB HB LB_ HnB BBD PBB ALB OBS OBL PBBB"] Lemma c_stage2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pi,$3.Pxt0,(2.&40.)Pxt1,(2.&40.)Pxa0,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)P,(18.Vys,VnA,R8.)(16.$<.VAL,VCS,VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,R8.R7.Vt2,(8.&40.VX,)(8.&40.(9.VAL,))R6.(8.&40.VAa,)(8.&40.VBa,)(8.&40.R9.)R5.R4.R3.R2.Vs2v,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+9>518.)Vfc,(:.(2.&40.))Vm,(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros i xt0 xt1 xa0 xa4 xa5 xa6 xa7 SX. al_facts. dpose SX as (I1 & _ & _).
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OBS (Ba + 10) 2.
    (* [comment removed for export] *)
    zstep. rewrite zx16_small by (clear - HnB; lia).
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - HnB; lia).
    - (* [comment removed for export] *) replace (Z_to_bv 64 nB) with (Z_to_bv 64 0) by (f_equal; clear - K0; lia).
      apply c_decide; [exact SX|]. split; [clear - HnB; lia|]. split; [rewrite K0; reflexivity| left; reflexivity].
    - destruct PBB as [N0|[QP QAL]]; [exfalso; exact (K0 N0)|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      eapply (c_loop2 (Z.to_nat nB) i nB); [reflexivity| clear - K0 HnB; lia| exact SX| reflexivity| f_equal; clear; lia].
    all: match goal with |- ?g => idtac "STAGE2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L11014210082.3 L11099433098.2 L15636317532.2 L1962756882.4  L23917405863.3 L23970764156.87L28084074302.84L28084119132.81L31024398201.2 L31326834835.4 L35193552079.3 L36571201320.0 L49887308664.3 L54425655405.3 L59308546259.3 L59308551419.6 L59308587409.4 L64912137160.4 L64930767917.4 Q19475995813.86Q26295627581.86Q26710936148.83Q26710966465.86Q26713490516.86Q35197213835.83Q49026296022.86Q50458135125.86Q6630548121.86 Q8943673138.83 00000900?00E00F00N01>01h02R02Z02f02o03003903B03L03^03j04604B04`05805V06406R07007N07i08L08dS2nA1r2HrS2pA1rS2pA1rFS1k1r2HkS2Aa2pA2nA2ys2Ba2zs3ABD4PABB3BBD1k1r2Hk2Hr2PP2wxS2Aa2pA2nA2ys2Ba2zs3ABD4PABB3BBD1k1r2Hk2HrS2Aa2pA2nA2ys2Ba2zs3ABD4PABB3BBD1k1r2Hk2HrS2nA3HnAS2nA1r2Hr2K2S2nA1r2HrSS2nA1r2HrS2nA1r2HrS2nA2N12N0S2nA2ys2LA1r2Hr2NXS2nA1r2Hk2HrS2nA1r2Hr2K2S2nA1r2Hr2K2S2pA2nA2ys2nB2zs3CMP1k1r2Hk2HrS2nA2ys2nB2zs3CMP1k1r2HkS2pA2nA2ys2nB2zs3CMP1k1r2Hk2HrS2pA2nA2ys2nB2zs3CMP1k1r2Hk2HrS2pA2nA2ys2nB2zs3CMP1k1r2Hk2HrS2pA2nA2ys2nB2zs3CMP1k1r2Hk2HrS2pA2nA2ys2nB2zs3CMP1k1r2Hk2HrS2pA2nA2ys2nB2zs3CMP1k1r2HkS2pA2nA2ys2nB2zs4PABB3CMP1k1r2Hk2HrS2nA2ys2nB2zs3CMP1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK sAw padA pB sBw padB CEA HA LA HnA ABD PAB ALA OAS OAL PABB CEB HB LB_ HnB BBD PBB ALB OBS OBL PBBB"] Lemma c_loop1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pk,$>.Pr,$3.Pw,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)P,(5.$>.(?.R7.)R8.)P,(4.(10.+1.R8.)(10.R8.VnA,))P,(5.$3.(13.Vys,VnA,)(13.Vys,R9.))P,(5.(2.&40.)R9.(8.&40.(14.VpA,(12.(15.+4.R:.)+4.))))(16.$<.VAL,VCS,VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,R9.R8.Vt2,(8.&40.VX,)(8.&40.(9.VAL,))R:.(8.&40.VAa,)(8.&40.VBa,)(8.&40.R;.)R:.R7.R6.R5.Vs2v,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+9>4=<.)Vfc,(:.(2.&40.))Vm,(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w xt0 xt1 xa5 xa6 xa7 Hk Hr INV ->; [exfalso; clear - Hk Hr; lia|]. al_facts.
    assert (N1 : 1 <= nA) by (clear - Hr; lia). pose proof (OAL N1) as OPn.
    destruct PAB as [N0|[PP PAL]]; [exfalso; clear - N0 N1; lia|].
    destruct (nth_error ys (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX Hr LA; lia].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OPn (pA + (4 * r - 4)) 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs m pA ys (r - 1) wx _ HA NX ltac:(clear - Hr; lia) eq_refl) as RDX.
    replace (pA + 4 * (r - 1)) with (pA + (4 * r - 4)) in RDX by (clear; lia).
    zstep. clear RDX. pose proof (limb32_of_read ys r wx NX) as LXr.
    pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(clear; lia)) as Bx.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - (* [comment removed for export] *)
      assert (NZ : limb32 ys (Z.to_nat (r - 1)) <> 0) by (rewrite LXr; intros E; apply K1; rewrite E; reflexivity).
      apply c_stage2. split; [clear - Hr; lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [clear - Hr; lia| exact NZ].
    - (* [comment removed for export] *) apply (proj1 (sxz_zero_iff _ Bx)) in K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - Hr HnA; lia).
      + eapply (IH (r - 1)); [clear - Hk; lia| clear - Hr K2; lia| rewrite INV; apply lval_drop_zero; [clear - Hr; lia| rewrite LXr; exact K1]| f_equal; clear; lia].
      + (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; clear - K2 Hr; lia).
        apply c_stage2. split; [clear - HnA; lia|]. split; [| left; reflexivity].
        rewrite INV, (lval_drop_zero ys r) by (first [clear - Hr; lia | rewrite LXr; exact K1]). replace (r - 1) with 0 by (clear - K2 Hr; lia). reflexivity.
    all: match goal with |- ?g => idtac "LOOP1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L15629573549.2 L17205578407.2 L27538740931.72L27542900496.75L31024398201.2 L32982772237.2 L39172636981.0 L47608523970.3 L51169019778.77L59435147825.78L61812216706.77L61814434366.75Q12540582640.80Q16331225058.80Q21970489654.76Q25097661437.77Q3604969708.80 Q37692437715.79Q39212284437.77Q40271659186.74Q40275837590.77Q40276794991.76Q4505932600.77 Q5638170198.74 Q60160662256.80Q60162728780.79Q60511567613.77Q68395779403.79Q9534297315.74 00000700>00O00`00h01001101<01P01j02A02U02V02j03>03R04404H04\05005D05X06006D06X06l07=07Q07bS2pA2nAS2nA2K0S2Aa2ys2Ba2zs3ABDS2Aa2ys2Ba2zs3ABDS2nA3HnAS2nA3HnASS2nA3HnA2K0S2Aa2pA2ys2Ba2zs3ABDS2Aa2pA2nA2ys2Ba2nB2zs3CMPS2Aa2pA2nA2ys2Ba2zs3HnAS2Aa2nA2ys2Ba2zs3HnAFS2Aa2nA2ys2nB2zs3CMPS2Aa2nA2ys2nB2zs3CMPS2Aa2nA2ys2nB2zs3CMPS2Aa2pA2nA2ys2Ba2nB2zs3ABD3ALA3CMPS2Aa2nA2ys2nB2zs3CMPS2Aa2nA2ys2nB2zs3CMPS2Aa2nA2ys2nB2zs3CMPS2Aa2nA2ys2nB2zs3CMPS2Aa2nA2ys2nB2zs3CMPS2Aa2nA2ys2nB2zs3ABD3CMPS2Aa2nA2ys2nB2zs3CMPS2Aa2nA2ys2nB2zs3CMPS2Aa2nA2ys2nB2zs3CMPS2nA2ys2nB2zs3CMPS2Aa2nA2ys2nB2zs3CMPS2nA2ys2nB2zs3CMP". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK pA sAw padA pB sBw padB CEA HA LA HnA ABD PAB ALA OAS OAL PABB CEB HB LB_ HnB BBD PBB ALB OBS OBL PBBB"] Lemma c_cmp : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pxt0,(2.&40.)Pxt1,(2.&40.)Pxa0,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)(16.$<.VAL,VCS,VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,R8.R7.Vt2,(8.&40.VX,)(8.&40.(9.VAL,))R6.(8.&40.VAa,)(8.&40.VBa,)R5.R4.R3.R2.R1.Vs2v,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+9>49<.)Vfc,(:.(2.&40.))Vm,(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xa7. al_facts.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OAS (Aa + 10) 2.
    (* [comment removed for export] *)
    zstep. rewrite zx16_small by (clear - HnA; lia).
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - HnA; lia).
    - (* [comment removed for export] *) replace (Z_to_bv 64 nA) with (Z_to_bv 64 0) by (f_equal; clear - K0; lia).
      apply c_stage2. split; [clear - HnA; lia|]. split; [rewrite K0; reflexivity| left; reflexivity].
    - destruct PAB as [N0|[PP PAL]]; [exfalso; exact (K0 N0)|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      eapply (c_loop1 (Z.to_nat nA) nA); [reflexivity| clear - K0 HnA; lia| reflexivity| f_equal; clear; lia].
    all: match goal with |- ?g => idtac "CMP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End CmpWalkA.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition add_sub_PHI (dX dA dB : mpd) : Z := add_abs_PHI dX dA dB.
Definition add_sub_FR (d : Z) : Z := add_abs_FR d.

(* [comment removed for export] *)
Definition as_frame (ra s0 s1 s2 : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L24059859474.3000009S2d12d21D". (* [comment removed for export] *)
Lemma mpd_sep_symA : forall d1 d2, mpd_sep d1 d2 -> mpd_sep d2 d1.
Proof. intros d1 d2 [E|D]; [left; symmetry; exact E| right; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L13800843439.6L5390336047.5 00000C00RS1d2lo2SP3SP'2Q42LES1d2SP3SP'2LE1H". (* [comment removed for export] *)
Lemma opnd_sep_sp_le : forall dX d lo SP SP', opnd_sep dX d lo SP -> SP' <= SP -> opnd_sep dX d lo SP'.
Proof.
  (intros dX d lo SP SP' dd_H; ddestruct dd_H as (Q1 & Q2 & Q3 & Q4 & Q5); intros LE). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
  split; [clear - Q4 LE; lia| intros N; destruct (Q5 N); [left; assumption| right; clear - H LE; lia]].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section WAS.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis HADD : mpi_add_abs_stmtA_o asegs R HIA A_MPI_ADD_ABS.
  Hypothesis HSUB : mpi_sub_abs_stmtA_o asegs R HIA A_MPI_SUB_ABS.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (lo d flip : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition AS_FRAME_A := as_frame ra s0 s1 s2.
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis UWA : uw_obj R (md_addr dA) 16 d.
  Hypothesis UWB : uw_obj R (md_addr dB) 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis FLIP : flip = 1 \/ flip = -1.
  Hypothesis BUD : havol asegs R HIA h + add_sub_PHI dX dA dB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + add_sub_FR d <= FR_MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 256 - arl_need_rt R.
  (* [comment removed for export] *)
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis SXB : mpd_sep dX dB.
  Hypothesis SAB : mpd_sep dA dB.
  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
  Hypothesis CRA : client_range L (LB ++ fdata LF) lo (md_addr dA) 16.
  Hypothesis CRAL : md_own dA = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dA) (4 * md_n dA).
  Hypothesis CRB : client_range L (LB ++ fdata LF) lo (md_addr dB) 16.
  Hypothesis CRBL : md_own dB = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dB) (4 * md_n dB).
  Hypothesis IA1 : md_addr dA <> X -> md_own dA = LStatic -> AImgGlobals.img_norz (md_p dA) (4 * md_n dA) = true.
  Hypothesis IA2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "P,(5.$19.(1:.VdA,)$1;.)P,Pi,$3.P,(4.(10.=R1.)(1<.R1.(15.+4.(1=.VdA,))))(5.$1>.(1?.$<.(20.(14.(21.VdA,)R2.)))$22.)(5.$1>.(23.(21.VdA,)(15.+4.(1=.VdA,)))$22.)")
(* [comment removed for export] *).
  Hypothesis IB2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "P,(5.$19.(1:.VdB,)$1;.)P,Pi,$3.P,(4.(10.=R1.)(1<.R1.(15.+4.(1=.VdB,))))(5.$1>.(1?.$<.(20.(14.(21.VdB,)R2.)))$22.)(5.$1>.(23.(21.VdB,)(15.+4.(1=.VdB,)))$22.)")
(* [comment removed for export] *).
  Hypothesis A47A : md_own dA = LStatic -> md_p dA + 4 * md_n dA + 8 <= 2^47.
  Hypothesis A47B : md_own dB = LStatic -> md_p dB + 4 * md_n dB + 8 <= 2^47.
  Hypothesis SGA : md_sg dA = 1 \/ md_sg dA = -1.
  Hypothesis SGB : md_sg dB = 1 \/ md_sg dB = -1.
  Hypothesis NRA : 0 <= md_n dA <= 10000.
  Hypothesis NRB : 0 <= md_n dB <= 10000.

  Definition AS_POST_A := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "(24.$<.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(25.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(26.Vflip,VLB,(25.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(27.(25.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)(28.Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).
  Definition AS_VAL_A := mpd_val dA + flip * mpd_val dB.

  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A []).
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).

  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRAM; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L21887662552.149L29428324939.5  L33510041944.149L34289808772.1  L39939305631.152L41562522431.151L66083662040.149L9962237875.149 Q29963071266.152Q33963780182.152Q3859172566.152 Q39849717666.152Q39974853590.152Q45996133718.152Q49411331106.152Q546509986.152  00000700I00P00T00o01601=01D01`02802P02l03D03\04804TS2ra2spS1R2lo3LOS3ALO3ACPS2ra2spS2spS1R2ra2sp2lo4SLO25NEEDR3SPRS2ra2spS2ra2spS2ra2spS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOSS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R2sp2lo4SLO25NEEDR3LOSS1R2sp2lo4SLO25NEEDR3LOSS1R3HIA1h2sp3TOP2hc3HT14HTOPS1R3HIA1h2sp3TOP2hc3HT14HTOP". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma as_ret : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pv,$3.Pf,$3.Phc,(29.$<.VR,VHIA,)PLBc,(2:.$2;.)Pmc,P,(2.&40.)(2<.(2.&8.))PdXc,$2=.Pr,$3.Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxs0',(2.&40.)Pxs1,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxs2,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(2>.$<.VR,VHIA,Vh,VLB,VLF,Vm,(25.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+20.$2?.(30.$2;.)R19.R18.R17.R16.R15.R14.)P,(=.(4.(5.$3.R14.=)(5.$3.(31.R15.)$32.))(5.$3.R14.$33.))P,(10.R1;.(27.(25.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(10.R1;.(28.Vd,))(34.$<.(35.$<.VR,VHIA,R1;.Vmo,)$36.(6.(7.R16.(8.&40.(14.(37.&40.Vsp,)-20.))Vgp,Vtp,R15.R14.R13.R12.R11.(8.&40.R17.)R10.R?.R>.R=.R<.R;.R:.R9.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(8.&40.+9>5>4.)Vfc,(:.(2.&40.))R19.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold AS_FRAME_A, as_frame in FR1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    do 4 zstep.
    zstep.
    release_frame FR1 ST1 (bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold AS_POST_A.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A JC); [exact J| | exact HK9| exact MF9| exact HV| exact HF].
    split; [exact HR|]. split; [exact AD1|]. split; [exact PD1|]. split; [exact FRS1| exact NM1].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@D24976250634.181D50797141399.181D52014138856.181K43040026633.181L29074096193.169L29074168500.172L35663928186.7  L43046430437.6  L60098763854.3  Q22285631880.178Q22285648010.175Q22286196081.177Q24974040330.180Q39212284437.178Q42081808994.178Q4926406185.178 Q52016320488.180Q54253886744.177Q56761401107.178Q6027349519.181 Q60511567613.178Q62965564504.179Q63231501142.175Q9538787269.175 00000T01S02702o03K03g04<04=04G04Q04[04e05@05J05Z05d06?06I06V07107907P07Z07bS2ra2sp1X3xs02xs1w2sg2HB5Ha_st5Hl_stS1R2ra2sp1X3xs02lo4SLO22xs1w2sg5NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs1w2sg2HB5Ha_st5Hl_stS1R2sp1X3xs02lo4SLO21p2xs1w5NEEDR3FSZ3DSX2HB5Ha_st5Hl_stS2ra2sp1X3xs02xs1w2sg2X03X16S2ra2sp1X3xs02xs1w2sg2X03X16S1R3HIA1h2sp2lo3TOP1HFS1R2lo3LOSS1X3xs02xsS1X3xs02xsS1X3xs02xsS1X3xs02xs1w2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xs2X02HBS1X3xs02xsS1X3xs02xs1w2HB5Ha_st5Hl_stS1X3xs02xsS1X3xs02xs2X0S1X3xs02xs1w2HB5Ha_st5Hl_stS3xs02xsS1X3xs02xs3X162HB5Ha_stS1X3xs02xsS3xs02xs". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma as_FIN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pv,$3.Pf,$3.Phc,(29.$<.VR,VHIA,)PLBc,(2:.$2;.)Pmc,P,(2.&40.)(2<.(2.&8.))PdXc,$2=.Pw,$3.Psg,$3.Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(2>.$<.VR,VHIA,Vh,VLB,VLF,Vm,(25.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+20.$2?.(30.$2;.)R18.R17.R16.R15.R14.R13.)P,(5.$3.(38.R13.(39.+2.+10.))(38.R12.(39.+2.+10.)))P,(=.(5.$3.R13.+1.)(5.$3.R13.-1.))P,(5.$3.(15.R14.(3:.R16.))$32.)P,(10.R1<.(27.(25.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,))P,(10.R1<.(28.Vd,))(34.$<.(35.$<.VR,VHIA,R1<.Vmo,)$36.(6.(7.R16.(8.&40.(14.(37.&40.Vsp,)-20.))Vgp,Vtp,R15.R14.R13.(8.&40.VX,)(8.&40.(9.(3;.VR,)))R12.R11.R10.R?.R>.R=.R<.R;.(8.&40.R18.)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(8.&40.+9>5<8.)Vfc,(:.(2.&40.))R1:.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 WS SG HVV BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg0 n p xs pad' own]. pose proof J0 as JX; pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
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
    match type of CX2 with rw_cells _ _ _ [C8 _; C2 (Z_to_bv 64 ?v); _; _] =>
      pose proof (rw_cells_C2_congr asegs m2 X [C8 (Z_to_bv 64 p)] v sg [C2 (Z_to_bv 64 n); C4 padX] CX2) as CX3 end.
    cbn [app] in CX3.
    pose proof (xa_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ sg J0 MU WM MI2 (CX3 WS) SG HH2 OX2) as J2.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J2.
    eapply as_ret; [exact J2| left; split; [reflexivity|]| exact BV| exact BF].
    unfold mpd_val, mpd_abs in *. cbn [md_sg md_limbs] in *. exact HVV.
    all: match goal with |- ?g => idtac "FIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition at1 (m1 : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "(4.(2>.$<.VR,VHIA,Vh,VLB,VLF,Vm,(25.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+20.$2?.(30.$2;.)==Vh,VLB,O1.(25.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))(4.(3<.$<.O1.VLB,VdA,)(4.(3=.$<.VR,VLF,O1.VLB,(37.&40.Vsp,)VdB,)(4.(3>.$<.(3;.VR,)(3?.$<.VR,VHIA,Vh,)O1.VdA,)(3>.$<.(3;.VR,)(3?.$<.VR,VHIA,Vh,)O1.VdB,)))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac call_side :=
    first [ eassumption | reflexivity | exact BUD | exact BUDF | exact IA1 | exact UWX
          | (rewrite unsigned_lit by (clear; lia); reflexivity)
          | (apply mpd_sep_symA; eassumption)
          | (eapply opnd_sep_sp_le; [eassumption| clear; lia])
          | (eapply opnd_atA_SP_le; [first [eassumption| apply opnd_atA_mpd; eassumption]| clear; lia])
          | (apply opnd_atA_mpd; eassumption) ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L11783059779.1  L16073620949.11 L17808963162.4  L17829113186.9  L19808959425.4  L29010569984.197L34289808772.1  L36042104371.11 L36560747987.4  L37463353716.2  L37764321808.197L40290687782.1  L41942189128.1  L45290914134.11 L48752871491.9  L5266079642.1   L58354988820.4  L59124818608.2  L59308632561.1  L6186700884.4   L63632471619.5  L8574640154.4   Q5261966311.162 Q7190997524.197 Q7192832867.162 00000300C00J00i01401501901G01U01Y01k01n02202302S02T02[02a02e02l03@03G03U04>04gS1dS1R3HIA1h2sp3TOPS2dA2dBS2sp1X2sX2nX2pX3xs04padX4ownX1HS2dA2dB3NRAFS2spS1R2sp2lo4SLO2S2dA2dB3dX22CVS2spS2ra2sp1X3xs02dA1wS1XS2spFS1X2sX2nX2pX3xs04padX4ownX2dA2dBFS2dA2dBS1d2D0S2KRS2dA2dBS1R2sp2lo4SLO25NEEDRS2dA2dBS1X3xs02X03X16S1R2sp3xs02lo4SLO25NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO25NEEDR3LOS4SP643ALO3ACP". (* [comment removed for export] *)
  #[using="IMG HADD JC TPV UWX UWA UWB D0 FLIP BUD BUDF SLO2 SXA SXB SAB OA OB CRA CRAL CRB CRBL IA1 IA2 IB2 SGA SGB NRA"] Lemma as_KADD : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pm1,P,(2.&40.)(2<.(2.&8.))Pw,$3.Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(40.R10.)P,(5.$3.(38.R10.(39.+2.+10.))(38.(41.VdA,)(39.+2.+10.)))P,(5.$3.(15.Vflip,(41.VdB,))(41.VdA,))(34.$<.(35.$<.VR,VHIA,Vh,Vmo,)$36.(6.(7.R11.(8.&40.(14.(37.&40.Vsp,)-20.))Vgp,Vtp,R10.R?.R>.(8.&40.VX,)(8.&40.(9.(3;.VR,)))R=.(8.&40.(42.VdA,))(8.&40.(42.VdB,))R<.R;.R:.R9.R8.(8.&40.R12.)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(8.&40.+9>48<.)Vfc,(:.(2.&40.))R13.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; (intros dd_H; ddestruct dd_H as (J0 & MA1 & MB1 & OAA1 & OBA1); intros WS SGN).
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof J0 as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX1.
    replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in ST1 by (clear; lia).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    assert (XW1 : mpd_writableA R LB LF (bv_unsigned sp + -32) (htop asegs R HIA h) dX) by (eapply mpd_writableA_sp_mono; [exact XW| clear; lia]).
    assert (XLS1' : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp + -32 <= md_p dX) by (intros N; destruct (XLS N); [left; assumption| right; clear - H; lia]).
    assert (OXA1 : mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dX) by (split; [exact OX1| intros E; exfalso; exact (NST E)]).
    (* [comment removed for export] *)
    zstep. zstep.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HADD as SPc. unfold mpi_add_abs_stmtA_o in SPc.
      eapply SPc with (h := h) (LB := LB) (LF := LF) (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by qlia; try call_side.
      all: try (rewrite ?(unsigned_lit X) by qlia; eapply uw_obj_uwc; [exact UWX| clear; lia]).
      all: try (clear - SLO2 NEEDR TOP SPR LOS LOSP; lia).
      all: try (clear - SPA; replace (bv_unsigned sp + -32) with (bv_unsigned sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact SPA).
      all: match goal with |- ?g => idtac "KADD-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    destruct CR as [CR1 BK].
    assert (PHI0 : 0 <= add_abs_PHI dX dA dB) by (unfold add_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA NRB; lia).
    assert (FR0 : 0 <= add_abs_FR d) by (unfold add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -32) (add_abs_PHI dX dA dB) (add_abs_FR d) J0 ltac:(clear - SLO2 NEEDR; lia)
                  PHI0 FR0 MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      destruct CR1 as [(-> & _)| ->]; [exfalso; apply KR; reflexivity|].
      eapply as_ret; [exact J1| right; reflexivity| unfold add_sub_PHI; clear; lia| unfold add_sub_FR; clear; lia].
    - destruct CR1 as [(-> & CV & CSG)| ->]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
      (* [comment removed for export] *)
      zstep.
      eapply as_FIN with (sg := md_sg dA); [exact J1| exact WS| exact SGA| | unfold add_sub_PHI; clear; lia| unfold add_sub_FR; clear; lia].
      unfold AS_VAL_A. unfold mpd_val in CV. rewrite CSG in CV. unfold mpd_abs in *. unfold mpd_val. rewrite <- SGN.
      replace (limbs_val (md_limbs dX2)) with (limbs_val (md_limbs dA) + limbs_val (md_limbs dB)) by (clear - CV; lia).
      clear - SGB FLIP. destruct SGB as [-> | ->]; destruct FLIP as [-> | ->]; lia.
    all: match goal with |- ?g => idtac "KADD-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0@L11794092686.2  L16073620949.11 L16128897414.2  L17829113186.9  L18283994230.2  L28837201624.4  L29010569984.202L31465033811.12 L31466922472.6  L31467150834.15 L32016504687.20 L32022846158.14 L34289808772.1  L36560747987.4  L37463353716.14 L37463353716.2  L37463353716.6  L40290687782.1  L41942189128.1  L45290914134.11 L47026640784.205L48740486386.10 L5266079642.1   L59308518135.4  L59308632561.1  L63632471619.5  L64491265552.2  L8288358478.2   L9568782131.11  L9847631648.2   Q5261966311.170 Q7190997524.205 Q7192832867.170 00000800H00N00m01601A01B01C01X01Y01Z02K02O02]02a02e02i02l03003103C03h03i04604:04N04T04\04j05105?05h06QS1d4FR1'S1R3HIA1h2sp3TOPS1d2D0S2sp1X2sX2nX2pX3xs04padX4ownX1HS2dB4flipS2dA2dB3NRAFFS1R3HIA1h1d4BUDF4FR1'FFS1R3HIA1h1X2sX2nX2pX3xs04padX4ownX2dA2dB3BUD4PHI1S2spS2dA2dB3dX22CVS2spS2spS2spS1XS2spFS2ra2sp1X3xs01w2sgS1X2sX2nX2pX3xs04padX4ownX2dA2dB4PHI1FS2dA2dB2LE2LTS2KRS1R2sp2lo4SLO25NEEDRS1d2D0S2dA3NRAS1R2sp2lo4SLO2S2dA2dBS1X3xs02X03X16S1R2sp3xs02lo4SLO25NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO25NEEDR3LOS4SP643ALO3ACP". (* [comment removed for export] *)
  #[using="IMG HSUB JC TPV UWX UWA UWB D0 BUD BUDF SLO2 SXA SXB SAB OA OB CRA CRAL CRB CRBL IA2 IB2 A47A NRA"] Lemma as_KSUBAB : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pm1,P,(2.&40.)(2<.(2.&8.))Pw,$3.Psg,$3.Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(40.R11.)P,(5.$3.(38.R11.(39.+2.+10.))(38.R10.(39.+2.+10.)))P,(=.(5.$3.R11.+1.)(5.$3.R11.-1.))P,(5.$3.(15.Vflip,(41.VdB,))(43.(41.VdA,)))P,(10.(3:.VdB,)(3:.VdA,))P,(5.$3.(15.R14.(12.(3:.VdA,)(3:.VdB,)))(15.(41.VdA,)(12.(3:.VdA,)(3:.VdB,))))(34.$<.(35.$<.VR,VHIA,Vh,Vmo,)$36.(6.(7.R14.(8.&40.(14.(37.&40.Vsp,)-20.))Vgp,Vtp,R13.R12.R11.(8.&40.VX,)(8.&40.(9.(3;.VR,)))R10.(8.&40.(42.VdA,))(8.&40.(42.VdB,))R?.R>.R=.R<.R;.(8.&40.R16.)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(8.&40.+9>598.)Vfc,(:.(2.&40.))R17.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; (intros dd_H; ddestruct dd_H as (J0 & MA1 & MB1 & OAA1 & OBA1); intros WS SG SGN LE HVS).
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof J0 as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX1.
    replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in ST1 by (clear; lia).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    assert (XW1 : mpd_writableA R LB LF (bv_unsigned sp + -32) (htop asegs R HIA h) dX) by (eapply mpd_writableA_sp_mono; [exact XW| clear; lia]).
    assert (XLS1' : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp + -32 <= md_p dX) by (intros N; destruct (XLS N); [left; assumption| right; clear - H; lia]).
    assert (OXA1 : mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dX) by (split; [exact OX1| intros E; exfalso; exact (NST E)]).
    assert (PHI0 : 0 <= sub_abs_PHI dX dA dB) by (unfold sub_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA; lia).
    assert (FR0 : 0 <= sub_abs_FR d) by (unfold sub_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    assert (PHI1 : sub_abs_PHI dX dA dB <= add_sub_PHI dX dA dB) by (unfold sub_abs_PHI, add_sub_PHI, add_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA NRB; lia).
    assert (FR1' : sub_abs_FR d <= add_sub_FR d) by (unfold sub_abs_FR, add_sub_FR, add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    (* [comment removed for export] *)
    zstep. zstep.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HSUB as SPc. unfold mpi_sub_abs_stmtA_o in SPc.
      eapply SPc with (h := h) (LB := LB) (LF := LF) (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by qlia; try call_side.
      all: try (rewrite ?(unsigned_lit X) by qlia; eapply uw_obj_uwc; [exact UWX| clear; lia]).
      all: try (clear - SLO2 NEEDR TOP SPR LOS LOSP; lia).
      all: try (clear - SPA; replace (bv_unsigned sp + -32) with (bv_unsigned sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact SPA).
      all: try (clear - BUD PHI1; lia). all: try (clear - BUDF FR1'; lia).
      all: match goal with |- ?g => idtac "KSUBAB-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    destruct CR as [CR1 BK].
    pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -32) (sub_abs_PHI dX dA dB) (sub_abs_FR d) J0 ltac:(clear - SLO2 NEEDR; lia)
                  PHI0 FR0 MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - destruct CR1 as [(-> & _)|[-> |[-> LT]]]; [exfalso; apply KR; reflexivity| | exfalso; clear - LT LE; lia].
      eapply as_ret; [exact J1| right; reflexivity| clear - PHI1; lia| clear - FR1'; lia].
    - destruct CR1 as [(-> & CV & CSG)|[-> |[-> LT]]];
        [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia| exfalso; clear - LT LE; lia].
      (* [comment removed for export] *)
      zstep.
      eapply as_FIN with (sg := sg); [exact J1| exact WS| exact SG| | clear - PHI1; lia| clear - FR1'; lia].
      unfold AS_VAL_A. unfold mpd_val in CV. rewrite CSG in CV.
      replace (mpd_abs dX2) with (mpd_abs dA - mpd_abs dB) by (unfold mpd_abs in *; clear - CV; lia).
      rewrite HVS. unfold mpd_val, mpd_abs.
      replace (flip * (md_sg dB * limbs_val (md_limbs dB))) with ((flip * md_sg dB) * limbs_val (md_limbs dB)) by (clear; lia). rewrite SGN. clear; lia.
    all: match goal with |- ?g => idtac "KSUBAB-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@L11794092686.2  L16073620949.11 L16128897414.2  L17578730821.2  L17829113186.9  L18283994230.2  L19489910334.2  L28837201624.4  L29010569984.201L31465033811.12 L31466922472.6  L31467150834.15 L32083503036.14 L32089811485.20 L34289808772.1  L36560747987.4  L37463353716.14 L37463353716.2  L37463353716.6  L40290687782.1  L41942189128.1  L42290037104.10 L45290914134.11 L5231095820.202 L5266079642.1   L59308632561.1  L59310615242.4  L63632471619.5  L64491265552.2  L7441479568.203 L8288358479.2   L9568782131.11  Q5261966311.168 Q7190997524.203 Q7192832867.168 00000800H00N00U01401=01E01T01U01V01k01l02]02^02b03003403803<03?03C03h03i04>04?04C04Q04e04k05=05E05S05a06J073S1d4FR1'S1R3HIA1h2sp3TOPS1d2D0S2dA2dBS2sp1X2sX2nX2pX3xs04padX4ownX1HS2dB4flipS2dA3SGAS2dA2dB3NRA3NRBFFS1R3HIA1h1d4BUDF4FR1'FS1R3HIA1h1X2sX2nX2pX3xs04padX4ownX2dA2dB3BUD4PHI1FS2spS2dA2dB3dX22CVS2spS2spS2spS1XS2spS1X2sX2nX2pX3xs04padX4ownX2dA2dB4PHI1FS2ra2sp1X3xs02dA1w2WBFS2KRS2dA2dB2LT3LT'S1R2sp2lo4SLO25NEEDRS1d2D0S2ra2sp1X3xs02dA1wS2dB3NRBS1R2sp2lo4SLO2S1X3xs02X03X16S1R2sp3xs02lo4SLO25NEEDR3LOS4SP643ALO3ACPS1R2sp3xs02lo4SLO25NEEDR3LOS4SP643ALO3ACP". (* [comment removed for export] *)
  #[using="IMG HSUB JC TPV UWX UWA UWB D0 BUD BUDF SLO2 SXA SXB SAB OA OB CRA CRAL CRB CRBL IA2 IB2 A47B SGA NRA NRB"] Lemma as_KSUBBA : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pm1,P,(2.&40.)(2<.(2.&8.))Pw,$3.Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(40.R10.)P,(5.$3.(38.R10.(39.+2.+10.))(38.(41.VdA,)(39.+2.+10.)))P,(4.(10.=R11.)(1<.R11.(39.+2.+10.)))P,(5.$3.(15.Vflip,(41.VdB,))(43.(41.VdA,)))P,(1<.(3:.VdA,)(3:.VdB,))(34.$<.(35.$<.VR,VHIA,Vh,Vmo,)$36.(6.(7.R13.(8.&40.(14.(37.&40.Vsp,)-20.))Vgp,Vtp,R12.R11.R10.(8.&40.VX,)(8.&40.(9.(3;.VR,)))R?.(8.&40.(42.VdA,))(8.&40.(42.VdB,))R>.R=.R<.R;.R:.(8.&40.R14.)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(8.&40.+9>5:<.)Vfc,(:.(2.&40.))R15.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; (intros dd_H; ddestruct dd_H as (J0 & MA1 & MB1 & OAA1 & OBA1); intros WS WB SGN LT).
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof J0 as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX1.
    replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in ST1 by (clear; lia).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    assert (XW1 : mpd_writableA R LB LF (bv_unsigned sp + -32) (htop asegs R HIA h) dX) by (eapply mpd_writableA_sp_mono; [exact XW| clear; lia]).
    assert (XLS1' : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp + -32 <= md_p dX) by (intros N; destruct (XLS N); [left; assumption| right; clear - H; lia]).
    assert (OXA1 : mpd_aobjA asegs AL (hcs asegs R HIA h) m1 dX) by (split; [exact OX1| intros E; exfalso; exact (NST E)]).
    assert (PHI0 : 0 <= sub_abs_PHI dX dB dA) by (unfold sub_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NRB; lia).
    assert (FR0 : 0 <= sub_abs_FR d) by (unfold sub_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    assert (PHI1 : sub_abs_PHI dX dB dA <= add_sub_PHI dX dA dB) by (unfold sub_abs_PHI, add_sub_PHI, add_abs_PHI, grow_PHI; unfold AVOL_CALL; clear - NRA NRB; lia).
    assert (FR1' : sub_abs_FR d <= add_sub_FR d) by (unfold sub_abs_FR, add_sub_FR, add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HSUB as SPc. unfold mpi_sub_abs_stmtA_o in SPc.
      eapply SPc with (h := h) (LB := LB) (LF := LF) (dX := dX) (dA := dB) (dB := dA) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by qlia; try call_side.
      all: try (rewrite ?(unsigned_lit X) by qlia; eapply uw_obj_uwc; [exact UWX| clear; lia]).
      all: try (clear - SLO2 NEEDR TOP SPR LOS LOSP; lia).
      all: try (clear - SPA; replace (bv_unsigned sp + -32) with (bv_unsigned sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact SPA).
      all: try (clear - BUD PHI1; lia). all: try (clear - BUDF FR1'; lia).
      all: match goal with |- ?g => idtac "KSUBBA-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    destruct CR as [CR1 BK].
    pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -32) (sub_abs_PHI dX dB dA) (sub_abs_FR d) J0 ltac:(clear - SLO2 NEEDR; lia)
                  PHI0 FR0 MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - destruct CR1 as [(-> & _)|[-> |[-> LT']]]; [exfalso; apply KR; reflexivity| | exfalso; clear - LT LT'; lia].
      eapply as_ret; [exact J1| right; reflexivity| clear - PHI1; lia| clear - FR1'; lia].
    - destruct CR1 as [(-> & CV & CSG)|[-> |[-> LT']]];
        [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia| exfalso; clear - LT LT'; lia].
      (* [comment removed for export] *)
      zstep.
      eapply (as_FIN _ _ _ _ _ _ (0 - w) (- md_sg dA)); [exact J1| | clear - SGA; lia| | clear - PHI1; lia| clear - FR1'; lia].
      + rewrite Zminus_mod, WS, <- Zminus_mod. reflexivity.
      + unfold AS_VAL_A. unfold mpd_val in CV. rewrite CSG in CV.
        replace (mpd_abs dX2) with (mpd_abs dB - mpd_abs dA) by (unfold mpd_abs in *; clear - CV; lia).
        unfold mpd_val, mpd_abs.
        replace (flip * (md_sg dB * limbs_val (md_limbs dB))) with ((flip * md_sg dB) * limbs_val (md_limbs dB)) by (clear; lia). rewrite SGN. clear; lia.
    all: match goal with |- ?g => idtac "KSUBBA-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308546259.300000:S2dE2N12N0". (* [comment removed for export] *)
  #[using="Type"] Lemma opnd_aobjA_limbs : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Phc,(29.$<.VR,VHIA,)PLBc,(2:.$2;.)Pmc,P,(2.&40.)(2<.(2.&8.))PSPx,$3.PdE,$2=.P,(44.$<.VR,VHIA,R5.R4.VLF,R3.)P,(3=.$<.VR,VLF,R4.R5.R3.R2.)P,(3>.$<.(3;.VR,)(3?.$<.VR,VHIA,R7.)R5.R3.)P,(10.+1.(1=.R4.))(45.$<.(3;.VR,)(3?.$<.VR,VHIA,R9.)R7.(21.R5.)(15.+4.(1=.R5.)))")
(* [comment removed for export] *).
  Proof.
    intros hc LBc mc SPx dE HMc ME [_ OL] N1. pose proof (opnd_viewA _ _ _ _ _ _ _ ME) as [(_ & _ & _ & _ & _ & OW) _].
    destruct (md_own dE) eqn:EO.
    - exfalso. destruct OW as [_ N0]. clear - N0 N1. lia.
    - ddestruct OW as (_ & EIN & _). eapply hm_aobj_block; [exact HMc| exact EIN].
    - exact (OL eq_refl).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01L0@D21329468335.153D21329468335.154D23379772182.154D35881667587.153D35881667587.154L13720147517.4  L17305750384.4  L19431261630.4  L19945316590.2  L21765854580.143L21887662552.142L22366621351.0  L27775132660.143L33478855426.4  L33510041944.143L34290115814.149L35653441506.7  L3680515908.3   L40834179097.174L42479632545.4  L43059266230.147L43935804614.173L43935886280.174L43935886280.176L43936346429.171L54383256528.1  L54748384003.143L60098763854.3  L60814849355.3  L60976029790.4  L6419290535.0   L6482734895.4   L66083662040.143L9716869748.142 L9962237875.143 Q10333294960.183Q13280261335.184Q13715427560.186Q15643324129.149Q18696506101.183Q20498771212.185Q21800401414.183Q22053704889.184Q22053704889.185Q22056211846.181Q23512175082.151Q24267381591.186Q24330840805.183Q25160350961.183Q25513505925.152Q25513505925.153Q25664719138.183Q27668705378.152Q27668705378.153Q31226872993.183Q31396957457.183Q32655500769.150Q35016271767.183Q35715139857.183Q35765334355.150Q35765334355.151Q36426122721.183Q37374748791.183Q3830427394.150 Q38735600301.185Q38736348717.186Q38737697513.183Q39212284437.184Q39212284437.186Q39939554818.150Q4141071397.183 Q44648843873.150Q45399902939.185Q49698585326.151Q49698585326.152Q50301287168.183Q51235796833.150Q53972118266.183Q54209832123.181Q60511567613.184Q60511567613.186Q61800308129.183Q62495047012.184Q6414620453.183 Q64253126389.183Q66522067074.150Q67426116409.153Q67528989526.153Q67528989526.154Q9538243134.183 Q9538787269.181 Q9843367298.149 00000g01d02^03F04704A04M04[04b04o05<05=05J05W05d06106I06W07607B07W08808Y09:09[09_09l0:60:D0:N0:O0:]0:j0;70;D0;E0;Z0;o0<:0<V0<k0<l0=A0=V0=k0>60>O0>P0>l0?I0?l0?m0@O0A40AQ0Af0B10BN0BO0BZ0Be0Bf0C;0CK0C`0D50DJ0D_0E40ED0EE0EP0Ee0F;0FQ0FR0F]0G:0GO0Gd0H90H:0HS0Ho0I00I@0Ib0JD0Jl0KA0KV0KfS1R2ra2sp1X3xs02lo4SLO25NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02lo4SLO25NEEDR3LOS2X03SPR2HB5Ha_st5Hl_st2s1S1R2ra2sp2s21X3xs02lo4SLO25NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X3xs03TOP2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs03TOP2HB5Ha_st5Hl_st2s12s2S2dA2dB2C0S2sp2dA2lo1HS2sp2dA2lo3OA4S2sp2loS2ra2sp1X3xs0S2ra2sp1X3xs0SS2ra2sp1X3xs0S2dA2dB2C02C1S2ra2sp1X3xs0S2ra2sp1X3xs0S1R3HIA1h2sp2lo3TOP4HTOPS2dA4LENA4PABBS1R2ra2sp1X3xs02dA2dB4PABB4PBBBS2sp2dB2lo1HS2ra2sp1X3xs02lo4LOSPS2ra2sp1X3xs02dA2dB3BBD4PABB4PBBBS2ra2sp1X3xs02dA2dB3ABD4PABB4PBBBS2ra2sp1X3xs02dA2dB3BBD4PABB4PBBBS2ra2sp1X3xs02dA2dB3ABD4PABB4PBBBS2dAS2ra2sp1X3xs0S1R2lo3LOSS2dB4LENB4PBBBS2dA2dB2CmSS2sp2dB2lo3OB4S2ra2sp1X3xs0S2ra2sp1X3xs0S2ra2sp1X3xs0FS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS2sp3xs02loS1R3xs02dA2dB4IMG'4PABB4PBBBS3xs02dA2dB4PABB4PBBBFS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS2sp3xs02HBS3xs02dA2dB3BBD4PABB4PBBBFS1R3xs02dA2dB4IMG'4PABB4PBBBS2ra2sp3xs02lo2HB5Ha_st5Hl_stS2sp2s03xs02lo2HB5Ha_st5Hl_st2s12s2FS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s1S1R3xs02dA2dB5ALWF'4PABB4PBBBS3xs02dA2dB4PABB4PBBBS2sp3xs02loS1R3xs02dA2dB5ALWF'4PABB4PBBBFS2sp3xs02HBS2sp3xs02HBFS3xs02dA2dB4PABB4PBBBS2sp3xs02lo4LOSPS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS2sp3xs02lo4LOSPFS2sp3xs02loS3xs02dA2dB4PABB4PBBBS2sp3xs04SP642HB5Ha_stS2sp3xs04SP642HB5Ha_stFS2sp3xs02loS1R3xs02dA2dB5ALWF'4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBFS3xs02dA2dB3ABD4PABB4PBBBS1R3xs02dA2dB4IMG'4PABB4PBBBFS2sp3xs02lo4LOSPS2sp2s23xs02lo4LOSP2HB5Ha_st5Hl_stS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s12s2S3xs02dA2dB4PABB4PBBBS3xs02dA2dB4PABB4PBBBS2sp3xs02lo4LOSP". (* [comment removed for export] *)
  #[using="IMG HADD HSUB JC TPV UWX UWA UWB D0 FLIP BUD BUDF SLO2 SXA SXB SAB OA OB CRA CRAL CRB CRBL IA1 IA2 IB2 A47A A47B SGA SGB NRA NRB"] Lemma as_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(46.$<.VR,VHIA,Vh,Vmo,)P,(3<.$<.Vm,VLB,VdA,)P,(3=.$<.VR,VLF,Vm,VLB,(37.&40.Vsp,)VdB,)P,(47.$<.Vm,Vlo,(37.&40.Vsp,))P,(48.$<.Vm,)P,(3>.$<.(3;.VR,)(3?.$<.VR,VHIA,Vh,)Vm,(25.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(3>.$<.(3;.VR,)(3?.$<.VR,VHIA,Vh,)Vm,VdA,)P,(3>.$<.(3;.VR,)(3?.$<.VR,VHIA,Vh,)Vm,VdB,)(49.$<.$36.(4:.(6.(7.Vra,Vsp,Vgp,Vtp,R13.R12.R11.Vs0,Vs1,(8.&40.VX,)(8.&40.(42.VdA,))(8.&40.(42.VdB,))(8.&40.Vflip,)R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(8.&40.$4;.)Vfc,(:.(2.&40.))Vm,(;.$<.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK MA0 MB0 ST MI OXA OAA OBA. unfold A_ADD_SUB_MPI.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 32 AS_FRAME_A JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h. pose proof (art_alwf asegs R HIA) as ALWF.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof OXA as [OX _]. pose proof OAA as [OAs OAl]. pose proof OBA as [OBs OBl]. cbn [md_addr] in OX.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    change (rw_cells asegs m1 (bv_unsigned sp + -32) AS_FRAME_A) in FR.
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
    assert (AT : at1 m1) by (split; [exact J0| split; [exact MA1| split; [exact MB1| split; [split; [exact OAs| exact OAl1]| split; [exact OBs| exact OBl1]]]]]).
    (* [comment removed for export] *)
    destruct (hm_apart asegs R HIA h LB LF m1 HH) as [HF0 _]. rewrite Forall_forall in HF0.
    pose proof (opnd_atA_mpd asegs R LF m1 LB (bv_unsigned sp) dA MA1) as MA1o.
    assert (PA0 : md_own dA = LHeap -> 0 < md_p dA).
    { intros EO. pose proof (opnd_viewA _ _ _ _ _ _ _ MA1o) as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. ddestruct OW as (_ & AIN & _).
      destruct (HF0 _ ltac:(apply in_or_app; left; exact AIN)) as (R0 & _). exact R0. }
    assert (PB0 : md_own dB = LHeap -> 0 < md_p dB).
    { intros EO. pose proof (opnd_viewA _ _ _ _ _ _ _ MB1) as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. ddestruct OW as (_ & BIN & _).
      destruct (HF0 _ ltac:(apply in_or_app; left; exact BIN)) as (R0 & _). exact R0. }
    destruct (opnd_rawA _ _ _ _ _ _ _ MA1o PA0) as (CEA & ABY & LENA & NRA1 & _ & ABD & PAB).
    destruct (opnd_rawA _ _ _ _ _ _ _ MB1 PB0) as (CEB & BBY & LENB & NRB1 & _ & BBD & PBB).
    pose proof (proj1 (proj2 (proj1 (opnd_viewA _ _ _ _ _ _ _ MA1o)))) as ALA. pose proof (proj1 (proj2 (proj1 (opnd_viewA _ _ _ _ _ _ _ MB1)))) as ALB.
    pose proof (bytes_at_bound _ _ _ _ ABY) as PABB. rewrite u32s_length in PABB.
    pose proof (bytes_at_bound _ _ _ _ BBY) as PBBB. rewrite u32s_length in PBBB.
    assert (OALn : 1 <= md_n dA -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dA) (4 * md_n dA)) by (intros N1; eapply (opnd_aobjA_limbs h LB m1 _ dA HH MA1o); [split; [exact OAs| exact OAl1]| exact N1]).
    assert (OBLn : 1 <= md_n dB -> aobj asegs AL (hcs asegs R HIA h) m1 (md_p dB) (4 * md_n dB)) by (intros N1; eapply (opnd_aobjA_limbs h LB m1 _ dB HH MB1); [split; [exact OBs| exact OBl1]| exact N1]).
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OAs (md_addr dA + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OBs (md_addr dB + 8) 2.
    (* [comment removed for export] *)
    zstep.
    pose proof (mpd_abs_lval dA LENA) as EVA. pose proof (mpd_abs_lval dB LENB) as EVB.
    pose proof (mpd_abs_nonneg dA) as NNA. pose proof (mpd_abs_nonneg dB) as NNB.
    pose proof SGA as SGA'. pose proof SGB as SGB'. pose proof FLIP as FLIP'.
    destruct SGA' as [EA|EA]; destruct SGB' as [EB|EB]; destruct FLIP' as [EF|EF]; rewrite ?EA, ?EB, ?EF; rewrite ?sx16_small by (clear; lia).
    (* [comment removed for export] *)
    all: zstep; zstep; zstep; zstep; zstep.
    all: try (if_cases K0; zify_cond K0; try (exfalso; clear - K0; lia)).
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- aevtA _ _ _ (MS _ _ (Z_to_bv 64 0x09e48c) _ _ _ _) =>
             eapply (as_KADD m1); [exact AT| rewrite EA; vm_compute; reflexivity| rewrite EA, EB, EF; reflexivity]
         | |- _ => idtac end.
    (* [comment removed for export] *)
    all: eapply (aevtA_cut_evtA_KF asegs R HIA h mo);
      [ eapply (c_cmp AL IMG ALWF (hcs asegs R HIA h) CSOK) with (ys := md_limbs dA) (zs := md_limbs dB);
          [exact CEA| exact ABY| exact LENA| exact NRA1| exact ABD| exact PAB| exact ALA| exact OAs| exact OALn| clear - PABB LENA; lia
          | exact CEB| exact BBY| exact LENB| exact NRB1| exact BBD| exact PBB| exact ALB| exact OBs| exact OBLn| clear - PBBB LENB; lia]
      | ].
    all: cbv beta; intros ms' PC; unfold cmpw_postA in PC; ddestruct PC as (y0 & y1 & b0 & b3 & b4 & b5 & b6 & b7 & w & pc & -> & CASES).
    all: rewrite <- EVA, <- EVB in CASES.
    all: destruct CASES as [(-> & [[C1 ->]|[C0 ->]])|(-> & Cm & ->)].
    all: try (eapply (as_KSUBBA m1); [exact AT| rewrite EA; vm_compute; reflexivity| vm_compute; split; [discriminate| reflexivity]| rewrite EA, EB, EF; reflexivity
                                    | pose proof (Z.sgn_spec (mpd_abs dA - mpd_abs dB)) as SS; clear - Cm SS; lia]).
    all: try (eapply (as_KSUBAB m1) with (sg := 1); [exact AT| vm_compute; reflexivity| left; reflexivity| rewrite EA, EB, EF; reflexivity
              | pose proof (Z.sgn_spec (mpd_abs dA - mpd_abs dB)) as SS; clear - C0 SS; lia
              | pose proof (Z.sgn_spec (mpd_abs dA - mpd_abs dB)) as SS; replace (mpd_abs dA - mpd_abs dB) with 0 by (clear - C0 SS; lia); clear; lia]).
    all: try (eapply (as_KSUBAB m1) with (sg := md_sg dA); [exact AT| rewrite EA; vm_compute; reflexivity| exact SGA| rewrite EA, EB, EF; reflexivity
              | pose proof (Z.sgn_spec (mpd_abs dA - mpd_abs dB)) as SS; clear - C1 SS; lia
              | reflexivity]).
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WAS.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mpi_addsub_stmtA_o (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) (PA3 : word -> Prop)
    (Rr : list blk -> mpd -> mpd -> mpd -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Ph,(29.O6.O5.O4.)PLB,(2:.$2;.)PLF,(2:.$2;.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(4<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(2<.(2.&8.))Pmo,$4=.PdX,$2=.PdA,$2=.PdB,$2=.Plo,$3.Pd,$3.P,(44.O6.O5.O4.R2;.R2:.R29.R7.)P,(46.O6.O5.O4.R2<.R7.)P,(3<.O6.R9.R2<.R7.)P,(3<.O6.R:.R2=.R7.)P,(3=.O6.O5.R2=.R;.R2>.(37.&40.R2;.)R7.)P,(4>.R:.R9.)P,(4>.R;.R9.)P,(4>.R;.R:.)P,(4?.(5.$19.(1:.R=.)$1;.))P,(50.R>.R=.R;.(37.&40.R30.))P,(50.R?.R=.R<.(37.&40.R31.))P,(51.(52.O5.)(53.$2;.R35.(54.R34.))R=.(42.R?.)+10.)P,P,(5.$19.(1:.R10.)$55.)(51.(52.O5.)(53.$2;.R37.(54.R36.))R?.(21.R11.)(15.+4.(1=.R11.)))P,(51.(52.O5.)(53.$2;.R37.(54.R36.))R?.(42.R10.)+10.)P,P,(5.$19.(1:.R11.)$55.)(51.(52.O5.)(53.$2;.R39.(54.R38.))R11.(21.R12.)(15.+4.(1=.R12.)))P,(56.O5.R39.R38.(37.&40.R36.)(57.O6.O5.O4.R3:.)R14.)P,P,(4?.(5.$19.(1:.R15.)$58.))(=.(10.(14.(21.R16.)(15.+4.(1=.R16.)))R13.)(10.(37.&40.R38.)(21.R16.)))P,(47.O6.R18.R13.(37.&40.R38.))P,(10.(59.O5.)R14.)P,(10.R15.(12.(12.(37.&40.R3:.)+100.)(5:.O5.)))P,(10.(37.&40.R3;.)(57.O6.O5.O4.R3?.))P,(5.$3.(38.(37.&40.R3<.)+10.)=)P,(5.(2.&40.)R3;.(8.&40.(5;.O5.)))P,(48.O6.R1>.)P,(5.$3.(38.(37.&40.R40.)+2.)=)P,(3>.O6.(3;.O5.)(3?.O6.O5.O4.R44.)R20.R1>.)P,(3>.O6.(3;.O5.)(3?.O6.O5.O4.R45.)R21.R1>.)P,(3>.O6.(3;.O5.)(3?.O6.O5.O4.R46.)R22.R1>.)P,P,(4?.(5.$3.(42.R20.)(42.R21.)))P,(5.$19.(1:.R21.)$1;.)(5.$1>.(23.(21.R22.)(15.+4.(1=.R22.)))$22.)P,P,(5.$19.(1:.R21.)$1;.)P,Pi,$3.P,(4.(10.=R1.)(1<.R1.(15.+4.(1=.R23.))))(5.$1>.(1?.O6.(20.(14.(21.R24.)R2.)))$22.)(5.$1>.(23.(21.R23.)(15.+4.(1=.R23.)))$22.)P,P,(5.$19.(1:.R21.)$1;.)P,Pi,$3.P,(4.(10.=R1.)(1<.R1.(15.+4.(1=.R23.))))(5.$1>.(1?.O6.(20.(14.(21.R24.)R2.)))$22.)(5.$1>.(23.(21.R23.)(15.+4.(1=.R23.)))$22.)P,P,(5.$19.(1:.R22.)$1;.)(10.(14.(14.(21.R23.)(15.+4.(1=.R23.)))+8.)(39.+2.+2?.))P,(10.(14.(5<.O6.O5.O4.R4;.)(27.R25.R24.R23.))$5=.)P,(5>.O6.R28.(59.O5.)(5?.O6.O5.O4.R4<.)(37.&40.R42.)(37.&40.R48.)R22.)P,(60.O5.(42.R27.)+10.R23.)P,(60.O5.(42.R27.)+10.R24.)P,(60.O5.(42.R27.)+10.R25.)P,(10.(14.(61.O6.O5.O4.R50.)(28.R26.))$62.)P,(5.(2.&40.)R45.(8.&40.(42.R2;.)))P,(5.(2.&40.)R45.(8.&40.(42.R2;.)))P,(5.(2.&40.)R45.(8.&40.(42.R2;.)))P,A1.O2.R45.(49.O6.(24.O6.O5.O4.R52.R51.R50.R4?.R4;.R4:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R33.R32.R55.R54.R53.R2?.A4.O1.R54.R2?.R2>.R2=.(27.R2?.R2>.R2=.)(28.R2;.)R2<.R31.R30.)(4:.(6.(7.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R33.(8.&40.O3.)R32.(:.(2.&40.))R31.(;.O6.))R30.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition add_sub_mpi_stmtA_o (flip : Z) segs R HIA ENTRY := mpi_addsub_stmtA_o segs R HIA ENTRY (fun a3 => a3 = Z_to_bv 64 flip) (add_sub_mpi_R flip).
Definition mpi_add_mpi_stmtA_o segs R HIA ENTRY := mpi_addsub_stmtA_o segs R HIA ENTRY (fun _ => True) add_mpi_R.
Definition mpi_sub_mpi_stmtA_o segs R HIA ENTRY := mpi_addsub_stmtA_o segs R HIA ENTRY (fun _ => True) sub_mpi_R.

(* [comment removed for export] *)
Definition mpi_addsub_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z)
    (Rr : list blk -> mpd -> mpd -> mpd -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Ph,(29.O5.O4.O3.)PLB,(2:.$2;.)PLF,(2:.$2;.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(4<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(2<.(2.&8.))Pmo,$4=.PdX,$2=.PdA,$2=.PdB,$2=.Plo,$3.Pd,$3.P,(44.O5.O4.O3.R2;.R2:.R29.R7.)P,(46.O5.O4.O3.R2<.R7.)P,(3<.O5.R9.R2<.R7.)P,(3<.O5.R:.R2=.R7.)P,(3<.O5.R;.R2>.R7.)P,(4>.R:.R9.)P,(4>.R;.R9.)P,(4>.R;.R:.)P,(4?.(5.$19.(1:.R=.)$1;.))P,(50.R>.R=.R;.(37.&40.R30.))P,(50.R?.R=.R<.(37.&40.R31.))P,(51.(52.O4.)(53.$2;.R35.(54.R34.))R=.(42.R?.)+10.)P,P,(5.$19.(1:.R10.)$55.)(51.(52.O4.)(53.$2;.R37.(54.R36.))R?.(21.R11.)(15.+4.(1=.R11.)))P,(51.(52.O4.)(53.$2;.R37.(54.R36.))R?.(42.R10.)+10.)P,P,(5.$19.(1:.R11.)$55.)(51.(52.O4.)(53.$2;.R39.(54.R38.))R11.(21.R12.)(15.+4.(1=.R12.)))P,(56.O4.R39.R38.(37.&40.R36.)(57.O5.O4.O3.R3:.)R14.)P,P,(4?.(5.$19.(1:.R15.)$58.))(=.(10.(14.(21.R16.)(15.+4.(1=.R16.)))R13.)(10.(37.&40.R38.)(21.R16.)))P,(47.O5.R18.R13.(37.&40.R38.))P,(10.(59.O4.)R14.)P,(10.R15.(12.(12.(37.&40.R3:.)+100.)(5:.O4.)))P,(10.(37.&40.R3;.)(57.O5.O4.O3.R3?.))P,(5.$3.(38.(37.&40.R3<.)+10.)=)P,(5.(2.&40.)R3;.(8.&40.(5;.O4.)))P,(48.O5.R1>.)P,(5.$3.(38.(37.&40.R40.)+2.)=)P,(3>.O5.(3;.O4.)(3?.O5.O4.O3.R44.)R20.R1>.)P,(3>.O5.(3;.O4.)(3?.O5.O4.O3.R45.)R21.R1>.)P,(3>.O5.(3;.O4.)(3?.O5.O4.O3.R46.)R22.R1>.)P,P,(4?.(5.$3.(42.R20.)(42.R21.)))P,(5.$19.(1:.R21.)$1;.)(5.$1>.(23.(21.R22.)(15.+4.(1=.R22.)))$22.)P,P,(5.$19.(1:.R21.)$1;.)P,Pi,$3.P,(4.(10.=R1.)(1<.R1.(15.+4.(1=.R23.))))(5.$1>.(1?.O5.(20.(14.(21.R24.)R2.)))$22.)(5.$1>.(23.(21.R23.)(15.+4.(1=.R23.)))$22.)P,P,(5.$19.(1:.R21.)$1;.)P,Pi,$3.P,(4.(10.=R1.)(1<.R1.(15.+4.(1=.R23.))))(5.$1>.(1?.O5.(20.(14.(21.R24.)R2.)))$22.)(5.$1>.(23.(21.R23.)(15.+4.(1=.R23.)))$22.)P,(10.(14.(5<.O5.O4.O3.R4:.)(27.R24.R23.R22.))$5=.)P,(5>.O5.R27.(59.O4.)(5?.O5.O4.O3.R4;.)(37.&40.R41.)(37.&40.R47.)R21.)P,(60.O4.(42.R26.)+10.R22.)P,(60.O4.(42.R26.)+10.R23.)P,(60.O4.(42.R26.)+10.R24.)P,(10.(14.(61.O5.O4.O3.R4?.)(28.R25.))$62.)P,(5.(2.&40.)R44.(8.&40.(42.R2:.)))P,(5.(2.&40.)R44.(8.&40.(42.R2:.)))P,(5.(2.&40.)R44.(8.&40.(42.R2:.)))(49.O5.(24.O5.O4.O3.R50.R4?.R4>.R4=.R49.R48.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R31.R30.R53.R52.R51.R2=.A4.O1.R52.R2=.R2<.R2;.(27.R2=.R2<.R2;.)(28.R29.)R2:.R2?.R2>.)(4:.(6.(7.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.)R31.(8.&40.O2.)R30.(:.(2.&40.))R2?.(;.O5.))R2>.))")
(* [comment removed for export] *).
Definition mpi_add_mpi_stmtA segs R HIA ENTRY := mpi_addsub_stmtA segs R HIA ENTRY add_mpi_R.
Definition mpi_sub_mpi_stmtA segs R HIA ENTRY := mpi_addsub_stmtA segs R HIA ENTRY sub_mpi_R.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010<L410472236.2000006S1d2HI". (* [comment removed for export] *)
Lemma mpd_at_static47 : forall m LB d, mpd_at asegs m LB d -> md_own d = LStatic -> md_p d + 4 * md_n d + 8 <= 2^47.
Proof.
  intros m LB d [(_ & _ & _ & LEN & _ & OW) _] EO. rewrite EO in OW. ddestruct OW as (N1 & _ & _ & BY & RO).
  destruct (A_mpi_copy.static_limbs_low (Z_to_bv 64 0) m _ _ _ BY LEN N1 RO) as [_ HI]. clear - HI. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma binop_postA_mono : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Psegs,(2:.$63.)PR,$64.PHIA,(65.R2.R1.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)PF,(4<.&5.(2.&40.))Pfc,(2.&20.)Ph,(29.R15.R14.R13.)PLB,(2:.$2;.)PLF,(2:.$2;.)PdX,$2=.PR1,P,$3.P,$2=.SpPR2,P,$3.P,$2=.SpPPHI,$3.PFR,$3.Plo,$3.Pm,P,(2.&40.)(2<.(2.&8.))Pmo,$4=.Pmo1,$4=.Pc,$66.P,(67.R3.R2.)P,Pr,$3.Pd,$2=.P,A2.R<.R2.R1.A2.R<.R3.R2.P,(24.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R9.R8.R7.R6.R4.R3.)(24.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R;.R:.R9.R8.R7.R6.R4.)")
(* [comment removed for export] *).
Proof.
  intros until c. intros MF HR P. unfold mpi_binop_postA in *.
  ddestruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & mo' & h' & LB' & dX' & r & P).
  dexists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m', mo', h', LB', dX', r.
  ddestruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16).
  split; [exact P0|]. split; [exact P1|]. split; [exact P2|]. split; [eapply mo_frame_trans; [exact MF| exact P3]|].
  repeat (split; [assumption|]). apply HR. exact P16.
Qed.


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L65106939752.7000007S2dA2dB". (* [comment removed for export] *)
Lemma wrap_R_add : forall LB dX dA dB r d, add_sub_mpi_R 1 LB dX dA dB r d -> add_mpi_R LB dX dA dB r d.
Proof. intros LB dX dA dB r d [V K]. split; [| exact K]. destruct V as [[-> E]|E]; [left; split; [reflexivity| rewrite E; lia]| right; exact E]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L52849495742.7000007S2dA2dB". (* [comment removed for export] *)
Lemma wrap_R_sub : forall LB dX dA dB r d, add_sub_mpi_R (-1) LB dX dA dB r d -> sub_mpi_R LB dX dA dB r d.
Proof. intros LB dX dA dB r d [V K]. split; [| exact K]. destruct V as [[-> E]|E]; [left; split; [reflexivity| rewrite E; lia]| right; exact E]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)



(* [comment removed for export] *)

Section Closed.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
  Hypothesis IMG : asan_img_ok (arl_AL R).
  Hypothesis HADD : mpi_add_abs_stmtA_o asegs R HIA A_MPI_ADD_ABS.
  Hypothesis HSUB : mpi_sub_abs_stmtA_o asegs R HIA A_MPI_SUB_ABS.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R).
  Hypothesis ROIMG : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub ()) "Pa,$3.P,(5.$1>.(1?.$<.(20.R1.))$22.)P,(4.(10.=R2.)(1<.R2.(39.+2.+40.)))(4.(10.(68.(52.VR,))R3.)(1<.R3.(69.(52.VR,))))")
(* [comment removed for export] *).

        End Closed.
