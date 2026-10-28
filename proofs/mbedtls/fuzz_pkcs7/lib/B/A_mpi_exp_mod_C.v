(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_divmod_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_frame_lib A_frame_kit A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_copy
     A_mpi_core_bitlen A_mpi_stmtA_sz A_mpi_exp_mod_P A_mpi_cmp_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_exp_mod_lib.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_exp_mod_C () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "WEC.VIEWg"; "WEC.VIEW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_exp_mod_P.EM_POISON"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_exp_mod_lib.snapA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "WEC.EMB"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_bitlen.A_MPI_CORE_BITLEN"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "WEC.SLOTS"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"].

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([658888]).
Local Ltac zchk_new ::= constr:([657484; 657488; 657512; 657516; 657520; 657608; 657612; 657616; 657844; 657848; 658272; 658276; 658280; 658676; 658680; 658684; 658740; 658744; 658748]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
Local Ltac zstep_to L :=
  repeat (lazymatch goal with
          | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (List.existsb (Z.eqb pc) L) with true => fail | false => zstep end
          end).
Section WEC.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (dX : mpd) (lo slo : Z).
  Local Notation X := (md_addr dX).
  Local Notation KEEP := (mpd_keep LB dX).
  Local Notation WX := [(X, X + 16)].
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 1088 - arl_need_ecp R.
  Hypothesis NEEDE : 0 <= arl_need_ecp R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis HH0 : HM asegs R HIA h LB LF m.
  Hypothesis MI0 : mem_inv asegs m.

  (* [comment removed for export] *)
  Definition VIEWg (hc : HST asegs R HIA) (LBc : list blk) (mq : mem) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "(0.(1.$2.O2.(3.O1.)(4.$5.(6.(7.&40.(8.O1.)))(4.$5.(9.(7.&40.(:.O1.)))(4.$5.(9.(7.&40.(;.O1.)))(4.$5.(<.(=.O1.))(>.$5.))))))(0.(?.$2.O2.(8.O1.)(10.(11.O1.)))(0.(12.$13.(14.(15.(16.&40.)(11.O1.)))(;.O1.))(0.(0.(17.=(;.O1.))(17.(;.O1.)+2710.))(0.(18.(12.$13.(:.O1.)+1.)(12.$13.(:.O1.)-1.))(0.(0.(19.=(3.O1.))(17.(1:.(3.O1.)+10.)(1;.+2.+40.)))(0.(18.(12.$13.(;.O1.)=)(0.(19.=(8.O1.))(12.$13.(1<.(8.O1.)+4.)=)))(0.(12.$13.(1<.(3.O1.)+8.)=)(0.(1=.$2.(1>.VR,)(1?.$2.VR,VHIA,O4.)O2.(3.O1.)+10.)(0.P,(17.+1.(;.O1.))(1=.$2.(1>.VR,)(1?.$2.VR,VHIA,O4.)O2.(8.O1.)(20.+4.(;.O1.)))(0.(0.(17.=(8.O1.))(17.(1:.(8.O1.)(20.+4.(;.O1.)))(1;.+2.+40.)))(21.$2.O2.O3.O1.))))))))))))")
(* [comment removed for export] *).
  Definition VIEW (mq : mem) (d : mpd) : Prop := VIEWg h LB mq d.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0>L26892418956.1L29438984485.3L47535788809.3L52343332758.3L52616024670.7L52616371395.7L59308546259.3L59311123687.2L60376875688.3L63827843616.300000400>00J00R00d01801A01I01Q01\S2spS2dX1d3SXDS1d4LENc3PBBS2dX1d1CS2sp2lo1d1a2Ha1S1HS2sp2lo1d3OS41a2Ha1SS1d2N12N0S2dX3SXDS2dX1d1QS1d2BD4DPOS". (* [comment removed for export] *)
  #[using="IMG HH0 MI0"] Lemma em_view_g : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Pd,$22.Phc,(23.$2.VR,VHIA,)PLBc,(24.$25.)Pmq,P,(16.&40.)(26.(16.&8.))P,(21.$2.Vm,VLB,R4.)P,(18.(17.(1:.(3.VdX,)+10.)(3.R5.))(17.(1:.(3.R5.)+10.)(3.VdX,)))P,(27.VdX,R6.Vlo,(28.&40.Vsp,))P,(29.(2:.VR,)(2;.$25.VLB,(2<.VLF,))Vlo,(3.R7.)+10.)P,P,(12.$2=.(2>.R8.)$2?.)(29.(2:.VR,)(2;.$25.VLB,(2<.VLF,))Vlo,(8.R9.)(20.+4.(;.R9.)))P,(30.$2.(1>.VR,)(1?.$2.VR,VHIA,Vh,)Vm,R9.)P,(31.R:.)P,(32.$2.VR,VHIA,R:.R9.VLF,R8.)P,Px,$13.P,(1?.$2.VR,VHIA,Vh,R1.)(1?.$2.VR,VHIA,R=.R2.)P,Pb,$25.P,(33.$25.R1.(34.R>.))(33.$25.R2.R=.)P,(35.$2.R;.)P,(36.$2.VR,VHIA,Vh,(37.VLB,VdX,)VLF,(28.&40.Vsp,)(28.&40.Vsp,)(4.(38.$13.$13.)(39.$13.$13.(3.VdX,)(1:.(3.VdX,)+10.))(>.(38.$13.$13.)))Vm,R<.)(3:.R?.R>.R=.R10.)")
(* [comment removed for export] *).
  Proof.
    intros d hc LBc mq MD SXD OS CRD CRDL OD IMD HHq HCSc SUBc MIq PRES.
    dpose OS as (OS1 & OS2 & OS3 & OS4 & OS5).
    pose proof (presW_presA asegs R HIA h _ _ _ _ _ _ _ PRES) as HPA. pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HPA) as HPX.
    pose proof (hcs_ok asegs R HIA h) as CSOK.
    assert (CRk : client_range L (KEEP ++ fdata LF) (bv_unsigned sp) (md_addr d) 16).
    { pose proof (client_range_keep L LB LF lo dX (md_addr d) 16 CRD OS2) as C0.
      intros a Ha. destruct (C0 a Ha) as [S|[D|B]]; [left; clear - S Ha OS4; lia| right; left; exact D| right; right; exact B]. }
    assert (CRLk : md_own d = LHeap -> client_range L (KEEP ++ fdata LF) (bv_unsigned sp) (md_p d) (4 * md_n d)).
    { intros EH. assert (NN : md_own d <> LNull) by (rewrite EH; discriminate).
      assert (AP : md_own dX = LHeap -> md_p d + 4 * md_n d <= md_p dX \/ md_p dX + 4 * md_n dX <= md_p d).
      { intros EX. destruct OS3 as [C|[C|[C|C]]]; [exfalso; subst d; clear - SXD; lia| exfalso; exact (C EX)| exfalso; exact (NN C)| clear - C; lia]. }
      pose proof (client_range_keep L LB LF lo dX (md_p d) (4 * md_n d) (CRDL EH) AP) as C0.
      intros a Ha. destruct (C0 a Ha) as [S|[D|B]]; [left; pose proof (OS5 NN); clear - S Ha H; lia| right; left; exact D| right; right; exact B]. }
    assert (MDq : mpd_at asegs mq LBc d).
    { eapply (mpd_at_heap_presx asegs L m mq LB (KEEP ++ fdata LF) LBc (bv_unsigned sp) WX d); [exact MD| exact HPX| exact MI0| exact MIq| exact CRk| exact CRLk| | | exact SUBc].
      - cbn [disjoint_from]. split; [clear - SXD; lia| exact I].
      - intros EH. cbn [disjoint_from]. split; [pose proof (OS1 ltac:(rewrite EH; discriminate)) as Q; clear - Q; lia| exact I]. }
    assert (PNZ : md_own d = LHeap -> 0 < md_p d).
    { intros EH. pose proof MD as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (_ & HIN & _).
      pose proof (hm_blocks_low asegs R HIA h LB LF m HH0 (md_p d) (4 * md_n d) ltac:(apply in_or_app; left; exact HIN)) as BL.
      destruct (hm_apart asegs R HIA h LB LF m HH0) as [HF _]. rewrite Forall_forall in HF. destruct (HF _ ltac:(apply in_or_app; left; exact HIN)) as (P0 & _). cbn in P0. exact P0. }
    destruct (opnd_rawA _ _ _ _ _ _ _ (opnd_atA_mpd asegs R LF mq LBc (bv_unsigned sp) d MDq) PNZ) as (CE & BY & LENc & NRc & SGc & BD & PBc).
    pose proof (bytes_at_bound _ _ _ _ BY) as PBB. rewrite u32s_length in PBB.
    pose proof MDq as [(_ & DAL & DPOS & _) _].
    assert (OSq : aobj asegs AL (hcs asegs R HIA hc) mq (md_addr d) 16).
    { eapply aobj_cs_mono; [exact HCSc|]. eapply (presA_aobj asegs R CS); [exact CSOK| exact HPA| exact (proj1 OD)| exact CRk| clear; lia| intros x Hx; eapply hcs_below_top; exact Hx]. }
    unfold VIEWg. split; [exact CE|]. split; [exact BY|]. split; [exact LENc|]. split; [exact NRc|]. split; [exact SGc|].
    split; [clear - BD DPOS; lia|]. split; [exact PBc|]. split; [exact DAL|]. split; [exact OSq|].
    split; [| split; [clear - PBB LENc; lia| exact MDq]].
    intros N1. pose proof MDq as [(_ & _ & _ & _ & _ & OW) _].
    destruct (md_own d) eqn:EOD; [exfalso; destruct OW as (_ & N0); clear - N0 N1; lia| |].
    - ddestruct OW as (_ & EIN & _). eapply hm_aobj_block; [exact HHq| exact EIN].
    - eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMG hc)| eapply (hm_img_shadow asegs R HIA); exact HHq| exact (IMD EOD)].
    all: match goal with |- ?g => idtac "VIEW-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG HH0 MI0"] Lemma em_view : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Pd,$22.Pmq,P,(16.&40.)(26.(16.&8.))P,(21.$2.Vm,VLB,R2.)P,(18.(17.(1:.(3.VdX,)+10.)(3.R3.))(17.(1:.(3.R3.)+10.)(3.VdX,)))P,(27.VdX,R4.Vlo,(28.&40.Vsp,))P,(29.(2:.VR,)(2;.$25.VLB,(2<.VLF,))Vlo,(3.R5.)+10.)P,P,(12.$2=.(2>.R6.)$2?.)(29.(2:.VR,)(2;.$25.VLB,(2<.VLF,))Vlo,(8.R7.)(20.+4.(;.R7.)))P,(30.$2.(1>.VR,)(1?.$2.VR,VHIA,Vh,)Vm,R7.)P,(31.R8.)P,(32.$2.VR,VHIA,Vh,VLB,VLF,R8.)P,(35.$2.R9.)P,(36.$2.VR,VHIA,Vh,(37.VLB,VdX,)VLF,(28.&40.Vsp,)(28.&40.Vsp,)(4.(38.$13.$13.)(39.$13.$13.(3.VdX,)(1:.(3.VdX,)+10.))(>.(38.$13.$13.)))Vm,R:.)(3;.R;.R<.)")
(* [comment removed for export] *).
  Proof.
    intros d mq MD SXD OS CRD CRDL OD IMD HHq MIq PRES. unfold VIEW.
    eapply em_view_g; try eassumption; [intros x Hx; exact Hx|].
    intros b Hb. pose proof MD as [(_ & _ & _ & _ & _ & OW) _]. unfold mpd_blk in Hb. destruct (md_own d); try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)).
  Qed.
  Variable mo : Model.
  Variable (Rr : Z -> mpd -> Prop) (PHI FR : Z).
  Hypothesis SSMAP : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Ph,(23.$2.VR,VHIA,)PLB,(24.$25.)PLF,(24.$25.)Pm,P,(16.&40.)(26.(16.&8.))Pg,$13.P,(32.$2.VR,VHIA,R5.R4.R3.R2.)P,(0.(17.(3<.VR,)R2.)(19.R2.(3=.$2.VR,VHIA,R6.)))(3>.(12.(26.(16.&8.))A1.R4.(3?.(40.(1>.VR,)R3.))(41.(16.&8.))))")
(* [comment removed for export] *).
  Hypothesis SSL : arl_stklo R <= slo.
  Hypothesis SLL : slo <= lo.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SS0 : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis MX0 : mpd_at asegs m LB dX.
  Hypothesis CRX : crange CS X 16.
  Hypothesis DSX : X + 16 <= lo \/ bv_unsigned sp <= X.
  Hypothesis XL0 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "P,(3>.(12.$2=.(2>.VdX,)$42.))(0.(43.(1?.$2.VR,VHIA,Vh,)(8.VdX,)(20.+4.(;.VdX,)))(0.(19.=(;.VdX,))(18.(17.(1:.(8.VdX,)(20.+4.(;.VdX,)))Vlo,)(17.(28.&40.Vsp,)(8.VdX,)))))")
(* [comment removed for export] *).
  Hypothesis PHI0 : 0 <= PHI.
  Hypothesis FR0 : 0 <= FR.
  Hypothesis NSX : md_own dX <> LStatic.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation POSTA := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX Rr PHI FR lo m mo).

  (* [comment removed for export] *)
  Definition EMB (sp1 : Z) (mq : mem) (sl : list word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "(0.(0.(17.(44.(28.&40.Vsp,)+150.)O3.)(17.O3.(44.(28.&40.Vsp,)+140.)))(0.(12.$13.(1<.O3.+20.)=)(0.(32.$2.VR,VHIA,Vh,VLB,VLF,O2.)(0.(1.$2.O2.(1:.(28.&40.Vsp,)-68.)(4.$5.(6.Vs11,)(4.$5.(6.Vs10,)(4.$5.(6.Vs9,)(4.$5.(6.Vs8,)(4.$5.(6.Vs7,)(4.$5.(6.Vs6,)(4.$5.(6.Vs5,)(4.$5.(6.Vs4,)(4.$5.(6.Vs3,)(4.$5.(6.Vs2,)(4.$5.(6.Vs1,)(4.$5.(6.Vs0,)(4.$5.(6.Vra,)(>.$5.)))))))))))))))(0.(1.$2.O2.O3.(45.(16.&40.)$5.$6.O1.))(0.(12.$46.(15.(16.&40.)O1.)#1;.)(0.(47.$2.O2.(1:.O3.+=8.)(1:.(28.&40.Vsp,)-68.))(0.(47.$2.O2.Vlo,O3.)(0.(35.$2.O2.)(0.(1.$2.O2.(1:.(48.(1:.O3.+60.)+3.)(49.(1>.VR,)))$4:.)(0.(4;.$2.(1>.VR,)O2.Vslo,(1:.O3.+60.))(0.(4;.$2.(1>.VR,)O2.(1:.O3.+<0.)(28.&40.Vsp,))(0.(4<.$2.(1>.VR,)Vm,O2.(3<.VR,)(1:.O3.+60.))(0.(4<.$2.(1>.VR,)Vm,O2.(1:.O3.+<0.)(28.&40.Vsp,))(0.(36.$2.VR,VHIA,Vh,(37.VLB,VdX,)VLF,(28.&40.Vsp,)(28.&40.Vsp,)(4.(38.$13.$13.)(39.$13.$13.(3.VdX,)(1:.(3.VdX,)+10.))(>.(38.$13.$13.)))Vm,O2.)(0.(4=.(4.(38.$13.$13.)(39.$13.$13.Vlo,(28.&40.Vsp,))(4.(38.$13.$13.)(39.$13.$13.(1:.(48.(1:.O3.+60.)+3.)(49.(1>.VR,)))(1:.(1:.(48.(1:.O3.+60.)+3.)(49.(1>.VR,)))+<.))(>.(38.$13.$13.))))Vm,O2.)(4>.$2.Vm,O2.)))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0>L23633349615.4L23984723757.2L29038974481.4L38000921400.8L38948636245.0L39188636933.0L39332637397.0L40622469209.2L519294241.8  L65288602837.4L8224808951.4 00000>00E00Q00n00o01001101801W01e021S2sp2dX2lo3DSPS2dX2NPS1R2dX3sp11QS1R3HIA1h2sp3TOP3sp13SP14HTOPSSSS1R3sp1S1R2sp2lo3LOS3SLO5NEEDE3sp13SP1S2sp2dX2lo3DSXS1R2dX3sp11Q". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 MX0 CRX DSX XL0"] Lemma emb_X : forall sp1 mq sl, EMB sp1 mq sl -> mpd_at asegs mq LB dX.
  Proof.
    (intros sp1 mq sl dd_H; ddestruct dd_H as (SP1 & SP1M & HHq & SAVE & SPILL & LSL & SThi & STlo & MIq & SHC & SSlo & SShi & SNlo & SNhi & PRES & MU & WM)).
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    assert (SCW : crange CS (sp1 + 96) (12 * 8)) by (eapply crange_sub; [exact SCS0| clear - SP1 SLO NEEDE LOS; lia| clear - SP1 TOP HTOP; lia]).
    eapply mpd_at_munch_any; [exact MX0| exact MU| exact WM| |].
    - cbn [disjoint_from].
      destruct (apart_shadow_client AL CS X 16 (sp1 + 96) (Z.shiftr (sp1 + 96) 3 + al_sb AL) 12 CSOK CRX SCW
                  ltac:(unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [Q|Q];
        (split; [clear - DSX; lia| split; [clear - Q; lia| exact I]]).
    - intros NN. ddestruct (XL0 NN) as (CRP & NP & DSP). cbn [disjoint_from].
      destruct (apart_shadow_client AL CS (md_p dX) (4 * md_n dX) (sp1 + 96) (Z.shiftr (sp1 + 96) 3 + al_sb AL) 12 CSOK CRP SCW
                  ltac:(unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia) ltac:(clear - NP; lia) ltac:(clear; lia)) as [Q|Q];
        (split; [clear - DSP; lia| split; [clear - Q; lia| exact I]]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L15767349020.5L26073930352.4L26084710128.4L35268428478.5L35279081022.5L48964082895.5L48965947471.6L627380229.6  L629185669.6  00000B00C00D00E00F00V00W00X00YS1R3HIA1h3PHI4PHI0FFFFS1R3HIA1h2FR3FR0FFF". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSMAP SSL SLL SS0 MX0 CRX DSX XL0 PHI0 FR0 NSX"] Lemma em_exit : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Psp1,$13.Pmq,P,(16.&40.)(26.(16.&8.))Psl,(24.(16.&40.))Pr,$13.Pxra,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pxs1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pxs2,(16.&40.)Pxs3,(16.&40.)Pxs4,(16.&40.)Pxs5,(16.&40.)Pxs7,(16.&40.)Pxs9,(16.&40.)Pxs10,(16.&40.)Pxs11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(4?.R1=.R1<.R1;.)P,A2.VRr,R1;.VdX,(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.R1;.(7.&40.R1?.)Vgp,Vtp,R1:.R19.R18.Vsp,R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.(7.&40.R1<.)R:.(7.&40.(1:.(48.(1:.R1?.+60.)+3.)(49.(1>.VR,))))R9.R8.R7.R6.R5.R4.R3.)VF,(7.&40.+:0:>0.)Vfc,(41.(16.&40.))R1>.(55.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EB RRr. pose proof (emb_X _ _ _ EB) as MXq.
    ddestruct EB as (SP1 & SP1M & HHq & SAVE & SPILL & LSL & SThi & STlo & MIq & SHC & SSlo & SShi & SNlo & SNhi & PRES & MU & WM).
    eapply (em_epi R HIA IMG h LB LF m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dX lo slo) with (hc := h) (LBc := LB) (dXc := dX) (sl := sl);
      first [ eassumption | reflexivity | clear - PHI0; lia | clear - FR0; lia | intros x Hx; exact Hx | apply mpd_out_refl; exact NSX | intros b Hb; left; exact Hb
            | match goal with |- ?g => idtac "EXIT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Variables (dA dE dN : mpd).
  Local Notation A := (md_addr dA).
  Local Notation E := (md_addr dE).
  Local Notation N := (md_addr dN).
  Local Notation SBw := (Z_to_bv 64 (al_sb AL)).
  Local Notation SH a := (Z_to_bv 64 (Z.shiftr a 3 + al_sb AL)).
  Hypothesis RR4 : Rr (-4) dX.
  (* [comment removed for export] *)
  Local Notation RN sp1 xt0 xt1 xt2 xa0 xa6 xa7 xs7 xs8 xs9 xt3 xt4 xt5 xt6 :=
    (mkR ra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 (N + 10)) xa0 (Z_to_bv 64 A) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 N) (Z_to_bv 64 0) xa6 xa7
         (SH N) s3 (Z_to_bv 64 X) SBw (SH (N + 10)) xs7 xs8 xs9 (Z_to_bv 64 (sp1 + 128)) (SH (sp1 + 96)) xt3 xt4 xt5 xt6).

  Ltac emb_open EB := pose proof EB as (SP1 & SP1M & HHq & SAVE & SPILL & LSL & SThi & STlo & MIq & SHC & SSlo & SShi & SNlo & SNhi & PRES & MU & WM).
  Ltac emb_close sp1 EBn :=
    lazymatch goal with
    | |- context [MS _ _ _ _ _ ?m2 _] =>
      lazymatch goal with
      | SPc : rw_cells asegs m2 sp1 ?cs |- _ =>
        let ws := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) cs) in
        assert (EBn : EMB sp1 m2 ws)
          by (unfold EMB; refine (conj _ (conj _ (conj _ (conj _ (conj SPc (conj eq_refl (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))));
              eassumption)
      end
    end.
  Ltac cut_cells H k H1 H2 :=
    lazymatch type of H with rw_cells ?sg ?mx ?A ?cs =>
      let E := fresh "Ecut" in
      pose proof (eq_sym (firstn_skipn k cs)) as E; rewrite E in H; clear E;
      apply (proj1 (rw_cells_app sg mx A _ _)) in H; destruct H as [H1 H2]; cbn [firstn skipn] in H1, H2
    end.
  Ltac c4cb_all H :=
    repeat (lazymatch type of H with
            | rw_cells ?sg ?mx ?A ?cs =>
                let rec go pre rest :=
                  lazymatch rest with
                  | C4 ?w :: CB 4 ?bs :: ?post => apply (rw_cells_merge sg mx A pre [C4 w; CB 4 bs] post) in H; cbn [app cells_size csize cells_bytes cbytes Nat.add] in H
                  | ?c :: ?post => go (pre ++ [c]) post
                  end in go (@nil cell) cs
            end).
  Ltac cb8c_all H :=
    repeat (lazymatch type of H with
            | rw_cells ?sg ?mx ?A ?cs =>
                let rec go pre rest :=
                  lazymatch rest with
                  | CB 8 ?bs :: ?post => apply (rw_cells_CB8_C8 sg mx A pre bs post) in H; cbn [app] in H
                  | ?c :: ?post => go (pre ++ [c]) post
                  end in go (@nil cell) cs
            end).
  Ltac c8cb_at H i :=
    lazymatch type of H with rw_cells ?sg ?mx ?A ?cs =>
      lazymatch eval cbv beta iota zeta delta [nth] in (nth i cs (C1 (Z_to_bv 8 0))) with C8 ?x =>
        apply (rw_cells_reshape sg mx A cs (firstn i cs ++ CB 8 (le8 x) :: skipn (S i) cs)) in H;
        [ cbn [firstn skipn app] in H | cbn; repeat split; try apply length_le8 | reflexivity ]
      end
    end.
  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (AIh_laws asegs R HIA h) as LAWS; pose proof (KF_kinv asegs R HIA h mo) as KINV;
    pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L13284853040.122L18292428764.119L22728327174.3  L24815139881.121L35653441506.7  L41996436675.72 L49532791131.122L59314841581.120L60098763854.3  L8288663128.122 L8929159528.117 L8942128512.114 L9356559676.11  Q20440747526.120Q26295627581.120Q27816433611.122Q28519977204.117Q41818000070.120Q50458135125.120Q61110407306.117Q61114167189.120Q61114592028.122Q8956078776.117 00000V01D01O01m02E04^05?06006:06T07B08008[09209E09\0:30:J0:]0;00;C0;V0;iS2sp2dN1k2kz3sp12sl2Hk2NB3LSL3SPR4SP1RS2sp2dN1k2kz3sp12sl2Hk3Hkz2NB3PB23LSL3SPR4SP1RS2dN2kz3HkzS2sp2dN1k2kz3sp12sl2Hk3Hkz3LSLS1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA1h2LB2LF1m2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc2dX2lo2mo2Rr3PHI2FR2dA2dE2dN2kz3sp12mq3xt13xt23xs73xs83xs93xt33xt43xt53xt62Hk3HkzS2sp2dN1k2kz3sp12sl2Hk3Hkz3LSL2K2S2sp2dN1k2kz3sp12sl2Hk3Hkz4LENN2NB3LSL3SPR4SP1R1NS1R2lo3LOSS2sp2dN1k2kz3sp12sl2Hk3LSLS2sp2dN1k2kz3sp12sl2Hk3Hkz2NB3PB23LSL3SPR4SP1RS2sp2dN1k2kz3sp12sl2Hk3Hkz2NB3PB23LSL3SPR4SP1RS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRS2dN1k2kz2sl2Hk3PB23LSLS2dN1k2kz2sl2Hk3LSLS2dN1k2kz2sl2Hk3Hkz3LSLS2dN1k2kz2sl2Hk3Hkz3LSLS2dN1k2kz2sl2Hk3Hkz3LSLS2dN1k2kz2sl2Hk3LSLS2dN1k2kz2sl2Hk3LSLS2dN1k2kz2sl2Hk3LSLS2dN1k2kz2sl2Hk3LSLS2dN1k2kz2sl2Hk3LSL". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSMAP SSL SLL SS0 MX0 CRX DSX XL0 PHI0 FR0 NSX RR4"] Lemma scanN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Psp1,$13.Pmq,P,(16.&40.)(26.(16.&8.))Psl,(24.(16.&40.))Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pxa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(4?.R12.R11.R10.)P,(3;.R12.VdN,)P,(17.+1.(;.VdN,))P,Pya0,(16.&40.)Pya1,(16.&40.)Pya2,(16.&40.)(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:083<.)(7.&40.R18.)Vgp,Vtp,R15.R14.R13.Vsp,(7.&40.=)R3.R2.R1.R?.R>.R=.R<.R;.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R18.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))Vs11,R:.R9.R8.R7.)VF,(7.&40.+:0890.)Vfc,(41.(16.&40.))R17.(55.$2.)))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:083<.)(7.&40.R16.)Vgp,Vtp,R13.R12.R11.Vsp,(7.&40.=)R10.R?.R>.R=.R<.R;.R:.R9.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R16.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))Vs10,Vs11,R8.R7.R6.R5.)VF,(7.&40.+:0848.)Vfc,(41.(16.&40.))R15.(55.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros sp1 mq sl t0 t1 t2 xa0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EB VN N1 KF'.
    emb_open EB. rt_facts.
    ddestruct VN as (CE & BY & LENN & NRN & SGN & NB & PBN & NAL & ON & ONL & PB2 & MDN).
    pose proof (ONL N1) as OL.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    destruct PBN as [PBN|[PBN1 PBN2]]; [exfalso; clear - PBN N1; lia|].
    (* [comment removed for export] *)
    zstep_to [657532]. shadow_chk OL (md_p dN) 4.
    (* [comment removed for export] *)
    pose proof (u32s_length (md_limbs dN)) as ULN. pose proof (u32ro_bound _ _ _ _ BY) as BYB.
    rd8 BY 0. zstep_to [657548]. zstep. if_cases K3; [eapply em_exit; [exact EB| exact RR4]|]. clear K3.
    - (* [comment removed for export] *)
      + (* [comment removed for export] *)
        eapply KF'.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation RE sp1 xt0 xt1 xt2 xa0 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (mkR ra (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 (N + 10)) xa0 (Z_to_bv 64 A) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 N) (Z_to_bv 64 0) xa6 xa7
         (SH N) s3 (Z_to_bv 64 X) SBw (SH (N + 10)) (Z_to_bv 64 (E + 10)) (Z_to_bv 64 (Z.shiftr E 3)) (SH (E + 10)) (Z_to_bv 64 (sp1 + 128)) (SH (sp1 + 96)) xt3 xt4 xt5 xt6).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L11762865365.3  L13284853040.119L16575650497.119L18292428764.116L24815139881.118L35653441506.7  L50081380530.119L50954860132.69 L59314841581.117L60098763854.3  L8929159528.114 L8942128512.111 L9356559676.11  Q2183115807.117 Q22043167663.117Q26295627581.117Q27197904934.114Q27210147641.117Q27210507184.119Q35463523389.114Q3727687810.119 Q50458135125.117Q8956078776.114 00000;00b01<01k02I02a03B05K06=06G07607e08P08g09>09Q09d0:70:J0:a0;80;K0;^S2dE2kz3HkzS2sp2dE1k2kz3sp12sl2Hk3EB03LSL3SPR4SP1RS2sp2dE1k2kz3sp12sl2Hk3LSLS2sp2dE1k2kz3sp12sl2Hk3Hkz3EB03PB23LSL3SPR4SP1RS2sp2dE1k2kz3sp12sl2Hk3Hkz3LSLS1R3HIA1h2sp2lo3TOP4HTOPS2sp2dE1k2kz3sp12sl2Hk3Hkz3LSL2K2S1R3HIA1h2LB2LF1m2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc2dX2lo2mo2Rr3PHI2FR2dA2dE2dN2kz3sp12mq3xt23xt33xt43xt53xt62Hk3HkzS2sp2dE1k2kz3sp12sl2Hk3Hkz4LENE3EB03LSL3SPR4SP1R1NS1R2lo3LOSS2sp2dE1k2kz3sp12sl2Hk3Hkz3EB03PB23LSL3SPR4SP1RS2sp2dE1k2kz3sp12sl2Hk3Hkz3EB03PB23LSL3SPR4SP1RS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRS2dE1k2kz2sl2Hk3Hkz3LSLS2dE1k2kz2sl2Hk3PB23LSLS2dE1k2kz2sl2Hk3LSLS2dE1k2kz2sl2Hk3LSLS2dE1k2kz2sl2Hk3LSLS2dE1k2kz2sl2Hk3LSLS2dE1k2kz2sl2Hk3Hkz3LSLS2dE1k2kz2sl2Hk3Hkz3LSLS2dE1k2kz2sl2Hk3LSLS2dE1k2kz2sl2Hk3LSL". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL"] Lemma scanE : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Psp1,$13.Pmq,P,(16.&40.)(26.(16.&8.))Psl,(24.(16.&40.))Pxt0,(16.&40.)Pxt1,(16.&40.)Pxt2,(16.&40.)Pxa0,(16.&40.)Pxa1,(16.&40.)Pxa2,(16.&40.)Pxa3,(16.&40.)Pxa4,(16.&40.)Pxa5,(16.&40.)Pxa6,(16.&40.)Pxa7,(16.&40.)Pxt3,(16.&40.)Pxt4,(16.&40.)Pxt5,(16.&40.)Pxt6,(16.&40.)P,(4?.R12.R11.R10.)P,(3;.R12.VdE,)P,(18.(17.(1:.(3.VdE,)+10.)Vlo,)(17.(28.&40.Vsp,)(3.VdE,)))P,Pm',P,(16.&40.)(26.(16.&8.))Psl',(24.(16.&40.))Pya2,(16.&40.)P,(4?.R18.R3.R2.)P,(12.(26.(16.&40.))(57.(16.&40.)R3.#:.)(58.(16.&40.)(7.&40.(1:.(48.(3.VdE,)+3.)(49.(1>.VR,))))))P,(12.(26.(16.&40.))(57.(16.&40.)R4.#;.)(58.(16.&40.)(7.&40.(1:.(48.(1:.(3.VdE,)+:.)+3.)(49.(1>.VR,))))))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:08;<.)(7.&40.R1;.)Vgp,Vtp,R18.R17.R16.Vsp,(7.&40.=)(7.&40.(8.VdE,))(7.&40.(;.VdE,))R4.R12.R11.R10.R?.R>.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R1;.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))(7.&40.(1:.(3.VdE,)+:.))R=.R<.R;.R:.)VF,(7.&40.+:0908.)Vfc,(41.(16.&40.))R6.(55.$2.)))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:08;<.)(7.&40.R16.)Vgp,Vtp,R13.R12.R11.Vsp,(7.&40.=)R10.R?.R>.R=.R<.R;.R:.R9.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R16.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))Vs11,R8.R7.R6.R5.)VF,(7.&40.+:08<8.)Vfc,(41.(16.&40.))R15.(55.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros sp1 mq sl xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 EB VE DSE K.
    emb_open EB. rt_facts.
    ddestruct VE as (CE & BY & LENE & NRE & SGE & EB0 & PBE & EAL & OE & OEL & PB2 & MDE).
    repeat (destruct sl as [|? sl]; [discriminate LSL|]). destruct sl; [| discriminate LSL]. clear LSL. cbn [map] in SPILL.
    unfold EM_POISON in SHC.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    (* [comment removed for export] *)
    destruct DSE as [DSE|DSE]; zstep_to [657656]; shadow_chk OE (E + 10) 2;
    (* [comment removed for export] *)
    zstep; rewrite ?zx16_small by (clear - NRE; lia); emb_close sp1 EB2.
    - (* [comment removed for export] *)
      + (* [comment removed for export] *)
        eapply (K _ _ _ EB2); first [reflexivity | cbn [nth_error]; f_equal; f_equal; clear; lia].
    - eapply (K _ _ _ EB2); first [reflexivity | cbn [nth_error]; f_equal; f_equal; clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0?L10134628787.4 L10876717696.5 L11999187128.6 L18080252378.11L20569440628.4 L22706556809.9 L23927528628.8 L27739284940.7 L34036982883.4 L35653441506.7 L3730675808.4  L39188636933.0 L39332637397.0 L4029010041.6  L40622469209.2 L42437087959.3 L44353706781.3 L456726504.6   L57031302710.7 L5832837669.4  L59654577821.4 L60098763854.3 L62018535662.1 L64052154934.7 L64683549666.9 L7483610394.11 00000;00H00S00f01401O01l02C02M02e03203303403B03I03T03^03o04J04Y04f05005305N05o06IS2sp2lo3sp1S3sp11a1b1n1DS1R3sp11a1QS1R2lo3LOS3sp11a2HaS2sp3sp11a3SP1S1R2sp2lo3sp11a2Ha3SP11x2HxS1R3HIA1h2sp3TOP3sp13SP14HTOPS1R2lo3LOS3sp11a2Ha3ALOS2sp3sp11aS1R3HIA1h2sp2lo3TOP4HTOPS2lo3sp11a2HaSSS2sp3sp11a3SP1S1R3sp1S1R3slo3SSLS3sp12sl1aS2sp2lo3sp11a3SP1S1R2sp2lo3SLO5NEEDE3sp13SP1S2sp2lo3sp13SP1S2lo3sp11a2HaS1R2lo3LOSS1RS1R2sp2lo3SLO5NEEDE3sp13SP1S1R3HIA1h2sp3slo3TOP3sp13SP14HTOPS1R3HIA1h2sp3TOP3sp11a3SP1". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 mo SSL"] Lemma emb_munch : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Psp1,$13.Pmq,P,(16.&40.)(26.(16.&8.))Psl,(24.(16.&40.))Pm',P,(16.&40.)(26.(16.&8.))Pa,$13.P,(4?.R5.R4.R3.)P,(0.(17.Vlo,R2.)(19.R2.R6.))P,(4=.(4.(38.$13.$13.)(39.$13.$13.R3.R7.)(>.(38.$13.$13.)))R6.R4.)P,(4>.$2.R7.R5.)P,(35.$2.R6.)P,(47.$2.R7.Vlo,R:.)(4?.R;.R8.R9.)")
(* [comment removed for export] *).
  Proof.
    intros sp1 mq sl m' a EB Ha MUc WMc MI' ST'. emb_open EB. rt_facts.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (WC : w_client CS [(a, sp1)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear - Ha; lia| clear - Ha SP1; lia]| apply Forall_nil]. }
    assert (DJ : forall b n, (b + n <= a \/ sp1 <= b) -> disjoint_from [(a, sp1)] b n) by (intros b n D; cbn [disjoint_from]; split; [clear - D; lia| exact I]).
    assert (SCW : crange CS (sp1 + 96) (12 * 8)) by (eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]).
    unfold EMB. split; [exact SP1|]. split; [exact SP1M|].
    split. { eapply (hm_munch asegs R HIA h LB LF _ mq m'); [exact HHq| exact MUc| exact WMc|].
             apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. apply w_writable_of_client_wrange. apply client_wrange_stack; clear - Ha LOS SP1 TOP; lia. }
    split; [eapply rw_cells_transport; [exact SAVE| exact MUc| exact WMc| apply DJ; simpl_sizes; clear - SP1; lia]|].
    split; [eapply rw_cells_transport; [exact SPILL| exact MUc| exact WMc| apply DJ; clear; lia]|]. split; [exact LSL|].
    split; [eapply stk_transport_disjoint; [exact SThi| exact MUc| exact WMc| apply DJ; clear - SP1; lia]|].
    split; [exact ST'|]. split; [exact MI'|].
    split. { eapply rw_cells_transport; [exact SHC| exact MUc| exact WMc|]. apply DJ. unfold EM_POISON. simpl_sizes.
             destruct (apart_shadow_client AL CS a (sp1 - a) (sp1 + 96) (Z.shiftr (sp1 + 96) 3 + al_sb AL) 12 CSOK) as [Q|Q];
               [eapply crange_sub; [exact SCS| clear - Ha; lia| clear - Ha SP1; lia]| exact SCW
               | unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia| clear - Ha; lia| clear; lia| |];
               clear - Q Ha; lia. }
    split; [eapply (sshad_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS0| clear - SSL; lia| clear - SP1 TOP HTOP; lia]| exact MUc| exact WMc| exact SSlo]|].
    split; [eapply (sshad_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]| exact MUc| exact WMc| exact SShi]|].
    split; [eapply (snapA_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS0| clear; lia| clear - SP1 TOP HTOP; lia]| exact MUc| exact WMc| exact SNlo]|].
    split; [eapply (snapA_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]| exact MUc| exact WMc| exact SNhi]|].
    split. { eapply (presW_munch asegs R HIA h); [exact PRES| exact MUc| exact WMc| exact WC|].
             apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. eapply (wcover_of_stack asegs R HIA h); [exact PRES| clear - Ha LOS ALO; lia| clear - Ha SP1; lia]. }
    split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUc]; intros x Hx; cbn [outside] in *; clear - Hx Ha SP1; lia|].
    eapply wmono_trans; [exact WM| exact WMc].
    all: match goal with |- ?g => idtac "EMBM-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MN0 : mpd_at asegs m LB dN.
  Hypothesis SXN : X + 16 <= N \/ N + 16 <= X.
  Hypothesis OSN : opnd_sep dX dN lo (bv_unsigned sp).
  Hypothesis CRN : client_range L (LB ++ fdata LF) lo N 16.
  Hypothesis CRNL : md_own dN = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dN) (4 * md_n dN).
  Hypothesis ODN : mpd_aobjA asegs AL CS m dN.
  Hypothesis IMN : mpd_imgA dN.
  Hypothesis ME0 : mpd_at asegs m LB dE.
  Hypothesis SXE : X + 16 <= E \/ E + 16 <= X.
  Hypothesis OSE : opnd_sep dX dE lo (bv_unsigned sp).
  Hypothesis CRE : client_range L (LB ++ fdata LF) lo E 16.
  Hypothesis CREL : md_own dE = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dE) (4 * md_n dE).
  Hypothesis ODE : mpd_aobjA asegs AL CS m dE.
  Hypothesis IME : mpd_imgA dE.

  #[using="IMG HH0 MI0 MN0 SXN OSN CRN CRNL ODN IMN"] Lemma emb_viewN : forall sp1 mq sl, EMB sp1 mq sl -> VIEW mq dN.
  Proof. intros sp1 mq sl EB. emb_open EB. eapply em_view; eassumption. Qed.
  #[using="IMG HH0 MI0 ME0 SXE OSE CRE CREL ODE IME"] Lemma emb_viewE : forall sp1 mq sl, EMB sp1 mq sl -> VIEW mq dE.
  Proof. intros sp1 mq sl EB. emb_open EB. eapply em_view; eassumption. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0110@L11830469135.3  L15043131708.146L21703347828.2  L22594986486.2  L22726192844.3  L35653441506.7  L38418633005.134L39172636981.0  L43935878913.134L43935886280.137L47492451383.128L47492451383.137L58641002120.124L59308628179.3  L59308628304.4  L59314841581.145L60098763854.3  L62482812546.139L62482820040.124L62482879988.127L62485383624.136L63389698527.148L8288012388.1   L9356559676.11  Q12483333515.141Q16285785003.129Q17968854497.128Q17969015064.129Q17982002695.126Q18152175808.132Q18152175808.141Q26295627581.143Q28250278547.131Q28252264111.140Q2991978521.131 Q2994447397.140 Q30139424658.147Q30188290649.141Q31600242951.132Q31600242951.141Q31820333557.126Q34080507509.143Q39212284437.129Q39212284437.141Q46531759602.143Q50458135125.143Q51752217908.128Q57124660775.140Q58049729908.138Q59141654149.140Q59142923526.138Q59142937144.141Q60305443321.129Q60511567613.129Q60511567613.141Q63077529488.140Q66946372256.131Q66946421281.143Q66946848424.147Q66946854044.132Q66946854044.141Q66949402268.140Q8946157850.140 Q9534663128.126 Q9538464249.138 00000;00Q00Y00a00l01D02402502J02_03103C03X03c04304j05405d06:06S07C07Y07]08H08V08d08o09:09E09P09[09f0:10:<0:G0:R0:j0;50;\0<C0<N0<b0<m0=80=H0=S0=^0>20>=0>H0>S0>^0>i0?40??0?J0?U0?`0?o0@:0@E0@P0@[0@f0A1S2dN3NRN2K0S2sp2dN3sp12sl3LSL3ULNS2dN3NRNS2dN3NRNS2dN3NRN2K0S1R3HIA1h2sp2lo3TOP4HTOPS2sp2dN3sp12sl3LSL3SPR2NB4PBN13PB24SP1R3kz'4Hkz'SS2sp2dN3sp12sl3LSL2NBS2sp2dN3sp12sl3LSL2NBS2sp2dN3sp12sl3LSLS2sp2dN3sp12sl3LSLS2sp2dN3sp12sl3LSL2NBS2dN3PBN2K0S2dN3kz'4Hkz'2K1S2sp2dN3sp12sl3LSL3SPR4LENN2NB4PBN14SP1R3kz'4Hkz'3ULN1NS1R2lo3LOSS2sp2dN3sp12sl3LSL3SPR2NB4PBN13PB24SP1R3kz'4Hkz'S2sp2dN3sp12sl3LSL3NRNS2sp2dN3sp12sl3LSL2NB3NRNS2sp2dN3sp12sl3LSL3SPR2NB4PBN13PB24SP1R3kz'4Hkz'S2sp2dN3sp12sl3LSL3ULNS2dNS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRS2dN2sl3LSL2NBS2dN2sl3LSL2NBS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSL3kz'4Hkz'3ULNS2dN2sl3LSLS2sp2dN3sp12sl3LSL3SPR2NB4PBN13NAL4SP1RS2sp2dN3sp12sl3LSL3SPR2NB4PBN13NAL4SP1RS2dN2sl3LSLS2dN2sl3LSL3kz'4Hkz'S2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSL4PBN1S2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSL3kz'4Hkz'S2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSL3ULNS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSLS2dN2sl3LSL". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 MI0 SSMAP SSL SLL SS0 MX0 CRX DSX XL0 PHI0 FR0 NSX RR4 MN0 SXN OSN CRN CRNL ODN IMN"] Lemma chkN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Psp1,$13.Pmq,P,(16.&40.)(26.(16.&8.))Psl,(24.(16.&40.))Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(4?.R11.R10.R?.)P,Pya0,(16.&40.)Pya1,(16.&40.)Pya2,(16.&40.)P,(17.+1.(;.VdN,))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:083<.)(7.&40.R16.)Vgp,Vtp,R13.R12.R11.Vsp,(7.&40.=)R4.R3.R2.R>.R=.R<.R;.R:.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R16.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))Vs11,R9.R8.R7.R6.)VF,(7.&40.+:0890.)Vfc,(41.(16.&40.))R15.(55.$2.)))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:083<.)(7.&40.R13.)Vgp,Vtp,R10.R?.R>.Vsp,(7.&40.=)(7.&40.(5:.(5;.VdN,)))R=.R<.R;.R:.R9.R8.R7.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R13.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))Vs10,Vs11,R6.R5.R4.R3.)VF,(7.&40.+:0844.)Vfc,(41.(16.&40.))R12.(55.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EB KE. pose proof (emb_viewN _ _ _ EB) as VN.
    dpose VN as (CE & BY & LENN & NRN & SGN & _).
    zstep. if_cases K0; zify_cond K0.
    { eapply em_exit; [exact EB| exact RR4]. }
    assert (N1 : 1 <= md_n dN).
    { destruct (Z_lt_le_dec 0 (md_n dN)) as [P|P]; [clear - P; lia|]. exfalso.
      assert (EL : md_limbs dN = []) by (destruct (md_limbs dN); [reflexivity| cbn [length] in LENN; clear - LENN P; lia]).
      assert (V0 : Z.sgn (mpd_val dN) = 0) by (unfold mpd_val; rewrite EL; cbn [limbs_val]; rewrite Z.mul_0_r; reflexivity).
      match goal with H : 0 < Z.sgn (mpd_val dN) mod _ |- _ => rewrite V0 in H; revert H end. clear. vm_compute. intros K; discriminate K. }
    (* [comment removed for export] *)
    eapply scanN; [exact EB| exact VN| exact N1|]. intros ya0 ya1 ya2. eapply KE. exact N1.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L20771900360.3 L24364708814.7 L27938763061.13L27940684716.11L3482512389.11 L3484442268.13 L35653441506.7 L38235734261.1 L41691824508.13L44335583989.11L60098763854.3 L7030081863.172L9080220944.4  L9160756122.11 L9356559676.11 00000:00U01001K01U01_02702;02M02T02^03703F03g04RS1d3NRD2NNS1R2sp2lo3SLO5NEEDE3sp13SP1S1R2sp2lo3SLO5NEEDE3sp13SP1S1R2sp2lo3SLO5NEEDE3sp13SP1S3sp14SP1MS3sp14SP1MS1R3HIA1h2sp2lo3TOP4HTOPS2loS1d3sp13PB23OWN2N0S1d3sp1S1R2lo3LOSS2sp1d3sp12sl3RET3RRg3LSLS2sp2lo3sp13SP1S1R2sp2lo3SLO5NEEDE1d3sp13SP13DS'S1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL"] Lemma bl_call : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Pd,$22.Psp1,$13.Pmq,P,(16.&40.)(26.(16.&8.))Psl,(24.(16.&40.))PRET,$13.Pxra,(16.&40.)Pxt0,(16.&40.)Pxt1,(16.&40.)Pxt2,(16.&40.)Pys0,(16.&40.)Pys1,(16.&40.)Pxa2,(16.&40.)Pxa3,(16.&40.)Pxa4,(16.&40.)Pxa5,(16.&40.)Pxa6,(16.&40.)Pxa7,(16.&40.)Pys2,(16.&40.)Pys3,(16.&40.)Pys4,(16.&40.)Pys5,(16.&40.)Pys6,(16.&40.)Pys7,(16.&40.)Pys8,(16.&40.)Pys9,(16.&40.)Pys10,(16.&40.)Pys11,(16.&40.)Pxt3,(16.&40.)Pxt4,(16.&40.)Pxt5,(16.&40.)Pxt6,(16.&40.)P,(4?.R1>.R1=.R1<.)P,(3;.R1>.R20.)P,P,(3>.(12.$2=.(2>.R21.)$42.))(18.(17.(1:.(8.R22.)(20.+4.(;.R22.)))Vlo,)(17.(28.&40.Vsp,)(8.R22.)))P,(12.(16.&40.)R1=.(7.&40.R1>.))P,(12.$13.(1<.R1?.+2.)=)P,(0.(17.=R20.)(19.R20.(1;.+2.+40.)))P,Pm',P,(16.&40.)(26.(16.&8.))Pyt0,(16.&40.)Pyt1,(16.&40.)Pyt2,(16.&40.)Pya0,(16.&40.)Pya1,(16.&40.)Pya2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Pyt3,(16.&40.)Pyt4,(16.&40.)Pyt5,(16.&40.)Pyt6,(16.&40.)P,(4?.R34.R10.R32.)(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.R31.(7.&40.R35.)Vgp,Vtp,R10.R?.R>.R2=.R2<.R=.R<.R;.R:.R9.R8.R7.R6.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R5.R4.R3.R2.)VF,(7.&40.R32.)Vfc,(41.(16.&40.))R11.(55.$2.)))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.R21.(7.&40.R25.)Vgp,Vtp,R20.R1?.R1>.R1=.R1<.(7.&40.(8.R26.))(7.&40.(;.R26.))R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)VF,(7.&40.$56.)Vfc,(41.(16.&40.))R24.(55.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros EB VD DS -> RE RRg K. emb_open EB. rt_facts.
    ddestruct VD as (CE & BY & LEND & NRD & SGD & DB & PBD & DAL & OD & ODL & PB2 & MDD).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    pose proof (hm_abase asegs R HIA h LB LF mq HHq) as ABq.
    assert (OWN : (md_p d = 0 /\ md_n d = 0) \/ (md_own d <> LNull /\ 1 <= md_n d)).
    { pose proof MDD as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own d); [left; exact OW| right; split; [discriminate| exact (proj1 OW)]| right; split; [discriminate| exact (proj1 OW)]]. }
    pose proof (A_mpi_core_bitlen_z_spec AL IMG) as SPZ. pose proof (A_mpi_core_bitlen_spec AL IMG) as SPB.
    unfold mpi_core_bitlen_z_stmtA, A_MPI_CORE_BITLEN in SPZ. unfold mpi_core_bitlen_stmtA, A_MPI_CORE_BITLEN in SPB. unfold A_MPI_CORE_BITLEN.
    assert (TAIL : forall xs n ms', mpi_core_bitlen_postA asegs (Z_to_bv 64 RET) (Z_to_bv 64 sp1) gp tp ys0 ys1 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 F fc xs n lo mq ms' ->
              aevtA asegs (KF asegs R HIA h mo) POSTA ms').
    { intros xs n ms' PO. unfold mpi_core_bitlen_postA, MPI_CORE_BITLEN_STACK_A in PO. rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
      ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m' & -> & MUc & WMc & MIc & _ & STc).
      replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET) by (symmetry; apply ret_pc_even; [lia | exact RE]).
      eapply K. eapply (emb_munch sp1 mq sl m' (sp1 - 16)); [exact EB| clear - SP1 SLO NEEDE; lia| exact MUc| exact WMc| exact MIc| exact STc]. }
    destruct (Z.eq_dec (md_n d) 0) as [N0|NN]; (eapply (aevtA_cut_evtA_KF asegs R HIA h mo); [| eapply TAIL]).
    - rewrite N0. eapply SPZ with (CS := CS) (A := md_p d) (lo := lo);
          rewrite ?(unsigned_lit sp1) by exact SP1R;
          first [ exact MIq | exact STlo | exact CSOK | exact ABq | exact (art_alwf asegs R HIA) | reflexivity
                | eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]
                | unfold MPI_CORE_BITLEN_STACK_A; clear - SP1 SP1M SLO NEEDE PB2 NRD OWN N0; first [lia | Z.div_mod_to_equations; lia]
                | match goal with |- ?g => idtac "BLZ-PRE-LEFT:" g end ].
    - destruct PBD as [PBD|[PBD1 PBD2]]; [exfalso; exact (NN PBD)|]. destruct OWN as [[_ N0']|[OWN _]]; [exfalso; exact (NN N0')|].
      eapply SPB with (CS := CS) (A := md_p d) (n := md_n d) (lo := lo) (xs := md_limbs d);
          rewrite ?(unsigned_lit sp1) by exact SP1R;
          first [ exact BY | exact MIq | exact STlo | exact CSOK | exact ABq | exact (art_alwf asegs R HIA) | exact PBD1 | exact PBD2 | exact NRD | reflexivity
                | apply ODL; clear - NN NRD; lia
                | eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]
                | rewrite ?LEND; unfold MPI_CORE_BITLEN_STACK_A; pose proof (DS OWN) as DS'; clear - SP1 SP1M SLO NEEDE DS' NRD; first [lia | Z.div_mod_to_equations; lia]
                | match goal with |- ?g => idtac "BL-PRE-LEFT:" g end ].
    all: match goal with |- ?g => idtac "BL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation RF sp1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (mkR (Z_to_bv 64 0xa0944) (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 (N + 10)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         (SH N) (Z_to_bv 64 N) (Z_to_bv 64 X) SBw (SH (N + 10)) (Z_to_bv 64 (E + 10)) (SH E) (SH (E + 10)) (Z_to_bv 64 (sp1 + 128)) (SH (sp1 + 96)) xt3 xt4 xt5 xt6).
  Definition SLOTS (sl : list word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "(0.(12.(26.(16.&40.))(57.(16.&40.)O1.#8.)(58.(16.&40.)(7.&40.(1:.(48.(1:.(3.VdN,)+:.)+3.)(49.(1>.VR,))))))(0.(12.(26.(16.&40.))(57.(16.&40.)O1.#9.)(58.(16.&40.)(7.&40.(1:.(3.VdN,)+:.))))(0.(12.(26.(16.&40.))(57.(16.&40.)O1.#:.)(58.(16.&40.)(7.&40.(1:.(48.(3.VdE,)+3.)(49.(1>.VR,))))))(12.(26.(16.&40.))(57.(16.&40.)O1.#;.)(58.(16.&40.)(7.&40.(1:.(48.(1:.(3.VdE,)+:.)+3.)(49.(1>.VR,)))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01Y0@D21667997106.147D21667997106.148D60189065437.147D60189065437.148L11765020826.3  L1685717371.0   L22594986486.2  L23072471841.0  L35653441506.7  L36459744067.145L37196404897.0  L41799535211.190L45357801578.2  L47492451383.170L57698627611.2  L58641002120.170L58641002120.190L60098763854.3  L9356559676.11  P57713046236.147P57713046236.148Q10149575540.147Q10149575540.148Q11597359476.192Q11801279589.147Q11801279589.148Q13400466953.144Q1345703177.144 Q16285785003.175Q17968854497.174Q17969015064.175Q17971062944.172Q18152175808.173Q19398699415.143Q20414272036.147Q20414272036.148Q20608191892.144Q23833845127.144Q23927705296.147Q23927705296.148Q27882953602.147Q27882953602.148Q28250262034.174Q28465177121.144Q28465177121.145Q2994075936.172 Q30064061911.194Q31600242951.173Q31814123346.172Q3421936230.146 Q3421936230.147 Q34423045936.145Q37471993808.195Q39035803284.144Q39180574961.147Q39180574961.148Q39212284437.175Q39212284437.195Q41265738516.144Q41368571430.195Q41410744564.195Q41412728269.192Q41413135433.194Q42439443119.147Q42439443119.148Q4447376314.145 Q51087705995.147Q51087705995.148Q5129158642.147 Q5129158642.148 Q51752217908.174Q5265442331.145 Q5265442331.146 Q53882835466.143Q55415036769.147Q55415036769.148Q57037327601.147Q57037327601.148Q57228775306.146Q57228775306.147Q58125335435.147Q58125335435.148Q59026489841.149Q59028897108.144Q59030962408.145Q59865321072.147Q59865321072.148Q60305443321.175Q60511567613.175Q60511567613.195Q6186103236.147 Q6186103236.148 Q62011970312.147Q62011970312.148Q64041402609.147Q64041402609.148Q64683667846.147Q64683667846.148Q66946421281.174Q66946854044.173Q66948469657.172Q68602471406.149Q7381151881.144 Q9540490238.192 Q9540491135.172 00000g01a02_03`03l03m04504604N04Y04Z04l05505C05D05V05h06206]07;07\08908Y08]08^08_09=09[09f09m0:40:;0:B0:`0;M0<=0<O0<S0=B0>40>50>60>=0>M0>]0>d0>h0?L0?S0@40@X0@\0@d0A60Ak0Bc0Bj0Bn0C@0CD0CH0CL0CP0D10DU0Dl0EC0E]0E^0E_0Ef0F70FH0FZ0G80GY0HF0I60Ic0JS0Jj0KD0KH0KL0KP0KQ0KR0KY0K]0Ka0LB0Lf0M?0M[0NH0O80Ok0Pa0Ph0Po0Q60Q:0QX0Q\0Q`S1R3HIA1h2sp3TOP2dE3sp13EB03SP13SPR4SP1R2HB5Ha_st5Hl_stS1R3HIA1h2sp3TOP2dA2dE3sp13EB03SP13SPR4SP1R2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE2dE3sp13EB03SP13SPR4SP1R2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE2dA2dE3sp13EB03SP13SPR4SP1R2HB5Ha_st5Hl_stS2dE4NRE42K3SS2dN3NRNSS1R3HIA1h2sp2lo3TOP4HTOPS2sp2dE3sp1SS2sp2dE2dN3sp13NRES2dE4NRE4S2sp2dE2dN3sp1FS2sp2dE2dN3sp13NB3S2sp2dE2dN3sp13EB0S1R2lo3LOSS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRS2sp2dE3sp13SP12HB5Ha_st5Hl_stS2sp2dA2dE3sp13SP12HB5Ha_st5Hl_stS2sp2lo2dE3sp12HB5Ha_st5Hl_stS2sp2lo2dA2dE3sp12HB5Ha_st5Hl_stS2dEFFS1R2sp2lo3SLO5NEEDE2dE3sp13SP1S1R2sp2lo3SLO5NEEDE2dE3sp13SP1S2dE2dN3NB3S2dE2dNS2dE2dNS2dE2dNS2dE2dNS1R2sp2lo3SLO5NEEDE2dE3sp13SP1S1R2sp2lo3SLO5NEEDE2dE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE2dA2dE3sp13SP12HB5Ha_st5Hl_stS2sp2lo2dE3sp13SP1S2dES1R3HIA1h2sp3TOP2dE3sp13SP14HTOP2HB5Ha_st5Hl_stS1R3HIA1h2sp3TOP2dA2dE3sp13SP14HTOP2HB5Ha_st5Hl_stFFS2dE2dNS2dE3sp14SP1R2HBS2dE3sp14SP1R2HBS2dE2dNS2dES2sp2dE2dN3sp13EB03SPR4SP1R3NB34NAL3S2dE2dNS2sp2lo2dE3sp13SP12HB5Ha_st5Hl_stS2sp2lo2dA2dE3sp13SP12HB5Ha_st5Hl_stS2dES2dE3EB0S2sp2lo2dE3sp13SP1S1R2sp2lo3LOS3SLO5NEEDE2dE3sp13SP13ALO2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE2dA2dE3sp13SP13ALO2HB5Ha_st5Hl_stS2dE2dNS2dES2sp2lo2dE3sp13SP1S2dES2dES2dES2dES1R3slo3SSL2dE3sp12HB5Ha_st5Hl_stS1R3slo3SSL2dA2dE3sp12HB5Ha_st5Hl_stS2sp2dE3sp13EB03EAL3SPRS2dE3sp12HB5Ha_st5Hl_stS2dA2dE3sp12HB5Ha_st5Hl_stFFS2dE2dNS2dE3sp12HB5Ha_stS2dE3sp12HB5Ha_stS2sp2lo2dE3sp13SP1S2sp2dE3sp13SP12HB5Ha_st5Hl_stS2sp2dA2dE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE2dE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE2dA2dE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE2dE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE2dA2dE3sp13SP12HB5Ha_st5Hl_stS2dE3sp12HB5Ha_st5Hl_stS2dA2dE3sp12HB5Ha_st5Hl_stS2dES2dES2dEFFS2dE2dNS2dES2dES2sp2lo2dE3sp13SP12HB5Ha_st5Hl_stS2sp2lo2dA2dE3sp13SP12HB5Ha_st5Hl_stS1R2dE3sp12HB5Ha_st5Hl_stS1R2dA2dE3sp12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE2dE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE2dA2dE3sp13SP12HB5Ha_st5Hl_stS1R3HIA1h2sp3slo3TOP2dE3sp13SP14HTOP2HB5Ha_st5Hl_stS1R3HIA1h2sp3slo3TOP2dA2dE3sp13SP14HTOP2HB5Ha_st5Hl_stS2dE2dNS2dE2dNS2dE2dNS2dES1R2sp2lo3SLO5NEEDE2dE3sp13SP1S2dES2dE". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 MI0 SSMAP SSL SLL SS0 MX0 CRX DSX XL0 PHI0 FR0 NSX RR4 MN0 SXN OSN CRN CRNL ODN IMN ME0 SXE OSE CRE CREL ODE IME"] Lemma chk568 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Psp1,$13.Pmq,P,(16.&40.)(26.(16.&8.))Psl,(24.(16.&40.))Pxt0,(16.&40.)Pxt1,(16.&40.)Pxt2,(16.&40.)Pxa2,(16.&40.)Pxa3,(16.&40.)Pxa4,(16.&40.)Pxa5,(16.&40.)Pxa6,(16.&40.)Pxa7,(16.&40.)Pxt3,(16.&40.)Pxt4,(16.&40.)Pxt5,(16.&40.)Pxt6,(16.&40.)P,(4?.R10.R?.R>.)P,(12.(26.(16.&40.))(57.(16.&40.)R?.#:.)(58.(16.&40.)(7.&40.(1:.(48.(3.VdE,)+3.)(49.(1>.VR,))))))P,(12.(26.(16.&40.))(57.(16.&40.)R10.#;.)(58.(16.&40.)(7.&40.(1:.(48.(1:.(3.VdE,)+:.)+3.)(49.(1>.VR,))))))P,(17.+1.(;.VdN,))P,Pm',P,(16.&40.)(26.(16.&8.))Psl',(24.(16.&40.))Pyt0,(16.&40.)Pyt1,(16.&40.)Pyt2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Pyt3,(16.&40.)Pyt4,(16.&40.)Pyt5,(16.&40.)Pyt6,(16.&40.)P,(4?.R22.R>.R=.)P,(59.R>.)P,(17.+1.(;.VdN,))P,(17.+1.(;.VdE,))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:0944.)(7.&40.R26.)Vgp,Vtp,R10.R?.R>.Vsp,(7.&40.=)(7.&40.(1:.(3.VdN,)+:.))(7.&40.(;.VdE,))(7.&40.(1:.(48.(1:.(3.VdN,)+:.)+3.)(49.(1>.VR,))))R=.R<.R;.R:.R9.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R26.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))(7.&40.(1:.(3.VdE,)+:.))R8.R7.R6.R5.)VF,(7.&40.+:0968.)Vfc,(41.(16.&40.))R12.(55.$2.)))P,Pm',P,(16.&40.)(26.(16.&8.))Psl',(24.(16.&40.))Pyt0,(16.&40.)Pyt1,(16.&40.)Pyt2,(16.&40.)Pya2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Pyt3,(16.&40.)Pyt4,(16.&40.)Pyt5,(16.&40.)Pyt6,(16.&40.)P,(4?.R24.R?.R>.)P,(59.R?.)P,(17.+1.(;.VdN,))P,(12.$13.(;.VdE,)=)(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:0944.)(7.&40.R28.)Vgp,Vtp,R11.R10.R?.Vsp,(7.&40.=)(7.&40.(1:.(3.VdN,)+:.))(7.&40.=)R>.R=.R<.R;.R:.R9.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R28.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))(7.&40.(1:.(3.VdE,)+:.))R8.R7.R6.R5.)VF,(7.&40.+:0:00.)Vfc,(41.(16.&40.))R13.(55.$2.)))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:08;<.)(7.&40.R16.)Vgp,Vtp,R13.R12.R11.Vsp,(7.&40.=)(7.&40.(8.VdE,))(7.&40.(;.VdE,))R10.R?.R>.R=.R<.R;.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R16.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))(7.&40.(1:.(3.VdE,)+:.))R:.R9.R8.R7.)VF,(7.&40.+:0908.)Vfc,(41.(16.&40.))R15.(55.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros sp1 mq sl xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 EB S10 S11 N1 KA KL.
    pose proof (emb_viewE _ _ _ EB) as VE. emb_open EB. rt_facts.
    dpose VE as (CE & BY & LENE & NRE & SGE & EB0 & PBE & EAL & OE & OEL & PB2 & MDE).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    repeat (destruct sl as [|? sl]; [discriminate LSL|]). destruct sl; [| discriminate LSL]. cbn [nth_error] in S10, S11.
    injection S10 as S10. injection S11 as S11. subst. dpose OSE as (_ & _ & _ & _ & OSE5). dpose OSN as (_ & _ & _ & _ & OSN5).
    (* [comment removed for export] *)
    zstep.
    eapply (bl_call dE sp1 _ _ 657676); [exact EB| exact VE| exact OSE5| reflexivity| reflexivity| clear; lia|].
    clear dependent mq; intros m3 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 EB3.
    zstep. zstep. if_cases K1; [eapply em_exit; [exact EB3| exact RR4]|]. clear K1.
    pose proof EB3 as EB3c. ddestruct EB3c as (_ & _ & HH3 & SAVE3 & SPILL3 & LSL3 & SThi3 & STlo3 & MI3 & SHC3 & SSlo3 & SShi3 & SNlo3 & SNhi3 & PRES3 & MU3 & WM3).
    cbn [map] in SPILL3. unfold EM_POISON in SHC3.
    pose proof (emb_viewN _ _ _ EB3) as VN3. dpose VN3 as (CN3 & _ & _ & NRN & _ & NB3 & _ & NAL3 & ON3 & _).
    zstep_to [657708].
    (* [comment removed for export] *)
    emb_close sp1 EB4. pose proof (emb_viewN _ _ _ EB4) as VN4. dpose VN4 as (CN4 & _ & _ & _ & _ & _ & _ & _ & ON4 & _).
    shadow_chk ON4 (N + 10) 2.
    zstep. emb_close sp1 EB5. pose proof (emb_viewN _ _ _ EB5) as VN5. pose proof VN5 as VN5c. dpose VN5c as (CN5 & _).
    zstep. rewrite zx16_small by (clear - NRN; lia). zstep.
    (* [comment removed for export] *)
    eapply (bl_call dN sp1 _ _ 657732); [exact EB5| exact VN5| exact OSN5| reflexivity| reflexivity| clear; lia|].
    intros m5 zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 EB6.
    zstep. zstep. if_cases K2; [eapply em_exit; [exact EB6| exact RR4]|]. clear K2.
    (* [comment removed for export] *)
    pose proof EB6 as EB6c. ddestruct EB6c as (_ & _ & HH6 & SAVE6 & SPILL6 & LSL6 & SThi6 & STlo6 & MI6 & SHC6 & SSlo6 & SShi6 & SNlo6 & SNhi6 & PRES6 & MU6 & WM6).
    pose proof (emb_viewE _ _ _ EB6) as VE6. dpose VE6 as (CE6 & _ & _ & NRE6 & _ & EB6' & _ & EAL6 & OE6 & _).
    cbn [map] in SPILL6. unfold EM_POISON in SHC6. zstep_to [657744].
    (* [comment removed for export] *)
    shadow_chk OE6 (E + 10) 2.
    zstep. rewrite zx16_small by (clear - NRE6; lia). zstep.
    (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by (clear - NRE6; lia).
    - rewrite K3. eapply KL; [exact EB6| unfold SLOTS; cbn [nth_error]; repeat split; first [reflexivity | f_equal; f_equal; f_equal; clear; lia]| exact N1| exact K3].
    - zstep. eapply KA; [exact EB6| unfold SLOTS; cbn [nth_error]; repeat split; first [reflexivity | f_equal; f_equal; f_equal; clear; lia]| exact N1| clear - K3 NRE6; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 MI0 SSMAP SSL SLL SS0 MX0 CRX DSX XL0 PHI0 FR0 NSX RR4 ME0 SXE OSE CRE CREL ODE IME"] Lemma em_cmpE : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Psp1,$13.Pmq,P,(16.&40.)(26.(16.&8.))Psl,(24.(16.&40.))Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pxa0,(16.&40.)Pxa1,(16.&40.)Pxa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(4?.R12.R11.R10.)P,Pm',P,(16.&40.)(26.(16.&8.))Psl',(24.(16.&40.))Pyt0,(16.&40.)Pyt1,(16.&40.)Pyt2,(16.&40.)Pya0,(16.&40.)Pya1,(16.&40.)Pya2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Pyt3,(16.&40.)Pyt4,(16.&40.)Pyt5,(16.&40.)Pyt6,(16.&40.)P,(4?.R24.R11.R10.)(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:08;<.)(7.&40.R25.)Vgp,Vtp,R10.R?.R>.Vsp,(7.&40.=)R=.R<.R;.R:.R9.R8.R7.R6.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R25.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))Vs11,R5.R4.R3.R2.)VF,(7.&40.+:08<8.)Vfc,(41.(16.&40.))R12.(55.$2.)))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:083<.)(7.&40.R14.)Vgp,Vtp,R11.R10.R?.Vsp,(7.&40.=)R>.R=.R<.R;.R:.R9.R8.R7.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R14.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))Vs11,R6.R5.R4.R3.)VF,(7.&40.+:0890.)Vfc,(41.(16.&40.))R13.(55.$2.)))").
  Proof.
    intros sp1 mq sl t0 t1 t2 xa0 xa1 xa2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EB K. pose proof (emb_viewE _ _ _ EB) as VE. emb_open EB. rt_facts.
    ddestruct VE as (CE & BY & LENE & NRE & SGE & EB0 & PBE & EAL & OE & OEL & PB2 & MDE). repeat (destruct sl as [|? sl]; [discriminate LSL|]). destruct sl; [| discriminate LSL]. clear LSL. cbn [map] in SPILL. unfold EM_POISON in SHC.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]). assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    dpose OSE as (OS1 & OS2 & OS3 & OS4 & OS5).
    c8cb_at SPILL 16%nat. c8cb_at SPILL 26%nat.
    zstep_to [657592].
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
    norm_b8 SHC.
    ddestruct IMG' as (EGOT & ELO & EHI).
    pose proof (presW_presA asegs R HIA h _ _ _ _ _ _ _ PRES) as HPA. pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HPA) as HPX.
    assert (CRk : client_range L (KEEP ++ fdata LF) (bv_unsigned sp) E 16).
    { pose proof (client_range_keep L LB LF lo dX E 16 CRE OS2) as C0.
      intros a Ha. destruct (C0 a Ha) as [S|[D|B]]; [left; clear - S Ha OS4; lia| right; left; exact D| right; right; exact B]. }
    assert (CRLk : md_own dE = LHeap -> client_range L (KEEP ++ fdata LF) (bv_unsigned sp) (md_p dE) (4 * md_n dE)).
    { intros EH. assert (NN : md_own dE <> LNull) by (rewrite EH; discriminate).
      assert (AP : md_own dX = LHeap -> md_p dE + 4 * md_n dE <= md_p dX \/ md_p dX + 4 * md_n dX <= md_p dE).
      { intros EX. destruct OS3 as [C|[C|[C|C]]]; [exfalso; rewrite C in SXE; clear - SXE; lia| exfalso; exact (C EX)| exfalso; exact (NN C)| clear - C; lia]. }
      pose proof (client_range_keep L LB LF lo dX (md_p dE) (4 * md_n dE) (CREL EH) AP) as C0.
      intros a Ha. destruct (C0 a Ha) as [S|[D|B]]; [left; pose proof (OS5 NN) as Q; clear - S Ha Q; lia| right; left; exact D| right; right; exact B]. }
    set (LBy := (sp1 + 128, 4) :: LB).
    assert (MDq : mpd_at asegs m2 LBy dE).
    { eapply (mpd_at_heap_presx asegs L m m2 LB (KEEP ++ fdata LF) LBy (bv_unsigned sp) WX dE); [exact ME0| exact HPX| exact MI0| exact MIq| exact CRk| exact CRLk| | | ].
      - cbn [disjoint_from]. split; [clear - SXE; lia| exact I].
      - intros EH. cbn [disjoint_from]. split; [pose proof (OS1 ltac:(rewrite EH; discriminate)) as Q; clear - Q; lia| exact I].
      - intros bk Hb. right. pose proof ME0 as [(_ & _ & _ & _ & _ & OW) _]. unfold mpd_blk in Hb. destruct (md_own dE); try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)). }
    assert (PNZ : md_own dE = LHeap -> 0 < md_p dE).
    { intros EH. pose proof ME0 as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (_ & HIN & _).
      destruct (hm_apart asegs R HIA h LB LF m HH0) as [HF _]. rewrite Forall_forall in HF. destruct (HF _ ltac:(apply in_or_app; left; exact HIN)) as (P0 & _). cbn in P0. exact P0. }
    assert (OSq : aobj asegs AL CS m2 E 16).
    { eapply (presA_aobj asegs R CS); [exact CSOK| exact HPA| exact (proj1 ODE)| exact CRk| clear; lia| intros x Hx; eapply hcs_below_top; exact Hx]. }
    assert (IMGCS : img_cs CS).
    { eapply img_cs_of; [exact ELO| exact (proj1 EHI)| exact EGOT| exact (proj2 EHI)|]. intros a n H1 H2 H3 H4. eapply (hcs_img asegs R HIA h); assumption. }
    assert (OPq : 1 <= md_n dE -> aobj asegs AL CS m2 (md_p dE) (4 * md_n dE)).
    { intros N1. pose proof ME0 as [(_ & _ & _ & _ & _ & OW) _].
      destruct (md_own dE) eqn:EOD; [exfalso; destruct OW as (_ & N0); clear - N0 N1; lia| |].
      - ddestruct OW as (_ & EIN & _). eapply hm_aobj_block; [exact HHq| exact EIN].
      - eapply (AImgGlobals.aobj_img asegs AL); [exact IMGCS| eapply (hm_img_shadow asegs R HIA); exact HHq| exact (IME EOD)]. }
    assert (OYq : aobj asegs AL CS m2 (sp1 + 200) 16).
    { pose proof (sshad_chunk asegs AL m2 (sp1 + 192) (bv_unsigned sp) 1 (sp1 + 200) SShi ltac:(clear; lia) ltac:(clear - SP1; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as SH.
      replace (shadow_of AL (sp1 + 200)) with (Z.shiftr (sp1 + 200) 3 + al_sb AL) in SH by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia).
      change 16 with (8 * Z.of_nat 2).
      eapply (aobj_of_zero_shadow_sh asegs AL CS m2 (sp1 + 200) (zcells 2) (sp1 + 200) 0 2 CSOK SH); [eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1R; lia| clear; lia|].
      intros i Hi. apply cell_at_zcells. exact Hi. }
    assert (OQq : aobj asegs AL CS m2 (sp1 + 128) 4).
    { assert (HB : (sp1 + 96) mod 8 = 0) by (clear - SP1M; Z.div_mod_to_equations; lia).
      lazymatch type of SHC with rw_cells _ _ _ ?cs => assert (HZ : cell_at cs 4 = Some (C1 (Z_to_bv 8 4))) by reflexivity end.
      pose proof SHC as H.
      replace (Z.shiftr (sp1 + 96) 3 + al_sb AL) with (shadow_of AL (sp1 + 96)) in H by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia).
      assert (HC : crange CS (sp1 + 128) 4) by (eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]).
      split; [exact HC|].
      intros a Ha. exists (Z_to_bv 8 4). split.
      - pose proof CSOK as OK. destruct OK as [C1' _]. destruct (C1' a (HC a Ha)) as (R0 & R1 & R2 & _).
        pose proof (rw_cells_read asegs m2 _ _ 4 _ H HZ) as RD. cbn [csize cbytes] in RD.
        assert (E0 : shadow_of AL a = shadow_of AL (sp1 + 96) + Z.of_nat 4).
        { unfold shadow_of.
          assert (E8 : a / 8 = (sp1 + 96) / 8 + Z.of_nat 4); [| rewrite E8; lia].
          pose proof (Z.div_mod (sp1 + 96) 8 ltac:(lia)) as DB. rewrite HB in DB.
          symmetry. apply (Z.div_unique a 8 ((sp1 + 96) / 8 + Z.of_nat 4) (a - (sp1 + 96) - 8 * Z.of_nat 4)); lia. }
        rewrite E0. apply (bytes_at_of_read1 asegs); [lia| lia| exact RD].
      - right. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow Z.of_N Pos.pow]. rewrite (Z.mod_small 4) by lia.
        pose proof (Z.div_mod (sp1 + 96) 8 ltac:(lia)) as DB. rewrite HB in DB.
        assert (EM : a mod 8 = a - (sp1 + 96) - 8 * Z.of_nat 4).
        { symmetry. apply (Z.mod_unique a 8 ((sp1 + 96) / 8 + Z.of_nat 4) (a - (sp1 + 96) - 8 * Z.of_nat 4)); lia. }
        rewrite EM. lia. }
    pose proof SPILL as SPc. cut_cells SPc 26%nat SPP SPY.
    lazymatch type of SPY with rw_cells _ _ ?a _ => replace a with (sp1 + 200) in SPY by (cbn; lia) end.
    cut_cells SPP 16%nat SQa SQb. cut_cells SQb 1%nat SPL0 SPM.
    lazymatch type of SPL0 with rw_cells _ _ ?a _ => replace a with (sp1 + 128) in SPL0 by (cbn; lia) end.
    clear SQa SPM.
    lazymatch type of SPY with rw_cells _ _ _ [_; _; CB 4 ?pb] => set (padb := pb) in SPY end.
    assert (LPB : length padb = 4%nat) by (destruct SPY as [[WF _] _]; exact (proj1 (proj2 (proj2 WF)))).
    set (dY := mkMPD (sp1 + 200) 1 1 (sp1 + 128) [Z_to_bv 64 0] (le_bytes_to_word padb) LHeap).
    assert (E4 : le4 (Z_to_bv 64 65537) = le2 (Z_to_bv 64 1) ++ le2 (Z_to_bv 64 1)).
    { rewrite le4_split. change (bv_unsigned (Z_to_bv 64 65537) / 2 ^ 16) with 1. f_equal. rewrite !le2_of_Z. rewrite <- (CellsX.Z_to_le_bytes_mod 2 65537). reflexivity. }
    assert (MY : mpd_at asegs m2 LBy dY).
    { unfold mpd_at, mpi_at, dY. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own length].
      split; [| left; reflexivity].
      split.
      { unfold mpi_cells. eapply rw_cells_reshape; [exact SPY| cbn; repeat split|].
        cbn [cells_bytes cbytes]. rewrite le4_le_bytes_to_word by exact LPB. rewrite E4, <- !app_assoc. reflexivity. }
      split; [clear - SP1M; Z.div_mod_to_equations; lia|].
      split; [clear - SP1 SLO LOS ALO ACP NEEDE; lia|].
      split; [reflexivity|].
      split; [unfold MPI_MAX_LIMBS; clear; lia|].
      split; [clear; lia|]. split; [left; reflexivity|]. split; [clear - SP1M; Z.div_mod_to_equations; lia|].
      eapply (u32arr_of_cells _ _ _ 4 (le4 (Z_to_bv 64 0))); [eapply rw_cells_reshape; [exact SPL0| cbn; split; [apply (length_le4 (Z_to_bv 64 0))| exact I]| cbn; rewrite ?app_nil_r; reflexivity]| cbn; rewrite ?app_nil_r; reflexivity]. }
    assert (EVY : mpd_val dY = 0) by (unfold mpd_val, dY; cbn [md_sg md_limbs limbs_val]; reflexivity).
    pose proof (A_mpi_cmp_mpi_spec AL IMG) as CMPc. unfold mpi_cmp_mpi_stmtA in CMPc.
    zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply (CMPc CS) with (LB := LBy) (dX := dE) (dY := dY) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact MDq | exact MY | exact MIq | exact CSOK | exact OSq | exact OPq | exact STlo | exact PNZ | exact OYq | reflexivity
              | exact (art_alwf asegs R HIA)
              | exact (hm_abase asegs R HIA h LB LF m2 HHq)
              | (intros _; exact OQq)
              | (intros _; unfold dY; cbn [md_p]; clear - SP1 SLO LOS ALO ACP NEEDE; lia)
              | (clear - LOS ALO ACP; lia)
              | (clear - SLO SP1 NEEDE; lia)
              | (clear - SP1M; Z.div_mod_to_equations; lia)
              | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
              | (destruct OS4 as [Q|Q]; [left; exact Q| right; clear - Q SP1; lia])
              | (right; unfold dY; cbn [md_addr]; clear; lia)
              | (intros _; right; unfold dY; cbn [md_p]; clear; lia)
              | (intros N1; assert (NN : md_own dE <> LNull) by (intros E0; pose proof ME0 as [(_ & _ & _ & _ & _ & OW) _]; rewrite E0 in OW; destruct OW as [_ N0]; clear - N0 N1; lia);
                 destruct (OS5 NN) as [Q|Q]; [left; exact Q| right; clear - Q SP1; lia])
              | match goal with |- ?g => idtac "CMPPRE-LEFT:" g end ]. }
    rewrite EVY, Z.sub_0_r.
    clear MDq MY OSq OPq OYq OQq SPL0 SPY CMPc.
    cbv beta. intros ms3 PO. unfold mpi_cmp_postA in PO.
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & -> & MU2 & WM2 & MI3 & ST3).
    rewrite ?(unsigned_lit sp1) in MU2, ST3 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 657596)) with (Z_to_bv 64 657596 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (WC : w_client CS [(lo, sp1)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]| apply Forall_nil]. }
    assert (DJ : forall bq nq, (bq + nq <= lo \/ sp1 <= bq) -> disjoint_from [(lo, sp1)] bq nq) by (intros bq nq D; cbn [disjoint_from]; split; [clear - D; lia| exact I]).
    assert (HH3 : HM asegs R HIA h LB LF m3).
    { eapply (hm_munch asegs R HIA h LB LF _ m2 m3); [exact HHq| exact MU2| exact WM2|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. apply w_writable_of_client_wrange. apply client_wrange_stack; clear - LOS SP1 TOP SLO NEEDE; lia. }
    eapply (rw_cells_transport asegs) in SAVE; [| exact MU2| exact WM2| apply DJ; right; clear - SP1; lia].
    eapply (rw_cells_transport asegs) in SPILL; [| exact MU2| exact WM2| apply DJ; right; clear; lia].
    eapply (stk_transport_disjoint asegs) in SThi; [| exact MU2| exact WM2| apply DJ; right; clear; lia].
    eapply (rw_cells_transport asegs) in SHC; [| exact MU2| exact WM2|].
    2: { apply DJ. simpl_sizes.
         destruct (apart_shadow_client AL CS lo (sp1 - lo) (sp1 + 96) (Z.shiftr (sp1 + 96) 3 + al_sb AL) 12 CSOK) as [Q|Q];
           [eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]
           | eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]
           | unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia
           | clear - SP1 SLO NEEDE; lia| clear; lia| |];
           clear - Q; lia. }
    assert (SSlo3 : sshad asegs AL m3 slo (sp1 + 96)).
    { eapply (sshad_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS0| clear - SSL; lia| clear - SP1 TOP HTOP; lia]| exact MU2| exact WM2| exact SSlo]. }
    assert (SShi3 : sshad asegs AL m3 (sp1 + 192) (bv_unsigned sp)).
    { eapply (sshad_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]| exact MU2| exact WM2| exact SShi]. }
    assert (SNlo3 : snapA asegs AL m m3 (arl_stklo R) (sp1 + 96)).
    { eapply (snapA_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS0| clear; lia| clear - SP1 TOP HTOP; lia]| exact MU2| exact WM2| exact SNlo]. }
    assert (SNhi3 : snapA asegs AL m m3 (sp1 + 192) (bv_unsigned sp)).
    { eapply (snapA_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]| exact MU2| exact WM2| exact SNhi]. }
    assert (PRES3 : presW asegs R HIA h KEEP LF (bv_unsigned sp) (bv_unsigned sp) WX m m3).
    { eapply (presW_munch asegs R HIA h); [exact PRES| exact MU2| exact WM2| exact WC|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. eapply (wcover_of_stack asegs R HIA h); [exact PRES| clear - LOS ALO; lia| clear - SP1; lia]. }
    assert (MU3 : munch [(lo, bv_unsigned sp); (Z.shiftr (sp1 + 96) 3 + al_sb AL, Z.shiftr (sp1 + 96) 3 + al_sb AL + 12)] m m3).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x Hx; cbn [outside] in *; clear - Hx SP1; lia. }
    assert (WM3 : wmono asegs m m3) by (eapply wmono_trans; [exact WM| exact WM2]).
    clear HHq MIq STlo SSlo SShi SNlo SNhi PRES MU WM MU2 WM2 WC DJ HPA HPX CRk CRLk.
    rename HH3 into HHq, MI3 into MIq, ST3 into STlo, SSlo3 into SSlo, SShi3 into SShi, SNlo3 into SNlo, SNhi3 into SNhi, PRES3 into PRES, MU3 into MU, WM3 into WM.
    zstep. zstep. norm_b8 SHC.
    c4cb_all SPILL. cb8c_all SPILL.
    emb_close sp1 EB2.
    zstep. if_cases K1; zify_cond K1.
    - eapply em_exit; [exact EB2| exact RR4].
    - eapply K. exact EB2.
  Qed.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00[0@L16575340660.1  L19959785096.3  L35653441506.7  L36459744067.129L39172636981.0  L41799534830.126L41799534830.128L41800247978.125L43935886280.136L43937754247.133L45355707097.2  L58641002120.126L58644793952.123L59308628179.3  L60098763854.3  L63568659730.2  L9356559676.11  Q11603972946.128Q14380675221.137Q23831879739.132Q241020884.140  Q242348908.137  Q242365289.139  Q24828717958.140Q30061964691.130Q33680029232.140Q34423045936.133Q3746170871.139 Q37471993808.131Q39212284437.131Q39212284437.140Q41368571430.131Q41410744564.131Q41411038221.130Q41414766571.128Q4447376314.133 Q59030847720.132Q59030962408.133Q60511567613.131Q60511567613.140Q68614955767.132Q9534663128.128 Q9540323967.137 00000400?00W00i00j01@01V01l02B02X02`03603L03W03a03i04T04_04j05505@05K05V05a05l06;06F06Q06`06k07607A07L07W07b08@08K08V08a08l09709B09MS2dES2dE3NRE2K0S1R3HIA1h2sp2lo3TOP4HTOPS2sp2dE3sp12sl3LSLSS2sp2dE3sp12sl3LSL3NRES2sp2dE3sp12sl3LSL3NRES2sp2dE3sp12sl3LSL3EB0S2sp2dE3sp12sl3LSL3EB0S2sp2dE3sp12sl3LSL3EB0S2dE3NRES2sp2dE3sp12sl3LSL3EB0S2sp2dE3sp12sl3LSL3EB0S2dE3PBE2K0S1R2lo3LOSS2dE3NRES1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSL3EB0S2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSL3EB0S2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2sp2dE3sp12sl3LSL3SPR3EB03EALS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSLS2dE2sl3LSL". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 MI0 SSMAP SSL SLL SS0 MX0 CRX DSX XL0 PHI0 FR0 NSX RR4 MN0 SXN OSN CRN CRNL ODN IMN ME0 SXE OSE CRE CREL ODE IME"] Lemma chkE : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Psp1,$13.Pmq,P,(16.&40.)(26.(16.&8.))Psl,(24.(16.&40.))Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pxa0,(16.&40.)Pxa1,(16.&40.)Pxa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(4?.R12.R11.R10.)P,(17.+1.(;.VdN,))P,Pm',P,(16.&40.)(26.(16.&8.))Psl',(24.(16.&40.))Pyt0,(16.&40.)Pyt1,(16.&40.)Pyt2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Pyt3,(16.&40.)Pyt4,(16.&40.)Pyt5,(16.&40.)Pyt6,(16.&40.)P,(4?.R22.R>.R=.)P,(59.R>.)P,(17.+1.(;.VdN,))P,(17.+1.(;.VdE,))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:0944.)(7.&40.R26.)Vgp,Vtp,R10.R?.R>.Vsp,(7.&40.=)(7.&40.(1:.(3.VdN,)+:.))(7.&40.(;.VdE,))(7.&40.(1:.(48.(1:.(3.VdN,)+:.)+3.)(49.(1>.VR,))))R=.R<.R;.R:.R9.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R26.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))(7.&40.(1:.(3.VdE,)+:.))R8.R7.R6.R5.)VF,(7.&40.+:0968.)Vfc,(41.(16.&40.))R12.(55.$2.)))P,Pm',P,(16.&40.)(26.(16.&8.))Psl',(24.(16.&40.))Pyt0,(16.&40.)Pyt1,(16.&40.)Pyt2,(16.&40.)Pya2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Pyt3,(16.&40.)Pyt4,(16.&40.)Pyt5,(16.&40.)Pyt6,(16.&40.)P,(4?.R24.R?.R>.)P,(59.R?.)P,(17.+1.(;.VdN,))P,(12.$13.(;.VdE,)=)(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:0944.)(7.&40.R28.)Vgp,Vtp,R11.R10.R?.Vsp,(7.&40.=)(7.&40.(1:.(3.VdN,)+:.))(7.&40.=)R>.R=.R<.R;.R:.R9.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R28.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))(7.&40.(1:.(3.VdE,)+:.))R8.R7.R6.R5.)VF,(7.&40.+:0:00.)Vfc,(41.(16.&40.))R13.(55.$2.)))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:083<.)(7.&40.R16.)Vgp,Vtp,R13.R12.R11.Vsp,(7.&40.=)R10.R?.R>.R=.R<.R;.R:.R9.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R16.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))Vs11,R8.R7.R6.R5.)VF,(7.&40.+:0890.)Vfc,(41.(16.&40.))R15.(55.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros sp1 mq sl t0 t1 t2 xa0 xa1 xa2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EB N1 KA KL.
    eapply em_cmpE; [exact EB|].
    intros m1 sl1 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 EB1.
    pose proof (emb_viewE _ _ _ EB1) as VE1. dpose OSE as (_ & _ & _ & OSE4 & _).
    (* [comment removed for export] *)
    eapply scanE; [exact EB1| exact VE1| exact OSE4|].
    (* [comment removed for export] *)
    intros m2 sl2 yb2 EB2 S10 S11.
    (* [comment removed for export] *)
    - (* [comment removed for export] *)
      eapply chk568; [exact EB2| exact S10| exact S11| exact N1| exact KA| exact KL].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 MI0 SSMAP SSL SLL SS0 MX0 CRX DSX XL0 PHI0 FR0 NSX RR4 MN0 SXN OSN CRN CRNL ODN IMN ME0 SXE OSE CRE CREL ODE IME"] Lemma em_checks : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_C ()) "Psp1,$13.Pmq,P,(16.&40.)(26.(16.&8.))Psl,(24.(16.&40.))Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(4?.R11.R10.R?.)P,Pm',P,(16.&40.)(26.(16.&8.))Psl',(24.(16.&40.))Pyt0,(16.&40.)Pyt1,(16.&40.)Pyt2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Pyt3,(16.&40.)Pyt4,(16.&40.)Pyt5,(16.&40.)Pyt6,(16.&40.)P,(4?.R20.R>.R=.)P,(59.R>.)P,(17.+1.(;.VdN,))P,(17.+1.(;.VdE,))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:0944.)(7.&40.R24.)Vgp,Vtp,R10.R?.R>.Vsp,(7.&40.=)(7.&40.(1:.(3.VdN,)+:.))(7.&40.(;.VdE,))(7.&40.(1:.(48.(1:.(3.VdN,)+:.)+3.)(49.(1>.VR,))))R=.R<.R;.R:.R9.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R24.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))(7.&40.(1:.(3.VdE,)+:.))R8.R7.R6.R5.)VF,(7.&40.+:0968.)Vfc,(41.(16.&40.))R12.(55.$2.)))P,Pm',P,(16.&40.)(26.(16.&8.))Psl',(24.(16.&40.))Pyt0,(16.&40.)Pyt1,(16.&40.)Pyt2,(16.&40.)Pya2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Pyt3,(16.&40.)Pyt4,(16.&40.)Pyt5,(16.&40.)Pyt6,(16.&40.)P,(4?.R22.R?.R>.)P,(59.R?.)P,(17.+1.(;.VdN,))P,(12.$13.(;.VdE,)=)(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:0944.)(7.&40.R26.)Vgp,Vtp,R11.R10.R?.Vsp,(7.&40.=)(7.&40.(1:.(3.VdN,)+:.))(7.&40.=)R>.R=.R<.R;.R:.R9.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R26.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))(7.&40.(1:.(48.(3.VdN,)+3.)(49.(1>.VR,))))(7.&40.(1:.(3.VdE,)+:.))R8.R7.R6.R5.)VF,(7.&40.+:0:00.)Vfc,(41.(16.&40.))R13.(55.$2.)))(50.$2.(51.$2.VR,VHIA,Vh,Vmo,)(52.$2.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(53.(54.(7.&40.+:083<.)(7.&40.R14.)Vgp,Vtp,R11.R10.R?.Vsp,(7.&40.=)(7.&40.(5:.(5;.VdN,)))R>.R=.R<.R;.R:.R9.R8.(7.&40.(3.VdN,))(7.&40.(3.VdX,))(7.&40.(3.VdE,))(7.&40.(3.VdA,))(7.&40.-4.)(7.&40.=)(7.&40.(1:.(48.(1:.R14.+60.)+3.)(49.(1>.VR,))))(7.&40.(49.(1>.VR,)))Vs10,Vs11,R7.R6.R5.R4.)VF,(7.&40.+:0844.)Vfc,(41.(16.&40.))R13.(55.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EB KA KL.
    eapply chkN; [exact EB|]. intros ya0 ya1 ya2 N1.
    eapply chkE; [exact EB| exact N1| exact KA| exact KL].
  Qed.
End WEC.
