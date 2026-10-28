(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_copy P_mpi_shrink.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_shrink () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_xop_stmtA"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "shrink_PHI"; "shrink_FR"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_shrink.shrink_R"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limbs_val"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_copy.zeros_above"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SHRINK"].


Definition A_WRAP_CALLOC_SH : Z := 0x69484.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMCPY_SH : Z := 0x67dbc.    (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Definition shrink_FR (d : Z) : Z := calls_FR 2 d.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L29598275300.1000003S1d". (* [comment removed for export] *)
Lemma shrink_FR_val : forall d, shrink_FR d = 2 * (d + 3).
Proof. intros. unfold shrink_FR, calls_FR, fr_charge. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition shrink_PHI (dX : mpd) (nb : Z) : Z := grow_PHI (Z.max nb (md_n dX)).

Definition mpi_shrink_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_shrink ()) "(0.O4.O3.O2.O1.+60.Lnb,$1.(2.(3.=R1.)(4.R1.(5.+2.+40.)))$6.$7.LLB,(8.$9.)LdX,$:.Lnb,$1.Lr,$1.LdX',$:.(;.R3.R4.R5.R2.R1.))")
(* [comment removed for export] *).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x09bda4]).
Local Ltac zchk_new ::= constr:([0x09bbb4; 0x09bbb8; 0x09bbbc; 0x09bc10; 0x09bc14; 0x09bc18; 0x09bc1c; 0x09bc20; 0x09bc24; 0x09bc28; 0x09bc94; 0x09bc98; 0x09bc9c; 0x09bcec; 0x09bcf0; 0x09bcf4]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Hypothesis C24T : c24_transition.   (* [comment removed for export] *)
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_SH.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_SH.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X sg n P : Z) (limbs : list word) (pad : word) (own : limb_own) (nb lo d : Z).
  Local Notation dX := (mkMPD X sg n P limbs pad own).
  Hypothesis HNS : own <> LStatic.
  Hypothesis NB : 0 <= nb < 2^64.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis DSP : own <> LNull -> P + 4 * n <= lo \/ bv_unsigned sp <= P.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 96 - arl_need_rt R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis XUW : uw_obj R X 16 d.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation SHX10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Notation FRAME := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].   (* [comment removed for export] *)
  Notation POST := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
                      (fun r dX' => shrink_R nb dX LB r dX') (grow_PHI (Z.max nb n)) (shrink_FR d) lo).

  Ltac basic_facts hc LBc mm HH TOPc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0; pose proof (hm_top asegs R HIA hc LBc LF mm HH) as HTOP;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOP; lia]).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0@L15302269400.100L22446743512.100L24387680389.99 L29428324939.5  L34705680216.100L35653441506.7  L3949578456.100 L41843875160.100L51454941784.100L5699067096.100 L58591023192.100L59506921496.98 L60098763854.3  L67280348888.100Q15641568614.99 Q18364007270.99 Q21877861637.99 Q27583156582.99 Q27904925317.99 Q30413285893.99 Q31269115878.99 Q32653586022.99 Q33915848709.99 Q36423571333.99 Q3832210565.99  Q39941338501.99 Q41154176102.99 Q44650594790.99 Q51233520870.99 Q59840699110.99 Q66523986693.99 Q9840924165.99  00000400800O00a00e01?01C01G01K01O01S01W01a01e01l02302F02M02`03303:03A03T03g04:04M04T04[04b04i05<05OS2spS2spS1R5NEEDR2sp2lo3SLO3SPRS1R2lo3LOS3ALO3ACPS2spS1R3HIA2sp2lo2hc4TOPc4HTOPS2spS2spS2spS2spS2spS2spS1R2lo3LOSS2spS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2loS2sp2loS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shrink ()) "Phc,(<.$=.VR,VHIA,)PLBc,(8.$9.)Pmm,P,(>.&40.)(?.(>.&8.))Pr,$1.Pjk,(8.(>.&8.))Pxra,(>.&40.)Pxs0,(>.&40.)Pxs1,(>.&40.)Pxs2,(>.&40.)Pxs3,(>.&40.)Pxs4,(>.&40.)Pxs5,(>.&40.)Pxs6,(>.&40.)Pxs7,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(10.$=.VR,VHIA,R1<.R1;.VLF,R1:.)P,(3.(11.&40.Vsp,)(12.$=.VR,VHIA,R1=.))P,(13.$=.R1<.(14.(11.&40.Vsp,)-50.)(15.$16.(17.#8.R1:.)(15.$16.(18.Vs7,)(15.$16.(18.Vs6,)(15.$16.(18.Vs5,)(15.$16.(18.Vs4,)(15.$16.(18.Vs3,)(15.$16.(18.Vs2,)(15.$16.(18.Vs1,)(15.$16.(18.Vs0,)(15.$16.(18.Vra,)(19.$16.))))))))))))P,(1:.$=.R1=.Vlo,(14.(11.&40.Vsp,)-50.))P,(1;.$=.R1>.)(1<.$=.(1=.VR,)(1>.$=.VR,VHIA,R21.)Lms',$1?.(20.(>.&40.)Lx5,(>.&40.)(20.(>.&40.)Lx6,(>.&40.)(20.(>.&40.)Lx7,(>.&40.)(20.(>.&40.)La1',(>.&40.)(20.(>.&40.)La2',(>.&40.)(20.(>.&40.)La3',(>.&40.)(20.(>.&40.)La4',(>.&40.)(20.(>.&40.)La5',(>.&40.)(20.(>.&40.)La6',(>.&40.)(20.(>.&40.)La7',(>.&40.)(20.(>.&40.)Lx28,(>.&40.)(20.(>.&40.)Lx29,(>.&40.)(20.(>.&40.)Lx30,(>.&40.)(20.(>.&40.)Lx31,(>.&40.)(2.(21.$1?.R?.(22.(23.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(24.&40.R2=.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(25.Vra,)Vfc,(26.(>.&40.))R2>.(27.$=.)))(1:.$=.R2>.Vlo,(11.&40.Vsp,)))))))))))))))))(22.(23.R1<.(24.&40.(14.(11.&40.Vsp,)-50.))Vgp,Vtp,R13.R12.R11.R1;.R1:.(24.&40.R1>.)R10.R?.R>.R=.R<.R;.R:.R19.R18.R17.R16.R15.R14.Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(24.&40.+9;=58.)Vfc,(26.(>.&40.))R1?.(27.$=.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH TOPc FR ST MI. basic_facts hc LBc mm HH TOPc.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: match goal with |- ?g => idtac "EPI-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0160@D24976250634.115D52014138856.115D52014138856.116D62155808737.116K21652967687.115K21652967687.116L15302269400.112L21646329835.2  L22446743512.112L23100341967.112L24389400072.112L29428324939.5  L34705680216.112L35653441506.7  L3949578456.112 L41843875160.112L46160487540.111L49578233423.112L50790580594.6  L51454941784.112L5260050330.111 L5699067096.112 L58591023192.112L59506921496.111L60098763854.3  L67280348888.112Q12370813529.113Q15643290603.112Q17207353341.112Q18365959659.112Q20414272036.115Q20414272036.116Q21879808904.112Q24974040330.114Q26207421841.111Q26207721832.112Q26207967338.109Q27585109995.112Q27907166216.112Q30415201416.112Q31271557483.112Q31654082872.111Q32655335659.112Q33918027400.112Q36425783560.112Q37625275423.112Q3830196744.112 Q39212284437.112Q39939652360.112Q41152162539.112Q42081808994.112Q43925228937.112Q44648681323.112Q51236024939.112Q52016320488.114Q52016320488.115Q5485174314.113 Q5485603330.112 Q59843171435.112Q60511567613.112Q60697995187.112Q6143569392.113 Q62157788641.115Q62965564504.113Q62965564504.114Q66522035592.112Q7891539809.113 Q8880503606.109 Q9538787269.109 Q9843398792.112 00000J00d01?01Z02G03503>03?03H03Q03m04?04H04b04k05405=05F05]05f05o06806A06J06T06]06k07707=07I07f08D08\09309909?09E09Q09i0:A0:M0:S0:_0;70;O0;U0;m0<30<K0<W0<`0<f0=20=>0=U0=m0>30>90>E0>K0>Q0>W0>o0?>0?M0?e0?n0@40@:0@RS2sp1X1k2XB2HB5Ha_st5Hl_stS2sp1X1k2XB2HB5Ha_st5Hl_stS2sp1X2pn2XB2HB5Ha_st5Hl_stS2sp1X2pn2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO1k3DSX2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO2pn3DSX2XB2HB5Ha_st5Hl_stS2sp1X2XBFS2sp1X2XBS2sp1X2XBS1R5NEEDR2sp1X2lo3SLO3SPR2XBS1R2lo3LOS3ALO3ACPS2sp1X2XBS1R3HIA2sp2lo2hc4TOPc4HTOPS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS1R5NEEDR2sp2lo3LOS3SLOS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS2sp1X2XBS1R2lo3LOSS2sp1X2XBS2sp1X4ALX82XBS2sp1X2lo2XBS1X2XBS2sp1X2lo2XBS2sp1X2lo1k2XB2HB5Ha_st5Hl_stS2sp1X2lo2pn2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3SLO2XBS1X1k2XB2HB5Ha_st5Hl_stS1X2XBS1X2XBS1X2XBS2sp1X2lo2XBS1R5NEEDR2sp1X2lo3SLO2XBS1R5NEEDR2sp1X2lo3SLO2XBS2sp1X2lo2XBS1X2XBS2sp1X2lo2XBS1R5NEEDR2sp1X2lo3SLO2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XBS2sp1X2lo2XBS1X2XB2HBS1X2XBS2sp1X2lo2XBS2sp1X2lo2XBS1X1k2XB2HB5Ha_st5Hl_stS1X2pn2XB2HB5Ha_st5Hl_stS1X2XBS1X2XBS2sp1X2lo2XBS1X2XBS1X2XBS1X2XBS1X2pn2XB2HB5Ha_st5Hl_stS1X2XB2HB5Ha_stS1X2XB2HB5Ha_stS1R5NEEDR2sp1X2lo3SLO2XBS1X2XB2HBS1X2XBS1X2XBS1R5NEEDR2sp1X2lo3SLO2XB". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma fin_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shrink ()) "Phc,(<.$=.VR,VHIA,)PLBc,(8.$9.)Pmm,P,(>.&40.)(?.(>.&8.))Ppw,$1.Pnw,$1.Ppn,$1.Pk,$1.Pjk,(8.(>.&8.))Pxra,(>.&40.)Pxs4,(>.&40.)Pxs7,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa0,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(10.$=.VR,VHIA,R1:.R19.VLF,R18.)P,(21.$1.(12.$=.VR,VHIA,R1;.)(12.$=.VR,VHIA,Vh,))P,(3.(11.&40.Vsp,)(12.$=.VR,VHIA,R1<.))P,(21.$1.(28.VX,+8.)=)P,(29.(3.(14.VX,+10.)Vlo,)(3.(11.&40.Vsp,)VX,))P,(2.(3.=R1:.)(4.R1:.(5.+2.+40.)))P,(2.(3.=R1:.)(4.R1:.(5.+2.+40.)))P,(13.$=.R1?.VX,(2:.R1>.(24.&40.Vsg,)R1=.Vpad,))P,(2;.(2<.VR,)(2=.$9.R21.(2>.VLF,))(11.&40.Vsp,)(12.$=.VR,VHIA,Vh,)VX,+10.)P,(2?.$=.(1=.VR,)(1>.$=.VR,VHIA,R23.)R21.VX,+10.)P,(13.$=.R22.(14.(11.&40.Vsp,)-50.)(15.$16.(17.#8.R1=.)(15.$16.(18.Vs7,)(15.$16.(18.Vs6,)(15.$16.(18.Vs5,)(15.$16.(18.Vs4,)(15.$16.(18.Vs3,)(15.$16.(18.Vs2,)(15.$16.(18.Vs1,)(15.$16.(18.Vs0,)(15.$16.(18.Vra,)(19.$16.))))))))))))P,(1:.$=.R23.Vlo,(14.(11.&40.Vsp,)-50.))P,(1;.$=.R24.)(1<.$=.(1=.VR,)(1>.$=.VR,VHIA,R27.)Lms',$1?.(20.(>.&40.)Lx5,(>.&40.)(20.(>.&40.)Lx6,(>.&40.)(20.(>.&40.)Lx7,(>.&40.)(20.(>.&40.)La1',(>.&40.)(20.(>.&40.)La2',(>.&40.)(20.(>.&40.)La3',(>.&40.)(20.(>.&40.)La4',(>.&40.)(20.(>.&40.)La5',(>.&40.)(20.(>.&40.)La6',(>.&40.)(20.(>.&40.)La7',(>.&40.)(20.(>.&40.)Lx28,(>.&40.)(20.(>.&40.)Lx29,(>.&40.)(20.(>.&40.)Lx30,(>.&40.)(20.(>.&40.)Lx31,(>.&40.)(20.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(2.(21.$1?.R10.(22.(23.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(24.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(25.Vra,)Vfc,(26.(>.&40.))R1.(27.$=.)))(2.(30.(15.(31.$1.$1.)(32.$1.$1.Vlo,(11.&40.Vsp,))(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(19.(31.$1.$1.))))R35.R1.)(2.(33.$=.R35.R1.)(2.(1;.$=.R1.)(2.(13.$=.R1.VX,(2:.R32.(24.&40.Vsg,)R31.Vpad,))(2.(1:.$=.R1.Vlo,(11.&40.Vsp,))(10.$=.VR,VHIA,R37.R36.VLF,R1.))))))))))))))))))))))(22.(23.R1?.(24.&40.(14.(11.&40.Vsp,)-50.))Vgp,Vtp,R1<.R1;.R1:.(24.&40.VX,)(24.&40.(14.VX,+:.))R19.R18.R17.R16.R15.R14.R13.R12.(24.&40.R21.)(24.&40.R22.)R1>.(24.&40.(34.(1=.VR,)))(24.&40.(14.(35.(14.VX,+:.)+3.)(34.(1=.VR,))))R1=.Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(24.&40.+9;=30.)Vfc,(26.(>.&40.))R25.(27.$=.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT TOPc ALX8 DSX PNB KB HX CWc OX FR ST MI. basic_facts hc LBc mm HH TOPc.
    pose proof (rw_cells_bound _ _ _ _ HX) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    assert (CWs : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) X 16) by (rewrite HT; eapply client_wrange_sp_mono; [| exact CWc]; clear - LOS SLO NEEDR; lia).
    unfold mpi_cells in HX.
    pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    (* [comment removed for export] *)
    shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: match goal with |- ?g => idtac "FIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L15083318809.3000008S1n2nb1E". (* [comment removed for export] *)
  #[using="HNS"] Lemma post_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shrink ()) "Pmo,$36.Pmo',$36.Ph',(<.$=.VR,VHIA,)Pm',P,(>.&40.)(?.(>.&8.))Pr,$1.Px5,(>.&40.)Px6,(>.&40.)Px7,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Px28,(>.&40.)Px29,(>.&40.)Px30,(>.&40.)Px31,(>.&40.)P,(1;.$=.R10.)P,(1:.$=.R11.Vlo,(11.&40.Vsp,))P,(37.R15.R14.)P,(38.$=.VR,(39.VLB,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(11.&40.Vsp,)(3;.VR,)(3<.$=.VR,VHIA,Vh,)(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(19.(31.$1.$1.)))Vm,R13.)P,(21.$1.(12.$=.VR,VHIA,R15.)(12.$=.VR,VHIA,Vh,))P,(21.$1.(3<.$=.VR,VHIA,R16.)(3<.$=.VR,VHIA,Vh,))P,(21.$1.(3=.$=.VR,VHIA,R17.)(3=.$=.VR,VHIA,Vh,))P,(3>.$=.VR,VHIA,R18.R19.)P,Px,$1.P,(1>.$=.VR,VHIA,Vh,R1.)(1>.$=.VR,VHIA,R1;.R2.)P,(3.(3?.$=.VR,VHIA,R1:.)(14.(3?.$=.VR,VHIA,Vh,)(40.(41.Vnb,Vn,))))P,(3.(42.$=.VR,VHIA,R1;.)(14.(42.$=.VR,VHIA,Vh,)(7.Vd,)))P,(10.$=.VR,VHIA,R1<.VLB,VLF,R1;.)P,(43.$=.R1<.VLB,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))P,(29.(21.$1.R1<.$44.)(2.(21.$1.R1<.=)(21.$1.Vnb,Vn,)))(45.$=.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$:.(;.Vnb,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(40.(41.Vnb,Vn,))(7.Vd,)Vlo,Vm,R21.(46.(22.(23.Vra,Vsp,Vgp,Vtp,R1<.R1;.R1:.Vs0,Vs1,(24.&40.R1=.)R19.R18.R17.R16.R15.R14.R13.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.R10.R?.)VF,(25.Vra,)Vfc,(26.(>.&40.))R1>.(27.$=.))R20.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros MI ST MF HP HT HS HFL HK HCS HV HFR HH MA Hr.
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h', LB, dX, r.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|]. split; [exact MA|].
    split; [apply mpd_out_refl; cbn [md_own]; exact HNS|].
    split; [intros b Hb; left; exact Hb|].
    unfold shrink_R. split; [| intros b Hb; left; exact Hb].
    destruct Hr as [->|[-> E]]; [right; split; reflexivity| left].
    cbn [md_sg md_n md_pad md_limbs].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [clear - E; lia|]. intros _; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L13106851282.2L34871785966.2L59314873579.4L59314873579.800000600<00F00ZS1k2HkS1k2HkS1k1A2Hk1HS1P1k1A2Hk2E11H1n2E2". (* [comment removed for export] *)
  #[using="HNS XW DSP"] Lemma post_new : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shrink ()) "Pk,$1.PA,$1.Pla,(8.(>.&40.))PLBr,(8.$9.)Pmo,$36.Pmo',$36.Ph',(<.$=.VR,VHIA,)Pm',P,(>.&40.)(?.(>.&8.))Px5,(>.&40.)Px6,(>.&40.)Px7,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Px28,(>.&40.)Px29,(>.&40.)Px30,(>.&40.)Px31,(>.&40.)P,(21.$1.(28.VX,+8.)=)P,(4.=VX,)P,(29.(21.$1.Vsg,+1.)(21.$1.Vsg,-1.))P,(47.$1.(48.(31.$1.$1.)$1.(49.$1.$1.)VLB,))P,(2.(3.+1.R1:.)(3.R1:.+2710.))P,(3.Vnb,R1;.)P,(4:.(21.$1.Vnb,Vn,))P,(21.$1.(4;.(4<.(>.&40.)R1;.))R1=.)P,(21.$1.(4=.R1<.)(4=.Vlimbs,))P,(21.$1.(28.R1>.+10.)=)P,(4>.VR,VLB,VLF,R1?.(4?.+4.R20.))P,Pb,$9.P,(50.$9.R1.R1?.)(50.$9.R2.VLB,)P,Pb,$9.P,(50.$9.R1.VLB,)P,(4:.(50.$9.R2.(51.(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))))(50.$9.R3.R22.)P,Pb,$9.P,(50.$9.R1.(51.(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(4:.(50.$9.R2.R22.))P,Pb,$9.P,(50.$9.R1.(51.(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)))(50.$9.R2.VLB,)P,(1;.$=.R1>.)P,(1:.$=.R1?.Vlo,(11.&40.Vsp,))P,(37.R23.R22.)P,(38.$=.VR,(39.VLB,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(11.&40.Vsp,)(3;.VR,)(3<.$=.VR,VHIA,Vh,)(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(19.(31.$1.$1.)))Vm,R21.)P,(21.$1.(12.$=.VR,VHIA,R23.)(12.$=.VR,VHIA,Vh,))P,(21.$1.(3<.$=.VR,VHIA,R24.)(3<.$=.VR,VHIA,Vh,))P,(21.$1.(3=.$=.VR,VHIA,R25.)(3=.$=.VR,VHIA,Vh,))P,(3>.$=.VR,VHIA,R26.R27.)P,Px,$1.P,(1>.$=.VR,VHIA,Vh,R1.)(1>.$=.VR,VHIA,R29.R2.)P,(3.(3?.$=.VR,VHIA,R28.)(14.(3?.$=.VR,VHIA,Vh,)(40.(41.Vnb,Vn,))))P,(3.(42.$=.VR,VHIA,R29.)(14.(42.$=.VR,VHIA,Vh,)(7.Vd,)))P,(10.$=.VR,VHIA,R2:.(15.(31.$1.$1.)(32.$1.$1.R2?.(4?.+4.R30.))R2=.)VLF,R29.)P,(13.$=.R2:.VX,(2:.R30.(24.&40.Vsg,)R31.Vpad,))P,(52.$=.R2;.R31.R30.)(45.$=.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$:.(;.Vnb,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(40.(41.Vnb,Vn,))(7.Vd,)Vlo,Vm,R2?.(46.(22.(23.Vra,Vsp,Vgp,Vtp,R2;.R2:.R29.Vs0,Vs1,(24.&40.=)R28.R27.R26.R25.R24.R23.R22.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R21.R20.R1?.R1>.)VF,(25.Vra,)Vfc,(26.(>.&40.))R2<.(27.$=.))R2>.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros ALX X0 SG ND Hk HNB NBX HL HV A16 HFRA HI1 HI2 HI3 HI0 MI ST MF HP HT HS HFL HK HCS HVOL HFR HH HX HA.
    dpose HFRA as (A0 & AC & AD & HAP).
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h', ((A, 4 * k) :: LBr), (mkMPD X sg k A la pad LHeap), 0.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HVOL|]. split; [exact HFR|]. split; [exact HH|].
    split.
    { eapply mpd_at_rebuild; [discriminate| exact HX| exact ALX| exact X0| exact HL| unfold MPI_MAX_LIMBS; clear - Hk; lia| exact SG| intros E; discriminate E|].
      intros _. split; [clear - Hk; lia|]. split; [left; reflexivity|]. split; [exact A16| exact HA]. }
    split.
    { unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n].
      split; [reflexivity|]. split; [discriminate|].
      split; [intros b [Hb|Hb]; [right; left; exact Hb| left; apply HI1, Hb]|].
      split; [intros b Hb Hn; right; exact (HI2 b Hb Hn)|].
      intros b Hb [E|Hin]; [| exfalso; exact (HI3 b Hb Hin)].
      exfalso. pose proof (HI0 b Hb) as HbL. revert Hb E HbL. unfold mpd_blk. cbn [md_own md_p md_n].
      destruct own; [intros []| | intros []]. intros [<-|[]] E HbL. injection E as E1 E2.
      destruct (HAP P (4 * n) ltac:(apply in_app_iff; left; exact HbL)); clear - H E1 E2 Hk; lia. }
    split.
    { cbn [mpd_blk md_own md_p md_n]. intros b [<-|[]]. right. cbn [fst snd]. apply fresh_apart_keep. exact HFRA. }
    unfold shrink_R. cbn [md_sg md_n md_pad md_limbs mpd_blk md_own md_p]. split.
    { left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [unfold mpd_val; cbn [md_sg md_limbs]; rewrite HV; reflexivity|].
      split; [exact HNB|]. intros E. exfalso. exact (NBX E). }
    intros b [<-|[]]. right. intros Hin. destruct (HAP A (4 * k) ltac:(apply in_app_iff; left; exact Hin)); clear - H Hk; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0?L10569489964.3 L13015518834.1 L16475646230.94L16475699316.97L21743611808.1 L23100341967.95L27697600485.3 L32954672833.92L36571201320.0 L37149681802.4 L45380660450.2 L4566640310.3  L48440399099.3 L48442456122.4 L59308551419.6 L59310683537.4 Q12370813529.95Q17207320573.94Q24415927399.97Q26295627581.97Q29651637810.95Q37625373727.94Q39944472214.97Q42426514348.97Q50458135125.97Q5485174314.95 Q5485505026.94 Q57549166911.97Q57549198250.94Q57549266358.97Q6143569392.95 Q63571026702.94Q8943673138.94 00000800;00_01C01F01^01g02K02L02X02]02e02n03703L03X04404D04Z04h04i05905O05b06206B06R06b07207B07R07h086S1k1j2HjS1jS2sp1X1n1P5limbs1k1j2Hj3Hjr2PP2PB2X0S2sp1X1n1P5limbs1k1j2Hj3Hjr2PP2PB2X0S1jS2sp1X1P5limbs1k1j2Hj2X0S1n1j3HjrS2sp1X1n1P5limbs1k1j2Hj3Hjr2PP2PB2X0SS1n1j3Hjr2K1S1P1jS1j1i2HiS1n1j3HjrS1n1j3HjrS1n5limbs1j3Hjr2LL2NXS1n1j2Hj3HjrS2sp1X1P5limbs1k1j2Hj3ALX2X0S1X5limbs1k1j2HjS1n1P5limbs1k1j2Hj3HjrS5limbs1k1j2HjFS1X5limbs1k1j2HjS1n1P5limbs1k1j2Hj3HjrS1P5limbs1k1j2Hj2PPS1P5limbs1k1j2HjS1X5limbs1k1j2HjS1X5limbs1k1j2HjS1P5limbs1k1j2HjS1P5limbs1k1j2HjS1P5limbs1k1j2HjS1X5limbs1k1j2HjS1n1P5limbs1k1j2Hj3HjrS5limbs1k1j2Hj". (* [comment removed for export] *)
  #[using="IMG"] Lemma scan_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shrink ()) "Pk,$53.Pj,$1.Pmm,P,(>.&40.)(?.(>.&8.))Pw3,(>.&40.)Pxa2,(>.&40.)Pxra,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxs3,(>.&40.)Pxs4,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(21.$1.R13.(4;.R14.))P,(2.(3.+1.R14.)(3.R14.Vn,))P,(54.Vlimbs,R15.)P,(21.(>.&40.)R14.(24.&40.(55.(4?.+4.R16.)+4.)))P,(13.$=.R16.VX,(15.$16.(18.(24.&40.VP,))(15.$16.(56.(24.&40.Vsg,))(15.$16.(56.(24.&40.Vn,))(15.$16.(57.Vpad,)(19.$16.))))))P,(58.$=.R17.VP,(59.Vlimbs,))P,(21.$1.(4;.(4<.(>.&40.)Vlimbs,))Vn,)P,(3.Vn,+2710.)P,(4.=VP,)P,(21.$1.(28.VP,+4.)=)P,(3.(14.VP,(4?.+4.Vn,))(5.+2.+40.))P,(21.$1.(28.VX,+8.)=)P,(3.=VX,)P,(3.(14.VX,+10.)(5.+2.+40.))P,(2?.$=.(1=.VR,)(1>.$=.VR,VHIA,Vh,)R20.VX,+10.)P,(2?.$=.(1=.VR,)(1>.$=.VR,VHIA,Vh,)R21.VP,(4?.+4.Vn,))P,(1;.$=.R22.)(1<.$=.(1=.VR,)(1>.$=.VR,VHIA,Vh,)Lms',$1?.(20.$1.Li,$1.(20.(>.&40.)Lxa0',(>.&40.)(20.(>.&40.)Lxa1',(>.&40.)(20.(>.&40.)Lxa2',(>.&40.)(20.(>.&40.)Lxa3',(>.&40.)(20.(>.&40.)Lxa4',(>.&40.)(2.(21.$1?.R7.(22.(23.R27.(24.&40.(14.(11.&40.Vsp,)-50.))Vgp,Vtp,R26.R25.R24.(24.&40.VX,)(24.&40.(14.VX,+:.))R5.R4.R3.R2.R1.R21.R20.R1?.(24.&40.Vnb,)R1>.(24.&40.R6.)(24.&40.(34.(1=.VR,)))(24.&40.(14.(35.(14.VX,+:.)+3.)(34.(1=.VR,))))(24.&40.(14.(35.VX,+3.)(34.(1=.VR,))))Vs8,Vs9,Vs10,Vs11,R1<.R1;.R1:.R19.)VF,(24.&40.+9;<;<.)Vfc,(26.(>.&40.))R2:.(27.$=.)))(2.(2.(3.+1.R6.)(3.R6.R2;.))(54.Vlimbs,R6.)))))))))(22.(23.R20.(24.&40.(14.(11.&40.Vsp,)-50.))Vgp,Vtp,R1?.R1>.R1=.(24.&40.VX,)(24.&40.(14.VX,+:.))(24.&40.R24.)R22.R21.R1<.R1;.R1:.R19.R18.(24.&40.Vnb,)R17.R16.(24.&40.(34.(1=.VR,)))(24.&40.(14.(35.(14.VX,+:.)+3.)(34.(1=.VR,))))(24.&40.(14.(35.VX,+3.)(34.(1=.VR,))))Vs8,Vs9,Vs10,Vs11,R15.R14.R13.R12.)VF,(24.&40.+9;;?8.)Vfc,(26.(>.&40.))R23.(27.$=.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hj Hjr ZX -> HXS HX LL N10 PP PAL PB ALX X0 X16 OX OP MI; [exfalso; clear - Hj Hjr; lia|].
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - Hjr N10; lia).
    - (* [comment removed for export] *)
      apply evtA_done. deexists 6. split; [reflexivity|]. split; [clear - K1 Hjr; lia| first [exact ZX| rewrite <- K1; exact ZX]].
    - destruct (nth_error limbs (Z.to_nat (j - 1))) as [w|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX Hjr LL; lia].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OP (P + (4 * j - 4)) 4.
      (* [comment removed for export] *)
      pose proof (u32ro_read asegs mm P limbs (j - 1) w _ HX NX ltac:(clear - Hjr; lia) eq_refl) as RD.
      replace (P + 4 * (j - 1)) with (P + (4 * j - 4)) in RD by (clear; lia).
      zstep. clear RD.
      pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(clear; lia)) as Bw.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?bv_unsigned_sx32 in K2.
      + (* [comment removed for export] *)
        apply (proj1 (sxz_zero_iff _ Bw)) in K2.
        pose proof (zeros_above_down' limbs (j - 1) w ltac:(clear - Hjr; lia) ltac:(replace (j - 1 + 1) with j by (clear; lia); exact ZX) NX K2) as ZX'.
        eapply evtA_mono; [eapply (IH (j - 1)); try eassumption; [clear - Hj; lia| clear - Hjr K1; lia| replace (j - 1) with (j + -1) by (clear; lia); exact ZX' .. | f_equal; clear; lia] |].
        all: cycle -1.
        { cbv beta. intros ms' PO. ddestruct PO as (i & xa0' & xa1' & xa2' & xa3' & xa4' & E & Hi & Zi). deexists 6. split; [exact E|]. split; [clear - Hi; lia| exact Zi]. }
        all: try (replace (j + -1) with (j - 1) by (clear; lia); exact ZX').
        all: match goal with |- ?g => idtac "SCAN-IH-LEFT:" g end.
      + (* [comment removed for export] *)
        zstep. apply evtA_done. deexists 6. split; [reflexivity|]. split; [clear - Hjr; lia| exact ZX].
    all: match goal with |- ?g => idtac "SCAN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac epi_return hh LBx rr FR LAWS KINV :=
    eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
      [ eapply epi_walk with (hc := hh) (LBc := LBx) (r := rr); try eassumption; exact FR
      | intros y Hy; exact Hy | ];
    let ms' := fresh "ms'" in let PO := fresh "PO" in
    intros ms' PO; destruct_exs PO;
    let E := fresh "E" in let ST9 := fresh "ST9" in
    destruct PO as [E ST9]; subst ms';
    apply aevtA_done;
    let mo9 := fresh "mo9" in let HK9 := fresh "HK9" in let MF9 := fresh "MF9" in
    intros mo9 [HK9 MF9].

  Ltac post_side :=
    first [ eassumption
          | reflexivity
          | match goal with |- mo_frame _ _ => repeat (eapply mo_frame_trans; [eassumption|]); eassumption end
          | match goal with |- mo_frame _ _ => eapply mo_frame_trans; [| eassumption]; eapply mo_frame_trans; eassumption end
          | match goal with H : ?f asegs R HIA ?h2 = ?f asegs R HIA ?hc, H' : ?f asegs R HIA ?hc = ?f asegs R HIA h |- ?f asegs R HIA ?h2 = ?f asegs R HIA h => rewrite H; exact H' end
          | match goal with |- forall x, hcs _ _ _ _ x -> hcs _ _ _ _ x => let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; repeat match goal with H : forall x, hcs _ _ _ ?a x -> hcs _ _ _ ?b x |- hcs _ _ _ ?b y => apply H end; exact Hy end
          | match goal with |- havol _ _ _ _ <= _ => unfold grow_PHI, AVOL_CALL in *; lia end
          | match goal with |- hfr _ _ _ _ <= _ => rewrite ?shrink_FR_val in *; unfold fr_charge in *; repeat match goal with H : hfr _ _ _ _ <= _ |- _ => revert H end; generalize (uw_obj_nonneg _ _ _ _ XUW); clear; intros; lia end
          | match goal with H : rw_cells asegs ?mx X _ |- rw_cells asegs ?mx X _ => unfold mpi_cells; exact H end
          | left; reflexivity
          | right; split; [reflexivity| lia]
          | match goal with |- ?g => idtac "POST-SIDE-LEFT:" g end ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Paths.
    Variables (mo : Model) (m1 : mem) (jk1 : list byte).
    Hypothesis HH1 : HM asegs R HIA h LB LF m1.
    Hypothesis HXS1 : rw_cells asegs m1 X [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 pad].
    Hypothesis PCH1 : own = LHeap -> rw_cells asegs m1 P [CB (4 * length limbs)%nat (u32s limbs)].
    Hypothesis OX1 : aobj asegs AL CS m1 X 16.
    Hypothesis FR1 : rw_cells asegs m1 (bv_unsigned sp + -80) (CB 8 jk1 :: FRAME).
    Hypothesis ST1 : stk asegs m1 lo (bv_unsigned sp + -80).
    Hypothesis MI1 : mem_inv asegs m1.
    Hypothesis HP1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shrink ()) "(38.$=.VR,(39.VLB,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(11.&40.Vsp,)(3;.VR,)(3<.$=.VR,VHIA,Vh,)(15.(31.$1.$1.)(32.$1.$1.VX,(14.VX,+10.))(19.(31.$1.$1.)))Vm,Vm1,)")
(* [comment removed for export] *).
    Hypothesis ALX : X mod 8 = 0.
    Hypothesis X0 : 0 < X.
    Hypothesis LL : Z.of_nat (length limbs) = n.
    Hypothesis NR : 0 <= n <= 10000.
    Hypothesis SG : sg = 1 \/ sg = -1.
    Hypothesis P0 : 0 <= P.
    Hypothesis PC : P + 4 * n <= alloc_ceiling.
    Hypothesis PHEAP : own = LHeap -> 0 < P /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ 1 <= n.
    Hypothesis PNULL : own = LNull -> P = 0 /\ n = 0.
    Hypothesis CW : client_wrange L (LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16.
    Hypothesis DXP : own = LHeap -> X + 16 <= P \/ P + 4 * n <= X.
    Hypothesis DSX : X + 16 <= lo \/ bv_unsigned sp <= X.
    Hypothesis ND : List.NoDup (map fst LB).
    Hypothesis NB10 : nb <= 10000.
    Hypothesis BUD : havol asegs R HIA h + grow_PHI (Z.max nb n) <= AVOL_MAX.
    Hypothesis BUDF : hfr asegs R HIA h + shrink_FR d <= FR_MAX.

    (* [comment removed for export] *)
    Ltac calloc_call cntv :=
      replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity);
      eapply aevtA_call;
      [ let mo1 := fresh "mo1" in let HK1 := fresh "HK1" in let MF1 := fresh "MF1" in
        intros mo1 [HK1 MF1];
        eapply (heapA_calloc asegs R HIA) with (h := h) (LB := LB) (LF := LF) (cnt := cntv) (sz := 4) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia; rewrite ?(unsigned_lit X) by qlia; try eassumption; try reflexivity;
        first [ eapply uw_obj_uwc; [exact XUW | clear; lia]
              | unfold AMAX, AVOL_CALL, grow_PHI, fr_charge in *; rewrite ?shrink_FR_val in *;
                repeat match goal with H : _ <= _ |- _ => revert H | H : _ < _ |- _ => revert H | H : _ <= _ < _ |- _ => revert H | H : _ <= _ <= _ |- _ => revert H end;
                generalize (uw_obj_nonneg _ _ _ _ XUW); generalize (arl_need_rt_malloc R); generalize SPA; clear; intros; lia
              | apply c24_of_transition; exact C24T   (* [comment removed for export] *)
              | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end ]
      | ].

    (* [comment removed for export] *)
    Ltac free_limbs_call hh LBx HIN PCHx :=
      let SPZ := fresh "SPZ" in
      pose proof ZF as SPZ; unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ;
      eapply aevtA_call;
      [ let mo1 := fresh "mo1" in let HK1 := fresh "HK1" in let MF1 := fresh "MF1" in
        intros mo1 [HK1 MF1];
        eapply SPZ with (h := hh) (LB := LBx) (LF := LF) (buf := P) (len := n * 4) (lo := lo) (d := d) (junk := u32s limbs);
          rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia; rewrite ?(unsigned_lit X) by qlia; try eassumption; try reflexivity;
        first [ right; split; [right; replace (n * 4) with (4 * n) by (clear; lia); exact HIN | exact PCHx]
              | eapply uw_obj_uwc; [exact XUW | clear; lia]
              | unfold AVOL_CALL, grow_PHI, fr_charge in *; rewrite ?shrink_FR_val in *;
                repeat match goal with H : _ <= _ |- _ => revert H | H : _ < _ |- _ => revert H | H : _ <= _ < _ |- _ => revert H | H : _ <= _ <= _ |- _ => revert H end;
                generalize (uw_obj_nonneg _ _ _ _ XUW); generalize (arl_need_rt_free R); generalize (arl_need_rt_amem R); generalize SPA; clear; intros; lia
              | match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end ]
      | clear SPZ ].

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "03V0@C17025492443.208C31740276271.209D13589037945.237D16049893661.210D17815656873.236D20501856385.210D33379250345.237D34779215654.237D37703914153.236D37703914153.237D39375088350.154D39375475909.237D42750138435.236D42750138435.237D48201086591.237D50796826103.210D63595235433.210K25897202343.209K36795542264.209K53933808495.209K60573057312.208K61205767951.209K65071292344.209L11468776467.3  L11500568735.39 L11504513181.17 L11581774232.12 L1160237219.264 L11668949970.169L12694533441.2  L12750819336.13 L12755534717.11 L13603882068.12 L14213399799.39 L14369733550.2  L16256253080.7  L17379355392.39 L17585880332.15 L19130742250.39 L19148509272.6  L1936974140.17  L19834694388.5  L19947878820.264L23100341967.169L23100341967.201L24483526758.2  L24912882372.1  L24914258088.264L25426381488.10 L25426381488.12 L25890634160.3  L26707095699.5  L26798959255.4  L26798959255.6  L26892418956.1  L27001969330.52 L27006593843.17 L28715365361.3  L28767265244.7  L28813938827.13 L28814040852.169L28943460204.4  L29007570709.3  L29428324939.5  L32409531553.0  L32693198944.7  L3278082148.2   L32987209960.7  L33087634096.2  L34171955900.9  L34425302674.52 L34476921401.4  L34838801432.39 L35561496115.4  L35653441506.7  L35655538624.7  L36807145629.3  L37334827261.4  L37714553091.1  L38314509377.12 L38948636245.0  L39172636981.0  L40108971872.12 L40281191306.3  L40290687782.1  L40369445627.7  L40825480686.39 L41471587942.8  L42762855401.8  L43170267636.12 L43170267636.6  L43170267636.7  L44697879740.4  L45013738119.41 L45771419496.4  L46160487540.179L46160487540.201L46357874486.242L46732241046.2  L46952797974.52 L47209170218.1  L48132467214.7  L48225685459.5  L49346446901.52 L49591838433.52 L49657279893.4  L50635453427.5  L50790809970.7  L51040919409.12 L51879758738.7  L51881576583.10 L5260163351.168 L5262145463.198 L53791977879.153L53923074168.4  L5479049730.1   L54897920813.3  L57402658371.4  L58804912007.12 L59294908043.5  L59294908043.6  L59308632307.1  L59308633593.3  L59308661072.8  L59308668813.4  L59308742867.3  L60098763854.3  L60447862057.2  L60549562490.3  L60576273221.2  L61211782168.3  L61929067222.178L61929718192.2  L61931164306.200L62018535662.1  L62369652128.2  L62624471726.46 L62625145375.46 L63259805175.52 L63259968628.39 L63792902737.265L6387124300.39  L64966926188.10 L64968776825.7  L65066372573.4  L656136024.1    L66610669263.178L66617043407.205L68108785696.1  L6935467336.1   L7273050298.6   L8810490561.4   L9981636555.6   N12401863469.209N20716133971.209N31170017719.209N32071669760.209N53807417181.209O11257354870.209O17025492443.208O29478932113.209O31740276271.209O39322336069.209O47259422021.209O49587672251.208O57399310481.209O65674534437.209P25897202343.209P28709353702.209P35876208370.236P35876208370.237P35876323561.153P35876323561.154P44704452523.208P50646218980.209P60573057312.208Q11523265569.211Q12370813529.174Q12370813529.207Q16049893661.211Q17207204208.173Q17207350632.208Q26056220419.191Q26056447029.122Q26056447030.213Q26058334103.140Q26058334103.231Q26207421841.186Q26207721832.187Q26207721832.209Q26209519061.208Q26209819600.206Q26220304629.184Q29651637810.207Q31651985788.208Q31654082872.186Q37623180338.206Q37625422482.173Q37703787028.211Q38248387216.211Q39212284437.187Q39212284437.209Q43879899724.211Q43925228937.187Q43925228937.209Q45998615361.237Q45998740826.154Q5262061745.122 Q5262061746.213 Q5483504175.206 Q5485174314.174 Q5485174314.207 Q5485489295.173 Q5485600919.208 Q57478834698.211Q60511567613.187Q60511567613.209Q60537631851.153Q60537752176.236Q60697995187.187Q60697995187.209Q6143569392.174 Q6143569392.207 Q63595235433.211Q65983947055.174Q65983947055.207Q8882911372.206 Q8885009321.184 Q9534281562.184 Q9540572287.206 00000100200]00^01901:01b02M02h03C03\04704804904:05505605705W06;06<06]07L07X08:08O08P08k0:00:10:20:30:40:N0:O0:d0;?0;@0;Z0;[0<00<A0<_0=:0=U0=Z0=]0>80>T0?60?70?I0?T0?e0?i0@E0@W0@X0A30A`0B]0Bi0C20CD0CE0CU0CV0Ci0Co0DJ0Da0Dm0ET0E`0F80FS0FT0FX0F[0Fl0Fm0Fn0GC0GL0GO0Ge0H30H40H50H60H70H80H90H:0HH0Hf0ID0I_0If0JO0JR0Jm0K60KS0L?0LH0LI0L`0La0Lb0M00MN0Ml0NE0NF0NI0NU0Nc0OE0OF0OG0OK0OT0Oj0P50P>0PH0PN0PV0PW0PX0Q60Q<0QZ0Q]0Qb0Qc0Qd0RX0SL0TJ0T[0To0U00U10U40Uf0V]0Va0Ve0W70WE0WF0X=0X_0YA0YB0YC0YD0YE0YF0YG0YH0YI0YJ0YK0YL0YM0ZE0Z^0[70[P0[i0\M0];0]<0]W0^<0^a0^b0_80_N0`I0aD0b?0c:0d50dK0da0e70eM0ec0f90f:0fP0ff0g<0gR0gj0hC0hY0ho0iK0ia0j70j80j90jR0jk0kA0kW0km0lC0lY0lZ0m00mF0n50nd0o=0oV0ol10B10C10D10E10[11111G11]FFS2sp1X1n1P5limbs2nb2X02P02K13SPR2XB1A2A02N1FS2sp1X1n1P5limbs2nb2P02XB1AFS2sp1X1n1P5limbs2nb2X02P02K13SPR2XB1A2A0S2sp1X1n1P5limbs2nb2X02LL2P02K13SPR2XB1A2A0S2sp1X1n1P5limbs2nb2P02XB1AS2sp1X1n1P5limbs2nb2P02XB1AS2sp1X1n1P5limbs2nb2P02XBS2sp1X1n1P5limbs2nb2P02XB1AFFFS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2X02P02K13SPR2XB1A2A0FFS2sp1X1n1P5limbs2nb2lo2P03DSX2XBS1X1n1P5limbs2nb2LL2P02K12XB1A2KP2PAFS1X1n1P5limbs2nb2P02K12XB1A2XA2KPS1R2sp1X1n1P5limbs2nb2lo3LOS2LL2P02PC2K13ALO2XBS1n5limbs2LLS1R2sp1X1n2nb2lo2XB3SPR2K13SLO3NRMS1R2sp2lo3SLO3NRA3SPRFS2sp1X1n1P5limbs2nb2P02XB1AS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2X02LL2P02PC2K13ALO3SPR2XB1A2A0FFFFS1R3HIA1h2sp1X1n2nb2XB3TOPFS1R3HIA1h1d2h21H4HFR2S1R3HIA1h2sp1X1n2nb2XB4BUD'FS2sp1X1n2nb2XB3SPR2K14NB10FS2sp1n2nb4NB102K13SPRS1n2nb2NR4NB102K1S2sp1X1n1P5limbs2nb2lo2P02XB1AS2sp1X1n1P5limbs2nb2P02XB1AS2sp1X1n1P5limbs2nb2P02XB1AS1n1PS1nS2sp1X1n1P5limbs2nb2P02XB1AS2sp1X1n2nb2lo2NR2K11A2XA2ASS2sp1X1n5limbs2nb2lo2LL2K11A2XA2ASFS1n5limbs2nb2LL2K1S1n2nb2K11AS1n5limbs2nb2K11AS2spS1R3HIA2sp1X1n2nb2h22XB4TOP2S1R3HIA2sp2h24TOP2FS1R5NEEDR2sp2lo3LOS3SLO3ALOS1R5NEEDR2sp2nb2lo2NB3LOS3SLO3ALO3SPR1A2A02ACS1R5NEEDR2sp1X1n1P5limbs2nb2lo3SLO2X02LL2P02K13SPR2XB1A2A02ASS1n2nb2NR2K1S1n2nb2K1S1R2lo3LOS3ALO3ACPSS1n1P2nb2K11A2PAFS1n1P2nb2K11A2N12PAS1n2NRS1R3HIA1h1d2h22h44HFR24HFR4S1R2sp1X1n2nb2lo2XB3SLOS1n2nb2NR2K1S1R3HIA1h2sp1X1n2nb1d2XB3SPR2K14BUDF2D0S1n2nb2K12N1S1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA2sp2lo2h24TOP25HTOP2FS2nbS1AS1n2nb2lo2K11A2ASSSS1R1n1P2lo3LOS2PC3ALOS1R3HIA1hS1XS1R2nb2lo3LOS3ALO1A2ACS2sp1X1n2nb2XBFFFFFFFS1n5limbs2LL1AS2sp1X1n1P5limbs2nb2X02P02XB1AS2sp1X1n1P5limbs2nb2X02P02XB1AS2sp1X1n1P5limbs2nb2P02XB1AS2sp2loS1R3HIA1h2sp1X1n2nb2h22XB3SPR2K14BUD'3HV2S1PS1R5NEEDR2sp2lo3LOS3SLO3ALOS1n2nb2K1S2sp1X1n2nb2XB3SPR2K14NB102N1S1R3HIA1h2sp1X1n2nb1d2h22XB3SPR2K14BUDF4HFR2S1n2nb2K1FS1R5NEEDR2sp2lo3LOS3SLOFFS1R1n1P2PC3ACVS2sp1X1n1P5limbs2nb2X02P02XB1AS2sp1X1n1P5limbs2nb2X02P02XB1AS2sp1X1n1P5limbs2nb2P02XBFS1XS1n5limbs2LLS1n5limbs2LL1AS2sp1X1n5limbs2nb2lo2LL2K11A2XA2ASFFS2KPS1A2A02KZS1n1P2nb2K11A2N12PA2E1S1n1l2LL2EnS1P2KP2B0S1R2lo3LOSS1n2NRS1n2nb1AFFS2sp1X1n1P5limbs2nb2NR2P02XB1AS1n2NRS2sp1X1n1P5limbs2nb2NR2P02XB1AS1RS1n1PFFS1R2sp1X1n2nb2lo3SPA2XB3SPR2K13ACP5NEEDR3LOS3SLO3ALOS1R2sp1X1n2nb2lo3SPA2XB3SPR2K13ACP5NEEDR3LOS3SLO3ALOS1R3HIA1h2sp1X1n1P5limbs2nb2X02P02K13SPR2XB2h23HV21A2A02h43HV4S2sp1X1n2nb2XB2NBS1R1n2nb2K11A2AC3ACVFFS1XS1R3HIA1h2sp1X1n1P5limbs2nb2X02P02K13SPR2XB2h23HV2S1R3HIA1h2sp1X1n1P5limbs2nb2X02P02K13SPR2XB2h23HV21A2A0S2nbS2spS1n5limbs2nb2LL2K1S1n1P5limbs2LLFS1R2sp1X1n1P5limbs2nb2lo3LOS2P02K13ALO2XB1A2AC2N13x291CS2sp1X1n1P5limbs2nb2lo2P02XB3x291CS2sp1X1n1P5limbs2nb2lo2P02XB3x291CFFFFFFFFFFFFS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P02K13ALO2XB1A2ACS2sp1X1n1P5limbs2nb2P02XBS2sp1X1n1P5limbs2nb2P02XBS2sp1X1n1P5limbs2nb2P02XBS2sp1X1n1P5limbs2nb2P02XBS2sp1X1n1P5limbs2nb2lo2P02K12XB1A2ASS1R2sp1X1n1P5limbs2nb2lo3LOS2P02K13ALO2XB1A2ACFS1X1n1P5limbs2nb2P02K12XB1AS2sp1X1n1P5limbs2nb3ALX2X02P02K12XB1AS2sp1X1n1P5limbs2nb3ALX2X02P02K12XB1AFS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P02K13ALO3ACP3SPR2XBS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P02K13ALO3ACP3SPR2XBS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P02K13ALO3ACP3SPR2XBS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P02K13ALO3ACP3SPR2XBS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P02K13ALO3ACP3SPR2XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBFS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XB1AS1X1n1P5limbs2nb2lo2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS2sp1X1n1P5limbs2nb2lo2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBFFS1X1n1P5limbs2nb2X02P02XBS1X1n1P5limbs2nb2X02P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBFS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P02K12XBS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P02K12XBS1X1n1P5limbs2nb2X02P02XBS1X1n1P5limbs2nb2X02P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBFFFS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P02XB". (* [comment removed for export] *)
    #[using="C24T IMG ZF CALLOC AMC NEEDR DIMG HNS NB XW DSP LOS SLO TOP SPA TPV XUW jk1 HH1 HXS1 PCH1 OX1 FR1 ST1 MI1 HP1 ALX X0 LL NR SG P0 PC PHEAP PNULL CW DXP DSX ND NB10 BUD BUDF"] Lemma grow_path : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shrink ()) "Pxra,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa0,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxs3,(>.&40.)Pxs4,(>.&40.)Pxs7,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(4.Vn,Vnb,)(5:.$=.(5;.$=.VR,VHIA,Vh,Vmo,)(45.$=.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$:.(;.Vnb,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(40.(41.Vnb,Vn,))(7.Vd,)Vlo,Vm,Vmo,)(22.(23.R14.(24.&40.(14.(11.&40.Vsp,)-50.))Vgp,Vtp,R13.R12.R11.(24.&40.VX,)(24.&40.(14.VX,+:.))R10.R?.R>.R=.R<.R;.R:.R9.(24.&40.Vnb,)R8.R7.(24.&40.(34.(1=.VR,)))(24.&40.(14.(35.(14.VX,+:.)+3.)(34.(1=.VR,))))R6.Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(24.&40.+9;<64.)Vfc,(26.(>.&40.))Vm1,(27.$=.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros K1. basic_facts h LB m1 HH1 TOP.
      rewrite shrink_FR_val in BUDF. pose proof BUD as BUD'. unfold grow_PHI in BUD'. rewrite Z.max_l in BUD' by (clear - K1; lia).
      pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0.
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      pose proof (rw_cells_bound _ _ _ _ HXS1) as XB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
      pose proof (client_wrange_keep L LB LF _ _ dX X 16 CW DXP) as CWk.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      calloc_call nb.
      all: match goal with |- forall _ _, _ -> aevtS _ _ _ => idtac | |- ?g => idtac "CALLOC1-LEFT:" g end.
      (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
      ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
      unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by qlia.
      ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
      (* [comment removed for export] *)
      assert (PCH2 : own = LHeap -> rw_cells asegs m2 P [CB (4 * length limbs)%nat (u32s limbs)]).
      { intros E0. ddestruct (PHEAP E0) as (B0' & HIN' & _).
        eapply (presA_rw_cells asegs R); [exact HP2| exact (PCH1 E0)| | cbn; clear; tauto].
        simpl_sizes. eapply client_range_block; [apply in_app_iff; left; exact HIN'| clear; lia| clear - LL; lia]. }
      presA_transport HP2.
      assert (HPX2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
      { eapply presA_trans; [exact HP1|].
        eapply presA_weaken; [exact HP2| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]. }
      clear HP2.
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OX1) as OX2.
      assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
      pose proof (hcs_ok asegs R HIA h2) as CSOK2. pose proof (cs_ok_sb _ _ CSOK2) as SB64'. pose proof (hcs_stack asegs R HIA h2) as SCS2.
      (* [comment removed for export] *)
      zstep. zstep.
      destruct CASES as [[E0 HH2] | (A & E0 & A16 & HFRA & HAS & HH2 & HNEW)]; match type of E0 with ?v = _ => subst v end.
      - (* [comment removed for export] *)
        pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP2.
        assert (MA2 : mpd_at asegs m2 LB dX).
        { eapply mpd_at_rebuild; [exact HNS| unfold mpi_cells; exact HXS1| exact ALX| exact X0| exact LL| unfold MPI_MAX_LIMBS; clear - NR; lia| exact SG| exact PNULL|].
          intros E. ddestruct (PHEAP E) as (B0 & HIN & HP16 & N1). split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
          eapply (u32arr_of_cells asegs); [exact (PCH2 E)| reflexivity]. }
        zstep.
        epi_return h2 LB MBEDTLS_ERR_MPI_ALLOC_FAILED FR1 LAWS2 KINV2.
        eapply post_keep; post_side.
        all: match goal with |- ?g => idtac "GFAIL-LEFT:" g end.
      - (* [comment removed for export] *)
        replace (nb * 4) with (4 * nb) in HFRA, HAS, HH2, HNEW by (clear; lia).
        pose proof (hm_top asegs R HIA h2 _ LF m2 HH2) as HTOP2.
        assert (SCS2' : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS2| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
        dpose HFRA as (A0 & AC & AD & HAP).
        pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * nb) :: LB) LF m2 A (4 * nb) HH2 (or_introl eq_refl)) as OA.
        assert (HINA : In (A, 4 * nb) (((A, 4 * nb) :: LB) ++ fdata LF)) by (left; reflexivity).
        assert (XA : X + 16 <= A \/ A + 4 * nb <= X).
        { destruct (fresh_apart_client R LB LF (bv_unsigned sp) X 16 A (4 * nb) HFRA); [| clear; lia| clear - K1 NR; lia| clear - ALO LOS SLO NEEDR; lia| right; assumption| left; assumption].
          eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]. }
        assert (AS : A + 4 * nb <= lo) by (clear - AC ALO LOS; lia).
        (* [comment removed for export] *)
        zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - A0 AC H; lia); clear - KZ A0; lia|]. clear KZ.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. if_cases KP; zify_cond KP.
        + (* [comment removed for export] *)
          rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
          assert (EO : own = LNull) by (destruct own; [reflexivity| exfalso; destruct (PHEAP eq_refl) as [B0 _]; clear - B0 KP; lia| exfalso; exact (HNS eq_refl)]).
          destruct (PNULL EO) as [EP En].
          assert (limbs = []) as EL by (destruct limbs; [reflexivity| exfalso; cbn in LL; clear - LL En; lia]).
          assert (CW3 : client_wrange L (((A, 4 * nb) :: LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
          { eapply client_wrange_mono; [exact CW|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; exact Hb]. }
          eapply (aevtA_cut_evtA asegs AL _ LAWS2 _ _ _ _ _ _ KINV2);
            [ eapply fin_walk with (hc := h2) (LBc := (A, 4 * nb) :: LB); try eassumption; try reflexivity
            | intros y Hy; exact Hy | ].
          all: try (unfold mpi_cells; exact HXS1).
          all: try (clear - A0 AC ALO LOS SLO SPR NEEDR NB; lia).
          all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "GFIN0-PRE-LEFT:" g end.
          intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & ST9 & HH9). subst ms'.
          lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
          apply aevtA_done. intros mo9 [HK9 MF9].
          assert (HA9 : u32arr asegs m9 A (repeat (Z_to_bv 64 0) (Z.to_nat nb))).
          { replace (Z.to_nat (4 * nb)) with (4 * Z.to_nat nb)%nat in HNEW by (clear - K1 NR; lia).
            eapply (u32arr_of_cells asegs); [| symmetry; apply u32s_repeat0].
            eapply (rw_cells_transport asegs _ m2 m9); [exact HNEW| exact MU| exact WM|].
            cbn [disjoint_from cells_size csize Nat.add]. clear - XA AS K1 NR; lia. }
          assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
          { eapply presA_trans; [exact HPX2|]. rewrite <- HS2.
            eapply (presA_tail asegs R HIA h2 ((A, 4 * nb) :: LB)); [exact HH2| intros b Hb; right; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP2| exact OX2| exact MU| exact WM]. }
          eapply (post_new nb A (repeat (Z_to_bv 64 0) (Z.to_nat nb)) LB mo _ h2); try post_side.
          all: try (clear - K1 NR NB10; lia).
          all: try (rewrite repeat_length; clear - K1 NR; lia).
          all: try (rewrite EL, limbs_val_repeat0; reflexivity).
          all: try (intros b Hb; exact Hb).
          all: try (intros b Hb _; exact Hb).
          all: try (cbn [mpd_blk md_own md_p md_n]; rewrite EO; intros b []).
          all: match goal with |- ?g => idtac "GFIN0-LEFT:" g end.
        + (* [comment removed for export] *)
          assert (EO : own = LHeap).
          { destruct own; [| reflexivity| exfalso; exact (HNS eq_refl)]. exfalso. rewrite (proj1 (PNULL eq_refl)) in KP.
            rewrite ?unsigned_lit in KP by (clear; lia). clear - KP. lia. }
          ddestruct (PHEAP EO) as (B0 & HIN & HP16 & N1). pose proof (PCH2 EO) as PCH. clear PCH2.
          rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
          pose proof (DXP EO) as DXP'. pose proof (DSP ltac:(rewrite EO; discriminate)) as DSP'.
          pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * nb) :: LB) LF m2 P (4 * n) HH2 (or_intror HIN)) as OP.
          assert (PA : A + 4 * nb <= P \/ P + 4 * n <= A) by (apply HAP; apply in_app_iff; left; exact HIN).
          assert (HINP : In (P, 4 * n) (((A, 4 * nb) :: LB) ++ fdata LF)) by (right; apply in_app_iff; left; exact HIN).
          (* [comment removed for export] *)
          shadow_chk OX2 (X + 10) 2.
          zstep.
          replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
            by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
          zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
          zstep. zstep.
          (* [comment removed for export] *)
          assert (HN2 : rw_cells asegs m2 A ([CB (4 * length limbs)%nat (repeat (Z_to_bv 8 0) (4 * length limbs))]
                                              ++ [CB (Z.to_nat (4 * (nb - n))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * (nb - n))))])).
          { eapply rw_cells_reshape; [exact HNEW| |].
            - cbn. rewrite !repeat_length; repeat split; reflexivity.
            - cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- repeat_app. f_equal. clear - LL K1; lia. }
          apply rw_cells_app in HN2. destruct HN2 as [HNA HNB]. cbn [cells_size csize Nat.add] in HNB. clear HNEW.
          replace (A + Z.of_nat (4 * length limbs + 0)) with (A + n * 4) in HNB by (clear - LL; lia).
          apply (u8arr_of_rw_cells asegs) in HNA.
          pose proof (proj1 (u32arr_of_cells asegs m2 P _ _ limbs PCH eq_refl)) as PBA.
          pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + n * 4); (X, X + 16)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2'.
          pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_SH) as SPC. unfold A_ASAN_MEMCPY_SH in SPC.
          acallxA_sp (bv_unsigned sp + -80)
            (eapply SPC with (h := h2) (LB := (A, 4 * nb) :: LB) (LF := LF) (DST := A) (SRC := P) (n := n * 4) (lo := lo)
                              (ds := repeat (Z_to_bv 8 0) (4 * length limbs)) (ss := u32s limbs);
             rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia;
             try eassumption; try reflexivity;
             first [ left; rewrite AMC; reflexivity
                   | rewrite repeat_length; clear - LL; lia
                   | rewrite u32s_length; clear - LL; lia
                   | eapply aobj_sub; [exact OA| clear; lia| clear - K1 LL; lia]
                   | eapply aobj_sub; [exact OP| clear; lia| clear; lia]
                   | right; clear - PA K1 N1; lia
                   | left; clear - AS PC ALO LOS K1 N1; lia
                   | right; pose proof (alloc_ceiling_val R) as ACV; clear - AC PC K1 N1 ACV; lia
                   | eapply crange_sub; [exact SCS2| clear - LOS; lia| clear - TOP2 HTOP2; lia]
                   | eapply client_wrange_block; [exact HINA| clear; lia| clear - K1; lia]
                   | clear - NR NB10 K1 LOS SLO NEEDR NRA TOP2 SPA SPR; lia
                   | match goal with |- ?g => idtac "MEMCPY1-PRE-LEFT:" g end ]).
          clear SPC.
          all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY1-SIDE:" g end.
          lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
          match goal with H : u8arr asegs m3 A (u32s limbs) |- _ => rename H into HPA end.
          match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
          match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
          match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep.
          shadow_chk OX2 (X + 10) 2.
          zstep.
          replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
            by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
          zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
          zstep.
          replace (4 * length limbs)%nat with (Z.to_nat (n * 4)) in PCH by (clear - LL; lia).
          assert (CW4 : client_wrange L (((A, 4 * nb) :: lb_remove P LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
          { eapply client_wrange_mono; [exact CWk|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff.
            destruct Hb as [Hb|Hb]; [left; right; eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb] | right; exact Hb]. }
          free_limbs_call h2 ((A, 4 * nb) :: LB) HIN PCH.
          all: match goal with |- forall _ _, _ -> aevtS _ _ _ => idtac | |- ?g => idtac "ZF1-LEFT:" g end.
          (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
          destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
          rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by qlia.
          ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
          lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
            replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
          lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
          match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
          rewrite (lb_remove_cons_other A (4 * nb) P LB) in HP4, HH4 by (clear - PA K1 N1; lia).
          assert (HP4' : presA asegs R ((A, 4 * nb) :: lb_remove P LB) LF (bv_unsigned sp + -80) (arl_stklo R) (hstkhi asegs R HIA h2) [] m3 m4).
          { eapply (presA_drop_freed asegs R HIA h2 ((A, 4 * nb) :: LB) LF _ [] P (4 * n) m3 m3 m4);
              [exact HH3| right; exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia
              | replace (P + 4 * n) with (P + n * 4) by (clear; lia); exact HP4].
            intros b xb [Hb|Hb] Hr.
            - subst b. split; [left; reflexivity|]. intros E. injection E as E1 E2. clear - E1 PA K1 N1. lia.
            - split; [right; eapply In_lb_remove; exact Hb|]. intros E. subst b. exact (lb_remove_notin LB P (4 * n) ND Hb). }
          clear HP4 PCH PBA OP HINP HINA.
          apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
          presA_transport HP4'.
          apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
          pose proof (AIh_laws asegs R HIA h4) as LAWS4. pose proof (KF_kinv asegs R HIA h4 mo) as KINV4.
          pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS4 OX2) as OX4.
          assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
          (* [comment removed for export] *)
          eapply (aevtA_cut_evtA asegs AL _ LAWS4 _ _ _ _ _ _ KINV4);
            [ eapply fin_walk with (hc := h4) (LBc := (A, 4 * nb) :: lb_remove P LB); try eassumption; try reflexivity
            | intros y Hy; exact Hy | ].
          all: try (rewrite HT4; exact HT2).
          all: try (unfold mpi_cells; exact HXS1).
          all: try (clear - A0 AC ALO LOS SLO SPR NEEDR NB; lia).
          all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "GFIN1-PRE-LEFT:" g end.
          intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & ST9 & HH9). subst ms'.
          lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
          apply aevtA_done. intros mo9 [HK9 MF9].
          (* [comment removed for export] *)
          assert (HA9 : u32arr asegs m9 A (limbs ++ repeat (Z_to_bv 64 0) (Z.to_nat (nb - n)))).
          { apply u32arr_app. split.
            - eapply (u32arr_of_cells asegs); [| reflexivity].
              eapply (rw_cells_transport asegs _ m4 m9); [exact HPA| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - XA AS K1 NR LL; lia].
            - replace (A + 4 * Z.of_nat (length limbs)) with (A + n * 4) by (clear - LL; lia).
              replace (Z.to_nat (4 * (nb - n))) with (4 * Z.to_nat (nb - n))%nat in HNB by (clear - K1 NR; lia).
              eapply (u32arr_of_cells asegs); [| symmetry; apply u32s_repeat0].
              eapply (rw_cells_transport asegs _ m4 m9); [exact HNB| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - XA AS K1 NR LL; lia]. }
          (* [comment removed for export] *)
          assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
          { eapply presA_trans; [exact HPX2|]. eapply presA_trans; [| eapply presA_trans].
            - (* [comment removed for export] *)
              eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                        (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16)]);
                [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
              eapply (presA_drop_fresh asegs R HIA h LB LF [(X, X + 16)] A (n * 4) m2 m3 (bv_unsigned sp));
                [| eapply fresh_apart_sub; [exact HFRA| clear - K1 N1; lia] | clear - ALO LOS SLO NEEDR; lia].
              eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) _ m2 m3); [exact HH1| | clear; lia| exact LOS].
              eapply (presA_of_munch asegs R LB LF _ _ _ _ m2 m3 (hcs asegs R HIA h2) CSOK2); [| | exact MU2 | exact WM2'].
              + unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS2'|].
                apply Forall_cons; [cbn [fst snd]; replace (A + n * 4 - A) with (n * 4) by lia; eapply aobj_crange; eapply aobj_sub; [exact OA| clear; lia| clear - K1; lia]|].
                apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX2|]. apply Forall_nil.
              + intros c0 Hc. eapply cshd_hcs; [exact HH3| | rewrite HS2; eapply cshd_mono_lb; [exact Hc| intros b Hb; right; exact Hb]]. clear; lia.
            - (* [comment removed for export] *)
              eapply presA_weaken; [exact HP4'| | intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HS2; clear; lia| intros y _; exact I].
              intros b Hb. right. eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb].
            - (* [comment removed for export] *)
              rewrite <- HS2, <- HS4.
              eapply (presA_tail asegs R HIA h4 ((A, 4 * nb) :: lb_remove P LB)); [exact HH4| | exact LOS| exact TOP4| exact OX4| exact MU| exact WM].
              intros b Hb. right. eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb]. }
          eapply (post_new nb A (limbs ++ repeat (Z_to_bv 64 0) (Z.to_nat (nb - n))) (lb_remove P LB) mo _ h4); try post_side.
          all: try (clear - K1 NR NB10; lia).
          all: try (rewrite length_app, repeat_length; clear - LL K1 NR; lia).
          all: try (rewrite limbs_val_app, limbs_val_repeat0, Z.mul_0_r, Z.add_0_r; reflexivity).
          all: try (intros b Hb; eapply In_lb_remove; exact Hb).
          all: try (intros [Bb kb] Hb Hn; apply In_lb_remove_keep; [exact Hb|]; apply (nodup_fst_neq LB P (4 * n) Bb kb ND HIN Hb); intros E; apply Hn; cbn [mpd_blk md_own md_p md_n]; rewrite EO; left; symmetry; exact E).
          all: try (cbn [mpd_blk md_own md_p md_n]; rewrite EO; intros b [<-|[]]; first [exact (lb_remove_notin LB P (4 * n) ND) | exact HIN]).
          all: match goal with |- ?g => idtac "GFIN1-LEFT:" g end.
      all: match goal with |- ?g => idtac "GROW-PATH-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "03=0@C17025492443.211C31740276271.212D16049893661.213D20501856385.213D3271578208.241 D3284265934.240 D33868571107.238D37703914153.238D37703914153.240D39360408676.165D39375475909.240D41458601420.240D41471292514.241D42750138435.238D42750138435.240D49352068557.240D50796826103.213D63595235433.213K25897202343.212K36795542264.212K53933808495.212K60573057312.211K61205767951.212K65071292344.212L10895938021.5  L11468776467.3  L11500667164.45 L11504513181.18 L11581774232.15 L1160237219.266 L11668949970.180L12694533441.2  L12750819336.13 L12755534717.11 L14213301620.45 L14369733550.2  L16256253080.7  L17379191427.45 L17585880332.15 L18468365315.17 L18468466326.180L19947878820.266L22230398665.18 L23100341967.180L23100341967.204L24912882372.1  L25426167464.13 L25890634160.2  L26892418956.1  L27002055060.56 L27006593843.18 L27173483799.164L27453137369.3  L27948009755.1  L28715365361.3  L28767265244.7  L28813938827.17 L28814040852.180L29428324939.5  L32130153560.8  L32693198944.7  L3278082148.2   L32987209960.7  L33087634096.2  L34120414369.0  L34171955900.9  L34425511348.56 L34838900123.45 L35653441506.7  L35655538624.7  L36341307619.3  L36807145629.3  L37102430021.12 L37714553091.1  L38948636245.0  L39172636981.0  L40281191306.3  L40290687782.1  L40825381997.45 L41134980759.3  L41212707352.9  L41335755164.4  L41471587942.8  L42201630183.266L42762855401.8  L43170267636.10 L43170267636.15 L44697879740.4  L45013738119.47 L46160487540.204L46357874486.245L46732241046.2  L46952686640.56 L47209170218.1  L48132467214.7  L48225685459.8  L49346311443.56 L49591653831.56 L50790809970.7  L51040919409.15 L51647682115.12 L51794599906.3  L51794636988.45 L51879758738.7  L51881576583.10 L52236805504.8  L5262145463.201 L53923074168.4  L5479049730.1   L58765998846.9  L59308632307.3  L59308633593.3  L59308661072.8  L59800442951.3  L60098763854.3  L60447862057.2  L60576273221.2  L6113407666.7   L61211782168.3  L61929067222.203L61929718192.2  L62018535662.1  L62124143020.12 L62369652128.2  L62624471726.49 L63259805175.45 L63260063441.56 L63792902737.267L64966926188.10 L64968776825.7  L65064387521.5  L65066372573.4  L656136024.1    L65625398152.45 L66610669263.189L67033008523.4  L6935467336.1   L7830778770.3   L8810490561.4   N12401863469.212N20716133971.212N31170017719.212N32071669760.212N61761254804.212O11257354870.212O17025492443.211O29478932113.212O31740276271.212O39322336069.212O47259422021.212O49587672251.211O57399310481.212P25897202343.212P28709353702.212P35876208370.238P35876208370.240P35878422099.164P35878422099.165P44704452523.211P60573057312.211Q12370813529.188Q12370813529.210Q16049893661.214Q17203156213.187Q17207350632.211Q26056220419.194Q26056447029.133Q26056447030.216Q26058334103.151Q26058334103.234Q26207421841.211Q26207721832.212Q26209819600.209Q29651637810.188Q29651637810.210Q31654082872.211Q37621083927.187Q37623180338.209Q37703787028.214Q38248387216.214Q39212284437.212Q43879899724.214Q43925228937.212Q45094823946.214Q45992448992.165Q45998615361.239Q5262061745.133 Q5262061746.216 Q5473018122.187 Q5483504175.209 Q5485174314.188 Q5485174314.210 Q5485600919.211 Q57478834698.214Q60511567613.212Q60537752176.238Q60543922897.164Q60697995187.212Q6143569392.188 Q6143569392.210 Q63595235433.214Q65983947055.188Q65983947055.210Q8882911372.209 Q9540572287.209 00000100200300400500600V01601V01o02O02P02Q02R02S03C04F04G04H04m05Y05Z06:07107B07N08008E08F08f09k09l09m09n0:H0:I0:^0;;0;<0;j0<i0=L0=^0>90>Y0>\0?=0?>0?B0?^0@00@I0@Q0@T0@U0A00A^0B]0Bo0C:0CI0CJ0C\0Cb0Cc0D>0DU0E<0ET0Eo0F70F80FR0FU0FV0FW0F`0Fc0G10G90G:0GD0GE0Ge0Gf0Gg0Gh0Gi0Gj0HM0Hm0I40I_0Ib0J=0JF0Ja0KM0Kd0Ke0Kf0Kn0LA0LB0LU0Lh0MK0ML0MO0MP0MY0Mb0N70N?0NI0NO0NP0Ne0Nf0OI0OO0OR0O]0Ob0Oc0PW0QK0RQ0R_0R`0Ra0Rb0Re0SB0T90T>0TB0TJ0TX0UT0V;0Vb0Vc0Vd0Ve0Vf0Vg0Vh0Vi0Vj0Vk0Vl0Vm0Wm0XK0Xi0YB0Y[0ZA0ZB0Zg0[T0[U0[k0\F0]I0^D0_G0`B0aE0a`0b;0bV0bW0bX0c30cI0cd0dA0d_0e:0e[0f60fS0fT0fU0fn0gL0gb0h=0hS0hn0iI0iJ0ie0j\0kK0ki0l?0lZ0l[0l\0l]0m80mSFFFFFFS2sp1X1n1P5limbs2nb2P01k2XB1A2LKS2sp1X1n1P5limbs2nb2P01k2XB1A2LKS2sp1X1n1P5limbs2nb2P01k2XB1A2LKS2sp1X1n1P5limbs2nb2P02XBS2sp1X1n1P5limbs2nb2P01k2XB1A2LKFFFFS2sp1X1n1P5limbs2nb2X02P01k2Hk2K13SPR2XB1A2A02LKS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2X02P01k2Hk2K13SPR2XB1A2A02LKFFS2sp1X1n1P5limbs2nb2lo2P03DSX1k2XB2LKS1X1n1P5limbs2nb2P01k2Hk2K12XB1A2PA2KP2LK2LLFS1X1n1P5limbs2nb2P01k2XB1A2XA2LKS1R2sp1X1n1P5limbs2nb2lo3LOS2P02PC1k2Hk2K13ALO2XB2LK2LLS1n5limbs2LL1k2HkS1n5limbs2LLS1R2sp1X1n2nb2lo2XB3SPR2K13SLO3NRMS1R2sp2lo3SLO3NRA3SPRFS2sp1X1n1P5limbs2nb2P01k2XB1A2LKS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2X02P02PC2K13ALO3SPR2XB2N11A2A0FFFS1R3HIA1h2sp1X1n2nb2XB3TOPFS1R3HIA1h1d2h21H4HFR2S1R3HIA1h2sp1X1n2nb1k2XB4BUDkFS1R5NEEDR2sp1n2lo3LOS3SLO1k2Hk3ALO3SPR1A2A02ACS1R5NEEDR2sp1X1n1P5limbs2nb2lo3SLO2X02P01k2Hk2K13SPR2XB1A2A02ASS2sp1X1n1P5limbs2nb2lo2P01k2XB1A2LKS2sp1n2NR1k2Hk3SPRS2sp1X1n1P5limbs2nb2P02XB1AS2sp1X1n1P5limbs2nb2P01k2XB1A2LKS1nS2sp1X1n5limbs2lo1k2Hk1A2XA2AS2LKFS2spS1R3HIA2sp1X1n2nb2h22XB4TOP2S1R3HIA2sp2h24TOP2S2sp1X1n1P5limbs2nb2P02XBS1n1k2HkS1kFS1R5NEEDR2sp2lo3LOS3SLO3ALOS1R5NEEDR2sp1n2lo3LOS3SLO1k2Hk3ALO3SPR1A2A02ACS1R5NEEDR2sp1X1n1P5limbs2nb2lo3SLO2X02P01k2Hk2K13SPR2XB1A2A02ASS1R2lo3LOS3ALO3ACPS1n2NR1k2HkS1n1P1k2Hk1A2PAFS1n1P1k2Hk2N11A2PAS1n2NRSS1R3HIA1h1d2h22h44HFR24HFR4S1R2sp1X1n2nb2lo2XB3SLOS1R3HIA1h2sp1X1n2nb1d2XB3SPR2K14BUDF2D0S1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA2sp2lo2h24TOP25HTOP2S1n1k2HkFS1R1n1P2lo3LOS2PC1k2Hk3ALOS1ASSS1R3HIA1hS1XS2sp1X1n2nb2XBS1n1k2HkFS1n1P1k2HkFS2sp1X1n1P5limbs2nb2P01k2XB1A2LKFFFFFS2sp1X1n1P5limbs2nb2X02P01k2XB1A2LKS2sp1X1n1P5limbs2nb2P01k2XB1A2LKS2sp2loS1R3HIA1h2sp1X1n2nb1k2h22XB3SPR2K14BUDk3HV2S1PS1R5NEEDR2sp2lo3LOS3SLO3ALOS1n2nb2K1S2sp1X1n2nb2NR2XB3SPR2K12N1S1R3HIA1h2sp1X1n2nb1d2h22XB3SPR2K14BUDF4HFR2S1R5NEEDR2sp2lo3LOS3SLOFFS1n1k2HkS2sp1X1n2nb1k2Hk2XBFS1R1n1P2PC1k2Hk3ACVS1R3HIA1h1n2nb1k2HkS2sp1X1n1P5limbs2nb2X02P01k2XB1A2LKFS1XFS1P2B02KPS1A2A02KZS1n1P1k2Hk2N11A2PA2E1S1n1k2HkS1R2lo3LOSS1n2NRFS1R2lo3LOS1k3ALO1A2ACFS2sp1X1n1P5limbs2nb2NR2P01k2XB1A2LKS1n2NRS1RS2lo1k1A2ASS1n1PFS1R2sp1X1n2nb2lo3SPA2XB3SPR2K13ACP5NEEDR3LOS3SLO3ALOS1R2sp1X1n2nb2lo3SPA2XB3SPR2K13ACP5NEEDR3LOS3SLO3ALOS1R3HIA1h2sp1X1n1P5limbs2nb2X02P01k2Hk2K13SPR2XB2h23HV21A2A02LK2h43HV4S1R1k1A2AC3ACVFFFS1XS2sp1X1n2nb1k2NR2Hk2XB3SPR2K1S1R3HIA1h2sp1X1n1P5limbs2nb2X02P01k2Hk2K13SPR2XB2h23HV2S1k1AS2spS1n1k2HkS1n1P5limbs2LLS1R2sp1X1n1P5limbs2nb2lo3LOS2P01k2Hk2K13ALO2XB1A2AC2LK3x291CS2sp1X1n1P5limbs2nb2lo2P01k2XB2LK3x291CS2sp1X1n1P5limbs2nb2lo2P01k2XB2LK3x291CFFFFFFFFFFFS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P01k2Hk2K13ALO2XB1A2AC2LKS2sp1X1n1P5limbs2nb2P01k2XB2LKS2sp1X1n1P5limbs2nb2P01k2XB2LKS2sp1X1n1P5limbs2nb2P02XBS2sp1X1n1P5limbs2nb2P02XBS2sp1X1n1P5limbs2nb2lo2P01k2XB1A2AS2LKFS2sp1X1n1P5limbs2nb3ALX2X02P02K12XB1AS2sp1X1n1P5limbs2nb3ALX2X02P01k2Hk2K12XB1A2LKFS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P01k2XB2LKS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P01k2Hk2K13ALO3ACP3SPR2XB2LKS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P02K13ALO3ACP3SPR2XBS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P01k2Hk2K13ALO3ACP3SPR2XB2LKS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P02K13ALO3ACP3SPR2XBS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P01k2Hk2K13ALO3ACP3SPR2XB2LKS1X1n1P5limbs2nb2P01k2XB2LKS1X1n1P5limbs2nb2P01k2XB2LKS1X1n1P5limbs2nb2P01k2XB2LKFFS1X1n1P5limbs2nb2P01k2XB2LKS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P01k2XB2LKS1X1n1P5limbs2nb2P01k2XB1A2LKS1X1n1P5limbs2nb2lo2P01k2XB2LKS1X1n1P5limbs2nb2P01k2XB2LKS2sp1X1n1P5limbs2nb2lo2P01k2XB2LKS1X1n1P5limbs2nb2P01k2XB2LKS1X1n1P5limbs2nb2P01k2XB1A2LKFFS1X1n1P5limbs2nb2X02P02XBS1X1n1P5limbs2nb2X02P01k2XB2LKS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P01k2XB2LKS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P01k2XB2LKS1X1n1P5limbs2nb2P01k2XB2LKFS1X1n1P5limbs2nb2P01k2XB2LKS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P01k2Hk2K12XB2LKS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2P02K12XBS1X1n1P5limbs2nb2X02P01k2XB2LKS1X1n1P5limbs2nb2P02XBS1X1n1P5limbs2nb2P01k2XB2LKFFFS1X1n1P5limbs2nb2P01k2XB2LKS1X1n1P5limbs2nb2P01k2XB2LK". (* [comment removed for export] *)
    #[using="C24T IMG ZF CALLOC AMC NEEDR DIMG HNS NB XW DSP LOS SLO TOP SPA TPV XUW jk1 HH1 HXS1 PCH1 OX1 FR1 ST1 MI1 HP1 ALX X0 LL NR SG P0 PC PHEAP PNULL CW DXP DSX ND NB10 BUD BUDF"] Lemma shrink_from24 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shrink ()) "Pk,$1.Pxra,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa0,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxs2,(>.&40.)Pxs3,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(21.$5<.Vown,$5=.)P,(2.(3.+1.R14.)(3.R14.Vn,))P,(3.Vnb,R15.)P,(4.Vnb,Vn,)P,(54.Vlimbs,R17.)(5:.$=.(5;.$=.VR,VHIA,Vh,Vmo,)(45.$=.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$:.(;.Vnb,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(40.(41.Vnb,Vn,))(7.Vd,)Vlo,Vm,Vmo,)(22.(23.R17.(24.&40.(14.(11.&40.Vsp,)-50.))Vgp,Vtp,R16.R15.R14.(24.&40.VX,)(24.&40.(14.VX,+:.))R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.(24.&40.R18.)(24.&40.(34.(1=.VR,)))(24.&40.(14.(35.(14.VX,+:.)+3.)(34.(1=.VR,))))(24.&40.(14.(35.VX,+3.)(34.(1=.VR,))))Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(24.&40.+9;<<4.)Vfc,(26.(>.&40.))Vm1,(27.$=.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros EO Hk HNB K1 ZXk. basic_facts h LB m1 HH1 TOP.
      rewrite shrink_FR_val in BUDF. pose proof BUD as BUD'. unfold grow_PHI in BUD'.
      assert (BUDk : havol asegs R HIA h + (8 * k + 2 * AVOL_CALL) <= AVOL_MAX) by (eapply Z.le_trans; [| exact BUD']; clear - Hk HNB; unfold AVOL_CALL; lia).
      pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0.
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      pose proof (rw_cells_bound _ _ _ _ HXS1) as XB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
      pose proof (client_wrange_keep L LB LF _ _ dX X 16 CW DXP) as CWk.
      ddestruct (PHEAP EO) as (B0 & HIN & HP16 & N1).
      pose proof (DXP EO) as DXP'. pose proof (DSP ltac:(rewrite EO; discriminate)) as DSP'.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      calloc_call k.
      all: match goal with |- forall _ _, _ -> aevtS _ _ _ => idtac | |- ?g => idtac "CALLOC2-LEFT:" g end.
      (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
      ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
      unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by qlia.
      ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
      (* [comment removed for export] *)
      assert (PCH : rw_cells asegs m2 P [CB (4 * length limbs)%nat (u32s limbs)]).
      { eapply (presA_rw_cells asegs R); [exact HP2| exact (PCH1 EO)| | cbn; clear; tauto].
        simpl_sizes. eapply client_range_block; [apply in_app_iff; left; exact HIN| clear; lia| clear - LL; lia]. }
      presA_transport HP2.
      assert (HPX2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
      { eapply presA_trans; [exact HP1|].
        eapply presA_weaken; [exact HP2| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]. }
      clear HP2.
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OX1) as OX2.
      assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
      pose proof (hcs_ok asegs R HIA h2) as CSOK2. pose proof (cs_ok_sb _ _ CSOK2) as SB64'. pose proof (hcs_stack asegs R HIA h2) as SCS2.
      (* [comment removed for export] *)
      zstep. zstep.
      destruct CASES as [[E0 HH2] | (A & E0 & A16 & HFRA & HAS & HH2 & HNEW)]; match type of E0 with ?v = _ => subst v end.
      - (* [comment removed for export] *)
        pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP2.
        assert (MA2 : mpd_at asegs m2 LB dX).
        { eapply mpd_at_rebuild; [exact HNS| unfold mpi_cells; exact HXS1| exact ALX| exact X0| exact LL| unfold MPI_MAX_LIMBS; clear - NR; lia| exact SG| exact PNULL|].
          intros _. split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
          eapply (u32arr_of_cells asegs); [exact PCH| reflexivity]. }
        zstep.
        epi_return h2 LB MBEDTLS_ERR_MPI_ALLOC_FAILED FR1 LAWS2 KINV2.
        eapply post_keep; post_side.
        all: match goal with |- ?g => idtac "SFAIL-LEFT:" g end.
      - (* [comment removed for export] *)
        replace (k * 4) with (4 * k) in HFRA, HAS, HH2, HNEW by (clear; lia).
        pose proof (hm_top asegs R HIA h2 _ LF m2 HH2) as HTOP2.
        assert (SCS2' : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS2| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
        dpose HFRA as (A0 & AC & AD & HAP).
        pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * k) :: LB) LF m2 A (4 * k) HH2 (or_introl eq_refl)) as OA.
        assert (HINA : In (A, 4 * k) (((A, 4 * k) :: LB) ++ fdata LF)) by (left; reflexivity).
        assert (XA : X + 16 <= A \/ A + 4 * k <= X).
        { destruct (fresh_apart_client R LB LF (bv_unsigned sp) X 16 A (4 * k) HFRA); [| clear; lia| clear - Hk; lia| clear - ALO LOS SLO NEEDR; lia| right; assumption| left; assumption].
          eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]. }
        assert (AS : A + 4 * k <= lo) by (clear - AC ALO LOS; lia).
        pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * k) :: LB) LF m2 P (4 * n) HH2 (or_intror HIN)) as OP.
        assert (PA : A + 4 * k <= P \/ P + 4 * n <= A) by (apply HAP; apply in_app_iff; left; exact HIN).
        assert (HINP : In (P, 4 * n) (((A, 4 * k) :: LB) ++ fdata LF)) by (right; apply in_app_iff; left; exact HIN).
        (* [comment removed for export] *)
        zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - A0 AC H; lia); clear - KZ A0; lia|]. clear KZ.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. if_cases KP; zify_cond KP; [exfalso; rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - B0 PC H; lia); clear - KP B0; lia|].
        (* [comment removed for export] *)
        zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
        zstep. zstep.
        (* [comment removed for export] *)
        pose proof (proj1 (u32arr_of_cells asegs m2 P _ _ limbs PCH eq_refl)) as PBA.
        pose proof (u32arr_of_cells asegs m2 P _ _ limbs PCH eq_refl) as PU. rewrite <- (firstn_skipn (Z.to_nat k) limbs) in PU.
        apply u32arr_app in PU. destruct PU as [PUk _]. apply u32arr_ro in PUk.
        assert (LK : length (firstn (Z.to_nat k) limbs) = Z.to_nat k) by (apply firstn_length_le; clear - Hk LL; lia).
        apply (u8arr_of_rw_cells asegs) in HNEW.
        pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + k * 4); (X, X + 16)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2'.
        pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_SH) as SPC. unfold A_ASAN_MEMCPY_SH in SPC.
        acallxA_sp (bv_unsigned sp + -80)
          (eapply SPC with (h := h2) (LB := (A, 4 * k) :: LB) (LF := LF) (DST := A) (SRC := P) (n := k * 4) (lo := lo)
                            (ds := repeat (Z_to_bv 8 0) (Z.to_nat (4 * k))) (ss := u32s (firstn (Z.to_nat k) limbs));
           rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia;
           try eassumption; try reflexivity;
           first [ left; rewrite AMC; reflexivity
                 | rewrite repeat_length; clear - Hk; lia
                 | rewrite u32s_length, LK; clear - Hk; lia
                 | eapply aobj_sub; [exact OA| clear; lia| clear - Hk; lia]
                 | eapply aobj_sub; [exact OP| clear; lia| clear - Hk; lia]
                 | right; clear - PA Hk N1; lia
                 | left; clear - AS PC ALO LOS Hk N1; lia
                 | right; pose proof (alloc_ceiling_val R) as ACV; clear - AC PC Hk N1 ACV; lia
                 | eapply crange_sub; [exact SCS2| clear - LOS; lia| clear - TOP2 HTOP2; lia]
                 | eapply client_wrange_block; [exact HINA| clear; lia| clear - Hk; lia]
                 | clear - NR NB10 Hk LOS SLO NEEDR NRA TOP2 SPA SPR; lia
                 | match goal with |- ?g => idtac "MEMCPY2-PRE-LEFT:" g end ]).
        clear SPC.
        all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY2-SIDE:" g end.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        match goal with H : u8arr asegs m3 A (u32s _) |- _ => rename H into HPA end.
        match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
        match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
        match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        shadow_chk OX2 (X + 10) 2.
        zstep.
        replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
        zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
        zstep.
        replace (4 * length limbs)%nat with (Z.to_nat (n * 4)) in PCH by (clear - LL; lia).
        assert (CW4 : client_wrange L (((A, 4 * k) :: lb_remove P LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
        { eapply client_wrange_mono; [exact CWk|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff.
          destruct Hb as [Hb|Hb]; [left; right; eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb] | right; exact Hb]. }
        free_limbs_call h2 ((A, 4 * k) :: LB) HIN PCH.
        all: match goal with |- forall _ _, _ -> aevtS _ _ _ => idtac | |- ?g => idtac "ZF2-LEFT:" g end.
        (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
        destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
        rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by qlia.
        ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
          replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
        match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
        rewrite (lb_remove_cons_other A (4 * k) P LB) in HP4, HH4 by (clear - PA Hk N1; lia).
        assert (HP4' : presA asegs R ((A, 4 * k) :: lb_remove P LB) LF (bv_unsigned sp + -80) (arl_stklo R) (hstkhi asegs R HIA h2) [] m3 m4).
        { eapply (presA_drop_freed asegs R HIA h2 ((A, 4 * k) :: LB) LF _ [] P (4 * n) m3 m3 m4);
            [exact HH3| right; exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia
            | replace (P + 4 * n) with (P + n * 4) by (clear; lia); exact HP4].
          intros b xb [Hb|Hb] Hr.
          - subst b. split; [left; reflexivity|]. intros E. injection E as E1 E2. clear - E1 PA Hk N1. lia.
          - split; [right; eapply In_lb_remove; exact Hb|]. intros E. subst b. exact (lb_remove_notin LB P (4 * n) ND Hb). }
        clear HP4 PCH PBA OP HINP HINA.
        apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length, LK in HPA.
        presA_transport HP4'.
        apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
        pose proof (AIh_laws asegs R HIA h4) as LAWS4. pose proof (KF_kinv asegs R HIA h4 mo) as KINV4.
        pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS4 OX2) as OX4.
        assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
        (* [comment removed for export] *)
        eapply (aevtA_cut_evtA asegs AL _ LAWS4 _ _ _ _ _ _ KINV4);
          [ eapply fin_walk with (hc := h4) (LBc := (A, 4 * k) :: lb_remove P LB); try eassumption; try reflexivity
          | intros y Hy; exact Hy | ].
        all: try (rewrite HT4; exact HT2).
        all: try (unfold mpi_cells; exact HXS1).
        all: try (clear - A0 AC ALO LOS SLO SPR NEEDR NB Hk NR; lia).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "SFIN-PRE-LEFT:" g end.
        intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & ST9 & HH9). subst ms'.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        apply aevtA_done. intros mo9 [HK9 MF9].
        (* [comment removed for export] *)
        assert (HA9 : u32arr asegs m9 A (firstn (Z.to_nat k) limbs)).
        { eapply (u32arr_of_cells asegs); [| reflexivity].
          eapply (rw_cells_transport asegs _ m4 m9); [exact HPA| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - XA AS Hk NR LL LK; lia]. }
        (* [comment removed for export] *)
        assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
        { eapply presA_trans; [exact HPX2|]. eapply presA_trans; [| eapply presA_trans].
          - (* [comment removed for export] *)
            eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                      (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16)]);
              [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
            eapply (presA_drop_fresh asegs R HIA h LB LF [(X, X + 16)] A (k * 4) m2 m3 (bv_unsigned sp));
              [| eapply fresh_apart_sub; [exact HFRA| clear - Hk; lia] | clear - ALO LOS SLO NEEDR; lia].
            eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) _ m2 m3); [exact HH1| | clear; lia| exact LOS].
            eapply (presA_of_munch asegs R LB LF _ _ _ _ m2 m3 (hcs asegs R HIA h2) CSOK2); [| | exact MU2 | exact WM2'].
            + unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS2'|].
              apply Forall_cons; [cbn [fst snd]; replace (A + k * 4 - A) with (k * 4) by lia; eapply aobj_crange; eapply aobj_sub; [exact OA| clear; lia| clear - Hk; lia]|].
              apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX2|]. apply Forall_nil.
            + intros c0 Hc. eapply cshd_hcs; [exact HH3| | rewrite HS2; eapply cshd_mono_lb; [exact Hc| intros b Hb; right; exact Hb]]. clear; lia.
          - (* [comment removed for export] *)
            eapply presA_weaken; [exact HP4'| | intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HS2; clear; lia| intros y _; exact I].
            intros b Hb. right. eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb].
          - (* [comment removed for export] *)
            rewrite <- HS2, <- HS4.
            eapply (presA_tail asegs R HIA h4 ((A, 4 * k) :: lb_remove P LB)); [exact HH4| | exact LOS| exact TOP4| exact OX4| exact MU| exact WM].
            intros b Hb. right. eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb]. }
        eapply (post_new k A (firstn (Z.to_nat k) limbs) (lb_remove P LB) mo _ h4); try post_side.
        all: try (clear - Hk NR NB10 HNB K1; lia).
        all: try (rewrite LK; clear - Hk; lia).
        all: try (apply limbs_val_firstn; [clear - Hk; lia| exact ZXk]).
        all: try (intros b Hb; eapply In_lb_remove; exact Hb).
        all: try (intros [Bb kb] Hb Hn; apply In_lb_remove_keep; [exact Hb|]; apply (nodup_fst_neq LB P (4 * n) Bb kb ND HIN Hb); intros E; apply Hn; cbn [mpd_blk md_own md_p md_n]; rewrite EO; left; symmetry; exact E).
        all: try (cbn [mpd_blk md_own md_p md_n]; rewrite EO; intros b [<-|[]]; first [exact (lb_remove_notin LB P (4 * n) ND) | exact HIN]).
        all: match goal with |- ?g => idtac "SFIN-LEFT:" g end.
      all: match goal with |- ?g => idtac "SHRINK24-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L14814410920.7  L15450681962.3  L27151043260.5  L27750330872.1  L29428324939.5  L35653441506.7  L60098763854.3  L66259998979.11600000@00H00U00Y00k01C01M02LS1n2nb1i2Hi2K11KS2nb1i1KS1n2nb1i2Hi1KS2nbS1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS1R2lo3LOSS1R5NEEDR2sp1X1n1P5limbs2nb2lo3LOS3SLO2X02P02PC1i2Hi2K13ALO3SPR". (* [comment removed for export] *)
    #[using="C24T IMG ZF CALLOC AMC NEEDR DIMG HNS NB XW DSP LOS SLO TOP SPA TPV XUW jk1 HH1 HXS1 PCH1 OX1 FR1 ST1 MI1 HP1 ALX X0 LL NR SG P0 PC PHEAP PNULL CW DXP DSX ND NB10 BUD BUDF"] Lemma shrink_path : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shrink ()) "Pi,$1.Pxra,(>.&40.)Pxt0,(>.&40.)Pxt1,(>.&40.)Pxt2,(>.&40.)Pxa0,(>.&40.)Pxa1,(>.&40.)Pxa2,(>.&40.)Pxa3,(>.&40.)Pxa4,(>.&40.)Pxa5,(>.&40.)Pxa6,(>.&40.)Pxa7,(>.&40.)Pxs3,(>.&40.)Pxt3,(>.&40.)Pxt4,(>.&40.)Pxt5,(>.&40.)Pxt6,(>.&40.)P,(21.$5<.Vown,$5=.)P,(2.(3.+1.R13.)(3.R13.Vn,))P,(4.Vnb,Vn,)P,(54.Vlimbs,R15.)(5:.$=.(5;.$=.VR,VHIA,Vh,Vmo,)(45.$=.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$:.(;.Vnb,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(40.(41.Vnb,Vn,))(7.Vd,)Vlo,Vm,Vmo,)(22.(23.R15.(24.&40.(14.(11.&40.Vsp,)-50.))Vgp,Vtp,R14.R13.R12.(24.&40.VX,)(24.&40.(14.VX,+:.))R11.R10.R?.R>.R=.R<.R;.R:.(24.&40.Vnb,)R9.(24.&40.R16.)(24.&40.(34.(1=.VR,)))(24.&40.(14.(35.(14.VX,+:.)+3.)(34.(1=.VR,))))(24.&40.(14.(35.VX,+3.)(34.(1=.VR,))))Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(24.&40.+9;<;<.)Vfc,(26.(>.&40.))Vm1,(27.$=.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros EO Hi K1 ZX. basic_facts h LB m1 HH1 TOP.
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      (* [comment removed for export] *)
      zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (clear - Hi NR NB; lia).
      - eapply (shrink_from24 i); [exact EO| exact Hi| clear - K; lia| exact K1| exact ZX].
      - (* [comment removed for export] *)
        zstep. eapply (shrink_from24 nb); [exact EO| clear - K Hi K1 NB; lia| clear; lia| exact K1| eapply zeros_above_mono; [| exact ZX]; clear - K Hi; lia].
      all: match goal with |- ?g => idtac "SHRINK-PATH-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Paths.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0260@D3399625391.116 D3399625391.117 D35881667587.116D35881667587.117K42587433812.116K42587433812.117L1157912586.114 L15302269400.112L1685717371.0   L1954497222.2   L19946008845.114L20737611832.1  L22331872950.5  L22446743512.112L25214214772.112L2530059704.6   L26892418956.1  L29428324939.5  L30068506963.137L31225147636.112L33087634096.2  L33759267971.3  L33765440805.2  L33769912227.7  L33771834502.6  L34705680216.112L35653441506.7  L37246946676.111L38727422828.5  L38948636245.0  L39172636981.0  L39280637297.0  L3949578456.111 L40281191306.3  L40374333670.112L40834179097.118L41274399090.6  L41276385489.1  L41286998391.2  L41843875160.112L4235686485.134 L4235686485.137 L42594106808.2  L43061363337.110L44822654374.5  L45370769414.3  L45375012867.6  L45376961318.7  L45381006760.1  L46122776823.12 L46160478526.114L46160487540.117L49283344500.112L51454941784.112L5255850739.125 L53465339911.5  L54039885912.7  L54041871229.6  L54043702998.1  L54054437752.3  L54976800961.5  L55310518004.112L5699067096.112 L57818804596.112L58591023192.112L59308668813.5  L60098763854.3  L60447862057.2  L61321319284.112L61929718192.2  L61929812241.117L61929812368.118L61933949395.125L62018535662.1  L62620801324.47 L62623048204.49 L62624422185.46 L62624979241.49 L63829069812.112L64194470200.2  L67280348888.112L67351568884.112L774765788.5    Q15643324129.112Q17530203490.115Q17530203490.116Q18365925601.113Q18694146040.119Q21798041355.119Q21879645826.113Q25157988860.119Q25513505925.115Q25513505925.116Q25662358575.119Q26207421841.118Q26207721832.119Q26207774677.116Q27584944865.113Q27907200258.113Q30415036802.113Q31228709292.119Q31271525473.113Q31394594844.119Q31654082872.118Q32655500769.113Q33918256002.113Q35014437530.119Q35717497884.119Q36425882626.113Q3830427394.113 Q39212284437.119Q39939554818.113Q41152393185.113Q4143427880.119 Q43925228937.119Q44648843873.113Q49698585326.114Q49698585326.115Q51235796833.113Q5300226131.113 Q5300226131.114 Q53969758199.119Q59843137889.113Q60511567613.119Q60697995187.119Q61802139820.119Q6416456232.119 Q64255486968.119Q66522067074.113Q67528989526.116Q67528989526.117Q8880817289.116 Q9538463866.116 Q9843367298.112 00001002E03704>05<06O06c07707807>07U07X07Y07m08A08B08F08X09209F09L09M09N09a09b0:60:N0:b0:o0;00;10;20;F0;O0;c0<90<:0<;0<C0<W0==0=f0=g0>Q0>]0>^0>_0>e0>f0?G0?^0@50@I0@]0A90A?0AE0AF0AG0AH0AT0Ah0B<0BP0Bd0C30C=0CC0CW0C]0D40DK0Dg0Dj0Dk0Dl0Dm0Dn0EB0EI0E]0F10FD0F[0GP0HZ0I10II0IJ0Im0JE0Jn0Kl0Km0L>0LO0L`0M70MZ0N=0NV0Nm0O>0OO0Of0PI0Pb0Pc0QF0Qi0R:0R]0S40S50SF0S]0T>0T_0U60UM0Ud0V=0VT0Ve0W90W:0WR0WS0X60Xk0Z50ZF0ZW0[:S1R5NEEDR2ra2sp1X1n5limbs2nb2lo3LOS3SLO2X03SPR2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X1n5limbs2nb2lo3LOS3SLO2X03SPR2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1R3HIA1h2ra2sp1X1n5limbs2nb3TOP2XB2HB5Ha_st5Hl_stS1R3HIA1h2sp2s01X1n5limbs2nb3TOP2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1R5NEEDR2ra2sp1X1n1P5limbs2nb2lo3SLO2XB2P03DSX2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X1n1P5limbs2nb2lo3SLO2XB2P03DSX2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp1X1n5limbs2nb2XBS2sp1X1n5limbs2nb2XBSS1P2B0S2sp1X1n5limbs2nb2lo2XBS1nFS2sp1X1n5limbs2nb2XBS2sp1X1n5limbs2nb2XBFS2spS1R2lo3LOS3ALO3ACPS2sp1X1n5limbs2nb2XB2K12K2S2sp1X1n5limbs2nb2XBS1n2NRFFS1R1X1n1P2XB2PC3ACVFS2sp1X1n5limbs2nb2XBS1R3HIA1h2sp2lo3TOP4HTOPS2sp1X1n5limbs2nb2XBS1R3HIA1h1d1HSSSS2sp1X1n5limbs2nb2XBS1R3HIA1hS2sp1X1n5limbs2nb2XBS1R2sp1X1n5limbs2nb2XBFFS1P4HP16S2sp1X1n5limbs2nb2XBS1R3HIA1h2sp1X1n5limbs2nb2X03SPR2XB2K0S1R3HIA1h2sp1X1n5limbs2nb2NB2X03SPR2XB2K1FS1R5NEEDR2sp1X1n5limbs2nb2lo3SLO2X03SPR2XBS1n2nb2NB2K1FFS1X2XBFS1R2sp1n1P5limbs2lo3LOS2LL3ALO2PCS2sp1X1n5limbs2nb2X02XBS2sp1X1n5limbs2nb2X02XBS2sp1X1n5limbs2nb2XBS2sp1X1n5limbs2nb2XBS2sp1X1n1P5limbs2nb2X02XB2P0S1n2NRS1X2XBFFFS1n2nb2NB2K1S2sp1X1n5limbs2nb2XBS2sp1X1n5limbs2nb2XBS2sp1X1n5limbs2nb2XBS2sp1X1n5limbs2nb2XBS1n2nb2NB2K12EnS1R2lo3LOSS1n2NRS2sp1X1n5limbs2nb2XBS1n2NRS2sp1X1n5limbs2nb2NR2XBS2sp1X1n5limbs2nb2NR2XBS2sp1X1n1P5limbs2nb2NR2XB2P0S1RFFFFS2sp1X1n5limbs2nb2XBS1R3ACPS2sp1X1n5limbs2nb2XBS2sp1X1n5limbs2nb2XBS1R5NEEDR2sp2lo3SLOS2sp1X1n5limbs2nb2lo2XBS1R5NEEDR2ra2sp1X1n5limbs2nb2lo3SLO2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X1n5limbs2nb2lo3SLO2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp1X1n5limbs2nb2lo2XBS1R1X1n5limbs2nb4IMG'2XBFS1R5NEEDR2sp1X1n5limbs2nb2lo3SLO2XBS1R1X1n5limbs2nb4IMG'2XBS2ra2sp1X1n5limbs2nb2lo2XB2HB5Ha_st5Hl_stS2sp2s01X1n5limbs2nb2lo2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7FS1X1n5limbs2nb2XBS1X1n5limbs2nb2XBS1X1n5limbs2nb2XBS2sp1X1n5limbs2nb2lo2XBS1R5NEEDR2sp1X1n5limbs2nb2lo3SLO2XBS1R5NEEDR2sp1X1n5limbs2nb2lo3SLO2XBS1R1X1n5limbs2nb5ALWF'2XBS2sp1X1n5limbs2nb2lo2XBS1X1n5limbs2nb2XBS1X1n5limbs2nb2XBS2sp1X1n5limbs2nb2lo2XBS1R5NEEDR2sp1X1n5limbs2nb2lo3SLO2XBS1R1X1n5limbs2nb5ALWF'2XBFS1R5NEEDR2sp1X1n5limbs2nb2lo3SLO2XBS1R5NEEDR2sp1X1n5limbs2nb2lo3SLO2XBS1X1n5limbs2nb2XBS1R5NEEDR2sp1X1n5limbs2nb2lo3SLO2XBS2sp1X1n5limbs2nb2lo2XBFS1X1n5limbs2nb2XBS2sp1X1n5limbs2nb2lo2XBS2sp1X1n5limbs2nb3SPR2XB2HB5Ha_stS2sp1X1n5limbs2nb3SPR2XB2HB5Ha_stS2sp1X1n5limbs2nb2lo2XBS2sp1X1n5limbs2nb2XB2HBS2sp1X1n5limbs2nb2XB2HBS1R1X1n5limbs2nb5ALWF'2XBS2sp1X1n5limbs2nb2lo2XBS1X1n5limbs2nb2XBS1X1n5limbs2nb2X02XBFS1R1X1n5limbs2nb4IMG'2XBFS1R5NEEDR2sp1X1n5limbs2nb2lo3SLO2XBS1R5NEEDR2ra2sp1X1n5limbs2nb2lo3SLO2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X1n5limbs2nb2lo3SLO2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1X1n5limbs2nb2XBS1X1n5limbs2nb2XBS1R5NEEDR2sp1X1n5limbs2nb2lo3SLO2XB". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC NEEDR HND DIMG HNS NB XW DSP LOS SLO TOP SPA TPV XUW"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_shrink ()) "Pmo,$36.Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)P,(10.$=.VR,VHIA,Vh,VLB,VLF,Vm,)P,(3>.$=.VR,VHIA,Vh,R?.)P,(43.$=.Vm,VLB,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))P,(1:.$=.Vm,Vlo,(11.&40.Vsp,))P,(1;.$=.Vm,)P,(2?.$=.(1=.VR,)(1>.$=.VR,VHIA,Vh,)Vm,VX,+10.)P,(3.(14.(3?.$=.VR,VHIA,Vh,)(40.(41.Vnb,Vn,)))$5>.)P,(3.(14.(42.$=.VR,VHIA,Vh,)(7.Vd,))$5?.)(60.$=.(45.$=.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$:.(;.Vnb,(3:.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)(40.(41.Vnb,Vn,))(7.Vd,)Vlo,Vm,R16.)(46.(22.(23.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,(24.&40.VX,)(24.&40.Vnb,)R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(24.&40.$61.)Vfc,(26.(>.&40.))Vm,(27.$=.))R16.))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HKmo MX ST MI OX BUD BUDF. unfold A_MPI_SHRINK. basic_facts h LB m HH TOP.
    pose proof (HND _ _ _ _ HH) as ND. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0.
    destruct MX as [(HXS & ALX & X0 & LL & NR & HOWN) SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HXS, ALX, X0, LL, NR, HOWN, SG.
    destruct XW as [CW DXP]. cbn [md_addr md_own md_p md_n] in CW, DXP.
    pose proof (rw_cells_bound _ _ _ _ HXS) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HF BA]. rewrite Forall_forall in HF.
    unfold MPI_MAX_LIMBS in NR.
    (* [comment removed for export] *)
    assert (PB : 0 <= P /\ P + 4 * n <= alloc_ceiling
                 /\ (own = LHeap -> 0 < P /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ u32arr asegs m P limbs /\ 1 <= n)
                 /\ (own = LNull -> P = 0 /\ n = 0)).
    { destruct own; [| | exfalso; exact (HNS eq_refl)].
      - destruct HOWN as [E0 En]. split; [rewrite E0; clear; lia|]. split; [rewrite E0, En; clear - ACP; lia|].
        split; [intros E; discriminate E| intros _; split; [exact E0| exact En]].
      - ddestruct HOWN as (N1 & HIN & HP16 & HXL). destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
        split; [clear - B0; lia|]. split; [exact BC|].
        split; [intros _; split; [exact B0| split; [exact HIN| split; [exact HP16| split; [exact HXL| exact N1]]]]| intros E; discriminate E]. }
    ddestruct PB as (P0 & PC & PHEAP & PNULL). clear HOWN.
    assert (DSX : X + 16 <= lo \/ bv_unsigned sp <= X).
    { eapply (client_wrange_where_A asegs R HIA h LB LF m); [exact HH| intros b Hb; exact Hb| exact CW| clear; lia| exact LOS| clear - SLO NEEDR; lia]. }
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    unfold mpi_cells in HXS.
    carve_frame 80%nat ST.
    (* [comment removed for export] *)
    do 10 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch type of FR with rw_cells _ _ _ ?cs => set (FRC := cs) in FR end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    assert (HP1 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m1).
    { eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16)]);
        [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
      eapply (presA_drop_below asegs R HIA h LB LF [(X, X + 16)] lo (bv_unsigned sp) _ m m1); [exact HH| | clear; lia| exact LOS].
      eapply (presA_of_munch asegs R LB LF _ _ _ _ m m1 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | | exact WM0].
      - unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX|]. apply Forall_nil.
      - eapply munch_weaken; [| exact MU0]. clear. intros y Hy; clear - Hy; cbn [outside] in *. tauto (* [comment removed for export] *). }
    assert (PCH1 : own = LHeap -> rw_cells asegs m1 P [CB (4 * length limbs)%nat (u32s limbs)]).
    { intros E. ddestruct (PHEAP E) as (B0 & _ & _ & HXL & _). apply u32arr_cells.
      eapply (u32arr_transport asegs _ m m1); [exact HXL| exact MU0| exact WM0| cbn [disjoint_from]; clear - PC ALO LOS SLO NEEDR LL; lia]. }
    assert (MA1 : mpd_at asegs m1 LB dX).
    { eapply mpd_at_rebuild; [exact HNS| unfold mpi_cells; exact HXS| exact ALX| exact X0| exact LL| unfold MPI_MAX_LIMBS; clear - NR; lia| exact SG| exact PNULL|].
      intros E. ddestruct (PHEAP E) as (B0 & HIN & HP16 & HXL & N1). split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
      eapply (u32arr_of_cells asegs); [exact (PCH1 E)| reflexivity]. }
    assert (PHEAP' : own = LHeap -> 0 < P /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ 1 <= n)
      by (intros E; ddestruct (PHEAP E) as (B0 & HIN & HP16 & _ & N1); split; [exact B0| split; [exact HIN| split; [exact HP16| exact N1]]]).
    clear MU0 WM0.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      subst FRC. epi_return h LB MBEDTLS_ERR_MPI_ALLOC_FAILED FR LAWS KINV.
      eapply post_keep; post_side.
      all: match goal with |- ?g => idtac "E1-LEFT:" g end. }
    rewrite ?unsigned_lit in K0 by (clear - NB; lia).
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB AB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - NB NR; lia).
    { (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - NB NR; lia).
      { (* [comment removed for export] *)
        zstep.
        subst FRC. epi_return h LB 0 FR LAWS KINV.
        eapply post_keep; post_side.
        all: try (right; split; [reflexivity| clear - K1 K2; lia]).
        all: match goal with |- ?g => idtac "E2-LEFT:" g end. }
      subst FRC. eapply grow_path; try eassumption. all: try (clear - K0 K1 K2; lia).
      all: match goal with |- ?g => idtac "GP-LEFT:" g end. }
    (* [comment removed for export] *)
    assert (EO : own = LHeap).
    { destruct own; [| reflexivity| exfalso; exact (HNS eq_refl)]. exfalso. destruct (PNULL eq_refl) as [_ En]. clear - En K1 NB. lia. }
    ddestruct (PHEAP EO) as (B0 & HIN & HP16 & _ & N1).
    pose proof (hm_aobj_block asegs R HIA h LB LF m1 P (4 * n) ltac:(eassumption) HIN) as OP.
    pose proof (PCH1 EO) as PCHm1.
    pose proof (u32arr_ro _ _ _ _ (u32arr_of_cells asegs m1 P _ _ limbs PCHm1 eq_refl)) as HXro.
    (* [comment removed for export] *)
    zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    zstep. zstep. zstep.
    eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
      [ eapply (scan_walk (Z.to_nat n) n m1); try eassumption; try reflexivity
      | intros y Hy; exact Hy | ].
    all: try (clear - K1 NB NR; lia).
    all: try (apply zeros_above_all; exact LL).
    all: try (f_equal; clear; lia).
    all: try (clear - HP16; lia).           (* [comment removed for export] *)
    all: try (pose proof (alloc_ceiling_val R) as ACV; clear - PC ACV XB; lia).
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "SCAN-PRE-LEFT:" g end.
    intros ms' PO. ddestruct PO as (i & xa0' & xa1' & xa2' & xa3' & xa4' & E & Hi & Zi). subst ms'.
    subst FRC. eapply shrink_path; try eassumption. all: try (clear - K0 K1 Hi; lia).
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.


(* [comment removed for export] *)
