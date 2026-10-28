(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_mpi_cmp P_mpi_mul_stmt P_mpi_divmod_stmt P_ecp_group_free P_ecp_red P_ecp_mul_mod.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_opnd A_mpi_journey A_mpi_journey2 A_mpi_copy A_mpi_core_add_if A_mpi_core_sub A_mpi_cmp_mpi A_mpi_cmp_int A_mpi_bitlen A_ecp_red_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_ecp_mul_mod () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_h"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_mul_mod_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.mm_PHIn"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.mm_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.mm_nz"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "MM.MMFIN"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "MM.MM_POST"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "MM.MM_FRAME"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "MM.MMS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.JBA"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.binop_keep"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mul_mpi_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mul_mpi_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mul_mpi_nz"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.w_client"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_modp"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_opnd.opnd_atA"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.BJA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "A_MPI_MUL_MOD_E"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_mul_mpi_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_MUL_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_mod_mpi_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_MOD_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.modp_table_okA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_mul_mod_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_MUL_MOD"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_MUL_COUNT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_int.A_UAR_GOT_CI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_int.A_SMALLOC_0_CI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"].


Definition A_MPI_MUL_MOD_E : Z := 0xcef9c.   (* [comment removed for export] *)
Definition mm_frame64 (ra s0 s1 s2 s3 s4 s5 : word) (fj : list byte) : list cell := [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59308585345.1400000BS1d1A1k2AP1x2Hx2Hr". (* [comment removed for export] *)
Lemma client_range_keepA : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "PLx,$0.PLB,(1.$2.)PLF,(1.$2.)PSP,$3.Pd,$4.PA,$3.Pk,$3.P,(5.R7.(6.$2.R6.(7.R5.))R4.R2.R1.)P,P,(8.$9.(:.R4.)$;.)(<.(=.(>.R4.R3.)(?.R5.))(=.(>.(?.R5.)(10.+4.(11.R5.)))R4.))(5.R9.(6.$2.(12.R8.R5.)(7.R7.))R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros Lx LB LF SP d A k CR AP x Hx. destruct (CR x Hx) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right].
  exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
  apply In_mpd_keep_intro; [exact Hb|]. unfold mpd_blk. destruct (md_own d) eqn:EO; [intros []| | intros []].
  intros [E|[]]. subst b. cbn in Hr. specialize (AP eq_refl). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ecp_group_at_LB_any : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Psegs,(1.$13.)PMT,(1.$14.)Pm,P,(15.&40.)(16.(15.&8.))PLB,(1.$2.)PLB',(1.$2.)PG,$3.Pg,$17.P,(18.R7.R6.R5.R4.R2.R1.)P,(8.$3.(19.R2.)+1.)(18.R9.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros segs MT m LB LB' G g HG H1.
  assert (NH : forall e, In e (grp_mpds g) -> md_own e <> LHeap) by (intros e He; eapply (grp_static_own segs); eassumption).
  ddestruct HG as (HD & AL & POS & EP & EA & EB & EN & MP & MA & MB & (EX & EY & EZ & MX & MY & MZ) & MN & REST).
  pose proof (fun e He Hm => mpdr_at_LB_any segs m LB LB' e Hm (NH e He)) as RB.
  unfold grp_mpds, pt_mpds in RB. cbn [app In] in RB.
  refine (conj HD (conj AL (conj POS (conj EP (conj EA (conj EB (conj EN _))))))).
  split; [apply RB; [tauto| exact MP]|]. split; [apply RB; [tauto| exact MA]|]. split; [apply RB; [tauto| exact MB]|].
  split; [refine (conj EX (conj EY (conj EZ _))); split; [apply RB; [tauto| exact MX]| split; [apply RB; [tauto| exact MY]| apply RB; [tauto| exact MZ]]]|].
  split; [apply RB; [tauto| exact MN]| exact REST].
Qed.

Section MM.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Variable MT : list modp_ent.
  Hypothesis HMUL : mpi_mul_mpi_stmtA_sz asegs R HIA A_MPI_MUL_MPI.
  Hypothesis HMOD : mpi_mod_mpi_stmtA_sz asegs R HIA A_MPI_MOD_MPI.
  Hypothesis HTAB : modp_table_okA asegs R HIA MT.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (G : Z) (g : ecp_grp) (MC lo d : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Variable fj : list byte.
  Definition MM_FRAME := mm_frame64 ra s0 s1 s2 s3 s4 s5 fj.
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 64 MM_FRAME.
  Hypothesis FJ : rw_cells asegs m (bv_unsigned sp - 64) [CB 8 fj].
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis GRP : ecp_grp_preA asegs R HIA MT h LB LF m G g MC lo (bv_unsigned sp) d.
  Hypothesis OSEP : ecp_out_sepA dX G MC.
  Hypothesis MCOK : mc_okA R MC.
  Hypothesis MIm : mem_inv asegs m.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 1040 - arl_need_ecp R.
  Local Notation PHI0 := (mm_PHIn nX (md_n dA) (md_n dB) (md_n (g_P g))).
  Local Notation SZ0 := (mm_nz nX (md_n dA) (md_n dB) (md_n (g_P g))).
  Local Notation FR0 := (mm_FRn nX (md_n dA) (md_n dB) (md_n (g_P g)) d).
  Variable slo : Z.
  Hypothesis SSH : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis SLO1 : arl_stklo R <= slo.
  Hypothesis SLO3 : slo <= lo.

  Definition MM_POST := ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "(1:.$1;.VR,VHIA,VMT,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VG,Vg,VMC,(1=.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,)))(1?.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))Vd,)(20.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,)))Vlo,Vm,Vmo,)")
(* [comment removed for export] *).
  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -64)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 64 MM_FRAME []).
  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (arl_need_ecp_rt R) as NER; pose proof (arl_need_ecp_smalloc R) as NES;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Record MMFIN (hF : HST asegs R HIA) (LBF : list blk) (mF : mem) (dXF : mpd) (cntF : word) : Prop := {
    mf_mi : mem_inv asegs mF;
    mf_stk : stk asegs mF lo (bv_unsigned sp - 64);
    mf_fr : rw_cells asegs mF (bv_unsigned sp - 64) MM_FRAME;
    mf_pres : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16); (MC, MC + 8)] m mF;
    mf_top : htop asegs R HIA hF = htop asegs R HIA h;
    mf_stkhi : hstkhi asegs R HIA hF = hstkhi asegs R HIA h;
    mf_flag : hflag asegs R HIA hF = hflag asegs R HIA h;
    mf_hcs : forall x, hcs asegs R HIA h x -> hcs asegs R HIA hF x;
    mf_vol : havol asegs R HIA hF <= havol asegs R HIA h + PHI0;
    mf_frs : hfr asegs R HIA hF <= hfr asegs R HIA h + FR0;
    mf_hm : HM asegs R HIA hF LBF LF mF;
    mf_X : mpd_at asegs mF LBF dXF;
    mf_out : mpd_out LB dX LBF dXF;
    mf_fresh : forall b, In b (mpd_blk dXF) -> In b (mpd_blk dX) \/ fresh_apart R (mpd_keep LB dX) LF (fst b) (snd b);
    mf_grp : ecp_group_at asegs MT mF LBF G g;
    mf_mc : rw_cells asegs mF MC [C8 cntF];
    mf_keep : binop_keep LB dX dXF;
    mf_sz : md_n dXF <= SZ0 }.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L12283411672.154L14106684376.154L17645738372.1  L20181524131.1  L35663928186.7  L38041015762.4  L40229485618.1  L41288976216.154L44866992728.154L48429268312.154L5145216728.154 L60098763854.3  L67158371251.154L8722184664.154 Q15645341323.154Q18359718027.154Q21890219752.154Q27909213544.154Q31256953867.154Q32657489291.154Q33911823336.154Q36436182120.154Q3836573544.154 Q39937631848.154Q41141761931.154Q44655022603.154Q51221294859.154Q59828537611.154Q66536663272.154Q9837151720.154 00000P01001401801M01Y01]02=02]03=03]03g04G04g05G05g06L07107Q08108V09;09`0:E0:e0;E0;e0<E0<j0=OS2ra2sp1X2sX2nX2pX3xs04padX4ownXS2ra2sp1X2sX2nX2pX3xs04padX4ownXS2spS2spS1R3HIA1h2sp2lo3TOP1HS2sp2lo4LOSPS2spS2ra2sp1X2sX2nX2pX3xs04padX4ownXS2ra2sp1X2sX2nX2pX3xs04padX4ownXS2ra2sp1X2sX2nX2pX3xs04padX4ownXS2ra2sp1X2sX2nX2pX3xs04padX4ownXS1R2lo3LOSS2ra2sp1X2sX2nX2pX3xs04padX4ownXS2ra2sp1X2sX2nX2pX3xs04padX4ownXS2sp1X2sX2nX2pX3xs04padX4ownX2loS2sp1X2sX2nX2pX3xs04padX4ownX2loS2sp1X2sX2nX2pX3xs04padX4ownX2lo4LOSPS2sp1X2sX2nX2pX3xs04padX4ownX2lo4LOSPS2sp1X2sX2nX2pX3xs04padX4ownX2loS2sp1X2sX2nX2pX3xs04padX4ownX2loS2sp1X2sX2nX2pX3xs04padX4ownX2lo4LOSPS2sp1X2sX2nX2pX3xs04padX4ownX2lo4LOSPS2sp1X2sX2nX2pX3xs04padX4ownX2lo4LOSPS2sp1X2sX2nX2pX3xs04padX4ownX2lo4LOSPS2sp1X2sX2nX2pX3xs04padX4ownX2loS2sp1X2sX2nX2pX3xs04padX4ownX2loS2sp1X2sX2nX2pX3xs04padX4ownX2loS2sp1X2sX2nX2pX3xs04padX4ownX2loS2sp1X2sX2nX2pX3xs04padX4ownX2lo4LOSPS2sp1X2sX2nX2pX3xs04padX4ownX2lo4LOSP". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma mm_exit : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "PhF,(21.$1;.VR,VHIA,)PLBF,(1.$2.)PmF,P,(15.&40.)(16.(15.&8.))PdXF,$4.PcntF,(15.&40.)Pr,$3.Pxra,(15.&40.)Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pxs0',(15.&40.)Pxs1,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pxs2,(15.&40.)Pxs3,(15.&40.)Pxs4,(15.&40.)Pxs5,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)P,(22.R1;.R1:.R19.R18.R17.)P,(23.(24.(25.(26.+2.+1?.))R17.)(=.R17.=))(27.$1;.(28.$1;.VR,VHIA,R1=.Vmo,)$29.(2:.(2;.R17.(2<.&40.(>.(2=.&40.Vsp,)-40.))Vgp,Vtp,R16.R15.R14.R13.R12.(2<.&40.R18.)R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(2<.&40.+<>?>4.)Vfc,(2>.(15.&40.))R1;.(2?.$1;.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros FIN HR. basic_factsA hF.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    destruct FIN as [MI1 ST1 FR1 HP1 HT1 HS1 HF1 HCS1 HV1 HFR1 HH1 MX1 OUT1 FRA1 GR1 MC1 BK1 SZ1].
    pose proof (hm_top asegs R HIA hF LBF LF mF HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hF) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hF) as LAWS. pose proof (KF_kinv asegs R HIA hF mo) as KINV.
    pose proof (stk_release asegs mF lo (bv_unsigned sp - 64) MM_FRAME ST1 FR1 ltac:(clear - LOSP LO0; lia)) as STR.
    unfold MM_FRAME, mm_frame64 in FR1, STR. cbn [cells_size csize Nat.add] in STR. replace (bv_unsigned sp - 64 + Z.of_nat 64) with (bv_unsigned sp) in STR by (clear; lia).
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mF) as MU. pose proof (wmono_refl asegs mF) as WM.
    pose proof (conj MC1 I) as MCbox. pose proof (conj GR1 I) as GRbox. pose proof (conj MX1 I) as MXbox.
    do 7 zstep.
    zstep.
    replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by (clear; lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold MM_POST, ecp_mul_mod_postA.
    destruct MCbox as [MC1' _]. destruct GRbox as [GR1' _]. destruct MXbox as [MX1' _].
    deexists 14. dexists mF, mo9, hF, LBF, dXF, r, cntF.
    split; [reflexivity|]. split; [exact MI1|]. split; [exact STR|]. split; [exact MF9|]. split; [exact HP1|].
    split; [exact HT1|]. split; [exact HS1|]. split; [exact HF1|]. split; [exact HK9|]. split; [exact HCS1|].
    split; [exact HV1|]. split; [exact HFR1|]. split; [exact HH1|]. split; [exact MX1'|]. split; [exact OUT1|]. split; [exact FRA1|].
    split; [exact GR1'|]. split; [exact MC1'|]. split; [split; [exact HR| exact BK1]| exact SZ1].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11347533506.3 L13758199680.11L16273301179.5 L26892418956.1 L30072796923.7 L3368192773.12 L34409126551.6 L40281191306.3 L48111173305.5 L53341971708.3 L59315317366.6 L59582329008.3 L59673527198.3 L60302866585.8 L62018535662.1 L9397345616.5  00000900Y00n01201K01n02A02J02X02b03203<03E03b03e045S2MC1x2HxS1R3HIA1h2nX2dA2dB1g1v2hc2HV3HV1S2sp2MC2lo4LOSP5MCLOWS2spS1R2MC2lo3LOS3ALO3DLO3MC2S1R3HIA1h2nX2dA2dB1g1d1f2hc2HF4HFR1S1R2MC3MC13MC21x2HxS1R3HIA1hS2sp1G2GS1x2HxS1G2MC3GMCS1G2lo2GS1x2Hx1SS1X2MC3OS3S1X1G3OS1S1R2MC3DI13DI23dXc3MC13MC22PIS1RS2sp2MC2lo5MCLOW". (* [comment removed for export] *)
  #[using="IMG JC GRP OSEP MCOK MIm"] Lemma mm_fin : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.PmF,P,(15.&40.)(16.(15.&8.))PcntF,(15.&40.)P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R8.R7.R6.R5.R4.R3.)P,(33.(34.(35.$3.$3.)(36.$3.$3.VMC,(>.VMC,+8.))(32.(35.$3.$3.)))R5.R3.)P,(37.$1;.R6.R4.)P,(38.$1;.R5.)P,(39.$1;.VR,VHIA,R:.R9.VLF,R6.)P,(3:.$1;.R7.VMC,(34.$3;.(3<.R6.)(32.$3;.)))P,(=.R>.(1=.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))))P,(=.R>.(1?.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))Vd,))P,(=.(11.R;.)(20.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))))(22.R?.R>.R;.R<.R:.)")
(* [comment removed for export] *).
  Proof.
    jc_open. intros v f hc LBc mc dXc mF cntF J MU WM MIF HHF MCF HV HF HSZ. basic_factsA hc.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (art_data_lo asegs R HIA) as DLO.
    ddestruct MCOK as (MC1 & MC2 & MC3 & MC4 & MC5 & MC6).
    ddestruct OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    ddestruct GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW).
    assert (MCLOW : MC + 8 <= lo) by (clear - MC2 DLO ALO LOS; lia).
    (* [comment removed for export] *)
    assert (MCL : md_own dXc <> LNull -> disjoint_from [(MC, MC + 8)] (md_p dXc) (4 * md_n dXc)).
    { intros ON. ddestruct (OWN1 ON) as (_ & _ & _ & _ & _ & _ & _ & PI & _). cbn [disjoint_from fst snd]. split; [| exact I].
      destruct DIMG as [DI1 DI2]. clear - PI MC1 MC2 DI1 DI2. lia. }
    assert (HPF : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16); (MC, MC + 8)] m mF).
    { eapply presA_trans.
      + eapply presA_weaken; [exact HPX1| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. first [clear - Hx; cbn [outside fst snd] in *; tauto | cbn [outside fst snd] in *; tauto]. (* [comment removed for export] *)
      + rewrite <- HS1.
        eapply presA_weaken; [| intros b Hb; eapply xa_keep_sub; [exact J| exact Hb]| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl|].
        * eapply (presA_of_munch asegs R LBc LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA hc) [(MC, MC + 8)] mc mF (hcs asegs R HIA hc) CSOK); [| | exact MU| exact WM].
          -- unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros x Hx. apply (hcs_static asegs R HIA hc).
             split; [clear - Hx MC1 MC2; lia| apply MC3; clear - Hx; lia].
          -- intros c0 Hc. eapply cshd_hcs; [exact HH1| apply Z.le_refl| exact Hc].
        * intros x Hx. first [clear - Hx; cbn [outside fst snd] in *; tauto | cbn [outside fst snd] in *; tauto]. (* [comment removed for export] *) }
    constructor; try assumption.
    - eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. cbn [disjoint_from fst snd]. split; [clear - MCLOW LOSP; lia| exact I].
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. rewrite FSZ. cbn [disjoint_from fst snd]. split; [clear - MCLOW LOSP; lia| exact I].
    - clear - HV1 HV. lia.
    - clear - HFR1 HF. lia.
    - eapply mpd_at_munch_any; [exact MX1| exact MU| exact WM| |exact MCL].
      rewrite AD1. cbn [md_addr disjoint_from fst snd]. split; [clear - OS3; lia| exact I].
    - (* [comment removed for export] *)
      pose proof (ecp_group_at_LB_any asegs MT m LB (mpd_keep LB dX ++ fdata LF) G g GAT GH1) as GAT0.
      assert (GCR0 : client_range L (mpd_keep LB dX ++ fdata LF) (bv_unsigned sp) G 192).
      { apply client_range_keepA; [| exact OS2]. intros x Hx. destruct (GCR x Hx) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
        destruct GSP as [GS|GS]; [exfalso; clear - S Hx GS; lia| left; clear - Hx GS; lia]. }
      eapply (ecp_group_at_presx asegs L MT m mF _ LBc (bv_unsigned sp) [(X, X + 16); (MC, MC + 8)] G g GAT0);
        [eapply presA_presx; exact HPF| exact MIm| exact MIF| exact GCR0| |].
      + cbn [disjoint_from fst snd]. split; [clear - OS1; lia| split; [clear - GMC; lia| exact I]].
      + intros e He EO. exfalso. exact (grp_static_own asegs MT m LB G g e GAT GH1 He EO).
    - split; [exact AD1|]. split; [exact PD1|]. split; [exact FRS1| exact NM1].
    all: match goal with |- ?g => idtac "FIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis MCE : MC = 0x63c120.

  (* [comment removed for export] *)
  #[using="IMG JC GRP OSEP MCOK MIm SLO2"] Lemma mm_fail : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.Pcntc,(15.&40.)Pr,$3.Pxra,(15.&40.)Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pxs0',(15.&40.)Pxs1,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pxs2,(15.&40.)Pxs3,(15.&40.)Pxs4,(15.&40.)Pxs5,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R1=.R1<.R1;.R1:.R19.R18.)P,(3:.$1;.R1:.VMC,(34.$3;.(3<.R18.)(32.$3;.)))P,(23.(24.(25.(26.+2.+1?.))R18.)(=.R18.=))P,(=.R20.(1=.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))))P,(=.R20.(1?.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))Vd,))P,(=.(11.R1=.)(20.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))))(27.$1;.(28.$1;.VR,VHIA,R21.Vmo,)$29.(2:.(2;.R1;.(2<.&40.(>.(2=.&40.Vsp,)-40.))Vgp,Vtp,R1:.R19.R18.R17.R16.(2<.&40.R1<.)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(2<.&40.+<>?>4.)Vfc,(2>.(15.&40.))R1?.(2?.$1;.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J MCc HR HV HF HSZ.
    eapply mm_exit; [| exact HR].
    eapply (mm_fin v f hc LBc mc dXc mc cntc J (munch_refl _ mc) (wmono_refl asegs mc)); try assumption.
    - exact (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J).
    - pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HHc. cbn [app] in HHc. exact HHc.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@D44412773793.157D60246393192.157L2397676628.0   L34409126551.6  Q41197071117.157Q44851740177.154Q48507632145.154Q50377214961.155Q51854248945.154Q53190598271.157Q53972118266.154Q62174664229.15400000g01^01_02202302M02N02k03K04904[05<S2ra2sp1X2sX2nX2pX3xs04padX4ownX2MC4cntc2HB5Ha_st5Hl_stS2ra2sp1X2sX2nX2pX3xs04padX4ownX2MC4cntc2HB5Ha_st5Hl_stSS1R2MC3MC13MC21x2HxFS1X2sX2nX2pX3xs04padX4ownXFS1X2sX2nX2pX3xs04padX4ownX2HBS1R1X2sX2nX2pX3xs04padX4ownX3MC5S1X2sX2nX2pX3xs04padX4ownX4cntc2HB5Ha_st5Hl_stS1R1X2sX2nX2pX3xs04padX4ownX5ALWF'S1R1X2sX2nX2pX3xs04padX4ownX4IMG'". (* [comment removed for export] *)
  #[using="IMG JC GRP OSEP MCOK MIm SLO2 MCE"] Lemma mm_count : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.Pcntc,(15.&40.)Pxra,(15.&40.)Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pxs0',(15.&40.)Pxs1,(15.&40.)Pxa0,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pxs2,(15.&40.)Pxs3,(15.&40.)Pxs4,(15.&40.)Pxs5,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R1=.R1<.R1;.R1:.R19.R18.)P,(3:.$1;.R1:.VMC,(34.$3;.(3<.R18.)(32.$3;.)))P,(=.R1?.(1=.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))))P,(=.R1?.(1?.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))Vd,))P,(=.(11.R1<.)(20.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))))(27.$1;.(28.$1;.VR,VHIA,R20.Vmo,)$29.(2:.(2;.R1;.(2<.&40.(>.(2=.&40.Vsp,)-40.))Vgp,Vtp,R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(2<.&40.+<?124.)Vfc,(2>.(15.&40.))R1>.(2?.$1;.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J MCc HV HF HSZ. basic_factsA hc.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    dpose MCOK as (MC1 & MC2 & MC3 & MC4 & MC5 & MC6).
    assert (CWMC : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) MC 8).
    { intros x Hx. right. left. split; [clear - Hx MC1 MC2; lia| apply MC3; exact Hx]. }
    pose proof (conj J I) as Jbox. clear J MX1 OUT1 FRS1 FRA1 HPX1 XP1 XLS1 NM1 NS1 ST1 FR1 OX1.
    rewrite MCE in MCc, CWMC, MC4, MC5.
    pose proof (munch_refl [(0x63c120, 0x63c120 + 8)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    destruct Jbox as [J _].
    match goal with MCq : rw_cells asegs mF _ [C8 ?c9], MIq : mem_inv asegs mF, HHq : HM asegs R HIA hc LBc LF mF |- _ =>
      eapply (mm_exit hc LBc mF dXc c9 0); [| clear; lia];
      eapply (mm_fin v f hc LBc mc dXc mF c9 J); [rewrite MCE; exact MU| exact WM| exact MIq| exact HHq| rewrite MCE; exact MCq| exact HV| exact HF| exact HSZ] end.
    all: match goal with |- ?g => idtac "COUNT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation dP := (g_P g).
  Local Notation JBP := (JBA asegs R HIA LB LF m dX sp lo dP).

  (* [comment removed for export] *)
  Record MMS (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) (cntc : word) : Prop := {
    ms_mc : rw_cells asegs mc MC [C8 cntc];
    ms_gt : rw_cells asegs mc (G + 120) (grp_tail_cells g);
    ms_og : aobj asegs AL (hcs asegs R HIA hc) mc G 192;
    ms_bp : BJA asegs R HIA LF sp dP hc LBc mc dXc;
    ms_ss : sshad asegs AL mc slo (bv_unsigned sp) }.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L39738688048.5L48111173305.5L59315317366.600000?00M00]S2sp3SPc2HS1x1SS2sp1G2GS1x2HxS1G2lo2GS1x2Hx1S". (* [comment removed for export] *)
  #[using="MT g MC d GRP OSEP"] Lemma mm_grp_cr : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.PSPc,$3.P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R7.R6.R5.R4.R3.R2.)P,(=.R2.(2=.&40.Vsp,))(5.(3=.VR,)(6.$2.(12.R6.R4.)(7.VLF,))R3.VG,+<0.)")
(* [comment removed for export] *).
  Proof.
    intros v f hc LBc mc dXc SPc J HS.
    ddestruct OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    ddestruct GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW).
    assert (GCR0 : client_range L (mpd_keep LB dX ++ fdata LF) (bv_unsigned sp) G 192).
    { apply client_range_keepA; [| exact OS2]. intros x Hx. destruct (GCR x Hx) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
      destruct GSP as [GS|GS]; [exfalso; clear - S Hx GS; lia| left; clear - Hx GS; lia]. }
    intros x Hx. destruct (GCR0 x Hx) as [S|[D|(b & Hb & Hr)]]; [left; clear - S HS; lia| right; left; exact D| right; right].
    exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
    eapply xa_keep_keep; first [exact JC | exact J | exact Hb].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L11347533506.3L30017877813.4L31036473107.6L31894977752.3L33357133290.3L34409126551.6L43075739398.3L46197683974.700000900I00]00g00o01B01K01aS2MC1x2HxS2sp2lo3SPc4HSPcS1R3HIA1h2sp3TOP3HT0S1X2MC3OS3S1G1x2HxS1R2MC3MC13MC21x2HxS1X1G3OS1S1R2sp2lo3LOS3SPc4HSPc". (* [comment removed for export] *)
  #[using="MT d JC GRP OSEP MCOK SLO1"] Lemma mm_step : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.Pcntc,(15.&40.)Pm',P,(15.&40.)(16.(15.&8.))Ph',(21.$1;.VR,VHIA,)PLB',(1.$2.)PdX',$4.PSPc,$3.PPHI',$3.PFR',$3.P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R>.R=.R<.R;.R:.R9.)P,(3>.R=.R<.R;.R:.R9.)P,(3?.$1;.VR,VHIA,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(1>.Vg,))P,(23.(=.Vlo,R6.)(=.R6.(40.(2=.&40.Vsp,)+40.)))P,(=.=R6.)P,(=.=R6.)P,(38.$1;.R=.)P,(41.$1;.R>.Vlo,(40.(2=.&40.Vsp,)+40.))P,(42.$1;.VR,(12.R13.R11.)VLF,R;.(43.VR,)(44.$1;.VR,VHIA,R14.)(34.(35.$3.$3.)(36.$3.$3.VX,(>.VX,+10.))(32.(35.$3.$3.)))R12.R?.)P,(8.$3.(45.$1;.VR,VHIA,R?.)(45.$1;.VR,VHIA,R15.))P,(8.$3.(44.$1;.VR,VHIA,R10.)(44.$1;.VR,VHIA,R16.))P,(8.$3.(46.$1;.VR,VHIA,R11.)(46.$1;.VR,VHIA,R17.))P,Px,$3.P,(47.$1;.VR,VHIA,R19.R1.)(47.$1;.VR,VHIA,R14.R2.)P,(=.(48.$1;.VR,VHIA,R13.)(>.(48.$1;.VR,VHIA,R19.)R?.))P,(=.(49.$1;.VR,VHIA,R14.)(>.(49.$1;.VR,VHIA,R1:.)R?.))P,(39.$1;.VR,VHIA,R15.R14.VLF,R16.)P,(4:.$1;.R17.R15.R14.)P,(4;.R1<.R1:.R16.R15.)P,(4<.R1=.R1;.R16.)P,Pb,$2.P,(4=.$2.R1.(4>.R18.))(<.(4=.$2.R2.(4>.R1>.))(4?.VR,(12.R20.R1>.)VLF,(50.$3.$3.R2.)(51.$3.$3.R2.)))(23.(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)(>.R22.R16.)(>.R21.R15.)R1:.R19.R1;.R18.)(3>.R1:.R19.R1;.R18.R1<.))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until FR'. intros J S DPJ HSPc HPHI HFR MI' ST' HP HT' HS' HF' HCS' HV' HFR' HH' MX' OUT' BK FRA'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (art_data_lo asegs R HIA) as DLO.
    destruct S as [SMC SGT SOG SBP SSS].
    ddestruct OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    ddestruct MCOK as (MC1 & MC2 & MC3 & MC4 & MC5 & MC6).
    pose proof (mm_grp_cr v f hc LBc mc dXc SPc J ltac:(clear - HSPc; lia)) as GCRc.
    split.
    - eapply (xa_call asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC); eassumption.
    - constructor.
      + eapply (presA_rw_cells asegs R); [exact HP| exact SMC| |].
        * cbn [cells_size csize Nat.add]. intros x Hx. right. left. split; [clear - Hx MC1 MC2; lia| apply MC3; clear - Hx; lia].
        * cbn [cells_size csize Nat.add disjoint_from fst snd]. split; [clear - OS3; lia| exact I].
      + eapply (presA_rw_cells asegs R); [exact HP| exact SGT| |].
        * unfold grp_tail_cells. cbn [cells_size csize Nat.add]. intros x Hx. apply GCRc. clear - Hx. lia.
        * unfold grp_tail_cells. cbn [cells_size csize Nat.add disjoint_from fst snd]. split; [clear - OS1; lia| exact I].
      + eapply aobj_cs_mono; [exact HCS'|].
        eapply (presA_aobj0 asegs R); [exact (hcs_ok asegs R HIA hc)| exact HP| exact SOG| intros x Hx; eapply hcs_below_top; exact Hx|].
        right. split; [exact GCRc| clear - ALO LOS HSPc; lia].
      + eapply (bja_call asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC dP DPJ); eassumption.
      + eapply (presA_sshad asegs R); [exact HP| exact SSS| exact SLO1|].
        rewrite (xa_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J). pose proof (hm_top asegs R HIA h LB LF m HH) as HT0. clear - TOP HT0. lia.
    all: match goal with |- ?g => idtac "STEP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L28704391748.3L30030460357.4L38569812941.1L41886271693.1L62195706060.6L8816488554.6 00000<00J00O00T00i01=S2sp2lo4LOSPS2sp2lo3SPc2HSS3dXcS3dXcS2sp2lo3dXc3SPc2HS2XLS2sp1X2lo3SPc2HS3DSX". (* [comment removed for export] *)
  #[using="JC"] Lemma mm_opX : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.PSPc,$3.P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R7.R6.R5.R4.R3.R2.)P,(23.(=.Vlo,R2.)(=.R2.(40.(2=.&40.Vsp,)+40.)))(23.(4:.$1;.R5.R6.R4.)(23.(52.(8.$9.(:.R4.)$53.))(23.(8.$3.(54.R4.)VX,)(23.(55.R4.R4.Vlo,R3.)(23.(5.(3=.VR,)(6.$2.R6.(7.VLF,))Vlo,VX,+10.)(23.P,(8.$9.(:.R4.)$;.)(5.(3=.VR,)(6.$2.R7.(7.VLF,))Vlo,(?.R5.)(10.+4.(11.R5.)))(23.(56.VR,R6.VLF,R3.(45.$1;.VR,VHIA,R7.)R4.)(23.P,(52.(8.$9.(:.R4.)$57.))(<.(=.(>.(?.R5.)(10.+4.(11.R5.)))Vlo,)(=.R4.(?.R5.)))(23.(58.$1;.(59.VR,)(47.$1;.VR,VHIA,R7.)R5.R4.)(5:.R4.))))))))))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros v f hc LBc mc dXc SPc J HS.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    cbn [md_addr] in AD1.
    assert (OWH : md_own dXc <> LNull -> md_own dXc = LHeap) by (destruct (md_own dXc); [intros C; exfalso; exact (C eq_refl)| reflexivity| intros _; exfalso; exact (NS1 eq_refl)]).
    split; [exact MX1|]. split; [exact NS1|]. split; [exact AD1|].
    split.
    { unfold opnd_sep. rewrite AD1.
      split; [intros ON; exact (XP1 (OWH ON))|]. split; [intros EO; exact (XP1 EO)|]. split; [left; reflexivity|].
      split; [clear - DSX HS; lia|]. intros ON. destruct (XLS1 ON) as [XL|XL]; [left; exact XL| right; clear - XL HS; lia]. }
    split; [pose proof (xa_crX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ lo J ltac:(clear - LOSP; lia)) as CR; cbn [app] in CR; exact CR|].
    split.
    { intros EO. ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & _).
      eapply client_range_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]. }
    split.
    { split; [rewrite AD1, HT1; eapply client_wrange_sp_mono; [| exact (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J)]; clear - HS; lia|].
      rewrite AD1. exact XP1. }
    split; [intros ON; destruct (XLS1 ON) as [XL|XL]; [left; exact XL| right; clear - XL HS; lia]|].
    split; [split; [rewrite AD1; exact OX1| intros ES; exfalso; exact (NS1 ES)]| intros ES; exfalso; exact (NS1 ES)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L28704391748.3L36326650258.3L38241851068.6L41111806811.6L48528905425.3L59450024946.300000<00E00Y00k01401=S2sp2lo4LOSPS1X1G3OS1S2sp1g2lo3SPc2HS3OB4S2sp1g2lo3SPc2HS1KS1X1G3OS1S1R1G3GU1". (* [comment removed for export] *)
  #[using="MT JC GRP OSEP"] Lemma mm_opP : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.Pcntc,(15.&40.)PSPc,$3.P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R8.R7.R6.R5.R4.R3.)P,(3>.R7.R6.R5.R4.R3.)P,(3?.$1;.VR,VHIA,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(1>.Vg,))P,(23.(=.Vlo,R4.)(=.R4.(40.(2=.&40.Vsp,)+40.)))(23.(4:.$1;.R8.R9.(1>.Vg,))(23.(8.$3.(54.(1>.Vg,))(>.VG,+8.))(23.(5;.R7.(1>.Vg,))(23.(52.(8.$3.(54.R7.)(54.(1>.Vg,))))(23.(55.R7.(1>.Vg,)Vlo,R5.)(23.(5.(3=.VR,)(6.$2.R9.(7.VLF,))Vlo,(54.(1>.Vg,))+10.)(23.P,(8.$9.(:.(1>.Vg,))$;.)(5.(3=.VR,)(6.$2.R:.(7.VLF,))Vlo,(?.(1>.Vg,))(10.+4.(11.(1>.Vg,))))(23.(58.$1;.(59.VR,)(47.$1;.VR,VHIA,R:.)R8.(1>.Vg,))(23.(5:.(1>.Vg,))(5<.VR,(54.(1>.Vg,))+10.Vd,))))))))))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros v f hc LBc mc dXc cntc SPc J S DPJ HS.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    destruct S as [SMC SGT SOG SBP SSS]. pose proof SBP as [BA BS BL BO BOL].
    pose proof DPJ as [MB0 OB CRB CRBL SXB BIMG]. dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof (xa_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as AD1. cbn [md_addr] in AD1, OB1, SXB.
    ddestruct OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    ddestruct GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW).
    dpose GAT as (_ & _ & _ & EP & _ & _ & _ & MP & _).
    assert (MPo : mpd_at asegs m LB dP) by (split; [exact MP| left; exact GPS]).
    split; [eapply opnd_atA_mpd_back; [exact MPo| exact BA]|]. split; [exact EP|].
    split; [right; rewrite AD1, EP; clear - OS1; lia|]. split; [rewrite AD1, EP; clear - OS1; lia|].
    split.
    { unfold opnd_sep. rewrite AD1.
      split; [exact OB1|]. split; [exact BS|].
      split; [destruct (limb_own_eq_dec (md_own dXc) LHeap) as [EO|NEO]; [| right; left; exact NEO];
              destruct (limb_own_eq_dec (md_own dP) LNull) as [EN|NEN]; [right; right; left; exact EN| right; right; right; exact (BL EO NEN)]|].
      split; [clear - OB4 HS; lia|]. intros ON. destruct (OB5 ON) as [K|K]; [left; exact K| right; clear - K HS; lia]. }
    destruct (bja_client asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC dP DPJ [] v f hc LBc mc dXc LBc lo J SBP ltac:(intros b Hb _; exact Hb) ltac:(clear - LOSP; lia)) as [CR1 CR2].
    split; [exact CR1|]. split; [exact CR2|].
    split; [split; [exact BO| intros ES; apply BOL; rewrite ES; discriminate]|].
    split; [unfold grp_imgA, grp_mpds in GIMG; apply Forall_inv in GIMG; exact GIMG|].
    rewrite EP. destruct GUW as [[GU1 GU2]|GU]; [left; split; [clear - GU1; lia| exact GU2]| right; exact GU].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis BUD : havol asegs R HIA h + PHI0 <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FR0 <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_ECP_MUL_MOD <= C24MAX.
  Hypothesis LFB : (length LF + 2 <= 512)%nat.
  Hypothesis SZA : 0 <= md_n dA /\ 0 <= md_n dB /\ 0 <= nX /\ 0 <= md_n dP.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L33709973054.76L40230658807.76L58421668177.7700000?00N00mS2LF2ra3LFB3dXcS2LF2ra3LFB3dXcS2LB2LF2ra3LFB3LBc3dXc2C12C22C3". (* [comment removed for export] *)
  #[using="JC LFB"] Lemma mm_cnt24 : forall v f hc LBc mc dXc, XJ0 v f hc LBc mc dXc -> cnt24 LBc <= cnt24 LB + 1.
  Proof.
    intros v f hc LBc mc dXc J.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & _). cbn [app] in ND1.
    pose proof (xa_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as (_ & _ & O3 & _).
    assert (INC : incl LBc (mpd_blk dXc ++ LB)) by (intros b Hb; apply in_or_app; destruct (O3 b Hb); [right| left]; assumption).
    pose proof (cnt24_incl LBc (mpd_blk dXc ++ LB) (NoDup_map_inv fst LBc ND1) INC) as C1.
    rewrite cnt24_app in C1. pose proof (cnt24_le_length (mpd_blk dXc)) as C2.
    assert (C3 : Z.of_nat (length (mpd_blk dXc)) <= 1) by (unfold mpd_blk; destruct (md_own dXc); cbn; lia).
    lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0@D3739879934.232 D51036099192.230D59441450494.231D7389163526.232 L11570029709.1  L1175746480.1   L11962609179.43 L12530931678.13 L13449167246.13 L1579419076.5   L16826948112.231L17645738372.1  L26825993283.6  L28145219905.9  L29010569984.238L33428267848.43 L35663928186.7  L37707956009.43 L38738191873.9  L39029471052.43 L40290687782.1  L48442012624.43 L49994140762.10 L5261871668.3   L57146531606.43 L57395829415.2  L58569561783.10 L60098763854.3  L62704181792.8  L66151427842.16 P49988094288.231Q30985333526.196Q30985398804.231Q33421864530.229Q42435318089.229Q44741466490.231Q49988094288.231Q68268723142.22900000100200F01g01j01n02o03G03W03g04;04?04W05305405V05k06@06`07307607V07W07a08d08j09J09T0:50:O0;<0<10<f0=M0=d0=e0=f0>MFFS2LF2ra2sp1X3xs03LFBS1R2LF2ra2sp1X2sX2nX2pX3xs04padX4ownX2lo4SLO23LFB5NEEDR3LOS3dXc3NER3SPR4ALO'4ACP'2X03XAD3AD11x2HxS1GS2spS1R3HIA1h2LF2sp2nX2dA2dB1g3BUD3LFB3SZA1v2hc3dXc2HV3SPR3HV14MONO1HS2nX2dA2dB1g3SZA3dXc3NM1S2nX2dA2dB1g3SZAS2nX2dA2dB1g3SZAS2LF2ra2sp1X3xs03LFBS2spS1R2sp2lo4SLO25NEEDR3NERS2nX2dA2dB1g1v3dXc2HV4MONO1HFS1R3HIA1h2LF2sp3LFB3TOP2hc3SPR3HT1S1R3HIA1h2sp2lo3TOP1HS1R2LF2sp2lo4SLO23LFBS2nX2dA2dB1g3SZA3dXc3HSZ3dX23SZ2S2LF2sp3LFB3SPA3SPRS1XS2LB2LF2sp4C24H3LFB3LBc3SPR4C24cFS1X2X03X16S1R3HIA1h2LF2sp2nX2dA2dB1g1d2D04BUDF3LFB1f2hc3dXc2HF3SPR4HFR15MONOFS1d2D0S2nX2dA2dB1g1d2D01f3dXc2HF5MONOFS1R2lo3LOSS1R2sp2lo4SLO23slo4SLO35NEEDR3NERS2sp2r03SPA1q1r1H2H02q02H4S1R2LF2sp1X3xs02lo4SLO23LFB5NEEDR3FSZ3NER3DSXS1R2LF2sp3xs02lo4SLO23LFB5NEEDR3LOS3NER3SPR4ALO'4ACP'S1R2LF2sp3xs02lo4SLO23LFB5NEEDR3LOS3NER3SPR4ALO'4ACP'S1R3HIA1h2LF2sp3xs03LFB3TOP2hc3HT14HTOPS1R2LF3xs03slo4SLO13LFBFFS1R3HIA1h2LF2sp3xs03LFB3TOP2hc3HT14HTOP". (* [comment removed for export] *)
  #[using="IMG HMOD JC TPV UWX D0 GRP OSEP MCOK MIm SLO2 SLO1 SLO3 MCE BUD BUDF C24H LFB SZA"] Lemma mm_mod : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.Pcntc,(15.&40.)Pxra,(15.&40.)Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pxa0,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pxs2,(15.&40.)Pxs3,(15.&40.)Pxs4,(15.&40.)Pxs5,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R1;.R1:.R19.R18.R17.R16.)P,(3>.R1:.R19.R18.R17.R16.)P,(3?.$1;.VR,VHIA,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(1>.Vg,))P,(=.R1>.(5=.(11.VdA,)(11.VdB,)))P,(=.R1>.(5>.Vd,))P,(=.(11.R1;.)(5?.VnX,(11.VdA,)(11.VdB,)))(27.$1;.(28.$1;.VR,VHIA,R1?.Vmo,)$29.(2:.(2;.R1:.(2<.&40.(>.(2=.&40.Vsp,)-40.))Vgp,Vtp,R19.R18.R17.(2<.&40.VX,)(2<.&40.VG,)R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(2<.&40.+<?110.)Vfc,(2>.(15.&40.))R1=.(2?.$1;.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J S DPJ HV HF HSZ. basic_factsA hc.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    ddestruct (mm_opX v f hc LBc mc dXc (bv_unsigned sp + -64) J ltac:(clear - SLO2 NER NEEDR; lia)) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (mm_opP v f hc LBc mc dXc cntc (bv_unsigned sp + -64) J S DPJ ltac:(clear - SLO2 NER NEEDR; lia)) as (PM & PAD & PSEP & PNE & POS & PCR & PCRL & PAO & PIM & PUW).
    pose proof (mm_cnt24 v f hc LBc mc dXc J) as C24c.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    pose proof (ms_ss _ _ _ _ _ S) as SSc.
    assert (M8 : (bv_unsigned sp + -64) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
    pose proof (sshad_split asegs AL mc slo (bv_unsigned sp + -64) (bv_unsigned sp) SSc ltac:(clear - SLO3 SLO2 NER NEEDR; lia) M8) as [SS1 _].
    pose proof (conj S I) as Sbox. pose proof (conj J I) as Jbox.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    clear MU WM.
    assert (MONO : mod_mpi_PHIn (md_n dXc) (md_n dP) <= mod_mpi_PHIn (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n dP)) by (apply mod_mpi_PHIn_mono; [exact HSZ| apply Z.le_refl]).
    assert (MONOF : mod_mpi_FRn (md_n dXc) (md_n dP) d <= mod_mpi_FRn (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n dP) d)
      by (apply mod_mpi_FRn_mono; [split; [clear - NM1 SZA; cbn [md_n] in *; lia| exact HSZ]| apply Z.le_refl| clear - D0; lia]).
    assert (FRNN : 0 <= mod_mpi_FRn (md_n dXc) (md_n dP) d) by (apply mod_mpi_FRn_nonneg; [clear - NM1 SZA; cbn [md_n] in *; lia| exact D0]).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HMOD as CP. unfold mpi_mod_mpi_stmtA_sz, mpi_binop_stmtA_sz in CP.
      eapply CP with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (dA := dXc) (dB := dP) (lo := lo) (d := d) (slo := slo);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia; try eassumption; try reflexivity.
      all: try (intros _; split; [exact SS1| split; [exact SLO1| exact SLO3]]).
      all: try (left; reflexivity).
      all: try (intros _; exact PNE).
      all: try (rewrite XAD; exact XCR).
      all: try (rewrite XAD; exact UWX).
      all: try (eapply uw_obj_uwc; [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear; lia]).
      all: try (rewrite XAD; reflexivity).
      all: try (rewrite PAD; apply f_equal; clear; lia).
      all: unfold mm_PHIn, mm_FRn, red_PHIn, red_FRn, C24_ECP_MUL_MOD, C24_MOD_MPI in *;
           try (clear - LOS SLO SLO2 NEEDR NER NES SPA SPR BUD BUDF C24H C24c D0 LOSP TOP HT1 HV HF HV1 HFR1 MONO MONOF FRNN SZA LFB;
                pose proof (grow_PHI_nonneg (2 * md_n (g_P g))); unfold mul_mpi_FRn, calls_FR, fr_charge in *; lia).
      all: match goal with |- ?g => idtac "MOD-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & GR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2, HP2 by qlia. rewrite XAD in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    presA_transport HP2.
    destruct Sbox as [S0 _]. destruct Jbox as [J0 _].
    destruct GR as [[MR BK] SZ2].
    pose proof ST2 as ST2'. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST2' by (clear; lia).
    destruct (mm_step v f hc LBc mc dXc cntc m2 h2 LB2 dX2 (bv_unsigned sp + -64) (mod_mpi_PHIn (md_n dXc) (md_n dP)) (mod_mpi_FRn (md_n dXc) (md_n dP) d) J0 S0 DPJ
                ltac:(clear - SLO2 NER NEEDR; lia) ltac:(apply mod_mpi_PHIn_nonneg; clear - SZA NM1; cbn [md_n] in *; lia) ltac:(exact FRNN)
                MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as [J2 S2].
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    assert (BV2 : v + mod_mpi_PHIn (md_n dXc) (md_n dP) <= PHI0) by (unfold mm_PHIn, red_PHIn; pose proof (grow_PHI_nonneg (2 * md_n (g_P g)) ltac:(clear - SZA; lia)); clear - HV MONO H; lia).
    assert (BF2 : f + mod_mpi_FRn (md_n dXc) (md_n dP) d <= FR0) by (unfold mm_FRn, red_FRn, calls_FR, fr_charge; clear - HF D0 MONOF; lia).
    assert (SZ2' : md_n dX2 <= SZ0).
    { unfold mod_mpi_nz in SZ2. unfold mm_nz. clear - SZ2 HSZ SZA. lia. }
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - eapply mm_fail; [exact J2| exact (ms_mc _ _ _ _ _ S2)| exact (proj2 MR)| exact BV2| exact BF2| exact SZ2'].
    - eapply mm_count; [exact J2| exact (ms_mc _ _ _ _ _ S2)| exact BV2| exact BF2| exact SZ2'].
    all: match goal with |- ?g => idtac "MOD-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L16194418498.1L38400154755.1L42439184616.3L52314013762.1L62065999094.1L64685646146.700000300600B00E00H00aS1GS1GS1R3slo4SLO1S1GS1GS1R3HIA1h2sp3slo4TOPo3HT0". (* [comment removed for export] *)
  #[using="MT d JC GRP SLO1"] Lemma mm_limbs : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.Pcntc,(15.&40.)PW,(1.$60.)Pm',P,(15.&40.)(16.(15.&8.))Pxs',(1.(15.&40.))P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R:.R9.R8.R7.R6.R5.)P,(3>.R9.R8.R7.R6.R5.)P,(33.R5.R8.R4.)P,(37.$1;.R9.R5.)P,(38.$1;.R6.)P,(41.$1;.R7.Vlo,(40.(2=.&40.Vsp,)+40.))P,(39.$1;.VR,VHIA,R>.R=.VLF,R8.)P,Pa,$3.P,(52.(61.R;.R1.))(<.(23.(8.$9.(:.R>.)$;.)(23.(=.(?.R>.)R2.)(24.R2.(>.(?.R>.)(10.+4.(11.R>.))))))(23.(=.Vlo,R2.)(24.R2.(40.(2=.&40.Vsp,)+40.))))P,(62.R;.(40.(2=.&40.Vsp,)+40.)+40.)P,(62.R<.VX,+10.)P,(63.$1;.R<.(?.R?.)R;.)P,(8.$64.(65.(15.&40.)R<.)(65.(15.&40.)(66.R10.)))P,(67.(47.$1;.VR,VHIA,R14.)R?.)P,(62.R10.VG,+<0.)P,(62.R11.VMC,+8.)P,P,(52.(8.$9.(:.(1>.Vg,))$57.))(62.R13.(?.(1>.Vg,))(10.+4.(11.(1>.Vg,))))(23.(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R1:.R19.R18.R17.R12.(1<.(54.R15.)(68.R15.)(11.R15.)(?.R15.)R11.(69.R15.)(:.R15.)))(3>.R18.R17.R12.(1<.(54.R15.)(68.R15.)(11.R15.)(?.R15.)R11.(69.R15.)(:.R15.))R14.))")
(* [comment removed for export] *).
  Proof.
    intros until xs'. intros J S MU WM MI' ST' HH' HW DF DS ARR LEN' WC DG DM DPL.
    pose proof JC as [_ _ _ _ HHo _ _ _ _ _ _ _ TOPo _ _].
    destruct S as [SMC SGT SOG SBP SSS].
    ddestruct GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW).
    dpose GAT as (_ & _ & _ & EP & _).
    split.
    - eapply (xa_limbs asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC); eassumption.
    - constructor.
      + eapply rw_cells_transport; [exact SMC| exact MU| exact WM| cbn [cells_size csize Nat.add]; exact DM].
      + eapply rw_cells_transport; [exact SGT| exact MU| exact WM|]. unfold grp_tail_cells. cbn [cells_size csize Nat.add].
        eapply disjoint_from_sub; [exact DG| clear; lia| clear; lia].
      + eapply (aobj_munch asegs AL _ (hcs_ok asegs R HIA hc) W mc m'); [exact WC| exact MU| exact SOG].
      + assert (B' : BJA asegs R HIA LF sp dP hc LBc m' dXc).
        { eapply bja_munch; first [exact J | exact SBP | exact MU | exact WM | exact WC | exact DPL | idtac].
          rewrite EP; eapply disjoint_from_sub; [exact DG| clear; lia| clear; lia]. }
        destruct B' as [BA BS BL BO BOL]. constructor; cbn [md_own md_p md_n]; assumption.
      + eapply (sshad_munch asegs AL (hcs asegs R HIA hc) W mc m'); [exact (hcs_ok asegs R HIA hc)| exact WC| | exact MU| exact WM| exact SSS].
        eapply crange_sub; [exact (hcs_stack asegs R HIA hc)| clear - SLO1; lia|].
        rewrite (xa_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J). pose proof (hm_top asegs R HIA h LB LF m HHo) as HT0. clear - TOPo HT0. lia.
    all: match goal with |- ?g => idtac "LIMBS-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation SHq E := (Z_to_bv 64 (Z.shiftr E 3 + al_sb AL)).

  (* [comment removed for export] *)
  Ltac mm_open_limbs J S DPJ :=
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1);
    pose proof (bja_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC (g_P g) DPJ _ _ _ _ (ms_bp _ _ _ _ _ S)) as (P0' & P16' & PAL' & LENP & NRP & PSS & OWNP0 & OWNP1);
    pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ (ms_bp _ _ _ _ _ S))) as [(CP & _) _].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L1016930933.3 L1016930933.7 L15766842478.4L17838428278.3L17838428278.7L29916022107.2L38180633941.000000900N00]00f01501=01>S1G3dXc1KS2nX2pX1G3dXc2E12E21KS1R2lo3LOS4ALO'S1G3dXc1KS2pX1G3dXc2E11KS3dXc2N1S". (* [comment removed for export] *)
  #[using="MT g MC d JC GRP OSEP"] Lemma mm_grp_xl : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R6.R5.R4.R3.R2.R1.)P,(8.$9.(:.R2.)$;.)(<.(=.(>.VG,+<0.)(?.R3.))(=.(>.(?.R3.)(10.+4.(11.R3.)))VG,))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros v f hc LBc mc dXc J EO.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & _).
    ddestruct OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    destruct (xa_freshA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [Hb|HFR].
    - unfold mpd_blk in Hb. cbn [md_own md_p md_n] in Hb. destruct ownX; try (destruct Hb; fail). destruct Hb as [E|[]]. injection E as E1 E2.
      destruct (OS2 eq_refl) as [K|K]; [left| right]; clear - K E1 E2; lia.
    - cbn [fst snd] in HFR. pose proof (mm_grp_cr v f h LB m dX (bv_unsigned sp)) as _.
      ddestruct GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW).
      assert (GCR0 : client_range L (mpd_keep LB dX ++ fdata LF) lo G 192).
      { apply client_range_keepA; [exact GCR| exact OS2]. }
      destruct (fresh_apart_client R (mpd_keep LB dX) LF lo G 192 _ _ HFR GCR0 ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO' LOS; lia)) as [K|K]; [right| left]; clear - K; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02C0@C24112444547.248D17433993720.248D17444351834.249D30202740417.249D30213615715.248D42633159082.249D42643779336.248D65414904706.249D65429976352.248K11420089551.248K28284592895.247K320726878.248  K33706984260.248K43070029892.247K50678622482.248K54822521893.248K61717199003.248K6599509340.248 L11416546478.3  L1175746480.1   L11899326182.3  L11901388147.2  L15263448759.7  L16073392874.2  L17645738372.1  L19630045162.2  L19892448499.9  L21877607696.8  L21890123013.7  L21890137397.14 L21892252690.9  L21892255376.7  L23100341967.212L23643762344.7  L24101795768.214L24537859376.214L27631494112.8  L28003093277.2  L28270437390.4  L28513481806.7  L28515534827.14 L28515549147.8  L2975768925.2   L30202704871.5  L31834319237.7  L331342290.2    L33706525504.6  L33717624121.2  L33719176021.4  L33719186277.11 L33721172160.3  L33721174594.8  L33721664349.8  L35455353877.1  L35651110259.214L35663928186.7  L37369374369.0  L38235734261.1  L39025373398.7  L39025375828.3  L39027372481.3  L39040022996.5  L39843563160.11 L39843577512.4  L39845705021.4  L39845707711.6  L39845707711.7  L39996994530.9  L39996995936.5  L39998982853.11 L39998993141.5  L40011643616.7  L40011840149.9  L40653140888.12 L41128898453.2  L42585609932.3  L42633816569.1  L43082027553.2  L43882228554.6  L45643336298.5  L46805364568.8  L47795326910.3  L47797453867.3  L50671808483.11 L51245119830.3  L52181964255.9  L54815705812.2  L54816067489.4  L54817938500.3  L54818194484.5  L54822538941.4  L54822538941.6  L55714478185.11 L55986908889.1  L60098763854.3  L60283674290.12 L61711433322.3  L6609783617.2   L66151427842.16 L66151427842.17 O13427959270.248O17159180510.248O21957337947.248O24112444547.248O2453481106.247 O27573497883.247O3348508776.248 O40755074099.248O43419437345.248O63469524774.248P11420089551.248P42591375421.248P43070029892.247Q11495966671.224Q12370813529.224Q13515859141.224Q17198776989.223Q22915297438.225Q26999370278.226Q30213615715.248Q30987168515.226Q31834646913.248Q34220676136.224Q37617138047.223Q37924141703.223Q39212284437.226Q39830861497.248Q42643779336.248Q47792156591.224Q48363247790.248Q48971481744.223Q50786263537.248Q5118570719.225 Q5118667814.226 Q5127240659.223 Q52316291654.225Q52316470523.224Q52324505011.223Q5477005154.223 Q5485174314.224 Q59703481013.224Q60441339931.224Q60511567613.226Q6143569392.224 Q67970158471.225Q68049981125.226Q9530130738.223 00000101@02X03f04h05S06507R08f08g09W0:c0<20<30=20><0?@0@L0@M0@Q0@R0@X0@k0A20A60A=0AA0AB0AC0AD0AE0AF0Ah0B;0B]0Ca0D?0D@0DA0DB0DC0DD0DK0DX0D_0D`0Da0Db0Dc0Dd0De0Df0ED0EH0Ej0F?0F@0FD0FE0FF0FG0FS0FT0FU0FV0Fn0GF0GG0GH0GI0GJ0GK0Gn0HT0HU0HV0H[0H\0Hc0I00IN0IO0IP0IQ0IR0Io0J00J10J20J30JA0JS0K>0KA0KK0L40L50L60LR0LS0LT0LU0LV0LW0LX0LY0LZ0L[0L\0L]0L^0O@0OA0OT0P=0P>0PQ0Pd0Q:0QU0RY0S00S10SD0SW0Sj0TR0Tg0Th0UA0UT0Uh0V;0VN0Va0W40WG0WZ0Wm0X@0XA0YI0YZ0Ym0Z@0ZS0ZdFS1R3HIA1h2LF2ra2sp1X3xs01G1g2MC3MCE3LFB3TOP2hc3pXc2xs3SPR2X03P0'3PP02G03HT13XP0S1R3HIA1h2LF2ra2sp1X3xs01G1g2MC3MCE3LFB3TOP2hc3pXc2xs3SPR2X03P0'3PP02G03HT13XP03xs64LEN6S2LF2ra2sp1X3xs01G1g2MC3MCE3LFB1N3pXc2xs3HNP3SPR2X03P0'3PP02G02N13XP03xs64LEN6S2LF2ra2sp1X3xs01G1g2MC3MCE3LFB1N3pXc2xs3HNP3SPR2X03P0'3PP02G03XP0S2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xs3xs64LEN6S2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xsS1R2LF2ra2sp1X3xs01G1g2MC2lo4SLO23MCE3LFB5NEEDR3LOS3pXc2xs3NER3SPR2X03P0'3PP02G03XP03xs64LEN6S1R2LF2ra2sp1X3xs01G1g2MC2lo4SLO23MCE3LFB5NEEDR3LOS3pXc2xs3NER3SPR2X03P0'3PP02G03XP0FS1R2LF2sp3xs01g2lo3LFB3LOS1N3pXc2xs3HNP4ALO'3XPCS1R2LF2sp1X3xs01g2lo4SLO23LFB5NEEDR3pXc2xs1c3NER3DSX3x143PP02x23x153x164POSTS1R2LF2sp3xs01g2lo4SLO23LFB5NEEDR3pXc2xs1c3NER4LENP3PP03PSK3x142x23x153x164POSTFS1R2LF2sp3xs01g2lo4SLO23LFB5NEEDR3LOS1N3pXc2xs3HNP3NER4ALO'3XPCS2LF2sp3xs01g2lo3LFB1N3pXc2xs1c3HNP4LEN14LENP3PP03x144SEPL2x23x153x164POSTS2LF2sp1X3xs01g2lo3LFB1N3pXc2xs1c3HNP3x143PP02N13XPc2x23x153x164POSTS1R2LF2sp3xs01G1g2lo4SLO23LFB5NEEDR3pXc2xs1c3NER3PP03x143GSP2x23x153x164POSTFS2spFS1c2HCS1G1g1N3pXc3HNP3GXLS1g3NRPS2spS1g3NRPS2spFFFFFS2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xsS1X1g1N3pXc3HNP3XPcS2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xsS2LF2ra2sp1X3xs01G1g2MC3MCE3LFB3pXc2xs3SPR2X03P0'4P16'3PP02G02EP3XP0S1R2sp1G2lo4SLO25NEEDR3NER3GSPFFFFFS1N3pXcS1g1N3pXc3HNPS2sp2loFFFFFFFS1R2sp1g2lo4SLO25NEEDR3NER3PSKS2spS2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xsS1R3HIA1h2sp2lo3TOP1HSS2loFFFS2sp3SPA3SPRFFFS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERFFFFFS1R2sp2lo4SLO25NEEDR1N3pXc3NER4XLScS1R1g2MC3DI13DI21N3pXc3HNP3MC13MC23XPIFFS3pXcFS2sp2loS1g1N3pXc3HNPS1R2sp1X2lo4SLO25NEEDR3NER3DSXFFFFS2sp1g2lo1N3pXc3HNP4LOSP4XLScFFFFS1g1N3pXc4SEPLS1g1N3pXc3HNP4SEPLS1R2sp2MC2lo4SLO25NEEDR3LOS3ALO3NER3MC23DLOS1gS1R2lo3LOSS1R2sp1g2lo4SLO25NEEDR1N3pXc3HNP3NER1a2NOFFS3pXc2r04XPAL1q1r1H2H02q02H4FFFFFFFFFFFFS1R2LF2sp1X3xs01G1g2MC2lo4SLO23slo4SLO14SLO33LFB5NEEDR4DIMG3LOS1N3pXc2xs1c3HNP3NER4ALO'3PP03x143GSP3GMC3OS13MC13MC23DLO2N13XPC3XPI4XLSc3XPc6GXLbox2x23x153x164POSTFS2LF3xs01G1g3LFB2xsS2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xs2X03XALFS2LF1X3xs01g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xs2G0S2LF3xs01g3LFB1N3pXc2xs3HNPS1R2LF2sp3xs01g2MC2lo4SLO23MCE3LFB5NEEDR3LOS2xs3NER3SPR4ALO'3MC23DLOS2LF2sp3xs01g2lo3LFB2xsFS2LF1X3xs01g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS1R2LF2sp3xs01g2lo4SLO23LFB5NEEDR2xs3NERS2LF3xs01g3LFB3pXc2xsFS2LF3xs01g3LFB3pXc2xs3NP1S2LF3xs01G1g3LFB2xsS2LF2sp3xs01g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF1X3xs01g3LFB2xsS2LF1X3xs01g3LFB2xsFS2LF2ra2sp1X3xs01G1g2MC3MCE3LFB3pXc2xs3SPR2X03P0'4PAL'3PP03GAL2G02EP3XP0S2LF3xs01g3LFB2xsS2LF1X3xs01g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01g3LFB2xs". (* [comment removed for export] *)
  #[using="IMG JC GRP OSEP MCOK MIm SLO2 SLO1 SLO3 MCE LFB"] Lemma mm_addif : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.Pcntc,(15.&40.)Pc,$3.Pxra,(15.&40.)Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R17.R16.R15.R14.R13.R12.)P,(3>.R16.R15.R14.R13.R12.)P,(3?.$1;.VR,VHIA,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(1>.Vg,))P,(8.$9.(:.R15.)$;.)P,(=.(11.(1>.Vg,))(11.R16.))P,(52.(8.$9.(:.(1>.Vg,))$57.))P,(23.(=.=R16.)(=.R16.+1.))P,(=.R1>.(1=.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))))P,(=.R1>.(1?.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))Vd,))P,(=.(11.R1;.)(20.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))))(27.$1;.(28.$1;.VR,VHIA,R1?.Vmo,)$29.(2:.(2;.R19.(2<.&40.(>.(2=.&40.Vsp,)-40.))Vgp,Vtp,R18.R17.R16.(2<.&40.VX,)(2<.&40.(>.VG,+12.))(2<.&40.R1:.)R15.R14.R13.R12.R11.R10.R?.(2<.&40.(>.VG,+8.))(2<.&40.(>.(6:.(>.VG,+12.)+3.)(6;.(59.VR,))))(2<.&40.(>.(6:.VX,+3.)(6;.(59.VR,))))(2<.&40.(>.(6:.(>.VG,+8.)+3.)(6;.(59.VR,))))Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(2<.&40.+<?0>0.)Vfc,(2>.(15.&40.))R1=.(2?.$1;.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J S DPJ EO HNP PNN HC HV HF HSZ. basic_factsA hc.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    mm_open_limbs J S DPJ.
    pose proof (mm_grp_xl v f hc LBc mc dXc J EO) as GXL.
    ddestruct (OWNP1 PNN) as (NP1 & PP0 & PPAL & PBY & PSK & _).
    pose proof (ms_og _ _ _ _ _ S) as OG. pose proof (bj_aobjL _ _ _ _ _ _ _ _ _ _ (ms_bp _ _ _ _ _ S) PNN) as OPL.
    pose proof (bj_sepL _ _ _ _ _ _ _ _ _ _ (ms_bp _ _ _ _ _ S) EO PNN) as SEPL.
    ddestruct GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW). dpose GAT as (_ & GAL & G0 & EP & _).
    ddestruct OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    ddestruct MCOK as (MC1 & MC2 & MC3 & MC4 & MC5 & MC6). pose proof (art_data_lo asegs R HIA) as DLO.
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J as JX.
    pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1. clear JX.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' own.
    unfold mpi_cells in CX1, CP. rewrite EP in CP.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & XP0 & XPC & XPI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * md_n dP); (bv_unsigned sp + -64 - MPI_CORE_ADD_IF_STACK_A, bv_unsigned sp + -64)] mc) as MU; unfold MPI_CORE_ADD_IF_STACK_A in MU; pose proof (wmono_refl asegs mc) as WM.
    pose proof (aobj_crange _ _ _ _ _ _ OP) as CRP.
    pose proof (conj J I) as Jbox. pose proof (conj S I) as Sbox. pose proof (conj GXL I) as GXLbox. clear J S GXL.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk OG (G + 18) 2.
    zstep.
    replace (zx16 (Z_to_bv 64 (md_n dP))) with (Z_to_bv 64 (md_n dP)) by (unfold zx16; rewrite !unsigned_lit by (clear - NRP; lia); rewrite Z.mod_small by (clear - NRP; lia); reflexivity).
    zstep.
    pose proof (A_mpi_core_add_if_spec AL IMG) as SPC. unfold mpi_core_add_if_stmtA, mpi_core_add_if_postB, A_MPI_CORE_ADD_IF, MPI_CORE_ADD_IF_STACK_A in SPC.
    acallxA_sp (bv_unsigned sp + -64)
      (eapply SPC with (X := pXc) (A := md_p dP) (n := md_n dP) (cond := c) (lo := lo) (xs := xs) (ys := md_limbs dP);
       rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia;
       try eassumption; try reflexivity;
       first [ clear - NRP; lia
             | rewrite LEN1; exact HNP
             | rewrite LENP; clear; lia
             | clear - HC; lia
             | rewrite LENP, LEN1; clear - SEPL; lia
             | clear - XPAL; Z.div_mod_to_equations; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear - HNP NRP; lia]
             | clear - SLO2 NER NEEDR LOS; lia
             | clear - SPA SPR LOSP; lia
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NER NEEDR; lia]
             | rewrite LEN1; clear - XLSc SLO2 NER NEEDR; lia
             | rewrite LENP; clear - PSK SLO2 NER NEEDR; lia
             | match goal with |- ?g => idtac "ADDIF-PRE-LEFT:" g end ]).
    clear SPC.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-ADDIF-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with Hq : u32arr asegs m6 pXc ?l |- _ => rename Hq into XARR6; rename l into xs6 end.
    match goal with Hq : length xs6 = length xs |- _ => rename Hq into LEN6 end.
    match goal with Hq : mem_inv asegs m6 |- _ => rename Hq into MI6 end.
    match goal with Hq : stk asegs m6 lo (bv_unsigned sp + -64) |- _ => rename Hq into ST6 end.
    destruct Jbox as [J _]. destruct Sbox as [S _]. destruct GXLbox as [GXL _].
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HH6. cbn [app] in HH6.
    apply (hm_munch asegs R HIA hc LBc LF [(pXc, pXc + 4 * md_n dP); (bv_unsigned sp + -64 - MPI_CORE_ADD_IF_STACK_A, bv_unsigned sp + -64)] mc m6) in HH6; [| exact MU| exact WM| unfold MPI_CORE_ADD_IF_STACK_A; solve_w_writable].
    pose proof ST6 as ST6'. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST6' by (clear; lia).
    destruct (mm_limbs v f hc LBc mc _ cntc _ m6 xs6 J S MU WM MI6 ST6' HH6) as [J6 S6]; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
    - intros a NO. cbn [outside fst snd] in NO.
      assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 64) by (clear - NO HNP SLO2 NER NEEDR; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D].
    - cbn [disjoint_from fst snd]. split; [clear - XLSc HNP NRP LOSP; lia| split; [clear; lia| exact I]].
    - cbn [disjoint_from fst snd]. split; [clear - XPc HNP NRP; lia| split; [clear - DSX SLO2 NER NEEDR; lia| exact I]].
    - exact XARR6.
    - exact LEN6.
    - unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact CRP| clear; lia| clear - HNP NRP; lia]|].
      apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear - SLO2 NER NEEDR; lia| clear - SLO2 NER NEEDR LOSP; lia]| apply Forall_nil].
    - cbn [disjoint_from fst snd]. split; [clear - GXL HNP NRP; lia| split; [clear - GSP SLO2 NER NEEDR; lia| exact I]].
    - cbn [disjoint_from fst snd]. split; [destruct DIMG as [DI1 DI2]; clear - XPI MC1 MC2 DI1 DI2 HNP NRP; lia| split; [clear - MC2 DLO ALO LOS SLO2 NER NEEDR; lia| exact I]].
    - intros _. cbn [disjoint_from fst snd]. split; [clear - SEPL HNP NRP; lia| split; [clear - PSK SLO2 NER NEEDR; lia| exact I]].
    - cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6, S6.
      (* [comment removed for export] *)
      zstep.
      eapply mm_count; [exact J6| exact (ms_mc _ _ _ _ _ S6)| exact HV| exact HF| exact HSZ].
    all: match goal with |- ?g => idtac "ADDIF-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02:0@C24112444547.251D17433993720.251D17444351834.252D30202740417.252D30213615715.251D42633159082.252D42643779336.251D65414904706.252D65429976352.251K11420089551.251K28284592895.250K320726878.251  K33706984260.251K43070029892.250K50678622482.251K54822521893.251K61717199003.251K6599509340.251 L11416546478.3  L1175746480.1   L15263448759.7  L16073392874.2  L17645738372.1  L19630045162.2  L19892448499.9  L21877607696.8  L21890137397.14 L21892252690.9  L21892255376.7  L22658091809.0  L23100341967.215L23643762344.7  L24101795768.217L24529406258.214L24537859376.217L27631494112.8  L28003093277.2  L28270437390.4  L28513481806.7  L28515534827.14 L2975768925.2   L30202704871.5  L31834319237.7  L331342290.2    L33706525504.6  L33717624121.2  L33719186277.11 L33721172160.3  L33721174594.8  L33721664349.8  L35455353877.1  L35651110259.217L35663928186.7  L38235734261.1  L39025373398.7  L39025375828.3  L39040022996.5  L39843563160.11 L39845705021.4  L39845707711.6  L39845707711.7  L39996994530.9  L39996995936.5  L39998982853.11 L40011643616.7  L40011840149.9  L40653140888.12 L41128898453.2  L42585609932.3  L42633816569.1  L43082027553.2  L43882228554.6  L45643336298.5  L46805364568.8  L47795326910.3  L50671808483.11 L51245119830.3  L52181964255.9  L5251670778.214 L54333577394.214L54815705812.2  L54822538941.4  L54822538941.6  L55714478185.11 L55986908889.1  L60098763854.3  L60283674290.12 L61711433322.3  L6609783617.2   L66151427842.16 L66151427842.17 O13427959270.251O17159180510.251O21957337947.251O24112444547.251O2453481106.250 O27573497883.250O3348508776.251 O40755074099.251O43419437345.251O63469524774.251P11420089551.251P42591375421.251P43070029892.250Q11495966671.227Q12370813529.227Q13515859141.227Q17198776989.226Q22915297438.228Q26999370278.229Q30213615715.251Q30987168515.229Q31834646913.251Q34220676136.227Q37617138047.226Q37924141703.226Q39212284437.229Q39830861497.251Q42643779336.251Q47792156591.227Q48363247790.251Q48971481744.226Q50786263537.251Q5118570719.228 Q5118667814.229 Q5127240659.226 Q52316291654.228Q52316470523.227Q52324505011.226Q5477005154.226 Q5485174314.227 Q59703481013.227Q60441339931.227Q60511567613.229Q6143569392.227 Q67970158471.228Q68049981125.229Q9530130738.226 00000101@02X03f04h05S06507R08f08g09W0:a0;n0;o0<n0>60?80@B0@C0@G0@Z0@a0@e0@l0A00A10A20A30A40A50AW0Aj0BL0CP0DT0E20E30E40E50E60E=0EJ0EQ0ER0ES0ET0EU0EV0EW0F50F90F[0G00G40G50G60GB0GC0GD0G\0H40H50H60H70H80H[0IA0IB0IC0IH0II0IP0I]0J;0J<0J=0J>0J[0KD0LH0LI0LW0Li0MT0MW0Ma0NJ0NK0NL0Nh0Ni0Nj0Nk0Nl0Nm0Nn0No0O00O10O20O30O40QT0QU0Qh0RQ0RR0Re0S80SN0Si0Tm0UD0UE0UX0Uk0V>0Vf0W;0W<0WU0Wh0X<0XO0Xb0Y50YH0Y[0Yn0ZA0ZT0ZU0[]0[n0\A0\T0\g0]8FS1R3HIA1h2LF2ra2sp1X3xs01G1g2MC3MCE3LFB3TOP2hc3pXc2xs3SPR2X03P0'3PP02G03HT13XP0S1R3HIA1h2LF2ra2sp1X3xs01G1g2MC3MCE3LFB3TOP2hc3pXc2xs3SPR2X03P0'3PP02G03HT13XP03xl64LEN6S2LF2ra2sp1X3xs01G1g2MC3MCE3LFB1N3pXc2xs3HNP3SPR2X03P0'3PP02G02N13XP03xl64LEN6S2LF2ra2sp1X3xs01G1g2MC3MCE3LFB1N3pXc2xs3HNP3SPR2X03P0'3PP02G03XP0S2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xs3xl64LEN6S2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xsS1R2LF2ra2sp1X3xs01G1g2MC2lo4SLO23MCE3LFB5NEEDR3LOS3pXc2xs3NER3SPR2X03P0'3PP02G03XP03xl64LEN6S1R2LF2ra2sp1X3xs01G1g2MC2lo4SLO23MCE3LFB5NEEDR3LOS3pXc2xs3NER3SPR2X03P0'3PP02G03XP0FS1R2LF2sp3xs01g2lo3LFB3LOS1N3pXc2xs3HNP4ALO'3XPCS1R2LF2sp1X3xs01g2lo4SLO23LFB5NEEDR3pXc2xs3NER3DSX3x143PP02x23x153x164POSTS1R2LF2sp3xs01g2lo4SLO23LFB5NEEDR3pXc2xs3NER4LENP3PP03PSK3x142x23x153x164POSTFS1R2LF2sp3xs01g2lo4SLO23LFB5NEEDR3LOS1N3pXc2xs3HNP3NER4ALO'3XPCS2LF2sp3xs01g2lo3LFB1N3pXc2xs3HNP4LEN14LENP3PP03x144SEPL2x23x153x164POSTS2LF2sp1X3xs01g2lo3LFB1N3pXc2xs3HNP3x143PP02N13XPc2x23x153x164POSTS1R2LF2sp3xs01G1g2lo4SLO23LFB5NEEDR3pXc2xs3NER3PP03x143GSP2x23x153x164POSTFS2spS1G1g1N3pXc3HNP3GXLS1g3NRPS2spS1g3NRPS2spFFFFSS2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xsS1X1g1N3pXc3HNP3XPcS2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xsS2LF2ra2sp1X3xs01G1g2MC3MCE3LFB3pXc2xs3SPR2X03P0'4P16'3PP02G02EP3XP0S2LF2ra2sp1X3xs01G1g2MC3MCE3LFB3pXc2xs3SPR2X03P0'4P16'3PP02G02EP3XP0S1R2sp1G2lo4SLO25NEEDR3NER3GSPFFFFS1N3pXcS1g1N3pXc3HNPS2sp2loFFFFFFS1R2sp1g2lo4SLO25NEEDR3NER3PSKS2spS2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xsS1R3HIA1h2sp2lo3TOP1HS2loFFS2sp3SPA3SPRFFS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERFFFFS1R2sp2lo4SLO25NEEDR1N3pXc3NER4XLScS1R1g2MC3DI13DI21N3pXc3HNP3MC13MC23XPIFFS3pXcFS2sp2loS1g1N3pXc3HNPS1R2sp1X2lo4SLO25NEEDR3NER3DSXFFFS2sp1g2lo1N3pXc3HNP4LOSP4XLScS2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xs2X03X16S2LF2ra2sp1X3xs01G1g2MC3MCE3LFB3pXc2xs3SPR2X03P0'4P16'3PP02G02EP3XP0FS1g1N3pXc4SEPLS1g1N3pXc3HNP4SEPLS1R2sp2MC2lo4SLO25NEEDR3LOS3ALO3NER3MC23DLOS1gS1R2lo3LOSS1R2sp1g2lo4SLO25NEEDR1N3pXc3HNP3NER1a2NOFFS3pXc2r04XPAL1q1r1H2H02q02H4FFFFFFFFFFFFS1R2LF2sp1X3xs01G1g2MC2lo4SLO23slo4SLO14SLO33LFB5NEEDR4DIMG3LOS1N3pXc2xs3HNP3NER4ALO'3PP03x143GSP3GMC3OS13MC13MC23DLO2N13XPC3XPI4XLSc3XPc6GXLbox2x23x153x164POSTFS2LF3xs01G1g3LFB2xsS2LF2ra2sp1X3xs01G1g2MC3LFB3pXc2xs2X03XALFS2LF1X3xs01g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xs2G0S2LF3xs01g3LFB1N3pXc2xs3HNPS1R2LF2sp3xs01g2MC2lo4SLO23MCE3LFB5NEEDR3LOS2xs3NER3SPR4ALO'3MC23DLOS2LF2sp3xs01g2lo3LFB2xsFS2LF1X3xs01g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS1R2LF2sp3xs01g2lo4SLO23LFB5NEEDR2xs3NERS2LF3xs01g3LFB3pXc2xsFS2LF3xs01g3LFB3pXc2xs3NP1S2LF3xs01G1g3LFB2xsS2LF2sp3xs01g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF1X3xs01g3LFB2xsS2LF1X3xs01g3LFB2xsFS2LF2ra2sp1X3xs01G1g2MC3MCE3LFB3pXc2xs3SPR2X03P0'4PAL'3PP03GAL2G02EP3XP0S2LF3xs01g3LFB2xsS2LF1X3xs01g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01G1g3LFB2xsS2LF3xs01g3LFB2xs". (* [comment removed for export] *)
  #[using="IMG JC GRP OSEP MCOK MIm SLO2 SLO1 SLO3 MCE LFB"] Lemma mm_sub : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.Pcntc,(15.&40.)Pxra,(15.&40.)Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pxa0,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pxs2,(15.&40.)Pxs3,(15.&40.)Pxs5,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R1:.R19.R18.R17.R16.R15.)P,(3>.R19.R18.R17.R16.R15.)P,(3?.$1;.VR,VHIA,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(1>.Vg,))P,(8.$9.(:.R18.)$;.)P,(=.(11.(1>.Vg,))(11.R19.))P,(52.(8.$9.(:.(1>.Vg,))$57.))P,(=.R20.(1=.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))))P,(=.R20.(1?.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))Vd,))P,(=.(11.R1=.)(20.VnX,(11.VdA,)(11.VdB,)(11.(1>.Vg,))))(27.$1;.(28.$1;.VR,VHIA,R21.Vmo,)$29.(2:.(2;.R1<.(2<.&40.(>.(2=.&40.Vsp,)-40.))Vgp,Vtp,R1;.R1:.R19.(2<.&40.VX,)(2<.&40.VG,)R18.R17.R16.R15.R14.R13.R12.R11.R10.(2<.&40.(6;.(59.VR,)))R?.R>.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(2<.&40.+<?094.)Vfc,(2>.(15.&40.))R1?.(2?.$1;.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J S DPJ EO HNP PNN HV HF HSZ. basic_factsA hc.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    mm_open_limbs J S DPJ.
    pose proof (mm_grp_xl v f hc LBc mc dXc J EO) as GXL.
    ddestruct (OWNP1 PNN) as (NP1 & PP0 & PPAL & PBY & PSK & _).
    pose proof (ms_og _ _ _ _ _ S) as OG. pose proof (bj_aobjL _ _ _ _ _ _ _ _ _ _ (ms_bp _ _ _ _ _ S) PNN) as OPL.
    pose proof (bj_sepL _ _ _ _ _ _ _ _ _ _ (ms_bp _ _ _ _ _ S) EO PNN) as SEPL.
    ddestruct GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW). dpose GAT as (_ & GAL & G0 & EP & _).
    ddestruct OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    ddestruct MCOK as (MC1 & MC2 & MC3 & MC4 & MC5 & MC6). pose proof (art_data_lo asegs R HIA) as DLO.
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J as JX.
    pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1. clear JX.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' own.
    unfold mpi_cells in CX1, CP. rewrite EP in CP.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & XP0 & XPC & XPI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * md_n dP); (bv_unsigned sp + -64 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -64)] mc) as MU; unfold MPI_CORE_SUB_STACK_A in MU; pose proof (wmono_refl asegs mc) as WM.
    pose proof (aobj_crange _ _ _ _ _ _ OP) as CRP.
    pose proof (conj J I) as Jbox. pose proof (conj S I) as Sbox. pose proof (conj GXL I) as GXLbox. clear J S GXL.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OG (G + 18) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 (md_n dP))) with (Z_to_bv 64 (md_n dP)) by (unfold zx16; rewrite !unsigned_lit by (clear - NRP; lia); rewrite Z.mod_small by (clear - NRP; lia); reflexivity).
    zstep. zstep.
    pose proof (A_mpi_core_sub_spec AL IMG) as SPC. unfold mpi_core_sub_stmtA, mpi_core_sub_postA, A_MPI_CORE_SUB, MPI_CORE_SUB_STACK_A in SPC.
    acallxA_sp (bv_unsigned sp + -64)
      (eapply SPC with (X := pXc) (A := pXc) (B := md_p dP) (n := md_n dP) (lo := lo) (xs := xs) (ys := xs) (zs := md_limbs dP);
       rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia;
       try eassumption; try reflexivity;
       first [ apply u32arr_ro; exact XARR
             | left; split; reflexivity
             | right; rewrite LENP, LEN1; clear - SEPL; lia
             | clear - NRP; lia
             | rewrite LEN1; exact HNP
             | rewrite LENP; clear; lia
             | rewrite LENP, LEN1; clear - SEPL; lia
             | clear - XPAL; Z.div_mod_to_equations; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear - HNP NRP; lia]
             | clear - SLO2 NER NEEDR LOS; lia
             | clear - SPA SPR LOSP; lia
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NER NEEDR; lia]
             | rewrite LEN1; clear - XLSc SLO2 NER NEEDR; lia
             | rewrite LENP; clear - PSK SLO2 NER NEEDR; lia
             | match goal with |- ?g => idtac "CSUB-PRE-LEFT:" g end ]).
    clear SPC.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-CSUB-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with Hq : u32arr asegs m6 pXc ?l |- _ => rename Hq into XARR6; rename l into xl6 end.
    match goal with Hq : length xl6 = length xs |- _ => rename Hq into LEN6 end.
    match goal with Hq : mem_inv asegs m6 |- _ => rename Hq into MI6 end.
    match goal with Hq : stk asegs m6 lo (bv_unsigned sp + -64) |- _ => rename Hq into ST6 end.
    destruct Jbox as [J _]. destruct Sbox as [S _]. destruct GXLbox as [GXL _].
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HH6. cbn [app] in HH6.
    apply (hm_munch asegs R HIA hc LBc LF [(pXc, pXc + 4 * md_n dP); (bv_unsigned sp + -64 - MPI_CORE_SUB_STACK_A, bv_unsigned sp + -64)] mc m6) in HH6; [| exact MU| exact WM| unfold MPI_CORE_SUB_STACK_A; solve_w_writable].
    pose proof ST6 as ST6'. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST6' by (clear; lia).
    destruct (mm_limbs v f hc LBc mc _ cntc _ m6 xl6 J S MU WM MI6 ST6' HH6) as [J6 S6]; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
    - intros a NO. cbn [outside fst snd] in NO.
      assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 64) by (clear - NO HNP SLO2 NER NEEDR; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D].
    - cbn [disjoint_from fst snd]. split; [clear - XLSc HNP NRP LOSP; lia| split; [clear; lia| exact I]].
    - cbn [disjoint_from fst snd]. split; [clear - XPc HNP NRP; lia| split; [clear - DSX SLO2 NER NEEDR; lia| exact I]].
    - exact XARR6.
    - exact LEN6.
    - unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact CRP| clear; lia| clear - HNP NRP; lia]|].
      apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear - SLO2 NER NEEDR; lia| clear - SLO2 NER NEEDR LOSP; lia]| apply Forall_nil].
    - cbn [disjoint_from fst snd]. split; [clear - GXL HNP NRP; lia| split; [clear - GSP SLO2 NER NEEDR; lia| exact I]].
    - cbn [disjoint_from fst snd]. split; [destruct DIMG as [DI1 DI2]; clear - XPI MC1 MC2 DI1 DI2 HNP NRP; lia| split; [clear - MC2 DLO ALO LOS SLO2 NER NEEDR; lia| exact I]].
    - intros _. cbn [disjoint_from fst snd]. split; [clear - SEPL HNP NRP; lia| split; [clear - PSK SLO2 NER NEEDR; lia| exact I]].
    - cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6, S6.
      match goal with Ec : ?xc = Z_to_bv 64 ?cc, Hc : 0 <= ?cc <= 1 |- _ => subst xc;
        eapply (mm_addif v f hc LBc m6 _ cntc cc); [exact J6| exact S6| exact DPJ| reflexivity| exact HNP| exact PNN| exact Hc| exact HV| exact HF| exact HSZ] end.
    all: match goal with |- ?g => idtac "SUB-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L32962794368.8 L33142917281.10L3551965570.8  L35663928186.7 L42439184616.3 L44972859269.8 L60098763854.3 L64685646146.7 L66566358642.8 00000M01201O01d02002M02W03003LS2sp1G2lo3wlo3whi3HLO3HHI3GSPS1R2MC2lo3LOS3wlo3whi3HLO3ALO3MC23DLOS2sp1G2lo3wlo3whi3HLO3HHI3GSPS1R3HIA1h2sp2lo3TOP1HS1R3slo4SLO1S2sp1g2lo3wlo3whi3HLO3HHI3PSKS1R2lo3LOSS1R3HIA1h2sp3slo4TOPo3HT0S2sp2lo3wlo3whi3HLO3HHI1x2Hx". (* [comment removed for export] *)
  #[using="IMG MT d JC GRP MCOK SLO1"] Lemma mm_scratch : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.Pcntc,(15.&40.)Pwlo,$3.Pwhi,$3.Pm',P,(15.&40.)(16.(15.&8.))P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R:.R9.R8.R7.R6.R5.)P,(3>.R9.R8.R7.R6.R5.)P,(3?.$1;.VR,VHIA,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(1>.Vg,))P,(33.(34.(35.$3.$3.)(36.$3.$3.R6.R5.)(32.(35.$3.$3.)))R9.R4.)P,(37.$1;.R:.R5.)P,(38.$1;.R6.)P,(41.$1;.R7.Vlo,(40.(2=.&40.Vsp,)+40.))P,(39.$1;.VR,VHIA,R?.R>.VLF,R8.)P,(=.Vlo,R;.)P,(=.R;.(40.(2=.&40.Vsp,)+40.))(23.(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R14.R13.R12.R11.R;.(1<.(54.R?.)(68.R?.)(11.R?.)(?.R?.)(66.R?.)(69.R?.)(:.R?.)))(3>.R12.R11.R;.(1<.(54.R?.)(68.R?.)(11.R?.)(?.R?.)(66.R?.)(69.R?.)(:.R?.))R>.))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until m'. intros J S DPJ MU WM MI' ST' HH' HLO HHI. basic_factsA hc.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    pose proof (bja_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC (g_P g) DPJ _ _ _ _ (ms_bp _ _ _ _ _ S)) as (P0' & P16' & PAL' & LENP & NRP & PSS & OWNP0 & OWNP1).
    pose proof JC as [_ _ _ _ HHo _ _ _ _ _ _ _ TOPo _ _].
    destruct S as [SMC SGT SOG SBP SSS].
    ddestruct GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW). dpose GAT as (_ & _ & _ & EP & _).
    ddestruct MCOK as (MC1 & MC2 & MC3 & MC4 & MC5 & MC6). pose proof (art_data_lo asegs R HIA) as DLO.
    pose proof (xa_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HS1.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    assert (WC : w_client (hcs asegs R HIA hc) [(wlo, whi)]).
    { unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros x Hx. apply SCS. clear - Hx HLO HHI. lia. }
    split.
    - eapply (xa_scratch asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC); eassumption.
    - constructor.
      + eapply rw_cells_transport; [exact SMC| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. split; [clear - MC2 DLO ALO LOS HLO; lia| exact I].
      + eapply rw_cells_transport; [exact SGT| exact MU| exact WM|]. unfold grp_tail_cells. cbn [cells_size csize Nat.add disjoint_from fst snd]. split; [clear - GSP HLO HHI; lia| exact I].
      + eapply (aobj_munch asegs AL _ (hcs_ok asegs R HIA hc) [(wlo, whi)] mc m'); [exact WC| exact MU| exact SOG].
      + assert (B' : BJA asegs R HIA LF sp dP hc LBc m' dXc).
        { eapply bja_munch; first [exact J | exact SBP | exact MU | exact WM | exact WC | idtac].
          - rewrite EP. cbn [disjoint_from fst snd]. split; [clear - GSP HLO HHI; lia| exact I].
          - intros PN. ddestruct (OWNP1 PN) as (_ & _ & _ & _ & PSK & _). cbn [disjoint_from fst snd]. split; [clear - PSK HLO HHI; lia| exact I]. }
        destruct B' as [BA BS BL BO BOL]. constructor; cbn [md_own md_p md_n]; assumption.
      + eapply (sshad_munch asegs AL (hcs asegs R HIA hc) [(wlo, whi)] mc m'); [exact (hcs_ok asegs R HIA hc)| exact WC| | exact MU| exact WM| exact SSS].
        eapply crange_sub; [exact (hcs_stack asegs R HIA hc)| clear - SLO1; lia|].
        rewrite (xa_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J). pose proof (hm_top asegs R HIA h LB LF m HHo) as HT0. clear - TOPo HT0. lia.
    all: match goal with |- ?g => idtac "SCRATCH-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01R0@C17025492443.230D20701942042.282D20701942042.283D20701942042.286D20701942042.287D21475581589.285D51036099192.280D51036099192.284D56475227919.230D59441450494.284D60109446735.230D7820960534.282 D7820960534.283 D7820960534.286 D7820960534.287 D8385136658.281 K36719207456.230L1175746480.1   L13449382718.5  L14436300032.3  L14857815666.9  L15697236124.4  L1579419076.5   L17645738372.1  L18240307034.2  L18293330070.10 L19095841334.8  L21824241726.2  L21877607696.8  L21892288304.10 L23258591603.230L23305025156.0  L23792326817.0  L24949496458.10 L26825993283.6  L27379387855.15 L28036885525.8  L29010569984.285L35663928186.7  L36715738693.2  L37737240688.5  L38235734261.1  L38271492189.7  L39025343476.8  L39040022996.5  L39845737629.8  L40290687782.1  L41497933390.9  L42287188496.285L43882228554.6  L45595919683.8  L49633402408.3  L49994140762.10 L52155962762.3  L5261871668.3   L56066579390.6  L56066643508.10 L57672453661.5  L57835863895.5  L58517950242.6  L59308660947.3  L59308660947.5  L60098763854.3  L61057171266.9  L62645706309.229L62948672147.2  L66022206678.1  L66151426447.10 L66151427842.16 L7143015064.231 L7717397652.14  L8481888824.3   O17025492443.230O19420042482.230P14853559319.230P36719207456.230P49988094288.284Q14290048923.235Q16192523259.234Q16192582724.233Q30985398804.285Q30987168515.210Q30987329589.249Q36438237060.230Q38248387216.230Q38398320517.233Q41595424392.234Q43879899724.230Q43957738831.235Q44741466490.282Q44741466490.283Q46916161383.233Q49988094288.284Q5166018377.234 Q5166159483.235 Q63583527707.234Q66877350506.234Q7404148431.234 00000101F01G02\02]02^02_02`03e04H05005105[05\06F06G06H06L06\06e06f07807H07L07Q07X07e07k07l07m08P08Q08R09309K0::0:P0:Q0:f0:g0;70;;0;O0;P0;\0<40<70<R0=50=<0=T0=^0=_0=m0>70>K0>b0>l0?<0?S0?^0?_0?i0@F0@l0A40A80AI0Ac0BF0C30C:0C;0C<0DB0DC0EI0F@0FY0G20H40I00J20J\0K20KK0Kd0L=0LV0LW0LX0M10M20MK0Md0N[0O40OMFS2LF2ra2sp1X2sX2nX2pX3xs04padX4ownX1G1g3LFB3dXc3SPR2X03XAD2G05Bmodp2ws3AD13GTB3x132HxFS2LF2ra2sp1X2sX2nX2pX3xs04padX4ownX1G1g3LFB3dXc3SPR2X03XAD2G05Bmodp2ws3AD13GTB3x132HxFFFFS1R3HIA1h2LF2ra2sp1X3xs01G1g2lo3LFB3TOP2hc3dXc3SPR2X02G05Bmodp2ws3HT1S2LF2ra2sp1X3xs01G1g3LFB3dXc2ws3GTBS1R2LF2ra2sp1X3xs01G1g2lo3LFB3LOS3dXc2wsFS2LF2ra2sp1X3xs01G1g3LFB3dXc2ws3GTB3x132HxFS2LF2ra2sp1X3xs01G1g3LFB3dXc2ws3GTB3x132HxFFS2spS2nX2dA2dB1g3SZAS1g5BmodpFS2LB4C24H3LBc4C24dS2nX2dA2dB1g3SZAS2spS3dX6S2sp2loS2sp1X2lo3DSXS1d2D0FFS2LF2ra2sp1X3xs01G1g3LFB3dXc2ws3GTBSSS2nX2dA2dB1g3dXc3HSZ2ws1K3KGE3LNPS1R2sp2lo4SLO25NEEDR3NERS1R3HIA1h2nX2dA2dB1g3BUD1v2hc2HV1K3HV14KPHI3PNNS2nX2dA2dB1g1v2HV1H2H0FS1R3HIA1h2sp2lo3TOP1HFS1g2ws1K3KGE3LNPS2loS1g2ws1K3KGE3dX63LNPFS2sp3SPA3SPRS1R2sp2lo4SLO25NEEDR3NERS1XS2nX2dA2dB1g1d2D01f2HF4FRNNS2LF2ra2sp1X3xs01G1g3LFB3dXc2ws3GTBS2sp2loS2nX2dA2dB1g1d1f2HF4FRNNS2ws1K3KGEFS1g5Bmodp4EVENS1X2X03X16S2nX2dA2dB1g3dXc3HSZS2nX2dA2dB1g3dXc3HSZ2wsS2nX2dA2dBS1R3HIA1h2sp3TOPS1R2sp2lo4SLO23STK4STKBS3dXc2N12E0FS1R2lo3LOSS2nX2dA2dB1g1v2HV1K4KPHI4PNNqS2LF2ra2sp1X3xs01G1g3LFB3dXc2G02ws3GTBS2LF3LFBS2spS1r3GRr2r02KR1q1HS2sp2r03SPA1q1r1H2H02q02H4S2LF2ra2sp1X3xs01G1g3LFB3dXc2ws3GTBS1R3HIA1h2nX2dA2dB1g1d4BUDF1f2hc2HF4HFR14FRNNS1K3dX6FFS2LF2sp1X2sX2nX2pX3xs04padX4ownX1g2lo3LFB3dXc3GNZ3DSX3XAD5Bmodp2ws3AD1FS1R2LF2sp1X3xs01G1g2lo4SLO23LFB5NEEDR3FSZ3dXc3GNZ3NER3DSX5Bmodp2ws3GTBS2LF2ra2sp1X3xs01G1g3LFB3dXc3SPR2X03GAL2G05Bmodp2ws3GTBS2LF3xs01G3LFB3dXc2ws3GTBS2LF3xs01G3LFB3dXc2ws3GTBS1R2LF2sp3xs01G2lo4SLO23LFB5NEEDR3LOS3dXc3NER3SPR4ALO'4ACP'2ws3GTBS1R2LF2sp3xs02lo4SLO23LFB5NEEDR3LOS3dXc3NER3SPR4ALO'4ACP'2wsS1R2LF2sp3xs01G2lo4SLO23LFB5NEEDR3LOS3dXc3NER3SPR4ALO'4ACP'2ws3GTBS1R2LF2sp3xs02lo4SLO23LFB5NEEDR3dXc3NER2wsS2LF3xs02lo3LFB3dXc2wsS2LF3xs01G3LFB3dXc2ws3GTBS2LF3xs01G3LFB3dXc2ws3GTBS2LF2sp3xs02lo3LFB3dXc2wsS2LF3xs01G3LFB3dXc2ws3GTBFFS2LF3xs01G3LFB3dXc2ws3GTBFS2LF3xs01G3LFB3dXc2ws3GTBS2LF3xs01G3LFB3dXc2ws3GTBS2LF2ra2sp1X3xs01G1g3LFB3dXc3SPR2X03GAL2G05Bmodp2ws3GTBS2LF3xs01G3LFB3dXc2ws3GTBS2LF3xs01G3LFB3dXc2ws3GTB". (* [comment removed for export] *)
  #[using="IMG HTAB JC TPV UWX D0 GRP OSEP MCOK MIm SLO2 SLO1 SLO3 MCE BUD BUDF C24H LFB SZA"] Lemma mm_red2 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.Pcntc,(15.&40.)Pxra,(15.&40.)Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pxa0,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pxs5,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R18.R17.R16.R15.R14.R13.)P,(3>.R17.R16.R15.R14.R13.)P,(3?.$1;.VR,VHIA,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(1>.Vg,))P,(52.(8.$3.(6<.Vg,)=))P,(=.R1<.(5=.(11.VdA,)(11.VdB,)))P,(=.R1<.(5>.Vd,))P,(=.(11.R19.)(5?.VnX,(11.VdA,)(11.VdB,)))(27.$1;.(28.$1;.VR,VHIA,R1=.Vmo,)$29.(2:.(2;.R18.(2<.&40.(>.(2=.&40.Vsp,)-40.))Vgp,Vtp,R17.R16.R15.(2<.&40.VX,)(2<.&40.VG,)R14.R13.R12.R11.R10.R?.R>.R=.(2<.&40.(>.VG,+90.))(2<.&40.(6;.(59.VR,)))(2<.&40.(>.(6:.(>.VG,+90.)+3.)(6;.(59.VR,))))R<.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(2<.&40.+<?054.)Vfc,(2>.(15.&40.))R1;.(2?.$1;.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J S DPJ GNZ HV HF HSZ. basic_factsA hc.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    ddestruct (mm_opX v f hc LBc mc dXc (bv_unsigned sp + -64) J ltac:(clear - SLO2 NER NEEDR; lia)) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof (mm_cnt24 v f hc LBc mc dXc J) as C24c.
    dpose GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW). dpose GAT as (_ & GAL & G0 & EP & _ & _ & _ & _ & _ & _ & _ & _ & _ & GREST).
    ddestruct GREST as (_ & Bpb & _ & _ & Bmodp & _ & _ & _ & _ & _ & _ & _ & GMO).
    destruct GMO as [Z0 | (lp & ws & INMT & ELP & EWS & OWNP & SGP)]; [exfalso; exact (GNZ Z0)|].
    destruct (HTAB _ _ _ INMT) as (EVEN & K & STK & KGE & STKB & RED).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp + -64)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    pose proof (conj S I) as Sbox. pose proof (conj J I) as Jbox. clear J S.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPC. unfold mpi_bitlen_stmtA, mpi_query_stmtA, mpi_query_postA, A_MPI_BITLEN_Q in SPC.
    acallxA_sp (bv_unsigned sp + -64)
      (eapply SPC with (LB := LBc) (dX := dXc) (v := bv_unsigned xa1) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia;
       try eassumption; try reflexivity;
       first [ exact I
             | rewrite XAD; exact OX1
             | rewrite XAD; reflexivity
             | symmetry; apply Z_to_bv_bv_unsigned
             | intros EO; ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & _ & _ & _ & _ & XP0 & _); exact XP0
             | intros N1; assert (ON : md_own dXc <> LNull) by (intros C; destruct (OWN0 C) as [_ E0]; clear - E0 N1; lia);
               ddestruct (OWN1 ON) as (_ & _ & _ & _ & _ & _ & _ & _ & OPq & _); exact OPq
             | intros N1; assert (ON : md_own dXc <> LNull) by (intros C; destruct (OWN0 C) as [_ E0]; clear - E0 N1; lia);
               destruct (XLSq ON) as [XL|XL]; [left; exact XL| right; exact XL]
             | rewrite XAD; clear - DSX SLO2 NER NEEDR; lia
             | clear - SLO2 NER NEEDR LOS LO0; lia
             | clear - SPA SPR LOSP; lia
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NER NEEDR; lia]
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPC.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with Hq : mem_inv asegs m6 |- _ => rename Hq into MI6 end.
    match goal with Hq : stk asegs m6 lo (bv_unsigned sp + -64) |- _ => rename Hq into ST6 end.
    match goal with Hq : HM asegs R HIA hc LBc LF m6 |- _ => rename Hq into HH6 end.
    destruct Jbox as [J _]. destruct Sbox as [S _].
    pose proof ST6 as ST6'. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST6' by (clear; lia).
    destruct (mm_scratch v f hc LBc mc dXc cntc lo (bv_unsigned sp + -64) m6 J S DPJ MU WM MI6 ST6' HH6 ltac:(clear; lia) ltac:(clear; lia)) as [J6 S6].
    set (dX6 := mkMPD (md_addr dXc) (md_sg dXc) (md_n dXc) (md_p dXc) (md_limbs dXc) (md_pad dXc) (md_own dXc)) in *.
    pose proof (ms_og _ _ _ _ _ S6) as OG6. pose proof (ms_gt _ _ _ _ _ S6) as GT6. unfold grp_tail_cells in GT6.
    pose proof (rw_cells_bound _ _ _ _ GT6) as GTB. cbn [cells_size csize Nat.add] in GTB.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KB.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      lazymatch goal with |- _ (MS ?RR _ _ _ _ _ _) => let v0 := getx RR 10%positive in replace v0 with (Z_to_bv 64 (-20352)) by (apply bv_eq; vm_compute; reflexivity) end.
      assert (FRNN : 0 <= mod_mpi_FRn (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g)) d) by (apply mod_mpi_FRn_nonneg; [unfold mul_mpi_nz; clear - SZA; lia| exact D0]).
      eapply mm_fail; [exact J6| exact (ms_mc _ _ _ _ _ S6)| clear; lia
                      | unfold mm_PHIn, red_PHIn; pose proof (grow_PHI_nonneg (2 * md_n (g_P g)) ltac:(clear - SZA; lia)); pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g)) ltac:(unfold mul_mpi_nz; clear - SZA; lia) ltac:(clear - SZA; lia)); clear - HV H H0; lia
                      | unfold mm_FRn, red_FRn, calls_FR, fr_charge; clear - HF D0 FRNN; lia
                      | unfold dX6; cbn [md_n]; unfold mm_nz; clear - HSZ; lia].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      rewrite (ret_pc_even (g_modp g)) by (clear - Bmodp EVEN; lia).
      ddestruct (mm_opX v f hc LBc m6 dX6 (bv_unsigned sp + -64) J6 ltac:(clear - SLO2 NER NEEDR; lia)) as (XM6 & XNS6 & XAD6 & XOS6 & XCR6 & XCRL6 & XWR6 & XLS6 & XAO6 & XIM6).
      pose proof (mm_cnt24 v f hc LBc m6 dX6 J6) as C24d.
      assert (KPHI : grow_PHI K <= red_PHIn (md_n (g_P g))).
      { unfold red_PHIn. apply grow_PHI_mono.
        assert (LNP : Z.of_nat (length ws) = md_n (g_P g)) by (rewrite <- EWS; dpose GAT as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & LP & _) & _); exact LP).
        clear - KGE LNP. lia. }
      pose proof (conj S6 I) as Sbox. pose proof (conj J6 I) as Jbox.
      clear MU WM.
      eapply aevtA_call.
      { intros mo1 [HK1 MF1]. unfold ecp_reducer_stmtA in RED.
        eapply RED with (h := hc) (LB := LBc) (LF := LF) (dX := dX6) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia.
        - exact HH6.
        - exact HK1.
        - clear - LFB; lia.
        - exact XM6.
        - exact XNS6.
        - exact XWR6.
        - exact XLS6.
        - exact ST6.
        - exact LOS.
        - clear - SLO2 STKB; lia.
        - rewrite HT1; clear - TOP; lia.
        - clear - SPA; Z.div_mod_to_equations; lia.
        - exact TPV.
        - exact MI6.
        - reflexivity.
        - exact XAO6.
        - pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g)) ltac:(unfold mul_mpi_nz; clear - SZA; lia) ltac:(clear - SZA; lia)) as PNN.
          unfold mm_PHIn in BUD. clear - BUD HV HV1 KPHI PNN. lia.
        - eapply uw_obj_uwc; [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear; lia].
        - rewrite XAD6; exact UWX.
        - assert (FRNN : 0 <= mod_mpi_FRn (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g)) d) by (apply mod_mpi_FRn_nonneg; [unfold mul_mpi_nz; clear - SZA; lia| exact D0]).
          unfold mm_FRn in BUDF. clear - BUDF HF HFR1 FRNN. lia.
        - unfold C24_ECP_RED, C24_ECP_MUL_MOD in *. clear - C24d C24H. lia.
        - rewrite XAD6; reflexivity. }
      (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
      ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & GR).
      injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2, HP2 by qlia. rewrite XAD6 in HP2.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      presA_transport HP2.
      destruct Sbox as [S0 _]. destruct Jbox as [J0 _].
      assert (BK : binop_keep LBc dX6 dX2).
      { ddestruct GR as [[(_ & _ & Hn & Hp & _)|[_ ->]] [FRq _]]; destruct OUT2 as (EA & _).
        - split; [exact EA|]. split; [exact Hp|]. split; [exact FRq|]. rewrite Hn. clear; lia.
        - split; [reflexivity|]. split; [reflexivity|]. split; [exact FRq|]. clear; lia. }
      pose proof ST2 as ST2'. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST2' by (clear; lia).
      destruct (mm_step v f hc LBc m6 dX6 cntc m2 h2 LB2 dX2 (bv_unsigned sp + -64) (grow_PHI K) (red_FRn d) J0 S0 DPJ
                  ltac:(clear - SLO2 NER NEEDR; lia) ltac:(apply grow_PHI_nonneg; clear - KGE; lia) ltac:(unfold red_FRn, calls_FR, fr_charge; clear - D0; lia)
                  MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as [J2 S2].
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
      pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
      assert (PNNq : 0 <= mod_mpi_PHIn (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g))) by (apply mod_mpi_PHIn_nonneg; [unfold mul_mpi_nz; clear - SZA; lia| clear - SZA; lia]).
      assert (FRNN : 0 <= mod_mpi_FRn (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g)) d) by (apply mod_mpi_FRn_nonneg; [unfold mul_mpi_nz; clear - SZA; lia| exact D0]).
      assert (BV2 : v + grow_PHI K <= PHI0) by (unfold mm_PHIn; clear - HV KPHI PNNq; lia).
      assert (BF2 : f + red_FRn d <= FR0) by (unfold mm_FRn; clear - HF FRNN; lia).
      assert (LNP : Z.of_nat (length ws) = md_n (g_P g)) by (rewrite <- EWS; dpose GAT as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & LP & _) & _); exact LP).
      (* [comment removed for export] *)
      zstep. if_cases KR; zify_cond KR.
      + (* [comment removed for export] *)
        ddestruct GR as (GR1 & _ & GRr).
        assert (SZ2 : md_n dX2 <= SZ0).
        { unfold mm_nz. destruct GR1 as [(_ & _ & Hn & _)|[_ ->]]; [rewrite Hn| ]; unfold dX6; cbn [md_n]; clear - HSZ KGE LNP; lia. }
        eapply mm_fail; [exact J2| exact (ms_mc _ _ _ _ _ S2)| exact GRr| exact BV2| exact BF2| exact SZ2].
      + ddestruct GR as (GR1 & _ & GRr).
        destruct GR1 as [(_ & _ & Hn & _ & HO)|[RF _]]; [| exfalso; subst r; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; discriminate KR].
        assert (R0 : r = 0) by (clear - KR GRr; Z.div_mod_to_equations; lia). subst r.
        assert (SZ2 : md_n dX2 <= SZ0) by (unfold mm_nz; rewrite Hn; unfold dX6; cbn [md_n]; clear - HSZ KGE LNP; lia).
        eapply mm_sub; [exact J2| exact S2| exact DPJ| exact HO| rewrite Hn; clear - KGE LNP; lia| rewrite OWNP; discriminate| exact BV2| exact BF2| exact SZ2].
    all: match goal with |- ?g => idtac "RED2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_CI.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0_CI.
  Hypothesis NSM : 0 <= arl_need_smalloc R.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00o0@C17025492443.232D56475227919.232D60109446735.232K36719207456.232K51736254456.232L1175746480.1   L12492594119.1  L13449382718.5  L1579419076.5   L17009103649.0  L17645738372.1  L18293330070.10 L19095841334.8  L21877607696.8  L21890651493.5  L21892288304.10 L23305025156.0  L26825993283.6  L26912816584.5  L28036885525.8  L29061603126.205L29074168500.208L35663928186.7  L36715738693.2  L38235734261.1  L38691415991.0  L39025343476.8  L39027518260.1  L39040022996.5  L39843112156.2  L39845737629.8  L41497933390.9  L43882228554.6  L45330810912.3  L51731989917.3  L56066579390.6  L5651171884.3   L57672453661.5  L59308660947.3  L59308660947.5  L60098763854.3  L66022206678.1  O17025492443.232O57399310481.232P36719207456.232Q25012919281.211Q30987168515.213Q36438237060.232Q38248387216.232Q39212284437.212Q43862317284.212Q43862606877.211Q43879899724.232Q49734034272.212Q56761401107.212Q60511567613.212Q62122750648.209Q64224247845.212Q64225271004.211Q64236871248.209Q9534245042.209 Q9670180795.212 Q9670796098.211 00000101601^01_02>02B02C02S02c02d02h02o03<03=03>03?03@03X03Y03o04U05;05P05Q05U05V05W05X05d05e06=06X06_06`06a07507607@07K07L07V07Z07[07\07]08M09I0:30:I0:^0:_0:`0;90;i0<A0<T0=D0>40>d0?T0?g0?h0?iFS1R3HIA1h2LF2ra2sp1X3xs01G1g2lo3LFB3TOP2hc3dXc3SPR2X02G05Bmodp2ws3HT1S1R2LF2ra2sp1X3xs01G1g2lo3LFB3LOS3dXc2wsFS2LF2sp1X3xs02lo3LFB3dXc3DSX2wsS2spFS2nX2dA2dB1g3SZAS2nX2dA2dB1g3SZASS2spS2sp2loS2sp1X2lo3DSXFFFSS1R2sp2lo4SLO25NEEDR3NERFS2nX2dA2dB1g1v2HV1H2H0S2LF2ra2sp1X3xs01G1g3LFB3dXc2X03X162wsS2LF2ra2sp1X3xs01G1g3LFB3dXc2X03X162wsS1R3HIA1h2sp2lo3TOP1HFS2loSFFS2sp3SPA3SPRFS1R2sp2lo4SLO25NEEDR3NERS2nX2dA2dB1g1d2D01f2HF4FRNNS2sp2loFFS2nX2dA2dB1g3dXc3HSZFS2nX2dA2dBS3dXc2N12E0FS1R2lo3LOSS2spFFFS2LF1X2sX2nX2pX3xs04padX4ownX3LFB3dXc3XAD2ws3AD1S1R2LF2sp3xs02lo4SLO23LFB5NEEDR3LOS3dXc3NER3SPR4ALO'4ACP'2wsS1R2LF2sp3xs02lo4SLO23LFB5NEEDR3dXc3NER2wsS2LF3xs02lo3LFB3dXc2wsS2LF1X3xs03LFB3dXc2wsFFS2LF2sp3xs02lo3LFB3dXc2wsS2LF1X2sX2nX2pX3xs04padX4ownX3LFB3dXc3XAD2ws3AD1S2LF1X3xs03LFB3dXc2X02wsS2LF3xs03LFB3dXc2wsS2LF1X2sX2nX2pX3xs04padX4ownX3LFB3dXc3XAD2ws3AD1S2LF1X2sX2nX2pX3xs04padX4ownX3LFB3dXc3XAD2ws3AD1S2LF1X2sX2nX2pX3xs04padX4ownX3LFB3dXc3XAD2ws3AD1S2LF1X2sX2nX2pX3xs04padX4ownX3LFB3dXc3XAD2ws3AD1S2LF3xs03LFB3dXc2wsFF". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NSM HTAB JC TPV UWX D0 GRP OSEP MCOK MIm SLO2 SLO1 SLO3 MCE BUD BUDF C24H LFB SZA"] Lemma mm_red : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pv,$3.Pf,$3.Phc,(21.$1;.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(15.&40.)(16.(15.&8.))PdXc,$4.Pcntc,(15.&40.)Pxra,(15.&40.)Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pxa0,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pxs5,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)P,(30.$1;.VR,VHIA,Vh,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$31.(32.$2.)R18.R17.R16.R15.R14.R13.)P,(3>.R17.R16.R15.R14.R13.)P,(3?.$1;.VR,VHIA,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(1>.Vg,))P,(52.(8.$3.(6<.Vg,)=))P,(=.R1<.(5=.(11.VdA,)(11.VdB,)))P,(=.R1<.(5>.Vd,))P,(=.(11.R19.)(5?.VnX,(11.VdA,)(11.VdB,)))(27.$1;.(28.$1;.VR,VHIA,R1=.Vmo,)$29.(2:.(2;.R18.(2<.&40.(>.(2=.&40.Vsp,)-40.))Vgp,Vtp,R17.R16.R15.(2<.&40.VX,)(2<.&40.VG,)R14.R13.R12.R11.R10.R?.R>.R=.(2<.&40.(>.VG,+90.))(2<.&40.(6;.(59.VR,)))(2<.&40.(>.(6:.(>.VG,+90.)+3.)(6;.(59.VR,))))R<.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(2<.&40.+<?038.)Vfc,(2>.(15.&40.))R1;.(2?.$1;.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J S DPJ GNZ HV HF HSZ. basic_factsA hc.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    ddestruct (mm_opX v f hc LBc mc dXc (bv_unsigned sp + -64) J ltac:(clear - SLO2 NER NEEDR; lia)) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof (mm_cnt24 v f hc LBc mc dXc J) as C24c.
    dpose GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW). dpose GAT as (_ & GAL & G0 & EP & _ & _ & _ & _ & _ & _ & _ & _ & _ & GREST).
    ddestruct GREST as (_ & Bpb & _ & _ & Bmodp & _ & _ & _ & _ & _ & _ & _ & GMO).
    destruct GMO as [Z0 | (lp & ws & INMT & ELP & EWS & OWNP & SGP)]; [exfalso; exact (GNZ Z0)|].
    destruct (HTAB _ _ _ INMT) as (EVEN & K & STK & KGE & STKB & RED).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp + -64)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    pose proof (conj S I) as Sbox. pose proof (conj J I) as Jbox. clear J S.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    shadow_chk OX1 (X + 8) 2.
    (* [comment removed for export] *)
    unfold mpi_cells in CX1. cbn [md_addr md_pad] in CX1.
    zstep. zstep.
    if_cases KS.
    -
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      pose proof (ms_ss _ _ _ _ _ (proj1 Sbox)) as SSc.
      assert (M8 : (bv_unsigned sp + -64) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
      pose proof (sshad_split asegs AL mc slo (bv_unsigned sp + -64) (bv_unsigned sp) SSc ltac:(clear - SLO3 SLO2 NER NEEDR; lia) M8) as [SS1 _]. clear SSc M8.
      pose proof (A_mpi_cmp_int_spec R HIA IMG UARG SM0 NSM) as SPC. unfold mpi_cmp_int_stmtA, A_MPI_CMP_INT_E in SPC.
      eapply (aevtA_cut_evtA_KF asegs R HIA hc mo).
      { eapply SPC with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (z := 0) (lo := lo) (slo := slo);
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia;
          try eassumption; try reflexivity;
          first [ rewrite XAD; exact OX1
                | rewrite XAD; exact XCR
                | rewrite XAD; reflexivity
                | exact XIM
                | clear; lia
                | clear - LFB; lia
                | intros EO; ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & _ & _ & _ & _ & XP0 & _); exact XP0
                | intros N1; assert (ON : md_own dXc <> LNull) by (intros C; destruct (OWN0 C) as [_ E0]; clear - E0 N1; lia);
                  ddestruct (OWN1 ON) as (_ & _ & _ & _ & _ & _ & _ & _ & OPq & _); exact OPq
                | intros N1; assert (ON : md_own dXc <> LNull) by (intros C; destruct (OWN0 C) as [_ E0]; clear - E0 N1; lia);
                  destruct (XLSq ON) as [XL|XL]; [left; exact XL| right; exact XL]
                | rewrite XAD; clear - DSX SLO2 NER NEEDR; lia
                | rewrite HT1; clear - TOP; lia
                | clear - SPA; Z.div_mod_to_equations; lia
                | clear - SLO2 NES; lia
                | clear - SLO3 SLO2 NER NEEDR; lia
                | clear - SLO2 NER NEEDR; lia
                | match goal with |- ?g => idtac "CMPINT-PRE-LEFT:" g end ]. }
      clear SPC SS1.
      intros ms' PO. unfold mpi_cmp_int_postA in PO.
      destruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m6 & h6 & E & MI6 & ST6 & HP6 & HCS6 & HT6 & HS6 & HF6 & HV6 & HFR6 & HKE6 & HH6).
      subst ms'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST6, HP6 by qlia.
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
      lazymatch goal with |- aevtA ?sg (KF _ _ _ hc mo) ?Q ?ms0 =>
        cut (aevtA sg (KF asegs R HIA h6 mo) Q ms0); [intros AH mo9 [K9 F9]; apply AH; split; [apply (proj2 (HKE6 mo9)); exact K9| exact F9]|] end.
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h6) as LAWS. pose proof (KF_kinv asegs R HIA h6 mo) as KINV.
      destruct Jbox as [J _]. destruct Sbox as [S _].
      pose proof ST6 as ST6'. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST6' by (clear; lia).
      assert (HP6' : presA asegs R ([] ++ LBc) LF (bv_unsigned sp - 64) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m6)
        by (cbn [app]; replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by (clear; lia); exact HP6).
      assert (HCSm : forall x, hcs asegs R HIA hc x -> hcs asegs R HIA h6 x) by (intros x Hx; rewrite HCS6; exact Hx).
      assert (HV6' : havol asegs R HIA h6 <= havol asegs R HIA hc + 0) by (rewrite HV6; clear; lia).
      assert (HFR6' : hfr asegs R HIA h6 <= hfr asegs R HIA hc + 0) by (rewrite HFR6; clear; lia).
      assert (HH6' : HM asegs R HIA h6 ([] ++ LBc) LF m6) by (cbn [app]; exact HH6).
      pose proof (xa_transport _ _ _ _ _ _ _ _ _ _ _ _ JC [] [] v f 0 0 hc LBc mc dXc m6 h6 J MI6 ST6' HP6' HT6 HS6 HF6 HCSm HV6' HFR6' HH6') as J6x.
      pose proof (xa_X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J6x) as MX6. clear J6x HP6' HH6'.
      assert (HPk : presA asegs R (mpd_keep LBc dXc) LF (bv_unsigned sp + -64) (arl_stklo R) (hstkhi asegs R HIA hc) [(X, X + 16)] mc m6)
        by (eapply presA_weaken; [exact HP6| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]).
      destruct (mm_step v f hc LBc mc dXc cntc m6 h6 LBc dXc (bv_unsigned sp + -64) 0 0 J S DPJ
                  ltac:(clear - SLO2 NER NEEDR; lia) ltac:(clear; lia) ltac:(clear; lia)
                  MI6 ST6' HPk HT6 HS6 HF6 HCSm HV6' HFR6' HH6 MX6
                  ltac:(apply mpd_out_refl; exact XNS)
                  ltac:(split; [reflexivity|]; split; [reflexivity|]; split; [intros b Hb; left; exact Hb| clear; lia])
                  ltac:(intros b Hb; left; exact Hb)) as [J6 S6].
      rewrite !Z.add_0_r in J6.
      clear MU WM. pose proof (munch_refl ([] : list ivl) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KC.
      +
        eapply (mm_red2 v f h6 LBc m6 dXc cntc); [exact J6| exact S6| exact DPJ| exact GNZ| exact HV| exact HF| exact HSZ].
      + (* [comment removed for export] *)
        zstep. zstep. zstep.
        lazymatch goal with |- _ (MS ?RR _ _ _ _ _ _) => let v0 := getx RR 10%positive in replace v0 with (Z_to_bv 64 (-20352)) by (apply bv_eq; vm_compute; reflexivity) end.
        assert (FRNN : 0 <= mod_mpi_FRn (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g)) d) by (apply mod_mpi_FRn_nonneg; [unfold mul_mpi_nz; clear - SZA; lia| exact D0]).
        eapply mm_fail; [exact J6| exact (ms_mc _ _ _ _ _ S6)| clear; lia
                        | unfold mm_PHIn, red_PHIn; pose proof (grow_PHI_nonneg (2 * md_n (g_P g)) ltac:(clear - SZA; lia)); pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g)) ltac:(unfold mul_mpi_nz; clear - SZA; lia) ltac:(clear - SZA; lia)); clear - HV H H0; lia
                        | unfold mm_FRn, red_FRn, calls_FR, fr_charge; clear - HF D0 FRNN; lia
                        | unfold mm_nz; clear - HSZ; lia].
    -
      destruct Jbox as [J _]. destruct Sbox as [S _].
      eapply (mm_red2 v f hc LBc mc dXc cntc); [exact J| exact S| exact DPJ| exact GNZ| exact HV| exact HF| exact HSZ].
    all: match goal with |- ?g => idtac "RED-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308579668.400000=S1X2Ea3SXE2H5". (* [comment removed for export] *)
  #[using="IMG"] Lemma mm_mk_JBd : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "PdE,$4.Pm1,P,(15.&40.)(16.(15.&8.))P,(6=.$1;.VR,VLF,Vm,VLB,(2=.&40.Vsp,)R2.)P,(55.(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R3.Vlo,(2=.&40.Vsp,))P,(5.(3=.VR,)(6.$2.VLB,(7.VLF,))Vlo,(54.R4.)+10.)P,P,(8.$9.(:.R5.)$;.)(5.(3=.VR,)(6.$2.VLB,(7.VLF,))Vlo,(?.R6.)(10.+4.(11.R6.)))P,(<.(=.(>.VX,+10.)(54.R6.))(=.(>.(54.R6.)+10.)VX,))P,P,(8.$9.(:.R7.)$53.)(8.$6>.(6?.(?.R8.)(10.+4.(11.R8.)))$70.)P,(71.$1;.(59.VR,)(47.$1;.VR,VHIA,Vh,)R7.(54.R8.)+10.)P,P,(8.$9.(:.R9.)$53.)(71.$1;.(59.VR,)(47.$1;.VR,VHIA,Vh,)R9.(?.R:.)(10.+4.(11.R:.)))P,(39.$1;.VR,VHIA,Vh,VLB,VLF,R9.)P,(6=.$1;.VR,VLF,R:.VLB,(2=.&40.Vsp,)R;.)(23.(3?.$1;.VR,VHIA,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,R<.)(72.$1;.VR,VHIA,VLF,Vsp,R<.Vh,VLB,R;.(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))")
(* [comment removed for export] *).
  Proof.
    intros dE m1; intros ME OE CRE CREL SXE IE OEs OEl HM1 ME1. dpose OE as (OE1 & OE2 & OE3 & OE4 & OE5).
    destruct dE as [Ea sE nE pE zs0 padE ownE].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    split.
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption.
      intros EO RO hc LBc mc HMc. eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HMc| exact (IE EO)].
    - constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      + exact ME1.
      + exact OE2.
      + intros EOX EN. destruct OE3 as [C|[C|[C|C]]]; [exfalso; injection C; intros; clear - SXE H5; lia| exfalso; exact (C EOX)| exfalso; exact (EN C)| exact C].
      + exact OEs.
      + intros EN. pose proof (opnd_viewA _ _ _ _ _ _ _ ME1) as [(_ & _ & _ & _ & _ & OW) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OW.
        destruct ownE; [exfalso; exact (EN eq_refl)| |].
        * ddestruct OW as (_ & EIN & _). eapply hm_aobj_block; [exact HM1| exact EIN].
        * exact (OEl eq_refl).
    all: match goal with |- ?g => idtac "JBD-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0>L15178124.7   L1685717371.0 L18040234563.4L19945316590.2L22309472313.3L23661207263.4L30616158697.2L33357133290.3L35653441506.7L36292206092.4L36326650258.3L4442768650.7 L48174279700.2L48736977024.5L51165555193.2L51394408146.4L52314013762.1L60098763854.3L62065999094.1L62676605567.3L8927507728.5 00000D00E00R00Y00a00n01401<01T01_01h02A02G02X02^02i02l03603903A03RS1R2nX2pX1g2R02R12IASS2sp1g2lo3OP4S2sp2loS1X1g2APS2sp1G2lo3GSPS1g2N1S1G1x2HxS1R3HIA1h2sp2lo3TOP4HTOPS2sp1g2lo1KS1X1G3OS1S1R1g2lo3LOS4ALO'3ACL3IHIS1g2N1S1g3DHL2N12P03PBBS1g2N1S2nX2pX1G1KS1GS1R2lo3LOSS1GS1R1g2R1S1g3DHL2N12P03PBB". (* [comment removed for export] *)
  #[using="IMG MT ra s0 s1 s2 s3 s4 s5 s6 G MC d JC GRP OSEP MIm"] Lemma mm_grp_P : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pm1,P,(15.&40.)(16.(15.&8.))P,(33.(34.(35.$3.$3.)(36.$3.$3.Vlo,(2=.&40.Vsp,))(32.(35.$3.$3.)))Vm,R1.)P,(37.$1;.Vm,R2.)P,(39.$1;.VR,VHIA,Vh,VLB,VLF,R3.)(23.(3?.$1;.VR,VHIA,VLB,VLF,Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(1>.Vg,))(72.$1;.VR,VHIA,VLF,Vsp,(1>.Vg,)Vh,VLB,R4.(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros m1 MU WM HH1. basic_factsA h.
    dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    ddestruct GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW).
    dpose GAT as (_ & GAL & G0 & EP & _ & _ & _ & MP & _).
    ddestruct OSEP as (OS1 & OS2 & OS3). cbn [md_addr md_own md_p md_n] in OS1, OS2, OS3.
    assert (MPo : mpd_at asegs m LB dP) by (split; [exact MP| left; exact GPS]).
    assert (NH : md_own dP <> LHeap) by (eapply (grp_static_own asegs); [exact GAT| exact GH1| unfold grp_mpds; left; reflexivity]).
    assert (PIM : mpd_imgA dP) by (unfold grp_imgA, grp_mpds in GIMG; apply Forall_inv in GIMG; exact GIMG).
    pose proof (alloc_ceiling_lo (L := arl_L R)) as ACL.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (DST : md_own dP <> LNull -> 1 <= md_n dP /\ 0 < md_p dP /\ (forall i, 0 <= i < 4 * md_n dP -> ro_addr asegs (wa (md_p dP + i)) = true)
                                      /\ md_p dP + 4 * md_n dP <= 0x65f000 /\ hl_img_lo L <= md_p dP /\ md_p dP + 4 * md_n dP <= hl_img_hi L).
    { intros NN. dpose MP as (_ & _ & _ & DHL & DHN & DHO). unfold mpd_imgA in PIM.
      destruct (md_own dP) eqn:OD; [exfalso; apply NN; reflexivity| exfalso; apply NH; reflexivity|].
      ddestruct DHO as (N1 & _ & P0 & PB & PRO). pose proof (bytes_at_bound _ _ _ _ PB) as PBB. rewrite u32s_length in PBB.
      destruct (AImgGlobals.img_norz_sound _ _ (PIM eq_refl)) as (_ & _ & IHI & _). unfold AImgGlobals.IMG_HI in IHI.
      pose proof (ROIMG _ (PRO 0 ltac:(clear - N1; lia)) ltac:(clear - P0 PBB N1 DHL; lia)) as R0. rewrite Z.add_0_r in R0.
      pose proof (ROIMG _ (PRO (4 * md_n dP - 1) ltac:(clear - N1; lia)) ltac:(clear - P0 PBB N1 DHL; lia)) as R1.
      split; [exact N1|]. split; [exact P0|]. split; [exact PRO|]. split; [exact IHI|]. split; [exact (proj1 R0)| clear - R1; lia]. }
    pose proof MX as [(CX & _ & _ & _ & _ & OWX) _]. unfold mpi_cells in CX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX, OWX.
    assert (OSP : opnd_sep dX dP lo (bv_unsigned sp)).
    { unfold opnd_sep. cbn [md_addr md_own md_p md_n].
      split.
      { intros NN. ddestruct (DST NN) as (N1 & P0 & PRO & _).
        pose proof (P_ecp_mul_mod.rw_ro_apart asegs m _ _ (md_p dP) (4 * md_n dP) MIm CX ltac:(cbn; clear; lia) ltac:(clear - N1; lia) PRO) as AP.
        cbn [cells_size csize Nat.add] in AP. clear - AP. lia. }
      split; [intros O; rewrite EP; pose proof (OS2 O) as K; clear - K; lia|].
      split.
      { destruct ownX eqn:OX; [right; left; discriminate| | exfalso; apply NST; reflexivity].
        destruct (limb_own_eq_dec (md_own dP) LNull) as [EN|NN]; [right; right; left; exact EN|].
        right; right; right. ddestruct (DST NN) as (_ & _ & _ & _ & R0 & R1).
        ddestruct OWX as (_ & XIN & _). destruct (hm_apart asegs R HIA h LB LF m HH) as [HF0 _]. rewrite Forall_forall in HF0.
        destruct (HF0 _ ltac:(apply in_or_app; left; exact XIN)) as (_ & _ & _ & IA). cbn [fst snd] in IA. clear - IA R0 R1. lia. }
      split; [rewrite EP; clear - GSP; lia|].
      intros NN. ddestruct (DST NN) as (_ & _ & _ & IHI & _). left. clear - IHI ACL ALO' LOS. lia. }
    dpose OSP as (_ & _ & _ & OP4 & OP5).
    assert (WC0 : w_client (hcs asegs R HIA h) [(lo, bv_unsigned sp)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]. }
    eapply mm_mk_JBd.
    - apply opnd_atA_mpd. exact MPo.
    - exact OSP.
    - rewrite EP. intros x Hx. apply GCR. clear - Hx. lia.
    - intros O. exfalso. exact (NH O).
    - rewrite EP. clear - OS1. lia.
    - exact PIM.
    - eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU|]. rewrite EP. eapply aobj_sub; [exact GOB| clear; lia| clear; lia].
    - intros E. eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH1| exact (PIM E)].
    - exact HH1.
    - eapply opnd_atA_munch_any; [apply opnd_atA_mpd; exact MPo| exact MU| exact WM| cbn [disjoint_from fst snd]; split; [clear - OP4; lia| exact I]|].
      intros ON. cbn [disjoint_from fst snd]. split; [destruct (OP5 ON) as [K|K]; clear - K; lia| exact I].
    all: match goal with |- ?g => idtac "GRPP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02=0@D11157215372.233D11157215372.235D13554616751.179D13554616751.180D30841324822.180D33357133290.233D33357133290.235D35881667587.179D35881667587.180D43120647727.233D43120647727.235D44176293503.231D51611362854.233D66022014388.233L1175746480.1   L11783059779.1  L12283411672.174L13301871092.174L13449382718.5  L14106684376.173L1579419076.5   L17305700853.4  L17646078182.175L17722885571.2  L19431261630.4  L19945316590.2  L2397676628.0   L24026834428.10 L26825993283.6  L27932457901.6  L29010569984.234L29956516996.0  L30061891851.3  L30072648280.7  L31466921807.11 L33057867371.2  L34299728400.233L34994544387.174L35653441506.7  L36558768539.2  L38738191873.6  L39887139444.174L40290687782.1  L40834179097.192L41288976216.174L42479583780.4  L43059266230.173L43575585406.4  L44866992728.174L45898055924.174L46393950340.3  L48193575137.7  L48429268312.174L49807537001.4  L51035954534.9  L5145216728.174 L51925114228.174L5261871668.3   L57672453661.5  L57797391894.5  L57835863895.5  L57933933556.174L58921766052.2  L60098763854.3  L61581888254.233L62948672147.2  L63235947448.2  L63962036340.173L6482734895.4   L66151427842.16 L67158371251.174L67996112456.1  L7143015064.234 L7274816372.174 L7795562387.4   L8722184664.174 L8892999663.4   P17727118770.179P17727118770.180P58928204206.233Q14290048923.242Q15457446739.176Q15457446739.177Q15643324129.175Q18365925601.176Q18700391810.198Q19120365881.179Q21804148081.198Q21879645826.176Q25156068230.198Q25513505925.178Q25513505925.179Q25660479061.198Q27907200258.176Q28068660573.198Q30985333526.198Q30985398804.233Q31034260529.230Q31230991318.198Q31271525473.176Q31400710758.198Q32655500769.176Q33918256002.176Q35029170400.198Q35702871654.198Q36425882626.176Q3830427394.176 Q39939554818.176Q41152393185.176Q4128564050.198 Q41599235262.241Q42435318089.230Q42439443119.179Q42439443119.180Q43928033258.177Q43957738831.242Q44648843873.176Q44741466490.232Q49698585326.177Q49698585326.178Q51235796833.176Q5153559935.241 Q5166159483.242 Q53959357837.198Q54316617865.198Q58928204206.233Q59843137889.176Q59865321072.179Q59865321072.180Q61795893974.198Q6418335826.198 Q64240990594.198Q64683667846.179Q64683667846.180Q66522067074.176Q66890061916.241Q67528989526.179Q67528989526.180Q7377275490.178 Q7377275490.179 Q9843367298.175 00000100201D02h04=04>04?05706D06E06F06G06H06e06i06l07I07f08608S08c08o09L09M09[09b09c0:C0:[0;00;10;20;;0;T0<70<@0<]0=:0=R0=X0=l0>I0>L0>k0?H0?T0@90@G0@d0AA0AJ0A`0B=0BJ0Bj0CG0Cd0Cn0D80DH0DX0E50E60E@0Eb0Ej0F10FN0F\0G60GS0GW0H60HS0Ha0I>0IL0JP0Kf0LU0MF0M^0N60NN0Nf0O?0On0Oo0PL0Pe0QO0RK0RL0Ri0Rj0Se0T`0UF0U`0V80VJ0Vb0W?0WY0WZ0X70XT0Y10YI0YJ0Y\0Z90Zk0[o0\G0\Y0]10]20]U0^80^P0^b0_40_N0_O0_P0_h0_i0_j0_k0`D0`E0aA0bO0bl0c>0cm0dn0e]0f[0g8FFS1R2LF2ra2sp1X3xs01G2MC2lo4SLO23MCE3LFB5NEEDR3LOS2X03NER3SPR2G03GTB2HB5Ha_st5Hl_stS1R2LF2ra2sp2s01X3xs01G2MC2lo4SLO23MCE3LFB5NEEDR3LOS2X03NER3SPR2G03GTB2HB5Ha_st5Hl_st2s12s22s32s42s5S1R2LF2ra2sp2s61X3xs01G2MC2lo4SLO23MCE3LFB5NEEDR3LOS2X03NER3SPR2G03GTB2HB5Ha_st5Hl_stFFS1R3HIA1h2LF2ra2sp1X3xs01G2MC3LFB3TOP3GTB2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp2s01X3xs01G2MC3LFB3TOP3GTB2HB5Ha_st5Hl_st2s12s22s32s42s52s6FFFFS2LF2ra2sp1X3xs01G2MC3LFB3GTBS2spS1dS2LF2ra2sp1X3xs01G2MC3LFB3GTBS2LF2ra2sp1X3xs01G2MC3LFB3GTBS2nX2dA2dB1g3SZAS2LF2ra2sp1X3xs01G2MC3LFB3GTBS2nX2dA2dB1g3SZAS2sp2dA2lo1KS2LF2ra2sp1X3xs01G2MC3LFB3GTBFS2sp2dA2lo3OA4S2sp2loSS1R3HIA1h2nX2dA2dB1g3BUD3PNN3GNNS1R2sp2lo4SLO25NEEDR3NERS2nX2dA2dB1g4PNNq3GNNFSS2sp2dA1KS1R2MC2lo3LOS3ALO3MC23DLOS1R3HIA1h2nX2dA2dB1g1d2D04BUDF4FRNNS2LB4C24HS2LF2ra2sp1X3xs01G2MC3LFB3GTBS2LF2ra2sp1X3xs01G2MC3LFB3GTBS1R3HIA1h2sp2lo3TOP4HTOPS1d2D0S2nX2dA2dB1g3dX23SZ2S2LF2ra2sp1X3xs01G2MC3LFB3GTBS1XS1R2LF2ra2sp1X3xs01G2MC3LFB3GTBS2LF2ra2sp1X3xs01G2MC3LFB3GTBS2sp2dB2lo1KS2LF2ra2sp1X3xs01G2MC2lo3LFB4LOSP3GTBS2sp2dB2lo3OB4S2LF2ra2sp1X3xs01G2MC3LFB3GTBS2LF2ra2sp1X3xs01G2MC3LFB3GTBS2sp2dB1KS2nX2dA2dB1g1d2D04FRNNS2LF2ra2sp1X3xs01G2MC3LFB3GTBS2sp1G2lo3GSPS2sp1X2sX2nX2pX3xs04padX4ownX2XLS2LF2ra2sp1X3xs01G2MC3LFB3GTBS2LF2ra2sp1X3xs01G2MC3LFB3GTBS1X2X03X16S2nX2dA2dBS2nX2dA2dB1g3SZAS1R3HIA1h2sp3TOPS2LF2ra2sp1X3xs01G2MC3LFB3GTBFS1R2lo3LOSS2LF2ra2sp1X3xs01G2MC3LFB2G03GTB1rS2LF3LFBS2dA2dBS2LF2ra2sp1X3xs01G2MC3LFB3GTBS2sp2dB2lo3OB4S2sp2r03SPA1q1r1H2H02q02H4S2LF2ra2sp1X3xs01G2MC3LFB3GTBS2spS2LF2ra2sp1X3xs01G2MC3LFB3GTB1rS2LF2ra2sp1X3xs01G2MC3LFB3GTBS1R2sp2lo4SLO2S2LF2ra2sp1X3xs01G2MC3LFB3GTBS2sp2dA2lo3OA4S1R2LF2ra2sp3xs01G2MC2lo4SLO23LFB5NEEDR3NER5MCLOW3GTB2HB5Ha_st5Hl_stS1R2LF2sp2s03xs01G2MC2lo4SLO23LFB5NEEDR3NER5MCLOW3GTB2HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R2LF2sp1X3xs01G2lo4SLO23LFB5NEEDR3DSX3NER3GTBS2LF2ra2sp1X3xs01G2MC3MCE3LFB2X03SPR3GAL2G03GTB1rS2LF2sp3xs01G3LFB3GTB2HBS2LF2sp3xs01G3LFB3GTB2HBS2LF2sp3xs01G2lo3LFB3GTBS2LF2sp3xs01G2lo3LFB3GTBS1R2LF3xs01G3LFB4IMG'3GTBS2LF2sp2s63xs01G2lo3LFB4LOSP3GTB2HB5Ha_st5Hl_stFS2LF2sp3xs01G2lo3LFB4LOSP3GTBS1R2LF3xs01G3LFB4IMG'3GTBS2LF2ra2sp3xs01G2lo3LFB3GTB2HB5Ha_st5Hl_stS2LF2sp2s03xs01G2lo3LFB3GTB2HB5Ha_st5Hl_st2s12s22s32s42s52s6FS2LF2sp3xs01G2lo3LFB4LOSP3GTBFS1R2LF2sp3xs01G2MC2lo4SLO23MCE3LFB5NEEDR4SP643NER5MCLOW3GTBS1R2LF2sp3xs01G2MC2lo4SLO23MCE3LFB5NEEDR4SP643NER5MCLOW3GTBS1R3HIA1h2LF2sp3xs01G3LFB3TOP4HTOP3GTBS1R2LF3xs01G3LFB5ALWF'3GTBS2LF2sp3xs01G2lo3LFB3GTBS2LF3xs01G3LFB3GTBS2LF2sp3xs01G2lo3LFB3GTBS2LF2sp3xs01G2lo3LFB4LOSP3GTBS1R2LF3xs01G3LFB5ALWF'3GTBFS2LF2sp3xs01G2lo3LFB4LOSP3GTBS2LF2sp3xs01G2lo3LFB4LOSP3GTBS2LF2sp3xs01G2lo3LFB4LOSP3GTBS2LF2sp3xs01G2lo3LFB3GTBFS2LF3xs01G3LFB3GTBS1R2LF3xs01G3slo4SLO13LFB3GTBS1R2LF2ra2sp3xs01G3slo4SLO13LFB3GTB2HB5Ha_st5Hl_stS1R2LF2sp2s03xs01G3slo4SLO13LFB3GTB2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2LF2sp3xs01G3LFB3GTB2HBS2LF3xs01G3LFB3GTBS2LF2sp3xs01G2lo3LFB3GTBFS2LF2sp3xs01G3LFB4SP643GTB2HB5Ha_stS2LF2sp3xs01G3LFB4SP643GTB2HB5Ha_stS2LF2sp3xs01G2lo3LFB3GTBS2LF3xs01G3LFB3GTBS2LF3xs01G3LFB3GTBS1R2LF3xs01G3LFB5ALWF'3GTBFFS2LF2sp3xs01G2lo3LFB3GTBFFFS1R2LF3xs01G3LFB4IMG'3GTBFS1R3HIA1h2LF2ra2sp3xs01G3slo3LFB3TOP4HTOP3GTB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2s03xs01G3slo3LFB3TOP4HTOP3GTB2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2LF2sp3xs01G2lo3LFB4LOSP3GTBS2LF3xs01G3LFB3GTBS2LF2ra2sp3xs01G2lo3LFB4LOSP3GTB2HB5Ha_st5Hl_stS2LF2sp2s03xs01G2lo3LFB4LOSP3GTB2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2LF2ra2sp3xs01G2lo3LFB4LOSP3GTB2HB5Ha_st5Hl_stS2LF2sp2s03xs01G2lo3LFB4LOSP3GTB2HB5Ha_st5Hl_st2s12s22s32s42s5S2LF2sp3xs01G2lo3LFB4LOSP3GTB". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NSM HMUL HMOD HTAB JC FJ TPV UWX D0 GRP OSEP MCOK MIm SLO2 slo SSH SLO1 SLO3 MCE BUD BUDF C24H LFB SZA"] Lemma mm_main : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "Pt0,(15.&40.)Pt1,(15.&40.)Pt2,(15.&40.)Pa4,(15.&40.)Pa5,(15.&40.)Pa6,(15.&40.)Pa7,(15.&40.)Pt3,(15.&40.)Pt4,(15.&40.)Pt5,(15.&40.)Pt6,(15.&40.)Pcnt,(15.&40.)Pm0,P,(15.&40.)(16.(15.&8.))P,(8.P,(15.&40.)(16.(15.&8.))R1.Vm,)P,(73.$1;.VR,VHIA,Vh,Vmo,)P,(41.$1;.Vm,Vlo,(2=.&40.Vsp,))P,(58.$1;.(59.VR,)(47.$1;.VR,VHIA,Vh,)Vm,(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(4:.$1;.Vm,VLB,VdA,)P,(4:.$1;.Vm,VLB,VdB,)P,(5;.(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)P,(5;.(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdB,)P,(5;.VdA,VdB,)P,(55.(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,Vlo,(2=.&40.Vsp,))P,(55.(1<.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdB,Vlo,(2=.&40.Vsp,))P,(5.(3=.VR,)(6.$2.VLB,(7.VLF,))Vlo,(54.VdA,)+10.)P,P,(8.$9.(:.VdA,)$;.)(5.(3=.VR,)(6.$2.VLB,(7.VLF,))Vlo,(?.VdA,)(10.+4.(11.VdA,)))P,(5.(3=.VR,)(6.$2.VLB,(7.VLF,))Vlo,(54.VdB,)+10.)P,P,(8.$9.(:.VdB,)$;.)(5.(3=.VR,)(6.$2.VLB,(7.VLF,))Vlo,(?.VdB,)(10.+4.(11.VdB,)))P,(58.$1;.(59.VR,)(47.$1;.VR,VHIA,Vh,)Vm,VdA,)P,(58.$1;.(59.VR,)(47.$1;.VR,VHIA,Vh,)Vm,VdB,)P,(5:.VdA,)P,(5:.VdB,)P,(5<.VR,(54.VdA,)+10.Vd,)P,(5<.VR,(54.VdB,)+10.Vd,)P,(3:.$1;.Vm,VMC,(34.$3;.(3<.R17.)(32.$3;.)))(74.$1;.$29.(75.(2:.(2;.Vra,Vsp,Vgp,Vtp,R23.R22.R21.Vs0,Vs1,(2<.&40.VG,)(2<.&40.VX,)(2<.&40.(54.VdA,))(2<.&40.(54.VdB,))R20.R1?.R1>.R1=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1<.R1;.R1:.R19.)VF,(2<.&40.$76.)Vfc,(2>.(15.&40.))R17.(2?.$1;.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until m0; intros EM HK ST OXA MA MB SXA SXB SAB OA OB CRA CRAL CRB CRBL OAA OBA IMA IMB UWA UWB MC0. unfold A_MPI_MUL_MOD_E.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 64 MM_FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof OXA as [OX _]. cbn [md_addr] in OX.
    dpose GRP as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW). dpose GAT as (_ & GAL & G0 & EP & _ & _ & _ & _ & _ & _ & _ & _ & GT0 & GREST).
    ddestruct GREST as (_ & Bpb & _ & _ & Bmodp & _).
    dpose MCOK as (MC1 & MC2 & MC3 & MC4 & MC5 & MC6). pose proof (art_data_lo asegs R HIA) as DLO.
    assert (MCLOW : MC + 8 <= lo) by (clear - MC2 DLO ALO LOS; lia).
    pose proof (rw_cells_bound _ _ _ _ GT0) as GTB. unfold grp_tail_cells in GTB. cbn [cells_size csize Nat.add] in GTB.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    (* [comment removed for export] *)
    pose proof MIm as MI0. pose proof SSH as SSH0. pose proof MC0 as MC0'. pose proof GT0 as GT0'. pose proof FJ as FJ0.
    rewrite <- EM in HH, ST, OX, MI0, SSH0, MC0', FJ0.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    destruct (stk_split asegs m0 lo (bv_unsigned sp - 56) (bv_unsigned sp) ST ltac:(clear - SLO2 NER NEEDR; lia)) as [STlo ST56].
    destruct (stk_split asegs m0 lo (bv_unsigned sp - 64) (bv_unsigned sp - 56) STlo ltac:(clear - SLO2 NER NEEDR; lia)) as [STlo' _].
    clear ST STlo. rename ST56 into ST.
    carve_frame 56%nat ST.
    assert (FRc : rw_cells asegs m0 (bv_unsigned sp + -64) ([CB 8 fj] ++ [CB 56 junk])).
    { apply rw_cells_app. split.
      - replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by (clear; lia). exact FJ0.
      - cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by (clear; lia). exact FR. }
    cbn [app] in FRc. clear FR ST FJ0. rename FRc into FR. rename STlo' into ST.
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST by (clear; lia).
    do 8 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    subst m0.
    replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in FR, ST by (clear; lia).
    fold MM_FRAME in FR. unfold mm_frame64 in FR.
    pose proof (xa_start _ _ _ _ _ _ _ _ _ _ _ _ JC mP HH MI0 ST FR OX MU WM) as J0.
    destruct (mm_grp_P mP MU WM HH) as [DPJ BP0].
    assert (WC0 : w_client (hcs asegs R HIA h) [(lo, bv_unsigned sp)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]. }
    assert (S0 : MMS h LB mP dX cnt).
    { constructor.
      - exact MC0'.
      - eapply rw_cells_transport; [exact GT0'| exact MU| exact WM|]. unfold grp_tail_cells. cbn [cells_size csize Nat.add disjoint_from fst snd]. split; [clear - GSP; lia| exact I].
      - eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact GOB].
      - exact BP0.
      - exact SSH0. }
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    assert (MA1 : mpd_at asegs mP LB dA).
    { eapply mpd_at_munch_any; [exact MA| exact MU| exact WM| cbn [disjoint_from fst snd]; split; [clear - OA4; lia| exact I]|].
      intros ON. cbn [disjoint_from fst snd]. split; [destruct (OA5 ON) as [K|K]; clear - K; lia| exact I]. }
    assert (MB1 : mpd_at asegs mP LB dB).
    { eapply mpd_at_munch_any; [exact MB| exact MU| exact WM| cbn [disjoint_from fst snd]; split; [clear - OB4; lia| exact I]|].
      intros ON. cbn [disjoint_from fst snd]. split; [destruct (OB5 ON) as [K|K]; clear - K; lia| exact I]. }
    assert (OAA1 : mpd_aobjA asegs AL (hcs asegs R HIA h) mP dA).
    { destruct OAA as [OAs OAl]. split; [eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact OAs]| intros E; eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact (OAl E)]]. }
    assert (OBA1 : mpd_aobjA asegs AL (hcs asegs R HIA h) mP dB).
    { destruct OBA as [OBs OBl]. split; [eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact OBs]| intros E; eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU| exact (OBl E)]]. }
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF mP HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) mP) as MU; pose proof (wmono_refl asegs mP) as WM.
    pose proof (conj S0 I) as Sbox. pose proof (conj J0 I) as Jbox.
    zstep. zstep. zstep. zstep. clear GOT GSB AB.
    zstep. zstep. zstep. zstep. 
    zstep.
    destruct XW as [CW DXP].
    clear MU WM.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HMUL as CP. unfold mpi_mul_mpi_stmtA_sz, mpi_binop_stmtA_sz in CP.
      eapply CP with (h := h) (LB := LB) (LF := LF) (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d) (slo := slo);
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by qlia.
      - exact HH.
      - exact HK1.
      - clear - LFB; lia.
      - exact (xa_X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0).
      - exact MA1.
      - exact MB1.
      - exact SXA.
      - exact SXB.
      - exact SAB.
      - exact NST.
      - intros C; discriminate C.
      - unfold opnd_sep. split; [exact OA1|]. split; [exact OA2|]. split; [exact OA3|]. split; [clear - OA4; lia|]. intros ON. destruct (OA5 ON) as [K|K]; [left; exact K| right; clear - K; lia].
      - unfold opnd_sep. split; [exact OB1|]. split; [exact OB2|]. split; [exact OB3|]. split; [clear - OB4; lia|]. intros ON. destruct (OB5 ON) as [K|K]; [left; exact K| right; clear - K; lia].
      - exact CRA.
      - exact CRAL.
      - exact CRB.
      - exact CRBL.
      - split; [eapply client_wrange_sp_mono; [| exact CW]; clear; lia| exact DXP].
      - intros ON; destruct (XLS ON) as [XL|XL]; [left; exact XL| right; clear - XL; lia].
      - replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by (clear; lia). exact ST.
      - exact LOS.
      - clear - SLO2; lia.
      - intros C; discriminate C.
      - clear - TOP; lia.
      - clear - SPA; Z.div_mod_to_equations; lia.
      - exact TPV.
      - exact MI0.
      - reflexivity.
      - split; [exact OX| intros EST; exfalso; exact (NST EST)].
      - exact OAA1.
      - exact OBA1.
      - exact IMA.
      - exact IMB.
      - pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g)) ltac:(unfold mul_mpi_nz; clear - SZA; lia) ltac:(clear - SZA; lia)) as PNN.
        pose proof (grow_PHI_nonneg (2 * md_n (g_P g)) ltac:(clear - SZA; lia)) as GNN.
        unfold mm_PHIn, red_PHIn in BUD. clear - BUD PNN GNN. lia.
      - eapply uw_obj_uwc; [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear; lia].
      - exact UWX.
      - exact UWA.
      - exact UWB.
      - assert (FRNN : 0 <= mod_mpi_FRn (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g)) d) by (apply mod_mpi_FRn_nonneg; [unfold mul_mpi_nz; clear - SZA; lia| exact D0]).
        unfold mm_FRn, red_FRn, calls_FR, fr_charge in BUDF. clear - BUDF FRNN D0. lia.
      - unfold C24_MUL_MPI, C24_ECP_MUL_MOD in *. clear - C24H. lia.
      - reflexivity.
      - reflexivity.
      - reflexivity. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & GR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    presA_transport HP2.
    destruct Sbox as [S0' _]. destruct Jbox as [J0' _].
    destruct GR as [[MR BK] SZ2]. cbn [md_n] in SZ2.
    pose proof ST2 as ST2'. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST2' by (clear; lia).
    assert (PHIM : 0 <= mul_mpi_PHIn (md_n dA) (md_n dB)) by (unfold mul_mpi_PHIn, grow_PHI; unfold AVOL_CALL; clear - SZA; lia).
    assert (FRM : 0 <= mul_mpi_FRn d) by (unfold mul_mpi_FRn, calls_FR, fr_charge; clear - D0; lia).
    destruct (mm_step 0 0 h LB mP dX cnt m2 h2 LB2 dX2 (bv_unsigned sp + -64) (mul_mpi_PHIn (md_n dA) (md_n dB)) (mul_mpi_FRn d) J0' S0' DPJ
                ltac:(clear - SLO2 NER NEEDR; lia) PHIM FRM
                MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as [J2 S2].
    cbn [Z.add] in J2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    assert (PNNq : 0 <= mod_mpi_PHIn (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g))) by (apply mod_mpi_PHIn_nonneg; [unfold mul_mpi_nz; clear - SZA; lia| clear - SZA; lia]).
    assert (FRNN : 0 <= mod_mpi_FRn (mul_mpi_nz nX (md_n dA) (md_n dB)) (md_n (g_P g)) d) by (apply mod_mpi_FRn_nonneg; [unfold mul_mpi_nz; clear - SZA; lia| exact D0]).
    assert (GNN : 0 <= grow_PHI (2 * md_n (g_P g))) by (apply grow_PHI_nonneg; clear - SZA; lia).
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    -
      pose proof (ms_og _ _ _ _ _ S2) as OG2. pose proof (ms_gt _ _ _ _ _ S2) as GT2. unfold grp_tail_cells in GT2.
      (* [comment removed for export] *)
      clear CSOK SB64 SCS0 SCS WC0. pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
      zstep. if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by (clear - G0 GTB; lia); clear - KN G0 GTB; lia|]. clear KN.
      assert (GL7 : Z.land G 7 = 0)
        by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact GAL | clear - GAL; Z.div_mod_to_equations; lia]).
      zstep. zstep. if_cases KG; zify_cond KG; [exfalso; clear - KG GL7; rewrite ?GL7 in KG; rewrite ?Zmod_0_l in KG; lia|]. clear KG.
      zstep. zstep. zstep. zstep. zstep.
      zstep.
      zstep.
      if_cases KM; zify_cond KM.
      +
        eapply (mm_mod _ _ h2 LB2 m2 dX2 cnt); [exact J2| exact S2| exact DPJ| clear; lia| clear; lia| exact SZ2].
      +
        assert (XL7 : Z.land X 7 = 0)
          by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact XAL | clear - XAL; Z.div_mod_to_equations; lia]).
        zstep. zstep. if_cases KX; zify_cond KX; [exfalso; clear - KX XL7; rewrite ?XL7 in KX; rewrite ?Zmod_0_l in KX; lia|]. clear KX.
        eapply (mm_red _ _ h2 LB2 m2 dX2 cnt); [exact J2| exact S2| exact DPJ| | clear; lia| clear; lia| exact SZ2].
        intros C. apply KM. rewrite C. reflexivity.
    -
      eapply (mm_fail _ _ h2 LB2 m2 dX2 cnt r); [exact J2| exact (ms_mc _ _ _ _ _ S2)| | | |].
      + destruct MR as [MR|MR]; rewrite MR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia.
      + unfold mm_PHIn, red_PHIn. clear - PNNq GNN. lia.
      + unfold mm_FRn, red_FRn, calls_FR, fr_charge. clear - FRNN D0. lia.
      + unfold mm_nz. clear - SZ2. lia.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End MM.

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L22820285897.0L32169498310.8L33316717491.600000100I00ZSS2nX2dA2dB1g2NA2NB2NX2NPS1R2sp2lo3SLO3NER". (* [comment removed for export] *)
Theorem A_ecp_mul_mod_spec : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mul_mod ()) "PR,$77.PHIA,(78.$1;.R1.)PMT,(1.$14.)P,(79.(59.R3.))P,(8.$3.(8;.R4.)$8<.)P,(8.$3.(8=.R5.=)$8>.)P,(=.=(8?.R6.))P,(7:.$1;.R7.R6.$7;.)P,(7<.$1;.R8.R7.$7=.)P,(7>.$1;.R9.R8.R7.)P,(=.=(7?.R:.))P,Ph,(21.$1;.R;.R:.)PLB,(1.$2.)PLF,(1.$2.)Pm,P,(15.&40.)(16.(15.&8.))P,(39.$1;.R?.R>.R4.R3.R2.R1.)(80.$3.(81.(35.$3.$3.)$3.(50.$3.$3.)R4.))P,(23.(=.(82.(3=.R<.))(83.(3=.R<.)))(=.(84.(3=.R<.))(85.(3=.R<.))))P,Pa,$3.P,(8.$6>.(86.$1;.(87.R1.))$70.)P,(23.(=.=R2.)(24.R2.(26.+2.+40.)))(23.(=.(82.(3=.R10.))R3.)(24.R3.(85.(3=.R10.))))(88.$1;.R>.R=.R<.$89.$8:.)")
(* [comment removed for export] *).
Proof.
  intros R HIA MT IMG UARG SM0 NSM HMUL HMOD HTAB NEEDR HND DIMG ROIMG. unfold ecp_mul_mod_stmtA.
  intros until slo. intros HH HK LFB GRP OSEP MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL MCA MCB XW XLS MC0 MCOK ST LOS SLO SSH SLO1 SLO3 TOP SPA TPV MI RAE OXA OAA OBA IMA IMB BUD UW UWX UWA UWB BUDF C24H -> -> -> ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  pose proof (arl_need_ecp_rt R) as NER.
  destruct (stk_split asegs m lo (bv_unsigned sp - 56) (bv_unsigned sp) ST ltac:(clear - SLO NEEDR NER; lia)) as [STa _].
  destruct (stk_carve asegs m lo (bv_unsigned sp - 56) 8 STa ltac:(clear - SLO NEEDR NER; lia)) as [_ [fj FJ]].
  replace (bv_unsigned sp - 56 - Z.of_nat 8) with (bv_unsigned sp - 64) in FJ by (clear; lia). clear STa.
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 64 (MM_FRAME ra s0 s1 s2 s3 s4 s5 fj)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR NER; lia. }
  assert (SZA : 0 <= md_n dA /\ 0 <= md_n dB /\ 0 <= nX /\ 0 <= md_n (g_P g)).
  { pose proof MA as [(_ & _ & _ & _ & NA & _) _]. pose proof MB as [(_ & _ & _ & _ & NB & _) _]. pose proof MX as [(_ & _ & _ & _ & NX & _) _]. cbn [md_n] in NX.
    destruct GRP as (GAT & _). dpose GAT as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & NP & _) & _).
    clear - NA NB NX NP. lia. }
  cbn [md_addr md_n] in *.
  eapply (mm_main R HIA IMG MT HMUL HMOD HTAB h LB LF m mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X sX nX pX xs0 padX ownX dA dB G g A_MUL_COUNT lo d fj JC)
    with (m0 := m) (cnt := cnt) (slo := slo);
    first [ exact JC | eassumption | reflexivity | eapply uwc_nonneg; exact UW | clear - SLO NEEDR NER; lia | idtac ].
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
