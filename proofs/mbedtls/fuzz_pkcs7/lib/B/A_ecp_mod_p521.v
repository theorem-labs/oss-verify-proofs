(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_ecp_red.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_journey A_mpi_grow A_mpi_core_mla A_mpi_core_add A_ecp_red_lib.
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
Ltac2 gd_tbl_A_ecp_mod_p521 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_red.reducer_R"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.red_FRn"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "RED.RFRAME"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RED.RPOST"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "A_ECP_MOD_P521"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_grow_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_GROW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_red_lib.A_ASAN_MEMSET_EC"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_reducer_stmtA"].


Definition A_ECP_MOD_P521 : Z := 0xd6640.   (* [comment removed for export] *)
Local Lemma zchk_land3 x : Z.land x 3 = x mod 4. Proof. apply (Z.land_ones x 2); lia. Qed.
Local Lemma zchk_land7 x : Z.land x 7 = x mod 8. Proof. apply (Z.land_ones x 3); lia. Qed.
Local Ltac zchk_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ < _)%Z => fail | (_ <= _)%Z => fail | (_ > _)%Z => fail | (_ >= _)%Z => fail
      | (_ <= _ < _)%Z => fail | (_ < _ < _)%Z => fail | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail
      | @eq Z _ _ => fail | ~ (@eq Z _ _) => fail
      | _ => match type of T with Prop => clear H end
      end
  end.
Local Ltac zlia := zchk_clear; lia.
Local Ltac zchk_dec :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; zlia)
            | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; zlia) ]
  | |- context [Z.leb ?a ?b] =>
      first [ replace (Z.leb a b) with true by (symmetry; apply Z.leb_le; zlia)
            | replace (Z.leb a b) with false by (symmetry; apply Z.leb_gt; zlia) ]
  end.
Local Ltac zchk_base :=
  first [ reflexivity
        | apply Z.ltb_lt; zlia | apply Z.ltb_ge; zlia | apply Z.leb_le; zlia | apply Z.leb_gt; zlia
        | apply Z.eqb_eq; zlia | apply Z.eqb_neq; zlia ].
Local Ltac zchk_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); zchk_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); zchk_rec
  | _ => zchk_base
  end.
Local Ltac zchk_solve :=
  rewrite ?zchk_land3, ?zchk_land7;
  zchk_dec;
  first [ reflexivity
        | unfold_cond; fold_lit_ux;
          repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by zlia end;
          zchk_rec ].
Local Ltac zchk_if :=
  match goal with
  | |- _ (MS _ _ (if ?c then Z_to_bv 64 ?t else _) _ _ _ _) =>
      lazymatch eval vm_compute in (Z.eqb t (A_ECP_MOD_P521 + 308)) with true =>
        replace c with false; [cbv_concl_iota | symmetry; zchk_solve] end
  | |- _ (MS _ _ (if ?c then _ else Z_to_bv 64 ?t) _ _ _ _) =>
      lazymatch eval vm_compute in (Z.eqb t (A_ECP_MOD_P521 + 308)) with true =>
        replace c with true; [cbv_concl_iota | symmetry; zchk_solve] end
  end.
Local Ltac zabsorb :=
  lazymatch goal with
  | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch eval vm_compute in (List.existsb (Z.eqb pc) (List.map (Z.add A_ECP_MOD_P521)
        [56; 60; 64; 68; 72; 76; 80; 84; 88; 96; 100; 152; 156; 164; 168; 188; 196; 204; 224])) with true => step; zsimp end
  end.
Local Ltac zpre := repeat (first [ zchk_if | zabsorb ]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section RED.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis GROW : mpi_grow_stmtA_sz asegs R HIA A_MPI_GROW.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_EC.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (lo d : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition RFRAME : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 48 RFRAME.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis BUD : havol asegs R HIA h + grow_PHI 34 <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + red_FRn d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_ECP_RED <= C24MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 160 - arl_need_ecp R.

  Definition RPOST := ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p521 ()) "(0.$1.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(3.+22.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,)(4.+22.)(5.Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).
  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 48 RFRAME []).
  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (arl_need_ecp_rt R) as NER;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L11741095640.134L26924648792.134L29428324939.5  L31378091396.1  L35663928186.7  L4202106291.134 L43654564952.134L59499841752.134L60098763854.3  L66187946659.1  L7510805464.134 Q15643598972.133Q18366170748.133Q27906956191.133Q32655747964.133Q33918012703.133Q3830178207.133 Q39939305631.133Q44648563964.133Q51235551740.133Q59842863100.133Q66521824799.133Q9843086111.133 00000700>00P00T00i01001701>01H01L01S01Z01a02902@02X03003H03O03V03]04504MS2ra2spS2ra2spS1R2lo3LOS3ALO3ACPS2spS1R3HIA1h2sp2lo3TOP1HS2ra2spS2ra2spS2ra2spS1R2lo3LOSS2spS2ra2spS2sp2loS2sp2loS1R2sp2lo4SLO25NEEDR3NERS2sp2loS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERS2sp2loS2sp2loS2sp2loS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NER". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma r_ret : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p521 ()) "Pv,$6.Pf,$6.Phc,(7.$1.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(:.&40.)(;.(:.&8.))PdXc,$<.Pr,$6.Pxra,(:.&40.)Pxt0,(:.&40.)Pxt1,(:.&40.)Pxt2,(:.&40.)Pxs0,(:.&40.)Pxs1,(:.&40.)Pxa1,(:.&40.)Pxa2,(:.&40.)Pxa3,(:.&40.)Pxa4,(:.&40.)Pxa5,(:.&40.)Pxa6,(:.&40.)Pxa7,(:.&40.)Pxs2,(:.&40.)Pxs3,(:.&40.)Pxs4,(:.&40.)Pxt3,(:.&40.)Pxt4,(:.&40.)Pxt5,(:.&40.)Pxt6,(:.&40.)P,(=.$1.VR,VHIA,Vh,VLB,VLF,Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+30.$>.(?.$9.)R1;.R1:.R19.R18.R17.R16.)P,(3.+22.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,R16.R17.)P,(10.R1=.(4.+22.))P,(10.R1=.(5.Vd,))(11.$1.(12.$1.VR,VHIA,R1=.Vmo,)$13.(14.(15.R18.(16.&40.(17.(18.&40.Vsp,)-30.))Vgp,Vtp,R17.R16.R15.R14.R13.(16.&40.R19.)R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(16.&40.+=6754.)Vfc,(19.(:.&40.))R1;.(1:.$1.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold RFRAME in FR1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    do 6 zstep.
    zstep.
    replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by (clear; lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold RPOST.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 48 RFRAME JC); [exact J| exact HR| exact HK9| exact MF9| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00[0@C41025970927.155D2736047263.154 D67194504253.154K14719093649.155K19496893622.155K39356616831.155L14723926928.2  L19511257639.2  L23643762344.4  L2397676628.0   L28812485200.151L2975768925.2   L29773195157.0  L31378091396.1  L35123631238.2  L35663928186.7  L39346407150.2  L42633816569.1  L54669551926.4  L55736136592.5  L57030252976.1  L60031621599.6  L60098763854.3  L60283674290.6  L6825600392.145 L8163305600.150 L8166013561.149 P14719093649.155Q2507926616.154 Q26295627581.150Q2738228895.154 Q2738261779.147 Q2748717286.150 Q2750469862.150 Q34201322783.153Q50458135125.150Q59999739466.150Q65887500098.152Q65898003402.150Q66983863780.147Q67196423741.154Q67209451076.150Q8958280274.147 00000100E00i00j01^02602702802E02F02Z02a02b02f02m03B03C03H03U03h03l04C04M04_05G06006Y06Z07N07V07b07n08:08F08\08h09:09I09X09j0:<0:N0:VFS2ra2sp1X3xs03pXc2xsS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR2P0FS1R2sp3xs02lo4SLO21N3pXc2xs3HNK5NEEDR3LOS3ALO3NER2PCS1X3xs01N3pXc2xs3HNK3XPcFFS1X1N3pXc3XPcSS2ra2sp1X3xs03pXc2xsS1N3pXcSS2spS2sp2loS1R3HIA1h2sp2lo3TOP1HFS3pXcS2sp1X2lo3DSXS1N2xs4LEN12ws4LENXS2spS2sp2lo1N3pXc4LOSP4XLScS1R2lo3LOSS2sp2lo1N3pXc1a2NOS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR2P03P47S2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR2P04LENXS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR2P04LENXFS1R2sp3xs02lo4SLO21N3pXc2xs3HNK5NEEDR3LOS3ALO3NER2PCS3xs02xsS3xs03pXc2xsS3xs03pXc2xsS3xs03pXc2xsS3xs03pXc2xsS3xs01N3pXc2xs3HNK3P47S3xs03pXc2xsS3xs01N3pXc2xs3HNKS3xs03pXc2xs2P0S3xs03pXc2xs2P0S3xs01N3pXc2xs3HNKS3xs01N3pXc2xs3HNKS3xs01N3pXc2xs3HNKS3xs02xs". (* [comment removed for export] *)
  #[using="IMG JC SLO2"] Lemma r_s3 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p521 ()) "Pv,$6.Pf,$6.Phc,(7.$1.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(:.&40.)(;.(:.&8.))PdXc,$<.Pxra,(:.&40.)Pxt0,(:.&40.)Pxt1,(:.&40.)Pxt2,(:.&40.)Pxs1,(:.&40.)Pxa0,(:.&40.)Pxa1,(:.&40.)Pxa2,(:.&40.)Pxa3,(:.&40.)Pxa4,(:.&40.)Pxa5,(:.&40.)Pxa6,(:.&40.)Pxa7,(:.&40.)Pxs2,(:.&40.)Pxt3,(:.&40.)Pxt4,(:.&40.)Pxt5,(:.&40.)Pxt6,(:.&40.)P,(=.$1.VR,VHIA,Vh,VLB,VLF,Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+30.$>.(?.$9.)R18.R17.R16.R15.R14.R13.)P,(1;.$1<.(1=.R14.)$1>.)P,(10.+22.(1?.R15.))P,Pws,(8.(:.&40.))Pr,$6.P,(20.(21.(22.(23.+2.+1?.))R1.)(10.R1.=))P,(24.(1;.$6.R2.$25.))(3.+22.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,R3.(2.(26.R1:.)(27.R1:.)(1?.R1:.)(28.R1:.)R4.(29.R1:.)(1=.R1:.)))P,(10.R1<.(4.+22.))P,(10.R1<.(5.Vd,))(11.$1.(12.$1.VR,VHIA,R1<.Vmo,)$13.(14.(15.R18.(16.&40.(17.(18.&40.Vsp,)-30.))Vgp,Vtp,R17.R16.R15.(16.&40.(17.(28.R19.)+44.))R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.(16.&40.=)(16.&40.(17.(2:.(17.(28.R19.)+44.)+3.)(2;.(2<.VR,))))Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(16.&40.+=6744.)Vfc,(19.(:.&40.))R1:.(1:.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 EO HNK HR0 BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 48 RFRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX.
    pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1. clear JX.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' own.
    unfold mpi_cells in CX1.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    pose proof LEN1 as LENX.
    unfold RFRAME in FR1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    pose proof (conj J0 I) as J0box. clear J0 HV1 HFR1 FRS1 FRA1 HPX1 OUT1 NM1 MX1 XP1 XLS1 NS1 HCS1 HF1.
    (* [comment removed for export] *)
    shadow_chk OP (pXc + 68) 4.
    wrq XARR LENX 17.
    zstep.
    destruct J0box as [J0 _].
    (match goal with STq : stk asegs ?mq lo (bv_unsigned sp + -48) |- _ => pose proof STq as STM; replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in STM by (clear; lia) end).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    lazymatch type of XARR with u32arr _ _ _ ?l => assert (LENF : length l = length xs) by (clear - LENX LEN1; lia) end.
    assert (HWF : forall a, ~ outside [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 48).
    { intros a NO. cbn [outside fst snd] in NO. assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 48) by (clear - NO; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
    assert (DJF : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] (bv_unsigned sp - 48) 48).
    { cbn. split; [clear - XLSc LOSP; lia| split; [clear; lia| exact I]]. }
    assert (DJX : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] X 16).
    { cbn. split; [clear - XPc; lia| split; [clear - DSX; lia| exact I]]. }
    match goal with MIq : mem_inv asegs mF, HHq : HM asegs R HIA hc LBc LF mF |- _ =>
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ mF _ J0 MU WM MIq STM HHq HWF DJF DJX XARR LENF) as J9 end.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J9.
    eapply r_ret with (r := 0); [exact J9| apply HR0; [clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]| exact BV| exact BF].
    all: match goal with |- ?g => idtac "S3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03i0@C11052782127.178C17025492443.172C24110347431.209C41025970927.184C48465687945.173D17431896540.209D2736047263.183 D30202740465.211D30215712839.209D35540590329.173D40105381855.177D42633159066.211D42645876524.209D46124353855.173D55519686148.209D56475227919.173D56485321117.211D60098826461.211D60109446735.173D6066455549.177 D67194504253.183K11417992427.209K11436977188.209K11774176678.173K14719093649.184K18472349375.178K19496893622.184K21830140982.209K28282495707.208K31141949688.173K32926047287.172K33508533600.208K37974724982.178K39356616831.184K42013958895.173K49968154321.178K61715101887.209K62514807418.209K6518702880.172 K66941307317.173L11414367424.2  L11430812705.11 L11432911257.4  L11433393167.3  L11433393167.4  L11433393167.7  L11433393167.9  L11434749041.10 L11763166039.2  L12238390386.2  L13750712193.1  L14334147345.3  L14724008848.2  L15909478677.4  L15909478708.7  L16596701601.0  L16759534334.13 L16759664763.6  L16760140280.10 L16760140280.11 L16760140280.5  L1685717371.0   L1748702530.4   L18476640837.3  L18482277573.16 L18486753326.2  L19511257639.2  L20179120384.174L20495812378.1  L21842199267.2  L23072471841.0  L23158360938.161L23162605832.164L23162605832.168L23643762344.4  L25075740679.13 L2750943758.1   L28119628375.5  L28270437390.3  L28812485200.180L29323519773.4  L29323912600.11 L29324363740.2  L29325974719.7  L29379457461.1  L2975768925.2   L31154987677.3  L31378091396.1  L31974602906.0  L32296344079.0  L32923425478.3  L33515419425.2  L34125036709.11 L35123631238.2  L35658369193.0  L35663928186.7  L36402544236.4  L36597884286.0  L37353520832.4  L37358039631.150L37374225478.2  L37976573927.2  L38235734261.1  L39346407150.2  L41128898453.2  L42023920670.2  L42633816569.1  L4385124467.2   L43882228554.6  L46134317006.1  L46475141726.3  L46488580170.16 L47796013771.1  L48357452652.4  L48359486980.151L49974642367.2  L50059343616.173L50062002109.172L51645370583.2  L52707419215.3  L53056398486.2  L5391542165.10  L5395470277.11  L5397438741.2   L5397526507.3   L5397526507.4   L5397526507.7   L5397526507.9   L54669551926.4  L57030252976.1  L59063125690.3  L59308548964.169L60031621599.6  L60098763854.3  L60283674290.6  L61288034645.4  L61711433322.2  L62523327698.2  L64384729721.10 L64384729721.11 L64384729721.5  L64385204607.13 L64385598458.6  L65001425081.6  L6514053445.2   L65502327065.170L65897978885.9  L65898110592.2  L65900735189.1  L66151427842.16 L66151427842.17 L66956466619.2  L67072661306.5  L67449985494.4  L6813106154.168 L6825600392.171 L805784116.1    L806333044.3    L807932374.7    L808409686.5    L8163305600.179 L8166005432.178 L8265267294.0   L9591582058.1   L968913461.14   L969306288.7    L969431653.5    L971098898.9    L971407506.8    N27705263330.209N30361834118.209N37104593031.173N4403435184.209 N53586258358.209N62916601611.173N64598165055.173O16836876713.173O17025492443.172O24110347431.209O2451383990.208 O25567854274.209O2726716959.172 O27575595071.208O31708404188.173O32675157126.209O3350605900.209 O43421534469.209O48465687945.173O57399310481.173P11417992427.209P14719093649.184P33508533600.208P49968154321.178P6518702880.172 P66941307317.173Q14330168789.209Q14790846211.187Q14790846217.153Q23874735428.166Q23889447023.170Q2507926616.177 Q2507926616.183 Q26295627581.169Q26295627581.173Q26295627581.176Q2736200051.173 Q2738228895.183 Q2748717286.176 Q2750469862.179 Q27911231108.173Q28526310026.169Q28526310026.173Q28532555266.175Q29313029533.209Q30215712839.209Q31832549797.209Q34201322783.182Q35540590329.173Q3745056394.169 Q3745056394.173 Q38248387216.173Q3857074015.176 Q40103134687.177Q40105169459.166Q40107220390.173Q40107235096.170Q40109429670.169Q40109429670.172Q40109429670.173Q42645876524.209Q43879899724.173Q46124353855.173Q50458135125.169Q50458135125.173Q50458135125.176Q59275590258.209Q59999739466.176Q6062088068.172 Q6064099716.173 Q6068374013.177 Q65887500098.181Q65898003402.176Q66985997188.173Q67196423741.183Q67209451076.179Q7799078285.173 Q8945570073.170 Q8956220466.166 Q8956220466.173 00000100200300400500j01D01l02T03<03W04=04U04m05g06_07e08T09509`0:J0:K0;D0<<0<=0<\0=V0>N0?70?O0@80@90A40AR0An0Ao0Bg0Cj0Ck0Cl0Cm0Cn0Co0D00D10D20D30DV0DW0D^0D_0Dj0Dk0E;0EU0EV0EW0EX0EY0EZ0E[0E\0El0Em0FG0FH0FI0Fa0Fb0Fc0Fd0GP0H<0Hh0I50IT0IY0Ii0Ij0JA0JB0JC0JD0J\0J`0Jg0Jh0Jl0Jm0Jn0Jo0K00KF0KM0KN0Kc0L60L70LG0M40M=0M>0MB0MC0MD0ME0MJ0MK0MR0MW0MX0N20N30NC0O00O10O^0PK0PT0P_0Pf0QM0QN0QO0QP0QQ0QR0QS0Q`0Qd0Qo0R_0S60S@0SR0Sb0Sc0Sd0Se0Sf0Sg0Sh0Si0TA0TB0TZ0T[0Tc0Td0U@0UA0UB0UC0UR0V=0Vh0Vi0Vj0Vk0W70Wc0XO0XP0XQ0XR0XS0XT0XU0XV0Xl0YA0YB0Y^0ZG0Z]0[90[:0[;0[<0[=0[>0[?0[@0[A0[B0[C0[D0[E0[F0[G0[H0[I0[J0[K0[L0[[0\O0]C0]Y0]o0^j0_d0`00`<0`G0`V0`h0a70aF0ai0b<0bO0bb0cE0c[0cm0dF0d\0e20eH0eW0f10fD0fT0fd0g40gD0gT0gd0h40hF0hV0hf0i60iE0iU0ij0j@0jV0jo0kA0kS0kh0l@0lU0le0m10m=0mHFFFFFS1R3HIA1h2ra2sp1X3xs02hc3pXc2xs3TOP2X03SPR3HT12P03wsYS2ra2sp1X3xs03pXc2xs2v32wsS2ra2sp1X3xs01N3pXc2xs3wsY3xs74LEN74LENFS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR2P03wsYS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR3wsZ2P0S2ra2sp1X3xs03pXc2xs2v03wsZS2ra2sp1X3xs03pXc2xs3wsY3xs74LEN74LENFS2ra2sp1X3xs03pXc2xs3wsYS2ra2sp1X3xs03pXc2xs3wsZS1R2ra2sp1X3xs02lo4SLO23pXc2xs5NEEDR3LOS2X03NER3SPR2P03wsYS1R3HIA1h2ra2sp1X3xs02lo2hc3pXc2xs3TOP2X03SPR3HT13wsZ2P0S1R3HIA1h2ra2sp1X3xs02lo2hc3pXc2xs3TOP2X03SPR3HT12P03wsY3xs74LEN74LENFS1R2ra2sp1X3xs02lo3pXc2xs3LOS3wsY3xs74LEN74LENFS1R2ra2sp1X3xs02lo3pXc2xs3LOS3wsZS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR2v03wsZ2P0S2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR2v32P02wsFS1R2sp3xs02lo4SLO21N3pXc2xs5NEEDR3LOS3ALO3NER2PC3wsY4LENBS1R2sp3xs02lo4SLO21N3pXc2xs3HNK5NEEDR3LOS3ALO3NER3wsZ2PCFS1X3xs01N3pXc2xs3HNK2v03wsZ3XPcS1R2sp3xs02lo4SLO21N3pXc2xs3HNK5NEEDR3LOS3ALO3NER2PC2v32wsS1R2sp3xs02lo4SLO21N3pXc2xs3HNK5NEEDR3LOS3ALO3NER2PC3wsYS1R2sp3xs02lo1N3pXc2xs3HNK3LOS3ALO2PC3wsYS2sp1X3xs02lo2xs3DSX3wsZS1R2sp3xs02lo1N3pXc2xs3HNK3LOS3ALO3wsZ2PCFS1R2sp3xs02lo4SLO21N3pXc2xs3HNK5NEEDR3LOS3ALO3NER3wsZ2PC2v0S1X3xs01N3pXc2xs3HNK2v33XPc2wsS1X3xs01N3pXc2xs3HNK3wsZ3XPcFS2sp1X3xs02lo1N3pXc2xs3HNK3x293XPc3wsY3x173x303x315POST0S1R2sp1X3xs02lo4SLO23pXc2xs5NEEDR3DSX3NER3x293wsY3x173x303x315POST0FFFFFFFFFS1R2sp2lo4SLO21N3pXc5NEEDR3NER4XLScFS1N3HNKFS1N3pXc3HNKFS1N3HNK3wsZ4LENXS1N3wsY4LENA4LENB3xs74LEN7SFFFFFSS1N3HNK3wsY4LENXFS2sp2lo1N3pXc3HNK3SPR4XLScFFS2ra2sp1X3xs03pXc2xs3wsZFFSS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR3wsZ2P03P47S2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR3wsZ2P03P47S2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR3wsZ2P03P47S1X1N3pXc3XPcS2sp2lo1N3pXc3HNK3wsZ4XLSc4LENXS3pXcS1R3HIA1h2sp3TOPFS2ra2sp1X3xs03pXc2xs2wsFFFS1R2sp2lo4SLO25NEEDR3NERS2spS1N3pXcFS2spSSFFS2sp2lo1N3pXc3HNK4XLScS2sp2loSS1R3HIA1h2sp2lo3TOP1HS3wsY4LENA3xs74LEN7SS1N3HNK3wsZ4LENXS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR3wsZ2P04LENXS3pXc3wsYFS2loFFFS3pXcFS2sp2loS3pXcFS1R2sp2lo4SLO23NRA3NER3SPRFS1N3HNK3wsZ4LENXS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR3wsZ2P04LENXFS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR3wsZ2P04LENXS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR3wsZ2P04LENXS3pXc3wsYS1N3pXc3HNKS2sp2loS1R2sp2lo4SLO21N3pXc3HNK5NEEDR3NER4XLScFFFFFFS2sp1X2lo3DSXS2spS1N3pXc3HNKS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR3wsZ2P04LENX2NES2sp2lo1N3pXc4LOSP4XLScS1R2lo3LOSS2sp2lo1N3pXc1a2NOS1N3HNK3wsY4LENXFFFFFFFS1N2xs4LEN13wsY3xs74LENXFS2ra2sp1X3xs03pXc2xs3wsZFS3pXc2P0FS3pXc2r04XPAL1q1r1H2H02q02H4FFFS1N3pXc3HNK3P47S2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR2P03P472wsS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR2P03P472wsFFFS2sp3SPA3SPRS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR2P02ws4LENXS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR2P02ws4LENXSFFFFFFS3xs03pXc2xs3wsY3x321CS2sp3xs02xs3wsY3x321CFS3xs01N3pXc2xs3HNK3wsY3x321CS1R2sp3xs02lo4SLO22xs5NEEDR3NER3wsY3x321CS3xs03pXc2xs3wsZ3x151CS3xs01N3pXc2xs3HNK3wsZ3x151CFFFFFFFFFFFFFFFFFFFS2sp3xs02xs3wsYS1R2sp3xs02lo4SLO22xs5NEEDR3LOS4SP643ALO3ACP3NER3wsYS1R2sp3xs02lo4SLO22xs5NEEDR3LOS4SP643ALO3ACP3NER3wsZS3xs01N3pXc2xs3HNK3wsZS3xs01N3pXc2xs3HNK3wsZS1R2sp3xs02lo4SLO21N3pXc2xs3HNK5NEEDR3LOS3ALO3NER2v03wsZ2PCS1R2sp3xs02lo4SLO21N3pXc2xs3HNK5NEEDR3LOS3ALO3NER2v32PC2wsS3xs02xs3wsZS3xs02xs3wsZS3xs02xs2wsS3xs03pXc2xs2wsS3xs03pXc2xs2v32wsS3xs03pXc2xs2wsS3xs03pXc2xs2wsS1R2sp3xs02lo4SLO22xs5NEEDR3NER3wsZS3xs03pXc2xs3wsZ2P0S3xs03pXc2xs3wsZ2P0S3xs03pXc2xs3wsZ2P0S1R2sp3xs02lo4SLO22xs5NEEDR3NER3wsYS3xs01N3pXc2xs3HNK3wsYS2sp3xs02lo2xs3wsYS3xs01N3pXc2xs3HNK3P472wsS3xs01N3pXc2xs3HNK3wsZS3xs01N3pXc2xs3HNK3wsZS3xs01N3pXc2xs3HNK3wsZS3xs02lo2xs3wsZS3xs01N3pXc2xs3HNK3wsZ3P47S3xs03pXc2xs3wsZ2v0S3xs03pXc2xs3wsZS3xs03pXc2xs3wsZS3xs03pXc2xs3wsZS3xs03pXc2xs3wsZS3xs03pXc2xs3wsZS3xs03pXc2xs3wsZS3xs03pXc2xs3wsYS2sp3xs02lo2xs3wsZS3xs03pXc2xs3wsZS3xs03pXc2xs3wsZS3xs03pXc2xs3wsZS3xs03pXc2xs2wsS3xs03pXc2xs3wsYS3xs01N3pXc2xs3HNK2wsS3xs01N3pXc2xs3HNK3wsZS3xs01N3pXc2xs3HNK3wsZS3xs01N3pXc2xs3HNK3wsZ2v0S3xs03pXc2xs2P02wsS3xs03pXc2xs2P02wsS3xs01N3pXc2xs3HNK2wsS3xs01N3pXc2xs3HNK2v32wsS3xs01N3pXc2xs3HNK2wsS3xs03pXc2xs3wsZS3xs02xs3wsZS3xs02xs3wsZS3xs02xs2ws". (* [comment removed for export] *)
  #[using="IMG AMS JC SLO2"] Lemma r_s2 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p521 ()) "Pv,$6.Pf,$6.Phc,(7.$1.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(:.&40.)(;.(:.&8.))PdXc,$<.Pxra,(:.&40.)Pxt0,(:.&40.)Pxt1,(:.&40.)Pxt2,(:.&40.)Pxa0,(:.&40.)Pxa1,(:.&40.)Pxa2,(:.&40.)Pxa3,(:.&40.)Pxa4,(:.&40.)Pxa5,(:.&40.)Pxa6,(:.&40.)Pxa7,(:.&40.)Pxs2,(:.&40.)Pxt3,(:.&40.)Pxt4,(:.&40.)Pxt5,(:.&40.)Pxt6,(:.&40.)P,(=.$1.VR,VHIA,Vh,VLB,VLF,Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+30.$>.(?.$9.)R17.R16.R15.R14.R13.R12.)P,(1;.$1<.(1=.R13.)$1>.)P,(10.+22.(1?.R14.))P,Pws,(8.(:.&40.))Pr,$6.P,(20.(21.(22.(23.+2.+1?.))R1.)(10.R1.=))P,(24.(1;.$6.R2.$25.))(3.+22.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,R3.(2.(26.R19.)(27.R19.)(1?.R19.)(28.R19.)R4.(29.R19.)(1=.R19.)))P,(10.R1;.(4.+22.))P,(10.R1;.(5.Vd,))(11.$1.(12.$1.VR,VHIA,R1;.Vmo,)$13.(14.(15.R17.(16.&40.(17.(18.&40.Vsp,)-30.))Vgp,Vtp,R16.R15.R14.(16.&40.(17.(28.R18.)+44.))(16.&40.(28.R18.))R13.R12.R11.R10.R?.R>.R=.R<.R;.(16.&40.=)(16.&40.(2;.(2<.VR,)))Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(16.&40.+=66<4.)Vfc,(19.(:.&40.))R19.(1:.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 EO HNK HR0 BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 48 RFRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX.
    pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1. clear JX.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' own.
    unfold mpi_cells in CX1.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    pose proof LEN1 as LENX.
    unfold RFRAME in FR1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    pose proof (conj J0 I) as J0box. clear J0 HV1 HFR1 FRS1 FRA1 HPX1 OUT1 NM1 MX1 XP1 XLS1 NS1 HCS1 HF1.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch type of XARR with u32arr _ _ _ ?l => remember l as wsZ eqn:EwsZ in XARR, LENX; clear EwsZ end.
    split3 XARR 17 17 PUlo PUmid PUtop.
    change (4 * Z.of_nat (Z.to_nat 17)) with 68 in PUmid, PUtop.
    pose proof (conj PUlo I) as PUloB. pose proof (conj PUtop I) as PUtopB. clear PUlo PUtop XARR.
    rename MU into MUA; rename WM into WMA.
    lazymatch type of PUmid with u32arr _ ?mm _ _ => pose proof (munch_refl [(pXc + 68, pXc + 68 + 68); (lo, bv_unsigned sp + -48)] mm) as MU; pose proof (wmono_refl asegs mm) as WM end.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_EC) as SPM. unfold A_ASAN_MEMSET_EC in SPM.
    acallxA_sp (bv_unsigned sp + -48)
      (eapply SPM with (h := hc) (LB := LBc) (LF := LF) (DST := pXc + 68) (v := 0) (n := 68) (lo := lo) (ds := u32s (firstn (Z.to_nat 17) (skipn (Z.to_nat 17) wsZ)));
       rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by qlia;
       try eassumption; try reflexivity;
       first [ left; rewrite AMS; reflexivity
             | apply MpiWalkAux.u8arr_of_u32arr; exact PUmid
             | rewrite u32s_length, firstn_length_le by (rewrite length_skipn; clear - LENX HNK; lia); clear; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear - HNK; lia]
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NER NEEDR; lia]
             | eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear - HNK; lia]
             | rewrite HT1; clear - TOP; lia
             | f_equal; clear; lia
             | apply bv_eq; rewrite bv_eqb_Z in KC; apply Z.eqb_eq in KC; exact KC
             | right; clear - P47 HNK; lia
             | clear - XLSc SLO2 NER NEEDR NRA HNK NR1 LOS SPA SPR LOSP; lia
             | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]).
    clear SPM.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMSET-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with Hz : u8arr asegs m6 (pXc + 68) _ |- _ => rename Hz into HPZ end.
    destruct PUloB as [PUlo _]. destruct PUtopB as [PUtop _].
    pose proof (u32arr_transport asegs _ _ m6 _ _ PUlo MU WM) as PUlo6. rewrite firstn_length_le in PUlo6 by (clear - LENX HNK; lia).
    specialize (PUlo6 ltac:(cbn [disjoint_from]; clear - XLSc SLO2 NER NEEDR P0 HNK; lia)).
    pose proof (u32arr_transport asegs _ _ m6 _ _ PUtop MU WM) as PUtop6. rewrite !length_skipn in PUtop6.
    specialize (PUtop6 ltac:(cbn [disjoint_from]; clear - XLSc SLO2 NER NEEDR P0 HNK LENX; lia)).
    replace (Z.to_nat 68) with (4 * Z.to_nat 17)%nat in HPZ by (clear; lia).
    apply (rw_cells_of_u8arr asegs) in HPZ.
    assert (XARR : u32arr asegs m6 pXc (firstn (Z.to_nat 17) wsZ ++ repeat (Z_to_bv 64 0) (Z.to_nat 17) ++ skipn (Z.to_nat 17) (skipn (Z.to_nat 17) wsZ))).
    { apply u32arr_app. split; [exact PUlo6|]. rewrite firstn_length_le by (clear - LENX HNK; lia). change (4 * Z.of_nat (Z.to_nat 17)) with 68.
      apply u32arr_app. split; [eapply (u32arr_of_cells asegs); [exact HPZ| symmetry; apply u32s_repeat0]|].
      rewrite repeat_length. change (4 * Z.of_nat (Z.to_nat 17)) with 68. exact PUtop6. }
    assert (LENX6 : Z.of_nat (length (firstn (Z.to_nat 17) wsZ ++ repeat (Z_to_bv 64 0) (Z.to_nat 17) ++ skipn (Z.to_nat 17) (skipn (Z.to_nat 17) wsZ))) = N).
    { rewrite !length_app, repeat_length, !length_skipn, firstn_length_le by (clear - LENX HNK; lia). clear - LENX HNK. lia. }
    clear MU WM LENX PUlo PUtop PUlo6 PUtop6 HPZ. rename MUA into MU; rename WMA into WM; rename LENX6 into LENX.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OP (pXc + 64) 4.
    (* [comment removed for export] *)
    rdq XARR 16 RD1. zabsorb. clear RD1.
    (* [comment removed for export] *)
    vstep 12%positive. wrq XARR LENX 16.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OP (pXc + 68) 4.
    (* [comment removed for export] *)
    vstep 11%positive. vstep 18%positive. vstep 10%positive. wrq XARR LENX 17.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch type of XARR with u32arr _ _ _ ?l => remember l as wsY eqn:EwsY in XARR, LENX; clear EwsY end.
    pose proof XARR as PU. rewrite <- (firstn_skipn 17 wsY) in PU. apply u32arr_app in PU. destruct PU as [PA PB].
    rewrite firstn_length_le in PB by (clear - LENX HNK; lia). change (4 * Z.of_nat 17) with 68 in PB.
    assert (LENA : Z.of_nat (length (firstn 17 wsY)) = 17) by (rewrite firstn_length_le by (clear - LENX HNK; lia); reflexivity).
    assert (LENB : Z.of_nat (length (skipn 17 wsY)) = N - 17) by (rewrite length_skipn; clear - LENX HNK; lia).
    pose proof (conj PB I) as PBbox. clear XARR.
    lazymatch type of PA with u32arr _ ?mm _ _ => pose proof (munch_refl [(pXc, pXc + 4 * 17); (bv_unsigned sp + -48 - MPI_CORE_ADD_STACK_A, bv_unsigned sp + -48)] mm) as MU2; unfold MPI_CORE_ADD_STACK_A in MU2; pose proof (wmono_refl asegs mm) as WM2;
      pose proof (hm_abase asegs R HIA hc LBc LF mm ltac:(eassumption)) as AB2 end.
    pose proof (A_mpi_core_add_spec AL IMG) as SPC. unfold mpi_core_add_stmtA, mpi_core_add_postA, A_MPI_CORE_ADD, MPI_CORE_ADD_STACK_A in SPC.
    acallxA_sp (bv_unsigned sp + -48)
      (eapply SPC with (X := pXc) (A := pXc) (B := pXc + 68) (n := 17) (lo := lo) (xs := firstn 17 wsY) (ys := firstn 17 wsY) (zs := skipn 17 wsY);
       rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by qlia;
       try eassumption; try reflexivity;
       first [ apply u32arr_ro; exact PA
             | apply u32arr_ro; exact PB
             | clear; lia
             | rewrite LENA; clear; lia
             | rewrite LENB; clear - HNK; lia
             | left; split; reflexivity
             | right; right; rewrite LENA; clear; lia
             | clear - XPAL; Z.div_mod_to_equations; lia
             | clear - P0; lia
             | unfold MPI_CORE_ADD_STACK_A; clear - SLO2 NER NEEDR LOS; lia
             | clear - SPA SPR LOSP; lia
             | unfold MPI_CORE_ADD_STACK_A; rewrite LENA; clear - XLSc SLO2 NER NEEDR HNK; lia
             | unfold MPI_CORE_ADD_STACK_A; rewrite LENB; clear - XLSc SLO2 NER NEEDR HNK; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear - HNK; lia]
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NER NEEDR; lia]
             | match goal with |- ?g => idtac "CADD-PRE-LEFT:" g end ]).
    clear SPC.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-CADD-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    match goal with Hq : u32arr asegs m7 pXc ?l, H2 : length ?l = length (firstn 17 wsY) |- _ => rename Hq into PA7; rename H2 into LEN7; rename l into xs7 end.
    destruct PBbox as [PBo _].
    first [ match goal with PBq : u32arr asegs m7 (pXc + 68) _ |- _ => rename PBq into PB7 end
          | pose proof (u32arr_transport asegs _ _ m7 _ _ PBo MU2 WM2) as PB7; rewrite LENB in PB7;
            specialize (PB7 ltac:(cbn [disjoint_from]; clear - XLSc SLO2 NER NEEDR P0 HNK; lia)) ].
    assert (XARR : u32arr asegs m7 pXc (xs7 ++ skipn 17 wsY)).
    { apply u32arr_app. split; [exact PA7|]. replace (4 * Z.of_nat (length xs7)) with 68 by (clear - LEN7 LENA; lia). exact PB7. }
    assert (LENX7 : Z.of_nat (length (xs7 ++ skipn 17 wsY)) = N) by (rewrite length_app; clear - LEN7 LENA LENB HNK; lia).
    clear LENX MU2 WM2 PA7 PB7 PBo. rename LENX7 into LENX.
    destruct J0box as [J0 _].
    (match goal with STq : stk asegs ?mq lo (bv_unsigned sp + -48) |- _ => pose proof STq as STM; replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in STM by (clear; lia) end).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    lazymatch type of XARR with u32arr _ _ _ ?l => assert (LENF : length l = length xs) by (clear - LENX LEN1; lia) end.
    assert (HWF : forall a, ~ outside [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 48).
    { intros a NO. cbn [outside fst snd] in NO. assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 48) by (clear - NO; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
    assert (DJF : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] (bv_unsigned sp - 48) 48).
    { cbn. split; [clear - XLSc LOSP; lia| split; [clear; lia| exact I]]. }
    assert (DJX : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] X 16).
    { cbn. split; [clear - XPc; lia| split; [clear - DSX; lia| exact I]]. }
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HHF. cbn [app] in HHF.
    apply (hm_munch asegs R HIA hc LBc LF [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] mc mF) in HHF; [| exact MU| exact WM| solve_w_writable].
    match goal with MIq : mem_inv asegs mF, HHq : HM asegs R HIA hc LBc LF mF |- _ =>
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ mF _ J0 MU WM MIq STM HHq HWF DJF DJX XARR LENF) as J9 end.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J9.
    lazymatch type of J9 with XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?dd => eapply (r_s3 _ _ _ _ _ dd) end;
      [exact J9| reflexivity| exact HNK| exact HR0| exact BV| exact BF].
    all: match goal with |- ?g => idtac "S2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02;0@C24112444547.177D19402610976.177D30202740465.176D30213615715.177D42633159066.176D42643779336.177D56485321117.176D590406392.177  D60098826461.176K11420089551.177K21828043794.177K28284592895.176K38110079326.177K51413406464.177K61717199003.177K66625715780.176L10086398133.1  L11414367424.2  L12238390386.2  L12684653604.3  L13750712193.1  L15909478708.7  L1748702530.4   L20788141597.4  L20788534424.11 L20789001948.2  L20790535615.7  L21286346697.10 L21286477132.3  L21288992743.2  L21842199267.2  L23100341967.144L23597864534.1  L23599440387.2  L23599571078.9  L23643762344.4  L23675662835.3  L26056305788.2  L26056740062.4  L26056880618.3  L26058837719.3  L26058968146.10 L2750943758.1   L28270437390.3  L2975768925.2   L31378091396.1  L32398930337.0  L35123631238.2  L35658369193.0  L35663928186.7  L36402544236.4  L36597884286.0  L37374225478.2  L38103920594.2  L38235734261.1  L41128898453.2  L41425388208.3  L42633816569.1  L43882228554.6  L47796013771.1  L51413275505.10 L51415057167.3  L51415057167.7  L51415057167.9  L51415507885.5  L51415637657.4  L51417604516.4  L51417735969.11 L51645370583.2  L52177866465.13 L52177996900.6  L52179580977.5  L52179941318.11 L52180155462.10 L5260161664.143 L52707419215.3  L54669551926.4  L57030252976.1  L58610993813.10 L58612698133.2  L58612718315.3  L58612718315.7  L58612718315.9  L58613234249.5  L58614938309.11 L58615330880.4  L59111715361.1  L59112227965.4  L60031621599.6  L60098763854.3  L60283674290.6  L61288034645.4  L61711433322.2  L65001425081.6  L66151427842.16 L66151427842.17 L66638883873.2  L7630606937.13  L7630999772.6   L7632612222.11  L7633051902.10  L7633626249.5   L805784116.1    L806333044.3    L807932374.7    L808409686.5    L9591582058.1   L968913461.14   L969306288.7    L969431653.5    L971098898.9    L971407506.8    N12460094892.177N28225170738.177N32130546710.177N6320619906.177 O12136774050.177O24112444547.177O25565757158.177O27573497883.176O43419437345.177O54191722898.176O65857858408.177P11420089551.177P66625715780.176Q12370813529.149Q14790846211.156Q17207202535.148Q20800728249.177Q25263129329.177Q30213615715.177Q31990265985.177Q37625424133.148Q42643779336.177Q5485174314.149 Q5485487896.148 Q59277687382.177Q59703481013.149Q6143569392.149 00000100k01S02;02a03904?05405c05d06\07E08?09809g09h09l09m0:40:50:60:P0:`0:a0:b0:c0;;0;<0;=0;>0;?0;S0;T0;\0;]0;j0;k0;l0<70<80<90<:0<?0<@0<G0<K0<L0<S0<T0<i0=<0==0=F0=G0=K0=L0=W0=\0=c0=d0>G0>H0>I0>J0>K0>L0>M0>N0>W0>X0>Y0>Z0>[0>\0?70?B0?O0?S0@:0@;0@<0@=0@>0@?0@@0@A0@B0@Q0@h0A20AD0AT0AU0Am0BI0BJ0BK0BL0BM0BN0BO0BP0BQ0BR0BS0B_0B`0Ba0Bb0Bc0Bd0Be0CA0CV0Cl0DU0DV0DW0DX0DY0DZ0D[0D\0D]0D^0E90Em0F70FZ0Fi0G?0GQ0G[0Gk0H50H?0HO0HP0HZFS1R2ra2sp1X3xs02lo4SLO23pXc2xs5NEEDR3LOS2X03NER3SPR3wsY2P0S2ra2sp1X3xs01N3pXc2xs3wsY3xs74LEN74LENFS2ra2sp1X3xs01N3pXc2xs3HNK2X03SPR3wsY2P0S2ra2sp1X3xs03pXc2xs3wsY3xs74LEN74LENFS2ra2sp1X3xs03pXc2xs3wsYS1R3HIA1h2ra2sp1X3xs02lo2hc3pXc2xs3TOP2X03SPR3HT13wsY2P03xs74LEN74LENFS1R3HIA1h2ra2sp1X3xs02hc3pXc2xs3TOP2X03SPR3HT13wsY2P0S1R2ra2sp1X3xs02lo3pXc2xs3LOS3wsY3xs74LEN74LENFFS1R2sp3xs02lo4SLO21N3pXc2xs3HNK5NEEDR3LOS3ALO3NER3wsY2PCS1R2sp3xs02lo1N3pXc2xs3HNK3LOS3ALO3wsY2PCS1R2sp1X3xs02lo4SLO23pXc2xs5NEEDR3DSX3NER3x143wsY3x154POSTS1R2sp3xs02lo4SLO21N3pXc2xs5NEEDR3LOS3ALO3NER3wsY2PC4LENBS2sp1X3xs02lo1N3pXc2xs3HNK3x143wsY3XPc3x154POSTFS2spFS1N3HNKFFS1N3wsY4LENA4LENB3xs74LEN7S1N3HNK3wsY4LENXFFFS1R2sp2lo4SLO25NEEDR3NERFFFFS2ra2sp1X3xs03pXc2xsFS3pXc2P0FS1X1N3pXc3XPcFFS1N3pXc3P47FFFS3pXcFS1N3pXcS2spSS2sp2loSS1R3HIA1h2sp2lo3TOP1HS3wsY4LENA3xs74LEN7SS3pXc3wsYFS2loFS1N3pXc3HNKS3pXcS2sp2loFS1R2sp2lo4SLO21N3pXc5NEEDR3NER4XLScFFFFFFFS3pXc3wsYFFFFFS2ra2sp1X3xs03pXc2xs2X03X16S1N3pXc3HNKS2sp1X2lo3DSXS2spS1R2sp2lo4SLO21N3pXc3HNK5NEEDR3NER4XLScFFFFFFFFS1N3pXc3HNK3P47S2sp2lo1N3pXc4LOSP4XLScS1R2lo3LOSS2sp2lo1N3pXc1a2NOS1N3HNK3wsY4LENXFS1N2xs4LEN13wsY3xs74LENXS3pXc2r04XPAL1q1r1H2H02q02H4FFFFFFFFFFS2sp3SPA3SPRFFFFFFS3xs01N3pXc2xs3HNK3wsY3x161CS2sp3xs02xs3wsY3x161CS3xs03pXc2xs3wsY3x161CS1R2sp3xs02lo4SLO22xs5NEEDR3NER3wsY3x161CFFFFFFFFFS2ra2sp1X3xs03pXc2xs2X03XALS1R2sp3xs02lo4SLO22xs5NEEDR3LOS4SP643ALO3ACP3NER3wsYS1X3xs02xsS1R2sp3xs02lo4SLO22xs5NEEDR3NER3wsYS2sp3xs02xs3wsYS3xs01N3pXc2xs3HNK3wsYS2sp3xs02lo2xs3wsYS1X3xs02xsS3xs03pXc2xs3wsYS1X3xs02xsS1X3xs02xsS3xs03pXc2xs3wsYFS1X3xs02xs". (* [comment removed for export] *)
  #[using="IMG AMS JC SLO2"] Lemma r_body : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p521 ()) "Pv,$6.Pf,$6.Phc,(7.$1.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(:.&40.)(;.(:.&8.))PdXc,$<.Pxra,(:.&40.)Pxt0,(:.&40.)Pxt1,(:.&40.)Pxt2,(:.&40.)Pxs1,(:.&40.)Pxa1,(:.&40.)Pxa2,(:.&40.)Pxa3,(:.&40.)Pxa4,(:.&40.)Pxa5,(:.&40.)Pxa6,(:.&40.)Pxa7,(:.&40.)Pxs2,(:.&40.)Pxs3,(:.&40.)Pxt3,(:.&40.)Pxt4,(:.&40.)Pxt5,(:.&40.)Pxt6,(:.&40.)P,(=.$1.VR,VHIA,Vh,VLB,VLF,Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+30.$>.(?.$9.)R18.R17.R16.R15.R14.R13.)P,(1;.$1<.(1=.R14.)$1>.)P,(10.+22.(1?.R15.))P,Pws,(8.(:.&40.))Pr,$6.P,(20.(21.(22.(23.+2.+1?.))R1.)(10.R1.=))P,(24.(1;.$6.R2.$25.))(3.+22.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,R3.(2.(26.R1:.)(27.R1:.)(1?.R1:.)(28.R1:.)R4.(29.R1:.)(1=.R1:.)))P,(10.R1<.(4.+22.))P,(10.R1<.(5.Vd,))(11.$1.(12.$1.VR,VHIA,R1<.Vmo,)$13.(14.(15.R18.(16.&40.(17.(18.&40.Vsp,)-30.))Vgp,Vtp,R17.R16.R15.(16.&40.VX,)R14.(16.&40.=)R13.R12.R11.R10.R?.R>.R=.R<.R;.(16.&40.(2;.(2<.VR,)))Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(16.&40.+=6678.)Vfc,(19.(:.&40.))R1:.(1:.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 EO HNK HR0 BV BF.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 48 RFRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX.
    pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1. clear JX.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' own.
    unfold mpi_cells in CX1.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    pose proof LEN1 as LENX.
    unfold RFRAME in FR1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    pose proof (conj J0 I) as J0box. clear J0 HV1 HFR1 FRS1 FRA1 HPX1 OUT1 NM1 MX1 XP1 XLS1 NS1 HCS1 HF1.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    do 7 zstep.
    lazymatch type of XARR with u32arr _ _ _ ?l => remember l as wsY eqn:EwsY in XARR, LENX; clear EwsY end.
    pose proof XARR as PU. rewrite <- (firstn_skipn 17 wsY) in PU. apply u32arr_app in PU. destruct PU as [PA PB].
    rewrite firstn_length_le in PB by (clear - LENX HNK; lia). change (4 * Z.of_nat 17) with 68 in PB.
    assert (LENA : Z.of_nat (length (firstn 17 wsY)) = 17) by (rewrite firstn_length_le by (clear - LENX HNK; lia); reflexivity).
    assert (LENB : Z.of_nat (length (skipn 17 wsY)) = N - 17) by (rewrite length_skipn; clear - LENX HNK; lia).
    pose proof (conj PB I) as PBbox. clear XARR.
    pose proof (munch_refl [(pXc, pXc + 4 * 17); (bv_unsigned sp + -48 - MPI_CORE_MLA_STACK_A, bv_unsigned sp + -48)] mc) as MU2; unfold MPI_CORE_MLA_STACK_A in MU2; pose proof (wmono_refl asegs mc) as WM2.
    pose proof (A_mpi_core_mla_spec AL IMG) as SPC. unfold mpi_core_mla_stmtA, mpi_core_mla_postA, A_MPI_CORE_MLA, MPI_CORE_MLA_STACK_A in SPC.
    acallxA_sp (bv_unsigned sp + -48)
      (eapply SPC with (D := pXc) (dl := 17) (S := pXc + 68) (sl := 17) (lo := lo) (ds := firstn 17 wsY) (ss := skipn 17 wsY);
       rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by qlia;
       try eassumption; try reflexivity;
       first [ apply u32arr_ro; exact PB
             | clear; lia
             | rewrite LENA; clear; lia
             | rewrite LENB; clear - HNK; lia
             | right; right; rewrite LENA; clear; lia
             | clear - XPAL; Z.div_mod_to_equations; lia
             | clear - P0; lia
             | right; clear - P0; lia
             | rewrite LENA; clear - P47 HNK; lia
             | rewrite LENB; clear - P47 HNK; lia
             | unfold MPI_CORE_MLA_STACK_A; clear - SLO2 NER NEEDR LOS; lia
             | clear - SPA SPR LOSP; lia
             | unfold MPI_CORE_MLA_STACK_A; rewrite LENA; clear - XLSc SLO2 NER NEEDR HNK; lia
             | unfold MPI_CORE_MLA_STACK_A; rewrite LENB; clear - XLSc SLO2 NER NEEDR HNK; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear - HNK; lia]
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NER NEEDR; lia]
             | match goal with |- ?g => idtac "MLA-PRE-LEFT:" g end ]).
    clear SPC.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MLA-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    match goal with Hq : u32arr asegs m7 pXc ?l, H2 : length ?l = length (firstn 17 wsY) |- _ => rename Hq into PA7; rename H2 into LEN7; rename l into xs7 end.
    destruct PBbox as [PBo _].
    first [ match goal with PBq : u32arr asegs m7 (pXc + 68) _ |- _ => rename PBq into PB7 end
          | pose proof (u32arr_transport asegs _ _ m7 _ _ PBo MU2 WM2) as PB7; rewrite LENB in PB7;
            specialize (PB7 ltac:(cbn [disjoint_from]; clear - XLSc SLO2 NER NEEDR P0 HNK; lia)) ].
    assert (XARR : u32arr asegs m7 pXc (xs7 ++ skipn 17 wsY)).
    { apply u32arr_app. split; [exact PA7|]. replace (4 * Z.of_nat (length xs7)) with 68 by (clear - LEN7 LENA; lia). exact PB7. }
    assert (LENX7 : Z.of_nat (length (xs7 ++ skipn 17 wsY)) = N) by (rewrite length_app; clear - LEN7 LENA LENB HNK; lia).
    clear LENX MU2 WM2 PA7 PB7 PBo. rename LENX7 into LENX.
    destruct J0box as [J0 _].
    (match goal with STq : stk asegs ?mq lo (bv_unsigned sp + -48) |- _ => pose proof STq as STM; replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in STM by (clear; lia) end).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    lazymatch type of XARR with u32arr _ _ _ ?l => assert (LENF : length l = length xs) by (clear - LENX LEN1; lia) end.
    assert (HWF : forall a, ~ outside [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 48).
    { intros a NO. cbn [outside fst snd] in NO. assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 48) by (clear - NO; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
    assert (DJF : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] (bv_unsigned sp - 48) 48).
    { cbn. split; [clear - XLSc LOSP; lia| split; [clear; lia| exact I]]. }
    assert (DJX : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] X 16).
    { cbn. split; [clear - XPc; lia| split; [clear - DSX; lia| exact I]]. }
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HHF. cbn [app] in HHF.
    apply (hm_munch asegs R HIA hc LBc LF [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -48)] mc mF) in HHF; [| exact MU| exact WM| solve_w_writable].
    match goal with MIq : mem_inv asegs mF, HHq : HM asegs R HIA hc LBc LF mF |- _ =>
      pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ mF _ J0 MU WM MIq STM HHq HWF DJF DJX XARR LENF) as J9 end.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J9.
    lazymatch type of J9 with XJA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?dd => eapply (r_s2 _ _ _ _ _ dd) end;
      [exact J9| reflexivity| exact HNK| exact HR0| exact BV| exact BF].
    all: match goal with |- ?g => idtac "S1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01H0@D11189028015.115D11189028015.116D33586717206.116D35881667587.115D35881667587.116D9071893887.150 D9377647540.153 L11246298883.112L11741095640.111L14158341354.0  L14381209145.0  L19354909044.112L19841622416.153L25382082548.112L26924648792.112L28119579349.23 L29010569984.153L30092191652.8  L31378308326.111L31392867444.112L31486427280.23 L31792063299.6  L35653441506.7  L36926558666.0  L37414286068.112L40290687782.1  L40834179097.117L40978259644.7  L4202106291.112 L42243864115.23 L43059266230.109L43442376564.111L43654564952.112L49631015752.1  L5261871668.3   L57030252976.1  L59308632561.1  L59360765542.9  L59411595710.2  L59499841752.112L60098763854.3  L62998051744.23 L64491265552.2  L7510805464.112 L808409686.23   P30094500526.153Q14793205526.118Q14793270804.153Q15643324129.111Q18365925601.112Q18696506101.117Q21800401414.117Q25160350961.117Q25513505925.114Q25513505925.115Q25604052563.112Q25604052563.113Q25664719138.117Q27907200258.112Q30094500526.153Q31226872993.117Q31396957457.117Q32655500769.112Q33721217258.113Q33918256002.112Q35016271767.117Q35715139857.117Q37821600610.114Q37821600610.115Q3830427394.112 Q39939554818.112Q4141071397.117 Q44648843873.112Q49698585326.113Q49698585326.114Q51235796833.112Q53972118266.117Q57198265401.115Q59843137889.112Q61800308129.117Q6414620453.117 Q64253126389.117Q64706984570.151Q64706984570.152Q66522067074.112Q67528989526.115Q67528989526.116Q9843367298.111 00000k02203003X04O04P04l05905F05G05H05U06106>06K06[06\06]06j07707;07S07k07l08908<08Z09409A09W09l0:90:F0:J0:T0:X0:\0;<0;?0;L0;V0;i0;o0<<0<H0<I0=H0>G0>R0>]0?;0?<0?Z0@70@`0@k0A60A70AG0AH0Ag0B>0BI0BT0Bd0CC0CD0Cf0DQ0Da0E10E20E=0ES0Ei0F40FS0G50G@0GA0G_0G`0Ga0Gb0H20HT0IB0IRS1R2ra2sp1X3xs02lo4SLO25NEEDR3LOS2X03NER3SPR2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02lo4SLO25NEEDR3LOS2X03NER3SPR2HB5Ha_st5Hl_st2s12s22s3S1R2ra2sp2s41X3xs02lo4SLO25NEEDR3LOS2X03NER3SPR2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X3xs03TOP2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs03TOP2HB5Ha_st5Hl_st2s12s22s32s4FS2ra2sp2s02s12s22s32s41X3xs0S2ra2sp1X3xs0S2ra2sp1X3xs0SSS2ra2sp1X3xs0S2ra2sp2s02s12s22s32s41X3xs0S2ra2sp1X3xs0S2ra2sp1X3xs0S1R3HIA1h2sp3TOPFFS2ra2sp1X3xs0S2ra2sp1X3xs0S2spS1R2sp2lo4SLO25NEEDR3NERS1R3HIA1h2sp2lo3TOP4HTOPSS2ra2sp1X3xs0S1XS1R2ra2sp2s02s12s22s32s41X3xs0S1X2sX2nX2pX3xs04padX4ownXS2ra2sp1X3xs0S1R2sp2lo4SLO23NER3SPRS2ra2sp1X3xs02lo4LOSPS2ra2sp1X3xs0S2ra2sp1X3xs0S2spS1X2X03X16S2spS2KRS2sp1X2sX2nX2pX3xs04padX4ownX2XLS1dS2ra2sp1X3xs0S1R2lo3LOSS1R3HIA1h2sp1d4BUDFS1d2D0S2ra2sp1X3xs0S2sp3SPA3SPRFS1R2ra2sp2s02s12s22s32s43xs02lo4SLO25NEEDR3LOS4SP643ALO3ACP3NERS1R2ra2sp2s02s12s22s32s43xs02lo4SLO25NEEDR3LOS4SP643ALO3ACP3NERS2sp3xs02loS2sp3xs02loS1R2ra2s02s12s22s32s43xs04IMG'FS1R2ra2s02s12s22s32s43xs04IMG'S2ra2sp3xs02lo2HB5Ha_st5Hl_stS2sp2s03xs02lo2HB5Ha_st5Hl_st2s12s22s32s4S2sp3xs02HBS2sp3xs02HBFS2sp3xs02lo4LOSPFS1R2ra2s02s12s22s32s43xs05ALWF'S2ra2s02s12s22s32s43xs0S2sp3xs02loS2sp3xs02HBS2sp3xs02lo4LOSPS1R2ra2s02s12s22s32s43xs05ALWF'FS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s12s22s3S2sp3xs02lo4LOSPS2sp3xs02lo4LOSPFS2sp3xs02loS2sp3xs04SP642HB5Ha_stS2sp3xs04SP642HB5Ha_stS2sp3xs02loS1R2ra2s02s12s22s32s43xs05ALWF'S2sp2s43xs02lo4LOSP2HB5Ha_st5Hl_stS2sp3xs02loFS1R2ra2s02s12s22s32s43xs04IMG'FFFS2sp3xs02lo4LOSPS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s12s22s32s4S2sp3xs02lo4LOSP". (* [comment removed for export] *)
  #[using="IMG GROW AMS JC TPV UWX D0 BUD BUDF C24H SLO2"] Lemma r_main : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p521 ()) "Pt0,(:.&40.)Pt1,(:.&40.)Pt2,(:.&40.)Pa1,(:.&40.)Pa2,(:.&40.)Pa3,(:.&40.)Pa4,(:.&40.)Pa5,(:.&40.)Pa6,(:.&40.)Pa7,(:.&40.)Pt3,(:.&40.)Pt4,(:.&40.)Pt5,(:.&40.)Pt6,(:.&40.)P,(2=.$1.VR,VHIA,Vh,Vmo,)P,(2>.$1.Vm,Vlo,(18.&40.Vsp,))P,(2?.$1.Vm,)P,(30.$1.(2<.VR,)(31.$1.VR,VHIA,Vh,)Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))(32.$1.$13.(33.(14.(15.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(16.&40.VX,)R?.R>.R=.R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(16.&40.$34.)Vfc,(19.(:.&40.))Vm,(1:.$1.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK ST MI OXA. unfold A_ECP_MOD_P521.
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo 48 RFRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof OXA as [OX _]. cbn [md_addr] in OX.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    do 7 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    unfold RFRAME in *.
    change (rw_cells asegs m1 (bv_unsigned sp + -48) RFRAME) in FR. replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in FR by (clear; lia).
    pose proof ST as ST1. replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in ST1 by (clear; lia).
    fold RFRAME in FR.
    pose proof (xa_start _ _ _ _ _ _ _ _ _ _ _ _ JC m1 HH MI ST1 FR OX MU WM) as J0.
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep. zstep. clear GOT GSB AB.
    do 2 zstep.
    zstep.
    pose proof (xa_X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MX1.
    destruct XW as [CW DXP].
    clear MU WM.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof GROW as CP. unfold mpi_grow_stmtA_sz in CP.
      eapply CP with (h := h) (LB := LB) (LF := LF) (dX := dX) (v := 34) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by qlia; try eassumption; try reflexivity.
      all: try (split; [eapply client_wrange_sp_mono; [| exact CW]; clear; lia| exact DXP]).
      all: try (split; [exact OX| intros EST; exfalso; exact (NST EST)]).
      all: try (eapply uw_obj_uwc; [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear; lia]).
      all: try (intros ON; destruct (XLS ON) as [XL|XL]; [left; exact XL| right; clear - XL; lia]).
      all: unfold grow_PHI, grow_FR, red_FRn, calls_FR, fr_charge, C24_GROW, C24_ECP_RED in *; unfold AVOL_CALL in *;
           try (clear - LOS SLO SLO2 NEEDR NER NRM NRF NRA SPA SPR BUD BUDF C24H D0 LOSP TOP; lia).
      all: match goal with |- ?g => idtac "GROW-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & GR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    presA_transport HP2.
    pose proof ST2 as ST2'. replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in ST2' by (clear; lia).
    pose proof (grow_R_keep _ _ _ _ _ _ GR OUT2) as BK.
    pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -48) (grow_PHI 34) (grow_FR d) J0 ltac:(clear - SLO2 NER NEEDR; lia)
                  ltac:(unfold grow_PHI; unfold AVOL_CALL; clear; lia) ltac:(unfold grow_FR, calls_FR, fr_charge; clear - D0; lia)
                  MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      ddestruct GR as [[(R0 & _)|(RF & EQ)] FRg]; [exfalso; apply KR; rewrite R0; reflexivity|]. subst r dX2.
      eapply r_ret; [exact J1| apply reducer_R_fail| unfold grow_PHI; unfold AVOL_CALL; clear; lia| unfold grow_FR, red_FRn, calls_FR, fr_charge; clear - D0; lia].
    - ddestruct GR as [[(R0 & GSG & GN & GPD & GLM & GID)|(RF & EQ)] FRg]; [| exfalso; subst r; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
      subst r.
      ddestruct (grow_ok_facts asegs m2 LB2 LB dX dX2 34 MX2 OUT2 ltac:(split; [left; repeat split; assumption| exact FRg]) ltac:(clear; lia)) as (GO & GNN & _).
      eapply r_body; [exact J1| exact GO| rewrite GNN; clear; lia| | unfold grow_PHI; unfold AVOL_CALL; clear; lia| unfold grow_FR, red_FRn, calls_FR, fr_charge; clear - D0; lia].
      intros ws r Hr Hne.
      exact (reducer_R_ok 34 dX dX2 LB LB2 ws r asegs m2 MX2 OUT2 ltac:(split; [left; repeat split; assumption| exact FRg]) ltac:(clear; lia) (conj Hr Hne)).
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RED.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L24612291273.0L27157546675.600000100BSS1R2sp2lo3SLO3NER". (* [comment removed for export] *)
Lemma A_ecp_mod_p521_spec : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p521 ()) "PR,$35.PHIA,(36.$1.R1.)P,(37.(2<.R2.))P,(38.$1.R3.R2.$39.)P,(1;.$6.(3:.R4.)$3;.)P,(10.=(3<.R5.))P,Ph,(7.$1.R6.R5.)PLB,(8.$9.)PLF,(8.$9.)Pm,P,(:.&40.)(;.(:.&8.))P,(3=.$1.R:.R9.R4.R3.R2.R1.)(3>.$6.(3?.(40.$6.$6.)$6.(41.$6.$6.)R4.))P,(20.(10.(42.(43.R7.))(44.(43.R7.)))(10.(45.(43.R7.))(46.(43.R7.))))P,Pa,$6.P,(1;.$47.(48.$1.(49.R1.))$4:.)P,(20.(10.=R2.)(21.R2.(23.+2.+40.)))(20.(10.(42.(43.R;.))R3.)(21.R3.(46.(43.R;.))))(4;.$1.R9.R8.$34.+22.+:0.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG GROW AMS NEEDR HND DIMG ROIMG. unfold ecp_reducer_stmtA.
  intros until d. intros HH HK LFB MX NST XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA BUD UW UWX BUDF C24H ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  pose proof (arl_need_ecp_rt R) as NER.
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 48 (RFRAME ra s0 s1 s2 s3 s4)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR NER; lia. }
  eapply r_main; first [ exact JC | eassumption | eapply uwc_nonneg; exact UW | clear - SLO NEEDR NER; lia | idtac ].
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
