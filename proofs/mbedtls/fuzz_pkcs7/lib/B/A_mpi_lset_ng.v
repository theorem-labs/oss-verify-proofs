(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_lset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_lset.
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
Ltac2 gd_tbl_A_mpi_lset_ng () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_lset.lset_R"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_LSET"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_lset.A_ASAN_MEMSET_LS"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "mpi_lset_ng_stmtA"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"].



(* [comment removed for export] *)
Definition mpi_lset_ng_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_lset_ng ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.Pv,$8.Plo,$8.P,(9.O4.O3.O2.R29.R28.R27.R5.)P,(:.O4.O3.O2.R2:.R5.)P,(;.O4.R7.R2:.R5.)P,(<.(=.$>.(?.R6.)$10.))P,(11.+1.(12.R7.))P,(13.(11.(14.(15.+2.+1?.))R7.)(16.R7.(15.+2.+1?.)))P,(17.O3.R2>.R2=.(18.&40.R2;.)(19.O4.O3.O2.R2?.)R9.)P,P,(<.(=.$>.(?.R:.)$1:.))(1;.(11.(1<.(1=.R;.)(1>.+4.(12.R;.)))R9.)(11.(18.&40.R2=.)(1=.R;.)))P,(1?.O4.R=.R9.(18.&40.R2=.))P,(11.(20.O3.)R:.)P,(11.R;.(21.(21.(18.&40.R2?.)+60.)(22.O3.)))P,(11.(18.&40.R30.)(19.O4.O3.O2.R34.))P,(=.$8.(23.(18.&40.R31.)+10.)=)P,(=.(3.&40.)R30.(24.&40.(25.O3.)))P,(26.O4.R13.)P,(=.$8.(23.(18.&40.R35.)+2.)=)P,(27.O4.(28.O3.)(29.O4.O3.O2.R39.)R15.R13.)P,(=.(3.&40.)R2>.(24.&40.(2:.R14.)))P,(=.(3.&40.)R2>.(24.&40.R14.))(2;.O4.(2<.O4.O3.O2.R39.R38.R37.R36.R32.R31.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1:.R19.R3<.R3;.R3:.R16.Lr,$8.LdX',$7.(2=.R17.R18.R3=.R2.R1.)==R14.R18.R17.)(2>.(2?.(30.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(24.&40.O1.)R19.(31.(3.&40.))R18.(32.O4.))R17.))")
(* [comment removed for export] *).

Definition mpi_lset_ng_stmtA_v (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_lset_ng ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.Pv,$8.Plo,$8.P,(9.O4.O3.O2.R29.R28.R27.R5.)P,(:.O4.O3.O2.R2:.R5.)P,(;.O4.R7.R2:.R5.)P,(<.(=.$>.(?.R6.)$10.))P,(11.+1.(12.R7.))P,(13.(11.(14.(15.+2.+1?.))R7.)(16.R7.(15.+2.+1?.)))P,(17.O3.R2>.R2=.(18.&40.R2;.)(19.O4.O3.O2.R2?.)R9.)P,P,(<.(=.$>.(?.R:.)$1:.))(1;.(11.(1<.(1=.R;.)(1>.+4.(12.R;.)))R9.)(11.(18.&40.R2=.)(1=.R;.)))P,(1?.O4.R=.R9.(18.&40.R2=.))P,(11.(20.O3.)R:.)P,(11.R;.(21.(21.(18.&40.R2?.)+60.)(22.O3.)))P,(11.(18.&40.R30.)(19.O4.O3.O2.R34.))P,(=.$8.(23.(18.&40.R31.)+10.)=)P,(=.(3.&40.)R30.(24.&40.(25.O3.)))P,(26.O4.R13.)P,(=.$8.(23.(18.&40.R35.)+2.)=)P,(27.O4.(28.O3.)(29.O4.O3.O2.R39.)R15.R13.)P,(=.(3.&40.)R2>.(24.&40.(2:.R14.)))P,(=.(3.&40.)R2>.(24.&40.R14.))(2;.O4.(2<.O4.O3.O2.R39.R38.R37.R36.R32.R31.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1:.R19.R3<.R3;.R3:.R16.Lr,$8.LdX',$7.(13.(2=.R17.R18.R3=.R2.R1.)P,(=.$8.R2.=)(=.$8.(46.R2.)R18.))==R14.R18.R17.)(2>.(2?.(30.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(24.&40.O1.)R19.(31.(3.&40.))R18.(32.O4.))R17.))").

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x09c39c]).
Local Ltac zchk_new ::= constr:([0x09c22c; 0x09c234; 0x09c238; 0x09c240; 0x09c244; 0x09c248; 0x09c24c; 0x09c294; 0x09c298; 0x09c29c; 0x09c318; 0x09c31c; 0x09c320]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_LS.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X sg n P : Z) (limbs : list word) (pad : word) (own : limb_own) (z lo d : Z).
  Local Notation dX := (mkMPD X sg n P limbs pad own).
  Hypothesis HNS : own <> LStatic.
  Hypothesis ZB : -2^31 <= z < 2^31.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis DSP : own <> LNull -> P + 4 * n <= lo \/ bv_unsigned sp <= P.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 96 - arl_need_rt R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts hh :=
    pose proof (hcs_ok asegs R HIA hh) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA hh) as SCS0;
    pose proof (arl_need_rt_free R) as NRF; pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    match goal with HH : HM _ _ _ hh ?LBx LF ?mx, TOPx : bv_unsigned sp <= htop _ _ _ hh |- _ =>
      pose proof (hm_top asegs R HIA hh LBx LF mx HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange (hcs asegs R HIA hh) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPx HTOP; lia])
    end.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation SHX10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Notation FRAME := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation ZSG := (if z <? 0 then -1 else 1).
  Notation POST := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
                      (fun r dX' => lset_R z dX LB r dX' /\ (r = 0 -> mpd_val dX' = z)) 0 0 lo).

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
  Hypothesis N1H : 1 <= n.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L36257435357.2L57111244952.2L61449593947.200000700>00ES2n'2NRS2n'2NRS2n'2NR". (* [comment removed for export] *)
  #[using="ZB"] Lemma post_set : forall (LBr : list blk) (mo mo' : Model) (h' : HST asegs R HIA) m' (p' n' : Z) (w0 : word)
      x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> mo_frame mo mo' ->
    presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m' ->
    htop asegs R HIA h' = htop asegs R HIA h -> hstkhi asegs R HIA h' = hstkhi asegs R HIA h ->
    hflag asegs R HIA h' = hflag asegs R HIA h -> HK asegs R HIA h' mo' ->
    (forall x, hcs asegs R HIA h x -> hcs asegs R HIA h' x) ->
    havol asegs R HIA h' <= havol asegs R HIA h + 0 -> hfr asegs R HIA h' <= hfr asegs R HIA h + 0 ->
    HM asegs R HIA h' LBr LF m' -> rw_cells asegs m' X (mpi_cells p' (Z_to_bv 64 ZSG) n' pad) ->
    u32arr asegs m' p' (w0 :: repeat (Z_to_bv 64 0) (Z.to_nat (n' - 1))) -> w0 = Z_to_bv 64 (bv_swrap 32 (Z.abs z)) ->
    In (p', 4 * n') LBr -> p' mod 16 = 0 ->
    1 <= n' <= MPI_MAX_LIMBS -> n' = Z.max n 1 -> X mod 8 = 0 -> 0 < X ->
    (forall b, In b LBr -> In b LB \/ b = (p', 4 * n')) -> (forall b, In b LB -> ~ In b (mpd_blk dX) -> In b LBr) ->
    (forall b, In b (mpd_blk dX) -> In b LBr -> [(p', 4 * n')] = mpd_blk dX) ->
    (In (p', 4 * n') (mpd_blk dX) \/ (fresh_apart R (mpd_keep LB dX) LF p' (4 * n') /\ ~ In (p', 4 * n') LB)) ->
    POST m mo (mkCfg (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                          F (ret_pc ra) fc None m' (seg_rom asegs)) mo').
  Proof.
    intros until x31. intros MI ST MF HP HT HS HFL HK HCS HV HFR HH HX HPL HW0 HIN PAL NR En ALX X0 HI1 HI2 HI3 HF.
    unfold mpi_binop_postA. deexists 14.
    dexists m', mo', h', LBr, (mkMPD X ZSG n' p' (w0 :: repeat (Z_to_bv 64 0) (Z.to_nat (n' - 1))) pad LHeap), 0.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|].
    split. { split; [| cbn [md_sg]; destruct (z <? 0); [right| left]; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact HX|]. split; [exact ALX|]. split; [exact X0|]. split; [cbn [length]; rewrite repeat_length; clear - NR; lia|]. split; [clear - NR; lia|].
      split; [clear - NR; lia|]. split; [exact HIN|]. split; [exact PAL| exact HPL]. }
    split. { unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
      split; [intros b Hb; destruct (HI1 b Hb) as [Hb'| ->]; [left; exact Hb'| right; left; reflexivity]|].
      split; [exact HI2| exact HI3]. }
    split; [cbn [mpd_blk md_own md_p md_n]; intros b [<-|[]]; destruct HF as [HF'|[HF' _]]; [left; exact HF'| right; exact HF']|].
    cbv beta. split; [| intros _; unfold mpd_val; cbn [md_sg md_limbs]; rewrite HW0; apply lset_val_abs; exact ZB].
    unfold lset_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk].
    split; [left; split; [reflexivity|]; split; [exact En|]; split; [reflexivity|]; split; [eexists; reflexivity| split; reflexivity]|].
    split; [reflexivity|]. intros b [<-|[]]. destruct HF as [HF'|[_ HF']]; [left; exact HF'| right; exact HF'].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01j0@D3399625391.111 D3399625391.112 D35881667587.111D35881667587.112K42587433812.111K42587433812.112L1160155683.139 L15302269400.107L1685717371.0   L1954497222.2   L19947928356.139L22446743512.107L25214214772.107L26892418956.1  L29428324939.5  L29767916836.3  L31225147636.107L3226164952.10  L3226164952.9   L3227728773.8   L33087634096.2  L34705680216.107L35653441506.7  L37246946676.106L38948636245.0  L39280637297.0  L3949578456.106 L40281191306.3  L40374333670.107L40834179097.109L41843875160.107L42594106808.2  L43061363337.105L46122776823.12 L46160487540.108L46160572444.105L48132467214.7  L49283344500.107L51041001329.10 L51041001329.9  L51043613228.8  L51454941784.107L51613292135.1  L5255722929.107 L55310518004.107L56010806032.10 L56013452877.11 L56013452877.12 L5699067096.107 L57344136272.139L57818804596.107L58591023192.107L59308546259.3  L59308628304.3  L60098763854.3  L61321319284.107L61929718192.2  L61929812241.108L62018535662.1  L62624897321.37 L63829069812.107L64194470200.2  L64630569949.3  L65358966972.3  L65361583713.1  L66356286070.3  L66358289365.4  L66358289365.5  L67280348888.107L67351568884.107L774765788.5    Q15643324129.107Q17530203490.110Q17530203490.111Q18365925601.108Q18694146040.110Q21798041355.110Q21879645826.108Q25157988860.110Q25513505925.110Q25513505925.111Q25662358575.110Q26207688439.107Q26207721832.110Q26220436438.109Q27584944865.108Q27907200258.108Q30415036802.108Q31228709292.110Q31271525473.108Q31394594844.110Q31649392511.109Q32655500769.108Q33918256002.108Q35014437530.110Q35717497884.110Q36425882626.108Q3830427394.108 Q39212284437.110Q39939554818.108Q41152393185.108Q4143427880.110 Q43925228937.110Q44648843873.108Q49698585326.109Q49698585326.110Q51235796833.108Q5300226131.108 Q5300226131.109 Q53969758199.110Q59843137889.108Q60511567613.110Q60697995187.110Q61802139820.110Q6416456232.110 Q64255486968.110Q66522067074.108Q67528989526.111Q67528989526.112Q8880780715.107 Q9538509144.107 Q9843367298.107 00000k02;02h03j04c06106E06T06U06[07207A07P07T07f07o08>08?08@08A08G08V08n09=09>09?09N09W09f0:70:F0:G0:l0;M0;_0<10<L0<[0<\0<]0<^0<m0<n0=@0=O0=P0=Q0=R0=a0>70>F0>U0>^0>h0?20?A0?G0?_0?b0?c0@20@90@B0@H0@I0@J0@K0@L0@[0@j0A=0AO0B?0CD0CV0Ci0Cj0DH0D[0E?0F80F90FE0FQ0F]0Fo0GM0Gk0H?0HQ0H]0Hi0I;0IY0Im0In0JL0Jj0K60KT0Kf0Kg0L30LE0La0M=0MO0Ma0N30NG0NY0Ne0O40O50OH0OI0Og0PW0Q\0Qh0R40RRS1R5NEEDR2ra2sp1X5limbs2lo3LOS3SLO2X03SPR2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3LOS3SLO2X03SPR2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1R3HIA1h2ra2sp1X5limbs3TOP2XB2HB5Ha_st5Hl_stS1R3HIA1h2sp2s01X5limbs3TOP2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1R5NEEDR2ra2sp1X1P5limbs2lo3SLO2XB2P03DSX2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X1P5limbs2lo3SLO2XB2P03DSX2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp1X1P5limbs2XB2P0S2sp1X5limbs2XBSS1P2B0S2sp1X1P5limbs2lo2XB2P0S2sp1X5limbs2XBS2sp1X5limbs2XBS2spS1R2lo3LOS3ALO3ACPS1n2NR2N1S2sp1X5limbs2XBFFFS1n2NRS2sp1X5limbs2XBS1R3HIA1h2sp2lo3TOP4HTOPS2sp1X5limbs2XBSSS2sp1X5limbs2XBS1R3HIA1hS2sp1X5limbs2XBS1R2sp1X5limbs2XBS2sp1X5limbs2XBFS1R5NEEDR2sp1X5limbs2lo3SLO2X03SPR2XBS1R2sp1n1P5limbs2lo3LOS2LL3ALO2PCS2sp1X5limbs2X02XBS2sp1X5limbs2X02XBS1R5NEEDR2sp2lo3LOS3SLO3ALOS2sp1X5limbs2XBFFFS2sp1X5limbs2XBFS2sp1X5limbs2X02XBS2sp1X5limbs2XBFFFS2sp1X5limbs2XBS2sp1X1n1P5limbs2XB2P0S2sp1X5limbs2XBS2sp1X5limbs2XBS1n2K12N0S1n3N1H2K1S1R2lo3LOSS2sp1X5limbs2XBS1n2NRS2sp1X1n5limbs3N1H2NR2XBS1RFS2sp1X5limbs2XBS1R3ACPS1R3HIA1hS1n2N1FFFFS2sp1X5limbs2XBS2sp1X5limbs2XBS1R5NEEDR2sp2lo3SLOS2sp1X5limbs2lo2XBS1R5NEEDR2ra2sp1X5limbs2lo3SLO2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3SLO2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp1X5limbs2lo2XBS1R1X5limbs4IMG'2XBFS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R1X5limbs4IMG'2XBS2ra2sp1X5limbs2lo2XB2HB5Ha_st5Hl_stS2sp2s01X5limbs2lo2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7FS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R1X5limbs5ALWF'2XBS2sp1X5limbs2lo2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R1X5limbs5ALWF'2XBFS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS2sp1X5limbs2lo2XBFS1X5limbs2XBS2sp1X5limbs2lo2XBS2sp1X5limbs3SPR2XB2HB5Ha_stS2sp1X5limbs3SPR2XB2HB5Ha_stS2sp1X5limbs2lo2XBS2sp1X5limbs2XB2HBS2sp1X5limbs2XB2HBS1R1X5limbs5ALWF'2XBS2sp1X5limbs2lo2XBS1X5limbs2XBS1X5limbs2X02XBFS1R1X5limbs4IMG'2XBFS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2ra2sp1X5limbs2lo3SLO2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3SLO2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XB". (* [comment removed for export] *)
  #[using="IMG AMS NEEDR HND DIMG HNS ZB XW DSP LOS SLO TOP N1H"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_lset_ng ()) "Pmo,$6.Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(9.$33.VR,VHIA,Vh,VLB,VLF,Vm,)P,(:.$33.VR,VHIA,Vh,R?.)P,(;.$33.Vm,VLB,(34.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))P,(1?.$33.Vm,Vlo,(18.&40.Vsp,))P,(26.$33.Vm,)P,(35.$33.(28.VR,)(29.$33.VR,VHIA,Vh,)Vm,VX,+10.)(2;.$33.(2<.$33.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(34.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$8.LdX',$7.(13.(2=.Vz,(34.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)P,(=.$8.R2.=)(=.$8.(46.R2.)Vz,))==Vlo,Vm,R14.)(2>.(2?.(30.Vra,Vsp,Vgp,Vtp,R13.R12.R11.Vs0,Vs1,(24.&40.VX,)(24.&40.Vz,)R10.R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(24.&40.$36.)Vfc,(31.(3.&40.))Vm,(32.$33.))R14.))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HKmo MX ST MI OX. unfold A_MPI_LSET. rt_facts h.
    pose proof (HND _ _ _ _ HH) as ND.
    destruct MX as [(HXS & ALX & X0 & LL & NR & HOWN) SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HXS, ALX, X0, LL, NR, HOWN, SG.
    destruct XW as [CW DXP]. cbn [md_addr md_own md_p md_n] in CW, DXP.
    pose proof (client_wrange_keep L LB LF _ _ dX X 16 CW DXP) as CWk.
    pose proof (rw_cells_bound _ _ _ _ HXS) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HF BA]. rewrite Forall_forall in HF.
    unfold MPI_MAX_LIMBS in NR.
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
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB AB.
    (* [comment removed for export] *)
    zstep. shadow_chk OX (X + 10) 2.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HP1 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m1).
    { apply presA_nil_any. eapply (presA_tail0 asegs R HIA h LB); [exact HH| intros b Hb; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP| exact MU0| exact WM0]. }
    assert (PCH1 : own = LHeap -> u32arr asegs m1 P limbs).
    { intros E. ddestruct (PHEAP E) as (_ & _ & _ & HXL & _).
      eapply (u32arr_transport asegs _ m m1); [exact HXL| exact MU0| exact WM0| cbn [disjoint_from]; clear - PC ALO LOS SLO NEEDR LL; lia]. }
    clear MU0 WM0.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K1 by (clear - NR; lia).
      assert (EO : own = LHeap).
      { destruct own; [| reflexivity| exfalso; exact (HNS eq_refl)]. exfalso. destruct (PNULL eq_refl) as [_ N0]. clear - N0 K1. lia. }
      ddestruct (PHEAP EO) as (B0 & HIN & HP16 & _ & N1). pose proof (PCH1 EO) as HXL1. clear PHEAP PCH1 PNULL.
      specialize (DXP EO).
      eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
        [ eapply (A_mpi_lset.tail_walk R HIA IMG AMS) with (hc := h) (LBc := LB); try eassumption; try reflexivity | intros y Hy; exact Hy | ].
      all: try (unfold mpi_cells; exact HXS).
      all: try (exact FR).
      all: try (unfold MPI_MAX_LIMBS; clear - NR N1; lia).
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "TAIL0-PRE-LEFT:" g end.
      intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & HPL9 & W09 & ST9 & HH9). subst ms'.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      apply aevtA_done. intros mo9 [HK9 MF9].
      assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
      { eapply presA_trans; [exact HP1|].
        eapply (presA_drop_freed asegs R HIA h LB LF (mpd_keep LB dX) [(X, X + 16)] P (4 * n) m1 m1 m9);
          [exact HH| exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia|].
        - intros b xb Hb Hr. unfold mpd_keep in Hb. cbn [md_own md_p md_n] in Hb. rewrite EO in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
          split; [exact Hb|]. intros E. rewrite E in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
        - eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                    (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16); (P, P + 4 * n)]);
            [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| cbn [outside]; clear; intros y Hy; tauto].
          eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) _ m1 m9); [exact HH| | clear; lia| exact LOS].
          eapply (presA_of_munch asegs R LB LF _ _ _ _ m1 m9 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | exact MU | exact WM].
          unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
          apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX|].
          apply Forall_cons; [cbn [fst snd]; replace (P + 4 * n - P) with (4 * n) by lia; eapply hcs_block; [exact HH| exact HIN]|]. apply Forall_nil. }
      eapply (post_set LB mo mo9 h); try eassumption; try reflexivity.
      all: try (intros y Hy; exact Hy).
      all: try (clear; lia).
      all: try (unfold MPI_MAX_LIMBS; clear - NR N1; lia).
      all: try (clear - N1; lia).
      all: try (intros b Hb; left; exact Hb).
      all: try (intros b Hb _; exact Hb).
      all: try (cbn [mpd_blk md_own md_p md_n]; rewrite EO; intros b Hb _; destruct Hb as [<-|[]]; reflexivity).
      all: try (left; cbn [mpd_blk md_own md_p md_n]; rewrite EO; left; reflexivity).
      all: match goal with |- ?g => idtac "SET0-LEFT:" g end.
    - (* [comment removed for export] *)
      exfalso. rewrite ?unsigned_lit in K1 by (clear - NR; lia). clear - K1 N1H. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Lemma A_mpi_lset_ng_spec_v : forall (R : art_layout) (HIA : artA asegs R),
  asan_img_ok (arl_AL R) -> arl_amemset R = A_ASAN_MEMSET_LS -> 0 <= arl_need_rt R ->
  (forall (h : HST asegs R HIA) (LB LF : list blk) (m : bv 64 -> option (bv 8)), HM asegs R HIA h LB LF m -> List.NoDup (map fst LB)) ->
  hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R) ->
  mpi_lset_ng_stmtA_v asegs R HIA A_MPI_LSET.
Proof.
  intros R HIA IMG AMS NEEDR HND DIMG. unfold mpi_lset_ng_stmtA_v.
  intros until lo. intros HH HK MX HNS N1 ZBv XW DSP ST LOS SLO TOP SPA TPV MI RA2 OXA -> ->.
  destruct dX as [X sg n P limbs pad own].
  eapply main_walk; try eassumption. exact (proj1 OXA).
Qed.

Lemma A_mpi_lset_ng_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_lset_ng ()) "PR,$37.PHIA,(38.$33.R1.)P,(39.(28.R2.))P,(=.$8.(3:.R3.)$3;.)P,(11.=(22.R4.))P,Ph,(0.$33.R5.R4.)PLB,(1.$2.)PLF,(1.$2.)Pm,P,(3.&40.)(5.(3.&8.))P,(9.$33.R9.R8.R4.R3.R2.R1.)(3<.$8.(3=.(3>.$8.$8.)$8.(3?.$8.$8.)R4.))P,(13.(11.(40.(41.R6.))(42.(41.R6.)))(11.(43.(41.R6.))(44.(41.R6.))))(45.$33.R7.R6.$36.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG AMS NEEDR HND DIMG. pose proof (A_mpi_lset_ng_spec_v R HIA IMG AMS NEEDR HND DIMG) as V.
  unfold mpi_lset_ng_stmtA_v, mpi_lset_ng_stmtA in *.
  intros until lo. intros. eapply aevtS_mono; [eapply V; eassumption|].
  intros c PO. unfold mpi_binop_postA in *.
  ddestruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & mo' & h' & LB' & dX' & r & PO).
  dexists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m', mo', h', LB', dX', r.
  ddestruct PO as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16).
  repeat (split; [assumption|]). exact (proj1 P16).
Qed.
