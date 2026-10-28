(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux X509Aux MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pk_free P_pk_info.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_pk_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_pk_info () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.P.P_pk_info.pk_info_of"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "pk_info_from_type_postA"; "Stdlib.ZArith.BinInt.Z.pow"].


Definition A_PK_INFO_FROM_TYPE : Z := 0x0b17fc.
Definition A_PK_INFO_TBL : Z := 0x0f2140.
Definition A_PK_INFOS : list Z := [A_RSA_INFO; A_ECKEY_INFO; A_ECKEYDH_INFO; A_ECDSA_INFO].
Notation PK_INFO_STACK_A := 16 (only parsing).

Definition pk_info_from_type_postA (segs : list Segment) (INFOS : list Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (t lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_info ()) "Lms',$0.(1.(2.&40.)La0',(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R5.(6.(7.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.O19.R4.R3.R2.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.)O5.(8.O21.)O4.(9.(2.&40.))R1.(:.O23.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.O20.)+10.)(11.&40.O20.))(12.(=.$>.$>.)))O1.R1.)(4.(13.O23.O1.R1.)(4.(14.O23.R1.)(4.(15.O23.R1.O2.(11.&40.O20.))(5.(2.&40.)R4.(16.&40.(17.O22.O3.))))))))))))")
(* [comment removed for export] *).

Definition pk_info_from_type_stmtA (segs : list Segment) (AL : asan_layout) (L : heap_layout) (TBL : Z) (INFOS : list Z) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_info ()) "PCS,P,$>.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(18.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Plo,$>.P,(14.O6.R2.)P,(19.R3.)P,(5.$>.(1:.(11.&40.R25.)+2.)=)P,(15.O6.R5.R4.(11.&40.R25.))P,(1;.R5.(10.(11.&40.R26.)+10.))P,(1;.(1<.O4.)R6.)P,(5.$>.(1:.(11.&40.R28.)+10.)=)P,(1=.O5.)P,(1>.O5.R2<.)P,(1?.O6.O5.R;.)P,(20.O6.O5.R2>.R<.O3.+20.)P,(21.R2?.R<.(10.(11.&40.R2=.)R<.))(22.O6.O5.R30.(23.O6.O2.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.(1:.(11.&40.R26.)(24.+2.+20.))R=.R>.)(6.(7.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(16.&40.O1.)R?.(9.(2.&40.))R>.(:.O6.)))")
(* [comment removed for export] *).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Variable L : heap_layout.

  Local Ltac2 Set LiaOrc.tbl := fun () => "01@0?L12950997904.1 L14935379672.4 L14942038703.67L16516839824.1 L1685717371.0  L18926546934.12L18926689488.11L18928398988.71L18928483345.70L20406138101.5 L20433961190.65L25089186826.11L31399144472.68L31399144472.71L31804118914.12L32049487064.66L32049487064.70L32049487064.73L35503470861.13L3832229667.72 L3834306085.69 L39188636933.0 L41617822073.12L41617973855.11L41872764395.73L43061380748.63L43098387356.72L46748113268.66L49048232372.12L55371958114.4 L59094670377.11L59308661072.12L59308696420.11L60999597968.1 L9066874074.70 L9385680272.1  P12939200788.69P16520772372.69P60986752276.69P9389088532.69 Q11801279589.69Q1219017780.73 Q15641521856.72Q15643324129.65Q15647858630.69Q16420663452.72Q16461065663.73Q17910201056.71Q21492310800.69Q21545477007.69Q21639271868.69Q21798041355.73Q23150033886.73Q23192065976.73Q23674762511.69Q23772899132.69Q25513505925.68Q2587180432.69 Q31394594844.73Q34513865977.72Q41126203749.73Q44034257392.73Q45177286159.69Q45258625084.69Q45914037331.66Q49632246059.72Q49634315695.71Q49698585326.67Q53519952433.73Q55406890128.69Q56873555452.73Q58146298210.68Q62929613328.69Q63037100374.73Q65676169383.73Q66715549212.73Q77032079.69   Q9838832805.69 Q9840975267.72 Q9843367298.65 00000100?00@00A00B00K00Q00]00i01701>01W01c01o02C02J02V02b03503H03[03\03l04804G04U04f04m05805F05\06006H06I06a06b07I08008W09>09T09c09o0:60:B0:`0:a0:o0;50;;0;<0;=0;L0;R0;X0;Y0<20<80<>0<L0<M0<[0<a0<b0<i0=70=E0=V0=e0=k0>90>V0>\0>j0>k0?90??0?O0?_0?jFS2a01z2sw4SW03FFSS2a01z2swS2a01zS2ra2sp2a01zS2ra2sp2a01zS2a01z2sw1K2SRS2ra2spS2a01z2AR2sw1K2SM4SW032GES2ra2sp2a01zS2ra2sp2a01zS2a01z2AR2sw4SW032E2S2ra2spS2ra2sp2a01zS2ra2sp2a01zS2a01z2AR2sw4SW031HS2ra2sp2a02lo3SPL1zS2ra2sp2a02lo3SPL1zSS2a01z2sw3TR12LTS2a01z2TR2H1S2AL2ra2sp2a01zS2ra2sp2lo3SPLS2ra2sp1z2sw4SW03S2ra2spS2a01z2AR1HS2a01z2sw4SW03S2a01z2AR2sw1K2SM4SW03S2a01z2AR1K2SM2H22E1S2a01z2AR2SR2SM2H12H22GEFS2ra2sp1z2AR3SPR2sw4SW03FS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS2ra2sp2HB5Ha_st5Hl_stS2AL2a05ALWF'1zS2sp2a02lo1zS2sp2loS2sp2a02lo1zS2ra2sp2a01z2AR3SPR2sw4SW032ETFS2a01z2sw4SW03S2a01zS2a01zFFS2AL2a05ALWF'1zS2a01zS2a01zFS2ra2sp2lo2HB5Ha_st5Hl_stS2a01zS2a01zS2a01z2sw4SW03FS2AL2a04IMG'1zS2a01zFS2sp2HBS2a01z2sw4SW03S2a01z2sw4SW03S2sp3SPR2HB5Ha_stS2AL2a05ALWF'1zS2a01zS2AL2a04IMG'1zS2ra2sp2lo3SPL2HB5Ha_st5Hl_stS2a01zS2AL2a04IMG'1zFS2AL2a04IMG'1zS2a01zS2sp2a02lo3SPL1zS2sp2a02lo3SPL1zS2sp2lo3SPL". (* [comment removed for export] *)
  #[using="IMG"] Lemma A_pk_info_from_type_spec : pk_info_from_type_stmtA asegs AL L A_PK_INFO_TBL A_PK_INFOS A_PK_INFO_FROM_TYPE.
  Proof.
    unfold pk_info_from_type_stmtA, A_PK_INFO_FROM_TYPE. intros until lo. intros MI SOK RA ST SPL ACL SPA ALWF CSOK AB OTBL SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 64 a0) as AR. change (bv_modulus 64) with (2^64) in AR.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (proj1 ST) as LO0. pose proof (@alloc_ceiling_bounds _) as ACV.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    let tbl_entry k TB :=
        let a := eval vm_compute in (A_PK_INFO_TBL + 8 * k) in
        let bs := eval vm_compute in (match image_bytes asegs a 8 with Some bs => bs | None => [] end) in
        pose proof (asan_rtc_const m a bs SOK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as TB;
        cbn [length] in TB in
    tbl_entry 0 TE0; tbl_entry 1 TE1; tbl_entry 2 TE2; tbl_entry 3 TE3.
    clear SOK. unfold A_PK_INFO_TBL in *.
    Ltac epilogue :=
      zstep; zstep; zstep;
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with FRx : rw_cells _ mm _ [CB 8 _; C8 _], STx : stk _ mm _ _ |- _ =>
          lazymatch type of STx with stk _ _ _ (bv_unsigned ?spv + -16) => release_frame FRx STx (bv_unsigned spv) end end end;
      apply evtA_done; unfold pk_info_from_type_postA; eexists; eexists; eexists; eexists; split; [reflexivity|];
      repeat match goal with |- _ /\ _ => split end; try eassumption.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K; set (z := bv_unsigned a0) in *;
      pose proof (bv_swrap_in_range 32 (z + -1) ltac:(discriminate)) as SR; unfold bv_half_modulus in SR;
      replace (bv_modulus 32 `div` 2) with (2^31) in SR by reflexivity;
      pose proof (swrap32_mod64 (z + -1)) as SM; unfold sxz in SM; change (2^64) with 18446744073709551616 in SM; change (2^32) with 4294967296 in SM;
      pose proof (Z.mod_pos_bound z 4294967296 ltac:(lia)) as TR; pose proof (Z.mod_pos_bound (z + -1) 4294967296 ltac:(lia)) as TR1;
      change (2^32) with 4294967296.
    - (* [comment removed for export] *)
      zstep. epilogue.
      unfold pk_info_of.
      destruct (Z.leb_spec 1 (z mod 4294967296)) as [H1|H1]; [destruct (Z.leb_spec (z mod 4294967296) 4) as [H2|H2]|]; cbn [andb]; try reflexivity.
      exfalso. clear -K H1 H2 AR SR SM TR TR1.
      destruct (Z.ltb_spec ((z + -1) mod 4294967296) (2^31)) as [LT|GE]; [| lia].
      assert (E1 : (z + -1) mod 4294967296 = z mod 4294967296 - 1).
      { replace (z + -1) with (z mod 4294967296 - 1 + (z / 4294967296) * 4294967296) by (pose proof (Z.div_mod z 4294967296 ltac:(lia)); lia). rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
      lia.
    - (* [comment removed for export] *)
      set (sw := bv_swrap 32 (z + -1)) in *.
      assert (SW03 : 0 <= sw <= 3) by (clear -K SR; lia).
      assert (ET : z mod 4294967296 = sw + 1).
      { clear -K SR SM TR TR1 SW03 AR. destruct (Z.ltb_spec ((z + -1) mod 4294967296) (2^31)) as [LT|GE]; [| lia].
        assert (E2 : (z + -1) mod 4294967296 = sw) by lia.
        replace z with ((z + -1) mod 4294967296 + 1 + ((z + -1) / 4294967296) * 4294967296) by (pose proof (Z.div_mod (z + -1) 4294967296 ltac:(lia)); lia).
        rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia. }
      assert (SWM : sw mod 18446744073709551616 = sw) by (apply Z.mod_small; clear -SW03; lia).
      rewrite SWM in *.
      assert (SW4 : sw = 0 \/ sw = 1 \/ sw = 2 \/ sw = 3) by (clear -SW03; lia).
      clearbody sw. clear K SR SM TR TR1 SWM.
      pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
      (* [comment removed for export] *)
      zstep. zstep. zstep. rewrite (Z.shiftl_mul_pow2 sw 3) by (clear; lia). change (2^3) with 8.
      zstep. clear GOT GSB. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      destruct SW4 as [->|[->|[->| ->]]]; cbn [Z.mul Z.add Pos.mul Pos.add];
        (zstep; zstep; epilogue; unfold pk_info_of; rewrite ET; reflexivity).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
