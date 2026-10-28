(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pk_free P_pk_type.
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
Ltac2 gd_tbl_A_pk_type () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.le"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "pk_get_type_postA"].


Definition A_PK_GET_TYPE : Z := 0x0b195c.
Notation PK_GET_TYPE_STACK_A := 16 (only parsing).

Definition pk_get_type_postA (segs : list Segment) (RSAI : Z) (ECIS : list Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (info lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3' : word) (ty : Z) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ty) a1 a2 a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom segs) /\
    munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m' /\
    stk segs m' lo (bv_unsigned sp) /\
    (info = 0 -> ty = 0) /\ (info = RSAI -> ty = 1) /\ (In info ECIS -> 2 <= ty /\ ty <= 4) /\ (0 <= ty /\ ty <= 4)
(* [comment removed for export] *).

Definition pk_get_type_stmtA (segs : list Segment) (AL : asan_layout) (L : heap_layout) (RSAI : Z) (ECIS : list Z) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_type ()) "PCS,P,$3.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(19.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(4.(2.&8.))PA,$3.Pinfo,$3.Plo,$3.Pc,(2.&40.)P,(1:.O6.R5.R4.(>.$1;.(1<.(9.&40.R3.))(>.$1;.(1<.R1.)(13.$1;.))))P,(6.$3.(1=.R5.+8.)=)P,(1>.=R6.)P,(1?.(6.$3.R6.=)(1?.(6.$3.R6.O3.)(17.$3.R6.O2.)))P,(15.O6.R9.)P,(20.R:.)P,(6.$3.(1=.(12.&40.R2<.)+2.)=)P,(16.O6.R<.R9.(12.&40.R2<.))P,(18.R:.(11.(12.&40.R2=.)+10.))P,(18.(21.O4.)R;.)P,(6.$3.(1=.(12.&40.R2?.)+10.)=)P,(1?.(18.(22.R?.+10.)R=.)(18.(12.&40.R30.)R?.))P,(23.O5.)P,(24.O5.R34.)P,(25.O6.O5.R13.)P,(26.O6.O5.R36.R14.R13.+10.)P,P,(27.(6.$3.R13.=))(26.O6.O5.R38.R16.R14.+4.)P,(28.R38.R13.(11.(12.&40.R36.)R13.))P,(6.(2.&40.)R2?.(9.&40.R16.))(29.O6.O5.R3:.(2:.O6.O3.O2.R39.R38.R37.R36.R35.R34.R33.R32.R31.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R16.R15.R18.)(7.(8.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(9.&40.O1.)R19.(;.(2.&40.))R18.(<.O6.)))")
(* [comment removed for export] *).

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x0b19bc]).
Local Ltac zchk_new ::= constr:([0x0b1968; 0x0b196c; 0x0b1994; 0x0b1998]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Variable L : heap_layout.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0290?K54978542206.74K54978542206.78L13946228446.76L1451155519.77 L14753738640.1 L15045276710.71L16629399520.72L1685717371.0  L20433961190.70L20433961190.74L20484379080.77L22231146956.77L23258596110.76L24926455156.72L25380471876.2 L25478759144.77L25819467664.1 L26982580167.2 L28814043710.71L28814043710.74L29784543482.76L30998130576.1 L31399144472.71L31399144472.76L32049487064.70L32049487064.72L32049487064.73L32049487064.77L32195670001.72L32195670001.75L34791198520.77L34795348415.77L35943307932.77L36014159563.2 L3829644388.77 L3830242848.72 L40825690058.71L40825690058.76L40856024236.77L41415807082.76L41872764395.74L41872764395.77L43059266230.68L43059658930.72L44764531871.72L46748113268.70L46748113268.73L54559550588.77L54968017161.2 L55629907246.76L57240063888.1 L59308628179.4 L59308631400.3 L61266280920.77L62027870591.77L6755571354.76 L8256535039.77 L8943491390.76 P14758194452.74P14758194452.78P25807146260.74P25807146260.78P30994722068.74P30994722068.78P57227742484.74P57227742484.78Q1171540727.72 Q1171540727.76 Q11801279589.74Q11801279589.78Q1219017780.74 Q1219017780.78 Q15643065735.77Q15643271107.72Q15643324129.70Q15643324129.74Q17104982033.77Q21798041355.74Q21798041355.78Q23024867311.72Q23024867311.76Q23150033886.74Q23150033886.78Q23481115726.77Q25513505925.73Q25513505925.77Q26284880783.77Q26284896393.80Q26295627581.80Q2648600593.77 Q29637398545.77Q3090987133.80 Q31394594844.74Q31394594844.78Q31954582050.73Q31954582050.77Q37708009648.73Q37708009648.77Q37708157104.72Q37708157104.76Q38180398158.77Q40688494363.74Q40688494363.78Q41126203749.74Q41126203749.78Q44034257392.74Q44034257392.78Q44589874661.78Q45033272398.77Q45124942924.73Q45124942924.77Q45535445369.77Q45914037331.71Q45914037331.75Q49018925073.77Q49698585326.72Q49698585326.76Q53519952433.74Q53519952433.78Q54057591853.74Q54057591853.78Q58146298210.73Q58146298210.77Q60973937803.78Q6103773729.80 Q63037100374.74Q63037100374.78Q63494419478.80Q65281364526.77Q66715549212.74Q66715549212.78Q7221187662.77 Q8943621793.77 Q9843367298.70 Q9843367298.74 Q9843420320.72 Q9843625700.77 00000R01401=01F01G01P01[01\01e01n02902D02M02V02b02m02n03903I03Y03b03c03l04504>04G04P04Y04b04k05605?05H05T05d06406=06F06Q06Z06f07207B07R07]07f07o08:08;08D08E08N08]08h09309<09E09N0:50:\0;C0;j0<Q0=80=_0>F0>I0>L0>b0?80?B0?L0?S0?Z0?a0?h0?i0?j0?k0?n0@10@;0@E0@F0@_0A80A>0AD0AE0AF0AG0AM0AN0AO0AR0AU0AX0A[0A^0Aa0Ab0Ac0Ad0Ae0Af0Ao0B80B90B:0BN0Bb0Bh0Bo0C60C70CH0CY0Cc0Cm0Cn0Co0DL0Di0Dj0E50E>0EG0EM0EN0EW0E`0Ea0Eb0Em0F80FC0FNS2ra2sp1A2lo3SPL2DS2HB5Ha_st5Hl_stS2ra2sp1A2lo3SPL2DS2HB5Ha_st5Hl_stS2ra2sp1AS2ra2sp1AFS2ra2sp1AS2ra2sp1A1HSS2ra2sp1AS2ra2sp1AS2ra2sp1A1HS2ra2sp1A1HS2ra2sp1AS2ra2sp1AS4info5CASESS2ra2sp1A1HFS4info4HINFS2ra2sp1A2NZ3PKBS2ra2sp1A2NZ3PKBS2ra2sp1AFS2ra2sp1AS2ra2sp1AS2ra2sp1AS2ra2sp1AS2ra2sp1AS2ra2sp1AS2ra2sp1AS2ra2sp1AS2ra2sp1A1HS2ra2sp1AS2ra2sp1AS4info5CASESS2ra2sp1A2lo3SPLS2ra2sp1A2lo3SPLS2ra2sp1AS2ra2sp1AS2ra2sp1A1HS2ra2sp1AS2AL2ra2sp1AS2AL2ra2sp1AS2ra2sp1A2lo3SPLS2ra2sp1A2lo3SPLS2ra2sp1A1HS2ra2sp1AS2ra2sp1AS2ra2sp1A1HFS2ra2sp1AFS1A2NZ2K0S4info5CASES2KIS2ra2sp1A1HS2ra2sp1A1HS2ra2sp1AS2ra2sp1AS2ra2sp1AS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS1L2ra2sp2lo3SPL3ACL3ACV2HB5Ha_st5Hl_stS1AS1AS2ra2sp2HB5Ha_st5Hl_stS2ra2sp2HB5Ha_st5Hl_stS2AL5ALWF'S2AL5ALWF'S2sp2loS2sp2loS2sp2loS2sp2loSFFS1AS1AS2AL5ALWF'S2AL5ALWF'SS2ra2sp2lo2HB5Ha_st5Hl_stS2ra2sp2lo2HB5Ha_st5Hl_stS4infoS4infoSSSS4infoSSS1AS1AS1AS1AS1AS1ASFFFFS2AL4IMG'S2AL4IMG'FSS2ra2sp1A3AL82NZ3SPRS2ra2sp1A3AL82NZ3SPRS4infoS2sp2HBS2sp2HBSS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS2AL5ALWF'S2AL5ALWF'FFS2ra2sp2lo3SPL2HB5Ha_st5Hl_stS2ra2sp2lo3SPL2HB5Ha_st5Hl_stFS4info4INFBS2AL4IMG'S2AL4IMG'S4infoFS2AL4IMG'S2AL4IMG'SSS2sp2lo3SPLS2sp2lo3SPLS2sp2lo3SPLS2sp2lo3SPL". (* [comment removed for export] *)
  #[using="IMG"] Lemma A_pk_get_type_spec : pk_get_type_stmtA asegs AL L A_RSA_INFO A_EC_INFOS A_PK_GET_TYPE.
  Proof.
    unfold pk_get_type_stmtA, A_PK_GET_TYPE. intros until c. intros HPK AL8 NZ HINF MI SOK RA ST SPL ACL SPA DS ALWF CSOK AB OCTX OINF SCS ->.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (rw_cells_bound _ _ _ _ HPK) as PKB. cbn [cells_size csize Nat.add] in PKB. change (Z.of_nat 16) with 16 in PKB.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (proj1 ST) as LO0. pose proof (@alloc_ceiling_bounds _) as ACV.
    (* [comment removed for export] *)
    pose proof (asan_rtc_const m A_RSA_INFO [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] SOK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as TB1.
    pose proof (asan_rtc_const m A_ECKEY_INFO [Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] SOK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as TB2.
    pose proof (asan_rtc_const m A_ECKEYDH_INFO [Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] SOK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as TB3.
    pose proof (asan_rtc_const m A_ECDSA_INFO [Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] SOK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as TB4.
    unfold A_RSA_INFO, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in TB1, TB2, TB3, TB4. cbn [length] in TB1, TB2, TB3, TB4. clear SOK.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    Ltac epilogue ty :=
      zstep; zstep; zstep;
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with FRx : rw_cells _ mm _ [CB 8 _; C8 _], STx : stk _ mm _ _ |- _ =>
          lazymatch type of STx with stk _ _ _ (bv_unsigned ?spv + -16) => release_frame FRx STx (bv_unsigned spv) end end end;
      apply evtA_done; unfold pk_get_type_postA; eexists; eexists; eexists; exists ty; eexists; split; [reflexivity|];
      repeat match goal with |- _ /\ _ => split end; try eassumption;
      unfold A_RSA_INFO, A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO; cbn [In]; intros; try lia.
    (* [comment removed for export] *)
    Ltac prologue ST AB IMG' K0 NZ PKB :=
      carve_frame 16%nat ST;
      zstep; zstep;
      zstep; if_cases K0; zify_cond K0;
      [ exfalso; clear -K0 NZ PKB; rewrite ?unsigned_lit in K0 by lia; lia | ];
      let GOT := fresh "GOT" in let GSB := fresh "GSB" in
      pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB; rewrite (proj1 IMG') in GOT;
      zstep; zstep; zstep; clear GOT GSB;
      zstep; zstep; zstep; zstep; zstep.
    destruct HINF as [->|HINF].
    { clear OINF. prologue ST AB IMG' K0 NZ PKB. (* [comment removed for export] *) zstep. epilogue 0. }
    assert (CASES : info = 0x0f2180 \/ info = 0x0f2200 \/ info = 0x0f2280 \/ info = 0x0f2300).
    { clear - HINF. unfold A_RSA_INFO, A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in HINF. cbn [In] in HINF. lia. }
    clear HINF.
    assert (INF : info <> 0) by (clear -CASES; lia). assert (INFB : 0 <= info < 2^64) by (clear -CASES; lia).
    pose proof (OINF INF) as OI. clear OINF INF.
    assert (INF8 : info mod 8 = 0) by (destruct CASES as [-> | [-> | [-> | ->]]]; reflexivity).
    prologue ST AB IMG' K0 NZ PKB.
    zstep. if_cases KI; zify_cond KI. { exfalso. clear -KI CASES. rewrite ?unsigned_lit in KI by lia. lia. }
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_byte OI info 4 as k RD HK. zstep. clear RD. step_to_if. shadow_merge_regs2 info k HK 11 12.
    (* [comment removed for export] *)
    destruct CASES as [-> | [-> | [-> | ->]]].
    - zstep. epilogue 1.
    - zstep. epilogue 2.
    - zstep. epilogue 3.
    - zstep. epilogue 4.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
