(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepRsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_cmp U_mpi_cmp_int U_mpi_bitlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_rsa_check_context () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "rsa_ctxck_post"; "stdpp.bitvector.definitions.Z_to_bv"].


Definition U_RSA_CHECK_CONTEXT : Z := 0x2aa68.
(* [comment removed for export] *)
Notation RSA_CTXCK_STACK := 80 (only parsing).

Definition rsa_ctxck_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_rsa_check_context ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O14.O13.O12.O11.R10.R?.R>.O10.O?.R=.R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(8.O14.)O3.(9.(2.&40.))R1.(:.O15.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.O13.)+50.)(11.&40.O13.))(12.(=.$>.$>.)))O1.R1.)(4.(13.O15.O1.R1.)(4.(14.O15.R1.)(15.O15.R1.O2.(11.&40.O13.))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition rsa_field_live {L : heap_layout} (d : mpd) : Prop :=
  md_own d <> LStatic /\ (md_own d = LHeap -> 0 < md_p d /\ md_p d + 4 * md_n d <= alloc_ceiling).

Definition rsa_check_context_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list blk) (C : Z) (r : rsa_st) (lo : Z),
  rw_cells segs m C (rsa_head_cells r) -> 0 <= r_len r < 2^64 ->
  mpd_at segs m LB (r_N r) -> mpd_at segs m LB (r_E r) -> md_addr (r_N r) = C + 16 -> md_addr (r_E r) = C + 32 ->
  rsa_field_live (r_N r) -> rsa_field_live (r_E r) ->
  C mod 8 = 0 -> 0 < C -> C + RSA_CTX_SIZE <= alloc_ceiling ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSA_CTXCK_STACK -> alloc_ceiling <= lo -> bv_unsigned sp mod 16 = 0 ->
  mem_inv segs m -> bv_unsigned ra mod 2 = 0 ->
  a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 0 ->
  evt segs (rsa_ctxck_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Lemma fj8 : ltac2:(CDefT.buildp (gd_tbl_P_rsa_check_context ()) "Pmq,P,(2.&40.)(3.(2.&8.))PA,$>.Pbs,(16.(2.&8.))Prest,(16.$17.)P,(18.$19.R4.R3.(<.$17.(1:.#8.R2.)R1.))(18.$19.R5.R4.(<.$17.(1;.(1<.R3.))R2.))")
(* [comment removed for export] *).
Proof.
  intros mq A bs rest H. dpose H as [[[LEN WF] _] _]. cbn [cell_wf] in LEN.
  eapply rw_cells_reshape; [exact H| split; [exact I| exact WF]|].
  cbn [cells_bytes cbytes]. rewrite le8_le_bytes_to_word by exact LEN. reflexivity.
Qed.

Section CK.
  Context {L : heap_layout}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis SLO : lo <= bv_unsigned sp - RSA_CTXCK_STACK.
  Hypothesis ACL : alloc_ceiling <= lo.

  Notation POST := (rsa_ctxck_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
  Notation FRAME x := ([C8 x; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L11741095640.53L26924648792.53L27905220224.52L43654564952.53L51711223320.51L59499841752.53L7510805464.53 00000400800C00G00K00O00SS2spS2spS2sp2lo3SLOS2spS2spS2spS2sp". (* [comment removed for export] *)
  #[using="L SLO"] Lemma epilogue : ltac2:(CDefT.buildp (gd_tbl_P_rsa_check_context ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Px0,(2.&40.)Px1,(2.&40.)Px2,(2.&40.)Px3,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pxj,(2.&40.)P,(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.Vsp,)+50.)(11.&40.Vsp,))(12.(=.$>.$>.)))Vm,R16.)P,(13.$19.Vm,R17.)P,(14.$19.R18.)P,(15.$19.R19.Vlo,(1=.(11.&40.Vsp,)-30.))P,(18.$19.R1:.(1=.(11.&40.Vsp,)-30.)(<.$17.(1;.R5.)(<.$17.(1;.Vs3,)(<.$17.(1;.Vs2,)(<.$17.(1;.Vs1,)(<.$17.(1;.Vs0,)(<.$17.(1;.Vra,)(12.$17.))))))))(1>.$19.(1?.$19.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,Vm,)(6.(7.R1:.(20.&40.(1=.(11.&40.Vsp,)-30.))Vgp,Vtp,R19.R18.R17.R16.R15.R12.R11.R10.R?.R>.R=.R<.R;.R14.R13.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(20.&40.+2:<10.)Vfc,(9.(2.&40.))R1;.(:.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until xj. intros MU WM MI ST FR.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold rsa_ctxck_post. deexists 16.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End CK.

(* [comment removed for export] *)
Ltac after_call MU WM MU2 WM2 :=
  let MU' := fresh "MU" in let WM' := fresh "WM" in
  lazymatch type of MU2 with munch ?W2 ?ma ?mb =>
    lazymatch type of MU with munch ?W ?m0 ma =>
      assert (MU' : munch W m0 mb) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]; intros a Ha; cbn in Ha |- *; lia]);
      assert (WM' : wmono usegs m0 mb) by (eapply wmono_trans; [exact WM| exact WM2]);
      repeat match goal with
      | H : rw_cells usegs ma ?A ?cs |- _ => first [ apply (rw_cells_transport usegs W2 ma mb A cs) in H; [| exact MU2| exact WM2| cbn; repeat split; try exact I; lia] | clear H ]
      | H : stk usegs ma ?lo ?hi |- _ => first [ apply (stk_transport_disjoint usegs W2 ma mb lo hi) in H; [| exact MU2| exact WM2| cbn; repeat split; try exact I; lia] | clear H ]
      end;
      repeat match goal with H : mem_inv usegs ma |- _ => clear H end;
      clear MU WM MU2 WM2; try clear ma; rename MU' into MU; rename WM' into WM
    end
  end.

Local Ltac2 Set LiaOrc.tbl := fun () => "00o0@L11741095640.73 L14792943382.126L14792943382.76 L14792943382.92 L14792959895.127L14792959895.77 L14792959895.93 L16075573500.138L16075583823.104L16732214785.75 L17275046973.126L17275046973.92 L19354909044.74 L22706553362.112L22706553362.146L22706553362.96 L25161853392.76 L25161853392.92 L25382082548.74 L26924648792.74 L29323532093.76 L29377949301.96 L31378308326.72 L31392867444.74 L33512646752.96 L34150195072.127L37214132146.75 L37214132146.76 L37414286068.74 L3818671721.126 L3818671721.92  L38800639408.94 L41974782336.96 L43061382206.70 L43442376564.73 L43654564952.74 L4444862769.71  L4444862769.72  L46876645584.126L49937499712.78 L49937499712.79 L51467090849.88 L53136099426.70 L53136428267.71 L53519009202.108L53844364661.112L53844364661.146L55354765664.112L55354765664.146L57933459510.122L59308585216.129L59499841752.74 L61484595796.126L61484595796.92 L63720776961.76 L64343031936.112L64343031936.146L67564855989.144L7443838135.110 L7510805464.74  L806312532.126  L806312532.76   L806312532.92   00000;00^01A01d02G02j03M03N03O04204D04V04a05105J05Z06906X06c06n07@07K07V07a07b07m08_09]09h0:<0:P0:[0;>0;P0;[0;f0<D0<b0=A0=c0>E0>F0>e0?D0?O0?Z0?e0?f0?g0@80@C0@N0@Y0@d0AG0Aj0BM0BX0Bc0Bn0C[0DB0DiS2ra2sp1C1rS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPFFS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPBS2ra2sp1C1r2lo3SLOS2ra2sp1C1r2lo3SLOS2ra2sp1C1rS2ra2sp1C1r1a2HaS2ra2sp1C1r2rb2RB2KD1a2HaS2ra2sp1C1r1a2HaS1L2ra2sp1C1r2lo2C03CAC3ACL3SPBS1L2ra2sp1C1r2lo2C03CAC3ACL3SPBS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1r2lo3SLOS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rFS2ra2sp1C1rS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPB2HB5Ha_st5Hl_stS1L2ra2sp2s01C1r2lo2C03CAC3SLO3ACL3SPB2HB5Ha_st5Hl_st2s12s22s3S2ra2sp1C1rS1L2ra2sp1C1r2lo3ACLS1L2ra2sp1C1r2lo3ACLS2ra2sp1C1rS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPBS2ra2sp1C1r2lo3SLOS2ra2sp1C1rS2ra2sp1C1rS1L2ra2sp1C1r2lo2C03ACL3SPB2H0S1L2ra2sp1C1r2lo2C03ACL3SPB2H0S1L2ra2sp1C1r2lo2C03CAC3ACL3SPBS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB2H1S1L2ra2sp1C1r2lo2C03SLO3ACL3SPB2H1FS1L2ra2sp1C1r2lo2C03ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03ACL3SPB3ACPS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rFFS2ra2sp1C1r2rb2RBS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPBS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPBS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPBS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS1L2ra2sp1C1r2lo2C03SLO3ACL3SPA3SPB3ACP2K02K4S1L2ra2sp1C1r2lo2C03SLO3ACL3SPA3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPA3SPB3ACP". (* [comment removed for export] *)
Theorem U_rsa_check_context_spec {L : heap_layout} : rsa_check_context_stmt usegs U_RSA_CHECK_CONTEXT.
Proof.
  unfold rsa_check_context_stmt, U_RSA_CHECK_CONTEXT. intros until lo.
  intros HD LEN MN ME AN AE [NSN LVN] [NSE LVE] CAL C0 CAC ST SLO ACL SPA MI RA -> ->. unfold RSA_CTX_SIZE in CAC.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
  dpose MN as [[_ (_ & _ & LENN & NRN & OWNN)] SGN]. dpose ME as [[_ (_ & _ & LENE & NRE & OWNE)] SGE]. unfold MPI_MAX_LIMBS in NRN, NRE.
  assert (PN : md_own (r_N r) = LHeap -> 0 < md_p (r_N r)) by (intros H; exact (proj1 (LVN H))).
  assert (PE : md_own (r_E r) = LHeap -> 0 < md_p (r_E r)) by (intros H; exact (proj1 (LVE H))).
  assert (DN : md_p (r_N r) + 4 * md_n (r_N r) <= lo).
  { destruct (md_own (r_N r)) eqn:EO; [| destruct (LVN eq_refl); lia| exfalso; exact (NSN eq_refl)].
    destruct OWNN as [P0 N0]. rewrite P0, N0. lia. }
  assert (DE : md_p (r_E r) + 4 * md_n (r_E r) <= lo).
  { destruct (md_own (r_E r)) eqn:EO; [| destruct (LVE eq_refl); lia| exfalso; exact (NSE eq_refl)].
    destruct OWNE as [P0 N0]. rewrite P0, N0. lia. }
  (* [comment removed for export] *)
  assert (TRN : forall ma mb, mpd_at usegs ma LB (r_N r) -> munch [(bv_unsigned sp - 80, bv_unsigned sp)] ma mb -> wmono usegs ma mb -> mpd_at usegs mb LB (r_N r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSN| exact MUx| exact WMx| cbn; split; [rewrite AN; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (LVN EO). lia. }
  assert (TRE : forall ma mb, mpd_at usegs ma LB (r_E r) -> munch [(bv_unsigned sp - 80, bv_unsigned sp)] ma mb -> wmono usegs ma mb -> mpd_at usegs mb LB (r_E r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSE| exact MUx| exact WMx| cbn; split; [rewrite AE; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (LVE EO). lia. }
  clear OWNN OWNE.
  unfold rsa_head_cells in HD.
  carve_frame 48%nat ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mx) as MU; pose proof (wmono_refl usegs mx) as WM end.
  do 6 zstep. apply fj8 in FR.
  zstep; if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
  zstep. zstep. zstep; if_cases K00; zify_cond K00; [exfalso; rewrite ?unsigned_lit in K00 by lia; change 7 with (Z.ones 3) in K00; rewrite Z.land_ones in K00 by lia; change (2 ^ 3) with 8 in K00; lia|].
  zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_size_spec as SP. unfold mpi_size_stmt, U_MPI_SIZE in SP.
  eapply evt_cut; [ eapply SP with (lo := lo) (LB := LB) (dX := r_N r); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
    [ eapply TRN; [exact MN| exact MU| exact WM] | exact PN | assumption | eassumption | lia | lia | rewrite AN; lia | left; exact DN | rewrite AN; reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_size_post in PO. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by lia.
  ddestruct PO as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  replace (ret_pc (Z_to_bv 64 0x2aaa4)) with (Z_to_bv 64 0x2aaa4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_call MU WM MU2 WM2.
  zstep. zstep. zstep.
  zstep; if_cases K1; zify_cond K1.
  { eapply epilogue; eassumption. }
  zstep. zstep.
  zstep; if_cases K2; zify_cond K2.
  { eapply epilogue; eassumption. }
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_cmp_int_spec as SP. unfold mpi_cmp_int_stmt, U_MPI_CMP_INT in SP.
  eapply evt_cut; [ eapply SP with (lo := lo) (LB := LB) (dX := r_N r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
    [ eapply TRN; [exact MN| exact MU| exact WM] | exact PN | lia | eassumption | lia | lia | lia | rewrite AN; lia | left; exact DN | assumption | rewrite AN; reflexivity | reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_cmp_int_post in PO. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by lia.
  ddestruct PO as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & b12 & b13 & m3 & -> & MU3 & WM3 & MI3 & ST3).
  replace (ret_pc (Z_to_bv 64 0x2aacc)) with (Z_to_bv 64 0x2aacc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_call MU WM MU3 WM3.
  zstep. zstep. zstep.
  zstep; if_cases K3; zify_cond K3.
  { eapply epilogue; eassumption. }
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_get_bit_spec as SP. unfold mpi_get_bit_stmt, U_MPI_GET_BIT in SP.
  eapply evt_cut; [ eapply SP with (LB := LB) (dX := r_N r) (pos := 0);
    [ eapply TRN; [exact MN| exact MU| exact WM] | exact PN | assumption | lia | rewrite AN; reflexivity | reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_query_post in PO.
  ddestruct PO as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & m4 & rb & -> & MU4 & WM4 & MI4 & RB).
  replace (ret_pc (Z_to_bv 64 0x2aaec)) with (Z_to_bv 64 0x2aaec) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_call MU WM MU4 WM4.
  zstep. zstep.
  zstep; if_cases KD; zify_cond KD.
  { eapply epilogue; eassumption. }
  (* [comment removed for export] *)
  zstep; if_cases KE; zify_cond KE; [| exfalso; apply KE; reflexivity].
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_cmp_int_spec as SP. unfold mpi_cmp_int_stmt, U_MPI_CMP_INT in SP.
  eapply evt_cut; [ eapply SP with (lo := lo) (LB := LB) (dX := r_E r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
    [ eapply TRE; [exact ME| exact MU| exact WM] | exact PE | lia | eassumption | lia | lia | lia | rewrite AE; lia | left; exact DE | assumption | rewrite AE; reflexivity | reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_cmp_int_post in PO. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by lia.
  ddestruct PO as (d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & d8 & d9 & d10 & d11 & d12 & d13 & m5 & -> & MU5 & WM5 & MI5 & ST5).
  replace (ret_pc (Z_to_bv 64 0x2abfc)) with (Z_to_bv 64 0x2abfc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_call MU WM MU5 WM5.
  zstep; if_cases KF; zify_cond KF.
  - zstep. zstep. eapply epilogue; eassumption.
  - zstep. zstep. eapply epilogue; eassumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
