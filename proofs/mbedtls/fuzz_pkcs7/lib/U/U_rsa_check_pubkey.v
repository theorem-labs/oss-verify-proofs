(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepRsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_cmp U_mpi_cmp_int U_mpi_bitlen U_rsa_check_context.
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
Ltac2 gd_tbl_P_rsa_check_pubkey () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "rsa_ckpub_post"; "stdpp.bitvector.definitions.Z_to_bv"].


Definition U_RSA_CHECK_PUBKEY : Z := 0x2a6b4.
(* [comment removed for export] *)
Notation RSA_CKPUB_STACK := 64 (only parsing).

Definition rsa_ckpub_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_rsa_check_pubkey ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O14.O13.O12.O11.R10.R?.R>.O10.O?.R=.R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(8.O14.)O3.(9.(2.&40.))R1.(:.O15.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.O13.)+40.)(11.&40.O13.))(12.(=.$>.$>.)))O1.R1.)(4.(13.O15.O1.R1.)(4.(14.O15.R1.)(15.O15.R1.O2.(11.&40.O13.))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rsa_check_pubkey_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list blk) (C : Z) (r : rsa_st) (lo : Z),
  rw_cells segs m C (rsa_head_cells r) -> 0 <= r_len r < 2^64 ->
  mpd_at segs m LB (r_N r) -> mpd_at segs m LB (r_E r) -> md_addr (r_N r) = C + 16 -> md_addr (r_E r) = C + 32 ->
  rsa_field_live (r_N r) -> rsa_field_live (r_E r) ->
  C mod 8 = 0 -> 0 < C -> C + RSA_CTX_SIZE <= alloc_ceiling ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSA_CKPUB_STACK -> alloc_ceiling <= lo -> bv_unsigned sp mod 16 = 0 ->
  mem_inv segs m -> bv_unsigned ra mod 2 = 0 ->
  a0 = Z_to_bv 64 C ->
  evt segs (rsa_ckpub_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

(* [comment removed for export] *)
Ltac after_callg segs MU WM MU2 WM2 :=
  let MU' := fresh "MU" in let WM' := fresh "WM" in
  lazymatch type of MU2 with munch ?W2 ?ma ?mb =>
    lazymatch type of MU with munch ?W ?m0 ma =>
      assert (MU' : munch W m0 mb) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]; intros a Ha; cbn in Ha |- *; lia]);
      assert (WM' : wmono segs m0 mb) by (eapply wmono_trans; [exact WM| exact WM2]);
      repeat match goal with
      | H : rw_cells segs ma ?A ?cs |- _ => first [ apply (rw_cells_transport segs W2 ma mb A cs) in H; [| exact MU2| exact WM2| cbn; repeat split; try exact I; lia] | clear H ]
      | H : stk segs ma ?lo ?hi |- _ => first [ apply (stk_transport_disjoint segs W2 ma mb lo hi) in H; [| exact MU2| exact WM2| cbn; repeat split; try exact I; lia] | clear H ]
      end;
      repeat match goal with H : mem_inv segs ma |- _ => clear H end;
      clear MU WM MU2 WM2; try clear ma; rename MU' into MU; rename WM' into WM
    end
  end.

Section CK.
  Context {L : heap_layout}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis SLO : lo <= bv_unsigned sp - RSA_CKPUB_STACK.
  Hypothesis ACL : alloc_ceiling <= lo.

  Notation POST := (rsa_ckpub_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
  Notation FRAME := ([C8 s2; C8 s1; C8 s0; C8 ra] : list cell).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L21887662552.51L33510041944.51L39941633408.50L41564619544.49L66083662040.51L9962237875.51 00000400800C00G00K00OS2spS2spS2sp2lo3SLOS2spS2spS2sp". (* [comment removed for export] *)
  #[using="L SLO"] Lemma ckpub_epilogue : ltac2:(CDefT.buildp (gd_tbl_P_rsa_check_pubkey ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Px0,(2.&40.)Px1,(2.&40.)Px2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.Vsp,)+40.)(11.&40.Vsp,))(12.(=.$>.$>.)))Vm,R14.)P,(13.$16.Vm,R15.)P,(14.$16.R16.)P,(15.$16.R17.Vlo,(17.(11.&40.Vsp,)-20.))P,(18.$16.R18.(17.(11.&40.Vsp,)-20.)(<.$19.(1:.Vs2,)(<.$19.(1:.Vs1,)(<.$19.(1:.Vs0,)(<.$19.(1:.Vra,)(12.$19.))))))(1;.$16.(1<.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,Vm,)(6.(7.R18.(1=.&40.(17.(11.&40.Vsp,)-20.))Vgp,Vtp,R17.R16.R15.R14.R13.R11.R10.R?.R>.R=.R<.R;.R:.R12.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(1=.&40.+2:7=0.)Vfc,(9.(2.&40.))R19.(:.$16.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros MU WM MI ST FR.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold rsa_ckpub_post. deexists 16.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End CK.

Local Ltac2 Set LiaOrc.tbl := fun () => "01<0@L13179633280.128L16073379393.207L16075573500.138L16075583823.105L16824686265.209L17326920880.95 L19579175174.179L21094488528.126L21233063351.111L21765854580.75 L21887662552.74 L22706553362.113L22706553362.146L22706553362.97 L23766147455.157L24866855941.196L25966668349.77 L2687496512.79  L2687496512.80  L27011181408.97 L2742311509.157 L2742311509.192 L27775132660.75 L3109483053.192 L32872689248.113L32872689248.146L33510041944.75 L34238294325.144L34290115814.73 L37214132146.76 L37214132146.77 L3818671721.126 L3818671721.93  L42815031504.77 L42815031504.93 L43061382206.71 L43198170881.76 L44390406261.97 L4444862769.72  L4444862769.73  L45293011284.126L45293011284.77 L45293011284.93 L46754034689.77 L50411599744.113L50411599744.146L51467090849.89 L52065442077.207L53136099426.71 L53136428267.72 L53519009202.109L53519009202.160L54059809799.161L54748384003.75 L57933459510.123L58571135293.126L58571135293.93 L59308585216.130L59308585216.163L59308585216.181L59308585216.198L59979377002.174L61484595796.126L61484595796.93 L62463095424.97 L6445239157.113 L6445239157.146 L66083662040.75 L7190686615.127 L7190686615.78  L7190686615.94  L7190735638.126 L7190735638.77  L7190735638.93  L9716869748.74  L9962237875.75  00000;00<00=00>00I00T00_01>01I01T01_01o02H02X03803C03U04704Y04Z04i05805C05`05a05b05m06806C07508008D08X09709V09h0:K0:V0;40;R0<?0<f0=M0>00>S0?60?70?80?W0@60@A0@L0@W0@b0A30AE0AW0Ab0Am0B80BC0BT0B_0Bj0CM0CX0Cc0Cn0DQ0E40EW0F:0F]0G@0GK0GVS2ra2sp1C1rFFFS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS1L2ra2sp1C1r2lo2C03CAC3ACL3SPBS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1r1a2HaS2ra2sp1C1r2rb2RB2KD1a2HaS2ra2sp1C1r1a2HaS2ra2sp1C1r2C03SPB3NRN2rc2RC3RCBS2ra2sp1C1rS2ra2sp1C1r2lo3SLOS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB2H1S1L2ra2sp1C1r2lo2C03SLO3ACL3SPB2H1FS2ra2sp1C1r3NRNS2ra2sp1C1r3NRES2ra2sp1C1rS2ra2sp1C1r2C03SPB3NRE2re3REBFFS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPB2HB5Ha_st5Hl_stS1L2ra2sp2s01C1r2lo2C03CAC3SLO3ACL3SPB2HB5Ha_st5Hl_st2s12s2S1L2ra2sp1C1r2lo3ACLS1L2ra2sp1C1r2lo3ACLS1L2ra2sp1C1r2lo2C03CAC3ACL3SPBS1L2ra2sp1C1r2lo2C03CAC3ACL3SPBS2ra2sp1C1r2lo3SLOS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPBS2ra2sp1C1rS1L2ra2sp1C1r2lo2C03ACL3SPB2H0S1L2ra2sp1C1r2lo2C03ACL3SPB2H0S1L2ra2sp1C1r2lo2C03SLO3ACL3SPA3SPB3ACP2K02K4S1L2ra2sp1C1r2lo2C03SLO3ACL3SPA3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPA3SPB3ACPS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPBS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPBS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPBFFS1L2ra2sp1C1r2lo2C03ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03ACL3SPB3ACPS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1r2rb2RBS2ra2sp1C1r2lo3SLOS2ra2sp1C1r2lo3SLOS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1r2rd2RDS2ra2sp1C1rS2ra2sp1C1rS1L2ra2sp1C1r2lo2C03CAC3SLO3ACL3SPBS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPS1L2ra2sp1C1r2lo2C03SLO3ACL3SPB3ACPS2ra2sp1C1rS2ra2sp1C1r". (* [comment removed for export] *)
Theorem U_rsa_check_pubkey_spec {L : heap_layout} : rsa_check_pubkey_stmt usegs U_RSA_CHECK_PUBKEY.
Proof.
  unfold rsa_check_pubkey_stmt, U_RSA_CHECK_PUBKEY. intros until lo.
  intros HD LEN MN ME AN AE [NSN LVN] [NSE LVE] CAL C0 CAC ST SLO ACL SPA MI RA ->. unfold RSA_CTX_SIZE in CAC.
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
  assert (TRN : forall ma mb, mpd_at usegs ma LB (r_N r) -> munch [(bv_unsigned sp - 64, bv_unsigned sp)] ma mb -> wmono usegs ma mb -> mpd_at usegs mb LB (r_N r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSN| exact MUx| exact WMx| cbn; split; [rewrite AN; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (LVN EO). lia. }
  assert (TRE : forall ma mb, mpd_at usegs ma LB (r_E r) -> munch [(bv_unsigned sp - 64, bv_unsigned sp)] ma mb -> wmono usegs ma mb -> mpd_at usegs mb LB (r_E r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSE| exact MUx| exact WMx| cbn; split; [rewrite AE; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (LVE EO). lia. }
  clear OWNN OWNE.
  unfold rsa_head_cells in HD.
  carve_frame 32%nat ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] mx) as MU; pose proof (wmono_refl usegs mx) as WM end.
  do 5 zstep.
  zstep; if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
  zstep. zstep. zstep; if_cases K00; zify_cond K00; [exfalso; rewrite ?unsigned_lit in K00 by lia; change 7 with (Z.ones 3) in K00; rewrite Z.land_ones in K00 by lia; change (2 ^ 3) with 8 in K00; lia|].
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_size_spec as SP. unfold mpi_size_stmt, U_MPI_SIZE in SP.
  eapply evt_cut; [ eapply SP with (lo := lo) (LB := LB) (dX := r_N r); rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia;
    [ eapply TRN; [exact MN| exact MU| exact WM] | exact PN | assumption | eassumption | lia | lia | rewrite AN; lia | left; exact DN | rewrite AN; reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_size_post in PO. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
  ddestruct PO as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  replace (ret_pc (Z_to_bv 64 0x2a6e8)) with (Z_to_bv 64 0x2a6e8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_callg usegs MU WM MU2 WM2.
  zstep. zstep. zstep.
  zstep; if_cases K1; zify_cond K1.
  { eapply ckpub_epilogue; eassumption. }
  zstep. zstep.
  zstep; if_cases K2; zify_cond K2.
  { eapply ckpub_epilogue; eassumption. }
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_cmp_int_spec as SP. unfold mpi_cmp_int_stmt, U_MPI_CMP_INT in SP.
  eapply evt_cut; [ eapply SP with (lo := lo) (LB := LB) (dX := r_N r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia;
    [ eapply TRN; [exact MN| exact MU| exact WM] | exact PN | lia | eassumption | lia | lia | lia | rewrite AN; lia | left; exact DN | assumption | rewrite AN; reflexivity | reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_cmp_int_post in PO. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
  ddestruct PO as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & b12 & b13 & m3 & -> & MU3 & WM3 & MI3 & ST3).
  replace (ret_pc (Z_to_bv 64 0x2a710)) with (Z_to_bv 64 0x2a710) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_callg usegs MU WM MU3 WM3.
  zstep. zstep. zstep.
  zstep; if_cases K3; zify_cond K3.
  { eapply ckpub_epilogue; eassumption. }
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_get_bit_spec as SP. unfold mpi_get_bit_stmt, U_MPI_GET_BIT in SP.
  eapply evt_cut; [ eapply SP with (LB := LB) (dX := r_N r) (pos := 0);
    [ eapply TRN; [exact MN| exact MU| exact WM] | exact PN | assumption | lia | rewrite AN; reflexivity | reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_query_post in PO.
  ddestruct PO as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & m4 & rb & -> & MU4 & WM4 & MI4 & RB).
  replace (ret_pc (Z_to_bv 64 0x2a730)) with (Z_to_bv 64 0x2a730) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_callg usegs MU WM MU4 WM4.
  zstep. zstep.
  zstep; if_cases KD; zify_cond KD.
  { eapply ckpub_epilogue; eassumption. }
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_cmp_int_spec as SP. unfold mpi_cmp_int_stmt, U_MPI_CMP_INT in SP.
  eapply evt_cut; [ eapply SP with (lo := lo) (LB := LB) (dX := r_E r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia;
    [ eapply TRE; [exact ME| exact MU| exact WM] | exact PE | lia | eassumption | lia | lia | lia | rewrite AE; lia | left; exact DE | assumption | rewrite AE; reflexivity | reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_cmp_int_post in PO. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
  ddestruct PO as (d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & d8 & d9 & d10 & d11 & d12 & d13 & m5 & -> & MU5 & WM5 & MI5 & ST5).
  replace (ret_pc (Z_to_bv 64 0x2a74c)) with (Z_to_bv 64 0x2a74c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_callg usegs MU WM MU5 WM5.
  zstep. zstep. zstep.
  zstep; if_cases KF; zify_cond KF.
  { eapply ckpub_epilogue; eassumption. }
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_bitlen_spec as SP. unfold mpi_bitlen_stmt, U_MPI_BITLEN in SP.
  eapply evt_cut; [ eapply SP with (LB := LB) (dX := r_N r);
    [ eapply TRN; [exact MN| exact MU| exact WM] | exact PN | assumption | rewrite AN; reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_query_post in PO.
  ddestruct PO as (e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & e12 & e13 & m6 & rc & -> & MU6 & WM6 & MI6 & RC).
  replace (ret_pc (Z_to_bv 64 0x2a768)) with (Z_to_bv 64 0x2a768) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_callg usegs MU WM MU6 WM6.
  pose proof (core_bitlen_range (md_limbs (r_N r)) (md_n (r_N r)) ltac:(lia)) as RCB. rewrite <- RC in RCB.
  zstep. zstep. zstep.
  zstep; if_cases KG; zify_cond KG.
  { eapply ckpub_epilogue; eassumption. }
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_get_bit_spec as SP. unfold mpi_get_bit_stmt, U_MPI_GET_BIT in SP.
  eapply evt_cut; [ eapply SP with (LB := LB) (dX := r_E r) (pos := 0);
    [ eapply TRE; [exact ME| exact MU| exact WM] | exact PE | assumption | lia | rewrite AE; reflexivity | reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_query_post in PO.
  ddestruct PO as (f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & f9 & f10 & f11 & f12 & f13 & m7 & rd & -> & MU7 & WM7 & MI7 & RD).
  replace (ret_pc (Z_to_bv 64 0x2a784)) with (Z_to_bv 64 0x2a784) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_callg usegs MU WM MU7 WM7.
  zstep. zstep. zstep.
  zstep; if_cases KH; zify_cond KH.
  { eapply ckpub_epilogue; eassumption. }
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_bitlen_spec as SP. unfold mpi_bitlen_stmt, U_MPI_BITLEN in SP.
  eapply evt_cut; [ eapply SP with (LB := LB) (dX := r_E r);
    [ eapply TRE; [exact ME| exact MU| exact WM] | exact PE | assumption | rewrite AE; reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_query_post in PO.
  ddestruct PO as (g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & g9 & g10 & g11 & g12 & g13 & m8 & re & -> & MU8 & WM8 & MI8 & RE).
  replace (ret_pc (Z_to_bv 64 0x2a7a0)) with (Z_to_bv 64 0x2a7a0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_callg usegs MU WM MU8 WM8.
  pose proof (core_bitlen_range (md_limbs (r_E r)) (md_n (r_E r)) ltac:(lia)) as REB. rewrite <- RE in REB.
  zstep. zstep. zstep.
  zstep; if_cases KI; zify_cond KI.
  { eapply ckpub_epilogue; eassumption. }
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof U_mpi_cmp_mpi_spec as SP. unfold mpi_cmp_mpi_stmt, U_MPI_CMP_MPI in SP.
  eapply evt_cut; [ eapply SP with (LB := LB) (dX := r_E r) (dY := r_N r);
    [ eapply TRE; [exact ME| exact MU| exact WM] | eapply TRN; [exact MN| exact MU| exact WM] | exact PE | exact PN | assumption | rewrite AE; reflexivity | rewrite AN; reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO.
  ddestruct PO as (h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & h11 & h12 & h13 & -> & _ & _ & MI9).
  replace (ret_pc (Z_to_bv 64 0x2a7bc)) with (Z_to_bv 64 0x2a7bc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  pose proof (Z.sgn_spec (mpd_val (r_E r) - mpd_val (r_N r))) as SG3.
  zstep. zstep. zstep. zstep. zstep.
  eapply ckpub_epilogue; eassumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
