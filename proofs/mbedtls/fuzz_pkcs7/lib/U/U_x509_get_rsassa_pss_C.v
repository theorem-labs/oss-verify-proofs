(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_asn1_get_tag U_asn1_get_int U_oid U_oid_md_alg U_asn1_get_mpi U_platform_zeroize U_asn1_get_alg_A U_asn1_get_alg U_asn1_get_alg_null U_x509_get_hash_alg U_x509_get_rsassa_pss_A U_x509_get_rsassa_pss_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_get_rsassa_pss_C () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_rsassa_pss_A.x509_get_rsassa_pss_params_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section Walk.
  Variable L : heap_layout.
  Variables (MSF MDTBL : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PAR MD MGF SALT BUF pp lo : Z) (bs : list byte) (plen : word).

  Notation CTX := (rsassa_ctx usegs L MSF MDTBL U_ASN1_GET_ALG_NULL U_ASN1_GET_ALG U_OID_GET_MD_ALG U_X509_GET_HASH_ALG sp PAR MD MGF SALT BUF pp lo bs plen).
  Notation W := [(MD, MD + 4); (MGF, MGF + 4); (SALT, SALT + 4); (bv_unsigned sp - 240, bv_unsigned sp)].
  Notation POST := (x509_get_rsassa_pss_params_post usegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MD MGF SALT lo m).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -128)).
  Notation ENDv := (pp + bv_unsigned plen).
  Hypothesis HC : CTX.
  Let exit_walk' := exit_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.
  Let sel_walk' := sel_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.
  Let s4_walk' := s4_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.

  Let s3_walk' := s3_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.

  Ltac ro_const A n RO :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
      let cbs := eval vm_compute in (match image_bytes sg A n with Some cbs => cbs | None => [] end) in
      match goal with MI : mem_inv sg mx |- _ =>
        pose proof (ro_image_bytes_at sg mx A cbs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO end
    end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01B0@D12328612326.174D14496695657.175D1471770214.174 D15429104890.174D18283440501.174D21794495455.174D21964444855.175D26726616166.174D27268078258.174D28855904.174   D34638905935.174D40042707382.174D43565027189.174D44487020398.174D4595660713.174 D52025008742.174D52101704109.176D52830801283.176D53319155855.174D54422918901.174D57792617333.174D57979815413.174D58861881746.174D59307640550.174D59572647843.174D620542826.174  D62864553446.174D7426572789.174 L12328612326.157L13653540782.141L1471770214.157 L15429104890.157L19687428440.124L21794495455.157L26726616166.157L27268078258.157L28855904.157   L29010568730.153L34478491677.154L34638905935.157L3574711452.0   L36428190876.0  L36537129205.141L40042707382.157L44487020398.157L45639079680.128L4595660713.157 L52025008742.157L52253708504.123L52830801283.159L53319155855.157L53524301853.154L55810242966.155L57933460272.134L58222605362.173L58861881746.157L59307640550.157L59572647843.157L620542826.157  L62864553446.157L63612566464.128L6410639089.2   L67158371251.154L9510584448.128 R10189368499.153R1271112229.153 R15780612700.153R18476940209.142R18480641073.143R24181160982.172R30206791381.142R30210556245.143R30278721906.153R30643776721.153R34848507724.153R46366855809.153R47179524219.172R51273849100.153R51859990687.142R51872999199.143R63054757964.153R66030093070.15300000100U00V00W01501601Z01[01\01]01^01_02=02>02?02@03G03H03I03g04E04c04d04e04f04g04h05F06B06Y07U09I09`0;M0<I0=E0=F0=G0?50?V0?W0?X0?o0@00@10@L0A00Al0BC0C>0C_0EM0Eh0Ei0FG0GC0H?0Hd0Id0J`0LI0LS0M30MN0Of0PK0Rc0T<0UU0V^0WA0Wd0XI0YL0ZS0[40\50\^0]50]S0^Z0_]FS2sp3PAR2MD3MGF4SALT2bs3obs2rb3x381HFFS2sp3PAR2MD3MGF4SALT2bs3obs2rbFS2sp3PAR2MD3MGF4SALT2bs3obs2rb3x381HFFFFFS2sp3PAR2MD3MGF4SALT2bs3obs2rbFFFS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPR3obs2rb1a1HFFS2sp3PAR2MD3MGF4SALT2bs3obs2rbS2sp3PAR2MD3MGF4SALT2bs3obs2rbS2sp3PAR2MD3MGF4SALT2bs3obs2rbFFFFFS2sp3PAR2MD3MGF4SALT2bs3obs2rbS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obs2rbS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obs2rbS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen2q22e22ap3ALw4HAP23Hq13Hq24HPP23NZP3NZ13NZ23NZ33SLO2HD3SPR2K93obs4LENO2rb4HAP1S2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT3BUF2bs2ap4HAP12HD3NZP3NZ13NZ23NZ33SPR3obs2rb2pp4plen2q22e23ALw4HAP23Hq13Hq24HPP22K94LENOS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obs2rbS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obs2rbFFS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen2q22e22ap3ALw4HAP14HAP23Hq13Hq24HPP22B43NZP3NZ13NZ23NZ33NZB3SPR2K93obs2rb1rS2sp3PAR2MD3MGF4SALT2bs2HD3obs2rbSSS2sp3PAR2MD3MGF4SALT2bsFFS2sp3PAR2MD3MGF4SALT2bs3obsS2sp3PAR2MD3MGF4SALT2lo2bs2HD3obs2rbS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obs2rbS2sp3PAR2MD3MGF4SALT2bsS1L2sp3PAR2MD3MGF4SALT2bs3NZP3NZ13NZ23NZ32HD3SPR3obs2rb1a1HS2sp3PAR2MD3MGF4SALT2bs2HD3obs2rbS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen2q22e22ap3ALw4HAP14HAP23Hq13Hq24HPP22B43NZP3NZ13NZ23NZ33NZB3SPR2K93obs2rb1rS2sp3PAR2MD3MGF4SALT2bs3obsFS2sp3PAR2MD3MGF4SALT2bs3obs2rbS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obs2rbS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obs2rbS2sp3PAR2MD3MGF4SALT3BUF2bs2HD3obs2rbS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obs2rbS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obs2rbS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen2q22e22ap3ALw4HAP14HAP23Hq13Hq24HPP22B43NZP3NZ13NZ23NZ33NZB3SPR2K93obsS3obs4LENOS2sp3PAR2MD3MGF4SALT2bs3obs2rb1rS2sp3PAR2MD3MGF4SALT2bs3obsS1L2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen2q22e22ap2qp3QLw3ALw4HAP14HAP23HQP3Hq13Hq24HPP23NZP3NZ13NZ23NZ33NZB3SLO3ACL3ACP3SPR3MDB4MGFB5SALTB3QLR2K93obs2rbS2sp3PAR2MD3MGF4SALT2lo2bs3SLO3obs2rbS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen2q22e22ap3ALw4HAP14HAP23Hq13Hq24HPP23D123D233D2P3D2B3AL23NZP3NZ13NZ23NZ33SLO3SPA3DSP3DS13DS23DS33DSB3SPR2K93obs2rbS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen2q22e22ap3ALw4HAP23Hq13Hq24HPP23NZP3NZ13NZ23NZ33SPR2K9S2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen2q22e22ap3ALw4HAP23Hq13Hq24HPP23NZP3NZ13NZ23NZ33SPR2K9S2sp3PAR2MD3MGF4SALT2pp2bs4plen2q22e23Hq23NZP3NZ13NZ23NZ33SPR3obs2rb1r2KMS2sp3PAR2MD3MGF4SALT3BUF2bs2ap4HAP1S2sp3PAR2MD3MGF4SALT3BUF2bs2ap4HAP1S2sp3PAR2MD3MGF4SALT2lo2bs3DS23obs2rbS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPR3obs2rbS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPR3obs2rbS2sp3PAR2MD3MGF4SALT2lo2bs3obs2rbS2sp3PAR2MD3MGF4SALT2bs2q22e23Hq13NZP3NZ13NZ23NZ33SPR3obs2rb1r2KMS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3DSB3obs2rbS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT3BUF2bs2apS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPR3obs2rbS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPR3obs2rb". (* [comment removed for export] *)
  #[using="MSF MDTBL PAR HC exit_walk' s3_walk'"] Lemma s2b_walk : forall (q2 e2 ap qp : Z) (j4 : list byte) (tfw lw qtag qpad QLw atag apad ALw w1 w2 w3 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -128) [CB 12 j4; C4 tfw] ->
    rw_cells usegs mm (bv_unsigned sp + -112) [C4 qtag; C4 qpad; C8 QLw; C8 (Z_to_bv 64 qp)] ->
    rw_cells usegs mm (bv_unsigned sp + -88) [C4 atag; C4 apad; C8 ALw; C8 (Z_to_bv 64 ap)] ->
    rw_cells usegs mm (bv_unsigned sp + -64) [C8 lw] ->
    rw_cells usegs mm (bv_unsigned sp + -56) [C8 (Z_to_bv 64 q2)] ->
    rw_cells usegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs mm MD [C4 w1] -> rw_cells usegs mm MGF [C4 w2] -> rw_cells usegs mm SALT [C4 w3] ->
    bytes_at usegs mm BUF bs ->
    stk usegs mm lo (bv_unsigned sp + -128) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> statics_ok usegs L mm ->
    BUF <= ap -> ap + bv_unsigned ALw <= q2 ->
    ((qp = 0 /\ bv_unsigned QLw = 0) \/ (BUF <= qp /\ qp + bv_unsigned QLw = q2)) ->
    BUF <= q2 -> q2 <= e2 -> e2 <= ENDv ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 ENDv) (Z_to_bv 64 MGF) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 e2) (Z_to_bv 64 SALT) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x27b00) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros q2 e2 ap qp j4 tfw lw qtag qpad QLw atag apad ALw w1 w2 w3 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 mm
      F0 FPAR FALG FL FP FS HMD HMGF HSALT HBUF ST MU WM MI SOK HAP1 HAP2 HQP Hq0 Hq1 Hq2.
    open_ctx HC.
    pose proof (bv_unsigned_in_range 64 plen) as PLR. unfold bv_modulus in PLR. cbn in PLR.
    pose proof (bv_unsigned_in_range 64 ALw) as ALR. unfold bv_modulus in ALR. cbn in ALR.
    pose proof (bv_unsigned_in_range 64 QLw) as QLR. unfold bv_modulus in QLR. cbn in QLR.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
    { (* [comment removed for export] *)
      lxp_apply exit_walk. }
    lxp_gc.
    assert (A9 : bv_unsigned ALw = 9) by lxp_lia.
    (* [comment removed for export] *)
    ro_const 0x109dd 9%nat RO.
    set (obs := firstn (Z.to_nat 9) (skipn (Z.to_nat (ap - BUF)) bs)).
    assert (LENO : Z.of_nat (length obs) = 9) by (subst obs; apply bytes_at_sub_length; plia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with HB : bytes_at _ mx BUF bs |- _ =>
        assert (HOB : bytes_at usegs mx ap obs) by (subst obs; eapply bytes_at_sub; [exact HB| plia| plia| plia]) end end.
    clearbody obs.
    pose proof U_bcmp_spec as SPB. unfold memcmp_stmt in SPB.
    callp (eapply SPB; rewrite ?unsigned_lit by (clear_disj; lia);
           [ exact RO | exact HOB | reflexivity | clear -LENO; cbn; lia ]).
    clear SPB RO.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rb end.
    lxp_gc.
    lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
    { (* [comment removed for export] *) lxp_apply exit_walk. }
    (* [comment removed for export] *)
    lxp_gc. try lxp_statics.
    lxp_frame_cut (bv_unsigned sp + -128) [16; 40].
    pose proof HHASH as SPH. unfold x509_get_hash_alg_stmt, U_X509_GET_HASH_ALG in SPH.
    callx_sp (bv_unsigned sp + -128)
      (eapply SPH with (ALG := bv_unsigned sp + -112) (MGF := MGF) (BUF := BUF) (bs := bs) (ap := qp) (alen := QLw) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by plia; try eassumption; try reflexivity; try plia).
    clear SPH.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
    match goal with H : _ < r <= 0 |- _ => rename H into Hr end.
    match goal with H : stk _ m6 lo _ |- _ => rename H into ST6 end.
    lxp_gc.
    lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
    all: first [ lxp_at 162428; lxp_apply exit_walk | lxp_at 162188; lxp_apply s3_walk ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.
