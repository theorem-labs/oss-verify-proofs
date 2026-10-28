(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt ZBridge Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame LibTail MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import Restrict RestrictLib RestrictRun NodesA SymDriveA SymDriveAX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_base A_exit_lib A_exit_defs A_unreg_globals A_exit A_stdio_defs A_stdio_write A_stdio_call A_rip A_amem_lib A_imemcpy A_fwrite_oom A_oomtail A_printf1 A_refused.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SymDriveH4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AHeapL0.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tailkit_defs A_tailkit_exit2 A_splice A_imz A_icpt_str A_icpt_strnlen A_icpt_strnlenJ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tail_lib A_tail_openfail_defs A_tail_openfail_defs2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxADrvKit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxAKnDS.

Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_A_tail_openfail_S5 () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibA.SymDriveA.DcovZ"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_tail_lib.outzone"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_LO"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_HI"; "OF.VF"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.Env"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymDrive.blobs_ev"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.B.A_refused.SHW"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "Stdlib.ZArith.BinInt.Z.lxor"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Nat.sub"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "OF.EnvV"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_tail_lib.AGR"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "OF.FD2"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "OF.TT"; "OF.XL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.cons"; "OF.TT64"].

#[local] Existing Instance Lib.PropExec.fx0.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition PRE17 : list byte := s2b "cli: cannot open "%string.
Lemma PRE17_len : length PRE17 = 17%nat. Proof. reflexivity. Qed.
Lemma msg_cannot_open_eq : forall p, msg_cannot_open p = PRE17 ++ p ++ [Z_to_bv 8 10].
Proof. intros p. unfold msg_cannot_open, PRE17. reflexivity. Qed.

Lemma mo_mat_fds' : forall mo mo', mo_mat mo mo' -> m_fds mo' = m_fds mo.
Proof. unfold mo_mat, m_fds; intros mo mo' H; intuition congruence. Qed.

Section OF.  (* [comment removed for export] *)
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable KI : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000%Z.
  Hypothesis GSB : al_gsb AL = 0x1099f8%Z.
  Hypothesis IMGCS : A_unreg_globals.img_cs AL CS.
  Hypothesis K_halted : forall mo, KI mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "Pmo,$0.Pacc,(1.(2.(3.&40.)$4.))P,A1.VKI,R2.P,(5.VAL,VCS,R2.)(6.$0.Lmo',$0.(7.(8.(9.$0.)(:.R5.R4.)(;.$0.R1.))(7.A1.VKI,R1.(<.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "Pmo,$0.Pmo',$0.P,A1.VKI,R2.P,(8.$=.(>.R2.)(>.R3.))P,(8.(1.(2.(3.&40.)(3.&40.)))(?.R3.)(?.R4.))P,(8.(1.(3.&40.))(10.R4.)(10.R5.))P,(8.(9.(3.&40.))(11.R5.)(11.R6.))A1.VKI,R6.")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Variable sp0 : word.
  Variable model : Model.
  Hypothesis SPlo : (0x7fff7f000000 + 16384 <= bv_unsigned sp0)%Z.      (* [comment removed for export] *)
  Hypothesis SPhi : (bv_unsigned sp0 + 128 <= 0x800000000000)%Z.
  Hypothesis SPal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Hypothesis HKI : KI model.
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  (* [comment removed for export] *)
  Variable lo : Z.
  Hypothesis LOlo : (0x10007fff7fff < lo)%Z.
  Hypothesis LOhi : (lo + 16384 <= bv_unsigned sp0)%Z.
  Hypothesis LOdeep : (bv_unsigned sp0 - 8388608 <= lo)%Z.
  (* [comment removed for export] *)
  Variable STKHI : Z.
  Hypothesis STKHIlo : (bv_unsigned sp0 + 128 <= STKHI)%Z.
  Hypothesis STKHIhi : (STKHI <= 0x800000000000)%Z.
  Hypothesis STKHI64 : (STKHI mod 64 = 0)%Z.
  Hypothesis SCS : crange CS lo (STKHI - lo).
  (* [comment removed for export] *)
  Hypothesis FCS : crange CS 0x208c0 64.

  Variables (R : bvmap 5 word) (M : word -> option byte) (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Hypothesis G2 : getr R 2 = sp0.
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x63ca90.
  Hypothesis G8 : getr R 8 = Z_to_bv 64 2.
  Hypothesis G9 : getr R 9 = Z_to_bv 64 2.
  Hypothesis G20 : getr R 20 = Z_to_bv 64 0.
  Hypothesis G21 : getr R 21 = Z_to_bv 64 0.
  Hypothesis G22 : getr R 22 = Z_to_bv 64 0.
  Hypothesis G23 : getr R 23 = Z_to_bv 64 0.
  Hypothesis G24 : getr R 24 = Z_to_bv 64 0.
  Hypothesis G25 : getr R 25 = Z_to_bv 64 0.
  Hypothesis G26 : getr R 26 = Z_to_bv 64 0.
  Hypothesis G27 : getr R 27 = Z_to_bv 64 0.
  Hypothesis TM : tail_memA sp0 M can tid wp0 rp0 wp1 rp1.
  Hypothesis MAPD : mapped M lo (bv_unsigned sp0).
  (* [comment removed for export] *)
  Hypothesis ZSH : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "Ps,$12.P,(7.(13.(14.+7???8000.(15.Vlo,+8.))R1.)(16.R1.(14.+7???8000.(15.VSTKHI,+8.))))(8.(9.(3.&8.))A1.VM,(17.&40.R2.)(;.(3.&8.)(17.&8.=)))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Variables (P : word) (path extra : list byte).
  Let L : Z := Z.of_nat (length path).
  Let buf : list byte := path ++ Z_to_bv 8 0 :: extra.
  Hypothesis G18 : getr R 18 = P.
  Hypothesis BY : bytes_at asegs M (bv_unsigned P) buf.
  Hypothesis NZ : ~ In (Z_to_bv 8 0) path.
  Hypothesis WIN8 : ((bv_unsigned P + L) / 8 * 8 + 8 <= bv_unsigned P + Z.of_nat (length buf))%Z.
  Hypothesis Plo : (bv_unsigned sp0 + 128 <= bv_unsigned P)%Z.
  Hypothesis Phi : (bv_unsigned P + Z.of_nat (length buf) <= STKHI)%Z.          (* [comment removed for export] *)
  Hypothesis PL16 : (bv_unsigned P + L + 16 <= STKHI)%Z.                        (* [comment removed for export] *)
  Hypothesis LMAX : (L <= 131071)%Z.                                            (* [comment removed for export] *)
  Hypothesis L63 : (L <= 63)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L30247682266.71L35495549846.7000000f01>S3sp04SPlo2lo5STKHI7STKHIlo1P4path1L3buf3Plo1z2Hz1H2H0S3sp05STKHI1P4path1L3buf". (* [comment removed for export] *)
  Lemma PCS : crange CS (bv_unsigned P - bv_unsigned P mod 64) (STKHI - (bv_unsigned P - bv_unsigned P mod 64)).
  Proof. intros z Hz. apply SCS. pose proof LOhi. pose proof (Z.mod_pos_bound (bv_unsigned P) 64 ltac:(lia)). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SHRD : forall c, CS c -> exists b, bytes_at asegs M (shadow_of AL c) [b].
  Hypothesis CSTOP : forall c, CS c -> (c < 2^47)%Z.

  Let WINLO := (bv_unsigned sp0 - 4096)%Z.

  (* [comment removed for export] *)
  Let D : word -> bool := Dimg [(bv_unsigned sp0 - 4096, bv_unsigned sp0)%Z; (0x7fffc118, 0x7fffc120)%Z; (SSH_LO sp0, SSH_HI sp0); (bv_unsigned P + L, bv_unsigned P + L + 1)%Z].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L32276418883.71L57167447340.71L57657395591.7200000N01601gS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H". (* [comment removed for export] *)
  Lemma SSH_facts : (0x7fff8000 <= SSH_LO sp0)%Z /\ (SSH_HI sp0 <= 2^46)%Z /\ (SSH_LO sp0 < SSH_HI sp0)%Z.
  Proof. pose proof (SHW_range sp0 (-64) ltac:(lia) SPal ltac:(lia)). unfold SSH_LO, SSH_HI in *. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30247691664.7300000lS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1z2Hz". (* [comment removed for export] *)
  Lemma WCS : crange CS (bv_unsigned sp0 - 4096) 4096.
  Proof. intros z Hz. apply SCS. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma D_Dseg : forall a : word, segcov asegs (bv_unsigned a) = true -> D a = true.
  Proof. intros a H. unfold D. apply Dimg_Dseg. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L6097392651.7300000PS3sp05STKHI1P4path1L3buf5WINLO1c". (* [comment removed for export] *)
  Lemma shadow_aok : forall c x, CS c -> (x = 0x7fff8000 + c / 8)%Z -> aok_addr AL CS x.
  Proof. intros c x Hc ->. right; left. exists c. split; [exact Hc|]. unfold shadow_of. rewrite ASB. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L30247682393.77L51355856640.75L5268879960.75 L57161095762.75L60694983881.77L61028787006.75L67812584585.7500000m01a02A02i03L03j04MS3sp04SPlo2lo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1z2Hz2H02H1S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLO1zS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1z2A1S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1z2Hz". (* [comment removed for export] *)
  Lemma D_DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
  Proof.
    intros a H. unfold D in H. eapply (Dimg_DOK_aok AL CS IMG); [|exact H].
    repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
    - intros z Hz. left. apply WCS. lia.
    - intros z Hz. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply FCS; lia|]. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - intros z Hz. destruct (ssh_app sp0 z ltac:(lia) SPal Hz) as [A1 A2]. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply WCS; lia| exact A2].
    - intros z Hz. left. apply SCS. pose proof LOhi. pose proof PL16. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L21596567953.73L39798645229.73L54785595177.7300000`01C01oS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf4PL165WINLOS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp04SPlo5STKHI1P4path1L3buf3Plo4PL165WINLO". (* [comment removed for export] *)
  Lemma D_pl : DcovZ D (bv_unsigned P + L) (bv_unsigned P + L + 1).
  Proof. intros z Hz. unfold D. eapply Dimg_cov; [right; right; right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L15567213029.74L44851314733.74L54785602528.74L60924558468.7400000P00n01\02?S3sp05STKHI1P4path1L3buf5WINLO1HS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf4PL165WINLO2H02H1S3sp04SPlo5STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_D0 : D (Z_to_bv 64 0) = false.
  Proof. pose proof SSH_facts. pose proof SPlo. pose proof Plo. unfold D. apply Dimg_D0. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition RRUN := rz_runA asegs D AL CS KI K_halted K_mat D_Dseg asegs_top D_DOK D_D0.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L30901545954.77L46534914516.77L60924549197.7700000n01Q024S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1a1b2Ha2Hb1z2HzS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_frame : forall a b, (bv_unsigned sp0 - 4096 <= a)%Z -> (b <= bv_unsigned sp0)%Z -> DcovZ D a b.
  Proof. intros a b Ha Hb z Hz. unfold D. apply (Dimg_cov _ (bv_unsigned sp0 - 4096) (bv_unsigned sp0)); [left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40646207469.7700000nS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1a1b2Ha2Hb1z2Hz". (* [comment removed for export] *)
  Lemma D_img : forall a b, (0x10000 <= a)%Z -> (b <= 0x65f000)%Z -> DcovZ D a b.
  Proof. intros a b Ha Hb z Hz. unfold D. apply Dimg_img. unfold AIMG_LO, AIMG_HI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L43185048941.73L44851324132.73L58554083103.7300000S01101OS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_fsh : DcovZ D 0x7fffc118 0x7fffc120.
  Proof. intros z Hz. unfold D. eapply Dimg_cov; [right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LITS_KND : list (Z * Z) := [(0x10000, 0x65f000)%Z; (0x7fffc118, 0x7fffc120)%Z].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L51855127614.7100000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma HLITS_KND : Forall (fun iv => DcovZ D (fst iv) (snd iv)) LITS_KND.
  Proof. repeat (apply Forall_cons; [cbn [fst snd] |]); [apply D_img; lia | exact D_fsh | apply Forall_nil]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18267881737.75L5599869189.75 00000V01<S3sp05STKHI1P4path1L3buf5WINLO3qhi3HhiS3sp05STKHI1P4path1L3buf5WINLO3qlo3Hlo". (* [comment removed for export] *)
  Lemma D_frameS : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "Pqlo,$12.Pqhi,$12.P,(13.(14.(18.&40.Vsp0,)-1000.)R2.)P,(13.R2.(14.(18.&40.Vsp0,)=))(19.VD,R4.R3.)")
(* [comment removed for export] *).
  Proof. intros qlo qhi Hlo Hhi. apply D_frame; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L13440388671.74L15567222060.74L52039345437.7400000S01301SS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLO1HS3sp05STKHI1P4path1L3buf5WINLO1H". (* [comment removed for export] *)
  Lemma D_ssh : DcovZ D (SSH_LO sp0) (SSH_HI sp0).
  Proof. pose proof SSH_facts. intros z Hz. unfold D. eapply Dimg_cov; [right; right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L53694884100.75000017S3sp02lo5STKHI1P4path1L3buf5WINLO1x2Hr2O24SPlo4LOhi7STKHI643Plo4PL162O1". (* [comment removed for export] *)
  Lemma D_out_zone : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "Px,(3.&40.)P,(8.$1:.A1.VD,R1.$1;.)P,(1<.Vlo,(18.&40.Vsp0,)R2.)(1=.(7.(7.(13.+10000.(18.&40.R3.))(16.(18.&40.R3.)+65?000.))(1>.(7.(13.+?:488.(18.&40.R3.))(16.(18.&40.R3.)+?:570.))))(1=.(7.(13.+7???<118.(18.&40.R3.))(16.(18.&40.R3.)+7???<120.))(1=.(7.(13.(1?.Vsp0,)(18.&40.R3.))(16.(18.&40.R3.)(20.Vsp0,)))(8.$12.(18.&40.R3.)(14.(18.&40.VP,)VL,)))))")
(* [comment removed for export] *).
  Proof.
    intros x Dx [O1 O2]. unfold D, Dimg in Dx. apply Dof_true in Dx as (iv & Hin & Hr).
    cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; unfold AIMG_LO, AIMG_HI in *; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition V0 : list word := [sp0] ++ junk_vals R ++ [can] ++ repeat (Z_to_bv 64 0) 8.
  Lemma V0_len : length V0 = 42%nat.
  Proof. unfold V0. rewrite !length_app, junk_vals_length. reflexivity. Qed.
  Lemma V0_0 : vals_ev V0 0 = sp0. Proof. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54434947932.7100000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma V0_33 : vals_ev V0 33 = can.
  Proof. unfold V0, vals_ev. change ([sp0] ++ junk_vals R ++ [can] ++ repeat (Z_to_bv 64 0) 8) with (([sp0] ++ junk_vals R) ++ ([can] ++ repeat (Z_to_bv 64 0) 8)).
    rewrite app_nth2; [|rewrite length_app, junk_vals_length; cbn; lia]. rewrite length_app, junk_vals_length. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma V0_junk : forall i, (i < 32)%nat -> vals_ev V0 (1 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold V0, vals_ev. cbn [app length Nat.add].
    change (sp0 :: junk_vals R ++ can :: repeat (Z_to_bv 64 0) 8) with ([sp0] ++ (junk_vals R ++ (can :: repeat (Z_to_bv 64 0) 8))).
    change (S i) with (length [sp0] + i)%nat. rewrite app_nth2_plus. rewrite app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54434947932.7100000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma V0_19 : vals_ev V0 19 = P. Proof. change 19%nat with (1 + 18)%nat. rewrite (V0_junk 18) by lia. exact G18. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VF (V : list word) : Prop :=
    (forall n, (n < 42)%nat -> vals_ev V n = vals_ev V0 n) /\ (42 <= length V)%nat.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L25269778915.7100000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma VF0 : VF V0. Proof. split; [intros; reflexivity | rewrite V0_len; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L21188810707.77L9784235213.75 00000i01aS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2P21n2HnS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V3ext2P2". (* [comment removed for export] *)
  Lemma VF_app : forall V ext, VF V -> VF (V ++ ext).
  Proof. intros V ext [P1 P2]. split; [| rewrite length_app; lia]. intros n Hn. rewrite vals_ev_app_l by lia. apply P1. exact Hn. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30227048842.7300000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf0 : forall V, VF V -> vals_ev V 0 = sp0. Proof. intros V [P1 _]. rewrite (P1 0%nat) by lia. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54441433323.7300000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf19 : forall V, VF V -> vals_ev V 19 = P. Proof. intros V [P1 _]. rewrite (P1 19%nat) by lia. apply V0_19. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54441433323.7300000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf33 : forall V, VF V -> vals_ev V 33 = can. Proof. intros V [P1 _]. rewrite (P1 33%nat) by lia. apply V0_33. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55760870395.7500000US3sp05STKHI1R1P4path1L3buf5WINLO1i2Hi". (* [comment removed for export] *)
  Lemma regs_okV0 : regs_ok (Env (vals_ev V0) (blobs_ev [])) sr_OF R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_OF all_regs];
      first [ (cbn [edenot]; first [ reflexivity | exact G3 | exact G4 | exact G8 | exact G9 | exact G20 | exact G21 | exact G22 | exact G23
                                   | exact G24 | exact G25 | exact G26 | exact G27 | (cbn [ev]; rewrite V0_0; exact G2) ])
            | (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                 change (edenot (Env (vals_ev V0) (blobs_ev [])) (EVar n)) with (vals_ev V0 n); rewrite (V0_junk (n - 1)) by lia; reflexivity end) ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01;0?L13042945941.85L13484217602.85L14054083309.89L14499496082.85L15439463048.85L16774753289.85L17543312104.87L1756166345.85 L18928696722.85L2183569985.85 L21927717721.85L21986899558.85L22604873481.85L2431328725.89 L24690173574.85L24992216082.85L25271909867.85L2564951689.85 L25940753974.85L27134698386.85L27315410273.85L27352604565.85L28434372873.85L29762371858.85L31327315070.89L31396711570.85L32648418366.91L32873232769.89L33148392579.85L33669037980.85L34577004134.85L34774111081.85L3506990866.85 L3829630897.89 L39213365269.85L39510883410.85L40253358217.85L43030311433.85L44353219849.85L44510486418.85L44751598473.85L44851494802.85L4504975677.89 L46809767186.85L48461698953.85L5004984661.85 L51238950418.85L52457697417.85L52875384210.85L53519161933.89L53519190958.85L54226205864.85L54967497737.85L55007380242.85L55149030888.87L55662616861.89L55849630025.85L5641132690.85 L58560891017.85L58961367305.85L5926593349.85 L61064399881.85L62675677899.85L6275277449.85 L64037435666.85L64202541330.85L64791502857.85L65502196882.85L65732472201.85L66336703634.85L67631326282.89L68058909735.85L68075363561.85L7781517330.85 L9911486354.85 00000f01D02B02`03>03\04?04]05;05Y06706Z07807Z08808V09409R0:00:N0;10;T0<20<P0=H0=f0>f0?K0?L0?j0@H0@f0AD0Aj0Ak0BI0Bg0CE0Cc0DA0D_0E=0Ea0F?0F]0GE0Gc0HA0H_0I?0I]0I^0J<0JZ0K=0L80LV0M40MR0N00NN0Nl0Nm0OK0Oi0PG0Pe0QC0Qa0R?0Rd0SB0S`0T>0T\S3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1HS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H2H01d1m2Hd2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1n1BS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf3Plo4PL165WINLO1H3off1n1B1CS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1d1m2Hd2Hm1x2HxS3sp05STKHI1P4path1L3buf5WINLO1d1m2HdFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO3off1n1CFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO3off1AS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1mS3sp05STKHI1P4path1L3buf5WINLOFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1d1m2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1d1m2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma know_okV0 : know_ok asegs (Env (vals_ev V0) (blobs_ev [])) M kn_OF.
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal. pose proof (u64_range P) as PR.
    pose proof TM as TM'. destruct TM' as [WIN RO ERR CAN RTC ZI ZS _ _ _ _ _ _ _ _ _ _ _ _].
    assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat (Env (vals_ev V0) (blobs_ev [])) (SA (ELit 0) off) n).
    { intros off n A B C. apply flat_abs0; lia. }
    unfold know_ok, kn_OF.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    all: try (split; [lia|]; split; [apply FL; lia|]; rewrite adenot_lit0; cbn [edenot];
              first [ exact CAN
                    | (apply (rtc_rdn1 _ _ _ RTC); rtc_in)
                    | (apply (rtc_rdn8 _ _ _ RTC); rtc_in)
                    | (eapply (zrun_rdn8 _ _ _ _ ZI); cbv -[Z.le]; lia) ]).
    all: first
      [ (* [comment removed for export] *) split; [lia|]; cbn [edenot ev]; rewrite V0_0; assumption
      | (* [comment removed for export] *) cbn [edenot ev]; rewrite V0_0; lia
      | (* [comment removed for export] *) cbn [edenot ev]; rewrite V0_19; lia
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot ev]; rewrite ?V0_0; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off]; cbn [edenot ev]; rewrite ?V0_0;
        apply store_ok_of_all; rewrite u_small by lia; [lia|]; intros x Hx; apply WIN; lia
      | (* [comment removed for export] *) split; [lia|]; split; [lia|]; intros i Hi; first [apply RO; lia | apply ERR; lia]
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia;
        apply store_ok_data; rewrite u_small by lia; lia
      | match goal with |- ?g => idtac "KNOWN-GOAL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac covtac :=
    try (unfold estart, elenZ; cbn [a_base a_off]);
    first [ exact I
          | cbn [edenot ev];
            lazymatch goal with VFV : VF ?V |- _ => rewrite ?(vf0 V VFV) | _ => idtac end;
            rewrite ?u_small by lia; intros z Hz;
            first [ apply (D_img z (z + 1)); lia | apply (D_frame z (z + 1)); lia | apply D_fsh; lia ] ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L17034448047.78L29784460291.77L3479498253.77 L43935895424.79L47803405696.79L55715225071.77L59576963504.79L63368316460.79L63368316589.78L63368325619.77L64266648997.77L66561261592.79L8929201831.80 00000i01G02J03003V04404T05405T06206h07H08GS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1k2HkS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1k2H12H2S3sp05STKHI1P4path1L3buf5WINLO1k2H12H2S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1kS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2Hk2H12H22H3". (* [comment removed for export] *)
  Lemma shw_denotV : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "PV,(1.(3.&40.))Pk,$12.P,(21.R2.)P,(7.(13.-1000.R2.)(13.R2.=))(8.$12.(18.&40.(22.(23.(24.R4.)(25.(26.(1.(3.&8.)))))(27.$28.(27.$29.(27.$2:.(27.$29.(2;.#0.)(2<.R3.))(2<.+3.))(2<.+7???8000.))(2<.-8.))))(2=.Vsp0,R3.))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo. pose proof SPhi.
    intros V k VFV Hk. cbn [edenot ev]. rewrite (vf0 V VFV).
    rewrite alu_and. rewrite alu_add. rewrite alu_srl. rewrite (alu_add sp0).
    unfold v_and, v_add, v_srl.
    replace (bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + bv_unsigned (Z_to_bv 64 k))))%Z with (bv_unsigned sp0 + k)%Z.
    2:{ rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
        rewrite Zplus_mod_idemp_r. symmetry. apply Z.mod_small. lia. }
    rewrite (unsigned_lit 3) by lia. change (3 mod 64)%Z with 3%Z. rewrite Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
    pose proof (Z.div_pos (bv_unsigned sp0 + k) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (bv_unsigned sp0 + k) 8 (2^45) ltac:(lia) ltac:(lia)).
    rewrite (unsigned_lit ((bv_unsigned sp0 + k) / 8)) by lia. rewrite (unsigned_lit 2147450880) by lia.
    rewrite (unsigned_lit ((bv_unsigned sp0 + k) / 8 + 2147450880)) by lia.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with 18446744073709551608%Z by reflexivity.
    rewrite A_rip.land_m8 by lia. rewrite unsigned_lit.
    2:{ pose proof (Z.mod_pos_bound ((bv_unsigned sp0 + k) / 8 + 2147450880) 8 ltac:(lia)). lia. }
    unfold SHW. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L3479498253.75 L35907637249.76L40825277235.75L53519168529.76L55715225071.75L64266638075.76L64266648997.7500001301V02402T03203h04^S3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1k2H1S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2HkS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2Hk". (* [comment removed for export] *)
  Lemma and3_lit : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "Pk,$12.P,(7.(13.-1000.R1.)(13.R1.=))(8.$1:.(2>.&40.(2?.$28.(17.&40.(14.(18.&40.Vsp0,)R2.))(17.&40.+3.))(17.&40.=))(30.(31.R2.+4.)=))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo. pose proof SPhi.
    intros k Hk. rewrite alu_and. unfold v_and. rewrite (unsigned_lit 3), (unsigned_lit (bv_unsigned sp0 + k)) by lia.
    rewrite land3_mod4 by lia. pose proof (Z.mod_pos_bound (bv_unsigned sp0 + k) 4 ltac:(lia)).
    unfold bv_eqb. rewrite !unsigned_lit by lia. apply (mod4_of_sp (bv_unsigned sp0) k); [exact SPal | lia | reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L37106200957.75L5744834796.75 L61929758668.75L8443611008.75 00000]01@01c02FS3sp04SPlo5STKHI1P4path1L3buf5WINLO1x1n2Hx2HnS3sp05STKHI1P4path1L3buf5WINLO1x2HxS3sp05STKHI1P4path1L3buf5WINLO1n2HnS3sp05STKHI1P4path1L3buf5WINLO1x2Hx". (* [comment removed for export] *)
  Lemma not_ltu_small : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "Px,$12.Pn,$12.P,(7.(13.=R2.)(16.R2.(32.+2.+30.)))P,(7.(13.=R2.)(16.R2.(32.+2.+10.)))(8.$1:.(33.&40.(17.&40.(34.(18.&40.(17.&40.R4.))(18.&40.(17.&40.-1.))))(17.&40.R3.))$35.)")
(* [comment removed for export] *).
  Proof.
    intros x n Hx Hn. rewrite (unsigned_lit x) by lia. replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z by reflexivity.
    rewrite zb_lxor_ones by lia. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma alu_add_zlit : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "Px,(3.&40.)Pk,$12.P,(7.(13.=(14.(18.&40.R2.)R1.))(16.(14.(18.&40.R2.)R1.)(32.+2.+40.)))(8.(3.&40.)(2?.$29.R3.(17.&40.R2.))(17.&40.(14.(18.&40.R3.)R2.)))")
(* [comment removed for export] *).
  Proof.
    intros x k Hk. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac evs :=
    cbn [ev eb];
    lazymatch goal with VFV : VF ?V |- _ => rewrite ?(vf0 V VFV), ?(vf19 V VFV), ?(vf33 V VFV) | _ => idtac end;
    repeat match goal with H : vals_ev ?V ?n = _ |- context [vals_ev ?V ?n] => rewrite H end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L21188810707.7500000US3sp05STKHI1P4path1L3buf5WINLO1V1n2Hn". (* [comment removed for export] *)
  Lemma vals_ev_app_ge : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "PV,(1.(3.&40.))Pext,(1.(3.&40.))Pn,$4.P,(36.(37.(3.&40.)R3.)R1.)(8.(3.&40.)(24.(38.(3.&40.)R4.R3.)R2.)(24.R3.(39.R2.(37.(3.&40.)R4.))))")
(* [comment removed for export] *).
  Proof. intros V ext n Hn. unfold vals_ev. rewrite app_nth2 by lia. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Ltac solve_sc :=
    cbn [sc_denot branch_taken];
    first
      [ (* [comment removed for export] *)
        lazymatch goal with VFV : VF ?V |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off];
          rewrite !(shw_denotV V) by (first [exact VFV | lia]);
          lazymatch goal with |- context [SHW sp0 ?k] =>
            pose proof (SHW_range sp0 k ltac:(lia) SPal ltac:(lia)); pose proof SSH_facts end;
          cbn [edenot]; rewrite ?(u_small 8), ?(u_small 4), ?(u_small 0) by lia; lia end
      | (* [comment removed for export] *)
        lazymatch goal with VFV : VF ?V, AGk : AGR M lo (bv_unsigned sp0) ?Mk |- exists bs, rdn _ (restrict _ ?Mk) _ _ = Some bs /\ _ =>
          exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
          [ lazymatch goal with |- rdn _ _ (adenot _ (SA ?e 0)) 8 = _ =>
              unfold adenot, v_addi; cbn [a_base a_off]; rewrite Z.add_0_r;
              lazymatch e with context [ELit ?k] =>
                rewrite (shw_denotV V k VFV) by lia;
                pose proof (SHW_range sp0 k ltac:(lia) SPal ltac:(lia)); pose proof SSH_facts;
                apply (RestrictRun.rdn_restrictD asegs D);
                [ eapply (AGR_rdn M lo (bv_unsigned sp0) LOlo Mk); [exact AGk | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | lia |];
                  eapply (zrun_rdn8 _ _ _ _ (tm_zstk _ _ _ _ _ _ _ _ TM)); lia
                | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                | rewrite u_small by lia; intros z Hz; apply D_ssh; cbn in Hz; lia ] end end
          | cbn [edenot]; evs; vm_compute; reflexivity ] end
      | cbn [edenot]; evs; rewrite ?alu_add_zlit by lia;
        first
          [ (* [comment removed for export] *) apply Bool.negb_true_iff; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia
          | (* [comment removed for export] *)
            unfold bv_eqb, bv_ltu; rewrite !unsigned_lit by lia; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Bool.negb_false_iff; apply Z.ltb_lt]; lia
          | (* [comment removed for export] *) rewrite and3_lit by lia; reflexivity
          | (* [comment removed for export] *) rewrite alu_or; unfold v_or; rewrite !unsigned_lit by lia; reflexivity
          | (* [comment removed for export] *) rewrite alu_and, alu_or; unfold v_and, v_or; apply rf_memset_align_false'; lia
          | (* [comment removed for export] *) rewrite alu_xor; unfold v_xor; apply not_ltu_small; lia ]
      | match goal with |- ?g => idtac "SC-LEFT:" g end ].

(* [comment removed for export] *)
  Lemma regs_ok_tree : forall E sr Rx, regs_ok E sr Rx -> regs_ok E sr (regs_tree Rx).
  Proof. intros E sr Rx HR r. rewrite getr_regs_tree. apply HR. Qed.

  (* [comment removed for export] *)
  Ltac to_tree HR :=
    lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?Rx _ _ _) _) _ =>
      apply (srzJ_getr_ext asegs (regs_tree Rx) Rx); [intros r; apply getr_regs_tree|];
      apply regs_ok_tree in HR; unfold regs_tree in HR |- * end.
  (* [comment removed for export] *)
  Ltac regvV HR r :=
    lazymatch type of HR with regs_ok ?E ?sr ?Rx =>
      let e := eval vm_compute in (sr_get sr r) in
      rewrite (reg_val E sr Rx r HR); change (sr_get sr r) with e; cbn [edenot]; evs; rewrite ?alu_add_zlit by lia
    end.


  (* [comment removed for export] *)
  Record FK (Mk : mem) : Prop := MKFK {
    fk_mi : mem_inv asegs Mk;
    fk_mapped : mapped Mk lo (bv_unsigned sp0);
    fk_stk : stk asegs Mk lo (bv_unsigned sp0);
    fk_buf : bytes_at asegs Mk (bv_unsigned P) buf;
    fk_shrd : forall c, CS c -> exists b, bytes_at asegs Mk (shadow_of AL c) [b];
    fk_rip : rip_consts Mk;
    fk_sn : sn_consts Mk;
    fk_amem : amem_consts Mk;
    fk_zstr : forall s : Z, (0x7fff8000 + lo / 8 <= s < 0x7fff8000 + STKHI / 8)%Z -> Mk (Z_to_bv 64 s) = Some (Z_to_bv 8 0);
    fk_zstk : forall a : Z, SSH_LO sp0 <= a < SSH_HI sp0 -> Mk (Z_to_bv 64 a) = Some (Z_to_bv 8 0);
    fk_aobj : aobj asegs AL CS Mk (bv_unsigned P) (L + 1)
  }.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L17743517653.92 L18614817987.92 L2008272931.101 L24498169710.92 L27076589246.94 L29443216221.92 L29731801447.94 L30247691664.94 L37492600210.101L42153134065.92 L46058870405.92 L46530783016.92 L56457790905.92 L56765667309.94 L58965540039.89 L65604097635.92 L8120965920.94  L8564305960.92  00000[01`02a03_05805d06m08608d09P0:70:`0;e0<d0=B0>90?80?lS3sp02lo5STKHI1P4path5extra1L3buf3Plo5WINLOS3sp04SPlo2lo4LOlo6LOdeep5STKHI7STKHIhi1P4path1L3buf3Plo5WINLO1H1s2HsS3sp04SPlo2lo6LOdeep5STKHI1P4path5extra1L3buf3Plo5WINLO1H1c2Q02H3S3sp04SPlo2lo4LOlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1s2HsS3sp04SPlo2lo4LOlo4LOhi5STKHI7STKHIlo7STKHI641P4path5extra1L3buf3Plo4PL165WINLO1H2H11s2HsS3sp02lo4LOlo5STKHI1P4path5extra1L3buf5WINLOS3sp04SPlo2lo6LOdeep5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1H2H21a2HaS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path5extra1L3buf3Plo4PL165WINLO1H1z2HzS3sp04SPlo5STKHI1P4path5extra1L3buf5WINLO1c2Q0S3sp02lo4LOlo5STKHI1P4path5extra1L3buf5WINLOS3sp05STKHI1P4path5extra1L3buf5WINLO2H1S3sp04SPhi5STKHI1P4path5extra1L3buf5WINLOS3sp04SPlo2lo4LOlo6LOdeep5STKHI7STKHIhi1P4path1L3buf3Plo5WINLO1H1s2HsS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1H2H21a2HaS3sp05STKHI1P4path5extra5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1HS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1H2H21a2HaS3sp04SPlo5STKHI1P4path5extra1L3buf3Plo4PL165WINLO1H". (* [comment removed for export] *)
  Lemma facts : forall Mk, AGR M lo (bv_unsigned sp0) Mk -> FK Mk.
  Proof.
    intros Mk AG. pose proof SPlo. pose proof SPhi. pose proof (u64_range P). pose proof SSH_facts.
    pose proof TM as TM'. destruct TM' as [WIN RO ERR CAN RTC ZI ZS STKW MI _ _ _ _ _ _ _ _ _ _].
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    assert (MP : mapped Mk lo (bv_unsigned sp0)) by (eapply (AGR_mapped M lo (bv_unsigned sp0)); [exact AG | exact MAPD]).
    assert (ZSTR' : forall s : Z, (0x7fff8000 + lo / 8 <= s < 0x7fff8000 + STKHI / 8)%Z -> Mk (Z_to_bv 64 s) = Some (Z_to_bv 8 0)).
    { intros s Hs. eapply (AGR_byte M lo (bv_unsigned sp0) Mk s); [exact AG | lia | lia | lia | apply ZSH; exact Hs]. }
    assert (LBUF : Z.of_nat (length buf) = L + 1 + Z.of_nat (length extra)) by (subst buf L; rewrite length_app; cbn [length]; lia).
    split.
    - eapply (AGR_mem_inv M lo (bv_unsigned sp0) LOlo MI Mk AG ERR).
    - exact MP.
    - apply mapped_stk; [exact MP | lia | lia].
    - eapply (AGR_bytes_at M lo (bv_unsigned sp0) Mk); [exact AG | rewrite LBUF; lia | rewrite LBUF; lia | exact BY].
    - intros c Hc. destruct (SHRD c Hc) as [b Hb]. exists b.
      destruct CSOK as (C1 & _). destruct (C1 c Hc) as (Q0 & Q1 & Q2 & _). pose proof (CSTOP c Hc).
      eapply (AGR_bytes_at M lo (bv_unsigned sp0) Mk); [exact AG | cbn [length]; unfold shadow_of; rewrite ASB; lia | cbn [length]; unfold shadow_of; rewrite ASB; lia | exact Hb].
    - apply rtc_rip_consts. eapply asan_rtc_munch_fw; [apply (AGR_munch2 M lo (bv_unsigned sp0) Mk AG) | lia | exact RTC].
    - apply rtc_sn_consts. eapply asan_rtc_munch_fw; [apply (AGR_munch2 M lo (bv_unsigned sp0) Mk AG) | lia | exact RTC].
    - apply rtc_amem_consts. eapply asan_rtc_munch_fw; [apply (AGR_munch2 M lo (bv_unsigned sp0) Mk AG) | lia | exact RTC].
    - exact ZSTR'.
    - intros a Ha. eapply (AGR_byte M lo (bv_unsigned sp0) Mk a); [exact AG | lia | lia | lia | apply ZS; exact Ha].
    - apply (aobj_of_zero_range AL CS Mk (bv_unsigned P) (L + 1) CSOK ASB); [| lia | lia | intros s Hs; apply ZSTR'; lia].
      intros z Hz. apply SCS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac awp Ls := (repeat (first [ rewrite (edenot_addw0_r _ _) by (exact Ls) | rewrite (edenot_addw0_l _ _) by (exact Ls) | rewrite (edenot_exts4 _ _) by (exact Ls) ])); exact Ls.
  Ltac awn Ls := repeat (first [ rewrite (edenot_addw0_r _ _) by (awp Ls) | rewrite (edenot_addw0_l _ _) by (awp Ls) | rewrite (edenot_exts4 _ _) by (awp Ls) ]).
  (* [comment removed for export] *)
  Ltac swnorm := repeat match goal with
    | |- context [bv_swrap 32 ?z] =>
        lazymatch z with context [bv_swrap 32 _] => fail | context [bv_unsigned (Z_to_bv 64 _)] => fail | _ => rewrite (swrap32_small z) by lia end end.
  Ltac cmpL :=
    cbn [edenot ev]; repeat match goal with H : vals_ev ?V ?n = _ |- context [vals_ev ?V ?n] => rewrite H end;
    rewrite ?w_addw, ?w_subw; unfold v_addw, v_subw;
    rewrite ?alu_add, ?alu_sub, ?m_mul;
    repeat (progress (unorm; swnorm; rewrite ?vadd_ZZ, ?vsub_ZZ, ?vmul_ZZ));
    rewrite ?lts_ZZ, ?ltu_ZZ, ?eqb_ZZ by lia; cbn [negb];
    first [ reflexivity
          | apply Z.ltb_ge; lia | apply Z.ltb_lt; lia | apply Z.eqb_neq; lia | apply Z.eqb_eq; lia
          | apply Bool.negb_true_iff; first [apply Z.ltb_ge; lia | apply Z.eqb_neq; lia | apply Z.leb_gt; lia]
          | apply Bool.negb_false_iff; first [apply Z.ltb_lt; lia | apply Z.eqb_eq; lia | apply Z.leb_le; lia] ].


  (* [comment removed for export] *)
  Ltac azl := repeat match goal with
    | |- context [alu64 ALU_ADD ?x (Z_to_bv 64 ?k)] =>
        lazymatch x with context [alu64 ALU_ADD _ _] => fail | _ => rewrite (alu_add_zlit x k) by (unorm; lia) end
    end; unorm.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EnvV (V : list word) : env := Env (vals_ev V) (blobs_ev []).
  Definition TT : TSet := t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model)).
  Definition FD2 (mo : Model) : Prop := fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Definition STG (V : list word) (nx : nat) (sr : list expr) (kn : list kentry) (pc : Z) (X : list word -> mem -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "PRk,(3:.&5.(3.&40.))PMk,P,(3.&40.)(9.(3.&8.))Pmok,$0.P,(21.O6.)P,(8.$4.(37.(3.&40.)O6.)O5.)P,(3;.(3<.O6.)O4.R5.)P,(3=.$3>.(3<.O6.)R5.O3.)P,(3?.VM,Vlo,(18.&40.Vsp0,)R6.)P,A1.VKI,R6.P,(8.$40.(41.R7.)(41.Vmodel,))P,(42.R8.)P,A2.O1.O6.R:.(43.$3>.(44.(45.$46.R<.(17.&40.O2.)R;.(47.$3>.))R:.)$48.)")
(* [comment removed for export] *).
  Definition XL (V : list word) : Prop := vals_ev V 150 = Z_to_bv 64 L.
  Definition X0 (V : list word) (Mk : mem) : Prop := True.
  Definition XC (V : list word) (Mk : mem) : Prop := XL V.
  Definition XD (V : list word) (Mk : mem) : Prop := XL V /\ bytes_at asegs Mk (bv_unsigned sp0 - 447) path.
  Definition XE (V : list word) (Mk : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "(7.(49.O2.)(7.(4:.$3>.O1.(4;.(18.&40.Vsp0,)+1;?.)Vpath,)(4:.$3>.O1.(14.(4;.(18.&40.Vsp0,)+1;?.)VL,)(4<.(3.&8.)(17.&8.+:.)(26.(3.&8.))))))")
(* [comment removed for export] *).
  Definition S_A2 : Prop := forall V, STG V 74 srA2 knA2 0x5b1b4 X0.
  Definition S_B1 : Prop := forall V, STG V 106 srB1 knB1 0x5b504 X0.
  Definition S_B2 : Prop := forall V, STG V 138 srB2 knB2 0x5b1b4 X0.
  Definition S_C1 : Prop := forall V, STG V 172 srC1 knC1 0x0e79c4 XC.
  Definition S_D : Prop := forall V, STG V 205 srD knD 0x0e6f40 XD.
  Definition S_E : Prop := forall V, STG V 237 srE knE 0x0e6f40 XE.
  (* [comment removed for export] *)
  Definition TT64 : TSet := t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model)).
  Definition STG64 (V : list word) (nx : nat) (sr : list expr) (kn : list kentry) (pc : Z) (X : list word -> mem -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S5 ()) "PRk,(3:.&5.(3.&40.))PMk,P,(3.&40.)(9.(3.&8.))Pmok,$0.P,(21.O6.)P,(8.$4.(37.(3.&40.)O6.)O5.)P,(3;.(3<.O6.)O4.R5.)P,(3=.$3>.(3<.O6.)R5.O3.)P,(3?.VM,Vlo,(18.&40.Vsp0,)R6.)P,A1.VKI,R6.P,(8.$40.(41.R7.)(41.Vmodel,))P,(42.R8.)P,A2.O1.O6.R:.(43.$3>.(44.(45.$46.R<.(17.&40.O2.)R;.(47.$3>.))R:.)$4=.)")
(* [comment removed for export] *).
  Definition S_D64 : Prop := forall V, STG64 V 205 (sc_sr resC2X) (sc_kn resC2X) (sc_ret resC2X) XC.

  (* [comment removed for export] *)
  Ltac block_AG AGk EQM OUT :=
    first [ eapply (AGR_blockb D _ M lo (bv_unsigned sp0) _ _ _ 0%nat (-16384) 0 sp0 AGk EQM OUT);
            [ cbv [ev EnvV]; apply vf0; assumption
            | vm_compute; reflexivity
            | clear -LOhi; lia
            | clear; lia
            | clear -LOlo; lia
            | pose proof (u64_range sp0) as XAG; clear -XAG; lia ]
          | idtac "block_AG: slow path";
            eapply (AGR_block D); [exact AGk | exact EQM | exact OUT |];
            intros x Dx Ox; destruct (D_out_zone x Dx Ox) as [Z1|[Z1|[Z1|Z1]]]; cbn [log_out]; unfold adenot, v_addi; cbn [a_base a_off edenot]; evs;
            rewrite ?(u_small 0) by lia; repeat split; rewrite ?u_small by lia; first [lia | exact I] ].

  Hypothesis NEXT : S_D.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L23025466106.74L34632200121.7400000d01GS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLOS3sp05STKHI1P4path1L3buf4LMAX5WINLO". (* [comment removed for export] *)
  Lemma L_small : forall V, VF V -> XL V -> (bv_unsigned (edenot (EnvV V) (EVar 150)) < 2 ^ 31)%Z.
  Proof. intros V _ X. unfold EnvV. cbn [edenot ev]. unfold XL in X. rewrite X, u_small by lia. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01:0@L10522145838.104L10532534814.131L11579491730.131L11590142882.109L14099423816.131L14334882987.152L1549806836.131 L1561655345.109 L18151294435.131L18452601618.1  L18883718649.131L19447901811.131L19447918453.128L20567396662.104L21207871518.109L21652664198.109L21891445317.131L23020990950.109L23033794386.94 L24623709742.148L24625795186.148L25271742705.91 L26284087059.131L26507518862.131L27076589246.133L27271145910.104L28154758796.131L29443215018.2  L29445646130.104L30247691664.133L30426774553.131L30798836150.104L31239185691.128L32032333883.3  L32969781146.131L34640370193.94 L35223706974.131L35793178497.128L37622523289.154L39798645229.106L41501515606.104L41501515606.109L42086406536.131L42150874946.143L42333743922.154L43227823838.131L46533078311.2  L47504249154.104L49101448649.131L49670407343.131L50087249302.104L50355136518.104L50355136518.109L51286067578.105L52516241414.104L5305592158.131 L53517044390.104L53517044390.109L54426540266.92 L54439436909.143L57477269362.104L58695151760.152L59281996762.131L5965105702.104 L59774524505.131L60601234940.131L60669077807.152L60679793202.131L61345436742.131L61673028896.128L63536787603.104L64880151874.109L68512710453.133L93225074.131   00000h01i02_03L04804d05W06:07G07L08=08n09V0:90::0:]0;N0<K0=O0>H0?d0@L0A@0Al0CF0DC0EI0ER0FG0Gj0H^0IA0J:0JG0K30Kb0LS0MO0Nf0ON0PK0QH0RL0S@0T40T`0Ti0UQ0V=0Vl0WO0X20XU0Y80Y[0ZL0Zo0[R0\:0\f0]N0^W0_M0`J0a;0b<0c20ch0d\0eG0f00fW0gh0hjS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V3Hlo2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V3Hlo2LV3ds44LEN4S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp02lo5STKHI1P4path1L3buf3Plo5WINLO1V2LV3ds44LEN4S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2PR2LV3ds44LEN4S3sp0S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVFS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV3ds44LEN4S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V3Hlo2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO2V13LV11V3Hlo2LVS3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN41x1l2l02HxS3sp04SPlo2lo5STKHI7STKHI641P4path1L3buf3Plo4PL165WINLO1V3Hlo2LV3ds44LEN41H1x2Hx1g7STKHIlo1lS3sp05STKHI1P4path1L3buf5WINLO2V13LV12LVS3sp02lo4LOlo5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp04SPlo4SPal2lo5STKHI7STKHIlo7STKHI641P4path1L3buf3Plo3L635WINLO1V3Hlo2LV3ds44LEN41s2HsS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V3Hlo2LVS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V3Hlo2LV3ds44LEN4S2lo4LOloS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf4PL165WINLO1V2LVS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo4PL165WINLO1V3Hlo2LV3ds44LEN41z2Hz4SPal7STKHI642PRS3sp02lo4LOhi5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LVS3sp02lo4LOhiS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp05STKHI1P4path1L3buf4LMAX5WINLO2V13LV11V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L635WINLO1V3Hlo2LVS3sp04SPlo2lo4LOhi5STKHI7STKHI641P4path1L3buf3Plo4PL163L635WINLO1V3Hlo2LV3ds44LEN41x2HxS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V3Hlo2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V3Hlo2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V3Hlo2LV2HL3ds44LEN4S3sp02lo4LOlo5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN41x2HxS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp03XAGS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO2V13LV12LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp04SPlo2lo5STKHI7STKHI641P4path1L3buf3Plo4PL165WINLO1V3Hlo2LV3ds44LEN4S3sp02lo6LOdeep5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V3Hlo2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V3Hlo2LV3ds44LEN4S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp02lo4LOhi5STKHI1P4path1L3buf5WINLO1V2LV3ds44LEN4S3sp02lo4LOhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path5extra1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf3L635WINLO1V2LVS3sp04SPlo2lo5STKHI7STKHI641P4path1L3buf3Plo4PL165WINLO1V3Hlo2PR2LV3ds44LEN41z2HzS3sp04SPlo5STKHI1P4path1L3buf3Plo4PL163L635WINLO1V3Hlo2LV3ds44LEN4". (* [comment removed for export] *)
  Theorem stage_C1 : S_C1.
  Proof.
    intros V1 Rk Mk mok VFV1 LV1 HR HK AGk HKk FS FD XC1.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SSH_facts as SSF. pose proof (u64_range P) as PR.
    unfold EnvV in HR, HK. unfold XC in XC1.
    (* [comment removed for export] *)
    set (V := V1 ++ [Z_to_bv 64 0]).
    apply (env_app_regs V1 [Z_to_bv 64 0] (blobs_ev []) srC1 Rk ltac:(rewrite LV1; vm_compute; reflexivity)) in HR.
    apply (env_app_know asegs V1 [Z_to_bv 64 0] (blobs_ev []) Mk knC1 ltac:(rewrite LV1; vm_compute; reflexivity)) in HK.
    pose proof (VF_app V1 [Z_to_bv 64 0] VFV1) as VFV. fold V in HR, HK, VFV.
    assert (LV : length V = 173%nat) by (subst V; rewrite length_app, LV1; reflexivity).
    assert (EV172 : vals_ev V 172 = Z_to_bv 64 0) by (subst V; rewrite vals_ev_app_ge, LV1 by (rewrite LV1; lia); reflexivity).
    assert (EV150 : vals_ev V 150 = Z_to_bv 64 L) by (subst V; rewrite vals_ev_app_l by (rewrite LV1; lia); exact XC1).
    assert (Lsmall : (bv_unsigned (edenot {| ev := vals_ev V; eb := blobs_ev [] |} (EVar 150)) < 2 ^ 31)%Z).
    { cbn [edenot ev]. rewrite EV150, u_small by lia. lia. }
    clearbody V. clear VFV1 LV1 XC1.
    destruct (facts Mk AGk) as [MIk MPk STk BUFk SHRDk RIPk SNk AMk ZSTRk ZSTKk OBJk].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try clear KND; lazymatch type of HR with regs_ok (Env (vals_ev ?Vx) ?bb) _ _ =>
      pose proof (kn_inD_residualS D (Env (vals_ev Vx) bb) sp0 (-4096) 0 LITS_KND ltac:(cbn [ev]; apply vf0; assumption) D_frameS HLITS_KND) as KND end.
    time (run_blockA3S RRUN KND FUEL_OF STOPS_OF scrC1 172%nat true covtac).
    all: try solve_sc.
    (* [comment removed for export] *)
    all: try (lazymatch goal with |- srealizesJ _ _ _ => fail | _ => cbn [sc_denot branch_taken]; awn Lsmall; cmpL end).
    (* [comment removed for export] *)
    all: try (lazymatch goal with |- exists bs, rdn _ (restrict _ _) _ _ = Some bs /\ _ =>
      exists [Z_to_bv 8 0]; split;
      [ unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite (vf19 V VFV), EV150, Z.add_0_r;
        rewrite alu_add_zlit by lia; rewrite (u_small (bv_unsigned P + L)) by lia;
        apply (RestrictRun.rdn_restrictD asegs D);
        [ pose proof (bytes_at_rdn asegs Mk (bv_unsigned P) buf (length path) 1 BUFk ltac:(unfold buf; rewrite length_app; cbn [length]; lia)) as RD;
          unfold buf in RD; rewrite skipn_app, Nat.sub_diag, skipn_all in RD; cbn [skipn firstn app] in RD;
          unfold wa in RD; replace (bv_unsigned P + Z.of_nat (length path))%Z with (bv_unsigned P + L)%Z in RD by (unfold L; lia); exact RD
        | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
        | rewrite u_small by lia; intros z Hz; apply D_pl; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz; lia ]
      | cbn [edenot ev]; rewrite EV172; reflexivity ] end).
    all: try (lazymatch goal with |- flat _ _ _ => unfold flat, estart, elenZ; cbn [a_base a_off edenot ev]; rewrite (vf19 V VFV), EV150; rewrite ?alu_add_zlit, ?u_small by lia; lia end).
    all: match goal with |- srealizesJ _ _ _ => idtac | |- ?g => idtac "C1-SC-LEFT" g end.
    rename EQM into EQM1. rename OUT into OUT1. rename R0 into R1. rename M0 into M1. rename mo into mo1. rename HKmo into HK1. rename MM into MM1.
    assert (AG1 : AGR M lo (bv_unsigned sp0) M1) by (block_AG AGk EQM1 OUT1).
    clear AGk EQM1 OUT1. rename AG1 into AGk.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try clear KND; lazymatch type of HR with regs_ok (Env (vals_ev ?Vx) ?bb) _ _ =>
      pose proof (kn_inD_residualS D (Env (vals_ev Vx) bb) sp0 (-4096) 0 LITS_KND ltac:(cbn [ev]; apply vf0; assumption) D_frameS HLITS_KND) as KND end.
    time (run_blockA3S RRUN KND FUEL_OF STOPS_OF scrC2 173%nat true covtac).
    all: try solve_sc.
    all: try (lazymatch goal with |- srealizesJ _ _ _ => fail | _ => cbn [sc_denot branch_taken]; awn Lsmall; cmpL end).
    all: match goal with |- srealizesJ _ _ _ => idtac | |- ?g => idtac "C2-SC-LEFT" g end.
    rename EQM into EQM2. rename OUT into OUT2. rename R0 into R2. rename M0 into M2. rename mo into mo2. rename HKmo into HK2. rename MM into MM2.
    assert (AG2 : AGR M lo (bv_unsigned sp0) M2) by (block_AG AGk EQM2 OUT2).
    clear AGk EQM2 OUT2. rename AG2 into AGk.
    (* [comment removed for export] *)
    pose proof HR as HR0. to_tree HR.
    destruct (facts M2 AGk) as [MI2 MP2 ST2 BUF2 SHRD2 RIP2 SN2 AM2 ZSTR2 ZSTK2 OBJ2].
    assert (HL : L = Z.of_nat (length path)) by reflexivity.
    assert (BYP2 : bytes_at asegs M2 (bv_unsigned P) path).
    { unfold buf in BUF2. exact (proj1 (proj1 (bytes_at_app asegs M2 (bv_unsigned P) path (Z_to_bv 8 0 :: extra)) BUF2)). }
    destruct (u8arr_of_mapped M2 (bv_unsigned sp0 - 447) (length path)
                ltac:(eapply mapped_sub; [exact MP2 | lia | lia]) ltac:(lia) ltac:(lia)) as (ds4 & LEN4 & ARR4).
    time (eapply (splice_evtA2 AL CS KI K_halted K_mat V (blobs_ev []) _ _ _ M2 mo2 KEPT_CR (-1088) (-447) 63 lo
              (fun R' M' => u8arr asegs M' (bv_unsigned sp0 - 447) path /\ mem_inv asegs M') 0x67db8 0x0e6f40);
      [ exact HR | exact HK | exact HK2
      | rewrite LV; vm_compute; reflexivity | rewrite LV; vm_compute; reflexivity | cbn; intuition discriminate
      | rewrite (vf0 V VFV); unfold AIMG_HI; lia | rewrite (vf0 V VFV); lia | lia | lia | lia | rewrite (vf0 V VFV); lia | rewrite (vf0 V VFV); lia
      | | ]).
    { (* [comment removed for export] *)
      regvV HR0 (1%bv : reg). regvV HR0 (2%bv : reg). regvV HR0 (10%bv : reg). regvV HR0 (11%bv : reg). regvV HR0 (12%bv : reg).
      eapply (evtA_cut asegs AL CS); [apply (jstep_walk_memcpy AL IMG ALWF); exact CSOK|].
      cbn beta. intros ms1 ->.
      eapply evtA_mono.
      - time (eapply (imemcpy_spec AL IMG ALWF CS CSOK ASB) with (DST := bv_unsigned sp0 - 447) (SRC := bv_unsigned P) (n := L) (lo := lo) (ds := ds4) (ss := path);
          rewrite ?(unsigned_lit (bv_unsigned sp0 + -1088)) by lia;
          first [ exact ARR4 | exact BYP2 | exact SHRD2 | exact AM2 | exact MI2
                | lazymatch goal with |- aobj _ _ _ _ (bv_unsigned P) _ => eapply aobj_sub; [exact OBJ2 | lia | lia] end
                | lazymatch goal with |- aobj _ _ _ _ _ _ => apply (aobj_of_zero_range AL CS M2 _ _ CSOK ASB); [intros z Hz; apply SCS; lia | lia | lia | intros s Hs; apply ZSTK2; unfold SSH_LO, SSH_HI; lia] end
                | lazymatch goal with |- app_range _ _ => unfold app_range; right; lia end
                | lazymatch goal with |- amem_apart _ _ => unfold amem_apart; lia end
                | lazymatch goal with |- (1 <= _)%Z -> crange CS (bv_unsigned P - _) _ /\ _ => intros _; split; intros z Hz; apply PCS; lia end
                | lazymatch goal with |- (1 <= _)%Z -> _ /\ _ => intros _; split; intros z Hz; apply SCS; lia end
                | lazymatch goal with |- crange CS lo _ => intros z Hz; apply SCS; lia end
                | lazymatch goal with |- stk _ _ lo ?hi => apply (proj1 (stk_split asegs M2 lo hi (bv_unsigned sp0) ST2 ltac:(lia))) end
                | lazymatch goal with |- @eq word _ (Z_to_bv 64 (bv_unsigned P)) => symmetry; apply Z_to_bv_bv_unsigned end
                | lazymatch goal with |- @eq word (Z_to_bv 64 _) (Z_to_bv 64 _) => f_equal; lia end
                | lazymatch goal with |- @eq word _ (Z_to_bv 64 L) => exact EV150 end
                | lazymatch goal with |- _ \/ _ => lia end
                | lia
                | match goal with |- ?g => idtac "IMC4-LEFT:" g end ]).
      - cbn beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ARR' & SRC' & ST').
        eexists _, m'. split; [rewrite ret_pc_even by (first [lia | reflexivity]); reflexivity|].
        split; [intros r Hr; cbn [In KEPT_CR] in Hr; repeat (destruct Hr as [<-|Hr]; [reflexivity|]); destruct Hr|].
        rewrite ?(unsigned_lit (bv_unsigned sp0 + -1088)) in MU by lia. rewrite ?(vf0 V VFV).
        split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [Frame.outside]; intros x Hx; repeat split; try exact I; lia|].
        split; [exact WM|]. split; [exact ARR' | exact MI']. }
    (* [comment removed for export] *)
    intros R3 M3 mo3 (ARR3 & MI3) MU3 WM3 HR3 HK3 HKmo3 MM3.
    rewrite LV in HR3.
    pose proof (VF_app V (junk_vals R3) VFV) as VF3.
    apply (NEXT (V ++ junk_vals R3) R3 M3 mo3 VF3).
    - rewrite length_app, junk_vals_length, LV. reflexivity.
    - exact HR3.
    - exact HK3.
    - eapply (AGR_munch _ M lo (bv_unsigned sp0) M2 M3); [exact AGk | exact MU3 | exact WM3 | | unfold AIMG_HI; lia].
      cbn [Frame.outside]. rewrite !(vf0 V VFV). pose proof LOhi. intros x Hx.
      destruct (Z_le_gt_dec lo x); destruct (Z_lt_le_dec x (bv_unsigned sp0)); try lia; exfalso; apply Hx; repeat split; lia.
    - exact HKmo3.
    - rewrite (mo_mat_fs _ _ MM3), (mo_mat_fs _ _ MM2), (mo_mat_fs _ _ MM1). exact FS.
    - unfold FD2 in *. rewrite (mo_mat_fds' _ _ MM3), (mo_mat_fds' _ _ MM2), (mo_mat_fds' _ _ MM1). exact FD.
    - (* [comment removed for export] *) split.
      + unfold XL. rewrite vals_ev_app_l by (rewrite LV; lia). exact EV150.
      + exact (proj1 ARR3).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End OF.
