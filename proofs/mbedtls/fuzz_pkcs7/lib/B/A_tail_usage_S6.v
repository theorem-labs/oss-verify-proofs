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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tailkit_defs A_tailkit_exit2 A_tailkit_exit3 A_splice A_imz A_icpt_str A_icpt_strnlen A_icpt_strnlenJ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tail_lib A_tail_usage_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxADrvKit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxAKnDS.

Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_A_tail_usage_S6 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.LibA.SymDriveA.DcovZ"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_tail_lib.outzone"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_LO"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_HI"; "OF.VF"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.Env"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymDrive.blobs_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.B.A_refused.SHW"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "Stdlib.ZArith.BinInt.Z.lxor"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Nat.sub"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "OF.EnvV"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.AgentSubmission.B.A_tail_lib.AGR"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "OF.FD2"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "OF.TT"; "OF.XL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.sub"; "SUF7"; "OF.TT64"; "Corelib.Init.Datatypes.None"].

#[local] Existing Instance Lib.PropExec.fx0.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition PRE17 : list byte := s2b "usage: "%string.            (* [comment removed for export] *)
Lemma PRE17_len : length PRE17 = 7%nat. Proof. reflexivity. Qed.
Definition SUF7 : list byte := (s2b " INPUT"%string) ++ [Z_to_bv 8 10].   (* [comment removed for export] *)
Lemma SUF7_len : length SUF7 = 7%nat. Proof. reflexivity. Qed.
Lemma msg_cannot_open_eq : forall p, msg_usage p = PRE17 ++ p ++ SUF7.
Proof. intros p. unfold msg_usage, PRE17, SUF7. reflexivity. Qed.

(* [comment removed for export] *)
Lemma stk_agree : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Plo,$2.Phi,$2.P,Pa,$2.P,(3.(4.R3.R1.)(5.R1.R2.))(6.(1.(0.&8.))A1.R5.(7.R2.)A1.R6.(7.R2.))P,(8.$9.R5.R3.R2.)(8.$9.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m m' lo hi AG (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  unfold wview, mrd in *. rewrite (AG a Ha). exact (H a Ha).
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L47745453783.6000007S1w3LEN". (* [comment removed for export] *)
Lemma rw_C8_rdn : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "PMk,P,(0.&40.)(1.(0.&8.))PA,$2.Pw,(0.&40.)P,(:.$9.R3.R2.(;.$<.(=.R1.)(>.$<.)))(6.(1.(?.(0.&8.)))(10.$9.R4.(11.&40.R3.)#8.)(12.(?.(0.&8.))(13.#8.R2.)))")
(* [comment removed for export] *).
Proof.
  intros Mk A w [[WF B] _].
  pose proof (cells_bytes_length [C8 w] WF) as LEN. cbn [cells_size csize Nat.add] in LEN.
  pose proof (bytes_at_rdn asegs Mk A _ 0 8 B ltac:(rewrite LEN; lia)) as RD.
  rewrite Z.add_0_r in RD. unfold wa in RD. rewrite RD. cbn [cells_bytes cbytes]. rewrite ?app_nil_r. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "Pmo,$14.Pacc,(?.(15.(0.&40.)$16.))P,A1.VKI,R2.P,(17.VAL,VCS,R2.)(18.$14.Lmo',$14.(3.(6.(1.$14.)(19.R5.R4.)(12.$14.R1.))(3.A1.VKI,R1.(1:.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "Pmo,$14.Pmo',$14.P,A1.VKI,R2.P,(6.$1;.(1<.R2.)(1<.R3.))P,(6.(?.(15.(0.&40.)(0.&40.)))(1=.R3.)(1=.R4.))P,(6.(?.(0.&40.))(1>.R4.)(1>.R5.))P,(6.(1.(0.&40.))(1?.R5.)(1?.R6.))A1.VKI,R6.")
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
  Hypothesis STKHIlo : (bv_unsigned sp0 + 144 <= STKHI)%Z.
  Hypothesis STKHIhi : (STKHI <= 0x800000000000)%Z.
  Hypothesis STKHI64 : (STKHI mod 64 = 0)%Z.
  Hypothesis SCS : crange CS lo (STKHI - lo).
  (* [comment removed for export] *)
  Hypothesis FCS : crange CS 0x16bc0 64.

  Variables (R : bvmap 5 word) (M : word -> option byte) (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Hypothesis G1 : getr R 1 = Z_to_bv 64 0x0e0aa8.
  Hypothesis G2 : getr R 2 = sp0.
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x63ca90.
  Hypothesis G8 : getr R 8 = Z_to_bv 64 2.
  Hypothesis G11 : getr R 11 = Z_to_bv 64 (bv_unsigned sp0 + 136).     (* [comment removed for export] *)
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
  Hypothesis UFR : stk asegs M (bv_unsigned sp0) (bv_unsigned sp0 + 80).      (* [comment removed for export] *)
  Variables (w8 w16 w24 w32 w40 w48 w56 w64 : word).                             (* [comment removed for export] *)
  Hypothesis FRW : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "(:.$9.VM,(20.(21.&40.Vsp0,)+8.)(;.$<.(=.Vw8,)(;.$<.(=.Vw16,)(;.$<.(=.Vw24,)(;.$<.(=.Vw32,)(;.$<.(=.Vw40,)(;.$<.(=.Vw48,)(;.$<.(=.Vw56,)(;.$<.(=.Vw64,)(>.$<.))))))))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Hypothesis ZSH : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "Ps,$2.P,(3.(4.(20.+7???8000.(22.Vlo,+8.))R1.)(5.R1.(20.+7???8000.(22.VSTKHI,+8.))))(6.(1.(0.&8.))A1.VM,(11.&40.R2.)(12.(0.&8.)(11.&8.=)))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Variables (P : word) (path extra : list byte).      (* [comment removed for export] *)
  Let L : Z := Z.of_nat (length path).
  Let buf : list byte := path ++ Z_to_bv 8 0 :: extra.
  Hypothesis G18 : getr R 18 = Z_to_bv 64 0x0970e0.
  Hypothesis AV0 : rw_cells asegs M (bv_unsigned sp0 + 136) [C8 P].                       (* [comment removed for export] *)
  Hypothesis FRA : rw_cells asegs M (bv_unsigned sp0 + 72) [C8 (Z_to_bv 64 0x0e0aa8)].    (* [comment removed for export] *)
  Hypothesis BY : bytes_at asegs M (bv_unsigned P) buf.
  Hypothesis NZ : ~ In (Z_to_bv 8 0) path.
  Hypothesis WIN8 : ((bv_unsigned P + L) / 8 * 8 + 8 <= bv_unsigned P + Z.of_nat (length buf))%Z.
  Hypothesis Plo : (bv_unsigned sp0 + 128 <= bv_unsigned P)%Z.
  Hypothesis Phi : (bv_unsigned P + Z.of_nat (length buf) <= STKHI)%Z.          (* [comment removed for export] *)
  Hypothesis PL16 : (bv_unsigned P + L + 16 <= STKHI)%Z.                        (* [comment removed for export] *)
  Hypothesis LMAX : (L <= 131071)%Z.                                            (* [comment removed for export] *)
  Hypothesis L62 : (L <= 66)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L30247682266.84L35495549846.8300000f01>S3sp04SPlo2lo5STKHI7STKHIlo1P4path1L3buf3Plo1z2Hz1H2H0S3sp05STKHI1P4path1L3buf". (* [comment removed for export] *)
  Lemma PCS : crange CS (bv_unsigned P - bv_unsigned P mod 64) (STKHI - (bv_unsigned P - bv_unsigned P mod 64)).
  Proof. intros z Hz. apply SCS. pose proof LOhi. pose proof (Z.mod_pos_bound (bv_unsigned P) 64 ltac:(lia)). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SHRD : forall c, CS c -> exists b, bytes_at asegs M (shadow_of AL c) [b].
  Hypothesis CSTOP : forall c, CS c -> (c < 2^47)%Z.

  Let WINLO := (bv_unsigned sp0 - 4096)%Z.

  (* [comment removed for export] *)
  Let D : word -> bool := Dimg [(bv_unsigned sp0 - 4096, bv_unsigned sp0 + 144)%Z; (0x7fffad78, 0x7fffad80)%Z; (SSH_LO sp0, SSH_HI sp0)].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L32276418883.84L57167447340.84L57657395591.8500000N01601gS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H". (* [comment removed for export] *)
  Lemma SSH_facts : (0x7fff8000 <= SSH_LO sp0)%Z /\ (SSH_HI sp0 <= 2^46)%Z /\ (SSH_LO sp0 < SSH_HI sp0)%Z.
  Proof. pose proof (SHW_range sp0 (-64) ltac:(lia) SPal ltac:(lia)). unfold SSH_LO, SSH_HI in *. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30247691664.8600000lS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1z2Hz". (* [comment removed for export] *)
  Lemma WCS : crange CS (bv_unsigned sp0 - 4096) 4096.
  Proof. intros z Hz. apply SCS. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30247691664.8600000lS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1z2Hz". (* [comment removed for export] *)
  Lemma WCS' : crange CS (bv_unsigned sp0 - 4096) (4096 + 144).
  Proof. intros z Hz. apply SCS. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma D_Dseg : forall a : word, segcov asegs (bv_unsigned a) = true -> D a = true.
  Proof. intros a H. unfold D. apply Dimg_Dseg. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L6097392651.8600000PS3sp05STKHI1P4path1L3buf5WINLO1c". (* [comment removed for export] *)
  Lemma shadow_aok : forall c x, CS c -> (x = 0x7fff8000 + c / 8)%Z -> aok_addr AL CS x.
  Proof. intros c x Hc ->. right; left. exists c. split; [exact Hc|]. unfold shadow_of. rewrite ASB. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L11408572375.88L37650509568.88L5268879960.88 L57161095762.88L60694983881.90L61028787006.8800000S01G01g02O03203PS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLO1zS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1z2A1S3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
  Proof.
    intros a H. unfold D in H. eapply (Dimg_DOK_aok AL CS IMG); [|exact H].
    repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
    - intros z Hz. left. apply WCS'. lia.
    - intros z Hz. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply FCS; lia|]. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - intros z Hz. destruct (ssh_app sp0 z ltac:(lia) SPal Hz) as [A1 A2]. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply WCS; lia| exact A2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L15567212646.86L40578935982.86L60924558599.8600000P00n01QS3sp05STKHI1P4path1L3buf5WINLO1HS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_D0 : D (Z_to_bv 64 0) = false.
  Proof. pose proof SSH_facts. pose proof SPlo. unfold D. apply Dimg_D0. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition RRUN := rz_runA asegs D AL CS KI K_halted K_mat D_Dseg asegs_top D_DOK D_D0.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L13601108214.90L4172514697.90 L60924549197.9000000S01Q024S3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1a1b2Ha2Hb1z2HzS3sp04SPlo5STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_frame : forall a b, (bv_unsigned sp0 - 4096 <= a)%Z -> (b <= bv_unsigned sp0 + 144)%Z -> DcovZ D a b.
  Proof. intros a b Ha Hb z Hz. unfold D. apply (Dimg_cov _ (bv_unsigned sp0 - 4096) (bv_unsigned sp0 + 144)); [left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40646207469.9000000nS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1a1b2Ha2Hb1z2Hz". (* [comment removed for export] *)
  Lemma D_img : forall a b, (0x10000 <= a)%Z -> (b <= 0x65f000)%Z -> DcovZ D a b.
  Proof. intros a b Ha Hb z Hz. unfold D. apply Dimg_img. unfold AIMG_LO, AIMG_HI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L32683096429.86L40578927076.86L55842434079.8600000S01101OS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_fsh : DcovZ D 0x7fffad78 0x7fffad80.
  Proof. intros z Hz. unfold D. eapply Dimg_cov; [right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LITS_KND : list (Z * Z) := [(0x10000, 0x65f000)%Z; (0x7fffad78, 0x7fffad80)%Z].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L51855127614.8400000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma HLITS_KND : Forall (fun iv => DcovZ D (fst iv) (snd iv)) LITS_KND.
  Proof. repeat (apply Forall_cons; [cbn [fst snd] |]); [apply D_img; lia | exact D_fsh | apply Forall_nil]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18362884487.88L5599869189.88 00000V01<S3sp05STKHI1P4path1L3buf5WINLO3qhi3HhiS3sp05STKHI1P4path1L3buf5WINLO3qlo3Hlo". (* [comment removed for export] *)
  Lemma D_frameS : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "Pqlo,$2.Pqhi,$2.P,(4.(20.(21.&40.Vsp0,)-1000.)R2.)P,(4.R2.(20.(21.&40.Vsp0,)+90.))(23.VD,R4.R3.)")
(* [comment removed for export] *).
  Proof. intros qlo qhi Hlo Hhi. apply D_frame; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L13440388671.87L15567222060.87L52039345437.8700000S01301SS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLO1HS3sp05STKHI1P4path1L3buf5WINLO1H". (* [comment removed for export] *)
  Lemma D_ssh : DcovZ D (SSH_LO sp0) (SSH_HI sp0).
  Proof. pose proof SSH_facts. intros z Hz. unfold D. eapply Dimg_cov; [right; right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L53694884100.8800001:S3sp02lo5STKHI1P4path1L3buf5WINLO1x2Hr2O24SPlo4LOhi7STKHIlo7STKHI643Plo2O1". (* [comment removed for export] *)
  Lemma D_out_zone : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "Px,(0.&40.)P,(6.$24.A1.VD,R1.$25.)P,(26.Vlo,(21.&40.Vsp0,)R2.)(27.(3.(3.(4.+10000.(21.&40.R3.))(5.(21.&40.R3.)+65?000.))(28.(3.(4.+?:488.(21.&40.R3.))(5.(21.&40.R3.)+?:570.))))(27.(3.(4.+7???:=78.(21.&40.R3.))(5.(21.&40.R3.)+7???:=80.))(27.(3.(4.(29.Vsp0,)(21.&40.R3.))(5.(21.&40.R3.)(2:.Vsp0,)))(3.(4.(21.&40.Vsp0,)(21.&40.R3.))(5.(21.&40.R3.)(20.(21.&40.Vsp0,)+90.))))))")
(* [comment removed for export] *).
  Proof.
    intros x Dx [O1 O2]. unfold D, Dimg in Dx. apply Dof_true in Dx as (iv & Hin & Hr).
    cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; unfold AIMG_LO, AIMG_HI in *; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition V0 : list word := [sp0] ++ junk_vals R ++ [can] ++ [P] ++ repeat (Z_to_bv 64 0) 7.
  Lemma V0_len : length V0 = 42%nat.
  Proof. unfold V0. rewrite !length_app, junk_vals_length. reflexivity. Qed.
  Lemma V0_0 : vals_ev V0 0 = sp0. Proof. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54434947932.8400000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma V0_33 : vals_ev V0 33 = can.
  Proof. unfold V0, vals_ev. change ([sp0] ++ junk_vals R ++ [can] ++ [P] ++ repeat (Z_to_bv 64 0) 7) with (([sp0] ++ junk_vals R) ++ ([can] ++ [P] ++ repeat (Z_to_bv 64 0) 7)).
    rewrite app_nth2; [|rewrite length_app, junk_vals_length; cbn; lia]. rewrite length_app, junk_vals_length. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma V0_junk : forall i, (i < 32)%nat -> vals_ev V0 (1 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold V0, vals_ev. cbn [app length Nat.add].
    change (sp0 :: junk_vals R ++ can :: P :: repeat (Z_to_bv 64 0) 7) with ([sp0] ++ (junk_vals R ++ (can :: P :: repeat (Z_to_bv 64 0) 7))).
    change (S i) with (length [sp0] + i)%nat. rewrite app_nth2_plus. rewrite app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54434947932.8400000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma V0_19 : vals_ev V0 34 = P.   (* [comment removed for export] *)
  Proof. unfold V0, vals_ev. change ([sp0] ++ junk_vals R ++ [can] ++ [P] ++ repeat (Z_to_bv 64 0) 7) with (([sp0] ++ junk_vals R ++ [can]) ++ ([P] ++ repeat (Z_to_bv 64 0) 7)).
    rewrite app_nth2; [|rewrite !length_app, junk_vals_length; cbn; lia]. rewrite !length_app, junk_vals_length. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VF (V : list word) : Prop :=
    (forall n, (n < 42)%nat -> vals_ev V n = vals_ev V0 n) /\ (42 <= length V)%nat.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L25269778915.8400000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma VF0 : VF V0. Proof. split; [intros; reflexivity | rewrite V0_len; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L21188810707.90L9784235213.88 00000i01aS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2P21n2HnS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V3ext2P2". (* [comment removed for export] *)
  Lemma VF_app : forall V ext, VF V -> VF (V ++ ext).
  Proof. intros V ext [P1 P2]. split; [| rewrite length_app; lia]. intros n Hn. rewrite vals_ev_app_l by lia. apply P1. exact Hn. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30227048842.8600000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf0 : forall V, VF V -> vals_ev V 0 = sp0. Proof. intros V [P1 _]. rewrite (P1 0%nat) by lia. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54441433323.8600000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf19 : forall V, VF V -> vals_ev V 34 = P. Proof. intros V [P1 _]. rewrite (P1 34%nat) by lia. apply V0_19. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54441433323.8600000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf33 : forall V, VF V -> vals_ev V 33 = can. Proof. intros V [P1 _]. rewrite (P1 33%nat) by lia. apply V0_33. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L45321507673.87L55760870395.8800000[01@S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO2HiS3sp05STKHI1R1P4path1L3buf5WINLO1i2Hi". (* [comment removed for export] *)
  Lemma regs_okV0 : regs_ok (Env (vals_ev V0) (blobs_ev [])) sr_OF R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_OF all_regs];
      first [ (cbn [edenot]; first [ reflexivity | exact G1 | exact G3 | exact G4 | exact G8 | exact G18 | (cbn [ev]; rewrite V0_0, (alu_add_zlit sp0 136) by (unorm; lia); exact G11) | exact G20 | exact G21 | exact G22 | exact G23
                                   | exact G24 | exact G25 | exact G26 | exact G27 | (cbn [ev]; rewrite V0_0; exact G2) ])
            | (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                 change (edenot (Env (vals_ev V0) (blobs_ev [])) (EVar n)) with (vals_ev V0 n); rewrite (V0_junk (n - 1)) by lia; reflexivity end) ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01C0@L11615743984.98 L13042945941.98 L13484217602.98 L14054083309.102L14499496082.98 L15439463048.98 L17543312104.100L1756166345.98  L18928696722.98 L21294246587.98 L21683230006.98 L2183569985.98  L21927717721.98 L21986899558.98 L22163189566.98 L22604873481.98 L2431328725.102 L24992216082.98 L25271909867.98 L25484198400.98 L2564951689.98  L27134698386.98 L27315410273.98 L27352604565.98 L28325820091.98 L28434372873.98 L29762371858.98 L31327315070.102L31396711570.98 L32648418366.104L32873232769.102L33148392579.98 L33669037980.98 L34577004134.98 L34774111081.98 L3506990866.98  L38114121216.98 L3829630897.102 L39213365269.98 L39510883410.98 L40253358217.98 L40579027602.98 L43030311433.98 L44353219849.98 L44510486418.98 L44751598473.98 L4504975677.102 L46809767186.98 L48461698953.98 L48555263348.98 L5004984661.98  L51238950418.98 L52457697417.98 L52875384210.98 L53129770761.98 L53519161933.102L53519190958.98 L54226205864.98 L54292390718.98 L54967497737.98 L55007380242.98 L55149030888.100L55662616861.102L55849630025.98 L5641132690.98  L57481666438.98 L58560891017.98 L58961367305.98 L5926593349.98  L61064399881.98 L62675677899.98 L6275277449.98  L64037435666.98 L64202541330.98 L64791502857.98 L65502196882.98 L65732472201.98 L66336703634.98 L67631326282.102L68058909735.98 L68075363561.98 L7781517330.98  L9911486354.98  00000100o01M02P02n03L03o04M04k05N05l06J06h07K07n08L08n09L09j0:M0:k0;I0;l0<O0=20=P0=n0>i0?G0@G0@l0@m0AK0Ai0BG0Be0CH0Cn0Co0DM0Dk0EI0Eg0FE0Fc0GA0Ge0HC0Ha0Hb0IJ0Ih0JF0Jd0KB0Kb0L@0LA0Ld0MB0M`0NC0OA0O_0P=0P[0Q90QW0R50RS0RT0S20SP0Sn0TL0Tj0UH0Uf0VK0Vi0WG0We0XCFS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1HS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1H1d1m2Hd2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1n1BS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H3off1n1B1CS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1d1m2Hd2Hm1x2HxS3sp05STKHI1P4path1L3buf5WINLO1d1m2HdFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO3off1n1CFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO3off1AS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOFS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1mS3sp05STKHI1P4path1L3buf5WINLOFS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1d1m2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1d1m2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
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
      | (* [comment removed for export] *) split; [lia|]; split; [apply flat_intro; cbn [edenot ev]; rewrite ?V0_0; lia|];
        unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite ?V0_0, ?V0_19; rewrite ?alu_add_zlit by (unorm; lia);
        first [exact (rw_C8_rdn _ _ _ AV0) | exact (rw_C8_rdn _ _ _ FRA)]
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L17034448047.91L29784460291.90L3479498253.90 L43935895424.92L47803405696.92L55715225071.90L59576963504.92L63368316460.92L63368316589.91L63368325619.90L64266648997.90L66561261592.92L8929201831.93 00000l01J02H02n03T04204R05205R06006f07F08ES3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1k2HkS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1k2H12H2S3sp05STKHI1P4path1L3buf5WINLO1k2H12H2S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1kS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2Hk2H12H22H3". (* [comment removed for export] *)
  Lemma shw_denotV : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "PV,(?.(0.&40.))Pk,$2.P,(2;.R2.)P,(3.(4.-1000.R2.)(4.R2.=))(6.$2.(21.&40.(2<.(2=.(2>.R4.)(2?.(>.(?.(0.&8.)))))(30.$31.(30.$32.(30.$33.(30.$32.(34.#0.)(35.R3.))(35.+3.))(35.+7???8000.))(35.-8.))))(36.Vsp0,R3.))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L3479498253.88 L35907637249.89L40825277235.88L53519168529.89L55715225071.88L64266638075.89L64266648997.8800000n01Q01o02O02m03c04YS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1k2H1S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2HkS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2Hk". (* [comment removed for export] *)
  Lemma and3_lit : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "Pk,$2.P,(3.(4.-1000.R1.)(4.R1.=))(6.$24.(37.&40.(38.$31.(11.&40.(20.(21.&40.Vsp0,)R2.))(11.&40.+3.))(11.&40.=))(39.(3:.R2.+4.)=))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo. pose proof SPhi.
    intros k Hk. rewrite alu_and. unfold v_and. rewrite (unsigned_lit 3), (unsigned_lit (bv_unsigned sp0 + k)) by lia.
    rewrite land3_mod4 by lia. pose proof (Z.mod_pos_bound (bv_unsigned sp0 + k) 4 ltac:(lia)).
    unfold bv_eqb. rewrite !unsigned_lit by lia. apply (mod4_of_sp (bv_unsigned sp0) k); [exact SPal | lia | reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L37106200957.88L5744834796.88 L61929758668.88L8443611008.88 00000]01@01c02FS3sp04SPlo5STKHI1P4path1L3buf5WINLO1x1n2Hx2HnS3sp05STKHI1P4path1L3buf5WINLO1x2HxS3sp05STKHI1P4path1L3buf5WINLO1n2HnS3sp05STKHI1P4path1L3buf5WINLO1x2Hx". (* [comment removed for export] *)
  Lemma not_ltu_small : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "Px,$2.Pn,$2.P,(3.(4.=R2.)(5.R2.(3;.+2.+30.)))P,(3.(4.=R2.)(5.R2.(3;.+2.+10.)))(6.$24.(3<.&40.(11.&40.(3=.(21.&40.(11.&40.R4.))(21.&40.(11.&40.-1.))))(11.&40.R3.))$3>.)")
(* [comment removed for export] *).
  Proof.
    intros x n Hx Hn. rewrite (unsigned_lit x) by lia. replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z by reflexivity.
    rewrite zb_lxor_ones by lia. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma alu_add_zlit : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "Px,(0.&40.)Pk,$2.P,(3.(4.=(20.(21.&40.R2.)R1.))(5.(20.(21.&40.R2.)R1.)(3;.+2.+40.)))(6.(0.&40.)(38.$32.R3.(11.&40.R2.))(11.&40.(20.(21.&40.R3.)R2.)))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L21188810707.8800000US3sp05STKHI1P4path1L3buf5WINLO1V1n2Hn". (* [comment removed for export] *)
  Lemma vals_ev_app_ge : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "PV,(?.(0.&40.))Pext,(?.(0.&40.))Pn,$16.P,(3?.(40.(0.&40.)R3.)R1.)(6.(0.&40.)(2>.(41.(0.&40.)R4.R3.)R2.)(2>.R3.(42.R2.(40.(0.&40.)R4.))))")
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L17743517653.105L18614817987.105L2008272931.114 L24498169710.105L27076589246.107L29443216221.105L29731801447.107L30247691664.107L37492600210.114L42153134065.105L46058870405.105L46530783016.105L56457790905.105L56765667309.107L58965540039.102L65604097635.105L8120965920.107 L8564305960.105 00000[01`02a03_05805d06m08608d09P0:70:`0;e0<d0=B0>90?80?oS3sp02lo5STKHI1P4path5extra1L3buf3Plo5WINLOS3sp04SPlo2lo4LOlo6LOdeep5STKHI7STKHIhi1P4path1L3buf3Plo5WINLO1H1s2HsS3sp04SPlo2lo6LOdeep5STKHI1P4path5extra1L3buf3Plo5WINLO1H1c2Q02H3S3sp04SPlo2lo4LOlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1s2HsS3sp04SPlo2lo4LOlo4LOhi5STKHI7STKHIlo7STKHI641P4path5extra1L3buf3Plo4PL165WINLO1H2H11s2HsS3sp02lo4LOlo5STKHI1P4path5extra1L3buf5WINLOS3sp04SPlo2lo6LOdeep5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1H2H21a2HaS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path5extra1L3buf3Plo4PL165WINLO1H1z2HzS3sp04SPlo5STKHI1P4path5extra1L3buf5WINLO1c2Q0S3sp02lo4LOlo5STKHI1P4path5extra1L3buf5WINLOS3sp05STKHI1P4path5extra1L3buf5WINLO2H1S3sp04SPhi5STKHI1P4path5extra1L3buf5WINLOS3sp04SPlo2lo4LOlo6LOdeep5STKHI7STKHIhi1P4path1L3buf3Plo5WINLO1H1s2HsS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1H2H21a2HaS3sp05STKHI1P4path5extra5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1HS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1H2H21a2HaS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1H". (* [comment removed for export] *)
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
  Definition TT : TSet := t_emit (W 2 (msg_usage path)) (t_exit (exit_code 2) (m_fs model)).
  Definition FD2 (mo : Model) : Prop := fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Definition STG (V : list word) (nx : nat) (sr : list expr) (kn : list kentry) (pc : Z) (X : list word -> mem -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "PRk,(43.&5.(0.&40.))PMk,P,(0.&40.)(1.(0.&8.))Pmok,$14.P,(2;.O6.)P,(6.$16.(40.(0.&40.)O6.)O5.)P,(44.(45.O6.)O4.R5.)P,(46.$9.(45.O6.)R5.O3.)P,(47.VM,Vlo,(21.&40.Vsp0,)R6.)P,A1.VKI,R6.P,(6.$48.(49.R7.)(49.Vmodel,))P,(4:.R8.)P,A2.O1.O6.R:.(4;.$9.(4<.(4=.$4>.R<.(11.&40.O2.)R;.(4?.$9.))R:.)$50.)")
(* [comment removed for export] *).
  Definition XL (V : list word) : Prop := vals_ev V 150 = Z_to_bv 64 L.
  Definition X0 (V : list word) (Mk : mem) : Prop := True.
  Definition XC (V : list word) (Mk : mem) : Prop := XL V.
  Definition XD (V : list word) (Mk : mem) : Prop := XL V /\ bytes_at asegs Mk (bv_unsigned sp0 - 457) path.
  Definition XE (V : list word) (Mk : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "(3.(51.O2.)(3.(52.$9.O1.(53.(21.&40.Vsp0,)+1<9.)Vpath,)(52.$9.O1.(20.(53.(21.&40.Vsp0,)+1<9.)VL,)$54.)))")
(* [comment removed for export] *).
  Definition S_A2 : Prop := forall V, STG V 74 srA2 knA2 0x5b1b4 X0.
  Definition S_B1 : Prop := forall V, STG V 106 srB1 knB1 0x5b504 X0.
  Definition S_B2 : Prop := forall V, STG V 138 srB2 knB2 0x5b1b4 X0.
  Definition S_C1 : Prop := forall V, STG V 172 srC1 knC1 0x0e79c4 XC.
  Definition S_D : Prop := forall V, STG V 205 srD knD 0x0e6f40 XD.
  Definition S_E : Prop := forall V, STG V 237 srE knE 0x0e6f40 XE.
  (* [comment removed for export] *)
  Definition TT64 : TSet := t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model)).
  Definition STG64 (V : list word) (nx : nat) (sr : list expr) (kn : list kentry) (pc : Z) (X : list word -> mem -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "PRk,(43.&5.(0.&40.))PMk,P,(0.&40.)(1.(0.&8.))Pmok,$14.P,(2;.O6.)P,(6.$16.(40.(0.&40.)O6.)O5.)P,(44.(45.O6.)O4.R5.)P,(46.$9.(45.O6.)R5.O3.)P,(47.VM,Vlo,(21.&40.Vsp0,)R6.)P,A1.VKI,R6.P,(6.$48.(49.R7.)(49.Vmodel,))P,(4:.R8.)P,A2.O1.O6.R:.(4;.$9.(4<.(4=.$4>.R<.(11.&40.O2.)R;.(4?.$9.))R:.)$55.)")
(* [comment removed for export] *).
  Definition S_D64 : Prop := forall V, STG64 V 205 (sc_sr resC2X) (sc_kn resC2X) (sc_ret resC2X) XC.
  (* [comment removed for export] *)

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

  Hypothesis NEXT : S_E.

  (* [comment removed for export] *)
  Lemma nl_img : rdn asegs (fun _ => None) (Z_to_bv 64 0x16bd1) 7%nat = Some SUF7.
  Proof. vm_compute. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L43670765215.87L50837337284.87L5186248952.89 L5473887539.89 00000N00l01O022S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp05STKHI1P4path1L3buf5WINLO1i2Hi". (* [comment removed for export] *)
  Lemma nl_bytes_at : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S6 ()) "PMk,Px,(0.&40.)(1.(0.&8.))P,Pa,$2.P,(3.(4.+10000.R1.)(5.R1.+?1000.))(6.(1.(0.&8.))A1.R3.(11.&40.R2.)(56.(0.&8.)))(52.$9.R2.+16;=1.$54.)")
(* [comment removed for export] *).
  Proof.
    intros Mk RO. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    unfold mrd, wa. rewrite (RO (0x16bd1 + Z.of_nat i)) by lia.
    do 7 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01c0@L10522145838.116L10769333283.126L10825310353.144L1102062031.144 L11093386449.116L12162701095.126L12352482293.116L12381576378.116L13888154583.141L14309645649.116L14334882987.165L14564977834.116L14949938610.126L15047244086.116L16109195408.141L16252466602.116L16735959893.144L18014153940.116L18381454536.126L18452601618.1  L18883718650.144L19168251272.146L19458343858.126L20632353634.144L21539612081.140L22071780554.116L22494550619.126L23019306992.103L24623709742.162L24625795186.162L24984672390.116L25069796662.165L25325349558.116L26284087056.144L26507518861.144L26725352500.126L27076589246.146L27352116571.126L27816511892.126L29443215018.2  L29445890821.141L29731801447.141L30247691664.146L30426774554.144L31003767474.126L32012096746.126L32032333883.3  L33178294566.116L33355456082.116L33748443578.116L3377943716.140 L3420509078.116 L34634427059.103L35117101588.144L35223706973.144L357715257.144  L3586481814.116 L36714795227.126L36782180292.116L37622523289.167L38557618280.126L38950490845.116L39015870258.126L39055317628.126L39835184468.116L39960338522.144L40044123314.126L41531727740.126L41676065725.144L42150874946.157L42333743922.167L42720804476.126L43658395449.144L43971931716.146L44492042876.126L46533078311.2  L46965831548.126L47015191917.141L47021567849.144L48023884600.116L49492805814.116L49938019708.126L50615126198.116L50774715085.116L50961132635.126L52135528630.116L52331461418.116L52341781785.144L52416194011.126L52726078230.116L5305592157.144 L53519159512.126L53756951209.144L54439436909.157L55069172786.126L55810752186.116L56765667309.141L58638672156.144L58695151760.165L59179232279.144L59281996761.144L5963170837.144 L60669077807.165L60679793201.144L60820242395.126L61014438335.116L61345436741.144L62712594841.140L63258512436.140L63606425980.126L64111889970.126L64830566235.126L65211166553.116L7276823820.116 L8120965920.141 00000h01P02^03J03m04j05R06?06f07I08508608^09A0:A0:d0;e0<L0=10=60>70?H0@00@\0A?0Ag0BO0CL0DE0E\0F?0GC0H@0I40I`0JC0K]0LE0MF0MO0NH0OO0Pj0Q^0RF0Ri0S60T30U00Um0VP0W80W`0Xn0Y_0ZK0[70[_0\W0^10_;0_^0`F0a30ak0b\0cD0d10d]0eQ0fE0g20g^0ho0i\0ie0jR0kJ0lK0lL0lo0m\0nY0oQ10910\11?11k12S12T13E13h14\15H16016m17U18Y19e1:Q1;G1<U1=K1>A1>i1?Q1@E1A01AS1B@1Bh1CP1D81D`1EHS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LV3Hlo3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo1z2HzS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf3L625WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5FS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo3ds54LEN5S3sp05STKHI1P4path1L3buf3L625WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1zS3sp0S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo3ds54LEN5S3sp04SPlo2lo5STKHI7STKHIlo7STKHI641P4path1L3buf3Plo5WINLO1V2LV3Hlo3ds54LEN51s2HsS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN51x1l2l02HxS3sp04SPlo2lo5STKHI7STKHIlo7STKHI641P4path1L3buf3Plo5WINLO1V2LV3Hlo3ds54LEN51H1x2Hx1g1lS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo2lo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo3ds54LEN5S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp02lo4LOlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPal2lo5STKHI7STKHIlo7STKHI641P4path1L3buf3Plo3L625WINLO1V2LV3Hlo3ds54LEN51s2HsS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L625WINLO1V2LV3Hlo1z2HzS2lo4LOloS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LVS3sp04SPlo2lo6LOdeep5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo1a2HaS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo4PL165WINLO1V2LV3Hlo3ds54LEN51z2Hz7STKHI64S3sp02lo4LOhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp02lo4LOhiS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LV3Hlo3ds54LEN5S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPlo5STKHI1P4path1L3buf3L625WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp04SPlo2lo4LOhi5STKHI7STKHIlo7STKHI641P4path1L3buf3Plo3L625WINLO1V2LV3Hlo3ds54LEN51x2HxS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LV3Hlo1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp02lo4LOlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN51x2HxS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN51z2Hz4SPlo2lo7STKHIlo7STKHI643Plo3HloS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp03XAGS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo3ds54LEN5FS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzFS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp02lo4LOlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV1a2HaS3sp04SPlo2lo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo3ds54LEN5S3sp04SPlo2lo5STKHI7STKHIlo7STKHI641P4path1L3buf3Plo5WINLO1V2LV3Hlo3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp02lo6LOdeep5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LV3Hlo3ds54LEN5S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp02lo4LOhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp02lo4LOlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1a2Ha". (* [comment removed for export] *)
  Theorem stage_D : S_D.
  Proof.
    intros V Rk Mk mok VFV LV HR HK AGk HKk FS FD XD1.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SSH_facts as SSF. pose proof (u64_range P) as PR.
    unfold EnvV in HR, HK. destruct XD1 as [XL1 BYP1]. unfold XL in XL1. rename XL1 into EV150.
    assert (Lsmall : (bv_unsigned (edenot {| ev := vals_ev V; eb := blobs_ev [] |} (EVar 150)) < 2 ^ 31)%Z).
    { cbn [edenot ev]. rewrite EV150, u_small by lia. lia. }
    destruct (facts Mk AGk) as [MIk MPk STk BUFk SHRDk RIPk SNk AMk ZSTRk ZSTKk OBJk].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok (Env (vals_ev ?Vx) ?bb) _ _ =>
      pose proof (kn_inD_residualS D (Env (vals_ev Vx) bb) sp0 (-4096) 144 LITS_KND ltac:(cbn [ev]; apply vf0; assumption) D_frameS HLITS_KND) as KND end.
    time (run_blockA3S RRUN KND FUEL_OF STOPS_OF scrD 205%nat true covtac).
    all: try solve_sc.
    all: try (lazymatch goal with |- srealizesJ _ _ _ => fail | _ => cbn [sc_denot branch_taken]; awn Lsmall; cmpL end).
    all: match goal with |- srealizesJ _ _ _ => idtac | |- ?g => idtac "D-SC-LEFT" g end.
    rename EQM into EQM1. rename OUT into OUT1. rename R0 into R1. rename M0 into M1. rename mo into mo1. rename HKmo into HK1. rename MM into MM1.
    assert (AG1 : AGR M lo (bv_unsigned sp0) M1) by (block_AG AGk EQM1 OUT1).
    (* [comment removed for export] *)
    assert (BYP1' : bytes_at asegs M1 (bv_unsigned sp0 - 457) path).
    { eapply (bytes_at_block D _ Mk M1 _ _ _ BYP1 EQM1). intros z Hz. split.
      - apply (D_frame z (z + 1)); rewrite <- ?HLz; unfold L in *; lia.
      - cbn [log_out]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
        rewrite ?(u_small 0) by lia. repeat split; rewrite ?u_small by lia; first [unfold L in *; lia | exact I]. }
    clear AGk EQM1 OUT1. rename AG1 into AGk.
    (* [comment removed for export] *)
    pose proof HR as HR0. to_tree HR.
    destruct (facts M1 AGk) as [MI1 MP1 ST1 BUF1 SHRD1 RIP1 SN1 AM1 ZSTR1 ZSTK1 OBJ1].
    assert (HL : L = Z.of_nat (length path)) by reflexivity.
    pose proof TM as TM'. destruct TM' as [_ RO _ _ _ ZI _ _ _ _ _ _ _ _ _ _ _ _ _].
    assert (NL1 : bytes_at asegs M1 0x16bd1 SUF7).
    { apply nl_bytes_at. intros a Ha. eapply (AGR_byte M lo (bv_unsigned sp0) M1 a); [exact AGk | lia | lia | lia | apply RO; exact Ha]. }
    assert (ZF1 : M1 (Z_to_bv 64 0x7fffad7a) = Some (Z_to_bv 8 0)).
    { eapply (AGR_byte M lo (bv_unsigned sp0) M1); [exact AGk | lia | lia | lia | apply ZI; unfold ZIMG_LO, ZIMG_HI; lia]. }
    destruct (u8arr_of_mapped M1 (bv_unsigned sp0 - 457 + L) 7
                ltac:(eapply mapped_sub; [exact MP1 | lia | cbn; lia]) ltac:(lia) ltac:(cbn; lia)) as (ds5 & LEN5 & ARR5).
    time (eapply (splice_evtA2 AL CS KI K_halted K_mat V (blobs_ev []) _ _ _ M1 mo1 KEPT_CR (-1088) (-457) 73 lo
              (fun R' M' => bytes_at asegs M' (bv_unsigned sp0 - 457) path /\ bytes_at asegs M' (bv_unsigned sp0 - 457 + L) SUF7 /\ mem_inv asegs M')
              0x67db8 0x0e6f40);
      [ exact HR | exact HK | exact HK1
      | rewrite LV; vm_compute; reflexivity | rewrite LV; vm_compute; reflexivity | cbn; intuition discriminate
      | rewrite (vf0 V VFV); unfold AIMG_HI; lia | rewrite (vf0 V VFV); lia | lia | lia | lia | rewrite (vf0 V VFV); lia | rewrite (vf0 V VFV); lia
      | | ]).
    { (* [comment removed for export] *)
      regvV HR0 (1%bv : reg). regvV HR0 (2%bv : reg). regvV HR0 (10%bv : reg). regvV HR0 (11%bv : reg). regvV HR0 (12%bv : reg).
      eapply (evtA_cut asegs AL CS); [apply (jstep_walk_memcpy AL IMG ALWF); exact CSOK|].
      cbn beta. intros ms1 ->.
      eapply evtA_mono.
      - time (eapply (imemcpy_spec AL IMG ALWF CS CSOK ASB) with (DST := bv_unsigned sp0 - 457 + L) (SRC := 0x16bd1) (n := 7) (lo := lo) (ds := ds5) (ss := SUF7);
          rewrite ?(unsigned_lit (bv_unsigned sp0 + -1088)) by lia;
          first [ exact ARR5 | exact NL1 | exact SHRD1 | exact AM1 | exact MI1
                | lazymatch goal with |- aobj _ _ _ _ 0x16bd1 _ =>
                    apply (aobj_of_zero_range AL CS M1 _ _ CSOK ASB); [intros z Hz; apply FCS; lia | lia | lia | intros s Hs; replace s with 0x7fffad7a by lia; exact ZF1] end
                | lazymatch goal with |- aobj _ _ _ _ _ _ => apply (aobj_of_zero_range AL CS M1 _ _ CSOK ASB); [intros z Hz; apply SCS; lia | lia | lia | intros s Hs; apply ZSTK1; unfold SSH_LO, SSH_HI; lia] end
                | lazymatch goal with |- app_range 0x16bd1 _ => unfold app_range; left; lia end
                | lazymatch goal with |- app_range _ _ => unfold app_range; right; lia end
                | lazymatch goal with |- amem_apart _ _ => unfold amem_apart; lia end
                | lazymatch goal with |- (1 <= _)%Z -> crange CS (0x16bd1 - _) _ /\ _ => intros _; split; intros z Hz; apply FCS; lia end
                | lazymatch goal with |- (1 <= _)%Z -> _ /\ _ => intros _; split; intros z Hz; apply SCS; lia end
                | lazymatch goal with |- crange CS lo _ => intros z Hz; apply SCS; lia end
                | lazymatch goal with |- stk _ _ lo ?hi => apply (proj1 (stk_split asegs M1 lo hi (bv_unsigned sp0) ST1 ltac:(lia))) end
                | lazymatch goal with |- @eq word (Z_to_bv 64 _) (Z_to_bv 64 _) => f_equal; lia end
                | lazymatch goal with |- @eq word (alu64 _ _ _) _ => rewrite (alu_add_zlit sp0) by lia; rewrite alu_add_zlit by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia; f_equal; lia end
                | lazymatch goal with |- @eq nat _ _ => exact LEN5 end
                | lazymatch goal with |- _ \/ _ => lia end
                | lazymatch goal with |- Z.of_nat _ = _ => first [rewrite LEN5; reflexivity | reflexivity] end
                | lia
                | match goal with |- ?g => idtac "IMC5-LEFT:" g end ]).
      - cbn beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ARR' & SRC' & ST').
        eexists _, m'. split; [rewrite ret_pc_even by (first [lia | reflexivity]); reflexivity|].
        split; [intros r Hr; cbn [In KEPT_CR] in Hr; repeat (destruct Hr as [<-|Hr]; [reflexivity|]); destruct Hr|].
        rewrite ?(unsigned_lit (bv_unsigned sp0 + -1088)) in MU by lia. rewrite ?(vf0 V VFV).
        split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [Frame.outside]; intros x Hx; repeat split; try exact I; lia|].
        split; [exact WM|]. split; [| split; [exact (proj1 ARR') | exact MI']].
        eapply bytes_at_transport; [exact BYP1' | exact MU | cbn [disjoint_from fst snd]; lia]. }
    (* [comment removed for export] *)
    intros R3 M3 mo3 (BYP3 & NL3 & MI3) MU3 WM3 HR3 HK3 HKmo3 MM3.
    rewrite LV in HR3.
    pose proof (VF_app V (junk_vals R3) VFV) as VF3.
    apply (NEXT (V ++ junk_vals R3) R3 M3 mo3 VF3).
    - rewrite length_app, junk_vals_length, LV. reflexivity.
    - exact HR3.
    - exact HK3.
    - eapply (AGR_munch _ M lo (bv_unsigned sp0) M1 M3); [exact AGk | exact MU3 | exact WM3 | | unfold AIMG_HI; lia].
      cbn [Frame.outside]. rewrite !(vf0 V VFV). pose proof LOhi. intros x Hx.
      destruct (Z_le_gt_dec lo x); destruct (Z_lt_le_dec x (bv_unsigned sp0)); try lia; exfalso; apply Hx; repeat split; lia.
    - exact HKmo3.
    - rewrite (mo_mat_fs _ _ MM3), (mo_mat_fs _ _ MM1). exact FS.
    - unfold FD2 in *. rewrite (mo_mat_fds' _ _ MM3), (mo_mat_fds' _ _ MM1). exact FD.
    - (* [comment removed for export] *) split; [| split; [exact BYP3 | exact NL3]].
      unfold XL. rewrite vals_ev_app_l by (rewrite LV; lia). exact EV150.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End OF.
