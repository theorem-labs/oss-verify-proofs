(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA Restrict RestrictLib NodesA SymDriveA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg ARestrict A_exit_base A_stdio_defs A_stdio_write A_stdio_call A_code_96000_97000 A_code_e3000_e4000 A_code_e6000_e7000 A_code_e7000_e8000            A_rip.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import SymDriveAX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_printf1_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxAKnD.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_A_printf1 () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.env"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "Corelib.Lists.ListDef.nth"; "all_regs"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.s_pc"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sym_state"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sidecond"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.scripts"; "RocqVerifyHarness.AgentSubmission.B.A_printf1_defs.rA"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.B.A_printf1_defs.rB"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_call.stdio_res"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_call.stdio_call"; "RocqVerifyHarness.AgentSubmission.B.A_printf1_defs.srB"; "RocqVerifyHarness.AgentSubmission.B.A_printf1_defs.knB"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.B.A_printf1_defs.resC"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_call.sc_ret"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_call.sc_f"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_call.sc_fd"; "RocqVerifyHarness.AgentSubmission.B.A_printf1_defs.rC"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sentry"; "RocqVerifyHarness.AgentSubmission.LibA.Restrict.restrict"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.mem_denot"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BB.StoreOk.mem_grows"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.SymDriveA.DcovZ"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.estart"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.lor"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "Stdlib.ZArith.BinInt.Z.lxor"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "p1_postA"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.zero_lines"].

#[local] Existing Instance Lib.PropExec.fx0.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition all_regs : list reg := ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "(0.(1.&5.)(2.&5.=$3.)(0.(1.&5.)(2.&5.+1.$3.)(0.(1.&5.)(2.&5.+2.$3.)(0.(1.&5.)(2.&5.+3.$3.)(0.(1.&5.)(2.&5.+4.$3.)(0.(1.&5.)(2.&5.+5.$3.)(0.(1.&5.)(2.&5.+6.$3.)(0.(1.&5.)(2.&5.+7.$3.)(0.(1.&5.)(2.&5.+8.$3.)(0.(1.&5.)(2.&5.+9.$3.)(0.(1.&5.)(2.&5.+:.$3.)(0.(1.&5.)(2.&5.+;.$3.)(0.(1.&5.)(2.&5.+<.$3.)(0.(1.&5.)(2.&5.+=.$3.)(0.(1.&5.)(2.&5.+>.$3.)(0.(1.&5.)(2.&5.+?.$3.)(0.(1.&5.)(2.&5.+10.$3.)(0.(1.&5.)(2.&5.+11.$3.)(0.(1.&5.)(2.&5.+12.$3.)(0.(1.&5.)(2.&5.+13.$3.)(0.(1.&5.)(2.&5.+14.$3.)(0.(1.&5.)(2.&5.+15.$3.)(0.(1.&5.)(2.&5.+16.$3.)(0.(1.&5.)(2.&5.+17.$3.)(0.(1.&5.)(2.&5.+18.$3.)(0.(1.&5.)(2.&5.+19.$3.)(0.(1.&5.)(2.&5.+1:.$3.)(0.(1.&5.)(2.&5.+1;.$3.)(0.(1.&5.)(2.&5.+1<.$3.)(0.(1.&5.)(2.&5.+1=.$3.)(0.(1.&5.)(2.&5.+1>.$3.)(0.(1.&5.)(2.&5.+1?.$3.)(4.(1.&5.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L1649687558.2000006S1n2Hn". (* [comment removed for export] *)
Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L8912114872.6000007S1r3Hr0". (* [comment removed for export] *)
Lemma regs_ok_by_index : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "PE,$5.Psr,(6.$7.)PR,(8.&5.(1.&40.))P,Pi,$9.P,(:.R1.#20.)(;.(1.&40.)(<.R3.(=.(1.&5.)R2.$>.(2.&5.=$3.)))(?.R5.(=.$7.R2.R4.(10.=))))(11.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma itinerary_p1 : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "(12.(;.(13.$14.$9.)(15.$14.$9.(16.(17.$18.(6.$19.)(17.(13.$18.(6.$19.))$1:.$1;.)))(1<.$19.(1=.$18.(6.$19.)(17.(13.$18.(6.$19.))$1:.$1;.))))(15.$14.$9.+>7118.#:9.))(12.(;.(13.$14.(6.$19.))(15.$14.(6.$19.)(16.(17.$18.(6.$19.)(17.(13.$18.(6.$19.))$1:.$1>.)))(1=.$18.(6.$19.)(17.(13.$18.(6.$19.))$1:.$1>.)))(15.$14.(6.$19.)+>66;8.(4.$19.)))(12.(;.(1?.$20.)(21.#22.$22.$23.)(24.$20.$25.))(12.(;.(13.(13.$14.$14.)$14.)(15.(13.$14.$14.)$14.(15.$14.$14.(26.$25.)(27.$25.))(28.$25.))(15.(13.$14.$14.)$14.(15.$14.$14.+>713<.+?:578.)+1.))(;.(13.$14.(6.$19.))(15.$14.(6.$19.)(16.(17.$18.(6.$19.)(17.(13.$18.(6.$19.))$1:.$29.)))(1=.$18.(6.$19.)(17.(13.$18.(6.$19.))$1:.$29.)))(15.$14.(6.$19.)+9748<.(4.$19.)))))))")
(* [comment removed for export] *).
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Record stdout_bufferedA (M : word -> option byte) (wpos : Z) : Prop := SOBA {
  sob_flags : rdn RSEGS M (Z_to_bv 64 0x0fa578) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  sob_rpos  : rdn RSEGS M (Z_to_bv 64 (0x0fa578 + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  sob_rend  : rdn RSEGS M (Z_to_bv 64 (0x0fa578 + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  sob_wend  : rdn RSEGS M (Z_to_bv 64 (0x0fa578 + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65d5a0));
  sob_wpos  : rdn RSEGS M (Z_to_bv 64 (0x0fa578 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wpos));
  sob_wbase : rdn RSEGS M (Z_to_bv 64 (0x0fa578 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65d1a0));
  sob_write : rdn RSEGS M (Z_to_bv 64 (0x0fa578 + 72)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0e66b8));
  sob_buf   : rdn RSEGS M (Z_to_bv 64 (0x0fa578 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65d1a0));
  sob_bsz   : rdn RSEGS M (Z_to_bv 64 (0x0fa578 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  sob_fd    : rdn RSEGS M (Z_to_bv 64 (0x0fa578 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sob_lock  : rdn RSEGS M (Z_to_bv 64 (0x0fa578 + 140)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sob_lbf   : rdn RSEGS M (Z_to_bv 64 (0x0fa578 + 144)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
}.

(* [comment removed for export] *)
Record pf_mem (sp0 : word) (M : word -> option byte) (can : word) : Prop := PF_MEM {
  pf_win : forall a : word, (bv_unsigned sp0 - 4096 <= bv_unsigned a < bv_unsigned sp0)%Z -> wview RSEGS M a <> None;
  pf_ro  : forall a : Z, (0x10000 <= a < 0x0f1000)%Z -> M (Z_to_bv 64 a) = None;
  pf_file : forall a : Z, (0x0fa488 <= a < 0x0fa780)%Z -> M (Z_to_bv 64 a) = None;
  pf_inited : rdn RSEGS M (Z_to_bv 64 0x10a6d8) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1));
  pf_ric    : rdn RSEGS M (Z_to_bv 64 0x10a6d9) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1));
  pf_gric   : rdn RSEGS M (Z_to_bv 64 0x0f69b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a6d9));
  pf_cf     : rdn RSEGS M (Z_to_bv 64 0x0f5e40) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x19b528));
  pf_chk    : rdn RSEGS M (Z_to_bv 64 0x19b57c) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1));
  pf_got    : rdn RSEGS M (Z_to_bv 64 0x0f5e50) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1099f8));
  pf_sb     : rdn RSEGS M (Z_to_bv 64 0x1099f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000));
  pf_rvp    : rdn RSEGS M (Z_to_bv 64 0x0f7bc0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0ea30c));
  pf_rvfp   : rdn RSEGS M (Z_to_bv 64 0x0f7bc8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0e71fc));
  pf_rmc    : rdn RSEGS M (Z_to_bv 64 0x0f7cc8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0ea9c0));
  pf_rms    : rdn RSEGS M (Z_to_bv 64 0x0f7cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0eadc4));
  pf_shf    : rdn RSEGS M (Z_to_bv 64 0x7fffaad8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  pf_shb    : rdn RSEGS M (Z_to_bv 64 0x800c3a30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  pf_shs    : rdn RSEGS M (Z_to_bv 64 ((bv_unsigned sp0 - 912) / 8 + 0x7fff8000 - ((bv_unsigned sp0 - 912) / 8 + 0x7fff8000) mod 8)) 8
                = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  pf_g88    : rdn RSEGS M (Z_to_bv 64 0x0f5e58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a6e8));
  pf_g90    : rdn RSEGS M (Z_to_bv 64 0x0f5e60) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a6f0));
  pf_g98    : rdn RSEGS M (Z_to_bv 64 0x0f5e68) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a6e0));
  pf_kmb    : rdn RSEGS M (Z_to_bv 64 0x10a6e8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  pf_kme    : rdn RSEGS M (Z_to_bv 64 0x10a6f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  pf_khe    : rdn RSEGS M (Z_to_bv 64 0x10a6e0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff));
  pf_cgot   : rdn RSEGS M (Z_to_bv 64 0x0f6ae0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65cad0));
  pf_can    : rdn RSEGS M (Z_to_bv 64 0x65cad0) 8 = Some (word_to_le_bytes 8 can);
  pf_buf    : forall a : word, (0x65d1a0 <= bv_unsigned a < 0x65d1a0 + 1032)%Z -> wview RSEGS M a <> None
}.

Record p1_postA (sp0 : word) (M M' : word -> option byte) : Prop := P1_POSTA {
  p1p_agree : forall x : word,
      ~ (bv_unsigned sp0 - 4096 <= bv_unsigned x < bv_unsigned sp0)%Z ->
      ~ (0x0fa578 <= bv_unsigned x < 0x0fa660)%Z ->
      ~ (bv_unsigned x = 0x65d1a0)%Z -> M' x = M x;
  p1p_munch : munch [((bv_unsigned sp0 - 4096)%Z, (bv_unsigned sp0)%Z); (0x0fa578%Z, 0x0fa660%Z); (0x65d1a0%Z, 0x65d1a1%Z)] M M';
  p1p_grows : mem_grows M M';
  p1p_wmono : wmono RSEGS M M';
  p1p_file  : stdout_bufferedA M' 0x65d1a0
}.

(* [comment removed for export] *)
Fixpoint log_out (E : env) (x : word) (log : list sentry) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest =>
      (bv_unsigned (adenot E a) + Z.of_nat w <= 2 ^ 64)%Z
      /\ (bv_unsigned x < bv_unsigned (adenot E a) \/ bv_unsigned (adenot E a) + Z.of_nat w <= bv_unsigned x)%Z
      /\ log_out E x rest
  end.
Lemma mem_denot_out : forall E M log (x : word), log_out E x log -> mem_denot E M log x = M x.
Proof.
  intros E M log x. induction log as [|[a w v] rest IH]; intros H; [reflexivity|].
  cbn [log_out] in H. destruct H as (H1 & H2 & H3).
  cbn [mem_denot]. rewrite MemSplit.wbytes_outside.
  - apply IH. exact H3.
  - rewrite length_N_to_le_bytes. exact H1.
  - rewrite length_N_to_le_bytes. exact H2.
Qed.

(* [comment removed for export] *)
Definition entry_inW_b (spi : nat) (flo fhi : Z) (iws : list (Z * Z)) (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => Nat.eqb i spi && Z.leb flo k && Z.leb (k + Z.of_nat w) fhi && Z.ltb 0 (Z.of_nat w)
  | SE (SA (ELit z) k) w _ => Z.eqb z 0 && Z.ltb 0 (Z.of_nat w) && existsb (fun lh => Z.leb (fst lh) k && Z.leb (k + Z.of_nat w) (snd lh)) iws
  | _ => false
  end.
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L12898983783.25L3479485672.19 L37618800479.25L5273659168.19 L53518956311.25L55375918571.19L63980919008.2500000F00g01A01_01b02702ES1k1w1x2lo2hi2H12H22W3S1E3spi3flo3fhi1k1w2H12H01H2S12S2S1k1w2Hw2lo2hi2H12H22W12W2S1E3spi3flo3fhi1k1w1x2H12H02N1S1wS1E3spi3fhi1k1w2H02S2S1k1w2hi2H22W2". (* [comment removed for export] *)
Lemma log_out_inW : forall E spi flo fhi iws log (x : word),
  forallb (entry_inW_b spi flo fhi iws) log = true ->
  (0 <= bv_unsigned (ev E spi) + flo)%Z -> (bv_unsigned (ev E spi) + fhi <= 2 ^ 64)%Z ->
  Forall (fun lh => 0 <= fst lh /\ snd lh <= 2 ^ 64 /\ ~ (fst lh <= bv_unsigned x < snd lh))%Z iws ->
  ~ (bv_unsigned (ev E spi) + flo <= bv_unsigned x < bv_unsigned (ev E spi) + fhi)%Z ->
  log_out E x log.
Proof.
  intros E spi flo fhi iws log x Hb S1 S2 IW N1.
  induction log as [|[[b k] w v] rest IH]; [exact I|].
  cbn [forallb] in Hb. apply andb_prop in Hb. destruct Hb as [He Hr].
  cbn [log_out]. unfold adenot, v_addi. cbn [a_base a_off].
  destruct b as [z|i| | | | | |]; cbn [entry_inW_b] in He; try discriminate.
  - apply andb_prop in He. destruct He as [He Hx]. apply andb_prop in He. destruct He as [Hz Hw].
    apply Z.eqb_eq in Hz. subst z. apply Z.ltb_lt in Hw.
    apply existsb_exists in Hx. destruct Hx as [[lo hi] [Hin Hlh]]. cbn [fst snd] in Hlh.
    apply andb_prop in Hlh. destruct Hlh as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) IW _ Hin) as (W1 & W2 & W3). cbn [fst snd] in W1, W2, W3.
    cbn [edenot]. rewrite (u_small 0) by lia. rewrite u_small by lia.
    split; [lia | split; [lia | exact (IH Hr)]].
  - repeat (apply andb_prop in He; destruct He as [He ?]).
    apply Nat.eqb_eq in He. subst i.
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H | H : (_ <? _)%Z = true |- _ => apply Z.ltb_lt in H end.
    cbn [edenot]. rewrite u_small by lia.
    split; [lia | split; [lia | exact (IH Hr)]].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma mem_grows_wmono : forall M M', mem_grows M M' -> wmono RSEGS M M'.
Proof.
  intros M M' G x Hx. unfold wview in *. destruct (M x) as [b|] eqn:EE.
  - specialize (G x ltac:(congruence)). destruct (M' x); [discriminate|contradiction].
  - destruct (M' x); [discriminate|exact Hx].
Qed.

(* [comment removed for export] *)
Lemma grows_of_rst : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "PD,P,(1.&40.)$2:.PE,$5.PM,P,(1.&40.)(1?.(1.&8.))PM',P,(1.&40.)(1?.(1.&8.))Plog,(6.$2;.)P,(;.P,(1.&40.)(1?.(1.&8.))(2<.R5.R2.)(2=.R4.(2<.R5.R3.)R1.))P,Pa,(1.&40.)P,(;.$2:.A1.R7.R1.$2>.)(;.(1?.(1.&8.))A1.R5.R2.A1.R6.R2.)(2?.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros D E M M' log EQ OUT x Hx. destruct (D x) eqn:Dx.
  - pose proof (mem_denot_grows E (restrict D M) log x) as G. rewrite <- EQ in G.
    rewrite !(restrict_in D _ _ Dx) in G. apply G. exact Hx.
  - rewrite (OUT x Dx). exact Hx.
Qed.

Section P1.
  (* [comment removed for export] *)
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable KI : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000%Z.
  Hypothesis K_halted : forall mo, KI mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "Pmo,$30.Pacc,(6.(13.(1.&40.)$9.))P,A1.VKI,R2.P,(31.VAL,VCS,R2.)(32.$30.Lmo',$30.(12.(;.(1?.$30.)(33.R5.R4.)(24.$30.R1.))(12.A1.VKI,R1.(34.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "Pmo,$30.Pmo',$30.P,A1.VKI,R2.P,(;.$35.(36.R2.)(36.R3.))P,(;.(6.(13.(1.&40.)(1.&40.)))(37.R3.)(37.R4.))P,(;.(6.(1.&40.))(38.R4.)(38.R5.))P,(;.(1?.(1.&40.))(39.R5.)(39.R6.))A1.VKI,R6.")
(* [comment removed for export] *).

  Variable sp0 : word.
  Variable model : Model.
  Hypothesis SPlo : (0x7fff7f000000 + 4096 <= bv_unsigned sp0)%Z.
  Hypothesis SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis SPal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Hypothesis HKI : KI model.
  Hypothesis Hfd1 : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
  (* [comment removed for export] *)
  Hypothesis WCS : crange CS (bv_unsigned sp0 - 4096) 4096.
  Hypothesis FCS : crange CS 0x156c0 64.
  Hypothesis BCS : crange CS 0x65d180 128.

  Variables (R : bvmap 5 word) (M : word -> option byte) (can : word).
  Hypothesis G1 : getr R 1 = Z_to_bv 64 0x09748c.
  Hypothesis G2 : getr R 2 = sp0.
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x63ca90.
  Hypothesis G11 : getr R 11 = Z_to_bv 64 0.
  Hypothesis FM : pf_mem sp0 M can.

  (* [comment removed for export] *)
  Let SSW : Z := ((bv_unsigned sp0 - 912) / 8 + 0x7fff8000 - ((bv_unsigned sp0 - 912) / 8 + 0x7fff8000) mod 8)%Z.

  (* [comment removed for export] *)
  Let D : word -> bool := Dimg [(bv_unsigned sp0 - 4096, bv_unsigned sp0)%Z; (0x7fffaad8, 0x7fffaae0)%Z; (0x800c3a30, 0x800c3a38)%Z; (SSW, SSW + 8)%Z].

  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L11799440607.32L14237735119.35L15515289822.35L41954718695.35L45367718360.35L50539368496.33L52538284047.30L56697058689.35L60918251839.29L61028779249.33L61028779894.32L61028780023.31L61034932151.35L61338975526.36L63368316331.33L63368316460.32L63368316718.30L63374425370.28L63374621462.2900000500H00I00[00h00m01701F01P01U01Z01_01d02302802=02B02G02LS3sp0S3sp04SPlo2H12H22H4FS3sp04SPlo1H2H22H3S3sp04SPlo2H4S3sp0S3sp04SPhiS3sp04SPlo1H2H3S3sp04SPloS3sp0S3sp0S3sp0S3sp0S3sp04SPlo1q2H5S3sp0S3sp0S3sp0S3sp0S3sp0". (* [comment removed for export] *)
  Lemma SSW_range : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "(12.(3:.(3;.+7???8000.(3<.(3=.(3>.&40.Vsp0,)+1000.)+8.))VSSW,)(12.(3:.(3;.VSSW,+8.)(3;.+7???8000.(3<.(3>.&40.Vsp0,)+8.)))(12.(;.$14.(3?.VSSW,+8.)=)(12.(3:.+7???8000.VSSW,)(3:.(3;.VSSW,+8.)(40.+2.+2>.))))))")
(* [comment removed for export] *).
  Proof.
    subst SSW. pose proof (Z.mod_pos_bound ((bv_unsigned sp0 - 912) / 8 + 2147450880) 8 ltac:(lia)).
    pose proof (Z.div_pos (bv_unsigned sp0 - 4096) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (bv_unsigned sp0) 8 (2^45) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_mod ((bv_unsigned sp0 - 912) / 8 + 2147450880) 8 ltac:(lia)).
    assert ((bv_unsigned sp0 - 4096) / 8 + 7 <= (bv_unsigned sp0 - 912) / 8)%Z.
    { replace ((bv_unsigned sp0 - 4096) / 8 + 7)%Z with ((bv_unsigned sp0 - 4096 + 56) / 8)%Z by (rewrite <- Z.div_add by lia; reflexivity).
      apply Z.div_le_mono; lia. }
    assert ((bv_unsigned sp0 - 912) / 8 + 8 <= bv_unsigned sp0 / 8)%Z.
    { replace ((bv_unsigned sp0 - 912) / 8 + 8)%Z with ((bv_unsigned sp0 - 912 + 64) / 8)%Z by (rewrite <- Z.div_add by lia; reflexivity).
      apply Z.div_le_mono; lia. }
    assert (M8 : forall q, ((q - q mod 8) mod 8 = 0)%Z).
    { intros q. pose proof (Z.div_mod q 8 ltac:(lia)). replace (q - q mod 8)%Z with (8 * (q / 8))%Z by lia. rewrite Z.mul_comm. apply Z_mod_mult. }
    repeat split; try lia. apply M8.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma D_Dseg : forall a : word, segcov RSEGS (bv_unsigned a) = true -> D a = true.
  Proof. intros a H. unfold D. apply Dimg_Dseg. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L6097392651.3100000;S3sp03SSW1c". (* [comment removed for export] *)
  Lemma shadow_aok : forall c x, CS c -> (x = 0x7fff8000 + c / 8)%Z -> aok_addr AL CS x.
  Proof. intros c x Hc ->. right; left. exists c. split; [exact Hc|]. unfold shadow_of. rewrite ASB. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L19627418368.38L24890867569.42L3515141888.38 L5268879960.38 L60692804685.43L61028780023.40L61028787006.38L63368316460.41L63368316718.39L67812584585.3800000F00O00e01001Y01b01k02402=02KS3sp04SPlo3SSW2S41z2HzS3sp03SSWS3sp04SPlo3SSW2S41z2HzS3sp03SSW1zS3sp04SPlo3SSW2S12S22S41z2Hz2H02H12H23D16S3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW1z2Hz". (* [comment removed for export] *)
  Lemma D_DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
  Proof.
    pose proof SSW_range as (S1 & S2 & S3 & S4 & S5).
    intros a H. unfold D in H. eapply (Dimg_DOK_aok AL CS IMG); [|exact H].
    repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
    - intros z Hz. left. apply WCS. lia.
    - intros z Hz. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply FCS; lia|]. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - intros z Hz. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply BCS; lia|]. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - intros z Hz. apply (shadow_aok (8 * (z - 0x7fff8000))).
      + apply WCS. pose proof (Z.div_mod (bv_unsigned sp0 - 4096) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned sp0 - 4096) 8 ltac:(lia)).
        pose proof (Z.div_mod (bv_unsigned sp0) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned sp0) 8 ltac:(lia)).
        pose proof (Z.div_mod (bv_unsigned sp0) 16 ltac:(lia)) as D16. rewrite SPal in D16. lia.
      + rewrite Z.mul_comm, Z.div_mul by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L22864299158.35L24994215446.35L3891981915.35 L60918251839.3500000900B00N00\S3sp03SSWS3sp03SSWS3sp03SSW2S4S3sp04SPlo3SSW". (* [comment removed for export] *)
  Lemma D_D0 : D (Z_to_bv 64 0) = false.
  Proof. destruct SSW_range as (S1 & S2 & S3 & S4 & S5). pose proof SPlo. unfold D. apply Dimg_D0. clearbody SSW. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition RRUN := rz_runA RSEGS D AL CS KI K_halted K_mat D_Dseg asegs_top D_DOK D_D0.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L30901545954.35L46534914516.35L60924549197.3500000Q00_00mS3sp04SPlo3SSW2lo2hi3Hlo3Hhi1z2HzS3sp04SPhi3SSWS3sp04SPlo3SSW". (* [comment removed for export] *)
  Lemma D_frame : forall lo hi, (bv_unsigned sp0 - 4096 <= lo)%Z -> (hi <= bv_unsigned sp0)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply (Dimg_cov _ (bv_unsigned sp0 - 4096) (bv_unsigned sp0)); [left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40646207469.3500000QS3sp04SPlo3SSW2lo2hi3Hlo3Hhi1z2Hz". (* [comment removed for export] *)
  Lemma D_img : forall lo hi, (0x10000 <= lo)%Z -> (hi <= 0x65f000)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply Dimg_img. unfold AIMG_LO, AIMG_HI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L24992116580.31L3213283949.31 L58982879647.3100000900G00PS3sp03SSWS3sp03SSW1z2HzS3sp03SSW". (* [comment removed for export] *)
  Lemma D_shf : DcovZ D 0x7fffaad8 0x7fffaae0.
  Proof. intros z Hz. unfold D. eapply Dimg_cov; [right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L22862208484.31L54431367533.31L56544821279.3100000900G00PS3sp03SSWS3sp03SSW1z2HzS3sp03SSW". (* [comment removed for export] *)
  Lemma D_shb : DcovZ D 0x800c3a30 0x800c3a38.
  Proof. intros z Hz. unfold D. eapply Dimg_cov; [right; right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L23944427781.38L3885692713.38 L48091327752.3800000<00H00VS3sp03SSW2S5S3sp03SSW2S4S3sp03SSW1z2Hz". (* [comment removed for export] *)
  Lemma D_shs : DcovZ D SSW (SSW + 8).
  Proof. destruct SSW_range as (S1 & S2 & S3 & S4 & S5). pose proof SPlo. pose proof SPhi. intros z Hz. unfold D. eapply Dimg_cov. { right; right; right; left; reflexivity. } all: clearbody SSW; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition valsP1 : list word := [sp0] ++ junk_vals R ++ [can].
  Let E : env := Env (vals_ev valsP1) (blobs_ev []).

  Lemma valsP1_len : length valsP1 = 34%nat.
  Proof. unfold valsP1. rewrite !length_app, junk_vals_length. reflexivity. Qed.
  Lemma vP0 : vals_ev valsP1 0 = sp0. Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Definition LITS_KND : list (Z * Z) := [(0x10000, 0x65f000)%Z; (0x7fffaad8, 0x7fffaae0)%Z; (0x800c3a30, 0x800c3a38)%Z].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L43821501577.34L51855111613.30L59283940997.3400000@00I00YS3sp03SSW2hi3HhiS3sp03SSWS3sp03SSW2lo3Hlo". (* [comment removed for export] *)
  Lemma KND : forall kn, Forall (kentry_inD D E) (knd_residual (-4096) LITS_KND kn) -> kn_inD D E kn.
  Proof.
    apply (kn_inD_residual D E sp0 (-4096) LITS_KND).
    - exact vP0.
    - intros lo hi Hlo Hhi. apply D_frame; lia.
    - repeat (apply Forall_cons; [cbn [fst snd] |]); [apply D_img; lia | exact D_shf | exact D_shb | apply Forall_nil].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18267881737.34L5599869189.34 00000A00RS3sp03SSW3qhi3HhiS3sp03SSW3qlo3Hlo". (* [comment removed for export] *)
  Lemma D_frameS : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "Pqlo,$14.Pqhi,$14.P,(3:.(3;.(3>.&40.Vsp0,)-1000.)R2.)P,(3:.R2.(3>.&40.Vsp0,))(41.VD,R4.R3.)")
(* [comment removed for export] *).
  Proof. intros qlo qhi Hlo Hhi. apply D_frame; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L38995425597.30L4957445309.30 L51855111613.30L54869566397.30L58753121597.3000000100:00C00D00MFS3sp03SSWS3sp03SSWFS3sp03SSW". (* [comment removed for export] *)
  Lemma HLITS_KND : Forall (fun iv => DcovZ D (fst iv) (snd iv)) LITS_KND.
  Proof. unfold LITS_KND. repeat (apply Forall_cons; [cbn [fst snd] |]); [ .. | apply Forall_nil]; first [ apply D_img; lia | exact D_shf | exact D_shb ]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54434931423.30000009S3sp03SSW". (* [comment removed for export] *)
  Lemma vP33 : vals_ev valsP1 33 = can.
  Proof. unfold valsP1, vals_ev. change ([sp0] ++ junk_vals R ++ [can]) with (([sp0] ++ junk_vals R) ++ [can]).
    rewrite app_nth2; [|rewrite length_app, junk_vals_length; cbn; lia].
    rewrite length_app, junk_vals_length. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Ltac evs := unfold E; cbn [ev eb]; rewrite ?vals_ev_app_l by (rewrite valsP1_len; lia); rewrite ?vP0, ?vP33.

  Lemma evP1_junk : forall i, (i < 32)%nat -> ev E (1 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E. cbn [ev]. unfold valsP1.
    change (1 + i)%nat with (length [sp0] + i)%nat.
    unfold vals_ev. cbn [app length Nat.add]. change (S i) with (length [sp0] + i)%nat. change (sp0 :: junk_vals R ++ [can]) with ([sp0] ++ (junk_vals R ++ [can])). rewrite app_nth2_plus. rewrite app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2871711490.3400000BS3sp01R3SSW1E1i2Hi". (* [comment removed for export] *)
  Lemma regs_okP1 : regs_ok E sr_PF R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_PF all_regs];
      first [ (cbn [edenot]; first [ reflexivity | exact G1 | exact G3 | exact G4 | exact G11 | (evs; exact G2) ])
            | (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                 change (edenot E (EVar n)) with (ev E n); rewrite (evP1_junk (n - 1)) by lia; reflexivity end) ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L29784466142.32L43935895424.34L47684058185.33L47803405696.34L53081583146.32L55715230514.32L59576963504.34L59591279578.33L59875528097.32L62923639303.32L63368316460.34L63368316589.33L63368316718.32L8929201831.35 00000900H00M00\00e00n01701E01X01f01o02802A02XS3sp03SSWS3sp03SSW2H12H2S3sp0S3sp03SSW2H12H2S3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo3SSW2H12H22H3". (* [comment removed for export] *)
  Lemma ssw_denot : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "(;.$14.(42.VE,(43.(44.$45.(44.$46.(44.$47.(44.$46.(48.#0.)(10.-390.))(10.+3.))(10.+7???8000.))(10.-8.))=))VSSW,)")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo. pose proof SPhi.
    unfold estart. cbn [a_base a_off edenot]. evs.
    rewrite alu_and. rewrite alu_add. rewrite alu_srl. rewrite (alu_add sp0).
    unfold v_and, v_add, v_srl.
    replace (bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + bv_unsigned (Z_to_bv 64 (-912)))))%Z with (bv_unsigned sp0 - 912)%Z.
    2:{ rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
        change ((-912) mod 18446744073709551616)%Z with 18446744073709550704%Z.
        apply Z.mod_unique with (q := 1%Z); lia. }
    rewrite (unsigned_lit 3) by lia. change (3 mod 64)%Z with 3%Z. rewrite Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
    pose proof (Z.div_pos (bv_unsigned sp0 - 912) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (bv_unsigned sp0 - 912) 8 (2^45) ltac:(lia) ltac:(lia)).
    rewrite (unsigned_lit ((bv_unsigned sp0 - 912) / 8)) by lia. rewrite (unsigned_lit 2147450880) by lia.
    rewrite (unsigned_lit ((bv_unsigned sp0 - 912) / 8 + 2147450880)) by lia.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with 18446744073709551608%Z by reflexivity.
    rewrite A_rip.land_m8 by lia. rewrite unsigned_lit.
    2:{ pose proof (Z.mod_pos_bound ((bv_unsigned sp0 - 912) / 8 + 2147450880) 8 ltac:(lia)). lia. }
    subst SSW. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma adenot_of_estart : forall a, flat E a 8 -> adenot E a = Z_to_bv 64 (estart E a).
  Proof. intros a Hf. rewrite <- (flat_u E a 8 Hf). symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "01H0?L11617837940.66L12421601389.66L13482121606.66L14054083309.70L14342781974.66L14515323471.66L1550781718.66 L16135356490.70L17543312104.68L18433691966.66L18926596374.66L21030657615.66L21513524980.72L21925619677.66L21988997858.66L22606967693.66L22860139030.66L23160250867.66L2431328725.69 L24990120086.66L25240541541.65L25274003823.66L2562851341.66 L27136798486.66L27313314277.66L27354698513.66L27849931296.66L28678382092.66L29590715798.66L30433548301.66L31327315070.69L31423595263.66L31739632336.66L32150991245.66L32421441036.66L32648418366.72L32959583144.66L33208650381.66L33671131928.66L34019894934.66L3509085078.66 L35823809814.66L37373102157.66L37953715094.66L38258383245.66L3829630897.69 L38641882893.66L39512977622.66L42219554177.70L42633676813.66L43828629189.66L44346061185.70L44749504269.66L44750447231.66L4504975677.69 L46642545046.66L46811861398.66L47630204329.66L48557361648.66L48617825302.66L48941761558.66L5007085009.66 L50716179816.68L51241048726.66L51518472845.66L53517092650.66L53519161933.70L55662616861.70L55847531981.66L5639034390.66 L58557398989.66L58683819149.66L5928693697.66 L59434479766.66L61564446486.66L62675630477.66L63882226373.66L64035337622.66L64793603213.66L64904567632.66L65174944269.66L65500100630.66L65730371853.66L6675556237.66 L68056809635.66L68077457517.66L725126413.66  L9271789352.66 00000100:00C00c00l00m01601F01T01U01^01_02?02H02V02_02h02i03603?03N03W03`03i04704E04F04O04X04a05<05=05>05G05P06006106:06C06L06U06^06g07007907J07S07\07l08508>08N08W08X08g09009909:09;09D09M09`09n0:70:@0:I0:T0:o0;80;A0;J0;S0;\0;e0;n0<70<@0<I0<R0<S0<\0<e0<n0=70=@0=I0=R0=SFS3sp03SSWS3sp03SSWS3sp04SPlo3SSW1H2H02S41d1m2Hd2HmS3sp03SSWFS3sp03SSWS3sp03SSW1d1m2HmS3sp03SSW1i2HiFS3sp03SSWFS3sp04SPlo3SSW2S41d1m2Hd2Hm1x2HxS3sp03SSWS3sp04SPhi3SSWS3sp03SSWS3sp03SSWFS3sp03SSW1n1BS3sp03SSWS3sp03SSW2S42S5S3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPhi3SSWS3sp04SPlo3SSWFS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo3SSW2S43off1n1B1CFFS3sp03SSWS3sp03SSWS3sp04SPlo3SSW2S41d1m2Hd2Hm1x2HxFS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW3off1n1CS3sp03SSWS3sp03SSWS3sp03SSW1d1m2HdS3sp03SSWS3sp03SSWS3sp03SSW1d1m2HdS3sp03SSWFS3sp03SSW3off1AS3sp03SSWS3sp03SSWFFS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSW1i2HiS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW1mS3sp04SPlo3SSW2H02S41d1m2HmS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWFS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWF". (* [comment removed for export] *)
  Lemma know_okP1 : know_ok RSEGS E M kn_PF.
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal. pose proof SSW_range as (S1 & S2 & S3 & S4 & S5).
    destruct FM.
    assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
    { intros off n A B C. apply flat_abs0; lia. }
    assert (FSH : flat E (SA (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 0) (ELit (-912))) (ELit 3)) (ELit 2147450880)) (ELit (-8))) 0) 8).
    { unfold flat. rewrite ssw_denot. clearbody SSW. lia. }
    unfold know_ok, kn_PF.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    all: try (split; [lia|]; split; [apply FL; lia|]; rewrite adenot_lit0; cbn [edenot]; assumption).
    all: first
      [ (* [comment removed for export] *) split; [lia|]; cbn [edenot]; evs; assumption
      | (* [comment removed for export] *) cbn [edenot]; evs; lia
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot]; evs; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off]; cbn [edenot]; evs;
        apply store_ok_of_all; rewrite u_small by lia; [lia|]; intros x Hx; apply pf_win0; lia
      | (* [comment removed for export] *) split; [lia|]; split; [lia|]; intros i Hi; first [apply pf_ro0; lia | apply pf_file0; lia]
      | (* [comment removed for export] *) split; [lia|]; split; [exact FSH|]; rewrite (adenot_of_estart _ FSH), ssw_denot; cbn [edenot]; exact pf_shs0
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia;
        first [ apply store_ok_data; rewrite u_small by lia; lia
              | apply store_ok_of_all; rewrite u_small by lia; [lia|]; intros x Hx; apply pf_buf0; lia ] ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L13450929509.3100000BS3sp04SPlo3SSW1E1H". (* [comment removed for export] *)
  Lemma ssw_denot' : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "(;.$14.(3>.&40.(?.VE,(44.$45.(44.$46.(44.$47.(44.$46.(48.#0.)(10.-390.))(10.+3.))(10.+7???8000.))(10.-8.))))VSSW,)")
(* [comment removed for export] *).
  Proof. pose proof ssw_denot as H. unfold estart in H. cbn [a_base a_off] in H. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac covtac :=
    try (unfold estart, elenZ; cbn [a_base a_off]);
    first [ exact I
          | rewrite ssw_denot'; intros z Hz; apply D_shs; lia
          | cbn [edenot]; evs; rewrite ?(u_small 0) by lia; intros z Hz;
            first [ apply (D_img z (z + 1)); lia | apply (D_frame z (z + 1)); lia | apply D_shf; lia | apply D_shb; lia | apply D_shs; lia ] ].

  Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x156fc) 1%nat = Some [Z_to_bv 8 10].
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rdn_of_rst : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "PMM,P,(1.&40.)(1?.(1.&8.))Pa,(1.&40.)Pn,$9.Pbs,(6.(1.&8.))P,(;.(1?.(6.(1.&8.)))(49.$4:.(2<.VD,R4.)R3.R2.)(24.(6.(1.&8.))R1.))P,(3:.(3;.(3>.&40.R4.)(4;.R3.))(40.+2.+40.))P,(41.VD,(3>.&40.R5.)(3;.(3>.&40.R5.)(4;.R4.)))(;.(1?.(6.(1.&8.)))(49.$4:.R7.R6.R5.)(24.(6.(1.&8.))R4.))")
(* [comment removed for export] *).
  Proof. intros MM a n bs H Hnw HD. rewrite <- (rdn_restrict_in RSEGS D MM a n Hnw HD). exact H. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L24890950346.35L29782367974.35L39407514431.36L59308648300.36L61028858315.3600000;00F00Q00^00iS3sp03SSW1xS3sp03SSW1xS3sp03SSW1xS3sp03SSW1x1TS3sp03SSW1x". (* [comment removed for export] *)
  Lemma lor40_mod16 : forall x, (0 <= x)%Z -> ((Z.lor 40 x) mod 16 <> 0)%Z.
  Proof.
    intros x Hx EQ.
    assert (T : Z.testbit (Z.lor 40 x) 3 = true) by (rewrite Z.lor_spec; reflexivity).
    apply Z.testbit_true in T; [|lia]. change (2 ^ 3)%Z with 8%Z in T.
    pose proof (Z.lor_nonneg 40 x) as NN.
    pose proof (Z.div_mod (Z.lor 40 x) 16 ltac:(lia)) as DM. rewrite EQ, Z.add_0_r in DM.
    rewrite DM in T. replace (16 * (Z.lor 40 x / 16) / 8)%Z with (2 * (Z.lor 40 x / 16))%Z in T.
    2:{ symmetry. replace (16 * (Z.lor 40 x / 16))%Z with ((2 * (Z.lor 40 x / 16)) * 8)%Z by lia. apply Z.div_mul. lia. }
    rewrite Z.mul_comm, Z_mod_mult in T. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L15524776872.34L40825274790.32L53519057080.34L65502424806.3200000=00F00Q00ZS3sp03SSW1x1BS3sp03SSWS3sp03SSW1xS3sp03SSW". (* [comment removed for export] *)
  Lemma memset_align_false : forall x, (0 <= x)%Z ->
    bv_eqb (Z_to_bv 64 (Z.land (Z.lor 40 x) 15)) (Z_to_bv 64 0) = false.
  Proof.
    intros x Hx. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4)%Z with 16%Z.
    pose proof (Z.mod_pos_bound (Z.lor 40 x) 16 ltac:(lia)) as B. pose proof (lor40_mod16 x Hx) as NZ.
    unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact NZ.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L1327034471.32 L20406137190.32L56093574452.33L56093676630.32L56093765662.34L60195477991.34L9074610895.33 00000>00G00X00f01401C01QS3sp03SSW1x2HxS3sp03SSWS3sp03SSW1x2Hx2NZS3sp03SSW1x2HxS3sp03SSW1x2HxS3sp03SSW1x1H1nS3sp03SSW1x2Hx". (* [comment removed for export] *)
  Lemma lor40_bound : forall x, (0 <= x < 2^64)%Z -> (0 <= Z.lor 40 x < 2^64)%Z.
  Proof.
    intros x Hx. split; [apply Z.lor_nonneg; lia|].
    apply Z.log2_lt_pow2. { assert (0 <= Z.lor 40 x)%Z by (apply Z.lor_nonneg; lia). destruct (Z.eq_dec (Z.lor 40 x) 0) as [E0|]; [|lia]. exfalso. pose proof (lor40_mod16 x ltac:(lia)) as MZ. rewrite E0 in MZ. apply MZ. reflexivity. }
    rewrite Z.log2_lor by lia. apply Z.max_lub_lt; [reflexivity|].
    destruct (Z.eq_dec x 0) as [->|NZ]; [reflexivity|]. apply Z.log2_lt_pow2; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L36115031034.32L56093676630.32L5744833530.32 L60706472698.3200000900G00U00^S3sp03SSWS3sp03SSW1x2HxS3sp03SSW1x2HxS3sp03SSW". (* [comment removed for export] *)
  Lemma memset_align_false' : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "Px,$14.P,(12.(3:.=R1.)(4<.R1.(40.+2.+40.)))(;.$2:.(4=.&40.(4>.&40.(4?.(3>.&40.(4>.&40.(50.(3>.&40.(4>.&40.+28.))(3>.&40.(4>.&40.R2.)))))(3>.&40.(4>.&40.+?.))))(4>.&40.=))$2>.)")
(* [comment removed for export] *).
  Proof.
    intros x Hx. rewrite (unsigned_lit 40), (unsigned_lit 15), (unsigned_lit x) by lia.
    rewrite unsigned_lit by (apply lor40_bound; lia). apply memset_align_false. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L36108758349.32L52514167674.32L5744833530.32 L8443612310.32 00000>00G00U00cS3sp03SSW1x2HxS3sp03SSWS3sp03SSW1x2HxS3sp03SSW1x2Hx". (* [comment removed for export] *)
  Lemma not_ltu1_false : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "Px,$14.P,(12.(3:.=R1.)(4<.R1.(3=.(40.+2.+40.)+1.)))(;.$2:.(51.&40.(4>.&40.(52.(3>.&40.(4>.&40.R2.))(3>.&40.(4>.&40.-1.))))(4>.&40.+1.))$2>.)")
(* [comment removed for export] *).
  Proof.
    intros x Hx. rewrite (unsigned_lit x) by lia. replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z by reflexivity.
    rewrite zb_lxor_ones by lia. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma alu_add_zlit : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "Px,(1.&40.)Pk,$14.P,(12.(3:.=(3;.(3>.&40.R2.)R1.))(4<.(3;.(3>.&40.R2.)R1.)(40.+2.+40.)))(;.(1.&40.)(53.$46.R3.(4>.&40.R2.))(4>.&40.(3;.(3>.&40.R3.)R2.)))")
(* [comment removed for export] *).
  Proof.
    intros x k Hk. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac solve_sc :=
    cbn [sc_denot branch_taken];
    first
      [ lazymatch goal with |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off]; rewrite !ssw_denot'; cbn [edenot];
          rewrite ?(u_small 8), ?(u_small 4), ?(u_small 0) by lia; clearbody SSW; lia end
      | cbn [edenot]; evs; rewrite !alu_add_zlit by lia;
        first
          [ (* [comment removed for export] *) apply Bool.negb_true_iff; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia
          | (* [comment removed for export] *) rewrite alu_and, alu_or; unfold v_and, v_or; apply memset_align_false'; lia
          | (* [comment removed for export] *) rewrite alu_xor; unfold v_xor; apply not_ltu1_false; lia ] ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "03n0?L10407095782.85L10830652995.46L11206318435.46L13009263681.86L13221020802.79L13221105924.62L13224975996.63L13253319459.46L14142502659.46L14343077299.46L14597676067.46L15086884022.54L15861370436.64L16160542995.46L16868042531.46L16968254566.85L17364985923.46L17567094771.46L17576185571.46L18201495267.46L18539745683.46L18602099603.46L18791736675.46L18844788515.46L18937142251.86L19052695123.46L192353827.46  L19345286379.86L19377636035.46L19472243267.46L20405665987.46L20478444611.46L20514225091.46L21150977731.46L21268405955.46L21732500547.46L21782345138.86L22048891619.46L22095414115.46L22291521683.46L22697159619.46L22706783811.46L22850406691.46L22858427880.62L23963578915.46L24141865027.46L24869343059.46L25271894999.82L25271896031.83L25271923445.81L25273991249.87L25273991509.85L25273991639.86L25273991761.84L25273992785.90L25273993045.88L25273993183.89L25276088791.92L25276089047.91L25942147171.46L26310382947.46L26530001329.85L26674031171.46L26716195107.46L2682011987.46 L26847972035.46L27352565217.85L27459585427.46L27697886595.46L2889549507.46 L30042034723.46L30093800355.46L30226844737.85L30568069347.46L30757990355.46L30922035139.46L31062386611.46L31069185473.86L31292086702.62L31380875363.46L31594092367.62L31620911811.46L31749915075.46L31784182995.46L32057867010.62L32127152595.46L32344960755.46L32539622979.46L32648425590.86L32675216371.46L327682691.46  L33441588787.46L33469914851.46L33489276979.46L34301840690.85L34301963263.85L34357744995.46L34361453155.46L34449921731.46L34767090818.62L35022440483.46L35268241800.62L35573945123.46L36204878403.46L36356587363.46L36419201379.46L3702805603.46 L37193380147.46L37317935811.46L37506911299.46L38153225443.46L38687958051.46L38802598371.46L39104362563.46L39227656739.46L39243064657.46L39334201703.46L39390230819.46L39958151523.46L40459202595.46L40922741651.46L40969107907.46L41286941395.46L41707283107.46L41835265267.46L4236472419.46 L42706834461.54L43587890403.46L43766362339.46L44122098723.46L44129599779.46L44283042835.46L44316796707.46L44417343363.46L45264827843.46L45404868723.46L45657750643.46L45874800581.78L46329768035.46L46683983854.62L46796545539.46L46984569331.46L47158443971.46L47426611491.46L47560756579.46L47611842339.46L47644030019.46L47962744883.46L48042514019.46L48091327752.48L4846689763.46 L48508369123.46L49117164835.46L49852368451.46L50221185587.46L50462742077.62L50548189443.46L51370933475.46L51493768547.46L52094159352.64L52096288384.62L52514167416.64L52516164864.62L52516164865.54L52744587715.46L52893976643.46L53112855336.85L53174586053.62L53506559943.46L53516658691.54L53861255907.46L54032169216.62L54034364024.64L54570748835.46L54605573779.46L54640703645.85L54945810789.86L55190205635.46L55935018563.46L56174103411.46L56842278144.62L56844606072.64L57139524083.46L5723349572.64 L57332219971.46L57517727523.46L5790411049.86 L57913131363.46L58418114595.46L59194474947.46L5926590833.83 L5926591865.82 L5926612059.81 L5928687871.90 L5928687985.89 L5928688123.88 L5928688895.84 L5928689407.87 L5928689529.86 L5928689659.85 L5928695627.62 L5930785913.91 L5930786681.92 L59500160067.46L59918142931.46L60206267939.46L60394071587.46L60683564259.46L60868360787.46L60900512787.46L61142528963.46L62181556557.46L62195195859.46L62672136992.85L62809801891.46L62859678147.46L63035641795.46L63385867080.85L63576125955.46L63829252722.62L63885892195.46L64006830787.46L64934825027.46L65869085251.46L66172673731.46L66428072254.81L6682615076.62 L67061404339.46L67188026435.46L67812584585.64L67818668628.83L67818669660.82L67820765780.89L67820765918.88L67820766170.90L67820766300.86L67820766430.85L67820766682.87L67820767194.84L67822863452.92L67822864220.91L67919596867.46L67951513317.62L68034928195.46L68162793235.46L68262436419.46L7064005299.46 L715194659.46  L787562291.46  L807600963.46  L8593087975.46 L9052512899.46 L9059424835.46 L9675510131.46 00000900L00_00h01;01N01a01j02302<02O02X02f02o03B03K03^03g04:04M04V04_05205E05N05W05`05i06<06E06N06a07407G07Z07c07l08508>08G08Z08m09609?09R09e09n0:70:@0:I0:R0:[0:d0:m0;60;?0;H0;Q0;Z0;m0<@0<Z0<m0=60=?0=R0=`0=i0>20>E0>X0>a0>j0?=0?F0?O0?X0?a0?j0@=0@F0@Y0@l0A50A>0AG0AP0Ac0B10B:0BC0BL0B_0Bh0C60CG0CZ0Cm0D@0DN0Da0Dj0E30EF0EO0EX0Ea0Ej0F=0FP0Fc0G60G?0GR0Ge0H40H=0HP0Hc0I60I?0IR0I[0Id0Im0J@0JI0J\0Jo0KB0KU0K^0L10L:0LC0LL0LU0Lh0M10M:0MC0ML0M_0N20NE0NX0Na0Nj0O=0OK0OT0Og0P:0PM0PV0P_0Ph0Q;0QD0QM0QV0Q_0Qh0R10RD0RW0Re0Rn0S70S@0SS0S\0Se0Sn0T70T@0TI0TR0Te0Tn0U70U@0UI0UW0Uj0V=0VQ0Vd0W70WJ0WS0W\0We0Wn0X70X@0XI0XR0X[0Xd0Xm0Y60Y?0YR0Y[0Yd0Z70Z@0ZI0ZR0Ze0[80[A0[O0[X0[k0\>0\G0\P0\Y0\l0]?0]R0]e0^80^A0^J0^S0^f0_40_=0_F0_O0_X0_a0_j0`30`<0`E0`N0`W0``0`n0aA0aJ0aS0a\0ao0b80bA0bJ0bS0bf0boS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSW1z2HzS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo3SSW3Hlo2S41x2O3S3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSW1x2H0S3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSW1x2O1S3sp03SSW1x2N12N2S3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSW2S42S5S3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp01R3SSW2RC1i2HiS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSW1z2HzS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSW1x2O2S3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW1z2HzS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSW1x2H02N22N3S3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSW1z2HzS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSW". (* [comment removed for export] *)
  Theorem printf1A : ltac2:(CDefT.buildp (gd_tbl_A_printf1 ()) "PKK,$54.P,A1.R1.(4.$55.)P,Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PM',P,(1.&40.)(1?.(1.&8.))Pmo',$30.P,(56.Vsp0,VM,R2.)P,A1.VKI,R2.P,(34.Vmodel,R3.)(57.$4:.(58.(59.(5:.(4>.&40.+9748<.)Vsp0,(4>.&40.+10800.)(4>.&40.+63<:90.)R14.R13.R12.(<.VR,(2.&5.+8.$3.))(<.VR,(2.&5.+9.$3.))R11.R10.R?.R>.R=.R<.R;.R:.(<.VR,(2.&5.+12.$3.))(<.VR,(2.&5.+13.$3.))(<.VR,(2.&5.+14.$3.))(<.VR,(2.&5.+15.$3.))(<.VR,(2.&5.+16.$3.))(<.VR,(2.&5.+17.$3.))(<.VR,(2.&5.+18.$3.))(<.VR,(2.&5.+19.$3.))(<.VR,(2.&5.+1:.$3.))(<.VR,(2.&5.+1;.$3.))R9.R8.R7.R6.)(5;.&5.(1.&40.))(4>.&40.+9748<.)(4>.&20.=)(5<.(1.&40.))R5.(5=.$4:.))R4.)R16.)(57.$4:.(58.(5>.$5?.VR,(4>.&40.+97538.)VM,(5=.$4:.))Vmodel,)(60.(61.+1.(62.#1.))R3.))")
(* [comment removed for export] *).
  Proof.
    intros KK HKnil HC.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SSW_range as (S1 & S2 & S3 & S4 & S5).
    pose proof regs_okP1 as HR. pose proof know_okP1 as HK.
    pose proof FM as FM'. destruct FM' as [Wn RO FI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try clear KNDc.
    lazymatch goal with HRx : regs_ok ?EE _ _ |- _ => let EE2 := eval unfold E in EE in lazymatch EE2 with Env (vals_ev ?Vx) ?bb => pose proof (kn_inD_residual D (Env (vals_ev Vx) bb) sp0 (-4096) LITS_KND ltac:(cbn [ev]; first [ exact vP0 | rewrite ?vals_ev_app_l by (rewrite ?length_app, ?junk_vals_length, ?valsP1_len; cbn; lia); exact vP0 ]) D_frameS HLITS_KND) as KNDc end end.
    run_blockA3 RRUN KNDc FUEL_PF STOPS_PF scrA 34%nat true covtac.
    all: try solve_sc.
    rename EQM into EQMA. rename OUT into OUTA. rename R0 into RA. rename M0 into MA. rename HKmo into HKA. rename MM into MMA.
    (* [comment removed for export] *)
    assert (FdA : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))).
    { unfold m_fds in *. destruct MMA as (E1 & _). rewrite E1. exact Hfd1. }
    eapply (rz_ioctl_winszA RSEGS KI K_halted RA _ MA mo W_e3d68 (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)));
      [ exact F_e3d68 | exact E_e3d68 | exact HKA
      | regv HR (17 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | exact FdA
      | exact I        (* [comment removed for export] *)
      | regv HR (11 : reg); apply bv_eq; reflexivity | ].
    rewrite v_addi_pc4 by lia.
    pose proof (regs_set_a0 E _ _ (errno_ret ENOTTY) (ELit (2 ^ 64 - 25)) HR ltac:(cbn [edenot]; rewrite errno_ret_lit; apply bv_eq; reflexivity)) as HR2.
    clear HR. rename HR2 into HR.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try clear KNDc.
    lazymatch goal with HRx : regs_ok ?EE _ _ |- _ => let EE2 := eval unfold E in EE in lazymatch EE2 with Env (vals_ev ?Vx) ?bb => pose proof (kn_inD_residual D (Env (vals_ev Vx) bb) sp0 (-4096) LITS_KND ltac:(cbn [ev]; first [ exact vP0 | rewrite ?vals_ev_app_l by (rewrite ?length_app, ?junk_vals_length, ?valsP1_len; cbn; lia); exact vP0 ]) D_frameS HLITS_KND) as KNDc end end.
    run_blockA3 RRUN KNDc FUEL_PF STOPS_PF scrB 34%nat true covtac.
    all: try solve_sc.
    rename EQM into EQMB. rename OUT into OUTB. rename R0 into RB0. rename M0 into MB. rename HKmo into HKB. rename MM into MMB.
    (* [comment removed for export] *)
    change (W 1 (zero_lines 1)) with (map (WriteEv (Z_to_bv 64 (sc_fd resC))) ([Z_to_bv 8 48] ++ [Z_to_bv 8 10])).
    assert (FdB : fd_lookup (m_fds mo0) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))).
    { unfold m_fds in *. destruct MMB as (E1 & _). rewrite E1. exact FdA. }
    eapply (stdio_call_sound_frA AL CS KI IMG K_halted K_mat K_vmonly valsP1 (blobs_ev []) srB knB RB0 MB mo0 resC [Z_to_bv 8 48] [Z_to_bv 8 10] KK HR HK);
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resC edenot].
    + vm_compute. reflexivity.
    + rewrite !u_small by lia. lia.
    + cbn [length Z.of_nat Pos.of_succ_nat]. rewrite !u_small by lia. lia.
    + cbn [length Z.of_nat Pos.of_succ_nat]. rewrite !u_small by lia. lia.
    + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.add]. lia.
    + left. evs. rewrite alu_add_zlit by lia. rewrite !u_small by lia. lia.
    + left. evs. rewrite alu_add_zlit by lia. rewrite !u_small by lia. lia.
    + rewrite !u_small by lia. lia.
    + rewrite !u_small by lia. lia.                               (* [comment removed for export] *)
    + rewrite !u_small by lia. lia.                               (* [comment removed for export] *)
    + (* [comment removed for export] *)
      rewrite u_small by lia. krd HK 0x65d1a0%Z 1%nat Wb0. cbn [length]. rewrite Wb0. reflexivity.
    + (* [comment removed for export] *)
      cbn [length]. krd HK 0x156fc%Z 1%nat Wnl. rewrite Wnl. reflexivity.
    + exact FdB.
    + exact HKB.
    + (* [comment removed for export] *)
      intros z Hz. revert Hz. evs. rewrite alu_add_zlit by lia. rewrite !u_small by lia. intros Hz. apply WCS. lia.
    + intros z Hz. left. apply BCS. rewrite !u_small in Hz by lia. lia.
    + intros z Hz. left. apply FCS. rewrite !u_small in Hz by lia. lia.
    + exact HKnil.
    + (* [comment removed for export] *)
      intros Rm MC moC HPOST HRm HKm HKC MMC. clear HR HK. rename HRm into HR. rename HKm into HK.
      (* [comment removed for export] *)
      try clear KNDc.
      lazymatch goal with HRx : regs_ok ?EE _ _ |- _ => let EE2 := eval unfold E in EE in lazymatch EE2 with Env (vals_ev ?Vx) ?bb => pose proof (kn_inD_residual D (Env (vals_ev Vx) bb) sp0 (-4096) LITS_KND ltac:(cbn [ev]; first [ exact vP0 | rewrite ?vals_ev_app_l by (rewrite ?length_app, ?junk_vals_length, ?valsP1_len; cbn; lia); exact vP0 ]) D_frameS HLITS_KND) as KNDc end end.
      run_blockA3 RRUN KNDc FUEL_PF STOPS_PF scrC 66%nat true covtac.
      all: try solve_sc.
      lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into RC; rename Mn into MD end.
      rename EQM into EQMC. rename OUT into OUTC. rename HKmo into HKD. rename MM into MMD.
      (* [comment removed for export] *)
      apply (srzJ_getr_ext RSEGS
               (mkR (Z_to_bv 64 0x09748c) sp0 (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90)
                    (getr RC (Z_to_bv 5 5)) (getr RC (Z_to_bv 5 6)) (getr RC (Z_to_bv 5 7)) (getr R 8) (getr R 9)
                    (getr RC (Z_to_bv 5 10)) (getr RC (Z_to_bv 5 11)) (getr RC (Z_to_bv 5 12)) (getr RC (Z_to_bv 5 13))
                    (getr RC (Z_to_bv 5 14)) (getr RC (Z_to_bv 5 15)) (getr RC (Z_to_bv 5 16)) (getr RC (Z_to_bv 5 17))
                    (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                    (getr R 25) (getr R 26) (getr R 27)
                    (getr RC (Z_to_bv 5 28)) (getr RC (Z_to_bv 5 29)) (getr RC (Z_to_bv 5 30)) (getr RC (Z_to_bv 5 31))) RC).
      { intros r. pose proof (ridx_range r) as Hi.
        rewrite <- (ridx_roundtrip r). set (i := ridx r) in *. clearbody i.
        destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
          [ .. | lia];
          lazymatch goal with |- _ = getr RC (Z_to_bv 5 (Z.of_nat ?k)) =>
            first
              [ (transitivity (getr RC (Z_to_bv 5 (Z.of_nat k))); [reflexivity|reflexivity])
              | rewrite (HR (Z_to_bv 5 (Z.of_nat k)));
                lazymatch goal with |- _ = edenot _ (sr_get ?L ?rr) =>
                  let e := eval vm_compute in (sr_get L rr) in change (sr_get L rr) with e end;
                cbn [edenot];
                first [ reflexivity
                      | (lazymatch goal with |- _ = ev _ ?n =>
                           change (ev _ n) with (vals_ev (valsP1 ++ junk_vals Rm) n);
                           rewrite vals_ev_app_l by (rewrite valsP1_len; lia);
                           first [ change (vals_ev valsP1 n) with sp0; reflexivity
                                 | change (vals_ev valsP1 n) with (ev E n); rewrite (evP1_junk (n - 1)) by lia;
                                   etransitivity; [reflexivity|]; reflexivity ] end) ] ]
          end. }
      change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
      apply HC; [ | exact HKD | ].
      2:{ eapply mo_mat_trans; [exact MMA|]. eapply mo_mat_trans; [exact MMB|]. eapply mo_mat_trans; [exact MMC|]. exact MMD. }
      (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      cbn [sc_sp sc_f sc_bufp sc_bufsz resC edenot] in Pagree, Pwend, Pwpos, Pwbase.
      unfold E in Pagree. cbn [ev] in Pagree. rewrite vP0 in Pagree. rewrite alu_add_zlit in Pagree by lia. rewrite !u_small in Pagree by lia.
      assert (AG : forall x : word,
                 ~ (bv_unsigned sp0 - 4096 <= bv_unsigned x < bv_unsigned sp0)%Z ->
                 ~ (0x0fa578 <= bv_unsigned x < 0x0fa660)%Z ->
                 ~ (bv_unsigned x = 0x65d1a0)%Z -> MD x = M x).
      { intros x N1 N2 N3. pose proof (u64_range x).
        destruct (D x) eqn:Dx.
        - (* [comment removed for export] *)
          rewrite <- (restrict_in D MD x Dx). rewrite EQMC. rewrite mem_denot_out.
          2:{ apply (log_out_inW _ 0 (-4096) 0 [(0x0fa578, 0x0fa660); (0x65d1a0, 0x65d1a0 + 1)]%Z); [vm_compute; reflexivity | evs; lia | evs; lia | repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia| split; [lia| first [intros ?; apply N2; lia | intros ?; apply N3; lia]]]) | evs; intros ?; apply N1; lia]. (* [comment removed for export] *) }
          rewrite (restrict_in D MC x Dx). rewrite Pagree by lia.
          rewrite <- (restrict_in D MB x Dx). rewrite EQMB. rewrite mem_denot_out.
          2:{ apply (log_out_inW _ 0 (-4096) 0 [(0x0fa578, 0x0fa660); (0x65d1a0, 0x65d1a0 + 1)]%Z); [vm_compute; reflexivity | evs; lia | evs; lia | repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia| split; [lia| first [intros ?; apply N2; lia | intros ?; apply N3; lia]]]) | evs; intros ?; apply N1; lia]. (* [comment removed for export] *) }
          rewrite EQMA. rewrite mem_denot_out.
          2:{ apply (log_out_inW _ 0 (-4096) 0 [(0x0fa578, 0x0fa660); (0x65d1a0, 0x65d1a0 + 1)]%Z); [vm_compute; reflexivity | evs; lia | evs; lia | repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia| split; [lia| first [intros ?; apply N2; lia | intros ?; apply N3; lia]]]) | evs; intros ?; apply N1; lia]. (* [comment removed for export] *) }
          apply (restrict_in D M x Dx).
        - (* [comment removed for export] *)
          assert (ND : forall lo hi, DcovZ D lo hi -> ~ (lo <= bv_unsigned x < hi)%Z).
          { intros lo hi Hc Hin. specialize (Hc (bv_unsigned x) Hin). rewrite Z_to_bv_bv_unsigned in Hc. congruence. }
          rewrite (OUTC x Dx). rewrite Pagree.
          2:{ apply (ND _ _ (D_frame (bv_unsigned sp0 - 1184 - 112) (bv_unsigned sp0 - 1184) ltac:(lia) ltac:(lia))). }
          2:{ apply (ND _ _ (D_img (0x0fa578 + 32) (0x0fa578 + 48) ltac:(lia) ltac:(lia))). }
          2:{ apply (ND _ _ (D_img (0x0fa578 + 56) (0x0fa578 + 64) ltac:(lia) ltac:(lia))). }
          rewrite (OUTB x Dx). apply (OUTA x Dx). }
      assert (GR : mem_grows M MD).
      { eapply mem_grows_trans; [eapply (grows_of_rst D); [exact EQMA | exact OUTA]|].
        eapply mem_grows_trans; [eapply (grows_of_rst D); [exact EQMB | exact OUTB]|].
        eapply mem_grows_trans; [exact Pgrows|]. eapply (grows_of_rst D); [exact EQMC | exact OUTC]. }
      split.
      * exact AG.
      * intros x Hout. cbn [outside] in Hout. destruct Hout as (O1 & O2 & O3 & _). apply AG; lia.
      * exact GR.
      * apply mem_grows_wmono. exact GR.
      * (* [comment removed for export] *)
        krd HK 0x0fa578%Z 4%nat F0. krd HK (0x0fa578 + 8)%Z 8%nat F8. krd HK (0x0fa578 + 16)%Z 8%nat F16.
        krd HK (0x0fa578 + 32)%Z 8%nat F32. krd HK (0x0fa578 + 40)%Z 8%nat F40. krd HK (0x0fa578 + 56)%Z 8%nat F56.
        krd HK (0x0fa578 + 72)%Z 8%nat F72. krd HK (0x0fa578 + 88)%Z 8%nat F88. krd HK (0x0fa578 + 96)%Z 8%nat F96.
        krd HK (0x0fa578 + 120)%Z 4%nat F120. krd HK (0x0fa578 + 140)%Z 4%nat F140. krd HK (0x0fa578 + 144)%Z 4%nat F144.
        split; first [exact F0 | exact F8 | exact F16 | exact F32 | exact F40 | exact F56 | exact F72 | exact F88
                     | exact F96 | exact F120 | exact F140 | exact F144
                     | rewrite F0; reflexivity | rewrite F8; reflexivity | rewrite F16; reflexivity | rewrite F32; reflexivity
                     | rewrite F40; reflexivity | rewrite F56; reflexivity | rewrite F72; reflexivity | rewrite F88; reflexivity
                     | rewrite F96; reflexivity | rewrite F120; reflexivity | rewrite F140; reflexivity | rewrite F144; reflexivity
                     | match goal with |- ?g => idtac "FILEGOAL:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End P1.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

