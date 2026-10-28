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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg ARestrict A_exit_base A_stdio_defs A_stdio_write A_stdio_call A_code_96000_97000 A_code_e3000_e4000 A_code_e6000_e7000 A_code_e7000_e8000          A_rip.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import SymDriveAX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_printf1_defs A_printfN_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxAKnD.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_printfN2 () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.env"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "Corelib.Lists.ListDef.nth"; "all_regs"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sentry"; "RocqVerifyHarness.AgentSubmission.LibA.Restrict.restrict"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.mem_denot"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BB.StoreOk.mem_grows"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.estart"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.LibA.SymDriveA.DcovZ"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.lor"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "Stdlib.ZArith.BinInt.Z.lxor"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "pn_postA"; "WP"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"].


Definition WP : Z := 0x65d1a2%Z.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
#[local] Existing Instance Lib.PropExec.fx0.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition all_regs : list reg := ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "(0.(1.&5.)(2.&5.=$3.)(0.(1.&5.)(2.&5.+1.$3.)(0.(1.&5.)(2.&5.+2.$3.)(0.(1.&5.)(2.&5.+3.$3.)(0.(1.&5.)(2.&5.+4.$3.)(0.(1.&5.)(2.&5.+5.$3.)(0.(1.&5.)(2.&5.+6.$3.)(0.(1.&5.)(2.&5.+7.$3.)(0.(1.&5.)(2.&5.+8.$3.)(0.(1.&5.)(2.&5.+9.$3.)(0.(1.&5.)(2.&5.+:.$3.)(0.(1.&5.)(2.&5.+;.$3.)(0.(1.&5.)(2.&5.+<.$3.)(0.(1.&5.)(2.&5.+=.$3.)(0.(1.&5.)(2.&5.+>.$3.)(0.(1.&5.)(2.&5.+?.$3.)(0.(1.&5.)(2.&5.+10.$3.)(0.(1.&5.)(2.&5.+11.$3.)(0.(1.&5.)(2.&5.+12.$3.)(0.(1.&5.)(2.&5.+13.$3.)(0.(1.&5.)(2.&5.+14.$3.)(0.(1.&5.)(2.&5.+15.$3.)(0.(1.&5.)(2.&5.+16.$3.)(0.(1.&5.)(2.&5.+17.$3.)(0.(1.&5.)(2.&5.+18.$3.)(0.(1.&5.)(2.&5.+19.$3.)(0.(1.&5.)(2.&5.+1:.$3.)(0.(1.&5.)(2.&5.+1;.$3.)(0.(1.&5.)(2.&5.+1<.$3.)(0.(1.&5.)(2.&5.+1=.$3.)(0.(1.&5.)(2.&5.+1>.$3.)(0.(1.&5.)(2.&5.+1?.$3.)(4.(1.&5.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L1649687558.2000006S1n2Hn". (* [comment removed for export] *)
Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L8912114872.6000007S1r3Hr0". (* [comment removed for export] *)
Lemma regs_ok_by_index : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "PE,$5.Psr,(6.$7.)PR,(8.&5.(1.&40.))P,Pi,$9.P,(:.R1.#20.)(;.(1.&40.)(<.R3.(=.(1.&5.)R2.$>.(2.&5.=$3.)))(?.R5.(=.$7.R2.R4.(10.=))))(11.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Record pn_memA (sp0 : word) (w : Z) (M : word -> option byte) (can : word) : Prop := PN_MEM {
  pn_win : forall a : word, (bv_unsigned sp0 - 4096 <= bv_unsigned a < bv_unsigned sp0)%Z -> wview RSEGS M a <> None;
  pn_ro  : forall a : Z, (0x10000 <= a < 0x0f1000)%Z -> M (Z_to_bv 64 a) = None;
  pn_flags : rdn RSEGS M (Z_to_bv 64 0x0fa578) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  pn_wend  : rdn RSEGS M (Z_to_bv 64 0x0fa598) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65d5a0));
  pn_wpos  : rdn RSEGS M (Z_to_bv 64 0x0fa5a0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 w));
  pn_bsz   : rdn RSEGS M (Z_to_bv 64 0x0fa5d8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  pn_lock  : rdn RSEGS M (Z_to_bv 64 0x0fa604) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  pn_lbf   : rdn RSEGS M (Z_to_bv 64 0x0fa608) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  pn_inited : rdn RSEGS M (Z_to_bv 64 0x10a6d8) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1));
  pn_ric    : rdn RSEGS M (Z_to_bv 64 0x10a6d9) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1));
  pn_gric   : rdn RSEGS M (Z_to_bv 64 0x0f69b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a6d9));
  pn_cf     : rdn RSEGS M (Z_to_bv 64 0x0f5e40) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x19b528));
  pn_chk    : rdn RSEGS M (Z_to_bv 64 0x19b57c) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1));
  pn_got    : rdn RSEGS M (Z_to_bv 64 0x0f5e50) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1099f8));
  pn_sb     : rdn RSEGS M (Z_to_bv 64 0x1099f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000));
  pn_rvp    : rdn RSEGS M (Z_to_bv 64 0x0f7bc0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0ea30c));
  pn_rvfp   : rdn RSEGS M (Z_to_bv 64 0x0f7bc8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0e71fc));
  pn_rmc    : rdn RSEGS M (Z_to_bv 64 0x0f7cc8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0ea9c0));
  pn_rms    : rdn RSEGS M (Z_to_bv 64 0x0f7cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0eadc4));
  pn_shf    : rdn RSEGS M (Z_to_bv 64 0x7fffaad8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  pn_shb    : rdn RSEGS M (Z_to_bv 64 0x800c3a30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  pn_shs    : rdn RSEGS M (Z_to_bv 64 ((bv_unsigned sp0 - 912) / 8 + 0x7fff8000 - ((bv_unsigned sp0 - 912) / 8 + 0x7fff8000) mod 8)) 8
                = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  pn_g88    : rdn RSEGS M (Z_to_bv 64 0x0f5e58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a6e8));
  pn_g90    : rdn RSEGS M (Z_to_bv 64 0x0f5e60) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a6f0));
  pn_g98    : rdn RSEGS M (Z_to_bv 64 0x0f5e68) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a6e0));
  pn_kmb    : rdn RSEGS M (Z_to_bv 64 0x10a6e8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  pn_kme    : rdn RSEGS M (Z_to_bv 64 0x10a6f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  pn_khe    : rdn RSEGS M (Z_to_bv 64 0x10a6e0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff));
  pn_cgot   : rdn RSEGS M (Z_to_bv 64 0x0f6ae0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65cad0));
  pn_can    : rdn RSEGS M (Z_to_bv 64 0x65cad0) 8 = Some (word_to_le_bytes 8 can);
  pn_buf    : forall a : word, (0x65d1a0 <= bv_unsigned a < 0x65d1a0 + 1032)%Z -> wview RSEGS M a <> None
}.

(* [comment removed for export] *)
Record pn_postA (sp0 : word) (w : Z) (M M' : word -> option byte) : Prop := PN_POSTA {
  pnp_agree : forall x : word,
      ~ (bv_unsigned sp0 - 4096 <= bv_unsigned x < bv_unsigned sp0)%Z ->
      ~ (0x0fa578 <= bv_unsigned x < 0x0fa57c)%Z ->
      ~ (0x0fa5a0 <= bv_unsigned x < 0x0fa5a8)%Z ->
      ~ (w <= bv_unsigned x < w + 2)%Z -> M' x = M x;
  pnp_munch : munch [((bv_unsigned sp0 - 4096)%Z, (bv_unsigned sp0)%Z); (0x0fa578%Z, 0x0fa57c%Z); (0x0fa5a0%Z, 0x0fa5a8%Z); (w, w + 2)%Z] M M';
  pnp_grows : mem_grows M M';
  pnp_wmono : wmono RSEGS M M';
  pnp_flags : rdn RSEGS M' (Z_to_bv 64 0x0fa578) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  pnp_wpos  : rdn RSEGS M' (Z_to_bv 64 0x0fa5a0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)));
  pnp_b0    : rdn RSEGS M' (Z_to_bv 64 w) 1 = Some [Z_to_bv 8 48];
  pnp_b1    : rdn RSEGS M' (Z_to_bv 64 (w + 1)) 1 = Some [Z_to_bv 8 10]
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
Lemma grows_of_rst : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "PD,P,(1.&40.)$12.PE,$5.PM,P,(1.&40.)(13.(1.&8.))PM',P,(1.&40.)(13.(1.&8.))Plog,(6.$14.)P,(;.P,(1.&40.)(13.(1.&8.))(15.R5.R2.)(16.R4.(15.R5.R3.)R1.))P,Pa,(1.&40.)P,(;.$12.A1.R7.R1.$17.)(;.(13.(1.&8.))A1.R5.R2.A1.R6.R2.)(18.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros D E M M' log EQ OUT x Hx. destruct (D x) eqn:Dx.
  - pose proof (mem_denot_grows E (restrict D M) log x) as G. rewrite <- EQ in G.
    rewrite !(restrict_in D _ _ Dx) in G. apply G. exact Hx.
  - rewrite (OUT x Dx). exact Hx.
Qed.

Section PN.
  (* [comment removed for export] *)
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable KI : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000%Z.
  Hypothesis K_halted : forall mo, KI mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "Pmo,$19.Pacc,(6.(1:.(1.&40.)$9.))P,A1.VKI,R2.P,(1;.VAL,VCS,R2.)(1<.$19.Lmo',$19.(1=.(;.(13.$19.)(1>.R5.R4.)(1?.$19.R1.))(1=.A1.VKI,R1.(20.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "Pmo,$19.Pmo',$19.P,A1.VKI,R2.P,(;.$21.(22.R2.)(22.R3.))P,(;.(6.(1:.(1.&40.)(1.&40.)))(23.R3.)(23.R4.))P,(;.(6.(1.&40.))(24.R4.)(24.R5.))P,(;.(13.(1.&40.))(25.R5.)(25.R6.))A1.VKI,R6.")
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
  Hypothesis FM : pn_memA sp0 WP M can.

  (* [comment removed for export] *)
  Let SSW : Z := ((bv_unsigned sp0 - 912) / 8 + 0x7fff8000 - ((bv_unsigned sp0 - 912) / 8 + 0x7fff8000) mod 8)%Z.

  (* [comment removed for export] *)
  Let D : word -> bool := Dimg [(bv_unsigned sp0 - 4096, bv_unsigned sp0)%Z; (0x7fffaad8, 0x7fffaae0)%Z; (0x800c3a30, 0x800c3a38)%Z; (SSW, SSW + 8)%Z].

  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L11799440607.32L14237735119.35L15515289822.35L41954718695.35L45367718360.35L50539368496.33L52538284047.30L56697058689.35L60918251839.29L61028779249.33L61028779894.32L61028780023.31L61034932151.35L61338975526.36L63368316331.33L63368316460.32L63368316718.30L63374425370.28L63374621462.2900000500H00I00[00h00m01701F01P01U01Z01_01d02302802=02B02G02LS3sp0S3sp04SPlo2H12H22H4FS3sp04SPlo1H2H22H3S3sp04SPlo2H4S3sp0S3sp04SPhiS3sp04SPlo1H2H3S3sp04SPloS3sp0S3sp0S3sp0S3sp0S3sp04SPlo1q2H5S3sp0S3sp0S3sp0S3sp0S3sp0". (* [comment removed for export] *)
  Lemma SSW_range : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "(1=.(26.(27.+7???8000.(28.(29.(2:.&40.Vsp0,)+1000.)+8.))VSSW,)(1=.(26.(27.VSSW,+8.)(27.+7???8000.(28.(2:.&40.Vsp0,)+8.)))(1=.(;.$2;.(2<.VSSW,+8.)=)(1=.(26.+7???8000.VSSW,)(26.(27.VSSW,+8.)(2=.+2.+2>.))))))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L14904356608.38L24890867569.42L5268879960.38 L60692804685.43L61028780023.40L61028787006.38L63368316460.41L63368316718.39L6708175616.38 L67812584585.3800000F00O00Z01C01L01U01^01g02=02KS3sp04SPlo3SSW2S41z2HzS3sp03SSWS3sp03SSW1zS3sp04SPlo3SSW2S12S22S41z2Hz2H02H12H23D16S3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo3SSW2S41z2HzS3sp03SSW1z2Hz". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L1546421142.35 L27132502422.35L3891981915.35 L60918251839.3500000900B00N00\S3sp03SSWS3sp03SSWS3sp03SSW2S4S3sp04SPlo3SSW". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L27134605540.31L4356861293.31 L59265415967.3100000900G00PS3sp03SSWS3sp03SSW1z2HzS3sp03SSW". (* [comment removed for export] *)
  Lemma D_shf : DcovZ D 0x7fffaad8 0x7fffaae0.
  Proof. intros z Hz. unfold D. eapply Dimg_cov; [right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L1548524260.31 L51648552223.31L8554424685.31 00000900B00PS3sp03SSWS3sp03SSWS3sp03SSW1z2Hz". (* [comment removed for export] *)
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
  Lemma ssw_denot : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "(;.$2;.(2>.VE,(2?.(30.$31.(30.$32.(30.$33.(30.$32.(34.#0.)(10.-390.))(10.+3.))(10.+7???8000.))(10.-8.))=))VSSW,)")
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "01N0?L11617837940.71L12106940429.71L12212799894.71L12389825151.71L12405253876.77L12664409869.71L13248579327.71L13482121606.71L14054083309.75L14497401878.71L15441563148.71L1550781718.71 L1754068045.71 L17543312104.73L18433691966.71L18614228816.71L18926596374.71L21592273281.75L2181476037.71 L21925619677.71L21988997858.71L22523925200.71L22606967693.71L23160250867.71L2431328725.74 L24990120086.71L25240541541.70L25274003823.71L25500362902.71L2562851341.71 L27136798486.71L27313314277.71L27354698513.71L27630313238.71L27849931296.71L28436469133.71L29435324237.71L31327315070.74L31394611222.71L32648418366.77L32706165901.71L32873232769.75L32959583144.71L33671131928.71L34019894934.71L3509085078.71 L3829630897.74 L39512977622.71L40255458317.71L42213366934.71L42354307853.71L43032411789.71L44351119757.71L44512580374.71L44749504269.71L4504975677.74 L47630204329.71L48463797005.71L48557361648.71L48623478351.71L5007085009.71 L50087589837.71L51241048726.71L51518472845.71L52455603213.71L52877482262.71L53517092650.71L53519161933.75L54247728652.71L54969596045.71L55005286294.71L55662616861.75L55847531981.71L5639034390.71 L56861382341.71L58370583382.71L58963467661.71L5928693697.71 L61062299789.71L61340137101.71L62677777999.71L6277377549.71 L64035337622.71L64204637590.71L64793603213.71L65500100630.71L65730371853.71L66334607382.71L67631326282.75L68056809635.71L68077457517.71L725126413.71  L7783613590.71 L9913584406.71 00000100:00C00D00d00m00n01701W01`01i02202;02I02J02K02T02d02m03603D03E03N03O03\03e04404=04F04O04X04f05405=05>05G05P05k06406T06]06m06n07707@07I07Z07c07l08508>08G08P08Y08b09109209;09<09=09P09Y09b09k0:40:=0:F0:Q0:Z0:c0:l0;G0;P0;Y0;b0;k0<40<=0<F0<O0<P0<Y0<b0<k0=40==0=F0=O0=_0=h0>10>:0>C0>LFS3sp03SSWS3sp03SSWFS3sp04SPlo3SSW2S41d1m2Hd2Hm1x2HxS3sp03SSWFS3sp03SSWS3sp04SPlo3SSW1H2H02S41d1m2Hd2HmS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW1i2HiFFS3sp03SSWS3sp03SSW1d1m2HdS3sp03SSWS3sp03SSWS3sp04SPhi3SSWFS3sp03SSWFS3sp03SSW1n1BS3sp03SSWS3sp03SSW2S42S5S3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPhi3SSWS3sp04SPlo3SSWS3sp03SSWFS3sp03SSWS3sp03SSWS3sp04SPlo3SSW2S43off1n1B1CS3sp03SSWS3sp04SPlo3SSW2S41d1m2Hd2Hm1x2HxS3sp03SSWS3sp03SSW1d1m2HdFS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW3off1n1CS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW3off1AFS3sp03SSWFFS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW1mS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo3SSW2H02S41d1m2HmS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWFS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW1d1m2HmS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW". (* [comment removed for export] *)
  Lemma know_okP1 : know_ok RSEGS E M (kn_PN WP).
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal. pose proof SSW_range as (S1 & S2 & S3 & S4 & S5).
    destruct FM.
    assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
    { intros off n A B C. apply flat_abs0; lia. }
    assert (FSH : flat E (SA (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 0) (ELit (-912))) (ELit 3)) (ELit 2147450880)) (ELit (-8))) 0) 8).
    { unfold flat. rewrite ssw_denot. clearbody SSW. lia. }
    unfold know_ok, kn_PN.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    all: try (split; [lia|]; split; [apply FL; lia|]; rewrite adenot_lit0; cbn [edenot]; assumption).
    all: first
      [ (* [comment removed for export] *) split; [lia|]; cbn [edenot]; evs; assumption
      | (* [comment removed for export] *) cbn [edenot]; evs; lia
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot]; evs; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off]; cbn [edenot]; evs;
        apply store_ok_of_all; rewrite u_small by lia; [lia|]; intros x Hx; apply pn_win0; lia
      | (* [comment removed for export] *) split; [lia|]; split; [lia|]; intros i Hi; apply pn_ro0; lia
      | (* [comment removed for export] *) split; [lia|]; split; [exact FSH|]; rewrite (adenot_of_estart _ FSH), ssw_denot; cbn [edenot]; exact pn_shs0
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia;
        first [ apply store_ok_data; rewrite u_small by lia; lia
              | apply store_ok_of_all; rewrite u_small by lia; [lia|]; intros x Hx; apply pn_buf0; lia ] ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L13450929509.3100000BS3sp04SPlo3SSW1E1H". (* [comment removed for export] *)
  Lemma ssw_denot' : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "(;.$2;.(2:.&40.(?.VE,(30.$31.(30.$32.(30.$33.(30.$32.(34.#0.)(10.-390.))(10.+3.))(10.+7???8000.))(10.-8.))))VSSW,)")
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
  Lemma rdn_of_rst : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "PMM,P,(1.&40.)(13.(1.&8.))Pa,(1.&40.)Pn,$9.Pbs,(6.(1.&8.))P,(;.(13.(6.(1.&8.)))(35.$36.(15.VD,R4.)R3.R2.)(1?.(6.(1.&8.))R1.))P,(26.(27.(2:.&40.R4.)(37.R3.))(2=.+2.+40.))P,(38.VD,(2:.&40.R5.)(27.(2:.&40.R5.)(37.R4.)))(;.(13.(6.(1.&8.)))(35.$36.R7.R6.R5.)(1?.(6.(1.&8.))R4.))")
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
  Lemma memset_align_false' : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "Px,$2;.P,(1=.(26.=R1.)(39.R1.(2=.+2.+40.)))(;.$12.(3:.&40.(3;.&40.(3<.(2:.&40.(3;.&40.(3=.(2:.&40.(3;.&40.+28.))(2:.&40.(3;.&40.R2.)))))(2:.&40.(3;.&40.+?.))))(3;.&40.=))$17.)")
(* [comment removed for export] *).
  Proof.
    intros x Hx. rewrite (unsigned_lit 40), (unsigned_lit 15), (unsigned_lit x) by lia.
    rewrite unsigned_lit by (apply lor40_bound; lia). apply memset_align_false. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L36108758349.32L52514167674.32L5744833530.32 L8443612310.32 00000>00G00U00cS3sp03SSW1x2HxS3sp03SSWS3sp03SSW1x2HxS3sp03SSW1x2Hx". (* [comment removed for export] *)
  Lemma not_ltu1_false : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "Px,$2;.P,(1=.(26.=R1.)(39.R1.(29.(2=.+2.+40.)+1.)))(;.$12.(3>.&40.(3;.&40.(3?.(2:.&40.(3;.&40.R2.))(2:.&40.(3;.&40.-1.))))(3;.&40.+1.))$17.)")
(* [comment removed for export] *).
  Proof.
    intros x Hx. rewrite (unsigned_lit x) by lia. replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z by reflexivity.
    rewrite zb_lxor_ones by lia. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma alu_add_zlit : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "Px,(1.&40.)Pk,$2;.P,(1=.(26.=(27.(2:.&40.R2.)R1.))(39.(27.(2:.&40.R2.)R1.)(2=.+2.+40.)))(;.(1.&40.)(40.$32.R3.(3;.&40.R2.))(3;.&40.(27.(2:.&40.R3.)R2.)))")
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "02m0?L10826441387.41L11193687435.41L11924528617.56L13240721355.41L14129935339.41L14330444123.41L14610208971.41L16173143547.41L16462646590.50L16872186827.41L17377553579.41L17572006411.41L17579660059.41L18188861963.41L18552378747.41L18589501307.41L18804367755.41L18857354187.41L19048549051.41L19365070379.41L19468000939.41L196596427.41  L20409812011.41L20474265771.41L20502771267.55L20510080811.41L21146798635.41L21264259627.41L21374136478.50L21736677547.41L22061491723.41L22082848651.41L22287311995.41L22684626731.41L22711026347.41L22837808587.41L23967823563.41L24129266859.41L24873585595.41L25271923445.50L25946293387.41L26322948491.41L26661465771.41L2669446587.41 L26720341451.41L26852150827.41L27352565217.55L27455439227.41L27628243430.55L27685351787.41L2902180395.41 L30037890763.41L30089557835.41L30555470859.41L30762167099.41L30934567723.41L31066596187.41L31385119883.41L31608280619.41L31754126635.41L31788425275.41L32114586939.41L32332327451.41L323538539.41  L32535476907.41L32648425590.56L32671072027.41L33148332573.55L33445831387.41L33457347083.41L33501811931.41L34017833062.55L34301840819.55L34345144715.41L34374086283.41L34454164011.41L35003615352.55L35018296523.41L35578157003.41L36192280235.41L36369185675.41L36406570379.41L3698626699.41 L37180749275.41L37322114603.41L37502765227.41L38165856267.41L38675390667.41L38789999883.41L39091829931.41L39240224459.41L39255630265.41L39330024847.41L39377698251.41L39954007435.41L40455025867.41L40935341947.41L40956476715.41L41274342971.41L41694684747.41L41831086107.41L4232295563.41 L43600488459.41L43762152459.41L44109465803.41L44133811659.41L44287219963.41L44320973771.41L44421487467.41L45252260139.41L45409080475.41L45661894811.41L45739324585.55L45874800581.51L46334012555.41L46800722667.41L46988748059.41L47145843499.41L47414013387.41L47548156299.41L47599307723.41L47631495339.41L47950179547.41L48038302347.41L48091327752.43L4834089227.41 L48512515083.41L49112986059.41L49856512683.41L50054782654.50L50225397467.41L50535656939.41L51358398475.41L51497945483.41L52731989291.41L52889832619.41L53172474325.50L53519158063.41L53865434635.41L54566539083.41L54601329275.41L55185993771.41L55922418347.41L56186638235.41L57126892827.41L57336431787.41L57515297422.50L57521871819.41L57900565899.41L58405516491.41L59198719275.41L5926612059.50 L59504369835.41L59922352443.41L60202056395.41L60381504203.41L60696129547.41L60880961211.41L60887978235.41L61146674987.41L62185768357.41L62207793979.41L62235073629.55L62672136992.55L62797201483.41L62855468331.41L63048207147.41L63580305131.41L63873326731.41L64019398187.41L64938969259.41L65881685675.41L66185206315.41L67073939035.41L67183782059.41L67502027782.55L67653482985.55L67923741099.41L68047493803.41L68150193147.41L68249901739.41L7076638299.41 L711050699.41  L775027675.41  L820234155.41  L8605718799.41 L9046793899.41 L9048335979.41 L9671300507.41 00000C00V00m01601?01H01[01d01m02@02S02f02o03B03K03T03g04:04C04V04_04h05105D05R05e06806K06T06]06f06o07807K07^07g08:08M08V08_09209E09X09a09j0:=0:K0:T0:]0:f0;90;L0;U0;h0<10<:0<C0<V0<i0=<0=E0=N0=W0=`0>30>A0>J0>S0>\0>o0?80?A0?O0?b0@50@H0@Q0@d0@m0A@0AI0AR0A[0Ad0B70BJ0B]0C00C90CL0C_0Cn0D70DJ0D]0E00E90EL0EU0E^0Eg0F:0FM0F`0G30GF0GO0Gb0Gk0H40H=0HF0HT0Hg0I00I90IB0IU0Ih0J;0JN0JW0J`0K30KA0KJ0K]0L00LC0LL0LU0L^0M10M:0MM0M`0Mi0N20NE0NN0NW0N`0O30O<0OE0OX0Oa0P40PG0PZ0Pm0Q60QI0QR0Q[0Qn0R70R@0RI0R\0Ro0S80SA0SO0SX0Sk0T>0TG0TZ0Tm0U@0US0Uf0Uo0VB0VK0VY0Vb0W50W>0WG0WP0Wc0Wl0X50X>0XQ0XZ0XcS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSW1x2H02N22N32N4S3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSW1x2O4S3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSW1x2H0S3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSW1x2O1S3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSW2S42S5S3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW1x2O3S3sp01R3SSW2RC1i2HiS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSW1z2HzS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp04SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSW1x2O2S3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp04SPlo4SPhi3SSWS3sp03SSWS3sp03SSW". (* [comment removed for export] *)
  Theorem printfNA : ltac2:(CDefT.buildp (gd_tbl_A_printfN2 ()) "PKK,$41.P,Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PM',P,(1.&40.)(13.(1.&8.))Pmo',$19.P,(42.Vsp0,$43.VM,R2.)P,A1.VKI,R2.P,(20.Vmodel,R3.)(44.$36.(45.(46.(47.(3;.&40.+9748<.)Vsp0,(3;.&40.+10800.)(3;.&40.+63<:90.)R14.R13.R12.(<.VR,(2.&5.+8.$3.))(<.VR,(2.&5.+9.$3.))R11.R10.R?.R>.R=.R<.R;.R:.(<.VR,(2.&5.+12.$3.))(<.VR,(2.&5.+13.$3.))(<.VR,(2.&5.+14.$3.))(<.VR,(2.&5.+15.$3.))(<.VR,(2.&5.+16.$3.))(<.VR,(2.&5.+17.$3.))(<.VR,(2.&5.+18.$3.))(<.VR,(2.&5.+19.$3.))(<.VR,(2.&5.+1:.$3.))(<.VR,(2.&5.+1;.$3.))R9.R8.R7.R6.)(48.&5.(1.&40.))(3;.&40.+9748<.)(3;.&20.=)(49.(1.&40.))R5.(4:.$36.))R4.)R15.)(44.$36.(45.(4;.$4<.VR,(3;.&40.+97538.)VM,(4:.$36.))Vmodel,)R2.)")
(* [comment removed for export] *).
  Proof.
    intros KK HC.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SSW_range as (S1 & S2 & S3 & S4 & S5).
    pose proof regs_okP1 as HR. pose proof know_okP1 as HK.
    (* [comment removed for export] *)
    run_blockA3 RRUN KND FUEL_PF STOPS_PN scrN 34%nat true covtac.
    all: try solve_sc.
    lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into RC; rename Mn into MD end.
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
                         first [ change (ev _ n) with sp0; reflexivity
                               | change (ev _ n) with (ev E n); rewrite (evP1_junk (n - 1)) by lia;
                                 etransitivity; [reflexivity|]; reflexivity ] end) ] ]
        end. }
    change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
    apply HC; [ | exact HKmo | exact MM ].
    (* [comment removed for export] *)
    assert (AG : forall x : word,
                 ~ (bv_unsigned sp0 - 4096 <= bv_unsigned x < bv_unsigned sp0)%Z ->
                 ~ (0x0fa578 <= bv_unsigned x < 0x0fa57c)%Z ->
                 ~ (0x0fa5a0 <= bv_unsigned x < 0x0fa5a8)%Z ->
                 ~ (WP <= bv_unsigned x < WP + 2)%Z -> MD x = M x).
    { intros x N1 N2 N3 N4. pose proof (u64_range x). unfold WP in N4.
      destruct (D x) eqn:Dx.
      - rewrite <- (restrict_in D MD x Dx). rewrite EQM. rewrite mem_denot_out; [apply (restrict_in D M x Dx)|].
        apply (log_out_inW _ 0 (-4096) 0 [(0x0fa578, 0x0fa57c); (0x0fa5a0, 0x0fa5a8); (0x65d1a2, 0x65d1a2 + 2)]%Z); [vm_compute; reflexivity | evs; lia | evs; lia | repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia| split; [lia| first [intros ?; apply N2; lia | intros ?; apply N3; lia | intros ?; apply N4; lia]]]) | evs; intros ?; apply N1; lia]. (* [comment removed for export] *)
      - exact (OUT x Dx). }
    assert (GR : mem_grows M MD) by (eapply (grows_of_rst D); [exact EQM | exact OUT]).
    split.
    - exact AG.
    - intros x Hout. cbn [outside] in Hout. destruct Hout as (O1 & O2 & O3 & O4 & _). apply AG; unfold WP in *; lia.
    - exact GR.
    - apply mem_grows_wmono. exact GR.
    - krd HK 0x0fa578%Z 4%nat F0. exact F0.
    - krd HK 0x0fa5a0%Z 8%nat F40. rewrite F40. reflexivity.
    - unfold WP. first [ krd HK 0x65d1a0%Z 1%nat FB; rewrite FB; reflexivity
                       | krd HK 0x65d1a2%Z 1%nat FB; rewrite FB; reflexivity
                       | krd HK 0x65d1a4%Z 1%nat FB; rewrite FB; reflexivity ].
    - unfold WP. match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => let a' := eval vm_compute in a in change a with a' end.
      first [ krd HK 0x65d1a1%Z 1%nat FB1; rewrite FB1; reflexivity
            | krd HK 0x65d1a3%Z 1%nat FB1; rewrite FB1; reflexivity
            | krd HK 0x65d1a5%Z 1%nat FB1; rewrite FB1; reflexivity ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PN.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

