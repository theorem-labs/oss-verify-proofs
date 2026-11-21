(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed Forall_one', LM_rdn, LM_wbytes8 and 63 more; added Hrdr; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Ub0StdioWrite.v, 470 lines within its lines 28-731. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0Exit_run1. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module Ns0StdioDefs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.SumWalkTac.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0Exit_run1. Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0ExitBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0Exit_run1.      (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
  swf_wpos  : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  swf_fd    : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
  swf_buf   : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swf_bsz   : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.

(* [comment removed for export] *)
Definition ssp_cells (mem : word -> option byte) (can : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0xc5ab8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf8ac0))
  /\ rdn RSEGS mem (Z_to_bv 64 0xf8ac0) 8%nat = Some (word_to_le_bytes 8 can).

(* [comment removed for export] *)
Record sw_post (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
       (mem' : word -> option byte) : Prop := {
  swp_agree : forall x : word,
      ~ (su - 112 <= bv_unsigned x < su)%Z ->
      ~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
      ~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
      mem' x = mem x;
  swp_grows : mem_grows mem mem';
  swp_wend  : rdn RSEGS mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
  swp_wpos  : rdn RSEGS mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swp_wbase : rdn RSEGS mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.

(* [comment removed for export] *)
Lemma sw_post_rdn : forall mem su f bufp bufsz mem' (a : word) n bs,
  sw_post mem su f bufp bufsz mem' ->
  rdn RSEGS mem a n = Some bs ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a + Z.of_nat n <= su - 112 \/ su <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 32 \/ f + 48 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 56 \/ f + 64 <= bv_unsigned a)%Z ->
  rdn RSEGS mem' a n = Some bs.
Proof.
  intros mem su f bufp bufsz mem' a n bs P H Hnw D1 D2 D3.
  rewrite (rdn_ext RSEGS n mem' mem a Hnw); [exact H|].
  intros x Hx. apply (swp_agree _ _ _ _ _ _ P); lia.
Qed.

Lemma sw_post_store_ok : forall mem su f bufp bufsz mem' (a : word) n,
  sw_post mem su f bufp bufsz mem' ->
  store_ok RSEGS mem a n = true -> store_ok RSEGS mem' a n = true.
Proof. intros mem su f bufp bufsz mem' a n P H. eapply store_ok_mono; [apply (swp_grows _ _ _ _ _ _ P) | exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record exit_common (regs : bvmap 5 word) (mem : word -> option byte)
       (sp tp code : word) (tid : Z) (wp2 rp2 : word) : Prop := {
  ec_sp   : getr regs 2 = sp;
  ec_tp   : getr regs 4 = tp;
  ec_a0   : getr regs 10 = code;
  ec_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
  ec_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
  ec_sok  : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
  ec_tplo : (168 <= bv_unsigned tp)%Z;
  ec_tphi : (bv_unsigned tp <= 4294967296)%Z;
  ec_tid  : (0 < tid < 2147483648)%Z;
  (* [comment removed for export] *)
  ec_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  (* [comment removed for export] *)
  ec_lock : rdn RSEGS mem (Z_to_bv 64 0xf8ab8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_fe   : rdn RSEGS mem (Z_to_bv 64 0xc5ac0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xbf9f0));
  ec_fs   : rdn RSEGS mem (Z_to_bv 64 0xc5ac8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xbf9e8));
  ec_fa   : rdn RSEGS mem (Z_to_bv 64 0xbf9e8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x38b9c));
  (* [comment removed for export] *)
  ec_comp : rdn RSEGS mem (Z_to_bv 64 0xc6e18) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (Z_to_bv 64 0xc5950) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa90ec));      (* [comment removed for export] *)
  ec_dso  : rdn RSEGS mem (Z_to_bv 64 0xc6ae8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc6ae8));      (* [comment removed for export] *)
  ec_ax   : exists ax : axv, atexit_cells mem ax;      (* [comment removed for export] *)
  ec_cb   : rdn RSEGS mem (Z_to_bv 64 0xd6e24) 1%nat = Some [Z_to_bv 8 0];      (* [comment removed for export] *)
  ec_g2   : rdn RSEGS mem (Z_to_bv 64 0xc5958) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  (* [comment removed for export] *)
  ec_err  : file_clean mem 0xc6bd0 wp2 rp2
}.

(* [comment removed for export] *)
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xae4d4));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0xf8ac8 <= wb < wp /\ wp <= 0xfa000)%Z;
  sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
  sp_max   : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
  sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
  sp_ssp   : ssp_cells mem can
}.

(* [comment removed for export] *)
Definition exit_pre (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
           (code : word) (pending : list byte) : Prop :=
  exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
    exit_common regs mem sp tp code tid wp2 rp2
    /\ m_halted model = None /\ m_vm_lazy model = []
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0xc6cc0 wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
              (* [comment removed for export] *)
              /\ m_channel_reader model = true) ).
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Ns0StdioDefs.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0143 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01058SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z6of_natK46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula07I46Stdlib9micromega7EnvRing5PExpr00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init9Datatypes4list00K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega:ZMicromega=Zeval_formulaC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z6shiftlC49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00C49OSSVerify5KrLib8PropExec5v_xorC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run17mem_sw1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:RdnPeelKit7wchainZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_oki59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs7sw_file00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs9ssp_cellsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C49OSSVerify5KrLib8PropExec9step_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC59OSSVerify5KrLib7Mh_00387SeqExec:step_sd_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:step_auipcC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib7Mh_0055:RdnPeelKit6wch_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:RdnPeelKit?rdn_wchainZ_outC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7step_ldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387WalkTac=wf_getr_chainC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_xorC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_sltuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4c_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib7Mh_0055:SumWalkTac6c_eq_ZC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_jal_x0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:SumWalkTac?bytes_le_to_Z_4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7step_lwC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:SumWalkTac:v_lw_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run1<sltu0_xor_neC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run17v_add_ZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run17v_sub_ZC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega6VarMap4findC46Stdlib9micromega5Tauto7eval_bfC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses5mkrelI59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic3and01K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes3nat00C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae498C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae498C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae498C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae49cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae49cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae49cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4c0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4c0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4c0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4c4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4c4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4c4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4c8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4c8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4c8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae4fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae4fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae4fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae500C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae500C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae500C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae504C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae504C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae504C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae50cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae50cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae50cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae510C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae510C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae510C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae514C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae514C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae514C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae518C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae518C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae518C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae51cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae51cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae51cC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:SumWalkTac9c_eq_reflC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run1<sltu0_xor_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387WalkTac9v_add_0_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8sub_diagC59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae508C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae508C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae508C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_subwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run2;sw_regs_butC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5c_ltsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run1;c_lts_pos_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_blt_ftC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_andC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geC49OSSVerify5KrLib8PropExec<step_bgeu_tkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_subwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7sub_0_rc59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run1@v_subw_small_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run19v_add_ZZ'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run18v_add_wZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run19v_and_0_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387WalkTac9v_add_0_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run17sltu_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5c0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5c0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5c0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5c4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5c4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5c4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5c8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5c8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5c8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae57cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae57cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae57cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae580C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae580C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae580C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae584C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae584C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae584C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae588C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae588C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae588C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae58cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae58cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae58cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae590C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae590C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae590C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae594C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae594C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae594C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae598C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae598C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae598C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae59cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae59cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae59cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5a4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC49OSSVerify5KrLib8PropExec<step_bgeu_ftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run1:v_and_m1_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run17sltu_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058;Ns0ExitBase=store_ok_dataC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_bne_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec<step_jalr_x0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run27mem_sw2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae52cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae52cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae52cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae530C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae530C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae530C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae534C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae534C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae534C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae538C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae538C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae538C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae53cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae53cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae53cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae540C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae540C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae540C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae544C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae544C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae544C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae548C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae548C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae548C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae54cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae54cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae54cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae550C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae550C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae550C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae554C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae554C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae554C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae558C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae558C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae558C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae55cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae55cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae55cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae560C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae560C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae560C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae564C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae564C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae564C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae568C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae568C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae568C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae56cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae56cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae56cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae570C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae570C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae570C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae574C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae574C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae574C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae578C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae578C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae578C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite<skipn_app_leC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List<length_skipnc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite<skipn_app_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega7EnvRing3Pol01K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite2RIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite2LMC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib7Mh_00385Hoare3at_C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib5Lists4List:length_appc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite;LM_store_okC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat;le_gt_casesc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite6LM_rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run2:sw_retry_aC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite:LM_wbytes8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite6RI_butC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C46Stdlib5Lists4List=skipn_all_iffC47Corelib4Init5Logic5proj1C46Stdlib9micromega;ZifyClasses9not_morphC59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9rdn_skipnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC59OSSVerify5KrLib7Mh_00949LibWritev=word_to_nat_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idc59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run28sw_c2_eqC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite:finish_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite7u_at_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run28sw_c2_neC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:LibWritevX@rz_writev2_wallXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run2:sw_retry_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite5loop1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:LibWritevX@rz_writev1_wallXC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec?rdn_wbytes_hit8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_mstepsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007E_ae5a8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite8pc_ae55cC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyi59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs7sw_post00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00949LibWritev>u64_roundtrip'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite=sw_post_of_LMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite5loop2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite7LM_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decc59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run1;sw_enter_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run28sw_c1_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:LibWritevX@rz_writev1_zeroXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run28sw_c1_neC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run18sw_enterC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae520C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae520C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007E_ae520C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite8pc_ae4d4C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall;Forall_one'C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z3lebK46Stdlib9micromega5Tauto8GFormula01C47Corelib5Lists7ListDef3seqK69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6eqb_eqK69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib5Arith8PeanoNat3Nat3eqbc59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall<lit_even_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX29split_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbK69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCallFlength_sr_after_call_jC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive:kblob_findC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_spC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX2:base_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25mkAluC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall8kimg_cutC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC69OSSVerify5KrLib7Mh_00638SymExec23SX28expr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S5elenZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22ebC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX:is_kwr_covC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055<LibKnowFrame8kn_frameC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC47Corelib4Init5Logic7f_equalC47Corelib4Init9Datatypes9andb_propC59OSSVerify5KrLib=SymExec2Sound4SX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eqb_eqC69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall:sr_get_natC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr08C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib=SymExec2Sound4SX2S@base_range_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall?split_lit_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall;kindex_someC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall9flat_abs0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive@kblob_find_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive9kblob_rdnC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib7Mh_01058SymDriveGword_to_le_bytes_of_lezC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs7sw_file01C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC46Stdlib4Bool4Bool8orb_propC59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib7Mh_00638SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun>vals_app_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun9env_agreeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK46Stdlib9micromega5Tauto8GFormula02C59OSSVerify5KrLib7Mh_01058SymDrive?regs_after_callC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall=length_sr_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive>sr_vars_lt_nthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun<edenot_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall?nth_sr_upd_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall@nth_sr_upd_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX;regs_ok_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall>kimg_cut_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall>split_lit_varsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall6u_lit0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall>know_ok_frame3C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S;mkAlu_denotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite?ref_stdio_writeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula0:C59OSSVerify5KrLib7Mh_01058SymDrive5kreadC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_srC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall7sc_bufpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall8sc_bufszC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX6kindexC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive9kread_rdnC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto4kind02I69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25two64C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall7SC_KEPTC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00I47Corelib5Lists7ListDef6Forall00K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00849HeapIface8hl_stackC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib3CPmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00556DrvKit7find_nzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib9sub_blockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib8dl_stackC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib9dl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib9dl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib8dl_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_errnoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib8dl_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib3SCmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z;lt_ge_casesc59OSSVerify5KrLib7Mh_01439Ns0DrvLib<sub_block_hzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib2hzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstc59OSSVerify5KrLib7Mh_01439Ns0DrvLibAhz_of_block_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib7Mh_01439Ns0DrvLib9dl_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint04K47Corelib4Init7Decimal4uint09K47Corelib4Init7Decimal4uint08K47Corelib4Init7Decimal4uint0:K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintC59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_windowC1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint0;K47Corelib4Init7Decimal4uint03K59OSSVerify5KrLib7Mh_00556DrvKit:regions_ok01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143;Ns0Drv_defs:IMG_CLIENTC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143;Ns0Drv_defs6IMG_RWC1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint01c59OSSVerify5KrLib7Mh_01439Ns0DrvLib:wseg_6a8b4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib:wseg_6f8b4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib5CPoutC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareI59OSSVerify5KrLib7Mh_00556DrvKit:regions_ok00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03K69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143;Ns0Drv_defs8kn_afterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5kdiffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5summGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs7keep_rdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26s_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25s_logC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5srC0LC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs7srRe_tkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4srRmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4srGaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4srGbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4srGcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4srGdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143;Ns0Drv_defs3MSOC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs3rRaC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4rC0LC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143;Ns0Drv_defs4knC0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5cellRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4knLPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5knLP6C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs3rPaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs6want_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs3rPbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5knLPpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5knRDpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4srPbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4srPaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4srRDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs6rRe_tkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5knRe0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs3rRmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5len_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs6rRe_ftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs7knRe_ftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5cellCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs7srRe_ftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4srGLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs3rGaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5knLPgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs6cap2_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs3rGbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5knGb0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs5knGc0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs3rGcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs3rGdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4srRaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4knRaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs3scRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs3rRbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvG_defs4srRbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4knTcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs:relay_ok_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5wposKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs7keep_pfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00556DrvKit7ksubl_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143;Ns0Drv_defs:keep_allocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4rT00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4rT10C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4rT01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4rT11C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs2rUC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs2rVC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4rLB1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4rLB2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4rLc1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4rLc2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs2rPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs2rQC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs2rRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5rS_tkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5rS_ftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs2rXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs2rYC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs2rZC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4knTeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4sr01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5srTm0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5knLH1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4knV0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4knU0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4sr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4sr10C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs3srVC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs3srRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs6srS_tkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5flag1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4srLBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5flag0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4srP0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5knLr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5knLp1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5knLr2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5knLp2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5knLc1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5knLH2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5knLc2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs3knRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs6flagsKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4knR2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0056<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs4knX0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs3srQC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs3knQC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs3scPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143<Ns0DrvD_defs5dec_xC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs4u_rAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs4u_rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs4u_rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs4u_rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs4u_rEC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs2LXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs4u_rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs4u_rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs4u_rHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs5u_rF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs5u_rG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs5u_rH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs5u_rE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs5u_rF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs5u_rG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs5u_rH4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K4ELinuxProcessSemantics5Riscv5Instr5aluop02c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs5u_srGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs5u_knGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs5u_scGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_srF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_knF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_scF3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_srG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_knG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_scG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_srE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_knE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_scE4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_srG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_knG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0Usage_defs6u_scG4C1?~~~~~~~~~~~~~~~".
Module Ns0StdioWrite_run1.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.LibAtomic OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4e000_4f000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Ns0StdioWrite_run1 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3addC49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3ltbC49OSSVerify5KrLib8PropExec<Z_lxor_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z7lxor_eqC47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec5v_xorC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z>lxor_nilpotentK47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec?bv_signed_smallC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5c_ltsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z8land_0_lC49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions>bv_swrap_smallC49OSSVerify5KrLib8PropExec6v_subwC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Ltac rdn_side_fast := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia_fast.
Local Ltac rdn_solve_fast :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (first [ RdnPeelKit.rdn_peel_many ltac:(idtac; rdn_side_fast) | rdn_peel1 ]; rdn_solve_fast)
  | |- _ => rdn_hyp
  end.
Local Ltac rdn_solve ::= rdn_solve_fast.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma v_sub_Z : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite_run1 ()) ["FPX_1"] "h04__x1h17__arithh24__ffh34__p1h46__sat3h56__sat4h68__varmaph75__with84__x2h92Hah:1zh;1Hh<2H2h=1ah>1bp;2p;1p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004>R0p4p710p8g004\j25Tg0058j28Tg005Sj11Tg0068j1HTg006Vj2XTg0073j26Tg007Oj1QTg007mj1PTg008Pj20Tg0096j2>Tg009`j27Tg00:=j39Tg00:Wj2GTg00;1j2_Tg00;Yj3YTg00<=j1WTg00<]j1VTg00==j2BTg00=[j1UTg00>9j1TTg00>dj2ATg00?Gj2@Tg00?jj1OTg00@Lj2NTg00@nj2MTg00AZj3LTg00B9j4KTg00Bkj1ETg00CJj2<Tg00D3j3FTg00D\j2JTg00EHj3ITg00Ehj1RTg00FFj4STg00Fdj3`Tg00GGj4=Tg00H2j3CTP0j6DTg00Hmj2^Tg00I`j7]Tg00JDj6ZTg00Jhj7[Tg00KLj8\Tg00L0R0f0R1'5p=2g00LNR2f1R3g00LlP1C=p=:P3g00MSR4g00N2R5P5g00NRR6P1g00O2F]p=3P3P4P5P5P6P1EZp=?f2R7P4P5P5P6P3P1F[p=;f3R8P4P5P5P6P7P3P1G\p=4%21R41513'8g00ORR9#1R:#HR;%1:#1#1#1#1R<#HR='XR>,67R?P2P8%Q<R<#PR@10<8RA,><RB,71,0<f4RC/78,0<RD39X:2P2P717C1,0<=9@DX:21787,0<RD,G@10<7RE,><1_;=RF160;%2=160>[[RG%2;RHg00P7RIAY;=3UW9R=%2>\I^9HRHp-0RIg00PSRJ#WRK%VJRL1B23RM%U2RN%T2RO1A20RP1@29R9':,3ORQ1?O85;O%O5R5PQC41NO6R6P1P7g00Q?RRg00Q_RS'G1M17=9RSdAL203CKR0b2b6b7X02W31843%23R4[^02^3IP1f5RSf6RR'5PSPCO3b1b4b5PFPGP=PHg00R?RT#ERU#E,<21<2U1<2T5F25F2g00R^'J=IJKRJPLP21B27P3%R2CSRTPNPOP21@2:R:g00SJRU1A2;=`2<R<C=,3OP5PO1?OC1:9:,3O5;OP5P2P9PUP<C=,3OR<C4C4P6P0b2b6b7X02X82X3I163>RU1537,88P?[[^02^82^3IP1%2SPRPSP8PCO5b1b4b55C7EDPBPFPGP=PHPJPLPTPNPO1:P:,3O1::9,3O5;OP5PQC4P6P0b2b6b7X02X821531,84P4[^02^82P1PSPRPCO3b1b4b5PFPGP=PHPKPLPMPNPOP<P5P<C4P6P0b2b6b7X02161>PU[^02P1PRP8O2b1b4b55C8ED1^AE=9@DeW<W;X>2X=2o"). Qed.

#[using="Type"] Lemma v_add_Z : forall a (l : word), (0 <= a < 2^64)%Z ->
  v_add (Z_to_bv 64 a) l = Z_to_bv 64 (a + bv_unsigned l).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite_run1 ()) ["FPX_1"] "h04__p1h14__x1h22Hah37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91Hh:1ah;1lh<1zp;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004>R0p4p710p8g005Sj10Tg007Oj1WTg007mj1FTg0068j1>Tg006Vj2OTg0073j22Tg0058j26Tg0096j25Tg00T1j24Tg008Pj23Tg00:=j37Tg00:Wj2=Tg00;1j2VTg00;Yj3UTg00<=j1TTg00<]j1NTg00==j2LTg00=[j1KTg00>9j1HTg00>dj2;Tg00?Gj2GTg00GGj4:Tg00JDj6ETg00?jj1DTg00@Lj2CTg00@nj2ITg00AZj3JTg00B9j4BTg00Fdj3ATg00H2j3MTP0j6@Tg00TNj2PTg004\j2QTg00I`j7?Tg00Jhj7RTg00KLj8STg00L0R0f0R1'Qp=1f1R2g00MSR3g00N2R4P4g00NRR5P1g00O2F?p=8f2R6P3P4P4P5P2P1FRp=9f3R7P3P4P4P5P6P2P1GSp=<g00LNR8g00ORR9#0R:#0#0#0#0#0R;#WR<#FR=%12R>%>:R:%>;R;'OR?,22R@'6P8P615<6RA,41,3<147A,3<57=X<815<2,46,3<RA,==13<6RB,5<1V:;RC120:%1;120?[[RD%1:REg00P7RFAU:;2UW2R;%1?\F^2EREp-0RFg00PSRG#TRH%NGRG1L82RI%K8RJ%H8RKP81;80g00Ll1G89R9C:,8KRLPKP3P4P4P5P7EER359K%D4R4PLC<1CK5R5P1P6g00Q?RLg00Q_RM'=1I16=7LMdAJ802CBR0b4b7b8X18W0%11/62P>[^18^0FP1f5R>/2?P>P7O3b3b5b6PCPDP;PEPHPGPIPJPKP8P9g00SJ1;8:=A8<C:,8KR<99K3P4P<C<P5P0b4b7b8X18X0F121?,62P@[^18^0FP1%1>P>P7O3b3b5b65M6E@1PB2=7=AeW9W;W:o"). Qed.

#[using="Type"] Lemma v_add_wZ : forall (b : word) c, (0 <= c < 2^64)%Z ->
  v_add b (Z_to_bv 64 c) = Z_to_bv 64 (bv_unsigned b + c).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite_run1 ()) ["FPX_1"] "h04__p1h14__x1h22Hah37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91Hh:1bh;1ch<1zp;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004>R0p4p710p8g005Sj10Tg007Oj1WTg007mj1FTg0068j1>Tg006Vj2OTg0073j22Tg0058j26Tg0096j25Tg00T1j24Tg008Pj23Tg00:=j37Tg00:Wj2=Tg00;1j2VTg00;Yj3UTg00<=j1TTg00<]j1NTg00==j2LTg00=[j1KTg00>9j1HTg00>dj2;Tg00?Gj2GTg00GGj4:Tg00JDj6ETg00?jj1DTg00@Lj2CTg00@nj2ITg00AZj3JTg00B9j4BTg00Fdj3ATg00H2j3MTP0j6@Tg00TNj2PTg004\j2QTg00I`j7?Tg00Jhj7RTg00KLj8STg00L0R0f0R1'Qp=1f1R2g00MSR3g00N2R4P4g00NRR5P1g00O2F?p=8f2R6P3P4P4P5P2P1FRp=9f3R7P3P4P4P5P6P2P1GSp=<g00ORR8#0R9#0#0#0#0#0R:#WR;#FR<g00LNR=%11R>%>9R9%>:R:'OR?,21R@'6P=P215;7RA/41,3;14A6,3;57<X<=15;6/42,3;RA,=<13;2RB,5;1V9:RC1209%1:120?[[RD%19REg00P7RFAU9:2UW2R:%1?\F^2EREp-0RFg00PSRG#TRH%NGRG1L=2RI%K=RJ%H=RKP=1;=0g00Ll1G=8R8C:,8KRLPKP3P4P4P5P7EER359K%D4R4PLC<1CK5R5P1P6g00Q?RLg00Q_RM'=1I16=7LMdAJ=02CBR0b4b7b8X1=W016>2%12[^1=^0FP1f4R>/2?P>P7O3b3b5b6PCPDP:PEPHPGPIPJPKP=P8g00SJ1;=9=A=;C:,8KR;99K3P4P;C<P5P0b4b7b8X1=X0F162@122?[^1=^0FP1%1>P>P7O3b3b5b65M2E@1P6B=7<AeW9W;W:o"). Qed.

#[using="Type"] Lemma v_add_ZZ' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite_run1 ()) ["FPX_1"] "h07__arithh14__p1h26__sat1h36__sat2h44__x1h52Hah64__ffh78__varmaph85__with91zh:1xh;1yp;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004>R0p4p710p8g005Sj12Tg0068j1;Tg006Vj2DTg0073j23Tg0058j26Tg007Oj1NTg007mj1HTg008Pj21Tg0096j27Tg00T1j24Tg00:=j35Tg00:Wj2@Tg00;1j2WTg00;Yj3VTg00<=j1UTg00<]j1RTg00==j2QTg00=[j1OTg00>9j1MTg00>dj2>Tg00?Gj2KTg00GGj4=Tg00JDj6GTg00?jj1FTg00@Lj2ETg00@nj2ITg00AZj3JTg00B9j4CTg00Fdj3LTg00H2j38TP0j6?Tg00TNj2BTg004\j2PTg00I`j7ATg00Jhj7STg00KLj8TTg00L0R0f0R1'Pp=0f1R2g00MSR3g00N2R4P4g00NRR5P1g00O2FAp=:f2R6P3P4P4P5P2P1FSp=<f3R7P3P4P4P5P6P2P1GTp=9g00LNR8%02R9g00ORR:#2R;#;R<%2;#2#2#2#2R;#;R='DR>,32R?'6R@P8P7%N;R;#HRA11;7RB,7;RC,41,1;f4RD/47,1;RE35X98P8P614D1,1;=5AEX981476,1;RE,@A11;6RF,7;1W<=RG130<%0=130>[[RH%0<RIg00P7RJAV<=2UW5R=%0>\J^5IRIp-0RJg00PSRK#URL%RKRK1Q82RM%O8RN%M8ROP81>80g00Ll1K8:R:C=,:ORPPOP3P4P4P5P7EGR35<O%F4R4PPC91EO5R5P1P6g00Q?RPg00Q_RQ'@1I16=5PQdAJ802CCR0b6b7b8X48W1RQ%01/62P9[^48^1JR9P1f5RP/3>PPP7O3b0b2b3PGPHP=PIPLPKPMPNPOP8P:g00SJ1>8<=L8;C=,:OR;9<O3P4P;C9P5P0b6b7b8X48X1JR0131>,62P?[^48^1JRJP1%0PPPP7O3b0b2b3586E?PCPGPHP=PIPQP9P1f6R9/3>P9PDO3b0b2b3PGPHP=PIP0PJP1%09P9PDO3b0b2b3587E?1BBF=5AEeV@UX;8W:o"). Qed.

#[using="Type"] Lemma sltu0_xor_ne : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z -> a <> b ->
  v_sltu (Z_to_bv 64 0) (v_xor (Z_to_bv 64 a) (Z_to_bv 64 b)) = Z_to_bv 64 1.
Proof.
  intros a b Ha Hb Hne. unfold v_sltu, c_ltu, bv_ltu, v_xor.
  rewrite (u_Z2bv a), (u_Z2bv b), (u_Z2bv 0) by lia.
  pose proof (Z_lxor_range a b Ha Hb) as Hr.
  rewrite u_Z2bv by lia.
  destruct (Z.ltb_spec 0 (Z.lxor a b)) as [Hlt|Hge]; [reflexivity|].
  exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.

#[using="Type"] Lemma sltu0_xor_eq : forall a : word, v_sltu (Z_to_bv 64 0) (v_xor a a) = Z_to_bv 64 0.
Proof.
  intros a. unfold v_sltu, c_ltu, bv_ltu, v_xor. rewrite Z.lxor_nilpotent.
  rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

#[using="Type"] Lemma sltu_ge : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [lia|reflexivity].
Qed.

#[using="Type"] Lemma sltu_lt : forall a b, (0 <= a < b)%Z -> (b < 2^64)%Z ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [reflexivity|lia].
Qed.

#[using="Type"] Lemma c_lts_pos_0 : forall a, (0 <= a < 2^63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof.
  intros a H. unfold c_lts, bv_lts. rewrite !bv_signed_small by (u_norm; lia). u_norm.
  destruct (Z.ltb_spec a 0); [lia|reflexivity].
Qed.

#[using="Type"] Lemma v_and_0_l : forall (x : word), v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite_run1 ()) ["FPX_1"] "h02Hah17__arithh24__ffh38__varmaph45__with51zh66__sat0h76__sat1h81xp;1p;2p;3p;6p;4p;7p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004>R0p4p710p8g005Sj10Tg007Oj1OTg007mj1DTg0096j24Tg00_hj2<Tg008Pj23Tg00:=j32Tg00:Wj27Tg00`Fj1BTP0j68Tg00<=j1@Tg00<]j1>Tg00Ehj1=Tg00=[j1NTg00>9j1MTg00>dj2;Tg00GGj4:Tg00@Lj2LTg00@nj2ITg00AZj3HTg00B9j4ETg004\j21Tg0068j16Tg00;1j2CTg0073j29Tg006Vj2FTg00;Yj3GTg00Fdj3ATg00H2j3JTg00`hj2KTg00I`j7?Tf1R0g00MSg00N2R1P1g00NRR1f0R2g00O2F?p=5g00OR#0R3#0#0#0#0#0R4#OR5#DR6g00LNR7g00L0R81450,<2,351358R9526X57P7P81352=269X5717691452R:,<8%B:E81459g00PSR:#@R;%>:R:%=7R<%N7R=%M7R>P71;78R?g00LlP?C:'51L>1R1P2f2R@g00Q?RAg00Q_RB'71I2@=2ABdAH780CERBb2b3b41188P2b1%63R3%64R4'C198311841F34RA,98R@[[1183RCg00P7RDAG340UW0118A\D^0CP;P:P<P=P7P?g00SJ1;73=A75C:,5>P1PBb2b3b4P@P2b1b6b75J8E81K92=269eW8o"). Qed.

#[using="Type"] Lemma v_and_m1_l : forall a, (0 <= a < 2^64)%Z ->
  v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 a) = Z_to_bv 64 a.
Proof.
  intros a H. unfold v_and. u_norm.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  f_equal. apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma v_subw_small_lit : forall a b, (0 <= b <= a)%Z -> (a < 2^31)%Z ->
  v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b H H2. unfold v_subw. u_norm.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw1 (mem : word -> option byte) (su : Z) (ra s0 s1 s2 s3 s4 s5 s6 : word)
           (can : word) (wb n : Z) (s l : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (su - 8))  (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (su - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 (su - 24)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (su - 32)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (su - 40)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 (su - 48)) (word_to_le_bytes 8 s4))
    (Z_to_bv 64 (su - 56)) (word_to_le_bytes 8 s5))
    (Z_to_bv 64 (su - 64)) (word_to_le_bytes 8 s6))
    (Z_to_bv 64 (su - 72)) (word_to_le_bytes 8 can))
    (Z_to_bv 64 (su - 104)) (word_to_le_bytes 8 (Z_to_bv 64 wb)))
    (Z_to_bv 64 (su - 96)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
    (Z_to_bv 64 (su - 88)) (word_to_le_bytes 8 s))
    (Z_to_bv 64 (su - 80)) (word_to_le_bytes 8 l).

#[using="Type"] Lemma sw_enter : forall regs mem rom (su f wb wp fd : Z) (s l bufp bufsz can ret : word),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0xc6000 <= f)%Z -> (f + 232 <= 0xf8ac0)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  (0 <= wb < wp)%Z -> (wp < 2^64)%Z -> (wp - wb + bv_unsigned l < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xae4d4 : word) mem rom)
      (mkst regs' (0xae55c : word)
         (mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                  (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l) rom)
    /\ getr regs' 17 = Z_to_bv 64 66
    /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (su - 104)
    /\ getr regs' 12 = Z_to_bv 64 2
    /\ getr regs' 2 = Z_to_bv 64 (su - 112)
    /\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
    /\ getr regs' 18 = Z_to_bv 64 2 /\ getr regs' 19 = Z_to_bv 64 (su - 104)
    /\ getr regs' 21 = Z_to_bv 64 0xf8ac0
    /\ getr regs' 22 = Z_to_bv 64 (wp - wb + bv_unsigned l)
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0143 ()) ["FPX_1"] "p'0h04__x1h17__arithh26__sat3h36__sat4h45__with54__ffh68__varmaph71bh84__p1h91Hh:4__x2h;1zh<2gHh=1nh>1xh?2Hah@1ohA5regs'hB1yhC2b1hD2b2hE1mhF2FDhG4FbszhH4FbufhI3FfdhJ3FhihK3FlohL3FwbhM3FwphN4GcanhO4GgothP3Ha0hQ3Ha1hR3Ha2hS3HrahT3HsphU5SMALLhV3SOKhW4SUhihX4SUlohY3WBPhZ4WPhih[6__sat5h\6__sat6h]4bufph^5bufszh_3canh`1fha2fdhb1lhc3memhd4regshe3rethf3romhg1shh2suhi2wbhj2wpi007swf_bszi017swf_bufi026swf_fdi039swf_wbasei048swf_wposp%0p%1p%2p%3p%4p%5p%6p%7p%8p%9p%:p%;p%<p%=p&0p&1p&2p;1p;3p;2p;5p;4p;6p;?p;7p;=p;Bp;<p;8p;Ap;>p;;p;:p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004`R1p4p710R2p8p1005>p4p710P2p8g005]j1:Tg006Bk10RTg006`k10ETg007Cj1BTg007hj1hTg008Fj1XTg008ej32Tg009?k11\Tg009jk21HTg00:Mk20~Tg00;0k51YTg00;TR2j20Tg00<0k11WTg00<Nj2jTg00<gR3j24Tg00=Dk41UTg00=gR4k10YTg00>Gk20xTg00?0k12:Tg00?Yk30jTg00@Bk627Tg00@fk126Tg00AIk11:Tg00Akk21OTg00BHk10rTg00Bhk30gTg00CKk31~Tg00Cok11}Tg00DMk31NTg00E0k216Tg00E\k10cTg00F<k302Tg00F\k212Tg00G:k11qTg00GXk11iTg00H6k11KTg00HXk21dTg00I:j2yTg00ITk21bTg00J@k41`Tg00K2k11>Tg00K^j2Ok11]Tg00LDk21ITg00Ldj25Tg00MAj2VTg00M]k30;Tg00NJk20TTg00ORj2MTg00PFk21GTg00Pnk31FTg00QRk20DTg00R:k21ETg00RZk21DTg00SOj4kTg00Sok21XTg00Tak20STg00UCj2ATg00Uoj29Tg00Vak201Tg00WAk200Tg00XJj5<Tg00Y<j2iTg00Yfj3`Tg00ZZj27Tg00[4S00j21Tg00[Ok20|Tg00\Bk12=Tg00]4k20zTg00]gk20yTg00^Zk21BTg00_Nm?2<Tg00`Uk306Tg00aPk30BTg00bQk20QTg00cOk21@Tg00dNj3]Tg00eIk42;Tg00fIS01k729Tg00gLk21TTg00hOk21<Tg00him=0PTg00i`j2UTP1j6=Tg00jCmB08Tg00kBm<22Tg00l:k40aTg00lej6FTg00mMj68Tg00n6k30fTg00o4k80iTg010;j6GTg010Wk10qTg011[mA0nTg012Pj4cTg013Rm=1zTg014Hm=1yTg015>m=1xTg0164m=1wTg016kk215Tg017]k210Tg018:k114Tg018Sk21uTg0194k41tTg01:2m>1sTg01:km;1rTg01;dk21pTg01<kmA1oTg01=`k21nTg01>\k10pTg01?Rk21jTg01@Tk51kTg01A`k31lTg01Bgk41mTg01Cnk41hTg01DHk40JTg01E3k70KTg01EWk31gTg01F:m<1fTg01F_k41eTg01G=k61vTg01Gak70OTg01HEk80hTg01Hik31{Tg01IHk41|Tg01IimB1cTg01JOk31JTg01K2k41PTg01Kck320Tg01LIm<21Tg01Lnk319Tg01Mjk11aTg01Njk81RTg01OGm:25Tg01PHk71_Tg01QJk71?Tg01Qnk40wTg01RIk71^Tf0R1#:#:#:#:#:#:#:#:p>0k%:1#:p>24%:1#:#:#:p>0b%:1#:#:#hp=a%X1#X#X#Xp>1[%X1#X#X#X#X#X#X#Xp>1Z%X1#X#X#X#X#X#X#X#X#X#X#X#X#X#X#Xp>0Z%B1#B#:#:p>0}%B1#Bp>0=%:1#Bp>0^%:1#B#:#Bp>0t%B1#:#:#:p>0W%:1#B#:#B#B#B#:#:#B#:p>0A%B1#:#B#:p>0]%B1#:#:#hp=t%:1#hp>0_%B1#:p>1M%:1#:#B#:p>13%:1#B#B#Bp>0Ng01SER5f3R6f2R7'if1R8/i132p=K%:1#B#B#:p>0sg01ScS02/V1p>0VQ02/01p=TP7g01TAR9g01T`R:P:g01U@R;P5P8g01U`R<P1H0Jg01VGR=K0Kp=>1y51p=NA2581p=@%:1#B#:#B#B#B#:#:p>0{%B1#:#:#Bp>0X%B1#B#B#:p>1A%:1#B#:#B#B#B#:#:#B#:#B#:p=q%:1#B#:#:p>0uP7P9P:P:P;P5P8g01VgR>P1H0JP=K0Kp=\P7P9P:P:P;P5P8g01WNR?P1H0JP=K0Kp>1;1V81,17p>0F21H51p=eB1g581p=|g01X5R@:0g81p=?%h1>0g8@p=ug01XQRAP5P5P5P4P4f5R4f4RBP6P7P8P1N<1fp>17P5P7P8P1H1ep>0\P8P9P:P:P;P1J1vp>11P4P9P:P:P;PBP9P:P:P;P6P7K0OP8P1L0hp>0UQ02>1{51p>0vP7P8P;P1H1|p>0[1478/01p=PQ02/071V81'1p=gP5P5P5P5P5P5P3P1P8P7P3P6PBP4f6R3f7RCf8RDf9RENB1cp=lB1J581p=WP6P9P:P:P;P7P8P1L0hp=LP7P9P:P:P;P8P1K0Op=zPBP9P:P:P;P6P9P:P:P;P5P7P<P8H0JP=K0KP1K0Op>0:P3P9P:P:P;P4PBP6P9P:P:P;P7P8P1L0hL0hp=CP5P8P>P1H0Jp>1VP6P9P:P:P;P7P8P9P:P:P;P1P=K0KK0Op>1C1M819`67p=xg01Y0R>P7P8P1H1Pp>0Gp-0RF/y1:2078p=~P5P7P8P1Ckp>09P5P5P2PCP2P3P4PBP6P7P8P1N<21p=3&0c6:024BP7P8P1Ccp>0I1081,77,16,1Bp=H10B61081,77'1,14p=Q&0c1:0278:02B6p>0CB02781:02B6p=6&0c1:0278:02B6:0234p=oB024B6P7P8P1Ccp=dPCA`34BP6P7P8D<>19>1p=fB19>81p>0m1978=261p>1=1967=2B8/11p=vA234BA2678/11'1p=w1181,17p>1S1481,O7p>0lP>P6P7P8H1P=2B1p>0>A2678/11p>28g01ZYR2&1a1'yp=}B0g678=2B1p=RP4PBP6P7P8D<>19>1p=JP5P3P4PBP6A]781E=p>0M20D78,M6=2B1p>0H1O78=261p>03P6P9P:P:P;P5B1J578P?P1H0JP=K0Kp>0<1478=251p>04P5PCP3P414B6P7P8P1L1Rp>0@P5PBP6P7P8P1E=p=D1M78=261p={P5PCP3P4PBP6P7H0aP8P1E=p=_1481,07p>0?14671481'0p>05P>P1P8P7P6PBP4P3PCPDN:25p>07P3P4PB1y67P8P1E=p=bP>P4PBP6P7P8P1K1_p=;&0c1:0278p>2320D81,M7p>1QP5P8P<P1H0Jp=pPCP9P:P:P;P3P4P9P:P:P;PBP6P9P:P:P;P7P9P:P:P;P8P=K0KP1K1?K0OK0Op=r144B/061078/71'1p=[Q02/061V78'1/11p=ZPB1167P8P1H0ap=E1078/71p=n1V4B,131467/08/11'1p=mPAPBP6P7P8P1E=p>0`P8g01[9S03P1P@H0wp>0ePCP3PAP4PBP6P7P8E=P1H0wp=IPB1067P8P1H0ap>18P3P9P:P:P;P4PBP9P:P:P;P6P9P:P:P;P5P7P<P8H0JP=K0KP1K1?K0Op=^P4P9P:P:P;PBP6P7P9P:P:P;P8P1K0OL0hp=Y10671781'1,1Bp=sP5P3P4PBP6P7P8P1L1Rp>1Lg01[US049221p>0dPBP9P:P:P;P6P9P:P:P;P5P7P<P8H0JP=K0KP1K1?p>0oP>P4PBP6P7P8P1K1^p=SP3P4PBP6P7P8P1H0wH0wp>0Lg01\5R=#:R<#:R?#:RG#:RH#:S05#:RI$0Rg01\ZRJ&0RG$0EP0%B=RK#:RL#:RM#hP5%:I$0k$0k$0kRN#:RO#hP5%BKRP#:RQ$24RR#:g01]8&0bO$0k#aP5g01]]RO#XRS#XRT#XRU#XS06$1[RV$1Z$0Z$0Z$0Z$0Z$0Z$0ZPA%:MRW$0}$0k#aP5%BQ#aP5&0==$0}$0^$0t$0W#aP5%hNP5%hIP5&0A=$0]$0=#tP5%hGP5%BH$0_P5%BLS07#:RL#:$0_P5%B<RI#BRN#B#hP5%hWP5%:IRQ#:RX#:RY#hP5%hRP5%BPRP#aP5%:NRR#:$0_P5%:WRW$0_P5&1M=$13$0=$0t$0N#aP5%hHP5Q05#hP5%hWP5%B?RW#:RH#:$0_P5&0_YP5&0W=$0]$0]$0b#aP5&0RMPJ&0E1RY&0E8RZP7P8P7P1CKR[&0E6?278R\[]D]C^=JR]PF&0A=$0s$0=#aP5%h<S08$0VPFQ08#TPF&1\5R^Q02-1H5R_20~5=R`3>P^P9P:P:P;I1YRa&0RIRb$0EP01081Rc$1WXB5X>51jcc^B5^>5P5P5g01^<1481H1URc#NXE5X=51@cc^E5^=5&0Y1Rc#NX>A1@cc^>A&0YVP5&0A=$0s$0=#tP5&0{=$0X$0}#aP5&0{=$0X$0}#tP5&0A=$0N$0^#aP5&0A=$0N$0^#tP5&0{=$0X$1A#aP5&0{=$0X$1A#tP5&0A=$0N$0=#aP5&0A=$0N$0=#tP5%q=$0b#aP5&0RXPJ%q=$0b#tP5%:=$0=$0N#aP5&0A=$0W$0^#aP5&0A=$0W$0^#tP5%q=$13#aP520x5U&2:5RU20x5S20x5OS0960j5PU%q=$13#tP5&0A=$0W$0=#aP5&0A=$0W$0=#tP5%q=$0u#aP5%q=$0u#tP5%q=$0t#aP5%q=$0t#tP5%q=$0s#aP5%q=$0s#tP5%q=$0N#aP520~5<S0:=\^`PaP^P9P:P:P;Q0::1;^`J27PaB0F7811@87g01^`[[^05^:5^8FPF20x5TPU20~5I&265RI%q=$0N#tP5%q=$0W#aP5%BQRU$0RPJ%q=$0X#aP5Q06$0YP5%h?R?#ePIA\^_`Pa%q=$0X#tP5%q=$0]#aP5%q=$0]#tP5&0A=$0]$0=#aP5Q0:,|`PIp+01FS0;$0EP0Q0;$1:P0Q08,?bfcS0<1ubQfdRQ1ubNfeS0=p+01IS0>,?bRNffS0?%h=RT,?bfgR9Q0>#hP5Q08p+01CS0@+1OP5p+01BS0A,?bfjS0B1ubWfkS0C1ubHflS0D%BW,ubfmRW1ubXfnRX1ubUfoRU1ubRfpS0E%BG,ubfqS0F1ubKfrRK1?b?fsS0GPNftS0HPNfuS0I%BM,ubfvRM1ubLfwRLQ07#B,ubfxS0Jp+01]RN$0rP0Q07,ubfzRGQ02>0gb@f{RRP[PFQ00P8\\&0EB?267\1&0E4?2B6\8B1~678P1n2001000000120000000aXDZXCYX=JP]p+01^S0K$1}P5p+01XR]#TPFp+01_S0L#eRJ9>^`PaQ08#eS0Mp+01eS0N61N5PIp+01WRY#eRZPIp+01ZR\#ePIp+01bS0O$0YP5P1X>5R[P[Q0APVp+01\RH%NHJ17P[p+01AS0PO1P[PHO1'@p+01TR<#ePIp+01SRO#ePIPZPI%eHPIp+01RRZ#ePIp+01VRS#ePIp+01URd#ePIPJPIp+01gS0Q#ePIp+01YRJ#ePIp+01aS0R#ePIQ0AQ0N'?Q0A$0EQ0L#NQ0LQ0L'@p+01`S0S#ePIQ0Rp+01PRe'4P5Q0Op+01lS0T'4P5p+021S0U#NQ0UQ0U'@p+022S0V#ePIp+023S0W/4<P5p+024S0Xp+020S0Y'4P5p+027S0Z#e=>^`Pap+029S0[/01%T8S0\[^05PFp+028S0]#ePIg01_=S0^p+01HS0_p+01GS0`60j5g01_iS0a+16Q0^$0cRf402Q0^$0rRgPfPg21257Rh&1q5S0b80\8Ri&1i5RjP^P^211^BS0cQ0A&1K:R:Q0PJ0U21d^;R;P1P7g01`US0d,y221b17Q0d522d&0v8H1`Rkb5b6b4X05X:5X8F21258RlQ0b80\1$0v$1>P^P^211^7p+01@RmP:f~S0eJ0U60[^^05^:5^8Fp+026S0f,?M&0EMQ0Y#ePIQ08Q0T+1OP5p+02<S0g#e9\^`Pap+01iS0h$0EP0Q0FQ0F[P0p+02FS0iQ0C'4P5p+02JS0j%:=$1M$1A$0u$0=$0^$0u'uQ0Gp+02KS0kp+02?S0l'?Q0Hp+02LS0mp+02>S0n'OQ0Ip+02MS0oQ08'OPMp+02NS0pp+02ES0q'OPLf`S0r$1:P0p+02PS0sQ0['OfyS0tp+02QS0uQ0X'OPGp+02RS0v/OTPRp+025S0w&0XP$0b'uf;RPf}S0x$1:P0p+02US0yQ0w'?Q0e&0VLPFQ0J#TPF%eGPIQ0<9\^`PaQ0gQ0k'?fBR=Q0Zp+01ES0z+1IP0p+02\Rn$1]Q0`^;5Q0_\5P0Q0?,|`PIp+02[Ro,01p+01DRp,58Q0@'V[^05PFfhS0{Q0@5P1X;5PF^;5Q0@#NQ0@Q0@'@p+02^S0|,01Q0`,58Q0`Q0;3P[^05PFp+02cS0}p+02:S0~'?p+01MRqQ0iQ0p'?fLS10fiS11,|`PIp+02fS12Q0g'?Pep+02IS13Q0v'?fOS14Q0B,|`PIp+02iS15Q0n'?POQ0mQ0p'?fRS16Q0C,|`PIp+02lS17p+02@S18'?PSp+02OS19Q0v'?fURrQ0D,|`PIp+02oS1:p+02BS1;'?PJQ0vp+02eS1<'?fXS1=1|`WPIp+032S1>p+02DS1?'?PHQ0yp+02`S1@'?f[S1A1|`UPIp+035Q0i'?Q0Lp+02XS1B/?nf^S1CQ0H,|`PIp+038Rsp+02HS1D'?Q0OQ02>0go@faS1Ep+03:RtQ13'?p+01dS1Fp+03;Q13'?Q0Np+01cS1Gp+01LS1H60;bP2p+03=RuQ13'?Q0QQ1@Q13'?Q0?p+01QRv-1I5P0Q15Q15Q0O3gPFQ0JQ1G'0PFQ0JQ1F'0PFP[P[P[p+02]R0Q17Q17f|S1IPop+036Rwp+01JS1JM:lP[PGO1Q0t'@Q1I/WqPIp+03ES1KQ19'?p+01oS1Lp+01hS1M9guuPFQ0h,0GPFp+01jS1N,0GPFP[P[P[Q0}p+03@RxPxQ0ep+02aS1Op+03<S1PPeM:lP[Q1IO1/@RQ0e/WOPIp+03KRyp+02TS1Q'?Q0wp+02nS1R/?tQ0H1|`qPIp+03NS1Sp+02VS1T'?Q0]P^Q0PP:Q17CLPa1W`mQ0z5>^Pap+03JRtp+03IS1U5P1Q0w,V8[^05PF1W`vPIQ0:Q0@'WQ0_5>^PaQ0:/WO/WNPIp+03US1Vp+02ZS1W'?Q0lp+02;S1Xp+01fS1Y60;bP21W`OPIQ0:/W<Q0R'WPIp+03YS1Z/?0p+02CS1[Q0wQ1N60;bP2p+03[S1\Q0|'?Q0qp+03\S1]Q0|'?Q0ip+03?Rzp+03P'?Q0;Q1M,|`R{PIp+03_S1^Q1@'?Q13p+03BS1_p+03HS1`'?Q0>Q0Q,|`PIp+03bS1ap+02bS1b'?Q0mQ1Kp+03RS1c'?Q1HP{PIp+03eS1dp+02dS1e'?Q19Q1`p+03MS1f'?p+01OR{Q0h,|`PIp+03hS1gQ12'?Q0vp+03iS1hQ12'?p+02SS1iQ13Q0~60;bP2p+03kS1jp+02gS1k'?Q0yp+03lS1lQ02'OQ1TQ0u,V1%T7R|@0F78S1mQ1i:0F|7[[^05^:5PFQ0v,V8Q0\@0F87Q1Q:0F|7[[^05^:5PFp+03oS1nQ1<'?p+02YS1op+040S1pQ1<'?Q1Wp+041S1qQ1e'?Pop+03TR|p+03^R}'?p+01[S1rQ0L,W`PIQ0:Q0S'WQ1<'WPIp+045S1sQ1e'?p+02_S1tp+03XS1u/?TQ0Lp+047S1vQ1<'?Q1Op+03ZS1wp+03jS1x'?Q0Rp+049S1yQ12'?Q0}p+04:S1zQ12'?Q1e20TVNQ0oQ0O/M?Q12Q1k$1KPJQ08p+043S1{+1Gp+03]S1|Q0mP\[[Q0oQ1r[\}PFQ03Q08Q1v<1F8UX?}Q03Q1r[^?}Q1^Q03PH[]?PFp+04?S1}#e/W\=>^`PaQ0K/M?R}p+02mS1~1yY]A2Y]]1|`NPIp+01nS20/01p+02kS21,58#T[^05PFA>^_JR~PaQ1i9\^\PaQ1rQ0v'WPI1MY?S22p+034S23A>^_SPap+02WS249\^YPaQ1T,W]PI1M]?PsA>^_YS25PaA\^]oPaQ1W,WJPI1MJ?S26Q1PA>^_]PaQ1t9\^JPaQ0|,W\PI1M\?RsPxP~PaQ0}9\^\PaQ1rQ1b'WPIQ1r/M?p+03DA>^_\PaQ1rQ1k5\^PaQ12,WHPI1MH?Q1`p+04AS2700DHP5A>^_HPaQ179\^NPaQ0KQ21'WPIP}Q1fA>^_NPaQ0Kp+030S285\^PaQ0LQ1:'WPIp+04IS29Q0K+0DP5Q0S/M?Q1cQ0L/M?R}p+03SR~P}P|Q0Sp+04[S2:p+04iS2;+1E+1DQ1VP}p+03VS2<Q29p+03WR}P|Q0mCkQ1;Q0oQ1y'MQ1uPsQ1Zp+04LS1ZQ1wp+03LQ0vCkQ0qQ1iQ02'MQ1\Q22Q1]p+04US1]00DYP5Q25PaA\^]xPa1WJzPIQ26p+03aS26PfPgPlPjPHP;Pkb5b6b4X0521251$0v$1>Rz>0[^\^05P^PJP:Q0sCLPa1Md?Rsp+03dS251MZ?R|Q1d1Mv?S22p+03fS1wQ22p+03gS22p+04`S1u00DvP5A>^_vPaA\^ZyPa1WOtPI1MO?Q1lA>^_ZPap+03OS2=9\^OPaQ1S,W<PI1M<?RtQ1pA>^_OPaA\^<~PaQ1c,WdPIPsp+044S2>A>^_<PaA\^d}PaQ2<,WSPI1MS?R}p+048S2?P}Q1yPsQ1zp+04mS2@p+04;S2AQ1pQ1:CkQ12p+04oS2BQ155z^PaPtp+04=S2Cp+04HS2Dp+03A+0D-1X<p+04>S2EPtQ1}p+058S2F00DeP5P|Q271MwTp+04BS2GP|p+04CS2HQ0Kp+05LS2I'Mp+04DS2JP|p+04ES2KQ2Fp+04FS2Lp+046S2MPxCkp+031S2Np+059S2Op+04Gp+04<S2PPxCkQ1>PtQ2DQ29p+04JS2Qp+03CRt721W7Q29PF]7Q2Q/ytQ2Q?2ttQ1{00SSQ1_p+03>S2R/ydQ2R?2ddP^PvP:p+01NS2S9>^_CLPaP^Q1pP:Q1n9\^{CLPa1WeuPIQ0FQ0E5z^PaQ0Ep+042S2T5>^PaAz^LMPaQ2>9>^MPaQ0eQ0x5z^PaQ0xQ2M5>^PaQ0z=z^pPaQ2?9>^pPap+01KS2UQ1J5z^PaQ1JQ1z5>^PaAz^vePaQ2P9>^ePaAz^YSPaQ2E9>^SPaAz^NHPap+04@S2V9>^HPaPfPgPlPjPUP;Pkb5b6b4X05B0[^zW^05Q0F9z^KPaQ0FQ2H5>^PaQ1FQ2G'WPIP^p+03QS2WP:P^P^P^P_p+051S2XQ2X=\^`I0:P:fWS2YFCPaP^p+052S2ZQ2L5\^P:P^P^p+05XS2[P^Q2Z-1V`H1CP:Q1=FCPaPfPgPlPjfKS2\P;Pkb5b6b4X05RIfIS2]:0[^z^05RxPIPxP^Q2QP:fHS2^Q295>^CLPaQ0^Q2Op+05GS2_60j5Q0a+16<02fPgQ0bQ0b:0\h780\8PjPDP;Pkb5b6Rhb4X05X:5Q0bQ0b:0\l880\1$0v$1>>0[^3^05^:5RaQ1qPgPhb4X05X:5PaPfPgPlPjP4P;Pkb5b6b4X05B0[^z6^05p+04lS2`,Abp+04kS2a,91Q2@Q2a,98p+04nS2bQ2a,97Q2BQ2a,96p+050S2cQ2a,9BQ2XQ2;,94Q2ZQ2;,93p+053S2dQ2;,9Cp+054S2eQ2;,9Dp+055S2fQ2;,9Ep+056S2gf:RzQ2;'9p+057S2hQ2;,9PQ2Ff<Rap+04hS2i'9Q2Of=RhQ2i'9p+05:S2jf>RxQ2i'9p+05;S2kf?S2lQ2i'9p+05<S2mf@RIQ2i'9p+05=S2nfAS2oQ2i'9p+05>S2pQ2i,9=p+05?S2q20TVhR|Q2iP|Q2;P|p+04jS2rP|Q2aP|Q2`P|Q2@P|Q2bfJS2sp+05ES2tQ2]p+06?S2uQ1z+0DCxQ2_,Abp+06]S2v0018PAp+06^S2w0016PAp+06_S2x0014PAp+06`S2y001CPAp+06aS2z001EPAp+06bS2{001PPAp+06cS2|001hPAfFS2}-00VA2A3VR|Q2^-00VP|Q2s-00VP|Q10-00VP|fNS2~-00VP|fPRT-00VP|Q16-00VP|p+04TS30p+04MS31>0G1Vp+04NS32p+04PS33>0G8Vp+04OS34Q33Q0x728PFp+04XS35p,2fxR|Q1Cp+04WS36PBP1D<g01a5S37p+06dS38,51P5p+06gS39,58P5Q2v,57P5p+06eS3:,56P5Q2w,5BP5p+06fS3;,54P5Q2x,53P5Q39,5CP5p+070S3<,5DP5Q2z,5EP5Q39,5zP5p+06iS3=,5PP5Q2|,5aP5p+07@S3>/Ohp+05jS3?p+05dS3@,5xP5p+07BRs/Oxp+05lS3Ap+07CS3B/Oxp+05mp+07DS3C/Oxp+05nS3Dp+07ES3E/Oxp+05oS3Fp+07FS3G/Oxp+060S3Hp+07GS3I/Oxp+061S3Jp+07HS3K/Oxp+062S3Lp+07IR}/Oxp+063S3Mp+07J/Oxp+064S3Np+07KS3O/Oxp+065S3Pp+07LS3Q/Oxp+066S3Rp+07MS3S/Oxp+067S3Tp+07NS3U/Oxp+068S3VQ2sQ39'4P5Q2\Q3B'4P5Q10#NQ10Q10'@Q10p+06jS3W'4P5fMS3XQ3G'4P5Q2~#NQ2~Q2~'@Q2~p+06mS3Y'4P5Q14/4}P5%NT1@TTQ3<,4TP5fQS3ZQ3Q'4P5Q16#NQ16Q16'@Q16p+073S3['4P5fSS3\p+07OS3]'4P5fTS3^#NQ3^Q3^'@Q3^p+076S3_'4P5p+07RS3`,4rP5fVS3a#NQ3aQ3a'@Q3ap+079S3b'4P5Q2Yp+07US3c'4P5Q1=#NQ1=Q1='@Q1=p+07<S3d'4P5fYS3ep+07XS3f'4P5fZS3g#NQ3gQ3g'@Q1AQ1Ap+06IR~3gPFp+05`S3hf\S3i'0PFQ1CQ1Cp+06KS3j3gPFp+05bS3kf_S3l'0PFQ1EQ1Ep+06MS3m3gPFQ3@fbS3n'0PFp+06O9gQQPFp+05fS3oQ0='0PFp+06QS3p9g99PFp+05hS3qQ0{'0PFQ0BQ0Bp+06SS3r3gPFQ3?Q0C'0PFp+06US3s9gWWPFQ3A/0XPFQ0EQ0Ep+06WS3A3gPFQ3DQ0F'0PFQ3DQ0C'0PFQ3F/0WPFQ3H/0UPFQ3JQ0F'0PFQ3LQ0G'0PFQ3MQ0I'0PFQ3N/0LPFQ3PQ0t'0PFQ3MQ0G'0PFQ3NQ0I'0PFQ3P/0LPFQ3RQ0t'0PFQ3T/0RPFQ3VQ0x'0PFp+069S3t/0mPFp+06:S3uQ0A'0PFQ3u/0RPFp+06;S3vQ0x'0PFp+06<S3w/0mPFp+06=S3xQ0A'0PFp+06>S3y/0pPFQ2uQ0;'0PFp+06@S3zQ0_'0PFp+06AS3{Q1J'0PFQ0@p+07gS3|'4P5p+08CS3},4pP5Q0z#NQ0zQ0z'@Q0;Q0;p+074S3~3gPFp+07kS40,4eP5p+08G,4vP5%NZ1@ZZQ0>p+07nS41'4P5Q1Jp+08JS42'4P5Q2U#NQ2UQ2U'@Q2Up+081S43'4P5Q1Hp+08M'4P5%Nq1@qqp+084S44,4qP5Q2Sp+08PS45'4P5%N{1@{{p+07AS469geePFAgZZsPFQ3B9g<<PFQ0LQ0LQ3C3gPFp+08cS47/OZQ3Sp+072S48,M<Q3UQ3Y,4<P514d}P5p+08gS49/i<P5P[P[P[p+08BS4:Q1FQ1FQ0`p+08@p+08[S4;p+06oS4<M:lP[Q0>O1Q0_'@p+08iS4=/idP5P[P[P[p+08DS4>Q0NQ0NQ0;Q4:p+08]S4:p+071S4?M:lP[Q0_O1Q0`'@S4@p+08kS4A/iSP5P[P[P[p+08FS4BQ1YQ1YQ0zQ4>p+08_S4>Q3[M:lP[Q0`O1Q0;'@p+08mS4C/iYP5P[P[P[p+08HS4DQ0QQ0QPpQ4Bp+08aS4Bp+075S4EM:lP[Q0;O1Q0z'@p+08oS4F/i]P5P[P[P[Q42Q1MQ1MQ0@Q4DQ47p+077S4DM:lP[Q0zO1/@pp+091S4G/iJP5P[P[P[p+08LS4HQ0hQ0hQ0AQ42p+08eS42Q3bM:lP[PpO1Q0@'@p+093S4I/i\P5P[P[P[p+08NS4JQ1NQ1NQ0PQ4HQ49p+07;S4HM:lP[Q0@O1Q0A'@p+095S4KQ1r'iP5P[P[P[Q45p+01kS45Q45PmQ4JQ4=p+07=S4LM:lP[Q0AO1Q0P'@Q0@p+07YS4M'0PFQ4B,0pPFp+07[S4N,0pPFQ0zQ47'0PFA~ppp1jppQ2Up+07^S4O'0PFQ1Hp+08fS4P'0PFQ1Hp+07`S4Q'0PFp+08hS4R,0qPFQ0`Q0`Q0`3~Q0`Q0`'jp+07cS4S,0OPFQ4A,0<PFp+07eS4T,0<PFQ4C,0dPFQ1JQ1JQ1J3~Q1JQ1J'jQ1rp+07hS4U'0PFp+090S4V,0HPFp+07jS4W,0HPFp+092S4X,0NPFA~qqq1jqqQ1Gp+07mS4Y'0PFQ1FQ4K'0PFQ1Fp+07oS4Z'0PFQ0Np+097S4['0PFA~eee1jeeQ45p+082S4\'0PFQ0Tp+09:S4]'0PFQ0TQ44'0PFp+01mS4^p+09<S4_'0PFA~OOO1jOOQ0Wp+087S4`'0PFQ0Xp+09?S4a'0PFQ0Xp+089S4b'0PFQ0wp+09AS4c'0PFA~SSS1jSSQ1Xp+08<S4d'0PFQ0gp+09DS4e'0PFQ0gp+08>S4f'0PFp+02=S4gp+09FS4h'0PFA~JJJ1jJJQ45p+09VS4i'0PFQ45p+09WS4j'0PFQ0Yp+09XS4k'0PFQ0Yp+09YS4l'0PFQ0wp+09ZS4m'0PFQ0wp+09[S4n'0PFQ0~p+09\S4o'0PFQ0~p+09]S4p'0PFQ0lp+09^S4q'0PFQ0lp+09_S4r'0PFQ1?p+09`S4s'0PFQ1?p+09aS4t'0PFQ13p+09bS4u'0PFQ13p+09cS4v'0PFQ0pp+09dS4w'0PFQ0pp+09eS4x'0PFp+09oS4yQ1Q'iP5P[P[P[p+09JS4zQ1eQ1eP{p+09HS4{Q4vQ4`M:lP[PvO1/@eS4|p+08S,0ZPFp+08T,0ZPFA~vvv1jvvQ0}p+09gS4}'4P5p+0:5S4~Q0}'iP5P[P[P[p+09PS50p+033S51Q51Pvp+09NS52p+09iS53p+08=S54M:lP[POO1/@Zp+0:7S55/ioP5P[P[P[p+09RS56Q21Q21PeQ50p+09kS57p+08?S58M:lP[PZO1/@vp+0:9S59/inP5P[P[P[p+09TS5:Q17Q17P{Q56p+09mS5;p+08AM:lQ4|p+0:;S4|/i0P5P[P[P[Q4iQ1~Q1~Q2SQ5:Q4yQ3}M:lP[PeO1/@{Q4lQ49Q4;Q21CkQ3`p+08`S3`,0ZPFQ4B,0ZPFp+08bS3},0YPFQ47,0YPFp+08dS5<,0HPFQ42,0HPFQ0RQ4P'0PFQ0RQ49'0PFQ4uQ4Vp+08lS5=Q23CkQ4NQ4GQ4X?21wW7Q4GPF]7Q4X/ywQ4X?2wwQ1vQ4G;`SQ4I,Abp+094S23?2YSPFQ4}Q4KQ4IP]CkQ4Qp+0:LS5>/iJP5Q4F,0]PFQ4V,0]PFP[P[P[Q53Q2RQ2RQ2R#Np+08WS2RQ4XP[P[p+09hS5?p+0:IS5@Q4XQ4X#NJ17M:lP[P\O1/@JQ3}Q1KQ25409Q46Q47p+03GQ1w409PsQ5<Q1UQ1g409Q3BQ42Q1x809yQ3CQ4PQ1fQ1l409Q3EQ49Q2=p+03nS1K409Q3GQ4RQ2WQ1p409Q3IQ1t/7{PFQ0uQ2S'7PFP[p+0:4S5AQ1<Q1ePOp+09;S5BQ5BQ4UG31jZeQ1@/7qPFQ1iQ1H'7PFP[Q55Q21p+02jS5CP]p+09>S5DQ5DQ40G3Q2S,jeQ1OQ2U'7PFQ0yQ1J'7PFP[p+0::S5EQ2NQ28PNQ4cQ4cQ41G3Q2SQ1H'jQ1bQ0>'7PFQ24Q0_'7PFP[p+0:=S28p+037PwQ0OQ4eQ4eQ43G3Q1HQ1J'jQ0}Q0`'7PFQ1oQ0;'7PFP[p+0:@S5FPuQ1PQ0Qp+09GS1PQ1PQ44G3Q1JQ0_'jQ1eQ0z'7PF17opPFP[p+0:CS5GPtQ1_Q0TQ4zQ4zQ4`G3Q0_Q0;'jQ1<Q0@'7PFQ0A,70PFP[p+0:FS1_Q1UQ1`Q0Up+09MS1`Q1`p+08:S1UG3Q0;/jpQ12Q0P'7PFQ1t/7mS5HPFP[Q5@Q2=Q1SQ0fQ50Q50Q54G3Q0A,jpQ1@/7mRwPFQ1o/7mPFQ1O/7mPFQ1W/7mPFQ1b/7mPF17omPFQ0}/7mPF17nmPFQ1e/7mPF170mPFQ1</7mPFQ0|/7mPFQ12/7mPFQ5HPFQ1k/7mPFPwPFP[p+0:ZRwQ1@Q1tQ0eQ4tQ4tQ4JG3Q0xQ1I'jQ0op+0;3S4J'Mp+09jS5HQ53,99Q57Q0{p+09fS1S'9p+09lS5IP[p+0:^S5JQ0pQ0oQ0<Q4xQ4xp+08RG3Q0=/jQp+09LS5K,49P5Q0CQ1S'9Q4yQ0DQ1S'9p+0:0S5LQ1S,9Wp+0:1S5MQ1S,9Xp+0:2S5NQ1S,9Up+0:3S5OQ0EQ1S'9Q5AQ0FQ1S'9Q4~Q5M,9Kp+0:6S5PQ2Gp+04_S5Q$0YRo'4P5Q2J/4oP5Q2L/4oP5Q2D/4oP5Q2Q/4oP5Q1Z/4oP5Q32/4oP5Q0oQ0D'1PFQ0mQ0D'1PFQ0jQ0C'1PFQ13Q0C'1PFp+02GS5RQ0B'1PFQ0iQ0B'1PFQ1?Q11'1PFQ1[Q11'1PFp+02AS5SQ0{'1PFQ18Q0{'1PFQ0n/19PFQ4g/19PFQ1XQ0?'1PFQ0~Q0?'1PFQ0]Q0='1PFQ0ZQ0='1PF110QPF11nQPFQ1W/1QPFQ1o/1QPFQ24/1QPFQ1T/1QPFQ1Q/1QPFQ1i/1QPFQ0u/1QPFQ0s/1QPFQ0p/1QPFQ0o/1QPFQ0k/1QPFQ0j/1QPFQ1D/1QPFQ5R/1QPFQ5Jp+04bS5TQ0<32PFp+04dS5U,@JPFp+0:`S5V?2QtPFp+0:aS5WQ3h72QPFQ0</0wPFp+0:cS5XQ0<p+05aS5Y32PFp+0:dS5ZQ0<Q5Y32PFp+0:eRtQ0<Q5Y32PFp+0:fRnQ0<Q5Y32PFp+0:gS5[Q0<Q5Y32PFp+0:hS5\Q0<Q5Y32PFp+0:iS5]Q0<Q5Y32PFQ0QQ5WQ0<P}Cxp+0:jS5^,Abp+0:kS5_p+05k72QPFQ5Z,0QPF10QtPF10QnPFQ5[,0QPFQ5\,0QPFQ5],0QPFQ5^,0QPFp+04RS5`/1QPFp+04QS5aQ0<'1PFQ33Q3n'1PFQ34Q1E'1PFQ32Q0r'1PFQ31Q3l'1PFQ1ZQ1C'1PFp+04KS5bf]S5c'1PFp+04ZS5dQ3i'1PFp+04YS5eQ1A'1PFQ35Q3g'1PFQ36Q3e'1PFp+04VS5fQ1='1PFQ1]Q2Y'1PFQ30Q3a'1PFp+04SS5g/1rPFp+09nS5hQ0nQ5hp+06GS5ip+0;AQ04,y2RnJ0IQ16eQ16p+04aS04Q2}Q1uPRp+0<CS5jDHPFQ1uQ2}Q5QPRp+0<DS5kDHPFQ5QQ2}p+04^S5lPRp+0<ES5mDHPFQ5lQ2}p+04]S5nPRp+0<FS5oDHPFQ5nQ2}p+04\S5pPRp+0<GS5qDHPFQ5pQ2}Q2:PRp+0<HS5rDHPFp+04gS5sQ10Q33Q0Ap+0<WS5tDHPFp+04fQ10Q33Q0Ap+0<XS5uDHPFp+04eS5vQ10Q33Q0Ap+0<YS5wDHPFQ5UQ10Q33Q0Ap+0<ZS5xDHPFp+04cQ10Q33Q0Ap+0<[S5yDHPFQ5TQ10Q33Q0Ap+0<\S5zDHPFp+0<US5{,41P5Q5{,48P5Q5{,47P5p+0<jS5|/O6p+0;TS5}p+0<kS5~/O6p+0;US60p+0<lS61/O6p+0;VS62p+0<mS63/O6p+0;WS64Q5o,43P5p+0<bS65,4CP5%ND1@DDp+0<IS66,4DP5p+0<eS67,4EP5%Nz1@zzp+0;fS68,4zP514P?P5%Na1@aaQ3v@0GPVp+0:XS69Q3w@0GPVp+0:YS6:Q3xQ0680GPPwp+0<VS6;p+0;dS6<p+0;ZS6=Q2lCkp+0:OS6>p+0=;S6?/iIP5Q2oQ5|'MQ68p+0;_S6@,0xPFP[P[P[Q5uQ2}Q2}PhQ6;p+0=1S6Ap+0;EM:lP[Q2lO1/@xQ3M,0IPFQ2oQ3P'0PFQ3T,0=PFfCRtQ3t'0PFfDS6BQ3v'0PFfES6CQ3x'0PFQ2}Q2u'0PFfGS6DQ3{'0PFQ2^p+06CS6E'0PFQ2;/0TPFQ2]Q3x'0PFQ2rQ16'0PFp+05WS6FQ3\'0PFQ10Q3{'0PFQ2[/0rPFp+05]S6GQ3a'0PFQ14p+06ES6H'0PFp+05^S6IQ1='0PFp+05cQ3e'0PFQ16/0~PFQ3@Q1A'0PFp+05iS6JQ3i'0PFQ3m,0rPFQ3?Q1C'0PFQ3FQ3l'0PFQ1=Q3p'0PFQ3HQ1E'0PFQ3PQ3n'0PFQ1AQ3s'0PFQ3R/0QPFQ3vQ0='0PFQ1Cp+06YS3s'0PFQ3w/09PFQ3{Q0{'0PFQ1EQ2v'0PFp+06BS6KQ0B'0PFQ0{p+0=PS6L'Mp+0<MS6MQ3nQ5o'0PFP[P[P[p+0=?S6NQ0DQ0DQ1Ep+0==S6Op+0=XS6Pp+0;lS6QM:lP[Q0<O1Q3n'@p+06ZS6R,0QPFQ0=p+06\S6S'0PFQ0?Q2w'0PFQ2y,09PFQ0{Q2{'0PFQ11Q38'0PFQ0BQ3;'0PFQ0Cp+06hS6T'0PFQ0DQ3W'0PFp+05PS6U/0MPFQ38,0WPFp+05QS6VQ0J'0PFQ3yQ0t'0PFQ0EQ6T'0PFQ2u/0RPFp+06DS6WQ1I'0PFQ0Gp+06lS6X'0PFQ6HQ0e'0PFp+06JS6Y/0mPFQ3<,0MPFQ3jQ0A'0PFp+06PR0Q0@'0PFQ0tQ3~'0PFQ3pQ0z'0PFp+06VQ0;'0PFQ1Ip+078S3p'0PFQ3AQ0_'0PFQ6SQ0>'0PFQ3d,0mPFQ2vQ2U'0PFQ2{Q1H'0PFQ0@Q3>'0PFQ2|Q2S'0PFQ6T/0{PFQ0;Q3C'0PFQ3=/0vPFp+0>6S3C,Mep+0=4S3AQ0`Q63'0PFP[P[P[p+0=fS3jPOPOQ0;p+0=>S6ZP?P[P[p+0=eS6[Q06P?%N?J17M:lQ4@Q0>p+07>S4@'0PFQ1JQ3>'0PFQ2U/0sPFQ1HQ3S'0PFQ3E,0qPFQ2SQ3I'0PF10{}PFQ3O,0ePFQ3S,0vPFQ3],0ZPFp+07Q,0OPFp+07SS6\,0<PFQ3c,0dPFQ3DQ0R'0PFQ3Q,0SPFQ3FQ1G'0PFQ3NQ1F'0PFp+07P,0JPFQ3PQ1Y'0PFQ3uQ0Q'0PFp+07TRo,0HPFQ3vQ0h'0PFQ3zQ1N'0PFQ0Lp+07aS3F'0PFQ3{Q0T'0PFQ5iQ4^'0PFQ0OQ4N'0PFp+06HQ1L'0PFQ4EQ0Y'0PFQ0Np+07_S5i'0PFQ3_Q0V'0PFQ4HQ0W'0PFQ1MQ4S'0PFQ3dQ0w'0PFQ46Q0f'0PFQ45Q3|'0PFQ0],0sPFQ3IQ0['0PFQ20Q40'0PFQ3KQ1X'0PFQ3SQ0g'0PFQ0UQ4Z'0PFQ3UQ0n'0PFQ6\Q0l'0PFQ0Xp+083S3S'0PFQ5S,0oPFQ4MQ1;'0PFQ0ZQ4`'0PFp+07ZS3IQ1?'0PFQ5iQ0q'0PFQ0~p+08;S46'0PFQ4QQ5R'0PFp+0=kS3DQ0iQ0w32PFQ0WQ1N'7PFQ1NQ0h'7PFQ0XQ0h'7PFQ0hQ1M'7PFQ0wQ1M'7PFQ1MQ0Q'7PFQ0fQ0Q'7PFQ0QQ1Y'7PFQ0ZQ1Y'7PFQ1YQ0N'7PFQ0]Q0N'7PFQ0NQ1F'7PFQ0[Q1F'7PFQ1FQ1G'7PFQ0~Q1G'7PFQ1GQ0O'7PFQ1XQ0O'7PFQ0OQ0R'7PFp+0>>S3cQ1BQ0R32PFQ0L/7SPF17SdPFQ0S/7dPF17d<PFQ0R/7<PF17<OPFQ0O/7OPF17OZPFQ1G/7ZPF17ZvPFQ1F/7vPF17vePFQ0N/7ePF17e{PFQ1Y/7{PFQ2S,7{PFQ0QQ2S'7PFQ2S/7qPFp+0>QS6]Q5C;2qPFQ2UQ0x'7PFQ0xQ1I'7PFQ1HQ1I'7PFQ1I/7RPF17qRPF17RGPFQ2S/7GPFQ0t,7GPFQ0t,7{PFQ0tQ0J'7PFQ0J,7ePFQ0J/7LPF17vLPF17LMPF17ZMPFQ0I,7MPFQ0I,7OPFQ0IQ0H'7PFQ0H,7<PFQ0HQ0G'7PFQ0G,7dPFQ0G/7KPF17SKPFQ0F,7KPFQ0F,7YPFQ0FQ0E'7PFQ3{/1US6^PFQ6^PFQ4L/1UPFQ3d/1UPFp+07:S6^/1UPFQ3b/1UPFQ4D/1UPFQ3_/1UPFQ3~/1UPFQ3[/1UPFQ4?/1UPFQ3</1UPFp+06nS6_/1UPFQ3Y/1UPFp+06kS6`/1UPFQ3W/1UPFQ6T/1UPFQ39/1UPFQ3r/1XS3rPFQ3rPFQ3]/1XPFQ3U/1XPFQ3Q/1XPFQ3O/1XPF11}XPFQ3K/1XPFQ3G/1XPFQ3E/1XPFQ3B/1XPF11sXPFQ3>/1XPFp+07?S3>/1XPFQ4L/1XPFQ3d/1XPFQ6^/1XPFQ3b/1XPFp+06XS3B/1WRsPFPsPFPsPFPsPFPsPFPsPFPsPFPsPFQ3Y/1WRsPFPsPFp+07iS3E/1WPFQ4U/1WPFp+07fS3G/1WPFQ4T/1WPFQ4S/1WPFp+07bS3K/1WPFQ4Q/1WPFQ5i/1WPFp+07]S3Q/1WPFp+07\S3U/1WPFQ3I/1WPFQ4M/1WPFp+07WS3]/1WPFp+07VS3r/1WPF11oWPFQ6\/1WPFp+08^S6\/1WPFQ4zQ0D'1PFp+09IS6aQ0C'1PFQ4{Q0B'1PFQ1PQ11'1PFQ4hQ0{'1PFp+09ES6b/19PFQ4eQ0?'1PFp+09CS6cQ0='1PFQ49/1QPFp+09SS6dQ0<'1PFQ56Q3n'1PFp+09QS6eQ1E'1PFQ50Q0r'1PFp+09OS6fQ3l'1PFQ52Q1C'1PFQ1`Q5c'1PFQ5KQ3i'1PFQ47Q1A'1PFQ47Q3g'1PFQ47Q3e'1PFQ47Q1='1PFQ23Q2Y'1PFQ4sQ3a'1PFQ4r/1rPFQ4qQ3^'1PFQ4pQ3\'1PFQ4oQ16'1PFQ4nQ3Z'1PFQ4m/1TPFQ4lQ14'1PFQ5?p+05MS3ZQ34Q6KQ2iDHPFQ4}Q3ZQ34Q6KQ2;DHPFQ1SQ3ZQ34Q6KQ2rDHPFQ4xQ3ZQ34Q6KQ2aDHPFQ4wQ3ZQ34Q6KQ2`DHPFQ4vQ3ZQ34Q6KQ2@DHPFQ4uQ3ZQ34Q6KQ2bDHPFQ4yp+05TS2@Q1nP~Q2bDHPFQ5hQ2@Q1nP~Q2BDHPFQ5;Q2@Q1nP~Q2cDHPFQ5IQ2@Q1nP~Q2XDHPFQ57Q2@Q1nP~Q2ZDHPFQ5HQ2@Q1nP~Q2dDHPFQ53Q2@Q1nP~Q2eDHPFQ5Pp+05[S2BPyP0Q2eDHPFQ4~Q2BPyP0Q2fDHPFQ5AQ2BPyP0Q2gDHPFQ5OQ2BPyP0Q2hDHPFQ5NQ2BPyP0Q2FDHPFQ5MQ2BPyP0Q2ODHPFQ5LQ2BPyP0Q2jDHPFp+0B5S2j/O1p+0@_S2f20TV1S2rp+0@HS6gp+0ASS6hp+0@aS6ip+0@\S6jP8Ckp+0?LS6kp+0@JS6l00S8p+0?YS6mp+0B8S6n0017PAp+0;7S6o/4cP5Q6aP1p+0@]S6pQ1\P1p+05BS6qEQPFAgDD1PFp+0@`S6r,V8PFp+0B?S6s/O7p+0@iS6tp+0B@R0156P'Op+0@jS6u20TV8Ryp+0@SS6vPyp+0@TS6w20|6hp+0@mS6xp+0A`S6yp+0@nS6zp+0@kS6{PBCkQ6mp+0AaS6|p+0@oS6}Q6rPBCkp+0?ZS6~p+0@XS7000SBp+0?gS71p+0AcS72p+0A1S73Q70P6Ckp+0?\S74p+0BGS750014PAp+0;<S76/4cP5Q4lP1p+0@lS77Q1jP1Q6VEQPFp+0BBS78,V1PF&0V8/11PFp+0BNS79/O7p+0A8S7:Q0600T1Q6i&2=8p+0A:S7;p+0AmS7<p+0A;S7=Q7:P7Ckp+0?fS7>p+0@dS7?00S7p+0@3S7@p+0A=S7AQ2rp+0@fS7Bp+0BTS7C0011PAp+0;H/4cP5Q4}P1p+0A9S7DQ1yP1Q6IEQPFp+0ABQ10Q3^'5p+0BYS7E/i1'4P5p+0BPS7F,V1PFp+0B[S7G/O8p+0AES7H20TV6Q6zp+0AGS7I/yBQ7I?2BBp+0B:Ryp+0AHS7Jp+0A?S7KP4CkQ7@p+0B;S7Lp+0AIS7MQ7;P6Ckp+0@4S7Np+0B_S7O0016PAp+0;RS7P/4cP5p+08Ip+0ACS7Q;`Ep+0ALS7R,AbQ7QQ6J5`1p+0AMS7S,Abp+0AKS7T,98p+0ANS7UQ7Rp+0@DS7V5`8p+0AOS7W,AbP6p+0AFS7XP8p+0=oS7YCxp+0APS7Z,Abp+0AQS7[p+0<SS7\727PFQ7Wp+0?]S7]Q2jp+0@cS7^+0Dp+0BfS7_+1E+1D5`Bp+0ARS7`,AbQ7Hp+0@KS7a5`6Q6h,AbQ7[,9Bp+0ATS7bp+0AUS7cQ6l721PFQ7J,97p+0AVS7dp+0AWS7ep+0@OR~721PFp+0AXS7fp+0AYS7gp+0AZS7hQ2rQ7Qp+0ADS7i00S1Q6vp+0BOS7jp+0A]S7kQ7hP7CkQ6gQ7Xp+0;hS7l<097p+0?eS7mp+0C4S7n0016PAp+0@WS7op+0<8;26PFp+0;kS7p&0Y8'4P5200VCA2A7Vp+0A[S7q,08PFP~p+0BVS7rp+0AdRTp+0A_S7sQ6pCkP~Q5<P~p+0=NS7tP~p+0=MS7uP~Q1=P~Q4CP~p+0=YS7vP~Q2sP~Q3nP~PQP~PKP~Q0=P~P3P~p+0>:S7wP~p+0>=S7xP~Q3HP~Q2\P~Q4>P~I0CD6D6D6D6D6D6D6D6&0r~Q6:P8Q5dP6Q6KDHPFQ72=`=Pp+0AfS3H,AbA`1TWp+0AgS7y,AbQ3H,98p+0AhS7zQ3H,97p+0AiS7{Q6y,96p+0AjS7|Q3H=`6Rp+0AkS7},Abp+0AlS7~Q6>726PFQ7<?26=PFp+0AnS80Q6Y726PFp+0AeS6Y,9Cp+0AoS81Q6|Q0I5`Bp+0B0S82,Abp+0B1S83Q3m728PFQ81,93p+0B2S3mQ80,9Cp+0B3S84Q7q=`6Mp+0B4S85,AbQ3H20z785`EQ2j,Abp+0B6S86Q1I726PFp+0B7S87Q0_726PFQ2j,9CQ6nQ85,9Dp+0B9S88Q7}=`4Q1Abyp+0AbS8920|785`zQ7L,Abp+0B<S8:Q0@726PFp+0B=S8;Q2S726PFQ8:,9Ep+0B>S8<19zyQ6sQ83,9PP0Q8;,9ap+0BARTQ88,9hQ78Q6np+0A7S8=5`Dp+0BCS8>,Abp+0BDS8?Q5[724PFp+0BES8@?24SPFp+0BFS8AQ1H724PFQ75p+0=HS8B724PFp+0BHS8CQ0I724PFQ6B20yD37`yp+0BIS8D,AbQ2lQ83'9p+0BJS8EQ6sp+0<OS8F5`Cp+0BKS8G,AbQ8=Q2UQ8=PqQ8=Q1rQ8=Q2SQ8=Q1CQ8=p+0>bS8HQ8=p+0>eS8IQ8=Q3BQ8=Q0GQ8=Q1PQ8=FoD6D6D6Q6LQ8EPnEdPCePCQ7:Q1HQ7:Q2SQ7:PHQ7:P{Q7:Q3lQ7:p+0>cS8JQ7:p+0>fS8KQ7:Q3sQ7:Q0HQ7:Q4{Q7:FoD6D6D6p+0=QS8LQ8<PnEdP3eP3Q7DPqQ7DP{Q7DPNQ7DPeQ7DQ0rQ7Dp+0>dS8MQ7Dp+0>gS8NQ7DQ6RQ7DQ0IQ7DQ6aQ7DFoD6D6D6p+0=RS8OQ8@PnEdP4eP4Q6BQ8?Q6BQ2j'901BB3`Q7j,AbQ7F?24OPFQ79,9hp+0BQS8Pp+0BMS8Q,9xp+0BRS8RQ2lQ8P'9p+0BSS8SQ8PQ1H5`DQ7C,Abp+0BUS8T?26HPFQ7rQ0Q726PFPtQ8GP6p+0>_S8UCxp+0BWS8V,Abp+0BXS8Wp+0;;S8X72BPFQ7r=`h{Q7E,AbQ7F,9xp+0BZS8YQ7FQ7b5`3Q7G,Abp+0B\S8ZQ3p728PFQ8R,9Dp+0B]S8[Q79Q7f5`7p+0B^S8\,AbPzQ7CP8p+0>OS8]CxQ7O,Abp+0B`S8^Q7b727PFP4Q8PQ75,94p+0CYS8_p+0?oS8`+0DCxp+0BaS8a,AbQ8\p+0<fS8b5`6p+0BbS8c,AbQ8V,9Bp+0BcS8dQ7OQ7k5`8p+0BdS8e,AbP3Q8aP8p+0?DS8fCxp+0BeS8g,AbQ7_Q5|727PFQ8Z,9Bp+0BgS8hQ8W,96p+0BhS8iQ7_,9Bp+0BiQ7_,94p+0BjS8jQ7_,93p+0BkS8kQ8j,9Cp+0BlS8lQ8e,9Dp+0BmS8mQ8e,9Ep+0BnS8nQ8e,9zp+0BoS8oQ8e,9Pp+0C0S8pQ8d,9ap+0C1S8qQ8d,9hp+0C2S8rQ8c,9xp+0C3S8sQ2lQ8c'9Q7nQ8c,9Ip+0C5S8tQ2oQ8c'9p+0C6S8uQ8c,9=p+0C7S8vQ8c,9tp+0C8S8wQ6BQ8c'9p+0C9S8xQ6DQ8tP=Q6mCxp+0C:,Abp+0C;S8yQ8572tPFp+0C<Q8672tPFp+0C=Q0w72tPFp+0C>S8zp+0=BS8{72tPFp+0C?RyQ6n72tPFp+0C@Rop+0;cS8|72tPFp+0CAS8}Q1L72tPFp+0CBRsQ4O72tPFp+0CCR}Q8:72tPFp+0CDS8~Q8B72tPFp+0CES8BQ8;72tPFp+0CFS90Q0U72tPFp+0CGS91Q3c72tPFp+0CHS92Q3c72tPFp+0CIS93Q3c72tPFp+0CJS94Q3c72tPFp+0CKS95Q3c72tPFp+0CLS96Q3c72tPFp+0CMS97Q3c72tPF1181PF1161PF1141PF11C1PF11E1PF11P1PF11h1PFQ2l/11PFQ2o/11PF11t1PFQ6C/11PFQ6D/11PFQ2]/11PFQ2\/11PFQ3X/11PFQ14/11PFp+0C^Q2rQ91Q7wp+0>4S2rP8p+0>^S98p+0>]S99p+0>\S9:p+0>[S9;p+0>ZS9<p+0>YS9=p+0>XS9>Q0fQ1>Q5CQ1>'5Q1iQ0pN?2<p+0C`S9?Q9?[p+0>;S9@p+0=dS9A<068p+0CaS9BQ9B[Q94Q2r<097Q7{p+0E8S9C0016PAQ3jp+0>TS9D6067p+0CdS9EQ9E[p+0>?S9Fp+0=hS9G60B4Q9F00Q6p+0>8S9H&0Y7'4P5200VDA2A6Vp+0=iS9Ip+0>WS9J6066p+0ChS9KQ9K[Q9=Q3D80BC20QCBp+0>DS9LQ83Q5VQ83p+0:_S9MQ83Q5JQ83p+0:]S9NQ83p+0:\S9OQ83p+0:[S9PQ83PwQ83PCQ83I0CD6D6D6+1@p+0CjS9QQ9Q[p+0CcS9R,0BPFp+0>FS9SQ84Q0nQ84p+0:bS9TQ84Q5WQ84Q5VQ84Q9MQ84Q5JQ84Q9NQ84Q9OQ84PEQ84FoD6D6D6+1@p+0ClS9UQ9U[Q85p+0CUS9VQ2rQ24409Q85Q9Vp+0>5S9WQ1t409Q85Q9VQ3CQ2N409Q85Q9Vp+0>@S2N<09uQ85Q0lQ85Q5XQ85Q9TQ85Q5WQ85Q5VQ85Q9MQ85Q5JQ85Q9NQ85PzQ85FoD6D6D6D6D6Q85$0rp+0=nS9XQ9:6064p+0CnS9YQ9Y[Q98p+0>0S9Z80Bz20Qz3p+0=APBp+0=@PEp+0DoS9[DHPFQ8{P4Q6APzp+0E>S8{DHPFp+0=CP3Q43PPp+08QRuDHPFp+0=DS9\PCQ3OPaPuDHPFp+0=ES3OPDQ2zPhPuDHPFQ2rQ8H6063p+0D5S9]Q9][Q8MQ3C80Bh20QhCQ03,13RuPFPuPFPuPFPuPFPuPFQ7wp+0>hS9^6063p+0D<S9_Q9_[p+0>jp+0><S9`80Bx20QxCRuQ42/13PFQ3`/13PFQ26/13PFQ1\/13PFQ1V/13PFQ2Np+0>nS1V6063p+0DCS1\Q1\[p+0?0S9ap+0>BS9b80BxPuQ4C/13PFQ4R/13PFQ1h/13PFp+03cS9c/13PFQ1|/13PFQ9Sp+0?4S1|6063p+0DJS9dQ9d[p+0?6S9ep+0>HS9f80BxPuQ4K/13PFQ4V/13PFQ1q/13PFQ1j/13PFQ1d/13PFp+0>LS9gQ126063p+0DQS9hQ9h[Q4_/14PFQ4[/14PFp+0?>S9ip+0>PS9j80BI20QIERuQ1y/13PFQ1{/13PFp+03mS9k/13PFQ9:Q1g6063p+0DXS9lQ9l[Q4e/13PFQ4a/13PFQ2V/14PFQ1z/14PFQ1>Q9>80B=20Q=PQ1s/13PFQ9=Q9c6063p+0D_S1zQ1z[Q2L/1BPFQ2V/1BPFQ2TQ8K80BIPuQ2A/1BPFQ99Q2<606Bp+0DdS99Q99[Q1hQ8U80Ba20Qa4Q1}/17PFQ8UQ2W6067p+0DgS8UQ8U[Q51/18PFQ2>/11PFQ1w/11PFP|Q0Zp+0CfS51P6p+0?AS2WD<Q37p+0DlS37P|p+0;jS2<Q99P1Q8xQ16p+0?CS2LP8GfW7Q37PF]7p+0DmS9mP|Q1cQ99P1Q8xQ3\Q8fP7GfW7Q9mPF]7p+0DnS3\p+0@1S1cQ1|32Q9[Q1cp+09KS9n32p+0E0S9oQ1cQ9c32p+0E1S9pQ1cQ1^32p+0E2S1^Q1c;2pp+0D0S9qp+0?GRu'0p+0?HS9rp+0FES9s'0Q8;Q8:Q8:Q7LPfPgPlPjP^Q8<P:Q88CLP;Pkb5b6b4X05Q9]/01p+0FBS9t,58S9u#TS9v[^05P1Q6kPBO2b1b2b3Q8;Q8:Q8:Q7LPfPgPlPjP^p+0D\S9wP:Q6nCLP;Pkb5b6b4X05p+0FIS9x,01Q9uQ9p'V[^05P1Q6kP6O2b1b2b35]up+0=TS9y/@uQ8<Q8;Q8;Q8:PfPgPlPjP^Q6sP:Q86CLP;Pkb5b6b4X05p+0D6S9z/01p+0F8S9{,58S9|#T[^05P1p+0?MS9}P4O2b1b2b3Q8<Q8;Q8;Q8:PfPgPlPjP^p+0D]S8:P:Q2jCLP;Pkb5b6b4X05p+0FJS9~,01Q9|Q1^'V[^05P1Q9}PBO2b1b2b35]up+0=SS9|/@uQ6sQ8<Q8<Q8;PfPgPlPjP^P0P:Q84CLP;Pkb5b6b4X05p+0D7S:0/01p+0F@S:1,58S:2#T[^05P1p+0?NS:3P3O2b1b2b3Q6sQ8<Q8<Q8;PfPgPlPjP^p+0D^S:4P:Q3mCLP;Pkb5b6b4X05p+0FKS:5,01Q:2p+0E3S:6'V[^05P1Q:3P4O2b1b2b35]uQ8O/@uP0Q6sQ6sQ8<PfPgPlPjP^PTP:Q82CLP;Pkb5b6b4X05p+0D8S:2/01p+0F9S:7,58S:8#T[^05P1p+0?OS:9PCO2b1b2b3P0Q6sQ6sQ8<PfPgPlPjP^Q1zP:Q81CLP;Pkb5b6b4X05p+0FLS::,01Q:8p+0E4S:;'V[^05P1Q:9P3O2b1b2b35]uQ8L/@uPTP0P0Q6sPfPgPlPjP^Q78P:Q7<CLP;Pkb5b6b4X05p+0D9S:8/01p+0FAS:<,58R3#T[^05P1p+0?PS:=PDO2b1b2b3PTP0P0Q6sPfPgPlPjP^p+0D`S:>P:Q7~CLP;Pkb5b6b4X05p+0FMS:?,01p+0E5S:@,V3[^05P1Q:=PCO2b1b2b35]uQ6L/@uQ78PTPTP0PfPgPlPjP^Q8>P:Q7|CLP;Pkb5b6b4X05p+0D:S:A/01p+0F:RC,58R3#T[^05P1p+0?QS:BPEO2b1b2b3Q78PTPTP0PfPgPlPjP^p+0DaS:CP:Q7{CLP;Pkb5b6b4X05p+0FNS:D,01p+0E6S:E,V3[^05P1Q:BPDO2b1b2b35]up+0=OS:F/@uQ8>Q78Q78PTPfPgPlPjP^Q8?P:Q3HCLP;Pkb5b6b4X05p+0D;S:G/01Q9v[^05P1p+0?RS9vPzO2b1b2b3Q8>Q78Q78PTPfPgPlPjP^p+0DbS:HP:Q6YCLP;Pkb5b6b4X05p+0FOS:I,01Q9up+0E7S:J'V[^05P1Q9vPEO2b1b2b35]uQ7t/@uQ8?Q8>Q8>Q78PfPgPlPjP^Q8@P:Q72CLP;Pkb5b6b4X05Q9_/01Q:5,58RE#T[^05P1p+0?SS9uPPO2b1b2b3Q8?Q8>Q8>Q78PfPgPlPjP^p+0DcS:KP:Q89CLP;Pkb5b6b4X05p+0FPS:L,01Q9C,VE[^05P1Q9uPzO2b1b2b35]uQ7u/@uQ8@Q8?Q8?Q8>PfPgPlPjP^Q8AP:Q7bCLP;Pkb5b6b4X05p+0D=S7u/01p+0F<Rz,58RE#T[^05P1p+0?TS9CPaO2b1b2b3Q8@Q8?Q8?Q8>PfPgPlPjP^Q99P:Q6hCLP;Pkb5b6b4X05p+0FQRD,01p+0E9S:M,VE[^05P1Q9CPPO2b1b2b35]up+0<TS:N/@uQ:BQ8AQ8@Q8@Q8?PfPgPlPjP^Q75P:p+0AJS:OCLP;Pkb5b6b4X05p+0D>S:P/01Q9x,58RP#T[^05P1p+0?US:QPhO2b1b2b3Q8AQ8@Q8@Q8?PfPgPlPjP^p+0DeS:RP:Q7MCLP;Pkb5b6b4X05p+0FRS:S,01p+0E:S:T,VP[^05P1Q:QPaO2b1b2b33]Q8FQ:B'@Q9rQ75Q8AQ8AQ8@PfPgPlPjP^Q8CP:Q7ICLP;Pkb5b6b4X05p+0D?S:U/01p+0FCS:V,58Ra#T[^05P1p+0?VS:WPxO2b1b2b3Q75Q8AQ8AQ8@PfPgPlPjP^p+0DfS:XP:Q7XCLP;Pkb5b6b4X05p+0FSS7X,01p+0E;S:Y,Va[^05P1Q:WPhO2b1b2b33]p+0<NS:ZQ9r'@Q9rQ8CQ75Q75Q8APfPgPlPjP^Q8DP:Q7iCLP;Pkb5b6b4X05p+0D@Rh/01Q9s,58Ra#T[^05P1p+0?WS:[Q2lO2b1b2b3Q8CQ75Q75Q8APfPgPlPjP^Q8UP:Q7QCLP;Pkb5b6b4X05p+0FTS:\,01p+0E<S:],Va[^05P1Q:[PxO2b1b2b33]Q6MQ9r'@Q9rQ8DQ8CQ8CQ75PfPgPlPjP^Q8EP:p+0AAS:^CLP;Pkb5b6b4X05p+0DAS:_/01p+0F?S:`,58Rx#T[^05P1p+0?XS:aPIO2b1b2b3Q8DQ8CQ8CQ75PfPgPlPjP^p+0DhS:bP:p+0A@S:cCLP;Pkb5b6b4X05p+0FURa,01p+0E=,Vx[^05P1Q:aQ2lO2b1b2b33]p+0<LS2lQ9r'@Q8EQ8DQ8DQ8Cp+0@NS:dQ8?P1Q6mQ2oO2b1b2b3Q8EQ8DQ8DQ8Cp+0@MS:ep+0CkS:fP1Q6mPIO2b1b2b35]up+0:SS:gQ9rQ8GQ8EQ8EQ8DP~Q8@P1Q6~P=O2b1b2b3Q8GQ8EQ8EQ8DQ:dQ9UP1Q6~Q2oO2b1b2b33]p+0:Tp+0?IS2op+0BLS:hQ8GQ8GQ8Ep+0@PS:iQ8AP1p+0?[S:jPtO2b1b2b3Q:hQ8GQ8GQ8EP~p+0CmS:kP1Q:jP=O2b1b2b33]p+0:US:lp+0?JS:mQ8QQ:hQ:hQ8Gp+0@QS:nQ75P1Q74Q6BO2b1b2b3Q8QQ:hQ:hQ8GQ:iQ9YP1Q74PtO2b1b2b33]p+0:VS:op+0?KS:pQ79Q8QQ8QQ:hp+0@RS:qQ8CP1Q7]Q6CO2b1b2b3Q79Q8QQ8QQ:hQ:np+0CoS:rP1Q7]Q6BO2b1b2b33]p+0:WS6BQ6kQ7jQ79Q79Q8QQ6vQ8DP1p+0?^S:sQ2}O2b1b2b3Q7jQ79Q79Q8QQ:qQ9qP1Q:sQ6CO2b1b2b33]Q69Q9}Q7FQ7jQ7jQ79Q6wQ8EP1p+0?_S6CQ6DO2b1b2b3Q7FQ7jQ7jQ79Q6vp+0D1S:tP1Q6CQ2}O2b1b2b33]Q6:Q:3Q8PQ7FQ7FQ7jp+0@US2}Q8GP1p+0?`S:uQ2^O2b1b2b3Q8PQ7FQ7FQ7jQ6wp+0D2S:vP1Q:uQ6DO2b1b2b33]PwQ:9Q8RQ8PQ8PQ7Fp+0@VS:wQ:hP1p+0?aS:xQ2]O2b1b2b3Q8RQ8PQ8PQ7FQ2}p+0D3S:yP1Q:xQ2^O2b1b2b33]Q9PQ:=Q8SQ8RQ8RQ8PQ7oQ8QP1p+0?bS:zQ2sO2b1b2b3Q8SQ8RQ8RQ8PQ:wp+0D4S:{P1Q:zQ2]O2b1b2b33]Q9OQ:BQ7CQ8SQ8SQ8RQ70Q79P1p+0?cS:|Q2\O2b1b2b3Q7CQ8SQ8SQ8RQ7oQ9]P1Q:|Q2sO2b1b2b33]Q9NQ9vQ8TQ7CQ7CQ8Sp+0@YS:}Q7jP1p+0?dS:~Q10O2b1b2b3Q8TQ7CQ7CQ8SQ70Q9zP1Q:~Q2\O2b1b2b33]Q5JQ9uQ7rQ8TQ8TQ7Cp+0@ZS;0Q7FP1Q7mQ3XO2b1b2b3Q7rQ8TQ8TQ7CQ:}Q:0P1Q7mQ10O2b1b2b33]Q9MP>p+0?iS;1p+0>2S;2p+0F_S;3H2;Q0d522Q;3Q5L'0Q5MQ;3p+0F^S0d3Pp+0?lS;4Q5NQ5UQ5pQ31Q1xQ1hK29Q01p+0?mS01Q5OQ5vQ5nQ32Q1jQ1xp+0?nS;5Q1x+1TQ32Q5QQ5QQ2Jp+0EYS;6,AbRtQ8`P|P1p+0DUS;7Q1Np+0@0S;8D<+0mp+0EZS;9P1p+0EJS;:p+0DTS;;H1=Q;9p+0EWS;<,91S;=Q5`Q;9p+0EVS;>,91S;?Q:sQ;9p+0EUS;@,91S;Ap+0DSS;BQ;9p+0EXS;C,91R=Q7xQ;9p+0EQS;D,91S;EQ2DQ;9p+0EPS;F,91RIQ5PQ;9p+0EOS;G,91RxQ;BQ;9p+0ENS;H,91RPQ:sQ;9P1p+0ELS;Ip+0DRS;JQ;9P1p+0EKS;KQ2KQ;9P1p+0EIS;LQ:nQ;9P1p+0EHREQ:iQ;9P1p+0EGS;MP~Q;9P1p+0EFS;NQ:dQ;9P1p+0EES;OQ:eQ;9P1p+0EDS;Pp+0@LS;QQ;9P1p+0ECS;RQ7aH1=DvDvDvDvDvDvDvDvFwFwFwFw41SXAt+1<[[[[[P1p+0DOS;SQ4}Q3532p+0DPS;TQ4}Q5s32Q9hQ4}Q3232Q;Jp+0@5S;Up+0G1S;VQ4|p+0F\S;W40lPVQ;RQ1{-0TVRt+0SI0>Q;Bp+0@6S;Xp+0G2S;Yp+0:<S;ZQ;W40lPVQ;P00StI0>p+0@7S;[Q1{+1TQ00Q;UQ1KQ35Q2;Q2;Q32p+0EcS;\,AbRtp+0@9S;]P|P1Q1zQ0Xp+0@:S;^D<+0mp+0EdR3p+0ETS;_,91S;`Q:432P3P1p+0EaS;aQ5pP3P1p+0E`S;bp+0?hS;cP3P1p+0E_S;dQ8:P3p+0EbS;e,91S;fp+0>GS;gP3p+0E[S;h,91S;iQ5`P3P1Q;9Q5FP3Q;6,91S;jQ8:P3P=Q;cP3Q;?Q9wP3Q;AQ34P3p+0ESS;k,91S;lp+0@[S;mP3p+0ERS;n,91S;oQ;0P3Q;EQ:}P3PIQ70P3PxQ7oP3PPQ:wP3P1p+0EMS;pQ2}H1=FwFwFwFwFwDvFwDvDvDv41SXAt+1<[[[[P1Q;[Q1qQ2:Q2`Q2`Q5ap+0EfS35,AbS;qQ;qp+0@<RtP|P1Q:HPUp+0@=S;rD<+0mp+0EgRPQ;=Q:CPP1913Q5QPPP1Q;\p+0?kRxPPQ;fQ:>PPp+0EeS;f,91p+0>JS;=PPP1p+0E^S;sQ1]PPP1p+0E]S;tQ5GPPP1p+0E\S;uQ:>PPQ;iPxPPQ;jQ1zPPP=Q5`PPQ;?p+0@^S;?PPQ;AQ6pPPQ;`Q6jPPQ;lQ;mPPQ;oQ;0PPQ;EQ:}Q7092PIH28FwFwFwFwDvDvDvFwDvFwS;E'1WAQ1>p+0@;S1>Q0B+0mQ1WQ0['1Q1>P|P21AbPQ;I:0;b3Q6uP~n0100000020000Q8pp+0@@S;oPtD<Q0BQ:OP|P>Q6uQ:HQ;oPtg01b<RIP3P3p+0DYS;lg01cF%}Ig01dPN=0PQ;Kp+0F]S;`P1p+0G=S;AQ9lQ8qQ;`#NQ;AQ9lQ;AQ8qCKdO4b9Q35p+0G<S;jQ;WP@Q;jQ;W'UdQ8pDRPPQ9lP|Q:nP1p+0@BS;ip+0@>S;vQ0DEJX7PPPQ01P|Q77Q35P1Q;ICxQ;lQ;iQ;vQ0DEJX7PQ1>p+0EhRIp+0>KS;wp+0G>S;xQ;I,41S;y'O32X;5Q;AQ1>Q;K40l,yPQ;AQ01'iQ1>Q8oQ8nQ8nQ8mPfPgPlPjP^Q8pP:Q;3CLP;Pkb5b6b4X05Q8U/01Q0\[^05P1Q;vQ0?O2b1b2b3Q8oQ8nQ8nQ8mPfPgPlPjP^Q;HP:Q;lCLP;Pkb5b6b4X05p+0G;S;z,01Q;\,V8[^05P1Q;vQ0=O2b1b2b3K0Mp+0<cS;{eQ;{PIQ;wP|Q6xPPP1p+0DZS;|p+0@CS;}p+0@?S;~PWGfX7IP|Q67Q;lQ;iQ;vD<P|Q67Q8kQ0ZQ;vD<Q0DQ7RP|P>Q67Q;lQ;iQ;vg01eZQ35Q;eQ;;PxQ0~g01fdPng01gnQ:lp+0;8S<0p+0EiS<1Q9gQ<1p+0EjS<2P1p+0FbS<3p+0DVS<4Q01I0HW7Q;5Q<2p+0G@S<5Q;V,41S<6Q01H03X;5Q<1Q;BQ;BQ;5p+0G0S<7Q1>Q8kQ8qQ8pQ8pQ8oPfPgPlPjP^Q8oQ;HQ<4H0<P;Pkb5b6b4X05Q;f,51S<8p+0G3S<9p+0G5S<:,51S<;404^05P1Q;oO1S<<b1b2b3L0@Q;{Q3aDDQ<1Q9gQ<7Q;4C{ep+0;nS<=P1E=b<Q;BQ;{Q;BQ77Q;ePnJ0IQ6oeQ6oQ<1p+0@hS<>Q<1Q<2Q0g721W7Q0?p+0;mS<?P1E=b<Q;iQ;wPxp+0G8S<@PVQ01p+0DNS<Ap+0<aS<Bp+0<`S<CQ7pQ8pQ8oQ8oQ8nQ6}Q<AP1Q;~Q0?O2b1b2b3Q65Q3^G_p+0;6S<DeQ2^Q01Q9f,01X;5Q;^Q;5/01X;5Q8pQ8oQ8oQ8nPfPgPlPjQ8nQ;75>^P;Pkb5b6b4X051513S2^p+0G4S<E,51S<F'0^05P1Q;~O1R=b1b2b3Q;gQ3nDDQ65Q3^DDQ65Q;g'0eQ;^p+0FWS<GQ7p5P1X;5Q01Q:uQ;M80?1X;5Q6Cp+0>IS<H'0Q:sQ9f'0P[p+0FYS<IQ6CQ:sQ9SQ<HQ9fp+0<_S<JG3Q8pQ8oQ8oQ8nPfPgPlPjQ8jQ7U5>^P;Pkb5b6b4X05Q<FQ<EQ2^P3H05^05P=b1b2b3Q65Q3^G_Q;gQ3nDDQ;gp+0FVR=Q2<3PeN907NB08Q;pQ;3P1p+0G?S3^p+0DLS2^Q8l%N=S<KQ3^Q2^Q3^Q8lCKdO4b9PIQ;xPaP@Q;x/UadQ8kDRQ<1Q2^Q<1P|p+0<gS8kP1Q0[Q;oPXEJW7P|Q8bQ2^Q0]Q;~D<P|Q8bQ8gQ0wQ;~D<PWQ7SP|P>Q8bQ2^Q0]Q;~g01i8PPQ;bp+0DKS<LPxp+0@gS<Mg01jBPng01kLQ:op+0;9S<NQ<2p+0>MS<OQ<2p+0EkS<PP1p+0FcS<Qp+0DMS<RQ01I0HW7Q8`Q<Pp+0GAS<Sp+0FkS<T,41Q01H03X;5Q<2Q;;Q;;Q8`p+0FjS<UQ1>Q8lQ8rQ8qQ8qQ8pPfPgPlPjP^Q8pQ;KQ;TH0<P;Pkb5b6b4X05Q35,51S<Vp+0FmS<WQ<T,51S<X404^05P1p+0@AS<YO1S<Zb1b2b3L0@p+0<dS<[PrDDQ<2Q<OQ<UQ;4C{ep+0;oS<\P1E=b<Q;;Q<[Q;;Q6xQ;bPnJ0IQ<DeQ<DQ<2Q<>Q<2Q<PQ6t721W7Q<2Q<>Q7pP1Fbb<PVQ;}Q0]PxQ0XQ;}Q9gPxp+0G9S<]PVQ;5Q;SQ65Q<BQ6QQ8qQ8pQ8pQ8op+0A0S<^Q;SP1Q;oP9O2b1b2b3Q;{Q3aG_Q6oeQ2]Q;5Q;g,01X;5Q;^Q8`/01X;5Q8qQ8pQ8pQ8oPfPgPlPjQ8oQ;S5>^P;Pkb5b6b4X05Q<8Q<U,51R9'0^05Q<<b1b2b3Q9SQ3nDDQ;{Q3aDDQ;{Q9S'0eQ;^p+0FXS;SQ6Q5P1X;5Q;5Q:s@0?1EX;5Q7]Q;='0Q74Q<H'0P[p+0FZS2]Q7]Q74p+0>ES6oQ;=Q<HQ<CG3Q8qQ8pQ8pQ8oPfPgPlPjQ8hQ7W5>^P;Pkb5b6b4X05P9Q<:Q<8Q;fH05^05Q<<b1b2b3Q;{Q3aG_Q9SQ3nDDQ9SQ<GQ7p3PeN907E;NB08Q;Hp+0F`S<<P1Q<5Q9dQ7_Q<KQ<5Q9dQ<5Q7_CKdO4b9Q<1Q3^PaP@Q3^/UadQ8gDRQ<2Q9dQ<2P|p+0<hS<8P1Q0ZQ<YPUEJW7P|Q8kQ9dQ0fQ;oD<P|Q8kQ8cQ0VQ;oD<PXQ7UP|P>Q8kQ9dQ0fQ;og01lVPIQ;bp+0DIS<_PxQ<Mg01m`Png01njQ6Bp+0;:S<`Q<Pp+0>NS<aQ<Pp+0ElS<bP1p+0FdS<cQ<LQ01I0HW7Q;8Q<bp+0GBR9Q<W,41S<dQ01H03X;5Q<PQ;7Q;7Q;8p+0FlS<eQ1>Q8mQ8sQ8rQ8rQ8qPfPgPlPjP^Q8qQ;:Q<AH0<P;Pkb5b6b4X05151PS8mp+0FoS<fQ<9,51S<g404^05P1Q;iO1S<hb1b2b3L0@Q67PrDDQ<PQ<aQ<eQ;4C{ep+0<0S<iP1E=b<Q;7Q67Q;7Q6zQ;bPnJ0IQ<DeQ<DQ<PQ<>Q<PQ<bQ6t721W7Q<PQ<>Q7pP1Fbb<PVQ0[Q0fPxQ0UPVQ7VQ0[PxQ0wQ7VQ<OPxp+0G:S<jPVQ8`Q;TQ;{Q65Q<?Q8rQ8qQ8qQ8pQ73Q;TP1Q<YQ0{O2b1b2b3Q<[PrG_Q<0eQ2sQ8`Q9S,01X;5Q;^Q;8/01X;5Q8rQ8qQ8qQ8pPfPgPlPjQ8pQ<R5>^P;Pkb5b6b4X05Q<VQ;Y,51S2s'0^05Q<Zb1b2b3Q6oQ3nDDQ<[PrDDQ<[Q6o'0eQ;^Q<IQ<?5P1X;5Q8`Q74Q;L80?1X;5Q:jQ;w'0Q6~Q;='0P[p+0F[S<kQ:jQ6~Q9LQ;wQ;=Q<BG3Q8rQ8qQ8qQ8pPfPgPlPjQ8eQ7Z5>^P;Pkb5b6b4X05Q2sp+0G6S2sQ<VQ35H05^05Q<Zb1b2b3Q<[PrG_Q6oQ3nDDQ6oQ;SQ6Q3PeN907E;E;NB08Q;Gp+0FaP1Q<Sp+0DHS<ZQ8dQ<KQ<SQ<ZQ<SQ8dCKdO4b9Q<2Q<5PaP@Q<5/UadQ8cDRQ<PQ<ZQ<PP|p+0<iS<VP1Q0XQ;iQ0EEJW7P|Q<8Q<ZQ0WQ<YD<P|Q<8Q7OQ4^Q<YD<PUQ7WP|P>Q<8Q<ZQ0WQ<Yg0204Q<1Q;bp+0DGS<lPxQ<Mg021>Png022HQ69Q8XQ<bQ8]Q<bp+0EmS<mP1p+0FeS<nQ<_Q01I0HW7Q1cQ<mp+0GCS<op+0FgS<p,41S<qQ01H03X;5Q<bQ<4Q<4Q1cp+0FfS<rQ1>Q8nQ7nQ8sQ8sQ8rPfPgPlPjP^Q8rQ;LQ2^H0<P;Pkb5b6b4X05151IS<sp+0FiS<tQ<e,51S<u404^05P1Q;}O1S<vb1b2b3L0@Q8bPrDDQ<bQ8]Q<rQ;4C{ep+0<1S<wP1E=b<Q<4Q8bQ<4Q6}Q;bPnJ0IQ<DeQ<DQ<bQ<>Q<bQ<mQ6t721W7Q<bQ<>Q7pP1Fbb<PVQ0ZQ0WPxQ0TPVQ0~Q0ZPxQ0VPVp+0@ES<xQ0~PxQ0fQ<xQ<aPxQ;zPVQ;8Q9hQ<[Q;{Q<=Q8sQ8rQ8rQ8qp+0A2S<yQ9hP1Q;iQ11O2b1b2b3Q67PrG_Q<NeQ2\Q;8Q6o,01X;5Q;^Q1c/01X;5Q8sQ8rQ8rQ8qPfPgPlPjQ8qQ<L5>^P;Pkb5b6b4X05Q8mQ<X'0^05Q<hb1b2b3Q9LQ3nDDQ67PrDDQ67Q9L'0eQ;^Q2]Q<=5P1X;5Q;8Q6~Q;:80?1X;5Q6mQ9g'0Q:aQ;w'0P[Q;WQ6mQ:ap+0>CS;:Q9gQ;wQ65G3Q8sQ8rQ8rQ8qPfPgPlPjQ8aQ7[5>^P;Pkb5b6b4X05Q<Xp+0G7S<XQ8mPPH05^05Q<hb1b2b3Q67PrG_Q9LQ3nDDQ9LQ<IQ<?3PeN907E;E;E;NB08Q;FQ<3P1P9p+0DFS<3Q8^Q<KP9Q<3P9Q8^CKdO4b9Q<PQ<SPaP@Q<S/UadQ7ODRQ<bQ<3Q<bP|Q5|P1Q1LQ;}Q0FEJW7P|Q<VQ<3Q20Q;iD<P|Q<VQ8ZQ0QQ;iD<Q0EQ7ZP|P>Q<VQ<3Q20Q;ig023RQ<2Q;bp+0DES<?PxQ<Mg024\Png025fQ6:Q76Q<mQ9jQ<mp+0EnS6:P1Q<rQ<lQ01I0HW7p+0@2S<hQ6:p+0GDS8mQ<t,41Q01H03X;5Q<mp+0DWS2\Q2\Q<hp+0FhS<NQ1>Q8oQ8tQ7nQ7nQ8sPfPgPlPjP^Q8sPEQ9dH0<P;Pkb5b6b4X05Q<1,51S9dQ<TQ<F404^05P1Q7VO1S11b1b2b3L0@Q8kPrDDQ<mQ9jQ<NQ;4C{ep+0<2S<NP1E=b<Q2\Q8kQ2\Q<^Q;bPnJ0IQ<DeQ<DQ<mQ<>Q<mQ6:Q6t721W7Q<mQ<>Q7pP1Fbb<PVQ0XQ20PxQ1YPVQ0]Q0XPxQ4^PVQ1XQ0]PxQ0WPVp+0@FS<zQ1XPxQ0ZQ<zQ8]PxQ;jPVQ1cQ;JQ67Q<[Q<\Q7nQ8sQ8sQ8rp+0A3S<{Q;JP1Q;}Q0BO2b1b2b3Q8bPrG_Q<`eQ10Q1cQ9L,01X;5Q;^Q<h/01X;5Q7nQ8sQ8sQ8rPfPgPlPjQ8rQ<_5>^P;Pkb5b6b4X05Q<sQ<g'0^05Q<vb1b2b3Q;:Q3nDDQ8bPrDDQ8bQ;:'0eQ;^Q<kQ<\5P1X;5Q1cQ:aQ;K80?1X;5Q:[Q<O'0Q:WQ9g'0P[Q;`Q:[Q:WQ9bQ<OQ9gQ;{G3Q7nQ8sQ8sQ8rPfPgPlPjQ8\Q7`5>^P;Pkb5b6b4X05Q<gQ<@Q<sPIH05^05Q<vb1b2b3Q8bPrG_Q;:Q3nDDQ;:Q2]Q<=3PeN907E;E;E;E;NB08Q;DQ<QP1Q<op+0DDS<QQ8[Q<KQ<oQ<QQ<oQ8[CKdO4b9Q<bP9PaP@1U9adQ8ZDRQ<mQ<QQ<mP|Q5~P1Q0hQ7VPKEJW7P|Q5|Q<QQ1MQ;}D<P|Q5|Q7EQ0RQ;}D<Q0FQ7[P|P>Q5|Q<QQ1MQ;}g0270Q<PQ;bQ1\PxQ<Mg028:Png029DPwp+0;=S<=Q6:Q6]Q6:p+0EoS<vP1Q<pQ<?Q01I0HW7Q7@Q<vp+0GES<sQ<j,41Q01H03X;5Q6:Q9lQ9lQ7@Q<]Q1>Q8pQ8uQ8tQ8tQ7nPfPgPlPjP^Q7nQ;MQ<ZH0<P;Pkb5b6b4X05Q<2,51S<ZQ;jQ<W,51404^05P1Q<xO1S;Mb1b2b3L0@Q<8PrDDQ6:Q6]Q<]Q;4C{ep+0<3P1E=b<Q9lQ<8Q9lQ73Q;bPnJ0IQ<DeQ<DQ6:Q<>Q6:Q<vQ6t721W7Q6:Q<>Q7pP1Fbb<PVQ1LQ1MPxQ0SPVQ0wQ1LPxQ0QPVQ0[Q0wPxQ20PVQ0gQ0[PxQ0XPVp+0@GS8pQ0gPxQ0]Q8pQ9jPxQ;APVQ<hQ;BQ8bQ67Q<iQ8tQ7nQ7nQ8sp+0A4S<gQ;BP1Q7VQ0CO2b1b2b3Q8kPrG_Q8XeQ3XQ<hQ;:,01X;5Q;^Q7@/01X;5Q8tQ7nQ7nQ8sPfPgPlPjQ8sQ<l5>^P;Pkb5b6b4X05Q9dQ<u'0^05Q11b1b2b3Q9bQ3nDDQ8kPrDDQ8kQ9b'0eQ;^Q;WQ<i5P1X;5Q<hQ:WQ;y'0X;5Q:QQ<a'0Q9CQ<O'0P[Q0dQ:QQ9Cp+0>AS;yQ<aQ<OQ<[G3Q8tQ7nQ7nQ8sPfPgPlPjQ7GQ6h5>^P;Pkb5b6b4X05Q<uQ<]Q9dQ<1H05^05Q11b1b2b3Q8kPrG_Q9bQ3nDDQ9bQ<kQ<\3PeN907E;E;E;E;E;NB08Q;nQ<cP1Q8mp+0DBS<cQ8YQ<KQ8mQ<cQ8mQ8YCKdO4b9Q<mQ<oPaP@Q<o/UadQ7EDRQ6:Q<cQ6:P|Q61P1Q1GQ<xQ0GEJW7P|Q5~Q<cQ0OQ7VD<P|Q5~Q7rQ1rQ7VD<PKQ7`P|P>Q5~Q<cQ0OQ7Vg02:NQ<bQ;bQ:_PxQ<Mg02;XPng02<bQ9Pp+0;>Q<vp+0>RS<\Q<vp+0F0S11P1Q8VQ01C{W7Q7NQ11p+0GFS9dQ<9,41S<uQ01H03X;5Q<vQ;lQ;lQ7NQ;YQ1>Q8qQ8vQ8uQ8uQ8tPfPgPlPjP^Q8tQ;NQ<3H0<P;Pkb5b6b4X05Q<P,51S<3Q<:Q<;404^05P1Q<zO1S<;b1b2b3L0@Q<VPrDDQ<vQ<\Q;YQ;4C{ep+0<4P1E=b<Q;lQ<VQ;lQ<yQ;bPnJ0IQ<DeQ<DQ<vQ<>Q<vQ11Q6t721W7Q<vQ<>Q7pP1Fbb<PVQ0hQ0OPxP\PVQ0YQ0hPxQ0RPVQ0fQ0YPxQ1MPVQ0~Q0fPxQ1LPVQ4gQ0~PxQ0wPVQ6gQ4gPxQ0[Q6gQ6]PxQ;xPVQ7@Q;;Q8kQ8bQ<wQ8uQ8tQ8tQ7np+0A5S8sQ;;P1Q<xQ0DO2b1b2b3Q<8PrG_Q76eQ2~Q7@Q9b,01X;5Q;^Q7N/01X;5Q8uQ8tQ8tQ7nPfPgPlPjQ7nQ<?5>^P;Pkb5b6b4X05Q<ZQ<F'0^05Q;Mb1b2b3Q;yQ3nDDQ<8PrDDQ<8Q;y'0eQ;^Q;`Q<w5P1X;5Q7@Q9CQ;p80?1X;5Q9uQ8]'0Q9vQ<a'0P[Q;3Q9uQ9vQ2NQ8]Q<aQ67G3Q8uQ8tQ8tQ7nPfPgPlPjQ8VQ7b5>^P;Pkb5b6b4X05Q<FQ<jQ<ZQ<2H05^05Q;Mb1b2b3Q<8PrG_Q;yQ3nDDQ;yQ;WQ<i3PeN907E;E;E;E;E;E;NB08Q;kQ<nP1Q<sPhQ8VQ<KQ<sPhQ<sQ8VCKdO4b9Q6:Q8mPaP@Q8m/UadQ7rDRQ<vPhQ<vP|Q63P1PNQ<zQ0HEJW7P|Q61PhPHQ<xD<P|Q61Q8RPdQ<xD<Q0GQ6hP|P>Q61PhPHQ<xg02=lQ<mQ;bQ:UPxQ<Mg02?6Png02@@Q9Op+0;?Q11p+0>SS<nQ11p+0F1S<iP1Q<tQ:_Q01I0HW7Q;UQ<ip+0GGS;WQ<dQ01H03X;5Q11Q;|Q;|Q;UQ<eQ1>Q8rQ8wQ8vQ8vQ8uPfPgPlPjP^Q8uPEQ<QH0<P;Pkb5b6b4X05Q<b,51Q<fQ;x,51404^05P1Q8pO1b1b2b3L0@Q5|Q;UQ8wQ8vQ8vQ8up+0A<S<dQ8rP1Q8pPUO2b1b2b3Q8wQ8vQ8vQ8uQ7=Q;lP1Q8pPXO2b1b2b3K0MQ11Q<nQ<eQ;4C{ep+0<5P1E=b<Q;|Q5|Q;|Q<{Q;bPnJ0IQ<DeQ<DQ11Q<>Q11Q<iQ6t721W7Q11Q<>Q7pP1Fbb<PVQ1GPHPxP<PVQ1NQ1GPxQ1rPVQ0UQ1NPxQ0OPVQ0ZQ0UPxQ0hPVQ1XQ0ZPxQ0YPVQ0nQ1XPxQ0fPVp+0@IS7pQ0nPxQ0~Q7pQ<\PxQ3^PVQ7NQ;7Q<8Q8kQ<NQ8vQ8uQ8uQ8tp+0A6S8wQ;7P1Q<zPWO2b1b2b3Q<VPrG_Q<=eQ14Q7NQ;y,01X;5Q;^Q;U/01X;5Q8vQ8uQ8uQ8tPfPgPlPjQ8tQ1\5>^P;Pkb5b6b4X05Q<3Q;A,51RW'0^05Q<;b1b2b3Q2NQ3nDDQ<VPrDDQ<VQ2N'0eQ;^Q0dQ<N5P1X;5Q7NQ9vQ;H80?1X;5Q:BQ9j'0Q:=Q8]'0P[Q<<Q:BQ:=Q9FQ9jQ8]Q8bG3Q8vQ8uQ8uQ8tPfPgPlPjQ7CQ7c5>^P;Pkb5b6b4X05PWQ;zQ<3Q<PH05^05Q<;b1b2b3Q<VPrG_Q2NQ3nDDQ2NQ;`Q<w3PeN907E;E;E;E;E;E;E;NB08Q;_Q<rP1Q9dQ:PQ8SQ<KQ9dQ:PQ9dQ8SCKdO4b9Q<vQ<sPaP@Q<s/UadQ8RDRQ11Q:PQ11P|p+0<nS<;P1PYQ8pQ0IEJW7P|Q63Q:PPSQ<zD<P|P2Q<i,AbQ;>:0;bPQ63Q<Dn0100000020000Q79PSQ<zD<Q0HQ7bP|P>Q63Q:PPSQ<zg02AJRrPPQ<PQ7ug02BT%}rg02C^N=0PQ;@Q<pP1Q;WQ7uQ7jQ<KQ;WQ7uQ;WQ7jCKdO4b9Q11Q9dPaP@Q9d/UadQ79DRQ<iQ7uQ<iP|Q<0P1P]Q6gPMEJW7Q9wQ61Q9wQ8sQ<bPnJ0IQ<DeQ<Dp+0F2S<DQ<yQ<DP|p+0=0S<0Q<2P1Q8RCxQ:UPJQ7pPLEJW7Q<DQ<yQ0IQ<DQ1uQ0IP|Q5fQ:PP]Q6gD<P|P2p+0F3S0I,AbQ;C:0;bIQ5fQ5`n0100000020000Q7jP]Q6gD<PMQ7dP|P>Q5fQ:PP]Q6gg02DhRrPIQ<vQ:Ug02F2%}rg02G<N=0PQ;<Q<tP1p+0GIS<KQ:PQ7FQ<G#NS<pQ<KQ:PQ<KQ7FCKdO4b9Q<Dp+0GHS<3P=P@Q<3/U=dQ7jDRQ0IQ:PQ0IP|Q30P1P\Q6lQ0JEJW7Q:4Q2:Q:4Q<;Q:4423Q8=Q11PnEdQ5`eQ5`p+0F4S8tQ8wQ8tP|Q5eQ<PP1Q7CCxPhQ1rQ7aQ0tEJW7Q8tQ8wPMQ8tp+0:PS7CPMP|Q36Q:UP\Q6lD<P|P2p+0F5S<P,AbQ:PQ36Q5`n0100000020000Q7FP\Q6lD<Q0JQ7fP|P>Q36Q:UP\Q6lg02HFRrQ<iQ;Og02IP%}rg02JZN<22Q;6Q<TP1p+0GKS<TQ:PQ8PQ<pQ<TQ:PQ<TQ8PCKdO4b9Q8tp+0GJS5eP=P@Q5e/U=dQ7FDRQ<PQ:PQ<PP|Q30P1PHQ;QPGEJW7Q;9Q<eP1p+0GLRrp+0DkS8uQ8PQ<f#NPrQ8uPrQ8PCKdO4b9Q<Pp+0DjS<<Q7F32p+0F6S14Q8uQ14P|Q5dQ8tP1PhPNQ:ePRGfW7P|Q36Q:UPHQ;QD<P|P2p+0F7RW,AbQ;u:0;bIQ36Q5gn0100000020000Q7FPHQ;QD<PGQ7hP|P>Q36Q:UPHQ;Qg02KdPIQ0IQ:PQ8}Q3\g02LnPng02N8Q:CQ7jQ:Cp+0:BS36Q:CQ5lQ:CQ6AQ:CFoQ7;Q0IPnEdQ5aeQ5aPWQ37Q9[Q0KQ<7>1Q1hPVQ7kI0>X7WQ;up+0FnS7;P1p+0GNS5dQ3\Q7FPEQ5dQ3\Q5dQ7FCKdO4b9Q9mQ7j52WQ9{Q3\Q9{Q9oQ0LP1PVp+0A^S8rI0>W7Q9[Q:nQ9[Q9oQ8r721W@Q6DQ0nQ3\<0GVP>Q:qQ:UQ<;Q:UQ63Q:UQ61Q:UQ5~Q:UQ5|Q:UQ<VQ:UQ<8Q:UQ0iQ:UI0CD6D6D6S:UQ<XPVPoPyPyQ8zPfPgQ0bPjP^P^P_Q;KQ;KQ;t5\^I0:P;Pkb5b6b4PhP1b1b2b3Q:PeQ7uQ9_P[Q<tQ;NQ;OQ:GQ11Q11Q8:G3PoPyPyQ8zPfPgQ0bPjQ:PQ;t5>^P;Pkb5b6b4Q:PP1b1b2b3H0aQ7ueQ:[Q76Q:WQ<wQ<XDHQ5Z/1{PVQ:aQ7V/4cRXQ<iQ:[PXQ<@EQX=Ap+0;5S<wQ:[p+0;iRXQ:[Q2<Q:[PXQ;:Q;gQ8kQ6oQ8bQ67Q:WQ9SPuQ9LP[Q<tQ;NQ;OQ:GQ;}Q;}Q:aG3P[Q<tQ6~Q6mQ9fQ<XQ<XPEG3EFE8E8PoPyPyQ8zPfPgPlPjP^Q;bP:P^PsP:P^Q8rP^Q7kP^P^Q<R,ph211^6S8kGrFCP;Pkb5b6b4X05X8Fp+0GMRX,01S2<Q:T/08S76Q<K,57RUPUQ14PUQ;WQ14Q;KPUP6E[CZ[[^05^8FP1Q;gP~PMPLO4b1b2b3DEQ<weQ6rQ:}Q5ZP{PVQ:WQ<x/4cS<wQ<iQ:QQ<wQ<@EQX=Ap+0;4S:PQ:Qp+0;gRUQ:QQ7lQ:QPUQ3cQ9bQ<[Q2NQ;{Q65Q9CQ;yp+0?FS<[Q9FP[Q<tQ;NQ;OQ:GQ7VQ7VQ:jG3P[Q<tQ7]Q74Q;=Q<XQ<XPEG3EFE8E8PoPyPyQ8zPfPgPlPjP^Q;bP:P^PsP:P^p+0A\S7lP^Q7qP^P^Q;T,phQ8kGrFCP;Pkb5b6b4X05X8FQ2<Q76Q<S,57RUPUQ14PUQ;WQ14Q;KPUP6E[CZ[[^05^8FP1Q9bP~PMPLO4b1b2b3DEQ:PeQ2fQ70Q5XPSPVQ9CQ<z/4cS;TQ<iQ9uQ;TQ<@EQX=AQ4JQ9up+0;eRUQ9uQ68Q9uPUp+0>9S68Q7xQ<BQ9@Q<CQ<JQ9vQ9`p+0?ES<BQ7wP[Q<tQ;NQ;OQ:GQ<xQ<xQ:sG3P[Q<tQ:uQ6CQ9gQ<XQ<XPEG3EFE8E8PoPyPyQ8zPfPgPlPjP^Q;bP:P^PsP:P^Q7hP^Q7gP^P^Q;B,phQ8kGrFCP;Pkb5b6b4X05X8FQ2<Q76Q<j,57RUPUQ14PUQ;WQ14Q;KPUP6E[CZ[[^05^8FP1Q7xP~PMPLO4b1b2b3DEQ4JeQ;?Q7oQ9TPHPVQ9vQ8p/4cS;BQ<iQ:BQ;BQ<@EQX=Ap+0;2RUQ:BQ8|Q:BQ6<Q:BQ8|Q2rQ9Hp+0<^Q3Cp+0<]S8|Q5zQ:=p+0>7S6<Q8fQ9WP[Q<tQ;NQ;OQ:GQ<zQ<zQ:xG3P[Q<tQ:|Q:zQ<aQ<XQ<XPEG3EFE8E8PoPyPyQ8zPfPgPlPjP^Q;bP:P^PsP:P^Q7fP^Q7eP^P^Q<4,phQ8kGrFCP;Pkb5b6b4X05X8FQ2<Q761579S<4#TS;MQ<4Q14Q<4Q;WQ14Q;KQ<4;n6Fm[[^05^8FP1Q9HP~PMPLO4b1b2b3DEPUeQ6pQ:wQ5WQ1GPVQ:=Q6g/4cS<ZQ<iQ:9Q<ZQ<@EQX=Ap+0;1S<FQ:9p+0;aRUQ:9p+0;bQ:9PUQ7Yp+0>3S7nQ5yp+0>1S5yQ5xQ5wQ:3Q;2Q2LQ9ZP[Q<tQ;NQ;OQ:GQ8pQ8pQ:~G3P[Q<tQ7>Q7mQ9jQ<XQ<XPEG3EFE8E8PoPyPyQ8zPfPgPlPjP^Q;bP:P^PsP:P^Q7dP^Q7cP^P^Q;l,phQ8kGrFCP;Pkb5b6b4X05X8FQ2<Q76Q;z,57S;p#TS<?Q;pQ14Q;pQ;WQ14Q;KQ;p;n6Fm[[^05^8FP1Q7nP~PMPLO4b1b2b3DEQ<FeQ6jQ2}Q5VQ1NPVQ:3Q7p/4cS5VQ<iQ9}Q5VQ<@EQX=Ap+0;0S<FQ9}Q6@Q9}p+0;`Q9}Q6@p+0=jS2~Q9XQ5up+0=lS0DQ5tQ6;Q6kp+0=mS8Xp+0?BS0CQ3DP[Q<tQ;NQ;OQ:GQ6gQ6gQ71G3P[Q<tQ;1Q;cQ<\Q<XQ<XPEG3EFE8E8PoPyPyQ8zPfPgPlPjP^Q;bP:P^PsP:P^Q7bP^Q6hP^P^Q9w,phQ8kGrFCP;Pkb5b6b4X05X8FQ2<Q76Q<o,57S9w#TS<_Q9wQ14Q9wQ;WQ14Q;KQ9w;n6Fm[[^05^8FP1Q9XP~PMPLO4b1b2b3DEQ<FeQ;mQ6wQ9MQ0UPVQ6kQ6l/4cS<`Q<iQ:pQ<`Q<@EQX=Ap+0:oS<|Q:pp+0;]RUQ:pp+0;^Q:pPUQ6[Q9IQ5{p+0=gS5{Q:NQ7\Q:mQ9GQ2WQ3jP[Q<tQ;NQ;OQ:GQ7pQ7pp+0?jS<}G3P[Q<tQ;4PxQ9DQ<XQ<XPEG3EFE8E8PoPyPyQ8zPfPgPlPjP^Q;bP:P^PsP:P^Q7`P^Q7[P^P^Q1z,phQ8kGrFCP;Pkb5b6b4X05X8FQ2<Q76Q;j,57S<~#TS=0Q<~Q14Q<~Q;WQ14Q;KQ<~;n6Fm[[^05^8FP1Q9IP~PMPLO4b1b2b3DEQ<|eQ;0Q6vQ0]PVQ:mQ7a/4cS=1Q<iQ2oQ=1Q<@EQX=Ap+0:nRUQ2op+0;[S=2Q2op+0;\Q2oQ=2p+0=`S2oQ9Ap+0<Rp+0=bS=3p+0<QS=4p+0<PS=5Q9rp+0=cS=6p+0?@S=7p+0=aS=8P[Q<tQ;NQ;OQ:GQ6lQ6lQ01G3P[Q<tQ8`Q;5p+0>VS=9Q<XQ<XPEG3EFE8E8PoPyPyQ8zPfPgPlPjP^Q;bP:P^PsP:P^Q7ZP^Q7WP^P^Q:X,phQ8kGrFCP;Pkb5b6b4X05X8FQ2<Q76Q;W,57S:XQ:XQ14Q:XQ;WQ14Q;KQ:XP6E[CZ[[^05^8FP1Q9AP~PMPLO4b1b2b3DEPUeQ0qQ5SI0`+0eGIGIGIGIGIGIGIQ<XQ:U80fVeL0iE=Q7FP1EGb9Q5gP1E=b<Q3\$0qNA0nQ;hQ<WP1PXQ:2Q8PQ<pPXQ:2PXQ8PCKdO4b9Q14PrP=P@1Ur=dQ7FDRPWQ:2P|Q1]P1Q0KQ:dQ1IEJX7WP|Q30Q:2PNQ:eD<P|P2Q9{,AbQ:_Q30Q27n0100000020000Q79PNQ:eD<PRQ7qP|P>Q30Q:2PNQ:eg02OBQ8tQ<1Q<QQ1ZQ31g02PLPng02QVQ:HQ8QQ:HQ7FQ:HQ5GQ:HQ5QQ:Hp+0=2S<QQ:HI0CD6Q7=Q<1PnEdQ33eQ33Q9{Q9oQ9{Q9oQ0LQ8W,M1PVQ31I0>W7Q;tQ<fP1p+0GOS7=Q9pQ79Q;OQ7=Q9pQ7=Q79CKdO4b9Q9{Q9oQ8Q32Q:7Q9pQ:7Q9pQ0SP1PVQ32I0>W7Q9oQ:nQ9oQ9pQ32721W@Q6DQ0lQ9p<0GVP>Q6vPhp+0<oS9pPhQ<;PhQ63PhQ61PhQ5~PhQ5|PhQ<VPhQ5RPhI0CD6D6D6S5|Q9dPVQ8}PoPoPyPfPgQ0bPjP^P^P_PEQ;s9\^EI0:P;Pkb5b6b4Q:GP1b1b2b3Q:8eQ:2Q:0P[Q<UQ;Rp+0EBS6DQ9zQ<iQ<iQ:4G3Q8}PoPoPyPfPgQ0bPjQ:8Q;s5>^P;Pkb5b6b4Q:8P1b1b2b3H0aQ:2eQ:aQ<=Q=7Q<NQ9dDHQ9M/1{PVQ6mQ<wQ<DQ2WQ<wQ;WEQX=APUQ:aQ6=Q:aQ=2Q:aQ6=Q9LQ9fQ=5Q9SQ8FQ8bQ=7Q2op+0?8S8Fp+0=_S=5P[Q<UQ;RQ6DQ9zQ7VQ7VQ6mG3P[Q<UQ:jQ6~Q<HQ9dQ9dQ;OG3EFE8E8Q8}PoPoPyPfPgPlPjP^Q;aP:P^P}P:P^Q7sP^Q8rP^P^Q:GQ<A'pQ8kGrFCP;Pkb5b6b4X05X8FQ5d,01S<AQ:Y/08S6=Q5e,57S=2Q=2PWQ=2Q<3PWPEQ=2P6E[CZ[[^05^8FP1Q=3Q:iPLQ0JO4b1b2b3DEPUeQ6iQ;0Q9MP{PVQ:[Q;TQ<DQ=7Q;TQ;WEQX=Ap+0:mS=3Q:Wp+0;XS=2Q:Wp+0;YQ:WQ=2Q9FQ;:Q:ZQ;yQ6MQ;{p+0??S6Mp+0=^S:Zp+0?7S=2p+0=]S<wP[Q<UQ;RQ6DQ9zQ<xQ<xQ74G3P[Q<UQ:sQ7]Q;wQ9dQ9dQ;OG3EFE8E8Q8}PoPoPyPfPgPlPjP^Q;aP:P^P}P:P^Q7kP^Q7lP^P^Q:GQ9h'pQ8kGrFCP;Pkb5b6b4X05X8FQ<AQ6=Q;MQ<4PWQ<4Q<3PWQ<4=nE6Fm[[^05^8FP1Q2oQ:iPLQ0JO4b1b2b3DEQ=3eQ6rQ:}Q5JPSPVQ:QQ;BQ<DQ6MQ;BQ;WEQX=Ap+0:lS=3Q9CQ62Q9CQ64Q9CQ62Q7wQ3cQ2lQ9`p+0<KQ<CQ9ip+0=\S2lQ9ep+0=[S62P[Q<UQ;RQ6DQ9zQ<zQ<zQ6CG3P[Q<UQ:xQ:uQ<OQ9dQ9dQ;OG3EFE8E8Q8}PoPoPyPfPgPlPjP^Q;aP:P^P}P:P^Q7qP^Q7hP^P^Q:GQ;;'pQ8kGrFCP;Pkb5b6b4X05X8FQ<AQ6=Q<?Q;pPWQ;pQ<3PWQ;p=nE6Fm[[^05^8FP1Q:ZQ:iPLQ0JO4b1b2b3DEQ=3eQ2fQ70Q9NPHPVQ9uQ<ZQ<DQ9iQ<ZQ;WEQX=AQ5_Q9vQ5}Q9vQ60Q9vQ5}Q9WQ68p+0<JQ6<Q66Q8|p+0?=S66p+0=ZS5}p+0?5S60Q7vP[Q<UQ;RQ6DQ9zQ8pQ8pQ:zG3P[Q<UQ:~Q:|Q8]Q9dQ9dQ;OG3EFE8E8Q8}PoPoPyPfPgPlPjP^Q;aP:P^P}P:P^Q7gP^Q7fP^P^Q:GQ2\'pQ8kGrFCP;Pkb5b6b4X05X8FQ<AQ6=Q<_Q9wPWQ9wQ<3PWQ9w=nE6Fm[[^05^8FP1Q2lQ:iPLQ0JO4b1b2b3DEQ5_eQ;?Q7oQ9OQ1GPVQ:BQ5VQ<DQ66Q5VQ;WEQX=AQ5^Q:=Q7PQ:=p+0;SQ:=Q7PQ9ZQ2rQ5rQ;2Q5qQ5xp+0?<S9OQ6PQ1|p+0=WS5_P[Q<UQ;RQ6DQ9zQ6gQ6gQ7mG3P[Q<UQ71Q7>Q6]Q9dQ9dQ;OG3EFE8E8Q8}PoPoPyPfPgPlPjP^Q;aP:P^P}P:P^Q7eP^Q7dP^P^Q:GQ;|'pQ8kGrFCP;Pkb5b6b4X05X8FQ<AQ6=Q=0Q<~PWQ<~Q<3PWQ<~=nE6Fm[[^05^8FP1Q5}Q:iPLQ0JO4b1b2b3DEQ5^eQ6pQ:wQ9PQ1NPVQ:9Q<`Q<DQ9OQ<`Q;WEQX=AQ5]Q:3p+0;PS<~Q:3p+0;QS=0Q:3Q<~Q3DQ7YQ5oQ8XQ5mQ5tp+0?;S2lp+0=VS9wp+0?3S<_p+0=US:ZP[Q<UQ;RQ6DQ9zQ7pQ7pQ;cG3P[Q<UQ<}Q;1Q<nQ9dQ9dQ;OG3EFE8E8Q8}PoPoPyPfPgPlPjP^Q;aP:P^P}P:P^Q7cP^Q7bP^P^Q:GQ8:'pQ8kGrFCP;Pkb5b6b4X05X8FQ<AQ6=Q8m,57S;pQ;pPWQ;pQ<3PWPEQ;pP6E[CZ[[^05^8FP1Q6PQ:iPLQ0JO4b1b2b3DEQ5]eQ6jQ2}PwQ0UPVQ9}Q=1Q<DQ2lQ=1Q;WEQX=AQ5\Q6kp+0;NS;pQ6kp+0;OS<?Q6kQ;pQ3jQ2~Q5kQ9GQ5jQ:Np+0?:S;pQ9yp+0?2S64Q9|P[Q<UQ;RQ6DQ9zQ6lQ6lPxG3P[Q<UQ01Q;4p+0>US2oQ9dQ9dQ;OG3EFE8E8Q8}PoPoPyPfPgPlPjP^Q;aP:P^P}P:P^Q6hP^Q7`P^P^Q:GQ:>'pQ8kGrFCP;Pkb5b6b4X05X8FQ<AQ6=Q;A,57S<4Q<4PWQ<4Q<3PWPEQ<4P6E[CZ[[^05^8FP1Q9wQ:iPLQ0JO4b1b2b3DEQ5\eQ;mQ6wQ0]PVQ:pQ;Q/4cS:pQ<DQ;pQ:pQ;WEQX=AQ5[Q:mp+0;LS<DQ:mp+0;MQ:mQ<DQ=8Q6[p+0<BS<DQ=6p+0<AQ=4p+0?9S=4Q8Op+0?1S:mQ8LP[Q<UQ;RQ6DQ9zQ7aQ7aQ;5G3P[Q<UQ;8Q8`Q9JQ9dQ9dQ;OG3EFE8E8Q8}PoPoPyPfPgPlPjP^Q;aP:P^P}P:P^Q7[P^Q7ZP^P^Q:GQ8U'pQ8kGrFCP;Pkb5b6b4X05X8FQ<AQ6=Q<3,57S<UQ<UPWQ<UQ<3PWPEQ<UP6E[CZ[[^05^8FP1Q9yQ:iPLQ0JO4b1b2b3DEQ5[eQ0iQ1;I0`+0eGIGIGIGIGIGIGIQ9dQ5|80fVeL0iE=Q79P1EGb9Q5`P1E=b<Q31$0qNA0nQ;uQ7;P1Q5dQ:yQ7jQ<pQ5dQ:yQ5dQ7jCKdO4b9PWPXP=P@1UX=dQ79DRQ9{Q:yQ9{P|Q2HP1Q0LP~Q0xEJW7P|Q2GQ:yQ0KQ:dD<P|Q2GQ:hPYQ:dD<Q1IQ7lP|P>Q2GQ:yQ0KQ:dg02R`Q14Q<PQ:vQ7@Q32g02SjPng02U4Q:KQ5bQ:KQ79Q:KQ8PQ:Kp+0:DS1IQ:KQ1uQ:Kp+0=3S7;Q:KI0CD6D6S5|Q<dQ14PnCcQ2PeQ2PQ:7Q9:Q:7PCP1Q8QQ;UC{W7Q;vPCp+0GPS5[Q;x,41Q;UH03X;5Q:7Q:KQ:KQ;vQ;AQ;}Q8yQ8}PoPoPyPfPgPlPjP^PyQ;kQ:0H0<P;Pkb5b6b4X05Q<P,51Q<5Q<X,51404^05P1Q:iO1b1b2b3L0@Q7;Q;vQ8}PoPoPyQ7HQ8yP1Q:iQ0JO2b1b2b3Q8}PoPoPyQ7iQ:HP1Q:iPLO2b1b2b3K0MQ:7Q9:Q;AQ7NC{eQ27P1E=b<Q5|Q<dQ<PPnCcQ2AeQ2AQ:7Q34Q:7Q3392C1W7Q:7Q34Q2VP1Fbb<PVQ0NQ0KQ7@P<PVQ0TQ0NQ7@PNPVQ0WQ0TQ7@Q1FPVQ0~Q0WQ7@Q45PVQ18Q0~Q7@Q0VPVQ1?Q18Q7@Q0[PVQ5RQ1?Q7@Q0lPVQ:qQ5RQ7@Q1[Q:qQ9;Q7@Q<3PVQ;rQ:4Q6AQ<0p+0<;RLPoPyPyQ8zQ7KQ:4P1P~PMO2b1b2b3Q<QQ5cG_p+0;FeQ1=Q;rQ6L,01X;5S7KQ;iQ;v/01X;5PoPyPyQ8zPfPgPlPjQ8zQ9z5>^P;Pkb5b6b4X05Q8t,51S0WQ2s,51S2s'0^05P1P~O1RMb1b2b3Q:FQ0BDDQ<QQ5cDDQ<QQ:F'0eQ;iQ<q/0LX;5Q;rQ9aQ;<80?1X;5p+0>oS<qQ9='0Q1VQ9>'0P[Q<tQ<qQ1VQ7tQ9=Q9>Q9pG3PoPyPyQ8zPfPgPlPjQ8QQ8r5>^P;Pkb5b6b4X05Q2sQ8mQ0WQ8tH05^05PMb1b2b3Q<QQ5cG_Q:FQ0BDDQ:FQ<rp+0<:3PeN907E;E;E;E;E;E;E;E;NB08Q;tQ<fP1Q7=Q:tQ8QQ<pQ7=Q:tQ7=Q8QCKdO4b9Q9{Q5dP=P@Q5d/U=dQ:hDRQ:7Q:tQ:7P|Q2JP1PJQ:iQ0eEJW7P|Q2HQ:tP]P~D<P|P21AbCQ1\Q2HQ2Gn0100000020000Q8CP]P~D<Q0xQ7kP|P>Q2HQ:tP]P~g02V>Q14Q<vQ:yQ2pp+05@S:yg02WHPng02XRQ99Q1ZQ99Q7jQ99Q8RQ99p+0:ES0xQ99Q04Q99Q3AQ99FoD6Q7AQ<vPnEdQ2AeQ2APCQ:oQ1^P\Q79,M1PVQ2kI0>X7CPwp+0F;RMQ:op+0GQS2kQ3^,41S79'O32X;5Q:l,yCQ0xPwPsQ8}Q8}PoQ8EQ;RP1Q9NQ3iO2b1b2b3PsQ8}Q8}PoQ7RQ:tP1Q9NQ1AO2b1b2b3K0MQ58eQ58PMQ:oQ:6Q1rP1PVQ2mI0>X7MQ1^p+0:JS7RQ1^Q:6Q2m721W@Q16Q0lQ:o<0GVP>Q2}Q<cQ31Q<cQ6AQ<cQ<0Q<cQ9pQ<cQ<;Q<cQ63Q<cQ61Q<cQ5~Q<cQ13Q<cFoD6D6D6S<cPwPVP}PsPsQ8}PfPgPlPjP^Q9zP:P^PEP:P^P^P_Q:{Q:{Q;a5\^I0:FCP;Pkb5b6b4X05141rS5~Q<T'0RoQ5d/08Q8m,47S1^#TS7AQ1^Q9{40F[[^05P1Q5JQ3iQ5cO3b1b2b3%TwS3AQ0I80FweQ1Ip+0:RS04Q0IP[Q<eQ:gQ04Q5GQ0IQ0IQ:>G3P}PsPsQ8}PfPgPlPjP^Q9zP:Q:{Q;d'WQ;a5>^CLP;Pkb5b6b4X05Q<o,48S:hQ<3;PW\o^05P1Q5JQ3iO2S<rb1b2b3I18Q1IeQ<qQ2DQ36Q2QPwDHQ3kQ2U'1PVQ9aQ;TQ8tQ5GQ;TQ9PEQX=AQ3{Q<qQ4@Q<qQ3>Q<qQ4@Q7tQ6LQ58Q:FQ4fQ<DQ36Q59p+0:8Q55P[Q<eQ:gQ04Q5GQ<xQ<xQ9aG3P[Q<eQ64Q:mQ8LPwPwp+0:QRoG3EFE8E8P}PsPsQ8}Q;OPgPiPjP^Q9]P:P^P3P:P^Q90P:P^Q7[P^Q7ZP^P^Q:{Q:GQ0cF^EYFCP;Pkb5b6b4X05X:5X8FQ5d=P8XS:Gp+0GRS59,08Ryp+0E?/07RLQ;x,56S<DQ<DPMQ<DPrPMQ;W,4BS4f/4rS58Q<DP4E[CZ[[[^05^:5^8FP1Q5EQ5JQ:qQ3iQ0tPGO6b1b2b3DEQ3{eQ1ZQ29Q3kQ2UPVQ:jQ;BQ8tQ36Q;BQ9P'0S36DsX=AQ3zQ6~Q3dQ6~Q4LQ6~Q3dQ9SQ;=Q54Q9fQ4dQ<8p+0:AS<8Q5PQ4~Q5AP[Q<eQ:gQ04Q5GQ<zQ<zQ:jG3P[Q<eQ7]Q74Q;wPwPwPoG3EFE8E8P}PsPsQ8}Q;OPgPiPjP^Q9]P:P^P3P:P^Q90P:P^Q89P^Q6|P^P^Q:{Q9hQ0cF^EYFCP;Pkb5b6b4X05X:5X8FQ:GQ5d,56S4~Q4~PMQ4~PrPMQ58Q4~P4E[CZ\L\y[^05^:5^8FP1Q55Q5JQ:qQ3iQ0tPGO6b1b2b3DEQ3zeQ7^Q6jQ5YPePVQ6mQ<ZQ8tQ<8Q<ZQ9P'0S<8DsX=AQ2uQ:aQ6^Q:aQ4HQ:aQ6^Q;yQ6oQ46Q;:Q1UQ67Q5FQ5OQ5NQ5MP[Q<eQ:gQ04Q5GQ8pQ8pQ:sG3P[Q<eQ:uQ6CQ<OPwPwPoG3EFE8E8P}PsPsQ8}Q;OPgPiPjP^Q9]P:P^P3P:P^Q90P:P^Q6yP^Q7sP^P^Q:{Q;;Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ:GQ9d,56S;;Q;;PMQ;;PrPMQ58Q;;P4E[CZ\L\y[^05^:5^8FP1Q5AQ5JQ:qQ3iQ0tPGO6b1b2b3DEQ2uep+0@bS5AQ;mQ3hPSPVQ:[Q5VQ8tQ5FQ5VQ9P'0S5FDsX=AQ3yQ:WQ3pQ:WQ3bQ:WQ3pQ9`Q2NQ4bQ3cp+088Q65p+0:?S65Q5LQ4yQ5hP[Q<eQ:gQ04Q5GQ6gQ6gQ:xG3P[Q<eQ:|Q:zQ8]PwPwPoG3EFE8E8P}PsPsQ8}Q;OPgPiPjP^Q9]P:P^P3P:P^Q90P:P^Q8rP^Q7kP^P^Q:{Q2\Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ:GQ3^,56S2\#TS4yQ2\PMQ2\PrPMQ58Q2\;n4Fm\L\y[^05^:5^8FP1Q5MQ5JQ:qQ3iQ0tPGO6b1b2b3DEQ3yeQ6iQ;0p+05_S5MPNPVQ:QQ<`Q8tQ65Q<`Q9P'0S65DsX=AQ3xQ9CQ3_Q9CQ4DQ9CQ3_Q6<Q9@Q4`Q68p+086Q<Jp+0:>S<JQ5;Q5IQ57P[Q<eQ:gQ04Q5GQ7pQ7pQ:~G3P[Q<eQ7>Q7mQ6]PwPwPoG3EFE8E8P}PsPsQ8}Q;OPgPiPjP^Q9]P:P^P3P:P^Q90P:P^Q7lP^Q7qP^P^Q:{Q;|Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ:GQ;W,56S;|#TS5IQ;|PMQ;|PrPMQ58Q;|;n4Fm\L\y[^05^:5^8FP1Q5hQ5JQ:qQ3iQ0tPGO6b1b2b3DEQ3xeQ6rQ:}Q6IQ1FPVQ9uQ=1Q8tQ<JQ=1Q9P'0S<JDsX=AQ3wQ9vQ3~Q9vQ4EQ9vQ3~Q;2Q3Cp+085Q2rQ44Q5zQ28Q5HQ53Q5?P[Q<eQ:gQ04Q5GQ6lQ6lQ71G3P[Q<eQ;1Q;cQ<nPwPwPoG3EFE8E8P}PsPsQ8}Q;OPgPiPjP^Q9]P:P^P3P:P^Q90P:P^Q7hP^Q7gP^P^Q:{Q8:Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ:GQ<5,56S<5#TS8:Q<5PMQ<5PrPMQ58Q<5;n4Fm\L\y[^05^:5^8FP1Q57Q5JQ:qQ3iQ0tPGO6b1b2b3DEQ3weQ2fQ70Q6GQ45PVQ:BQ:pQ8tQ28Q:pQ9P'0S28DsX=AQ3vQ:=Q48Q:=Q3[Q:=Q48Q8XQ5yQ3SQ7YQ4\Q5wQ;ZQ4}Q1SQ4xP[Q<eQ:gQ04Q5GQ7aQ7aQ<}G3P[Q<eQ;4PxQ2oPwPwPoG3EFE8E8P}PsPsQ8}Q;OPgPiPjP^Q9]P:P^P3P:P^Q90P:P^Q7fP^Q7eP^P^Q:{Q:>Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ:GQ<3,56S2o#TS1SQ2oPMQ2oPrPMQ58Q2o;n4Fm\L\y[^05^:5^8FP1Q5?Q5JQ:qQ3iQ0tPGO6b1b2b3DEQ3veQ;?Q7op+05\S5?Q0VPVQ:9Q:e/4cS4}Q8tQ;ZQ4}Q9P'0S;ZDsX=AQ3uQ:3Q3<Q:3Q4?Q:3Q3<Q9GQ0DQ43Q2~p+080Q6;Q4|Q4wQ4vQ4uP[Q<eQ:gQ04Q5GQ;QQ;QQ01G3P[Q<eQ8`Q;5Q9JPwPwPoG3EFE8E8P}PsPsQ8}Q;OPgPiPjP^Q9]P:P^P3P:P^Q90P:P^Q7dP^Q7cP^P^Q:{Q:KQ0cF^EYFCP;Pkb5b6b4X05X:5X8FQ:GQ<S,56S:K#TS4vQ:KPMQ:KPrPMQ58Q:K;n4Fm\L\y[^05^:5^8FP1Q4xQ5JQ:qQ3iQ0tPGO6b1b2b3DEQ3ueQ6pQ:wQ0[PVQ9}Q:d/4cS4xQ8tQ4|Q4xQ9P'0S4|DsX=AQ3tQ6kQ6_Q6kQ4<Q6kQ6_Q=6Q5{Q4ZQ6[Q41Q7\Q5EQ4tQ4sQ4rP[Q<eQ:gQ04Q5GQ:eQ:eQ;8G3P[Q<eQ<hQ1cQ9=PwPwPoG3EFE8E8P}PsPsQ8}Q;OPgPiPjP^Q9]P:P^P3P:P^Q90P:P^Q7bP^Q6hP^P^Q:{Q<<Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ:G156rS9]Q9]PMQ9]PrPMQ58Q9]P4E[CZ\L\y[^05^:5^8FP1Q4uQ5JQ:qQ3iQ0tPGO6b1b2b3DEQ3teQ1DQ1?I0`+0eGIGIGIGIGIGIGIGIQ<c:0fwVeL0iE=Q0xP1EGb9Q2VP1E=b<Q:y$0qNA0nQ;sQ<7P1Q5[Q:fQ8D%NaS0xQ5[Q:fQ5[Q8DCKdO4b9Q:7Q7=Q:\P@Q7=Q:\'UdQ8CDRPCQ:fP|Q2JP1P\Q:nPmEJX7CP|Q2HQ:fPJQ:iD<P|P21AbMQ9QQ2HQ1}n0100000020000Q8APJQ:iD<Q0eQ8rP|P>Q2HQ:fPJQ:ig02Y\Q<PQ11Q<Rp+05JS<Rp+05KS:ig02ZfPng02\0Q:RQ2mQ:RQ31Q:RQ7FQ:RQ8SQ:RQ1_Q:RQ5TQ:Rp+0=5S2mQ:RI0CD6D6p+0A>Q11PnEdQ1yeQ1yPMQ6BQ:6Q1rQ8d,M1PVQ<RI0>X7MQ9PQ:oQ59Q79'O52zX;5Q:l,yMQ1_Q9PP}PsPsQ8}Q8GQ;PP1Q5JQ5cO2b1b2b3P}PsPsQ8}Q7SQ:vQ<rb1b2b3K0MQ4YeQ4YPzQ:oQ:;PHP1PVQ:iI0>X7zQ:6Q7RQ:6Q:;Q:i721W@Q16Q18Q:o<0GVP>Q:wQ1\Q32Q1\Q<QQ1\Q6AQ1\Q<0Q1\Q9pQ1\Q<;Q1\Q63Q1\Q61Q1\Q0jQ1\FoD6D6D6S1\PwPVQ8~P}P}PsPfPgPlPjP^Q:0P:P^Q;LP:P^P^P_Q9qQ9qQ;e5\^I0:FCP;Pkb5b6b4X05AP1XrRyQ7=/08Q7AQ1^Q:740F[[^05P1Q9MQ5cQ1CO3b1b2b3Q3AQ8t80FweQ4qQ7CQ8tP[Q<WPoQ7CQ4pQ8tQ8tQ:CG3Q8~P}P}PsPfPgPlPjP^Q:0P:Q9qQ;b'WQ;e5>^CLP;Pkb5b6b4X05Q:hQ<KQ9{3P\y^05P1Q9MQ5cO2b1b2b3I18Q4qeQ9aQ29Q4oQ5bPwDHQ5?Q2U'1PVQ:mQ;BQ<PQ4pQ36DsX=AQ3tQ9aQ3YQ9aQ6_Q9aQ3YQ:FQ8LQ4YQ6Lp+07lS36Q5jQ4oQ6dQ56Q6eP[Q<WPoQ7CQ4pQ<zQ<zQ:mG3P[Q<WQ<_Q64Q8OPwPwQ6>G3EFE8E8Q8~P}P}PsQ;NPgPiPjP^Q9zP:P^Q;fP:P^Q91P:P^Q7`P^Q7[P^P^Q:tQ9_Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ7=Q5d5P8S9_p+0GSS56,08Ryp+0E@S6d/07RLQ4yQ2\PzQ2\PXPzQ4f/4XS4fQ2\;n4Fm[[[^05^:5^8FP1Q5:Q9MQ6vQ5cPGPRO6b1b2b3DEQ3teQ31Q2QQ5?Q2UPVQ74Q<ZQ<PQ4oQ<8DsX=AQ3VQ:jQ6`Q:jQ6XQ:jQ6`Q;gQ;wQ40Q<HQ4WQ<VQ4nQ50Q6fQ52P[Q<WPoQ7CQ4pQ8pQ8pQ74G3P[Q<WQ:sQ7]Q9gPwPwQ6>G3EFE8E8Q8~P}P}PsQ;NPgPiPjP^Q9zP:P^Q;fP:P^Q91P:P^Q72P^Q89P^P^Q:tQ;JQ0cF^EYFCP;Pkb5b6b4X05X:5X8FQ9_Q7=,56S;JQ;JPzQ;JPXPzQ4fQ;JP4E[CZ\L\y[^05^:5^8FP1Q6eQ9MQ6vQ5cPGPRO6b1b2b3DEQ3VeQ7?Q6pQ2BPePVQ6~Q5VQ<PQ4nQ5FDsX=AQ3TQ6mQ3=Q6mQ3WQ6mQ3=Q9bQ9SQ3EQ9LQ4UQ8bQ4mQ1`Q5KQ9nP[Q<WPoQ7CQ4pQ6gQ6gQ6CG3P[Q<WQ:xQ:uQ<aPwPwQ6>G3EFE8E8Q8~P}P}PsQ;NPgPiPjP^Q9zP:P^Q;fP:P^Q91P:P^Q6|P^Q6yP^P^Q:tQ;7Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ9_Q5IQ;|PzQ;|PXPzQ4fQ;|;n4Fm\L\y[^05^:5^8FP1Q52Q9MQ6vQ5cPGPRO6b1b2b3DEQ3TeQ7^Q6jp+05ZS3TPSPVQ:aQ<`Q<PQ4mQ65DsX=AQ3RQ:[Q39Q:[Q6TQ:[Q39Q7xQ;yQ3|Q9FQ3GQ;{Q4lQ4zQ6aQ4{P[Q<WPoQ7CQ4pQ7pQ7pQ:zG3P[Q<WQ:~Q:|Q9jPwPwQ6>G3EFE8E8Q8~P}P}PsQ;NPgPiPjP^Q9zP:P^Q;fP:P^Q91P:P^Q7sP^Q8rP^P^Q:tQ9lQ0cF^EYFCP;Pkb5b6b4X05X:5X8FQ9_Q8:Q<5PzQ<5PXPzQ4fQ<5;n4Fm\L\y[^05^:5^8FP1Q9nQ9MQ6vQ5cPGPRO6b1b2b3DEQ3ReQ5AQ;mp+05YS3RPNPVQ:WQ=1Q<PQ4lQ<JDsX=AQ3PQ:QQ3:Q:QQ3;Q:QQ3:Q9HQ9`Q4TQ7wp+07dS7wQ<CQ4kQ1PQ4hQ6bP[Q<WPoQ7CQ4pQ6lQ6lQ7mG3P[Q<WQ71Q7>Q<\PwPwQ6>G3EFE8E8Q8~P}P}PsQ;NPgPiPjP^Q9zP:P^Q;fP:P^Q91P:P^Q7kP^Q7lP^P^Q:tp+0D[Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ9_Q1SQ2oPzQ2oPXPzQ4fQ2o;n4Fm\L\y[^05^:5^8FP1Q4{Q9MQ6vQ5cPGPRO6b1b2b3DEQ3PeQ6iQ;0Q2[Q1FPVQ9CQ:pQ<PQ4kQ28DsX=AQ3NQ9uQ2|Q9uQ38Q9uQ2|Q7nQ6<Q4SQ9WQ3KQ8|Q4jQ4eQ6cp+09BS8|P[Q<WPoQ7CQ4pQ7aQ7aQ;cG3P[Q<WQ<}Q;1Q9DPwPwQ6>G3EFE8E8Q8~P}P}PsQ;NPgPiPjP^Q9zP:P^Q;fP:P^Q91P:P^Q7qP^Q7hP^P^Q:tQ:4Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ9_Q4vQ:KPzQ:KPXPzQ4fQ:K;n4Fm\L\y[^05^:5^8FP1Q6bQ9MQ6vQ5cPGPRO6b1b2b3DEQ3NeQ6rQ:}Q6FQ45PVQ9vQ4}Q<PQ4jQ;ZDsX=AQ3MQ:BQ2zQ:BQ2{Q:BQ2zQ9XQ;2Q3FQ9ZQ4QQ5xQ4iQ4cp+09@S5xQ4aP[Q<WPoQ7CQ4pQ;QQ;QPxG3P[Q<WQ01Q;4Q=9PwPwQ6>G3EFE8E8Q8~P}P}PsQ;NPgPiPjP^Q9zP:P^Q;fP:P^Q91P:P^Q7gP^Q7fP^P^Q:tQ:CQ0cF^EYFCP;Pkb5b6b4X05X:5X8FQ9_Q<K,56S9ZQ9ZPzQ9ZPXPzQ4fQ9ZP4E[CZ\L\y[^05^:5^8FP1Q8|Q9MQ6vQ5cPGPRO6b1b2b3DEQ3MeQ2fQ70p+05VS3MQ0VPVQ:=Q4xQ<PQ4iQ4|DsX=AQ3LQ:9Q2xQ:9Q2yQ:9Q2xQ9IQ8XQ5iQ3DQ4OQ5tp+09US5tQ5Dp+09=S3DQ4_P[Q<WPoQ7CQ4pQ:eQ:eQ;5G3P[Q<WQ;8Q8`Q9>PwPwQ6>G3EFE8E8Q8~P}P}PsQ;NPgPiPjP^Q9zP:P^Q;fP:P^Q91P:P^Q7eP^Q7dP^P^Q:tQ99Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ9_1569S7dQ7dPzQ7dPXPzQ4fQ7dP4E[CZ\L\y[^05^:5^8FP1Q4aQ9MQ6vQ5cPGPRO6b1b2b3DEQ3LeQ;?Q7oQ0[PVQ:314~cR~Q<PQ5tP~Q9PEQX=AQ3JQ9}Q2vQ9}Q2wQ9}Q2vQ9AQ9GQ3QQ3jQ3UQ:NQ5:Q5BQ4]p+099S5:P[Q<WPoQ7CQ4pQ:dQ:dQ1cG3P[Q<WQ7@Q<hQ9<PwPwQ6>G3EFE8E8Q8~P}P}PsQ;NPgPiPjP^Q9zP:P^Q;fP:P^Q91P:P^Q7cP^Q7bP^P^Q:tQ8uQ0cF^EYFCP;Pkb5b6b4X05X:5X8FQ9_156XRsPsPzPsPXPzQ4fPsP4E[CZ\L\y[^05^:5^8FP1Q4_Q9MQ6vQ5cPGPRO6b1b2b3DEQ3JeQ13Q0qI0`+0eGIGIGIGIGIGIGIGIQ1\:0fwVeL0iE=Q4rP1EGb9Q2PP1E=b<Q:i$0qNA0nQ;dQ;VP1Q2kQ9KQ75Q0xQ2kQ9KQ2kQ75CKdO4b9PCQ5[Q:\P@Q5[Q:\'UdQ8ADRPMQ9KP|Q27P1Q1rQ:qQ0PEJX7MP|Q2VQ9KP\Q:nD<P|P21Abzp+0CgRwQ2VQ2Mn0100000020000Q8AP\Q:nD<PmQ7sP|P>Q2VQ9KP\Q:ng02]:RRQ<bQ9{Q14g02^D%}Rg02_NN=1zQ;bQ;YP1Q59PwQ75Q0xQ59PwQ59Q75CKdO4b9PMQ2kQ:\P@Q2kQ:\'UdQ8ADRPzPwP|Q2?P1PHQ6vQ0AEJX7zQ8UQ:iQ8UQ2pQ8UQ34Q8UQ8RQ8UQ8TQ8Up+0:HQ8UQ5UQ8Up+0=7Q8UFoD6D6Q:cQ:7PnEdQ2MeQ2Mp+0F=S:cp+05DS34Q:cP|Q2HQ<vQ2A-0z1p+0CiRRPNQ6wQ0@GfW7Q:bQ2IQ:bQ2qQ:bQ33Q:bQ8SQ:bQ7rQ:bQ5@Q:bQ5vQ:bp+0=8S5vQ:bFoD6D6Q:^Q9{PnEdQ2MeQ2Mp+0F>RGp+05ORyP|Q2JQ11p+05FS:^00z1Q9QQ0KQ2}PpGfX7GPGQ34P|Q2JQ11P1Q9QQ0KQ2}PpGfX7GP|Q2EPRPNQ6wD<P|P2Q:`,AbQ;f>0;b3Q2EQ1{n0100000020000Q8CPNQ6wD<Q0@Q89P|P>Q2EPRPNQ6wg02`XRLQ;fPMQ:7g02ab%}Lg02blN=1yQ;\Q<:P1p+0GUS;fPRQ8DQ<pQ;fPRQ;fQ8DCKdO4b9PGp+0GTS5@P=P@Q5@/U=dQ8CDRQ:`PRQ:`P|Q1sP1Q0LQ:wQ0zEJW7Q<<Q:yQ<<p+05NS:wQ<<p+05ARLQ<<Q5`Q<<Q8TQ<<Q8WQ<<p+0:KQ<<Q5sQ<<p+0=:S5sQ<<I0CD6D6D6Q7QPzPnEdQ1{eQ1{Q:1Q2_Q:1P|Q27PIQ2?-0|1Q:fQ0SQ7oQ0;GfW7Q8uPLQ8uPyQ8uQ6qQ8uQ5gQ8uQ7rQ8uQ7EQ8uQ5>Q8uQ2iQ8uQ6?Q8uI0CD6D6D6Q7iPMPnEdQ1{eQ1{Q:<p+05RS7iQ:<P|Q2GQ<1p+05IS8u00|1Q9UQ0RQ70Q0`GfW7P|Q2CQ:fQ0SQ7oD<P|Q2CQ8EPJQ7oD<Q0;Q6YP|P>Q2CQ:fQ0SQ7og02d6Q:`PzQ9QQ<xQ7ig02e@Png02fJQ1dQ9kQ9tQ8IQ9tQ:VP1Q8GQ8pC{W7Q8pQ:Vp+0GYRLQ5~Q8pH03X;5Q9tQ37Q37Q9yQ2}Q8~Q94Q93Q93Q92PfPgPlPjQ7bQ:r61;^P;Pkb5b6b4X05151GRsQ5d151r404^05P1Q:}O1S:rb1b2b3K1Lp+0=<R}Q0?DDQ9tQ5rQ<z32eQ2>P1E=b<Q37Q:yQ37Q6qQ37Q6UQ37p+05CQ37Q30Q37Q8VQ37Q8YQ37p+0:MQ37Q2;Q37P}Q37FoD6D6D6Q7HPzPnEdQ1leQ1lQ9tp+05SS37Q9tQ:VQ2@721W7Q9tQ37Q1{P1Fbb<PVQ0QQ0SQ<xP<PVQ20Q0QQ<xPNPVQ0wQ20Q<xQ1YPVQ0gQ0wQ<xQ4^PVQ1[Q0gQ<xQ0XPVQ13Q1[Q<xQ1XPVQ0oQ13Q<xQ1;PVQ0sQ0oQ<xQ1DPVQ;mQ0sQ<xQ0mQ;mQ8MQ<xQ2kPVQ<zQ8UQ5sp+0=9S2kQ5kQ93Q92Q92Q91Q7JQ8UP1Q70PmO2b1b2b3Q6?PQG_Q<?eQ1EQ<zQ9|,01X;5Q6wQ8p/01X;5Q93Q92Q92Q91PfPgPlPjQ91Q9Y5>^P;Pkb5b6b4X05Q:c,51RmQ<T,51Ro'0^05P1Q70O1R~b1b2b3Q8OPKDDQ6?PQDDQ6?Q8O'0eQ6wQ<7Q5k5P1X;5Q<zQ60Q;b80?1X;5Q1|Q8H'0Q<_p+0>aS;b'0P[Q;YQ1|Q<_Q8LQ8HQ;bQ5vG3Q93Q92Q92Q91PfPgPlPjQ8GQ7y5>^P;Pkb5b6b4X05PoPXPmQ:cH05^05P~b1b2b3Q6?PQG_Q8OPKDDQ8OQ<fQ5j3PeN907E;E;E;E;E;E;E;E;E;NB08Q35Q<@P1p+0GXS<@PRQ8GQ<I#NS35Q<@PRQ<@Q8GCKdO4b9Q:<p+0GWR~Q;SP@Q;S,U~dQ8EDRQ9tPRQ9tP|Q1}P1Q1rQ:}Q0_EJW7P|Q2EPRP\Q70D<P|Q2EQ8APOQ70D<Q0`Q3HP|P>Q2EPRP\Q70g02gTQ:1Q0IQ9KPtp+05HS0`g02h^Png02ihQ1wQ1KQ:VQ8KQ:Vp+0FDRmP1Q;jQ9QQ;vI0HW7Q6gPmp+0GZS8E1419Q;vH03X;5Q:VQ9mQ9mQ6gQ<SQ;QQ8BQ95Q94Q94Q93PfPgPlPjP^Q93Q;\Q:kH0<P;Pkb5b6b4X05Q:`,51RoQ8mQ9d,51404^05P1Q;0O1S:kb1b2b3L0@Q6OQ0=DDQ:VQ8KQ<SQ;rC{eQ1sP1E=b<Q1dQ1lQ:VQ8uQ:VQ<R92m1W7Q:VQ8uQ1{P1Fbb<PVQ0RP\PtPePVQ1MQ0RPtPdPVQ1LQ1MPtQ0KPVQ0fQ1LPtQ0QPVQ4gQ0fPtQ20PVQ1?Q4gPtQ0wPVQ0jQ1?PtQ0gPVQ0pQ0jPtQ1[PVQ0uQ0pPtQ13PVQ6jQ0uPtQ0oQ6jQ8IPtQ59PVQ8pQ:bQ6?Q5sQ5mQ94Q93Q93Q92Q7MQ:bP1Q:}Q0PO2b1b2b3P}Q0?G_Q<~eQ3nQ8pQ8O,01X;5Q7aQ6g/01X;5Q94Q93Q93Q92PfPgPlPjQ92Q9U5>^P;Pkb5b6b4X05Q<s,51S3n,0s^05Q:rb1b2b3Q8LPKDDP}Q0?DDQ8L,0}eQ7aQ<6Q5m'0X;5Q8pQ<_Q;a80?1X;5Q64Q8J'0Q:mQ8H'0P[Q<9Q64Q:mQ6LQ8JQ8HQ2kG3Q94Q93Q93Q92PfPgPlPjQ8CQ7z5>^P;Pkb5b6b4X05Q3nQ5dPsPGH05^05Q:rb1b2b3P}Q0?G_Q8LPKDDQ8LQ<7Q5k3PeN907E;E;E;E;E;E;E;E;E;E;NB08PPQ<]P1PLPwQ75Q35PLPwPLQ75CKdO4b9Q9tQ<@Q;SP@Q<@Q;S'UdQ8ADRQ:VPwQ:VP|Q2VP1PdQ;0Q0>EJW7P|Q1}PwP<Q:}D<P|Q1}Q8>P{Q:}D<Q0_Q7yP|P>Q1}PwP<Q:}g02k2Q:<Q:`Q51PtQ2gg02l<Png02mFQ22Q1nPmQ8NQ9sP1Q;AQ9KQ;vI0HX7mQ7pQ9sp+0G[RGQ5e,41Q;vH03X;5PmQ3\Q3\Q7pQ<KQ;QQ90Q96Q95Q95Q94PfPgPlPjP^Q94Q;eQ:fH0<P;Pkb5b6b4X05Q:1,51S:fQ<3,51804r^05P1Q;mO1S;Ab1b2b3L0@Q6ZQ0=DDPmQ8NQ<KQ;rC{eQ2MP1E=b<Q3\Q6qQ3\Q34Q3\Q7iQ3\Q2tQ3\Q5fQ3\Q7EQ3\Q8ZQ3\Q6>Q3\Q2aQ3\Q6ZQ3\FoD6D6D6Q7IQ:`PnEdQ1leQ1lPmQ7HQ9sQ2F721X7mPpQ1{P1E=b<PVQ1rP<PtQ2SPVQ0OQ1rPtPvPVQ0hQ0OPtPSPVQ0YQ0hPtQ0LPVQ0ZQ0YPtQ1MPVQ0nQ0ZPtQ1LPVQ0qQ0nPtQ0fPVQ0kQ0qPtQ4gPVQ19Q0kPtQ1?PVQ0vQ19PtQ0jPVQ6pQ0vPtQ0pQ6pQ8KPtQ56PVQ6gp+0DiRsP}Q6?Q5oQ95Q94Q94Q93Q:OPsP1Q;0Q0AO2b1b2b3Q6OQ0=G_Q=0eQ0<Q6gQ8L,01X;5Q7aQ7p/01X;5Q95Q94Q94Q93PfPgPlPjQ93Q9Q5>^P;Pkb5b6b4X05Q;W,51Rs,0o^05Q:kb1b2b3Q6LPKDDQ6OQ0=DDQ6OQ6L'0eQ7aQ;YQ5o5P1X;5Q6gQ:mQ;e80?1X;5Q9aQ8M'0Q<qQ8J'0P[Q<EQ9aQ<qQ:FQ8MQ8JQ5sG3Q95Q94Q94Q93PfPgPlPjQ8@Q7{5>^P;Pkb5b6b4X05PsQ7=PoQ:`H05^05Q:kb1b2b3Q6OQ0=G_Q6LPKDDQ6LQ;VQ5m3PeN907E;E;E;E;E;E;E;E;E;E;E;NB08PIQ<jP1Q8Ep+0CeRoQ8?Q35Q8EPoQ8EQ8?CKdO4b9Q:VPLQ;SP@Q;S,ULdQ8>DRPmPoP|Q27P1PvQ;mQ1JEJX7mP|Q2VPoPeQ;0D<P|Q2VP0PqQ;0D<Q0>Q7zP|P>Q2VPoPeQ;0g02nPQ9tPMQ9EPtQ2Zg02oZPng030dQ1gQ1pQ9sQ9^Q9sp+0FFRsP1Q;xQ51Q;vI0HW7Q6lPsp+0G\S;xQ<o,41Q;vH03X;5Q9sQ9[Q9[Q6lP9Q;QQ91Q97Q96Q96Q95PfPgPlPjP^Q95Q;aPRH0<P;Pkb5b6b4X05Q:<,51Q<s1519404^05P1Q6jO1b1b2b3L0@Q6NQ6lQ97Q96Q96Q95Q7[Q91P1Q6jQ0zO2b1b2b3Q97Q96Q96Q95Q7ZQ3\P1Q6jPpO2b1b2b3K0MQ9sQ9^P9Q;rC{eQ1vP1E=b<Q1wQ1lQ9sQ2dQ9sQ2e92s1W7Q2bQ1{P1E=b<PVPdPePtQ2gQ;r80BdPVPHPdPtP{PVQ1GPHPtPZPVQ1NQ1GPtPYPVQ0UQ1NPtQ0SPVQ0]Q0UPtQ0hPVQ0lQ0]PtQ0YPVQ0iQ0lPtQ0ZPVQ0mQ0iPtQ0nPVQ0sQ0mPtQ0qPVQ1iQ0sPtQ0kPVQ;?Q1iPtQ19Q;?Q8NPtQ5@PVQ7pQ<<Q6OP}Q5qQ96Q95Q95Q94Q7TQ<<P1Q;mQ0@O2b1b2b3Q6ZQ0=G_Q7PePQQ7pQ7KQ7aQ6l/01X;5Q96Q95Q95Q94PfPgPlPjQ94Q9K5>^P;Pkb5b6b4X05Q:fQ<S,51RQ'0^05Q;Ab1b2b3Q:FPKDDQ6ZQ0=DDQ6ZQ:F'0eQ7aQ<uQ5q'0X;5Q7pQ<qQ;\80?1X;5Q1VQ8I'0p+0>mS7pQ8M'0P[Q<:Q1VQ7pQ7tQ8IQ8MQ6?G3Q96Q95Q95Q94PfPgPlPjQ78Q7|5>^P;Pkb5b6b4X05PQQ5[Q:fQ:1H05^05Q;Ab1b2b3Q6ZQ0=G_Q:FPKDDQ:FQ;YQ5o3PeN907E;E;E;E;E;E;E;E;E;E;E;E;NB08Q<1Q;zP1PGQ9RPTQ35PGQ9RPGPTCKdO4b9PmQ8EQ;SP@Q8EQ;S'UdP0DRQ9sQ9RQ9sP|Q2GP1P{Q6jQ2UEJW7P|Q27Q9RQ2SQ;mD<P|P21AbsQ:tQ27Q1ln0100000020000Q8;Q2SQ;mD<Q1JQ7{P|P>Q27Q9RQ2SQ;mg031nRQQ14Q14Pzg0338%}Qg034BN=1xQ<2Q;jP1Q;xQ9RQ8<Q35Q;xQ9RQ;xQ8<CKdO4b9Q9sPGQ;SP@Q;S,UGdQ8;DRPsQ9RP|Q1KP1PeQ6pQ1HEJX7sQ1hQ1pp+0FGRQQ3ZP|Q2JQ:7Q2M-0y1PoPvQ;?PqGfX7QQ1hQ1np+0FHS2JQ2gQ2JP|Q2KPC20yy1Q51PZQ2fQ2SGfW7Q2JQ2dQ2JP|Q2KPCP1Q51PZQ2fQ2SGfW7P|Q2EPoPvQ;?D<P|P2Q9x,AbQ9EQ2EQ1hn0100000020000Q6sPvQ;?D<PqQ7~P|P>Q2EPoPvQ;?g035LR}Q:cQ6:Q<vg036V%}}g037`N=1wQ<mQ3^P1p+0G_S3^Q9EP0Q<k#NQ3^Q9EQ3^P0CKdO4b9Q2Jp+0G^S<mQ2]P@Q<mQ2]'UdQ6sDRQ9xQ9EQ9xP|Q1jP1POQ6rP{EJW7Q:;Q2cQ:;Q0`Q:;Q<RQ:;Q2[Q:;Q:iQ:;Q5pQ:;Q7OQ:;Q8cQ:;Q:lQ:;Q2XQ:;Q9\Q:;I0CD6D6D6D6Q7SQ11PnEdQ1heQ1hQ9~Q3ZQ9~P|Q27Q:121Bo1Q51P<Q6iPeGfW7Q9~Q8{Q9~P|Q27Q:1P1Q51P<Q6iPeGfW7P|Q1vPoPOQ6rD<P|Q1vP0POQ6rD<P{Q80P|P>Q1vPoPOQ6rg038jPQQ9sQ07$0RQ<m'?g03:4Png03;>Q:@Q6sQ:@Q2XQ:@Q8uQ:@Q:iQ:@Q3RQ:@Q2IQ:@Q5nQ:@Q8^Q:@Q8dQ:@Q:oQ:@Q2ZQ:@Q3OQ:@FoD6D6D6D6Q7UPQPnEdQ1deQ1dQ:5Q7iQ:5Q1x-151$0dW7Q:EP0Q:EQ2ZQ:EQ<RQ:EQ2IQ:EQ3TQ:EQ3ZQ:EQ5lQ:EQ8aQ:EQ8eQ:EQ6BQ:EQ2dQ:Ep+0=FQ:EFoD6D6D6D6Q7WPsPnEdQ1deQ1dQ::Q6GQ::Q2@0151$0dW7P2Q3MQ6I+10&0d1X7221081$0dPFQ001@67$14RQ\11@78$14P8[P7\Q21u78P1n2001000000120000000aXB5X>51@81$1421078$0d[^B5^>5P1Q6FQ5MQ9Vp+0CTRQPQp+0CSR{Q;kQ0dP1Q3k#TQ3kQ3TQ3iO4b1b2b3O3b9Q37Q6G+15Q3MQ6IPQP{P{p+0CRS3MQ7cPwP1Q5YQ3RQ3gQ1AO4b1b2b3PQP{P{Q3MQ7bQ51P1Q3RQ5YQ3gQ1AO4b1b2b3H1tE=Q1xP1E=b<Q1xP1E=b<N>1sQ<vQ<SP1p+0GaRwp+0CbR}PTQ<pPwP}PwPTCKdO4b9Q9~p+0G`S<SP=P@Q<S/U=dP0DRQ:5P}Q:5P|Q1yP1PdQ5APvEJW7P|Q2?P}P<Q6iD<P|P2Q::,AbQ:`Q<i60;bQ2?Q25n0100000020000Q8<P<Q6iD<PeQ81P|P>Q2?P}P<Q6ig03<HRpQ:`Q9xQ:{g03=R%}pg03>\N=0PQ11P9P1p+0GbRpP}Q6sQ<pPpP}PpQ6sCKdO4b9Q:5PwP=P@1Uw=dQ8<DRQ::P}Q::P|Q1wP1PSQ7^PZEJW7Q:JPTQ:JQ2dQ:JQ:iQ:JQ3ZQ:JQ2BQ:JQ:wQ:JQ5QQ:JQ8cQ:JQ8gQ:JQ69Q:JQ2eQ:Jp+0=GS2eQ:JFoD6D6D6D6Q7ZQ9~PnEdQ25eQ25Q:?Q9aQ:?P|Q2AQ9tP1Q7rCxQ9EPYQ7?POEJW7Q:qQ:DQ:qp+0GdRZ@0l1~32X;5Q:?Q:JQ:JQ6rQ=5p+0COS:JQ9VPQPQP{PfPgPlPjQ:AQ7s61;^P;Pkb5b6b4X05151~Q9x,51/4L'@^05P1Q7?O1b1b2b3K1LQ2eQ:qQ9VPQPQP{Q7gQ:JP1Q7?PqO2b1b2b3Q9VPQPQP{Q7fQ:EP1Q7?Q1HO2b1b2b3K0MQ6@eQ6@Q:DQ:qQ:DP|Q2PQ:VP1PoP]p+0@eS2PP<GfW7P|Q1{Q9EPYQ7?D<P|Q1{P0PYQ7?D<POQ3mP|P>Q1{Q9EPYQ7?g03?fROQ;Dg03A0%}Og03B:N;1rQ0IQ<sP1p+0GeROQ9EPTQ;S#NS<sPOQ9EPOPTCKdO4b9Q:DPZQ<GP@Q<G,UZdP0DRQ:IQ9EQ:IP|Q1sP1PJQ7BPdEJW7P|Q2>Q9EP]Q2PD<P|P2Q:L,AbQ;lQ2>Q1wn0100000020000P0P]Q2PD<P<Q84P|P>Q2>Q9EP]Q2Pg03CDQ::Q9sQ9RQ:^Q2_g03DNPng03EXQ:TQ6PQ:TQ8?Q:TQ2gQ:TQ:wQ:TQ6UQ:TQ6IQ:TQ6VQ:TQ5TQ:TQ8gQ:TQ8iQ:TQ9PQ:TQ2hQ:Tp+0=JQ:TI0CD6D6D6D6D6Q6hQ9sPnEdQ9ceQ9cQ:LQ=3Q:LPEP\Q<K>1Q1oQ06Q2tI0>W7Q<FQ5^p+0GgS=3Q5680l152DX;5Q:LQ5]'yQ9PQ<Fp+0CXR<p+0CWR{P{p+0CVS<FQ8^Q;6P1Q4JPKO2b1b2b3P<P{P{Q<FQ89Q<lP1Q4JQ0FO2b1b2b3K0MQ4ZeQ4ZPDQ5^Q;LQ1rP1Q06Q:^I0>X7DPEQ5JQ;LQ:^721X@EQ0?Q6{Q1Q+1@Q5^Q0640GP>Q6{Q1QPUQ06Q8_P<P<P{PfPgPlPjP^Q2^P:P^Q;sP:P^P^P_PRA\^RWI0:FCP;Pkb5b6b4X05AP1pwRE10Z8Q<@,47RQQ:D7gQ[[^05P1Q:PPKQ0GO3b1b2b3Q9x9gUUeQ5KQ9TQ9xP[P9Q5XQ9TQ9nQ9xQ9xQ:EG3Q8_P<P<P{PfPgPlPjP^Q2^P:Q;`,WR=>^WCLP;Pkb5b6b4X05148~Q:?7P?\E^05P1Q:PPKO2b1b2b3I18Q5KeQ8FQ2gQ9xQ4zQ2gPUEQQ:y/1YPVQ=4Q:}/4cREQ9~Q9nPEQ<|EQX=AQ6HQ8FQ3<Q8FQ4?Q8FQ3<Q8FQ8FQ8F3~Q7vQ4ZQ6PQ41P[P9Q2lQ;pQ62Q9xQ9xQ:EG3Q4zQ3DQ4_Q5BP[P9Q5XQ9TQ9nQ70Q70Q=4G3P[P9Q2lQ;pQ62PUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^p+0C\REP:P^Q8SQ8R5z^P^P^Q8PQ:7P^P^Q9QQ:0Q0cI0oI0:EYFCP;Pkb5b6b4X05X:5X8Fp+0Gc9P8ZRRp+0Gh,08RQQ;@/07RqQ56,56S56Q56PDQ56PpPD14BG/4?R?Q56P4E[CZ[[[^05^:5^8FP1Q5DQ:PQ<>PKPePvO6b1b2b3DEQ6HeQ2hQ2q-00VQ:yPYPVQ8FQ;0/4cRGQ9~Q4zPGQ<|EQX=AQ6WQ=2Q6_Q=2Q4<Q=2Q6_Q=2Q=2Q=23~Q5_Q4YQ9wQ36P[P9Q9iQ66Q<wQ9xQ9xQ:EG3Q6aQ4]Q5:p+098S5:P[P9Q5XQ9TQ9nQ:}Q:}Q9OG3P[P9Q9iQ66Q<wPUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q8VQ7r5z^P^P^Q8TQ:7P^P^Q9QQ:AQ0cI0oI0:EYFCP;Pkb5b6b4X05X:5X8FQ8E,56RGPGPDPGPpPDP?PGP4E[CZ\q\Q\R^05^:5^8FP1Q5BQ:PQ<>PKPePvO6b1b2b3DEQ6WeQ6qQ34-00VQ3ZP]PVQ=2Q;m/4cRGQ9~Q6aPGQ<|EQX=AQ6EQ9eQ6XQ9eQ3YQ9eQ6XQ9eQ9eQ9e3~Q:ZQ40Q9yQ4WP[P9Q2WQ=7Q=5Q9xQ9xQ:EG3Q4{Q4[p+096Q4KP[P9Q5XQ9TQ9nQ;0Q;0Q6MG3P[P9Q2WQ=7Q=5PUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q7GQ8Y5z^P^P^Q7EQ:7P^P^Q9QQ7uQ0cI0oI0:EYFCP;Pkb5b6b4X05X:5X8F156LRLPLPDPLPpPDP?PLP4E[CZ\q\Q\R^05^:5^8FP1Q5:Q:PQ<>PKPePvO6b1b2b3DEQ6EePyQ6F-00VQ5?PJPVQ9eQ2P/4cRLQ9~Q4{PLQ<|EQX=AQ6KQ60Q3WQ60Q6`Q60Q3WQ60Q60Q603~Q9|Q3EQ8OQ4UP[P9Q8fQ2LQ=8Q9xQ9xQ:EG3Q1PQ23Q4IQ4XP[P9Q5XQ9TQ9nQ7?Q7?Q0CG3P[P9Q8fQ2LQ=8PUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q7OQ8\5z^P^P^Q8[Q:7P^P^Q9QPhQ0cI0oI0:EYFCP;Pkb5b6b4X05X:5X8FQ<S,56RhPhPDPhPpPDP?PhP4E[CZ\q\Q\R^05^:5^8FP1Q4KQ:PQ<>PKPePvO6b1b2b3DEQ6KeQ6IQ3k-00VQ5pQ1rPVQ<[Q6j/4cRhQ9~Q1PPhQ<|EQX=AQ3{Q<BQ6TQ<BQ3=Q<BQ6TQ9AQ3jQ3|Q6[Q3GQ5uQ4hQ4GQ4VQ4FP[P9Q5XQ9TQ9nQ;mQ;mQ<[G3P[P9Q9rPuQ5{PUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q7yP^Q3HP^P^Q9QQ9hQ0cF^EYFCP;Pkb5b6b4X05X:5X8FQ5@,56RuPuPDPuPpPDP?PuP4E[CZ\q\Q\R^05^:5^8FP1Q4XQ:PQ<>PKPePvO6b1b2b3DEQ3{eQ5TQ5QQ3?Q0KPVQ1cQ6p/4cRuQ9~Q4hPuQ<|EQX=AQ3zQ;8Q3;Q;8Q39Q;8Q3;Q9:p+0>`Q4TQ98Q7wQ6ZQ6bp+08nQ4CQ5=P[P9Q5XQ9TQ9nQ6jQ6jQ1cG3P[P9Q7@Q<hQ;bPUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q6nP^Q87P^P^Q9QQ8UQ0cF^EYFCP;Pkb5b6b4X05X:5X8F156ZRZPZPDPZPpPDP?PZP4E[CZ\q\Q\R^05^:5^8FP1Q4FQ:PQ<>PKPePvO6b1b2b3DEQ3zeQ7DQ<yQ6JQ1GPVQ8`Q;?/4cRZQ9~Q6bPZQ<|EQX=AQ2uQ;5Q38Q;5Q3:Q;5Q38Q9JQ9;Q4SQ9=Q3KQ6?Q4eQ4Ap+08jQ4=P[P9Q5XQ9TQ9nQ6pQ6pQ7NG3P[P9Q;XQ;UQ8JPUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q86P^Q2jP^P^Q9QQ<<Q0cF^EYFCP;Pkb5b6b4X05X:5X8FQ;x,56RZPZPDPZPpPDP?PZP4E[CZ\q\Q\R^05^:5^8FP1Q5=Q:PQ<>PKPePvO6b1b2b3DEQ2ueQ7:Q73Q3qQ1NPVQ01Q2f/4cRZQ9~Q4ePZQ<|EQX=AQ3yQ;4Q2{Q;4Q2|Q;4Q2{Q<\Q=9Q3FQ9DQ4QQ5vQ6cQ4RQ49Q4PP[P9Q5XQ9TQ9nQ;?Q;?Q;[G3P[P9Q;]p+0@8Q8IPUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q85P^Q84P^P^Q9QQ9mQ0cF^EYFCP;Pkb5b6b4X05X:5X8FQ;f,56RZPZPDPZPpPDP?PZP4E[CZ\q\Q\R^05^:5^8FP1Q4=Q:PQ<>PKPePvO6b1b2b3DEQ3yeQ8=Q<^p+05gRZQ0UPVPxQ6r/4cRuQ9~Q6cPuQ<|EQX=AQ3xQ<}Q2yQ<}Q2zQ<}Q2yQ<OQ6]Q5iQ8]Q4OQ2mQ8|Q42Q5<Q47P[P9Q5XQ9TQ9nQ2fQ2fQ;^G3P[P9PtQ1>Q8NPUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q3mP^Q83P^P^Q9QQ9oQ0cF^EYFCP;Pkb5b6b4X05X:5X8Fp+0G]Ru,56RhPhPDPhPpPDP?PhP4E[CZ\q\Q\R^05^:5^8FP1Q4PQ:PQ<>PKPePvO6b1b2b3DEQ3xeQ8wQ6}Q3oQ0]PVQ;1Q6i/4cRhQ9~Q8|PhQ<|EQX=AQ3wQ;cQ2wQ;cQ2xQ;cQ2wQ9fQ9gQ3QQ;=Q3UQ<QQ4cQ3}Q4BQ3`P[P9Q5XQ9TQ9nQ6rQ6rQ;rG3P[P9Q;~Q;vp+0>iPUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q82P^Q81P^P^Q9QQ:6Q0cF^EYFCP;Pkb5b6b4X05X:5X8Fp+0GV,56RhPhPDPhPpPDP?PhP4E[CZ\q\Q\R^05^:5^8FP1Q47Q:PQ<>PKPePvO6b1b2b3DEQ3weQ8sQ6zp+05eRhQ0lPVQ71Q5A/4cRLQ9~Q4cPLQ<|EQX=AQ3vQ7>Q6SQ7>Q2vQ7>Q6SQ;:Q;gQ4NQ6oQ3IQ9pQ5xQ4>Q6\Q4:P[P9Q5XQ9TQ9nQ6iQ6iQ;oG3P[P9Q;iQ<Yp+0>kPUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q80P^Q7<P^P^Q9QQ:EQ0cF^EYFCP;Pkb5b6b4X05X:5X8FQ<m,56RLPLPDPLPpPDP?PLP4E[CZ\q\Q\R^05^:5^8FP1Q3`Q:PQ<>PKPePvO6b1b2b3DEQ3veQ<gQ6xQ3@Q0iPVQ7mQ7^/4cRLQ9~Q5xPLQ<|EQX=AQ3uQ:~Q6RQ:~p+06[Q:~Q6RQ3cQ9bQ4MQ2NQ3fQ61Q4ap+08\Q4;p+08ZRLP[P9Q5XQ9TQ9nQ5AQ5AQ;}G3P[P9Q<xQ7VQ7pPUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q7~P^Q7}P^P^Q9QQ:MQ0cF^EYFCP;Pkb5b6b4X05X:5X8F156~R~P~PDP~PpPDP?P~P4E[CZ\q\Q\R^05^:5^8FP1Q4:Q:PQ<>PKPePvO6b1b2b3DEQ3ueQ<{Q77Q0oPVQ:|Q7?/4cRcQ9~Q4aPcQ<|EQX=AQ3tQ:zQ3BQ:zQ3sQ:zQ3BQ68Q7xQ3]Q9@Q3rQ<VQ5Dp+08Yp+08XQ2RP[P9Q5XQ9TQ9nQ7^Q7^Q<zG3P[P9Q6gQ8pQ<qPUPUQ5WG3EFE8E8Q8_P<P<P{Q;hPgPiPjP^Q<LP:P^PCP:P^PEP:P^Q7|P^Q7{P^P^Q9QQ6dQ0cF^EYFCP;Pkb5b6b4X05X:5X8F156pREPEPDPEPpPDP?PEP4E[CZ\q\Q\R^05^:5^8FP1PLQ:PQ<>PKPePvO6b1b2b3DEQ3teQ0|Q1WI0`+0eGIGIGIGIGIGIGIGIGIGIGIGIQ06Q1Q60fUeL0iE=Q1`P1EGb9Q1wP1E=b<Q2_Q<RQ;D,V1X;5Q0801GrQ8m%TXQ;n$0V[[Q8mQ03Q08Q7=<1F8UW?Q8mQ03Q;k#T[]?Q8_P<P<P{PfPgPlPjP^P^Q8kQ;<P:Q0MQ05$0R61N59\^`J0UP;Pkb5b6b4X05X8FB0F81wQ;<,V8[^05^8FP1&0VyPyQ1EO3b1b2b3b[b\Q2_,iOQ<RP{Q<FQ<FQ9VPfPgPlPjP^P^Q<kQ8kP:Q<3J0UP;Pkb5b6b4X05X8F&0V1RX/18Q0\[^05^8FP1Q2IQ3ZQ3lO3b1b2b3P{Q<FQ<FQ9VPfPgPlPjP^P^Q8kQ;@P:Q6DJ0UP;Pkb5b6b4X05X8FQ3^,V1RU,18Q::,V8[^05^8FP1Q3Z$0VQ3ZQ3lO3b1b2b3K0M+1pNA1oQ8tQ9dP1p+0GfRFQ9BPTQ0xPFQ9BPFPTCKdO4b9Q:IPOQ:\P@Q:\,UOdP0DRQ:LQ9BQ:LP|Q1gP1P\Q<MPSEJW7Q:LQ0`Q:LP|Q2MQ:DP1P}P\Q<MPSGfW7P|Q1lQ9BPJQ7BD<P|P21AbDQ9UQ1lQ26n0100000020000Q6sPJQ7BD<PdQ85P|P>Q1lQ9BPJQ7Bg03FbRdQ9sQ9sQ9?g03Gl%}dg03I6N=0PQ<PQ;WP1Q=3Q9?P0Q0xQ=3Q9?Q=3P0CKdO4b9Q:LPFQ:\P@Q:\,UFdQ6sDRPDQ9?P|Q9cP1Q1rQ<>PYEJX7DQ:]Q:^Q:]Q5}Q:]Q8AQ:]Q2FQ:]Q6UQ:]Q7iQ:]Q3hQ:]Q37Q:]Q5UQ:]Q8hQ:]Q8jQ:]Q9NQ:]Q2OQ:]p+0=LQ:]FoD6D6D6D6D6Q7cPsPnEdQ26eQ26Q:SQ;NQ:SP|Q1nQ2JP1Q8>CxP}PHQ6tP]EJW7PWQ<KP1p+0GiRWQ;IPTQ08#NPWQ;IPWPTCKdO4b9Q:SQ;K;20Q7XQ;IQ7XP|Q1pQ9xP1Q9RPNQ6uPJGfW7P|Q1gP}PHQ6tD<P|P2Q:\,AbQ:VQ:760;bQ1gQ1an0100000020000P0PHQ6tD<P]Q87P|P>Q1gP}PHQ6tg03J@R]Q:VQ:7Q9Bg03KJ%}]g03LTN=0PQ9{Q5eP1p+0GjR]Q9BPTQ<pP]Q9BP]PTCKdO4b9Q7XPWP=P@1UW=dP0DRQ:\Q9BQ:\P|Q25P1Q0KQ6{P\EJW7Q:7Q<TP1p+0GkRWQ;GPT%NuPWQ;GPWPTCKdO4b9Q:\Q;H;20PaQ;GP|Q1jPsP1Q9RQ0LQ77Q1rGfX7aP|Q22P}Q0KQ6{D<P|P21Ab=B0;bDMQ22p+03`RMn0100000020000P0Q0KQ6{D<P\Q88P|P>Q22P}Q0KQ6{g03M^R\PDQ9xQ:Hg03Nh%}\g03P2N=0PPCPrP1p+0GlRrP}PTQ<sPrP}PrPTCKdO4b9PaPWQ<GP@Q<G,UWdP0DRP=P}P|Q1aP1Q0SQ6xPHEJX7=p+0EAR=P0P=Q6sP=Q:iP=Q=5P=Q8GP=Q2nP=p+05UR}P=Q6FP=PhP=Q2[P=Q2;P=Q8lP=Q8oP=Q9TP=Q2pP=Q8LP=FoD6D6D6D6D6D6Q7hQ9~PnEdPMePMQ<GQ;mQ<GP|Q1xQ:\P1Q8vCxQ9EQ0RQ6zPNEJW7Q<GQ;mQ<GP|Q1xQ:\P1Q9EQ0RQ6zPNGfW7P|Q1dQ9RQ0SQ6xD<P|P2Q;S,AbQ<lQ1dQ1fn0100000020000Q6sQ0SQ6xD<PHQ7LP|P>Q1dQ9RQ0SQ6xg03Q<RHQ:SQ::Q99g03RF%}Hg03SPN=0PPzQ5dP1p+0GnRzQ;kP0%NpPzQ;kPzP0CKdO4b9Q<Gp+0GmRzPwP@1UzwdQ6sDRQ;SQ;kQ;SP|Q2=P1Q0OQ6}Q0KEJW7Q;RQ6PQ;RQ78Q;RPTQ;RQ3ZQ;RQ=8Q;RQ8QQ;RQ2qQ;RQ6FQ;RQ3RQ;RPZQ;RQ3TQ;RQ2aQ;RQ8nQ;RQ8qQ;RQ5ZQ;RQ:yQ;RQ9|Q;RI0CD6D6D6D6D6D6D6Q7lQ:?PnEdQ1feQ1fQ<IQ;nQ<IP|Q1gPaP1Q8xCxQ;@Q1GQ<^Q0LEJW7Q<IQ;nQ<IP|Q1gPaP1Q;@Q1GQ<^Q0LGfW7Q0K-1n>Q;nQ02'MQ;n$0pE=Q1aP1E=b<P0P1EGb9ESQ;mQ02'MQ;m$0pE=Q25P1E=b<PTP1EGb9ESPTP1EGb9PTP1EGb9ESPTP1EGb9Q1dP1E=b<P0P1EGb9ESQ:^Q:iP<P{P{Q<FPfPgPlPjP^P^Q<kQ;@P:Q<3Q;@5z^J0UP;Pkb5b6b4X0511XUQ0\Q<S80F8[^05P1Q:wQ0rO2b1b2b3+1jE=PTP1EGb9ESPTP1EGb9ESQ:NP1EGb9Q1xP1E=b<Q6sP1EGb9ESPTP1EGb9ESQ9EQ3Z+1BQ2@Q5?Q3Mp+0CQRUPUp+0CPRXQ6hPoP1Q5MQ6FQ1=Q3eO4b1b2b3Q3MPUPUPXQ7`Q9EP1Q6FQ5MQ1=Q3eO4b1b2b3Q3MPUPUPXQ;FQ<kP1Q5M#TQ5MQ6FQ3eO4b1b2b3I1kE=Q1pP1E=b<P0P1EGb9ESQ:wQ2g+0yQ7iQ3T'5Q2gPXQ:JQ:Jp+0CNQ0^Q<tQ2]Q0960j560j5Q0a+16<02fPgPiPjP^Q:YP:P^P^P^P_Q0:Q;3I0:P:P^P^P_Q:IQ:IQ<v5\^I0:FCP;Pkb5b6b4X05X:51V1mQ1m1576Rm?gms[[^05^:5P1Q6GP}Q3aQ2YO4b1b2b341lE=Q2MP1E=b<Q1vP1E=b<Q8<P1EGb9ESPTP1EGb9ESQ8?P1EGb9ESQ75P1EGb9ESQ8GP1EGb9ESQ2?P1E=b<Q2?P1E=b<Q8DP1EGb9ESQ2t00zyQ0`Q6UQ90Q8BQ8BQ8~PfPgPiPjP^P^Q<XQ0:9\^`P:P^Q<XP^Q0:,p`H1CJ0UP;Pkb5b6b4X05X:5Ag118Q0\1087'1[^05^:5P1Q:iQ37Q3XO3b1b2b3Q90Q8BQ8BQ8~PfPgPlPjP^Q9oP:Q9oCLP;Pkb5b6b4X05Q:7,V11V8C[^05P1Q:iQ10O2b1b2b3H1mE=Q2AP1E=b<Q2AP1E=b<Q75P1EGb9ESQ75P1EGb9ESQ8DP1EGb9ESQ8QP1EGb9ESQ7jP1EGb9ESQ8PP1EGb9ESQ8PP1EGb9Q8PP1EGb9ESQ8wQ0HE=Q8wQ02'MQ8w$0pE=Q5fP1E=b<Q7FP1EGb9ESQ<yQ0EE=Q<yQ02'MQ<y$0pE=Q6QP1E=b<Q7jP1EGb9ESQ8SP1EGb9ESQ8VP1EGb9ESQ8YP1EGb9ESQ8[P1EGb9ESQ8^P1EGb9ESQ8dP1EGb9ESQ7_P1EGb9ESQ8lP1EGb9ESQ;=P1EGb9Q6uQ0{E=Q8qP1EGb9ESQ1WQ0[Q2TQ6uQ;>PnCcQ1WeQ1WPPQ:CQ:H92I1X7PPPQ:CQ1:P1Fbb<Q1oQ0~Q2TQ6uQ;\PnCcQ1oeQ1oPPQ5QQ1u92I1X7PPPQ5QQ1RP1Fbb<Q1BQ1XQ2TQ6uQ;ePnCcQ1BeQ1BPPPxQ8bQ67Q1~P1E=b<Q24Q0gQ2TQ6uQ;aPnCcQ24eQ24PPQ:>Q7UQ7SQ17P1E=b<Q1TQ4gQ2TQ6uP3PnCcQ1TeQ1TPPQ;=Q;w92I1X7PPPQ;=Q21P1Fbb<Q0yQ0nQ2TQ6uQ;tPnCcQ0yeQ0yPPQ1]Q5f92I1X7PQ33Q5CP1E=b<Q1QQ0lQ2TQ6uQ;uPnCcQ1QeQ1QPPQ5GQ1I92I1X7PPPQ5GQ15P1Fbb<Q1iQ18Q2TQ6uQ;hPnCcQ1ieQ1iPPQ:>Q7UQ7Sp+02hP1E=b<Q0vQ5SQ2TQ6uQ;9PnCcQ0veQ0vPPPxQ8bQ67Q1kP1E=b<Q0uQ1;Q2TQ6uQ;CPnCcQ0ueQ0uPPQ1zQ:>92I1X7PPPQ1zQ12P1Fbb<Q0sQ1[Q2TQ6uQ;<PnCcQ0seQ0sPPQ5`Q5g92I1X7PPPQ5`Q1<P1Fbb<Q19Q1?Q2TQ6uQ;@PnCcQ19eQ19PPQ;?Q2f92I1X7PPPQ;?Q1eP1Fbb<Q0pQ0qQ2TQ6uQ;_PnCcQ0peQ0pPPQ6pQ;?92I1X7PPPQ6pQ0}P1Fbb<Q0oQ0iQ2TQ6uQ;kPnCcQ0oeQ0oPPQ6jQ6p92I1X7PPPQ6jQ1bP1Fbb<Q0mQ5RQ2TQ6uQ;nPnCcQ0meQ0mPPQ;mQ6j92I1X7PPPQ;mQ1OP1Fbb<Q0kQ1DQ2TQ6uQ;DPnCcQ0keQ0kPPQ;0Q;m92I1X7PPPQ;0Q1@P1Fbb<Q0jQ13Q2TQ6uQ;FPnCcQ0jeQ0jPPQ:}Q;092I1X7PPPQ:}Q1tP1Fbb<Q2TQ6uQ;GPnCcQ13eQ13PPQ70Q:}92I1X7PPPQ70Q0|P1Fbb<K0LK0LK0LK0LK0LK0LK0LK0LK0LH1hQ;qQ;qP|P1Q:HQ0ZQ;rD<-0mtQ;E'1WA+1<eWUWZWYWFWNWOP8P1O2n2001000000121000000W9WGWHWIWLWMPBP6P7P8P1O5n700000001000000151104103102101100W9WJWKWVaaaaaaaaaaaaaaaaaaaaaaaaaaWWWXWSWRWQWPWTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW_W^W]aaaaaaaaaaaaaaaaaaaaaWbaaaaWgaaaaaaaXa5aaaaaaaaaaaaaaXj5aaaaaaaXi5aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaX`5aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaXh5aWfaaaWcaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWdaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sw_enter_eq : forall regs mem rom (su f wp fd : Z) (s l bufp bufsz can ret : word),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0xc6000 <= f)%Z -> (f + 232 <= 0xf8ac0)%Z ->
  sw_file mem f wp wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  (0 <= wp < 2^64)%Z -> (bv_unsigned l < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xae4d4 : word) mem rom)
      (mkst regs' (0xae55c : word)
         (mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                  (getr regs 20) (getr regs 21) (getr regs 22) can wp 0 s l) rom)
    /\ getr regs' 17 = Z_to_bv 64 66
    /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (su - 88)
    /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 2 = Z_to_bv 64 (su - 112)
    /\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
    /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 (su - 88)
    /\ getr regs' 21 = Z_to_bv 64 0xf8ac0
    /\ getr regs' 22 = l
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0143 ()) ["FPX_1"] "p'0h04__x1h17__arithh26__sat3h36__sat4h44__ffh58__varmaph65__with71bh84__p1h91Hh:1zh;2gHh<4__x2h=1nh>2Hah?1oh@1xhA5regs'hB2b1hC2b2hD1mhE1yhF2FDhG4FbszhH4FbufhI3FfdhJ3FhihK3FlohL3FwbhM3FwphN4GcanhO4GgothP3Ha0hQ3Ha1hR3Ha2hS2HlhT3HrahU3HsphV5SMALLhW3SOKhX4SUhihY4SUlohZ4WPhih[6__sat5h\6__sat6h]4bufph^5bufszh_3canh`1fha2fdhb1lhc3memhd4regshe3rethf3romhg1shh2suhi2wpi007swf_bszi017swf_bufi026swf_fdi039swf_wbasei048swf_wposp%0p%1p%2p%3p%4p%5p%6p%7p%8p%9p%:p%;p%<p&0p&1p&2p;1p;3p;2p;5p;4p;?p;7p;=p;6p;Bp;<p;8p;Ap;>p;:p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004`R1p4p710R2p8p1005>p4p710P2p8g005]j1:Tg006Bk10UTg006`k10CTg007Cj1BTg007hj1iTg008Fj1STg008ej32Tg009?k11VTg009jk219Tg00:Mk218Tg00;0k51QTg00;TR2j20Tg00<0k11OTg00<Nj2hTg00<gR3j24Tg00=Dk427Tg00=gR4k10QTg00>Gk213Tg00?Yk31KTg00E0k220Tg00E\k10dTg00F<k30ATg00BHk10sTg00@fk11|Tg00AIk110Tg00Akk21FTg00Bhk30bTg00CKk31vTg00Cok11uTg00DMk31DTg00K^j2Qk11pTg00LDk21CTg00Ldj25Tg00MAj2ZTg00M]k30;Tg00H6k11HTg00NJk20NTg00ORj2MTg00PFk21NTg00Pnk31=Tg00I:j2yTg00QRk20BTg00R:k21<Tg00RZk21;Tg00SOj4jTg00F\k20{Tg00GXk11ZTg00HXk21YTg00ITk21XTg01Hik31:Tg00J@k41UTg00K2k11TTg01IHk40kTg00Sok21STg00Tak20VTg00Vak201Tg00UCj2@Tg00Uoj29Tg00WAk200Tg00XJj5<Tg00Y<j2fTg00Yfj3_Tg00ZZj27Tg00[4S00j21Tg00[Ok20iTg010Wk10yTg03TZk126Tg00\Bk124Tg00]4k20xTg00]gk20wTg00^Zk216Tg00_Nm?23Tg00`Uk306Tg00aPk30>Tg00bQk20PTg00cOk215Tg00dNj3]Tg00eIk422Tg00fIS01k721Tg00gLk21LTg00hOk211Tg03UWk11}Tg00him=0OTg00i`j2TTP1j6=Tg00jCmB08Tg00kBm<1zTg00G:k11wTg00l:k40cTg00lej6FTg00mMj68Tg00n6k30`Tg00o4k80]Tg010;j6ITg011[mA0jTg012Pj4bTg01F_k41tTg013Rm=1rTg014Hm=1qTg015>m=1oTg0164m=1nTg016kk21@Tg03VNk11mTg03WOm>1kTg01;dk21jTg01<kmA1iTg01=`k21hTg01>\k10nTg01?Rk21fTg03XHk11gTg03YTk11eTg03ZRk11dTg01Bgk41lTg01Cnk41cTg01DHk40MTg01E3k70RTg01F:m<1bTg01EWk31sTg01IimB1aTg01JOk31?Tg01HEk80pTg01Gak70YTg01K2k41>Tg01Kck31`Tg01LIm<1_Tg01Lnk30~Tg01Mjk11yTg01Njk81ITg01OGm:1^Tg01PHk71]Tg01G=k61\Tg01QJk714Tg01Qnk40uTg01RIk71[Tf0R1#:#:#:#:#:#:#:#:p>0e%:1#:p>1x%:1#:#:#:p>0^%:1#:#:#ip=`%S1#Sp>1W%S1#S#S#Sp>1R%S1#S#S#S#S#S#S#Sp>1P%S1#S#S#S#S#S#S#S#S#S#S#S#S#S#S#Sp>0[%B1#B#:#:p>0v%B1#Bp>09%:1#Bp>0Z%:1#B#:#Bp>0t%B1#:#:#:p>0T%:1#B#:#B#B#B#:#:#B#:p={%B1#:#B#:p>0X%B1#:#:#ip=s%:1#ip>0W%B1#:p>0_%:1#:#B#:p>0|%:1#B#B#Bp>0Gg01SER5f3R6f2R7'ff1R8/f132p=L%:1#B#B#:p>0mg01ScR9/Z1p>0S1091p=XP7g01TAR:g01T`R;P;g01U@R<P5P8g01U`R=P1H0Mg01VGR>K0Rp=>1y51p=NA2581p=A%:1#B#:#B#B#B#:#:p>1M%B1#:#:#Bp>0h%:1#B#:#B#B#B#:#:#B#:#B#:p=q%:1#B#:#:p>0r21951p=gP7P:P;P;P<P5P8g01VgP1H0MP>K0Rp=ag01X5R?:0b81p=?%i1>0b8?p=vg01XQR@P5P5P5P4P4f5R4f4RAP6P7P8P1N<1bp>0}B1s581p>041478/01p=O10971Z81'1p=pP5P5P5P5P5P5P3P1P8P7P3P6PAP4f6R3f7RBf8RCf9RDNB1ap=lB1?581p=UP6P:P;P;P<P7P8P1L0pp=Jg01ZYS02g01`URE721p>0lP7P:P;P;P<P8P1K0Yp=k1M819_67p=zg01Y0RFP7P8P1H1>p>0E1Z81,17p>0Lp-0RG/y1:1`78p=~P5P7P8P1Cjp>05P5P5P2PBP2P3P4PAP6P7P8P1N<1_p=3&0d6:0A4AP7P8P1Cbp>0D1081,77,16,1Ap=G10A61081,77'1,14p=P1098/11p>171f819257p>25&0d1:0A78:0AA6p>0@B0A781:0AA6p=6&0d1:0A78:0AA6:0A34p=oB0A4A6P7P8P1Cbp=cPBA_34AP6P7P8D<>0~F1p=eB0~F81p>0g1978=261p>121967=2A8/11p=xA234AA2678/11'1p=w1181,17p>1J1481,Q7p>0fPFP6P7P8H1>=2A1p>0=A2678/11p>1~Q02&1y1'yp>03B0b678=2A1p=WP4PAP6P7P8D<>0~F1p=KP5P3P4PAP6A]781E=p>0K20B78,M6=2A1p>0F1478,Q6=2A1p>0JP6P:P;P;P<P5B1?578g01WNR2P1H0MP>K0Rp>0<1478=251p>07P5PBP3P414A6P7P8P1L1Ip>0?P5PAP6P7P8P1E=p=D1M78=261p=|P5PBP3P4PAP6P7H0cP8P1E=p=^1481,07p>0:14671481'0p=}PFP1P8P7P6PAP4P3PBPCN:1^p>02P3P4PA1y67P8P1E=p=dPFP4PAP6P7P8P1K1]p=;1Q78=261p>0q&0d1:0A78p>1{20B81,M7p>1GPAP:P;P;P<P6P:P;P;P<P5P7P=P8H0MP>K0RP1K0Yp>0IP5P8P=P1H0Mp=uP8P:P;P;P<P1J1\p>1EPBP:P;P;P<P3P4P:P;P;P<PAP6P:P;P;P<P7P:P;P;P<P8P>K0RP1K14K0YK0Yp=tP3P:P;P;P<P4PAP6P:P;P;P<P7P8P1L0pL0pp=C144A/061078/71'1p=Y10961Z78'1/11p=[PA1167P8P1H0cp=E1078/71p=n1Z4A,131467/08/11'1p=mP@PAP6P7P8P1E=p>0aP8g01[9S03P1P?H0up>0\PBP3P@P4PAP6P7P8E=P1H0up=HPA1067P8P1H0cp>0zP3P:P;P;P<P4PAP:P;P;P<P6P:P;P;P<P5P7P=P8H0MP>K0RP1K14K0Yp=\P4P:P;P;P<PAP6P7P:P;P;P<P8P1K0YL0pp=R10671781'1,1Ap=rP7P:P;P;P<P5P8P2P1H0MP>K0Rp>1BP5P3P4PAP6P7P8P1L1Ip>1APAP:P;P;P<P6P:P;P;P<P5P7P=P8H0MP>K0RP1K14p>0oPFP4PAP6P7P8P1K1[p=VP3P4PAP6P7P8P1H0uH0up>0Hg01\5R>#:R=#:R2#:RH#:RI#:S04#:RJ$0Ug01\ZRK&0UH$0CP0%B>RL#:RM#:RN#iP5%:J$0e$0e$0eRO#:RP#iP5%BLRQ#:RR$1xRS#:g01]8&0^P$0e#`P5g01]]RP#SRT$1WRU#SS05$1RRV$1P$0[$0[$0[$0[$0[$0[P@%:NRW$0v$0e#`P5%BR#`P5&09>$0v$0Z$0t$0T#`P5%iOP5%iJP5%{>$0X$09#sP5%iHP5%BI$0WP5%B=RJ#BRO#:RR#:$0WP5%BO#iP5%iWP5%:JRX#:RY#:RZ#iP5%iSP5%BQRQ#`P5%:WRW$0WP5&0_>$0|$09$0t$0G#`P5%iIP5Q04#iP5%iWP5%B2RW#:RI#:$0WP5%BMRM#:RS#:$0WP5&0WZP5&0T>$0X$0X$0^#`P5&0UNPK&0C1RZ&0C8R[P7P8P7P1CLR\&0C6?278R][]C]B^=KR^PG%{>$0m$09#`P5%i=S06$0SPGQ06#XPG&1V5R_21959R`2185>Ra3>P_P:P;P;P<I1QR:&0UJRJ$0CP01081Rb$1OXE5X@51hbb^E5^@5P5P5g01^<1481H27Rb#NXD5X=51Abb^D5^=5&0Q1Rb#NX@@1Abb^@@&0QVP5%{>$0m$09#sP5&1M>$0h$0v#`P5&1M>$0h$0v#sP5%{>$0G$0Z#`P5%{>$0G$0Z#sP5%{>$0G$0_#`P5%{>$0G$0_#sP5%{>$0G$09#`P5%{>$0G$09#sP5%q>$0^#`P5&0UYPK%q>$0^#sP5%:>$09$0G#`P5%{>$0T$0Z#`P5%{>$0T$0Z#sP5%q>$0|#`P5g01_=Rc2135U2135T2135P61K561K5g01_i+20&0dcRP40A&0scRc%q>$0|#sP5%{>$0T$09#`P5%{>$0T$09#sP5%q>$0r#`P5%q>$0r#sP5%q>$0t#`P5%q>$0t#sP5%q>$0m#`P5%q>$0m#sP5%q>$0G#`P5&0UMPK%q>$0T#sP5%q>$0h#`P5Q05$0QP5%i2R2#g&1|5RTAa_`aP:%q>$0h#sP5%q>$0X#`P5%q>$0X#sP5%{>$0X$09#`P5f}S07$0CP0Q07$10P0Q06,?Jf[S081vJXf\S091vJOf]S0:p+01AS0;,?JROf^S0<%i>S0=,?Jf_S0>Q0;#iP5Q06fzRU+1FP5fyRd,?JfbS0?1vJWfcS0@1vJIfdRI%BW,vJfeRW1vJYffS0A%BX,vJfgRX1vJRfhS0B%BH,vJfiS0C1vJLfjS0D1?J2fkS0EPOflS0FPOfmRO%BN,vJfnRN1vJSfoRS%BM,vJfpS0Gp+01URL$0sP01vJMfrS0HB0bJ9?fsS0IP\PGQ00P8\]&0CA?267\1&0C4?2A6\8B1v678P1n2001000000120000000aXC[XBZX=KP^p+01VR^$1uP5p+01PRK#XS0JPGp+01WRZ#gR[9>_aP:Q06#gS0Kp+01]R]61D5PTp+01CR\#gPTp+01RRM#gRHPTp+01ZS0L$0QP5P1X@5RRPRPdPVp+01TRY%NYJ0}PRfxS0MO1RePRPYO1'Ap+01MRf#gPTp+01LS0N#gPT%gLPT%gYPTp+01JRg#gPTp+01ORh#gPTp+01NRi#gPTP[PTp+01_S0O#gPTPHPTp+01YRH#gR[PT1?d]&0Cdp+01XRj#NS0P1AjjS0QP[PTQ0Lp+01HS0R'4P5p+01[R[p+01dS0S'4P5p+01iS0T#NQ0TQ0T'Ap+01jS0U#gPTp+01kS0VQ0N'4P5p+01lS0Wp+01hS0X'4P5p+01oS0Y#g=>_aP:p+021S0Z/01%X8S0[[^05PGp+020S0\#gPTftS0]p+027S0^'?Q0]$0Cp+01fS0_#gPTQ06p+01cS0`+1FP5p+022S0a#g9a_aP:Q0O$0CP0PS\SP0p+02<S0bQ0C'4P5p+02@S0c%:>$0_$09$0_$0r$09$0Z$0r'vfqR>p+02AS0dp+025S0e'?Q0Hp+02BS0fp+024S0g'QQ0Ip+02CS0hQ0='QQ0]p+02DS0ip+02;S0j'QfuS0kQ0<$10P0p+02FS0lQ0\'QfwRkp+02GS0m/Q9Q0Mp+02HS0nQ0V'QPdQ0V&0hQ$0^'vf;RQf{S0o$10P0p+02KS0pQ0V'?f|S0qQ0k$0SPGfvS0r#XPGQ0M#gPTfaS0s9a_aP:Q0aQ0e'?fBS0tp+01mS0u01C\P0p+02RS0v$1pp+01ES0w^:5p+01FS0x\5P0204aIPTp+02QS0y,01p+01BS0z,58Q0;'Z[^05PGQ0AQ0;5O1X:5PG^:5Q0;#NQ0;Q0;'Ap+02TS0{,01Q0w,58Q0wp+01DRl3O[^05PGp+02YS0|Q0\'?p+01KS0}Q0bp+02ES0~'?fLRm204aXPTp+02\S10Q0a'?Pip+02?S11p+02NS12'?fOS13Q0B-04aPTp+02_S14Q0g'?p+01QRnQ0fQ0i'?fRS15Q0C-04aPTp+02bS16p+026S17'?PYQ0~p+02IS18'?fURoQ0D-04aPTp+02eS19p+028S1:'?PZQ0np+02[Rp'?fXS1;Q0E-04aPTp+02hS1<p+02:S1='?Q0LQ0pp+02VS1>'?Q08204aOPTp+02kS1?Q0b'?P]Q12p+02SS1@'?Q0<Q0H-04aPTp+02nS1Ap+02>S1B'?p+01`S1CQ0y@0b9?Q0sp+030S1DQ11'?p+01bS1Ep+031S1FQ11'?Q0`p+01aS1G>0;JgQ02p+033S1HQ11'?p+01eS1IQ1>Q11'?Q0A21C5hP0p+02`S1JQ1JQ1C3pPGQ0rQ1G'0PGQ0rQ1E'0PGPRPRPRQ1@p+02cS1KQ1KPUQ0yp+02lS1LQ0RM:l1AekQ0},UUPTp+03;ReQ0~'?Q0uQ1HQ1HQ0_3pPGQ0Mp+01gS1M'0PGQ0MQ0X'0PGPRPRPRQ0|p+036R0P0Q0qp+02WS1Np+032S1OPiM:lPRPUO1/AdQ0q/UnPTp+03Ap+02JS1P'?p+023S1Qp+02dS1RQ1D'?Q0]Q0}-04aPTp+03DS1Sp+02LS1T'?Q17P_f~S1U&1H;R;Q16CJP:Q07,Ua=>_\P:p+03@p+03?Rq5O1Q1Q,Z8[^05PG1UahPT2185=R=Q0;'UQ0x5>_P:1U=n/U[PTp+03KS1VQ0y'?p+02=S1Wp+029S1XQ0S60;JQ021UanPT1U=MQ0O'UPTp+03ORrQ0{'?Q0dQ1QQ0X60;JQ02p+03QRsp+02US1Y'?Q0hp+03RRtQ1Y'?Q0ip+035S1Zp+03FRu'?Q0xQ0_-04aRvPTp+03URwQ1N'?Q0mp+038/?qp+01IS1[Q1I-04aPTp+03XS1\Q0|'?Q1Pp+03HS1],?eQ0NPvPTp+03[/?pp+02MS1^p+03>S1_Q1S'?PhQ1M-04aPTp+03^p+02]S1`'?p+02PS1ap+03_S1bQ1`'?Q0yQ0mQ1:60;JQ02p+03aS1cp+02^S1d'?Q1@p+03bS1eQ1`'?Q0{p+03cS1fQ1`'?Q1Yp+03PRv,?uPZ1Ua[PTp+01\Rx,U=Q1d'UPTp+03gS1gQ1`'?Q0|p+03JS1hQ0='?P[p+03iS1iQ1d'?Ppp+03LS1jp+03\S1k'?P]p+03kS1lQ14'?Q1`p+03lS1mQ14'?Q1d20NVHQ0m20NVZQ0nQ0O/M2p+02aS1nQ16$1HP^Q06p+03fS1o+1NQ0mPZ[\vQ0nPj[\sPGQ03Q06p+03jS1p<1=8UX>sQ03Pj[^>sQ03PH[^>tPGp+042S1q#g/UZ=>_aP:1M[2R=Q1<1yYLA2YLLQ0L-04aPTQ0V/01p+02fS1r,58#X[^05PGA>_`^RyP:Q129a_ZP:Q1^,UjPT1MY2Rzp+02oS1sp+01SR{9>_`P:Q0v9a_YP:Q0y,ULPT1ML2Q1HA>_`YR|P:Q1>9a_LP:Q1Y,U^PT1M^2R}p+037S1tA>_`LP:p+02ZS1u9a_^P:Q0|,UZPT1MZ2R~PePyP:Q1d9a_ZP:Q1`,UjPT1Mj2PqA>_`ZP:Q169a_jP:Q1n,UHPT1MH2p+03CS1vp+044S1w00BHP5A>_`HP:Q0Lp+02gS1x5a_P:Q1r,U[PTP=Q1]Q0L9>_`P:Q1?9a_[P:p+02jS1y,UxPTp+04<S1z00B[P51M]2p+03MS1{1Mx2R=p+03NS1|P=Prp+04NS1}p+04\S1~+1<-1;]PvP=PsQ1zPtPrQ0nCjQ11Q18Q1m'Mp+03SR=P~p+03TS20p+04?S21Pwp+03GS22p+02OS23CjQ0fQ1a/M9p+03VS24Pzp+03Wp+04HS2500BYP5P|P:Aa_LeP:p+03:R|,U^PTP}Q1kPPPc20{58R}&1Z5RwPH21Y_<R~P1P7Q02/yE21X17$0ldB1:598H1UREb4b5b6X05P_20{51:1:59$1TRvP<PZH0k^05P_P^P;Q1^CJP:1MM2RyQ1b1Mh2S26p+03`S271Mi2Q1cp+04LS28Q1eP=Q0|CjQ23Q26Q1fA>_`iP:Aa_huP:p+03ES26,UKPT1MK2Q1gA>_`hP:Q1h9a_KP:p+03IS1h,UnPT1Mn2Q1lQ1~00BnP5A>_`nP:Aa_MrP:Q1|,U{PT1M{2p+040S29A>_`MP:Aa_{=P:1UYtPTPzQ1wPzp+045S2:p+04@S2;00Be-1S{p+046S2<p+04aS2=p+047S2>Q1mQ1ACjQ1RPzp+048S2?Pzp+049S2@p+04jS2A00BKP5Pyp+04;S2BQ1HQ0='MQ1zPyp+04=S2CQ1Zp+05>S2D'Mp+04>S1ZPyQ21Q2AQ2;Q29p+03<S2ECjp+02mS2Fp+04kS2Gp+04AS2HQ2<Q2ECjQ1APzp+04BS2Ip+04CS2Jp+04DS2K?21qW7Q2JPG]7Q2K/yqQ2K?2qqp+03mS2L00V^Q1_1y|YA2|YYP_PKP;A>_`fCJP:P_Q1pP;Q1i9a_iCJP:p+039,UhPTQ0G=k_SP:Q1m9>_SP:Q0rQ0k5k_P:Q0kp+03nS2M5>_P:Q07Q0q5k_P:Q0qQ295>_P:Ak_l\P:Q1q9>_\P:Q1[9k_gP:Q1[Q1w5>_P:Ak_KhP:Q2<9>_hP:Ak_^LP:Q2?9>_LP:Ak_x[P:p+04:9>_[P:PPPcP}PwPNP~PEb4b5b6X05P_PvP<Q0FH0k^05Q0G9k_>P:Q0GQ2C5>_P:Q0`Q2<'UPTp+05kS2Np+01nS2O+01P@PPPcP}PwfJS2PP~PEb4b5b6X05RTP_PvP<fHS2QH0k^05R|PTP|P_Q2JP;fGS2RQ2I5>_CJP:PPPcP}PwP6P~PEb4b5b6X05P_PvP<P8H0k^05p+04cS2S,@Jp+04bS2T,91p+04dS2UQ2T,98p+04eS2VQ2T,97p+04fS2WQ2T,96p+04gS2XQ2T,9Ap+04hS2Yp+04`S2Z,94p+04iS2[Q2Z,93Q2AQ2Z,9BQ2GQ2Z,9Cp+04lS2\Q2Z,9Dp+04mS2]f:R<Q2Z'9p+04nS2^Q2Z,9Qp+04oS2_f<S2`p+04_S2a'9p+050S2bf=RvQ2a'9p+051S2cf>R:Q2a'9p+052S2df?S2eQ2a'9p+053S2ff@S2gQ2a'9p+054S2hfAS2iQ2a'9p+055S2jQ0tQ2a'9p+056S2k20NVvR|Q2aP|Q2ZP|Q2=P|Q2TP|Q2SP|Q2UP|Q2VQ2Pp+05<S2lfIS2mp+05nS2np+043S2o+0BCzQ2D,@Jp+06LS2p0018P@p+06MR|0016P@p+06NS2q0014P@p+06OS2r001BP@p+06PS2s001DP@p+06QS2t001QP@p+06RS2u001vP@fFS2v-00VA2@3VRTQ2Q-00VPTQ2P-00VPT200VmPTfNS2w-00VPTfPRq-00VPTQ15-00VPTp+04MS2xp+04FS2y>0E1Vp+04GS2zp+04IS2{>0E8VQ25Q2{?28UPGp+04QS2|p,2fxRTQ0<p+04PS2}PAP1D<g01a5S2~p+06SS30,51P5p+06VS31,58P5157|P5p+06TS32,56P5Q2q,5AP5p+06US33,54P5Q2r,53P5Q31,5BP5p+06_S34,5CP5Q2t,5DP5Q2t,5<P5p+06XS35,5QP5Q2`Q2u'5P5p+06oS36/Qvp+05aS37p+05[S38,5:P5p+071S39/Q:p+05cS3:p+072S3;/Q:p+05dS3<p+073S3=/Q:p+05eS3>p+074S3?/Q:p+05fS3@p+075S3A/Q:p+05gR|p+076S3B/Q:p+05hS3Cp+077S3D/Q:p+05iS3Ep+078S3F/Q:p+05jS3Gp+079S3H/Q:Q2Np+07:S3I/Q:p+05lS3Jp+07;Rz/Q:p+05mS3Kp+07<S3L/Q:Q2np+07=Ry/Q:p+05oS3MQ2PQ31'4P5fKS3NQ3;'4P5%Nm1Ammp+06YS3O,4mP5fMS3PQ3A'4P5Q2w#NQ2wQ2w'AQ2wp+06\S3Q'4P5Q13Q3F'4P5%Nq1AqqQ34,4qP5fQS3R/4zP5Q15#NQ15Q15'AQ15p+06bS3S'4P5fSS3Tp+07>S3U'4P5fTS3V#NQ3VQ3V'AQ3Vp+06eS3W'4P5p+07AS3X,4oP5fVS3Y#NQ3YQ3Y'AQ3Yp+06hS3Z'4P5fWS3[p+07DS3\'4P5Q1;#NQ1;Q1;'AQ1;p+06kS3]'4P5fYS3^p+07GS3_'4P5fZRe#N1AeeQ08Q08p+06@S3`3pPGp+05WS3aQ09'0PGQ0<Q0<p+06BR=3pPGp+05YS3bQ0>'0PGQ0sQ0sp+06DRu3pPGQ38Q0?'0PGp+06FS3c9pIIPGp+05]S3d/0WPGp+06HS3e9pXXPGp+05_S3fQ0B'0PGQ0DQ0Dp+06JS3g3pPGQ37Q0E'0PGQ2p9pOOPGQ3:/0NPGQ0GQ0GQ2q3pPGQ3>/0>PGQ3>Q0E'0PGQ3@/0OPG10|SPGQ3C/0>PGQ3EQ0I'0PGQ3GQ0k'0PGQ2N/0kPGQ3J/0dPGQ3GQ0I'0PGQ2NQ0k'0PGQ3J/0kPGQ3K/0dPGQ2nQ0o'0PGQ3MQ07'0PGp+060S3@p+01@R|'0PGp+061S3:Q0z'0PGQ3:Q0o'0PGp+062S3hQ07'0PGp+063S3i/0|PGp+064S3jQ0z'0PGp+065S3k/0lPGp+066S3lQ0x'0PGp+067S3mQ0R'0PGp+068S3n/0gPGp+07VS3o,4\P5p+082S3p,4lP5Q0w#NQ0wQ0w'AQ0xQ0xQ3]3pPGQ0xp+07ZS3q'4P5p+01GS3rp+086S3s'4P5Q0R#NQ0RQ0R'AQ0Rp+07]S3t'4P5Q1[p+089S3u'4P5%Ng1Aggp+07`S3v,4^P5p+08<S3w,4ZP5Q0PQ0Qp+07cS0Q,4fP5p+08?S0P,4iP5%Nh1AhhQ0JQ3F80LKPGQ3H9p]]PGQ3I9p{{PGApLLzPGp+08RS0J/QMQ3\p+06iS3x,MYp+07ES3yp+06dS3z,4YP5p+07@S3{,4LP5p+08VS3|/fYP5PRPRPRp+081S3}Q0SQ0SQ3rp+07oS3~p+08JS40p+06fS41M:lPRQ1[O1Q0R'Ap+08XS42/fLP5PRPRPRp+083S43Q1IQ1IQ0xQ3}p+08LQ3ZM:lPRQ0RO1Q3r'AS44p+08ZS45/f^P5PRPRPRp+085S46Q0_Q0_Q0wQ43p+08NS47p+06jS48M:lPRQ3rO1Q0x'Ap+08\S49/fZP5PRPRPRp+087S4:Q1MQ1MPlQ46p+08PS4;p+06lS4<M:lPRQ0xO1Q0w'Ap+08^S4=/fjP5PRPRPRQ3uQ0XQ0XP\Q4:Q0Jp+06nS4>M:lPRQ0wO1/Alp+08`S4?/fHP5PRPRPRp+08;S4@Q0TQ0TQ0zQ3up+08TS3up+070S4AM:lPRPlO1/A\p+08bS4BQ0L'fP5PRPRPRp+08=S4CQ0UQ0UQ0;Q4@Q3|Q3;M:lPRP\O1Q0z'Ap+08dS4@/f[P5PRPRPRQ0PQ0VQ0VP|Q4CQ42Q3?M:lPRQ0zO1Q0;'Ap+07PS4C,0\PGp+08QS0P,0lPGp+07RS4D,0lPGQ0wp+08SS4E'0PGA~lll1hllQ0}p+07US4F'0PGQ0NQ3|'0PGQ0Np+07WS4G'0PGQ42,0fPGQ3rQ3rQ3r3~Q3rQ3r'hQ3q,0{PGp+08[S4H,0YPGp+07\S4I,0YPGp+08]S4J,0LPGA~ggg1hggp+07_S4K,0[PGQ4?,0xPGp+07aS4L,0xPGQ4B,0]PGA~fff1hffQ0`p+07dS4M'0PGQ0Sp+08eS4N'0PGQ0Sp+07fS4O'0PGQ1Ip+08gS4P'0PGA~KKK1hKKQ0Vp+07iS4Q'0PGQ0Wp+08jS4R'0PGQ0Wp+07kS4S'0PGQ0up+08lS4T'0PGA~{{{1h{{Q1Qp+07nS4U'0PGQ0gp+08oS4V'0PGQ0gp+080S4W'0PGQ0ep+091S4X'0PGA~^^^1h^^Q0jQ43'0PGQ0bp+094S4Y'0PGQ0bQ46'0PGQ1Wp+096S4Z'0PGA~HHH1hHHQ0Vp+09ES4['0PGQ0Vp+09FS4\'0PGQ0\p+09GS4]'0PGQ0\p+09HS4^'0PGQ0ep+09IS4_'0PGQ0ep+09JS4`'0PGQ1=p+09KS4a'0PGQ1=p+09LS4b'0PGQ11p+09MS4c'0PGQ11p+09NS4d'0PGQ0ip+09OS4e'0PGQ0ip+09PS4f'0PGQ18p+09QS4g'0PGQ18p+09RS4h'0PGQ12p+09SS4i'0PGQ12p+09TS4j'0PGp+09^S4kQ0{'fP5PRPRPRp+099S4lQ1RQ1RPhp+097S4mQ4hQ4UM:lPRPnO1/AKS4nQ40,0MPGp+08KS40,0MPGA~nnn1hnnp+09cS4op+02XS4p'fP5PRPRPRp+09>S4qQ1<Q1<PKp+09<S4rp+09WS4sQ43M:lPRPMO1/Anp+09eS4tQ0|'fP5PRPRPRp+09@S4up+02iS4vQ4vPhQ4qp+09YS4wQ46M:lQ4nQ1xp+09VS4x'4P5p+09hS4yQ1x'fP5PRPRPRp+09CS4zQ1tQ1tPhp+09AS4{p+09\S4|p+088S4}M:lQ4np+09jS4nQ1`'fP5PRPRPRQ4[Q2FQ2FPiQ4zQ4kp+08:M:lPRPKO1/AhQ4^Q4=Q0JQ1?Cjp+07Kp+08WS4~,0MPGQ42,0MPGp+08YS50,0ZPGQ45,0ZPGQ4H,0xPGQ49,0xPGQ1GQ4J'0PGQ1GQ4='0PGQ4gQ4Pp+08cS51p+034Cjp+07TS52p+08hS53p+08iS54?210W7Q53PG]7Q54/y0Q54?200Q2>Q53;_^Q4R,@Jp+08kS55?2Z^PGQ4xQ4TQ4RPjCjp+07YS56p+0:;S57/fHP5p+08fS58,0jPGQ4P,0jPGPRPRPRp+09XS59Q1_Q1_Q1_#NQ47Q54PRPRQ4sp+0:8S1_Q54Q54#NJ0}M:lPRQ0LO1/AHQ50Q26p+03dS5:405Q3IQ45Q22Q1o405PzQ4HQ1hp+03hS22405Q3LQ49Q1VQ1p405PyQ4JQ1{Q1m405Q3UQ4=Q2M805rp+07?S1{p+08_S1VQ29805sQ3{Q14/7hPGQ0y/7iPGPRQ4oQ19Q1RP{p+092S26Q26Q4LG31hMKQ1J/7fPGQ1@Q0N'7PGPRp+09fS5;Q1?Q1yPjp+095S5<Q5<Q4MG31hKiQ1nQ0}'7PGQ1Y/7gPGPRp+09iS5=Q1FQ1DP]p+098S1DQ1Dp+07gS1FG3Q0N,hiQ16Q1['7PGQ1NQ0R'7PGPRp+09lS5>Q1tP0Q1Ep+09;S1tQ1tp+07jS5?G3Q0N/hgQ1KQ3r'7PGQ0|Q0x'7PGPRp+09oS5@p+03=Q2EQ1MQ4qQ4qp+07mS2EG3Q0R,hgQ1RQ0w'7PG17plPGPRp+0:2S5AQ1vp+03BQ0WQ4{Q4{Q4WG3Q0RQ0x'hQ19/7\PGQ1`Q0z'7PGPRp+0:5S1vQ1hQ1]Q0Zp+09DS1]Q1]Q43G3Q0x/hlQ1rQ0;'7PGQ14/7|R0PGPRQ1_PrQ1|Q17Q4]Q4]Q3sG3Q0z,hlQ1J/7|RrPGQ0|/7|PGQ1n/7|PGQ1u/7|PGQ16/7|PG17p|PGQ1K/7|PGQ10/7|PGQ1R/7|PGQ1`/7|PGQ19/7|PGQ1d/7|PGQ1r/7|PGP0PGQ1x/7|PGPrPGPRp+0:IS1hQ1JQ14Q1UQ59Q59p+08GG3Q07Q0q'hQ1^p+0:^Rr'Mp+09aS5Bp+09`S5C,9Xp+09bS5DQ0Bp+09]S5E'9Q4oPRp+0:MS5FQ12Q1^Q0@Q4|Q4|Q40G31hWIQ4z,4XP5Q0EQ5E'9Q5;Q0FQ5E'9p+09gS40Q5E,9OQ4yQ5E,9NQ5=Q5E,9SQ4nQ0GQ5E'9p+09kS5GQ5E,9>Q5>Q0HQ4y'9p+09mS5HQ2IQ2a$0QR0'4P5Q2K/40P5Q2y/40P5Q25/40P5p+04JS2y/40P5Q28/40P5Q1}/40P5Q1^Q0F'1PGQ1TQ0F'1PGQ1PQ0E'1PGQ18Q0E'1PGQ0mQ0D'1PGQ0lQ0D'1PGQ0iQ0C'1PGQ0hQ0C'1PGQ0dQ0B'1PGQ0cQ0B'1PGQ1B/1XPGQ1W/1XPGQ0jQ0A'1PGQ1=Q0A'1PGQ1:/1WPGQ0^/1WPGQ1`/1IPGQ10/1IPGQ1u/1IPGQ0|/1IPGQ1N/1IPGQ1>/1IPGQ0{/1IPGQ1@/1IPGQ0y/1IPGQ1a/1IPGQ12/1IPGQ1^/1IPGQ0p/1IPGQ1P/1IPGQ0n/1IPGQ0m/1IPGp+0:US10Q2TQ0@32PGQ2XQ3C$0Q'4P5Q0LQ2V'APGp+0:XS5IQ1S72WPGp+0:YS1SQ3772WPGp+0:RR0,0IPGp+0:[S5Jp+05bRp72IPGp+0:\S5K?2IpPGp+0:]Rs?2IpPGA2rIpPGp+0:_S5L?2IpPGp+0:`S5M?2IpPGp+0:aS5N?2IpPGQ0XQ1SPIp+07FS5OCzp+0:bS5P,@Jp+0:cS5QQ3J72WPGQ5K,0WPG10WsPG10WrPGQ5L,0WPGQ5M,0WPGQ5N,0WPGQ5P,0WPGp+04SS5R/1WPGp+04RS5S/1IPGQ2|Q0@'1PGQ2}Q0?'1PGp+04OS5TQ0s'1PGQ1}f`S5U'1PGQ2xQ0>'1PGQ28Q0<'1PGp+04[S5VQ0:'1PGp+04ZS5WQ09'1PGp+04YS5XQ08'1PGp+04XS5Y/1ePGp+04WS5ZQ3^'1PGp+04VS5[Q1;'1PGp+04US5\Q3['1PGp+04TS5]Q3Y'1PGQ4yQ11Q4yQ3ep+0;9Q02g01[U'yRrJ0DQ15eQ15Q2TQ2vQ2=Q0qp+0<4S5^DGPGQ2=Q2vQ2ZQ0qp+0<5DGPGQ2ZQ2vQ2aQ0qp+0<6RsDGPGQ2aQ2vp+04^S5_Q0qp+0<7DGPGQ5_Q2vp+04]S5`Q0qp+0<8DGPGQ5`Q2vQ1~Q0qp+0<9RpDGPGQ2YPmQ2|P\p+0<GS5aDGPGQ2XPmQ2|P\p+0<HS5bDGPGQ2WPmQ2|P\p+0<IS5cDGPGQ2VPmQ2|P\p+0<JS5dDGPGQ2UPmQ2|P\p+0<KS5eDGPGQ2SPmQ2|P\p+0<LS5fDGPGp+0<ES5g,41P5Q5g,48P5Q5g,47P5p+0<ZS5h/Q6p+0;LS5ip+0<[S5j/Q6p+0;MS5kp+0<\S5l/Q6p+0;NS5mp+0<]S5n/Q6p+0;OS5o143sP5p+0<RS5p,4BP5%NC1ACC14CpP5p+0<US5q,4DP5%N<1A<<p+0;]S5r,4<P514Q2P5Q2`#NQ2`Q2`'Ap+06<S5s@0EQVP0p+06=S5t@0EQVp+0:SS5up+06>RpQ0580EQp+0:TS5vp+0<FS5wp+0;\S5xp+0;RS5yQ2eCjQ1hp+0<kS5zQ2g'fP5Q2iQ5h'Mp+0;^S5{p+0;WS5|,0:PGPRPRPRQ5bQ2vQ2vPvQ5wp+0<aS5}p+0;=M:lPRQ2eO1/A:Q2gQ3j'0PGQ2iQ3l'0PGQ0tQ3n'0PGfCRsp+06:S5~'0PGfDS60Q5s'0PGfES61/0pPGQ2vQ3`'0PGQ2R/0=PGQ2Q/0uPGQ2A/0qPGQ2m/0pPGQ2GQ15'0PGp+05XS62Q3T'0PG10m=PGQ3b/0oPGp+05^S63Q3Y'0PGQ13Q3c'0PGQ3fQ1;'0PGQ3<Q3^'0PGQ15Q3g'0PGQ3>Q08'0PGQ3GQ09'0PGQ2q,0oPGQ2NQ0<'0PGQ3@Q0>'0PGQ1;Q2u'0PGQ3:Q0s'0PGQ3lQ0?'0PGQ08Q31'0PGQ3m/0IPGQ5s/0WPGQ0<p+06ZS2q'0PGQ5t/0XPGQ0B,0=PGQ0sp+06^S5t'0PGp+06CQ0D'0PGQ0Bp+0=@S3>'MQ5gQ0?p+0<>S3g'0PGPRPRPRp+0<oQ0FQ0FQ0sp+0<mS3<p+0=HS64p+0;dS65M:lPRQ0@O1Q0?'Ap+06[S66,0IPGp+06]S67,0WPGQ0AQ34'0PGp+06aS68,0XPGQ0Bp+06cS69'0PGQ0CQ3W'0PGQ0Dp+06gS6:'0PGQ0EQ3x'0PGQ0FQ3]'0PGp+05QS6;Q0r'0PGQ3W,0OPGp+05RS6<Q0M'0PGp+06?/0dPGQ0GQ3x'0PGQ3`Q0o'0PGp+06ES3`Q0q'0PGQ0Ip+06mS6='0PGQ3cQ1U'0PGp+06KRp/0|PGQ0rQ39'0PGQ2pQ0z'0PGQ2t/0\PGQ3A,0dPGQ2uQ0w'0PGp+06WS2pQ0x'0PGQ0qQ3H'0PGQ35Q0R'0PGQ67Q1['0PG10|yPGQ5tQ0}'0PGQ69Q0N'0PGQ3X,0\PGQ3z/0iPGQ3x/0hPGQ0xQ3y'0PGQ48/0nPGp+0=fS3y,MKp+0<lS3HQ3rp+0<eS3c'0PGPRPRPRp+0=VS6>P{P{Q0xp+0=5S6?P2PRPRp+0=US6@Q05P2%N2J0}M:lQ44Q1[Q1{'0PGp+07LS1{,0gPGQ0}p+07BS44'0PGQ0NQ3\'0PGQ5O,0fPGp+07HS6A,0iPGp+07JS6B,0hPGQ1{,0KPGp+07NS6C,0nPGQ4C,0MPGQ4D,0{PGQ52,0YPGQ3o,0LPGQ3MQ1G'0PGp+07MS6D,0^PGQ3@Q0`'0PGQ3kQ0S'0PGQ4I,0HPGQ3lQ0_'0PGp+06;S6EQ1M'0PGQ52,0xPGQ5sQ0T'0PGp+06AQ0U'0PGQ0Op+07XS6F'0PGQ0W,0=PGQ3eQ0u'0PGQ1EQ4I'0PGp+06IQ0Y'0PGQ3BQ0\'0PGQ1IQ3v'0PGQ3DQ0a'0PGQ3LQ1Q'0PGQ0XQ4M'0PGQ0e,0yPGQ44Q17'0PGQ0Vp+07hS44'0PGp+07CS3LQ1:'0PGQ6AQ1X'0PGQ2Op+07lS6A'0PGp+07IS3eQ0j'0PGQ6CQ0b'0PGQ0ZQ4W'0PGp+07OS6GQ1B'0PGQ52Q11'0PGQ0gp+084S6H'0PGQ4FQ0d'0PGQ3qQ0f'0PGQ0^Q4}'0PGp+07[S4}Q0i'0PGQ3vQ0~'0PGQ1=Q3w'0PGQ4LQ0m'0PGp+0=cS3wQ0lQ0e32PGQ1QQ0U'7PGQ0UQ0T'7PGQ0gQ0T'7PGQ0TQ0X'7PGQ0eQ0X'7PGQ0XQ1M'7PGQ17Q1M'7PGQ1MQ0_'7PGQ0^Q0_'7PGQ0_Q1I'7PGQ1:Q1I'7PGQ1IQ0S'7PGQ1XQ0S'7PGQ0SQ0`'7PGQ1=Q0`'7PGQ0`Q1E'7PGQ0jQ1E'7PGQ1EQ1G'7PGp+0>6S6IQ4pQ1G32PGQ0O/7^PG17^LPGQ1C/7LPG17LYPGQ1G/7YPG17Y{PGQ1E/7{PG17{MPGQ0`/7MPG17MnPGQ0S/7nPG17nKPGQ1I/7KPG17KhPGQ0_/7hPG17hiPGQ1M/7iPG17ifPGp+0>IS6JQ1y;2fPGQ0}Q07'7PGQ07Q0q'7PGQ0NQ0q'7PGQ0qQ0o'7PGQ0o,7fPGQ0o/7UPG17iUPG17UdPG17hdPGQ0M,7dPGQ0M,7KPGQ0M/7kPG17nkPGQ0r,7kPGQ0r,7MPGQ0rQ0k'7PGQ0k,7{PGQ0kQ0]'7PGQ0],7YPGQ0]Q0I'7PGQ0I,7LPGQ0IQ0H'7PGQ0H,7^PGQ0H/7>PG17Z>PGQ0G,7>PG11=SS6KPGQ6KPGQ3U/1SPG11ySPG11zSPGQ3I/1SPGQ3F/1SPGQ3D/1SPGQ3A/1SPGQ3?/1SPGQ3;/1SPGQ39/1SPGQ36/1SPGQ4>/1SPGQ4</1SPGQ3]/1SPGQ3x/1SPGQ3Z/1SPGQ32/1NS3FPGQ3FPGQ4C/1NPGQ6G/1NPGQ6D/1NPGQ1{/1NPGQ6B/1NPGQ3e/1NPGQ3_/1NPGQ5O/1NPGQ3\/1NPGQ3L/1NPGQ3X/1NPGQ3{/1NPGQ3U/1NPG11yNPG11zNPGQ3I/1NPGQ3O/1ORzPGPzPGPzPGPzPGPzPGPzPGPzPGPzPGQ4>/1ORzPGPzPGQ5?/1OPGQ4Q/1OPGQ1F/1OPGQ4O/1OPGQ4M/1OPGQ0Q/1OPGQ4L/1OPGQ3v/1OPGp+07^S3I/1OPGQ3t/1OPGQ4}/1OPGQ3q/1OPGQ6F/1OPGQ4G/1OPGQ4F/1OPGQ52/1OPGQ1V/1OPGQ4aQ0F'1PGQ4`Q0E'1PGQ4_Q0D'1PGQ4^Q0C'1PGQ4]Q0B'1PGQ4\/1XPGQ4[Q0A'1PGQ1]/1WPGQ53/1IPGQ4jQ0@'1PGQ4iQ0?'1PGQ4hQ0s'1PGQ4gQ5U'1PGQ4fQ0>'1PGQ4eQ0<'1PGQ4dQ0:'1PGQ4cQ09'1PGQ4Bp+05NS3Up+0?lS3{Q1HQ3UQ5XEPPGQ4NQ09'1PGQ4NQ08'1PGQ4N/1ePGQ4NQ3^'1PGQ4ZQ1;'1PGQ5DQ3['1PGQ5BQ3Y'1PGQ5C/1oPGp+09_S3[Q3V'1PGQ4kQ3T'1PGQ5EQ15'1PGQ4|Q3R'1PGp+09[S3R/1qPGQ4nQ3UQ2}PuQ2[DGPGQ5=Q3UQ2}PuQ2ADGPGQ4yQ3UQ2}PuQ2GDGPGQ40Q3UQ2}PuQ2\DGPGQ5;Q3UQ2}PuQ2]DGPGQ4tQ3UQ2}PuQ2^DGPGp+09dS2^Q3UQ2}PuQ2_DGPGp+0:1S2]p+05US2\Q29PpQ2_DGPGp+0:0S3^Q2\Q29PpQ2bDGPGQ5@Q2\Q29PpQ2cDGPGp+09nS3XQ2\Q29PpQ2dDGPGQ5HQ2\Q29PpQ2fDGPGQ5>Q2\Q29PpQ2hDGPGQ5GQ2\Q29PpQ2jDGPGQ1_p+05\S3\Q1jQ2uQ2jDGPGp+0:7S5OQ3\Q1jQ2uQ2kDGPGp+0:6S3_Q3\Q1jQ2up+057S3eDGPGQ1vQ3\Q1jQ2up+058S6BDGPGp+0:4S1{Q3\Q1jQ2up+059S3FDGPGp+0:3S6KQ3\Q1jQ2up+05:S6LDGPGQ5AQ3\Q1jQ2up+05;DGPGp+0@PS6M,Z1PGp+0AgS6N/Q8p+0@YS6O21778PG20NV8p+0@CS6P20i77p+0@\S6Qp+0AGS6Rp+0@]S6Sp+0@ZS6TP6Cjp+0?JS6Up+0AHS6Vp+0@^S6WQ6OPACjp+0?KS6Xp+0@GS6Y00V6p+0?XS6Z&0y3&26Ap+0AnS6[<253p+0AKS6\p+0@aS6]p+0@HS6^PACjp+0?NS6_p+0AoRp0013P@p+0;5S6`/4bP5Q4gP1Q6QQ1eP1p+05IS6aEPPGp+0AjS6b,Z1PG&0S8/11PGp+0B6S6c/Q7p+0@hS6dQ0500N1p+0@QS6e&248p+0@jS6fp+0AUS6gp+0@kS6hQ6dP7CjQ6Zp+0@TS6i00V7p+0?eS6jp+0@mS6k20NV1S6lp+0@VS6mp+0B<S6n0011P@Q5i/4bP5Q5CP1p+0@iS6op+041S6pP1p+05VS6qEPPGp+0A2S6rp+0BAS6s/f1P5p+0B8S6t,Z1PG20NV7Q6Sp+0A6S6u/y6Q6u?266p+0A7S6vp+0A8S6w?214W7Q6vPG]7p+0AbS6xQ6wp+0@oS6yP4CjQ6jp+0AcS6zp+0A9S6{Q6fP3Cjp+0?fS6|p+0BGS6}001AP@p+0;KS6~/4bP5p+08Bp+0A3S70;_Dp+0A<S71,@JQ70Q375_1p+0A=S37,@Jp+0A;S72,98p+0A>S73Q71p+0@5S745_8p+0A?S75,@JP6Q6uP8p+0=dS76Czp+0A@S77,@Jp+0AAS78Q5f727PGQ75p+0?OS79p+0A]S7:p+0@SS7;+0Bp+0BNS7<+1<+1;5_Ap+0ABS7=,@Jp+0A5S7>p+0@=S7?5_6p+0ACS7@,@JQ78,9Ap+0ADS7Ap+0AES7Bp+0@;S7C721PGQ6w,97p+0AFS7DQ6Rp+0@ARu721PGQ6Vp+0AIS7Ep+0AJS7FQ6lQ70p+0A4S7G00V1p+0@ES7Hp+0B7S7Ip+0AMS7JQ7FP7Cjp+0@:S7KQ6up+0;aS7L<057p+0?WS7Mp+0B\S7N0016P@p+0@IS7Op+0<1;26PGQ65&0Q8'4P5200VBA2@7VQ6\,08PGPup+0B>S7Pp+0ATS7Qp+0AOS7Rp+0@OS7SCjPuQ4JPup+0=DS7TPup+0=CPuQ1;PuQ58Pup+0=MS7UPuQ2PPuQ0?Pup+0=bS7VPuPWPuQ0APuP3Pup+0=oS7WPup+0>2S7XPuQ3CPuQ3NPuQ42PuI0@D6D6D6D6D6D6D6D6&0suP0P8Q5SP6Q5~DGPGQ0tp+0ASS3C;_Qp+0AVS7Y,@JQ7Q=_1Op+0AWS7Z,@JQ7Y,98p+0AXS7[Q7Y,97p+0AYS7\p+0APS7],96p+0AZS7^Q7Y=_6>p+0A[S7_,@Jp+0A\S7`p+0:HS7a726PGQ7:Q0t726PGp+0A^S7b?26=PGQ6g,9Bp+0A_S7cp+0AQS7dp+0@WS7e5_Ap+0A`S7f,@Jp+0AaS7gQ3`728PGQ7c,93Q6xQ7b,9BQ6zQ6\=_6kp+0AdS3`,@JQ7Y20x785_Dp+0AeS7h,@Jp+0AfS7iQ0q726PGQ6NQ07726PGQ7h,9Bp+0AhS7jQ3`,9Cp+0AiS7kQ7_=_4XQ6b,@Jp+0ARS7l20i785_<p+0AkS7m,@Jp+0AlS7n?26\PGp+0AmS7o?26lPGQ7n,9DQ6[Q6b,9<PpQ7g,9Qp+0B0S7pQ2`Q7o'9p+0B1S7qQ7k,9vp+0B2S7rQ7jQ6f5_Cp+0B3S7s,@Jp+0B4S7tQ5M724PGp+0B5R=Q0N724PGQ6cQ6k724PGQ7Ip+0=ARq724PGQ6tQ0k724PGQ60Q6b20wC33_p+0B9S7u,@JQ2eQ7g'9p+0B:S7vQ5b9_Bpp+0B;S7w,@JQ6oQ0}Q6op+0>JS7xQ6oPiQ6oPhQ6oQ0<Q6op+0>WS7yQ6op+0>ZS7zQ6oQ2sQ6oQ0IQ6oQ4uQ6oFoD6D6D6p+0=IS7{Q7vPrEcPBePBQ6fQ0NQ6fp+0>KS7|Q6fPhQ6fPKQ6fQ0>Q6fp+0>XS7}Q6fp+0>[S7~Q6fQ2tQ6fQ0]Q6fQ4{Q6fFoD6D6D6p+0=JS80Q6[PrEcP3eP3Q6hPfQ6hp+0>LS81Q6hPKQ6hPnQ6hQ5UQ6hp+0>YS82Q6hp+0>\S83Q6hQ2uQ6hQ0kQ6hp+09BS84Q6hFoD6D6D6p+0=KS85P=PrEcP4eP4Q60Q7tQ60Q7h'9016A3_p+0B?S86,@Jp+0B@S87?24YPGQ7P,9vQ6sp+0B=S88,9:p+0BBS89Q2eQ6s'9p+0BCS8:Q6sQ0N5_Cp+0BDS8;,@Jp+0BES8<?26xPGp+0BFS8=?26]PGPsQ7wP6Q7|CzQ6},@Jp+0BHS8>p+0;4S8?72APGQ8==_vhp+0BIS8@,@JQ87,9:p+0BJS8AQ87Q7D5_3p+0BKS8B,@Jp+0BLS8CQ4A728PGQ89,9Cp+0BMS8DQ7PQ7F5_7Q7<,@JP<Q8;P8p+0>ES8ECzp+0BOS8F,@Jp+0BPS8GQ6R727PGP4Q6sQ7I,94p+0CAS8HQ6j+0BCzp+0BQS8I,@JQ7<p+0<_S8J5_6p+0BRS8K,@JQ6},9Ap+0BSS8LQ8FQ7R5_8p+0BTS8M,@JP3Q8IP8p+0?9S8NCzp+0BUS8O,@Jp+0BVS8Pp+0<cS8Q727PGQ8C,9Ap+0BWS8RQ8>,96p+0BXS8SQ8P,9Ap+0BYS8TQ8P,94p+0BZS8UQ8P,93p+0B[S8VQ8U,9BQ7NQ8M,9Cp+0B]Q8M,9Dp+0B^S8WQ8M,9<p+0B_S8XQ8M,9Qp+0B`S8YQ2`Q8L'9p+0BaS8ZQ8L,9vp+0BbS8[Q8K,9:p+0BcS8\Q2eQ8K'9p+0BdS8]Q2gQ8K'9p+0BeS8^Q2iQ8K'9p+0BfS8_Q0tQ8K'9p+0BgS8`Q8K,9sp+0BhReQ60Q8K'9p+0BiS8aQ2RQ8^Q0tQ6_Czp+0BjS8b,@Jp+0BkS8cQ7i72sPGp+0BlS8dQ7j72sPGp+0BmS8eQ0e72sPGp+0Bnp+0=;S8f72sPGp+0BoQ6b72sPGp+0C0S8gQ5x72sPGp+0C1Q0Y72sPGp+0C2Q3o72sPGp+0C3S8hQ6[72sPGp+0C4Rz?2sqPGp+0C5Rq?2spPGp+0C6S8iQ0g72sPGp+0C7Rpp+0>7S8j72sPGp+0C8RyQ8j72sPGp+0C9S8kQ8j72sPGp+0C:S8lQ8j72sPGp+0C;S8mQ8j72sPGp+0C<S8nQ8j72sPGp+0C=S8oQ8j72sPG1181PG1161PG1141PG11B1PG11D1PG11Q1PG11v1PGQ2e/11PGQ2i/11PG11s1PGQ61/11PGQ2R/11PGQ2m/11PGQ3N/11PGQ3P/11PGQ13/11PGp+0CNQ6lPpp+0>3S6lp+0=mS8pP8Q7yp+0>VS8qp+0>US8rp+0>TS8sp+0>SS8tp+0>RS8up+0>QS8vQ17Q4vP9Q1@Q12N?23p+0CPS8wQ8w[p+0>4S8xp+0=]S8y<068p+0CQS8zQ8z[Q8lQ8p<057Q7_p+0D`S8z0016P@p+0=_S8{p+0>MS8|6067p+0CTS8}Q8}[p+0>8S8}p+0=aS8~60>4Q8}00P6p+0>1S90&0Q7'4P5200VCA2@6VQ7Vp+0>PS916066p+0CXS92Q92[Q8uQ7680>B20PBAp+0>=S93Q6zQ1SQ6zQ5IQ6zp+0:WS94Q6zp+0:VS95Q6zQ10Q6zQ5vQ6zQ5uQ6zPBQ6zI0@D6D6D6+15p+0CZS96Q96[p+0CS,0APGp+0>?S97Q7hQ1BQ7hQ5JQ7hp+0:ZS98Q7hQ1SQ7hQ5IQ7hQ94Q7hQ95Q7hQ10Q7hPDQ7hFoD6D6D6+15p+0C\S99Q99[Q7ip+0CES9:Q8pQ4p405Q7iQ9:p+0>9S9;Q14405Q7iQ9:p+0=nS9<Q6k405Q7iQ9:Q7WQ1O405Q7iQ11Q7iQ5KQ7iQ5JQ7iQ98Q7iQ1SQ7iQ5IQ7iQ94Q7iQ95Q7iP<Q7iFoD6D6D6D6D6Q7i$0sp+0=gS9:Q8r6064p+0C^S9=Q9=[Q7yp+0=iS9>80><20P<3p+0=:PAp+0=9PDp+0DXS9?DGPGQ8fP4p+0<jS8fP<p+0DfS9@DGPGp+0=<P3Q4QPQp+08IS9ADGPGp+0==S9BPBQ3LQ2`Q9ADGPGp+0=>S3LPCQ3OPvQ9ADGPGQ8pQ7~6063p+0CeS9AQ9A[p+0>]S9CQ7W80>v20PvBQ03,13S9DPGQ9DPGQ9DPGQ9DPGQ9DPGQ6lp+0>aS9D6063p+0ClS9EQ9E[p+0>cS9Fp+0>5S9G80>:20P:BS9HQ4J/13PGQ42/13PGQ1\/13PG11t3PGQ1j/13PGQ9;p+0>gS1\6063p+0D3S9IQ9I[p+0>iS9Jp+0>;S9K80>:Q9HQ4N/13PGQ4?/13PGQ27/13PGp+03Z/13PGQ20/13PGQ97p+0>mS206063p+0D:S9LQ9L[p+0>oS9Mp+0>AS9N80>:Q9Hp+08mS9H/13PGQ53/13PGQ22/13PGQ1e/13PGQ1k/13PGQ8EQ1r6063p+0DAS1kQ1k[Q4Y/14PGQ4V/14PGp+0?7S9OQ2gQ6J40>Q2g00PDS9PQ29/13PGQ1p/13PGQ5:/13PGQ7|p+03]6063p+0DHS9QQ9Q[Q4r/13PGQ4m/13PGQ2>/14PGQ6p/14PGQ1OQ0tQ8v40>Q0t00PQQ1m/13PGQ8vQ7c6063p+0DOS9RQ9R[Q2C/1APGQ2>/1APGQ1gQ2gQ8r40>Q9PQ1q/1APGQ9DQ24606Ap+0DTS24Q24[Q7hQ2`Q7y40>Q2`00P4Q2</17PGQ7}>067tp+0DWS7yQ7y[Q1H/18PGp+03eS1H/11PGQ5[/11PGPTQ0^Q92P6p+0?:S9PD<Q2~p+0D\S2~PTp+0;cS9SQ24P1Q8cQ15p+0?<S9TP8GeW7Q2~PG]7p+0D]S9UPTPtQ24P1Q8cQ3Tp+0?=S3TP7GeW7Q9UPG]7p+0D^S9Vp+0?jS9WQ2032p+0D_S9XQ9WQ4z32Q8zQ9WQ1f32p+0DaS9YQ9WQ1b32p+0DbS9ZQ9W;2lp+0CbS9[p+0?@Rt'0p+0?AS9\p+0EmS9]'0Q7rQ7qQ7qQ7pPPPcP}PwP_Q7sP;Q6[CJP~PEb4b5b6X05p+0CgS9^/01p+0EjS9_,58S9`#XS9a[^05P1p+0?ES9bPAO2b1b2b3Q7rQ7qQ7qQ7pPPPcP}PwP_p+0DLS9cP;Q7oCJP~PEb4b5b6X05p+0F1S9d,01Q9`Q9Y'Z[^05P1Q9bP6O2b1b2b35]tQ7U/AtQ7sQ7rQ7rQ7qPPPcP}PwP_Q7tP;Q7mCJP~PEb4b5b6X05p+0ChS9e/01p+0EaS9f,58S9g#X[^05P1p+0?FS9hP4O2b1b2b3Q7sQ7rQ7rQ7qPPPcP}PwP_p+0DMS9iP;Q6bCJP~PEb4b5b6X05p+0F2S9j,01Q9gQ9Z'Z[^05P1Q9hPAO2b1b2b35]tp+0=LS9g/AtQ7tQ7sQ7sQ7rPPPcP}PwP_P=P;Q7jCJP~PEb4b5b6X05p+0CiS9k/01p+0EhS9l,58S9m#X[^05P1p+0?GS9nP3O2b1b2b3Q7tQ7sQ7sQ7rPPPcP}PwP_p+0DNS9oP;Q6NCJP~PEb4b5b6X05p+0F3S9p,01Q9mp+0DcS9q'Z[^05P1Q9nP4O2b1b2b35]tQ85/AtP=Q7tQ7tQ7sPPPcP}PwP_Q6cP;Q7hCJP~PEb4b5b6X05p+0CjS9m/01p+0EbS9r,58S9s#X[^05P1p+0?HS9tPBO2b1b2b3P=Q7tQ7tQ7sPPPcP}PwP_Q9RP;Q3`CJP~PEb4b5b6X05p+0F4S9u,01Q9sp+0DdS9v'Z[^05P1Q9tP3O2b1b2b35]tQ80/AtQ6cP=P=Q7tPPPcP}PwP_Q7IP;Q6xCJP~PEb4b5b6X05p+0CkS9s/01p+0EiR3,58S9w#X[^05P1p+0?IS9xPCO2b1b2b3Q6cP=P=Q7tPPPcP}PwP_p+0DPS9yP;Q7gCJP~PEb4b5b6X05p+0F5S9z,01Q9wp+0DeS9{'Z[^05P1Q9xPBO2b1b2b35]tQ7{/AtQ7IQ6cQ6cP=PPPcP}PwP_Q6tP;Q7cCJP~PEb4b5b6X05Q9E/01p+0EcS9E,58RB#X[^05P1Q6UPDO2b1b2b3Q7IQ6cQ6cP=PPPcP}PwP_p+0DQS9wP;Q7bCJP~PEb4b5b6X05p+0F6S9|,01Q9@,ZB[^05P1Q6UPCO2b1b2b35]tQ64/AtQ6tQ7IQ7IQ6cPPPcP}PwP_Q7uP;Q7_CJP~PEb4b5b6X05p+0CmS9}/01Q9a[^05P1Q6XP<O2b1b2b3Q6tQ7IQ7IQ6cPPPcP}PwP_p+0DRS9aP;Q7^CJP~PEb4b5b6X05p+0F7S7^,01Q9`p+0DgS9~'Z[^05P1Q6XPDO2b1b2b35]tp+0=GS9`/AtQ7uQ6tQ6tQ7IPPPcP}PwP_Q7vP;Q7[CJP~PEb4b5b6X05p+0CnS:0/01Q9p,58RD#XRC[^05P1p+0?LS:1PQO2b1b2b3Q7uQ6tQ6tQ7IPPPcP}PwP_p+0DSS:2P;Q7ZCJP~PEb4b5b6X05p+0F8S:3,01p+0DhS:4,ZD[^05P1Q:1P<O2b1b2b35]tp+0=F/AtQ7vQ7uQ7uQ6tPPPcP}PwP_Q7wP;Q7ECJP~PEb4b5b6X05p+0CoS:5/01p+0EeS:6,58R<#XRB[^05P1p+0?MS:7Q2`O2b1b2b3Q7vQ7uQ7uQ6tPPPcP}PwP_Q24P;Q6VCJP~PEb4b5b6X05p+0F9S:8,01p+0DiS:9,Z<[^05P1Q:7PQO2b1b2b35]tp+0<MS::/AtQ7wQ7vQ7vQ7uPPPcP}PwP_Q6nP;Q75CJP~PEb4b5b6X05p+0D0S75/01PB[^05P1Q6_PvO2b1b2b3Q7wQ7vQ7vQ7uPPPcP}PwP_p+0DUS:;P;Q73CJP~PEb4b5b6X05p+0F:S:<,01p+0DjS:=,Z<[^05P1Q6_Q2`O2b1b2b35]tQ5c/AtQ6nQ7wQ7wQ7vPPPcP}PwP_Q88P;Q71CJP~PEb4b5b6X05p+0D1S2`/01p+0ElR<,58RB#X[^05P1Q79P:O2b1b2b3Q6nQ7wQ7wQ7vPPPcP}PwP_p+0DVS:>P;Q72CJP~PEb4b5b6X05p+0F;S:?,01p+0DkS:@,ZB[^05P1Q79PvO2b1b2b35]tQ5b/AtQ:1Q88Q6nQ6nQ7wPPPcP}PwP_Q7PP;Q6wCJP~PEb4b5b6X05p+0D2Rv/01PC[^05P1p+0?PS:AQ2eO2b1b2b3Q88Q6nQ6nQ7wPPPcP}PwP_Q7yP;Q6vCJP~PEb4b5b6X05p+0F<S:B,01p+0DlS:C,ZD[^05P1Q:AP:O2b1b2b33]Q5wQ:1'AQ9\Q7PQ88Q88Q6nPPPcP}PwP_Q86P;Q7>CJP~PEb4b5b6X05Q9I/01p+0EgS:D,58R:#X[^05P1p+0?QS:EQ2gO2b1b2b3Q7PQ88Q88Q6nPPPcP}PwP_Q9?P;Q7GCJP~PEb4b5b6X05p+0F=RD,01p+0DmS:F,Z:[^05P1Q:EQ2eO2b1b2b33]Q5gQ9\'AQ86Q7PQ7PQ88Q7HQ7uP1p+0?RS2eQ2iO2b1b2b3Q86Q7PQ7PQ88p+0@DS:Gp+0C]S:HP1Q2eQ2gO2b1b2b35]tp+0:KS2gQ9\Q87Q86Q86Q7Pp+0@FS:IQ7vP1p+0?SS7vQ0tO2b1b2b3Q87Q86Q86Q7PQ7HQ9=P1Q7vQ2iO2b1b2b33]p+0:Lp+0?BS2iQ6sQ87Q87Q86Q6YQ7wP1p+0?TS:JPsO2b1b2b3Q6sQ87Q87Q86Q:Ip+0C_S:KP1Q:JQ0tO2b1b2b33]Q5Fp+0?CS0tQ89Q6sQ6sQ87Q6^Q6nP1p+0?US:LQ60O2b1b2b3Q89Q6sQ6sQ87Q6Yp+0C`S:MP1Q:LPsO2b1b2b33]p+0:NS:Np+0?DS:OQ8:Q89Q89Q6sQ7OQ88P1p+0?VS:PQ61O2b1b2b3Q8:Q89Q89Q6sQ6^p+0CaS:QP1Q:PQ60O2b1b2b33]p+0:OS60Q9bQ8;Q8:Q8:Q89p+0@JS:RQ7PP1Q7MQ2vO2b1b2b3Q8;Q8:Q8:Q89Q7OQ9[P1Q7MQ61O2b1b2b33]p+0:PS61Q9hQ8<Q8;Q8;Q8:p+0@KS:SQ86P1Q6ZQ2RO2b1b2b3Q8<Q8;Q8;Q8:Q:Rp+0CcS:TP1Q6ZQ2vO2b1b2b33]p+0:QS2vQ9nQ8=Q8<Q8<Q8;p+0@LS:UQ87P1p+0?YS:VQ2QO2b1b2b3Q8=Q8<Q8<Q8;Q:Sp+0CdS:WP1Q:VQ2RO2b1b2b33]P0Q9tQ6}Q8=Q8=Q8<p+0@MS:XQ6sP1p+0?ZS:YQ2mO2b1b2b3Q6}Q8=Q8=Q8<Q:UQ9AP1Q:YQ2QO2b1b2b33]Q5uQ9xQ8>Q6}Q6}Q8=p+0@NS:ZQ89P1p+0?[S:[Q2PO2b1b2b3Q8>Q6}Q6}Q8=Q:Xp+0CfS:\P1Q:[Q2mO2b1b2b33]Q5vQ6UQ8@Q8>Q8>Q6}Q7SQ8:P1p+0?\S:]Q3NO2b1b2b3Q8@Q8>Q8>Q6}Q:ZQ9^P1Q:]Q2PO2b1b2b33]Q10Q6XQ8AQ8@Q8@Q8>Q6MQ8;P1p+0?]S:^PmO2b1b2b3Q8AQ8@Q8@Q8>Q7SQ9eP1Q:^Q3NO2b1b2b33]Q95Q:1Q8BQ8AQ8AQ8@Q6eQ8<P1p+0?^S:_Q3PO2b1b2b3Q8BQ8AQ8AQ8@Q6MQ9kP1Q:_PmO2b1b2b33]Q94PFp+0?bS:`p+0=kS:ap+0FGS:bH22$0lQ:bQ4y'0Q5=Q:bp+0FFS:c3OQ6jQ4nQ5VQ5VQ2xQ1pQ1iK21Q01Q6|Q5GQ1~Q1~Q1}Q1lQ1pp+0?gS01Q1p+1LQ1}Q1~Q2Jp+0EHS:d,@JRsQ01PTP1p+0DFS:eQ0Tp+0?hS:fD<+0gp+0EIS:gP1p+0E9S:hp+0DES:iH12Q:gp+0EFS:j,91S:kQ2|Q:gp+0EES:l,91R:Q:PQ:gp+0EDS:m,91RCp+0DDS:nQ:gp+0EGS:o,91RBQ9GQ:gp+0E@S:p,91RQQ2zQ:gp+0E?S:q,91S:rQ5HQ:gp+0E>S:s,91S:tQ:nQ:gp+0E=S:u,91S:vQ:PQ:gP1p+0E;S:wp+0DCS:xQ:gP1p+0E:S:yQ2zQ:gP1p+0E8S2zQ7OQ:gP1p+0E7S:zQ6^Q:gP1p+0E6S:{Q6YQ:gP1p+0E5S:|Q:IQ:gP1p+0E4S:}Q7HQ:gP1p+0E3S:~Q:GQ:gP1p+0E2S;0Q6PH12DxDxDxDxDxDxDxDxFwFwFwFw41JXAs+11[[[[P1Q1kQ3[Q5X32p+0DBS;1Q3[Q5W32Q:xQ3[Q1}32Q:np+0?nS;2p+0FYS;3Q6Kp+0FJS;440fPVQ:~Q2o-0NVRs+0VI0=Q:ip+0?oS;5p+0FZS;6Q1{p+0FES;740fPVQ:}00VsI0=p+0@0S;8Q2o+1LQ00Q;2Q2MQ5YQ2WQ2xp+0ERS00,@JRsp+0@1S;9PTP1Q9yQ1Qp+0@2S;:D<+0gp+0ESS;;p+0ECS;<,91S;=Q9R32Q;;P1p+0EPS;>Q5VQ;;P1p+0EOS;?p+0?`S;@Q;;p+0ENS;A,91S;BQ9oQ;;p+0EQS;C,91Q97Q;;P1p+0EJS;DQ2|Q;;Q:g,91S;EQ5OQ;;Q:d,91S;FQ9oQ;;PBQ;@Q;;P:Q9iQ;;PCQ2|Q;;p+0EBS;G,91S;HQ7;Q;;p+0EAS;I,91S;Jp+0@RS;KQ;;PQQ6eQ;;Q:rQ6MQ;;Q:tQ7SQ;;Q:vQ:ZQ;;P1p+0E<S:vQ:XH12H1~FwFwFwFwFwDxFwDxDx41JXAs+11[[[P1Q;8Q6pQ5VQ2[Q2}Q5R$1}Q5SQ5Sp+0EMS5Y3pp+0EVS2W,@JS:tQ:tQ74PTP1Q24PSp+0@6S:rD<+0gp+0EWRsPBQ:2Psp+0ETS;L,91Q2aPsP1Q;;p+0?dRBPsP1Q00Q9aPsP1p+0EUS;Mp+0>CS;NPsQ;BQ5\PsQ5Y,91Q57PsP1p+0ELS;BQ9aPsP1p+0EKS;OPBPsQ;EQ9wPsQ;FQ5\PsQ:kQ7ePsP:Q6mPsPCp+0@US:kPsQ;=Q6iPsQ;HQ7;PsQ;JQ;KQ6e92sQFwFwFwFwDxDxFwDxDxDxFwS;J'1WAQ1Op+0@4RQQ0D+0gQ1uQ1X'1PQPTQ021@JsQ;LQ:v60;Jp+0@cS1OQ6^n0100000020000Q8^p+0@9S;HQ74D<Q0DQ77PTPFQ1OQ24Q;HQ74g01b<RCQ;LQ;Lp+0DKS;=g01cF&03Cg01dPN=0OQ:wQ;7P1p+0FeS;Fp+0DJS;EQ8_Q;7#NS;PQ;FQ;EQ;FQ8_CLdO4b9Q2Wp+0FdS;Qp+0FDS;RP?Q;QQ;R'TdQ8^DWPsQ;EPTQ:RP1Q7Cp+0@7S;SQ0FEKX7sPsQ6|PTp+0@eS;TQ2WP1Q:vCzQ;=Q7CQ;SQ0FEKX7sPQp+0EXRCp+0>DS;Up+0FfS;VQ:v,41S;W'Q32X:5Q;FQ:w80fQ,ysQ;FQ6|'fPQQ8]Q8\Q8\Q8[PPPcP}PwP_Q8^P;Q:bCJP~PEb4b5b6X05p+0DYS;X/01Q0[[^05P1Q;SQ0AO2b1b2b3Q8]Q8\Q8\Q8[PPPcP}PwP_Q:sP;Q;=CJP~PEb4b5b6X05p+0FcS;Y,01Q;;,Z8[^05P1Q;SPWO2b1b2b3K0KQ5leQ5lPCQ;UPTp+0@fS;ZPsP1Q9cp+0@<S;[p+0@8S;\POGeX7CPTp+0<^S;]Q;=Q7CQ;SD<PTQ;]Q8YQ0^Q;SD<Q0FQ7=PTPFQ;]Q;=Q7CQ;Sg01eZQ2WQ00Q:ePBQ1=g01fdPrg01gnQ5Fp+0;0S;^p+0EYS;_Q8EQ;_p+0EZS;`P1Q;4Q9QQ6|I0FW7Q01Q;`p+0FhS;aP1p+0FMS;bQ6|I0JX:5Q;_Q:iQ:iQ01p+0FLS;cPQQ8YQ8_Q8^Q8^Q8]PPPcP}PwP_Q8]Q:sQ9QH0<P~PEb4b5b6X05Q;M,51S;dp+0FOS;ep+0F]S;f,51S;g407^05P1Q;HO1S;hb1b2b3L0?Q5lQ3YDDQ;_Q8EQ;cQ6jC|ep+0;gS;iP1E=b;Q:iQ5lQ:iQ;TQ00PrJ0Dp+0:oS;jeQ;jQ;_Q6]Q;_Q;`Q0b721W7Q0Ap+0;fS;kP1E=b;Q7CQ;UPBp+0F`S;lPVQ6|p+0D@S;mQ5hp+0<YS;nQ65Q8^Q8]Q8]Q8\Q6dQ;mP1Q;\Q0AO2b1b2b3Q5jQ3VG^p+0:nS;oeQ2QQ6|Q9N,01X:5p+0@3S2QQ01/01X:5Q8^Q8]Q8]Q8\PPPcP}PwQ8\p+0DGS;p5>_P~PEb4b5b6X05Q;L,51S;qp+0F\S;r,51S;s'0^05P1Q;\O1R:b1b2b3p+0>@S;tQ0?DDQ5jQ3VDDQ5jQ;t'0eQ2Qp+0F?S;uQ655O1X:5Q6|Q:VQ:z80:1X:5Q6Zp+0>BS;v'0Q7MQ9N'0PRp+0FAS;wQ6ZQ7MQ97Q;vQ9Np+0<XS;xG3Q8^Q8]Q8]Q8\PPPcP}PwQ8XQ7A5>_P~PEb4b5b6X05Q;sQ;rQ;qQ;LC}^05P:b1b2b3Q5jQ3VG^Q;tQ0?DDQ;tp+0F>S3VQ9S3OeN902NB08Q:uQ:bP1p+0FgS;qp+0D>S8XQ8ZQ3V#NS;yQ;qQ8XQ;qQ8ZCLdO4b9PCQ;VPDP?Q;V/TDdQ8YDWQ;_Q8XQ;_PTp+0<`S;zP1Q1XQ;HPNEKW7PTQ8JQ8XQ1:Q;\D<PTQ8JQ8UQ0eQ;\D<POQ7@PTPFQ8JQ8XQ1:Q;\g01i8PsQ;>p+0D=S;{PBp+0@`S;|g01jBPrg01kLQ:Np+0;1S;}Q;`p+0>FS;~Q;`p+0E[S<0P1p+0FKS<1p+0D?S<2Q6|I0FW7Q:fQ<0p+0FiR:P1p+0FTS<3Q6|I0JX:5Q;`Q:eQ:eQ:fp+0FSS<4PQQ8ZQ8`Q8_Q8_Q8^PPPcP}PwP_Q8^Q:wQ;1H0<P~PEb4b5b6X05Q2W,51S<5p+0FVS<6Q<3,51S<7407^05P1Q7KO1S<8b1b2b3L0?Q5nPoDDQ;`Q;~Q<4Q6jC|ep+0;hS<9P1E=b;Q:eQ5nQ:eQ;ZQ;>PrJ0DQ;oeQ;oQ;`Q6]Q;`Q<0p+0@bS<:721W7Q;`Q6]Q65P1Fdb;PVQ;[Q1:PBQ0gQ;[Q8EPBp+0FaS<;PVQ01Q1kQ5jQ5hp+0;eS<<Q8_Q8^Q8^Q8]Q6oQ1kP1Q;HPXO2b1b2b3Q5lQ3YG^Q;jeQ2mQ01Q;t,01X:5Q2QQ:f/01X:5Q8_Q8^Q8^Q8]PPPcP}PwQ8]Q1k5>_P~PEb4b5b6X05Q;dQ<4,51S1k'0^05Q;hb1b2b3Q97Q0?DDQ5lQ3YDDQ5lQ97'0eQ2Qp+0F@RXQ<<5O1X:5Q01Q7MQ2z80:1X:5Q:PQ;N'0Q:LQ;v'0PRp+0FBS2mQ:PQ:Lp+0>>S;jQ;NQ;vQ;nG3Q8_Q8^Q8^Q8]PPPcP}PwQ7NQ7B5>_P~PEb4b5b6X05Q1kQ;fQ;dQ;MC}^05Q;hb1b2b3Q5lQ3YG^Q97Q0?DDQ97Q;uQ653OeN902E;NB08Q:sp+0FHS3YP1Q;ap+0D<S;hQ8VQ;yQ;aQ;hQ;aQ8VCLdO4b9Q;_Q;qPDP?Q;q/TDdQ8UDWQ;`Q;hQ;`PTQ5}P1Q0^Q7KPSEKW7PTQ;zQ;hQ17Q;HD<PTQ;zQ8RQ0aQ;HD<PNQ7APTPFQ;zQ;hQ17Q;Hg01lVPCQ;>p+0D;S;dPBQ;|g01m`Prg01njQ60p+0;2S1kQ<0p+0>GS<=Q<0p+0E\S<>P1Q;cQ;{Q6|I0FW7p+0?iS<?Q<>p+0FjS<@p+0F[S<A,41S<BQ6|H0qX:5Q<0Q;pQ;pQ<?Q;6PQQ8[PeQ8`Q8`Q8_PPPcP}PwP_Q8_Q:yQ;mH0<P~PEb4b5b6X05151sS<CQ;fQ<A,51S<D407^05P1Q7CO1S<Eb1b2b3L0?Q;]PoDDQ<0Q<=Q;6Q6jC|ep+0;iS<FP1E=b;Q;pQ;]Q;pp+0@gS<GQ;>PrJ0DQ;oeQ;oQ<0Q6]Q<0Q<>Q<:721W7Q<0Q6]Q65P1Fdb;PVQ1XQ17PBQ0ZPVQ7?Q1XPBQ0eQ7?Q;~PBp+0FbS<HPVQ:fQ;1Q5lQ5jQ;kQ8`Q8_Q8_Q8^Q6fQ;1P1Q7KQ0BO2b1b2b3Q5nPoG^Q;^eQ2PQ:fQ97,01X:5Q2QQ<?/01X:5Q8`Q8_Q8_Q8^PPPcP}PwQ8^Q<25>_P~PEb4b5b6X05Q<5Q;6,51S2P'0^05Q<8b1b2b3Q;jQ0?DDQ5nPoDDQ5nQ;j'0eQ2QQ;wQ;k5O1X:5Q:fQ:LQ:h80:1X:5Q:JQ;U'0Q7vQ;N'0PRp+0FCS<IQ:JQ7vQ93Q;UQ;NQ5hG3Q8`Q8_Q8_Q8^PPPcP}PwQ8TQ7D5>_P~PEb4b5b6X05Q2Pp+0F^Q<5Q2WC}^05Q<8b1b2b3Q5nPoG^Q;jQ0?DDQ;jQ<<7OXeN902E;E;NB08Q:qp+0FIS<8P1P:Q9LQ8SQ;yP:Q9LP:Q8SCLdO4b9Q;`Q;aPDP?Q;a/TDdQ8RDWQ<0Q9LQ<0PTp+0<bS<5P1Q0gQ7CQ0GEKW7PTQ5}Q9LQ1QQ7KD<PTQ5}Q8MQ0uQ7KD<PSQ7BPTPFQ5}Q9LQ1QQ7Kg0204Q;_Q;>p+0D9S2PPBQ;|g021>Prg022HQ61p+0;3S<JQ<>p+0>HS<KQ<>p+0E]S<LP1Q;bQ;dQ6|I0FW7Q9WQ<Lp+0FkS<MQ;e,41S<NQ6|H0qX:5Q<>Q9QQ9QQ9Wp+0FNS<OPQQ8\Q8aPePeQ8`PPPcP}PwP_Q8`Q:hQ8XH0<P~PEb4b5b6X05151CS8Xp+0FQS<Pp+0FUS<Q,51S<R407^05P1Q;[O1S<Sb1b2b3L0?Q8JPoDDQ<>Q<KQ<OQ6jC|ep+0;jS<TP1E=b;Q9QQ8JQ9QQ6dQ;>PrJ0DQ;oeQ;oQ<>Q6]Q<>Q<LQ<:721W7Q<>Q6]Q65P1Fdb;PVQ0^Q1QPBQ0WPVQ1=Q0^PBQ0aPVp+0@>S<UQ1=PBQ17Q<UQ<=PBQ;YPVQ<?Q:xQ5nQ5lQ;iPeQ8`Q8`Q8_Q6hQ:xP1Q7CQ0CO2b1b2b3Q;]PoG^Q;}eQ3NQ<?Q;j,01X:5Q2QQ9W/01X:5PeQ8`Q8`Q8_PPPcP}PwQ8_Q;{5>_P~PEb4b5b6X05Q<CQ<7'0^05Q<Eb1b2b3Q93Q0?DDQ;]PoDDQ;]Q93'0eQ2QQ2mQ;i5O1X:5Q<?Q7vQ:y80:1X:5Q2eQ8E'0Q:EQ;U'0PRQ;RQ2eQ:Ep+0><S3NQ8EQ;UQ5jG3PeQ8`Q8`Q8_PPPcP}PwQ8PQ6R5>_P~PEb4b5b6X05Q<7p+0F_S<7Q<CPsC}^05Q<Eb1b2b3Q;]PoG^Q93Q0?DDQ93Q;wQ;k3OeN902E;E;E;NB08Q:pQ;4P1Q<@p+0D8S;4Q8OQ;yQ<@Q;4Q<@Q8OCLdO4b9Q<0P:PDP?1T:DdQ8MDWQ<>Q;4Q<>PTQ8QP1Q0YQ;[P>EKW7PTQ<5Q;4Q2OQ7CD<PTQ<5Q8IQ1MQ7CD<Q0GQ7DPTPFQ<5Q;4Q2OQ7Cg023RQ;`Q;>p+0D7S;kPBQ;|g024\Prg025fQ2vQ8?Q<LQ6JQ<Lp+0E^S2vP1Q<OQ2PQ6|I0FW7p+0?kS<EQ2vp+0FlS<CP1p+0FRS;}Q6|I0JX:5Q<Lp+0DIS0CQ0CQ<EQ<PPQQ8]Q8bQ8aQ8aPePPPcP}PwP_PeQ2zQ;hH0<P~PEb4b5b6X05Q;_,51S8]Q<3Q;s407^05P1Q7?O1S<Vb1b2b3L0?Q;zPoDDQ<LQ6JQ<PQ6jC|ep+0;kS<WP1E=b;Q0CQ;zQ0CQ6oQ;>PrJ0DQ;oeQ;oQ<LQ6]Q<LQ2vQ<:721W7Q<LQ6]Q65P1Fdb;PVQ0gQ2OPBQ0_PVQ1:Q0gPBQ0uPVQ0jQ1:PBQ1QPVp+0@?S<XQ0jPBQ0^Q<XQ<KPBQ;QPVQ9WQ:nQ;]Q5nQ<9Q8aPePeQ8`p+0@lS<YQ:nP1Q;[Q0DO2b1b2b3Q8JPoG^Q1kePmQ9WQ93,01X:5Q2QQ<E/01X:5Q8aPePeQ8`PPPcP}PwQ8`Q;d5>_P~PEb4b5b6X05Q8XQ<D'0^05Q<Sb1b2b3Q3NQ0?DDQ8JPoDDQ8JQ3N'0eQ2QQ<IQ<95O1X:5Q9WQ:EQ:w80:1X:5Q:AQ;~'0Q79Q8E'0PRQ;7Q:AQ79Q9KQ;~Q8EQ5lG3Q8aPePeQ8`PPPcP}PwQ8LQ6V5>_P~PEb4b5b6X05Q<DQ;lQ8XPCC}^05Q<Sb1b2b3Q8JPoG^Q3NQ0?DDQ3NQ2mQ;i3OeN902E;E;E;E;NB08Q;IQ<1P1Q<Mp+0D6S;iQ8KQ;yQ<MQ;iQ<MQ8KCLdO4b9Q<>Q<@PDP?Q<@/TDdQ8IDWQ<LQ;iQ<LPTp+0<dS<SP1Q0TQ7?Q0HEKW7PTQ8QQ;iQ0XQ;[D<PTQ8QQ7<Q1GQ;[D<P>Q6RPTPFQ8QQ;iQ0XQ;[g0270Q<0Q;>p+0D5S8XPBQ;|g028:Prg029DP0Q6`Q2vQ7xQ2vp+0E_S<DP1Q;eQ;kQ6|I0FW7Q3{Q<Dp+0FmS;dP1Q<HQ6|I0JX:5Q2vQ;EQ;EQ3{Q<;PQQ8^Q8cQ8bQ8bQ8aPPPcP}PwP_Q8aQ:zQ9LH0<P~PEb4b5b6X05Q;`,51S9LQ;QQ<6,51407^05P1Q<UO1S1kb1b2b3L0?Q5}PoDDQ2vQ7xQ<;Q6jC|ep+0;lP1E=b;Q;EQ5}Q;EQ6fQ;>PrJ0DQ;oeQ;oQ2vQ6]Q2vQ<DQ<:721W7Q2vQ6]Q65P1Fdb;PVQ0YQ0XPBQ1CPVQ0eQ0YPBQ1MPVQ1XQ0ePBQ2OPVQ0bQ1XPBQ0gPVp+0@@RmQ0bPBQ1:PmQ6JPBQ;FPVQ<EQ:iQ8JQ;]Q<FQ8bQ8aQ8aPeQ6kQ:iP1Q7?Q0EO2b1b2b3Q;zPoG^Q<JeQ3PQ<EQ3N,01X:5Q2QQ3{/01X:5Q8bQ8aQ8aPePPPcP}PwQ2P9>_eP~PEb4b5b6X05Q8]Q<R'0^05Q<Vb1b2b3Q9KQ0?DDQ;zPoDDQ;zQ9K'0eQ2QQ;RQ<F5O1X:5Q<EQ79Q;W'0X:5Q6_Q<='0Q:7Q;~'0PRQ:cQ6_Q:7p+0>:S;WQ<=Q;~Q5nG3Q8bQ8aQ8aPePPPcP}PwQ8GQ7E5>_P~PEb4b5b6X05Q<RQ<;Q8]Q;_C}^05Q<Vb1b2b3Q;zPoG^Q9KQ0?DDQ9KQ<IQ<93OeN902E;E;E;E;E;NB08Q;GQ;cP1Q<Cp+0D4S;cQ8FQ;yQ<CQ;cQ<CQ8FCLdO4b9Q<LQ<MPDP?Q<M/TDdQ7<DWQ2vQ;cQ2vPTQ3cP1Q0`Q<UQ0IEKW7PTQ<SQ;cQ1EQ7?D<PTQ<SQ8BP[Q7?D<Q0HQ6VPTPFQ<SQ;cQ1EQ7?g02:NQ<>Q;>Q9IPBQ;|g02;XPrg02<bQ5up+0;6Q<DQ7|Q<Dp+0E`S<9P1Q8CQ6|C|W7p+0?mS<VQ<9p+0FnReQ<BQ6|H0qX:5Q<DQ;=Q;=Q<VQ;6PQQ8_Q8dQ8cQ8cQ8bPPPcP}PwP_Q8bQ:{Q;4H0<P~PEb4b5b6X05Q<0,51S8]Q;fQ;g407^05P1Q<XO1S;gb1b2b3L0?Q<5PoDDQ<DQ7|Q;6Q6jC|ep+0;mP1E=b;Q;=Q<5Q;=Q6hQ;>PrJ0DQ;oeQ;oQ<DQ6]Q<DQ<9Q<:721W7Q<DQ6]Q65P1Fdb;PVQ0TQ1EPBQ0LPVQ0\Q0TPBQ1GPVQ17Q0\PBQ0XPVQ1=Q17PBQ0YPVQ1WQ1=PBQ0ePVPuQ1WPBQ1XPuQ7xPBQ;VPVQ3{Q:eQ;zQ8JQ<TQ8cQ8bQ8bQ8ap+0@nS<RQ:eP1Q<UQ0FO2b1b2b3Q5}PoG^Q8?eQ2wQ3{Q9K,01X:5Q2QQ<V/01X:5Q8cQ8bQ8bQ8aPPPcP}PwQ8aQ;k5>_P~PEb4b5b6X05Q9LQ;s'0^05Q1kb1b2b3Q;WQ0?DDQ5}PoDDQ5}Q;W'0eQ2QQ;7Q<T5O1X:5Q3{Q:7Q:u80:1X:5Q:1Q<K'0Q6XQ<='0PRQ:bQ:1Q6XQ9;Q<KQ<=Q;]G3Q8cQ8bQ8bQ8aPPPcP}PwQ8CQ7F5>_P~PEb4b5b6X05Q;sQ<HQ9LQ;`C}^05Q1kb1b2b3Q5}PoG^Q;WQ0?DDQ;WQ;RQ<F3OeN902E;E;E;E;E;E;NB08Q;<Q;bP1Q;dPvQ8CQ;yQ;dPvQ;dQ8CCLdO4b9Q2vQ<CPDP?Q<C/TDdQ8BDWQ<DPvQ<DPTp+0<fS;bP1P]Q<XQ0]EKW7PTQ3cPvPxQ<UD<PTQ3cQ6}PLQ<UD<Q0IQ7EPTPFQ3cPvPxQ<Ug02=lQ<LQ;>Q2`PBQ;|g02?6Prg02@@Q5vp+0;7Q<9Q81Q<9Q9fP1Q<PQ9IQ6|I0FW7Q;2Q9fp+0FoS0IP1Q<6Q6|I0JX:5Q<9Q9cQ9cQ;2Q<QPQQ8`Q8eQ8dQ8dQ8cPPPcP}PwP_Q8cQ2zQ;iH0<P~PEb4b5b6X05Q<>,51p+0FXS<FQ;V,51407^05P1PmO1b1b2b3L0?Q8QQ;2Q8eQ8dQ8dQ8cQ70Q8`P1PmPSO2b1b2b3Q8eQ8dQ8dQ8cQ6rQ;=P1PmPNO2b1b2b3K0KQ<9Q81Q<QQ6jC|ep+0;nP1E=b;Q9cQ8QQ9cQ<YQ;>PrJ0DQ;oeQ;oQ<9Q6]Q<9Q9fQ<:721W7Q<9Q6]Q65P1Fdb;PVQ0`PxPBPYPVQ0UQ0`PBP[PVQ0ZQ0UPBQ1EPVQ0^Q0ZPBQ0TPVQ0jQ0^PBQ0\PVQ1BQ0jPBQ17PVp+0@BS65Q1BPBQ1=Q65Q7|PBQ;qPVQ<VQ;pQ5}Q;zQ<WQ8dQ8cQ8cQ8bQ6yQ;pP1Q<XPOO2b1b2b3Q<5PoG^Q6`eQ13Q<VQ;W,01X:5Q2QQ;2/01X:5Q8dQ8cQ8cQ8bPPPcP}PwQ8bQ8X5>_P~PEb4b5b6X05Q8]Q;F,51RO'0^05Q;gb1b2b3Q9;Q0?DDQ<5PoDDQ<5Q9;'0eQ2QQ:cQ<W5O1X:5Q<VQ6XQ:s80:1X:5Q6UQ6J'0Q9xQ<K'0PRQ3YQ6UQ9xQ8}Q6JQ<KQ8JG3Q8dQ8cQ8cQ8bPPPcP}PwQ8@Q6\5>_P~PEb4b5b6X05POQ;YQ8]Q<0C}^05Q;gb1b2b3Q<5PoG^Q9;Q0?DDQ9;Q;7Q<T3OeN902E;E;E;E;E;E;E;NB08Q:mQ<OP1PeQ75Q8>Q;yPeQ75PeQ8>CLdO4b9Q<DQ;dPDP?Q;d/TDdQ6}DWQ<9Q75Q<9PTp+0<gS;gP1PZPmQ0kEKW7PTQ;bQ75P^Q<XD<PTQ02Q9f,@JQ:j:0;JsQ;bQ;on0100000020000Q8:P^Q<XD<Q0]Q7FPTPFQ;bQ75P^Q<Xg02AJRoPsQ<0Q:5g02BT&03og02C^N=0OQ:lQ;eP1Q0IQ:5Q8;Q;yQ0IQ:5Q0IQ8;CLdO4b9Q<9PePDP?1TeDdQ8:DWQ9fQ:5Q9fPTQ;^P1PjPuQ0rEKW7Q9oQ3cQ9oQ<RQ<>PrJ0DQ;oeQ;oQ9rQ6hQ9rPTp+0<iS;oQ;`P1Q6}CzQ2`PHQ65PkEKW7Q9rQ6hQ0kQ9rQ2ZQ0kPTQ5[Q75PjPuD<PTQ02Q9E,@JQ:d:0;JCQ5[Q5Sn0100000020000Q8;PjPuD<Q0rp+0ALS0kPTPFQ5[Q75PjPug02DhRoPCQ<DQ2`g02F2&03og02G<N=0OQ:oQ<PP1p+0G1S;^Q75Q8<Q;u#NS;eQ;^Q75Q;^Q8<CLdO4b9Q9rp+0G0S8]Q3VP?Q8]Q3V'TdQ8;DWQ9EQ75Q9EPTQ5]P1Q0LQ6PQ0MEKW7Q9yQ5VQ9yQ;gQ9y41{p+0A0S8bQ<9PrEcQ5SeQ5Sp+0EdRoQ6yPTQ5XQ<0P1Q8@CzPvP[Q:GPdEKX7oPoQ6yQ0rPoQ7aQ0rPTQ5ZQ2`Q0LQ6PD<PTQ02Q:6,@JQ75Q5ZQ5Sn0100000020000Q8<Q0LQ6PD<Q0Mp+0ANS<0PTPFQ5ZQ2`Q0LQ6Pg02HFROQ9fQ:|g02IP&03Og02JZN<1zQ:gQ<4P1p+0G3S<4Q75Q8=Q;eQ<4Q75Q<4Q8=CLdO4b9Pop+0G2S:gQ3VP?Q:gQ3V'TdQ8<DWQ:6Q75Q:6PTQ5]P1PxQ7HPUEKW7Q;DQ<3P1p+0G4ROQ2~Q8=p+0FWS5X#NPOQ2~POQ8=CLdO4b9Q:6p+0D[S8dQ8<32p+0EfRNQ2~PTQ5WPoP1PvP]Q:IQ0oGeX7NPTQ5ZQ2`PxQ7HD<PTQ02Q:D,@JQ;B:0;JCQ5ZQ5Rn0100000020000Q8<PxQ7HD<PUQ7]PTPFQ5ZQ2`PxQ7Hg02KdPCQ9EQ75PpQ8zg02LnPrg02N8Q:2Q8;Q:2p+0::S5ZQ:2Q5_Q:2Q8fQ:2FoQ70Q9EPrEcQ2|eQ2|Q:DQ9UQ:DQ9Yp+01^S70Q<F>1G1vPVQ3CI0=W7Q;BQ<6P1p+0G6S5WQ8zQ8<Q2zQ5WQ8zQ5WQ8<CLdO4b9Q:DQ9XQ8;32Q9lQ8zQ9lQ9ZQ0OP1PVQ7QI0=W7Q9YQ:RQ9YQ9ZQ7Q721W?Q2RQ1BQ8z<0EVPFQ:SQ2`Q;gQ2`Q;bQ2`Q3cQ2`Q<SQ2`Q8QQ2`Q<5Q2`Q5}Q2`Q0lQ2`I0@D6D6D6S:sQ;lPVPqPzPzQ8hPPPc&1w5S13PwP_P_P`Q:wQ:wQ5Y5a_I0IP~PEb4b5b6PvP1b1b2b3Q75eQ:5Q:0PRQ<PQ:{Q:|Q9}Q<9Q<9Q9RG3PqPzPzQ8hPPPcQ13PwQ75Q5Y5>_P~PEb4b5b6Q75P1b1b2b3H0cQ:5eQ:AQ8?Q79Q<TQ;lDGQ5K/1hPVQ:EQ7?/4bRSQ9fQ:APSQ<;EPX=@p+0:mS<TQ:Ap+0;bRSQ:AQ9SQ:APSQ3NQ;tQ;zQ;jQ8JQ;]Q79Q97PtQ93PRQ<PQ:{Q:|Q9}Q;[Q;[Q:EG3PRQ<PQ7vQ2eQ9NQ;lQ;lQ2zG3EFE8E8PqPzPzQ8hPPPcP}PwP_Q;>P;P_PpP;P_Q7QP_Q3CP_P_Q<2,uv21E_6S;zGtFCP~PEb4b5b6X05X8Gp+0G5RS,01S9SQ:C/08S:CQ;^,57S8?Q8?PNQ8?Q0IPNQ:wQ8?P6EYC[[[^05^8GP1Q;tQ6^Q0rPkO4b1b2b3DEQ<TeQ6OQ;KQ5KPhPVQ79Q<U/4bS5KQ9fQ6_Q5KQ<;EPX=@p+0:lS<TQ6_p+0;`S8?Q6_Q7LQ6_Q8?Q8jQ9KQ5nQ9;Q5lQ5jQ:7Q;Wp+0??S5nQ8}PRQ<PQ:{Q:|Q9}Q7?Q7?Q:JG3PRQ<PQ:PQ:LQ;NQ;lQ;lQ2zG3EFE8E8PqPzPzQ8hPPPcP}PwP_Q;>P;P_PpP;P_Q7lP_Q7dP_P_Q;1,uvQ;zGtFCP~PEb4b5b6X05X8GQ9SQ:C157:S8?Q8?PNQ8?Q0IPNQ:wQ8?P6EYC[[[^05^8GP1Q9KQ6^Q0rPkO4b1b2b3DEQ<Tep+0@XS<TQ6eQ5JP^PVQ:7Q<X/4bS8?Q9fQ:1Q8?Q<;EPX=@p+0:kS7LQ:1Q5{Q:1p+0;_Q:1Q5{Q7XQ6IQ5hQ8xQ;nQ;xQ6XQ9Gp+0?>S5hQ6lPRQ<PQ:{Q:|Q9}Q<UQ<UQ7MG3PRQ<PQ:VQ6ZQ8EQ;lQ;lQ2zG3EFE8E8PqPzPzQ8hPPPcP}PwP_Q;>P;P_PpP;P_Q7]P_Q7RP_P_Q:i,uvQ;zGtFCP~PEb4b5b6X05X8GQ9SQ:CQ;Y,57S:iQ:iPNQ:iQ0IPNQ:wQ:iP6EYC[[[^05^8GP1Q6IQ6^Q0rPkO4b1b2b3DEQ7LeQ7eQ6MQ98PxPVQ6X14mbS:iQ9fQ6UQ:iQ<;EPX=@p+0:jS5{Q6UQ5xQ6UQ5rQ6UQ5xQ8pQ90p+0<WQ7Wp+0<VS5xQ5qQ9xp+0>0S5rQ3TQ9<PRQ<PQ:{Q:|Q9}Q<XQ<XQ:YG3PRQ<PQ:]Q:[Q<=Q;lQ;lQ2zG3EFE8E8PqPzPzQ8hPPPcP}PwP_Q;>P;P_PpP;P_Q<0P_Q7JP_P_Q9Q,uvQ;zGtFCP~PEb4b5b6X05X8GQ9SQ:CQ<@,57S9Q#XS:5Q9QPNQ9QQ0IPNQ:wQ9Q;n6Fm[[^05^8GP1Q90Q6^Q0rPkO4b1b2b3DEQ5{eQ6mQ7SQ1SQ0`PVQ9x14ubS75Q9fQ9tQ75Q<;EPX=@p+0:iS6rQ9tp+0;ZS8`Q9tp+0;[Q9tQ8`p+0=hS8`p+0=lS1kp+0<Tp+0=jS9Lp+0<SS;sQ5pQ9nQ:aQ9TQ9>PRQ<PQ:{Q:|Q9}PmPmQ:^G3PRQ<Pp+0?_S8aQ:_Q6JQ;lQ;lQ2zG3EFE8E8PqPzPzQ8hPPPcP}PwP_Q;>P;P_PpP;P_Q0kP_Q6\P_P_Q;=,uvQ;zGtFCP~PEb4b5b6X05X8GQ9SQ:CQ;Q,57S;=#XS;kQ;=PNQ;=Q0IPNQ:wQ;=;n6Fm[[^05^8GP1Q1kQ6^Q0rPkO4b1b2b3DEQ6reQ:kQ:ZQ5IQ0UPVQ9nQ65/4bS6rQ9fQ9hQ6rQ<;EPX=@p+0:hS2wQ9hp+0;XS0FQ9hp+0;YQ9hQ0FQ3wQ9:p+0<Qp+0=eS8Gp+0<PS2Pp+0<OS<JQ9bQ3yp+0?;S0EQ76PRQ<PQ:{Q:|Q9}PuPuQ;@G3PRQ<PQ:`p+0?aS<ZQ7|Q;lQ;lQ2zG3EFE8E8PqPzPzQ8hPPPcP}PwP_Q;>P;P_PpP;P_Q7FP_Q7EP_P_Q9o,uvQ;zGtFCP~PEb4b5b6X05X8GQ9SQ:CQ<M,57S9o#XS<[Q9oPNQ9oQ0IPNQ:wQ9o;n6Fm[[^05^8GP1Q9:Q6^Q0rPkO4b1b2b3DEQ2weQ6iQ:XQ94Q0ZPVQ9bQ6P/4bS2wQ9fQ:OQ2wQ<;EPX=@p+0:gS<\Q:Op+0;VS<]Q:OQ5|Q:OQ<]p+0=^S<]Q7Vp+0<Np+0=`S5|Q::Q5fQ0tQ8~Q9PQ8{PRQ<PQ:{Q:|Q9}Q65Q65p+0?cS<^G3PRQ<PQ6jPBQ8|Q;lQ;lQ2zG3EFE8E8PqPzPzQ8hPPPcP}PwP_Q;>P;P_PpP;P_Q6VP_Q6RP_P_Q9w,uvQ;zGtFCP~PEb4b5b6X05X8GQ9SQ:CQ;F,57S<_#XS<`Q<_PNQ<_Q0IPNQ:wQ<_;n6Fm[[^05^8GP1Q7VQ6^Q0rPkO4b1b2b3DEQ<\eQ7;Q:UQ1:PVQ0tQ:G/4bS<aQ9fQ2iQ<aQ<;EPX=@p+0:fS<bQ2ip+0;TS<cQ2ip+0;UQ2iQ<cp+0=YS2iQ8yQ5ep+0=[S5eQ5dQ5cQ9\p+0=\S9\Q8Np+0=ZS<dPRQ<PQ:{Q:|Q9}Q6PQ6PQ6|G3PRQ<PQ:fQ01p+0>OS:{Q;lQ;lQ2zG3EFE8E8PqPzPzQ8hPPPcP}PwP_Q;>P;P_PpP;P_Q7DP_Q7BP_P_Q9?,uvQ;zGtFCP~PEb4b5b6X05X8GQ9SQ:CQ0I,57S7BQ7BPNQ7BQ0IPNQ:wQ7BP6EYC[[[^05^8GP1Q8yQ6^Q0rPkO4b1b2b3DEQ<beQ0~Q0dI0a+0\GHGHGHGHGHGHGHQ;lQ:s80`VeL0]E=Q8<P1EIb9Q5RP1E=b;Q8z$0yNA0jQ;OQ<QP1PSQ9mQ8=Q;ePSQ9mPSQ8=CLdO4b9PNPOQ3VP?Q3V,TOdQ8<DWQ:DQ9mQ:DPTQ5\P1Q70Q6YQ0qEKW7PTQ5]Q9mP]Q:ID<PTQ02Q9l,@JQ9IQ5]Q2Hn0100000020000Q8:P]Q:ID<Q0oQ7dPTPFQ5]Q9mP]Q:Ig02OBPoQ;_Q;iQ28Q2xg02PLPrg02QVQ24Q89Q24Q8<Q24Q57Q24Q2aQ24Q5zQ24I0@D6Q7GQ;_PrEcQ2}eQ2}Q9lQ9ZQ9lQ9ZQ0OQ8D,M1PVQ2xI0=W7Q5YQ5XP1p+0G7S7GQ9qQ8:Q:|Q7GQ9qQ7GQ8:CLdO4b9Q9lQ9ZQ8932P3Q9qQ9qQ1CP1PVQ1}I0=X73Q9ZQ:RQ9ZQ9qQ1}721W?Q2RQ11Q9q<0EVPFQ:UPvp+0<hS2RPvQ;gPvQ;bPvQ3cPvQ<SPvQ8QPvQ<5PvQ0mPvI0@D6D6D6S8QPePVQ8iPqPqPzPPPcQ13PwP_P_P`Q2zQ2zQ;A5a_I0IP~PEb4b5b6Q9}P1b1b2b3Q9seQ9mQ9kPRQ;}Q:~Q;0Q9eQ9fQ9fQ9yG3Q8iPqPqPzPPPcQ13PwQ9sQ;A5>_P~PEb4b5b6Q9sP1b1b2b3H0cQ9meQ:EQ6`Q8NQ<WPeDGQ94/1hPVQ2eQ5KQ9rQ9PQ5KQ0IEPX=@Q<bQ:Ep+0;SRvQ:EQ<cQ:EPvQ93Q9NQ5cQ97Q5bQ8JQ8NQ2ip+0?1S5bp+0=XS5cPRQ;}Q:~Q;0Q9eQ7?Q7?Q2eG3PRQ;}Q:JQ7vQ;vPePeQ:|G3EFE8E8Q8iPqPqPzPPPcP}PwP_Q;CP;P_PyP;P_Q6gP_Q7QP_P_Q9}Q;m'uQ;zGtFCP~PEb4b5b6X05X8GQ5W,01S;mQ:F/08S<cQ:g,57RvPvQ:DPvQ8]Q:DQ2zPvP6EYC[[[^05^8GP1Q5eQ7OPkQ0MO4b1b2b3DEQ<beQ6TQ7;Q94PhPVQ:AQ8?Q9rQ8NQ8?Q0IEPX=@p+0:eRvQ79p+0;QS5eQ79Q5yQ79Q5eQ8}Q3NQ5aQ;WQ5wQ5lp+0?8S5wp+0=WS5ap+0?0S5eQ6>PRQ;}Q:~Q;0Q9eQ<UQ<UQ:LG3PRQ;}Q7MQ:PQ;UPePeQ:|G3EFE8E8Q8iPqPqPzPPPcP}PwP_Q;CP;P_PyP;P_Q3CP_Q7lP_P_Q9}Q:x'uQ;zGtFCP~PEb4b5b6X05X8GQ;mQ<cQ:5Q9QQ:DQ9QQ8]Q:DQ2zQ9Q;n6Fm[[^05^8GP1Q2iQ7OPkQ0MO4b1b2b3DEPveQ6OQ;KQ95P^PVQ6_Q:iQ9rQ5wQ:iQ0IEPX=@p+0:dS9QQ:7Q5oQ:7p+0;PQ:7Q5oQ6lQ8jQ5gQ9Gp+0<DQ;nQ9OQ6@Q9Mp+0=TS5gPRQ;}Q:~Q;0Q9eQ<XQ<XQ6ZG3PRQ;}Q:YQ:VQ;~PePeQ:|G3EFE8E8Q8iPqPqPzPPPcP}PwP_Q;CP;P_PyP;P_Q7dP_Q7]P_P_Q9}Q:e'uQ;zGtFCP~PEb4b5b6X05X8GQ;mQ<cQ;kQ;=Q:DQ;=Q8]Q:DQ2zQ;=;n6Fm[[^05^8GP1Q5aQ7OPkQ0MO4b1b2b3DEQ9QeQ<TQ6eQ10PxPVQ:1Q75Q9rQ9OQ75Q0IEPX=@Q5QQ6XQ5kQ6XQ5mQ6XQ5kQ9<Q7Xp+0<CS5kQ5rp+0<BQ5xp+0?6S5mp+0=SS9Qp+0>nS;=p+0=RS;kPRQ;}Q:~Q;0Q9ePmPmQ:[G3PRQ;}Q:^Q:]Q<KPePeQ:|G3EFE8E8Q8iPqPqPzPPPcP}PwP_Q;CP;P_PyP;P_Q7RP_Q<0P_P_Q9}Q0C'uQ;zGtFCP~PEb4b5b6X05X8GQ;mQ<cQ<[Q9oQ:DQ9oQ8]Q:DQ2zQ9o;n6Fm[[^05^8GP1Q6@Q7OPkQ0MO4b1b2b3DEQ5QeQ7eQ6MQ5vQ0`PVQ6UQ6rQ9rQ5mQ6rQ0IEPX=@Q5PQ9xQ6~Q9xQ5iQ9xQ6~Q9>Q8pp+0<AQ:ap+0<@S6~Q;sp+0?5S5ip+0=QS9oQ20p+0=PS<[PRQ;}Q:~Q;0Q9ePuPuQ:_G3PRQ;}Q;@Q8aQ7xPePeQ:|G3EFE8E8Q8iPqPqPzPPPcP}PwP_Q;CP;P_PyP;P_Q7JP_Q0kP_P_Q9}Q9c'uQ;zGtFCP~PEb4b5b6X05X8GQ;mQ<cQ<`Q<_Q:DQ<_Q8]Q:DQ2zQ<_;n6Fm[[^05^8GP1Q9QQ7OPkQ0MO4b1b2b3DEQ5PeQ6mQ7SQ5uQ0UPVQ9tQ2wQ9rQ5iQ2wQ0IEPX=@Q5NQ9np+0;IS5PQ9np+0;JS<_Q9nQ5PQ76Q8`p+0<?S<`Q3yQ3gQ2Pp+0?4S5op+0=OS:5p+0>lS6>p+0=NS5yPRQ;}Q:~Q;0Q9eQ65Q65Q<ZG3PRQ;}Q<^Q:`Q81PePeQ:|G3EFE8E8Q8iPqPqPzPPPcP}PwP_Q;CP;P_PyP;P_Q6\P_Q7FP_P_Q9}Q9R'uQ;zGtFCP~PEb4b5b6X05X8GQ;mQ<cQ<C,57S5KQ5KQ:DQ5KQ8]Q:DQ2zQ5KP6EYC[[[^05^8GP1Q9oQ7OPkQ0MO4b1b2b3DEQ5NeQ:kQ:ZP0Q0ZPVQ9hQ<aQ9rQ5oQ<aQ0IEPX=@Q5MQ9bp+0;GS5KQ9bp+0;HS<WQ9bQ5KQ8{Q3wp+0<=S6`Q8~p+0<<S9mQ::p+0?3S9ZQ7Up+0>kS;iQ9gPRQ;}Q:~Q;0Q9eQ6PQ6PPBG3PRQ;}Q6|Q6jp+0>NS9IPePeQ:|G3EFE8E8Q8iPqPqPzPPPcP}PwP_Q;CP;P_PyP;P_Q7EP_Q6VP_P_Q9}Q9a'uQ;zGtFCP~PEb4b5b6X05X8GQ;mQ<cQ;V,57S:sQ:sQ:DQ:sQ8]Q:DQ2zQ:sP6EYC[[[^05^8GP1Q:5Q7OPkQ0MO4b1b2b3DEQ5MeQ6iQ:XQ1:PVQ:OQ7H/4bS:OQ9rQ9ZQ:OQ0IEPX=@Q5LQ0tp+0;ES9rQ0tp+0;FQ0tQ9rQ<dQ<]p+0<;S9rQ9\p+0<:Q5dp+0?2S5dQ85p+0>jS0tQ80PRQ;}Q:~Q;0Q9eQ:GQ:GQ01G3PRQ;}Q<?Q:fQ91PePeQ:|G3EFE8E8Q8iPqPqPzPPPcP}PwP_Q;CP;P_PyP;P_Q6RP_Q7DP_P_Q9}Q;X'uQ;zGtFCP~PEb4b5b6X05X8GQ;mQ<cQ8],57S:|Q:|Q:DQ:|Q8]Q:DQ2zQ:|P6EYC[[[^05^8GP1Q7UQ7OPkQ0MO4b1b2b3DEQ5LeQ0lQ0fI0a+0\GHGHGHGHGHGHGHQ8Q:0`eVeL0]E=Q8:P1EIb9Q5SP1E=b;Q2x$0yNA0jQ;BQ<6P1Q5WQ9AQ8;Q;eQ5WQ9AQ5WQ8;CLdO4b9Q:DPSQ3VP?Q3V,TSdQ8:DWQ9lQ9AQ9lPTQ2JP1Q0OQ6^Q07EKW7PTQ2IQ9AQ70Q6YD<PTQ2IQ6sPZQ6YD<Q0qQ7lPTPFQ2IQ9AQ70Q6Yg02R`PNQ:6Q:WQ3{Q1}g02SjPrg02U4Q:;p+04KS0qQ:;Q8:Q:;Q8=Q:;p+0:<S<6Q:;Q2ZQ:;Q3HQ:;I0@D6D6S8QQ7>PNPrCbQ1zeQ1zP3Q8rQ9_Q89,M1S5LQ;232X73Q;SQ9_p+0G8S;mP1Q;VQ;2I0JX:5P3Q:;Q:;Q;SQ;FQ;[Q8gQ8iPqPqPzPPPcP}PwP_PzQ;<Q9kH0<P~PEb4b5b6X05Q:6,51Q;aQ;l,51407^05P1Q7OO1b1b2b3L0?Q3HQ;SQ8iPqPqPzQ71Q8gP1Q7OQ0MO2b1b2b3Q8iPqPqPzQ72Q24P1Q7OPkO2b1b2b3K0KP3Q8rQ;FQ<VC|eQ2HP1E=b;Q8QQ7>Q:6PrCbQ2BeQ2BP3Q5TQ9_Q2}721X73P3Q5TQ2;P1Fdb;PVQ1IQ70Q3{PYPVQ0WQ1IQ3{P]PVQ1QQ0WQ3{Q0SPVQ1=Q1QQ3{Q0VPVQ0cQ1=Q3{Q0aPVQ0iQ0cQ3{Q1XPVQ0mQ0iQ3{Q11PVQ:SQ0mQ3{Q0hQ:SQ8sQ3{Q8]PVQ:rQ9yQ8fQ;oQ5^PqPzPzQ8hQ6wQ9yP1Q6^Q0rO2b1b2b3Q5zQ0:G^p+0;>eQ1;Q:rQ7{,01X:5S1;Q7CQ;S/01X:5PqPzPzQ8hPPPcP}PwQ8hQ9e5>_P~PEb4b5b6X05151oS0rQ<7,51S6w'0^05P1Q6^O1Rkb1b2b3Q64Q0DDDQ5zQ0:DDQ5zQ64'0eQ7CQ<NQ5^'0X:5Q:rQ9JQ:o80:1X:5p+0>hS<NQ8u'0Q1\Q8v'0PRQ<PQ<NQ1\Q9`Q8uQ8vQ2RG3PqPzPzQ8hPPPcP}PwQ89Q7Q5>_P~PEb4b5b6X05Q6wQ<CQ0rPoC}^05Pkb1b2b3Q5zQ0:G^Q64Q0DDDQ64Q<Op+0<33OeN902E;E;E;E;E;E;E;E;NB08Q5YQ5XP1Q7GQ:TQ89Q;eQ7GQ:TQ7GQ89CLdO4b9Q9lQ5WQ3VP?Q5WQ3V'TdQ6sDWP3Q:TPTQ2KP1PHQ7OQ1UEKX73PTQ2JQ:TPjQ6^D<PTQ02Q9_,@JQ8XQ2JQ2In0100000020000Q88PjQ6^D<Q07Q3CPTPFQ2JQ:TPjQ6^g02V>PNQ<DQ9AQ2Dp+05@S9Ag02WHPrg02XRQ:>Q28Q:>Q8;Q:>Q6}Q:>p+0:=S07Q:>Q2=Q:>Q3<Q:>FoD6Q6uQ<DPrEcQ2BeQ2BQ9_Q:NQ9_Q9vQ0LQ8:,M1PVQ2lI0=W7P0p+0EkRkQ:Np+0G9S8:Q;q,41S6u'Q32X:5Q9_Q5F'yQ07P0PpQ8iQ8iPqQ86Q:~P1Q10Q09O2b1b2b3PpQ8iQ8iPqQ7=Q:TP1Q10Q08O2b1b2b3K0KQ4:eQ4:PkQ:NQ9{P[P1PVp+05=S08I0=X7kQ9vp+0:BS;eQ9vQ9{Q08721W?Q15Q11Q:N<0EVPFQ:ZQ;cQ2xQ;cQ8fQ;cQ;oQ;cQ2RQ;cQ;gQ;cQ;bQ;cQ3cQ;cQ<SQ;cQ18Q;cFoD6D6D6S;cP0PVPyPpPpQ8iPPPcP}PwP_Q9eP;P_Q2zP;P_P_P`Q:\Q:\Q;C5a_I0IFCP~PEb4b5b6X05141OS<OQ<4'0RqQ5W/08Q<C,47S0D#XS0rQ0DQ9l40L[[^05P1Q95Q09Q0:O3b1b2b3%X0S6wQ9E80L0eQ<6p+0:JS8hQ9EPRQ<3Q2gQ8hQ57Q9EQ9EQ9aG3PyPpPpQ8iPPPcP}PwP_Q9eP;Q:\Q;?'UQ;C5>_CJP~PEb4b5b6X05Q<M,48S<PQ8]Q:D3O\q^05P1Q95Q09O2S5^b1b2b3I0zQ<6eQ<NQ25Q5ZQ2yP0DGQ3bQ0}'1PVQ9JQ8?PoQ57Q8?Q5uEPX=@p+069S8?Q<NQ3BQ<NQ3DQ<NQ3BQ9`Q7{Q4:Q64Q3sQ9rQ5ZQ2]Q3^Q5@PRQ<3Q2gQ8hQ57Q<UQ<UQ9JG3PRQ<3Q;iQ0tQ80P0P0Q1hG3EFE8E8PyPpPpQ8iQ;7PcP520{57P8Q13H1tRqPwP_Q9^P;P_Q;LP;P_Q8mP;P_Q6RP_Q7DP_P_Q:\Q9}21E_ARzF\ERFCP~PEb4b5b6X05X<5X8GQ5W=O8SS9}p+0G:S13,08S3^p+0E1S2]/07S9rQ;q,56S3sQ3sPkQ3sPOPkQ0I,4AS4:/4OS3BQ3sP4EYC[[[[^05^<5^8GP1Q5AQ95Q:SQ09PdPUO6b1b2b3DEQ8?eQ28Q2{Q3bQ0}PVQ:JQ:iPoQ5ZQ:iQ5u'0S5ZDrX=@Q3nQ7vQ3?Q7vQ3AQ7vQ3?Q97Q;NQ46Q9NQ6HQ5}p+0:9S6HQ3XQ5HQ5>PRQ<3Q2gQ8hQ57Q<XQ<XQ:JG3PRQ<3Q:PQ:LQ;UP0P0Q1hG3EFE8E8PyPpPpQ8iQ;7PcPqPwP_Q9^P;P_Q;LP;P_Q8mP;P_Q7[P_Q7ZP_P_Q:\Q:xPzF\ERFCP~PEb4b5b6X05X<5X8GQ9}Q3^Q9rQ5W,56S:xQ:xPkQ:xPOPkQ3BQ:xP4EYC[[[[^05^<5^8GP1Q5@Q95Q:SQ09PdPUO6b1b2b3DEQ3neQ6QQ:kQ62PKPVQ2eQ75PoQ6HQ75Q5u'0S6HDrX=@Q3mQ:EQ3;Q:EQ3=Q:EQ3;Q;WQ;jQ43Q3NQ3pQ;]Q1_Q5GQ4nQ5=PRQ<3Q2gQ8hQ57PmPmQ7MG3PRQ<3Q:VQ6ZQ;~P0P0Q1hG3EFE8E8PyPpPpQ8iQ;7PcPqPwP_Q9^P;P_Q;LP;P_Q8mP;P_Q7YP_Q6gP_P_Q:\Q:ePzF\ERFCP~PEb4b5b6X05X<5X8GQ9}Q3^Q9r156eS:eQ:ePkQ:ePOPkQ3BQ:eP4EYC[[[[^05^<5^8GP1Q5>Q95Q:SQ09PdPUO6b1b2b3DEQ3mep+0@[S5>Q6iQ3aP^PVQ:AQ6rPoQ1_Q6rQ5u'0S1_DrX=@Q3lQ79Q4AQ79Q39Q79Q4AQ9GQ9;Q3}Q8jQ4WQ5jQ5OQ4yQ40Q5;PRQ<3Q2gQ8hQ57PuPuQ:YG3PRQ<3Q:]Q:[Q<KP0P0Q1hG3EFE8E8PyPpPpQ8iQ;7PcPqPwP_Q9^P;P_Q;LP;P_Q8mP;P_Q7QP_Q3CP_P_Q:\Q0CPzF\ERFCP~PEb4b5b6X05X<5X8GQ9}Q3^Q9rQ;a,56S0C#XS<KQ0CPkQ0CPOPkQ3BQ0C;n4Fm[[[^05^<5^8GP1Q5=Q95Q:SQ09PdPUO6b1b2b3DEQ3leQ6TQ7;Q6qP]PVQ6_Q2wPoQ5OQ2wQ5u'0S5ODrX=@Q3kQ:7Q4>Q:7Q36Q:7Q4>Q5rQ8xQ3~Q7XQ4UQ;xQ3_Q4tQ2^Q4oPRQ<3Q2gQ8hQ57Q65Q65Q:^G3PRQ<3Q8aQ:_Q7xP0P0Q1hG3EFE8E8PyPpPpQ8iQ;7PcPqPwP_Q9^P;P_Q;LP;P_Q8mP;P_Q7lP_Q7dP_P_Q:\Q9cPzF\ERFCP~PEb4b5b6X05X<5X8GQ9}Q3^Q9rQ0I,56S9c#XS2^Q9cPkQ9cPOPkQ3BQ9c;n4Fm[[[^05^<5^8GP1Q5;Q95Q:SQ09PdPUO6b1b2b3DEQ3keQ6OQ;KQ2\Q0SPVQ:1Q<aPoQ3_Q<aQ5u'0S3_DrX=@Q3jQ6XQ4<Q6XQ6=Q6XQ4<Q:aQ7WQ2EQ8pQ6AQ5qQ1vQ5DQ5BQ5CPRQ<3Q2gQ8hQ57Q6PQ6PQ;@G3PRQ<3Q:`Q<ZQ81P0P0Q1hG3EFE8E8PyPpPpQ8iQ;7PcPqPwP_Q9^P;P_Q;LP;P_Q8mP;P_Q7]P_Q7RP_P_Q:\Q9RPzF\ERFCP~PEb4b5b6X05X<5X8GQ9}Q3^Q9r156:S9R#XS5BQ9RPkQ9RPOPkQ3BQ9R;n4Fm[[[^05^<5^8GP1Q4oQ95Q:SQ09PdPUO6b1b2b3DEQ3jeQ<TQ6ep+05TS4oQ0VPVQ6UQ:OPoQ1vQ:OQ5u'0S1vDrX=@Q3iQ9xQ48Q9xQ3]Q9xQ48Q3yQ9LQ4SQ8`Q5?Q5pQ1{Q3[Q4kQ5EPRQ<3Q2gQ8hQ57Q:GQ:GQ<^G3PRQ<3Q6jPBQ9IP0P0Q1hG3EFE8E8PyPpPpQ8iQ;7PcPqPwP_Q9^P;P_Q;LP;P_Q8mP;P_Q<0P_Q7JP_P_Q:\Q9aPzF\ERFCP~PEb4b5b6X05X<5X8GQ9}Q3^Q9rQ8],56S4k#XS3[Q4kPkQ4kPOPkQ3BQ4k;n4Fm[[[^05^<5^8GP1Q5CQ95Q:SQ09PdPUO6b1b2b3DEQ3ieQ7eQ6Mp+05SS5CQ0aPVQ9tQ:I/4bS5pPoQ1{Q5pQ5u'0S1{DrX=@Q3hQ9nQ3ZQ9nQ3xQ9nQ3ZQ8~Q8GQ4QQ3wQ44Q<JQ6KQ4|Q3Rp+09ZS3RPRQ<3Q2gQ8hQ57Q7HQ7HQ6|G3PRQ<3Q:fQ01Q91P0P0Q1hG3EFE8E8PyPpPpQ8iQ;7PcPqPwP_Q9^P;P_Q;LP;P_Q8mP;P_Q0kP_Q6\P_P_Q:\Q:;PzF\ERFCP~PEb4b5b6X05X<5X8GQ9}Q3^Q9rQ<@,56S91#XS4|Q91PkQ91POPkQ3BQ91;n4Fm[[[^05^<5^8GP1Q5EQ95Q:SQ09PdPUO6b1b2b3DEQ3heQ6mQ7SQ1XPVQ9hQ6Y/4bS5EPoQ6KQ5EQ5u'0S6KDrX=@Q3:Q9bQ41Q9bQ6:Q9bQ41Q9\Q5|Q1FQ<]Q4OQ5fQ5AQ4wQ59Q4sPRQ<3Q2gQ8hQ57Q:IQ:IQ<?G3PRQ<3Q<EQ9WQ8uP0P0Q1hG3EFE8E8PyPpPpQ8iQ;7PcPqPwP_Q9^P;P_Q;LP;P_Q8mP;P_Q7FP_Q7EP_P_Q:\Q2~PzF\ERFCP~PEb4b5b6X05X<5X8GQ9}Q3^Q9r156OS9^Q9^PkQ9^POPkQ3BQ9^P4EYC[[[[^05^<5^8GP1Q3RQ95Q:SQ09PdPUO6b1b2b3DEQ3:eQ0nQ0iI0a+0\GHGHGHGHGHGHGHGHQ;c:0`0VeL0]E=Q07P1EIb9Q2;P1E=b;Q3FNA0jQ;AQ<FP1Q;mQ:HQ7PQ;yQ;mQ:HQ;mQ7PCLdO4b9P3Q7GPDP?Q7G/TDdQ88DWQ9_Q:HQ9_PTQ2KP1Q0LQ:RP|EKW7PTQ2JQ:HPHQ7OD<PTQ021@JkQ99Q2JQ21n0100000020000Q7wPHQ7OD<Q1UQ7QPTPFQ2JQ:HPHQ7Og02Y\Q:6Q<9Q<2p+05?S<2p+05AS7Og02ZfPrg02\0Q7yQ08Q7yQ2xQ7yQ8<Q7yQ8>Q7yp+0:>RdQ7yQ2TQ7yp+0<nQ7yI0@D6D6Q6vQ<9PrEcQ2@eQ2@PkQ60Q9{P[Q8S,M1PVQ08I0=X7kQ5uQ:NQ13Q6u'Q52<X:5Q5F,ykPdQ5uPyPpPpQ8iQ87Q:}P1Q95Q0:O2b1b2b3PyPpPpQ8iQ7@Q:WQ5^b1b2b3K0Kp+07eS5^eQ5^P<Q:NQ9@PxP1PVQ2DI0=X7<Q9{Q;eQ9{Q9@Q2D721W?Q15Q0cQ:N<0EVPFQ7SQ8XQ1}Q8XQ5zQ8XQ8fQ8XQ;oQ8XQ2RQ8XQ;gQ8XQ;bQ8XQ3cQ8XQ1PQ8XFoD6D6D6S8XP0PVQ8kPyPyPpPPPcP}PwP_Q9kP;P_Q:hP;P_P_P`Q9[Q9[Q005a_I0IFCP~PEb4b5b6X05AO1SORdQ7G/08Q0rQ0D<0L3[[^05P1Q94Q0:Q0<O3b1b2b3Q6w@0L0oeQ4xQ7aPoPRQ<QQ1hQ7ap+09US6wPoPoQ:2G3Q8kPyPyPpPPPcP}PwP_Q9kP;Q9[Q;>'UQ005>_CJP~PEb4b5b6X05Q<PQ;^Q9l3O\d^05P1Q94Q0:O2b1b2b3I0zQ4xeQ9JQ2{Q4jQ0qP0DGQ5CQ0}'1PVQ0tQ:iQ:6Q6wQ5ZDrX=@Q3:Q9JQ3WQ9JQ41Q9JQ3WQ64Q80Q5^Q7{Q4MQ9mQ4jQ4aQ4`Q4_PRQ<QQ1hQ7aQ6wQ<XQ<XQ0tG3PRQ<QQ6>Q;iQ85P0P0p+0:GS4`G3EFE8E8Q8kPyPyPpQ:cPcPqPwP_Q9eP;P_Q;MP;P_Q8nP;P_Q6VP_Q6RP_P_Q:TQ:0PzF\ERFCP~PEb4b5b6X05X<5X8GQ7GQ5W5O8S4ap+0G;S5Z,08S:iQ;0/07RdQ<KQ0CP<Q0CPSP<Q4:/4SS4:Q0C;n4Fm[[[^05^<5^8GP1Q4bQ94Q:UQ0:PUQ0oO6b1b2b3DEQ3:eQ2xQ2yQ5CQ0}PVQ:LQ75Q:6Q4jQ6HDrX=@Q3@Q:JQ69Q:JQ3zQ:JQ69Q;tQ;UQ0QQ;vp+07bS:JQ<5Q4iQ4^Q4]Q4\PRQ<QQ1hQ7aQ6wPmPmQ:LG3PRQ<QQ7MQ:PQ8EP0P0Q4`G3EFE8E8Q8kPyPyPpQ:cPcPqPwP_Q9eP;P_Q;MP;P_Q8nP;P_Q7\P_Q7[P_P_Q:TQ:nPzF\ERFCP~PEb4b5b6X05X<5X8GQ4aQ:iQ7G,56S:nQ:nP<Q:nPSP<Q4:Q:nP4EYC[\d[[^05^<5^8GP1Q4_Q94Q:UQ0:PUQ0oO6b1b2b3DEQ3@eQ6SQ6mQ6<PKPVQ7vQ6rQ:6Q4iQ1_DrX=@Q3MQ2eQ68Q2eQ3SQ2eQ68Q9KQ97Q4LQ93Q3vQ8JQ4hQ4[Q1]Q4zPRQ<QQ1hQ7aQ6wPuPuQ6ZG3PRQ<QQ:YQ:VQ<=P0P0Q4`G3EFE8E8Q8kPyPyPpQ:cPcPqPwP_Q9eP;P_Q;MP;P_Q8nP;P_Q7ZP_Q7YP_P_Q:TQ;pPzF\ERFCP~PEb4b5b6X05X<5X8GQ4aQ:iQ2^Q9cP<Q9cPSP<Q4:Q9c;n4Fm\d[[^05^<5^8GP1Q4\Q94Q:UQ0:PUQ0oO6b1b2b3DEQ3MeQ6QQ:kQ6;P^PVQ:EQ2wQ:6Q4hQ5ODrX=@Q2nQ:AQ34Q:Ap+06`S5OQ:AQ34Q6IQ;WQ4KQ8}Q3IQ5lQ4gQ84Q4{Q4uPRQ<QQ1hQ7aQ6wQ65Q65Q:[G3PRQ<QQ:^Q:]Q6JP0P0Q4`G3EFE8E8Q8kPyPyPpQ:cPcPqPwP_Q9eP;P_Q;MP;P_Q8nP;P_Q6gP_Q7QP_P_Q:TQ;EPzF\ERFCP~PEb4b5b6X05X<5X8GQ4aQ:iQ5BQ9RP<Q9RPSP<Q4:Q9R;n4Fm\d[[^05^<5^8GP1Q4zQ94Q:UQ0:PUQ0oO6b1b2b3DEQ2neQ5>Q6ip+05PS2nP]PVQ79Q<aQ:6Q4gQ3_DrX=@Q3KQ6_Q67Q6_Q5tQ6_Q67Q90Q9GQ3tQ6lQ4IQ;nQ4fp+09?S;nQ4qp+09=S6_PRQ<QQ1hQ7aQ6wQ6PQ6PQ:_G3PRQ<QQ;@Q8aQ7|P0P0Q4`G3EFE8E8Q8kPyPyPpQ:cPcPqPwP_Q9eP;P_Q;MP;P_Q8nP;P_Q3CP_Q7lP_P_Q:TQ9iPzF\ERFCP~PEb4b5b6X05X<5X8GQ4aQ:iQ3[Q4kP<Q4kPSP<Q4:Q4k;n4Fm\d[[^05^<5^8GP1Q4uQ94Q:UQ0:PUQ0oO6b1b2b3DEQ3KeQ6TQ7;p+05OS3KQ0SPVQ:7Q:OQ:6Q4fQ1vDrX=@Q3JQ:1Q66Q:1Q3QQ:1Q66Q1kQ5rQ4}Q9<Q3qQ5xQ4eQ4rQ1tp+09:S5xPRQ<QQ1hQ7aQ6wQ:GQ:GQ<ZG3PRQ<QQ<^Q:`Q8|P0P0Q4`G3EFE8E8Q8kPyPyPpQ:cPcPqPwP_Q9eP;P_Q;MP;P_Q8nP;P_Q7dP_Q7]P_P_Q:TQ9yPzF\ERFCP~PEb4b5b6X05X<5X8GQ4aQ:iQ4|Q91P<Q91PSP<Q4:Q91;n4Fm\d[[^05^<5^8GP1Q6_Q94Q:UQ0:PUQ0oO6b1b2b3DEQ3JeQ6OQ;KQ3UQ0VPVQ6XQ5pQ:6Q4eQ1{DrX=@Q2NQ6UQ3OQ6UQ2qQ6UQ3OQ9:Q:aQ56Q9>Q6FQ;sQ4dQ4lQ1DQ4mPRQ<QQ1hQ7aQ6wQ7HQ7HPBG3PRQ<QQ6|Q6jQ:{P0P0Q4`G3EFE8E8Q8kPyPyPpQ:cPcPqPwP_Q9eP;P_Q;MP;P_Q8nP;P_Q7RP_Q<0P_P_Q:TQ:2PzF\ERFCP~PEb4b5b6X05X<5X8GQ4aQ:iQ;^,56S<0Q<0P<Q<0PSP<Q4:Q<0P4EYC[\d[[^05^<5^8GP1Q5xQ94Q:UQ0:PUQ0oO6b1b2b3DEQ2NeQ<TQ6ep+05MS2NQ0aPVQ9xQ5EQ:6Q4dQ6KDrX=@Q3GQ9tQ2pQ9tQ35Q9tQ2pQ7VQ3yQ4GQ76Q3oQ2PQ4cQ4ZQ5<Q4YPRQ<QQ1hQ7aQ6wQ:IQ:IQ01G3PRQ<QQ<?Q:fQ8vP0P0Q4`G3EFE8E8Q8kPyPyPpQ:cPcPqPwP_Q9eP;P_Q;MP;P_Q8nP;P_Q7JP_Q0kP_P_Q:TQ:>PzF\ERFCP~PEb4b5b6X05X<5X8GQ4aQ:iQ<M,56S:>Q:>P<Q:>PSP<Q4:Q:>P4EYC[\d[[^05^<5^8GP1Q4mQ94Q:UQ0:PUQ0oO6b1b2b3DEQ3GeQ7eQ6MQ1XPVQ9nQ6^/4bS6^Q:6Q4cQ6^Q5uEPX=@Q3EQ9hQ33Q9hQ31Q9hQ33Q8yQ8~Q4FQ8{Q52Q::Q4bp+093S4bQ26Q4XPRQ<QQ1hQ7aQ6wQ6YQ6YQ9WG3PRQ<QQ3{Q<EQ8tP0P0Q4`G3EFE8E8Q8kPyPyPpQ:cPcPqPwP_Q9eP;P_Q;MP;P_Q8nP;P_Q6\P_Q7FP_P_Q:TQ9UPzF\ERFCP~PEb4b5b6X05X<5X8GQ4aQ:i156SRpPpP<PpPSP<Q4:PpP4EYC[\d[[^05^<5^8GP1Q4YQ94Q:UQ0:PUQ0oO6b1b2b3DEQ3EeQ18Q0~I0a+0\GHGHGHGHGHGHGHGHQ8X:0`0VeL0]E=Q4sP1EIb9Q1zP1E=b;Q6LNA0jQ;?Q;3P1Q8:Q96Q6nQ;yQ8:Q96Q8:Q6nCLdO4b9Q9_Q;mPDP?Q;m/TDdQ7wDWPkQ96PTQ2HP1P[Q:SQ0;EKX7kPTQ2;Q96Q0LQ:RD<PTQ021@J<p+0CYRUQ2;Q2<n0100000020000Q7wQ0LQ:RD<P|Q6gPTPFQ2;Q96Q0LQ:Rg02]:RdQ<>Q9lPNg02^D&03dg02_NN=1rQ;>Q;6P1Q13PUQ6nQ;yQ13PUQ13Q6nCLdO4b9PkQ8:PDP?Q8:/TDdQ7wDWP<PUPTQ2?P1PxQ:UQ0zEKX7<Q;XQ2DQ;XQ<2Q;XQ5TQ;XQ6}Q;XQ8AQ;Xp+0:@Q;XQ2UQ;Xp+0=0S2UQ;XFoD6D6Q6{P3PrEcQ2<eQ2<Q9]p+05DS6{Q9]PTQ2JQ<DQ2B-0x1p+0C[S2JP]Q:XP\GeW7p+0DZRdQ<2PdQ9APdQ2}PdQ8>PdQ8BPdp+0:APdQ2VPdp+0=1S2VPdFoD6D6p+0A:Q9lPrEcQ2<eQ2<p+0EnS5Tp+05ES:UQ5TPTQ2KQ<9p+05FS;y00x1Q99Q70Q:ZPlGeW7Q5Tp+0G<S<>p+05GS:RQ:R'5S;?'QQ5TPTQ2KQ<9P1Q99Q70Q:ZPlGeW7P5P9PTQ2KQ<9p+0G=S6L/Q1Q99Q70Q:ZPlGeX:5PTQ1ZQ2JP]Q:XD<PTQ02p+0EoS:Z,@JQ;MQ;L60;JQ1ZQ2on0100000020000Q88P]Q:XD<P\Q7[PTPFQ1ZQ2JP]Q:Xg02`XRpQ;MPkP3g02ab&03pg02blN=1qQ;;Q;fP1Q6LQ2JQ7P%NXQ6LQ2JQ6LQ7PCLdO4b9Q5TQ<>Q;uP?Q<>Q;u'TdQ88DWQ:ZQ2JQ:ZPTQ2:P1Q0OQ7SQ0wEKW7Q2~Q88Q2~Q7OQ2~p+05BS;MQ2~Q5SQ2~Q8AQ2~Q8DQ2~p+0:CQ2~Q2XQ2~p+0=3S2XQ2~I0@D6D6D6Q71P<PrEcQ2oeQ2op+0F0S71Q:RQ71PTQ2HPCQ2?-0i1Q:HQ1CQ6MQ0xGeW7Q9UQ7PQ9UQ;MQ9Up+05CS5SQ9UQ5RQ9UQ8BQ9UQ7<Q9Up+0:DQ9UQ2YQ9Up+0=4S8BQ9UI0@D6D6D6Q37PkPrEcQ2oeQ2oQ9dp+05HS37Q9dPTQ2IQ;_Q6a00i1Q9=Q1GQ6eQ3rGeW7PTQ2CQ:HQ1CQ6MD<PTQ2CQ7PPHQ6MD<Q0xQ7_PTPFQ2CQ:HQ1CQ6Mg02d6Q:ZP<Q99PQQ37g02e@Prg02fJQ1HQ2LQ9jp+0>^S2LQ9jQ9pP1Q;YQ9=Q:rI0FW7PmQ9pp+0GAS2CQ<OQ:rH0qX:5Q9jQ9VQ9VPmQ<4Q:GQ8kp+0C?Rpp+0C>RyPyQ8oPPPcP}PwP_Q8oQ2WQ:QH0<P~PEb4b5b6X05Q5T,51S:QQ5WQ;a,51407^05P1Q;KO1S;ab1b2b3L0?Q6?Q0ADDQ9jQ2LQ<4Q74C|eQ1wP1E=b;Q9VQ9AQ9VQ86Q9VQ5SQ9VQ6{Q9VQ5]Q9VQ8CQ9VQ8FQ9Vp+0:EQ9VQ2[Q9VQ6?Q9VFoD6D6D6Q73P<PrEcQ1meQ1mQ9jQ6aQ9jQ9pp+05JS5]721W7Q9jQ6aQ2oP1Fdb;PVQ1MQ1CPQPYPVQ2OQ1MPQP]PVQ0eQ2OPQQ0_PVQ0bQ0ePQQ0uPVQ0hQ0bPQQ0gPVQ18Q0hPQQ0jPVQ1^Q18PQQ0fPVQ1aQ1^PQQ0nPVQ6iQ1aPQQ1TQ6iQ9CPQQ8:PVQ<XQ;XQ2Xp+0=2S8:Q6`PyQ8oQ8oQ8nQ78Q;XP1Q6eP|O2b1b2b3Q8BPIG^Q5KeQ0sQ<XQ7U,01X:5Q6P10m1X:5PyQ8oQ8oQ8nPPPcP}PwQ8nQ:M5>_P~PEb4b5b6X05Q9],51S0sQ;q,51R|'0^05P1Q6eO1S5Kb1b2b3Q9gQ0HDDQ8BPIDDQ8BQ9g'0eQ6PQ<FQ6`5O1X:5Q<XQ;=Q;>80:1X:5Q20Q7~'0Q6>Q7z'0PRQ;6Q20Q6>Q85Q7~Q7zQ2VG3PyQ8oQ8oQ8nPPPcP}PwQ87Q7:5>_P~PEb4b5b6X05P|PSQ0sQ9]C}^05Q5Kb1b2b3Q8BPIG^Q9gQ0HDDQ9gQ5XQ9m3OeN902E;E;E;E;E;E;E;E;E;NB08Q2WQ;lP1p+0G@S;lQ2JQ86Q2m#NS2WQ;lQ2JQ;lQ86CLdO4b9Q9dp+0G?S9mQ;wP?Q9mQ;w'TdQ7PDWQ9jQ2JQ9jPTQ21P1P[Q;KQ0REKW7PTQ1ZQ2JQ0LQ6eD<PTQ1ZQ7wP{Q6eD<Q3rQ7`PTPFQ1ZQ2JQ0LQ6eg02gTQ71Q9EQ96PQQ:9g02h^Prg02ihQ1oQ2MQ9pp+0>_S3rQ9pQ9uP1Q;QQ99Q:rI0FW7PuQ9up+0GBS5XP1Q<MQ:rI0JX:5Q9pQ9XQ9XPuQ<@Q:GQ8lp+0C@R|PpPpPyPPPcP}PwP_PyQ;;Q:KH0<P~PEb4b5b6X05Q:Z,51S9XQ;dQ0I,51407^05P1Q7;O1S5Kb1b2b3L0?p+0=6S0sPWDDQ9pQ3rQ<@Q74C|eQ2:P1E=b;Q1HQ1mQ9pQ:=Q9pQ9uQ:@721W7Q9pQ:=Q2oP1Fdb;PVQ1GQ0LPQPKPVQ0XQ1GPQPLPVQ0YQ0XPQQ70PVQ17Q0YPQQ1MPVQ1WQ17PQQ2OPVQ0iQ1WPQQ0ePVQ1PQ0iPQQ0bPVQ12Q1PPQQ0hPVQ0yQ12PQQ18PVQ:kQ0yPQQ1^Q:kQ2LPQQ13PVPmPdQ8BQ2XQ3gPpPyPyQ8oQ7=PdP1Q;KQ0;O2b1b2b3Q6?Q0AG^Q<WeQ0?PmQ9g,01X:5Q6P10u1X:5PpPyPyQ8oPPPcP}PwQ8oQ9=5>_P~PEb4b5b6X05Q:Q151eRd'0^05Q;ab1b2b3Q85Q0HDDQ6?Q0ADDQ6?Q85'0eQ6PQ;3Q3g5O1X:5PmQ6>Q;C80:1X:5Q;iQ83'0Q0tQ7~'0PRQ<AQ;iQ0tQ80Q83Q7~Q8:G3PpPyPyQ8oPPPcP}PwQ88Q7b5>_P~PEb4b5b6X05PdQ5WQ:QQ5TC}^05Q;ab1b2b3Q6?Q0AG^Q85Q0HDDQ85Q<FQ6`3OeN902E;E;E;E;E;E;E;E;E;E;NB08PsQ<;P1Q2CPUQ6nQ2WQ2CPUQ2CQ6nCLdO4b9Q9jQ;lQ;wP?Q;lQ;w'TdQ7wDWQ9pPUQ9pPTQ2;P1PLQ7;Q1[EKW7PTQ21PUPYQ;KD<PTQ21Q6tPhQ;KD<Q0RQ7:PTPFQ21PUPYQ;Kg02k2Q9dQ:ZQ92PmQ2kg02l<Prg02mFQ1gp+03oS21Q9up+0>`S7:Q9uQ9zP1Q7uQ65C|W7Q65Q9zp+0GCS0RP1Q:gQ65I0JX:5Q9uQ8zQ8zQ85Q6MQ8mQ8HP|P|PpPPPcP}PwQ0kQ:H61B_P~PEb4b5b6X05Q71,51S0kQ5W,51807O^05P1Q6iO1S5Wb1b2b3K1Ap+0=7S7wPWDDQ9uQ5k;2ueQ2<P1E=b;Q8zQ;MQ8zQ6sQ8zQ:UQ8zQ;yQ8zQ5[Q8zQ7<Q8zQ8IQ8zQ4`Q8zQ2GQ8zQ7wQ8zFoD6D6D6Q77Q:ZPrEcQ1meQ1mQ9uQ73Q9uQ9zQ6B721W7PlQ2oP1E=b;PVP[PYPmPiPVQ1EP[PmPnPVQ0TQ1EPmP^PVQ0\Q0TPmQ0OPVQ0^Q0\PmQ0XPVQ1BQ0^PmQ0YPVQ0~Q1BPmQ17PVQ0pQ0~PmQ1WPVQ23Q0pPmQ0iPVQ0vQ23PmQ1PPVQ6mQ0vPmQ12Q6mQ3rPmQ5ZPVPuQ8dQ6?Q8BQ<`P|PpPpPyQ7@Q8dP1Q7;Q0zO2b1b2b3Q0sPWG^Q5PeQ0@PuQ80,01X:5Q7SQ65/01X:5P|PpPpPyPPPcP}PwQ999>_yP~PEb4b5b6X05Q9X151SRd'0^05Q5Kb1b2b3Q7{Q0HDDQ0sPWDDQ0sQ7{'0eQ7SQ;6Q<`5O1X:5PuQ0tQ0080:1X:5Q9JQ9C'0Q<NQ83'0PRQ;rQ9JQ<NQ64Q9CQ83Q2XG3P|PpPpPyPPPcP}PwQ7uQ7c5>_P~PEb4b5b6X05PdQ7GQ9XQ:ZC}^05Q5Kb1b2b3Q0sPWG^Q7{Q0HDDQ7{Q;3Q3g3OeN902E;E;E;E;E;E;E;E;E;E;E;NB08PCQ<HP1Q5Xp+0CWRdQ7uQ2WQ5XPdQ5XQ7uCLdO4b9Q9pQ2CQ;wP?Q2CQ;w'TdQ6tDWQ9uPdQ9uPTQ2HP1PnQ6iPgEKW7PTQ2;PdPKQ7;D<PTQ2;Q7tPfQ7;D<Q1[Q7bPTPFQ2;PdPKQ7;g02nPQ9jPkp+0CVRyQ74Q2dg02oZPrg030dQ22Q29Q9zQ9DQ9zQ9|P1Q;VQ92Q;SI0FW7Q6PQ9|p+0GDS;VP1Q<CQ;SI0JX:5Q9zQ9YQ9YQ6PQ<MQ7HQ8np+0CBS7HQ8HQ8HP|PPPcP}PwP_P|Q;CQ2JH0<P~PEb4b5b6X05Q9d,51Q<@,51807e^05P1Q:kO1b1b2b3L0?p+0=8Q6PQ7HQ8HQ8HP|Q6VQ8nP1Q:kQ0wO2b1b2b3Q7HQ8HQ8HP|Q6RQ8zP1Q:kPlO2b1b2b3K0KQ9zQ9DQ<MQ:rC|eQ2>P1E=b;Q1oQ1mQ9zQ2fQ9zQ9|Q2h721W7Q2_Q2oP1E=b;PVPLPKQ74Q2k@0>LuPVPxPLQ74PhPVQ0`PxQ74PMPVQ0UQ0`Q74PZPVQ0ZQ0UQ74Q1CPVQ1:Q0ZQ74Q0TPVQ11Q1:Q74Q0\PVQ0lQ11Q74Q0^PVQ1TQ0lQ74Q1BPVQ1aQ1TQ74Q0~PVQ1@Q1aQ74Q0pPVQ7eQ1@Q74Q23Q7eQ7:Q74Q<>PVQ65Q2~Q0sQ6?Q6~Q8HP|P|PpQ7AQ2~P1Q6iP\O2b1b2b3Q7wPWG^Q<_ePIQ65Q1;Q:GQ6P/01X:5Q8HP|P|PpPPPcP}PwQ969>_pP~PEb4b5b6X05Q0k151:RI'0^05Q5Wb1b2b3Q64Q0HDDQ7wPWDDQ7wQ64'0eQ:GQ<BQ6~'0X:5Q65Q<NQ;;80:1X:5Q1\Q2L'0p+0>fR\Q9C'0PRQ;fQ1\P\Q9`Q2LQ9CQ8BG3Q8HP|P|PpPPPcP}PwQ6cQ7f5>_P~PEb4b5b6X05PIQ;mQ0kQ71C}^05Q5Wb1b2b3Q7wPWG^Q64Q0HDDQ64Q;6Q<`3OeN902E;E;E;E;E;E;E;E;E;E;E;E;NB08Q;_Q;YP1Q0Rp+0CURIP=Q2WQ0RPIQ0RP=CLdO4b9Q9uQ5XQ;wP?Q5XQ;w'TdQ7tDWQ9zPIQ9zPTQ2IP1PhQ:kQ0}EKW7PTQ2HPIPiQ6iD<PTQ02Q9|,@JQ:TQ2HQ1mn0100000020000Q7qPiQ6iD<PgQ7cPTPFQ2HPIPiQ6ig031nRgPNPNP<g0338&03gg034BN=1oQ;`Q;QP1Q;VPIQ7rQ2WQ;VPIQ;VQ7rCLdO4b9Q9zQ0RQ;wP?Q0RQ;w'TdQ7qDWQ9|PIQ9|PTQ2MP1PKQ6mQ0NEKW7Q1iQ29Q7^p+0DnQ7^PTQ2KP3Q2<-0w1PdPnQ7ePfGeW7Q1iQ21Q:3Q2kQ:3PTp+04ERgQ9_p+0E000w1Q92PMQ<TPiGeW7Q:3Q2kQ:3PTPgQ9_P1Q92PMQ<TPiGeW7PTQ1ZPdPnQ7eD<PTQ02Q:8,@JPyQ1ZQ1in0100000020000Q7sPnQ7eD<PfQ6xPTPFQ1ZPdPnQ7eg035LRiQ9]Q2vQ<Dg036V&03ig037`N=1nQ<LQ;qP1p+0GGRiPyQ7tQ;R#NRgPiPyPiQ7tCLdO4b9Q:3p+0GFR<Q<IP?Q<I,T<dQ7sDWQ:8PyQ:8PTQ1lP1P{Q6OPhEKW7Q9@Q2bQ9@Q37Q9@Q6}Q9@p+05KS6}Q9@p+05LRpQ9@Q1~Q9@Q8MQ9@Q8RQ9@Q5FQ9@Q2cQ9@Q9BQ9@I0@D6D6D6D6Q7DQ<9PrEcQ1ieQ1iQ:<Q3UQ:<PTQ2HQ71Q;00161Q92PYQ6TPKGeW7Q:<Q2]Q:<PTQ2HQ71P1Q92PYQ6TPKGeW7PTQ2>PdP{Q6OD<PTQ2>Q7tP{Q6OD<PhQ3`PTPFQ2>PdP{Q6Og038jQ7^Q9zQ:qg03:4Prg03;>Q9~Q7sQ9~Q2cQ9~Q6aQ9~Q8>Q9~PpQ9~Q2NQ9~Q5`Q9~Q8OQ9~Q8SQ9~Q:NQ9~Q2dQ9~Q3LQ9~FoD6D6D6D6Q6RQ7^PrEcQ1HeQ1HQ:?Q6<Q:?Q1p-1@1$0lW7Q:4Q7tQ:4Q2dQ:4Q5]Q:4Q8@Q:4Q2NQ:4Q3UQ:4Q5_Q:4Q8PQ:4Q8TQ:4Q60Q:4Q2fQ:4p+0=?Q:4FoD6D6D6D6Q6VQ9|PrEcQ1HeQ1HQ:BQ5CQ:BQ4o01@1$0lW7Q5C$1mQ1pP1E=b;Q1pP1E=b;N>1kQ<DP:P1p+0GIR|PdP=PgP|PdP|P=CLdO4b9Q:<p+0GHR\Q<IP?Q<I,T\dQ7tDWQ:?PdQ:?PTQ2@P1PLQ5>PnEKW7PTQ2?PdPYQ6TD<PTQ02Q:B,@JQ:ZQ9f60;JQ2?Q5:n0100000020000Q7sPYQ6TD<PKQ7hPTPFQ2?PdPYQ6Tg03[4RnQ:ZQ:8Q:Mg03\>&03ng03]HN=0OQ<9Q<@P1p+0GJRnPdQ7tPgPnPdPnQ7tCLdO4b9Q:?P|Q<IP?Q<I,T|dQ7sDWQ:BPdQ:BPTQ1oP1P^Q6QPMEKW7Q:9P=Q:9Q2fQ:9Q6}Q:9Q8AQ:9Q3UQ:9Q3KQ:9Q2aQ:9Q8RQ:9Q8UQ:9Q61Q:9Q2hQ:9Q3>Q:9FoD6D6D6D6Q7EQ:<PrEcQ5:eQ5:PDQ9JPTQ2BQ9jQ5LPUPZQ6SP{GeX7DQ:SQ3VQ:Sp+0GLRMQ5Z80f132X:5PDQ:9Q:9Q6OQ5gp+0CDS5gp+0CJRgp+0CIRuPup+0CHRlPPPcP}PwQ:\Q6g61B_P~PEb4b5b6X05Q9m,51Q:8,51Q6L'4'A^05P1Q6SO1b1b2b3K1AQ3>Q:SPgPuPuPlQ7]Q5gP1Q6SPfO2b1b2b3PgPuPuPlQ7RQ:4P1Q6SQ0NO2b1b2b3K0KQ0FeQ0FQ3VQ:SQ3VPTQ1zQ9pP1Q96PjQ6WPYGeW7PTQ2oPUPZQ6SD<PTQ02Q;u,@JQ;EQ2oQ1Hn0100000020000P=PZQ6SD<P{Q7jPTPFQ2oPUPZQ6Sg03CDQ:?Q9uQ92Q:UQ;yg03DNPrg03EXQ:@Q<[Q:@Q7IQ:@Q2jQ:@Q2NQ:@Q8CQ:@Q2nQ:@Q6;Q:@Q2=Q:@Q8TQ:@Q7NQ:@P0Q:@Q2kQ:@p+0=BQ:@I0@D6D6D6D6D6Q6\Q9uPrEcQ1eeQ1eQ;uQ5QQ;uQ:hPHQ8]Q9661G1Q05Q6{I0=W7Q<\Q5Np+0GNS6{Q1380f152XX:5Q;uQ5M'yP0Q<\p+0CLR0p+0CKR{P{PgQ8MQ:dP1Q5{P>O2b1b2b3P0P{P{PgQ7ZQ;4P1Q5{Q0GO2b1b2b3K0KQ4OeQ4OPXQ5NQ:yQ0LP1Q05Q:UI0=X7XQ:hQ10Q:hQ:yQ:U721W?PWQ1OQ1@+15Q5NQ0540EPFQ1OQ1@PvQ05p+0CMRWP0P0P{PPPcP}PwP_Q;{P;P_Q5YP;P_P_P`Q9=Q9==a_NI0IFCP~PEb4b5b6X05AO1|\R`p+0GKRl/08Q9m,47Rf?pfD[[^05P1Q7LP>Q0HO3b1b2b3Q:39pvveQ4zQ1SQ:3PRP:Q98Q1SQ84Q:3Q:3Q9~G3PWP0P0P{PPPcP}PwP_Q;{P;Q9=Q<1'U=>_NCJP~PEb4b5b6X05p+0G>S<1,48Q:B7O2\`^05P1Q7LP>O2b1b2b3I0zQ4zeQ5eQ2jQ:3Q4{Q2jPvEPQ<2/1^PVQ5bQ6e/4bR`Q:8Q84P`Q<bEPX=@Q6EQ5eQ6:Q5eQ3ZQ5eQ6:Q5eQ5eQ5e3~Q9oQ4OQ<[Q5^PRP:Q9ZQ5dQ9QQ:3Q:3Q9~G3Q4{Q4YQ4bQ26PRP:Q98Q1SQ84Q6MQ6MQ5bG3PRP:Q9ZQ5dQ9QPvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q8=Q8<5k_P_P_Q8;Q9lP_P_Q:KQ9ePzI0oI0IERFCP~PEb4b5b6X05X<5X8GAO8lnRnp+0GO,08R`Q:j/07RfQ13,56S13Q13PXQ13P|PXQ5X,4A/42R2Q13P4EYC[[[[^05^<5^8GP1Q5<Q7LQ;|P>PhPKO6b1b2b3DEQ6EeQ2kQ2D-00VQ<2P^PVQ5eQ6S/4bS6SQ:8Q4{Q6SQ<bEPX=@Q5~Q9MQ3WQ9MQ41Q9MQ3WQ9MQ9MQ9M3~Q:5Q4MQ5yQ0QPRP:Q5mQ5iQ6@Q:3Q:3Q9~G3Q4uQ4Xp+090Q4VPRP:Q98Q1SQ84Q6QQ6QQ5oG3PRP:Q5mQ5iQ6@PvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q8AQ8@5k_P_P_Q8>Q9lP_P_Q:KQ9sPzI0oI0IERFCP~PEb4b5b6X05X<5X8G156iS9sQ9sPXQ9sP|PXP2Q9sP4EYC[\f\`\n^05^<5^8GP1Q26Q7LQ;|P>PhPKO6b1b2b3DEQ5~eQ7OQ5S-00VQ5sPZPVQ9MQ;K/4bS9MQ:8Q4uQ9MQ<bEPX=@Q8?Q;=Q69Q;=Q3zQ;=Q69Q;=Q;=Q;=3~Q7UQ:JQ9gQ4LPRP:Q8NQ5wQ5cQ:3Q:3Q9~G3Q;np+08nQ9HQ4TPRP:Q98Q1SQ84Q6eQ6eQ9OG3PRP:Q8NQ5wQ5cPvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q8FQ7<5k_P_P_Q8DQ9lP_P_Q:KQ:0PzI0oI0IERFCP~PEb4b5b6X05X<5X8GQ2C,56S2CQ2CPXQ2CP|PXP2Q2CP4EYC[\f\`\n^05^<5^8GP1Q4VQ7LQ;|P>PhPKO6b1b2b3DEQ8?eQ7lQ:z-00VPpPjPVQ;=Q7;/4bS;=Q:8Q;nQ;=Q<bEPX=@Q3nQ20Q68Q20Q3SQ20Q68Q20Q20Q203~Q85Q3vQ80Q4KPRP:Q9TQ0EQ<dQ:3Q:3Q9~G3Q4qQ55Q4RQ54PRP:Q98Q1SQ84Q;KQ;KQ9PG3PRP:Q9TQ0EQ<dPvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q8LQ8K5k_P_P_Q8IQ9lP_P_Q:KQ2`PzI0oI0IERFCP~PEb4b5b6X05X<5X8GQ5Z,56S5ZQ5ZPXQ5ZP|PXP2Q5ZP4EYC[\f\`\n^05^<5^8GP1Q4TQ7LQ;|P>PhPKO6b1b2b3DEQ3neQ3UQ3a-00VQ5VQ0LPVQ5hQ6i/4bS3nQ:8Q4qQ3nQ<bEPX=@Q3mQ3TQ34Q3TQ5OQ3TQ34Q9\Q<]Q3IQ8yQ3tQ2PQ6_Q53Q4PQ58PRP:Q98Q1SQ84Q7;Q7;Q5hG3PRP:PtQ5nQ8{PvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q7`P_Q7_P_P_Q:KQ;1PzF\ERFCP~PEb4b5b6X05X<5X8GQ<>,56RtPtPXPtP|PXP2PtP4EYC[\f\`\n^05^<5^8GP1Q54Q7LQ;|P>PhPKO6b1b2b3DEQ3meQ2=Q5_p+05`P]PVQ<?Q:k/4bRtQ:8Q6_PtQ<bEPX=@Q3lQ:fQ67Q:fQ5tQ:fQ67Q8sQ7}Q4IQ8qQ4}Q0sQ4rQ4NQ4@Q51PRP:Q98Q1SQ84Q6iQ6iQ<?G3PRP:Q<EQ9WQ82PvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q7oP_Q7nP_P_Q:KQ9?PzF\ERFCP~PEb4b5b6X05X<5X8G156lRlPlPXPlP|PXP2PlP4EYC[\f\`\n^05^<5^8GP1Q58Q7LQ;|P>PhPKO6b1b2b3DEQ3lep+0A1Q6fQ3fQ1EPVQ01Q6m/4bRlQ:8Q4rPlQ<bEPX=@Q3kQ6|Q66Q6|Q3QQ6|Q66Q:{Q8tQ3qQ8vQ56Q2XQ1tQ4Bp+08aQ4?PRP:Q98Q1SQ84Q:kQ:kQ3{G3PRP:Q;2Q<VQ7~PvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q7mP_Q6bP_P_Q:KQ8dPzF\ERFCP~PEb4b5b6X05X<5X8GQ0R,56RlPlPXPlP|PXP2PlP4EYC[\f\`\n^05^<5^8GP1Q51Q7LQ;|P>PhPKO6b1b2b3DEQ3keQ8bQ6oQ63Q0TPVQ6jQ7e/4bRlQ:8Q1tPlQ<bEPX=@Q3jPBQ3OPBQ2qPBQ3OQ7xQ9IQ6FQ81Q4GQ2UQ5xQ1VQ4=Q4JPRP:Q98Q1SQ84Q6mQ6mQ;5G3PRP:Q;9Q;8Q9CPvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q7kP_Q7jP_P_Q:KQ9VPzF\ERFCP~PEb4b5b6X05X<5X8GQ6L,56RlPlPXPlP|PXP2PlP4EYC[\f\`\n^05^<5^8GP1Q4?Q7LQ;|P>PhPKO6b1b2b3DEQ3jeQ6yQ6dQ3dQ0\PVQ<^Q<T/4bRlQ:8Q5xPlQ<bEPX=@Q3iQ:`Q2pQ:`Q35Q:`Q2pQ8EQ6JQ3oQ<=Q4FQ3<Q4lQ49Q4HQ45PRP:Q98Q1SQ84Q7eQ7eQ;:G3PRP:PQQ2QQ3rPvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q6NP_Q7iP_P_Q:KQ9YPzF\ERFCP~PEb4b5b6X05X<5X8GQ;V,56RQPQPXPQP|PXP2PQP4EYC[\f\`\n^05^<5^8GP1Q4JQ7LQ;|P>PhPKO6b1b2b3DEQ3ieQ<RQ<GQ3\Q0^PVQ<ZQ6O/4bRQQ:8Q4lPQQ<bEPX=@Q3hQ;@Q33Q;@Q31Q;@Q33Q;tQ;UQ52Q;vp+07SQ8fQ1DQ50Q42Q4~PRP:Q98Q1SQ84Q<TQ<TQ74G3PRP:Q;SQ:rQ9DPvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q7hP_Q3`P_P_Q:KQ9vPzF\ERFCP~PEb4b5b6X05X<5X8GQ<1,56RQPQPXPQP|PXP2PQP4EYC[\f\`\n^05^<5^8GP1Q45Q7LQ;|P>PhPKO6b1b2b3DEQ3heQ6kQ;ZQ38Q1BPVQ8aQ6T/4bRQQ:8Q1DPQQ<bEPX=@Q3:Q:_Q30Q:_Q32Q:_Q30Q9KQ97Q4DQ93p+07QQ;gQ4mQ3|p+08UQ3uPRP:Q98Q1SQ84Q6OQ6OQ;\G3PRP:Q7KQ;HQ9FPvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q6zP_Q6xP_P_Q:KQ9~PzF\ERFCP~PEb4b5b6X05X<5X8Gp+0GE,56RQPQPXPQP|PXP2PQP4EYC[\f\`\n^05^<5^8GP1Q4~Q7LQ;|P>PhPKO6b1b2b3DEQ3:eQ<YQ;Tp+05ZRQQ0~PVQ:^Q5>/4bRlQ:8Q4mPlQ<bEPX=@Q3@Q:]Q2tQ:]Q2uQ:]Q2tQ6IQ;WQ4CQ8}Q6GQ<SQ4ZQ4EQ0JQ0PPRP:Q98Q1SQ84Q6TQ6TQ7CG3PRP:Q7?Q;[p+0>ePvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q7gP_Q7fP_P_Q:KQ:=PzF\ERFCP~PEb4b5b6X05X<5X8GQ9m,56RlPlPXPlP|PXP2PlP4EYC[\f\`\n^05^<5^8GP1Q3uQ7LQ;|P>PhPKO6b1b2b3DEQ3@eQ6hp+0@dRlQ1TPVQ:[Q6Q/4bRbQ:8Q4ZPbQ<bEPX=@Q3MQ:YQ2rQ:YQ2sQ:YQ2rQ90Q9GQ6CQ6lQ6DQ5}Q5<Q4;p+08OQ47PRP:Q98Q1SQ84Q5>Q5>Q<UG3PRP:PmQ<XQ1\PvPvQ5IG3EFE8E8PWP0P0P{Q;6PcPqPwP_Q;hP;P_P3P;P_Q8wP;P_Q7cP_Q7bP_P_Q:KQ2]PzF\ERFCP~PEb4b5b6X05X<5X8G156|RzPzPXPzP|PXP2PzP4EYC[\f\`\n^05^<5^8GP1Q0PQ7LQ;|P>PhPKO6b1b2b3DEQ3MeQ1`Q0|I0a+0\GHGHGHGHGHGHGHGHGHGHGHGHQ05Q1@60`veL0]E=Q1]P1EIb9Q1HP1E=b;Q;yQ6aQ;G,Z1X:5Q0601NOQ<M%XSQ;<$0S[[Q<MQ03Q06Q7G<1=8UW>Q<MQ03Q:m#X[]>PWP0P0P{PPPcP}PwP_Q;zQ:d5k_P;Q0KQ04$0U61D59a_aCJP~PEb4b5b6X05X8GB0L81\Q:d,Z8[^05^8GP1Q3U$0SQ3UQ5UO3b1b2b3b[b\Q;y,fMQ6aP{PgPgPuPPPcP}PwP_Q<8Q;z5k_P;Q0ICJP~PEb4b5b6X05X8G&0S1RW/18Q0[[^05^8GP1Q6}PpQ0<O3b1b2b3P{PgPgPuPPPcP}PwP_Q;zQ:j5k_P;Q:~CJP~PEb4b5b6X05X8G1Z1<R<,18Q:?,Z8[^05^8GP1&0SpPpQ0<O3b1b2b3K0K+1jNA1iQ9EQ;dP1p+0GMRuPyQ6cQ<I#NROPuPyPuQ6cCLdO4b9Q3VPMQ2mP?Q2m,TMdP=DWQ;uPyQ;uPTQ1gP1PHp+0@_RMPLEKW7Q;uQ:RQ;uPTQ2:PDP1PdPHPMPLGeW7PTQ1lPyPjQ6WD<PTQ021@JXQ:HQ1lQ27n0100000020000Q7tPjQ6WD<PYQ7kPTPFQ1lPyPjQ6Wg03FbRYQ9uQ9uPIg03Gl&03Yg03I6N=0OPoPeP1Q6{PIP=POQ6{PIQ6{P=CLdO4b9Q;uPuQ2mP?Q2m,TudQ7tDWPXPIPTQ1eP1Q0LQ;|P^EKX7XQ:FQ:UQ:FQ;kQ:FQ7uQ:FQ3eQ:FQ3KQ:FQ7<Q:FQ6<Q:FQ5CQ:FQ2SQ:FQ8VQ:FQ8WQ:FQ5vQ:FQ6BQ:FQ7TQ:FFoD6D6D6D6D6Q7JQ9zPrEcQ27eQ27Q;wQ2zQ;wPTQ2MQ7^P1Q6tCzPdP[Q6]PZEKW7PNQ8]P1p+0GPRNQ:uQ6cQ0=#NPNQ:uPNQ6cCLdO4b9Q;wQ:v;2=Q2mQ:uQ2mPTQ21Q:3P1Q92PxQ<:PjGeW7PTQ1gPdP[Q6]D<PTQ02Q<I,@JQ9jQ9l60;JQ1gQ1cn0100000020000P=P[Q6]D<PZQ7nPTPFQ1gPdP[Q6]g03J@RZQ9jQ9lPyg03KJ&03Zg03LTN=0OQ:DQ;^P1p+0GQRZPyQ6cQ;PPZPyPZQ6cCLdO4b9Q2mPNQ;RP?Q;R,TNdP=DWQ<IPyQ<IPTQ1fP1P]Q1OPHEKW7Q9lQ:gP1p+0GRRyQ:pQ6cQ;V#NPyQ:pPyQ6cCLdO4b9Q<IQ:q;2=Q;RQ:pQ;RPTQ1pQ9zP1Q92Q70PlQ0LGeW7PTQ1oPdP]Q1OD<PTQ02Q;7,@JQ9_:0;JXQ1oQ1bn0100000020000P=P]Q1OD<PHQ6[PTPFQ1oPdP]Q1Og03M^RHPXQ:3Q:2g03Nh&03Hg03P2N=0OP3Q<4P1p+0GSR3PdQ6cQ:c#NP3PdP3Q6cCLdO4b9Q;RPyQ;7P?Q;7,TydP=DWQ;7PdQ;7PTQ1cP1Q0OQ;TP[EKW7Q;0P=Q;0Q7tQ;0Q5]Q;0Q5aQ;0Q7PQ;0Q2lQ;0Q4oQ;0Q8LQ;0Q3aQ;0Q62Q;0Q2YQ;0Q8YQ;0Q8\Q;0Q1SQ;0Q08Q;0Q7{Q;0FoD6D6D6D6D6D6Q7lQ:8PrEcQ1beQ1bQ:cQ7;Q:cPTQ1iQ<IP1Q8cCzPUQ1CQ;ZPxEKW7Q:cQ7;Q:cPTQ1iQ<IP1PUQ1CQ;ZPxGeW7PTQ5:Q92Q0OQ;TD<PTQ02Q:b,@JQ;4Q5:Q1jn0100000020000Q7tQ0OQ;TD<P[Q7pPTPFQ5:Q92Q0OQ;Tg03Q<R[Q;wQ:?Q:;g03RF&03[g03SPN=0OPkPSP1p+0GURSQ:mP=%N|PSQ:mPSP=CLdO4b9Q:cp+0GTRSP\P?1TS\dQ7tDWQ:bQ:mQ:bPTQ1|P1Q1GQ<GP]EKW7Q:}Q<[Q:}Q7IQ:}Q6cQ:}PpQ:}Q2iQ:}Q87Q:}Q2DQ:}Q6qQ:}Q8OQ:}Q3bQ:}PQQ:}Q2AQ:}Q8[Q:}Q8^Q:}Q5JQ:}Q<2Q:}Q85Q:}I0@D6D6D6D6D6D6D6Q7QQ:BPrEcQ1jeQ1jQ3YQ;<Q3YPTQ1gQ;RP1Q8eCzQ:jQ1EQ6dQ70EKW7Q3YQ;<Q3YPTQ1gQ;RP1Q:jQ1EQ6dQ70GeW721hF]Q;</M9Q;<$0nE=Q1cP1E=b;P=P1EIb9EVQ7;/M9Q7;$0nE=Q1fP1E=b;Q6cP1EIb9EVQ6cP1EIb9Q6cP1EIb9EVQ6cP1EIb9Q5:P1E=b;P=P1EIb9EVQ:UQ5]P0P{P{PgPPPcP}PwP_Q<8Q:j5k_P;P_Q0IQ:jERP~PEb4b5b6X0511W<Q0[@0L8i[^05P1Q2NQ0>O2b1b2b3+1fE=Q6cP1EIb9EVQ::P1EIb9Q1pP1E=b;Q7tP1EIb9EVP=P1EIb9EVQ2]Q3U+16Q6;$1gE=Q29P1E=b;Q7tP1EIb9EVp+0DoQ2k+0wQ2k$1eE=Q2<P1E=b;Q2>P1E=b;Q7rP1EIb9EVP=P1EIb9EVQ7uP1EIb9EVQ6nP1EIb9EVQ86P1EIb9EVQ2?P1E=b;Q2?P1E=b;Q7PP1EIb9EVQ;?Q:R$1dE=Q:UQ:U+0xQ:RQ:RQ8mQ8lQ8lQ8kPPPcP}PwP_Q<7Q;z5k_P;P_Q<7A>_aaERP~PEb4b5b6X05X8G21718Q0[1088'1[^05^8GP1Q6aQ5]Q3PO3b1b2b3Q8mQ8lQ8lQ8kPPPcP}PwP_Q;zQ9q5k_P;Q9qCJP~PEb4b5b6X05X8GQ9_:0L811Z8k[^05^8GP1Q5]#XQ5]Q3PO3b1b2b3H1lE=Q2BP1E=b;Q2BP1E=b;Q6nP1EIb9EVQ6nP1EIb9EVQ7PP1EIb9EVQ89P1EIb9EVQ8;P1EIb9EVQ8=P1EIb9EVQ8=P1EIb9Q8=P1EIb9EVQ6yQ0]E=Q6y/M9Q6y$0nE=Q5[P1E=b;Q8<P1EIb9EVQ6hQ0GE=Q6h/M9Q6h$0nE=Q<<P1E=b;Q8;P1EIb9EVQ8>P1EIb9EVQ8CP1EIb9EVQ8FP1EIb9EVQ8KP1EIb9EVQ8OP1EIb9EVQ8SP1EIb9EVQ8VP1EIb9EVQ8ZP1EIb9EVQ;NP1EIb9Q1OQ0BE=Q8_P1EIb9EVQ1uQ1XQ1qQ1OQ:jPrCbQ1ueQ1uPsQ:2Q2492C1X7sPsQ:2Q1sP1Fdb;Q0|Q1=Q1qQ1OQ;;PrCbQ0|eQ0|PsQ2aQ2Z92C1X7sPsQ2aQ1AP1Fdb;Q4pQ0jQ1qQ1OQ00PrCbQ4peQ4pPsPBQ8JQ;]Q2FP1E=b;Q1NQ0bQ1qQ1OQ;CPrCbQ1NeQ1NPsQ9aQ7AQ7@Q1LP1E=b;Q1>Q1WQ1qQ1OQ;LPrCbQ1>eQ1>PsQ;NQ;U92C1X7sPsQ;NQ1?P1Fdb;Q1YQ1BQ1qQ1OQ5YPrCbQ1YeQ1YPsQ5\Q2}Q2|Q1yP1E=b;Q0{Q11Q1qQ1OQ;BPrCbQ0{eQ0{PsQ57Q<692C1X7sPsQ57Q4vP1Fdb;Q1@Q0cQ1qQ1OQ;OPrCbQ1@eQ1@PsQ9aQ7AQ7@Q1<P1E=b;Q0vQ0dQ1qQ1OQ;DPrCbQ0veQ0vPsPBQ8JQ;]Q1xP1E=b;Q0yQ0fQ1qQ1OQ:dPrCbQ0yeQ0yPsQ9wQ9a92C1X7sPsQ9wQ1rP1Fdb;Q1aQ0hQ1qQ1OQ:oPrCbQ1aeQ1aPsQ5\Q2}Q2|Q19P1E=b;Q23Q0iQ1qQ1OQ:lPrCbQ23eQ23PsQ7eQ<T92C1X7sPsQ7eQ1RP1Fdb;Q12Q0~Q1qQ1OQ:mPrCbQ12eQ12PsQ6mQ7e92C1X7sPsQ6mQ1KP1Fdb;Q1^Q0lQ1qQ1OQ;<PrCbQ1^eQ1^PsQ:kQ6m92C1X7sPsQ:kQ16P1Fdb;Q1TQ0mQ1qQ1OQ;GPrCbQ1TeQ1TPsQ6iQ:k92C1X7sPsQ6iQ1nP1Fdb;Q0pQ0nQ1qQ1OQ;IPrCbQ0peQ0pPsQ7;Q6i92C1X7sPsQ7;Q1JP1Fdb;Q1PQ18Q1qQ1OQ:pPrCbQ1PeQ1PPsQ;KQ7;92C1X7sPsQ;KQ14P1Fdb;Q1qQ1OQ:qPrCbQ18eQ18PsQ6eQ;K92C1X7sPsQ6eQ1dP1Fdb;K0HK0HK0HK0HK0HK0HK0HK0HK0HH1cQ:tQ:tQ74PTP1Q24Q0^Q:rD<+0gQ;J'1WA+11ebSWVWZWFWNWOP8P1O2n2001000000121000000W9WGWHWIWLWMPAP6P7P8P1O5n700000001000000151104103102101100W9WJWKWWaaaaaaaaaaaaaaaaaaaaaaaaaaWXWYWTWRWQWPWUaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW_W^W]aaaaaaaaaaaaaaaaaaaaaWbaaaaWgaaaaaaaXa5aaaaaaaaaaaaaXi5aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaX`5aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaXh5aWfaaaWcaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWdaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.
End FPX_1.


(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0StdioWrite_run1.
Module Ns0StdioWrite_run2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.LibAtomic OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioWrite_run1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4b000_4c000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4e000_4f000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Ns0StdioWrite_run2 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01058SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run2;sw_regs_butC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC59OSSVerify5KrLib7Mh_00387SeqExec=step_jal_linkC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions4BvWfC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6shiftlC49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_luiC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C49OSSVerify5KrLib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:step_addiwC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib7Mh_00387WalkTac=wf_getr_chainC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<step_bltu_tkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec<step_jalr_x0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4c_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:SumWalkTac9c_eq_reflC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_bne_ftC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z2leI59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae524C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae524C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae524C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9454C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9454C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9454C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9458C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9458C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9458C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a945cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a945cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a945cC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9488C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9488C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9488C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae528C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae528C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae528C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib7Mh_0055:SumWalkTac6c_eq_ZC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_bne_tkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C49OSSVerify5KrLib8PropExec9step_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_ae5b4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
  /\ getr regs' 21 = getr regs 21
  /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
  /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
  /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

Lemma sw_c1_eq : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xae560 : word) mem rom) (mkst regs' (0xae568 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite_run2 ()) ["FPX_1"] "h01bh11Hh22gHh34__p1h44__x1h57__arithh64__ffh78__varmaph85__with91nh:2Hah;6__sat7h<6__sat8h=2b1h>2b2h?1mh@1zhA3Ha0hB3Hs6hC1KhD1khE3memhF4regshG5regs'hH3romp%0p&0p;1p;2p;5p;3p;<p;=p;4p;6p;>p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004`R0p4p710R1p8p1005>p4p710P1p8g005]j10Tg006Bj12Tg006gj1RTg007Ej1OTg007hk20MTg008Tj1sTg0096j2?Tg009\j2>Tg00:8R1j28Tg00:Sj56Tg00;Ej21Tg00<7j2qTg00=Bj1LTg00=`j33Tg00>Tj34Tg00>nj3ETg00?Qj3wTg00@>j2]Tg00A2j2ZTg00AZj2oTg00BLj1zTg00Bnj2PTg00CHj1nTg00DHm<0OTg00EJk30NTg00Enj2YTg00FQj2TTg00G;j2yTg00G[j1xTg00HNm<0LTg00IDk10KTg00Ibj2eTg00JWm=0HTg00KOk20GTg00Koj4mTg00LOj1uTg00Loj3lTg00MOj45Tg00NQj2dTg00ODj2kTg00Oak20FTg00PAk10ETg00Pak20DTg00Q?k10CTg00Q]k10BTg00RHk60ATg00Rlk20@Tg00SOj2cTg00T2k20>Tg00TTk20=Tg00U@k30<Tg00U_k40;Tg00VQk10:Tg00Voj4hTg00WZk208Tg00XBk207Tg00X_k306Tg00YCk305Tg00Yfj3pTP0j6JTg00Zam>04Tg00[[j2iTg00\Vm>09Tg00]Wj2`Tg00^Ik102Tg00_Jm>01Tg00`Ck20?Tg00a?j6GTg00a[j4^Tg00b6j4~Tg00bPj2}Tg00blj3vTg00chj7|Tg00dLk70ITg00e0j8{Tg00eTk70JTf0R0#0#0p=Uf1R2%L0g00fPR33Ep=7f3R4f2R5/12;40p=@g00flR6/}0p=I%00#0#0#0p=D%00#Lp=K%20#0p=<%20#2p=H%00#2p=f%00#2#0#2p=S%00#0#2#0p=F%00#2#0#0p=tAE203p=Cg00gJR7f5R8f4R9P4P5P2D6;v0p=A1820,85p=[%20#2#2#2p=a%20#2#2#2#2#2#2#2p=_A3945?320p=BAv720p>0011451120549p=9g00i3R:1T451T2034p=N1P:0p=Mf6R;A3894P5P2P0D6p=\1T2094:5p=gg00iQR<g00j1S00740p==P:P2g00jQP0Chp=bP2g00k8R=g00kWR>P>g00l7R?P0g00lWF|p=XP5P=P>P>P?P2P0K0Ip=rP4P=P>P>P?P5P2P0G{p=jP;P8P9P41152P0EJp=VA4:20p>03P7P8P9P4P5P2P0K0Jp=W11209445p=:f7R@P;P81P941152P0EJp=;P;P8P9P4P5P2P0C^C^p=Qg00m7RA#0RB#2RC#RRD%0BRE#0RF#0#URG#RRH#ORI+0MRJ%RF#O#s\IS01Q01PIP4%0CRK,7DRL1?H0C@PIP9%2CRC#0RM,7DRN1?H2C@%I5%DG#D#D#D#D#D#KRO,>5'8PJp,2fxRPP@%0A#<#H#<#f#S#<#D,7HRQP;P8PPP0%SA#H#F#<#H#t#KRR,CHRSP;P8D6EAPIP0PL1?H9C@PIP0%2ERT#2,7DRU11@US02C@PIP0%0KRV,7DRW11@WS03C@PIP0%0TS04,7DRX11@XS05C@PIP0PN11@NS06C@1q@03[3[3[XGJ%LARY,CDRZ%SA#H#F#<#H#F#KR[,?HR\53;17DCR]%2AR^#aR_#H#a#_R`#2#H#a#_#_#_#<#U#D#DRa#KRb,?HRcP]%2a#LRa,?HRdDBRePPP;PQP8P9D6RfPPPePSP8P9D6Rg+0011eLS071?H454IS08PIPePUP;PUD9RhPIPePWP;PWD9RiPIPePXP;PXD9RjPIPePNP;PND9Rk1q;e'83[3[S09PfPPP<PJAED63Rf9wDZP;%LERE,]QRl93;Zn0100000020000%2KS0:#RRK%0_#<#a#U#H#D,7KRK'Z,oQR_P8P9D6Pg%sI%zI'PRgPPP7P;PQP8P9g00m\RQPZPKg00nf%nQ,P<g0100N<0Og011:RQ%O0RK%O2RmP1%O5?420P4P5P4P2CNRn[P5P2P5P0CN%O4?452[Ro%O9?445\nB0N520P0n2001000000120000000W>W=W9RnPo^>m^=K^9QRQP0PH%SA#F#<#f#F#U#KRK,CHRmP_%MKPHPmPHP_CNdO4b1P31YHKd9EHK=4I_PIPmPPf8RK?3ZlP0P@P;PPA3KZ\Ro?3]cP]PdPSP@P;F\R9EAX0IPnPQP0PHP\Pl%M[Rp1TH\S0;?gHldO4b1A4I\lPIP\PPf9Rq?3Z0PmPKP@PPPqPZP\P]PcDBP]PdPSPKP@F\EAX0IPPPoPmP@P;D6PPP<PJAwD]fRfPo%RVRV17V`RV'Z%0^R`#0Rr#LRs'y#xRt93o]n01000000200001]mERuP@P;D6P9PgPPP7PoPmP@P;g011XRmP]PVg012b%nm,P<g013lN<0LPnPQP0PH%SA#F#<#f#F#<#KRm,CHRVPu%MmPHPVPHPuCNdO4b1P31YHmd9EHm=4IuPIPVPPf:Rm?3Z\Ro?3]tP0PqPKPPA3o]cRoP]PdPSPqPKF\RtEAX0IPnPQP0PHPc&0KA/ys#xRs%MbPHPcPHPsCNdO4b1A4IcsPIPcPPf;Rb?3Z\R9?3]0PVPmPqPPA39]cR9P]PdPSPmPqF\EAX0IPPPoPVPqPKD6PPP<PJPfPo11o]%RrRf1CfYRJ'ZRv'e93o]n01000000200011]VERwPqPKD6PtPgPPP7PoPVPqPKg0156RqP]P]PJg016@%nq,P<g017JN=0HPnPQP0PH%SA#F#<#t#H#U#KRq,CHRJPw%MqPHPJPHPwCNdO4b1P31YHqd9EHq=4IwPIPJPPf<RqPZP\P]PcDBRV11V]S0</ev73]P0PbPmPPPVP]PdPSPbPmF\EAX0I%ODRm00GIRVPmPIP]PcCmPmPIPZP\Cm%uV5lV3lRoPbP]g018T,P<RtC5PIP9P]PcC@R9eP9PIPcPPf=R9PZP\P]PcDBRx1e0v73]PJPqPbPPA3x]dRxPSPqPbD6RvEAX0IPnPQP0PHPd1ecYRY%Ma1THdRy?gHYdO4b1A4IdYPIPdPPf>RzPZP\P]PcDBR{?3]0PJP9PqPPA3{]dR{PSP9PqD6S0=EAX0IPPPxPJPqPbD6PPPx%2`R`#RR|%0M,7|RM'Z,oJR}PqPbD6PvPgPPP7PxPJPqPbg0194PLP]PMg01:>Ptg01;HPmPIP]PdCm=lVoRoP9PLPtC5PIPxPLP9PLD9RxePxPI11zLf?Rx?3Z\P]PcP]PdDBRV/1]S0>,d0#=X0IPoPzP]PtC5PIP{P]PdC@RmePmPIPdf@Rm/1LS0?/d0#=X0IPI1?HqS0@1d0d#=X0IP11k20#=1>52R1[1>201k52#=[RM1k45#=\120F20P0n2001000000120000000X?:X9:PM^?:^9:P01?H9,THS0APyP:P91>0yX@:P:Pa1>z0X@:p-0RMg01<RR1#uRJ&0E1R120D:2S0B&0C:Rv&0B:R~P~P=P>P>P?P4J0AS0C20@:AR=1c:O'b,X~5r~S0D%z>S0E1c:aR>,b=,X~Cj20>~?R?P0P5Q00,P<20=05#=dB0<:62H0;R5b6b7b8X4:W31>0O,82S001>2a[^4:^3MP0%IzPzPbO3b5PyPJP1&0::S0FPvP:1c:6S0Gg01=>S0HP>Ch,X~P?P5b6b7b8%IaP0b5%LBRB%LGRG+08S0I1>6B%IG207BGRy,>6[[S0J%IBS0Kg01=eR<B06BG2UW:S0LQ0K%Iy\<]:R<PJP1Q0FPv1c:B>05:HRG,b>,X~P?P5b6b7b81>ayP0b5b;b<5paEJQ0APJP1Q0BPvP~P:Q0GQ0HP=Ch,X~RaQ0C5r~Q0EPaCjP?P5b6b7b8X4:X3M%I0/82%I2[^4:^3MP01>zOPzPbO3b5Q0IQ0JQ0LP<PJP1Q0BPvP~Q0DQ0E1b=G,X~CjP?P5b6b7b8X4:X3MQ001>2y[^4:^3MP0%ImPmP9O3b5b;b<5p9EJO3b1Q0@/dd#=ePxPLPbFVQ0>P0EJb2P{PLP0FVb2N>04PnPQP0PH%SA#F#<#f#<#F#KRA,CHRbP}%MAPHPbPHP}CNdO4b1P31YHAd9EHA=4I}PIPbPPPVP0PzP9PPPVPSPzP9D6EAX0IPPP{PbP9PqD6PPP{1CH[RAAEf63RM,Zf'iRfP9PqD6Q0=PgPPP7P{PbP9Pqg01>APZPMPAg01?KPtg01@UPoPzPZPtC5PIP{PZP\C@R{eP{PIP\A4I0AX0IPnPQP0PHP\PAPpQ0;1THAR{+03dO4b1PVPZP0FVb2N>09PnPQP0PHPAPfPpAg{HfdO4b1P31YH[d9EH[R[=4IfPIPAPPA3mZ\P]PcP]PdDBRVP0PxPzPPPVPSPxPzD6RMEAX0IPnPQP0PHPA1iA6RqPpAg{HqdO4b1PAPIe/i694I[PPPVPAPxPzD6PPPV1]AER[PxPzD6PMPgPPP7PVPAPxPzg01A_PLPNQ04#0#U,7|g01BiPtg01D3PoPmPLPtC5PIPVPLQ0?C@RVePVPIfARV/1LfBR|?3Z\P]PcP]PdDBRA/1NRg,`0#=X0IPoPVPNPtC5PIA3VZ\P]PcP]PdDBRMPNPVPND9R6eP6PI11|NR6fCRq/1L/`0#=X0IPI1?HxR{11qN,`0#=X0IPIP{1?Hm/`0#=X0I&02{P6P9EJP|PLPzFVPgP0EJb2PMPLP0FVb2N>01PnPQP0PHPSP[%MRPHPSPHP[CNdO4b1P31YHRd9EHR=4I[PIPSPPPAP0PVPmPPPAPSPVPmD6EAX0IPPPMPSPmPxD6-0?7P[P0EGb1EWb1PfP0EGb1EWP}P0EGb1EWPYP0EGb1Q0<P0EJb2PwP0EGb1EWPsP0EGb1PuP0EGb1EWPlP0EGb1P_P0EGb1EWQ08PIPe1CDBRBP;PBD9R_PIPe17DFRFP;PFD9RlPIPe17DTRTP;PTD9RuPIPeQ0:,7DRsP;PsD9RwPIPe17D^R^P;P^D9RYPIPe1CDEREP;PED9R}PIPe%2C,7DRCP;PCD9RfPIPe%0r,7DR[P;P[D9R7PIPe%2r,7DRrP;PrD9RxPIPe%0`,7DRmP;PmD9RSPIPe%2`,7DRDP;PDD9R`'8Re'8RM'8RP'8RV'8RA'8RR'8R3'8RQ'8Rn'8Rg,8kRz,8jR|,8iR9,8hPoP;PLPtC5PIQ07P;PLC:R6eP6PI11@L1?H894I0X0IP4A3@Z\P]PcP]PdDBRdPLP0FVb2PhP9PoP;PUPtC5PhePhPIQ02PIP0PKPUC:X0IPIQ02PdPUP0G;b2PiP|PoP;PWPtC5PiePiPIQ03PIP0PKPWC:X0IPIQ03PdPWP0G;b2PjPzPoP;PXPtC5PjePjPIQ05PIP0PKPXC:X0IPIQ05PdPXP0G;b2PkPgPoP;PNPtC5PkePkPIQ06PIP0PKPNC:X0IPIQ06PdPNP0G;b2P_PnPoP;PBPtC5P_eP_PI11@BR_PIP0PKPBC:X0IPIP_PdPBP0G;b2PlPQPoP;PFPtC5PlePlPI11@FRlPIP0PKPFC:X0IPIPlPdPFP0G;b2PuP3PoP;PTPtC5PuePuPI11@TRuPIP0PKPTC:X0IPIPuPdPTP0G;b2PwPRPoP;PsPtC5PwePwPI11@sRwPIP0PKPsC:X0IPIPwPdPsP0G;b2PYPAPoP;P^PtC5PYePYPI11@^RYPIP0PKP^C:X0IPIPYPdP^P0G;b2P}PVPoP;PEPtC5P}eP}PI11@ER}PIP0PKPEC:X0IPIP}PdPEP0G;b2PfPPPoP;PCPtC5PfePfPI11@CRfPIP0PKPCC:X0IPIPfPdPCP0G;b2P7PMPoP;P[PtC5P7eP7PI11@[R7PIP0PKP[C:X0IPIP7PdP[P0G;b2PxPePoP;PrPtC5PxePxPI11@rRxPIP0PKPrC:X0IPIPxPdPrP0G;b2PSP`PoP;PmPtC5PSePSPI11@mRSPIP0PKPmC:X0IPIPSPdPmP0G;b2PoP;PDPtC5P`eP`PI11@DR@PIP0PKPDC:X0IPIP@PdPDP0G;b2C^FQFQFQFQFQFQFQQ09eC^C~WCWBWAXD:WHWEWFo"). Qed.

Lemma sw_c1_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0xae560 : word) mem rom) (mkst regs' (0xae5f4 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite_run2 ()) ["FPX_1"] "h01bh11Hh22gHh34__x1h47__arithh54__ffh66__sat7h76__sat8h88__varmaph95__with:4__p1h;1nh<2Hah=4__x2h>2b1h?2b2h@1mhA1xhB1yhC1zhD3Ha0hE3Hs6hF1KhG2NEhH3REMhI1khJ3memhK4regshL5regs'hM3remhN3romp%0p&0p;1p;2p;5p;3p;<p;=p;4p;6p;>p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004`R0p4p710R1p8p1005>p4p710P1p8g005]j12Tg006Bj11Tg006gj1WTg007Ej1QTg007hk20WTg008Tj1{Tg0096j2>Tg009\j2=Tg00:8S00j25Tg00=Bj1JTg00XBk20VTg01E=j1qTg00:Sj57Tg00;Ej20Tg00<7j2wTg00=`j33Tg00>Tj34Tg00>nj3BTg00?Qj3}Tg00@>j2rTg00A2j2]Tg00AZj2tTg00BLk101Tg00Bnj2PTg00CHj1sTg00DHm<0YTg00EJk30XTg00Enj2\Tg00FQj2VTg00G;k200Tg00G[j1~Tg00HNm<0STg00IDk10RTg00Ibj2lTg00JWm=0QTg00KOk20PTg00Koj4pTg00LOj1zTg00Loj3kTg00MOj46Tg00NQj2jTg00ODj2oTg00Oak20OTg00WZk20NTg00X_k30MTg00PAk10LTg00Paj2yTg00Q?k10KTg00Q]k10JTg00RHk60ITg00Rlj2xTg00SOj2iTg00T2k20BTg00TTk20ATg00U@k30@Tg00U_k40?Tg00VQk10>Tg00Voj4eTg00YCk30=Tg00Yfj3vTP0j6FTg00Zam>0<Tg00[[j2nTg00\Vm>0;Tg00]Wj2^Tg01EVj2dTg01F3k20:Tg01FTk109Tg01G3j2uTg01G\k208Tg01H=k30CTg01Hfk30DTg01IOk206Tg01J;k40ETg01JYk60FTg01K=k405Tg01L;m>0GTg00`Ck20HTg00a?j6GTg00a[j4cTg00b6k404Tg00bPk203Tg00blj3|Tg00chk702Tg00dLk70TTg00e0k80UTg00eTk70ZTf0R0#2#2p=Rf1R1%J0g00fPR23Bp=8f3R3f2R4/01;40p=@g00flR50030p=H%20#2#2#2p=E%20#Jp=Ng00i3R6?410p=X%10#2p=<%10#1p=M%20#1p=a%20#1#2#1p=S%20#2#1#2p=D%10#1#1#1p=`AB102p=Cg00gJR7f5R8f4R9P3P4P1D7;|0p=?1510,54p=_%10#1#1#1#1#1#1#1p=fA3934?310p=AA|710p>0710341010549p=91V341V10546p=O1P60p=Kf6R:A3893P4P1P0D7p=b1V109464p=mg00iQR;g00j1R<740p=LP6P1g00jQP0Cep=hP1g00k8S01g00kWR=P=g00l7R>P0g00lWK02p=UP4Q01P=P=P>P1P0K0Tp=gP3Q01P=P=P>P4P1P0L0Up=[P:P8P9P31041P0EFp=Zg018TR?94;0p=IP7P8P9P3P4P1P0K0Zp=Y10109434p=:f7R@P:P81P931041P0EFp=;P:P8P9P3P4P1P0CcCcp=Tg00m7RA#2RB#1RC#WRD%2BRE#2S02#2#RRF#WRG#QRH+0WRIQ02#W#Q#{\HS03Q03PHP9%2CRJ,8DRK1>G1RLC@PHP8%1CS04#2RC,8DRMPLC@%H3RL%EF#E#E#E#E#E#NRN,=3'5%JBRO%JFRF+0VRP,=3,5L1X89#qPIp,2fxRLf:RQ%2A#<#M#<#a#S#<#E,8GRRf9RSf8RTPLP0%SA#M#D#`#<#<#NRU,CGRVPSPTD7E?PHP0PK1>G@C@PHP0%1ES05#1,8DRW10QWS06C@PHP0%2JRX,8DRY10QYS07C@PHP0Q05#2S08,8DRZ10QZS09C@PHP0PM10QMS0:C@1wQ03_3_3_XLI%JAR[,CDR\%SA#M#D#<#M#D#NR],>GR^53SQ04,8DR_%1AS0;#`R`#M#`#fRa#1#M#`#f#f#f#<#R#E#ERb#NRc,>GRdP_%1b#JRb,>GReDARfPLPSPRPTP@D7RgPLPfPVPTP@D7Rh+0710fKS0<1>G:54HS0=PHPfPWPSPWD9R:PHPfPYPSPYD9RiPHPfPZPSPZD9RjPHPfPMPSPMD9Rk1wSf'53_3_S0>PgPLP;PIABD52Rg9}D\PS%JERE,rRRl93S\n0100000020000%1JS0?#WRJ%2`#<#`#R#M#E,8JRJ'],tRR`PTP@D7Ph%{H&01H'PRhPLP7PSPRPTP@g00m\R@P\PJg00nf%s@,P;g0100N<0Yg011:R@%Q0RJ%Q1RRQ00%Q4?410P3P4P3P1CORm[P4P1P4P0CO%Q3?441[Rn%Q9?434\mB0X410P0n2001000000120000000W?W>W;RmPn^?R^>J^;@R@P0PG%SA#D#<#a#D#R#NRJ,CGRRP`%KJPGPRPGP`COdO4b1P21\GJd9BGJ=4H`PHPRPLf;RJ?3\lP0PQPSPLA3J\^Rn?3_dP_PePVPQPSFbR9E?X0HPmP@P0PGP^Pl%K]S0@1VG^S0A?mGldO4b1A4H^lPHP^PLf<Ro?3\0PRPJPQPLPoP\P^P_PdDAP_PePVPJPQFbE?X0HPLPnPRPQPSD7PLP;PIA}D_gRgPn%WXRX18XaRX']Q0;#2Ra#2Rp#JRq+00#~Rr93n_n01000000200001rRERsPQPSD7P9PhPLP7PnPRPQPSg011XRRP_PXg012b%sR,P;g013lN<0SPmP@P0PG%SA#D#<#a#D#<#NRR,CGRXPs%KRPGPXPGPsCOdO4b1P21\GRd9BGR=4HsPHPXPLf=RR?3\^Rn?3_rP0PoPJPLA3n_dRnP_PePVPoPJFbRrE?X0HPmP@P0PGPd&0RAS0B000q#~S0C%KcPGPdPGQ0CCOdO4b1Q0C94HdPHPdPLf>Rc?3\^Rq?3_0PXPRPoPLA3q_dRqP_PePVPRPoFbE?X0HPLPnPXPoPJD7PLP;PIPgPn10n_%WpRg1Cg[RI']R9'l93n_n01000000200011rXERtPoPJD7PrPhPLP7PnPXPoPJg0156RoP_P_PIg016@%so,P;g017JN=0QPmP@P0PG%SA#D#<#a#R#M#R#NRo,CGRIPt%KoPGPIPGPtCOdO4b1P21\God9BGo=4HtPHPIPLf?RoP\P^P_PdDARX10X_S0D/l973_P0PcPRPLPXP_PePVPcPRFbE?X0H%QDRX00PHRnPXPHP_PdCpPXPHP\P^Cp%zn5kn3kRrPcP_1P;?R?C6PHPqP_PdC@RqePqPHPdPLf@RqP\P^P_PdDARu1l0973_PIPoPcPLA3u_eRuPVPoPcD7R9E?X0HPmP@P0PGPe1ld[R[%Kb1VGeS0E?mG[dO4b1A4He[PHPePLfARvP\P^P_PdDARw?3_0PIPqPoPLA3w_eRwPVPqPoD7S0FE?X0HPLPuPIPoPcD7PLPu%1aS0G#WRa%2C,8aRC'],tIRxPoPcD7P9PhPLP7PuPIPoPcg0194PKP_PCg01:>P?g01;HPXPHP_PeCp=knrRrPqPKP?C6PHPuPKPqPKD9RuePuPH10vKfBRu?3\^P_PdP_PeDAS0H/0_S0I,j0#LX0HPrPvP_P?C6PHPwP_PeC@RnePnPHPefCRn/0KS0J/j0#LX0HPH1>GoS0K1j0e#LX0HQ001o10#L1=41RX[1=101o41#L[RC1o34#L\X20O10P0n2001000000120000000X@6X;6PC^@6^;6P01>Gq,VGS0LQ0EP6PqQ0E,=0XC6P6Pb1=v0XC620NOFRC1=5O%HF1=5P[[RX%HORcg01=eRIB0MOF1UW<RF%HP\I^<cRcp-0RIg01<RS0M#zR9Q0M$0LRy1y61S0N&0K6Rz&0J6R{P{Q01P=P=P>P3J0IS0O1x6AR|1i6N'h,U{S0P5g{S0Q&01=R}1i6bS0R,h|,U{C[20B{>R~P0P41P;<20A04#LdB0@651H0?R<b5b8b9X36W:1=0NS0S,51S0T1=1b[^36^:IP0%HnPnPoO3S0Ub4b6b7Q0EPCPXPFPcP9Py&0>6S0EPzP61i65S0Vg01=>S0WQ0RCe,U{P~P<b5b8b9%HbP0b4b6b7PCPXPFPcP9PyQ0EPzQ0R1i6O>0=6GS0X'h,U{P~P<b5b8b91=bPP0b4b6b75vbEFQ0LPCPXPFPcP9PyQ0NPzP{P6Q0VQ0WP|Ce,U{RbQ0O5g{P}PbC[P~P<b5b8b9X36X:I%H0S0O/51%H1S0W[^36^:IP01=nNPnPoO3b4b6b7PCPXPFPcP9PyQ0NPzP{Q0QP}Q0X,h|,U{S0XC[P~P<b5b8b9X36X:IQ0T1=1PRN[^36^:IQ0Ub4b6b75vqEFO3b1Q0K/je#LePuPKPRFZQ0IP0EFb2PwPKP0FZb2N>0<PmP@P0PG%SA#D#<#a#<#D#NRA,CGRRPx%KAPGPRPGPxCOdO4b1P21\GAd9BGA=4HxPHPRPLQ0HP0PvPqPLQ0HPVPvPqD7E?X0HPLPwPRPqPoD7PLPw1CG]RAABg52RI,]g'nRgPqPoD7Q0FPhPLP7PwPRPqPog01>AP\PIPAg01?KP?g01@UPrPvP\P?C6PHPwP\P^C@RwePwPHP^A4H0AX0HPmP@P0PGP^PAQ0@Q0A1VGARw'XdO4b1Q0HP\P0FZb2N>0;PmP@P0PGPAPgQ0@AmwGgdO4b1P21\G]d9BG]R]=4HgPHPAPLA3n\^P_PdP_PeDARIP0PuPvPLPIPVPuPvD7S0HE?X0HPmP@P0PGPA1nA5RRQ0@AmwGRdO4b1PAPHe/n594H]PLPIPAPuPvD7PLPIQ08#2#R,8aR],]a,tARaPuPvD7Q0HPhPLP7PIPAPuPvg01A_PKPMP]g01BiP?g01D3PrPnPKP?C6PHPIPKQ0JC@RIePIPHfDRI/0KfER]?3\^P_PdP_PeDARA/0MS0J,^0#IX0HPrPIPMP?C6PHA3I\^P_PdP_PeDARhPMPIPMD9R5eP5PH10]MS0HfFR5/0K/^0#IX0HPH1>GuRR105M,^0#IX0HPH1>GvRw1>Gn/^0#IX0HP;1duv%I0X0;Q001d10#I1X41#qR;[1X10#q1d41#I[S001d34#I\;20:10P0n2001000000120000000XB6XA6Q00^B6^A6P0PnPuPCPXPFPcQ0Mg01M4R;$09,u6Q0B-0861u6;60C660D6g01MS+06;k9PyP61y64P1Q0EH0EPzP{P{Q01P=P=P>P6P|g01N?1x6BCe,U{J0FRBP}PBC[P~P<b5b8b9X36X=61X01g01NfRB[1X14PB[[^36^=6P0P]P5PqO3b4b6b7O3b11^RwPuPvPCPXPFPcP9PyQ0NPzP{Q0P9g{bP}Q0X9g{bRbC[P~P<b5b8b9X36Q0OQ0S'5Q0W/5NRN[^36P0P]PvO2b4b6b7PCPXPFPcP9PyQ0NPzP{PbP}PbC[P~P<b5b8b9X36Q0O1=0P'5PN[^36P0PIPqO2b4b6b7H05EFQ0HPoEFP]PKPqFZQ0JP0EFb2PhPKP0FZb2N>0GPmP@P0PGPVPa%KUPGPVPGPaCOdO4b1P21\GUd9BGU=4HaPHPVPLPAP0PIPnPLPAPVPIPnD7E?X0HPLPhPVPnPuD7-0H7PaP0EGb1EYb1PgP0EGb1EYPxP0EGb1EYP[P0EGb1Q0DP0EFb2PtP0EGb1EYQ0CP0EGb1PsP0EGb1EYPlP0EGb1P`P0EGb1EYQ0=PHPf1CDOROPSPOD9R`PHPfQ02,8DRlPSPlD9RsPHPfQ05,8DRtPSPtD9R[PHPfQ0?,8DRxPSPxD9RgPHPfQ0;,8DRaPSPaD9R7PHPf1CDEREPSPED9RuPHPfQ04#1,8DRnPSPnD9RVPHPf%2p,8DRhPSPhD9RLPHPf%1p,8DRpPSPpD9RIPHPfQ0G#2,8DRAPSPAD9RUPHPfQ0G#1,8DRDPSPDD9Rf'5R2'5R@'5Rm'5Rq'5R]'5Ro'5RN'5RP'5R<'5R~,5kRb,5jR},5iR{,5:PrPSPKP?C6PHQ0<PSPKC:RzePzPH10QK1>GT94H0X0HP8A3Q\^P_PdP_PeDARePKP0FZb2P:P{PrPSPWP?C6P:eP:PHQ06PHP0PJPWC:X0HPHQ06PePWP0G;b2PiP}PrPSPYP?C6PiePiPHQ07PHP0PJPYC:X0HPHQ07PePYP0G;b2PjPbPrPSPZP?C6PjePjPHQ09PHP0PJPZC:X0HPHQ09PePZP0G;b2PkP~PrPSPMP?C6PkePkPHQ0:PHP0PJPMC:X0HPHQ0:PePMP0G;b2P`P<PrPSPOP?C6P`eP`PH10QOR`PHP0PJPOC:X0HPHP`PePOP0G;b2PsPPPrPSPlP?C6PsePsPH10QlRsPHP0PJPlC:X0HPHPsPePlP0G;b2P[PNPrPSPtP?C6P[eP[PH10QtR[PHP0PJPtC:X0HPHP[PePtP0G;b2PgPoPrPSPxP?C6PgePgPH10QxRgPHP0PJPxC:X0HPHPgPePxP0G;b2P7P]PrPSPaP?C6P7eP7PH10QaR7PHP0PJPaC:X0HPHP7PePaP0G;b2PuPqPrPSPEP?C6PuePuPH10QERuPHP0PJPEC:X0HPHPuPePEP0G;b2PVPmPrPSPnP?C6PVePVPH10QnRVPHP0PJPnC:X0HPHPVPePnP0G;b2PLP@PrPSPhP?C6PLePLPH10QhRLPHP0PJPhC:X0HPHPLPePhP0G;b2PIP2PrPSPpP?C6PIePIPH10QpRIPHP0PJPpC:X0HPHPIPePpP0G;b2PUPfPrPSPAP?C6PUePUPH10QARUPHP0PJPAC:X0HPHPUPePAP0G;b2PrPSPDP?C6PfePfPH10QDRQPHP0PJPDC:X0HPHPQPePDP0G;b2CcFTFTFTFTFTFTFTQ0>eCcH04WGWHWFWEWDXM6XI6WNWJWKo"). Qed.

Lemma sw_c2_eq : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xae5e8 : word) mem rom) (mkst regs' (0xae568 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite_run2 ()) ["FPX_1"] "h01bh11Hh22gHh34__p1h44__x1h57__arithh64__ffh78__varmaph85__with91nh:2Hah;6__sat7h<6__sat8h=2b1h>2b2h?1mh@1zhA3Ha0hB3Hs6hC1KhD1khE3memhF4regshG5regs'hH3romp%0p&0p;1p;2p;5p;3p;<p;=p;4p;6p;>p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004`R0p4p710R1p8p1005>p4p710P1p8g005]j12Tg006Bj11Tg006gj1WTg007Ej1UTg007hk20RTg008Tj1yTg0096j2@Tg009\j2ATg00:8R1j27Tg00:Sj56Tg00;Ej20Tg00<7j2wTg00=Bj1NTg00>Tj34Tg00>nj3CTg00?Qj3rTg00@>j2QTg00=`j33Tg00A2j2\Tg00AZj2tTg00BLj1|Tg00Bnj2GTg00CHj1mTg00DHm<0TTg00EJk30STg00Enj2[Tg00FQj2ZTg00G;j2{Tg00G[j1zTg00HNm<0PTg00IDk10OTg00Ibj2iTg00JWm=0MTg00KOk20LTg00Koj4^Tg00LOj1xTg00Loj3]Tg00MOj45Tg00NQj2hTg00ODj2qTg00Oak20JTg00PAk10ITg00Pak20HTg00Q?k10GTg00Q]k10FTg00RHk60ETg00Rlk20DTg00SOj2fTg00T2k20BTg00TTk20ATg00U@k30?Tg00U_k40>Tg00VQk10<Tg00Voj4oTg00WZk20;Tg00XBk20:Tg00X_k309Tg00YCk308Tg00Yfj3uTP0j6ETg00Zam>07Tg00[[j2nTg00\Vm>05Tg01OCm=0=Tg00]Wj2aTg00^Ik10@Tg01P:m>03Tg00`Ck20CTg00a?j6FTg01Q3k102Tg00a[j4bTg00b6k401Tg00bPk20KTg00blj3sTg00chk700Tg00dLj7~Tg00e0k80NTg00eTj7}Tf0R0#2#2p=Hf1R2%N0g00fPR33Cp=8f3R4f2R5/02;40p=?g00flR600K0p=J%20#2#2#2p=R%20#Np=K%10#2p=T%10#1p=>%20#1#2#1p=j%10#2#1#2p=I%20#1#2#2p=XAC203p=Bg00gJR7f5R8f4R9P4P5P2D6;s0p=g1720,75p=`%20#2#1#2p=d%10#1#1#1p=c%20#1p=P%10#1#1#1#1#1#1#1p=kA3945?320p=:As720p>0410451020549p=9g00i3R:1Z451Z2034p=M1G:0p=Lf6R;A3894P5P2P0D6p>0Qf7R<A3;89P4P5P2D6=s70p=D1Z2094:5p=lP<109493;8P5P2P0D6p=Sg00iQR=g00j1S00740p==P:P2g00jQP0Cop=eP2g00k8R>g00kWR?P?g00l7R@P0g00lWK00p=_P5P>P?P?P@P2P0F~p=vP4P>P?P?P@P5P2P0L0Np=pP;P8P9P41052P0EEp=OA4:20p>06P7P8P9P4P5P2P0F}p=V10209445p=;P<P;P81G941052P0EEp=<P;P8P9P4P5P2P0CbCbp=Yg00m7RA#2RB#1RC#WRD%2BRE#2S01#2#HRF#WRG#URH+0RRIQ01#W#U#y\HS02Q02PHP4%2CRJ,8DRK1@G0C?PHP9%1CS03#2RC,8DRL1@G2C?%J5%RF#R#R#R#R#R#KRM,A5'7PIp,2fxRNP<%2A#T#>#T#j#>#I#H,8GROP;P8PNP0%jA#>#H#I#>#X#KRP,BGRQP;P8D6EgPHP0PK1@G9C?PHP0%1ES04#1,8DRR%2JRS,8DRT,0<RUC?PHP0PTPUC?PHP0Q04#2,8DRV10<VS05C?PHP0PL10<LS06C?1w<03`3`3`XGIP;%NARW,BDRX%jA#>#d#c#P#T#KRY,@GRZQ03,8DR[%1AR\#1#>S07#1R]#>#c#kR^#1#>#c#k#k#k#T#H#R#RR_#KR`,@GRaD:P[%1_#NR_,@GRbPR10;TS08D:RcPNP;POP8P9D6RdPNPcPQP8P9D6Re+0410cKS091@G454HS0:PHPcPRQ08C?RfPHPcPTQ08C?RgPHPcPVP;PVD9RhPHPcPLP;PLD9Ri1w;c'73`3`S0;PdPNP=PIACD63Rd9rDXP;%NERE,QORj93;Xn0100000020000%1JS0<#WRJ%2]#T#>#I#I#H,8JRJ'\,tOR]P8P9D6Pe%yH%|H'GRePNP7P;POP8P9g01QiROPXPJg01S3%mO,G=g01T=N<0Tg011:RO%U0RJ%U2RkP1%U5?420P4P5P4P2CMRl[P5P2P5P0CM%U4?452[Rm%U9?445\lB0S520P0n2001000000120000000W>W=W9RlPm^>k^=J^9OROP0PG%PA#X#I#P#d#H#KRJ,BGRkP]%LJPGPkPGP]CMdO4b1P31[GJd9CGJ=4H]PHPkPNf8RJPXPjP0P<P;PNA3JXZRmP[PaP[PbD:PR10JTS0=PQP<P;K0QR9GDX0HPlPOP0PGPZPj%LYS0>1ZGZS0??lGjdO4b1A4HZjPHPZPNf9RnPXP0PkPJP<PNA3nXZP[PaP[PbD:PRPnPTPQPJP<GSGDX0HPNPmPkP<P;D6PNP=PIArD[dRoPm%WSRS18S^RS'\%2\R^#2Rp#NRq'{#zRr93m[n01000000200001QkERsP<P;D6P9PePNP7PmPkP<P;g011XRkP[PSg012b%mk,G=g013lN<0PPlPOP0PG%PA#X#I#X#I#KRk,BGRSPs%LkPGPSPGPsCMdO4b1P31[Gkd9CGk=4HsPHPSPNf:Rk?3XZRmP[PrP0PnPJPNA3m[aRm?3[bPRPkPTPQPnPJGSRrGDX0HPlPOP0PGPa&0OA/{q#zRq%L`PGPaPGPqCMdO4b1A4HaqPHPaPNf;R`?3XZR9P[P0PSPkPnPNA39[aR9?3[bPRP`PTPQPkPnGSGDX0HPNPmPSPnPJD6PNP=PIPoPm10m[%WpRo1BoWRt'\Ru'i93m[n01000000200011QSERvPnPJD6PrPePNP7PmPSPnPJg0156RnP[P[Ptg016@%mn,G=g017JN=0MPlPOP0PG%PA#X#I#X#>#H#KRn,BGRtPv%LnPGPtPGPvCMdO4b1P31[Gnd9CGn=4HvPHPtPNf<RnPXPZP[PaD:RSP[10S[S0@/iuP0P`PkPNA3S[bPRPnPTPQP`PkGSGDX0H%UDRk00LHRSPkPHP[PaC^PkPHPXPZC^%xS5]S3]RmP`P[g018T,G=RrC5PHP9P[PaC?R9eP9PHPaPNf=R9PXPZP[PaD:RwP[1i0uPtPnP`PNA3w[bRwPRP9PTPQPnP`GSRuGDX0HPlPOP0PGPb1iaWRW%L_1ZGbRx?lGWdO4b1A4HbWPHPbPNf>RyPXPZP[PaD:RzP[P0PtP9PnPNA3z[bRzPRPyPTPQP9PnGSS0AGDX0HPNPwPtPnP`D6PNPw%1^R^#WR{%2C,8{RC'\,ttR|PnP`D6PuPePNP7PwPtPnP`g0194PKP[PCg01:>Prg01;HPkPHP[PbC^=]SmRmP9PKPrC5PHPwPKP9PKD9RwePwPH10yKf?Rw?3XZP[PaP[PbD:S0B/0[S0C,h0#=X0HPmPyP[PrC5PHPzP[PbC?RCePCPHPbf@RC/0K/h0#=X0HPH1@GnS0D1h0b#=X0HP11q20#=1A52R1[1A201q52#=[Rt1q45#=\120J20P0n2001000000120000000X?:X9:Pt^?:^9:P01@G9,ZGS0EPxP:P91A0xX@:P:P_1Ay0X@:p-0Rtg01<RR1#xRu&0I1R120H:2S0F&0G:R}&0F:R~P~P>P?P?P@P4J0ES0G20D:AR>1f:M'e,_~5v~S0H%|?S0I1f:_R?,e>,_~Cp20B~@R@P0P5Q00,G=20A05#=dB0?:62H0>R5b6b7b8X4:W31A0M,72S001A2_[^4:^3tP0%JyPyP`O3b5PxPuP1&0<:S0JP}P:1f:6S0Kg01=>S0LP?Co,_~P@P5b6b7b8%J_P0b5%NBRB%NFRF+0;S0M1A6B%JF20:BFRx,A6[[S0N%JBS0Og01=eS0PB09BF2UW:S0QQ0OQ0P%Jx[]:S0OPuP1Q0JP}1f:B>08:GRF,e?,_~P@P5b6b7b81A_xP0b5b;b<5u_EEQ0EPuP1Q0FP}P~P:Q0KQ0LP>Co,_~R_Q0G5v~Q0IP_CpP@P5b6b7b8X4:X3t%J0/72%J2[^4:^3tP01AyMPyP`O3b5Q0MQ0NQ0QQ0OPuP1Q0FP}P~Q0HQ0I1e>F,_~CpP@P5b6b7b8X4:X3tQ001A2x[^4:^3tP0%JCPCP9O3b5b;b<5u9EEO3b1Q0D/hb#=ePwPKP`FOQ0CP0EEb2PzPKP0FOb2N>07PlPOP0PG%PA#X#I#P#T#d#KR`,BGRtP|%L`PGPtPGP|CMdO4b1P31[G`d9CG`=4H|PHPtPNQ0BP0PyP9PNQ0BPRPwPTPQPyP9GSEgX0HPNPzPtP9PnD6PNPz1BGYR`ACo63Rx,\oRo'nR2P9PnD6Q0APePNP7PzPtP9Png01>APXPxP`g01?KPrg01@UPmPyPXPrC5PHPzPXPZC?RzePzPHPZA4H0`X0HPlPOP0PGPZP`Q0>Q0?1ZG`Rz+06dO4b1Q0BPXP0FOb2N>05PlPOP0PGP`P2Q0>AlzG2dO4b1P31[GYd9CGYRY=4H2PHP`PNA3CXZP[PaP[PbD:RnP0PwPyPNPnPRPCPTPQPwPyGSR9EgX0HPlPOP0PGP`1n`6RtQ0>AlzGtdO4b1P`PHe/n694HYPNPnP`PwPyD6PNP=PIArDRdPn10nT/Qo93nRn01000000201011Q`ERdPwPyD6P9PePNP7PnP`PwPyg01UGRyPRPTPxg01VQ%my,G=g01W[N=0=PlPOP0PG%jA#>#d#c#T#H#KRA,BGR=Pd%LAPGP=PGPdCMdO4b1P31[GAd9CGA=4HdPHP=PNfBRA?3XZP[PaP[PbD:RyPR10yTRx/QoP0fAR`PCPN10ATRn93yRRyPQP`PCD6R9GDX0HPmP`PTPrC5PHA3`XZP[PaP[PbD:PTP`PTD9RIePIPHPnPNfCRI?3XZP[PaP[PbD:RYPR1Q0oP=PAP`PN10ITRo93YRRtPQPAP`D6RzGDX0HPHPnPNPYPRP0P=PAP`PzGDX0HPNPyP=P`PCD6PNPyQ07#P#>#T#H,8{RY,\{,t=R{P`PCD6P9PePNP7PyP=P`PCg01XePKPLPYg01YoPrg01[9PkPHPRPnC^=]SmPAPKPrC5PHPyPKPAPKD9RyePyPH10IKfDRyPXPZP[PaD:P[PbPR10yTD:RY/0LR=,a0#=X0HPkPHPRPoC^=]SmPIPLPrC5PHPtPLPIPLD9RoePoPH10yLRofERe/0K/a0#=X0HPH1@G`R`10eL,a0#=X0HPHP`1@GA/a0#=X0H&0@`PoPwEEPyPKPCFOP=P0EEb2PtPKP0FOb2N>03PlPOP0PGPQP{%LPPGPQPGP{CMdO4b1P31[GPd9CGP=4H{PHPQPNPYP0PIPAPNPYPQPIPAD6EgX0H20C7zP{P0EFb1EV1Qn6&02nEEPxP0EEb2PdP0EFb1EVb1P2P0EFb1EVP|P0EFb1EVPWP0EFb1Q0@P0EEb2PvP0EFb1EVPqP0EFb1PsP0EFb1EVPjP0EFb1P]P0EFb1EVQ0:PHPc1BDBRBP;PBD9R]PHPcQ01,8DRjP;PjD9RsPHPcQ04,8DRqP;PqD9RvPHPcQ0<,8DRWP;PWD9R|PHPc18D\R\P;P\D9R2PHPc1BDEREP;PED9RdPHPcQ03#1,8DRxP;PxD9RnPHPc%2p,8DR6P;P6D9R{PHPc%1p,8DRpP;PpD9RzPHPc%2^,8DR7P;P7D9RAPHPc%1^,8DRDP;PDD9R^'7Rc'7RI'7RQ'7RY'7RN'7RP'7R3'7RO'7Rl'7Rt,7iR=,7hRC,7gRy,7fPkPHPRQ08C^=]SmRmP;PKPrC5PHQ09P;PKC;RSePSPH10<K1@G894H0X0HP4P<PXPZP[PaD:P[PbPRPUD:RbPKP0FOb2PfPyPmP;PRPrC5PfePfPHPUQ0=94H0X0HRf1GHURyPbPRP0FOb2PgPCPmP;PTPrC5PgePgPHPUPfPyPbPTP0FOb2PhP=PmP;PVPrC5PhePhPHQ05PHP0PJPVC;X0HPHQ05PbPVP0G<b2PiPtPmP;PLPrC5PiePiPHQ06PHP0PJPLC;X0HPHQ06PbPLP0G<b2P]PlPmP;PBPrC5P]eP]PH10<BR]PHP0PJPBC;X0HPHP]PbPBP0G<b2PsPOPmP;PjPrC5PsePsPH10<jRsPHP0PJPjC;X0HPHPsPbPjP0G<b2PvP3PmP;PqPrC5PvePvPH10<qRvPHP0PJPqC;X0HPHPvPbPqP0G<b2P|PPPmP;PWPrC5P|eP|PH10<WR|PHP0PJPWC;X0HPHP|PbPWP0G<b2P2PNPmP;P\PrC5P2eP2PH10<\R2PHP0PJP\C;X0HPHP2PbP\P0G<b2PdPYPmP;PEPrC5PdePdPH10<ERdPHP0PJPEC;X0HPHPdPbPEP0G<b2PnPQPmP;PxPrC5PnePnPH10<xRnPHP0PJPxC;X0HPHPnPbPxP0G<b2P{PIPmP;P6PrC5P{eP{PH10<6R{PHP0PJP6C;X0HPHP{PbP6P0G<b2PzPcPmP;PpPrC5PzePzPH10<pRzPHP0PJPpC;X0HPHPzPbPpP0G<b2PAP^PmP;P7PrC5PAePAPH10<7RAPHP0PJP7C;X0HPHPAPbP7P0G<b2PmP;PDPrC5P^eP^PH10<DR<PHP0PJPDC;X0HPHP<PbPDP0G<b2CbFYFYFYFYFYFYFYQ0;eCbH01WCWBWAXD:WHWEWFo"). Qed.

Lemma sw_c2_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0xae5e8 : word) mem rom) (mkst regs' (0xae5f4 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite_run2 ()) ["FPX_1"] "h01bh11Hh22gHh34__x1h47__arithh54__ffh66__sat7h76__sat8h88__varmaph95__with:4__p1h;1nh<2Hah=4__x2h>2b1h?2b2h@1mhA1xhB1yhC1zhD3Ha0hE3Hs6hF1KhG2NEhH3REMhI1khJ3memhK4regshL5regs'hM3remhN3romp%0p&0p;1p;2p;5p;3p;<p;=p;4p;6p;>p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004`R0p4p710R1p8p1005>p4p710P1p8g005]j12Tg006Bj11Tg006gj1YTg007Ej1VTg007hk20XTg008Tj1~Tg0096j2?Tg009\j2=Tg00:8S00j25Tg00=Bj1TTg00XBk20WTg01E=j1vTg00:Sj56Tg00;Ej20Tg00<7j2yTg00>Tj34Tg00>nj3BTg00?Qj3uTg00@>j2ITg00=`j33Tg00A2j2fTg00AZk203Tg00BLk102Tg00Bnj2FTg00CHj1rTg00DHm<0ZTg00EJk30YTg00Enj2]Tg00FQj2\Tg00G;k201Tg00G[k100Tg00HNm<0UTg00IDk10TTg00Ibj2nTg00JWm=0STg00KOk20RTg00Koj4_Tg00LOj1}Tg00Loj3ZTg00MOj47Tg00NQj2lTg00ODj2tTg00Oak20QTg00WZk20PTg00X_k30OTg00PAk10NTg00Paj2|Tg00Q?k10MTg00Q]k10HTg00RHk60GTg00Rlj2{Tg00SOj2kTg00T2k20ETg00TTk20CTg00U@k30BTg00U_k40ATg00VQk10@Tg00Voj4gTg00YCk30?Tg00Yfj3xTP0j6ATg00Zam>0>Tg00[[j2sTg00\Vm>0=Tg01OCm=0<Tg00]Wj2bTg01EVj2jTg01F3k20;Tg01FTk10DTg01G3j2zTg01G\k209Tg01H=k30FTg01Hfk308Tg01IOk20ITg01J;k40JTg01JYk607Tg01K=k40KTg01\Cm>0LTg00`Ck206Tg00a?j6GTg01Q3k105Tg00a[j4oTg00b6k404Tg00bPk20_Tg00blj3wTg00chk70^Tg00dLk70]Tg00e0k80\Tg00eTk70[Tf0R0#2#2p=<f1R1%T0g00fPR23Bp=8f3R3f2R4/01;40p=@g00flR500_0p=N%20#2#2#2p=P%20#Tp=Lg00i3R6?410p=`%10#2p=Q%10#1p=C%20#1#2#1p=S%10#2#1#2p=H%20#2#1#2p=e%10#1#1#1p=dAB102p=Dg00gJR7f5R8f4R9P3P4P1D6;w0p=h1510,54p=c%20#1p=^%10#1#1#1#1#1#1#1p=iA3934?310p=:Aw710p>0:10341010549p=91\341\10546p=K1F60p=Jf6R:A3893P4P1P0D6p>0Vf7R;A3:89P3P4P1D6=w70p=E1\109464p=qP;109393:8P4P1P0D6p=Ug00iQR<g00j1R=740p=RP6P1g00jQP0Cgp=mP1g00k8S01g00kWR>P>g00l7R?P0g00lWK0^p=[P4Q01P>P>P?P1P0K0]p=pP3Q01P>P>P?P4P1P0L0\p=aP:P8P9P31041P0EAp=Og018TR@94<0p=MP7P8P9P3P4P1P0K0[p=W10109434p=;P;P:P81F931041P0EAp=>P:P8P9P3P4P1P0CoCop=Xg00m7RA#2RB#1RC#YRD%2BRE#2S02#2#<RF#YRG#VRH+0XRIQ02#Y#V#~\HS03Q03PHP9%2CRJ,8DRK1?G1RLC@PHP8%1CS04#2RC,8DRMPLC@%N3RL%PF#P#P#P#P#P#LRN,=3'5%TBRO%TFRF+0WRP,=3,5L1`89#vPIp,2fxRLf:RQ%2A#Q#C#Q#S#C#H#<,8GRRf9RSf8RTPLP0%SA#C#e#d#H#LRU,DGRVPSPTD6EhPHP0PK1?G;C@PHP0%1ES05#1,8DRW%2JRX,8DRY,0QRZC@PHP0PYPZC@PHP0Q05#2,8DR[10Q[S06C@PHP0PM10QMS07C@1yQ03c3c3cXLIPS%TAR\,DDR]%SA#C#e#d#^#Q#LR^,?GR_Q04,8DR`%1AS08#1#CS09#1Ra#C#d#iRb#1#C#d#i#i#i#Q#<#P#PRc#LRd,?GReD:P`%1c#TRc,?GRfPW10SYS0:D:RgPLPSPRPTP;D6RhPLPgPVPTP;D6Ri+0:10gKS0;1?G:54HS0<PHPgPWQ0:C@R:PHPgPYQ0:C@S0=PHPgP[PSP[D9S0>PHPgPMPSPMD9S0?1ySg'53c3cS0@PhPLP<PIABD52S0A9uD]PS%TERE,IRRh93S]n0100000020000%1JS0B#YRJ%2a#Q#C#H#H#<,8JRJ'f-03RRaPTP;D6Pi%~H&02H'FRiPLP7PSPRPTP;g01QiR;P]PJg01S3%r;,F<g01T=N<0Zg011:R;%V0RJ%V1RRQ00%V4?410P3P4P3P1CKRj[P4P1P4P0CK%V3?441[Rk%V9?434\jB0Y410P0n2001000000120000000W?W>W;RjPk^?R^>J^;;R;P0PG%SA#<#H#^#e#<#LRJ,DGRRPa%JJPGPRPGPaCKdO4b1P21]GJd9BGJ=4HaPHPRPLf;RJP]PhP0PQPSPLA3J]_RkP`PeP`PfD:PW10JYS0CPVPQPSK0VR9GEX0HPjP;P0PGP_Ph%J^S0D1\G_S0E?qGhdO4b1A4H_hPHP_PLf<RlP]P0PRPJPQPLA3l]_P`PeP`PfD:PWPlPYPVPJPQGUGEX0HPLPkPRPQPSD6PLP<PIQ0A9uD`RmPk%YXRX18XbRX'fQ08#2Rb#2Rn#TRo+01$00Rp93k`n01000000200001IRERqPQPSD6P9PiPLP7PkPRPQPSg011XRRP`PXg012b%rR,F<g013lN<0UPjP;P0PG%SA#<#H#^#<#H#LRR,DGRXPq%JRPGPXPGPqCKdO4b1P21]GRd9BGR=4HqPHPXPLf=RR?3]_RkP`PpP0PlPJPLA3k`eRk?3`fPWPRPYPVPlPJGURpGEX0HPjP;P0PGPe&0TAS0F001o$00S0G%JdPGPePGQ0GCKdO4b1Q0G94HePHPePLf>Rd?3]_RoP`P0PXPRPlPLA3o`eRo?3`fPWPdPYPVPRPlGUGEX0HPLPkPXPlPJD6PLP<PIPmPk10k`%YnRm1Dm\R9'fRr'n93k`n01000000200011IXERsPlPJD6PpPiPLP7PkPXPlPJg0156RlP`P`P9g016@%rl,F<g017JN=0SPjP;P0PG%SA#<#H#^#<#C#<#LRl,DGR9Ps%JlPGP9PGPsCKdO4b1P21]Gld9BGl=4HsPHP9PLf?RlP]P_P`PeD:RXP`10X`S0H/nrP0PdPRPLA3X`fPWPlPYPVPdPRGUGEX0H%VDRX00RHRkPXPHP`PeC_PXPHP]P_C_%}k5Zk3ZRpPdP`1F<@R@C7PHPoP`PeC@RoePoPHPePLf@RoP]P_P`PeD:RtP`1n0rP9PlPdPLA3t`fRtPWPoPYPVPlPdGURrGEX0HPjP;P0PGPf1ne\R\%Jc1\GfS0I?qG\dO4b1A4Hf\PHPfPLfARuP]P_P`PeD:RvP`P0P9PoPlPLA3v`fRvPWPuPYPVPoPlGUS0JGEX0HPLPtP9PlPdD6PLPt%1bS0K#YS0LQ0L%2C'8RC'f-039RbPlPdD6PrPiPLP7PtP9PlPdg0194PKP`PCg01:>P@g01;HPXPHP`PfC_=ZkpRpPoPKP@C7PHPtPKPoPKD9RtePtPH10uKfBRt?3]_P`PeP`PfD:S0M/0`S0N,l0#RX0HPpPuP`P@C7PHPvP`PfC@RCePCPHPffCRC/0K/l0#RX0HPH1?GlS0O1l0f#RX0HQ001t10#R1=41Rd[1=101t41#R[R91t34#R\d20Q10P0n2001000000120000000X@6X;6P9^@6^;6P01?Go,\GS0PQ0IP6PoQ0I,=0XC6P6Pc1=u0XC620POFR91=5O%NF1=5P[[Rd%NORrg01=eRwB0OOF1UW<RF%NP\w^<rRrp-0Rwg01<RS0Q#}RxQ0Q$0NRy1|61S0R&0M6Rz&0H6R{P{Q01P>P>P?P3J0GS0S1{6AR|1k6N'm,[{S0T5p{S0U&02>R}1k6cS0V,m|,[{Ca20E{?R~P0P41F<=20C04#RdB0B651H0AR=b5b8b9X36W:1=0NS0W,51S0X1=1c[^36^:wP0%NCPCPlO3S0Yb4b6b7Q0IP9PdPFPrPxPy&0@6S0IPzP61k65S0Zg01=>S0[Q0VCg,[{P~P=b5b8b9%NcP0b4b6b7P9PdPFPrPxPyQ0IPzQ0V1k6O>0?6GS0\'m,[{P~P=b5b8b91=cPP0b4b6b75xcEAQ0PP9PdPFPrPxPyQ0RPzP{P6Q0ZQ0[P|Cg,[{RcQ0S5p{P}PcCaP~P=b5b8b9X36X:w%N0S0S/51%N1S0[[^36^:wP01=CNPCPlO3b4b6b7P9PdPFPrPxPyQ0RPzP{Q0UP}Q0\,m|,[{S0\CaP~P=b5b8b9X36X:wQ0X1=1PS0U[^36^:wQ0Yb4b6b75xoEAO3b1Q0O/lf#RePtPKPRFOQ0NP0EAb2PvPKP0FOb2N>0>PjP;P0PG%SA#<#H#^#Q#e#LRR,DGRwPb%JRPGPwPGPbCKdO4b1P21]GRd9BGR=4HbPHPwPLQ0MP0PuPoPLQ0MPWPtPYPVPuPoGUEhX0HPLPvPwPoPlD6PLPv1DG^RRABm52S0N,fmRm'sRNPoPlD6Q0JPiPLP7PvPwPoPlg01>AP]Q0NPRg01?KP@g01@UPpPuP]P@C7PHPvP]P_C@RvePvPHP_A4H0RX0HPjP;P0PGP_PRQ0DQ0E1\GRRv'`dO4b1Q0MP]P0FOb2N>0=PjP;P0PGPRPNQ0DAqvGNdO4b1P21]G^d9BG^R^=4HNPHPRPLA3C]_P`PeP`PfD:RlP0PtPuPLPlPWPCPYPVPtPuGURoEhX0HPjP;P0PGPR1sR5RwQ0DAqvGwdO4b1PRPHe/s594H^PLPlPRPtPuD6PLP<PIQ0A9uDWPl10lY/Im93lWn01000000201011IRERIPtPuD6PoPiPLP7PlPRPtPug01UGRRPWPYQ0Ng01VQ%rR,F<g01W[N=0<PjP;P0PG%SA#C#e#d#Q#<#LRA,DGRRPI%JAPGPRPGPICKdO4b1P21]GAd9BGA=4HIPHPRPLfERA?3]_P`PeP`PfD:RlPW10lYS0N/ImP0fDRoPCPL10AYR^93lWRlPVPoPCD6S0AGEX0HPpPoPYP@C7PHA3o]_P`PeP`PfD:PYPoPYD9RwePwPHP^PLfFRw?3]_P`PeP`PfD:RvPW1I0mPRPAPoPL10wYS0D93vWS0MPVPAPoD6RmGEX0HPHP^PLPvPWP0PRPAPoPmGEX0HPLPlPRPoPCD6PLPl1IRERvPoPCD6Q0APiPLP7PlPRPoPCg01XePKPMQ0LQ09#^#C#Q#<'8g01YoP@g01[9PXPHPWP^C_=ZkpPAPKP@C7PHPlPKPAPKD9RlePlPH10wKfGRlP]P_P`PeD:P`PfPW10lYD:S0L/0MS09,b0#MX0HPXPHPWQ0DC_=ZkpPwPMP@C7PHQ0MPMPwPMD9RRePRPH10lMS0DfHRR/0K/b0#MX0HPH1?GoS0A10RM,b0#MX0HPH1?GCRi1?GA/b0#MX0HP<1joC%M0X0<Q001j10#M1`41#vR<[1`10#v1j41#M[S001j34#M\<20;10P0n2001000000120000000XB6XA6Q00^B6^A6P0PAPoP9PdPFPrQ0Qg01M4R<$0D,z6Q0F-0961z6<60F66086g01MS+0I;ZxPyP61|64P1Q0IH0JPzP{P{Q01P>P>P?P6P|g01N?1{6BCg,[{J07RBP}PBCaP~P=b5b8b9X36X=61`01g01NfRB[1`14PB[[^36^=6P0PlPRPtO3b4b6b7O3b1Q0A/biPoPCP9PdPFPrPxPyQ0RPzP{Q0T9p{cP}Q0\9p{cRcCaP~P=b5b8b9X36Q0SQ0W'5Q0[Q0U'5Ro[^36P0PlPCO2b4b6b7P9PdPFPrPxPyQ0RPzP{PcP}PcCaP~P=b5b8b9X36Q0S1=0P'5Po[^36P0PwPtO2b4b6b7H0KEAQ0DPuEAPlPKPtFOQ09P0EAb2Q0MPKP0FOb2N>0LPjP;P0PGPVPv%JUPGPVPGPvCKdO4b1P21]GUd9BGU=4HvPHPVPLQ0LP0PwPAPLQ0LPVPwPAD6EhX0H2067mPvP0EGb1EW1I^5&05^EAQ0NP0EAb2PIP0EGb1EWb1PNP0EGb1EWPbP0EGb1EWP\P0EGb1Q0HP0EAb2PsP0EGb1EWQ0GP0EGb1PqP0EGb1EWPhP0EGb1PaP0EGb1EWQ0<Q0=Q0>Q0?PHPg1DDOROPSPOD9RaPHPgQ02,8DRhPSPhD9RqPHPgQ05,8DRsPSPsD9R\PHPgQ0B,8DRbPSPbD9RNPHPgQ08,8DRIPSPID9R^PHPg1DDEREPSPED9R5PHPgQ04#1,8DRvPSPvD9RmPHPg%2n,8DR7PSP7D9RAPHPg%1n,8DRnPSPnD9RwPHPgQ0K#2,8DRVPSPVD9RLPHPgQ0K#1,8DRDPSPDD9Rg'5RU'5R2'5R;'5Rj'5Rt'5Rl'5Ru'5Ro'5RP'5R='5R~'5Rc'5R},5:PXPHPWQ0:C_=ZkpRpPSPKP@C7PHQ0;PSPKC;RkePkPH10QK1?GT94H0X0HP8PQP]P_P`PeD:P`PfPWPZD:RfPKP0FOb2P:P}PpPSPWP@C7P:eP:PHPZQ0C94H0X0HR:1FHZR}PfPWP0FOb2Q0=PcPpPSPYP@C7Q0=eQ0=PHPZP:P}PfPYP0FOb2Q0>P~PpPSP[P@C7Q0>eQ0>PHQ06PHP0PJP[C;X0HPHQ06PfP[P0G>b2Q0?P=PpPSPMP@C7Q0?eQ0?PHQ07PHP0PJPMC;X0HPHQ07PfPMP0G>b2PaPPPpPSPOP@C7PaePaPH10QORaPHP0PJPOC;X0HPHPaPfPOP0G>b2PqPoPpPSPhP@C7PqePqPH10QhRqPHP0PJPhC;X0HPHPqPfPhP0G>b2P\PuPpPSPsP@C7P\eP\PH10QsR\PHP0PJPsC;X0HPHP\PfPsP0G>b2PNPlPpPSPbP@C7PNePNPH10QbRNPHP0PJPbC;X0HPHPNPfPbP0G>b2P^PtPpPSPIP@C7P^eP^PH10QIR^PHP0PJPIC;X0HPHP^PfPIP0G>b2P5PjPpPSPEP@C7P5eP5PH10QER5PHP0PJPEC;X0HPHP5PfPEP0G>b2PmP;PpPSPvP@C7PmePmPH10QvRmPHP0PJPvC;X0HPHPmPfPvP0G>b2PAP2PpPSP7P@C7PAePAPH10Q7RAPHP0PJP7C;X0HPHPAPfP7P0G>b2PwPUPpPSPnP@C7PwePwPH10QnRwPHP0PJPnC;X0HPHPwPfPnP0G>b2PLPgPpPSPVP@C7PLePLPH10QVRLPHP0PJPVC;X0HPHPLPfPVP0G>b2PpPSPDP@C7PgePgPH10QDRQPHP0PJPDC;X0HPHPQPfPDP0G>b2CoFXFXFXFXFXFXFXQ0@eCoH04WGWHWFWEWDXM6XI6WNWJWKo"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_retry_a : forall regs mem rom (su f fd io ic cnt n0 rem : Z) (b0 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 ic ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0xc6000 <= f)%Z -> (f + 232 <= 0xf8ac0)%Z ->
  (su - 104 <= io)%Z -> (io + 16 <= su - 72)%Z ->
  (1 <= ic <= 2)%Z ->
  (1 <= cnt <= n0)%Z -> (n0 < 2^62)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z ->
  (bv_unsigned b0 + n0 <= 2^64)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 io) 8%nat = Some (word_to_le_bytes 8 b0) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 < fd < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xae5f4 : word) mem rom)
      (mkst regs' (0xae5e4 : word)
        (wbytes (wbytes mem (Z_to_bv 64 io) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b0 + cnt))))
                (Z_to_bv 64 (io + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n0 - cnt)))) rom)
    /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 io /\ getr regs' 12 = Z_to_bv 64 ic
    /\ getr regs' 18 = Z_to_bv 64 ic /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 io
    /\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
    /\ sw_regs_but regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0143 ()) ["FPX_1"] "h01bh14__x1h27__arithh37__sat10h46__sat7h56__sat8h66__sat9h71Hh82gHh94__x2h:5__with;4__ffh<8__varmaph=1zh>4__p1h?2Hah@1nhA1xhB1yhC7__sat11hD7__sat12hE4__x3hF2b1hG2b2hH1mhI1ohJ2B0hK3CNThL2CRhM2FDhN3FhihO3FlohP3Ha0hQ3Hb0hR3Hs1hS3Hs2hT3Hs3hU3Hs6hV3HsphW2IChX4IOhihY4IOlohZ3Mb0h[3Mfdh\3Mn0h]2N0h^3REMh_3SOKh`4SUhiha4SUlohb2b0hc3cnthd1fhe2fdhf2ichg2iohh3memhi2n0hj4regshk5regs'hl3remhm3romhn2sup%0p%1p%2p%3p%4p%5p&0p&1p;1p;2p;5p;3p;4p;6p;>p;Ap;=p;8p;:p;Bp;9p;7p;<p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004`R1p4p710R2p8p1005>p4p710P2p8g005]j15Tg006Bj1hTg006`j1bTg007Cj16Tg007hj1TTg008Fj1=Tg00>Gk20@Tg00?0k11:Tg00:Mk20LTg00@fk116Tg009?k113Tg00;0k511Tg009jk20gTg008ej30Tg00;TR2j22Tg00<0k11gTg00<Nk20cTg00<gR3j2:Tg00=Dk41eTg00=gR4k10RTg00[4S00j29Tg00AIk10ZTg00Akk20<Tg00BHk10_Tg00Bhk30=Tg00E0k20OTg00DMk30?Tg00CKk31HTg00Y<j2ZTg00K^j2Hk118Tg00E\k103Tg00F<j3\Tg00M]j3iTg00Ldj2NTg00MAj2FTg00LDk219Tg00H6k10iTg00F\k20MTg00GXk117Tg00HXk215Tg00I:j2]Tg00ITk214Tg00J@k412Tg00K2k10[Tg00ORj2?Tg00PFk208Tg00Pnk307Tg00SOj4QTg03^Rk20YTg00QRk206Tg00]4j2}Tg00Sok210Tg00G:k10~Tg00UCj27Tg00Uoj23Tg00XJj58Tg00NJk20WTg00\Bk10|Tg00Tak20VTg01>\k10UTg00Yfj3<Tg03_Fk20TTg010Wk10dTg03TZk10{Tg00^Zk20FTg00`Uk30yTg00Vak21iTg00WAk21hTg03`9k20STg00]gk20DTg03`lk20CTg03a`k20xTg00dNj3VTg00eIk41fTg03UWk11dTg03bkk20vTg03c^k21aTP1j64Tg03dik11`Tg03egm>1_Tg00i`j2KTg010;j6@Tg011[mA0aTg0164m=1[Tg03f`m=1ZTg015>m=0`Tg013Rm=0JTg03gWm=1WTg012Pj4ITg01DHj4~Tg01Njk80hTg01OGm:0oTg00jCmB0nTg03hMk20PTg03hjk21UTg03iJm>1TTg00him=0NTg00ZZk202Tg00lek60mTg03jDm90kTg01;dk21RTg01<kmA1QTg03kGm=1PTg00aPk31OTg01PHk71NTg01=`k21MTg01Bgk40^Tg03l>k10jTg03l_k41GTg01?Rk21ITg03mok41JTg03o8k31FTg040@k11KTg041Ik11LTg042Gk41ETg01Qnk40]Tg01Cnk41DTg00?Yk31STg01E3k70;Tg01JOk31CTg01EWk31VTg01Gak70qTg01F:m<1BTg01HEk805Tg01G=k61ATg01Hik31@Tg01IHk41?Tg01F_k41]Tg01IimB1>Tg01LIm<1^Tg01K2k40uTg01Lnk30bTg01Mjk11=Tg00l:k41<Tg01QJk71;Tg01RIk71cTf0R1#5#5p=|%51#Tp>0Q%51#5#5#5#5#5#5#5p>0>%51#5#5#5p>0:%51#5#5#Tp=R%61#6#5#5p=d%61#6p>0}%51#6p=r%51#6#5#6p>0z%61#5p>0A%=1#=#=#=p>1\%=1#=#=#=#=#=#=#=p>1X%=1#=#=#=#=#=#=#=#=#=#=#=#=#=#=#=p>01%51#6#5#6#6#6#5#5#6#5#6#6p=v%61#5#5#Tp=ag01ScR5/F1p=l1251p=Og01SER6f1R7<1S1p>0020g61p=_f2R8g01TAR9g01T`R:P:g01U@R;P6P7g01U`R<P1C~g01VGR=K0;p=Df3R>/Z81Z71506p=C%61#6#6#6p>0X%51#6#5#6#6#6#5#5p={g01X5R?:0=71p=>%51#6#5#6#6#6p=q%51#5#6#6p>0E%51#5#6#5p=w1]61p=EA0671p=P%51#6#6#6p>0t%61#6#6#5p=yP8P9P:P:P;P6P7g01VgR@P1C~P=K0;p=k%61#5#6#6p>0r%T1>0=7?p=MB1C671p=^B1V671p>04P8P9P:P:P;P7P1K0qp=g1N87/21p=u1:87/21p=Gg01XQRAP6P6P6P4P4f5R4f4RBP>P8P7P1N<1Bp>0\P4P9P:P:P;PBP9P:P:P;P>P8K0qP7P1L05p=`P7P9P:P:P;P1J1Ap>09B1@651p>0KP8P7P;P1H1?p=nf6RCP9P:P:P;P4PBP>P9P:P:P;P8P7P1L05L05p=XP4P9P:P:P;PBP>P8P9P:P:P;P6P7P<P1C~P=K0;L05p=tP6P7P@P1C~p>0fPBP9P:P:P;P>P8P7P9P:P:P;P1P=K0;L05p>0eP6P8P7P1H1]p=xP>P9P:P:P;P8P7P1L05p>0IP6P6P6P6P6P6P3P1P7P8P3P>PBP4PCf7R3f8R@f9R<NB1>p>0HP6P6P2P3P2PCP4PBP>P8P7P1N<1^p=eg01Y0R2P8P7P1H0up>0Gg01ZYRDg01[US01701p=m20D719<>8p=s&0319\879\B>9\C4p=YA\8719\B>p=11}719<>8p=cP3A<C4BP>P8P7D8>0b21p=A1971,98p>0BP2P>P8P7H0u=0B1p=jB0b271p>0w1387=0>1p>1bA0>87/91p=zB0=>87=0B1p=LP4PBP>P8P7D8>0b21p=;P6PBP>P8P7P1E4p=S&1=1,]Dp=WA\4B>P8P7P1CIp=B&0319\87p>1Y1Z719068p>0s&0319\879\B>p=[P7P9P:P:P;P1P=K0;p>0pPCP4PB1]>8P7P1E4p=UP6P3PCP4PBP>P8H1<P7P1E4p=f1271-028p=oP8P9P:P:P;P7P1K1;p>0lP2P4PBP>P8P7P1K1cp=JPCP4PBP>P8P7P1H0]H0]p=pg01\5R=#5RE#5RF#5RG#5RH#5S02#5RI#hg01\ZRJ%hG#bP0%6=S03#6RK#5RL#|S04$0QP6%5I$0>$0>$0>RM#5RN#TP6&0:N$0>#RP6Q03#5RN#5RO#5RP#d$0>#RP6%6L#RP6&0}=#d#r$0z$0A#|#RP6%6NRQ#5RR#5$0QP6%THP6%6FRS#5RT#5$0QP6%6KRK#6S05#5g01]8%TIP6g01]]RI#=RU#=RV#=RW#=S06$1\RX$1X$01$01$01$01$01$01PA%TGP6%RKP6%TMP6%v=#d#aP6%6H$0QP6%hQPJQ05#6S07#TP6%TERH#lp-0RM%OHPM20@6W&1:6RW20@6U20@6IS08+00PW20L6N&166RI&136RU%T=S09#_S0:20L6=RY3DPUP9P:P:P;I11R920g65S0;=DUYP9%b1RZ%b7R[P8P7P8P1CCR\%b>?087R][]G]F^@JR^PM%v=$0X#RP6%hOPJ20@6VPW%v=$0X#aP6%{=#d$0:#RP6%6ERV#hR_#bP0%hNRN%TFRF'>%bN%{=#d$0:#aP6%q=$0E$0:#r#RP6%q=$0E$0:#r#aP6%{=#d#w#RP6%{=#d#w#aP6%{=#d$0E#RP6%{=#d$0E#aP61271S0<$1gXB6XA6Q0<Q0<+0c^B6^A6P6P6g01^<1:71H1eR`#EXH6X@61P``^H6^@6&0R1S0=#EXAAQ0=Q0='P^AA&0RXP6%{=#d#r#|#RP620L6ES0>9DUYP9%v=$0t#RP6%v=$0t#aP6%q=#w#y#|#RP6%q=#w#y#|#aP6%q=#w#y#r#RP6%q=#w#y#r#aP6Q06$0RP6Q02#TP6Q0;=kUYP9%q=#w#y$0A#RP6%q=#w#y$0A#aP6%v=$0r#RP6%v=$0r#aP6%v=#d#RP6Q09/21RE1217S0?'9%O7S0@1278S0A'9[^16^96PM19E7S0B1255Q0@'9[^16^>MPMQ05#TP6fqS0C#bP0Q0C$0ZP0%5VRE,M_fQS0D%6S,M_fRS0E1M_TfSS0F%6VRV#5,M_fTS0G1M_SfUS0H1>_HfVS0IfvS0JfwRS':P6foS0K#TP6Q0K-0<HP6f{S0L$0_P0%6G,M_f[S0M1M_Vf\S0N1M_Of]S0O%5E,M_f^S0P1M_Lf_S0Q1M_Qf`S0R1M_KfaS0SB0=_5?fbS0TQ0C-0<HP6fzS0U#OPMfpS0VQ0K+00g01_iS0W+0Og01_=S0X%_HS0Yf}S0Z#h60?6PIQ0V9DUYP9P\PMQ00P7\]%bB?0>8\1%b4?0B>\7B1H>87P1n2001000000120000000aXG[XFZX@JP^flS0[fsS0\+00PWp+01ERW#_R^PIp+01LS0]#_RJPIp+01FS0^#_,^YQ0>004^5DUP9PJPIQ0Yp+01QS0_60?6PIfnS0`,ZNP6Q0^$0RP6Q0^#EQ0^Q0^'Pp+01GS0a#_PIp+01CS0bQ07#5#r$0A#|'MQ0b#bp+01RS0c#_RN=DUYP91^YNQ0_#_5DUP9p+01JS0d#_,^YPIQ0S-0<HP6p+01KS0e#_9kUYP9p+01AS0ffkS0g5gUP9Q0;Q0;5DUp+01BS0h5gUP9Q0N-0<HP6Q0_,>_f|S0i%6E,M_Q0ZQ03,M_f~S0j1>_Fp+01@S0k%6V,M_Q0f1M_PQ0h%6O,M_Q0b1M_Rp+01DRR%6Q,M_PWQ0d#bP0ffS0lQ0l[P0Q0P-0<HP6Q0O$0ZP0p+01lS0m%5=$0A#y$0z$0X#r#|'MfiS0np+01mS0op+01\S0p'>fjS0qp+01nS0rQ0p'HQ0gp+01oS0s/H5Q0[p+020S0tp+01bS0u'HfmS0vQ0`$0ZP0Q0l#OPMQ0l#lPMfgS0w#OPMQ0XQ0NQ0X$03R=3\Q0X$0_RQp+01]S0xQ0N5kUP9Q0xQ0N5gUP9p+028S0yp+01[S0z'>fuS0{Q0nfcS0|5i_PDQ0pQ0m'>fAROQ0XQ0PQ0W+0O;\=PQQ0>Q0P+04=DUYP9p+02:S0}#_Q0P'^PIQ0y=u71Q0J/28%O8S0~[[^16^96PMQ0>Q0P5DUP9Q0P9kUYP9Q0}p+029S10,N75G1p+02@S11,28fxS12,F8[[^16^96PMp+02BS13Q0u'>Q0kfrS14Q0v5i_PDp+02DRPp+01cRV'>Q0hQ0b-19VP0ftS15Q0V5i_PDp+02GS16/>VPWp+02HS17/>VQ0^Q0JQ0\5i_PDQ0m@0=5?Q0Dp+02KS18p+01eS19'>p+01IS1:Q12Q0J5i_PDp+02MRWp+01fS1;'>Q0ep+02NS1<Q1;'>Q0]p+02OS1=Q1;'>p+01MS1>p+02PS1?Q1;'>p+01NS1@p+02QS1A$18p+01PS1B^=6Q0_\6P0Q0Vp+01HS1C5G1X=6PM^=6R0Q1C#EQ1CQ1C'PQ159DUYP9204YSPIp+02TRE,21p+02WS1D,N7Q1DQ1>3G[^16PMp+01OS1E/21p+02XRN,N7#O[^16PMp+02VS1F,21p+02YS1G,N7Q1E'F[^16PMQ0i-04YQ0>5DUP9P1XA6RJPJQ0rPXPWQ0JJ0\PJQ0oO1PJPWO1'PQ0J,^YPIQ0>Q0j+04Q0j'^PIp+02^S1HQ0s'>Q0pp+02_S1IQ0r'>Q0xp+02`R^Q0r'>p+01^S1Jp+02aS1KQ0r'>p+01_S1Lp+02bS1MQ0r'>p+01`S1NQ1EQ1@5i_PDQ1H=u71Q0x/28p+02ZS1O,:8#O[[^16^96PMQ1Hp+02]S1P,N75G1p+02dRZ,28p+02[S1Q,:8Q0x'F[[^16^96PMQ10Q0z5G1X=6P0Q1I,N79G1^p+02fS1R,28Q1PQ1L5G8[[^16^96PMp+02hS1Sp+023S1T'>Q1;p+02iS1UQ1T'>p+01gS1Vp+02LS1WQ1Q'>Q0CQ0h%_F'^PIp+02lS1Xp+022S1Y'>p+01jS1Zp+02mS1[Q1Y'>p+01kS1\p+02nQ1Y'>Q0mp+02oS1]Q1Y'>Q0op+02RS1^Q1H'>PSp+031S1_Q1T'>Q0sPUPUPNQ13&0i:R:Q0^E`P9P=PQ20M67R0&176R[PUPUQ1P209U>S1`P:Q0dE`215U;R;P1P8g01`US1a,]D21418Q1a50Dd&0K7H12R]b;b<b:X16X>M20M61$0K$0[R\PUPUQ1Q209U7P:Q1CE`5nU^16^>M1?SFQ1YQ1T$0iQ0\Q0L#lPMQ0i#OPMQ1X-08Hp+02cS1bQ0uQ0J[[PS\V\ZPMg01[9RKp+030S1c>07H7UX?ZPS\K^?Zp+02eS1dQ12\K]?PMQ0\/?FQ0}Q0KQ0>5DUP9PUQ1LP:PUQ0`P:Q0vFXP9Q0[/?FRSp+02=S1eQ0g/?Fp+02>S1fQ1Ip+02?S1gp+021S1hQ0hCQQ0gQ0b00YFQ11p+03CS1i/ZRP6PSQ13Q1bp+02CS1jp+024S1kQ0^CQQ0KQ0v/?FRLPPQ1UQ0[+06P6PSp+02FS1lQ0dQ0d'}Q16PSQ17Q1Up+02IS1mQ0yQ0]CQQ0{PLp+02JS1nPLQ18PLQ1WQ0[Q0v']Q0[Q0vQ0v30PUQ0qP:PUQ0nQ1Y'^Q0sEtP9PUADURYP:PUQ0;Q0qEtP9PUQ0[P:PUQ0gQ1h+0fI0eP9fdS1op+03@S1pQ0o+06+10Q1AQ0]PQ&0~6S1q20M68S1r7x8Q1q7x7S1sP[PUp+01SS1tP:PU209UBS1uQ1g5gUP:Q1:FXP;P]b;b<b:X16X96X>MQ1q?x70Q1q7x1$0K$0[PUQ0_P:PU209U8Q1e5gUP:Q0aFX5nU^16^96^>MQ1J,F7Q0A,9>Q1<,F8[[^16^96^>MPMPUQ1e9kUYP:Q0^H0IP9Q1J,F11F7W[^16PMfhS1v/?FRRQ1Fp+01ZS1wp+03KS1x'?Q1DQ0n/?FPNp+039RLQ1GQ1mQ0zCQQ0^Q0q/?FRSQ1OPSQ1QQ0CQ10'^PIPUQ11P:PUQ1BP:Q14Q1f5kUFXP9PUp+02AS1yP:PUQ0_P:Q0\Q1g5DUFXP9PRQ1IPRP^Q0l/?FR^Q1KP^Q1MP^Q1bP^PZp+01hS1zp+03U'?Q1dP^Q1Rp+03GS1{p+02gS1|Q1QQ1\CQp+01TS1}P=PQQ1rQ1q7x7S1~P[Q0gP;P]b;b<b:X16X96Q1q9x01$0K$0[R^Q0n5nU^16^96p+03PS20Q0z5gUP9Q1\Q0l']Q1\Q0lQ0l30Q1M-08Hp+03XRRQ0mQ1v[[p+03YS21Q0oQ0n[[PMQ21Q1R>07H7VKW?Q21Q0n\K]?p+03ZS22Q0q\K]?PMPUQ19P:PUQ0|P:p+03VS23FXP9p+01iS24PQQ1~P[Q0wP;P]b;b<b:X16X96feS259nU^^16^96P=PQP0P[Q0HP;P]b;b<b:X16RIQ0F9nU\^16RSPIPSPIPSP=PQP0P[Q0EP;P]b;b<b:X16fPS269nU\^16PUQ1\P:PUQ0nP:Q0;Q0e5DUFXP9Q0sPQQ1~P[fLR9P;P]b;b<R\b:X16X96fJRS9nU^^16^96RIQ0tPQP\b:X16X96PIQ1hPQQ1~P[f<S27P;P]b;b<b:X16X96f:RI9nU^^16^96Q1YPQQ1~P[P3P;P]b;b<b:X16X96AnU^4^16^96p+03:R^,7_131Lp+03;S28137Lp+03<S29138Lp+03=S2:13>Lp+03>S2;13BLp+03?S2<134LQ1p13CEp+03AS2=133Ep+03BS2>13@EQ1i13<Ep+03DS2?13IEp+03ES2@f;R\/3Ep+03FS2AQ27/3EQ1{f=RP/3Ep+03HS2Bf>S2C/3Ep+03IS2Dp+02SS2Ep,2fxRGPOQ1^P7P1D8g01a5RTp+04NS2F,N1P6p+04QS2G/H1p+03OS2HQ1],:7P6Q2G,:8P6Q2B,27PMQ2D,27PMPJPJPJp+03jS2IP4P4%E4p+033S2Jp+04TS2KPJPJp+03iS2Lp+04IS2MQ2KQ2K#EJ0\N:0HPJP>O1/P8p+04WS2N/Z4P6PJp+03mS2OP4PBP7p+03LS2PQ2PQ1kGe20c>8p+036S2Q,:7P61P8<PMQ2H,27PMQ2F,:1P6p+04^S2R/H7p+03\S2Sp+04_S2T/H7p+03]S2UQ2L,:8P61:>FP6%EB1PBBfFR`Q0680G>Q1Sp+04US2V,?4p+03bS2Wp+04eRa/Z4P6PJPJPJp+04:S2XP@P@P>p+03oS2YPFPJPJp+049S2ZQ06PF%EFJ0\N:0HPJP4O1/PBp+03eS2[?038PMp+041S2\,:8P6p+04ZRb,F1PMp+04kRc/H7Q2LQ0600W1p+03_S2]&0|7p+03kS2^p+04LS2_p+03lS2`Q2IP8CQQ1GQ2W00V8p+034S2ap+04cRd,:1P6p+04DS2b,:7P6p+053S2c/H8Q2\p+054Re/H8p+042S2dp+04GS2e,:>P612>BPMp+04iS2f,:4P612CCPM%E31P33p+03nRf,23PMQ2Y,2<PMfNS2g,2<PMfOS2h,2\PMQ0S@0G<XQ1ip+05?S2i/Z\P6Q27p+052S2j'?p+04>S2kQ2Tp+04?S2lp+040S2mPPCQQ1XQ2C/?5p+04@S2nPJPJPJQ2NfBRgPg%EgQ2Vp+055S2oPNN:0HPJf@RhO1/POp+04bS2pp+04BS2qp+045S2rPhCQQ1]Pdp+04CS2sp+043S2tPhCQQ1cp+05FS2u/ZOP612O`PMfGS2v,2hPMPJPJPJp+04]S2wQ2vQ2vf?Rip+04[S2xp+05;S2yQ1HN:0HPJfCS2zO1/POfERj/?5p+04HS2{fZS2|/2SPMQ2|fKRk'2PMp+04KS2}Q2_?01SW0Q2}PM]0Q2_/]SQ2_?0SSp+04MS2~Q2C70SPMQ2F?0P9PM1:OdP6p+04dR9,:\P6PJp+04hRlQ26Q0DPiQ2eQ2eQ1]GefHS30Q2v+0cQ0E,PPPMQ0G,PjPMQ0E$0UP4Q2v,2BPMQ2_,2CPMQ0RfIRm'2PM121HS31PMp+05\S32/H7PbQ2yQ2xQ2NP1CQQ2Bp+04\S33Q2w?018W0Q33PM]0Q2w/]8Q2w?088p+05aS34/H1Q2Tp+05@S35p+04`S36p+04ORnP1CQp+03MS37p+05cS38/Z7P6p+05eRo/H1Pdp+05fS391N74'HP920WX7RpPbQ0pp+04YS3:;<8p+04fRq,7_p+05GS3;p+04gRrPbP>CQp+03TS3<20T41#mX0lPM^0lp+05kS3=/Z4P6p+05JS3>p+04jS3?p+04XS3@PCCQp+03WS3Ap+05KS3BPcQ3:PCCQPRp+04aS3C00VCQ2tQ2TQ2m5<Cp+04mRR,7_&0dI&0{@/PBQ2p,3@p+04oRsp+04nRt,3<p+050RuQ2pp+044S3D5<>p+051Rv,7_20F879<\9Q2j,7_Q2c?0>iPMQ2490e>PM133rQ2oQ159<Brp+056S3E,7_Q2N-0Y79<<lp+057S3F,7_p+058S3Gp+04;Rw708PMQ3E,33p+059S3H13@cp+05:S3IP<p+04lS3JP7P1CsQ2y,7_p+05<S3KQ0t708PMp+05=S3LQ2n708PM133sp+05>S3MQ2iQ0Z701PMp+06CS3N/H1p+05AS3Op+06DS3PQ0F,N7'Hp+05BS3QQ38p+05CS3RQ3MP1CQQ2mp+05DS3Sp+06GS3T/Z1P6PpQ2yp+06IS3UfXS3V,:7'HQ3;Q3L00V7PnPpQ3Mp+05jRpQ3>Q3IP4CQp+047S3WQ3=Q3BQ2yP>CQp+048S3XQ1YQ0e<0y8p+05LS3YQ3Y[p+06NS3Z01i>PAPwp+05nS3[p+05NS3\Q35Q0|CQPwQ1DPwQ0EPwQ0TPwQ0cPwPIPwQ0FPwQ0UPwQ0LPwQ1dPwP8PwQ0OPwp+035RxPwPxPwP>PwQ0jPwQ28PwQ2<PwQ0IPwFYD1D1D1D1D1D1D1D1&0_wQ1>Q2|-0WX60y8p+05OS3]Q3][21hX@A0A8XQ3OQ275<Sp+05QS3^,7_Q3OQ2V5<1p+05RS3_,7_p+05ES3`,37p+05SS3aQ3RQ2N5<7p+05TS3b,7_P>Q3SQ3Q,3>P7Ccp+05US3c,7_p+05VS3dQ3:708PMQ2u,3Bp+05WS3eQ3B,34p+05XS3fp+05HS3gQ0n5<Bp+05YS3h,7_p+05IS3i20S875<3p+05ZS3j,7_p+05[S3kQ2R70>PMQ32Q1v70>PMQ3k,3@p+05]RSp+05MS3l,3<p+05^S3mQ3]Q2v5<4p+05_S3n,7_Q3]1}87Rx5<\p+05`S3o,7_Q34Q1F70>PMp+05bS3p?0>aPMQ3a,3<Q38Q3a,3Ip+05dRyQ3c=<4r17_oQ27Q3d20D87Rz3<Q39,7_p+05gS3qQ0E70>PMp+05hS3rQ1270>PMQ3j,3<p+05iS3sQ3j,3IPpQ3m,3\Q3=Q27/3pp+05lS3tQ3j,3Pp+06QS3u006a'?9<PSp+05mS3v,7_Q34Q0o5<@Q3[,7_p+05oS3wQ0r704PMp+060S3xQ3V704PMp+061R{Q0Z704PMp+062R|Q1|704PM13Pyp+063S3yQ1Y9<4yp+064R},7_Q3rp+03`S3z,?75<ip+065S3{,7_p+066S3|p+025S3}708PM13@}p+067S3~Q3r,3<p+068S40Q3qQ0^5<Bp+069S41,7_A<\pzp+06:S42,7_p+06;S43Q1]70>PMp+06<S44Q3M70>PMQ3v,3@p+06=RzQ41Q0g5<Bp+06>S45,7_p+06?S46Q1e707PMQ43,3Cp+06@S47Q46,33p+06AS48Q47Q1m5<>p+06BS49,7_Q45=<<xQ3N,7_Q3PQ2Q70>PMp+06ES4:?0>^PMQ3PQ185<3p+06FS4;,7_Q48,3@Q3TQ3PQ1J5<4p+06HS4<,7_Q3U?07^PMQ4;,33p+06JS4=13@zp+06KS4>Q42p+01XS4?5<>p+06LS4@,7_Q3U20C875<Ip+06MS4A,7_Q3ZQ2=70>PMp+06OS4BQ3_70>PMQ45,33p+06PS4CQ47,3@Q3uQ4;Q3d5<4p+06RS4D,7_Q48=<Ixp+06SS4E,7_p+06Tp+01aS4F70>PMp+06US4GQ1;70>PMQ4;,3<p+06VS4HQ4:,3Ip+06WS4IQ4@Q4:,3\p+07<S4J006b'?5<\p+06XS4K,7_Q4>Q0s5<Cp+06YS4L,7_p+06ZS4M?0>NPMp+06[S4NQ1V70>PMQ4K,3<p+06\S4OPGP>Q3pQ0ZQ2>D8PTQ4D,3Bp+06^S4Pp+06]S4Q,34p+06_S4RQ4E,3Cp+06`S4SQ4E,33p+06aS4TQ4P,3@p+06bS4UQ4S,3<p+06cS4VQ4G,3Ip+06dS4WQ4S,3\p+06eQ2zQ4KQ2G,?<3<p+06fS4X,7_p+06gS4YQ1e70IPMQ2CQ4T'3p+06hS4ZQ44,3ip+06iRTQ4W,3hp+06jS4[13Ozp+06kS4\13gzp+06lS4]Q2z/3zp+06mRNfDRx/3zp+06nR~13jzp+06oS4^13`zp+070S4_Q2v/3zp+071S4`Q30/3zp+072S4ap+073S4bQ3~70xPMp+074S4cQ2870xPMp+075S4dQ2a70xPMp+076S4eQ1W70xPMp+077S4f?0xWPMp+078S4gp+037S4h70xPMp+079S4ip+038S4j70xPMp+07:S4kQ1z70xPMp+07;S4lPGQ1lP~Q1m00F1PpQ2Wp+03aS4mQ2gGAW0Q4lPM]0Q4JPGp+02<S4nP~P1Q3qp+03cS4oQ2WQ2hGAW0Q4JPM]0p+07=S4pQ2O70xPMp+07>RWQ2O70xPMp+07?S4qQ2m70xPMp+07@S4r?0xfPMp+07AS4s?0xfPMp+07BS4t?0xfPMp+07CS4u?0xfPMp+07DS4v?0xfPMp+07ES4w?0xfPMp+07FS4x?0xfPMp+07GS4y?0xfPMp+07HR`Q0Gp+04<S4z30PMQ2zQ2CQ2lQ0Q+0x60Bi:0BOh80Bg:0BjxPM19>8PM1941PM1931PM19<1PM19\1PM19P1PM19i1PM19O1PMQ2z/91PM19j1PM19m1PM19k1PMfMS4{/91PMQ2h/91PMQ0D/91PMQ0F/91PMp+07Zp+02kS4|70np+07[Q2270np+07\p+03270np+07]S4}Q1W70np+07^S4~Q2d70np+07_Q2n70np+07XS50Q2s'2Q2bp+08_Rk'2Q2bPrPqPqPaQ3mPSPSQ32P9Q47P1p+04JS51PCO2b2b4b5b6b3PrPqPqPaQ3mPSPSQ32PdQ46P1Q51P4O2b2b4b5b6b33VQ2Xp+04ES52PlPrPrPqQ3nQ3mQ3mPSPaQ48P1Q2}P3O2b2b4b5b6b3PlPrPrPqQ3nQ3mQ3mPSP9Q47P1Q2}PCO2b2b4b5b6b33VPwp+08aRSQ2X'2p+08`Rm9GwSPcQ3?Q3?Q2fQ3pQ34Q34Q3oP=PQP0P[PUP`P:PUQ0;Q4xEtP;P]b;b<b:X16p+08hRj/211:7kS53#O[^16P1p+04AS54PCO2b2b4b5b6b3PcQ3?Q3?Q2fQ3pQ34Q34Q3oP=PQP0P[PUQ4yP:PUQ4xp+07NR\+0fI0eP;P]b;b<b:X16p+08gRg,:1S55p+08fS56'2Q53p+07bS57'F[^16P1Q54P4O2b2b4b5b6b35VwQ2t/PwQ51Q2L7uSQ2IQ2}/Nm7GSQ2^PtPRPRQ3JPoPyPyQ38PaQ4TP1Q2GQ2mPCPPO4b2b4b5b6b3PtPRPRQ3JPoPyPyQ38PRQ4PP1Q2GQ2mP4Q27O4b2b4b5b6b33VQ2AQ2`PsPtPtPRQ39PoPoPyPqQ4UP1p+04RS27Q2\P3Q2CO4b2b4b5b6b3PsPtPtPRQ39PoPoPyPtQ4RP1Q27Q2\PCPPO4b2b4b5b6b33VQ1{Q2`PuPsPsPtQ3qQ39Q39PoPqPzP1p+04SS53Q2dP@PiO4b2b4b5b6b3PuPsPsPtQ3qQ39Q39PoQ2fQ44P1Q53Q2dP3Q2CO4b2b4b5b6b33VQ2DPvPuPuPsQ3rQ3qQ3qQ39PlQ4WP1Q2KQ2tP<PhO4b2b4b5b6b3PvPuPuPsQ3rQ3qQ3qQ39PuQ4TP1Q2KQ2tP@PiO4b2b4b5b6b35VfQ2DQ2jPvPvPuQ3sQ3rQ3rQ3qPlQ46P1Q2VQ3DPIPOO4b2b4b5b6b3Q2jPvPvPuQ3sQ3rQ3rQ3qPcQ45P1Q2VQ3DP<PhO4b2b4b5b6b35VfQ1xQ09Q2A'2Q2@'9Q09Q2='2Q2=Q2:'2'9Q2;Q4g'FQ1iQ1K'2Q1MQ4k'FQ1HQ2=p+07iS1M3GP2PbQ2Vp+08iR<H1fQ1a50DQ4JQ2xQ3DPXQ1PDjQ4pQ2I;0^p+04FS4JQ2X50WQ54#lQ2n'9Q1d$1d%OZp+07oS1a,FZ'9p+08:S4W,7_RIQ2TPGP1Q4rp+02\RiQ36D8+0wp+08;R@P1Q1aQ4qH1bP@p+089S2C,31Q2qP@p+07nS58,31Q2XP@p+07mS59,31p+03QS5:P@p+087S5;,31Q5:P@p+088S5<,31Q2XP@p+07lS5=,31Q2XP@p+086S5>,31Q1U20xv1CzCzCzCzCzCzCz40BXkIQ0_Q2RQ1>+0wQ0RQ2RPGPuQ40Q36Q2TD8Q1>Q35PGP2PuQ4rQ36Q2Tg043NQ5<p+07gS2TQ04,M<g044XQ01,]DRIg045bQ4WQ4pQ4W20vu1#mW0Q4WQ1xQ4W20v1W#mW0Q2P208Hj%O<p+07hS01#l[\gp+08kS04>07H7VKX?gQ1M#O\K^?gQ3OQ35Q35Q2iQ40Q3~Q3~Q3|Q4qPQQ1sP[PUQ4rP:PUQ4qP:Q04Q0YQ07#h60?69kUY5gUFXP;P]b;b<b:X16X96p+07JS07,F7Q09/27S5?Q0A'9S5@Q0~p+080S5A,F8'9[[^16^96P1Q2Hp+03SS5BPhPOO4b2b4b5b6b3bCbD+1aPsQ2hE4Q2T,3u&1`uE4N>1_p+07aPmP1p+09=S5CQ4dQ41%EmS5DQ5CQ4dQ5CQ41CCdO4b7Q4Wp+09<S5EPkP?Q5E/KkdQ40DLP@Q4dPGQ2jP1Q2pQ3CQ1EE;X0@PGPvQ4dQ3CQ36D8PGPDp+08<RO,7_Q4cPvQ2@n0100000020000P{Q3CQ36D8Q1@Q3OPGP2PvQ4dQ3CQ36g046lQ58Q5<Q4bQ2AQ2Bg0486PIg049@P@Q2XQ4uQ2pp+090S1@,?1PXQ1pDjX0@p+04=S5FQ2Xp+09>S5GQ1@,:1'H50OX=6Q2Z,]@PfQ5FQ35Q2iQ2iQ3MQ3~Q3|Q3|Q3{Q3FQ4bP1PdQ2qQ30Q2hO4b2b4b5b6b3Q35Q2iQ2iQ3MQ3~Q3|Q3|Q3{Q2iQ4_P1PdQ2qQ2vQ2gO4b2b4b5b6b33VDSp+03^R3eP3POQ2XQ4vPdP1PXQ2=DjX0OP4PfP1E@b7PsQ2hE4Q2:NA0aQ57PSP1Q5GQ4]P|p+08^S2g#ES2vQ5GQ4]Q5GP|CCdO4b7P@Q5Cp+08]R3P?Q5C/K3dP{DLPOQ4]PGQ1{P1PdQ2pQ1BE;X0OPGQ2AQ4]Q2pQ3CD8PGPDp+08=S1B,7_Q4\Q2AP^n0100000020000Q3wQ2pQ3CD8Q1EQ3QPGP2Q2AQ4]Q2pQ3Cg04:JRPQ58Q1aQ4Wg04;T%WPg04<^N=1[p+07cS1Ep+08bS30P1p+09?RPQ4\Q3xQ2vPPQ4\PPQ3xCCdO4b7POQ5GP3P?Q5G/K3dQ3wDLQ1BQ4\Q1BPGQ29P1P9PdQ0_E;W0Q4[Q2AQ4[$03Q2cQ5APIEBP^eP^p+08>S0_Q1xQ0_PGQ2Dp+081S5HQ2<-0F1PNPaP9Q0cGAW0Q4\Q1{Q4\$03PePOPIEBP^eP^p+08?S5IPeQ0\Q5IQ20Q0\Q5IQ4tQ5IPGp+03JS4tp+082S5JP1P~PqPaQ1tGAW0PGQ2>PNPaP9D8PGPDp+08@S1t,7_Q4\Q2>Q4jn0100000020000P{PaP9D8Q0cQ3`PGP2Q2>PNPaP9g04=hRPQ5AQ5HQ2gg04?2%WPg04@<N=1Zp+07fS0cp+08eS5KP1p+09BS5LQ4\P|Q2vQ5LQ4\Q5LP|CCdO4b7Q5Ip+09AS2vP3P?Q2v/K3dP{DLQ1tQ4\Q1tPGP^P1PrPqQ1}E;W0PNP{Q2D>1YNNQ3EQ5JPIEBQ4jeQ4jp+08AS1}Q4vQ1}PGQ2@p+083S5MQ57-0Y1PNPlPrp+01URPGAW0Q01PgP1p+09DS57Q4wP|1]65S5NQ57>0s{|dO4b7Q1}Q4v;0{p+08BS5OQ4wQ5OPGQ2Ap+084S5PP1P~Q2fPlp+01VGAW0PGQ2=PNPlPrD8PGPDp+08CS5Q,7_P~Q2=Q4hn0100000020000Q3xPlPrD8PPQ3gPGP2Q2=PNPlPrg04AFRPQ5MQ5IQ5Mg04BP%WPg04CZN=0`Q1MPjP1p+09ES5RPNP{Q5DQ5RPNQ5RP{CCdO4b7Q5OQ57PkP?Q57/KkdQ3xDLQ5QPNQ5QPGPLP1Q3?Q2fp+01WE;W0Q4_Q3xQ4_P}Q4_Q2PQ4_D[Q3HQ1tPIEBQ4heQ4hp+08DS5DQ3GQ5DPGQ2?Q5>P1Q28CsQ4^PcQ3?Q4?E;W0Q4`P{Q4`Q3{Q4`Q37Q4`D[Q3Ip+085S5SPIEBQ4heQ4hp+08ES5TP`Q5TPGQ2@Q5;Q3IP1CsQ4_Q3JPcp+01YRPE;W0Q5TQ3HQ12Q5TQ2bQ12PGQ2<Q4^PcQ3?D8PGPDp+08FS5U,7_P~Q2<PZn0100000020000P{PcQ3?D8Q4?Q3BPGP2Q2<Q4^PcQ3?g04DdQ5SQ5>PNQ1]Q1_g04EnPIg04G8Q4ap+046S4?Q4aP|Q4aQ3|Q4ap+03NS5VQ4aFYQ2yQ5>PIEBQ2QeQ2QQ5UQ52Q5UP\PR1?1|PXQ1]DjW0Q5UQ52Q5UP\PRP1PXQ1]DjW0PhQ4?Q2WE4Q4jP1E4b8Q1_$0dNA0aQ5=Q04P1p+09HRhPNP|Q30#ES1]PhPNPhP|CCdO4b7Q5Tp+09GS5WPSP?Q5W/KSdP{DLQ5UPNQ5UPGQ1RP1PRQ3JQ1wE;W0PGQ1dPNQ3JPcD8PGPDp+08GS1w,7_Q4]Q1dQ1Kn0100000020000Q3xQ3JPcD8PPQ3YPGP2Q1dPNQ3JPcg04HBRPQ5SQ5MQ5<g04IL%WPg04JVN=0JQ59p+08lS5XP1p+09IS5YQ4]P{Q1]Q5YQ4]Q5YP{CCdO4b7Q5UPhPSP?1KhSdQ3xDLQ1wQ4]Q1wPGQ1bP1PtPRQ0zE;W0Q4cQ1[Q4cQ3XQ4cP}Q4cQ40Q4cQ20Q4cD[D1Q3LQ2CPIEBQ1KeQ1Kp+08HS1[p+07KS0zQ1[PGQ1SQ5<p+07LRhP1CcP~PsPtQ0pE;W0Q1ap+08nP1p+09KRPPhP|Q5NQ40@0sP|dO4b7Q1[Q0z;0{p+08IS5NPhQ5NPGQ1UQ2CP1Q4^PuPsQ0xGAW0PGQ1|P~PsPtD8PGPDp+08JS0x,7_Q4^Q1|Q1In0100000020000P{PsPtD8Q0pQ3]PGP2Q1|P~PsPtg04K`S1|Q5<Q5<POg04LjQ1|#Wg04N4N=1WQ5Ap+08oP1p+09LS5AP~P|p+08dS1|#EQ5AP~Q5AP|CCdO4b7Q5NPPp+08cS0pP?Q0p,KPdP{DLQ0xP~Q0xPGQ1KP1PvPuQ1JE;W0Q4fP{Q4fQ1cQ4fPwQ4fQ3~Q4fQ43Q4fQ5BQ4fFYD1Q35Q2CPIEBQ1IeQ1Ip+08KS4fP\Q4fPGp+02jS1cP@20S1ZQ4_Q2jPvQ1LGAW0Q4gP|Q4gQ1_Q4gQ4zQ4gQ40Q4gQ44Q4gQ3<Q4gFYD1Q3OQ0_PIEBQ1IeQ1Ip+08LS1IQ21Q1IPGQ4|POp+07P00S1Q4`Q2cQ2jQ1NGAW0Q1Ip+07OR~Q1IPGQ4|POP1Q4`Q2cQ2jQ1NGAW0PGQ1SQ4_Q2jPvD8PGPDp+08MS1N,7_Q4aQ1SPin0100000020000P|Q2jPvD8Q1LQ3_PGP2Q1SQ4_Q2jPvg04O>RPP@Q0xP@g04PH%WPg04QRN=0JQ5Mp+092P1p+09OS1LQ4_Q3yQ56#ES1_Q1LQ4_Q1LQ3yCCdO4b7Q1Ip+09NS1JQ5KP?Q1JQ5K'KdP|DLQ1NQ4_Q1NPGQ1HP1PeQ2cQ4FE;W0Q4kP}Q4kP}Q4kQ2JQ4kQ2kQ4kQ42Q4kQ45Q4kQ23Q4kD[D1D1Q3RQ4fPIEBPiePip+08NS2JQ3RQ2JPGQ4|Q0_P1Q1KCcQ4aQ2oPeQ0uE;W0Q4lQ3{Q4lQ3{Q4lQ2aQ4lQ2lQ4lQ43Q4lQ46Q4lQ3AQ4lD[D1D1Q3SQ1BPIEBPiePip+08OS4lp+07RRPQ4lPGQ1XQ5IQ3`P1CcQ4bQ3EQ2oPVE;W0Q4lQ3zQ4lPGQ1XQ5IP1p+07SS2aCcQ4bQ3EQ2oPVE;W0Q4lp+09QS4|Q4m/N5S4F'HQ4lPGQ1XQ5IP1Q4bQ3EQ2oPVGAW0Q4mPGQ1XQ5Ip+09RS1X/H1Q4bQ3EQ2oPVGAX=6PGQ1RQ4aQ2oPeD8PGPDp+08PS4b,7_Q4gQ1RQ1Gn0100000020000P}Q2oPeD8Q0uQ3cPGP2Q1RQ4aQ2oPeg04R\RVQ5IQ5IQ0_g04Sf%WVg04U0N=0`Q5>p+095P1Q1XQ4aQ3{%EjS0uQ1XQ4aQ1XQ3{CCdO4b7Q4lQ4|PgP?Q4|/KgdP}DLQ4bQ4aQ4bPGQ1QP1Q3FQ3Ep+01dE;W0Q4pQ3zQ4pQ3~Q4pQ3~Q4pQ2QQ4pQ54Q4pPzQ4pQ48Q4pQ21Q4pFYD1D1Q2uQ1tPIEBQ1GeQ1Gp+08QS1QQ2:Q1QPGQ1UQ5OP1Q1HCsQ4cQ3GQ3FQ19E;W0PWQ4mPWQ40PWQ40PWQ4hPWQ2qPWQ45PWQ49PWQ22PWFYD1D1Q3;Q1tPIEBQ1GeQ1Gp+08RS22Q4oQ22PGQ1cQ5QQ2<P1CsQ4dQ3HQ3GQ1;E;W0Q22Q28Q22PGQ1cQ5QP1Q4dQ3HQ3GQ1;GAW0PGQ1bQ4cQ3GQ3FD8PGQ1bQ3|Q2QQ3FD8Q19Q3fPGP2Q1bQ4cQ3GQ3Fg04V:Q5QQ5OQ4kQ2GQ28g04WDPIg04XNQ4qQ4hQ4qQ2WQ4qQ41Q4qQ41Q4qQ4jQ4qQ2sQ4qQ46Q4qQ3NQ4qp+03[Q4qFYD1D1D1S3NQ3gQ5QPICIQ2EeQ2Ep+08SS1bQ27Q1bp+08TRVQ46,?1Q5330W0Q2Vp+09VS461:15S19'HQ5350VX=6P6Q1bQ4cQ4cQ2V/:5Q2VQ3|Q3fQ3eQ3eQ3dQ4BQ3ZQ3ZQ4AP=PQP0P[P6Q0;,^Yg01WNS4cPYC~-0pUP;P]b;b<b:X16Q19/P1^16P1PbO1b2b4b5b6b3L0hQ4JQ2VQ3fQ3eQ3eQ3dQ4BQ3ZQ3ZQ4AQ3]Q0zP1Q2yPbQ0RQ0wO4b2b4b5b6b3Q3fQ3eQ3eQ3dQ4BQ3ZQ3ZQ4AQ3eP`P1Q2yPbQ0QQ0lO4b2b4b5b6b33VDSQ2reQ1OP1E4b8Q3NQ3gQ5OPICIQ1^eQ1^Q1bQ29Q1bQ2:90V1W0Q1bQ29Q1GP1FUb8P2Q3GQ2cQ2GQ5WPXPeQ4`PuPsQ3JQ3eQ3dQ3dQ3cQ3ZQ4AQ4AQ4@Q3cQ4`P1Q3IQ25O2b2b4b5b6b3PRQ0QGfQ2feQ4{PeQ4J,21X=6Q2KQ2o/21X=6Q3eQ3dQ3dQ3cQ3ZQ4AQ4AQ4@P=PQQ1~P[PUQ4aP:PUQ4eQ0>EtP;P]b;b<b:X16X96Q1X=u17p+09YS4e,N7S2o/28[^16^96P1Q3:Q3IQ0QO3b2b4b5b6b3Q52Q3VDSPRQ0QDSQ52,2ReQ2KQ55Q3J'2X=6PeQ53Q5J,:1'2X=6Q27Q2j'2Q53/2vPJP<Q27Q53Q54Q2jPvPtGeQ3eQ3dQ3dQ3cQ3ZQ4AQ4AQ4@P=PQQ1~P[PUQ1BP:PUQ4_Q4^EtP;P]b;b<b:X16X96Q4|p+09PS5J,N75G1p+09MS4|Q4e,N8Q4e':5G7[^16^96P1Q3IQ3:Q0PO3b2b4b5b6b3PRQ0QGfQ52Q3VDSQ2t/2ceN:0oNB0nQ2Cp+098S55P1p+09US4{Q4YQ3~Q1_Q4{Q4YQ4{Q3~CCdO4b7Q22p+09TS4`Q5KP?Q4`Q5K'KdQ3|DLQ1bQ4YQ1bPGQ1dP1Q4jQ3HQ1VE;W0PGPZQ4YQ4hQ3GD8PGPZP|Q4hQ3GD8Q1;Q3hPGP2PZQ4YQ4hQ3Gg04YXQ5UQ1QQ1ag04ZbPIg04[lQ4rQ4jQ4rQ4oQ4rQ42Q4rQ42Q4rPLQ4rQ2bQ4rQ47Q4rQ3PQ4rQ2SQ4rD[D1D1D1Q3iQ5UPIEBQ1^eQ1^PVQ4mQ1G-0T1#mX0VQ4sPLQ4sp+03dS3GQ4sQ43Q4sQ43Q4sP^Q4sQ52Q4sQ48Q4sQ4:Q4sQ2UQ4sD[D1D1D1Q3>Q22PIEBQ1^eQ1^p+08US4hQ3>Q2UQ4hp+03fS1;Q2UQ4oQ2[-0P1#mX=6p+03gS5WQ3G00P1#mX=620P71#mPMQ00128>S00\1Q0AP7[Q00P8[21U87P1n2001000000120000000aXB6XA6Q0?20P87#m[^B6^A6P1Q3Gp+03hS3NQ3kQ3jQ3jQ3hQ4DQ3uQ3uQ4CP=PQQ1~P[PUPUQ1up+091S2QP:Q2QE`P;P]b;b<b:X16X96X>MQ0?,98Q0A[^16^96^>MP1Q09Q2O'2Q2LQ2OQ0MO4b2b4b5b6b3O3b7Q3GQ5WQ3jQ3hQ3hQ3fQ3uQ4CQ4CQ4BP=PQP0P[PUPUQ5RQ1`P:Q57E`P;P]b;b<b:X16X>MQ0BQ0@[^16^>MP1Q2`Q3N'2Q2`Q2|O3b2b4b5b6b3Q3jQ3hQ3hQ3fQ3uQ4CQ4CQ4BQ3~Q3|P1Q09Q2`'2Q3NQ2`fYS0BQ2|O5b2b4b5b6b33VDSQ2SQ4oQ3jQ3hQ3hQ3fQ3uQ4CQ4CQ4BPPPQQ1sP[PUPUQ0:p+09FS2S5DUQ2S=DUYP:Q57E`P;P]b;b<b:X16X96Q5?Q0<'9Q0@[^16^96P1Q2`Q3NQ2|O3b2b4b5b6b3Q3jQ3hQ3hQ3fQ3uQ4CQ4CQ4BQ3cP}P1Q3NQ0BO2b2b4b5b6b33VDSQ2WQ1;+0T#meQ3>Q0qE4Q1GP1E4b8Q1GP1E4b8N>1TQ4Wp+099P1Q46Q4YQ3yQ5K#ES0<Q46Q4YQ46Q3yCCdO4b7Q1bQ4{Q1|P?Q4{Q1|'KdP|DLPVQ4YPGQ1RP1PLQ3IQ1zE;X0VPGQ1dQ4YQ4jQ3HD8PGPDQ4h,7_Q4pQ1dQ1Dn0100000020000Q3[Q4jQ3HD8Q1VQ3jPGP2Q1dQ4YQ4jQ3Hg04]6RLQ5DQ1}Phg04^@%WLg04_JN=0NP@p+09:S5DP1p+09WS4jQ4YQ3wQ0<Q4jQ4YQ4jQ3wCCdO4b7PVQ46Q1|P?Q46Q1|'KdQ3[DLQ4hQ4YQ4hPGQ1GP1P^Q2yQ24E;W0POp+09;S1GP1p+09XS46Q50Q3wQ5PQ46Q50Q46Q3wCCdO4b7Q4hp+07WRLQ3[30p+08VS0<Q50Q0<PGQ1SQ1wP1PTQ28Q3KQ1ZGAW0PGQ1KQ4ZP^Q2yD8PGPDp+08WS1Z,7_P~Q1KQ1An0100000020000Q3[P^Q2yD8Q24Q32PGP2Q1KQ4ZP^Q2yg04`TR^Q5NQ1wPWg04a^%W^g04bhN=0NQ1BQ5EP1Q4eQ4ZQ3wQ1_Q4eQ4ZQ4eQ3wCCdO4b7Q0<Q46Q5KP?Q46Q5K'KdQ3[DLQ1ZQ4ZQ1ZPGQ2EP1Q29Q3LQ1\E;W0Q4vQ3[Q4vQ29Q4vQ5WQ4vQ45Q4vQ45Q4vQ2:Q4vQ2{Q4vQ3PQ4vQ4<Q4vQ3zQ4vFYD1D1D1Q3lQ1[PIEBQ1AeQ1Ap+08XS1_Q2NQ1_PGPZQ1IQ3P,?1Q4[Q2:Q3MQ0mGAW0Q1_Q2NQ1_PGPZQ1IP1Q4[Q2:Q3MQ0mGAW0PGQ1OPTQ29Q3LD8PGPDp+08YS0m,7_Q4sQ1OQ1<n0100000020000Q3[Q29Q3LD8Q1\Q3mPGP2Q1OPTQ29Q3Lg04d2R^Q1[Q4hQ1[g04e<%W^g04fFN=0`Q5IQ5GP1p+09[S5GPTQ3w%EgQ5GPTQ5GQ3wCCdO4b7Q1_p+09ZS5IQ56P?Q5IQ56'KdQ3[DLQ0mPTQ0mPGQ1?P1Q2;Q2iQ0oE;W0Q4xQ2eQ4xQ3xQ4xQ2;Q4xQ2LQ4xQ47Q4xQ47Q4xQ2<Q4xQ51Q4xQ4;Q4xQ4=Q4xQ2WQ4xD[D1D1D1D1Q3]Q0<PIEBQ1<eQ1<p+08ZS47Q3\Q47PGQ1PQ4fP1Q2ECsQ4\Q2<Q35Q0rE;W0Q4yQ2{Q4yP{Q4yQ2<Q4yQ2IQ4yQ48Q4yQ48Q4yQ1pQ4yQ2}Q4yQ3TQ4yQ4>Q4yQ4oQ4yD[D1D1D1D1p+05PS3TQ0xPIEBQ1<eQ1<p+08[R^Q4}PGQ1HQ1IQ3TP1CsQ4]Q1pQ3OQ0sE;X0^P^PbPGQ1HQ1IP1Q4~CsQ4]Q1pQ3OQ0sE;X0^P^Q3:PGQ1HQ1IP1Q4]Q1pQ3OQ0sGAX0^PGQ1DQ4\Q2<Q35D8PGPDp+08\RW,7_Q4[Q1DQ1^n0100000020000Q3xQ2<Q35D8Q0rQ34PGP2Q1DQ4\Q2<Q35g04gPQ5NQ4fQ4uQ1;Q3Ng04hZPIg04idP`Q2{P`Q2MP`P|P`Q1pP`Q2^P`Q49P`Q49P`Q2=P`Q2_P`Q4<P`Q4@P`Q3GP`FYD1D1D1D1Q3^Q4fPIEBQ1WeQ1WPWPbp+07dS0rQ2=Q4<,?1PXQ4mDjX0WPWPbQ0rQ2=P1PXQ4mDjX0WQ1Ep+04PS4]Q1EQ0rQ4m701WIQ0HQ1p@0GbXP2Q1iQ3QQ2xPbPXPAPXQ3XQ4]Q0=':S1EQ2M3oX@AQ2wQ2Q,:1S2QQ4]'2Q2k;o1X=6Q2R12b1Q2QQ2R3oX=6Q2eQ3@+02Q4Jp+04VS2Q+02Q2eQ3@Q4JQ2QPJp+093S2kQ3:Q2NQ52Q2RQ2RQ2R#EGePJQ2kQ33Q2wQ2}Q2wQ2wQ2VGeJ0mQ34Q3oQ3oQ3nQ4KQ4IQ4IQ4HP=PQP0P[Q3~=DUYQ4iQ4i5DU60lUP;P]b;b<b:X16Q4{,:1S33Q4{;G1Q33Q333o^16P1PdO1b2b4b5b6b3PnQ0SGfQ2{Q0RDSQ3WQ5FQ2{3oeQ2<Q29E4Q2wQ4ZQ3:Q22'2Q2NQ22'2PJQ2kQ3:Q2NQ52Q22Q22Q4kGeQ34Q3oQ3oQ3nQ4KQ4IQ4IQ4Hp+07YS4kPQQ1~P[PUQ1wP:PUPLP:Q40Q5T5DUFXP;P]b;b<b:X16X96Q5GQ5I,N75G1p+09aS52,28Q46,:8Q46Q473G[[^16^96P1Q3SPdQ1vQ0KO4S2kb2b4b5b6b3Q2{Q0RGfQ4zQ22'2ePAPXQ1EQ1b'2X@AQ2RQ4ZQ2KQ53PwQ34Q3oQ3oQ3nQ4KQ4IQ4IQ4HQ3hQ4\Q2kb2b4b5b6b3PnQ0SGfQ4?eQ2<Q29E4N90kE4Q2b&0UbE4Q1=P1E4b8Q2UNA0aQ5OQ2vP1p+09^S2vQ4XP{%E<S2UQ2vQ4XQ2vP{CCdO4b7P^p+09]S2bPjP?Q2b/KjdQ3xDLPWQ4XPGPEP1Q2=Q3QQ0tE;X0WPGQ2EQ4XQ1pQ3OD8PGPD17_3Q1ZQ5N5i_Q2EQ1mn0100000020000Q3vQ1pQ3OD8Q0sQ3pPGP2Q2EQ4XQ1pQ3Og04jnS1pQ1ZQ1ZQ47g04l8Q1p#Wg04mBN=0JQ5QQ5LP1p+09_S5LQ4XQ3[Q2UQ5LQ4XQ5LQ3[CCdO4b7PWQ2vPjP?Q2v/KjdQ3vDLP3Q4XPGQ18P1Q2>Q3RQ1hE;X03Q07Q4oQ07Q51Q07Q2}Q07P}Q07Q2>Q07Q2OQ07Q3PQ07Q3PQ07Q1iQ07Q2FQ07Q4=Q07Q3ZQ07Q1;Q07D[D1D1D1D1D1Q3aQ1_PIEBQ1meQ1mQ2gQ3TQ2gPGQ1FQ47P1Q1<CcQ4ZQ1iQ3SQ1YE;W0Q0zQ3GQ0zQ2}Q0zQ2_Q0zQ3{Q0zQ1iQ0zPfQ0zQ4:Q0zQ4:Q0zQ2?Q0zPnQ0zQ4>Q0zQ4BQ0zQ5WQ0zD[D1D1D1D1D1Q3bPWPIEBQ1meQ1mPkQ3bPGQ1DP^Q3_P1CcPTQ2?Q3`Q1TE;X0kPkQ5VPGQ1DP^P1Q3cCcPTQ2?Q3`Q1TE;X0kPkQ2mPGQ1DP^Q2HP1CcPTQ2?Q3`Q1TE;X0kPkQ37PGQ1DP^P1PTQ2?Q3`Q1TGAX0kPGQ1AQ4ZQ1iQ3SD8PGPD17_mQ1I9i_3Q1AQ1mn0100000020000Q3wQ1iQ3SD8Q1YPoPGP2Q1AQ4ZQ1iQ3Sg04nLP3Q0mQ4YPaPqg04oVPIg050`PhQ2PPhQ2[PhQ2_PhQ2~PhQ3|PhQ2?PhQ2YPhQ4;PhQ4;PhQ2@PhQ4]PhQ4@PhQ4CPhQ3NPhFYD1D1D1D1D1Q3cQ0mPIEBQ1leQ1lPmQ3^Q01Q2@Q5R006T,?1Q06P9DjX0mPmPeQ01Q2@Q4`,?1Q06P9DjX0mQ3Ep+09cS1lQ4`,:1'H90SeX=6Q2c,]mp+09bS0m/ZeQ3EPoPyPyQ38Q4OQ4NQ4NQ4MP=PQP0P[PUQ5OP:Q1JH0IP;P]b;b<b:X16Q0m/21Q0@[^16P1Q2yQ0VO2b2b4b5b6b3PoPyPyQ38Q4OQ4NQ4NQ4MP=PQP0P[PUQ1}P:Q4kH0IP;P]b;b<b:X16Q52p+09`S1}5G11F7WS4C[^16P1Q2yQ0KO2b2b4b5b6b33VDSPcePcPSPeQ1MQ2AP1Q06PaDjX0SQ01PuQ01Q1M?01aWIQ0BQ2@Q0680GeP2Q2BQ3;Q36PeQ06PAPXQ2VQ0=':S0==owsX@AQ3Ep+08mS36,:1S01Q2V'2Q2s;o1X=6Pd12e1p+096,:1Q3F3oX=6Q2{Q2N+02Q2eQ2Q+02Q2{Q2NQ2eQ2QPJQ55Q2cQ2jPRPdPd%EdGePJQ55Q3CQ2pQ4]Q3EQ3EPvGeJ0mQ39PoPoPyQ4QQ4OQ4OQ4NQ0XQ4`Q4l+00Q0W+0O;\=PQQ1r20M6>7x7P[PUQ03-0L6RvQ4b+04Q0>5DUP:PUQ5TP:PUp+07`S5T=DUvP:Q4aQ0>5DU209U460lUH0IFXP;P]b;b<b:X16X96XE6X>MQ1l=u87p+09fR4p+09eRv5G7Q0p/2BQ5L,:>?GFB002C[[[^16^96^E6^>MP1Q2xQ3iPlQ3KQ0`Q0VQ0{O7b2b4b5b6b3Q2KQ1oGfPtQ0qDSQ2XQ2q;oteQ2?Q2=E4Q3EQ01Q1_'2X=6Q2cQ1Z'2Q2jQ1Z'2PJQ55Q2cQ2jPRQ1ZQ1ZQ4qGeQ39PoPoPyQ4QQ4OQ4OQ4NP=PQP0P[PUQ5OP:PUQ4^Q5NEtP;P]b;b<b:X16Q0mQ525G1Q5I,:7?GF3[^16P1Q3KQ0VO2b2b4b5b6b3PtQ0qGfQ1Z,2cePAPXQ0=Q1_'2X@APdPNQ3:Q3@Q2nQ39PoPoPyQ4QQ4OQ4OQ4NQ3mQ4_P1Q3iPlQ0vQ15O4b2b4b5b6b3Q2KQ1oGfPweQ2?Q2=E4N90kE4PsP1E@b7Q3^Q0CE4Q1mP1E4b8PlQ5<,F1X=6208H<Q5Ap+08jRN#OQ2C#l[[Q5AQ5X>07H7VKW?Q5AQ4W#O\K]?Q39PoPoPyQ4QQ4OQ4OQ4NP=PQP0P[PUPUQ1`Q1tP:Q0YQ02#h60?69kUYE`P;P]b;b<b:X16X>MQ4e,F1,97Q1t,F7S1t[^16^>MP1%lsPsQ0OO3b2b4b5b6b3bCbDQ52/ZqPyQ38Q38Q3pQ4NQ4MQ4MQ4LP=PQP0P[PUPUQ1@Q1`P:Q1JE`P;P]b;b<b:X16X>M%l1RA/97Q0@[^16^>MP1Q3JPRQ0MO3b2b4b5b6b3PyQ38Q38Q3pQ4NQ4MQ4MQ4LP=PQP0P[PUPUQ1`Q0_P:Q4kE`P;P]b;b<b:X16X>MQ4j,F1RF,97Q4C[^16^>MP1%lRPRQ0MO3b2b4b5b6b35VlDS-1RqNA1QQ5UQ5RP1Q0mQ4XQ3xQ0uQ0mQ4XQ0mQ3xCCdO4b7PkQ52PgP?Q52/KgdQ3wDLPmQ4XPGQ18P1Q2@Q2uQ1kE;X0mPmPrPGQ2EPkP1Q4YQ2@Q2uQ1kGAX0mPGQ1<Q4XQ2?Q3`D8PGPD17_SQ1N9i_WQ1<Q1jn0100000020000Q3wQ2?Q3`D8Q1TQ39PGP2Q1<Q4XQ2?Q3`g051jRCPWPWQ22g0534%WCg054>N=1PQ1wQ2SP1Q1lQ4XQ3xQ0uQ1lQ4XQ1lQ3xCCdO4b7PmQ0mPgP?Q0m/KgdQ3wDLPSQ4XPGp+02ERCP1Q2AQ3;Q3}E;X0SP\PaP\Q5VP\Q5WP\Q2FP\PnP\Q40P\Q2AP\Q2\P\Q4<P\Q4<P\Q1{P\Q27P\Q3ZP\Q4DP\Q2IP\D[D1D1D1D1D1D1Q3eP3PIEBQ1jeQ1jQ30Q3cQ30PGQ1APkQ17-0C1Q4ZQ1{Q3gp+026RkGAW0P~PqP~Q2HP~Q3NP~PnP~Q4]P~Q41P~Q1{P~Q2dP~Q3UP~Q3UP~Q2BP~Q53P~Q4BP~Q4EP~Q2^P~D[D1D1D1D1D1D1Q3fPVPIEBQ1jeQ1jQ0pQ0cQ0pPGQ1^PmQ3e00C1PTQ2BQ3ip+027R3GAW0Q0pQ2ZQ0pPGQ1^PmQ2T-0C1PTQ2BQ3iP3GAW0Q0p1Nw5RS,HvQ0pPGQ1^PmP1PTQ2BQ3iP3GAW0PwPGQ1^Pm1H41PTQ2BQ3iP3GAX=6PGQ18Q4ZQ1{Q3gD8PGPDQ1|,7_Q4aQ18Q11n0100000020000P{Q1{Q3gD8PkQ3sPGP2Q18Q4ZQ1{Q3gg055HRkQ1QQ1QQ22g056R%Wkg057\N=0JQ0xQ5YP1P4Q4ZP|%ENP4Q4ZP4P|CCdO4b7Q0pPvP<P?1Kv<dP{DLQ1|Q4ZQ1|PGQ13P1Q2DQ3>Q0yE;W0p+07QRkQ2ZPkPlPkQ5:PkQ2IPkQ2GPkQ27PkQ43PkQ2DPkQ3DPkQ4>PkQ4>PkQ4tPkQ2VPkQ3uPkQ4GPkQ2OPkFYD1D1D1D1D1D1Q3jQ22PIEBQ11eQ11Q5KQ2dQ5KPGQ1<PVP1PCCcQ4[Q4tQ3BQ10E;W0PPQ2XPPQ2fPPp+03RR3PPQ2^PPQ27PPQ53PPQ44PPQ4tPPQ2rPPQ4@PPQ4@PPQ1xPPQ2QPPQ4DPPQ4HPPPfPPFYD1D1D1D1D1D1Q3kPVPIEBQ11eQ11Q56Q3WQ56PGQ1=Q4hQ3DP1CcQ4\Q1xQ3YQ0}E;W0Q56Q2dQ56PGQ1=Q4hP1Q4\Q1xQ3YQ0}GAW0PGQ1nQ4[Q4tQ3BD8PGQ1nQ3yQ1{Q3BD8Q10Q3tPGP2Q1nQ4[Q4tQ3Bg058fQ0<PVP\P9Q2dg05:0PIg05;:Q2aQ2^Q2aPwQ2aQ3?Q2aQ5BQ2aQ2`Q2aQ53Q2aQ2KQ2aPzQ2aQ1xQ2aQ4?Q2aQ4AQ2aQ4AQ2aQ2PQ2aQ2NQ2aQ4EQ2aQ4IQ2aQ2YQ2aFYD1D1D1D1D1D1D1RzQ32Q0<PICIQ4neQ4nPgPaQ4E,?1=0jqX0gPlp+09jR\Q19'H=0jqX=6P6PgP`P`1:l5PlQ4=Q3tQ3=Q3=PpQ4VQ4UQ4UQ4TP=PQP0P[P6Q4vQ0;'^Q4cQ4vC~-0pUP;P]b;b<b:X16Q1},:1Rf/:5/Pf^16P1PtO1b2b4b5b6b3L0hQ53Q3tQ3=Q3=PpQ4VQ4UQ4UQ4TQ3pQ4iP1Q3]PtQ15Q0LO4b2b4b5b6b3Q3tQ3=Q3=PpQ4VQ4UQ4UQ4TPoQ4gP1Q3]PtQ0\Q0UO4b2b4b5b6b35VlDSA0gnaeQ1yP1E4b8PzQ32PVPICIp+02;RzePzPgQ2tQ3D90j1X0gPgQ2tQ11P1FUb8P2PXQ3YQ4tP9Q37Q3Y<1OaP2Q3YQ3;P9Q5GPXQ3gQ4wQ3SQ3RQ35Q3=PpPpQ3sQ4UQ4TQ4TQ4SQ3sQ4wP1Q3\fyRXO2b2b4b5b6b3Q3OQ14GfQ3LeQ0SQ3gQ53,21X=6PrQ3i/21X=6Q3=PpPpQ3sQ4UQ4TQ4TQ4SP=PQQ1~P[PUQ4xP:PUQ07Q0>Q4f'^EtP;P]b;b<b:X16X96Au147p+09mR4Q52,:85u7[^16^96P1PRQ3\Q0\O3b2b4b5b6b3Q27Q1vDSQ3OQ14DSQ3OQ27'2ePrQ1GQ355G1X=6Q3gQ5U,:1,29X=6Q2u,2dQ3CQ3`'2PJQ5CPdQ3CPnQ2uQ3`Q3QGeQ3=PpPpQ3sQ4UQ4TQ4TQ4SP=PQQ1~P[PUQ1QP:PUQ49Q4uEtP;P]b;b<b:X16X96p+09d,N79G1vQ52,:7Q521N84/:43G[^16^96P1Q3\PRQ14O3b2b4b5b6b3Q3OQ14GfQ27Q1vDSQ4JQ2i'2eN:0oK1NNB0nQ1NQ5AP1p+09iR4Q4[P}Q5X#ERvP4Q4[P4P}CCdO4b7Q56p+09hRnQ04P?Q04,KndQ3yDLPgQ4[PGQ1WP1Q2DQ3lPzE;X0gPGQ18Q4[Q2BQ3YD8PGPD17_jAi_^VQ18Q1gn0100000020000Q3yQ2BQ3YD8Q0}Q3vPGP2Q18Q4[Q2BQ3Yg05<DRzP^PVPTg05=N%Wzg05>XN=0NQ2JQ4|P1P\PTP}PvP\PTP\P}CCdO4b7PgP4Q04P?Q04,K4dQ3yDLPjPTPGQ1yP1Q4tQ3\Q4nE;X0jQ4lQ1JP1p+09kRTQ59P}Q4e#EPTQ59PTP}CCdO4b7Q5=Q3y50jP<Q59PGQ1<Q2gP1Q4\Q1xQ3]Q1eGAX0<PGQ16Q4[Q4tQ3\D8PGPD17_NQ50Q16Q1Tn0100000020000Q3yQ4tQ3\D8Q4nQ3wPGP2Q16Q4[Q4tQ3\g05?bR_P^Q5KPkg05@l%W_g05B6N=0NQ4bQ1LP1p+09lR_Q1aP}Q5G#EP_Q1aP_P}CCdO4b7P<PTQ5IP?Q5I,KTdQ3yDLPNQ1aPGQ3}P1Q2PQ3TQ1fE;X0NPLQ3yPLQ2YPLQ2lPLPtPLQ3APLQ2mPLQ2NPLQ3@PLQ48PLQ2HPLQ2XPLQ3uPLQ3uPLQ20PLQ2xPLQ4IPLQ4NPLQ2tPLFYD1D1D1D1D1D1D1Q3oQ56PIEBQ1TeQ1TQ04Q54Q04PGQ1nQ2gQ4I,?1Q5HQ37Q3^Q1gGAW0Q04Q54Q04PGQ1nQ2gP1Q5HQ37Q3^Q1gGAW0Q1f-1M2Q54/?5Q54$0UE4Q1gP1E4b8P}P1E@b7EJP}P1E@b7P}P1E@b7EJP}P1E@b7EJQ2tQ3W'}Q3DQ3XQ3=PpPpQ3sQ4UQ4TQ4TQ4SP|Q36P1Q2ZQ5FQ0gO3b2b4b5b6b3Q3=PpPpQ3sQ4UQ4TQ4TQ4SQ39Q4:P1Q2ZQ0qO2b2b4b5b6b3H0^E4PCP1E4b8PCP1E4b8P|P1E@b7EJPS&0jwDSQ2ZQ0c+0CPwP5Q3rQ3qQ3qQ39Q4RQ4PQ4PQ4QQ4XP<P1Q2lQ2nQ0nO3b2b4b5b6b3Q3rQ3qQ3qQ39Q56-08HQ1X%Og%l@[[Q1XB07H<7VKW?Q1X%OO\K]?Q4TQ4SQ4SQ4RP=PQP0P[PUPUQ1`Q0Y9DUYP:Q0YQ05#h60?69kUYE`P;P]b;b<b:X16X>MQ31,97Q1t[^16^>MP1Q09Q2q'2Q2qQ0gO3b2b4b5b6b3bCbDH1GE4Q3dQ0JE4Q17P1E4b8Q17P1E4b8Q3xP1E@b7EJPaQ2fPoPyPyQ38Q4OQ4NQ4NQ4MP=PQP0P[PUPUQ1@Q0_P:Q1JQ0_5gUE`P;P]b;b<b:X1619AFQ0@Q46,F7'9[^16P1PtQ0NO2b2b4b5b6b3+1IE4Q3xP1E@b7EJQ5VQ2m'}Q2HQ2\PyQ38Q38Q3pQ4NQ4MQ4MQ4LP=PQQ1~P[PUQ5DP:PUQ5JQ1u5gUP:Q0_FXP;P]b;b<b:X16X96X>MQ0?Q5?/9>Q0~Q00'9[[^16^96^>MP1Q4?Q2d'2Q3<Q4?Q0TQ1oO5b2b4b5b6b3PyQ38Q38Q3pQ4NQ4MQ4MQ4LQ3nQ45P1Q3<Q0SO2b2b4b5b6b3H0^E4Q3bQ15E4Q3^Q0CE4Q1<P1E4b8Q1<P1E4b8Q3[P1E@b7EJP{P1E@b7EJQ4}-0DbQ2wQ1LQ3oQ3nQ3nQ3mQ4IQ4HQ4HQ4GQ0XQ4fQ0XQ06-0@6Q57Q08+00+00Q0W+0OP=D1PQQ1~P[PUQ5UP:PUQ4kP:PUp+07VRbP:PUQ4KP:PpFXFXP;P]b;b<b:X16X96Q5IQ2o5G1p+09\=u87Q52,2>12WB%OB1FB^'9[[[[^16^96P1Q3RQ2pQ0wQ1vQ0`Q0KO6b2b4b5b6b3Q3oQ3nQ3nQ3mQ4IQ4HQ4HQ4GP=PQQ1qP[Q0;Q0_5DUQ0_Q5O5kU5gUP;P]b;b<b:p+09SR=#OQ4h,F='9P1b2b4b5b6b3H1JE4Q3]Q0KE4Q2EP1E4b8Q2EP1E4b8Q3wP1E@b7EJQ2{Q3DE4p+02UP1E4b8Q3wP1E@b7EJQ3wP1E@b7Q3wP1E@b7EJQ3yP1E@b7EJQ3~P1E@b7EJQ2;Q4o+0DQ2;Q3GQ3eQ3dQ3dQ3cQ3ZQ4AQ4AQ4@p+07UR=PQQ1sP[PUPbP:PUP=P:Q34FXP;P]b;b<b:X16X96Q5T,F7Q5@Q0~Q4b,F8'9[[^16^96P1Q2[Q2LQ0IfWR8O4b2b4b5b6b341FE4Q1HP1E4b8Q1HP1E4b8Q3{P1E@b7EJQ4FQ4m$0jDSQ3z/}PQ4mP5Q3bQ3aQ3aQ3_Q4>Q4=Q4=Q3UQ4DQ4hP1Q1;Q2W'2Q1;Q0GO3b2b4b5b6b3Q3bQ3aQ3aQ3_Q4>Q4=Q4=Q3UP{Q3xP1Q09Q1;'2Q2WQ1;Q0FQ0GO5b2b4b5b6b3H0^E4Q3SQ1oE4Q1KP1E4b8Q1KP1E4b8Q3yP1E@b7EJQ21-0S~Q21$1KE4PZP1E4b8PZP1E4b8P|P1E@b7EJP|P1E@b7Q1dP1E4b8P{P1E@b7EJP|P1E@b7EJQ3HQ0BE4Q3H00D`Q3H$1LE4Q28P1E4b8Q28P1E4b8P{P1E@b7EJP|P1E@b7Q29P1E4b8P|P1E@b7EJQ2PQ20+0FQ37Q5:Q3SQ3RQ3RQ3QQ43Q42Q42Q41Q3BQ5UP1P3Q23PxO3b2b4b5b6b3Q3SQ3RQ3RQ3QQ43Q42Q42Q41Q2iQ3mP1P3Q2zO2b2b4b5b6b3H1EE4PeQ0GE4Q2<P1E4b8Q2<P1E4b8Q3xP1E@b7EJP|P1E@b7EJQ41P1E@b7EJQ0JQ0{Q26'9PiPuQ58PICIQ0JeQ0JP@Q4qQ4r90O1X0@P@Q4qQ1>P1FUb8Q0{Q26PiPuQ5<PICIQ0{eQ0{P@Q2qQ2s90O1X0@P@Q2qQ0]P1FUb8Q15Q0DPiPuQ59PICIQ15eQ15P@Q2XQ3zQ2]Q0eP1E4b8Q0\Q0EPiPuQ5=PICIQ0\eQ0\P@Q5:Q2HQ5VQ0dP1E4b8Q14Q0FPiPuQ5>PICIQ14eQ14P@Q5:Q2HQ5VQ1:P1E4b8Q0CQ0GPiPuQ5;PICIQ0SeQ0SP@PsQ3zQ2hQ1CP1E4b8Q0VQ0HPiPup+07kPICIQ0VeQ0VP@Q2XQ3zQ2]Q0aP1E4b8Q0KQ0IPiPuQ5SPICIQ0KeQ0KP@Q1UQ1c90O1X0@P@Q1UQ0^P1FUb8Q0[P8PiPuQ5MPICIQ0[eQ0[P@PcQ3J90O1X0@P@PcQ0bP1FUb8Q0gQ3VPiPup+07MPICIQ0geQ0gP@Q3?A0O1cX0@P@Q3?Q0hP1FUb8Q0qQ0BPiPuQ5PPICIQ0qeQ0qP@Q3JA0O1RX0@P@Q3JQ0fP1FUb8Q0nQ2|PiPuPhPICIQ0neQ0nP@Q2fQ3?90O1X0@P@Q2fQ0kP1FUb8Q1vQ0MPiPuQ0zPICIQ1veQ1vP@PlQ2f90O1X0@P@PlQ0jP1FUb8Q0wQ0NPiPuQ07PICIQ0weQ0wP@PrA0O1lX0@P@PrQ0ZP1FUb8Q0lQ0OPiPup+07IPICIQ0leQ0lP@PqA0O1rX0@P@PqQ0iP1FUb8Q25Q0PPiPuP`PICIQ25eQ25P@PaA0O1qX0@P@PaQ0LP1FUb8Q1oQ0QPiPuQ4yPICIQ1oeQ1oP@P9A0O1aX0@P@P9Q0UP1FUb8Q0|Q0TPiPuQ4xPICIQ0|eQ0|P@PdA0O19X0@P@PdPXP1FUb8PiPuQ4wPICIQ0TeQ0TP@Q2pA0O1dX0@P@Q2pQ12P1FUb8FpFpFpFpFpFpFpFpFpQ0ReH0]H1DbQWMW[W\WZW_WJW^WLW]WKWWaaaaaWXWYaWNWOaaW`WaWVWRWUWSWTWPaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWbaaaXl6aaaaaaaaaaaaaaaaaaaaaaaaaaaaaXi6aaaXc6aaaaaXf6aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaXg6aaaaaaXe6aaaaaaaaaaaaXd6aaaaaaaaaaaaXn6aXmEWhaaaaaaaaaaaaaaaWjaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.


(* [comment removed for export] *)
Lemma sw_retry_b : forall regs mem rom (su f fd io cnt n0 n1 rem : Z) (b1 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 2 ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0xc6000 <= f)%Z -> (f + 232 <= 0xf8ac0)%Z ->
  (su - 104 <= io)%Z -> (io + 32 <= su - 72)%Z ->
  (0 <= n0 < cnt)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z -> (cnt - n0 <= n1)%Z -> (n1 < 2^62)%Z ->
  (bv_unsigned b1 + n1 <= 2^64)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 16)) 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n1)) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 < fd < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xae5f4 : word) mem rom)
      (mkst regs' (0xae5e4 : word)
        (wbytes (wbytes mem (Z_to_bv 64 (io + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0)))))
                (Z_to_bv 64 (io + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (n1 - (cnt - n0))))) rom)
    /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (io + 16) /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 (io + 16)
    /\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
    /\ sw_regs_but regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0143 ()) ["FPX_1"] "h01bh14__x1h27__arithh37__sat10h46__sat7h56__sat8h66__sat9h71Hh84__x2h92gHh:4__ffh;8__varmaph<5__with=1zh>4__p1h?4__x3h@2HahA1nhB1xhC1mhD2b1hE7__sat11hF7__sat12hG2b2hH1ohI1yhJ2B1hK2CRhL2FDhM3FhihN3FlohO3Ha0hP3Hb1hQ3Hs1hR3Hs2hS3Hs3hT3Hs6hU3HsphV4IOhihW4IOlohX3Mb1hY3MfdhZ3Mn0h[3Mn1h\2N0h]2N1h^4N1hih_3REMh`3SOKha4SUhihb4SUlohc3cnthd1fhe2fdhf2iohg3memhh2n0hi2n1hj4regshk5regs'hl3remhm3romhn2sup%0p%1p%2p%3p%4p%5p&0p&1p;1p;2p;5p;3p;4p;6p;>p;Ap;=p;8p;:p;Bp;;p;9p;7p;<p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004`R1p4p710R2p8p1005>p4p710P2p8g005]j14Tg006Bj1lTg006`j1iTg007Cj16Tg007hj1RTg008Fj1>Tg00>Gk20@Tg00?0k118Tg00:Mk20>Tg00@fk117Tg009?k116Tg009jk20mTg00;0k511Tg008ej30Tg00;TR2j23Tg00<0k11hTg00<Nk20jTg00<gR3j28Tg00=Dk41aTg00=gR4k10VTg00AIk10dTg00Akk20QTg00BHk10bTg00Bhk30BTg00DMk30STg00CKk31ETg00Y<j2_Tg00K^j2Ek11;Tg00M]j3mTg00LDk21<Tg00MAj2ATg00Ldj2STg00E\k107Tg00ORj2BTg00H6k10pTg00PFk20PTg00Pnk30NTg00SOj4OTg03^Rk20_Tg00QRk20=Tg00]4k206Tg00I:j2eTg00Sok215Tg03`lk20<Tg00F\k20MTg00G:k114Tg00GXk113Tg00HXk212Tg00ITk210Tg00J@k40~Tg00K2k10^Tg00UCj27Tg00Uoj22Tg00XJj59Tg00NJk20\Tg00\Bk10}Tg00Tak20HTg01>\k10[Tg00Yfj3<Tg03_Fk20ZTg00^Zk20GTg00`Uk30kTg00Vak21jTg00WAk21iTg03`9k20WTg00]gk20FTg03a`k20|Tg00[4S00j2;Tg00dNj3YTg00eIk41gTg03UWk11fTg03bkk20zTg03c^k21`TP1j65Tg03dik11_Tg03egm>1^Tg00i`j2JTg010;j6?Tg010Wk10hTg011[mA0gTg0164m=1ZTg03f`m=1XTg015>m=0fTg013Rm=0TTg03gWm=1TTg012Pj4KTg01DHk40;Tg01Njk80vTg01OGm:0uTg00jCmB0tTg03hMk20OTg05C@k21QTg05C`m>1PTg00him=0RTg01:km;1OTg00ZZk20:Tg00lek60sTg03jDm90qTg01;dk21LTg01<kmA1KTg03kGm=1JTg00aPk31ITg01PHk71GTg01=`k21FTg01Bgk40aTg01?Rk21HTg03mok40wTg03o8k31DTg05DZk21MTg05Edk41NTg01Qnk40`Tg01Cnk41CTg00?Yk31BTg01E3k70CTg01EWk31STg01Gak70xTg01JOk31ATg01F:m<1VTg00E0k21@Tg00F<j3nTg01HEk809Tg01F_k41?Tg01Hik31>Tg01IHk41=Tg01IimB1\Tg01LIm<1]Tg01K2k40yTg01Lnk30iTg01Mjk11:Tg00l:k41bTg01G=k619Tg01QJk71dTg01RIk71eTf0R1#4#4p=s%41#Rp>0U%41#4#4#4#4#4#4#4p>0A%41#4#4#4p>0?%41#4#4#Rp=V%61#6#4#4p>0L%61#6p>0l%41#6p=o%41#6#4#6p>0Y%61#4p>0E%>1#>#>#>p>1[%>1#>#>#>#>#>#>#>p>1U%>1#>#>#>#>#>#>#>#>#>#>#>#>#>#>#>p>08%41#6#4#6#6#6#4#4p>02%61#4#6#6p=x%61#4#4#Rp=`%61#6#6#6#6#6#6#6p>05g01ScR5/A1p=z1351p=Fg01SER6f1R7<1B1p=ff2R8g01TAR9g01T`R:P:g01U@R;P6P7g01U`R<P1H0;g01VGR=K0Cp=Cf3R>/_81_71506p=@%61#6#6#6p>0]%41#6#4#6#6#6#4#4#6#6#4#4p=rg01X5R?:0B71p==%41#6#4#6#6#6p=~%41#4#6#6p>0X%41#4#6#4p=}1e61p=HA0671p=QP8P9P:P:P;P6P7g01VgR@P1H0;P=K0Cp=U%41#6#6#6p>1Y%61#6#6#4p>00B1S671p>01%R1>0B7?p=M20m61p=aP8P9P:P:P;P7P1K0xp=bB1A671p=[g01XQRAP6P6P6P4P4f5R4f4RBP>P8P7P1N<1Vp>0eg01_i-1@1p>031S87/31p=c18>81S71'3p=t1887/31p=Ng01_=RC?n71p=T1A71,;8p=gf6RDP9P:P:P;P4PBP>P9P:P:P;P8P7P1L09L09p=PP4P9P:P:P;PBP>P8P9P:P:P;P6P7P<P1H0;P=K0CL09p=|P6P7P@P1H0;p>0oPBP9P:P:P;P>P8P7P9P:P:P;P1P=K0CL09p>0nP>P9P:P:P;P8P7P1L09p={P6P8P7P1H1?p=]g01ZYR@g01`UR<701p=qB1>651p>0KP8P7P;P1H1=p=pP6P6P6P6P6P6P3P1P7P8P3P>PBP4PDf7R3f8REf9RFNB1\p>0JP6P6P2P3P2PDP4PBP>P8P7P1N<1]p=jg01Y0R2P8P7P1H0yp>0I20F719<>8p=y&0719n879nB>9nD4p=\An8719nB>p=1206719<>8p=dP3A<D4BP>P8P7D9>0i21p=G1;71,;8p>0DP2P>P8P7H0y=0B1p=hB0i271p>0{1287=0>1p>1cA0>87/;1p>04B0B>87=0B1p=IP4PBP>P8P7D9>0i21p=:P6PBP>P8P7P1E5p=Z&1:1,e@p=WAn4B>P8P7P1CKp=D&0719n87p>1W&0719n879nB>p=^P7P9P:P:P;P1P=K0Cp>1RPDP4PB1e>8P7P1E5p=XP6P3PDP4PBP>P8H1bP7P1E5p=kP7P9P:P:P;P1J19p>0cP4P9P:P:P;PBP9P:P:P;P>P8K0xP7P1L09p=u1371-0:8p=wP8P9P:P:P;P7P1K1dp>0rP2P4PBP>P8P7P1K1ep=LPDP4PBP>P8P7P1H0`H0`p=vg01\5R=#4RG#4RH#4RI#4RJ#4S01#4RK#lg01\ZRL%lI#iP0%6=RM#6RN#4RO#sS02$0UP6%4K$0A$0A$0ARP#4RQ#RP6&0?Q$0A#VP6%4MRQ#4RR#4RS$0L$0A#VP6%6O#VP6&0l=$0L#o$0Y$0E#s#VP6%6QRT#4RU#4$0UP6Q01#RP6%6HRV#4RW#4$0UP6%6NRN#6RX#4g01]8%RKP6g01]]RK#>RY#>RZ#>R[#>S03$1[R\$1U$08$08$08$08$08$08PA%RIP6%RJP6%RSP6%VNP6%RPP6&02=#x$0L#`P6%6J$0UP6%6XS04$05RX$0l$05$05$05$05$05$05#RP6%lTPLQ04#RP6%RGRJ#zp-0RP%FJPPQ03-0@6&186RS20@6[PS20@6ZPS20@6Y20@6KS05'fPS20>6Q&176RK%6GRY-0>6PK&166RZ20m65R[20>6=R]3CPZP9P:P:P;I11R9%i1R^%i7R_P8P7P8P1C@R`%i>?087Ra[]G]D^ALRbPP&02=#x$0]#VP6%lRPL&02=#x$0]#`P6%r=$0?#VP6%lYRc#iP0%lQRQ%RHRH'=%iQ%r=$0?#`P6%~=$0X$0?#o#VP6%~=$0X$0?#o#`P6%r=#}#VP6%r=#}#`P6%r=$0X#VP6%r=$0X#`P61371Rd$1hXI6XB620jdd^I6^B6P6P6g01^<1871H1aRd#HXC6XA61Qdd^C6^A6&0V1S06#HXBAQ06Q06'Q^BA&0V\P6%r=#o#s#VP620>6GRG9UZ]P9%r=#o#s#`P6%r=$0Y#VP6%4YRd#6Re#lPL&02=#x$1Y#`P6%~=#}$00#s#VP6%~=#}$00#s#`P6%~=#}$00#o#VP6%~=#}$00#o#`P6Q03$0VP6AUZ[]P9%~=#}$00$0E#VP6%~=#}$00$0E#`P6&02=#x#x#VP6&02=#x#x#`P6&02=#x$0L#VP6201]GPKAUZG]P9ACZ]GP9fvS07#iP0Q07$0dP01McdfRS08%6V,McfSS091McWfTS0:%6YRY#4,McfUS0;1McVfVS0<1=cJfWS0=f{S0>f|S0?'8P6ftS0@#RP6Q0@-0QJP6p+01AS0A$0bP0%6I,Mcf\S0B1McYf]S0C1McRf^S0D%4d,Mcf_S0E1McOf`S0F1McTfaS0G1McNfbS0HB0Bc5?fcS0IfsS0J-0QJP6p+01@S0K#FRNPPfpROfoS0L'fPS%aJS0Mp+01CS0N#l60S6PKACZ]OP9ACZ[OAUZO]5bZP9P`PPQ00P7\a%iB?0>8\1%i4?0B>\7B1E>87P1n2001000000120000000aXG_XD^XALPbp+01JS0O#aRbPKp+01QS0P#aRLPKp+01KS0Q#a,[]201Gb5CZP9PLPKQ0Mp+01VS0R60S6PKQ0L,_QP6p+01IS0S#aPKp+01LS0T$0VP6P1XB6RQPQfhS0UP\Q0TQ0T#HJ0ePQfgS0VO1PQQ0TO1'Qp+01MS0W#aPKQ0?f}S0X5CZP9Q0X9UZ]P9ffS0Y%4X$0Y#s'MQ0Y#ip+01OS0Z#aPKp+01[S0[#aRX=CZ]P91[]Xp+01ZS0\#a5CZP91[]LPKQ0\-0QJP6p+01RS0]#a9UZ]P9Q0F20>6MS0^5CZP9Q0G9CZ[P9p+01GS0_Q0F5bZP9Q0WQ0Q'fPSQ0WQ05'fPSQ0OfuS0`5bZP9p+01]S0a,=cp+01ERS1Mcep+01FS0b1McMQ0_1=cHp+01HS0c%6Y,McQ0Sp+01`S0d,=cQ0O%6R,McQ0Q1McUQ0T%6T,McQ0WQ0P#iP0fmS0eQ0e[P0p+026S0f/EJfnRTQ0Y-0QJP6feS0g$0dP0p+029S0h%4=$0E$00$0Y$0]#o#s'MfqS0ip+02:S0jp+01gS0k'=frS0lp+02;S0mQ0k'EQ0Jp+02<S0n%R=S0o'EQ0@p+02=S0pp+01nS0q'EQ0`p+02>R=p+01iS0r'EQ07p+02?S0sp+01oS0t'EfwS0ufxS0v$0dP0p+02AS0w/E5fyS0xQ0i#FPPQ0i#zPPQ0l#FPPQ0V$03PCp+01hS0yQ0V5UZP9p+02GS0zp+01eS0{'=Q0KQ0JQ0e5mcP@Q0Y-01G=CZ]P9Q0z#aQ0Y'[PKQ0g9CZGP9Q0g9UZ]P9p+02MS0|Q0r'=Q0bQ0vQ0J5mcP@p+02OS0}p+01jS0~'=Q0cQ0~Q0S+1<P0fzS10Q075mcP@p+02RS11Q0~'=Q0Qp+02SS12Q0~'=Q0TQ0?Q0x5mcP@p+022S13@0B5?fPS14p+02VS15p+01lS16'=Q0Zf~S17Q0?5mcP@p+02XS18p+01mS19'=Q0Pp+02YRUQ19'=Q0]p+02ZS1:Q19'=p+01SS1;p+02[S1<Q19'=p+01TS1=p+02\RR$1;Q0R^=6p+01WS1>\6P0Q0`,[]PKAc7U1Q1;/38p+02TS1?,88#F[[^16^86PPP1PUP7Q18Ctp+02_R0,38p+02US1@,88Q1;'A[[^16^86PPQ0vQ0P5N1X=6PP^=6RYQ0P#HQ0PQ0P'QQ0X9CZ]P9Q0A-01]PKp+02bS1A,31p+02eS1B,S7Q1BQ0R3N[^16PPp+01XS1C/31p+02fS1D,S7#F[^16PPp+02dS1E,31p+02gS1F,S7Q1C'A[^16PPQ0b-01]=CZGP9Q0A,[GPKQ0_-01GQ0_'[PKp+02kS1Gp+028S1H'=p+01dS1Ip+02QS1JQ0Z'f$03&07CRM'T&0bCRCp+02mS1KQ1H'=p+01fS1Lp+02KS1Mp+02^S1N'=fiS1Op+02oS1PQ0h'=Q0yp+030S1QQ1H'=Q0rp+031ReQ1H'=Q0~p+032RLQ1H'=p+01kS1RQ0\p+01YS1S5mcP@1[]SPKQ1P=c71Q0r/38p+02iS1T,88#F[[^16^86PPP1Q1PP7p+02nRXCtp+035S1U,38p+02jS1V,88Q0r'A[[^16^86PPp+02FS1WQ0k5N1X=6PYP1PeP7Q1QCtp+037S1X,38Q1K,88Q1R7NX[[^16^86PPp+039S1Y/==Q13p+03:S1Z/==p+023S1[Q18Q1V'=Q07Q0O%aH'[PKp+03=S1\/==Q0fp+03>S1]/==p+027S1^p+03?S1_/==Q1Hp+03@S1`/==Q0hQ1NQ1K'=Q0?p+03BS1aQ0s'=Q0mP1p+03<S1bP7p+03;S1cCtQ1]=c87p+03CS1d,3>Q0h/3B%FBQ1H7gB[[[[^16^86PPQ10/BHQ0p&0p=Q0@Q17#zPPPNPPQ1b-0PJQ1QQ19Q07[[Q0qQ0u[\ePPg01[9S1eQ1`>0NJ7UX@eQ1eQ0u[^@eQ1eQ0v[^@LPPQ0@/BHp+02ERNQ0l=CZGP91BOHRYQ0zQ0L/BHRbp+02HR^Q1Vp+02IS1fQ0mp+01DR_COQ0L20_SHp+02JS1gPbQ1MQ1Kp+02LS1hQ0pQ0bCOQ0lPYQ0|Q0L-0=LP6PbQ0}Q0bQ0Q+06p+02PS1iPbQ1Jp+033S1jQ11Q0wQ0QCOQ0vPYQ12PYQ1?PYQ1@Q0L/eOQ0L?0OOPZQ0j&0p:R:PZQ0NP:Q0LQ1H5UZFPP9PZfkS1kP:PZfjS1lQ0n'[Q0hE|P9PZQ0b=CZ]P:PZP[Q1kE|P9PZQ0eP:PZflS1mQ0m+0oI0nP9Q0JQ1^'[PKQ0V/BHPRPZp+01NS1nP:PZPNP:Q0cFPP9Q0d,A71378S1oQ18,A8[[^16^86PPQ0U/BHRNP0Q0Rp+03WS1p'Bp+02`Q0UQ0j-0=e+15p+02aS1qPNQ1Ap+03DS1rp+02cS1sQ12Q0[COQ0OQ1O/BHRNQ1EPNQ1BQ0Up+02BS1t'[PKPZQ1gP:PZQ1;P:Q1O=UZ^FPP9Q0g/BHR^p+02hS1uP^Q1TQ0I/BHQ1VQ16Q1L+0<Q1GfdS1v/BHp+02lS1wp+03NS1xQ1KQ1TQ0yCOQ1=P^PXP^Q1PQ1Lp+03cS1y'BQ1QP^Pep+03SS1zPLQ1DQ0qCOQ1SPZAUZ]RP:p+01^S1{C{P9p+025S1|,A1Q1w,A7[^16PPp+03\S1}Q0d5bZP9p+036S1~Q1XQ13701W0Q1~PP]0Q1XQ13'eQ1XQ13Q1330Q0tQ1O'eQ0tQ1OQ1O30Q1Q-0PJp+03hS20Q0tQ1k[[p+03iS21p+020S22Q1m[[PPQ21Q1ep+034S23>0NJ7UW@Q21Q1eQ1m[]@p+03jS24Q1eQ0e[]@PPPZQ1RP:PZQ0YP:Q0R9CZ[FPP9Q13/TMPC20M68S25&146R^7]7S26&136RKfZS27212Z;R;P1P81e@<21018#qd&0K7H0~R<b:b;b<X16X8620M67S28?]1^$0K$0^RNfXS295pZ^16^86PMPCQ28PKfYS2:P;P<b:b;b<X16RY20M61$0K$0^RbQ0=5pZ^16RSPYPSPYPSQ0f/TMPCQ259]^8?]7^PKQ29P;P<b:b;b<X16X86Q289]^7?]1^$0K$0^Q0<5pZ^16^86PZp+021S2;P:PZQ1mP:Q0b9CZ[FPP9Q1H/TMPCQ26PKQ14P;P<b:b;b<X16X86fNS2<9pZN^16^86PZQ1uP:PZQ2;P:Q2:Q1D5CZFPP9PMPCQ28PKfES2=P;P<b:b;b<X16fCRS9pZb^16PZQ1VP:PZQ1|P:PZQ1[P:PZPOP:fAS2>FPFPP9Q0n/TMPCQ26PKf>S2?P;P<b:b;b<X16X86f<S2@9pZN^16^86Q0p/TMPCQ26PKPFP;P<b:b;b<X16X86ApZN3^16^861T=MPCQ26PKPEP;P<b:b;b<X16X86ApZND^16^86&03Rp+04:S2AQ1<'f$03/TM'TPCQ26PKP3P;P<b:b;b<X16X86ApZN4^16^86p+03LS2B,7cp+03KRN,21p+03MS2C127NQ1x128Np+03OS2D12>Np+03PS2E12BNp+03QS2F124Np+03RS2G12D0Q1z1230p+03TS2H12E0p+03US2I12F0p+03VS2Jf:R9/20Q1pf;Rb/20p+03XS2KQ2@/20p+03YS2Lf=RY/20p+03ZS2MQ2?/20p+03[S2NQ1Np,2fxRaQ2>PRP7P1D9g01a5S2Op+04eS2P,S1P6p+04hS2Q/E1p+03aS2RQ1`,87P6Q2Q,88P6Q2M,37PPQ2N,37PPPQPQPQp+04=R`P4P4%H4Q1rp+04kS2SPQPQp+04<S2Tp+04`S2UQ2SQ2S#HJ0eN:0JPQP>O1/Q8p+04nRd/_4P6PQp+04@S2VP4PBP7p+03^S2WQ2WQ0pGj20j>8p+03GS2X,87P61Q8FPPQ2R,37PPp+04cRI,81P6p+055RV/E7p+03nS2Yp+056RW/E7p+03oS2ZQ2A,88P618>HP6%HB1QBBfFS2[Q0380I>PLp+04jRf,B4p+044S2\p+05<S2]/_4P6PQPQPQp+04MS2^PEPEP>Q2VPHPQPQp+04LS2_Q03PH%HHJ0eN:0JPQP4O1/QBp+047S2`?038PPp+04BS2a,88P6p+04oRg,A1PPp+05BS2b/E7p+04;S2cQ0300\1p+041S2d&0}7P`p+04_S2ep+04>S2fQ2TP8COQ1BQ2\00H8Q1]p+059S2g,81P6Q2g,87P6p+05JS2h/E8p+04CS2ip+05KS2jp+05=S2k,8>'Ep+04DS2lp+05LS2m/E>p+04ES2np+05MS2o/E>p+04FRhp+04\S2p,84P6p+05AS2q,8DP6%H31Q33Q2e,83P6p+05DS2r,8EP6%HF1QFFQ0F@0ID\Q2Bp+05GS2s,B9p+04NS2tp+050Rip+04OS2uQ2VPFCOQ1~1B95p+04PS2vp+05XS2w/_bP6PQPQPQp+04iRjf@S2xQ2xPEp+04gS2yQ2jQ2ZN:0JPQP9O1/QFp+054Rkp+04SS2zPhPYCOQ1ZPVp+04TS2{Q2lPYCOQ1cp+05\S2|Q2?'_P6fDRl,3bPPf?S2}/3lPPQ2@Q2['3PPQ2xQ2['3PPPQPQPQp+051S2~fGRmPmPYPgp+05SS30Q2`N:0JPQQ2}O1Q2?'Qp+04QRn,3SPPp+04RS31,3SPPQ2[/B5p+04]S32Q0CfLRo'3PPQ0G,3mPPQ0DQ2<'3PPfHS33Q0I'3PPp+04bS34fMRp90I1W0Q34PP]01eIpA0Ippp+04dS35fOS36Q2=30PPQ2PQ3670lPPp+05;S37,8lP6Q2>Q2]'8P6PQp+05@S38Q14Q36Q2=p+04^S39Q39Q1\GjQ2@00jbQ0<,QSPPQ33Q29'QPPQ0;$0[P4fJS3:,3BPP13DIPPQ0g/3oPPp+067Rq/E1Pip+068S3;/_1P6p+06:S3</E1p+053Rrp+06;Rs1SB7'EPk20\\7RtPfQ0\?<j817cWQ2wp+057RuPfP>COQ2Wp+05YS3=p+058RvQ2yPBCOp+03_S3>p+05ZS3?Q2gQ2QPBCOp+03`S3@p+05:S3A20Z31#qW0Q3APP]020Hi4Q2AQ2`9<4dQ2],7c12DiQ2kQ2],23p+05>S3Bp+049S3C9<8ip+05?S3D,7cp+052Rw20G875<FQ38,7cQ2q?0>YPPQ2bQ0{70>PP12DVp+05CS3EA<BVTQ2r,7cQ2P-0_79<EWp+05ES3F,7cp+05FS3Gp+04AS3H708PPQ2r,23Q2sQ2g,2Ep+05HS3IPFQ3AP7P1Cyp+05IS3J,7cQ2hQ16708PPQ2jQ2n708PPQ2k,23Q2mQ2oQ0u701PPp+06VS3K/E1p+05OS3Lp+06WS3MQ14/Sp,S7'Ep+05PS3NPtQ3Gp+063S3Op+05RS3PQ38P8COQ3Cp+064S3QQ30Q2qP8COQ2AQ3J00H8Q2zp+06]S3R/E1p+05VS3Sp+06^S3TQ0=,S7'Ep+05WS3Up+069RpQ2wQ30P1COp+04?S3VQ3=p+06aS3W/_1P6PtQ3Np+06cS3XQ0BQ2:'S,87'EQ2|Q3P00H7Q2pPtQ30p+06@Rtp+05_S3YQ3LP4COPhp+06AS3Zp+05`S3[Q3NP>COp+04GS3\Q1|Q0T<0k8p+05aS3]Q3][p+06hS3^01j>PAp+04JRxp+03JS3_PxQ1qPxQ2}PxQ1DPxp+01US3`PxP9PxQ2xPxQ17PxQ0KPxQ1QPxP8PxQ2:PxQ27Pxp+03AS3aPxP>PxP_PxQ2XPxQ3_Pxf[S3bPxF\D1D1D1D1D1D1D1D1&0bxQ1n20\\S60k8p+05dS3cQ3c[21i\EA0A8\fQS3dQ3SQ2@3<p+05fS3e,7cQ3SQ2U5<1p+05gS3f,7cQ3?,27p+05hS3gQ2wQ0g5<7p+05iS3h,7cP>Q3=Q3U,2>P7Cdp+05jS3i,7cp+05kS3jp+04fS3k708PPp+05[S3l,2Bp+05lS3mQ3[,24p+05mS3np+05]S3oQ1O5<Bp+05nS3p,7cp+05^S3q20W875<3p+05oR_,7cp+060S3r?0>jPPp+061S3sQ0e70>PPQ3r,2Ep+062S3tp+05bS3u,2FQ3OQ3c=<4mQ3Q,7cQ3c20687Ry5<bp+065S3v,7cp+066S3w?0>UPPQ0J90q>PPQ3g,2FQ3;Q3g,29PpQ3i=<4wQ3<,7cQ2@Q3j20F87S3x3<17csp+06<RzQ0870>PPp+06=R{Q0v70>PP12F_p+06>R|129_p+06?R}Q3O,2bPtQ2@/2}Q3ZQ3t12Y_p+06fS3yp+04KS3z+0='B5<Yp+06BS3{,7cQ3wQ0q5<Ep+06CS3|,7cp+06DS3}Q0t704PPp+06ES3~Q29704PPp+06FS40Q0N704PPp+06GS41Q1V704PP12Ypp+06HS42Q1[9<4pp+06IS43,7cQ2}p+03lS44,B77<{p+06JS45,7cp+06KR~Q0f708PPQ43,2Ep+06LS4612F{p+06MS47A<BzTp+06NS48,7cQ3x9<b}p+06OS3x,7cp+06PS49?0>LPPp+06QS4:Q3J70>PPQ3{,2Ep+06RS4;Q48Q1k5<Bp+06SS4<,7cp+06TS4=?07=PPQ49,2Dp+06US4>Q4=,23Q3KQ4>Q1h5<>Q3M,7cQ4<=<Fyp+06XS4?,7cp+06YS4@Q1Y70>PPp+06ZS4AQ1\70>PPQ4@p+02NS4B5<3p+06[S4C,7cQ3K,2Ep+06\S4DQ4@Q2w5<4Q3R,7cQ3TQ1\707PPQ4C,23p+06_S3RQ4;,2Ep+06`S4EQ3xQ0A5<>Q3W,7cQ3T20<875<9p+06bS4F,7cQ3XQ1r70>PPp+06dS4GQ3Y70>PPQ4<,23p+06eS4HQ4>,2EQ3yQ4Cp+05cS4I5<4p+06gS4J,7cQ3K=<9yQ3^,7cp+06iS4KQ0O70>PPp+06jRyQ1L70>PPQ4C,2Fp+06kQ4A,29p+06lS4LQ3WQ4A,2bp+07QS4M00=I'B5<bp+06mS4N,7cQ4EQ3h5<Dp+06nS4O,7cp+06oS4P?0>UPPp+070S4Qp+01PS4R70>PPQ4N,2Fp+071S4SPaP>P_Q0Xp+03ES4TD9Q2OQ4J,2Bp+073RLp+072S2O,24p+074S4UQ3^,2Dp+075S4VQ3^,23p+076S4W12ELp+077S4XQ4V,2Fp+078129yp+079S4YQ4V,2bp+07:S4ZQ4NQ32,BF5<Sp+07;S4[,7cp+07<Ry?09qPPQ2?Q4W'2p+07=S4\Q2}Q45'2p+07>S4]Q2xQ4Y'2p+07?S4^Q2>/2~p+07@S4_fBS4`/2~p+07AS4a12S~p+07BS4b12l~p+07CS4cQ2=/2~p+07DS4dQ2[/2~p+07ES4e12m~p+07FS4fQ33/2~p+07GS4gp+07HS4hQ3}70lPPp+07IS4iQ1]70lPPp+07JS4jQ1U70lPPp+07KS1UQ4070lPPp+07LS4kQ4170lPPp+07MS4lQ1Z70lPPp+07NS4mQ1Y70lPPp+07OS4nQ0y70lPPp+07PS4oPaQ1MQ4cQ4B00G1Ppp+03eS4pp+03dS4qQ2<GGW0Q4oPP]0Q4MQ2Z70SPPp+07RS4rQ2Z70SPPp+07SS4sp+042S4t70SPPp+07TS4up+040Rp70SPPp+07US4v?0SpPPp+07VS4w?0SpPPp+07WS4x?0SpPPp+07XRm?0SpPPp+07YS4y?0SpPPp+07ZS4z?0SpPPp+07[Rq?0SpPPp+07\S4{Q09Q2f30PPQ4`Q2>Q2xQ2}Q2?Q3HQ0D+0|80DY40D40D:0DlSPP1;>8PP1;41PP1;31PP1;F1PP1;b1PP1;Y1PPQ2}/;1PPQ2>/;1PP1;S1PPQ2=/;1PPQ33/;1PPQ3:/;1PP1;o1PPQ2</;1PPQ14/;1PPQ08/;1PPp+07nS3:?0nXp+07oQ1}70np+080Q4S70np+081S4|Q1M70np+082S1MQ2\70np+083Q2a70np+07lQ2n'3p+098S4},3hp+04mS4~p+04lRXPXQ2SQ3fQ3eQ3ep+05eS50PfP~P1Q2_PDO2b2b4b5b6b3Q4~PXPXQ2SQ3fQ3eQ3eQ50PjQ45P1Q2_P4O2b2b4b5b6b35YhQ2TQ3\PdQ4~Q4~PXQ3gQ3fQ3fQ3eQ2SQ46P1Q2^P3O2b2b4b5b6b3PdQ4~Q4~PXQ3gQ3fQ3fQ3ePfP~P1Q2^PDO2b2b4b5b6b33YP`p+09:RoQ2T'3p+099S519N`oQ2~PiPiPgQ3jQ3iQ3iQ3hPMPCQ28PKPZPmP:PZP[Q4wE|P;P<b:b;b<X16p+09AS52/31p+096Rb,87S53#F[^16P1Q2iPDO2b2b4b5b6b3Q2~PiPiPgQ3jQ3iQ3iQ3hPMPCQ28PKPZQ4xP:PZQ4wp+07bRT+0oI0nP;P<b:b;b<X16p+09@S54p+09?S555N1Q53p+086S56'A[^16P1Q2iP4O2b2b4b5b6b35Y`p+045S53/Q`Q2_p+03kS577coQ44PoQ2^Q51CtQ44PkPrPrPwQ3pQ3nQ3nQ3mPjQ4@P1Q2zQ4tPDPYO4b2b4b5b6b3PkPrPrPwQ3pQ3nQ3nQ3mPrQ4?P1Q2zQ4tP4Q2@O4b2b4b5b6b33YQ1dp+03mS2@PVPkPkPrP_Q3pQ3pQ3nPfQ4AP1Q2{p+043S58P3Q2?O4b2b4b5b6b3PVPkPkPrP_Q3pQ3pQ3nPkQ4@P1Q2{Q58PDPYO4b2b4b5b6b33YQ1rQ2@PWPVPVPkQ3rP_P_Q3pPfQ3~P1p+04US59Q2\PEQ2}O4b2b4b5b6b3PWPVPVPkQ3rP_P_Q3pPgQ3}P1Q59Q2\P3Q2?O4b2b4b5b6b33Yp+03FS2?Q2ZPuPWPWPVQ3sQ3rQ3rP_PXQ4DP1p+04VS5:Q53PFQ2xO4b2b4b5b6b3PuPWPWPVQ3sQ3rQ3rP_PWQ4CP1Q5:Q53PEQ2}O4b2b4b5b6b33YQ2?Q2ZPvPuPuPWQ3tQ3sQ3sQ3rPXQ41P1p+04WS2}p+046S5;P9Q2>O4b2b4b5b6b3PvPuPuPWQ3tQ3sQ3sQ3rQ2~Q40P1Q2}Q5;PFQ2xO4b2b4b5b6b33Yp+03HS3rQ1`#FQ1`Q1d3gQ1rQ1N'3Q4d,A0Q2?Q1dQ1F3cQ1uQ4f'Ap+02]RFQ1Tp+08=S3s3NP2Q2pQ2}p+09BS5<H1g#qQ4hQ32Q53P\Q1]DhQ4iQ39Q53P\PFDhQ4jQ2YQ1F30Q1Up+04IS5=;0`Q2l#zQ2i';Q1B$1fQ1E#FQ1Ep+08DS5>3gp+08OS5?,7cRFQ34PaP1Q4lPRPID9+0{p+08PR9P1Q5>Q4kH1cP9p+08NS5@,21Q2nP9p+08CS5A,21Q2cP9p+08BS5B,21Q1UP9p+08LS5C,21Q1UP9p+08MS5D,21P`P9p+08AS5E,21Q2cP9p+08KS5F,21Q1T20|k1H04H04H04H04H04H04H0440DXkFQ0Pp+04aS5GQ0W+0{Q0GQ5GPaPrQ3{PIQ34D9Q0WQ2sPaP2PrQ4lPIQ34g043NQ5Dp+08<S5HQ54Q02'Mg044Xg01[URF,e@REg045bQ5?Q4eQ5?20zr1=0@FW0Q5?Q2DQ5?Q4f-0z1=0@FW0Q2EQ55-0PJp+09>RFQ54#FQ3s#z[[Q1eQ5<>0NJ7UX@FQ1ep+08>S4e#F[^@FQ3IQ2sQ2sQ3GQ3{Q3ZQ3ZPtp+09Ep+09DS02Q05'f'f$03Q4j/TM'TPC20M6>S059]^>Q25?]>^7]7S5IPKPZQ1UP:PZQ5BP:PZQ5EP:Q52Q0MQ04#l60S69UZ]5bZC{FPP;P<b:b;b<X16X86X?61A8m137>S5J%F>S5K1A>8S5L';S5MQ5Kp+08GS5N7g>[[[^16^86^?6P1PeQ2HQ1pQ2>Q4`PSO6b2b4b5b6b3bEbF+1`PwQ14E5Q5H,2r&1_rE5N>1^p+085S4`p+095RSP1p+09WS2>Q4_Q3|%HSQ2>Q4_Q2>Q3|C@dO4b7Q5?p+09VS5Op+094S5PP?Q5OQ5P'JdQ3{DIP9Q4_PaPVP1Q2PQ35Q0ZE:X09PaPkQ4_Q35PID9PaP@p+08QR_,7cQ4^PkQ3_n0100000020000PsQ35PID9Q1nQ3IPaP2PkQ4_Q35PIg046lQ5AQ5DQ5Pp+09IS1n'=PNQ2Cg0486PEg049@P9P`Q4oQ2Pp+09JS5Q,B1P\Q2?DhX09Q2Vp+09XS5RQ5Q,81'E90_`X=6Q2T,e9Q2>/_`Q2VQ2sQ3GQ3GQ3FQ3ZPtPtP}Q4h/TMRYPCQ26PKPZQ4fP:PZQ3{P:Q55FPP;P<b:b;b<X16X86p+09US5S=c71Q5?/38%F8S5T[[^16^86P1Q3kQ2nfIQ14O4b2b4b5b6b3Q2sQ3GQ3GQ3FQ3ZPtPtP}PYPCQ26PKPZp+08;S5UP:PZQ4dP:Q4cFPP;P<b:b;b<X16X86P1p+09TS5VP7p+09SS5WCtp+09ZS5X,38Q5@,A8[[^16^86P1Q3kQ2nQ33Q36O4b2b4b5b6b33YDZQ1}eQ1}P_P`Q4MQ3kP1P\Q2XDhX0_P3Q58P1E?b7PwQ14E5Q2C$0hNA0gQ56PbP1Q5RQ4[PzQ5P#HS36Q5RQ4[Q5RPzC@dO4b7P9Q2>p+093R3P?Q2>/J3dPsDIP_Q4[PaQ2BP1Q3kQ2PQ4RE:X0_PaPNQ4[Q2PQ35D9PaP@p+08RS4R,7cQ4ZPNQ3an0100000020000Q3<Q2PQ35D9Q0ZQ3JPaP2PNQ4[Q2PQ35g04:JRYQ5AQ5>Q5?g04;T%WYg04<^N=1Zp+087S0Zp+097S33P1p+09YS5YQ4ZPsQ36Q5YQ4ZQ5YPsC@dO4b7P_Q5RP3P?Q5R/J3dQ3<DIQ4RQ4ZQ4RPaQ1dP1Q2yQ3kQ0PE:W0Q4YPNQ4Y$07PWp+08ES0PPEEDQ3aeQ3ap+08SS5ZQ2EQ5ZPaQ1xp+08FS5[Q2?-0G1PyQ2QQ2yQ0]GGW0Q4ZQ2BQ4Z$07PuP_PEEDQ3aeQ3ap+08TS5\PuQ0JQ5\Q2HQ0JQ5\Q4nQ5\PaQ2DQ5NP1Q4\PjQ2QQ1;GGW0PaQ3rPyQ2QQ2yD9PaP@p+08US1;,7cQ4ZQ3rQ1_n0100000020000PzQ2QQ2yD9Q0]Q2mPaP2Q3rPyQ2QQ2yg04=hRYQ0PQ5[Q5Pg04?2%WYg04@<N=1Xp+08:S0]PoP1p+09\S5]Q4ZP{Q36Q5]Q4ZQ5]P{C@dO4b7Q5\p+09[S36P3P?Q36/J3dPzDIQ1;Q4ZQ1;PaQ3aP1PfPjQ1=E:W0PyPzQ1x>1WyyQ2gQ5NPEEDQ1_eQ1_p+08VS1=Q4MQ1=PaPNp+08HS5^Q0Z-0_1PyQ2SPfQ3`GGW0Q5Hp+09<S5_P1p+09^S5`Q4MP{p+09OS5a#HQ5`Q4MQ5`P{C@dO4b7Q1=Q4o;0zp+08WS5bQ4MQ5bPaQ2Bp+08IS5cP1Q4\PXQ2SQ0RGGW0PaQ3rPyQ2SPfD9PaP@p+08XS0R,7cQ4\Q3rQ1]n0100000020000PzQ2SPfD9Q3`Q3LPaP2Q3rPyQ2SPfg04AFRYQ5^Q5\Q5^g04BP%WYg04CZN=0fQ3sp+09=RYP1p+09_S3`PyP{%HbQ3`PyQ3`P{C@dO4b7Q5bQ5`PSP?Q5`/JSdPzDIQ0RPyQ0RPaQ1`P1Q4~PXQ1>E:W0Q4^PzQ4^P}Q4^Q2FQ4^D^Q2]Q1;PEEDQ1]eQ1]p+08YS1>Q37Q1>PaPNQ5FP1Q1aCyQ4]PdQ4~Q1CE:W0Q4_P{Q4_PtQ4_Q2GQ4_D^Q2kp+08JS5`PEEDQ1]eQ1]p+08ZS5dQ4uQ5dPaQ2BQ5CQ2kP1CyQ4^PgPdQ1SE:W0Q5dQ3\Q5dPaQ2BQ5CP1Q4vCyQ4^PgPdQ1SE:W0Q5dQ2nQ5dPaQ2BQ5CP1Q4^PgPdQ1SGGW0PaQ2?Q4]PdQ4~D9PaP@p+08[S5e,7cQ4\Q2?Q1En0100000020000P{PdQ4~D9Q1CQ3PPaP2Q2?Q4]PdQ4~g04DdQ5`Q5FPyQ1PPeg04EnPEg04G8Q4aQ2cQ4aP|Q4aQ3ZQ4aQ1zQ4aF\Q3BQ5FPEEDQ1\eQ1\Q5ePhQ5ePqPi1B1|P\Q1PDhW0Q5ePhQ5ePqPiP1P\Q1PDhW0Q2xQ2cQ3@E5Q1_P1E5b9&0heNA0gp+08@S2xQ54P1p+09bS1PPyP|Q4}#HS1CQ1PPyQ1PP|C@dO4b7Q5dp+09aS5dQ33P?Q5dQ33'JdP{DIQ5ePyQ5ePaQ1DP1PiPgQ0\E:W0PaQ1BPyPgPdD9PaP@p+08\S0\,7cQ4[Q1BQ1qn0100000020000PzPgPdD9Q1SQ30PaP2Q1BPyPgPdg04HBS1SQ5`Q5^Q5Dg04ILQ1S#Wg04JVN=0TQ5EQ52P1p+09cS1SQ4[P{Q1CQ1SQ4[Q1SP{C@dO4b7Q5eQ1PQ33P?Q1PQ33'JdPzDIQ0\Q4[Q0\PaQ1sP1Q2~PiQ0[E:W0Q4cQ1KQ4cP`Q4cPtQ4cQ3|Q4cQ2IQ4cD^D1Q38Q5@PEEDQ1qeQ1qp+08]S1KPmQ1KPaQ1uQ5DQ4uP1CdQ4\PwQ2~p+01\S0[E:W0Q5Ap+09CS4[P1p+09eS1CQ4xP|p+09PS5f#HQ1CQ4xQ1CP|C@dO4b7Q1KQ4w;0{p+08^S5gQ4xQ5gPaQ1TQ5@P1Q4]PrPwQ0aGGW0PaQ1FQ4\PwQ2~D9PaP@p+08_S0a,7cQ4]Q1FP0n0100000020000P{PwQ2~D9Q0[Q3SPaP2Q1FQ4\PwQ2~g04K`S1FQ5DQ5DP_g04LjQ1F#Wg04N4N=1TQ5>Q02P1p+09fS02Q4\P|%HoQ02Q4\Q02P|C@dO4b7Q5gQ1CQ51P?Q1CQ51'JdP{DIQ0aQ4\Q0aPaQ1qP1PkPrQ1{E:W0Q4fP{Q4fQ1QQ4fQ2VQ4fQ3|Q4fQ40Q4fQ2KQ4fF\D1Q3EQ5@PEEDP0eP0p+08`S4fQ4yQ4fPaQ1VP9Q1E-0W1Q4^PVPkp+01_S2KGGW0Q4gP|Q4gPeQ4gQ3HQ4gQ3}Q4gQ41Q4gQ2LQ4gF\D1Q2rQ5ZPEEDP0eP0p+08aS1QQ2WQ1QPaQ1GP_20Wq1Q4_PWPVQ0dGGW0Q1QQ2WQ1QPaQ1GP_P1Q4_PWPVQ0dGGW0PaQ1uQ4^PVPkD9PaP@p+08bS0d,7cQ4aQ1uPRn0100000020000P|PVPkD9Q2KQ3=PaP2Q1uQ4^PVPkg04O>ReP9Q0aP9g04PH%Weg04QRN=0TQ5Np+09GS5NP1p+09iReQ4^P}Q5_#HS2KPeQ4^PeP}C@dO4b7Q1Qp+09hS4_p+09;S1{P?Q4_Q1{'JdP|DIQ0dQ4^Q0dPaQ1NP1PuPWp+01aE:W0Q4iQ2MQ4iPtQ4iQ1jQ4iQ2iQ4iQ40Q4iQ43Q4iQ2NQ4iD^D1D1Q3GQ4fPEEDPRePRp+08cS1jQ3GQ1jPaQ1GQ5ZP1Q1qCdQ4aPvPup+01bS1GE:W0Q4jQ2NQ4jQ3ZQ4jQ23Q4jQ2lQ4jQ41Q4jQ45Q4jQ1}Q4jD^D1D1Q2sQ4RPEEDPRePRp+08dS2lQ2RQ2lPaQ1wQ5\Q3IP1CdQ4bQ2gPvp+01cReE:W0Q2lQ4qQ2lPaQ1wQ5\P1p+03bS4^CdQ4bQ2gPvPeE:W0Q2lQ3@Q2lPaQ1wQ5\P1Q4bQ2gPvPeGGW0PaQ1DQ4aPvPuD9PaP@p+08eS1w,7cQ4gQ1DPUn0100000020000PtPvPuD9Q1GQ2|PaP2Q1DQ4aPvPug04R\ReQ5\Q5\Q5Zg04Sf%Weg04U0N=0fQ5`Q5QP1p+09lS1GQ4aQ3Z%HFS1FQ1GQ4aQ1GQ3ZC@dO4b7Q2lp+09kS0[PYP?Q0[/JYdPtDIQ1wQ4aQ1wPaQ1<P1Q3AQ2gQ1IE:W0Q4kQ1}Q4kp+03]S1}Q4kQ3|Q4kQ1~Q4kPhQ4kQ43Q4kQ46Q4kQ2WQ4kF\D1D1Q3JQ1;PEEDPUePUp+08fS1IQ1\Q1IPaQ1TQ5bP1Q1NCyQ4cQ37Q3AQ0{E:W0Q4lQ1}Q4lQ2WQ4lQ3}Q4lQ1XQ4lQ3\Q4lQ45Q4lQ47Q4lQ3>Q4lF\D1D1Q2hQ1;PEEDPUePUp+08gS1;Q1yQ1;PaQ1VQ0RQ1_P1CyQ4dQ2]Q37Q1LE:W0Q1;Q1cQ1;PaQ1VQ0RP1Q4dQ2]Q37Q1LGGW0PaQ1sQ4cQ37Q3AD9PaQ1sQ3{Q1~Q3AD9Q0{Q3YPaP2Q1sQ4cQ37Q3Ag04V:Q0RQ5bQ4iQ31Q1cg04WDPEg04XNQ4mQ1XQ4mQ2WQ4mQ3>Q4mQ3~Q4mp+038S4iQ4mp+04HS0{Q4mP~Q4mQ48Q4mQ3@Q4mF\D1D1D1S1~Q2jQ0RPECKQ12eQ12p+08hReQ2zp+08iS2g1B1~Q2{30X0eQ2}Q2gp+0:0S4a1815S5h'EQ2{30X=6P6PeQ4cQ4cQ2}/85Q2}Q3{Q3YQ3qQ3qQ3oQ4@Q4?Q4?Q3MPMPCQ28PKP6Q4h/[[g01WNQ4hH0;-1RZP;P<b:b;b<X16S4hQ1C,81S5i/85Q5i'Q^16P1Q32O1b2b4b5b6b3L0vQ3\Q2}Q3YQ3qQ3qQ3oQ4@Q4?Q4?Q3Mp+05TS5iQ4dP1Q3BQ32Q0GQ0UO4b2b4b5b6b3Q3YQ3qQ3qQ3oQ4@Q4?Q4?Q3MQ3qQ4cP1Q3BQ32Q0FQ0VO4b2b4b5b6b33YDZQ58eQ1:P1E5b9Q1~Q2jQ5bPECKQ11eQ11PeQ1bQ2gQ1\701X0ePeQ1bPUP1FXb9P2Q37PWQ31Q5dP\PuQ4\PrPwPgQ3qQ3oQ3oQ2|Q4?Q3MQ3MQ3KQ2|Q4\P1Q2kQ0YO2b2b4b5b6b3PiQ0FGkPXeQ2<PuQ3\,31X=6Q5:13v1S2<X=6Q3qQ3oQ3oQ2|Q4?Q3MQ3MQ3KPMPCQ26PKPZQ4]P:PZQ4bQ4\E|P;P<b:b;b<X16X86Q1G=c17p+0:3S4bQ02,885c7[^16^86P1Q2pQ2kQ0FO3b2b4b5b6b3PhQ2:DZPiQ0FDZ13iheQ5:AN1YgX=6PuQ5[,81,3nX=6Q2v/3VQ2u/3kPQQ55Q2vQ2uQ2nPVPkQ2~GjQ3qQ3oQ3oQ2|Q4?Q3MQ3MQ3KPMPCQ26PKPZQ4RP:PZQ3}PyE|P;P<b:b;b<X16X86P1Q0[P7p+09jCtQ02,87p+09gS0[Q4b,S8Q4b'83N[^16^86P1Q2kQ2pQ0EO3b2b4b5b6b3PiQ0FGkPhQ2:DZQ2d/3deN:0uNB0tQ5Dp+09MS5[P1p+09oS5dQ4UQ3|Q2KQ5dQ4UQ5dQ3|C@dO4b7Q1;p+09nS1~Q1{P?Q1~Q1{'JdQ3{DIPeQ4UPaQ1BP1Q4iQ2]Q0kE:X0ePaQ1EQ4UQ1XQ37D9PaQ1EPzQ1XQ37D9Q1LQ3[PaP2Q1EQ4UQ1XQ37g04YXQ5eQ1IQ5YQ04#4#o$0E#s'Mg04ZbPEg04[lQ4nQ4iQ4nQ3>Q4nQ3@Q4nQ40Q4nQ1YQ4nQ5=Q4nQ46Q4nQ3xQ4nQ2RQ4nD^D1D1D1Q2mQ5ePEEDQ11eQ11Q2gp+03fS46Q2g20Z1U#qW0Q4oQ1YQ4oQ3@Q4oQ2RQ4oQ41Q4oQ1ZQ4oPxQ4oQ47Q4oQ49Q4oQ4^Q4oD^D1D1D1Q2oQ1;PEEDQ11eQ11p+08jS4oQ2oQ3@Q4oQ24Q3@Q20Q24-0O1#qX=6Q57Q2100O1#qX=620O71#qPPQ00Q5L\11A87S00P7[Q5LP8[21Q87P1n2001000000120000000aXC6XA61A71S5L20O87#q[^C6^A6P1Q21Q44Q3uQ3]Q3]Q3[Q4DQ4CQ4CQ4APMPCQ26PKPZPZ20cZBQ5NP:Q5NEuP;P<b:b;b<X16X86X>P1A17S5N,;81A78S3u[^16^86^>PP1Q2Y#FQ2dQ2YQ0CO4b2b4b5b6b3O3b7Q21Q57Q3]Q3[Q3[Q3YQ4CQ4AQ4AQ4@1TTMPCQ25?]8^9]^7PKPZQ1>P:Q5YC{P;P<b:b;b<X16X86%F7S3@Q5L';Q3@[^16^86P1Q2@PpQ0BO3b2b4b5b6b3Q3]Q3[Q3[Q3YQ4CQ4AQ4AQ4@Q2|PtP1Q3_PpQ27Q3bO4b2b4b5b6b33YDZp+0:1S5Lp+03gS41'_Q20Q3]Q3[Q3[Q3YQ4CQ4AQ4AQ4@PMPCQ28PKPZPZQ5Y20cZ>S40P:Q5YEuP;P<b:b;b<X16X>P%F1S5Y/;7Q3@[^16^>PP1Q2@/ApQ2@Q0BO3b2b4b5b6b3Q3]Q3[Q3[Q3YQ4CQ4AQ4AQ4@Q4\PCQ5IPKPZp+07eP:PZQ5?P:PZPZ20cZ4S4\Q5@P:p+07_S04EuFPP;P<b:b;b<X16X86X?6X>PQ1M,A8138>S1X1A8>S1L,;4p+08kS1:,A>[[[^16^86^?6^>PP1Q2@#FQ3_PpQ2@Q27Q3bQ0BO7b2b4b5b6b33YDZQ41Q24+0Z#qeQ2oQ1kE5PUP1E5b9PUP1E5b9N>1PQ5@p+09NP1Q4aPLP{Q1{#HR4Q4aPLQ4aP{C@dO4b7PeQ5dPoP?Q5d/JodPzDIQ2gPLQ2gPaQ1DP1Q1YQ2kQ0yE:W0PaQ1BPLQ4iQ2]D9PaP@Q4o,7cQ4kQ1Bp+02WS0yn0100000020000Q3<Q4iQ2]D9Q0kQ3]PaP2Q1BPLQ4iQ2]g05FkS4iQ1>Q1=Q2Og05H5Q4i#Wg05I?N=0RQ5?Q5aP1Q5LQ2OPsP4Q5LQ2OQ5LPsC@dO4b7Q2gQ4aPoP?Q4a/JodQ3<DIQ4oQ2OQ4oPaPUP1Q1ZQ3BQ0rE:W0P9Q5fP1p+0:2S5fp+07cRUPsQ1P#HQ5fPUQ5fPsC@dO4b7Q4oQ3<70TQ1:PUQ1:PaQ1uQ0\P1Q4UQ1cQ3DQ0~GGW0PaQ1qPLQ1ZQ3BD9PaQ1qQ3<Q1ZQ3BD9Q0rQ4IPaP2Q1qPLQ1ZQ3Bg05JIS3BQ5>g05KSQ3B#Wg05L]N;1OP_p+09QS3BP1Q4bPLPsP4Q4bPLQ4bPsC@dO4b7Q1:Q5fPoP?Q5f/JodQ3<DIp+08lS1ZPLQ1ZPaQ1sP1Q1bQ38Q1RE:W0PaQ1APLQ1cQ3DD9PaP@p+08mS1R,7cPqQ1AQ11n0100000020000Q3<Q1cQ3DD9Q0~Q3cPaP2Q1APLQ1cQ3Dg04`TS1cQ0aQ1KQ4mg04a^Q1c#Wg04bhN=0RQ4Rp+09RS1cP1p+0:4S4mPLPsP4Q4mPLQ4mPsC@dO4b7Q1ZQ4bPoP?Q4b/JodQ3<DIQ1RPLQ1RPaQ1?P1Q1\Q2qQ16E:W0Q4uQ3<Q4uQ1\Q4uQ4qQ4uQ4pQ4uP~Q4uQ1]Q4uQ2tQ4uQ4:Q4uQ4=Q4uQ46Q4uF\D1D1D1p+05QS1AQ5gPEEDQ11eQ11p+08nS3cp+04YS0~Q3cPaQ1BQ0dQ4:,B1Q4VQ1]Q2bQ19GGW0Q3cQ0~Q3cPaQ1BQ0dP1Q4VQ1]Q2bQ19GGW0PaQ1<Q4UQ1\Q2qD9PaP@p+08oS19,7cQ4MQ1<Q0}n0100000020000Q3<Q1\Q2qD9Q16Q3ePaP2Q1<Q4UQ1\Q2qg04d2R4Q5gQ1:Q5gg04e<%W4g04fFN=0fQ5\Q5VP1p+0:6S5VQ4UPsQ2KQ5VQ4UQ5VPsC@dO4b7Q3cp+0:5S2KQ1{P?Q2KQ1{'JdQ3<DIQ19Q4UQ19PaQ1JP1Q1_Q3EQ0qE:W0Q4wQ2_Q4wPzQ4wQ1_Q4wQ46Q4wQ41Q4wQ47Q4wQ1`Q4wQ2vQ4wQ4<Q4wQ3KQ4wQ20Q4wD^D1D1D1D1Q30Q1ZPEEDQ0}eQ0}p+090S47Q3PQ47PaQ1NQ1QP1Q1?CyQ4WQ1`Q2rQ0tE:W0Q4xQ2^Q4xP{Q4xQ1`Q4xQ41Q4xQ20Q4xQ48Q4xQ3aQ4xPnQ4xQ4=Q4xQ3MQ4xQ21Q4xD^D1D1D1D1Q5iQ4fPEEDQ0}eQ0}p+091S46p+07iS1_Q46PaP0Q0dQ5iP1CyQ4XQ3aQ3FQ22E:W0Q46Q39Q46PaP0Q0dP1p+07jS0qCyQ4XQ3aQ3FQ22E:W0Q46p+04[S5gQ46PaP0Q0dP1Q4XQ3aQ3FQ22GGW0PaQ18Q4WQ1`Q2rD9PaP@p+092R4,7cQ4VQ18Q12n0100000020000PzQ1`Q2rD9Q0tQ3hPaP2Q18Q4WQ1`Q2rg04gPQ0aQ1QQ4sQ2EQ2Gg04hZPEg04idPmQ2^PmQ2tPmP|PmQ3aPmQ20PmQ21PmQ3xPmQ1aPmQ31PmQ4>PmQ4?PmQ24PmF\D1D1D1D1p+05US21Q1QPEEDQ0|eQ0|P4Q2pQ1MQ1aQ4>,B1P\Q2DDhX04P4Q2pQ1MQ1aP1P\Q2DDhX04Q4|Q59Q4|Q1MQ2D701WHQ0<Q3aQ2p<0I\P2Q1rQ3GQ32Q2pP\PAP\Q2`Q31Q06'8S4|Q2t3wXAAQ2Up+09H,81S2`Q31'3?w`1X=6Q5GQ0~/31Q2`Q5G3wX=6Q2_Q3z+0:Q5=-0:xQ2_Q3zPxQ5=PQQ5Qp+04XS2`Q2}Q0{Q5GQ5GQ0~GjPQQ5QQ5gp+04ZS5gQ2vQ2UQ2UQ5:GjJ0sQ3hQ3gQ3gQ3fQ3XQ4FQ4FQ3WPMPCQ28PKQ3|Q4r5CZQ48=CZy60rZP;P<b:b;b<X16Q1~,81S1~Q4aQ5d,81R`3NQ4a,8`Q1~3w^16P1Q2yO1b2b4b5b6b3PnQ0IGkQ2^Q0HDZQ5;Q2TQ2^3weQ1`Q1\E5Q2UQ2OQ2`/3eQ2}/3ePQQ5QQ2`Q2}Q0{PePeQ4gGjQ3hQ3gQ3gQ3fQ3XQ4FQ4FQ3WQ0q/TMPCQ26PKPZQ1KP:PZp+07fP:Q3}Q5e5CZFPP;P<b:b;b<X16X86P1Q5VP7Q2KCtp+0:<S0q,38Q5L,88Q4bQ473N[[^16^86P1Q3IQ2yQ1lQ0iO4R`b2b4b5b6b3Q2^Q0HGkQ2c/3eePAP\Q4|Q2g'3XAAQ5GQ2OQ3\PhQ2AQ3hQ3gQ3gQ3fQ3XQ4FQ4FQ3WQ2|Q4VP`b2b4b5b6b3PnQ0IGkQ53eQ1`Q1\E5N90qE5Q2nQ2p$0[E5Q1iP1E5b9Q2G$0hNA0gQ5bQ2>P1p+0:9R`Q4QP{Q1FP`Q4QP`P{C@dO4b7Q46p+0:8S2>PYP?Q2>/JYdPzDIP4Q4QPaQ1@P1Q1aQ3GQ2;E:X04PaQ1?Q4QQ3aQ3FD9PaP@17c3Q1RQ0a5mcQ1?Q1gn0100000020000Q3<Q3aQ3FD9Q22Q3iPaP2Q1?Q4QQ3aQ3Fg04jnS22Q1RQ1RQ47g04l8Q22#Wg04mBN=0TQ0RQ5RP1p+0::S5RQ4QPsQ1FQ5RQ4QQ5RPsC@dO4b7P4P`PYP?1J`YdQ3<DIP3Q4QPaQ1hP1Q1dQ2sQ13E:X03Q4zQ2FQ4zQ2uQ4zQ2vQ4zPtQ4zQ1dQ4zQ24Q4zQ57Q4zQ4:Q4zQ1rQ4zQ2{Q4zQ3MQ4zQ4AQ4zQ44Q4zD^D1D1D1D1D1Q3UQ3cPEEDQ1geQ1gQ5PQ5iQ5PPaQ0yQ47P1Q0}CdQ2OQ1rQ3IQ1[E:W0PqQ2GPqQ2vPqPnPqQ3ZPqQ1rPqQ57PqQ44PqQ4;PqQ4TPqQ59PqQ4?PqQ4CPqQ2@PqD^D1D1D1D1D1Q2wP4PEEDQ1geQ1gPSQ2wPaQ18Q46Q3SP1CdPLQ4TQ3Jp+024S57E:X0SPSQ2DPaQ18Q46P1Q3=CdPLQ4TQ3JQ57E:X0SPSQ53PaQ18Q46Q2EP1CdPLQ4TQ3JQ57E:X0SPSQ1xPaQ18Q46P1PLQ4TQ3JQ57GGX0SPaQ11Q2OQ1rQ3ID9PaP@17cbQ0d9mc3Q11Q1gn0100000020000PzQ1rQ3ID9Q1[Q3nPaP2Q11Q2OQ1rQ3Ig04nLP3Q19Q4SPjPfg04oVPEg050`Q4{Q2CQ4{Q1zQ4{PnQ4{Q31Q4{Q3{Q4{Q4TQ4{Q44Q4{Q2@Q4{Q4<Q4{Q2?Q4{Q5:Q4{Q4@Q4{Q4DQ4{Q2YQ4{F\D1D1D1D1D1Q3=Q19PEEDQ0zeQ0zPbQ21Q56Q2?Q3600=L,B1Q03Q2QDhX0bPbPvQ56Q2?p+09mR`,B1Q03Q2QDhX0bQ3AQ33p+0:>S19181`'E70vX=61ebup+0:=S4{/_vQ3AQ3nQ3mQ3mQ3jQ4JQ3yQ3yQ4HPMPCQ28PKPZQ5\P:p+09dS44C{P;P<b:b;b<X16Q4{/31Q3@[^16P1Q3DQ0lO2b2b4b5b6b3Q3nQ3mQ3mQ3jQ4JQ3yQ3yQ4HPMPCQ28PKPZQ5ZP:p+07hR`C{P;P<b:b;b<X16Q0qp+0:;S5Z5N11A74S3{[^16P1Q3DQ0iO2b2b4b5b6b33YDZPgePgQ33PvQ33Q0ZQ2XP1Q03PjDhW0Q56PkQ56Q0Z?01jWHQ27Q2?Q0380IvP2p+03IRkQ2jQ34PvQ03PAP\Q2AQ2}Q06'8S06;wrXAAQ3AQ5<,81RvQ2}'3Q2a;w1X=6Q3kQ2<Q5[,81Q373wX=6Q5=Q0{+0:Q3\00:hQ5=Q0{Q3\PhPQQ5aPuPWQ2~Q3kQ3kQ39GjPQQ5aQ2UQ2eQ59Q3AQ3APVGjJ0sQ3pQ3nQ3nQ3mQ3^Q4JQ4JQ3yQ4jPCQ25Q057]7S25PKPZQ0^Q1I+01=CZGP:PZQ5bP:PZQ3:Q0^5CZP:Q4n9CZyQ4\60rZC{FPP;P<b:b;b<X16X86X?6X>PQ19=c87p+0:ARyp+0:@RV5N7Q51/3BQ2>,8>Q5R,8B7NH00:D[[[^16^86^?6^>PP1Q3zQ2oPXQ38POQ0lQ0uO7b2b4b5b6b3Q5:Q0YGkPwQ1mDZQ3CQ3H;wweQ4TQ1aE5Q3AQ3c,3vX=6Q1R,3uQ1R,3WPQQ5aPuPWQ2~Q1RQ1RQ4kGjQ3pQ3nQ3nQ3mQ3^Q4JQ4JQ3yPMPCQ28PKPZQ5\P:PZQ4YQ0aE|P;P<b:b;b<X16Q4{Q0q5N1Q4b,87?NH3[^16P1Q38Q0lO2b2b4b5b6b3PwQ1mGkQ1R,3gePAP\Q06Q3c'3XAAQ3kQ4XQ2_Q3zQ3VQ3pQ3nQ3nQ3mQ3^Q4JQ4JQ3yQ3]Q4ZP1Q2oPXQ0LQ07O4b2b4b5b6b3Q5:Q0YGkQ2AeQ4TQ1aE5N90qE5PrP1E?b7Q21Q0JE5Q1gP1E5b9PXQ5`,A1X=6Q4b-0PJQ44Q4m#FQ5F#z[[Q44Q1eQ5V>0NJ7UW@Q44Q1eQ5C#F[]@Q3pQ3nQ3nQ3mQ3^Q4JQ4JQ3yPMPCQ28PKPZPZQ40Q4RP:Q0MQ01#l60S69UZ]EuP;P<b:b;b<X16X>PQ5f9g71Q4R,A7[^16^>PP1%zrPrQ0DO3b2b4b5b6b3bEbFQ0q/_fQ3mQ3jQ3jQ3iQ3yQ4HQ4HQ4GPMPCQ28PKPZPZp+09FRJQ40P:Q44EuP;P<b:b;b<X16X>P%z1RA/;7Q3@[^16^>PP1PiQ2~Q0BO3b2b4b5b6b3Q3mQ3jQ3jQ3iQ3yQ4HQ4HQ4GPMPCQ28PKPZPZQ40P9P:P`EuP;P<b:b;b<X16X>PQ4a,A1RH,;7Q3{[^16^>PP1Q2~#zQ2~Q0BO3b2b4b5b6b35YXDZ-1LfNA1KQ5eQ36P1Q4{Q4QP{Q1FQ4{Q4QQ4{P{C@dO4b7PSQ0qPYP?Q0q/JYdPzDIPbQ4QPaQ1hP1Q2?Q2hQ1|E:X0bPbQ2SPaQ1?PSP1Q4SQ2?Q2hQ1|GGX0bPaQ0}Q4QQ4TQ3JD9PaP@Q33,7cQ1j9mc4Q0}p+02DRWn0100000020000PzQ4TQ3JD9Q57Q3pPaP2Q0}Q4QQ4TQ3Jg051jRvP4P4Peg0534%Wvg054>N=1JQ0\Q5]P1Q19Q4QP{Q1FQ19Q4QQ19P{C@dO4b7PbQ4{PYP?Q4{/JYdPzDIQ33Q4QQ33PaQ1WP1Q2XQ2jQ0fE:W0p+07^RvPjPvQ2DPvQ2IPvQ2zPvQ2{PvQ3}PvQ2XPvQ2YPvQ2ZPvQ4>PvQ3rPvQ2`PvQ4CPvQ3TPvPpPvD^D1D1D1D1D1D1Q3lP3PEEDPWePWQ4}Q3=Q4}PaQ11PSQ1f-0<1Q2OQ3rQ2mQ1^GGW0Q04PfQ04Q2EQ04Q2JQ04Q2{Q04Q59Q04Q3~Q04Q3rQ04Q2ZQ04PpQ04Q3KQ04PkQ04Q0~Q04Q4DQ04Q3RQ04Q2dQ04D^D1D1D1D1D1D1Q2|Q4oPEEDPWePWQ51p+084RpQ51PaQ12PbQ3l00<1PLPkQ2oQ1HGGW0Q51Q0]Q51PaQ12PbQ4`-0<1PLPkQ2oQ1HGGW0Q0aQ3`P1PyQ4`P}Q0o#HPyQ4`PyP}C@dO4b7Q51?0p|PoQ4`PaQ1?Q33P1Q4UQ3_p+05NRpQ0hGGX0oPaQ0|PLPkQ2oD9PaP@Q1{,7cQ4]Q0|Q1tn0100000020000P|PkQ2oD9Q1HQ3tPaP2Q0|PLPkQ2og055HRbPePeQ2gg056R%Wbg057\N=0TQ4fp+09`P1p+0:BRbPLP}Q52#HPbPLPbP}C@dO4b7PoPyQ54P?Q54,JydP|DIQ1{PLQ1{PaPWP1PNQ3LQ0jE:W0PTP|PTQ4~PTQ1zPTQ2LPTQ2}PTQ2`PTQ42PTPNPTQ4tPTQ58PTQ4@PTQ2BPTQ2pPTQ3RPTQ4FPTQ2\PTF\D1D1D1D1D1D1Q3YQ2gPEEDQ1teQ1tQ5_Q1}Q5_PaQ1iQ1:P1Q0zCdQ4VQ2BQ3NQ0mE:W0PUP}PUPdPUQ2HPUQ2MPUQ2`PUQ0~PUQ43PUQ2BPUQ58PUQ2\PUQ4APUQ2CPUQ32PUQ4EPUQ3XPUQ53PUF\D1D1D1D1D1D1Q3[Q1:PEEDQ1teQ1tPYQ3CPaQ1JQ1ZQ3>P1CdQ4WQ2CQ1AQ0nE:X0YPYQ1}PaQ1JQ1ZP1Q4WQ2CQ1AQ0nGGX0YPaQ1hQ4VQ2BQ3ND9PaQ1hP}PkQ3ND9Q0mQ3vPaP2Q1hQ4VQ2BQ3Ng058fQ1RQ1:Q04Q2yQ1}g05:0PEg05;:p+07dRkQ2MPkPtPkPgPkQ2IPkQ2NPkQ0~PkQ5gPkQ45PkQ2CPkQ2\PkQ53PkQ4CPkQ1xPkQ39PkQ3WPkQ4GPkQ5;PkF\D1D1D1D1D1D1D1RkQ3]Q1RPECKP=eP=PFQ2QQ55Q3W,B1;0jX0FPXQ55p+0:FRUQ5h'E;0jX=6P6PFQ4yQ4y18X5PXQ4?Q3vQ3QQ3QQ3OQ4PQ4OQ4OQ4NQ4hQ5R,81RW/85/QW^16P1PrO1b2b4b5b6b3L0vQ0~Q3vQ3QQ3QQ3OQ4PQ4OQ4OQ4NQ3hQ4dP1Q5iPrQ0uQ17O4b2b4b5b6b3Q3vQ3QQ3QQ3OQ4PQ4OQ4OQ4NQ3pQ4cP1Q5iPrQ07Q0XO4b2b4b5b6b35YXDZQ2Q90Fnep+02CRnP1E5b9PkQ3]Q1:PECKQ0peQ0pPFQ2WQ55Q3>701X0FPFQ2WQ1tP1FXb9P2P\Q1AQ2BQ2yQ2DQ1AQ2Q41IP2Q1AQ2mQ2yp+0:7P\Q2oQ4sQ3JQ3IQ3FQ3QQ3OQ3OQ3tQ4OQ4NQ4NQ4LQ3tQ4sP1Q30Q0?O2b2b4b5b6b3Q3GQ0`GkQ2beQ1vQ2oQ0~,31X=6Q2S13p1X=6Q3QQ3OQ3OQ3tQ4OQ4NQ4NQ4LPMPCQ26PKPZQ4uP:PZPmQ1K,[GE|P;P<b:b;b<X16X86Ac1b7p+0:IRbQ5Z,885c7[^16^86P1PwQ30Q07O3b2b4b5b6b3Q2`Q1kDZQ3GQ0`DZQ3GQ2`'3eQ2SQ5WQ3F5N1X=6Q2oQ35Q0\,81'3X=6Q2j,3IQ34Q2h'3PQQ5SPIQ34Q2zQ2jQ2hQ2sGjQ3QQ3OQ3OQ3tQ4OQ4NQ4NQ4LPMPCQ26PKPZPeP:PZQ3xQ4rE|P;P<b:b;b<X16X86P1PyP7PVCtQ5Z,87Q4{1S8b/8b3N[^16^86P1Q30PwQ0`O3b2b4b5b6b3Q3GQ0`GkQ2`Q1kDZQ2r,3heN:0uK1GNB0tQ1jQ1SP1p+0:ERbQ4VPtQ4[#HRVPbQ4VPbPtC@dO4b7PYp+0:DRyQ5<P?Q5<,JydP}DIPFQ4VPaQ4BP1PNQ3PQ0pE:X0FPaQ0|Q4VQ3_Q1AD9PaP@Q55,7cQ1:9mc4Q0|Q0wn0100000020000P}Q3_Q1AD9Q0nQ3wPaP2Q0|Q4VQ3_Q1Ag05<DRNP4Q1:Q4Ug05=N%WNg05>XN=0RQ2lQ44P1PUQ4UPtPVPUQ4UPUPtC@dO4b7PFPbQ5<P?Q5<,JbdP}DIQ55Q4UQ55PaPnP1Q2BQ30P=E:W0Q1wQ1CP1p+0:GRnQ5HPtQ4b#HPnQ5HPnPtC@dO4b7Q55Q5U;0}Q54Q5HQ54PaQ1iPSP1Q4WQ2CQ5iQ0sGGW0PaQ1fQ4VQ2BQ30D9PaP@Q52,7cQ1_Q1fQ1|n0100000020000P}Q2BQ30D9P=Q3;PaP2Q1fQ4VQ2BQ30g05?bR=P4Q5_PTg05@l%W=g05B6N=0RQ1IQ02P1p+0:HR=Q4ePtQ2K#HP=Q4eP=PtC@dO4b7Q54PnQ4mP?Q4m,JndP}DIQ52Q4eQ52PaQ1^P1Q1xQ21p+02@RnE:W0P`P}P`Q2WP`Q3}P`PrP`Q2LP`Q3>P`Q32P`Q39P`Q48P`Q2FP`p+048R?P`Q3CP`Q3RP`Q2GP`Q34P`Q4HP`Q3^P`Q2AP`F\D1D1D1D1D1D1D1Q50PYPEEDQ1|eQ1|Q5<Q3sQ5<PaQ1hPSQ4H,B1Q2xQ2DQ3SQ0wGGW0Q5<Q3sQ5<PaQ1hPSP1Q2xQ2DQ3SQ0wGGW021F2nQ3s/B5Q3s$0[E5Q0wP1E5b9PtP1E?b7ELPtP1E?b7PtP1E?b7ELPtP1E?b7ELQ2WQ3C+06Q3>Q2fQ2c'SQ3QQ3OQ3OQ3tQ4OQ4NQ4NQ4LPMPCQ25PKPZQ1>P:PZQ4\Q1n5bZP:Q0RQ1>5bZFPP;P<b:b;b<X16X86X?6X>PAc178Q00,;B1S8>Rt#F13tB';[[^16^86^?6^>PP1Q2V#FQ4qQ2VQ2iQ1mQ0LO6b2b4b5b6b3Q3QQ3OQ3OQ3tQ4OQ4NQ4NQ4LQ3jP{P1Q4qQ1kO2b2b4b5b6b3H0aE5Q0zP1E5b9Q0zP1E5b9P}P1E?b7ELP}P1E?b7Q3?Q0vE5Q1fP1E5b9Q1fP1E5b9P{P1E?b7ELPjQ4~Q3nQ3mQ3mQ3jQ4JQ3yQ3yQ4HPMPCQ28PKPZPZPJP9P:Q44=bZ9EuP;P<b:b;b<X161;AHQ3@Q5L7g7[^16P1PwQ0CO2b2b4b5b6b3+1HE5P{P1E?b7ELQ2DQ53+06Q2EQ5;Q3mQ3jQ3jQ3iQ3yQ4HQ4HQ4GQ3:/TMPCQ059]^8?]7^RHPKPZQ55P:PZQ0[9CZ[Q0[=UZ]5bZP:Q5@FPP;P<b:b;b<X16X86X?61317Q5K?g>7Q5TQ1X';[[^16^86^?6P1P?Q2IQ2cQ0YQ0VO5b2b4b5b6b3Q3mQ3jQ3jQ3iQ3yQ4HQ4HQ4GQ4IQ3vP1Q2IQ0gO2b2b4b5b6b3H0aE5Q2wQ07E5Q21Q0JE5Q0}P1E5b9Q0}P1E5b9PsP1E?b7ELP{P1E?b7ELQ39Q1_+0FQ5GQ4_Q3gQ3fQ3fQ3eQ4FQ3WQ3WQ4EQ3?Q4KP1Q2sQ3kQ1OQ1lPOQ0iO6b2b4b5b6b3Q3gQ3fQ3fQ3eQ4FQ3WQ3WQ4EPMPCP^PKQ5?9CZ[Q5?Q0R5UZ5bZP;P<b:b;b<Q1G#FQ1GQ1:3gP1b2b4b5b6b3H0wE5Q30Q0iE5Q1?P1E5b9Q1?P1E5b9PsP1E?b7ELQ2tQ58E5Q15P1E5b9PsP1E?b7ELPsP1E?b7ELPsP1E?b7PsP1E?b7ELP{P1E?b7ELQ3|P1E?b7ELQ1]Q1y+0FQ1]Q20Q4p'SQ3qQ3oQ3oQ2|Q4?Q3MQ3MQ3KQ36Q5XQ5H'f'f$03/TMPCPHPKPZp+07aP:PZQ0RP:PZPZACZ[GP4P:Q5EAUZ3_5bZEuFPP;P<b:b;b<X16X86X?6Q3:,A8Q5JQ5M1S>BRB#FQ1;7gB[[[^16^86^?6P1Q2XQ24Q2@Q0=Q29Q2:O6b2b4b5b6b341DE5Q1NP1E5b9Q1NP1E5b9Q3ZP1E?b7ELQ4qQ2R+06Q4pQ4^Q3lQ3?Q3?Q3=Q4>Q4=Q4=Q4<PMPCQ26PKPZp+089P:Q5HC{P;P<b:b;b<X16X86Q5YQ5N';RBQ3@Q1o';[^16^86P1Q24Q41Q0<O3b2b4b5b6b3Q3lQ3?Q3?Q3=Q4>Q4=Q4=Q4<Q3SQ3<P1Q1rQ24Q0:Q0;O4b2b4b5b6b3H0aE5Q2sQ0gE5Q1qP1E5b9Q1qP1E5b9P}P1E?b7ELQ4zQ2W+0WQ3>Q2wQ3UQ3UQ3SQ4;Q4:Q4:Q49Q5SQ0Z'f$03/TMPCQ5IPKPZPqP:PZQ0PP:PZPZQ3BQ5>P:Q50EuFPP;P<b:b;b<X16X86X?61A8`Q1XQ5TQ1L';Q5KQ1Q7g>[[[^16^86^?6P1Q3aQ41Q4qQ3dQ08Q09O6b2b4b5b6b3+1ME5Q1EP1E5b9Q1EP1E5b9P|P1E?b7ELP|P1E?b7Q1BP1E5b9P{P1E?b7ELP|P1E?b7ELQ3\Q4u+0FPxQ1cQ1AQ3NQ3NQ3LP~Q45Q45Q43Q3EQ4;P1PiQ2uQ08Q09Q2:Q27O6b2b4b5b6b3Q1AQ3NQ3NQ3LP~Q45Q45Q43PMPCP^PKp+08?R^9CZ[Q5E9UZ^5bZP;P<b:b;b<Q5O#FQ5OQ5\3gP1b2b4b5b6b3H0wE5Q2]Q27E5Q1aP1E5b9Q1aP1E5b9P{P1E?b7ELP{P1E?b7Q1dP1E5b9P{P1E?b7ELQ2FQ2H+0GQ2GQ2IQ2jQ2hQ2hQ3JQ3~Q3}Q3}Q3|PMPCQ26PKPZQ1_P:Q1_C{P;P<b:b;b<X16X86Q3@Q3u';\B^16^86P1Q2MQ1pQ2[O3b2b4b5b6b3Q2jQ2hQ2hQ3JQ3~Q3}Q3}Q3|Q3GQ3iP1Q23Q2MPlQ2=O4b2b4b5b6b3H1NE5PuQ0;E5Q2?P1E5b9Q2?P1E5b9PsP1E?b7ELPzP1E?b7ELQ3|P1E?b7ELQ07Q0`Q3d';PRPrQ5APECKQ07eQ07P9Q4kQ4l90_1X09P9Q4kQ0WP1FXb9Q0`Q3dPRPrQ5DPECKQ0`eQ0`P9Q2nA0_1hX09P9Q2nQ0TP1FXb9Q0@Q08PRPrQ5BPECKQ0@eQ0@P9Q2cQ2WQ1}Q0QP1E5b9Q0JQ09PRPrQ5EPECKQ0JeQ0JP9Q1UQ2hQ3JQ0OP1E5b9Q0lQ0:PRPrQ5FPECKQ0leQ0lP9Q1UQ2hQ3JQ0SP1E5b9Q0iQ0;PRPrQ5CPECKQ0HeQ0HP9PwQ2f90_1X09Q14Q0cP1E5b9POQ0<PRPrQ2xPECKPOePOP9Q2cQ2WQ1}Q0_P1E5b9Q0LQ0=PRPrQ5`PECKQ0LeQ0LP9Q1TQ1V90_1X09P9Q1TQ0bP1FXb9Q0eQ29PRPrQ5^PECKQ0eeQ0eP9PdA0_1gX09P9PdQ0NP1FXb9Q1mQ2:PRPrPqPECKQ1meQ1mP9Q4~A0_1dX09P9Q4~p+01BP1FXb9Q1kQ27PRPrQ5cPECKQ1keQ1kP9PgA0_1iX09P9PgQ0AP1FXb9Q1lQ3bPRPrQ4zPECKQ1leQ1lP9PXQ4~90_1X09P9PXQ0KP1FXb9Q1OQ0BPRPrQ4yPECKQ1OeQ1OP9Q2SA0_1XX09P9Q2SQ17P1FXb9Q0UQ0CPRPrPmPECKQ0UeQ0UP9PfQ2S90_1X09P9PfQ0XP1FXb9Q0VQ0DPRPrQ4xPECKQ0VeQ0VP9PjA0_1fX09P9PjQ0?P1FXb9Q0YQ0EPRPrQ4wPECKQ0YeQ0YP9Q2QA0_1jX09P9Q2QQ0>P1FXb9Q0gQ0FPRPrQ4vPECKQ0geQ0gP9Q2yQ2Q90_1X09P9Q2yQ10P1FXb9Q1vQ0IPRPrQ4uPECKQ1veQ1vP9Q3kQ2y90_1X09P9Q3kQ0xP1FXb9PRPrQ4sPECKQ0IeQ0IP9Q2PQ3k90_1X09P9Q2PQ0vP1FXb9FvFvFvFvFvFvFvFvFvQ0GeH0`H1CbPWLWYW[WXWZW`WJW^W]W_WKW\aaaaaWVWWaWMWNaaWaWbWUWQWTWRWSWOaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWDaaaXl6aaaaaaXi6aaaaaaaaaaaaaaaaaaaaaaaaaaaXh6aaXc6aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaXf6aaaaaaXe6aaaaaaaaaaaaXd6aaaaaaaaaaaaXn6aXm0WgaaaaaaaaaaaaaaaWjaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) :=
  wbytes (wbytes (wbytes mem1
    (Z_to_bv 64 (f + 32)) (word_to_le_bytes 8 (v_add bufp bufsz)))
    (Z_to_bv 64 (f + 40)) (word_to_le_bytes 8 bufp))
    (Z_to_bv 64 (f + 56)) (word_to_le_bytes 8 bufp).

Lemma sw_done : forall regs mem rom (su f : Z) (l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v : word),
  getr regs 2 = Z_to_bv 64 (su - 112) ->
  getr regs 8 = l -> getr regs 9 = Z_to_bv 64 f ->
  getr regs 21 = Z_to_bv 64 0xf8ac0 ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0xc6000 <= f)%Z -> (f + 232 <= 0xf8ac0)%Z ->
  ret_ok ret ->
  rdn RSEGS mem (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 s0v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 s1v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 s2v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 s3v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 s4v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 s5v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 s6v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn RSEGS mem (Z_to_bv 64 0xf8ac0) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz) ->
  exists regs',
    msteps RSEGS (mkst regs (0xae568 : word) mem rom)
                 (mkst regs' ret (mem_sw2 mem f bufp bufsz) rom)
    /\ getr regs' 10 = l /\ getr regs' 2 = Z_to_bv 64 su /\ getr regs' 1 = ret
    /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
    /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0143 ()) ["FPX_1"] "h07__arithh14__x1h27__sat73h37__sat74h41bh54__ffh68__varmaph75__with81nh91zh:4__p1h;4__x2h<1Hh=2gHh>1oh?1xh@2HahA2b1hB2b2hC1mhD5regs'hE1yhF3FhihG3FlohH4HrethI3Hs0hJ3Hs1hK3Hs5hL3HsphM3M16hN3M24hO3M32hP3M40hQ3M48hR3M56hS3M64hT3M72hU2M8hV4MbszhW4MbufhX4McanhY4SUhihZ4SUloh[4bufph\5bufszh]3canh^1fh_1lh`3memha4regshb3rethc3romhd3s0vhe3s1vhf3s2vhg3s3vhh3s4vhi3s5vhj3s6vhk2sup%0p%1p%2p%3p%4p%5p%6p%7p&0p&1p;1p;2p;3p;4p;5p;6p;Ap;=p;Bp;7p;>p;<p;8p;9p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p4p710g004`R1p4p710R2p8p1005>p4p710P2p8g005]j19Tg006Bk10CTg006`k102Tg007Cj1BTg007hj1bTg008Fk104Tg00MAj2^Tg008ej31Tg00;TR2j20Tg00<0k10tTg00<Nk20FTg00<gR3j22Tg00=Dk40oTg00>Gk20LTg00?Yk30^Tg00E0k20nTg00E\k10DTg00F<k30:Tg00BHk10JTg00:Mk20ZTg009jk20jTg00@fk11ITg00AIk10WTg00Bhk30BTg00Akk21FTg00DMk31ATg00CKk31?Tg00=gR4k10eTg009?k11:Tg00;0k516Tg00K^j2Ok10zTg00M]j3oTg00LDk20|Tg00Ldj2FTg00ORj2?Tg00H6k10bTg00PFk20yTg00Pnk30xTg00QRj2mTg00Y<j2\Tg00I:j2`Tg00F\k20OTg00GXk10wTg00HXk20vTg00ITk20uTg01Hik30aTg00J@k40sTg00K2k10rTg00G:k10qTg00dNj3>Tg00UCj2@Tg00Uoj2:Tg00XJj5;Tg00SOj4cTg00NJj2kTg00Yfj3XTg00Taj2sTg00Vak20`Tg00WAk20_Tg00]gj2rTg00`Uk30KTg00aPk30]Tg00bQk20mTg00[4R5j2UTg012Pj4RTg05Mgk10lTg010;j6DTP1j65Tg010Wj1qTg011[lAnTg00i`j2YTg01Mjk10YTg015>m=1HTg05N`k50VTg00jCmB0PTg01PHk70UTg00him=0iTg00ZZj26Tg00lej6KTg01F_k41@Tg016kk20fTg03VNk11>Tg05Ofm>1=Tg05P_k20dTg05QZm>19Tg01=`k218Tg01>\k117Tg01Qnk40QTg01Cnk415Tg05R[k414Tg00hOk213Tg01EWk312Tg01DHk406Tg01E3k705Tg01JOk30STg01F:m<11Tg01HEk80=Tg01IimB10Tg01IHk41;Tg01LIm<0~Tg00l:k40}Tg01K2k40HTg01Lnk30XTg01G=k61BTg01QJk70gTg03jDm91CTg01Njk81DTg01RIk71ETf0R1#B#9p>0;%91#9p>08%91#bp>0@%B1#Bp>0>%B1#B#9#9p=i%91#Bp>0E%91#B#9#Bp=t%91#9#9#bp=h%91#9#9#9#9#9#9#9p>0A%91#9#9#9p>0Rg01ScR6/01p=vg01SER7f3R8f2R9'\f1R:/\131p=T%B1#9#B#9p>0c%B1#B#9#Bp>0?%B1#9#9#bp=}%91#B#9#B#B#B#9#9#B#9p=l%B1#9#B#Bp=u1`71p=NA17:1p==%91#9#B#9p>0[B127:1p>09g01X5R;:0B:1p=C%b1>0B:;p=_20j71p=ZP9g01TAR<g01T`R=P=g01U@R>P7P:g01U`R?P1H06g01VGR@K05p=pB0S7:1p=d129:/01p=Ag01XQRAP7P7P7P4P4f5R4f4RBP8P9P:P1N<11p>0{P4P<P=P=P>PBP8P9P<P=P=P>P7P:P?P1H06P@K05L0=p=VP4P<P=P=P>PBP8P9P<P=P=P>P7P:g01VgRCP1H06P@K05L0=p=fP8P<P=P=P>P9P:P1L0=p>0G10B8129:/01'6p={P7P7P7P7P7P7P3P1P:P9P3P8PBP4f6R3f7RDf8REf9RFNB10p=jg01ZYRGg01`URH711p>0NP9P:P>P1H1;p>0<P9P<P=P=P>P7P:PCP1H06P@K05p>0pP7P7P2PDP2P3P4PBP8P9P:P1N<0~p=3P7PDP3P4PBP8P9H0}P:P1E5p=4g01Y0R2P9P:P1H0Hp=G12:1,O9p>0M&0D1:0:9::0:B8p=wB0:4B8P9P:P1CRp=[&0D1:0:9:p>00B0:9:1:0:B8p=<PDAX34BP8P9P:D;>0X21p>03P3P<P=P=P>P4PBP8P<P=P=P>P7B0S79:P?P1H06P@K05L0=p>01P2P8P9P:H0H=1B1p=gB0X2:1p>0\1:9:=181p>0k1:89=1B:/U1p=aP2PB1?89P:H0H=141p=P12:1,O991B8p=~P7P3P4PBP8A>9:1E5p=eB0B89:=1B1p=WP4PBP8P9P:D;>0X21p=QP3P4PB1`89P:P1E5p=]P7PBP8P9P:P1E5p=E1\:19179p>1G10:1,69p=7109:/61p=IP:P<P=P=P>P1J1Bp>0hP4P<P=P=P>PBP8P9P<P=P=P>P:P1K0gL0=p>0I129:/01,68p=HPAPBP8P9P:P1E5p=8P2PDP3P4PBP8P9P:P1N91Cp=JPDP3P4PBP2P8P9P:H0HP1E5p=x1O:19189p>0TP8P<P=P=P>P7P9g01WNRCB0S7:1H06P@K05p=y1F9:/219178p=|P7PDP3P4PB1289P:P1L1Dp=zPBP<P=P=P>P8P9P<P=P=P>P7P:P?P1H06P@K05K0gp=MP3P<P=P=P>P4PBP8P<P=P=P>P9P:P1L0=L0=p=LP9P<P=P=P>P7P:PCP1H06P@K05p>1<P2P4PBP8P9P:P1K1Ep=SP3P4PBP8P9P:P1H0QH0Qp>07g01\5R@#9RC#9R?#9RI#9RJ#9RK#9RL$0Cg01\ZRM&0CI$02P0%B@RN$0;RO$08RP$0@P7%bIP7&0>@#i$0E#t$0;$08#hP7&08L$0A$0A$0ARI#bP7&0RI$0A#hP7%9NRI#9RQ#9RR#i$0A#hP7%BO#hP7g01]]RO$04RS$04RT$04$04$04$04$04$04PA%bJP7%bRP7%bKP7%BCRK#9RJ#9RU#9RV#bP7%9RRR#bP7%bPP7%bLP7%B?RL#9RP#9$0@P7%BKRW#9RX#9$0@P7&0@RP7&0CQPM%bCRR,^6p-0RY%vRPY&021RZ&02:R[P9P:P9P1CTR\&028?19:R][]B]A^8MR^PY%t@#i$0c$0?#}P7&0CKRK$02P0%l@#u$0;#hP7%l@#u$0;#}P7&0>@$0?$08$0A#hP710:1R_$0tXE7X?720F__^E7^?7P7P7g01^<12:1H0oR_#NXC7X871=__^C7^87%l@#u$0>#hP7%l@#u$0>#}P7%t@#i#u$0R#hP7%t@#i#u$0R#}P7%l@#i$0E#hP7g01_=R_20L7T20L7S20L7O60^760^7g01_i+0n&0D_RO40:&0J_R_%l@#i$0E#}P7%t@#i#u$0[#hP7%BIS00#9S01#9$0@P7%t@#i#u$0[#}P7%l@#i$0>#hP7%l@#i$0>#}P7&0@VP7%l@$0?$08#hP7%l@$0?$08#}P7%t@#i#u#t#hP7%t@#i#u#t#}P7%l@$0?$0;#hP7%l@$0?$0;#}P720Z7@RV20j76RI+09&1I7RSfbRT$02P0&0WTP01CKRfKS021CKTfLR`1_KLfMS03%BJ,_KfNS04fcS05ffS06'2P7fhS07$0JP01_KJfQRJ1_K@fRRa1_KPfSS08%BL,_KfTS091_KUfURU1_KXfVS0:1_KNfWS0;%b?R?,CKfXS0<%BW,_KfYS0=Q07,CKfZS0>%BQ,_Kf[S0?Q01,_Kf\S0@Q00#B,_Kf]S0A1_KWf^S0B1_KQf_S0CB0BK6;f`S0DfsS0E#ZPSfuS0F/01%v:[^17PYflS0G#vPYfmS0H-1FRP7fvRQ#ZPSf{S0I#ZPS%ZRp+01AS0J61A7PSP\PYP5P:\]&02B?189\1&024?1B8\:B1?89:P1n2001000000120000000aXB[XAZX8MP^f|S0K/01X97PY^97R^fwS0L#ZPSf~S0M/01fzS0N,2:#v[^17PYQ0K$0eP7fjRM#N1=MMp+01ES0O#ZPSQ0G#ZPSQ0K#ZRZPSQ0O/01p+01@R[,2:#vR][^17PYPZPSp+01GS0P/01P][^17PYp+01JS0Q#NQ0QQ0Q'=p+01KS0Rp+01LS0S'2P7Q0M#ZPSp+01OS0T#ZPS&1:7R]Q0S#Z7pVP]P<P=P=P>I16R<p+01IS0U#Z-09VRZPSPZPSQ0P#ZPSp+01FS0V#ZPSp+01CS0W$02P0fdRZPZ[P0p+01YS0Xp+01US0Y'OfeS0ZQ0C$0WP0p+01[R5%9@#u$0;$0E#t$0c$08'_fgS0[Q0D=oKJPGfiS0\$0WP0Q0QQ0S'CP3Q08=p]VP<1^6JPY%vaPY1dVa=p]JP<p+01\R@p+01`S0]5A1Q0:,^:[^17PYp+01dS0^Q0S'CfpS0_Q0@Q0>5oKPGp+01RS0`p+01SS0a'Cf>R\p+01NS0bQ0E+0|P0p+01hS0cQ0b'CftS0dp+01iS0eQ0b'CQ0Fp+01VS0fp+01^S0g'CfBRWQ0:,dVRNPSp+01eS0hQ0e5A1p+01bS0i,2:Q0C'^[^17PYQ0;Q0`5A1X97P^P1X?7RXPX&0e1RL#NX?AQ0hp+01kS0jQ0j#NJ0{PXQ0;O1PXQ0jO1'=p+01oS0kp+01PS0l'CQ0Ip+01cS0m,C@fHRPPNPSQ0jQ0k5A1p+01gS0n,2:Q0Z'^[^17PYp+023S0oQ0a'CP[Q0]Q0h'CP`Q0<,dVPSQ0kQ0o5A1Q0e,2:Q0\'^[^17PYp+027S0pQ0f'Cp+01DS0qQ0^@0B6;fPS0rp+029S0sp+01WS0t'CQ0Vp+026S0uQ05'2P7Q0ZQ0H5A1X97P^Q0@Q0H'0PYfnS0v#NQ0vQ0v'=Q0pp+02;S0w5A1p+024S0x,2:RNp+02=S0yfqS0z3A[^17PYp+028S0{p+02<S0|5A1p+02>S0}frS0~5AN[^17PYQ0sQ0y5A1Q0o,2:p+02?S10Q0E3A[^17PYp+02AS11Q0g'CQ0bp+02BS12$0zQ0l^97p+01QS13\7P0Q05-09VR0PSP0PSQ11#Z/dZ=p]VP<Q0T/01p+02GS14,F:#v[^17PYp+02CS15,01p+02HS16,F:Q0I'^[^17PY20Z7CRCfyS17'dfxS185p]P<Q0F,dCQ0z'dPSQ0_,dCQ0~'dPSfoS19,dCQ0E'dPSp+02MS1:Q0c'Cp+01ZS1;p+02NS1<Q0c'CP5Q0wQ0c'CQ0[Q0L-09VPSp+02QS1=Q0e'CQ0gp+02RS1>Q0e'Cp+01_S1?p+02SS1@Q0e'CQ0]p+02@S1AQ0e'CQ0GQ0J-09VRCPSp+02VS1Bp+01jS1C'CQ0mQ15p+02FS1D'CQ19f}S1E-09VPSp+02YS1Fp+01lS1G'Cp+01fS1HQ1Dp+02JS1I'CQ0~Q0F-09VPSp+02\S1Jp+01nS1K'CQ0ePCPSp+02^S1LQ0k'CQ0jp+02KS1MQ1='CQ0LQ17-09VPSp+02aS1Np+021S1O'CQ1KQ1<p+02`S1P'CQ0Np+02cS1Qp+022S1R'Cp+020S1SQ18/??Q1OQ1R$0bQ0LP]PQ&0b=R=P]PIPVEVP<p+02WS1T-0yRQ1>Q18\5[Q1@Q17\@[PYQ1@g01[9RCp+02[S1U>0xR:UW@Q1@Q17\C]@p+02TS1VQ0N\C]@PYP]Q18P=P]PVQ1;EfP<Q0L/??Q0sQ1F/mQP7Q0F/??RCQ0wPCQ0|P]Q0JP=Q0d9p]IRRH0GP<P]Q0MP=P]Q0FQ0]EfP<Q1;,dQPSQ0E/??Q1AQ1PQ0E'mP7P]Q0VP=P]PIQ0EEVP<P]Q0qP=P]Q0dQ0hEfP<Q0FQ1?'dPSQ0d/??p+02ES1Wp+02eS1XQ0d'mP7P]Q0RP=PRH0GP<P]Q0UP=P]Q0FQ1CEfP<Q0^,dQPSp+02iS1YQ0d'mP71?Q?Q1MPCp+02LS1ZQ0t/?6Q1:p+03ARCp+01XS1['\P7Q18P1P1p+01mS1\p+03?S1]D{X97P^PXPXPXQ1XQ1]Q1]Q0hQ1\p+03@S1^Q0OM:jPXQ18O1Q0^'=Q0~/??Q1=Q0zQ0~'`Q0zQ0~Q0~31P]Q19P=P]PIQ0_EVP<P]Q0hP=P]Q0zQ0uEfP<1?M?RSp+02US1_PSQ1BQ07/??RSQ1TPSp+02XS1`PSQ1FQ06/??p+02ZS1a1?Z?Q1U1?T?Q1JfaS1b/??p+02]S1cp+03=S1dQ0B'mP7Q0D/??p+02_S1eQ1HQ0A'`Q1HQ0AQ0A31POP_20O7:R?&0w7RSQ0D20v]>R>P1P91`GH20u19$0NdB0a76:H0sRHb5b6b7X1720O71:0a76$0rRRQ0B60<]^17POP_P?PSQ0@P>PHb5b6b7X17Q0>:0<]R^17POP_P?PSQ0<P>PHb5b6b7X17R0Q0::0<]R^17RNP0PNPOP_P?PSPUP>PHb5b6b7X17RNQ08:0<]R^17R0PNP0POP_P?PSPaP>PHb5b6b7X17R0Q0r:0<]R^17RNP0PNfJRNQ1D'2P7p+03YR0POP_&0q7S1fPSp+02OS1g9p]IP>PHb5b6b7%v0P1b0Q0ZPZPZQ05POP_Q1fPSQ1=p+02PS1h60p]P>PHb5b6b7p+03[Q1='^P1b0b2b33>Q02/=0P]Q1GP=P]Q0?Q1:EVP<P]Q1\P=P]Q0;Q1<EVP<P]Q1KP=P]Q08Q1gEVP<POP_P?PSQ03P>PHb5b6b7X17R<Q02:0<]R^17RbP<PbQ1_,03PYPOP_P?PSPEP>PHb5b6b7X17RbB0<]R3^17RRPbPRPbPRp+03cRRP@p+01]RbQ1F'0P5PXp+03JS1iPbQ16Q08Q1FQ1FQ1;G3Q19Q0vQ0vQ0HPOP_Q1fPSQ1UQ1@'dQ1a5p]P>PHb5b6b7PbP1b0b2b3PUPFG4P8eP8p+035S1j,@Kp+034S1k,:1p+036S1lQ1k,::p+037S1mQ1k,:9p+038S1nQ1k,:8p+039S1op+02lS1p,:Bp+03:S1qQ1p,:4p+03;S1rQ1p,:3p+03<S1sQ1p,:DQ1dQ1p,:Ep+03>S1tQ1p,:FQ1]f:R<Q1p':Q1^Q1ZQ1Zp+03lS1u5G1Q1MQ1<p,2fxRcP\Q1ZP9P1D;g01a5Rdp+047S1v,F1P7Q1v,F:P7p+041Re,F9P71F8eP71FBeP71F4eP71F3eP71FDeP71FEeP71FFeP7p+04CS1w/OFp+03PS1xp+04DS1y/OFp+03QS1zp+04ES1{/OFp+03RS1|p+04FRf/OFp+03SS1}p+04GS1~/OFp+03TS20p+04HS21/OFp+03URgp+04IS22/OFp+03VRhp+04JS23/OFp+03Wp+04KS24/OFp+03XRip+04LS25/OFP0p+04MS26fDS27'Op+03ZRjf;S28Q1n'2P7f<RkQ25'2P7f=Rl#N1=llfFS29Q1r'2P7fGS2:p+04OS2;'2P7%NP1=PPQ1t,2PP7fIS2<p+04RS2='2P7%NN1=NN12NCP7Q02p+04US2>'2P7%N`1=``p+03DS2?,2`P7Q03p+04XS2@'2P7Q04#NQ04Q04'=Q04p+03GS2A'2P7fOS2Bp+04[S2C'2P7Q0r#NQ0rQ0r'=Q0rQ1i'2P7p+04^S2D,2JP7%Na1=aap+03MS2E,2aP7Q08p+04aS2F'2P7Q09#NQ09Q09'=Q09Q1x'2P7p+04dS2G,2UP7Q0:#NQ0:Q0:'=p+04iS2HQ0D/F6'Op+046S2IQ0ZQ2F7GUQ1^Q06p+04bS2J7GUPCQ0[p+04cS2K7GUp+03BS2LQ07Q2G7GUp+03CS2MQ0\p+04eS2N7GUQ2?p+04fS2O9GMUp+03ES2PfkS2Qp+04gS2R7GUp+03FS2SQ0Gp+04hS2T7GUQ2AQ0HQ2H7GUp+03HS2Up+053S2VQ0C'\P7Q0DQ2R'?p+04AS2Wp+055S2XQ0<'\P7Q0<P1P1p+03aS2YPZD{X97P^PXPXPXp+04YS2ZPZPZQ0:Q2Yp+054S2[Q1oM:jPXQ0<O1Q0;'=p+04QS2\,?ZQ1{p+059S2]/\ZP7Q0=P1P1p+03eS2^Q0_D{X97P^PXPXPXp+04]S2_Q0_Q0_Q0;Q2^p+058S2`Q1dM:jPXQ0=O1Q0<'=Q07Q2H'?Q22p+05=S2aQ0['\P7Q0>P1P1p+03iS2bQ0ED{X97P^PXPXPXQ2FQ0EQ0EQ0<Q2bp+05<S2cPCM:jPXQ0>O1Q0='=Q0Gp+04nS2d'?Q26p+05AS2e/\MP7Q0?P1P1p+03mS2fPQD{X97P^PXPXPXQ2NPQPQQ0=Q2fp+05@S2gQ2PM:jPXQ0?O1Q0>'=Q0_Q2Z'?Q2\p+05ES2hQ0H'\P7Q0@P1P1PeQ17D{X97P^PXPXPXQ2HQ17Q17Q0>Pep+05DRCp+03IS2iM:jPXQ0@O1Q0?'=Q0dp+057S2j'?Q2>p+05IS2kQ0_'\P7Q0AP1P1p+045S2lQ0KD{X97P^PXPXPXp+04mS2mQ0KQ0KQ0?Q2lp+05HS2nQ2EM:jPXQ0AO1Q0@'=Q18Q2c'?Q2Zp+05MS2oQ0E'\P7Q0BP1P1p+049S2pP[D{X97P^PXPXPXp+051S2qP[P[Q0@Q2pp+05LS2rQ1zM:jPXQ0BO1Q0A'=Q0KQ2e'?Q2_p+05QS2s/\QP7Q0CP1P1p+04=S2tQ0WD{X97P^PXPXPXQ2XQ0WQ0WQ0AQ2tp+05PS2uPgM:jPXQ0CO1Q0B'=Q0Jp+05FS2v'?Q2Fp+05US2wQ17'\P7Q0DP1P1Q2WQ0VD{X97P^PXPXPXQ2]Q0VQ0VQ0BQ2Wp+05TS2xP0M:jPXQ0DO1Q0C'=Q0Op+05VS2y'?Q2NQ2OQ0KQ0931PYQ09Q1y'2P7Q2TQ0P;1aPY12afP7p+04jS2zp+01HS2{Q0r31PYQ0rQ21'2P7p+04lS2|Q0UQ0431PYQ04Q23'2P7Q2dQ0Q;1`PYQ25,2`P7p+050S2}Q0R;1NPYp+04NS2~,2NP7p+052S30Q0S;1PPYp+04PS31,2PP7Q2[p+01MS32Q2931PYQ29Q2='2P7p+056S33Q0bQ2731PYQ27p+04TS34'2P7Q2`Q0z;1WPYfAR0Q2D'0PYf@S35p+04_S36'0PYf?S37p+04`S38'0PYQ2F,0\PYQ2J,0lPYQ2K,0kPYQ28Q2G'0PYQ2N,0<PYQ2O,0FPYp+05jS39,21P7Q39,2:P7p+05iS3:,29P7p+069S3;/O8Q2vp+06:S3<p+05hS3=80MBp+05GS3>p+06;S3?Q3=80M4Q2np+06<S3@/O4Q2kp+06=S3A/O4p+05JS3Bp+06>S3C/O4p+05KS3DQ2H,2EP7Q3A,2FP7%N<1=<<Q2|,2<P7Q28p+06@S3E'2P7%Nk1=kkp+04oS3F,2kP7p+06CS3G,2lP7%N\1=\\Q2H/00PYQ2z/00PYp+04kS3H/00PYp+06KS3I/\0P7Q3<,?Wp+05YS3JfCS3KQ3<'?p+05ZS3Lp+06NS3M/\0P7PXPXPXp+061S3NPPPPPlQ2]p+06LS3OQ2\M:jPXQ37O1/=\p+06PS3P/\WP7PXPXPXp+063S3QQ2<Q2<Pkp+05;S3RQ3Mp+04SS3SM:jPXP\O1/=lp+06RS3TQ3K'\P7PXPXPXp+065S3UPNPNQ28Q2aQ3PQ2>M:jPXPlO1/=kQ23Q03'0PYfES3Vp+06QS3W'0PYQ3VQ3T'0PYQ2:Q2k'0PYQ2:Q3B'0PYQ2;/0JPYQ2:p+06VS3X'0PYQ2:p+06WS3Y'0PYQ2<p+05NS3Z'0PYQ2<p+05OS3['0PYQ34/0UPYQ2<p+06[S3\'0PYQ2<p+06\S3]'0PYQ02p+05SS3^'0PYQ02Q2x'0PYQ1WQ0@'0PYQ09Q1>'0PYQ1DQ0B'0PYQ1V,0UPYp+02IS3_Q0C'0PYQ1B,0UPYQ1IQ1b'0PYQ0:Q1`'0PYQ1:/0TPYQ0:Q1a'0PYQ1</0ZPYQ0;Q1J'0PYQ1<Q07'0PYQ0Dp+02fS3`'0PYQ1g/0MPYQ1bp+02hS3a'0PYQ1>Q2Q'0PYQ1bp+02jS3b'0PYQ1@Q0H'0PYQ1p,0TPYQ1BQ0v'0PYp+02nS3c,0TPYQ1TQ0_'0PYQ05p+030S3d'0PYQ1TQ0d'0PYQ0Gp+031S3e'0PYQ1`/0QPYQ0Hp+033S3f'0PYQ1UQ0L'0PYQ0HQ1j'0PYQ1JQ17'0PYQ0vQ1m'0PYQ1eQ0N'0PYQ0vQ1o'0PYQ1PQ0K'0PYQ19Q1r'0PYQ1PQ0J'0PYQ18Q1s'0PYQ1NQ0W'0PYQ17Q1t'0PYp+02dS3gQ0q'0PYQ17Q1^'0PYQ1XQ0V'0PYQ0NQ2L'0PYQ3aQ0P'0PYQ0NQ2?'0PYQ1YQ0U'0PYQ0IQ2S'0PYQ1YQ32'0PYQ0OQ2A'0PYQ3bQ0T'0PYQ0VQ2i'0PYp+02mS3hQ0l'0PYQ0Vp+03KS3i'0PYQ3cQ0`'0PYQ0PQ2E'0PYQ3eQ0a'0PYQ0Pp+03OS3j'0PYp+032S3kQ0Y'0PYQ2{Q1z'0PYQ3kQ0X'0PYQ13Q1|'0PYQ3f/05PYQ0`Q20'0PYQ1l/0@PYQ0`/0hPYQ1mQ0g'0PYQ0a/0iPYQ1qQ1?'0PYQ0a/0jPYQ1rp+01aS3l'0PYp+01TS3mp+03\'0PYQ1rQ0h'0PYp+03]S3n,0bPYQ1sQ0n'0PYQ0gp+03_S3o'0PYQ1]Q0c'0PYQ0gQ2Y'0PYQ1^Q1C'0PYQ1?/0RPYQ2MQ0j'0PYQ1?Q2^'0PYQ2?Q1\'0PYQ0]p+03gS3p'0PYQ2?Q1O'0PYQ0ep+03hS3q'0PYQ2PQ0o'0PYQ1Cp+03jS3r'0PYQ2UQ0x'0PYQ1CQ1u'0PYQ2iQ0u'0PYQ0jp+03nS3s'0PYp+03LS3tQ0p'0PYQ0jp+040S3u'0PYQ2EQ0s'0PYQ1Gp+042S3v'0PYQ2EQ0y'0PYp+025S3wp+043S3x'0PYp+03NS3yQ10'0PYQ0uQ2l'0PYQ1zQ1A'0PYQ0uQ1v'0PYQ1|Q12'0PYQ0pQ2p'0PYQ15,0gPYQ0pp+04;S3z'0PYQ1W,0hPYQ0{Q2t'0PYp+07\S3{Q1WQ0o31PYp+07]S3|Q1WQ0o31PYQ0op+07;S3}'2P7Q1Rp+07<S3~'2P7Q1Op+07=S40'2P7PXp+087Q1Wp+02DS41Q3wp+07FRhPhp+06GS42G3Q1\Q1G+0FPXp+088Q15Q12Q0xp+07GRgPgp+06HS43G3Q0eQ0c+0FPXp+089RRQ11Q1AQ0op+07HRbPbp+06IS44G3Q0hQ0^+0FQ3wQ1g'=PYQ0{Q1='=PYQ0wQ1@'=PYQ2dQ0|'0PYp+07MS45,0FPYQ2}Q0|'0PYp+07OS46,0<PYQ30Q0|'0PYQ28p+07QS47'0PYQ1lQ12'0PYQ1mQ11'0PYQ1nQ1A'0PYQ1mQ1W'0PYQ1nQ41'0PYQ1oQ15'0PYQ1nQ16'0PYQ1oQ14'0PYQ1qQ1D'0PYQ1oQ1M'0PYQ1qQ1I'0PYQ1rQ3_'0PYQ1qQ1<'0PYQ1rQ1:'0PYQ1sQ1Z'0PYQ1rQ1='0PYQ1sQ1h'0PYQ1dQ1g'0PYQ1sQ1V'0PYQ1dQ1@'0PYQ1tQ1>'0PYQ1dQ1T'0PYQ1tQ1B'0PYQ1]Q1_'0PYQ1tQ1a'0PYQ1]Q1F'0PYQ1^Q1`'0PYp+08HS48p+08cp+08IS49p+08AS4:P1Ccp+07ES4;p+08JS4<p+095S4=/k1p+08DS4>Q3>Q4>;X:p+08LS4?,@Kp+08MS4@/`9Q4@?199p+08GRj/s9p+07WS4Ap+08iRip+08OS4BPjPBCcp+07KS4CQ4?,:8p+08PS4Dp+09CS4E00`4PAp+08RS4FQ3B71:PYp+09=S4G00_EQ4G91A:p+08TS4Hp+09?S4I/k1p+08NS4Jp+09@S4KQ28/r:'kQ4BQ4D/s:p+07`S4LQ3>Q1]<0K:p+08XS4MQ4M[Q4>=XkBp+08YS4N,@Kp+094S4Op+08ZS4Pp+08ES4QP4Ccp+07VS4RQ4=p+08[S4Sp+08FS4TQ35/r3CcQ4Ap+09NS4U00`4PAQ2M>0KB0p+08]S4VQ4V[Q49Q3K/rF5XBp+08^S4W,@Kp+08WS4X,:4p+08_S4Yp+08KS4Z,:3p+08`Q2uQ2U60]<Q2u00mEp+07lS4[p+09LS4\5GFp+07kS4]p+09MS4^1rP\+0_Q4^91A3Q28Q3RQ4U3Gp+07mS4_p+09OS4`9GkCp+07nS4ap+09PS4b9GlCp+07oS4cp+09QR@9G\Cp+080R5Q37p+09RR^7GCp+081RmQ35p+09SS4d7GCp+082Rnp+09TRo9G0Cp+083Rpp+09URq9GWCp+084RrQ3Kp+09VRs7GCp+085RCQ37Q1|<0KJp+08mS4eQ4e[Q37p+08fRt;XUp+08nS4f,@KQ3VQ4PQ37/r\3Xp+08oS4g,@Kp+090S4hQ35;1UPYp+091S4iQ35;1`PYQ3KQ4f':p+092S4jQ27Q4W':p+093S4kQ3Vp+08lS4l':Q4OQ29Q4j':Q4=p+08@S4mp+09`S4n5GPp+08?S4oQ2<Q3Zp+09aS4p3GQ4mp+05WS4qp+09bS4r5GNQ4:Q02Q4qp+09cS4s3Gp+08BRuQ4qp+09dS4t5G`p+08CS4uQ03Q4qp+09eS4v3GQ4>Q04Q4qp+09fS4w3GQ4QQ2BQ4qp+09gS4x3GQ4TQ0rQ4qp+09hS4y3GPjQ4qp+09iS4z5GJQ48Q4Kp+068S4{71lPYp+09AS4|Q06Q0@'r71lPYp+09BS4}Q0[71lPYQ09p+09;S4~p+06iS50,?l3XQ4E,@Kp+09DS51Q3A71\PYQ29Q4K':p+09ES52PuQ0>PuQ0?PuQ06PuDwp+06AS53Q4}g01[U,`GRvE[P4eP4Q4uQ0?Q4uQ0@Q4uQ0[Q4uDwp+06BS54Q4IPvE[PBePBp+09HRwp+06?S55719PYp+09IS56p+0:4S57/k1Q4EQ51/s1Q4HQ4wQ4\p+097S58P9CcQ48Q4xQ4^Q58P8CcQ49Q4XQ4M?118W>Q4XPY]>Q4MQ4N?11BW>Q4MPY]>Q4~=XJ3Q4b,@KQ4~=X1D1@K@Q4b,::P^Q4dp+06MS59711PYQ4I,:9PoQ4I,:8Pq1:BoPsp+09WS5:?19lPYp+09XRx?19\PYp+09YRyp+06SS5;719PYp+09ZS5<p+0:ES5=/k1Pop+09\S5>/`:Q5>?1::1ss:Ptp+0:8S5?p+09^S5@PqP8CcQ4Pp+08hRtA1i19W>PY^>tQ5:=X\4Q4n,@Kp+09_S5A,:1Q4pQ4rQ3]711PYQ4sp+0:NRt/k1p+09]S5BQ5@/s1Q4fp+0:@S5CQ4wQ4sP9Ccp+08bS5DQ4hQ4i?119W>Q4hPY]>Q4v=XDBQ4y,@KQ4x,:1Q4zp+09jS5Ep+06dS5F711PYp+09kS5Gp+0:VS5H/k1Q4vQ4w/s1p+096S5Ip+0:HRip+09nS5JQ5EP9Ccp+08jp+098S5Kp+099S5L?119W>Q5KPY]>p+09lS5M=XDBp+0:0S5N,@Kp+09oS5O,:1p+0:1S5Pp+0:2S5Qp+06lS5R711PYp+0:3S5Sp+0:^S5T/k1p+09mS5UQ5J/s1p+09>S5Vp+0:PS5Wp+0:6S5XQ5MP9CcQ4jQ4KQ4|?119W>Q4KPY]>Q5J=XDBQ5?,@Kp+0:7S5Y,:1p+0:9S5Zp+0::S5[p+074S5\711PYp+0:;S5]p+0:fS5^/k1p+0:5S5_Q5X/s1p+09FS5`p+0:XS5ap+0:>S5bQ5SP9Ccp+09:S5cQ56?119X>wPY^>wQ5_=XDBQ5C,@Kp+0:?S5d,:1p+0:ARzp+0:BR{Q3~711PYp+0:CS5ep+0:nS5f/k1p+0:=S5gQ5b/s1Q4Up+0:`S5hp+0:FS5iQ5[P9CcQ4}Q4bA1@19W>Q4bPY]>p+0:<S5j=XDB1@Kip+0:GS5k,:1p+0:IS5lp+0:JS5mp+07DS5n711PYp+0:KS5op+0;6S5p/k1Q5=Q5i/s1Psp+0:hS5qPtQ5lP9Ccp+09JS5rA1y19X>xPY^>xQ5o=XDBQ5W,@Kp+0:OS5s,:1p+0:QS5tp+0:RS5up+07LS5v711PYp+0:SS5wp+0;>S5x/k1p+0:MS5y1st1Q5@p+0;0S5zQ5HQ5lP9CcP^Q4nQ4p?119W>Q4nPY]>Pop+0;2S5{Q5aQ5Hp+06nS5|CcPoP:PoPFPoP0PoQ2<PoPJPoQ0=PoQ1bPoQ0\PoQ0NPoQ0IPoQ10PoQ1\PoQ1KQ0s>00ooD<D<D<D<D<D<D<&0Jop+0:LS5}=XE4p+0:YR|,@KQ5ap+070S5~5X1p+0:ZS60,@K1::|p+0:[S61PcP:Q0zQ1?p+07IS62D;Pdp+0:US63,:9p+0:]S64p+0:\S65,:8Q5TQ5H,:Bp+0:_RdQ64,:4Q5hQ64,:3p+0:aS66Q5a,:Dp+0:bS67Q5a,:Ep+0:cS68Q5a,:Fp+0:dS69Q5h,:<p+0:eS6:Q28/:|Q5^1:k|p+0:gS6;1:l|Q5q1:\|p+0:iS6<Q37/:|p+0:jS6=Q35/:|p+0:kS6>1:0|p+0:lS6?1:W|p+0:mS6@Q27Q6?Q4m,?W3XQ5f,@Kp+0:oS6AQ3Kp+07iS6B31PYQ5zQ1`71WPYp+0;1S6C?1WgPYQ5{Q2{71WPYp+0;3S6D?1W[PYp+0;4S6EQ1871WPYp+0;5S6FQ0z71WPYQ5p?1WMPYp+0;7S6GQ0571WPYp+0;8S6HQ0@71WPYp+0;9S6I?1WUPYp+0;:RM?1W5PYp+0;;S6J?1W5PYp+0;<S6K?1W5PYp+0;=S6L?1W5PYQ5x?1W5PYp+0;?S6M?1W5PYp+0;@S6N?1W5PYp+0;AS6OPcQ1VPMP1Q5MQ1WQ4cPUL03W4Q6OPY]41U9:PYQ0>p+08>S6PPMPvCRQ35eQ351U4:PY1UD1PY1UF1PYQ28/U1PY1Ul1PYQ37/U1PY1U01PYQ3K/U1PYQ3V/U1PYQ2:/U1PYQ2</U1PYQ02/U1PYQ03/U1PYQ2B/U1PYp+0;RS6QQ4?;1np+0;SS6RQ4?Q1r31p+0;TS6SQ4?Q3C31p+0;US6TQ4?;1dp+0;PS6UQ4:'0p+0<DS6V,0uPOP_P?PSP]Q5?P=P]PIQ5[EVP>PHb5b6b7X17Q6R/01p+0<<S6W,F:#v[^17P1Q4>P9O2b0PoQ4dQ4dP^POP_P?PSP]Q5fP=P]Q5jQ6MEfP>PHb5b6b7X17p+0<HS6X,01p+0<>S6Y,F:Q6O'^[^17P1Q4TP8O2b0b2b35>R1=hRPOP_P?PSP]Q5ZP=P]PIQ5OEVP>PHb5b6b7X17Q6S/01p+0<KS6Z,F:#v[^17P1Q4QP8O2b0PqPoPoQ4dPOP_P?PSP]Q6AP=P]Q5PQ6NEfP>PHb5b6b7X17p+0<IS6[,01p+0<MS6\,F:p+0;BS6]'^[^17P1PjPBO2b0b2b35>up+07CS6^/=uPOP_P?PSP]Q5[P=Q6@9p]IRRH0GP>PHb5b6b7X17Q6T/01p+0<ES6_,F:#vRd[^17P1Q4TPBO2b0PsPqPqPoPOP_P?PSP]Q5zP=P]Q6AQ6OEfP>PHb5b6b7X17p+0<JS6`,01p+0<GS6a,F:R}p+0;CS6b'^[^17P1Q48P4O2b0b2b35>up+07@R~/=uPOP_P?PSP]Q5]P=PRH0GP>PHb5b6b7X17p+0;VS6c/01Pd[^17P1PjP4O2b0Q5:PsPsPqPOP_P?PSP]Q6CP=P]Q6AQ6]EfP>PHb5b6b7X17Q6Z,01p+0;DS6d,^}[^17P1Q49P3O2b0b2b35>uQ40/=uPOP_P?PSP]Q5jP=P]PIQ5UEVP>PHb5b6b7X17p+0;WS6e/01Pd[^17P1Q48P3O2b0PxQ5:Q5:PsPOP_P?PSP]Q5{P=P]Q5OQ6bEfP>PHb5b6b7X17p+0<LS6f,01p+0;ES6g,^}[^17P1Q4<PDO2b0b2b35>up+07:S6h/=uPOP_P?PSP]Q5gP=P]PIQ5GEVP>PHb5b6b7X17p+0;XS6i/01Pd[^17P1Q49PDO2b0PyPxPxQ5:POP_P?PSP]Q6DP=P]Q5UQ6dEfP>PHb5b6b7X17Q6\,01p+0;FS6j,^}[^17P1Q4ZPEO2b0b2b35>up+077S6k/=uPOP_P?PSP]Q5bP=P]PIQ4zEVP>PHb5b6b7X17p+0;YS6l/01Pd[^17P1Q4<PEO2b0Q5<PyPyPxPOP_P?PSP]Q6EP=P]Q5GQ6gEfP>PHb5b6b7X17p+0<NS6m,01p+0;GRR,^}[^17P1Q4?PFO2b0b2b35>uQ5\/=uPOP_P?PSP]Q5dP=P]PIQ4yEVP>PHb5b6b7X17p+0;ZS6n/01Pd[^17P1Q4ZPFO2b0p+09[S6oQ5<Q5<PyPOP_P?PSP]Q6FP=P]Q5EQ6jEfP>PHb5b6b7X17p+0<OS6p,01p+0;HS6q,^}[^17P1Q4@P<O2b0b2b35>up+071S6r/=uPOP_P?PSP]Q5CP=P]PIQ4wEVP>PHb5b6b7X17p+0;[S6s/01Pd[^17P1Q4?P<O2b0Q5>Q6oQ6oQ5<POP_P?PSP]Q5pP=P]Q4yPREfP>PHb5b6b7X17p+0<PS6t,01p+0;IRd,^}[^17P1Q4JQ28O2b0b2b35>uQ5|/=uPuQ5lp+086RIQ6j'0Q6j,0CPXp+0<7S6uPIPCQ45Q6jQ6jQ5kG3Q5BQ5>Q5>Q6oPOP_P?PSP]Q6GP=P]Q5=Q6OQ6qK01P>PHb5b6b7X17p+0<QS6v,01p+0<US6wp+0;JS6x5A}[^17P1Q4BPkO2b0b2b3Q46PEG4p+06XR}eP}Q4ZQ5m10rR10pRPXp+0<8S6yPrPpp+07JS6zPRPRPiG3Q5@Q5BQ5BQ5>POP_P?PSP]Q6HP=P]Q5[Q6]PdK01P>PHb5b6b7X17p+0<RS6{,01p+0<VS6|,F:Q6|p+0;KRp3A[^17P1Q4DPlO2b0b2b3Q5vPEG4P}eP}Q4ZQ5oQ6q,0nQ6q,0mPXp+0<9S6}PnPmPgQ6qQ6qQ5lG3Q5AQ5@Q5@Q5BPOP_P?PSP]Q6IP=P]Q6HQ6bQ6xK01P>PHb5b6b7X17p+0<SS6~,01Q6t,F:S70p+0<WS71p+0;LRm3A[^17P1p+08QS72P\O2b0b2b3Q62PEG4P}eP}Q4ZQ5}105dQ4c/0dPXp+0<:S73P5Q4cQ5nPdPdQ5mG3Q4nQ5AQ5AQ5@POP_P?PSP]PMP=P]Q6HQ6dPpK01P>PHb5b6b7X17p+0<TS74,01Q70p+0<XS75p+0;MRn3A[^17P1Q4FQ37O2b0b2b3PhPEG4P}eP}Q4ZQ5yQ4aQ6x'0Q4_Q6x'0PXp+0<;S76Q4aQ4_p+07ARrQ6xQ6xQ5oG3Q4pQ4nQ4nQ5APOP_P?PSP]Q6JP=P]Q5?Q6gPmK01P>PHb5b6b7X17Q6w,01Q70p+0<YS77p+0;NRC3A[^17P1p+08SS78Q35O2b0b2b3Q6^PEG4P}eP}Q4ZPtQ4[/0pQ4]/0pPXQ6WQ4[Q4]p+07>S79PpPpQ5}G3Q4rQ4pQ4pQ4nPOP_P?PSP]Q6KP=P]Q5XQ6jPnK01P>PHb5b6b7X17Q6|,01Q70p+0<ZS7:p+0;OS7;3A[^17P1Q4HP0O2b0b2b3P~PEG4P}eP}Q4ZQ5sp+07jS7</0mQ6B/0mPXp+0<=S7=Q7<Q6BQ3}PmPmQ5yG3Q4sQ4rQ4rQ4pPOP_P?PSP]Q6LP=P]Q57PRPCK01P>PHb5b6b7X17Q71,01Q70p+0<[RIQ6U3A[^17P1p+08US7>PWO2b0b2b3Q40PEG4P}eP}Q4ZQ5Wp+07hS7?/0np+07gS7@/0nPXQ6YQ7?Q7@p+078S7@PnPnPtG3Q4tQ4sQ4sQ4rPOP_P?PSP]Q5xP=P]Q5SQ6qQ7;K01P>PHb5b6b7X17Q75,01Q70p+0<\Rtp+0;QS7?3A[^17P1p+08VS7AQ3KO2b0b2b3Q6hPEG4P}eP}Q4ZQ5tp+07fS7B/0Cp+07eS7C/0CPXp+0<?S7DQ7BQ7Cp+075S7CPCPCQ5sG3Q4vQ4tQ4tQ4sPOP_P?PSP]Q6MP=P]Q5PPdQ6UK01P>PHb5b6b7X17Q77,01Q70p+0<]S7BQ6Q3A[^17P1Q4XQ27O2b0b2b3Q6kPEG4P}eP}Q6|/0}p+06YS4XQ6|Q7:3AQ4XQ5LQ6xP1Q3\P9O2b0Q4yQ4xQ4xQ4wQ5cQ6:P1p+06]S70P8O2b0b2b33>Q2IQ4XQ5KQ6gP1Q3]P8O2b0Q4zQ4yQ4yQ4xQ5LQ5hP1p+06^S7EPBO2b0b2b33>p+048S7FQ4XQ58Q6dP1Q70PBO2b0Q5EQ4zQ4zQ4yQ5KQ64P1p+06_S7GP4O2b0b2b33>p+04:S7HQ3]p+09<S7IPnP1Q7EP4O2b0Q5GQ5EQ5EQ4zQ4GQ5qP1p+06`S7JP3O2b0b2b33>Q2pQ3]Q4~Q6qP1Q7GP3O2b0Q5MQ5GQ5GQ5EQ7IQ68P1p+06aS7KPDO2b0b2b33>Q3zQ3]Q5cPRP1Q7JPDO2b0Q5UQ5MQ5MQ5GQ4~Q5hP1p+06bS7LPEO2b0b2b33>Q2tQ7GQ4IQ6UP1Q7KPEO2b0Q5JQ5UQ5UQ5MQ4KQ6>P1p+06cS7MPFO2b0b2b33>p+04<S7NQ7GQ5VPpP1Q7LPFO2b0Q5OQ5JQ5JQ5UQ4IQ5^P1Q5FP<O2b0b2b33>p+04>S4IQ7GQ4GQ6xP1Q7MP<O2b0Q5NQ5OQ5OQ5JQ5VQ68P1p+06eR<Q28O2b0b2b33>p+04@S4GQ7LQ4}Q6RP1Q5FQ28O2b0Q5PQ5NQ5NQ5OQ4EQ5fP1p+06fS5fPkO2b0b2b33>p+04?S28Q7LQ4|PCP1P<PkO2b0Q5QQ5PQ5PQ5NQ4}Q6<P1p+06gS4}PlO2b0b2b33>Q2WQ7LQ4KPnP1Q5fPlO2b0Q5SQ5QQ5QQ5PQ4|Q5^P1p+06hS4|P\O2b0b2b33>Q1wQ52Q6cP1Q4}P\O2b0Q57Q5SQ5SQ5QQ5`Q6CP1Q50Q37O2b0b2b35><p+04BS4KQ51Q7?P1Q4|Q37O2b0Q5_Q57Q57Q5SQ52Q6?P1p+06jS37Q35O2b0b2b35><Q1yQ4EQ6UP1Q50Q35O2b0Q5XQ5_Q5_Q57Q51Q6<P1p+06kS51P0O2b0b2b35><PfQ4|PwQ6lP1Q37P0O2b0Q5YQ5XQ5XQ5_Q56Q6EP1Q5RPWO2b0b2b33>Q1{Q4|p+09GS4EQ6SP1Q51PWO2b0Q5?Q5YQ5YQ5XPwQ6AP1p+06mS7OQ3KO2b0b2b33>Q1~Q4|Q5`Q6RP1Q5RQ3KO2b0Q5ZQ5?Q5?Q5YQ4EQ6?P1Q5|Q27O2b0b2b33>Q22Q51p+09KS3Kp+0;\S7PP1Q7OQ27O2b0Q5[Q5ZQ5ZQ5?Q4\Q6GP1p+06oS27Q3VO2b0b2b33>Q21Q51Q5rQ6eP1Q5|Q3VO2b0Q5]Q5[Q5[Q5ZQ3KQ5{P1Q5~Q29O2b0b2b33>Q23Q51Q56Q6cP1Q27Q29O2b0Q5jQ5]Q5]Q5[Q5rQ6AP1Q6rQ2:O2b0b2b33>Q25Q5|Q4Up+0;_S6AP1Q5~Q2:O2b0Q5gQ5jQ5jQ5]Q4`PMP1p+072S2:PPO2b0b2b33>Q24Q5|Q4^Q6nP1Q6rPPO2b0Q5bQ5gQ5gQ5jQ4UQ6FP1p+073S29Q2<O2b0b2b33>Q26Q5|Q4\Q6lP1Q2:Q2<O2b0Q5dQ5bQ5bQ5gQ4^Q5{P1Q5\PNO2b0b2b33>Q2;Q6rP@p+0;bS2<P1Q29PNO2b0Q5CQ5dQ5dQ5bP^Q6LP1Q7CQ02O2b0b2b33>Q2~Q6rQ4bp+0;]RPP1Q5\Q02O2b0PzQ5CQ5CQ5dP@Q6HP1p+076S02P`O2b0b2b33>Q31Q6rQ4`Q7PP1Q7CP`O2b0P{PzPzQ5CQ4bQ6FP1Q6kQ03O2b0b2b33>Q2=Q5\Pop+0;eS3VP1Q02Q03O2b0Q5eP{P{PzPqQ6NP1Q7@Q04O2b0b2b33>Q2\Q5\Q4dp+0;`R`P1Q6kQ04O2b0p+0:DS04Q5eQ5eP{PoQ6JP1p+079S6NQ2BO2b0b2b33>Q3SQ5\P^Q6AP1Q7@Q2BO2b0Q5=Q04Q04Q5eQ4dQ6HP1Q6hQ0rO2b0b2b33>Q2>Q6kQ5:p+0;hS2BP1Q6NQ0rO2b0Q5iQ5=Q5=Q04PxQ6bP1Q3}PJO2b0b2b33>Q34Q6kPsp+0;cS0rP1Q6hPJO2b0Q5kQ5iQ5iQ5=Q5:Q5xP1Q3~PaO2b0b2b33>p+04VQ6kPqQ2<P1Q3}PaO2b0PiQ5kQ5kQ5iPsQ6JP1Q40Q08O2b0b2b33>Q2@Q1Q$0lQ6eQ1N71jQ6iQ1a71jQ6lQ1@71jQ6nQ1Z71jQ6sQ1W71jQ7PQ0}71jQ0p91Pjp+0;^S2@Q1S71jQ6AQ1r71jQ52Q1s51`p+0;aS52Q4EPrp+0=BS03Q7HDgQ2<PwPrp+0=CS7QQ3vDgQ7:,@KS7RQ7RQ4EPcP1Q3ep+03^S7SPwD;+0\PIP1Q6~Q1wPIP1Q77Q4iPIP1Q6{Q3ePIP1Q75Q3aPIP1Q71Q1PPIP1Q6vQ1`PIP1Q6tQ1hPIP1Q6pQ16PIP1Q6|Q1APIP1Q6mQ0{PIP1Q6\P@PIP1Q6fQ4bPIP1Q6ZQ4`PIP1Q6`Q4UPIP1Q6[Q4^PIP1Q6XQ4\PIP1Q6aQ3KH0kDaDaDaDaDaDaDaDaDaDaDaDaDaDaDaDaS7T'UWDQ1SQ5`Q1K+0\Q1;Q18'UQ5`PcPG1@KIQ52PqQ4In0100000020000P|Q56Q4ED;Q1KQ5EPcP2PqQ2<Q56Q4Eg05SbQ6{Q6|Q6AQ28Q4Gg05TlPvg05V6Q7:Q5nQ7:p+0;dS7UQ5rP1p+0=<S7Vp+0=ES7WQ2tEPW4PbPIQ5np+0=NS7XP1Q7VD~X97Q7:Q6^'`Q2:PbQ4zp+0<AS7YP1Q62Q0DO2b0Q5HQ63Q63p+0:TS63Q5EQ7PP1Q4CQ1bO2b0b2b3FeQ2deQ2dPIQ5nQ3VQ3KP1p+0=FS7ZQ4IDgX4IP9Q2:P1EDb<P^Q0FE5Q4G#qMAnQ76p+0=6S7[P1Q7XQ6nQ60Q7[#NQ7XQ6nQ7XQ60CTdO4b<Q7:p+0=MS7\p+0=5S7]P;Q7\Q7]'YdP|DWPIQ6nPcQ4GP1Q3KQ56Q1SEQX4IPcQ28Q6nQ5rPwD;PcPG1@KtQ6lQ28Q3vn0100000020000Q5uQ5rPwD;Q0kQ5GPcP2Q28Q6nQ5rPwg05W@p+0<FS0kQ71Q6iQ2IQ1vg05XJPvg05YTQ6eQ7NQ6e$0DPsQ71PvE[Q2peQ2pPtPop+0;fS7^Q4\P1Q5wp+0=GS7_Q2IEPX4tPtPhQ7^Q4\P1p+0==S7`Q7_Q2IEPX4tQ6zQ7BQ4;p+0=PRPP1Q7`D~X97Q5n,`tQ5\Q6zQ5Gp+0<CS7aP1Q4CPTO2b0Q5ap+0:WRaPaQ5HQ5MQ2@P1Q45Q05O2b0b2b3FeQ3FeQ3FQ7BQ4;Q7Bp+0;gS5aQ4^P1p+0=HS7bQ1vDgW4P8Q29P1EDb<PoQ0LE5Q7NP1E5b=Q1v#qMAnQ6Wp+0=7S7cP1p+0=OS7dQ6eQ5wQ7]#NS7eQ7dQ6eQ7dQ5wCTdO4b<PIQ7Xp+0=4S7fP;Q7XQ7f'YdQ5uDWPtQ6ePcp+044RaP1Q4\Q5rQ1OEQX4tPcQ3xQ6eQ3KQ56D;PcPGQ7B,@KQ6nQ3xQ3nn0100000020000Q5tQ3KQ56D;Q1SQ5MPcP2Q3xQ6eQ3KQ56g05Z^RJQ6aQ74Q6ag05[h&0YJ,`Gg05]2N=1HQ7=p+0=8RJP1PPQ6eQ5uQ7ePPQ6ePPQ5uCTdO4b<PtQ7dQ7fP;Q7dQ7f'YdQ5tDWQ7BQ6eQ7BPcQ3oP1Q4^Q3KQ1REQW4Q6lQ3xQ6lQ4IQ6l400PxQ6wPvE[Q3neQ3np+0<^S1SQ1yQ1SPcQ2IQ6`p+03oS7g,r1Q6lQ4UQ4\Q0oL03W4Q6nPaQ6nQ28Q6n400PyQ6[PvE[Q3neQ3np+0<_S7hQ3zQ7hPcQ1vQ6Z1rf1Q6nQ4`Q4^Q0xL03W4PcPeQ6lQ4UQ4\D;PcPeQ5wQ1vQ4\D;Q0oQ5OPcP2PeQ6lQ4UQ4\g05^<PIQ6`Q6iPhQ1{Q3z'rg05_FPvg05`PQ2iQ3jp+0<`RWPxp+0<aR0p+0=@S6lQ6n'm,?1;1bX4WPWQ6zQ7b,?1Rl=10bX4Wp+07NS7ip+0=TRkQ7b,21RF'O=10bX971`WgQ7@Q7iQ5OQ6aP1Q46Q06O2S7jb0Q65Q61Q61Q60Q5NQ2<P1Q47Q0[O2b0b2b3FeQ6zQ7_'?=1WgePxQ0IE5Q7SP1E5b=Q6sPaQ6sQ2lQ6sQ4GQ6sDwQ5<Q6`PvE[Q3yeQ3yPWQ7N,rfREQ1~Q2t'r9101X4WPWPEQ3nP1F]b=Q4UPhp+0=IS6sQ5vQ7DPOP_P?PSP]Q7^P=P]Q6`Q6nEVP>PHb5b6b7X17p+0=LS6n/01Q7\Q7b,2:RE'0[^17P1Q7iQ0ZO2b0Q5\PTDEp+0=KS7kQ5\'0eQ5vQ6TQ6^Q7['0p+07BS7lQ7['0PXQ7]Q6^Q7lQ29Q7[Q7[Q76G3POP_P?PSP]Q0rP=P]Q5wQ6WEVP>PHb5b6b7X17Q7kQ7d5A1p+0=QS7m=AEJ[^17P1Q7iPZO2b0Q5\PTG4Q2qQ7['0eI0VNB0Pp+0<@S7np+0=;S7oP1p+0=SRDQ6SQ63Q7f#NS7pPDQ6SPDQ63CTdO4b<Q7hp+0=RS7qp+0=3R3P;Q7q/Y3dQ5wDWPWQ6SPcQ3xP1Q2pQ4UQ3wEQX4WPcQ3vQ6SQ7FQ4^D;PcQ3vQ5WQ3xQ4^D;Q0xQ5NPcP2Q3vQ6SQ7FQ4^g05aZPtQ75Q6RPhPfg05bdPvg05cnQ1iQ1xP0Pyp+0<bR4Q5t,?1;1bX40P0Q4CA14lbX40Q46p+0=URl/OF=14bX971`0gQ6NQ46Q5NQ6XP1p+07PS0xQ0[O2RFb0Q64Q65Q65Q61Q5PQ0rP1p+07RS0[Q07O2b0b2b3FeQ4CQ7_'?=10gePyQ0KE5Q3oP1E5b=Q2iQ3yP0Q1~Q219141X40Q1yQ3nP1E5b=P2p+0=JS3nQ4`Q7FPhQ7gQ4`PhQ3nQ5vQ7nPOP_P?PSP]Q5aP=P]Q6ZQ6TEVP>PHb5b6b7X17Q7\/01Q7X/0E[^17Q7jb0Q29PTDEQ6nQ29'0eQ5vQ6cQ7c,0rQ7c,0~PXQ7[PrP~Q2:Q7cQ7cQ6WG3POP_P?PSP]Q7UP=P]Q5sQ7=EVP>PHb5b6b7X17Q6n,21S7j/0PQ7qp+0=9S7r5AE[^17P1Q46Q0ZO2b0Q29PTG4Q2qQ7c'0eI0VK0UNB0PQ7YQ7VP1PkQ7?Q5tQ7pPkQ7?PkQ5tCTdO4b<PWPDP3P;1YD3dQ5WDWP0Q7?PcPaP1Q2lQ4`Q0uEQX40PcQ3xQ7?PaQ4UD;PcQ3xQ5}p+03dQ4UD;Q3wQ5PPcP2Q3xQ7?PaQ4Ug05e8Q7BQ77Q6UPhQ1~g05fBPvg05gLQ3iQ1zP4Q5<p+0<cREQ5y,?1;1bX44P4Q5vQ7_,?1=1EbX44Q0xp+0=VS77Q7_80M1=1EbX971`4gQ6hQ0xQ5PQ6[P1Q47Q07O2b0Q5TQ64Q64Q65Q5QQ7UP1p+07SS65Q0\O2b0b2b3FeQ5vQ7Z'?=14geQ5<Q1EE5p+03`S0\P1E5b=Q1iQ3jP4Q21Q2291E1X44Q1{Q7SP1E5b=P2Q7kQ2pPaPhQ2p>0]fgP2Q7kQ4bQ2pPhQ3uQ4bPhQ7kQ5vQ7YPOP_P?PSP]Q2BP=P]Q6fQ6QEVP>PHb5b6b7X17Q7X/01Q7dQ7_,2:S7Y'0[^17PFb0Q2:PTDEQ7\Q2:'0eQ5vQ6ep+07?RF/0JQ79/0JPXQ7cPFQ79Q6rPJPJQ7=G3POP_P?PSP]Q3VP=P]Q5oQ6YEVP>PHb5b6b7X17Q7\,21S6YQ7m'0Q7Yp+0=:7AD[^17P1Q0xQ06O2b0Q2:PTG4Q2q/0JeI0VK0UK0UNB0Pp+0<BS7YQ7`P1PlPCQ5yQ7pPlPCPlQ5yCTdO4b<P0PkP3P;1Yk3dQ5}DWP4PCPcQ2lP1p+03fRJQ4bQ0pEQX44PcPaPCQ2^Q4`D;PcPG1@KEp+0;iS0pPaQ3jn0100000020000Q5kQ2^Q4`D;Q0uQ5QPcP2PaPCQ2^Q4`g05hVS2^Q7:Q7hPng05i`Q2^$0Y,`Gg05jjN=0iQ7ap+0=>S7aP1Q77PnPiQ7pQ77PnQ77PiCTdO4b<P4PlP3P;1Yl3dQ5kDWPEPnPcQ1zP1Q3pP@Q0{EQX4EQ6AQ7FQ6AQ2pQ6AQ1yQ6ADwQ5@PWPvE[Q3jeQ3jp+0<dS6AQ5BQ6APcQ1vQ7BQ5o,?1Q7;Q3qP^Q0sL03W4Q6AQ5BQ0aQ6AQ25Q0aPcPJPCQ3pP@D;PcPGp+0<eR4,@KQ2<PJQ2?n0100000020000PiQ3pP@D;Q0{Q57PcP2PJPCQ3pP@g05l4Q6pQ7hQ7;Q1iQ3ig05m>Pvg05nHP`Q24P`Q2pP`Q7HQ1{>00``D<Q5AQ7hPvE[Q3teQ3tP4Q5>p+0;oR`Q2bP1Q5}PPQ3iEPX44P4P`P`Q2bP1P6PPQ3iEPX44Q0kp+0=AS7hP1p+0=YRJp+0<0S3pQ5lQ76Q5l:1GiJdO4b<A14`ip+0<fS7BQ3pQ7BQ3pQ3rP1Q7mQ3tDgW4P`Q0\Q2UP`PaQ2UP`PoQ2UP\PaQ4GPqQ45Q3pPPPPQ2}Q3~/2LS2^Q5l37X8APlQ6V,21S6VQ3~Q2]/01S7:3IX97Q65Q5kQ7CQ5\'6Q29,6rQ7CQ5\PrQ29PXQ7VQ7;Q73Q5iQ65Q65PbG3PXQ7VQ6zQ62Q6hPlPlQ76G3EKPOP_P?PSP]p+0;kS0uP=P]20h]8S7SQ61Q6\5p]J0IP>PHb5b6b7X17X:Y121DS61p+0=WS64'0R\P912:PPJp+0=XR`CH[^17^:YP1Q7lp+07US5TQ2QO3b0Q3}Q06G4PiQ5MDEQ3FQ2`;7ieQ7HQ3xD8Q4rPPQ2^Q6f'0X8AQ65PCQ2:Q6rQ2XQ67Q66Q66Q5hQ4xPnP1Q4AQ0HO2S0Hb0b2b3Q3}Q06G4Q2deQ7HQ3xD8GJE5Q0\Q24Q4IQ5vQ3pPPPPQ2dQ6h/2LS06Q5l37X8APlQ6VQ6hQ2`/01S073IX97Q0[Q5kQ5~Q27'6Q5|,6~Q5~Q27P~Q5|PXQ7VQ7;Q73Q5iQ0[Q0[Q4;G3PXQ7VPgPhQ7@PlPlQ76G3EKPOP_P?PSP]Q0uP=P]Q7SQ5HQ6\5p]J0IP>PHb5b6b7X17X:YP9Q7d,2:PJP`CH\\^17^:YP1PrQ5TQ2QO3b0Q6NQ0ZG4PiQ5MDEQ2mQ2j;7ieQ1{Q1wD8Q4rPPQ06Q6f'0X8AQ0[PCQ7OQ5RQ2[Q67Q66Q66Q5hQ4wPmQ0Hb0b2b3Q6NQ0ZG4Q2|eQ1{Q1wD8GJE5Q2bQ3pPPQ24Q2pQ4CQ3pPPPPQ2|Q7@/2LS0ZQ5l37X8APlQ6VQ7@Q2j/013IX97Q47Q5kQ51Q37'6Q50,6FQ51Q37PFQ50PXQ7VQ7;Q73Q5iQ47Q47Q7lG3PXQ7VQ5nQ6^Q02PlPlQ76G3EKPOP_P?PSP]Q0uP=P]Q7SQ5tQ6\5p]J0IP>PHb5b6b7X17X:YP9Q7\,2:PJP`CH\\^17^:YP1P~Q5TQ2QO3b0Q6kPZG4PiQ5MDEQ3HQ33;7ieQ1{Q1wD8Q4rPPQ0ZQ6f'0X8AQ47PCQ4|Q4}Q2VQ67Q66Q66Q5hQ4vPpQ0Hb0b2b3Q6kPZG4Q2zeQ1{Q1wD8GJGxQ5lP1EDb<Q5>P[E5Q1xP1E5b=Q3i#qMAnQ6_Q6lP1P`PRQ5lQ7eP`PRP`Q5lCTdO4b<Q6AQ64Q7fP;Q64Q7f'YdPiDWP4PRPcQ2SP1Q2bQ4dp+02:S6AEQX44PcQ2PPRQ3qP^D;PcPGQ7B,@KQ6pQ6m5oKQ2PQ2?n0100000020000Q04Q3qP^D;Q0sQ5_PcP2Q2PPRQ3qP^g05oRQ6pPEQ6iQ3iQ3tg060\Pvg061fQ52Q2iQ52Q25Q52Q7HQ52Q3zQ52PfQ52DwD<Q4nPEPvE[Q2LeQ2LQ7BQ4nQ7BQ3pQ3rP1Q5HQ7mQ3tEPW4Q7BQ5`Q7BQ3pQ3rP1Q7\Q7mQ3tEPW4Q4bp+0<gS5`Q5Vp+0=ZREQ6YH0TX97Q7BPRPRQ4EQ4bQ6nQ04POP_P?PSP]Q6qPRQ7YCyP>PHb5b6b7X17Q6s,F1P1P`Q7\C|^17P1P^O1b0GzQ7AQ4bQ4yQ6]P1P^Q0JO2b0Q67Q66Q66Q5hQ4zQ6bP1Pop+01BS6]O2b0b2b3FeP5eP5Q5`Q5VQ5`p+0<1p+03kS4EP1Q7qQ2EDgW4Q3pQ0\Q2UQ3pQ3xQ2UQ3pQ4MQ2UQ35Q3xQ2WPsQ7iQ5VQ7mQ7mQ3HQ40/2LS35Q7A37X8APwQ6_,21S6_Q40p+05:S6Y/01S5H3IX97p+07TS52Q4HQ4}Q5f'6Q5F,6<Q4}Q5fP<Q5FPXQ7`Q7IQ4~Q78Q52Q52Q62G3PXQ7`Q4CQ6zQ3}PwPwQ5cG3EKQ7rP_P720O79P:Q1fH1@R<PSP]Q6jP=P]PdP=P]20h]BR\P]Q6gPpDMFLP>PHb5b6b7X17X;7X:YAA:lJS1f104:S5FPB128DS4}p+0=\S3qQ7X,F9S5_CH[[^17^;7^:YP1Q5fQ4RQ4dQ0GQ6]O5b0Q3~PZG4Q7>Q0MDEQ2zQ2]Q7>37eQ3zPaD8Q0FQ7mQ35Q6\'0X8AQ52Q7;Q29Q2:Q33Q68Q67Q67Q66Q4yPCP1p+07XS5fQ0vO2S7eb0b2b3Q3~PZG4Q3FeQ3zPaD8GJE5Q0\Q25Q28Q45Q5VQ7mQ7mQ2zQ3}/2LS0\Q7A37X8APwQ6_Q3}Q7:3IX97Q65Q4HQ7MQ7L'6Q7KQ7J'6Q7MQ7LQ7KQ7JPXQ7`Q7IQ4~Q78Q65Q65PhG3PXQ7`PbPgQ6NPwPwQ5cG3EKQ7rP_P<PSP]Q6jP=P]PdP=P]P\P]Q6dPpDMFLP>PHb5b6b7X17X;7X:YQ1fQ5FPBQ7q,28S7JQ3qQ5_CH[[^17^;7^:YP1Q7LQ4RQ4dQ0GQ6]O5b0Q6hQ05G4Q7>Q0MDEQ2HQ2`Q7>37ePfQ1yD8Q0FQ7mQ0\Q6\'0X8AQ65Q7;Q5|Q7OQ2XQ68Q67Q67Q66Q4xPnQ7eb0b2b3Q6hQ05G4Q2mePfQ1yD8GJE5Q3rQ5VQ7mQ25Q7HQ5vQ5VQ7mQ7mQ2HQ6N/2LRZQ7A37X8APwQ6_Q6NQ073IX97Q0[Q4HQ7GQ7E'6Q70Q3]'6S6_Q7GQ7EQ70Q3]PXQ7`Q7IQ4~Q78Q0[Q0[Q6^G3PXQ7`Q4;Q5nQ6kPwPwQ5cG3EKQ7rP_P<PSP]Q6jP=P]PdP=P]P\P]Q6bPpDMFLP>PHb5b6b7X17X;7X:YQ1fQ5FPB128PQ3qQ5_CH[[^17^;7^:YP1Q7EQ4RQ4dQ0GQ6]O5b0Q7@PTG4Q7>Q0MDEQ2TQ2jQ7>37ePfQ1yD8Q0FQ7mQ6\,0ZX8AQ0[Q7;Q50Q4|Q2[Q68Q67Q67Q66Q4wPmQ7eb0b2b3Q7@PTG4Q3HePfQ1yD8GJGxQ7AP1EDb<Q4nQ0qE5Q2?P1E5b=Q3t#qMAnQ0kQ7hP1PJQ6KQ5=Q7pPJQ6KPJQ5=CTdO4b<P4P`P3P;1Y`3dQ04DWQ7BQ6KQ7BPcQ2SP1Q3rPoQ0wEQW4PcQ2PQ6KQ2bQ4dD;PcQ2PPzQ2bQ4dD;Q6AQ5XPcP2Q2PQ6KQ2bQ4dg0630Q6vQ6tQ00$0CQ01#B$08'_g064:Pvg065DQ2<Q2iQ2<Q1iQ2<Q26Q2<Q3zQ2<Q7NQ2<Q1~Q2<400D<D<Q4pQ6vPvE[Q1]eQ1]Q5`Q3yQ5`Q2M-0f1$0NW4Q0rQ1iQ0rQ3iQ0rQ2~Q0rQ7NQ0rQ2tQ0rQ21Q0rDwD<D<S2<Q4rQ6vPvCRQ1]eQ1]p+0<hRZQ3jQ1x00f1$0NX4ZQ3j$1>Q2MP1E5b=Q2MP1E5b=N>1=Q6aQ03P1PEQ6KP{Q7pPEQ6KPEP{CTdO4b<Q7BPJP3P;1YJ3dPzDWQ5`Q6KQ5`PcQ2AP1Q4EPqQ0|EQW4PcQ2SQ6KQ3rPoD;PcPG1@KZQ1SQ6t5oKQ2SQ1mn0100000020000PzQ3rPoD;Q0wQ5YPcP2Q2SQ6KQ3rPog066NQ1SP4Q6JQ1sQ1dg067XPvg068bQ2<Q4rP4PvCRQ1teQ1tPZQ4rp+0<2S2<Q1uP1Q7bQ6L'mPDQ1sEPX4ZPZPwQ2<Q1uP1Q7]PDQ1sEPX4ZP^p+0<iS1SPwQ3qP1Q7]D~X97PZPdPdP@P^Q7fQ5iPOP_P?PSP]Q5xPdQ7c#ZCyP>PHb5b6b7X171F1JP1PEQ7]C|^17P1PoO1b0GzQ4MP^Q5EQ6dP1PoQ0WO2b0Q69Q68Q68Q67Q5GQ6gP1PsQ0qO2b0b2b3FeP5eP5Q1SPwQ1Sp+0<3S67Q2fP1PkQ1dDgW4Q2<Q2YQ1qQ2<PaQ1qQ2<Q5DQ1qPNPaQ1wPxQ0xPwPDPDQ2z12FLS2<Q4H37X8AP^Q6a,21S2zQ2c/01S6d7IFX97Q4RQ4FQ6_Q3\p+06ZR5'6Q70Q3]Q3\P5PXp+0=?S3\Q4~Q5cQ72Q4RQ4RQ4CG3PXQ3\Q45Q5vQ40P^P^Q5LG3EKQ7oP_P<PSP]Q6qP=P]PpP=P]P\P]PRQ6ODMFLP>PHb5b6b7X17X;7X:YQ64p+0=[S705A:S6_Q5`/0:S4MPB128lS7cp+0=^R51F95S5xCH[[^17^;7^:YP1Q3]Q5fPqQ0vQ0qO5b0Q79Q05G4Q78P[DEQ2HQ3RQ7837eQ2tQ2ID8PQPDQ2<Q6p'0X8AQ4RQ7?Q7CQ5\Q2`Q6:Q69Q69Q68Q5EQ6UP1p+07ZS3]Q0_O2S5ib0b2b3Q79Q05G4Q2qeQ2tQ2ID8GJE5Q2YQ2~Q2WQ46PwPDPDQ2HQ35Q4H37X8AP^Q2zQ40Q3R/01S2H3IX97Q5TQ4FQ4X/6}Q3YQ3X'6Q4XP}Q3YQ3XPXQ3\Q4~Q5cQ72Q5TQ5TPbG3PXQ3\Q6zQ62Q3}P^P^Q5LG3EKQ7oP_P<PSP]Q6qP=P]PpP=P]P\P]Q6jQ6ODMFLP>PHb5b6b7X17X;7X:YQ6_Q4MPB128kS3XP5Q5xCH[[^17^;7^:YP1P}Q5fPqQ0vQ0qO5b0Q3~PTG4Q78P[DEQ2TQ6YQ7837eQ21PfD8PQPDQ35Q6p'0X8AQ5TQ7?Q5~Q27Q2jQ6:Q69Q69Q68Q4zQ7;Q5ib0b2b3Q3~PTG4Q3FeQ21PfD8GJE5Q1uPwPDQ2~Q7NQ7iPwPDPDQ2TQ0\Q4H37X8AP^Q2zQ3}Q5H3IX97Q52Q4Fp+06URTp+06TR}'6Q5;Q3T'6PTP}Q5;Q3TPXQ3\Q4~Q5cQ72Q52Q52Q4;G3PXQ3\PgPhQ6NP^P^Q5LG3EKQ7oP_P<PSP]Q6qP=P]PpP=P]P\P]Q6gQ6ODMFLP>PHb5b6b7X17X;7X:YQ6_Q4MPBQ7JP5Q5xCH[[^17^;7^:YP1P}Q5fPqQ0vQ0qO5b0Q6hQ1bG4Q78P[DEQ2RQ2]Q7837eQ21PfD8PQPDQ0\Q6p'0X8AQ52Q7?Q51Q37Q33Q6:Q69Q69Q68Q4yPCQ5ib0b2b3Q6hQ1bG4Q2meQ21PfD8GJGxQ4HP1EDb<Q4rQ0VE5Q2LP1E5b=Q1d#qMAnQ6XQ7QP1Q70PMP{%N3S4rQ70PMQ70P{CTdO4b<Q5`PEp+0=2S4HP;Q4H,YEdPzDWPZPMPcQ1oP1Q1uPsQ0yEQX4ZPcQ1nPMQ4EPqD;PcPGQ1S,@KQ6v9oK4Q1nQ3dn0100000020000PzQ4EPqD;Q0|Q5?PcP2Q1nPMQ4EPqg069lP4Q7BQ3VQ1kQ1jg06;6Pvg06<@Q7UQ1qQ7UQ3iQ7UQ3tQ7UQ2;Q7UQ2tQ7UQ4IQ7UQ22Q7UDwD<D<Q4sQ7BPvE[Q1leQ1lQ1SQ4sQ1SQ67Q2fP1Q5hPkQ1jEPW4Q1SQ56Q1SQ67Q2fP1Q3nPkQ1jEPW4Q4dp+0<jR}Pwp+0=]S56P1Q3nD~X97Q1SQ6xQ6xP@Q4dQ6sQ5kPOP_P?PSP]Q6WQ6xQ6n#ZCyP>PHb5b6b7X171F1DS5kP1Q70Q3nC|^17P1PqO1b0GzQ4NQ4dQ5GQ6gP1PqQ0qO2b0Q6:Q69Q69Q68Q5MQ6jP1Q5:Q0OO2b0b2b3FeQ4ceQ4cP}Pwp+0<4S4cQ3sP1PlQ1lDgX4}Q67Q2YQ3fQ67PaQ3fQ67Q5DQ3fPNPaQ1yPyQ47PwPkPkQ2T12~LS67Q7237X8AP^Q6X,21S2TQ2a/01S687I~X97Q4AQ4BQ3TQ3W'6Q3Pp+06ORT'6Q3TQ3WQ3PPTPXQ6lQ5LQ5KQ4JQ4AQ4AQ5vG3PXQ6lQ7iQ45Q79P^P^Q58G3EKQ7VP_P<PSP]PdP=P]PmP=P]P\P]Q6qQ7DDMS3PFLP>PHb5b6b7X17X;7X:YQ3q9A:`S3T10Z:S6gPBQ77,28S4dp+0=_S4N1F9`R9CH[[^17^;7^:YP1Q3Wp+07YS3WPsQ19Q0OO5b0PFQ1bG4Q4DP[DEQ2RQ2cQ4D37eQ4IQ1vD8PQPkQ67Q6t'0X8AQ4AQ6QQ02Q7CQ2]Q5^Q6:Q6:Q69Q5GQ7?P1p+07[RTQ0zO2S5hb0b2b3PFQ1bG4Q30eQ4IQ1vD8GJE5Q2YQ2;Q4KQ0xPwPkPkQ2RQ79/2LS1bQ7237X8AP^Q2TQ79Q6d3IX97Q4RQ4BQ3MQ59'6Q3OQ3I'6Q3MQ59Q3OQ3IPXQ6lQ5LQ5KQ4JQ4RQ4RQ62G3PXQ6lQ4CQ6zQ3~P^P^Q58G3EKQ7VP_P<PSP]PdP=P]PmP=P]P\P]PRQ7DDMS3IFLP>PHb5b6b7X17X;7X:YQ3TQ6gPBQ7cQ4NP9CH[[^17^;7^:YP1Q59Q3WPsQ19Q0OO5b0Q40Q0DG4Q4DP[DEQ2OQ3RQ4D37eQ22Q1~D8PQPkQ1bQ6t'0X8AQ4RQ6QQ6rQ5~Q2`Q5^Q6:Q6:Q69Q5EQ6UQ5hb0b2b3Q40Q0DG4Q2}eQ22Q1~D8GJE5Q2fPwPkQ2;Q2tQ46PwPkPkQ2OQ2^Q7237X8AP^Q2TQ3~Q2H3IX97Q5TQ4Bp+06JS4BQ44'6Q43Q42'6Q4BQ44Q43Q42PXQ6lQ5LQ5KQ4JQ5TQ5TPhG3PXQ6lPbPgQ6hP^P^Q58G3EKQ7VP_P<PSP]PdP=P]PmP=P]P\P]Q6jQ7DDMFLP>PHb5b6b7X17X;7X:YQ3TQ6gPBQ4}Q4NP9CH[[^17^;7^:YP1Q44Q3WPsQ19Q0OO5b0Q3}Q0CG4Q4DP[DEQ2NQ6YQ4D37eQ22Q1~D8PQPkQ2^Q6t'0X8AQ5TQ6QQ5RQ51Q2jQ5^Q6:Q6:Q69Q4zQ7;Q5hb0b2b3Q3}Q0CG4Q2deQ22Q1~D8GJGxQ72P1EDb<Q4sQ0PE5Q1nP1E5b=Q1j#qMAnQ6[p+0=DS72P1Q3qPMP{Q4rQ3qPMQ3qP{CTdO4b<PZQ70Q4HP;Q70Q4H'YdPzDWQ1SPMQ1SPcQ3kP1Q2fQ5:Q0}EQW4PcQ3ePMQ1uPsD;PcPG1@K}Q6{9oK4Q3eQ1Yn0100000020000PzQ1uPsD;Q0yQ5ZPcP2Q3ePMQ1uPsg06=JP4Q5`p+0;nQ3hQ3cg06>TPvg06?^Q3VQ3fQ3VQ1rQ3VQ3tQ3VQ2EQ3VQ31Q3VQ4IQ3VQ28Q3VQ23Q3V400D<D<D<Q4tQ5`PvE[p+02oS5`eQ5`P}Q4tQ4cQ3sP1Q3nQ3p'mPlQ3cEPX4}P}Q5rQ4cQ3sP1Q6nPlQ3cEPX4}Pop+0<kR4PwP5Q7jH0TX97P}PpPpP@PoQ7kPiPOP_P?PSP]Q6WPpQ7X#ZCyP>PHb5b6b7X17Q5kP1Q3qQ6nC|^17P1PsO1b0GzQ4PPoQ5MQ6jP1PsQ0OO2b0Q5^Q6:Q6:Q69Q5UPRP1PxQ0VO2b0b2b3FeQ4aeQ4aP4Pwp+0<5RoQ7gP1Q77Q5`DgX44Q4cQ2YQ1pQ4cPaQ1pQ4cQ5DQ1pPNPaQ1{Q5<Q0[PwPlPlQ2O12rLS4cQ4J37X8AP^Q6[,21S2Op+05>S4a/01S697IrX97Q5fQ4?Q42p+06FS6j'6p+06ES4Pp+06DS6W'6Q42Q6jQ4PQ6WPXQ7hQ58Q5IQ4ZQ5fQ5fQ45G3PXQ7hQ46Q7iPFP^P^Q4=G3EKQ7`P_P<PSP]Q6xP=P]PnP=P]P\P]PdQ7DDMFLP>PHb5b6b7X17X;7X:YQ569A:JS7DQ1S/0:S6WPBQ64,28S4Pp+0=`S42P9CH[[^17^;7^:YP1Q6jQ3]Q5:Q0_Q0VO5b0P~Q0CG4Q4@P[DEQ2NQ2aQ4@37eQ28Q7FD8PQPlQ4cQ6v'0X8AQ5fQ6RQ6kQ02Q6YQ6;Q5^Q5^Q6:Q5MQ6QP1Q3{Q0~O2S6jb0b2b3P~Q0CG4Q2VeQ28Q7FD8GJE5Q2YQ31Q1wQ47PwPlPlQ2NQ2<Q4J37X8AP^Q2OQ687IFX97Q4AQ4?Q3GQ54'6Q53Q3E'6Q3GQ54Q53Q3EPXQ7hQ58Q5IQ4ZQ4AQ4AQ6zG3PXQ7hQ5vQ4CQ40P^P^Q4=G3EKQ7`P_P<PSP]Q6xP=P]PnP=Q3PFLP>PHb5b6b7X17X;7X:YQ7DQ6WPBQ4dQ42P9CH[[^17^;7^:YP1Q54Q3]Q5:Q0_Q0VO5b0Q79Q0BG4Q4@P[DEQ2GQ2cQ4@37eQ23Q21D8PQPlQ2<Q6v'0X8AQ4AQ6RQ2:Q6rQ2]Q6;Q5^Q5^Q6:Q5GQ7?Q6jb0b2b3Q79Q0BG4Q2qeQ23Q21D8GJE5Q3sPwPlQ31Q4IQ0xPwPlPlQ2GQ35Q4J37X8AP^Q2OQ40Q6d3IX97Q4RQ4?Q55Q3C'6Q3AQ3@'6Q55Q3CQ3AQ3@PXQ7hQ58Q5IQ4ZQ4RQ4RPgG3PXQ7hQ62PbQ3}P^P^Q4=G3EKQ7`P_P<PSP]Q6xP=P]PnP=Q3IFLP>PHb5b6b7X17X;7X:YQ7DQ6WPBQ3XQ42P9CH[[^17^;7^:YP1Q3CQ3]Q5:Q0_Q0VO5b0Q3~Q0AG4Q4@P[DEQ2KQ3RQ4@37eQ23Q21D8PQPlQ35Q6v'0X8AQ4RQ6RQ7OQ5RQ2`Q6;Q5^Q5^Q6:Q5EQ6UQ6jb0b2b3Q3~Q0AG4Q3FeQ23Q21D8GJGxQ4JP1EDb<Q4tQ2{E5Q3eP1E5b=Q3c#qMAnQ6`Q7WP1Q56PMP{Q4rQ56PMQ56P{CTdO4b<Q1SQ3qQ4HP;Q3qQ4H'YdPzDWP}PMPcp+02kP1Q3sPxQ10EQX4}PcQ3bPMQ2fQ5:D;PcPG1@K4Q6~9oKWQ3bp+02bS4rn0100000020000PzQ2fQ5:D;Q0}Q5[PcP2Q3bPMQ2fQ5:g06@hPWPZQ6IQ3`p+02gS2fg06B2Pvg06C<Q7^Q1pQ7^Q1kQ7^Q1sQ7^Q2EQ7^Q3yQ7^Q2\Q7^Q28Q7^Q4GQ7^Q24Q7^DwD<D<D<Q4vPZPvE[Q3aeQ3aP4Q4vPoQ7gP1Q7kQ6J'mQ77Q2fEPX44P4Q3KPoQ7gP1Q7fQ77Q2fEPX44Pqp+0<lRgPwQ4NP1Q7fD~X97P4PmPmP@PqP3Q5lPOP_P?PSP]Q6KPmQ7[#ZCyP>PHb5b6b7X17Q5kP1Q56Q7fC|^17P1Q5:O1b0GzQ4SPqQ5UPRP1Q5:Q0VO2b0Q6;Q5^Q5^Q6:Q5JQ6qP1PyQ0PO2b0b2b3FeQ4_eQ4_PgPwp+0<6RRQ3uP1Q64Q3aDgX4gPoQ2YQ1XPoPaQ1XPoQ5DQ1XPNPaPfQ6oQ65PwQ77Q77Q2GQ7l/2LS4_Q4Z37X8AP^Q6`,21S2GQ7lp+05?S6:/01S4S3IX97Q3WQ49Q3@Q3?'6Q3<Q3;'6Q3@Q3?Q3<Q3;PXQ03Q4=Q4OQ48Q3WQ3WQ7iG3PXQ03Q0xQ46P~P^P^Q4kG3EKQ7aP_P<PSP]PpP=P]PCP=P]P\P]Q6xQ6MDMFLP>PHb5b6b7X17X;7X:YAA:E5S3;10}:RoPB128`S3<p+0=aS3@P9CH[[^17^;7^:YP1Q3?PTPxQ0zQ0PO5b0PrQ0AG4Q4<P[DEQ2KQ4aQ4<37eQ4GQ2pD8PQQ77Q4_Q6{'0X8AQ3WQ6SQ7@Q6kQ3RQ5qQ6;Q6;Q5^Q5UQ6RP1Q3|Q0EO2S3?b0b2b3PrQ0AG4Q2[eQ4GQ2pD8GJE5Q2YQ2\Q1yQ0[PwQ77Q77Q2KQ67Q4Z37X8AP^Q2GQ697I~X97Q5fQ49Q4{p+067S2K'6p+066S2pQ3U'6Q4{Q2KQ2pQ3UPXQ03Q4=Q4OQ48Q5fQ5fQ4CG3PXQ03Q45Q5vQ79P^P^Q4kG3EKQ7aP_P<PSP]PpP=P]PCP=P]P\P]PdQ6MDMFLP>PHb5b6b7X17X;7X:YQ3;PBQ4PQ3@P9CH\o[^17^;7^:YP1Q2KPTPxQ0zQ0PO5b0PFQ0@G4Q4<P[DEQ2JQ2aQ4<37eQ24Q22D8PQQ77Q67Q6{'0X8AQ5fQ6SQ29Q2:Q6YQ5qQ6;Q6;Q5^Q5MQ6QQ3?b0b2b3PFQ0@G4Q30eQ24Q22D8GJE5Q7gPwQ77Q2\Q28Q47PwQ77Q77Q2JQ1bQ4Z37X8AP^Q2GQ79Q683IX97Q4AQ49p+064S49Q3Q'6p+062S2GQ3N'6Q49Q3QQ2GQ3NPXQ03Q4=Q4OQ48Q4AQ4APbG3PXQ03Q6zQ62Q3~P^P^Q4kG3EKQ7aP_P<PSP]PpP=P]PCP=P]P\P]Q6qQ6MDMFLP>PHb5b6b7X17X;7X:YQ3;PBQ7cQ3@P9CH\o[^17^;7^:YP1Q3QPTPxQ0zQ0PO5b0Q40Q0?G4Q4<P[DEQ2FQ2cQ4<37eQ24Q22D8PQQ77Q1bQ6{'0X8AQ4AQ6SQ5|Q7OQ2]Q5qQ6;Q6;Q5^Q5GQ7?Q3?b0b2b3Q40Q0?G4Q2}eQ24Q22D8GJGxQ4ZP1EDb<Q4vQ0UE5Q3bP1E5b=Q2f#qMAnQ6ZQ7ZP1P5Q6HP{Q4H#NS4vP5Q6HP5P{CTdO4b<P}Q56p+0=1RoP;Q56/YodPzDWP4Q6HPcQ3gP1Q7gPyQ1AEQX44PcQ1QQ6HQ3sPxD;PcPG1@KgQ749oKWQ1QQ1Un0100000020000PzQ3sPxD;Q10Q5]PcP2Q1QQ6HQ3sPxg06DFPWQ1SQ6GQ1eQ1Pg06EPPvg06FZQ5aQ1XQ5aQ3hQ5aQ1jQ5aQ1dQ5aQ3yQ5aQ3jQ5aQ2=Q5aQ4GQ5aQ2WQ5aQ25Q5a400D<D<D<D<Q4wQ1SPvE[Q1NeQ1NPgQ4wPRQ3uP1Q6nQ6I'mQ64Q1PEPX4gPgQ4\PRQ3uP1Q7dQ64Q1PEPX4gPsp+0<mRbPwQ42P1Q7dD~X97PgPnPnP@PsQ7XQ5mPOP_P?PSP]PMPnQ7YCyP>PHb5b6b7X17Q5kP1P5Q7dC|^17P1PxO1b0Gzp+08\PsQ5JQ6qP1PxQ0PO2b0Q5qQ6;Q6;Q5^Q5OPdP1Q5<Q2{O2b0b2b3FeQ4[eQ4[PbPwQ6uPeP1P`Q1NDgX4bPRQ2YQ1LPRPaQ1LPRQ5DQ1LPNPaQ1~Q5>Q52PwQ64Q64Q2JQ6^/2LS4[Q4837X8AP^Q6Z,21S2JQ6^Q2g/01S5^3IX97Q3]Q4TQ3Np+060S6q'6p+05oS7Yp+05nRR'6Q3NQ6qQ7YPRPXQ7QQ4kQ4jQ4QQ3]Q3]Q46G3PXQ7QQ47Q0xPrP^P^Q4iG3EKQ3\P_P<PSP]PmP=P]Q7;P=P]P\P]PpQ6LDMFLP>PHb5b6b7X17X;7X:YQ70Q4N5A:S7Y104:S3NPB128JS5mp+0=bRRP9CH[[^17^;7^:YP1Q6qQ3{PyQ0~Q2{O5b0Q7lQ0?G4PjP[DEQ2FQ6:;7jeQ2WQ7HD8PQQ64Q4[Q6~'0X8AQ3]Q6TQ6NQ7@Q2cQ6<Q5qQ5qQ6;Q5JQ6SP1p+07^S7@Q0dO2S6qb0b2b3Q7lQ0?G4Q2XeQ2WQ7HD8GJE5Q2YQ2=Q1{Q65PwQ64Q64Q2FQ4cQ4837X8AP^Q2JQ4S7IrX97Q3WQ4Tp+05mS2Fp+05lS7H'6p+05kS0?Q39'6Q2FQ7HQ0?Q39PXQ7QQ4kQ4jQ4QQ3WQ3WQ5vG3PXQ7QQ7iQ45PFP^P^Q4iG3EKQ3\P_P<PSP]PmP=P]Q7;P=P]P\P]Q6xQ6LDMFLP>PHb5b6b7X17X;7X:YQ7YQ3NPBQ3<PRP9CH[[^17^;7^:YP1Q7HQ3{PyQ0~Q2{O5b0P~Q0>G4PjP[DEQ38Q4a;7jeQ25Q23D8PQQ64Q4cQ6~'0X8AQ3WQ6TQ5\Q29Q3RQ6<Q5qQ5qQ6;Q5UQ6RQ6qb0b2b3P~Q0>G4Q2VeQ25Q23D8GJE5Q3uPwQ64Q2=Q4GQ0[PwQ64Q64Q38Q2<Q4837X8AP^Q2JQ697IFX97Q5fQ4TQ3:Q3='6p+05gS4Tp+05fS2J'6Q3:Q3=Q4TQ2JPXQ7QQ4kQ4jQ4QQ5fQ5fQ62G3PXQ7QQ4CQ6zQ40P^P^Q4iG3EKQ3\P_P<PSP]PmP=P]Q7;P=P]P\P]PdQ6LDMFLP>PHb5b6b7X17X;7X:YQ7YQ3NPBQ4dPRP9CH[[^17^;7^:YP1Q3=Q3{PyQ0~Q2{O5b0Q79Q0=G4PjP[DEQ36Q2a;7jeQ25Q23D8PQQ64Q2<Q6~'0X8AQ5fQ6TQ27Q5|Q6YQ6<Q5qQ5qQ6;Q5MQ6QQ6qb0b2b3Q79Q0=G4Q2qeQ25Q23D8GJGxQ48P1EDb<Q4wQ0QE5Q1QP1E5b=Q1P#qMAnQ6fQ7_P1Q4NQ5pP{Q4vQ4NQ5pQ4NP{CTdO4b<P4P5PoP;1Y5odPzDWPgQ5pPcQ1cP1Q3uQ5<Q11EQX4gPcQ1JQ5pQ7gPyD;PcPG1@KbQ6w9oKWQ1JQ1Vn0100000020000PzQ7gPyD;Q1AQ5jPcP2Q1JQ5pQ7gPyg06GdPWP}Q6FQ1`Q1Fg06HnPvg06J8Q2BQ1LQ2BQ3`Q2BQ3cQ2BQ1lQ2BQ1tQ2BQ3jQ2BQ1xQ2BQ3SQ2BQ2WQ2BQ4KQ2BQ26Q2BDwD<D<D<D<Q4xP}PvE[Q1aeQ1aPbQ4xQ6uPeP1Q7\Q6G'mP`Q1FEPX4bPbQ4^Q6uPeP1Q7mP`Q1FEPX4bQ5:p+0<nRWPwQ3@P1Q7mD~X97PbPCPCP@Q5:PPQ5oPOP_P?PSP]Q6HPCQ7=CyP>PHb5b6b7X17Q5kP1Q4NQ7mC|^17P1PyO1b0GzQ4VQ5:Q5OPdP1PyQ2{O2b0Q6<Q5qQ5qQ6;Q5NQ6xP1Q6oQ0UO2b0b2b3FeQ4]eQ4]PWPwQ6yQ3vP1PJQ1aDgX4WQ6uQ2YQ1TQ6uPaQ1TQ6uQ5DQ1TPNPaQ21Q5BQ5TPwP`P`Q38Q5n/2LRdQ4Q37X8AP^Q6f,21S38Q5nQ2e/01S6u3IX97PTQ4uQ2Jp+05eS4]'6p+05dRPp+05cRj'6Q2JQ4]PPPjPXQ72Q4iQ4hPuPTPTQ0xG3PXQ72Q0[Q47Q7lP^P^Q4gG3EKQ6lP_P<PSP]PnP=P]Q6UP=P]P\P]PmQ6JDMFLP>PHb5b6b7X17X;7X:YQ3qQ425A:S2J10g:RjPB128ES6;p+0=cRPP9CH[[^17^;7^:YP1Q4]Q3|Q5<Q0EQ0UO5b0Q6^Q0=G4Q4>P[DEQ36Q2gQ4>37eQ4KQ3zD8PQP`Q74,0dX8APTQ6cQ6hQ6NQ2aQ6=Q6<Q6<Q5qQ5OQ6TP1p+07_S6NQ0FO2S4]b0b2b3Q6^Q0=G4Q33eQ4KQ3zD8GJE5Q2YQ3SPfQ52PwP`P`Q36Q4_Q4Q37X8AP^Q38Q7lQ5^3IX97Q3]Q4up+05bS36p+05aS3z'6p+05`S0=p+05_S5:'6Q36Q3zQ0=Q5:PXQ72Q4iQ4hPuQ3]Q3]Q45G3PXQ72Q46Q7iP~P^P^Q4gG3EKQ6lP_P<PSP]PnP=P]Q6UP=P]P\P]PpQ6JDMFLP>PHb5b6b7X17X;7X:YQ2JPBQ5mPPP9CH\j[^17^;7^:YP1Q3zQ3|Q5<Q0EQ0UO5b0PrQ0<G4Q4>P[DEQ2DQ6:Q4>37eQ26Q24D8PQP`Q4_Q74'0X8AQ3]Q6cQ7CQ5\Q2cQ6=Q6<Q6<Q5qQ5JQ6SQ4]b0b2b3PrQ0<G4Q2[eQ26Q24D8GJE5PePwP`Q3SQ2WQ65PwP`P`Q2DQ67Q4Q37X8AP^Q38Q4S7I~X97Q3WQ4up+05^S4up+05]S38'6p+05\S4Sp+05[S3S'6Q4uQ38Q4SQ3SPXQ72Q4iQ4hPuQ3WQ3WQ6zG3PXQ72Q5vQ4CQ79P^P^Q4gG3EKQ6lP_P<PSP]PnP=P]Q6UP=P]P\P]Q6xQ6JDMFLP>PHb5b6b7X17X;7X:YQ2JPBQ4PPPP9CH\j[^17^;7^:YP1Q38Q3|Q5<Q0EQ0UO5b0PFQ0;G4Q4>P[DEQ2_Q4aQ4>37eQ26Q24D8PQP`Q67Q74'0X8AQ3WQ6cQ5~Q27Q3RQ6=Q6<Q6<Q5qQ5UQ6RQ4]b0b2b3PFQ0;G4Q30eQ26Q24D8GJGxQ4QP1EDb<Q4xQ0RE5Q1JP1E5b=Q1F#qMAnQ6\Q7bP1Q42Q6EP{Q4vQ42Q6EQ42P{CTdO4b<PgQ4NPoP;Q4N/YodPzDWPbQ6EPcQ1BP1PeQ6oQ12EQX4bPcQ1_Q6EQ3uQ5<D;PcPG1@KWQ6|9oKZQ1_Q1:n0100000020000PzQ3uQ5<D;Q11Q5gPcP2Q1_Q6EQ3uQ5<g06KBPZP4Q7PQ1=Q1>g06LLPvg06MVQ0pQ1TQ0pQ1eQ0pQ2fQ0pQ5`Q0pQ1mQ0pQ1]Q0pQ1xQ0pQ1zQ0pQ34Q0pQ4KQ0pQ1wQ0pQ2~Q0p400D<D<D<D<D<Q4yP4PvE[Q1@eQ1@PWQ4yQ6yQ3vP1P|PJQ1>EPX4WPWQ4UQ6yQ3vP1PDPJQ1>EPX4WPxp+0<oR4PwPRQ61H0TX97PWQ7;Q7;P@PxQ7qQ5}POP_P?PSP]Q6GQ7;Q6XCyP>PHb5b6b7X17Q5kP1Q42PDC|^17P1Q5<O1b0GzQ4WPxQ5NQ6xP1Q5<Q0UO2b0Q6=Q6<Q6<Q5qQ5PPpP1Q5>Q0QO2b0b2b3FeQ7<eQ7<P4PwQ6}Q3xP1PEQ1@DgX44Q6yQ2YQ1hQ6yPaQ1hQ6yQ5DQ1hPNPaQ22Q5@Q4RPwPJPJQ2DQ4;/2LRx;7uX8AP^Q6\,21RDQ4;p+05BS2D/01S223IX97Q3{Q4mQ3SQ3L'6Q3Jp+05XRZ'6Q3SQ3LQ3JPZPXQ7WQ4gQ4fQ4oQ3{Q3{Q47G3PXQ7WQ65Q0[Q6^P^P^Q4eG3EKQ7hP_P<PSP]PCP=P]Q7?P=P]P\P]PnPMDMFLP>PHb5b6b7X17X;7X:YQ56Q3@5A:RZ10b:R`PBQ70,28S56p+0=dS3JP9CH[[^17^;7^:YP1Q3LQ7@Q6oQ0dQ0QO5b0Q5nQ0;G4Q4:P[DEQ2_Q2eQ4:37eQ1wQ7ND8PQPJQ6w,0xX8AQ3{Q6eQ3}Q6hQ4aQ6>Q6=Q6=Q6<Q5NQ6cP1Q4LPQO2Rxb0b2b3Q5nQ0;G4Q2jeQ1wQ7ND8GJE5Q2YQ34Q1~Q5TPwPJPJQ2_Q4[;7uX8AP^Q6^Q6u5IDX97PTQ4mQ4qQ2y'6Q2wQ2x'6Q4qQ2yQ2wQ2xPXQ7WQ4gQ4fQ4oPTPTQ7iG3PXQ7WQ0xQ46PrP^P^Q4eG3EKQ7hP_P<PSP]PCP=P]Q7?P=P]P\P]PmPMDMFLP>PHb5b6b7X17X;7X:YPBQ6;Q3JP9CH\`\Z^17^;7^:YP1Q2yQ7@Q6oQ0dQ0QO5b0Q7lQ0:G4Q4:P[DEp+04\RjQ2gQ4:37eQ2~Q25D8PQPJQ4[Q6w'0X8APTQ6eQ02Q7CQ2aQ6>Q6=Q6=Q6<Q5OQ6TPxb0b2b3Q7lQ0:G4Q2XeQ2~Q25D8GJE5Q3vPwPJQ34Q4KQ52PwPJPJQ4c=7juX8AP^Q5^9IDrX97Q3]Q4mQ3^p+05RRD'6Q2sQ2u'6Q3^PDQ2sQ2uPXQ7WQ4gQ4fQ4oQ3]Q3]Q4CG3PXQ7WQ45Q5vPFP^P^Q4eG3EKQ7hP_P<PSP]PCP=P]Q7?P=P]P\P]PpPMDMFLP>PHb5b6b7X17X;7X:YPBQ3<Q3JP9CH\`\Z^17^;7^:YP1PDQ7@Q6oQ0dQ0QO5b0P~PUG4Q4:P[DEQ2CQ6:Q4:37eQ2~Q25D8PQPJQ4cQ6w'0X8AQ3]Q6eQ6rQ5~Q2cQ6>Q6=Q6=Q6<Q5JQ6SPxb0b2b3P~PUG4Q2VeQ2~Q25D8GJGxPuP1EDb<Q4yQ0SE5Q1_P1E5b=Q1>#qMAnQ6mQ6sP1Q3@Q6DP{Q4vQ3@Q6DQ3@P{CTdO4b<PbQ42PoP;Q42/YodPzDWPWQ6DPcQ1gP1Q3vQ5>Q15EQX4WPcQ1<Q6DPeQ6oD;PcPG1@K4Q719oK0Q1<Q1Wn0100000020000PzPeQ6oD;Q12Q5bPcP2Q1<Q6DPeQ6og06N`P0PgQ5{Q1IQ1Mg06OjPvg06Q4p+0;jR0Q1hP0Q1`P0Q1PP0Q3aP0Q3dP0Q1nP0Q1^P0Q1zP0Q1|P0Q2>P0Q1wP0Q1yP0Q2;P0DwD<D<D<D<D<Q4zPgPvE[Q1ZeQ1ZP4Q4zQ6}Q3xP1Q7dQ6E'mPEQ1MEPX44P4Q4`Q6}Q3xP1PlPEQ1MEPX44Pyp+0=0RgPwPPP1PlD~X97P4Q6UQ6UP@PyPkQ5yPOP_P?PSP]Q6FQ6UQ7nCyP>PHb5b6b7X17Q5kP1Q3@PlC|^17P1Q6oO1b0GzQ4YPyQ5PPpP1Q6oQ0QO2b0Q6>Q6=Q6=Q6<Q5QPmP1Q5BQ0RO2b0b2b3FeQ6BeQ6BPgPwQ73PaP1Q70Q1ZDgX4gQ6}Q2YQ3_Q6}PaQ3_Q6}Q5DQ3_PNPaQ23Q5AQ4APwPEPE12hLRLQ4o57jX8AP^Q6m,21Rjp+05C/017IhX97Q3|p+08=RhQ2uQ3['6Q3ZQ2o'6Q2uQ3[Q3ZQ2oPXQ7ZQ4eQ4lp+08<RNQ3|Q3|Q0[G3PXQ7ZQ52Q65Q5nP^P^p+08kRpG3EKQ03P_P<PSP]Q7;P=P]Q6QP=P]P\P]PCQ6HDMFLP>PHb5b6b7X17X;7X:YAA:5RR510W:R:PBQ3q,28p+0=eR8P9CH[[^17^;7^:YP1Q3[Q6NQ5>Q0FQ0RO5b0Q4;PUG4Q6PP[DEQ2CQ2DQ6P37eQ1yQ2tD8PQPEQ6|,0LX8AQ3|Q6iQ3~Q3}Q6:Q6?Q6>Q6>Q6=Q5PQ6eP1p+07aQ0LO2RLb0b2b3Q4;PUG4Q2`eQ1yQ2tD8GJE5Q2YQ2>Q21Q4RPwPEPEQ2CQ4o77dX8AP^Q5nQ225IjX97Q3{PhQ2rQ3D'6Q3BQ2k'6Q2rQ3DQ3BQ2kPXQ7ZQ4eQ4lPNQ3{Q3{Q46G3PXQ7ZQ47Q0xQ7lP^P^PpG3EKQ03P_P<PSP]Q7;P=P]Q6QP=P]P\P]PnQ6HDMFLP>PHb5b6b7X17X;7X:YPBQ56P8P9CH\:\5^17^;7^:YP1Q3DQ6NQ5>Q0FQ0RO5b0Q6^Q09G4Q6PP[DEp+04ZRyQ2eQ6P37eQ2;Q26D8PQPEQ6|,0dX8AQ3{Q6iQ6kQ02Q4aQ6?Q6>Q6>Q6=Q5NQ6cPLb0b2b3Q6^Q09G4Q33eQ2;Q26D8GJE5Q3xPwPEQ2>Q1wQ5TPwPEPEQ4_Q4o57yX8AP^Q7lQ6u5IjX97PTPhQ2nQ3>'6Q2vQ2h'6Q2nQ3>Q2vQ2hPXQ7ZQ4eQ4lPNPTPTQ5vG3PXQ7ZQ7iQ45P~P^P^PpG3EKQ03P_P<PSP]Q7;P=P]Q6QP=P]P\P]PmQ6HDMFLP>PHb5b6b7X17X;7X:YPBQ5mP8P9CH\:\5^17^;7^:YP1Q3>Q6NQ5>Q0FQ0RO5b0PrQ08G4Q6PP[DEQ2ZQ2gQ6P37eQ2;Q26D8PQPEQ4_Q6|'0X8APTQ6iQ2:Q6rQ2aQ6?Q6>Q6>Q6=Q5OQ6TPLb0b2b3PrQ08G4Q2[eQ2;Q26D8GJGxQ4oP1EDb<Q4zQ32E5Q1<P1E5b=Q1M#qMAnQ6pQ3nP1PRQ6CP{Q4vPRQ6CPRP{CTdO4b<PWQ3@PoP;Q3@/YodPzDWP4Q6CPcQ14P1Q3xQ5BQ41EQX44PcQ1DQ6CQ3vQ5>D;PcPG1@KgQ759oKbQ1DQ1On0100000020000Q5CQ3vQ5>D;Q15Q5dPcP2Q1DQ6CQ3vQ5>g06R>RKPbPbQ5zg06SH&0YK,`Gg06TRN=0iQ6tQ7kP1PPQ5zPzQ4vPPQ5zPPPzCTdO4b<P4PRPoP;1YRodQ5CDWPgQ5zPcQ0oP1PaQ5@Q1WEQX4gp+0;lRaQ1IPaQ1>PaQ1aPaQ4rPaQ3bPaQ3kPaQ1qPaQ2LPaQ1}PaQ20Pap+04WPaQ1{PaPfQ2\>00aaD<D<D<D<D<D<Q5GPWPvE[Q1OeQ1OPoQ5GPcQ3_PgQ04,?1Q5{Q2lQ5AQ1DL03X4oPoP@PcQ3_Pg1?1PQ5{Q2lQ5AQ1DL03X4oQ6oQ4HQ4lP8P1PPD~X97PoQ6QQ6QQ5>/F6Q6oPRQ5sPOP_P?PSP]Q7]Q6QQ0kCyP>PHb5b6b7X171F16RRP1PPPPC|^17P1Q5BO1b0Gzp+08aQ6oQ5SPnP1Q5BQ0SO2b0Q6@Q6?Q6?Q6>Q57PCP1Q5AQ32O2b0b2b3FeQ6BeQ6BQ4HQ4lQ4HPcQ1IPoP1Q6DQ2IQ4nQ14L03W4POP_P?PSQ7[:1<]VP>PHb5b6b7X171=1R^17P1Q5@O1b0Q5BQ5B/F6'=P7Q5@PcQ1MQ4Hp+0=g/O1Q6EQ1vQ4pQ16L03X97PcQ3_Q6DQ2IQ4nD;PcQ3_Q2i00d|Q2IQ4nD;Q14Q5ePcP2Q3_Q6DQ2IQ4ng06U\P}Q2@Q2ig06VfPvg06X0Q0]Q1OQ7fQ1iQ7fQ7]Q3i711W4Q2UQ1WP1E5b=N>19P3Q2iPcQ1IP1Q1vQ4pQ16EQX43Q14-182Q2i00d6PUE5ESQ5@/F6P1EDb<PhP1EDb<Q5GQ0TE5Q1DP1E5b=PzP1EDb<ESP{P1EDb<ESP{P1EDb<ESP{P1EDb<ESP{P1EDb<ESP{P1EDb<ESP{P1EDb<ESP{P1EDb<ESP{P1EDb<ESP{P1EDb<ESQ5=P1EDb<ESQ5lP1EDb<ESQ5BQ0JE5Q5B/?6Q5B$17E5Q3oP1E5b=PiP1EDb<ESQ5yP1EDb<ESQ5tP1EDb<ESQ63P1EDb<ESQ7gP1E5b=Q7gP1E5b=Q5uP1EDb<ESQ5wP1EDb<ESQ60P1EDb<ESQ1;Q18Q1RPqQ6{PvCRQ1;eQ1;PIQ1wQ1y91t1X4IPIQ1wQ1KP1F]b=Q0XQ17Q1RPqQ75PvCRQ0XeQ0XPIQ4iQ4j91t1X4IPIQ4iQ1\P1F]b=Q1[Q0NQ0PQ1[PIQ3eQ3k91t1X4IQ5`Q1GP1E5b=Q0tQ0IQ1RPqQ71PvCRQ0teQ0tPIQ3aQ1Y91t1X4IPIQ3aQ0jP1F]b=Q0fQ0KQ1RPqQ6|PvCRQ0feQ0fPIQ1PQ1N91t1X4IPIQ1PQ1CP1F]b=Q0YQ1EQ1RPqQ6tPvCRQ0YeQ0YPIQ1`Q1F91t1X4IPIQ1`Q0eP1F]b=Q3mQ0MQ1RPqQ6pPvCRQ3meQ3mPIQ1hQ1=91t1X4IPIQ1hQ0cP1F]b=Q0aP[Q1RPqQ6mPvCRQ0aeQ0aPIQ16Q3_91t1X4IPIQ16Q0nP1F]b=Q0`Q0JQ1RPqQ6wPvCRQ0`eQ0`PIQ1AQ1191t1X4IPIQ1AQ1HP1F]b=Q13Q6]Q1RPqQ6\PvCRQ13eQ13PIQ0{Q0s91t1X4IPIQ0{Q0hP1F]b=Q0lQ0WQ1RPqQ6fPvCRQ0leQ0lPIP@A1t1^X4IPIP@Q0^P1F]b=Q0TQ0qQ1RPqQ6ZPvCRQ0TeQ0TPIQ4bA1t1@X4IPIQ4bQ0mP1F]b=Q0bQ0OQ1RPqQ6`PvCRQ0beQ0bPIQ4`Q4b91t1X4IPIQ4`Q0iP1F]b=Q32Q0VQ1RPqQ6[PvCRQ32eQ32PIQ4UQ4`91t1X4IPIQ4UQ3lP1F]b=Q0SQ2{Q1RPqQ6XPvCRQ0SeQ0SPIQ4^Q4U91t1X4IPIQ4^Q0]P1F]b=Q0RQ0QQ1RPqQ6aPvCRQ0ReQ0RPIQ4\Q4^91t1X4IPIQ4\Q1?P1F]b=Q1RPqQ0kPvCRQ0QeQ0QPIQ3KQ4\91t1X4IPIQ3KQ0gP1F]b=H0QK07K07K07K07K07K07K07K07H15Q7RQ7RPcPsQ0rPIeQ5rPwPcP1Q3eQ5rQ62Q2WQ1vH14PwD;EQQ7T'UWD+13eWVWWWXWTWSWRWQWPWOWNWMWUWHaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWFWGaaaaaaaaaaaaaaaaaaWYWZWKWJWIWLaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWjaaaaaaaWiaaaaaaaWhaaaaaaaWgaaaaaaaWfaaaaaaaWeaaaaaaaWdaaaaaaaaWbaaaaaaaaaaaaaaaaW]aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW\aaaaaaaaaW[aW_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaX^7aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaXk7aWcaW`aaaaaaaaaaaWaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.
End FPX_1.


(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0StdioWrite_run2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.
Module Ns0StdioWrite.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.LibAtomic OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.LibWritev OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.LibWritevX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Frame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioWrite_run1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioWrite_run2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4e000_4f000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Ns0StdioWrite () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01058SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilC59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlgBsrealizes_nonemptyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_conseqC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9skipn_appI47Corelib4Init9Datatypes4list00I47Corelib4Init5Peano2le00C47Corelib4Init3Nat3subI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic6eq_indC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite<skipn_app_leC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=skipn_all_iffC47Corelib4Init5Logic5proj1C47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite<skipn_app_geC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib7Mh_00385Hoare3at_C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite2RIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run2;sw_regs_butC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk>mem_grows_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite2LMC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses9not_morphC59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Frame6in_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Frame>wbytes_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?mem_grows_transC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega8ZifyInst7Inj_Z_ZC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite6LM_rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphc59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run27sw_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run27mem_sw2C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_mstepsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite6finishC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite;rz_emit_nilC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C46Stdlib5Lists4List<length_skipnC47Corelib4Init5Peano2ltK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib4Init5Logic9False_indc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite;LM_store_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run2:sw_retry_aC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite:LM_wbytes8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite6RI_butC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec?rdn_wbytes_hit8C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib7Mh_0055:RdnPeelKit7wchainZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:RdnPeelKit6wch_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:RdnPeelKit?rdn_wchainZ_outC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib7Mh_0056<RefMemcpyLib9rdn_skipnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC59OSSVerify5KrLib7Mh_00949LibWritev=word_to_nat_ZC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387WalkTac=wf_getr_chainC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run28sw_c2_eqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite:finish_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run28sw_c2_neC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:LibWritevX@rz_writev1_wallXC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_ae5a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_ae5a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007E_ae5a8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEK47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite8pc_ae55cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143BNs0StdioWrite_run17mem_sw1C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs7sw_post00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs7sw_post01C1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Ltac rdn_side_fast := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia_fast.
Local Ltac rdn_solve_fast :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (first [ RdnPeelKit.rdn_peel_many ltac:(idtac; rdn_side_fast) | rdn_peel1 ]; rdn_solve_fast)
  | |- _ => rdn_hyp
  end.
Local Ltac rdn_solve ::= rdn_solve_fast.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.


(* [comment removed for export] *)
#[using="Type"] Lemma rz_emit_nil : forall c K, srealizes RSEGS scfg c K -> srealizes RSEGS scfg c (t_emit [] K).
Proof.
  intros c K H. eapply srz_conseq; [exact H|].
  apply t_eq_sym. apply t_emit_nil_eq. exact (srealizes_nonempty _ _ _ _ H).
Qed.

#[using="Type"] Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
  (k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.

#[using="Type"] Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
  (length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u_at_le : forall (b : word) (k : Z), (0 <= k)%Z -> (bv_unsigned b + k <= 2 ^ 64)%Z ->
  bv_unsigned (at_ b k) = (bv_unsigned b + k)%Z
  \/ (bv_unsigned (at_ b k) = 0 /\ bv_unsigned b + k = 2 ^ 64)%Z.
Proof.
  intros b k Hk Hle. unfold at_. pose proof (u64_range b).
  destruct (Z.eq_dec (bv_unsigned b + k) (2 ^ 64)) as [E|NE].
  - right. split; [|exact E]. rewrite E. vm_compute. reflexivity.
  - left. u_norm. reflexivity.
Qed.

Section Loop.
  Variables (su f fd : Z) (l bufp bufsz can ret : word).
  Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
  Variable mem1 : word -> option byte.
  Variable model : Model.
  Variable K : TSet.

  Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
  Hypothesis SUhi : (su <= 0x800000000000)%Z.
  Hypothesis Flo : (0xc6000 <= f)%Z.
  Hypothesis Fhi : (f + 232 <= 0xf8ac0)%Z.
  Hypothesis FD : (0 < fd < 2147483648)%Z.
  Hypothesis Hfd : fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  (* [comment removed for export] *)
  Hypothesis Hrdr : m_channel_reader model = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hret : ret_ok ret.
  Hypothesis HKnil : K [].
  Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
  Hypothesis M8  : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
  Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
  Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
  Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
  Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
  Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
  Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
  Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
  Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0xf8ac0) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
  Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
  Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).

  (* [comment removed for export] *)
  Definition LM (m : word -> option byte) : Prop :=
    (forall x : word, ~ (su - 104 <= bv_unsigned x < su - 72)%Z -> m x = mem1 x) /\ mem_grows mem1 m.

  (* [comment removed for export] *)
  Hypothesis HK : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = e8 -> getr regs' 9 = e9 ->
     getr regs' 18 = e18 -> getr regs' 19 = e19 -> getr regs' 20 = e20 ->
     getr regs' 21 = e21 -> getr regs' 22 = e22 -> getr regs' 23 = g23 ->
     getr regs' 24 = g24 -> getr regs' 25 = g25 -> getr regs' 26 = g26 ->
     getr regs' 27 = g27 -> getr regs' 3 = g3 -> getr regs' 4 = g4 ->
     LM m ->
     srealizes RSEGS scfg (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K.

  (* [comment removed for export] *)
  Definition RI (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (su - 112) /\ getr regs 8 = l /\ getr regs 9 = Z_to_bv 64 f
    /\ getr regs 21 = Z_to_bv 64 0xf8ac0 /\ getr regs 3 = g3 /\ getr regs 4 = g4
    /\ getr regs 23 = g23 /\ getr regs 24 = g24 /\ getr regs 25 = g25
    /\ getr regs 26 = g26 /\ getr regs 27 = g27.

  #[using="Type"] Lemma RI_but : forall regs regs', RI regs -> sw_regs_but regs regs' -> RI regs'.
  Proof.
    intros regs regs' (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27)
           (P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27).
    unfold RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. repeat split; assumption.
  Qed.

  #[using="Type"] Lemma LM_refl : LM mem1.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite ()) ["FPX_1"; "Loop"] "h01xp;1p;2p;3p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p100fbp6051000R0p100hfp4p710R1p8P0p100@jp4p710R2p8P0p100AJp4p710R3p8P0p1005>p4p710R0p8p100iEp6051000R4P1p8P4p1004`p4p710R1p8P4P2p8P4P3p8P4P0p8p1003_p4p710P1p8P0P1p8g00R1j10Tg00jLj13Tg00jjj12Tg00S9j11Tg00lTj15Tg00DPj24Tg00kMj2<Tg00GIj2;Tg00ISj2:Tg00Ioj27Tg00nfj16Tg01<7j18Tg00CVj39Tg01<Yj2@Tg00FJj2?Tg01=Wj1>Tg010Ej4=Tg00b\R1#0#0R0#0R4#0#0#0#3R3#2R2p,2suR5%11#0#1#0#0#0#5'4f0,<3R3';%10#0#0#0#5,45,:3'7#6R3%34#2#8R4p,4mem1R5f1O1R0;90[]01@551?40V3X02%>5C=o"). Qed.

  #[using="Type"] Lemma LM_rdn : forall m (a : word) n bs,
    LM m -> rdn RSEGS mem1 a n = Some bs ->
    (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    (bv_unsigned a + Z.of_nat n <= su - 104 \/ su - 72 <= bv_unsigned a)%Z ->
    rdn RSEGS m a n = Some bs.
  Proof.
    intros m a n bs [E G] H Hnw D.
    rewrite (rdn_ext RSEGS n m mem1 a Hnw); [exact H|].
    intros x Hx. apply E. lia.
  Qed.

  #[using="Type"] Lemma LM_store_ok : forall m (a : word) n,
    LM m -> store_ok RSEGS mem1 a n = true -> store_ok RSEGS m a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite ()) ["FPX_1"; "Loop"] "h01xh11Eh21Gh31Hh42H0h51ah61mh71np;1p;2p;3p;4p;7p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p100fbp6051000R0p100hfp4p710R1p8P0p100@jp4p710R2p8P0p100AJp4p710R3p8P0p1005>p4p710R0p8p100iEp6051000R4P1p8P4p1004`p4p710R1p8P4P2p8P4P3p8P4P0p8p1003_p4p710P1p8P0P1p8g00R1j10Tg00jLj19Tg00jjj16Tg01<7j1=Tg01>Zj1ATg00S9j11Tg00lTj17Tg00DPj25Tg00kMj2?Tg00GIj2>Tg00ISj2<Tg00IoR1j2;Tg00nfj1:Tg00CVj34Tg01<Yj28Tg01A_j43Tg01B_j7@Tg00ebf0R0g00fB34p=2g00b\R4#0#0R3#0R2#0#0#0#9R5#6R6%92#6#=R2[g00\Nf2R7#AP1p,2suR1%14#0#1#0#0#0#7'51?50R5'>%13#0#0#0#7,51,<5';#:R5f5R1f1R3O1p,4mem1R4P3O1R8542[^06f3R9,84g00=mR:P4P9P7C3#2P:P1f4P9C3#2[P0f7R9P3O1=428\5^06f6R5,84P:P4P5P1C3#2P:P5P4f8P9P3P0F@W3W2W1P3P0O2n2001000000120000000W4W7X56W6o"). Qed.

  #[using="SUlo SUhi"] Lemma LM_wbytes8 : forall m (a : Z) (v : word),
    LM m -> (su - 104 <= a)%Z -> (a + 8 <= su - 72)%Z ->
    LM (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
  Proof.
    intros m a v [E G] Hlo Hhi. split.
    - intros x Hx. rewrite wbytes_outside.
      + apply E, Hx.
      + unfold in_rng. rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
      + rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - eapply mem_grows_trans; [exact G | apply wbytes_grows].
  Qed.

  (* [comment removed for export] *)
  #[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK"] Lemma finish : forall regs m,
    RI regs -> LM m ->
    srealizes RSEGS scfg (mkCfg (mkst regs (0xae568 : word) m (seg_rom RSEGS)) model) K.
  Proof.
    intros regs m RIr LMm.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    destruct (sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)
      as (regs2 & RUN & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27);
      try assumption.
    all: try (eapply LM_rdn; [exact LMm | eassumption | u_norm; lia | u_norm; lia]).
    eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
    apply HK; try assumption.
    - rewrite Q23; exact R23.
    - rewrite Q24; exact R24.
    - rewrite Q25; exact R25.
    - rewrite Q26; exact R26.
    - rewrite Q27; exact R27.
    - rewrite Q3; exact R3.
    - rewrite Q4; exact R4.
  Qed.

  #[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK"] Lemma finish_nil : forall regs m,
    RI regs -> LM m ->
    srealizes RSEGS scfg (mkCfg (mkst regs (0xae568 : word) m (seg_rom RSEGS)) model) (t_emit [] K).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite ()) ["FPX_1"; "Loop"] "h01mh14regsp;1p;2p;3p;5p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p100fbp6051000R0p100hfp4p710R1p8P0p100@jp4p710R2p8P0p100AJp4p710R3p8P0p1005>p4p710R0p8p100iEp6051000R4P1p8P4p1004`p4p710R1p8P4P2p8P4P3p8P4P0p8p1003_p4p710P1p8P0P1p8g00R1j10Tg00S9j11Tg00jLj12Tg00jjj13Tg017Rj2>Tg01<7j1;Tg018>j1:Tg01>Zj15Tg00lTj16Tg01;8j37Tg01NHj14Tg01O=j58Tg01Vaj29Tg01WVj4=Tg01XWj3<Tg00b\R1#0R0#1#2%00#0R0#0#0#0#2R4#3R3'>%20#3#;\3f1R3#:%53p,2fxf3R0%01#1#0#1#1#1#0#0#1#0#1#0#1#1#0#1#0#0#0#6g01;[574f2R4g00=m#4D8p,5model'9p,1KP0P4P3f0C=3<UUW0W1o"). Qed.


  (* [comment removed for export] *)
  #[using="Type"] Lemma pc_ae55c : v_addi (0xae5e4 : word) 4 = (0xae5e8 : word).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite ()) ["FPX_1"; "Loop"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p100fbp6051000R0p100hfp4p710R1p8P0p100@jp4p710R2p8P0p100AJp4p710R3p8P0p1005>p4p710R0p8p100iEp6051000R4P1p8P4p1004`p4p710R1p8P4P2p8P4P3p8P4P0p8p1003_p4p710P1p8P0P1p8g00jjj14Tg00CVj31Tg00kMj22Tg01Y]j3<Tg00jLj1=Tg00R1j13Tg00lTj19Tg01;8j3:Tg01ZAj2;Tg00FJj2>Tg00S9j18Tf0R1#3#3p=6%81#3p=0%81#8p=7%31#8p=5g01[5R0%41R4f1R3#4R2g00Iof2R5#4?131g00\mR6f3R7/25127331R8[12531251516%47?153[R9f4#4?175\8A<531P1n2001000000120000000W1W0W2P9^12^04^20P1g00b\R1#6R0#6#6#=R4%31#0#7#0#5#5#7#0#5#6#9g01;[R25:4%90';R0%31#0#7#0#5#5#7#0#0#6#9R1=:42R21>6112401242516dO4b3o"). Qed.

  (* [comment removed for export] *)
  #[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK"] Lemma loop1 : forall n regs m (k : nat) (b : word) (bs : list byte),
    (length bs <= n)%nat ->
    RI regs -> LM m ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs)) ->
    getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 (su - 88) ->
    (1 <= k < length bs)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs)))) ->
    rdn RSEGS mem1 b (length bs) = Some bs ->
    (bv_unsigned b + Z.of_nat (length bs) <= su - 112 \/ su <= bv_unsigned b)%Z ->
    (bv_unsigned b + Z.of_nat (length bs) <= 2 ^ 47)%Z ->
    (Z.of_nat (length bs) <= 2 ^ 30)%Z ->
    srealizes RSEGS scfg (mkCfg (mkst regs (0xae5f4 : word) m (seg_rom RSEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K).
  Proof.
    induction n as [|n IH]; intros regs m k b bs LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b) as Hb.
    (* [comment removed for export] *)
    destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
                (Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
      as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
    { eapply LM_store_ok; [exact LMm | exact SOK1]. }
    { replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
    { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
    eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
    replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
    set (m' := wbytes (wbytes m _ _) _ _).
    assert (LMm' : LM m').
    { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
    assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
    (* [comment removed for export] *)
    eapply (rz_writev1_wallX RSEGS scfg regs1 (0xae5e4 : word) m' model W_ae5a8 fd
              (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
              (Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
      [ exact F_ae5a8 | exact E_ae5a8 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
      | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
    - subst m'. rdn_solve.
    - subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
    - rewrite word_to_nat_Z by lia.
      replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
      subst m'. repeat rdn_peel1.
      change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
      apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
      eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
    - unfold TASK_SIZE. u_norm. lia.
    - unfold TASK_SIZE. u_norm. lia.
    - u_norm. lia.
    - u_norm. lia.
    - (* [comment removed for export] *)
      intros k' K1 K2. rewrite pc_ae55c. rewrite length_skipn in K2.
      destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
      + (* [comment removed for export] *)
        destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite Q22. f_equal. lia. }
        { lia. }
        eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
        apply finish_nil; [| exact LMm'].
        eapply RI_but; [exact RI1|].
        revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      + (* [comment removed for export] *)
        destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                    (Z.of_nat (length bs) - Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact Q22. }
        { lia. }
        { lia. }
        { lia. }
        eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (IH regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs)).
        * rewrite length_skipn. lia.
        * eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * exact LMm'.
        * exact P10.
        * rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
        * rewrite P18. gres. exact Q18.
        * rewrite P19. gres. exact Q20.
        * rewrite length_skipn. lia.
        * subst m'. unfold at_. rdn_solve.
        * subst m'. rewrite length_skipn.
          replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
        * rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * rewrite length_skipn. lia.
  Qed.


  (* [comment removed for export] *)
  #[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK"] Lemma loop2 : forall n regs m (k : nat) (b0 : word) (bs0 : list byte) (b1 : word) (bs1 : list byte),
    (length bs0 + length bs1 <= n)%nat ->
    RI regs -> LM m ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs0) + Z.of_nat (length bs1)) ->
    getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 (su - 104) ->
    (1 <= k < length bs0 + length bs1)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 b0) ->
    rdn RSEGS m (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs0)))) ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b1) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs1)))) ->
    rdn RSEGS mem1 b0 (length bs0) = Some bs0 ->
    rdn RSEGS mem1 b1 (length bs1) = Some bs1 ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= su - 112 \/ su <= bv_unsigned b0)%Z ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= 2 ^ 47)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= su - 112 \/ su <= bv_unsigned b1)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= 2 ^ 47)%Z ->
    (Z.of_nat (length bs0) + Z.of_nat (length bs1) <= 2 ^ 30)%Z ->
    srealizes RSEGS scfg (mkCfg (mkst regs (0xae5f4 : word) m (seg_rom RSEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs0 ++ bs1))) K).
  Proof.
    induction n as [|n IH]; intros regs m k b0 bs0 b1 bs1 LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb
      Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
    destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
    - (* [comment removed for export] *)
      destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_le k bs0 bs1 LE).
      eapply (rz_writev2_wallX RSEGS scfg regs1 (0xae5e4 : word) m' model W_ae5a8 fd
                (Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
                (Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
                b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
        [ exact F_ae5a8 | exact E_ae5a8 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
      + subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
        destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
        { replace (length bs0 - k)%nat with 0%nat by lia.
          rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
        apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
      + rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
        subst m'. repeat rdn_peel1.
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2. rewrite pc_ae55c. rewrite length_app, length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
          apply finish_nil; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (IH regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
          -- subst m'. repeat rdn_peel1. exact Mb1.
          -- subst m'. repeat rdn_peel1. exact Mn1.
          -- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
          -- exact Bbs1.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- exact DISJ1.
          -- exact NW1.
          -- rewrite length_skipn. lia.
    - (* [comment removed for export] *)
      destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs1))
                  (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
      { replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
      replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
      replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_ge k bs0 bs1) by lia.
      eapply (rz_writev1_wallX RSEGS scfg regs1 (0xae5e4 : word) m' model W_ae5a8 fd
                (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
                (Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
                (skipn (k - length bs0) bs1) K);
        [ exact F_ae5a8 | exact E_ae5a8 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
        apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2. rewrite pc_ae55c. rewrite length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
          apply finish_nil; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (loop1 (length bs1) regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
             rdn_solve.
          -- rewrite length_skipn.
             apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- rewrite length_skipn. lia.
  Qed.

End Loop.
End FPX_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac wout1 :=
  rewrite wbytes_outside;
  [ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
    | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.


#[using="Type"] Lemma sw_post_of_LM : forall mem m (su f : Z) (ra s0 s1 s2 s3 s4 s5 s6 can : word) (wb n : Z) (s l bufp bufsz : word),
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0xc6000 <= f)%Z -> (f + 232 <= 0xf8ac0)%Z ->
  LM su (mem_sw1 mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l) m ->
  sw_post mem su f bufp bufsz (mem_sw2 m f bufp bufsz).
Proof.
  intros mem m su f ra s0 s1 s2 s3 s4 s5 s6 can wb n s l bufp bufsz SUlo SUhi Flo Fhi [E G].
  constructor.
  - intros x Hx1 Hx2 Hx3. pose proof (u64_range x) as Hx.
    unfold mem_sw2. do 3 wout1.
    rewrite (E x) by lia.
    unfold mem_sw1. do 13 wout1. reflexivity.
  - unfold mem_sw2. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    eapply mem_grows_trans; [|exact G].
    unfold mem_sw1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    apply mem_grows_refl.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
Qed.

#[using="Type"] Lemma pc_ae4d4 : v_addi (0xae55c : word) 4 = (0xae560 : word).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0StdioWrite ()) ["FPX_2"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p100fbp6051000R0p100hfp4p710R1p8P0p100@jp4p710R2p8P0p100AJp4p710R3p8P0p1005>p4p710R0p8p100iEp6051000R4P1p8P4p1004`p4p710R1p8P4P2p8P4P3p8P4P0p8p1003_p4p710P1p8P0P1p8g00jjj15Tg00CVj33Tg00kMj24Tg01Y]j3<Tg00jLj1=Tg00S9j12Tg00lTj17Tg01;8j39Tg01ZAj2;Tg00FJj2:Tg00R1j16Tf0R1#6#6p=1%61#2p=0%21#6p=8g01[5R0%51R4f1R3#5R2g00Iof2R5#5?331g00\mR6f3R7/45147333R8[14531451536%57?353[R9f4#5?375\8A<531P1n2001000000120000000W1W0W2P9^12^04^20P1g00b\R1#1R0#1#1#=R4%01#0#2#8#0#0#0#0#2#2#1#7g01;[R2594%70';R0%01#0#2#8#0#0#0#8#1#1#7R1=942R21:6114401442536dO4b3o"). Qed.

#[using="Type"] Theorem ref_stdio_write :
  forall regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0xc6000 <= f)%Z -> (f + 232 <= 0xf8ac0)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (0 <= wb <= wp)%Z -> (wp <= 2 ^ 47)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 2 ^ 47)%Z ->
  rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS mem s (length extra) = Some extra ->
  ret_ok ret ->
  K [] ->
  (forall regs' mem',
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     sw_post mem su f bufp bufsz mem' ->
     srealizes RSEGS scfg (mkCfg (mkst regs' ret mem' (seg_rom RSEGS)) model) K) ->
  srealizes RSEGS scfg (mkCfg (mkst regs (0xae4d4 : word) mem (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof.
  intros regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD Hfd Hrdr Hh Hlazy WBP WPhi
         LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
  pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
  pose proof SWF as SWF'. pose proof SSP as SSP'.
  destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
  { rewrite <- LENE. symmetry. apply u64_roundtrip'. }
  (* [comment removed for export] *)
  set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                       (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
  assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
  { subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
  assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0xf8ac0) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
  assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }
  (* [comment removed for export] *)
  assert (HK' : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     LM su mem1 m ->
     srealizes RSEGS scfg (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K).
  { intros. apply HK. all: try assumption.
    eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
    match goal with H : LM _ _ _ |- _ => exact H end. }
  pose proof (finish_nil scfg su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
  pose proof (loop1 scfg su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
  pose proof (loop2 scfg su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
  pose proof (LM_refl su mem1) as LM1.
  destruct (Z.eq_dec wb wp) as [EQ|NEQ].
  - (* [comment removed for export] *)
    destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
    subst wb.
    destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst _ _ ?M _) _) _ =>
      replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
    rewrite Z.sub_diag in M96.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    destruct extra as [|x0 extra'].
    + (* [comment removed for export] *)
      cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
      eapply (rz_writev1_zeroX RSEGS scfg regs1 (0xae55c : word) mem1 model W_ae520 fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
        [ exact F_ae520 | exact E_ae520 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | unfold TASK_SIZE; u_norm; lia | unfold TASK_SIZE; u_norm; lia | ].
      { u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
      rewrite pc_ae4d4.
      destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
        as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
      { gres. reflexivity. }
      { gres. rewrite R22. exact HlZ. }
      { lia. }
      eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
      apply FIN; [|exact LM1].
      eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
    + (* [comment removed for export] *)
      eapply (rz_writev1_wallX RSEGS scfg regs1 (0xae55c : word) mem1 model W_ae520 fd
                (Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
        [ exact F_ae520 | exact E_ae520 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | exact HKnil | ].
      * u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
      * unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
      * unfold TASK_SIZE. u_norm. lia.
      * unfold TASK_SIZE. u_norm. lia.
      * cbn [length] in LENE. lia.
      * lia.
      * intros k K1 K2. rewrite pc_ae4d4.
        destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
        -- destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. f_equal. lia. }
           { lia. }
           eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
           apply FIN; [|exact LM1].
           eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                       (Z.of_nat (length (x0 :: extra'))))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. reflexivity. }
           { lia. }
           { lia. }
           { lia. }
           eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           apply (L1 (length (x0 :: extra')) regs2 mem1 k s (x0 :: extra')); try lia.
           ++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
           ++ exact LM1.
           ++ exact P10.
           ++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
           ++ rewrite P18. gres. exact R18.
           ++ rewrite P19. gres. exact R19.
           ++ exact M88.
           ++ rewrite <- HlZ. exact M80.
           ++ exact Be.
  - (* [comment removed for export] *)
    destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1. fold mem1.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    eapply (rz_writev2_wallX RSEGS scfg regs1 (0xae55c : word) mem1 model W_ae520 fd
              (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
      [ exact F_ae520 | exact E_ae520 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
      | exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | exact HKnil | ].
    + u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
    + u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
    + u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
    + rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
    + unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
    + unfold TASK_SIZE. u_norm. lia.
    + unfold TASK_SIZE. u_norm. lia.
    + unfold TASK_SIZE. u_norm. lia.
    + u_norm. lia.
    + u_norm. lia.
    + intros k K1 K2. rewrite pc_ae4d4. rewrite length_app in K2.
      destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
      * destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite R22. f_equal. lia. }
        { lia. }
        eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
        apply FIN; [|exact LM1].
        eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      * destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                    (wp - wb + bv_unsigned l))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact R22. }
        { lia. }
        { lia. }
        { lia. }
        eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (L2 (length pending + length extra)%nat regs2 mem1 k (Z_to_bv 64 wb) pending s extra); try lia.
        -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- exact LM1.
        -- exact P10.
        -- rewrite P22. gres. rewrite R22. f_equal. lia.
        -- rewrite P18. gres. exact R18.
        -- rewrite P19. gres. exact R19.
        -- exact M104.
        -- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
        -- exact M88.
        -- rewrite <- HlZ. exact M80.
        -- exact Bp.
        -- exact Be.
        -- u_norm. lia.
        -- u_norm. lia.
Qed.
End FPX_2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Ns0StdioWrite.
From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.
Module Ns0LibStdioCall.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.SpecConsts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.LibKnowFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0ExitBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0StdioWrite.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Ns0LibStdioCall () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite<skipn_app_leC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite<skipn_app_geC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_01058SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5hi_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26erangeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib=SymExec2Sound4SX2S<erange_soundC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7compareC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indc59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall3inrC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib4Init5Logic3notC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes>Morphisms_Prop@not_iff_morphismc59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall8inr_specC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_SymmetricK69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbI47Corelib4Init5Logic2or00c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall9inr_falseC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula07C46Stdlib4Bool4Bool:orb_true_rC59OSSVerify5KrLib7Mh_0055<LibKnowFrame8kn_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055<LibKnowFrame=know_ok_frameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op205K47Corelib5Lists7ListDef6Forall02K47Corelib5Lists7ListDef6Forall01c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall;Forall_one'C1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List?Forall_flat_mapc59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall9kimg_cut1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=orb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List:Forall_appC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall8kimg_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00I69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall6u_lit0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX29split_litC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7add_0_lK69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_rC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr08C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I4ELinuxProcessSemantics5Riscv5Instr5aluop00I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics5Riscv5Instr5mulop00C59OSSVerify5KrLib7Mh_01056SymRun<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC59OSSVerify5KrLib7Mh_01059SymDriveX6kindexC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subI47Corelib4Init5Peano2le00K47Corelib4Init5Peano2le01C46Stdlib5Lists4List9nth_errorC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes8list_indI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z9mod_smallC69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK45stdpp9bitvector;definitions2bv01C46Stdlib9micromega;ZifyClasses9and_morphC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib5Lists7ListDef3nthc59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall8ridx_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC47Corelib4Init9Datatypes7nat_indC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List:length_seqC56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib7Mh_01058SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_spC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsc59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_01058SymDrive9junk_valsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_srC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall5sc_knC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall7sc_bufpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall8sc_bufszC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_0143<Ns0StdioDefs7sw_post00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCallCstdio_call_sound_frC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00i59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SC_KEPT : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Record stdio_res : Type := SCR_ {
  sc_f : Z;            (* [comment removed for export] *)
  sc_fd : Z;           (* [comment removed for export] *)
  sc_ret : Z;          (* [comment removed for export] *)
  sc_wb : expr;        (* [comment removed for export] *)
  sc_wp : expr;        (* [comment removed for export] *)
  sc_bufp : expr;      (* [comment removed for export] *)
  sc_bufsz : expr;     (* [comment removed for export] *)
  sc_s : expr;         (* [comment removed for export] *)
  sc_l : expr;         (* [comment removed for export] *)
  sc_sp : expr;        (* [comment removed for export] *)
  sc_sr : list expr;   (* [comment removed for export] *)
  sc_kn : list kentry  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition hi_ok (kn : list kentry) (e : expr) : bool :=
  match erange kn e with Some (_, hi) => Z.leb hi 0x800000000000 | None => false end.

Lemma hi_ok_sound : forall E M kn e, know_ok RSEGS E M kn -> hi_ok kn e = true ->
  (bv_unsigned (edenot E e) <= 0x800000000000)%Z.
Proof.
  intros E M kn e HK H. unfold hi_ok in H.
  destruct (erange kn e) as [[lo hi]|] eqn:He; [|discriminate].
  pose proof (erange_sound RSEGS E M kn e lo hi HK He). apply Z.leb_le in H. lia.
Qed.

Definition lit_even_ret (e : expr) : option Z :=
  match e with
  | ELit r => if ((r mod 2 =? 0) && (0 <=? r) && (r <? two64))%bool then Some r else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition kimg_cut1 (a n : Z) (K : kentry) : list kentry :=
  match K with
  | KImg lo hi =>
      if (Z.leb hi a || Z.leb (a + n) lo)%bool then [K]
      else (if Z.ltb lo a then [KImg lo a] else []) ++ (if Z.ltb (a + n) hi then [KImg (a + n) hi] else [])
  | _ => [K]
  end.
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := List.flat_map (kimg_cut1 a n) k.

Definition stdio_call (nv : nat) (sr : list expr) (kn : list kentry) : option stdio_res :=
  match nth 10 sr (ELit 0), lit_even_ret (nth 1 sr (ELit 0)) with
  | ELit f, Some ret =>
    match kread RSEGS kn (ELit 0) (f + 120) 4, kread RSEGS kn (ELit 0) (f + 40) 8, kread RSEGS kn (ELit 0) (f + 56) 8,
          kread RSEGS kn (ELit 0) (f + 88) 8, kread RSEGS kn (ELit 0) (f + 96) 8,
          kread RSEGS kn (ELit 0) 0xc5ab8 8, kblob_find kn (ELit 0) 0xf8ac0 with
    | Some (ELit fd), Some wp, Some wb, Some bufp, Some bufsz, Some (ELit cg), Some (clen, _) =>
      let sp := nth 2 sr (ELit 0) in
      let '(qb, k0) := split_lit sp in
      let qk := (k0 - 112)%Z in
      match kindex (is_kwr_cov qb qk 112) kn 0, base_range kn qb with
      | Some _, Some (blo, bhi) =>
        if ((0xc6000 <=? f) && (f + 232 <=? 0xf8ac0)
            && ((fd =? 1) || (fd =? 2)) && (cg mod two64 =? 0xf8ac0)
            && (4294967296 + 112 <=? blo + k0) && (bhi + k0 <=? 0x800000000000)
            && expr_eqb clen (ELit 8)
            && expr_vars_lt nv bufp && expr_vars_lt nv bufsz
            && sr_vars_lt nv sr && kn_vars_lt nv kn && Nat.eqb (length sr) 32)%bool
        then
          let k0 := kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8 in
          let k1 := kn_frame k0 qb qk 112 in
          let k2 := kn_frame k1 (ELit 0) (f + 32) 16 in
          let k3 := kn_frame k2 (ELit 0) (f + 56) 8 in
          Some (SCR_ f fd ret wb wp bufp bufsz (nth 11 sr (ELit 0)) (nth 12 sr (ELit 0)) sp
                     (sr_upd (sr_after_call_j sr SC_KEPT nv) 10 (nth 12 sr (ELit 0)))
                     (KWord (SA (ELit 0) (f + 32)) 8 (mkAlu ALU_ADD bufp bufsz)
                      :: KWord (SA (ELit 0) (f + 40)) 8 bufp
                      :: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3))
        else None
      | _, _ => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inr (lo n : Z) (x : word) : bool := (Z.leb lo (bv_unsigned x) && Z.ltb (bv_unsigned x) (lo + n))%bool.

Lemma inr_spec : forall lo n x, inr lo n x = true <-> (lo <= bv_unsigned x < lo + n)%Z.
Proof. intros lo n x. unfold inr. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Lemma inr_false : forall lo n x, inr lo n x = false <-> ~ (lo <= bv_unsigned x < lo + n)%Z.
Proof. intros lo n x. rewrite <- inr_spec. destruct (inr lo n x); split; congruence. Qed.

(* [comment removed for export] *)
Lemma know_ok_frame3 : forall E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3,
  know_ok RSEGS E M kn ->
  flat E (SA b1 o1) n1 -> flat E (SA b2 o2) n2 -> flat E (SA b3 o3) n3 ->
  (forall x : word,
     ~ (estart E (SA b1 o1) <= bv_unsigned x < estart E (SA b1 o1) + n1)%Z ->
     ~ (estart E (SA b2 o2) <= bv_unsigned x < estart E (SA b2 o2) + n2)%Z ->
     ~ (estart E (SA b3 o3) <= bv_unsigned x < estart E (SA b3 o3) + n3)%Z ->
     M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn b1 o1 n1) b2 o2 n2) b3 o3 n3).
Proof.
  intros E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3 HK F1 F2 F3 Hout Hg.
  set (a1 := estart E (SA b1 o1)) in *. set (a2 := estart E (SA b2 o2)) in *. set (a3 := estart E (SA b3 o3)) in *.
  set (M1 := fun x : word => if (inr a2 n2 x || inr a3 n3 x)%bool then M x else M' x).
  set (M2 := fun x : word => if inr a3 n3 x then M x else M' x).
  assert (O1 : forall x : word, (bv_unsigned x < a1 \/ a1 + n1 <= bv_unsigned x)%Z -> M1 x = M x).
  { intros x Hx. unfold M1. destruct (inr a2 n2 x) eqn:E2; [reflexivity|]. destruct (inr a3 n3 x) eqn:E3; [reflexivity|].
    cbn [orb]. apply inr_false in E2. apply inr_false in E3. apply Hout; [lia | exact E2 | exact E3]. }
  assert (G1 : mem_grows M M1).
  { intros x Hx. unfold M1. destruct (inr a2 n2 x || inr a3 n3 x)%bool; [exact Hx | exact (Hg x Hx)]. }
  assert (O2 : forall x : word, (bv_unsigned x < a2 \/ a2 + n2 <= bv_unsigned x)%Z -> M2 x = M1 x).
  { intros x Hx. unfold M1, M2. destruct (inr a3 n3 x) eqn:E3; [rewrite orb_true_r; reflexivity|].
    destruct (inr a2 n2 x) eqn:E2; [|reflexivity]. apply inr_spec in E2. lia. }
  assert (G2 : mem_grows M1 M2).
  { intros x Hx. unfold M1, M2 in *. destruct (inr a3 n3 x); [rewrite orb_true_r in Hx; exact Hx|].
    destruct (inr a2 n2 x); cbn [orb] in Hx; [exact (Hg x Hx) | exact Hx]. }
  assert (O3 : forall x : word, (bv_unsigned x < a3 \/ a3 + n3 <= bv_unsigned x)%Z -> M' x = M2 x).
  { intros x Hx. unfold M2. destruct (inr a3 n3 x) eqn:E3; [|reflexivity]. apply inr_spec in E3. lia. }
  assert (G3 : mem_grows M2 M').
  { intros x Hx. unfold M2 in Hx. destruct (inr a3 n3 x); [exact (Hg x Hx) | exact Hx]. }
  eapply know_ok_frame; [| exact F3 | exact O3 | exact G3].
  eapply know_ok_frame; [| exact F2 | exact O2 | exact G2].
  eapply know_ok_frame; [exact HK | exact F1 | exact O1 | exact G1].
Qed.

Lemma Forall_one' : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof. intros A P x H. constructor; [exact H | constructor]. Qed.

Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof.
  intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | |lo hi| | | |]; cbn [kimg_cut1]; try (apply Forall_one'; exact HKK).
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hap; [apply Forall_one'; exact HKK|].
  apply Bool.orb_false_iff in Hap as [Hap1 Hap2]. apply Z.leb_gt in Hap1. apply Z.leb_gt in Hap2.
  cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Himg).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:E1; [|constructor]. apply Z.ltb_lt in E1. apply Forall_one'. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
  - destruct (Z.ltb (a + n) hi) eqn:E2; [|constructor]. apply Z.ltb_lt in E2. apply Forall_one'. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
Qed.

Lemma u_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros E. cbn [edenot]. apply u64_lit. lia. Qed.

Lemma flat_abs0 : forall E off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z ->
  flat E (SA (ELit 0) off) n.
Proof. intros E off n H0 Hn Hnw Hlt. unfold flat, estart. cbn [a_base a_off]. rewrite u_lit0. lia. Qed.

Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
  intros E e b k H.
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_lit by lia. rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

Lemma split_lit_vars : forall n e b k, split_lit e = (b, k) -> expr_vars_lt n e = true -> expr_vars_lt n b = true.
Proof.
  intros n e b k H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; first [reflexivity | exact Hv]).
  lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; exact Hv).
  injection H as <- <-. cbn [expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

Lemma kindex_some : forall p kn i j, kindex p kn i = Some j ->
  exists K, nth_error kn (j - i) = Some K /\ p K = true /\ (i <= j)%nat.
Proof.
  intros p kn. induction kn as [|K rest IH]; intros i j H; cbn [kindex] in H; [discriminate|].
  destruct (p K) eqn:HP.
  - injection H as <-. exists K. rewrite Nat.sub_diag. cbn. auto.
  - destruct (IH (S i) j H) as (K' & Hn & HP' & Hle). exists K'.
    replace (j - i)%nat with (S (j - S i))%nat by lia. cbn [nth_error]. repeat split; try assumption. lia.
Qed.

Lemma ridx_lit : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sr_get_nat : forall sr n, (0 < n < 32)%nat -> sr_get sr (Z_to_bv 5 (Z.of_nat n)) = nth n sr (ELit 0).
Proof.
  intros sr n Hn. unfold sr_get.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz, ridx_lit by lia. reflexivity.
Qed.

Lemma length_sr_upd : forall sr n e, (n < length sr)%nat -> length (sr_upd sr n e) = length sr.
Proof.
  intros sr. induction sr as [|h t IH]; intros n e Hn; cbn [length] in Hn; [lia|].
  destruct n; cbn [sr_upd length]; [reflexivity|]. rewrite IH by lia. reflexivity.
Qed.

Lemma nth_sr_upd_same : forall sr n e, (n < length sr)%nat -> nth n (sr_upd sr n e) (ELit 0) = e.
Proof.
  intros sr. induction sr as [|h t IH]; intros n e Hn; cbn [length] in Hn; [lia|].
  destruct n; cbn [sr_upd nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_sr_upd_other : forall sr n m e, n <> m -> nth m (sr_upd sr n e) (ELit 0) = nth m sr (ELit 0).
Proof.
  intros sr. induction sr as [|h t IH]; intros n m e Hne.
  - revert m Hne. induction n as [|n IHn]; intros m Hne; cbn [sr_upd].
    + destruct m; [lia | destruct m; reflexivity].
    + destruct m; [reflexivity|]. cbn [nth]. rewrite IHn by lia. destruct m; reflexivity.
  - destruct n; destruct m; cbn [sr_upd nth]; try reflexivity; [lia|]. apply IH. lia.
Qed.

Lemma length_sr_after_call_j : forall sr kept nv, length (sr_after_call_j sr kept nv) = 32%nat.
Proof. intros. unfold sr_after_call_j. rewrite length_map, length_seq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem stdio_call_sound_fr :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z -> (wp <= 2 ^ 47)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 2 ^ 47)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     sw_post M su (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
     srealizes RSEGS scfg (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xae4d4) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K Hrdr E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0xc5ab8 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kblob_find kn (ELit 0) 0xf8ac0) as [[canlen canb]|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hwp47 Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hh Hlz HKnil HCONT.
  set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
  set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
  set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
  apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hclen].
  apply expr_eqb_eq in Hclen.
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
  apply andb_prop in Hcond as [Hf0 Hf232].
  apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
  (* [comment removed for export] *)
  assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
  { unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
    apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
  assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
  { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
  assert (R1 : getr R 1 = Z_to_bv 64 ret).
  { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
  assert (R10 : getr R 10 = Z_to_bv 64 f).
  { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    rewrite H10. reflexivity. }
  assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R11 : getr R 11 = s).
  { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R12 : getr R 12 = l).
  { replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
  set (sp := edenot E (nth 2 sr (ELit 0))) in *.
  pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
  pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
  assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
  { subst su. rewrite Hsqd. apply u64_lit. lia. }
  pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
  (* [comment removed for export] *)
  destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
  destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
  apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
  apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
  assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
  { unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
    replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C. apply flat_abs0; lia. }
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0xc5ab8 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kblob_find_sound RSEGS E M kn (ELit 0) 0xf8ac0 canlen canb HK Hcan) as Kcan.
  pose proof (kblob_rdn RSEGS E M kn (ELit 0) 0xf8ac0 canlen canb HK Hcan) as Rcan.
  assert (Lcan : length (eb E canb) = 8%nat).
  { cbn [kentry_ok] in Kcan. destruct Kcan as (_ & Hl & _). rewrite Hclen in Hl. unfold elenZ in Hl. cbn [edenot] in Hl.
    rewrite ?u64_lit, ?u_Z2bv in Hl by lia. lia. }
  set (canw := Z_to_bv 64 (bytes_le_to_Z (eb E canb))).
  rewrite Lcan, <- (word_to_le_bytes_of_lez 8 (eb E canb) Lcan ltac:(lia)) in Rcan. fold canw in Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0xae4d4) with (0xae4d4%bv : word) by (apply bv_eq; reflexivity).
  eapply (ref_stdio_write scfg R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) canw (Z_to_bv 64 ret)
            pending extra K).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst'.
  - lia.
  - lia.
  - constructor.
    + rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rfd. cbn [edenot]. reflexivity.
    + exact Rbufp.
    + exact Rbufsz.
  - split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
  - apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
  - exact Hfdlk.
  - exact Hrdr.
  - exact Hh.
  - exact Hlz.
  - lia.
  - exact Hwp47.
  - exact Hlenp.
  - exact Hlene.
  - exact H30.
  - exact Dw.
  - exact Ds.
  - exact Hsl.
  - exact Rpend.
  - exact Rextra.
  - apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
  - exact HKnil.
  - (* [comment removed for export] *)
    intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply HCONT.
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [lia|]);
            lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
              first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
            end.
        - unfold SC_KEPT. cbn [In]. lia. }
      apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
        [ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
      intros i Hi. rewrite length_sr_after_call_j in Hi.
      destruct (Nat.eq_dec i 10) as [->|Hne].
      * rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
        unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
        change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
        rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
        apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
      * rewrite nth_sr_upd_other by lia. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
      assert (HK3 : know_ok RSEGS E' M'
                (kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
                   (ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
      { assert (Eqb : edenot E' qb = edenot E qb).
        { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
          apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
        apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
        - unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
        - intros x N1 N2 N3. apply Pagree.
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
    + (* [comment removed for export] *) exact HPOST.
Qed.

(* [comment removed for export] *)
Theorem stdio_call_sound :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  (* [comment removed for export] *)
  m_channel_reader model = true ->
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z -> (wp <= 2 ^ 47)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 2 ^ 47)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     srealizes RSEGS scfg (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xae4d4) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K Hrdr E HR HK Hc wb wp s l su
         H1 H1' H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HCONT.
  apply (stdio_call_sound_fr vals ebs sr kn R M model res pending extra K Hrdr HR HK Hc); try assumption.
  intros R' M' A B C. apply HCONT; assumption.
Qed.

End FPX_1.
End Ns0LibStdioCall.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State. From LinuxProcessSemantics.Riscv Require Prelude Instr. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec.
Module Ns0Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0MainEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0LibStdioCall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.DrvKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS : list Z :=
  [0xb9978; 0xb9ef8; 0xba46c; 0xb987c; 0xa92d0; 0xae4d4; 0xab2b4; 0xab174; 0x390cc; 0x39084]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition kn_image_d : list kentry :=
  [KWr (SA (ELit 0) 0xc6000) 0x34000;
   KImg 0x10000 0xc6dd0;
   KImg 0xc6dd1 0xc6e19; KImg 0xd6e19 0xd8780; KImg 0xf8858 0xf8878;
   KWord (SA (ELit 0) 0xd8788) 8 (ELit 0xd8788);
   KWord (SA (ELit 0) 0xd87a8) 4 (EVar 5);
   KImg 0xd87b4 0xd8800; KImg 0xd8808 0xd8820; KWord (SA (ELit 0) 0xd8820) 8 (ELit 0xf8b18); KImg 0xd8828 0xd8840;
   KBlob (SA (ELit 0) 0xd8840) (ELit 8) 2;
   KImg 0xd8850 0xd8860; KImg 0xd8868 0xd88d8; KImg 0xf8890 0xf8ab8; KImg 0xf8ab8 0xf8ac0;
   KBlob (SA (ELit 0) 0xf8ac0) (ELit 8) 2;
   KImg 0xf8ac8 0xf8ad0;
   KImg 0xf8ae1 0xf8ae8; KWord (SA (ELit 0) 0xf8ae8) 8 (EVar 3);
   KImg 0xf8af0 0xf8af8; KImg 0xf8b08 0xf8b10; KWord (SA (ELit 0) 0xf8b10) 8 (ELit 4096);
   KImg 0xf8b18 0xf8b48; KBlob (SA (ELit 0) 0xf8b48) (ELit 8) 3; KImg 0xf8b50 0xf8c58; KImg 0xf9000 0xfa000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].
Definition kn_d0 : list kentry := kn_stack ++ kn_auxv ++ kn_image_d.

Lemma kn_d0_sub : ksubl_b kn_main kn_d0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x38c2c sr_main [] kn_d0 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_d0.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0xba924 srB0 [] knA 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_CLIENT : list (Z * Z) := [(0x10000, 0xd87ac); (0xd87b0, 0xf8c58); (0xf9000, 0xfa000)]%Z.
(* [comment removed for export] *)
Definition IMG_RW : list (Z * Z) := [(0xbf000, 0xc6000); (0xc6000, 0xfa000)]%Z.
(* [comment removed for export] *)
Definition keep_alloc (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.
(* [comment removed for export] *)
Definition MSO : Z := -128.
Definition keepB : list kentry := Eval vm_compute in keep_alloc MSO [] [] knB.
(* [comment removed for export] *)
Definition kn_blk (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0xea000 (SA (EVar v) 0) n].
Definition knC0 : list kentry := Eval vm_compute in kn_blk 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

(* [comment removed for export] *)
Lemma drv_itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xba920%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB), s_log (fst (fst rB))) = (0xab2b4%Z, [], [])
  /\ (nth 10 srB (ELit 0), nth 21 srB (ELit 0), nth 20 srB (ELit 0), nth 18 srB (ELit 0), nth 2 srB (ELit 0))
     = (ELit 65536, ELit 65536, ELit 3, EVar 2, EAlu ALU_ADD (EVar 0) (ELit MSO)).
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX_1.

End Ns0Drv_defs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.
Module Ns0DrvLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.DrvKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0MainEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Ns0DrvLib () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite<skipn_app_leC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_0143=Ns0StdioWrite<skipn_app_geC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_01058SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143?Ns0LibStdioCall;Forall_one'C1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init7Decimal4uint04K47Corelib4Init7Decimal4uint09K47Corelib4Init7Decimal4uint08K47Corelib4Init7Decimal4uint0:K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintC59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init7Decimal4uint01K47Corelib4Init7Decimal4uint0;K47Corelib4Init7Decimal4uint03C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00c59OSSVerify5KrLib7Mh_01439Ns0DrvLib2hzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib9dl_img_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib9dl_img_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib8dl_sptopC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init5Logic6eq_indC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic3and01I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib7Mh_01439Ns0DrvLib9sub_blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2Inc59OSSVerify5KrLib7Mh_01439Ns0DrvLibAhz_of_block_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib6hz_subC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init5Logic2ex00K46Stdlib9micromega=RingMicromega3Op205I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2or02K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00c59OSSVerify5KrLib7Mh_0143;Ns0Drv_defs6c_keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface@callee_saved_idxC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notI47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_00556DrvKit:kentry_eqbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List>existsb_existsI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib7Mh_00556DrvKit=kentry_eqb_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<In_nth_errorI69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib7Mh_01439Ns0DrvLib=has_entry_nthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib:has_windowC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3oppc59OSSVerify5KrLib7Mh_01439Ns0DrvLib>has_window_nthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8stack_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib8dl_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7hl_segsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7add_modK46Stdlib9micromega7EnvRing5PExpr06c59OSSVerify5KrLib7Mh_01439Ns0DrvLib7dl_segsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143;Ns0Drv_defs6kn_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib7Mh_00556DrvKit7find_nzC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltc59OSSVerify5KrLib7Mh_01439Ns0DrvLib5dl_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;hl_alloc_roC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib9dl_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib2CWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22evC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib<sub_block_hzC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z7compareK59OSSVerify5KrLib7Mh_00556DrvKit:regions_ok01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith4Znat5Nat2Z6inj_ltc59OSSVerify5KrLib7Mh_01439Ns0DrvLib5IMG_WC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03C59OSSVerify5KrLib7Mh_00556DrvKit8log_in_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=alloc_privateC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib=regions_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00556DrvKitAmem_denot_frame_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S?mem_denot_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hio_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib5CPstkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib;regions_stkC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib>mem_heap_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6hio_wfC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC59OSSVerify5KrLib=SymExec2Sound4SX2S:wbytes_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib5CPoutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLibBregions_blockwriteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00556DrvKit9kn_keep_gC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00556DrvKitAknow_keep_g_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143;Ns0Drv_defs:IMG_CLIENTC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143;Ns0Drv_defs6IMG_RWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3nthC47Corelib4Init3Nat3addC59OSSVerify5KrLib7Mh_01059SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib7Mh_00849HeapIface9credit_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC59OSSVerify5KrLib7Mh_01058SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0143;Ns0Drv_defs:keep_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface5debitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface:hio_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface5hl_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>heap_pres_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_mallocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib9dl_mallocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib5dl_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLibBstack_ok_of_windowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib7Mh_01439Ns0DrvLib<vals_ev_junkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLibCregs_preserved_keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appc59OSSVerify5KrLib7Mh_01439Ns0DrvLib9kn_blk_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00556DrvKit7kn_keepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib3CPmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib3SCmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib=regions_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00556DrvKit?know_keep_soundC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_errnoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib8dl_errnoC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C46Stdlib9micromega;ZifyClasses6mkapp2C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib:c_kept_no0C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib7Mh_00849HeapIface8hio_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9heap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7hl_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01439Ns0DrvLib7dl_freeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes8list_ind".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Record drv_layout (L : heap_layout) (sp0 : word) : Prop := DRV_LAYOUT {
  dl_segs : hl_segs L = RSEGS;
  dl_malloc : hl_malloc L = 0xab2b4;
  dl_free : hl_free L = 0xab174;
  dl_tp : hl_tp L = 0xd8850;
  dl_img_lo : hl_img_lo L = 0x10000;
  dl_img_hi : hl_img_hi L = 0xfa000;
  dl_static : forall a, hl_alloc_static L a -> 0xf8c58 <= a < 0xf9000;
  dl_ro : forall a, hl_alloc_ro L a -> (0x10000 <= a < 0xc6000) \/ (0xf8ac0 <= a < 0xf8ac8) \/ (0xf8ae0 <= a < 0xf8c58) \/ (0xf9000 <= a < 0xf9008) \/ (0xf9444 <= a < 0xf9448) \/ bv_unsigned sp0 <= a;      (* [comment removed for export] *)
  dl_errno : hl_errno L = 0xd87ac;
  dl_sptop : hl_sptop L = bv_unsigned sp0;
  dl_stack : 0 <= hl_stack L <= 16384;
  dl_k : 0 <= hl_k_per_malloc L;
  dl_b : 0 <= hl_b_overhead L
}.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.
Section DrvLayout.
  Variable L : heap_layout.
  Variable HI : heap_iface.
  Hypothesis HIok : heap_iface_ok L scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layout L sp0.

  (* [comment removed for export] *)
  Lemma wseg_6a8b4 : wseg_ok RSEGS (Z_to_bv 64 0xbf000) 28672 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0DrvLib ()) ["FPX_1"; "DrvLayout"] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p6051000R0p1004fp4p710R1p8P0p1005Ep4p710R2p8P0p1005ep4p710R3p8P0p1006Bp4p710R0p8p1006ap6051000R4P1p8P4p1007hp4p710R1p8P4P2p8P4P3p8P4P0p8p1008Fp4p710P1p8p1009Gp6051001p100:Op4p710p8P0P1p8g00;0j2>Tg00;Jj12Tg00;oj14Tg00<Mj11Tg00=2j1;Tg00=Pj2:Tg00>6j13Tg00>Tj15Tg00?2j16Tg00?Pj17Tg00?nj18Tg00@Kj19Tg00@jj3=Tg00Ahj3<Tf0#2#2p=0g00BBR1g00BbR0'>g00CBg00Dk#2R4#2#0#0#4%14#1#1#1#1#1#0#0#0#0#0#0#;':g00EP#3#5#6#7#3#8#93==<10do"). Qed.
  Lemma wseg_6f8b4 : wseg_ok RSEGS (Z_to_bv 64 0xc6000) 212992 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0DrvLib ()) ["FPX_1"; "DrvLayout"] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p70p1003Cp4p7210p8p1003_p6051000R0p1004fp4p710R1p8P0p1005Ep4p710R2p8P0p1005ep4p710R3p8P0p1006Bp4p710R0p8p1006ap6051000R4P1p8P4p1007hp4p710R1p8P4P2p8P4P3p8P4P0p8p1008Fp4p710P1p8p1009Gp6051001p100:Op4p710p8P0P1p8g00;0j2=Tg00;oj16Tg00<Mj12Tg00;Jj11Tg00=2j1;Tg00=Pj2:Tg00>6j13Tg00Enj14Tg00FLj17Tg00?nj15Tg00@Kj18Tg00@jj39Tg00Ahj3<Tf0#1#1p=0g00BBR1g00BbR0'=g00CBg00DkR4#0#0#0#6%24#1#0#2#2#1#0#0#0#0#0#0#;':g00EP#3#4#4#3#7#3#5#839=<10do"). Qed.

  (* [comment removed for export] *)
  Definition CPm (LB : list (Z * Z)) (sp : Z) (a : Z) : Prop := client_addr L LB sp (hl_stack L) a /\ ~ in_errno L a.
  Definition SCm (sp : Z) (a : Z) : Prop := sp - hl_stack L <= a < sp.

  (* [comment removed for export] *)
  Definition sub_block (LB : list (Z * Z)) (A nb : Z) : Prop :=
    exists cap, 0 < nb <= cap /\ In (A, cap) LB /\ block_range L A cap.

  (* [comment removed for export] *)
  Definition hz (A n : Z) : Prop := 4096 <= A /\ (A + n <= 0x10000 \/ 0xfa000 <= A) /\ A + n <= bv_unsigned sp0 - 8388608.

  Lemma hz_of_block_range : forall A n, block_range L A n -> hz A n.
  Proof.
    clear Hsp Hal. intros A n (B1 & B2 & B3 & B4 & B5). pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    pose proof (dl_sptop L sp0 DL) as TOP. unfold hz. rewrite IL, IH in B2. rewrite TOP in B5. repeat split; try lia.
  Qed.

  Lemma hz_sub : forall A n a m, hz A n -> A <= a -> 0 <= m -> a + m <= A + n -> hz a m.
  Proof. clear Hsp Hal. intros A n a m (H1 & H2 & H3) Ha Hm Ham. unfold hz. lia. Qed.

  Lemma sub_block_hz : forall LB A nb, sub_block LB A nb -> hz A nb.
  Proof.
    clear Hsp Hal. intros LB A nb (cap & Hnb & _ & HB). apply hz_of_block_range in HB. eapply hz_sub; [exact HB | lia | lia | lia].
  Qed.

  Lemma regions_alloc : forall vals ebs so bls vbnd LB,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    - 2 ^ 22 <= so <= 0 ->
    (forall i nb, find_nz i bls = Some nb -> sub_block LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> bv_unsigned (vals_ev vals v) <= b) ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    regions_ok RSEGS 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW E
               (CPm LB (bv_unsigned sp0 + so)) (SCm (bv_unsigned sp0 + so)).
  Proof.
    intros vals ebs so bls vbnd LB E P0 Hso Hbl Hvb Hhi.
    pose proof (dl_stack L sp0 DL) as ST. pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    pose proof (dl_errno L sp0 DL) as ER. pose proof (dl_sptop L sp0 DL) as TOP.
    assert (NE : forall a, 0xd87b0 <= a \/ a < 0xd87ac -> ~ in_errno L a) by (intros a Ha; unfold in_errno; rewrite ER; lia).
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
    - intros z Hz. destruct (Z.lt_ge_cases (bv_unsigned sp0 + z) (bv_unsigned sp0 + so - hl_stack L)) as [A|A].
      + left. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
      + right. unfold SCm. lia.
    - intros i nb Hf. pose proof (sub_block_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
      destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
      split; [lia|].
      intros z Hz. unfold CPm, client_addr.
      split; [left; exists (bv_unsigned (vals_ev vals i), cap); split; [exact Hin|]; cbn [fst snd]; lia | apply NE; lia].
    - exact Hvb.
    - intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
      intros z Hz. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
    - intros lo hi Hin. unfold IMG_CLIENT in Hin.
      destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]);
        intros a Ha; unfold CPm, client_addr; (split; [| apply NE; lia]); right; right; rewrite IL, IH; (split; [lia|]);
        intros Hs; apply (dl_static L sp0 DL) in Hs; lia.
    - intros lo hi Hin. unfold IMG_RW in Hin.
      destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xbf000) _ 28672%nat m 0xbf000 0xc6000);
          [reflexivity | reflexivity | lia | exact wseg_6a8b4 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xc6000) _ 212992%nat m 0xc6000 0xfa000);
          [reflexivity | reflexivity | lia | exact wseg_6f8b4 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma regs_preserved_kept : forall R R', regs_preserved R R' -> forall r : reg, In r c_kept -> getr R' r = getr R r.
  Proof.
    intros R R' HP r Hr. apply HP. unfold c_kept in Hr. unfold callee_saved_idx.
    repeat (destruct Hr as [<-|Hr]; [cbn; tauto|]). destruct Hr.
  Qed.

  Lemma c_kept_no0 : ~ In (0%bv : reg) c_kept.
  Proof. unfold c_kept. intros H. repeat (destruct H as [H|H]; [discriminate|]). exact H. Qed.

  (* [comment removed for export] *)
  Lemma has_entry_nth : forall kn K, existsb (kentry_eqb K) kn = true -> exists i, nth_error kn i = Some K.
  Proof.
    intros kn K H. apply existsb_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'.
    apply In_nth_error in Hin. exact Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma block_store_ok : forall vals ebs M kn v n (A : Z) (k : Z) (m : nat),
    let E := Env (vals_ev vals) ebs in
    know_ok RSEGS E M kn -> existsb (kentry_eqb (KWr (SA (EVar v) 0) n)) kn = true ->
    vals_ev vals v = Z_to_bv 64 A -> (0 <= A)%Z -> (A < 2 ^ 64)%Z ->
    (0 <= k)%Z -> (k + Z.of_nat m <= n)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (A + k)) m = true.
  Proof.
    intros vals ebs M kn v n A k m E HK Hhas Pv HA HAn Hk Hm.
    destruct (has_entry_nth kn _ Hhas) as [i Hi].
    pose proof (kwr_store_ok RSEGS E M kn i (EVar v) 0 n k m HK Hi Hk Hm) as W.
    unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite Pv in W. unfold v_addi in W.
    rewrite u_small in W by lia. exact W.
  Qed.

  (* [comment removed for export] *)
  Definition has_window (kn : list kentry) : bool := existsb (kentry_eqb (KWr (SA (EVar 0) (- DRV_ZWIN)) DRV_ZWIN)) kn.

  Lemma has_window_nth : forall kn, has_window kn = true -> exists i, nth_error kn i = Some (KWr (SA (EVar 0) (- DRV_ZWIN)) DRV_ZWIN).
  Proof.
    intros kn H. unfold has_window in H. apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    apply In_nth_error in Hin. exact Hin.
  Qed.

  Lemma stack_ok_of_window : forall vals ebs M kn so,
    let E := Env (vals_ev vals) ebs in
    know_ok RSEGS E M kn -> has_window kn = true ->
    vals_ev vals 0 = sp0 ->
    - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    stack_ok L M (bv_unsigned sp0 + so).
  Proof.
    intros vals ebs M kn so E HK Hw P0 Hso Hsoal. destruct (has_window_nth kn Hw) as [i Hn]. pose proof (dl_stack L sp0 DL) as ST.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'. pose proof (dl_sptop L sp0 DL) as TOP.
    unfold stack_ok. rewrite TOP. split; [|split; [lia|split; [lia|split; [lia|]]]].
    { rewrite Z.add_mod, Hal, Hsoal by lia. reflexivity. }
    intros d m Hd Hm.
    (* [comment removed for export] *)
    pose proof (kwr_store_ok RSEGS E M kn i (EVar 0) (- DRV_ZWIN) DRV_ZWIN (so - hl_stack L + d) m HK Hn ltac:(lia) ltac:(lia)) as W.
    unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W.
    rewrite (dl_segs L sp0 DL).
    replace (bv_unsigned sp0 + so - hl_stack L + d) with (bv_unsigned sp0 + (so - hl_stack L + d)) by lia. exact W.
  Qed.

  (* [comment removed for export] *)
  Lemma kn_blk_ok : forall vals ebs M' v n A,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals v = Z_to_bv 64 A -> vals_ev vals 0 = sp0 ->
    block_range L A n -> defined M' A n ->
    know_ok RSEGS E M' (kn_blk v n).
  Proof.
    intros vals ebs M' v n A E Pv P0 HBR Hdef. pose proof HBR as (_ & _ & B2 & B3 & _).
    pose proof (hz_of_block_range _ _ HBR) as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
    assert (EA : bv_unsigned (edenot E (EVar v)) = A) by (cbn [edenot ev E]; rewrite Pv; apply u_small; lia).
    unfold kn_blk, know_ok.
    apply Forall_cons. { cbn [kentry_ok]. rewrite EA. lia. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite EA. split; [lia | exact B2]. }
    apply Forall_cons.
    { cbn [kentry_ok]. split. { unfold flat, estart. cbn [a_base a_off]. rewrite EA. lia. }
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. rewrite EA.
      destruct m as [|m']; [reflexivity|]. set (m := S m') in *.
      apply store_ok_of_all; [rewrite u_small by lia; lia|].
      intros x Hx. rewrite u_small in Hx by lia.
      specialize (Hdef (bv_unsigned x - A) ltac:(lia)). replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in Hdef by lia.
      rewrite Z_to_bv_bv_unsigned in Hdef. unfold wview. destruct (M' x); [discriminate | exfalso; apply Hdef; reflexivity]. }
    apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E]. rewrite P0.
                         change (ev E v) with (vals_ev vals v). rewrite Pv, u_small by lia. right. lia. }
    apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E].
                         change (ev E v) with (vals_ev vals v). rewrite Pv, !u_small by lia. lia. }
    apply Forall_nil.
  Qed.


  (* [comment removed for export] *)
  Definition IMG_W : list (Z * Z) := [(0xc6000, 0xf8ac0); (0xf8ac8, 0xf8ae0); (0xf9018, 0xf9444); (0xf9448, 0xfa000)]%Z.      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition CW (LB : list (Z * Z)) (a : Z) : Prop := ~ alloc_private L LB a.

  Lemma regions_write : forall vals ebs bls LB,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block LB (bv_unsigned (vals_ev vals i)) nb) ->
    regions_ok RSEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W [] E (CW LB) (fun _ => True).
  Proof.
    intros vals ebs bls LB E P0 Hbl.
    pose proof (dl_stack L sp0 DL) as ST. pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    pose proof (dl_sptop L sp0 DL) as TOP.
    assert (RO := dl_ro L sp0 DL). assert (STA := dl_static L sp0 DL).
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - (* [comment removed for export] *) intros z Hz Hnot. unfold CW, alloc_private. intros [[A _]|A]; [rewrite TOP in A; lia|].
      apply RO in A. lia.
    - intros z Hz. right. exact I.
    - intros i nb Hf. destruct (Hbl i nb Hf) as (Hi & HSB). pose proof (sub_block_hz _ _ _ HSB) as (Z1 & Z2 & Z3).
      destruct HSB as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
      split; [lia|]. intros z Hz. unfold CW, alloc_private. intros [[_ [A _]]|A].
      + apply A. exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia.
      + apply RO in A. lia.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. unfold IMG_W in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]);
        intros a Ha; unfold CW, alloc_private; intros [[_ [_ A]]|A];
        [ apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
        | apply RO in A; lia
        | apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
        | apply RO in A; lia
        | apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
        | apply RO in A; lia
        | apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
        | apply RO in A; lia ].
    - intros lo hi [].
  Qed.

  (* [comment removed for export] *)
  Lemma heap_block : forall vals ebs bls LB cr M VM log,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block LB (bv_unsigned (vals_ev vals i)) nb) ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) bls [] IMG_W log = true ->
    hi_heap HI LB cr M VM -> hi_heap HI LB cr (mem_denot E M log) VM.
  Proof.
    intros vals ebs bls LB cr M VM log E P0 Hbl Hlog HH.
    apply (hio_frame L scfg HI HIok LB cr M (mem_denot E M log) VM HH).
    - intros a Ha Hp. apply (mem_denot_frame_Z RSEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W E (CW LB) (fun _ => True) []
                               (regions_write vals ebs bls LB P0 Hbl) M log a Hlog Ha).
      unfold CW. tauto.
    - intros x Hx. exact (mem_denot_grows E M log x Hx).
  Qed.


  (* [comment removed for export] *)
  Definition CPstk (a : Z) : Prop := a < 4096 \/ (0x10000 <= a < 0xfa000) \/ bv_unsigned sp0 - 8388608 <= a.

  Lemma regions_stk : forall vals ebs,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    regions_ok RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_W [] E CPstk (fun _ => True).
  Proof.
    intros vals ebs E P0.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPstk. lia.
    - intros z Hz. right. exact I.
    - intros i nb Hf. discriminate.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. unfold IMG_W in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPstk; lia.
    - intros lo hi [].
  Qed.

  Lemma mem_heap_frame : forall vals ebs M log (a : Z),
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W log = true ->
    hz a 1 ->
    mem_denot E M log (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof.
    intros vals ebs M log a E P0 Hlog (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
    apply (mem_denot_frame_Z RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_W E CPstk (fun _ => True) [] (regions_stk vals ebs P0) M log a Hlog).
    - lia.
    - unfold CPstk. lia.
  Qed.

  Lemma rdn_heap_frame : forall vals ebs M log (a : Z) (n : nat),
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W log = true ->
    hz a (Z.of_nat n) ->
    rdn RSEGS (mem_denot E M log) (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n.
  Proof.
    intros vals ebs M log a n E P0 Hlog HZ. pose proof HZ as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
    apply rdn_agree. intros j Hj. rewrite u_small by lia.
    apply (mem_heap_frame vals ebs M log); [exact P0 | exact Hlog | eapply hz_sub; [exact HZ| lia | lia | lia]].
  Qed.

  (* [comment removed for export] *)
  Lemma heap_wbytes : forall LB cr M VM (A n a : Z) bs,
    hi_heap HI LB cr M VM -> In (A, n) LB -> A <= a -> a + Z.of_nat (length bs) <= A + n -> A + n <= 2 ^ 64 ->
    hi_heap HI LB cr (wbytes M (Z_to_bv 64 a) bs) VM.
  Proof.
    intros LB cr M VM A n a bs HH Hin H1 H2 H3.
    destruct (hio_wf L scfg HI HIok LB cr M VM HH) as [WF _]. destruct (WF _ Hin) as (HBR & _ & _). cbn [fst snd] in *.
    pose proof (hz_of_block_range _ _ HBR) as (Z1 & Z2 & Z3).
    apply (hio_frame L scfg HI HIok LB cr M _ VM HH).
    - intros x Hx Hp. apply wbytes_out; [rewrite u_small by lia; lia|]. rewrite !u_small by lia.
      destruct (Z.lt_ge_cases x a) as [Hlt|Hge]; [left; exact Hlt|]. right.
      destruct (Z.lt_ge_cases x (a + Z.of_nat (length bs))) as [Hlt2|Hge2]; [|exact Hge2].
      exfalso. destruct Hp as [[_ [Hnb _]]|Hro].
      + apply Hnb. exists (A, n). split; [exact Hin|]. cbn [fst snd]. lia.
      + apply (dl_ro L sp0 DL) in Hro. pose proof Hsp. lia.
    - intros x Hx. exact (wbytes_grows bs M (Z_to_bv 64 a) x Hx).
  Qed.


  (* [comment removed for export] *)
  Definition CPout (A n : Z) (a : Z) : Prop := ~ (A <= a < A + n).

  Lemma regions_blockwrite : forall vals ebs A n,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 -> hz A n ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    regions_ok RSEGS 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW E (CPout A n) (fun _ => False).
  Proof.
    intros vals ebs A n E P0 (Z1 & Z2 & Z3) Hhi. pose proof Hsp as Hsp'.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPout. lia.
    - intros z Hz. exfalso. lia.
    - intros i nb Hf. discriminate.
    - intros v b Hf. discriminate.
    - intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. intros z Hz. unfold CPout. lia.
    - intros lo hi Hin. unfold IMG_CLIENT in Hin.
      destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPout; lia.
    - intros lo hi Hin. unfold IMG_RW in Hin.
      destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xbf000) _ 28672%nat m 0xbf000 0xc6000);
          [reflexivity | reflexivity | lia | exact wseg_6a8b4 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xc6000) _ 212992%nat m 0xc6000 0xfa000);
          [reflexivity | reflexivity | lia | exact wseg_6f8b4 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.

  Lemma know_blockwrite : forall vals ebs M (A n a : Z) bs kn,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 -> hz A n -> A <= a -> a + Z.of_nat (length bs) <= A + n ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    know_ok RSEGS E M kn ->
    know_ok RSEGS E (wbytes M (Z_to_bv 64 a) bs) (kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW kn).
  Proof.
    intros vals ebs M A n a bs kn E P0 HZ Ha Hbs Hhi HK. pose proof HZ as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
    eapply (know_keep_g_sound RSEGS 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW E (CPout A n) (fun _ => False)
              (regions_blockwrite vals ebs A n P0 HZ Hhi) M).
    - intros x Hx Hout. unfold CPout in Hout. apply wbytes_out; rewrite ?u_small by lia; [lia|lia].
    - intros x [].
    - apply wbytes_grows.
    - exact HK.
  Qed.

  Lemma vals_ev_junk : forall vals R' i, (i < 32)%nat ->
    vals_ev (vals ++ junk_vals R') (length vals + i) = getr R' (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros vals R' i Hi. rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite nth_map_seq by exact Hi. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma malloc_site : forall vals ebs sr kn R M (model : Model) LB cr n so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok RSEGS E M kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (5 <= length vals)%nat ->
    vals_ev vals 0 = sp0 ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10 = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 -> credit_ok L cr n ->
    getr R 4 = Z_to_bv 64 0xd8850 -> getr R 1 = Z_to_bv 64 ra -> (0 <= ra < 2 ^ 64)%Z -> (ra mod 2 = 0)%Z ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model) (A : Z),
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       vals_ev vals' (length vals + 10) = Z_to_bv 64 A ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok RSEGS E' M' (kn_blk (length vals + 10) n ++ keep_alloc so bls vbnd kn) ->
       hi_heap HI ((A, n) :: LB) (debit L cr n) M' (m_vmmaps model') ->
       model_but_vm model model' -> block_range L A n -> blocks_apart A n LB ->
       (forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M' x = M x) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0x10000 <= a < 0xfa000 -> ~ (0xf8c58 <= a < 0xf9000) -> ~ (0xd87ac <= a < 0xd87b0) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes RSEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom RSEGS)) model') K) ->
    srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xab2b4) M (seg_rom RSEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB cr n so bls vbnd ra K E HR HK Hsv Hkv HL5 P0 Hhi Hiw
           R2 Hso Hsoal R10 Hn Hcr R4 R1 Hra Hra2 HH Hh Hlz Hmt Hbl Hvb HK0 CONT.
    pose proof (hio_malloc L scfg HI HIok fx R M model LB cr n K) as MS.
    rewrite (dl_segs L sp0 DL), (dl_malloc L sp0 DL), (dl_tp L sp0 DL) in MS.
    rewrite R1 in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) apply ret_ok_even. rewrite u_small by lia. exact Hra2.
    - (* [comment removed for export] *) rewrite R2, u_small by lia. eapply stack_ok_of_window; eassumption.
    - intros R' M' model' A HA HP HBR HAP HDEF HPRES HBUT HH'.
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (HA' : vals_ev (vals ++ junk_vals R') (length vals + 10) = Z_to_bv 64 A).
      { rewrite vals_ev_junk by lia. exact HA. }
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0).
      { rewrite vals_ev_app_l by lia. exact P0. }
      apply (CONT R' M' model' A HL' HA').
      + (* [comment removed for export] *) apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_kept R R' HP) c_kept_no0).
      + (* [comment removed for export] *) apply Forall_app. split.
        * eapply kn_blk_ok; [exact HA' | exact P0' | exact HBR | exact HDEF].
        * unfold keep_alloc.
          pose proof (env_app_know RSEGS vals (junk_vals R') ebs M kn Hkv HK) as HK1.
          destruct HPRES as (PR1 & PR2).
          eapply (know_keep_sound RSEGS 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW
                    (Env (vals_ev (vals ++ junk_vals R')) ebs) (CPm LB (bv_unsigned sp0 + so)) (SCm (bv_unsigned sp0 + so))).
          -- apply regions_alloc; try assumption.
             ++ intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1).
                rewrite vals_ev_app_l by exact Hi32. exact H1.
             ++ intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
             ++ intros i Hi. rewrite vals_ev_app_l; [apply Hhi; exact Hi|]. destruct Hi as [<-|[<-|[]]]; lia.
          -- intros a Ha [HC HE]. rewrite R2, u_small in PR1 by lia. apply PR1; assumption.
          -- intros a HS. rewrite R2, u_small in PR2 by lia. apply PR2. exact HS.
          -- exact HK1.
      + exact HH'.
      + exact HBUT.
      + exact HBR.
      + exact HAP.
      + intros x Hx. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia.
        rewrite <- (Z_to_bv_bv_unsigned 64 x). apply PR1.
        * pose proof (u64_range x). lia.
        * unfold client_addr. right. left. rewrite (dl_sptop L sp0 DL).
          pose proof (u64_range x). pose proof (dl_stack L sp0 DL). lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hb. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia. apply PR1; [exact Ha | left; exact Hb |].
        destruct Hb as (b & Hbin & Hr). destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
        destruct (WF b Hbin) as (HBRb & _ & _). pose proof (hz_of_block_range _ _ HBRb) as (Y1 & Y2 & Y3).
        unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hs He. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia. apply PR1; [lia | |].
        * unfold client_addr. right. right. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|].
          intros Hst. apply (dl_static L sp0 DL) in Hst. lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma free_site : forall vals ebs sr kn R M (model : Model) LB cr (A n : Z) so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok RSEGS E M kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (5 <= length vals)%nat ->
    vals_ev vals 0 = sp0 ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    In (A, n) LB -> getr R 10 = Z_to_bv 64 A ->
    getr R 4 = Z_to_bv 64 0xd8850 -> getr R 1 = Z_to_bv 64 ra -> (0 <= ra < 2 ^ 64)%Z -> (ra mod 2 = 0)%Z ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block (lb_remove A LB) (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model),
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok RSEGS E' M' (keep_alloc so bls vbnd kn) ->
       hi_heap HI (lb_remove A LB) cr M' (m_vmmaps model') ->
       model_but_vm model model' ->
       (forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M' x = M x) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block (lb_remove A LB) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0x10000 <= a < 0xfa000 -> ~ (0xf8c58 <= a < 0xf9000) -> ~ (0xd87ac <= a < 0xd87b0) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes RSEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom RSEGS)) model') K) ->
    srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xab174) M (seg_rom RSEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB cr A n so bls vbnd ra K E HR HK Hsv Hkv HL5 P0 Hhi Hiw
           R2 Hso Hsoal Hin R10 R4 R1 Hra Hra2 HH Hh Hlz Hmt Hbl Hvb HK0 CONT.
    pose proof (hio_free L scfg HI HIok fx R M model LB cr A n K) as MS.
    rewrite (dl_segs L sp0 DL), (dl_free L sp0 DL), (dl_tp L sp0 DL) in MS.
    rewrite R1 in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) apply ret_ok_even. rewrite u_small by lia. exact Hra2.
    - (* [comment removed for export] *) rewrite R2, u_small by lia. eapply stack_ok_of_window; eassumption.
    - intros R' M' model' HP HPRES HBUT HH'.
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0).
      { rewrite vals_ev_app_l by lia. exact P0. }
      apply (CONT R' M' model' HL').
      + apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_kept R R' HP) c_kept_no0).
      + unfold keep_alloc.
        pose proof (env_app_know RSEGS vals (junk_vals R') ebs M kn Hkv HK) as HK1.
        destruct HPRES as [[PR1 PR2] _].
        eapply (know_keep_sound RSEGS 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW
                  (Env (vals_ev (vals ++ junk_vals R')) ebs) (CPm (lb_remove A LB) (bv_unsigned sp0 + so)) (SCm (bv_unsigned sp0 + so))).
        * apply regions_alloc; try assumption.
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1).
             rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
          -- intros i Hi. rewrite vals_ev_app_l; [apply Hhi; exact Hi|]. destruct Hi as [<-|[<-|[]]]; lia.
        * intros a Ha [HC HE]. rewrite R2, u_small in PR1 by lia. apply PR1; assumption.
        * intros a HS. rewrite R2, u_small in PR2 by lia. apply PR2. exact HS.
        * exact HK1.
      + exact HH'.
      + exact HBUT.
      + intros x Hx. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia.
        rewrite <- (Z_to_bv_bv_unsigned 64 x). apply PR1.
        * pose proof (u64_range x). lia.
        * unfold client_addr. right. left. rewrite (dl_sptop L sp0 DL).
          pose proof (u64_range x). pose proof (dl_stack L sp0 DL). lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hb. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia. apply PR1; [exact Ha | left; exact Hb |].
        destruct Hb as (b & Hbin & Hr).
        assert (Hbin' : In b LB).
        { clear -Hbin. induction LB as [|c LB' IH]; [destruct Hbin|]. cbn [lb_remove] in Hbin.
          destruct (Z.eqb (fst c) A); [right; exact Hbin|]. destruct Hbin as [<-|Hbin]; [left; reflexivity | right; apply IH; exact Hbin]. }
        destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
        destruct (WF b Hbin') as (HBRb & _ & _). pose proof (hz_of_block_range _ _ HBRb) as (Y1 & Y2 & Y3).
        unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hs He. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia. apply PR1; [lia | |].
        * unfold client_addr. right. right. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|].
          intros Hst. apply (dl_static L sp0 DL) in Hst. lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
  Qed.
End DrvLayout.
End FPX_1.
End Ns0DrvLib.
Module Ns0OpenFail_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0MainEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0LibStdioCall.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition STOPS : list Z := [0xb9978; 0xb9ef8; 0xba46c; 0xb987c; 0xa8a80; 0xa8c0c; 0xacb38; 0xa92d0; 0xae4d4]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
(* [comment removed for export] *)
Definition sc_of (nv : nat) (sr : list expr) (kn : list kentry) : stdio_res :=
  match stdio_call nv sr kn with
  | Some r => r
  | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] []
  end.
(* [comment removed for export] *)
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IHI : Z := 0xfa000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x38c2c sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0xba924 srB0 [] knB0 39.
Definition scrB : scripts := SCR [false] [] [].
Definition rB := Eval vm_compute in run scrB ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-544)) 1 (ELit 32);
   SE (SA (EVar 0) (-552)) 8 (ELit 7954887939408031598);
   SE (SA (EVar 0) (-560)) 8 (ELit 7953747406983097443)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0xaecb0 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0xaecb0 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0xaf820 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0xaecb0 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0xaecb0 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0xaecb0 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS 0xaf180 srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrG3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition rG3 := Eval vm_compute in run scrG3 ssG0.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 199 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : sym_state := SS (sc_ret scG3) srH30 [] knH30 231.
Definition rH3 := Eval vm_compute in run scr0 ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 231 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : sym_state := SS 0xaf180 srI30 [] knI30 263.
Definition rI3 := Eval vm_compute in run scr0 ssI30.
Definition srI3 : list expr := Eval vm_compute in s_regs (fst (fst rI3)).
Definition knI3 : list kentry := Eval vm_compute in kn_after rI3 knI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrF4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition rF4 := Eval vm_compute in run scrF4 ssF0.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 167 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in sc_kn scF4.
(* [comment removed for export] *)
Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 199.
Definition rG4 := Eval vm_compute in run scr0 ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_after rG4 knG40.
(* [comment removed for export] *)
Definition logNL : list sentry := [SE (SA (EVar 0) (-560)) 1 (ELit 10)].
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 199.
(* [comment removed for export] *)
Definition ssH40 : sym_state := SS 0xaecb0 srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : sym_state := SS 0xaf180 srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Lemma itinerary_63_64 :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0xae4d4%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 199 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0xaf350%Z, 0xc6bd0%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x12be5, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0xae4d4%Z, [])
  /\ stdio_call 231 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0xaf180%Z, 0xc6bd0%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0xa92d0%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0xae4d4%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 167 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0xafd70%Z, 0xc6bd0%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0xb9978%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0xae4d4%Z, [])
  /\ stdio_call 231 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0xaf180%Z, 0xc6bd0%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0xa92d0%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma itinerary_le62 :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xba920%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0xb9978%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xb9978%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xba46c%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0xb9978%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0xb9978%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0xb9978%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xae4d4%Z, [])
  /\ stdio_call 231 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0xaf180%Z, 0xc6bd0%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0xa92d0%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX_1.

End Ns0OpenFail_defs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
Module Ns0DrvG_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0MainEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0LibStdioCall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.DrvKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS_L : list Z := (0x38cb4 :: STOPS)%Z.
Definition runL (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_L scr ss [].
(* [comment removed for export] *)
Definition STOPS_Q : list Z := [0xa92d0; 0xae4d4; 0xab2b4; 0xab174; 0x390cc]%Z.
Definition runQ (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_Q scr ss [].
Definition no_sc : stdio_res := SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [].
Definition the_sc (o : option stdio_res) : stdio_res := match o with Some r => r | None => no_sc end.

(* [comment removed for export] *)
Definition kn_blk2 (v : nat) : list kentry := [KRange (EVar v) 4096 (2 ^ 47); KAlign (EVar v) 16]%Z.
(* [comment removed for export] *)
Definition keep_rd (kn : list kentry) : list kentry := kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.

(* [comment removed for export] *)
Definition below_frame (K : kentry) : bool :=
  match K with KWord (SA (EVar 0) off) _ _ => (off <? -128)%Z | _ => false end.
Definition knLP6 : list kentry := Eval vm_compute in List.filter (fun K => negb (below_frame K)) keepB.
Definition knLP : list kentry := kn_blk 48 65536 ++ knLP6.
(* [comment removed for export] *)
Definition cellR : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x38d14).
Definition cellC : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x38d28).
Definition knRD : list kentry := cellR :: knLP.

(* [comment removed for export] *)
Definition srLP : list expr :=
  [ELit 0; EVar 7; EAlu ALU_ADD (EVar 0) (ELit (-128)); ELit 67584; ELit 886864; EVar 11; EVar 12; EVar 13;
   ELit 2; EVar 48; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 2; EVar 70; ELit 3; EVar 38; ELit 814617; EVar 48; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 34; EVar 35; EVar 36; EVar 37]%Z.
(* [comment removed for export] *)
Definition srRD : list expr :=
  [ELit 0; ELit 780452; EAlu ALU_ADD (EVar 0) (ELit (-144)); ELit 67584; ELit 886864; EVar 11; EVar 12; EVar 13;
   ELit 2; EVar 48; ELit 3; ELit 814617; EVar 71; ELit 0; ELit 0; ELit 0; ELit 0; ELit 63;
   EVar 2; EVar 70; ELit 3; EVar 38; ELit 814617; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 34; EVar 35; EVar 36; EVar 37]%Z.

(* [comment removed for export] *)
Definition rC0L := Eval vm_compute in runL scr0 (SS 0x38c80 srC0 [] knC0 70).
Definition srC0L : list expr := Eval vm_compute in s_regs (fst (fst rC0L)).

(* [comment removed for export] *)
Definition knLPp : list kentry := KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLP.
(* [comment removed for export] *)
Definition rPa := Eval vm_compute in runL (SCR [false; false] [] []) (SS 0x38cb4 srLP [] knLPp 71).
Definition srPa : list expr := Eval vm_compute in s_regs (fst (fst rPa)).
Definition knRDp : list kentry := Eval vm_compute in kn_after rPa knLPp.
(* [comment removed for export] *)
Definition rPb := Eval vm_compute in runL (SCR [false; true] [] []) (SS 0x38cb4 srLP [] knLPp 71).
Definition srPb : list expr := Eval vm_compute in s_regs (fst (fst rPb)).
(* [comment removed for export] *)
Definition want_x : expr := Eval vm_compute in nth 12 srPb (ELit 0).

(* [comment removed for export] *)
Definition srRe0 : list expr := sr_upd srRD (ridx 10) (EVar 72).
Definition knRe0 : list kentry := KRange (EVar 72) 1 65536 :: knRD.
Definition rRe_tk := Eval vm_compute in runL scr0 (SS 0xba924 srRe0 [] knRe0 73).
Definition srRe_tk : list expr := Eval vm_compute in s_regs (fst (fst rRe_tk)).
Definition knRe_tk : list kentry := Eval vm_compute in kn_after rRe_tk knRe0.
(* [comment removed for export] *)
Definition srRm0 : list expr := Eval vm_compute in sr_after_call_j srRe_tk (map ridx callee_kept) 73.
Definition rRm := Eval vm_compute in runL scr0 (SS 0x38cac srRm0 [] knRe_tk 105).
Definition srRm : list expr := Eval vm_compute in s_regs (fst (fst rRm)).
(* [comment removed for export] *)
Definition len_x : expr := Eval vm_compute in nth 19 srRm (ELit 0).
(* [comment removed for export] *)
Definition srRf0 : list expr := sr_upd srRD (ridx 10) (ELit 0).
Definition rRe_ft := Eval vm_compute in runL scr0 (SS 0xba924 srRf0 [] knRD 73).
Definition srRe_ft : list expr := Eval vm_compute in s_regs (fst (fst rRe_ft)).
Definition knRe_ft : list kentry := Eval vm_compute in kn_after rRe_ft knRD.

(* [comment removed for export] *)
Definition srGL : list expr := Eval vm_compute in sr_upd srRe_ft (ridx 10) (ELit 0).
Definition knGbase : list kentry := cellC :: knLP.
Definition knG (lo hi : Z) : list kentry := KRange (EVar 70) lo hi :: knGbase.

(* [comment removed for export] *)
Definition knLPg : list kentry := KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLP.
Definition rGa := Eval vm_compute in runL (SCR [true] [] []) (SS 0x38cb4 srLP [] knLPg 71).
Definition srGa : list expr := Eval vm_compute in s_regs (fst (fst rGa)).
Definition knGa : list kentry := Eval vm_compute in kn_after rGa knLPg.
(* [comment removed for export] *)
Definition cap2_x : expr := Eval vm_compute in nth 10 srGa (ELit 0).
(* [comment removed for export] *)
Definition srGb0 : list expr := Eval vm_compute in sr_after_call_j srGa (map ridx c_kept) 71.
Definition knGb0 : list kentry := Eval vm_compute in kn_blk2 81 ++ keep_alloc MSO [(48%nat, 65536%Z)] [] knGa.
Definition rGb := Eval vm_compute in runL scr0 (SS 0x38cd4 srGb0 [] knGb0 103).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
(* [comment removed for export] *)
Definition srGc0 : list expr := Eval vm_compute in sr_after_call_j srGb (map ridx callee_kept) 103.
Definition knGc0 : list kentry := Eval vm_compute in keep_rd knGb0.
Definition rGc := Eval vm_compute in runL scr0 (SS 0x38cf0 srGc0 [] knGc0 135).
Definition srGc : list expr := Eval vm_compute in s_regs (fst (fst rGc)).
(* [comment removed for export] *)
Definition srGd0 : list expr := Eval vm_compute in sr_after_call_j srGc (map ridx c_kept) 135.
Definition knGd0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knGc0.
Definition rGd := Eval vm_compute in runL scr0 (SS 0x38cf8 srGd0 [] knGd0 167).
Definition srGd : list expr := Eval vm_compute in s_regs (fst (fst rGd)).
Definition knGd : list kentry := Eval vm_compute in kn_after rGd knGd0.

(* [comment removed for export] *)
Definition knLPr : list kentry := KRange (EVar 70) 67108864 67108864 :: KRange (EVar 38) 67108864 67108864 :: knLP.
(* [comment removed for export] *)
Definition scr_refuse : scripts := SCR [false; false; false; true; false] [] [].   (* [comment removed for export] *)
Definition rRa := Eval vm_compute in runQ scr_refuse (SS 0x38cb4 srLP [] knLPr 71).
Definition srRa : list expr := Eval vm_compute in s_regs (fst (fst rRa)).
Definition knRa : list kentry := Eval vm_compute in kn_after rRa knLPr.
Definition scR : stdio_res := Eval vm_compute in the_sc (stdio_call 71 srRa knRa).
Definition srRb0 : list expr := Eval vm_compute in sc_sr scR.
Definition knRb0 : list kentry := Eval vm_compute in sc_kn scR.
Definition rRb := Eval vm_compute in runQ scr0 (SS (sc_ret scR) srRb0 [] knRb0 103).
Definition srRb : list expr := Eval vm_compute in s_regs (fst (fst rRb)).
Definition knRb : list kentry := Eval vm_compute in kn_after rRb knRb0.

(* [comment removed for export] *)
Definition summG (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
Definition kdiff (a b : list kentry) := List.filter (fun K => negb (existsb (kentry_eqb K) b)) a.
Lemma loop_itinerary_ok :
  summG rC0L = (0xba920%Z, [], 70%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x38d14%Z)]) /\ kn_after rC0L knC0 = cellR :: knC0
  /\ kdiff knLP knC0 = [] /\ kn_vars_lt 6 knLP6 = true
  /\ (nth 21 srC0L (ELit 0), nth 9 srC0L (ELit 0), nth 19 srC0L (ELit 0), nth 12 srC0L (ELit 0), nth 11 srC0L (ELit 0), nth 10 srC0L (ELit 0), nth 17 srC0L (ELit 0))
     = (ELit 65536, EVar 48, ELit 0, ELit 65536, ELit 814617, ELit 3, ELit 63)
  /\ summG rPa = (0xba920%Z, [SCBr false BC_LTU want_x (ELit 65536); SCBr false BC_EQ (EVar 70) (EVar 38)], 71%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x38d14%Z)])
  /\ summG rPb = (0xba920%Z, [SCBr true BC_LTU want_x (ELit 65536); SCBr false BC_EQ (EVar 70) (EVar 38)], 71%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x38d14%Z)])
  /\ kn_after rPb knLPp = knRDp /\ knRDp = cellR :: knLPp
  /\ srPb = sr_upd srPa (ridx 12) want_x /\ srPa = sr_upd (sr_upd srRD (ridx 12) (ELit 65536)) (ridx 23) (EVar 48)
  /\ want_x = EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit (-1)) (EVar 70))
  /\ summG rRe_tk = (0xb9978%Z, [], 73%nat, []) /\ kn_after rRe_tk knRe0 = knRe0 /\ keep_rd knRe0 = knRe0
  /\ (nth 10 srRe_tk (ELit 0), nth 11 srRe_tk (ELit 0), nth 12 srRe_tk (ELit 0), nth 1 srRe_tk (ELit 0), nth 2 srRe_tk (ELit 0))
     = (EAlu ALU_ADD (EVar 48) (EVar 70), ELit 814617, EVar 72, ELit 0x38cac%Z, EAlu ALU_ADD (EVar 0) (ELit (-128)))
  /\ summG rRm = (0x38cb4%Z, [], 105%nat, []) /\ len_x = EAlu ALU_ADD (EVar 70) (EVar 72)
  /\ (nth 9 srRm (ELit 0), nth 23 srRm (ELit 0), nth 21 srRm (ELit 0), nth 18 srRm (ELit 0), nth 2 srRm (ELit 0))
     = (EVar 48, EVar 48, EVar 38, EVar 2, EAlu ALU_ADD (EVar 0) (ELit (-128)))
  /\ summG rRe_ft = (0xba920%Z, [], 73%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x38d28%Z)]) /\ knRe_ft = cellC :: knLP
  /\ (nth 10 srRe_ft (ELit 0), nth 17 srRe_ft (ELit 0)) = (ELit 3, ELit 57) /\ sr_vars_lt 71 srGL = true
  /\ summG rGa = (0xab2b4%Z, [SCBr true BC_EQ (EVar 70) (EVar 38)], 71%nat, [])
  /\ kn_after rGa knLPg = knLPg /\ nth 10 srGa (ELit 0) = cap2_x /\ nth 21 srGa (ELit 0) = cap2_x /\ cap2_x = EMd M_MUL (ELit 2) (EVar 70)
  /\ nth 1 srGa (ELit 0) = ELit 0x38cd4%Z /\ nth 2 srGa (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit MSO)
  /\ summG rGb = (0xb9978%Z, [], 103%nat, []) /\ kn_after rGb knGb0 = knGb0
  /\ (nth 10 srGb (ELit 0), nth 11 srGb (ELit 0), nth 12 srGb (ELit 0), nth 1 srGb (ELit 0)) = (EVar 81, EVar 48, EVar 70, ELit 0x38cf0%Z)
  /\ kdiff knGb0 knGc0 = []
  /\ summG rGc = (0xab174%Z, [], 135%nat, []) /\ kn_after rGc knGc0 = knGc0 /\ nth 10 srGc (ELit 0) = EVar 48
  /\ nth 1 srGc (ELit 0) = ELit 0x38cf8%Z /\ nth 2 srGc (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit MSO)
  /\ summG rGd = (0xba920%Z, [], 167%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x38d14%Z)])
  /\ (nth 10 srGd (ELit 0), nth 11 srGd (ELit 0), nth 12 srGd (ELit 0), nth 17 srGd (ELit 0), nth 9 srGd (ELit 0), nth 21 srGd (ELit 0), nth 19 srGd (ELit 0))
     = (ELit 3, ELit 814617, ELit 65536, ELit 63, EVar 81, cap2_x, EVar 70)
  /\ (s_pc (fst (fst rRa)), s_next (fst (fst rRa))) = (0xae4d4%Z, 71%nat)
  /\ stdio_call 71 srRa knRa = Some scR /\ (sc_ret scR, sc_f scR, sc_fd scR, sc_s scR, sc_l scR) = (0xaf180%Z, 0xc6bd0%Z, 2%Z, ELit 0, ELit 0)
  /\ (sc_wb scR, sc_wp scR, sc_sp scR) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), EAlu ALU_ADD (EVar 0) (ELit (-576)))
  /\ summG rRb = (0xa92d0%Z, [], 103%nat, s_log (fst (fst rRb))) /\ nth 10 srRb (ELit 0) = ELit 2.
Proof.
vm_compute. repeat split; reflexivity. Qed.

End FPX_1.

End Ns0DrvG_defs.
Module Ns0DrvC_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0MainEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0LibStdioCall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.DrvKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0DrvG_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS_H : list Z := (0x38d54 :: 0x38efc :: STOPS)%Z.
Definition runH (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_H scr ss [].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition knGS : list kentry := knG 0 5.
Definition rHs := Eval vm_compute in run scr0 (SS 0xba924 srGL [] knGS 71).
Definition srHs : list expr := Eval vm_compute in s_regs (fst (fst rHs)).
Definition knHs : list kentry := Eval vm_compute in kn_after rHs knGS.
(* [comment removed for export] *)
Definition scS : stdio_res := Eval vm_compute in the_sc (stdio_call 71 srHs knHs).
Definition srIs0 : list expr := Eval vm_compute in sc_sr scS.
Definition knIs0 : list kentry := Eval vm_compute in sc_kn scS.
Definition rIs := Eval vm_compute in run scr0 (SS (sc_ret scS) srIs0 [] knIs0 103).
Definition srIs : list expr := Eval vm_compute in s_regs (fst (fst rIs)).
Definition knIs : list kentry := Eval vm_compute in kn_after rIs knIs0.
(* [comment removed for export] *)
Definition srJs0 : list expr := Eval vm_compute in sr_after_call_j srIs (map ridx c_kept) 103.
Definition knJs0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knIs.
Definition rJs := Eval vm_compute in run scr0 (SS 0x38e28 srJs0 [] knJs0 135).
Definition srJs : list expr := Eval vm_compute in s_regs (fst (fst rJs)).
Definition knJs : list kentry := Eval vm_compute in kn_after rJs knJs0.

(* [comment removed for export] *)
Definition kn_hdr : list kentry :=
  [KWord (SA (EVar 48) 0) 1 (EVar 71); KWord (SA (EVar 48) 1) 1 (EVar 72); KRange (EVar 71) 0 255; KRange (EVar 72) 0 255].
Definition knGL : list kentry := kn_hdr ++ knG 6 67108863.

(* [comment removed for export] *)
Definition scr_taken : scripts := SCR [true] [] [].
Definition rHo := Eval vm_compute in runH scr_taken (SS 0xba924 srGL [] knGL 73).
Definition srHo : list expr := Eval vm_compute in s_regs (fst (fst rHo)).
Definition knHo : list kentry := Eval vm_compute in kn_after rHo knGL.
Definition scO : stdio_res := Eval vm_compute in the_sc (stdio_call 73 srHo knHo).
Definition srIo0 : list expr := Eval vm_compute in sc_sr scO.
Definition knIo0 : list kentry := Eval vm_compute in sc_kn scO.
Definition rIo := Eval vm_compute in run scr0 (SS (sc_ret scO) srIo0 [] knIo0 105).
Definition srIo : list expr := Eval vm_compute in s_regs (fst (fst rIo)).
Definition knIo : list kentry := Eval vm_compute in kn_after rIo knIo0.
Definition srJo0 : list expr := Eval vm_compute in sr_after_call_j srIo (map ridx c_kept) 105.
Definition knJo0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knIo.
Definition rJo := Eval vm_compute in run scr0 (SS 0x38e28 srJo0 [] knJo0 137).
Definition srJo : list expr := Eval vm_compute in s_regs (fst (fst rJo)).
Definition knJo : list kentry := Eval vm_compute in kn_after rJo knJo0.

(* [comment removed for export] *)
Definition scr_fall : scripts := SCR [false] [] [].
Definition rHa := Eval vm_compute in runH scr_fall (SS 0xba924 srGL [] knGL 73).
Definition srHa : list expr := Eval vm_compute in s_regs (fst (fst rHa)).
(* [comment removed for export] *)
Definition cfglen_x : expr := Eval vm_compute in nth 18 srHa (ELit 0).
Definition sx8_x : expr := Eval vm_compute in nth 21 srHa (ELit 0).
(* [comment removed for export] *)
Definition srHb0 : list expr := Eval vm_compute in map (esub sx8_x (EVar 74)) (map (esub cfglen_x (EVar 73)) srHa).
(* [comment removed for export] *)
Definition PX : expr := EAlu ALU_ADD (EVar 48) (EVar 73).
Definition kn_bm : list kentry :=
  [KRange (EVar 73) 0 32767;
   KWord (SA PX 2) 1 (EVar 75); KWord (SA PX 3) 1 (EVar 76); KWord (SA PX 4) 1 (EVar 77); KWord (SA PX 5) 1 (EVar 78);
   KRange (EVar 75) 0 255; KRange (EVar 76) 0 255; KRange (EVar 77) 0 255; KRange (EVar 78) 0 255].
Definition knHb0 : list kentry := kn_bm ++ knGL.
Definition rHb := Eval vm_compute in runH scr0 (SS 0x38d54 srHb0 [] knHb0 79).
Definition srHb : list expr := Eval vm_compute in s_regs (fst (fst rHb)).
(* [comment removed for export] *)
Definition plen_x : expr := Eval vm_compute in nth 13 srHb (ELit 0).

(* [comment removed for export] *)
Definition srT0 : list expr := Eval vm_compute in map (esub plen_x (EVar 79)) srHb.
Definition kn_tgt : list kentry :=
  [KRange (EVar 73) 0 32767; KRange (EVar 79) 0 67108857; KWord (SA (EVar 48) 2) 1 (EVar 80); KRange (EVar 80) 0 255].
Definition knT0 : list kentry := kn_tgt ++ knGL.

(* [comment removed for export] *)
Lemma hdr_itinerary_ok :
  (s_pc (fst (fst rHs)), snd (fst rHs)) = (0xae4d4%Z, [])
  /\ stdio_call 71 srHs knHs = Some scS /\ (sc_ret scS, sc_f scS, sc_fd scS) = (0xaed6c%Z, 0xc6bd0%Z, 2%Z)
  /\ (s_pc (fst (fst rIs)), snd (fst rIs), s_log (fst (fst rIs))) = (0xab174%Z, [], [])
  /\ (s_pc (fst (fst rJs)), snd (fst rJs), s_log (fst (fst rJs))) = (0xa92d0%Z, [], [])
  /\ (s_pc (fst (fst rHo)), snd (fst rHo)) = (0xae4d4%Z, [SCBr true BC_LTU (EVar 70) (EAlu ALU_ADD cfglen_x (ELit 6))])
  /\ stdio_call 73 srHo knHo = Some scO /\ (sc_ret scO, sc_f scO, sc_fd scO) = (0xaed6c%Z, 0xc6bd0%Z, 2%Z)
  /\ (s_pc (fst (fst rIo)), snd (fst rIo), s_log (fst (fst rIo))) = (0xab174%Z, [], [])
  /\ (s_pc (fst (fst rJo)), snd (fst rJo), s_log (fst (fst rJo))) = (0xa92d0%Z, [], [])
  /\ (s_pc (fst (fst rHa)), snd (fst rHa), s_log (fst (fst rHa))) = (0x38d54%Z, [SCBr false BC_LTU (EVar 70) (EAlu ALU_ADD cfglen_x (ELit 6))], [])
  /\ kn_after rHa knGL = knGL
  /\ (s_pc (fst (fst rHb)), snd (fst rHb), s_log (fst (fst rHb))) = (0x38efc%Z, [], [])
  /\ kn_after rHb knHb0 = knHb0.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma knT0_sub : ksubl_b (kn_tgt ++ knHb0) knT0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma knGL_sub_Hb0 : ksubl_b knHb0 knGL = true.
Proof. vm_compute. reflexivity. Qed.

End FPX_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition cfgF (v71 v72 : word) : word :=
  edenot (Env (fun n => match n with 71%nat => v71 | 72%nat => v72 | _ => Z_to_bv 64 0 end) (blobs_ev [])) cfglen_x.

Lemma cfglen_x_cfgF : forall vals bl,
  edenot (Env (vals_ev vals) (blobs_ev bl)) cfglen_x = cfgF (vals_ev vals 71) (vals_ev vals 72).
Proof. intros. reflexivity. Qed.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).

Lemma in_zseq : forall n z, In z (zseq n) <-> (0 <= z < Z.of_nat n)%Z.
Proof.
  intros n z. unfold zseq. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Definition cfgG (v72 : word) : word :=
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 144115188075855872) (ext_val true 0 1 v72)) (Z_to_bv 64 49).
Definition cfgH (v71 : word) : word := ext_val false 0 1 v71.
Lemma cfgF_split v71 v72 : cfgF v71 v72 = bv_or (cfgG v72) (cfgH v71).
Proof. reflexivity. Qed.
Lemma cfgG_tab : forallb (fun b1 => Z.eqb (bv_unsigned (cfgG (Z_to_bv 64 b1))) (256 * (b1 mod 128))) (zseq 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfgH_tab : forallb (fun b0 => Z.eqb (bv_unsigned (cfgH (Z_to_bv 64 b0))) b0) (zseq 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lor_tab : forallb (fun a => forallb (fun b => Z.eqb (Z.lor (256 * a) b) (256 * a + b)) (zseq 256)) (zseq 128) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cfgF_val : forall b0 b1, (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z ->
  cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1) = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
  intros b0 b1 H0 H1.
  pose proof cfgG_tab as TG. rewrite forallb_forall in TG. specialize (TG b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))). apply Z.eqb_eq in TG.
  pose proof cfgH_tab as TH. rewrite forallb_forall in TH. specialize (TH b0 (proj2 (in_zseq 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TH.
  pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as HM.
  pose proof lor_tab as TL. rewrite forallb_forall in TL. specialize (TL (b1 mod 128)%Z (proj2 (in_zseq 128 (b1 mod 128)%Z) ltac:(cbn; lia))).
  rewrite forallb_forall in TL. specialize (TL b0 (proj2 (in_zseq 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TL.
  apply bv_eq. rewrite cfgF_split, stdpp.bitvector.definitions.bv_or_unsigned, TG, TH, TL. symmetry.
  assert (E : ((b0 + 256 * b1) mod 32768 = 256 * (b1 mod 128) + b0)%Z).
  { pose proof (Z.div_mod b1 128 ltac:(lia)) as D.
    symmetry. apply (Zmod_unique (b0 + 256 * b1) 32768 (b1 / 128)); lia. }
  rewrite E. apply u_small. lia.
Qed.

(* [comment removed for export] *)
Definition sx8F (v72 : word) : word := ext_val true 0 1 v72.
Lemma sx8_x_sx8F : forall vals bl, edenot (Env (vals_ev vals) (blobs_ev bl)) sx8_x = sx8F (vals_ev vals 72).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma plen_x_eq : plen_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 70) (EMd M_MUL (ELit (-1)) (EVar 73))) (ELit (-6)).
Proof. reflexivity. Qed.

Lemma mod_of_decomp' : forall a b q r, (0 < b)%Z -> (0 <= r < b)%Z -> (a = b * q + r)%Z -> (a mod b = r)%Z.
Proof. intros a b q r Hb Hr He. symmetry. apply (Zmod_unique a b q r); lia. Qed.
Lemma add_negmul : forall a c : Z, (0 <= c <= a)%Z -> (a < 2 ^ 64)%Z ->
  alu64 ALU_ADD (Z_to_bv 64 a) (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 c)) = Z_to_bv 64 (a - c).
Proof.
  intros a c H1 H2. apply bv_eq. rewrite alu_add. unfold v_add. rewrite u_mul64.
  rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  rewrite (bv_wrap_small 64 (a - c)) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  replace ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z by reflexivity.
  destruct (Z.eq_dec c 0) as [->|Hnz].
  - rewrite Z.mul_0_r. change ((0) mod 2 ^ 64)%Z with 0%Z. rewrite Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia.
  - rewrite (mod_of_decomp' ((2 ^ 64 - 1) * c) (2 ^ 64) (c - 1) (2 ^ 64 - c)) by lia.
    rewrite (mod_of_decomp' (a + (2 ^ 64 - c)) (2 ^ 64) 1 (a - c)) by lia. reflexivity.
Qed.
Lemma add_neglit : forall a k : Z, (k <= 0)%Z -> (0 <= a + k)%Z -> (a < 2 ^ 64)%Z ->
  alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a + k).
Proof.
  intros a k H0 H1 H2. apply bv_eq. rewrite alu_add. unfold v_add.
  rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  rewrite (bv_wrap_small 64 (a + k)) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  destruct (Z.eq_dec k 0) as [->|Hnz].
  - change ((0) mod 2 ^ 64)%Z with 0%Z. rewrite !Z.add_0_r. apply Z.mod_small. lia.
  - rewrite (mod_of_decomp' k (2 ^ 64) (-1) (2 ^ 64 + k)) by lia.
    rewrite (mod_of_decomp' (a + (2 ^ 64 + k)) (2 ^ 64) 1 (a + k)) by lia. reflexivity.
Qed.
Lemma plen_val : forall (Lz C : Z) vals bl,
  (0 <= C)%Z -> (6 + C <= Lz < 2 ^ 32)%Z ->
  vals_ev vals 70 = Z_to_bv 64 Lz -> vals_ev vals 73 = Z_to_bv 64 C ->
  edenot (Env (vals_ev vals) (blobs_ev bl)) plen_x = Z_to_bv 64 (Lz - 6 - C).
Proof.
  intros Lz C vals bl HC HL P70 P73. rewrite plen_x_eq. cbn [edenot ev]. rewrite P70, P73.
  rewrite add_negmul by lia. rewrite add_neglit by lia. f_equal. lia.
Qed.

End FPX_2.

End Ns0DrvC_defs.
Module Ns0DrvD_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0MainEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0LibStdioCall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.DrvKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0DrvG_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0DrvC_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS_T : list Z := (0x38fb4 :: 0x38da0 :: STOPS)%Z.
Definition runT (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_T scr ss [].
(* [comment removed for export] *)
Definition STOPS_P : list Z := [0xa92d0; 0xae4d4; 0xab2b4; 0xab174; 0x390cc]%Z.
Definition STOPS_R : list Z := (0x38fd8 :: STOPS_P)%Z.
Definition runP (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_P scr ss [].
Definition runR (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_R scr ss [].

(* [comment removed for export] *)
Definition knTc (clo chi plo phi : Z) : list kentry := KRange (EVar 73) clo chi :: KRange (EVar 79) plo phi :: knT0.
Definition rT00 := Eval vm_compute in runT scr0 (SS 0x38efc srT0 [] (knTc 0 0 0 0) 81).
Definition rT01 := Eval vm_compute in runT scr0 (SS 0x38efc srT0 [] (knTc 0 0 1 67108857) 81).
Definition rT10 := Eval vm_compute in runT scr0 (SS 0x38efc srT0 [] (knTc 1 32767 0 0) 81).
Definition rT11 := Eval vm_compute in runT scr0 (SS 0x38efc srT0 [] (knTc 1 32767 1 67108857) 81).
Definition sr00 : list expr := Eval vm_compute in s_regs (fst (fst rT00)).
Definition sr01 : list expr := Eval vm_compute in s_regs (fst (fst rT01)).
Definition sr10 : list expr := Eval vm_compute in s_regs (fst (fst rT10)).
Definition sr11 : list expr := Eval vm_compute in s_regs (fst (fst rT11)).
(* [comment removed for export] *)
Definition calls_x : expr := Eval vm_compute in nth 21 sr11 (ELit 0).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_case_entry (K : kentry) : bool :=
  existsb (kentry_eqb K) [KRange (EVar 73) 0 0; KRange (EVar 73) 1 32767; KRange (EVar 79) 0 0; KRange (EVar 79) 1 67108857].
Definition uncase (kn : list kentry) : list kentry := List.filter (fun K => negb (is_case_entry K)) kn.
Definition knTe : list kentry := Eval vm_compute in uncase (kn_after rT11 (knTc 1 32767 1 67108857)).

(* [comment removed for export] *)
Definition knTk : list kentry := Eval vm_compute in keep_alloc (-208) [(48%nat, 65536%Z)] [] knTe.

(* [comment removed for export] *)
Definition srTm0 : list expr := Eval vm_compute in sr_upd sr11 (ridx 21) (EVar 81).
Definition srU0 : list expr := Eval vm_compute in sr_after_call_j srTm0 (map ridx c_kept) 82.
(* [comment removed for export] *)
Definition knU0 : list kentry := Eval vm_compute in kn_blk2 92 ++ knTk.
Definition rU := Eval vm_compute in runT scr0 (SS 0x38f60 srU0 [] knU0 114).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
(* [comment removed for export] *)
Definition srV0 : list expr := Eval vm_compute in sr_after_call_j srU (map ridx callee_kept) 114.
Definition knV0 : list kentry := Eval vm_compute in keep_rd knU0.
Definition rV := Eval vm_compute in runT scr0 (SS 0x38f74 srV0 [] knV0 146).
Definition srV : list expr := Eval vm_compute in s_regs (fst (fst rV)).

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
(* [comment removed for export] *)
Definition srLH : list expr :=
  [ELit 0; EVar 85; spx (-208); ELit 67584; ELit 886864; EVar 86; EVar 87; EVar 88;
   EVar 79; EVar 82; EVar 89; EVar 90; EVar 91; EVar 92; EVar 93; EVar 94; EVar 95; EVar 96;
   EVar 83; EVar 84; ELit 880160; EVar 81; ELit 0; ELit 18446744073709551614; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 97; EVar 98; EVar 99; EVar 100].
(* [comment removed for export] *)
Definition knLH1 : list kentry := Eval vm_compute in keep_rd knTk.
(* [comment removed for export] *)
Definition shared_pos : list nat := [2; 3; 4; 8; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition relay_ok_b (sr : list expr) : bool :=
  forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLH (ELit 0)) && expr_vars_lt 82 (nth i sr (ELit 0))) shared_pos.
(* [comment removed for export] *)
Definition IMG_LIB : list (Z * Z) := [(0x10000, 0xd6e40); (0xd7fc8, 0xd8778); (0xd8780, 0xd87ac); (0xd87b0, 0xf8898); (0xf8ab8, 0xf8c58); (0xf9000, 0xfa000)]%Z.
Definition keep_lib (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 65536 bls vbnd [3%nat; 4%nat] IMG_LIB IMG_RW kn.

(* [comment removed for export] *)
Definition rLB1 := Eval vm_compute in runT scr0 (SS 0x38fb4 srLH [] knLH1 102).
Definition srLB : list expr := Eval vm_compute in s_regs (fst (fst rLB1)).
Definition knLc1 : list kentry := Eval vm_compute in kn_after rLB1 knLH1.
(* [comment removed for export] *)
Definition srLr0 : list expr := Eval vm_compute in sr_upd (sr_after_call_j srLB (map ridx c_kept) 102) (ridx 10) (ELit 0).
Definition knLr1 : list kentry := Eval vm_compute in keep_lib (-208) [(48%nat, 65536%Z)] [] knLc1.
(* [comment removed for export] *)
Definition rLc1 := Eval vm_compute in runT scr0 (SS 0x38fc8 srLr0 [] knLr1 134).
Definition srP0 : list expr := Eval vm_compute in s_regs (fst (fst rLc1)).
Definition knLp1 : list kentry := Eval vm_compute in kn_after rLc1 knLr1.
(* [comment removed for export] *)
Definition rP := Eval vm_compute in runP scr0 (SS 0x39084 srP0 [] knLp1 134).
Definition srP : list expr := Eval vm_compute in s_regs (fst (fst rP)).
Definition knP : list kentry := Eval vm_compute in kn_after rP knLp1.
(* [comment removed for export] *)
Definition srQ0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) (ELit 18446744073709551591).
Definition rQ := Eval vm_compute in runP scr0 (SS 0xaeefc srQ0 [] knP 134).
Definition srQ : list expr := Eval vm_compute in s_regs (fst (fst rQ)).
Definition knQ : list kentry := Eval vm_compute in kn_after rQ knP.
Definition scP : stdio_res := Eval vm_compute in the_sc (stdio_call 134 srQ knQ).
Definition srR0 : list expr := Eval vm_compute in sc_sr scP.
Definition knR0 : list kentry := Eval vm_compute in sc_kn scP.
Definition rR := Eval vm_compute in runR scr0 (SS (sc_ret scP) srR0 [] knR0 166).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition knR : list kentry := Eval vm_compute in kn_after rR knR0.

(* [comment removed for export] *)
Definition IMG_PF : list (Z * Z) := [(0x10000, 0xc6cc0); (0xc6cc4, 0xc6ce8); (0xc6cf0, 0xd6e40); (0xd8780, 0xd87ac); (0xd87b0, 0xf8c58); (0xf9000, 0xf9040); (0xf9440, 0xfa000)]%Z.
Definition keep_pf (kn : list kentry) : list kentry := kn_keep 0 (-208) 1056 [(48%nat, 65536%Z)] [] [3%nat; 4%nat] IMG_PF IMG_RW kn.
Definition wposK (e : expr) : kentry := KWord (SA (ELit 0) 0xc6ce8) 8 e.
Definition flagsK : kentry := KWord (SA (ELit 0) 0xc6cc0) 4 (ELit 5).
(* [comment removed for export] *)
Definition knR2 : list kentry := Eval vm_compute in keep_pf (keep_lib (-208) [(48%nat, 65536%Z)] [] knR).
Definition knLH2 : list kentry := wposK (EVar 101) :: KRange (EVar 101) 0xf9040 0xf9046 :: flagsK :: knR2.

(* [comment removed for export] *)
Definition rLB2 := Eval vm_compute in runT scr0 (SS 0x38fb4 srLH [] knLH2 102).
Definition knLc2 : list kentry := Eval vm_compute in kn_after rLB2 knLH2.
Definition knLr2 : list kentry := Eval vm_compute in keep_lib (-208) [(48%nat, 65536%Z)] [] knLc2.
Definition rLc2 := Eval vm_compute in runT scr0 (SS 0x38fc8 srLr0 [] knLr2 134).
Definition knLp2 : list kentry := Eval vm_compute in kn_after rLc2 knLr2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition srS0 : list expr := sr_upd srLH (ridx 19) (ELit 0).
Definition rS_tk := Eval vm_compute in runT (SCR [true] [] []) (SS 0x38fd8 srS0 [] knLH2 102).
Definition rS_ft := Eval vm_compute in runT (SCR [false] [] []) (SS 0x38fd8 srS0 [] knLH2 102).
Definition srS_tk : list expr := Eval vm_compute in s_regs (fst (fst rS_tk)).
Definition srS_ft : list expr := Eval vm_compute in s_regs (fst (fst rS_ft)).
Definition dec_x : expr := EAluw ALU_ADD (EVar 81) (ELit (-1)).

(* [comment removed for export] *)
Definition srX0 : list expr := Eval vm_compute in sr_after_call_j srS_ft (map ridx c_kept) 102.
Definition knX0 : list kentry := Eval vm_compute in keep_alloc (-208) [(48%nat, 65536%Z)] [] knLH2.
Definition rX := Eval vm_compute in runT scr0 (SS 0x38ff4 srX0 [] knX0 134).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX)).
(* [comment removed for export] *)
Definition srY0 : list expr :=
  Eval vm_compute in sr_upd (sr_upd (sr_upd (sr_upd srX (ridx 8) (ELit 0)) (ridx 10) (ELit 0)) (ridx 1) (EVar 134)) (ridx 11) (EVar 135).
Definition rY := Eval vm_compute in runT scr0 (SS 0x38e20 srY0 [] knX0 136).
Definition srY : list expr := Eval vm_compute in s_regs (fst (fst rY)).
(* [comment removed for export] *)
Definition srZ0 : list expr := Eval vm_compute in sr_after_call_j srY (map ridx c_kept) 136.
Definition knZ0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knX0.
Definition rZ := Eval vm_compute in runT scr0 (SS 0x38e28 srZ0 [] knZ0 168).
Definition srZ : list expr := Eval vm_compute in s_regs (fst (fst rZ)).
Definition knZ : list kentry := Eval vm_compute in kn_after rZ knZ0.

(* [comment removed for export] *)
Definition flag1 : list sentry := [SE (SA (ELit 0) 0xd6e24) 1 (ELit 1)].
Definition flag0 : list sentry := [SE (SA (ELit 0) 0xd6e24) 1 (ELit 0)].

(* [comment removed for export] *)
Lemma tgt_itinerary_ok :
  (s_pc (fst (fst rT00)), snd (fst rT00)) = (0x38fb4%Z, []) /\ (s_pc (fst (fst rT10)), snd (fst rT10)) = (0x38fb4%Z, [])
  /\ (s_pc (fst (fst rT01)), snd (fst rT01)) = (0xab2b4%Z, []) /\ (s_pc (fst (fst rT11)), snd (fst rT11)) = (0xab2b4%Z, [])
  /\ ksubl_b (kn_after rT00 (knTc 0 0 0 0)) knTe = true /\ ksubl_b (kn_after rT01 (knTc 0 0 1 67108857)) knTe = true
  /\ ksubl_b (kn_after rT10 (knTc 1 32767 0 0)) knTe = true /\ ksubl_b (kn_after rT11 (knTc 1 32767 1 67108857)) knTe = true
  /\ sr_upd sr01 (ridx 21) (EVar 81) = srTm0
  /\ ksubl_b knTe knLH1 = true /\ ksubl_b knV0 knLH1 = true /\ kn_after rV knV0 = knV0 /\ kn_after rU knU0 = knU0
  /\ relay_ok_b (sr_upd sr00 (ridx 21) (EVar 81)) = true /\ relay_ok_b (sr_upd sr10 (ridx 21) (EVar 81)) = true
  /\ relay_ok_b srV = true /\ relay_ok_b srR = true /\ relay_ok_b (sr_upd srS_tk (ridx 21) (EVar 81)) = true
  /\ kn_vars_lt 82 knLH1 = true /\ sr_vars_lt 82 srTm0 = true
  /\ (s_pc (fst (fst rU)), snd (fst rU), s_log (fst (fst rU))) = (0xb9978%Z, [], [])
  /\ (s_pc (fst (fst rV)), snd (fst rV), s_log (fst (fst rV))) = (0x38fb4%Z, [], [])
  /\ (s_pc (fst (fst rLB1)), snd (fst rLB1), s_log (fst (fst rLB1))) = (0x390cc%Z, [], flag1)
  /\ (s_pc (fst (fst rLB2)), snd (fst rLB2), s_log (fst (fst rLB2)), s_regs (fst (fst rLB2))) = (0x390cc%Z, [], flag1, srLB)
  /\ (s_pc (fst (fst rLc1)), snd (fst rLc1), s_log (fst (fst rLc1))) = (0x39084%Z, [], flag0)
  /\ (s_pc (fst (fst rLc2)), snd (fst rLc2), s_log (fst (fst rLc2)), s_regs (fst (fst rLc2))) = (0x39084%Z, [], flag0, srP0)
  /\ kn_after rLc1 knLr1 = knLp1 /\ kn_after rLc2 knLr2 = knLp2 /\ kn_after rLB1 knLH1 = knLc1 /\ kn_after rLB2 knLH2 = knLc2
  /\ knLr2 = knLc2 /\ ksubl_b knLp2 knLH2 = true /\ ksubl_b knLH2 knLp2 = true /\ ksubl_b knR (wposK (ELit 0xf9040) :: flagsK :: knR2) = true
  /\ keep_pf knLH2 = KRange (EVar 101) 0xf9040 0xf9046 :: knR2
  /\ kn_vars_lt 102 knLH2 = true /\ kn_vars_lt 81 knR2 = true
  /\ relay_ok_b (sr_after_call_j srP0 (map ridx callee_saved) 134) = true /\ ksubl_b knLH2 knX0 = true
  /\ keep_alloc (-208) [(48%nat, 65536%Z)] [] knLH2 = knX0
  /\ (s_pc (fst (fst rP)), snd (fst rP)) = (0xaeef8%Z, [])
  /\ (s_pc (fst (fst rQ)), snd (fst rQ)) = (0xae4d4%Z, [])
  /\ stdio_call 134 srQ knQ = Some scP /\ (sc_ret scP, sc_f scP, sc_fd scP, sc_wb scP, sc_wp scP, sc_s scP, sc_l scP)
                                           = (0xaef1c%Z, 0xc6cc0%Z, 1%Z, ELit 0xf9040, ELit 0xf9041, ELit 0x10d47, ELit 1)
  /\ (s_pc (fst (fst rR)), snd (fst rR)) = (0x38fd8%Z, [])
  /\ (s_pc (fst (fst rS_tk)), snd (fst rS_tk), s_log (fst (fst rS_tk))) = (0x38fb4%Z, [SCBr true BC_NE dec_x (ELit 0)], [])
  /\ (s_pc (fst (fst rS_ft)), snd (fst rS_ft), s_log (fst (fst rS_ft))) = (0xab174%Z, [SCBr false BC_NE dec_x (ELit 0)], [])
  /\ (s_pc (fst (fst rX)), snd (fst rX), s_log (fst (fst rX))) = (0x38da0%Z, [], []) /\ nth 10 (s_regs (fst (fst rX))) (ELit 1) = ELit 0
  /\ (s_pc (fst (fst rY)), snd (fst rY), s_log (fst (fst rY))) = (0xab174%Z, [], [])
  /\ (s_pc (fst (fst rZ)), snd (fst rZ), s_log (fst (fst rZ))) = (0xa92d0%Z, [], []).
Proof.
vm_compute. repeat split; reflexivity. Qed.

End FPX_1.

End Ns0DrvD_defs.
Module Ns0ReadErr_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0MainEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0LibStdioCall.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Definition STOPS : list Z := [0xb9978; 0xb9ef8; 0xba46c; 0xb987c; 0xa8a80; 0xa8c0c; 0xacb38; 0xa92d0; 0xae4d4]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0xfa000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0xd8850; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

(* [comment removed for export] *)
Definition knRE0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   (* [comment removed for export] *)
   KWr (SA (EVar 0) (- DRV_ZWIN)) DRV_ZWIN;
   KRange (EVar 2) 0x7fff80000000 0x800000400000;
   KWr (SA (ELit 0) 0xc6000) 0x34000;
   KImg 0x10000 0xc6dd0; KImg 0xc6dd1 0xc6e19; KImg 0xd6e19 0xd8780; KImg 0xf8858 0xf8878;
   KWord (SA (ELit 0) 0xd8788) 8 (ELit 0xd8788);
   KWord (SA (ELit 0) 0xd87a8) 4 (EVar 5);
   KImg 0xd87b4 0xd8800; KImg 0xd8808 0xd8820; KImg 0xd8828 0xd8840;
   KImg 0xd8850 0xd8860; KImg 0xd8868 0xd88d8; KImg 0xf8890 0xf8ac0;
   KBlob (SA (ELit 0) 0xf8ac0) (ELit 8) 2;
   KImg 0xf8ac8 0xf8ad0; KImg 0xf8ae1 0xf8ae8; KImg 0xf8af0 0xf8af8; KImg 0xf8b08 0xf8b10;
   KWord (SA (ELit 0) 0xf8b10) 8 (ELit 4096);
   KImg 0xf8b18 0xf8b48;
   KImg 0xf9018 0xfa000;   (* [comment removed for export] *)
   KRange (EVar 5) 1 4194303].

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x38e58 srRE0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-542)) 1 (ELit 32);
   SE (SA (EVar 0) (-544)) 2 (ELit 28271);
   SE (SA (EVar 0) (-552)) 8 (ELit 2338053693894893668);
   SE (SA (EVar 0) (-560)) 8 (ELit 7018141077071293539)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0xaecb0 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0xaecb0 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0xaf820 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0xaecb0 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0xaecb0 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0xaecb0 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scRE : stdio_res := Eval vm_compute in
  match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Lemma itinerary_re :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0xb9978%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xb9978%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xba46c%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0xb9978%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0xb9978%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0xb9978%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xae4d4%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0xaf180%Z, 0xc6bd0%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0xa92d0%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.


End FPX_1.
End Ns0ReadErr_defs.
Module Ns0Usage_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0MainEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0LibStdioCall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.Ns0OpenFail_defs.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0MainEntryN.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition u_ssA0 : sym_state := SS 0x38c2c sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.
(* [comment removed for export] *)
Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

(* [comment removed for export] *)
Definition u_ssB0 : sym_state := SS 0xaecb0 u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

(* [comment removed for export] *)
Definition u_ssC0 : sym_state := SS 0xaecb0 u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

(* [comment removed for export] *)
Definition u_ssD0 : sym_state := SS 0xaf820 u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

(* [comment removed for export] *)
Definition u_ssE0 : sym_state := SS 0xaecb0 u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

(* [comment removed for export] *)
Definition u_ssF0 : sym_state := SS 0xaecb0 u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG0 : sym_state := SS 0xaecb0 u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 : sym_state := SS 0xaf180 u_srH0 [] u_knH0 262.
Definition u_rH := Eval vm_compute in run scr0 u_ssH0.
Definition u_srH : list expr := Eval vm_compute in s_regs (fst (fst u_rH)).
Definition u_knH : list kentry := Eval vm_compute in kn_after u_rH u_knH0.

(* [comment removed for export] *)
Definition u_scrF3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition u_rF3 := Eval vm_compute in run u_scrF3 u_ssF0.
Definition u_srF3 : list expr := Eval vm_compute in s_regs (fst (fst u_rF3)).
Definition u_knF3 : list kentry := Eval vm_compute in kn_after u_rF3 u_knF0.
Definition u_scF3 : stdio_res := Eval vm_compute in sc_of 198 u_srF3 u_knF3.
Definition u_srG30 : list expr := Eval vm_compute in sc_sr u_scF3.
Definition u_knG30 : list kentry := Eval vm_compute in sc_kn u_scF3.
(* [comment removed for export] *)
Definition u_ssG30 : sym_state := SS (sc_ret u_scF3) u_srG30 [] u_knG30 230.
Definition u_rG3 := Eval vm_compute in run scr0 u_ssG30.
Definition u_srG3 : list expr := Eval vm_compute in s_regs (fst (fst u_rG3)).
Definition u_knG3 : list kentry := Eval vm_compute in kn_after u_rG3 u_knG30.
Definition u_scG3 : stdio_res := Eval vm_compute in sc_of 230 u_srG3 u_knG3.
Definition u_srH30 : list expr := Eval vm_compute in sc_sr u_scG3.
Definition u_knH30 : list kentry := Eval vm_compute in sc_kn u_scG3.
(* [comment removed for export] *)
Definition u_ssH30 : sym_state := SS 0xaf180 u_srH30 [] u_knH30 262.
Definition u_rH3 := Eval vm_compute in run scr0 u_ssH30.
Definition u_srH3 : list expr := Eval vm_compute in s_regs (fst (fst u_rH3)).
Definition u_knH3 : list kentry := Eval vm_compute in kn_after u_rH3 u_knH30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u_scrE4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition u_rE4 := Eval vm_compute in run u_scrE4 u_ssE0.
Definition u_srE4 : list expr := Eval vm_compute in s_regs (fst (fst u_rE4)).
Definition u_knE4 : list kentry := Eval vm_compute in kn_after u_rE4 u_knD.
Definition u_scE4 : stdio_res := Eval vm_compute in sc_of 166 u_srE4 u_knE4.
Definition u_srF40 : list expr := Eval vm_compute in sc_sr u_scE4.
Definition u_knF40 : list kentry := Eval vm_compute in sc_kn u_scE4.
(* [comment removed for export] *)
Definition u_ssF40 : sym_state := SS (sc_ret u_scE4) u_srF40 [] u_knF40 198.
Definition u_rF4 := Eval vm_compute in run scr0 u_ssF40.
Definition u_srF4 : list expr := Eval vm_compute in s_regs (fst (fst u_rF4)).
Definition u_knF4 : list kentry := Eval vm_compute in kn_after u_rF4 u_knF40.
(* [comment removed for export] *)
Definition u_logSUF : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 2907475163367712)].
Definition u_knG40 : list kentry := Eval vm_compute in fst (fst (carry u_logSUF u_knF4 [])).
Definition u_srG40 : list expr := Eval vm_compute in sr_after_call_j u_srF4 KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG40 : sym_state := SS 0xaecb0 u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 : sym_state := SS 0xaf180 u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

Lemma u_itinerary :
  (s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0xb9978%Z, [SCBr true BC_NE (EVar 16) (ELit 2)])
  /\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0xb9978%Z, [])
  /\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0xba46c%Z, [])
  /\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
     = (0xb9978%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
     = (0xb9978%Z, [SCBr true BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
     = (0xb9978%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0xae4d4%Z, [])
  /\ stdio_call 230 u_srG u_knG = Some u_scG
  /\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0xaf180%Z, 0xc6bd0%Z, 2%Z)
  /\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
  /\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0xa92d0%Z, [])
  /\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
     = (0xae4d4%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ stdio_call 198 u_srF3 u_knF3 = Some u_scF3
  /\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0xaf350%Z, 0xc6bd0%Z, 2%Z)
  /\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x110b8, ELit 7)
  /\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0xae4d4%Z, [])
  /\ stdio_call 230 u_srG3 u_knG3 = Some u_scG3
  /\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0xaf180%Z, 0xc6bd0%Z, 2%Z)
  /\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0xa92d0%Z, [])
  /\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
     = (0xae4d4%Z, [SCBr false BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ stdio_call 166 u_srE4 u_knE4 = Some u_scE4
  /\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0xafd70%Z, 0xc6bd0%Z, 2%Z)
  /\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
  /\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0xb9978%Z, [])
  /\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0xae4d4%Z, [])
  /\ stdio_call 230 u_srG4 u_knG4 = Some u_scG4
  /\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0xaf180%Z, 0xc6bd0%Z, 2%Z)
  /\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
  /\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0xa92d0%Z, []).
Proof.
vm_compute. repeat split; reflexivity. Qed.

End FPX_1.

End Ns0Usage_defs.
From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.
Module PnSExitCells.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0Exit_run1. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnTopS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0Exit_run1.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQSXC.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation AD := PnLayoutS.ADDR_S.
Abbreviation AQ := PnLayoutQS.QADDR_S.

(* [comment removed for export] *)
Lemma img_lock : rdn RSEGS (fun _ => None) (Z_to_bv 64 0xf889c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_next : rdn RSEGS (fun _ => None) (Z_to_bv 64 0xf88b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

(* [comment removed for export] *)
Lemma rdn_clear (M : word -> option byte) lo hi a (n : nat) :
  L5.img_clear M lo hi -> lo <= a -> a + Z.of_nat n <= hi -> 0 <= a < 2 ^ 64 -> hi <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros C H1 H2 H3 H4. apply rdn_ext.
  - rewrite L5.unsigned_lit by lia. lia.
  - intros x Hx. rewrite L5.unsigned_lit in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply C. lia.
Qed.

(* [comment removed for export] *)
Definition axmap (e : bool) : axv := if e then AXgc else AXg.

Lemma atexit_cells_of_st M e : PQST.atexit_st RSEGS AD AQ M e -> atexit_cells M (axmap e).
Proof.
  unfold PQST.atexit_st, atexit_cells. cbv zeta.
  cbn [pa_atexit pa_errcat_dtor pa_errcat_obj qa_drv_call qa_drv_guard AD PnLayoutS.ADDR_S AQ PnLayoutQS.QADDR_S].
  intros (C0 & S & _ & HD & C24 & F0 & F1 & _ & A0 & A1 & _).
  split; [rewrite (rdn_clear M _ _ 0xf889c 4 C0) by lia; exact img_lock|].
  destruct e; cbn [axmap].
  - split; [exact HD|]. split; [exact S|].
    split; [rewrite (rdn_clear M _ _ 0xf88b0 8 C24) by lia; exact img_next|].
    split; [exact F0|]. split; [exact A0|]. split; [exact F1| exact A1].
  - split; [exact HD|]. split; [exact S|].
    split; [rewrite (rdn_clear M _ _ 0xf88b0 8 C24) by lia; exact img_next|].
    split; [exact F0| exact A0].
Qed.

(* [comment removed for export] *)
Theorem top_lsx : forall g M, ls_ok PQTS.TopLS g M -> exists ax : axv, atexit_cells M ax.
Proof. intros g M H. exists (axmap (PMST.st_err g)). apply atexit_cells_of_st. exact (PQTS.top_statics_exit g M H). Qed.
End PQSXC.

End PnSExitCells.
