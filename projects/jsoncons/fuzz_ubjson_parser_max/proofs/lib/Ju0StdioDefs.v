(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim
ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes SumWalkTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Export Ju0ExitBase Ju0Exit_run1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0StdioDefs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0StdioDefs.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1list"; "1nat"; "1option"; "1true"; "2eq"; "2or"; "3Z"; "4store_ok"; "5sw_post"; "6rdn"; "7loaded_segments"; "8add"; "8le"; "8of_nat"]; ["8pow"; "8sub"; "0a"; "0bs"; "0bufp"; "0bufsz"; "0f"; "0mem"; "0mem'"; "0n"; "9bv"; "9bv_unsigned"; "0su"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
swf_wpos : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
swf_fd : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
swf_buf : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
swf_bsz : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.
Definition ssp_cells (mem : word -> option byte) (can : word) : Prop :=
rdn RSEGS mem (Z_to_bv 64 0xb5f18) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe8f20))
/\ rdn RSEGS mem (Z_to_bv 64 0xe8f20) 8%nat = Some (word_to_le_bytes 8 can).
Record sw_post (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
(mem' : word -> option byte) : Prop := {
swp_agree : forall x : word,
~ (su - 112 <= bv_unsigned x < su)%Z ->
~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
mem' x = mem x;
swp_grows : mem_grows mem mem';
swp_wend : rdn RSEGS mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
swp_wpos : rdn RSEGS mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
swp_wbase : rdn RSEGS mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.
Lemma sw_post_rdn : ltac2:(TCodec.tc2 tcn__Ju0StdioDefs "RL'JyR0%211'4y8%511%311p051'8'3'2%116':r9r8r7r6r5r4%76654321'6%B1:&;&<r:r3%443281(0r2%22B1%:3941&>&=&K%12Q1A&?%11B%5231&@+2+R0%3221%;251'7%;2Q;L%:1L%>221&Ar;+S@%3221%D251%E248%:221%E2QEQ7%D1Q7%H221+Q0%J2:1%L231+Q@%M2=1%O218%D241%O2QOQB%N1QB%Q2221r<+QH%Q5221%Q7241%Q724O%Q9218%N231%QD4QCQBQMQL%Q@2R0QL%QH3QG21p041p0?1p0J1p0Q61p0QC1p0QO1pQ8R81pQDR;1pQ6RC1pQBR?1pQ<RE1pQ:RF1pQ>RA1pQJRB1pQ@RD1").
Proof.
intros mem su f bufp bufsz mem' a n bs P H Hnw D1 D2 D3.
rewrite (rdn_ext RSEGS n mem' mem a Hnw); [exact H|].
intros x Hx. apply (swp_agree _ _ _ _ _ _ P); lia.
Qed.
Lemma sw_post_store_ok : ltac2:(TCodec.tc2 tcn__Ju0StdioDefs "Q7'JyR0%211'4y8%511%311p051'8'3':r8r7r6r5r4r3%76654321'6'1&9&<r9r2%443281(5%83721%746=<;%:3913p031p0=1pQDF1pQ6N1pQBJ1pQ<Q01pQ:Q11pQ>L1pQJM1pQ@O1").
Proof. intros mem su f bufp bufsz mem' a n P H. eapply store_ok_mono; [apply (swp_grows _ _ _ _ _ _ P) | exact H]. Qed.
Record exit_common (regs : bvmap 5 word) (mem : word -> option byte)
(sp tp code : word) (tid : Z) (wp2 rp2 : word) : Prop := {
ec_sp : getr regs 2 = sp;
ec_tp : getr regs 4 = tp;
ec_a0 : getr regs 10 = code;
ec_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
ec_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
ec_sok : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
ec_tplo : (168 <= bv_unsigned tp)%Z;
ec_tphi : (bv_unsigned tp <= 4294967296)%Z;
ec_tid : (0 < tid < 2147483648)%Z;
ec_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
ec_lock : rdn RSEGS mem (Z_to_bv 64 0xe8f18) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
ec_fe : rdn RSEGS mem (Z_to_bv 64 0xb5f20) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb0228));
ec_fs : rdn RSEGS mem (Z_to_bv 64 0xb5f28) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb0220));
ec_fa : rdn RSEGS mem (Z_to_bv 64 0xb0220) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33d8c));
ec_comp : rdn RSEGS mem (Z_to_bv 64 0xb7278) 1%nat = Some [Z_to_bv 8 0];
ec_g1 : rdn RSEGS mem (Z_to_bv 64 0xb5db0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x99940));
ec_dso : rdn RSEGS mem (Z_to_bv 64 0xb6f48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb6f48));
ec_ax : exists n : nat, atexit_cells mem n;
ec_g2 : rdn RSEGS mem (Z_to_bv 64 0xb5db8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
ec_glob : stdio_globals mem;
ec_err : file_clean mem 0xb7030 wp2 rp2
}.
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
(pending : list byte) : Prop := {
sp_lock : rdn RSEGS mem (Z_to_bv 64 (0xb7120 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
sp_wpos : rdn RSEGS mem (Z_to_bv 64 (0xb7120 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0xb7120 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
sp_write : rdn RSEGS mem (Z_to_bv 64 (0xb7120 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9ec8c));
sp_buf : rdn RSEGS mem (Z_to_bv 64 (0xb7120 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
sp_bsz : rdn RSEGS mem (Z_to_bv 64 (0xb7120 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
sp_fd : rdn RSEGS mem (Z_to_bv 64 (0xb7120 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
sp_rpos : rdn RSEGS mem (Z_to_bv 64 (0xb7120 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
sp_rend : rdn RSEGS mem (Z_to_bv 64 (0xb7120 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
sp_range : (0xe8f28 <= wb < wp /\ wp <= 0xea000)%Z;
sp_len : (wp - wb = Z.of_nat (length pending))%Z;
sp_max : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
sp_ssp : ssp_cells mem can
}.
Definition exit_pre (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
(code : word) (pending : list byte) : Prop :=
exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
exit_common regs mem sp tp code tid wp2 rp2
/\ m_halted model = None /\ m_vm_lazy model = []
/\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0xb7120 wp1 rp1)
\/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
stdout_pending mem wb wp bufp bufsz rp1 can pending
/\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
