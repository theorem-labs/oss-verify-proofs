(* past_nul 0x82728 over fs.asan: its decode table (FSW_<f>_tbl.v convention) and the return addresses of its three
   calls. 71 instructions, 284 bytes, no compressed instruction (dis of the unstripped twin, A_past_nul .. 0x82844;
   build_table steps pc + 4). The calls: `jal __wrap_malloc` 0x82768 (PC_malloc 0x53074), `jal __asan_memcpy`
   0x82784 (PC_memcpy 0x51d20, skipped by `beqz s2` 0x82774 when n = 0), `jal __asan_memset` 0x827a0 (PC_memset
   0x521bc). The error arms: `beqz a0` 0x8276c -> 0x82814 (`jal __asan_handle_no_return`; `jal abort`), and the three
   inline store checks' report calls `jal __asan_report_store1` 0x82828 / 0x82834 / 0x82840 (0x594a0).
   Control flow from the released plain lib/Prog/past_nul.v (read for the instruction sequence only).
   Rule 24: no function proved here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1w FSH_Gen FSH_Base FSW_K FSW_ret.
Import ListNotations.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the code: 71 words at A_past_nul (0x82728 .. 0x82844), and the three return addresses ---- *)
Definition RA_PN_MALLOC : Z := 0x8276c.   (* after `jal __wrap_malloc` 0x82768 *)
Definition RA_PN_MEMCPY : Z := 0x82788.   (* after `jal __asan_memcpy` 0x82784; also the `beqz s2` target *)
Definition RA_PN_MEMSET : Z := 0x827a4.   (* after `jal __asan_memset` 0x827a0 *)
Definition PN_RET : Z := 0x82810.         (* the `ret` *)
Definition pn_tbl : ctable := Eval vm_compute in build_table tfibsegs A_past_nul 71 TEmpty.
Lemma pn_tbl_ok : table_ok tfibsegs pn_tbl.
Proof.
assert (E : pn_tbl = build_table tfibsegs A_past_nul 71 TEmpty) by (vm_cast_no_check (eq_refl pn_tbl)).
rewrite E. apply build_table_ok0. unfold A_past_nul. lia.
Qed.
Lemma pn_tbl_probe : clookup pn_tbl 0x82728 = Some 0xfc010113 /\ clookup pn_tbl 0x82810 = Some 0x00008067 /\
  clookup pn_tbl 0x82840 <> None /\ clookup pn_tbl 0x82844 = None.
Proof. vm_compute. repeat split; discriminate || reflexivity. Qed.

(* the frame after any call: the seven saved registers (ra, s0, s1, s2, s3, s4, s5 of the entry) at sp + 56 .. 8, read
   back as the extra atoms 33 .. 39 of a T state (atom 32 is the shadow base; FSW_K's atom convention), i.e. the env
   Ereg regs' (fs_extraT ++ [ra; s0; s1; s2; s3; s4; s5]) *)
Definition pn_cs : list YP09.chunk :=
  [YP09.mkChunk 56 (CVal 8 (SOff 33 0)); YP09.mkChunk 48 (CVal 8 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 35 0));
   YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 24 (CVal 8 (SOff 37 0)); YP09.mkChunk 16 (CVal 8 (SOff 38 0));
   YP09.mkChunk 8 (CVal 8 (SOff 39 0))].
(* after __asan_memset: the two byte windows the three inline-checked stores write, [s2 + 1, s2 + 3) (c, then 'A') and
   [s3, s3 + 1) (the NUL at n + 17), as regions at the atoms of s2 (18) and s3 (19); their shadow entries for the token
   run, and the shadow base at s5 (21) *)
Definition pn_rs : list YP09.region := [YP09.mkRegion (Some 18%nat) 1 3 1 3 []; YP09.mkRegion (Some 19%nat) 0 1 0 1 []].
Definition pn_gf : list (nat * afact) :=
  [(18%nat, mkAF 4096 (2 ^ 47 - 8) 0); (19%nat, mkAF 4096 (2 ^ 47 - 8) 0); (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition pn_SH : list shent := [mkSHE 18 0 3; mkSHE 19 0 1].
Definition pn_Bx : sv := SOff 21 0.

(* the entry run (fss0T, frame 64) stops at the __wrap_malloc call with ra = 0x8276c, a0 = n + 18 *)
Example pn_run_entry :
  let r := sym_run_toN tfibsegs pn_tbl FUEL PC_malloc (fss0T A_past_nul 64) in
  ss_pc (fst r) = PC_malloc /\ sr_get (ss_regs (fst r)) 1%bv = SLit RA_PN_MALLOC /\
  sr_get (ss_regs (fst r)) 2%bv = SOff 2 (-64) /\ sr_get (ss_regs (fst r)) 10%bv = SOff 11 18 /\ ss_resv (fst r) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* after the call: `beqz a0` (the NULL arm, untaken: the harness malloc returns a block) *)
Example pn_run_malloc :
  snd (sym_runN tfibsegs pn_tbl FUEL (fss_retT RA_PN_MALLOC 64 pn_cs [] [])) = RS_stopped (SR_branch BC_EQ (SOff 10 0) (SLit 0)).
Proof. vm_compute. reflexivity. Qed.
(* after __asan_memcpy: straight to the __asan_memset call *)
Example pn_run_memcpy :
  let r := sym_runN tfibsegs pn_tbl FUEL (fss_retT RA_PN_MEMCPY 64 pn_cs [] []) in
  ss_pc (fst r) = PC_memset /\ snd r = RS_stopped SR_fetch /\ sr_get (ss_regs (fst r)) 1%bv = SLit RA_PN_MEMSET.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* after __asan_memset: the token run takes the three inline store checks (their report arms untaken) and stops at the
   `ret` with no open shadow obligation *)
Example pn_run_memset :
  let r := sym_runN_tok tfibsegs pn_tbl 40 pn_Bx fs_Bspan pn_SH FUEL (fss_retT RA_PN_MEMSET 64 pn_cs pn_rs pn_gf) in
  ss_pc (sh_ss (fst r)) = PN_RET /\ snd r = TS_stopped (SR_jalr (SOff 33 0)) /\ sh_obls (fst r) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
