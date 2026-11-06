(* past_nul B 0x82894 over fs.asan-ubsan (lib/B, image tfibsegs = fs.asan-ubsan's segments): its decode table
   (FSW_<f>_tbl.v convention), the return / resume addresses of its walk, and the symbolic states the walk resumes in.
   MEASURED on the pinned fs.asan-ubsan (sha256 5ac5ce0954f8..., capstone over 0x82894 .. 0x829f0): 87 instructions,
   348 bytes, no compressed instruction (0x829f0 - 0x82894 = 348 = 4 * 87; build_table steps pc + 4). The calls:
   `jal __wrap_malloc` 0x828d4 (PC_malloc 0x530e4), `jal __asan_memcpy` 0x828f0 (PC_memcpy 0x51d90, skipped by
   `beqz s3` 0x828e0 when n = 0), `jal __asan_memset` 0x82930 (PC_memset 0x5222c, on (t + n + 1, 0, 16)); the error
   arms: `beqz a0` 0x828d8 -> 0x829ac (`jal __asan_handle_no_return` 0x5a1ec; `jal abort` 0x8cca8), the three UBSan
   pointer-overflow guards `bltu s5, s3` 0x828f8 / `beq s2, a0` 0x82918 / `bltu s5, s6` 0x82934 -> `unimp` 0x829b4, and
   the four inline store checks' report calls `jal __asan_report_store1` 0x829c4 / 0x829d0 / 0x829e0 / 0x829ec
   (0x59510; 0x829ec is the last word, falling through into asan.module_ctor 0x829f0). B is not A: UBSan adds the
   guards and B stores t[n] = 0 (0x82914, checked 0x82900 .. 0x8290c) BEFORE the memset.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base FSW_K FSW_ret.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the code: 87 words at A_past_nul (0x82894 .. 0x829ec) ---- *)
Definition RA_PN_MALLOC : Z := 0x828d8.   (* after `jal __wrap_malloc` 0x828d4 *)
Definition PN_JOIN : Z := 0x828f4.        (* after `jal __asan_memcpy` 0x828f0, and the `beqz s3` 0x828e0 target *)
Definition PN_ADD1 : Z := 0x82900.        (* after `add s2, s0, s3` 0x828fc: s2 = t + n *)
Definition RA_PN_MEMSET : Z := 0x82934.   (* after `jal __asan_memset` 0x82930 *)
Definition PN_ADD2 : Z := 0x8293c.        (* after `add a0, s0, s6` 0x82938: a0 = t + n + 17 *)
Definition PN_RET : Z := 0x829a8.         (* the `ret` *)
Definition pn_tbl : ctable := Eval vm_compute in build_table tfibsegs A_past_nul 87 TEmpty.
Lemma pn_tbl_ok : table_ok tfibsegs pn_tbl.
Proof.
assert (E : pn_tbl = build_table tfibsegs A_past_nul 87 TEmpty) by (vm_cast_no_check (eq_refl pn_tbl)).
rewrite E. apply build_table_ok0. unfold A_past_nul. lia.
Qed.
Lemma pn_tbl_probe : clookup pn_tbl 0x82894 = Some 0xfc010113 /\ clookup pn_tbl 0x829a8 = Some 0x00008067 /\
  clookup pn_tbl 0x829b4 = Some 0xc0001073 /\ clookup pn_tbl 0x829ec <> None /\ clookup pn_tbl 0x829f0 = None.
Proof. vm_compute. repeat split; discriminate || reflexivity. Qed.

(* the frame after any call: the eight saved registers (ra, s0, s1, s2, s3, s4, s5, s6 of the entry) at sp + 56 .. 0,
   read back as the extra atoms 33 .. 40 of a T state (atom 32 is the shadow base, FSW_K's atom convention), i.e. the
   env Ereg regs' (fs_extraT ++ [ra; s0; s1; s2; s3; s4; s5; s6]) *)
Definition pn_cs : list YP09.chunk :=
  [YP09.mkChunk 56 (CVal 8 (SOff 33 0)); YP09.mkChunk 48 (CVal 8 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 35 0));
   YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 24 (CVal 8 (SOff 37 0)); YP09.mkChunk 16 (CVal 8 (SOff 38 0));
   YP09.mkChunk 8 (CVal 8 (SOff 39 0)); YP09.mkChunk 0 (CVal 8 (SOff 40 0))].
(* the shadow base: s4 = atom 20 of every resumed env *)
Definition pn_Bx : sv := SOff 20 0.
Definition pn_shf : nat * afact := (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
(* the fresh atom of each re-seat (FSW_K.fsw_reseat_atom): a byte of the block t computed as the sum of two registers
   (t + n at 0x82900, t + n + 17 at 0x8293c), with its one-byte write window and its fact (t + n + 18 <= alloc_ceiling
   < 2 ^ 47) *)
Definition PN_A : nat := 41.
Definition pn_af : afact := mkAF 4096 (2 ^ 47 - 8) 0.
Definition pn_rseat : YP09.region := YP09.mkRegion (Some PN_A) 0 1 0 1 [].
Definition pn_reseat (ss : sstate) (r : bv 5) : sstate :=
  add_atom (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff PN_A 0)) (pn_rseat :: ss_mem ss) (ss_resv ss) (ss_facts ss))
    PN_A pn_af.
(* before __asan_memset: the store t[n] = 0 0x82914 through the re-seated s2, whose shadow entry covers the whole
   granule [t + n, t + n + 8) (inside the block, t 16-aligned), so the inline check 0x82900 .. 0x8290c reads 0 *)
Definition pn_SH1 : list shent := [mkSHE PN_A 0 8].
(* after __asan_memset: the stores c at s2 + 1, 'A' at s2 + 2 (window [1, 3) at s2 = atom 18), 0 at the re-seated
   a0 = t + n + 17; the shadow entries of the three inline checks: a0 [0, 1), s2 [1, 3), s3 = t + n + 1 (atom 19) [0, 1) *)
Definition pn_rs2 : list YP09.region := [YP09.mkRegion (Some 18%nat) 1 3 1 3 []].
Definition pn_gf2 : list (nat * afact) := [(18%nat, pn_af); (19%nat, pn_af); pn_shf].
Definition pn_SH2 : list shent := [mkSHE PN_A 0 1; mkSHE 18 1 3; mkSHE 19 0 1].

(* the entry run (fss0T, frame 64) stops at the __wrap_malloc call with ra = 0x828d8, a0 = n + 18 *)
Example pn_run_entry :
  let r := sym_run_toN tfibsegs pn_tbl FUEL PC_malloc (fss0T A_past_nul 64) in
  ss_pc (fst r) = PC_malloc /\ sr_get (ss_regs (fst r)) 1%bv = SLit RA_PN_MALLOC /\
  sr_get (ss_regs (fst r)) 2%bv = SOff 2 (-64) /\ sr_get (ss_regs (fst r)) 10%bv = SOff 11 18 /\ ss_resv (fst r) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* after the call: `beqz a0` 0x828d8 (the NULL arm, untaken), then `beqz s3` 0x828e0 (n = 0 skips the copy) *)
Example pn_run_malloc :
  snd (sym_runN tfibsegs pn_tbl FUEL (fss_retT RA_PN_MALLOC 64 pn_cs [] [])) = RS_stopped (SR_branch BC_EQ (SOff 10 0) (SLit 0)).
Proof. vm_compute. reflexivity. Qed.
(* at the join 0x828f4 (after __asan_memcpy, or straight from `beqz s3`): the first UBSan guard 0x828f8 *)
Example pn_run_join :
  snd (sym_runN tfibsegs pn_tbl FUEL (fss_retT PN_JOIN 64 pn_cs [] [pn_shf])) =
  RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 8 0) (SLit (-1))) (SOff 19 0)).
Proof. vm_compute. reflexivity. Qed.
(* after __asan_memset: the third UBSan guard 0x82934 *)
Example pn_run_memset :
  snd (sym_runN tfibsegs pn_tbl FUEL (fss_retT RA_PN_MEMSET 64 pn_cs pn_rs2 pn_gf2)) =
  RS_stopped (SR_branch BC_LTU (SOff 21 0) (SOff 22 0)).
Proof. vm_compute. reflexivity. Qed.
