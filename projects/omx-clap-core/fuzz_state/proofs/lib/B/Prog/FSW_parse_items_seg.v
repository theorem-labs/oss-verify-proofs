(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) the MEASURED SEGMENTS of parse_items' member path on image B,
   in the form of the A walk's lib/A/FSW_parse_items_seg.v (a working branch 4480a5df1ae): every
   segment starts at a state the walk builds from a call's resume (FSW_ret.fss_retT, its write windows narrowed to what
   the segment writes, the kit's builders FSW_parse_items_kit.v) and runs, with the engine, straight to the next call
   stop or to the `ret`, raising NO obligation. B CALLS skip_ws where A inlines the white-space loops, so B's segments
   are cut at those calls and none needs a white-space window:
     C   grow #1 resume 0x84fb0 (a0 = 0)        -> skip_ws #2 entry 0x83598, ra 0x85000   (the frame slots 0x84fc8 ..
                                                     0x84ff0: 1 << 60, shadow (v + 32), v + 32, shadow (v + 24), v + 24;
                                                     s6 = v + 40, s8 = shadow (v + 40))
     J   grow #2 resume 0x85250 (a0 = 0)        -> skip_ws #2 entry, ra 0x85000          (0x85250 beqz -> 0x84ff4)
     D   skip_ws #2 resume 0x85000, byte 0x22   -> parse_string 0x85534, ra 0x85048
     E   parse_string resume 0x85048 (a0 = key) -> skip_ws #3 entry, ra 0x850bc          (keys[n] := key, 0x850ac)
     F   skip_ws #3 resume 0x850bc, byte `:`    -> __asan_memset 0x5222c, ra 0x85170     (in->p + 1, 0x8510c; a0 = the
                                                     kid kids + 56 n, a2 = 56)
     G   __asan_memset resume 0x85170           -> parse_value 0x82fcc, ra 0x851d0       (a0 = q, a1 = the kid)
     H   parse_value resume 0x851d0 (a0 = 0)    -> skip_ws #4 entry, ra 0x851f4          (v->n := n + 1, 0x851e0)
     Ic  skip_ws #4 resume 0x851f4, byte `,`    -> grow 0x83ca8, ra 0x85250              (in->p + 1, 0x85244)
     Ie  skip_ws #4 resume 0x851f4, byte `}`    -> the `ret` 0x852fc                     (in->p + 1, in->depth - 1)
   THE CURSOR BYTE after each skip_ws is a read-only literal window at the in->p atom (FSW_parse_items_kit.pik_treg) with
   the guard `in->p < in->end` as a fact: the writer text gives both. So segment F decides the `:` test 0x850f4 and the
   end test 0x850d4 itself: the fuzz_free block 0x85300 (entered only from those two edges) is not reached.
   B's UBSan checks the engine cannot decide from atom ranges are given as facts, each true under the premises: the
   index check (n + 2 ^ 60) >> 61 = 0 at 0x85088 (pib_c_n60), the slot and kid order checks `bltu slot, base` at
   0x8508c / 0x8514c / 0x851ac (pib_geu), and the multiplication check `mulh n 56` / `(56 n) >> 63` at 0x85164 /
   0x851c4 (pib_c_m56). The slots keys + 8 n and kids + 56 n are env atoms xatom 22 / xatom 23 with an alias fact each
   (YP0e.aliased2), as in the A walk.
   ATOMS at every member-loop resume: atom 9 = s1 = q, atom 19 = s3 = v, atom 32 = the shadow base, xatom 0 / 1 / 2 =
   in->p / in->end / in->depth, xatom 3 .. 15 = the entry ra and s0 .. s11 (pi_saved_regs, frame slots 136 .. 40),
   xatom 16 .. 19 = kids / keys / n / cap, xatom 20 / 21 = the key block and its length (after parse_string), xatom 22 /
   23 = the slots. MEASURED on image B with the engine (vm_compute), 2026-10-29, scratch
   (internal path) (deleted).
   rule 24: no function is proved in this file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the walk's fixed data ================= *)
(* the frame after the member-loop set-up 0x84fb4 .. 0x84ff0 (segment C) *)
Definition pib_csL : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SLit 1152921504606846976)); YP09.mkChunk 8 (CVal 8 (pi_shx 19 32));
   YP09.mkChunk 16 (CVal 8 (SOff 19 32)); YP09.mkChunk 24 (CVal 8 (pi_shx 19 24));
   YP09.mkChunk 32 (CVal 8 (SOff 19 24))] ++ pi_cs.
(* the callee-saved registers at grow #1 (before the set-up) and in the member loop (every later call) *)
Definition pib_R0 : list (bv 5 * sv) :=
  [(8%bv, SOff 9 16); (18%bv, SLit 1); (20%bv, SOff 9 8); (21%bv, SLit 18446744073709551615);
   (23%bv, pi_shx 9 8); (25%bv, pi_shx 9 16); (26%bv, SOff 32 0); (27%bv, pi_shx 9 0)].
Definition pib_RL : list (bv 5 * sv) :=
  [(8%bv, SOff 9 16); (18%bv, SLit 1); (20%bv, SOff 9 8); (21%bv, SLit 18446744073709551615); (22%bv, SOff 19 40);
   (23%bv, pi_shx 9 8); (24%bv, pi_shx 19 40); (25%bv, pi_shx 9 16); (26%bv, SOff 32 0); (27%bv, pi_shx 9 0)].
(* v after a grow: type 6, kids' at 24, keys' at 32, n at 40, cap' at 48 *)
Definition pib_vch : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 4 (SLit 6)); YP09.mkChunk 24 (CVal 8 (SOff (xatom 16) 0));
   YP09.mkChunk 32 (CVal 8 (SOff (xatom 17) 0)); YP09.mkChunk 40 (CVal 8 (SOff (xatom 18) 0));
   YP09.mkChunk 48 (CVal 8 (SOff (xatom 19) 0))].
Definition pib_vR : YP09.region := YP09.mkRegion (Some 19%nat) 0 56 0 56 pib_vch.
Definition pib_rs : list YP09.region := [pi_qR; pib_vR].
(* the atom facts at a member-loop resume; after parse_string also the key block and its length *)
Definition pib_gf : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (19%nat, mkAF 4096 (2 ^ 47 - 56) 3);
   (xatom 0, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (xatom 1, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (xatom 2, mkAF 1 2 0);
   (xatom 16, mkAF 4096 (2 ^ 47 - 2 ^ 23) 4); (xatom 17, mkAF 4096 (2 ^ 47 - 2 ^ 23) 4);
   (xatom 18, mkAF 0 (2 ^ 54) 0); (xatom 19, mkAF 0 (2 ^ 54) 0)].
Definition pib_gfP : list (nat * afact) :=
  pib_gf ++ [(xatom 20, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (xatom 21, mkAF 0 (2 ^ 54) 0)].
(* the resume env's extra words: in->p, in->end, in->depth, the entry ra / s0 .. s11, kids, keys, n, cap; after
   parse_string the key block a and its length, the key slot keys + 8 n and the kid kids + 56 n *)
Definition pib_xs (p e d : Z) (xr : list word) (kids keys n cap : Z) : list word :=
  [Z_to_bv 64 p; Z_to_bv 64 e; Z_to_bv 64 d] ++ xr ++ [Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 n; Z_to_bv 64 cap].
Definition pib_xsK (p e d : Z) (xr : list word) (kids keys n cap a klen : Z) : list word :=
  pib_xs p e d xr kids keys n cap ++
  [Z_to_bv 64 a; Z_to_bv 64 klen; Z_to_bv 64 (keys + 8 * n); Z_to_bv 64 (kids + 56 * n)].
(* the region list of a resume state with each write window given: the frame, the two shadow-base cells, q, v *)
Definition pib_rgs (cs : list YP09.chunk) (fw qw vw : Z * Z) : list YP09.region :=
  [YP09.mkRegion (Some 2%nat) 0 144 (fst fw) (snd fw) cs; fs_got_region; fs_bcell_region 32;
   YP09.mkRegion (Some 9%nat) 0 24 (fst qw) (snd qw) (YP09.r_chunks pi_qR);
   YP09.mkRegion (Some 19%nat) 0 56 (fst vw) (snd vw) pib_vch].
(* a segment's start state: the resume at r, its windows narrowed (rgs), registers R, extra regions, facts *)
Definition pib_start (r : Z) (cs : list YP09.chunk) (gf : list (nat * afact)) (rgs : list YP09.region)
  (R : list (bv 5 * sv)) (ex : list YP09.region) (atl : list (nat * afact)) (cds : list acond) (al : list (sv * sv))
  : sstate :=
  pik_addf (pik_addr (pik_setr (pik_setm (fss_retT r 144 cs pib_rs gf) rgs) R) ex) atl cds al.
(* the guard in->p < in->end *)
Definition pib_wsc0 : list acond := [mkAC BC_LTU (SOff (xatom 0) 0) (SOff (xatom 1) 0)].
(* the key slot: an 8-byte writable window at xatom 22, aliased to keys + 8 n *)
Definition pib_kaR : YP09.region := YP09.mkRegion (Some (xatom 22)) 0 8 0 8 [].
Definition pib_al_ka : sv * sv :=
  (SAlu ALU_ADD (SOff (xatom 17) 0) (SAlu ALU_SLL (SOff (xatom 18) 0) (SLit 3)), SOff (xatom 22) 0).
(* the kid: kids + 56 n, which B computes as ((n << 6) - (n << 3)) + kids, aliased to xatom 23 *)
Definition pib_n56 : sv :=
  SAlu ALU_SUB (SAlu ALU_SLL (SOff (xatom 18) 0) (SLit 6)) (SAlu ALU_SLL (SOff (xatom 18) 0) (SLit 3)).
Definition pib_al_vk : sv * sv := (SAlu ALU_ADD pib_n56 (SOff (xatom 16) 0), SOff (xatom 23) 0).
Definition pib_gf_ka : list (nat * afact) := [(xatom 22, mkAF 4096 (2 ^ 47 - 2 ^ 23) 3)].
Definition pib_gf_vk : list (nat * afact) := [(xatom 23, mkAF 4096 (2 ^ 47 - 2 ^ 23) 3)].
(* the UBSan facts: the index check of keys[n], the slot / kid order, the multiplication check of 56 n *)
Definition pib_c_n60 : acond :=
  mkAC BC_EQ (SAlu ALU_SRL (SOff (xatom 18) 1152921504606846976) (SLit 61)) (SLit 0).
Definition pib_geu (a b : nat) : acond := mkAC BC_GEU (SOff a 0) (SOff b 0).
Definition pib_c_m56 : acond :=
  mkAC BC_EQ (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff (xatom 18) 0) (SLit 56))
    (SAlu ALU_SRA (SMd M_MUL (SOff (xatom 18) 0) (SLit 56)) (SLit 63)))) (SLit 0).
(* the shadow entries of a member-loop run: q (atom 9), v (atom 19); the cursor byte; the key slot *)
Definition pib_SHm : list shent := [mkSHE 9 0 24; mkSHE 19 0 56].
Definition pib_SHc : list shent := mkSHE (xatom 0) 0 1 :: pib_SHm.
Definition pib_SHe : list shent := mkSHE (xatom 22) 0 8 :: pib_SHm.
Definition pib_run (SH : list shent) (s : sstate) : shst * trun_status :=
  sym_runN_tok tfibsegs pitems_tbl (run_K 0 fs_Bx SH s) fs_Bx fs_Bspan SH FUEL s.
Definition pib_regs_are (s : sstate) (l : list (bv 5 * sv)) : bool :=
  forallb (fun q => sv_eqb (sr_get (ss_regs s) (fst q)) (snd q)) l.

(* ================= the nine start states ================= *)
Definition pib_RO : Z * Z := (0, 0).
Definition pib_ss_C : sstate :=
  pib_start 0x84fb0 pi_cs pib_gf (pib_rgs pi_cs (0, 144) pib_RO pib_RO) ((10%bv, SLit 0) :: pib_R0) [] [] [] [].
Definition pib_ss_J : sstate :=
  pib_start 0x85250 pib_csL pib_gf (pib_rgs pib_csL pib_RO pib_RO pib_RO) ((10%bv, SLit 0) :: pib_RL) [] [] [] [].
Definition pib_ss_D : sstate :=
  pib_start 0x85000 pib_csL pib_gf (pib_rgs pib_csL pib_RO pib_RO pib_RO) pib_RL [pik_treg (xatom 0) 0 [34]] []
    pib_wsc0 [].
Definition pib_ss_E : sstate :=
  pib_start 0x85048 pib_csL pib_gfP (pib_rgs pib_csL pib_RO pib_RO pib_RO) ((10%bv, SOff (xatom 20) 0) :: pib_RL)
    [pib_kaR] pib_gf_ka [pib_c_n60; pib_geu (xatom 22) (xatom 17)] [pib_al_ka].
Definition pib_ss_F : sstate :=
  pib_start 0x850bc pib_csL pib_gfP (pib_rgs pib_csL pib_RO (0, 24) pib_RO) pib_RL [pik_treg (xatom 0) 0 [58]]
    pib_gf_vk (pib_c_m56 :: pib_geu (xatom 23) (xatom 16) :: pib_wsc0) [pib_al_vk].
Definition pib_ss_G : sstate :=
  pib_start 0x85170 pib_csL pib_gfP (pib_rgs pib_csL pib_RO pib_RO pib_RO) pib_RL [] pib_gf_vk
    [pib_c_m56; pib_geu (xatom 23) (xatom 16)] [pib_al_vk].
Definition pib_ss_H : sstate :=
  pib_start 0x851d0 pib_csL pib_gfP (pib_rgs pib_csL pib_RO pib_RO (40, 48)) ((10%bv, SLit 0) :: pib_RL) [] [] [] [].
Definition pib_ss_Ic : sstate :=
  pib_start 0x851f4 pib_csL pib_gfP (pib_rgs pib_csL pib_RO (0, 24) pib_RO) pib_RL [pik_treg (xatom 0) 0 [44]] []
    pib_wsc0 [].
Definition pib_ss_Ie : sstate :=
  pib_start 0x851f4 pib_csL pib_gfP (pib_rgs pib_csL pib_RO (0, 24) pib_RO) pib_RL [pik_treg (xatom 0) 0 [125]] []
    pib_wsc0 [].

(* ================= the runs (measured: each stops at the next call, or at the ret, with no obligation) ========== *)
Definition pib_st_C : shst := fst (pib_run pib_SHm pib_ss_C).
Definition pib_st_J : shst := fst (pib_run pib_SHm pib_ss_J).
Definition pib_st_D : shst := fst (pib_run pib_SHc pib_ss_D).
Definition pib_st_E : shst := fst (pib_run pib_SHe pib_ss_E).
Definition pib_st_F : shst := fst (pib_run pib_SHc pib_ss_F).
Definition pib_st_G : shst := fst (pib_run pib_SHm pib_ss_G).
Definition pib_st_H : shst := fst (pib_run pib_SHm pib_ss_H).
Definition pib_st_Ic : shst := fst (pib_run pib_SHc pib_ss_Ic).
Definition pib_st_Ie : shst := fst (pib_run pib_SHc pib_ss_Ie).
Lemma pib_run_C : pib_run pib_SHm pib_ss_C = (pib_st_C, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma pib_run_J : pib_run pib_SHm pib_ss_J = (pib_st_J, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma pib_run_D : pib_run pib_SHc pib_ss_D = (pib_st_D, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma pib_run_E : pib_run pib_SHe pib_ss_E = (pib_st_E, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma pib_run_F : pib_run pib_SHc pib_ss_F = (pib_st_F, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma pib_run_G : pib_run pib_SHm pib_ss_G = (pib_st_G, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma pib_run_H : pib_run pib_SHm pib_ss_H = (pib_st_H, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma pib_run_Ic : pib_run pib_SHc pib_ss_Ic = (pib_st_Ic, TS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma pib_run_Ie : pib_run pib_SHc pib_ss_Ie = (pib_st_Ie, TS_stopped (SR_jalr (SOff (xatom 3) 0))).
Proof. vm_compute. reflexivity. Qed.
(* the static checks of each run *)
Local Ltac pib_static := vm_compute; reflexivity.
Lemma pib_static_C : sh_static_ok (run_K 0 fs_Bx pib_SHm pib_ss_C) fs_Bx fs_Bspan pib_SHm
  (ss_facts pib_ss_C) (ss_mem pib_ss_C) = true.
Proof. pib_static. Qed.
Lemma pib_static_J : sh_static_ok (run_K 0 fs_Bx pib_SHm pib_ss_J) fs_Bx fs_Bspan pib_SHm
  (ss_facts pib_ss_J) (ss_mem pib_ss_J) = true.
Proof. pib_static. Qed.
Lemma pib_static_D : sh_static_ok (run_K 0 fs_Bx pib_SHc pib_ss_D) fs_Bx fs_Bspan pib_SHc
  (ss_facts pib_ss_D) (ss_mem pib_ss_D) = true.
Proof. pib_static. Qed.
Lemma pib_static_E : sh_static_ok (run_K 0 fs_Bx pib_SHe pib_ss_E) fs_Bx fs_Bspan pib_SHe
  (ss_facts pib_ss_E) (ss_mem pib_ss_E) = true.
Proof. pib_static. Qed.
Lemma pib_static_F : sh_static_ok (run_K 0 fs_Bx pib_SHc pib_ss_F) fs_Bx fs_Bspan pib_SHc
  (ss_facts pib_ss_F) (ss_mem pib_ss_F) = true.
Proof. pib_static. Qed.
Lemma pib_static_G : sh_static_ok (run_K 0 fs_Bx pib_SHm pib_ss_G) fs_Bx fs_Bspan pib_SHm
  (ss_facts pib_ss_G) (ss_mem pib_ss_G) = true.
Proof. pib_static. Qed.
Lemma pib_static_H : sh_static_ok (run_K 0 fs_Bx pib_SHm pib_ss_H) fs_Bx fs_Bspan pib_SHm
  (ss_facts pib_ss_H) (ss_mem pib_ss_H) = true.
Proof. pib_static. Qed.
Lemma pib_static_Ic : sh_static_ok (run_K 0 fs_Bx pib_SHc pib_ss_Ic) fs_Bx fs_Bspan pib_SHc
  (ss_facts pib_ss_Ic) (ss_mem pib_ss_Ic) = true.
Proof. pib_static. Qed.
Lemma pib_static_Ie : sh_static_ok (run_K 0 fs_Bx pib_SHc pib_ss_Ie) fs_Bx fs_Bspan pib_SHc
  (ss_facts pib_ss_Ie) (ss_mem pib_ss_Ie) = true.
Proof. pib_static. Qed.
