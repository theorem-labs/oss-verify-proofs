(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGc0.v (a working branch 30a1993588f, c5 + memnorm; file sha256 8fb81a716c51) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 16 image addresses moved by code-verified function pairs (4 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 12 code pcs the tool read as sizes, by funcpair.py), and 10 pcs named in comments; no other numeral changed. *)
(* The can_fill = 0 arm of the frame-generic Allocate walk (calloc's call: Allocate's a5 = 0).
   Ported from proofs/cgif/cgif_file_fuzzer/lib/YFhy.v..YFjg.v (cgif_file's released malloc walk, same image): the
   same scripts, with the caller's frame made abstract; the cf = 0 arm reuses the cf = 1 tail after 0x322b8.

   Allocate stores a5 (can_fill, atom 15 of the virtual regs0) at 8(sp), reloads it at 0x3227c and tests it at
   0x32280 (beqz a0, 0x322b8).  cf <> 0 runs the fill (AGi0.st_V / AGi2.kst_F); cf = 0 jumps to 0x322b8, where
   the code is the cf = 1 tail (the header writes and the ret at 0x32348).  This file holds:
   - the cf = 0 states from the test at 0x32280 to the ret, for the g path (even / odd) and the k path;
   - at_RET0 / at_RET0K: AGis.at_RET / AGj6.at_RET with the fill clause replaced by "the block keeps its
     contents" (the bytes of [Kv + RZ, Kv + RZ + n) are those of mem0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AFhy AGhy AFi1 AGhz AGho AGi0 AGi2.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGis AGj6.
Import ListNotations. Open Scope Z_scope.
Local Set Warnings "-notation-for-abbreviation".
(* The g path (n in 49..64512).  SS_V0x: the cf = 0 arm armed at the test (pc 0x32280); the run from there takes
   the branch to 0x322b8.  st_Y / st_Z / st_RET are the cf = 1 tail's (AGi0). *)
Definition SS_V0e : sstate := Eval vm_compute in st_V0 SS_Te.
Definition SS_Y0e : sstate := Eval vm_compute in st_Y SS_V0e.
Definition SS_Z0e : sstate := Eval vm_compute in st_Z SS_Y0e.
Definition SS_RET0e : sstate := Eval vm_compute in st_RET SS_Z0e.
Definition SS_V0o : sstate := Eval vm_compute in st_V0 SS_To.
Definition SS_Y0o : sstate := Eval vm_compute in st_Y SS_V0o.
Definition SS_Z0o : sstate := Eval vm_compute in st_Z SS_Y0o.
Definition SS_RET0o : sstate := Eval vm_compute in st_RET SS_Z0o.
(* The k path (n <= 48): from 0x322b8 the run reaches the ret with no further split, as in the cf = 1 arm. *)
Definition KS_V0e : sstate := Eval vm_compute in kst_V0 KS_Te.
Definition KS_RET0e : sstate := Eval vm_compute in st_RET KS_V0e.
Definition KS_V0o : sstate := Eval vm_compute in kst_V0 KS_To.
Definition KS_RET0o : sstate := Eval vm_compute in st_RET KS_V0o.
Lemma seg0_stops :
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 (runto 0x32280 SS_Te)) = RS_stopped (SR_branch BC_EQ (SOff 15 0) (SLit 0)) /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 (runto 0x32280 SS_To)) = RS_stopped (SR_branch BC_EQ (SOff 15 0) (SLit 0)) /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 (runto 0x32280 KS_Te)) = RS_stopped (SR_branch BC_EQ (SOff 15 0) (SLit 0)) /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 (runto 0x32280 KS_To)) = RS_stopped (SR_branch BC_EQ (SOff 15 0) (SLit 0)) /\
ss_pc SS_V0e = 0x32280 /\ ss_pc SS_V0o = 0x32280 /\ ss_pc KS_V0e = 0x32280 /\ ss_pc KS_V0o = 0x32280 /\
ss_pc SS_Y0e = 0x322e0 /\ ss_pc SS_Y0o = 0x322e0 /\ ss_pc SS_Z0e = 0x322e8 /\ ss_pc SS_Z0o = 0x322e8 /\
ss_pc SS_RET0e = 0x32348 /\ ss_pc SS_RET0o = 0x32348 /\ ss_pc KS_RET0e = 0x32348 /\ ss_pc KS_RET0o = 0x32348 /\
sr_get (ss_regs SS_RET0e) 10%bv = SOff aU 0 /\ sr_get (ss_regs SS_RET0o) 10%bv = SOff aU 0 /\
sr_get (ss_regs KS_RET0e) 10%bv = SOff aK 16 /\ sr_get (ss_regs KS_RET0o) 10%bv = SOff aK 16 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 SS_Z0e) = RS_stopped (SR_jalr (SOff 1 0)) /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 SS_Z0o) = RS_stopped (SR_jalr (SOff 1 0)) /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 KS_V0e) = RS_stopped (SR_jalr (SOff 1 0)) /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 KS_V0o) = RS_stopped (SR_jalr (SOff 1 0)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Section f. Context {fx : YK11.FPState}.
(* at_RET0: AGis.at_RET (same arguments, same clauses in the same order) with its last clause, the fill of
   [Kv + RZ, Kv + RZ + FILv) with 190, replaced by: the block [Kv + RZ, Kv + RZ + n) keeps mem0's bytes. *)
Section g.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z).
Variables (cl cnt v jb : Z).
Variable kz : Z.
Variable DPOST : Z -> (word -> option byte) -> Prop.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Local Abbreviation RZ := (@AGis.RZ kz).
Local Abbreviation N8D := (@AGis.N8D n).
Local Abbreviation Pv := (@AGis.Pv ly cl).
Local Abbreviation Kv := (@AGis.Kv ly cl v).
Local Abbreviation PBv := (@AGis.PBv ly n cl v kz).
Local Abbreviation SUv := (@AGis.SUv ly cl v kz).
Local Abbreviation WINT := (@AGis.WINT ly cl).
Local Abbreviation PBW := (@AGis.PBW ly n cl v kz).
Local Abbreviation WIN := (@AGis.WIN ly regs0 n cl v kz).
Local Abbreviation DZONE := (@AGis.DZONE ly).
Definition at_RET0 (odd : bool) (z : Z) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 10 = Z_to_bv 64 (Kv + RZ) /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(exists memD, DPOST z memD /\ (forall a, DZONE a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a) /\
forall x : word, DZONE (bv_unsigned x) -> mem' x = memD x) /\
(forall x : word, ~ WIN odd (bv_unsigned x) -> ~ DZONE (bv_unsigned x) -> ~ (Kv + RZ <= bv_unsigned x < Kv + RZ + n) ->
~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> mem' x = mem0 x) /\
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, WINT a \/ (Kv <= a < Kv + RZ + n) \/ PBW odd a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m Kv 8 0xCC6E96B9CC6E96B9 /\ val_mem tfibsegs m (Kv + 8) 8 (Kv + RZ - 16) /\
val_mem tfibsegs m (Kv + RZ - 16) 1 2 /\ val_mem tfibsegs m (Kv + RZ - 15) 1 (AGis.hdr_byte1 jb) /\
val_mem tfibsegs m (Kv + RZ - 14) 2 0 /\ val_mem tfibsegs m (Kv + RZ - 12) 4 n /\
val_mem tfibsegs m Pv 4 (cnt - 1) /\ val_mem tfibsegs m (T + t_unwinding) 1 0 /\
(forall x : word, SUv <= bv_unsigned x < SUv + N8D / 8 -> mem' x = Some (Z_to_bv 8 0)) /\
(odd = true -> val_mem tfibsegs m PBv 1 (n mod 8)) /\
(forall x : word, Kv + RZ <= bv_unsigned x < Kv + RZ + n -> mem' x = mem0 x).
End g.
(* at_RET0K: the same for AGj6.at_RET (the k path, RZ = 16, the block is [Kv + 16, Kv + 16 + NPv)). *)
Section k.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z).
Variables (cl cnt v jb : Z).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Local Abbreviation RZ := (@AGj6.RZ).
Local Abbreviation NPv := (@AGj6.NPv n).
Local Abbreviation N8D := (@AGj6.N8D n).
Local Abbreviation Pv := (@AGj6.Pv ly cl).
Local Abbreviation Kv := (@AGj6.Kv ly cl v).
Local Abbreviation PBv := (@AGj6.PBv ly n cl v).
Local Abbreviation SUv := (@AGj6.SUv ly cl v).
Local Abbreviation WINT := (@AGj6.WINT ly cl).
Local Abbreviation PBW := (@AGj6.PBW ly n cl v).
Local Abbreviation WIN := (@AGj6.WIN ly regs0 n cl v).
Local Abbreviation DZONE := (@AGj6.DZONE ly).
Definition at_RET0K (odd : bool) (z : Z) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 10 = Z_to_bv 64 (Kv + RZ) /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(exists memD, DPOST z memD /\ (forall a, DZONE a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a) /\
forall x : word, DZONE (bv_unsigned x) -> mem' x = memD x) /\
(forall x : word, ~ WIN odd (bv_unsigned x) -> ~ DZONE (bv_unsigned x) -> ~ (Kv + RZ <= bv_unsigned x < Kv + RZ + NPv) ->
~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> mem' x = mem0 x) /\
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, WINT a \/ (Kv <= a < Kv + RZ + NPv) \/ PBW odd a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m (Kv + RZ - 16) 1 2 /\ val_mem tfibsegs m (Kv + RZ - 15) 1 (AGj6.hdr_byte1 jb) /\
val_mem tfibsegs m (Kv + RZ - 14) 2 0 /\ val_mem tfibsegs m (Kv + RZ - 12) 4 NPv /\
val_mem tfibsegs m Pv 4 (cnt - 1) /\ val_mem tfibsegs m (T + t_unwinding) 1 0 /\
(forall x : word, SUv <= bv_unsigned x < SUv + N8D / 8 -> mem' x = Some (Z_to_bv 8 0)) /\
(odd = true -> val_mem tfibsegs m PBv 1 (NPv mod 8)) /\
(forall x : word, Kv + RZ <= bv_unsigned x < Kv + RZ + NPv -> mem' x = mem0 x).
End k.
End f.
