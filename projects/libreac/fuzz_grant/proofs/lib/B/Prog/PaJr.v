(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the step through a jump table (paj_jr_table) for the position-abstract walks, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/YC1g.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/PaJr.v, ported from a working branch a970a282587: the same text over image B's listing and walk layer (lib/B/Prog). Image B has two `jr a0` dispatches, ctrl_lay_block's at 0x83d84 and reac_box_model_block's at 0x84208; lib/B/Prog/GrantImg.v checks both tables against image B by computation. *)
(* A computed jump through a table of the image. At a `jr rs1` slot whose
   register holds VAL (A_OBJ i) + e, where the caller's equation says that this
   is BASE + k, the walk goes on at slot k with the same registers, regions and
   facts. The table's object i, the entry's value e and the target slot k are
   parameters; the caller supplies the equation that names the target (for
   ctrl_lay_block, the jump table's entry read from the image). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantSyms GrantList GrantPa GrantPaLib.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma even_of_mod4 : forall b k, b mod 4 = 0 -> k mod 2 = 0 -> (b + k) mod 2 = 0.
Proof.
intros b k Hb Hk.
pose proof (Z.div_mod b 4 ltac:(lia)) as Db. rewrite Hb, Z.add_0_r in Db.
pose proof (Z.div_mod k 2 ltac:(lia)) as Dk. rewrite Hk, Z.add_0_r in Dk.
rewrite Db, Dk. replace (4 * (b / 4) + 2 * (k / 2)) with ((2 * (b / 4) + k / 2) * 2) by lia.
apply Z_mod_mult.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g.
Context {L : ptable gsym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
Lemma paj_jr_table : forall (i : nat) (e k : Z) W E ss ms md Q w (rs1 : bv 5),
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
plookup pl_tpi (ss_pc ss) = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Jalr 0%bv rs1 0%bv, 4%Z) ->
getr (ms_regs ms) rs1 = Z_to_bv 64 (VAL (A_OBJ i) + e) ->
VAL (A_OBJ i) + e = BASE + k -> 0 <= k < 2 ^ 40 -> k mod 2 = 0 ->
(forall mat',
st_ok_pi SEGS VAL E (mkSS k (ss_regs ss) (ss_mem ss) None (ss_facts ss))
(restrict (w_H W) (mkst (ms_regs ms) (Z_to_bv 64 (BASE + k)) (ms_mem ms) (seg_rom SEGS))) ->
SRr SEGS W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (BASE + k)) (ms_mem ms) (seg_rom SEGS))
(with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr SEGS W (mkCfg ms md) Q.
Proof.
intros i e k W E ss ms md Q w rs1 HS Hrv Hpc Hdec Hrs Heq Hk Hk2 HK.
pose proof pa_B_ok as (HB0 & HB1 & HB4).
rewrite Heq in Hrs.
eapply (SRr_jr_pi W E ss ms md Q w rs1 (BASE + k) HS Hrv Hpc Hdec Hrs ltac:(lia) (even_of_mod4 _ _ HB4 Hk2)).
intros mat' ms1 -> HS1. apply HK.
unfold st_ok_pi, abs_ss, setpc.
eapply st_ok_ext; [exact HS1 | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia].
Qed.
End g.
End d.
