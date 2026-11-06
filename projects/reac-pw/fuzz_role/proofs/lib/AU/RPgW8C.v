(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 269 of its 297 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd (w5i_head), with the post
   of proofs/reac-pw/fuzz_rate/lib/A/RtPgW5Close.v at a1de917d2c21; rate's run C1 of the walk piece W8 (0x81f90 ->
   __asan_memcpy 0x51860) replaces role's Int-7 pod: the start state, the record copy's arguments and the n_ent
   update are new, the post is RtPgSteps.rts_post, the engine helpers are RtPgW8Kit's rw8_ ones. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd for reac-pw/fuzz_rate's
   image A: the two token runs w5i_head / w5i_tail become the runs B and C0 of the walk piece W8 (lib/A/RtPgW8Kit.v);
   the pcs, registers, start regions, atoms and facts are rate's; the post is RtPgSteps.rts_post (the statements
   rw8_runB_stmt and rw8_runC0_stmt) instead of a local one; the pad count of pod_pad is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW8C.v (run C1) and
   proofs/reac-pw/fuzz_rate/lib/A/RtPgW8B.v (run C0) at 8f1d7a0a9084 for the same unit's image B
   (fuzz_rate.asan-ubsan): both runs start at 0x8210c after the call of pod_write_ent; run C1's code has image B's
   three UBSan trap branches and two n_ent checks, its start state names pp, n_ent and the trap bound by extra atoms
   (no register holds pp); run C0 is three instructions on the plain engine; the post is RtPgStepsB.rtsb_post and
   the helpers are RtPgBW8Kit's rbw8_ ones; image A's run B and its pad lemmas are dropped. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgBW8C.v, with its module paths, module names, addresses and numbers changed; 351 of its 554 lines of code are new or changed and 94 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd (w5i_head), with the post
   of proofs/reac-pw/fuzz_rate/lib/A/RtPgW5Close.v at a1de917d2c21; rate's run C1 of the walk piece W8 (0x81f90 ->
   __asan_memcpy 0x51860) replaces role's Int-7 pod: the start state, the record copy's arguments and the n_ent
   update are new, the post is RtPgSteps.rts_post, the engine helpers are RtPgW8Kit's rw8_ ones. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd for reac-pw/fuzz_rate's
   image A: the two token runs w5i_head / w5i_tail become the runs B and C0 of the walk piece W8 (lib/A/RtPgW8Kit.v);
   the pcs, registers, start regions, atoms and facts are rate's; the post is RtPgSteps.rts_post (the statements
   rw8_runB_stmt and rw8_runC0_stmt) instead of a local one; the pad count of pod_pad is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW8C.v (run C1) and
   proofs/reac-pw/fuzz_rate/lib/A/RtPgW8B.v (run C0) at 8f1d7a0a9084 for the same unit's image B
   (fuzz_rate.asan-ubsan): both runs start at 0x8210c after the call of pod_write_ent; run C1's code has image B's
   three UBSan trap branches and two n_ent checks, its start state names pp, n_ent and the trap bound by extra atoms
   (no register holds pp); run C0 is three instructions on the plain engine; the post is RtPgStepsB.rtsb_post and
   the helpers are RtPgBW8Kit's rbw8_ ones; image A's run B and its pad lemmas are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgBW8C.v at 6c65f5a5cf5c for reac-pw/fuzz_role's
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; the prefix
   rbw8_ becomes w8_, RtPgMemB's rtmb_ becomes RPgMem's rm_ and RtPgStepsB's rtsb_ becomes RPgSteps' rl_; both runs
   start at 0x8190c and the cells are role B's (`first` R+0x138, k R+0x150, &pp->ent[0] R+0xd8, its complement R+0xe0,
   (&pp->n_ent) >> 3 R+0xe8, &pp->n_ent R+0x120, &e62 R+0x158), the shadow offset is s11 and &e62 is read from a cell
   (a sixth atom) instead of a register; run C1 is cut in three at the UBSan trap branch 0x81934, whose real-site
   lemma RPgStepsU.rl_trap_81934 refutes it, so the two token runs are 0x8190c -> 0x81930 and 0x81938 -> the copy. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses from the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): the runs C1 and C0 of the walk piece
   "write + record" of LLVMFuzzerTestOneInput (0x80020), from 0x8190c (after pod_write_ent) on the two values of
   `first` (R+0x138) (pod.h:432 `pp->ent[pp->n_ent++] = e`). Proves no function (kind: segment lemma).

   RUN C1, 0x8190c -> __asan_memcpy 0x5116c, `first` = 1, in three steps:
     C1a 0x8190c-0x81930:
       0x8190c-0x81914  a0 := `first` (R+0x138), a1 := k (R+0x150, overwritten below), `beqz a0` not taken
       0x81918-0x81924  the instrumented check of the 4-byte access at pp+0x4d14 (pp->n_ent): R+0xe8 holds
                        (pp+0x4d14)>>3, a1 := its shadow address (plus K in s11); the `bnez` to the error path
                        0x81a28 is decided by the full zero granule rule (0x4d14 rounds down to 0x4d10; the shadow
                        entry reaches 0x4d18)
       0x81928-0x8192c  a0 := n_ent (lw from R+0x120 = pp+0x4d14)
     the trap 0x81930-0x81934 `addiw a2,a0,1; blt a2,a0` -> 0x82604 (unimp): RPgStepsU.rl_trap_81934 (the same
       atom at offsets 1 and 0, both below 2^63), post a2 = n_ent + 1
     C1b 0x81938-0x81970:
       0x81938-0x8193c  the store check, the same shadow byte, `bnez` to the error path 0x81a3c not taken
       0x81940-0x81944  n_ent := n_ent + 1
       0x81948-0x8195c  the traps `bgeu a0,33` (n_ent <= 31) and `bltu ~(pp+0x4014), 104 n_ent` (the cell R+0xe0,
                        at least 2^63 since pp + 0x4014 < 2^63, against 104 n_ent <= 3224): neither is taken
       0x81960-0x81970  a0 := pp+0x4014 + 104 n_ent (R+0xd8 = &pp->ent[0]), a2 := 104, a1 := &e62 (R+0x158),
                        jal __asan_memcpy (ra = 0x81974)
     Atoms 32 = K, 33 = pp, 34 = kk (both the n_ent word and the cell R+0x150 hold it), 35 = the cell R+0xe0, read
     as 2^64 - 1 - (pp + 0x4014), 36 = the cell R+0x158 (&e62). The engine loads a shadow byte per run (one fresh
     atom each) and reaches the stop pc with no shadow obligation.
   RUN C0, 0x8190c -> 0x81978, `first` = 0: a0 := R+0x138 (= 0), a1 := R+0x150 (k), `beqz a0` taken. Atom 32 = k;
     no check, so the plain engine. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgMem RPgSteps RPgStepsU RPgW8Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- run C1a, the start state at 0x8190c: atoms 32 = K, 33 = pp, 34 = kk ---- *)
Definition c1a_ov : list (bv 5 * sv) := [((2%bv : bv 5), SOff 9 0); ((27%bv : bv 5), w8_Bx)].
Definition c1a_rR : YP09.region :=            (* the real frame's cells, read only; `first` = 1 *)
  YP09.mkRegion (Some 9%nat) 0xe8 0x158 0 0
   [YP09.mkChunk 0xe8 (CVal 8 (w8_shr 33 0x4d14));
    YP09.mkChunk 0x120 (CVal 8 (SOff 33 0x4d14));
    YP09.mkChunk 0x138 (CVal 8 (SLit 1));
    YP09.mkChunk 0x150 (CVal 8 (SOff 34 0))].
Definition c1a_rNent : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x4d14 0x4d18 0 0 [YP09.mkChunk 0x4d14 (CVal 4 (SOff 34 0))].
Definition c1a_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4);
           (32%nat, mkAF W8_SB W8_SB 0);
           (33%nat, mkAF 4096 140737479966720 4);
           (34%nat, mkAF 0 31 0)] [] [].
Definition c1a_ss : sstate := mkSS 0x8190c (w8_sr c1a_ov) [c1a_rR; c1a_rNent] None c1a_facts.
(* the shadow entry over pp->len .. pp->n_ent: the n_ent check needs the whole granule [0x4d10, 0x4d18) *)
Definition c1_SH : list shent := [mkSHE 33 0x4000 0x4d18].
Definition c1a_extra (pp kk : Z) : list word := [w64 W8_SB; w64 pp; w64 kk].

(* ---- run C1b, the start state at 0x81938: atoms 32 = K, 33 = pp, 34 = kk, 35 = the cell R+0xe0,
       36 = the cell R+0x158 (&e62) ---- *)
Definition c1b_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((10%bv : bv 5), SOff 34 0); ((11%bv : bv 5), w8_sh 33 0x4d14);
   ((12%bv : bv 5), SOff 34 1)].
Definition c1b_rR : YP09.region :=            (* the real frame's cells, read only *)
  YP09.mkRegion (Some 9%nat) 0xd8 0x160 0 0
   [YP09.mkChunk 0xd8 (CVal 8 (SOff 33 0x4014));
    YP09.mkChunk 0xe0 (CVal 8 (SOff 35 0));
    YP09.mkChunk 0x120 (CVal 8 (SOff 33 0x4d14));
    YP09.mkChunk 0x158 (CVal 8 (SOff 36 0))].
Definition c1b_rNent : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x4d14 0x4d18 0x4d14 0x4d18 [YP09.mkChunk 0x4d14 (CVal 4 (SOff 34 0))].
Definition c1b_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4);
           (32%nat, mkAF W8_SB W8_SB 0);
           (33%nat, mkAF 4096 140737479966720 4);
           (34%nat, mkAF 0 31 0);
           (35%nat, mkAF 9223372036854775808 18446744073709551615 0)] [] [].
Definition c1b_ss : sstate := mkSS 0x81938 (w8_sr c1b_ov) [c1b_rR; c1b_rNent] None c1b_facts.
Definition c1b_extra (pp kk FE : Z) : list word :=
  [w64 W8_SB; w64 pp; w64 kk; w64 (18446744073709551615 - (pp + 0x4014)); w64 FE].

(* ---- run C0, the start state at 0x8190c: atom 32 = k ---- *)
Definition c0_rR : YP09.region :=            (* the real frame's cells, read only; `first` = 0 *)
  YP09.mkRegion (Some 9%nat) 0x138 0x158 0 0
   [YP09.mkChunk 0x138 (CVal 8 (SLit 0)); YP09.mkChunk 0x150 (CVal 8 (SOff 32 0))].
Definition c0_facts : facts := mkFacts [(32%nat, mkAF 0 31 0)] [] [].
Definition c0_ss : sstate := mkSS 0x8190c sr_atoms [c0_rR] None c0_facts.
Definition c0_extra (kk : Z) : list word := [w64 kk].

(* ======================================== helpers ======================================== *)
Section h. Context {fx : YK11.FPState}.
(* the 64-bit complement of a value below 2^63, as the cell R+0xe0 holds it *)
Lemma c1_lnot : forall x, 0 <= x < 2 ^ 63 -> Z.lnot x mod 2 ^ 64 = 18446744073709551615 - x.
Proof.
intros x Hx. unfold Z.lnot. change (2 ^ 64) with 18446744073709551616. change (2 ^ 63) with 9223372036854775808 in Hx.
symmetry. apply (Z.mod_unique_pos _ _ (-1)); lia.
Qed.
(* the record copy's destination as the engine builds it: pp + 0x4014 + 104 * kk *)
Lemma c1_den_dst : forall E pp kk, ew E 33 = Z_to_bv 64 pp -> ew E 34 = Z_to_bv 64 kk ->
0 <= pp -> pp + 0x4014 + 104 * 31 < 2 ^ 64 -> 0 <= kk <= 31 ->
sv_denot E (SAlu ALU_ADD (SOff 33 16404) (SMd M_MUL (SOff 34 0) (SLit 104))) = w64 (pp + 0x4014 + 104 * kk).
Proof.
intros E pp kk H33 H34 Hp Hb Hk. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom_off E 33 pp 16404 H33) by lia. rewrite (U_atom E 34 kk H34) by lia. rewrite U_SLit.
rewrite (zcanon_id 104) by (unfold M64; lia).
rewrite (zcanon_id (kk * 104)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* the shadow address of the count word is a 64-bit value *)
Lemma c1_sa : forall pp, 0 <= pp -> pp + 19744 <= 2 ^ 63 -> 0 <= shadow_addr (pp + 0x4d14) < 2 ^ 64.
Proof.
intros pp H0 H1. unfold shadow_addr, SHADOW_OFF.
assert (0 <= (pp + 0x4d14) / 8 <= pp + 0x4d14)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
lia.
Qed.
End h.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* ================= run C1a: 0x8190c -> 0x81930, `first` = 1, no byte written ================= *)
Lemma w8_runC1a : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp kk : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x200 <= sp0 -> kHighMemBeg <= R - T_SEG_STK ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 (Z.shiftr (pp + 0x4d14) 3) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x120) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 1 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 kk ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4d14) 4 kk ->
0 <= kk <= 31 ->
SRr rsegs W (cfg_at rsegs W8_RA1 regs memc mdc)
(rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W8_T6 [10; 11]%bv
  (fun _ => False)
  (fun W2 regs2 mem2 =>
     getr regs2 10 = w64 kk /\ getr regs2 11 = w64 (shadow_addr (pp + 0x4d14)))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp kk
  HJ HR16 HRlo HRhi HRhb Hpp H2 H9 H27 Ve8 V120 V138 V150 Vnent Hkk.
pose proof w8_wx as Hwx. pose proof w8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hcl.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp.
unfold T_SEG_STK, ASTACK, kHighMemBeg in HRlo, HRhb.
set (E := Ereg regs (c1a_extra pp kk)).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 W8_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 kk) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (HE : E = Ereg regs (c1a_extra pp kk)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs w8_Bx c1_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor].
  apply (w8_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4d18 pp); try assumption;
  try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W8_SB) by (rewrite E32; apply unsigned_lit_small; unfold W8_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = kk) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w8_sr c1a_ov) regs).
{ apply (w8_regs_ok E regs (c1a_extra pp kk)); [exact HE|]. unfold c1a_ov.
  apply Forall_cons; [split; [apply w8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w8_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply w8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold w8_Bx. rewrite (w8_den_off E 32 W8_SB 0 E32) by (unfold W8_SB; lia).
    rewrite Z.add_0_r, H27. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E c1a_facts).
{ split; [| split; [exact I | exact I]].
  cbn [c1a_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33, U34.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ]. }
assert (HSR : 0 <= Z.shiftr (pp + 0x4d14) 3 < 2 ^ 64).
{ rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (HS : st_ok rsegs E c1a_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8190c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold c1a_ss. apply (w8_entry _ _ regs (c1a_extra pp kk) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold c1a_rR, c1a_rNent.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs E _ R 0xe8 8 (w8_shr 33 0x4d14) (Z.shiftr (pp + 0x4d14) 3));
          [ rewrite (w8_den_shr E 33 pp 0x4d14 E33) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Ve8 ].
      * apply (chunk_ok_val rsegs E _ R 0x120 8 (SOff 33 0x4d14) (pp + 0x4d14));
          [ rewrite (w8_den_off E 33 pp 0x4d14 E33) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V120 ].
      * apply (chunk_ok_val rsegs E _ R 0x138 8 (SLit 1) 1);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V138 ].
      * apply (chunk_ok_val rsegs E _ R 0x150 8 (SOff 34 0) kk);
          [ rewrite (w8_den_off E 34 kk 0 E34) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V150 ].
    + apply (rm_ro_region rsegs E (w_H W) memc 33 pp); [exact U33 | lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4d14 4 (SOff 34 0) kk);
        [ rewrite (w8_den_off E 34 kk 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 4) with 32; lia | lia | exact Vnent ].
  - unfold c1a_rR, c1a_rNent; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [r_base r_lo r_hi base_val]; rewrite U9, U33; repeat split; try exact I; lia.
  - exact HFK. }
unfold cfg_at; change (w64 W8_RA1) with (Z_to_bv 64 0x8190c).
aj_run_to_tok w8_tbl_ok HS HJ Hsh w8_Bspan 0x81930.
(* no write window: every start region is read only *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]).
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 35 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset2 | apply env_agree_ewset]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
  cbn [ms_regs restrict] in HRf;
  unfold rl_wpost; cbv beta; exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (w8_regs_kept E Ef 35 (w8_sr c1a_ov) (ss_regs ssf) regs (ms_regs msf) [10; 11]%bv HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply w8_same_io_wvb]|];
  split; [exact (mle_start MT Sc MTL)|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (w8_kept_run E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U33 in Hb; lia | ]);
    destruct Hr
  |];
  split; [rewrite (w8_reg_val E Ef 35 _ _ 10%bv (SOff 34 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (w8_den_off E 34 kk 0 E34) by lia; rewrite Z.add_0_r; reflexivity|];
  rewrite (w8_reg_val E Ef 35 _ _ 11%bv (w8_sh 33 0x4d14) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
  rewrite (w8_den_sh E 33 pp 0x4d14 E33 E32) by lia; reflexivity
  end.
Qed.

(* ================= run C1b: 0x81938 -> __asan_memcpy 0x5116c ================= *)
Lemma w8_runC1b : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp F kk : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x200 <= sp0 -> kHighMemBeg <= R - T_SEG_STK ->
0 <= F -> F + 1024 <= alloc_ceiling ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 2 = w64 R -> getr regs 9 = w64 R ->
getr regs 10 = w64 kk -> getr regs 11 = w64 (shadow_addr (pp + 0x4d14)) -> getr regs 12 = w64 (kk + 1) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 (pp + 0x4014) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (Z.lnot (pp + 0x4014) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x120) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4d14) 4 kk ->
0 <= kk <= 31 ->
SRr rsegs W (cfg_at rsegs W8_T6E regs memc mdc)
(rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W8_CPY [1; 10; 11; 12]%bv
  (fun a => pp + 0x4d14 <= a < pp + 0x4d18)
  (fun W2 regs2 mem2 =>
     getr regs2 1 = w64 W8_RA2 /\ getr regs2 10 = w64 (pp + 0x4014 + 104 * kk) /\
     getr regs2 11 = w64 (F + 0x210) /\ getr regs2 12 = w64 104 /\
     val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d14) 4 (kk + 1))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F kk
  HJ HR16 HRlo HRhi HRhb HF0 HFc Hpp Hfresh H2 H9 H10 H11 H12 Vd8 Ve0 V120 V158 Vnent Hkk.
pose proof w8_wx as Hwx. pose proof w8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hcl.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh.
unfold T_SEG_STK, ASTACK, kHighMemBeg in HRlo, HRhb.
rewrite (c1_lnot (pp + 0x4014)) in Ve0 by (change (2 ^ 63) with 9223372036854775808; lia).
pose proof (c1_sa pp ltac:(lia) ltac:(lia)) as Hsa.
set (E := Ereg regs (c1b_extra pp kk (F + 0x210))).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 W8_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 kk) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (18446744073709551615 - (pp + 0x4014))) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 (F + 0x210)) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (HE : E = Ereg regs (c1b_extra pp kk (F + 0x210))) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs w8_Bx c1_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor].
  apply (w8_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4d18 pp); try assumption;
  try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W8_SB) by (rewrite E32; apply unsigned_lit_small; unfold W8_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = kk) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = 18446744073709551615 - (pp + 0x4014))
  by (rewrite E35; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w8_sr c1b_ov) regs).
{ apply (w8_regs_ok E regs (c1b_extra pp kk (F + 0x210))); [exact HE|]. unfold c1b_ov.
  apply Forall_cons; [split; [apply w8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w8_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply w8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w8_den_off E 34 kk 0 E34) by lia. rewrite Z.add_0_r, H10. reflexivity. }
  apply Forall_cons; [split; [apply w8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w8_den_sh E 33 pp 0x4d14 E33 E32) by lia. rewrite H11. reflexivity. }
  apply Forall_cons; [split; [apply w8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w8_den_off E 34 kk 1 E34) by lia. rewrite H12. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E c1b_facts).
{ split; [| split; [exact I | exact I]].
  cbn [c1b_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33, U34, U35.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ]. }
assert (HS : st_ok rsegs E c1b_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81938) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold c1b_ss. apply (w8_entry _ _ regs (c1b_extra pp kk (F + 0x210)) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold c1b_rR, c1b_rNent.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs E _ R 0xd8 8 (SOff 33 0x4014) (pp + 0x4014));
          [ rewrite (w8_den_off E 33 pp 0x4014 E33) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vd8 ].
      * apply (chunk_ok_val rsegs E _ R 0xe0 8 (SOff 35 0) (18446744073709551615 - (pp + 0x4014)));
          [ rewrite (w8_den_off E 35 (18446744073709551615 - (pp + 0x4014)) 0 E35) by lia;
            rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Ve0 ].
      * apply (chunk_ok_val rsegs E _ R 0x120 8 (SOff 33 0x4d14) (pp + 0x4d14));
          [ rewrite (w8_den_off E 33 pp 0x4d14 E33) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V120 ].
      * apply (chunk_ok_val rsegs E _ R 0x158 8 (SOff 36 0) (F + 0x210));
          [ rewrite (w8_den_off E 36 (F + 0x210) 0 E36) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V158 ].
    + apply (rm_rw_region rsegs E (w_H W) memc 33 pp);
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4d14 4 (SOff 34 0) kk);
        [ rewrite (w8_den_off E 34 kk 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 4) with 32; lia | lia | exact Vnent ].
  - unfold c1b_rR, c1b_rNent; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [r_base r_lo r_hi base_val]; rewrite U9, U33; repeat split; try exact I; lia.
  - exact HFK. }
unfold cfg_at; change (w64 W8_T6E) with (Z_to_bv 64 0x81938).
aj_run_to_tok w8_tbl_ok HS HJ Hsh w8_Bspan 0x5116c.
(* the write window: pp->n_ent, in the fresh first block *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat pp);
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rl_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ]).
(* the state at the callee's entry *)
all: apply SRr_ret; unfold rl_wpost.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 37 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset | apply env_agree_ewset2]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & (_ & HM & _) & _);
  cbn [ms_regs restrict] in HRf;
  exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (w8_regs_kept E Ef 37 (w8_sr c1b_ov) (ss_regs ssf) regs (ms_regs msf) [1; 10; 11; 12]%bv HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply w8_same_io_wvb]|];
  split; [exact (mle_start MT Sc MTL)|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (w8_kept_run E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U33 in Hb; apply Hn; cbv beta; lia | ]);
    destruct Hr
  |];
  assert (F33 : ew Ef 33 = ew E 33) by (apply (proj1 HA); lia);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rs := fresh "Rs" in let Rn := fresh "Rn" in
  apply Forall_cons_iff in HM as [Rs HM]; apply Forall_cons_iff in HM as [Rn _];
  let Cn := fresh "Cn" in
  destruct Rn as (_ & _ & _ & Cn);
  cbn [r_chunks r_base base_val] in Cn; rewrite F33, U33 in Cn;
  rewrite Forall_forall in Cn;
  split; [rewrite (w8_reg_val E Ef 37 _ _ 1%bv (SLit 530804) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (w8_reg_val E Ef 37 _ _ 10%bv (SAlu ALU_ADD (SOff 33 16404) (SMd M_MUL (SOff 34 0) (SLit 104)))
                     HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          exact (c1_den_dst E pp kk E33 E34 ltac:(lia) ltac:(lia) ltac:(lia))|];
  split; [rewrite (w8_reg_val E Ef 37 _ _ 11%bv (SOff 36 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (w8_den_off E 36 (F + 0x210) 0 E36) by lia; rewrite Z.add_0_r; reflexivity|];
  split; [rewrite (w8_reg_val E Ef 37 _ _ 12%bv (SLit 104) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  apply (val_of_chunk_ok rsegs Ef _ pp 0x4d14 4 (SOff 34 1) (kk + 1));
  [ apply Cn; cbn [In]; repeat (first [left; reflexivity | right])
  | rewrite (sv_denot_agree 37 E Ef (SOff 34 1) HA eq_refl); exact (w8_den_off E 34 kk 1 E34 ltac:(lia) ltac:(lia))
  | change (8 * Z.of_N 4) with 32; lia | lia ]
  end.
Qed.

(* ================= run C1: the two token runs and the trap between them ================= *)
Lemma w8_runC1 : w8_runC1_stmt B MT.
Proof using MTL LAWS.
unfold w8_runC1_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos kk
  HJ HG Hpp Hfresh H2 H9 H27 Vd8 Ve0 Ve8 V120 V138 V150 V158 Vnent Hkk.
pose proof HG as (HR16 & HRlo & HRhi & HRhb & Hown & HF & HFapp & HF32).
destruct (rl_fbounds F HF32 HFapp) as (HF4096 & HFceil & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hcl.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & _ & _).
rewrite Hrq, HPS in Hpceil. rewrite HPS in Hpp.
unfold T_SEG_STK, ASTACK, kHighMemBeg in HRlo, HRhb.
(* ---- C1a ---- *)
eapply SRr_bind.
{ exact (w8_runC1a STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp kk
    HJ HR16 ltac:(unfold T_SEG_STK, ASTACK; lia) HRhi ltac:(unfold T_SEG_STK, ASTACK, kHighMemBeg; lia)
    Hpp H2 H9 H27 Ve8 V120 V138 V150 Vnent Hkk). }
cbv beta. intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hk1 & Hfr1 & Hperm1 & Hio1 & Hmo1 & Hm1
  & (A10 & A11)).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a)
  by (intros a Ha; apply Hm1; [exact Ha | intros X; exact X]).
assert (Hpp1 : In (pp, 19744) (ablocks B ly1 S1))
  by exact (Permutation_in _ (Permutation_sym Hperm1) Hpp).
assert (Hnz : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv) by exact w8_nz.
assert (R1_2 : getr regs1 2 = w64 R).
{ rewrite (Hk1 (2%bv) ltac:(vm_compute; lia)
    ltac:(cbn [In]; intros [X|[X|[]]]; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X)).
  exact H2. }
assert (R1_9 : getr regs1 9 = w64 R).
{ rewrite (Hk1 (9%bv) ltac:(vm_compute; lia)
    ltac:(cbn [In]; intros [X|[X|[]]]; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X)).
  exact H9. }
assert (Vcell1 : forall o v, 0 <= o -> o + 8 <= 0x200 -> val_mem rsegs (mrestrict (w_H W) memc) (R + o) 8 v ->
  val_mem rsegs (mrestrict (w_H W1) mem1) (R + o) 8 v).
{ intros o v Ho1 Ho2 Hv. apply (w8_val_kept (w_H W) memc); [exact Hv|]. intros y Hy. apply KA. lia. }
assert (Vnent1 : val_mem rsegs (mrestrict (w_H W1) mem1) (pp + 0x4d14) 4 kk).
{ apply (w8_val_kept (w_H W) memc); [exact Vnent|]. intros y Hy. apply KA. lia. }
(* ---- the UBSan trap 0x81934: not taken ---- *)
eapply SRr_bind.
{ exact (rl_trap_81934 B MT MTL LAWS STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 kk
    HJ1 A10 ltac:(lia)). }
cbv beta. intros W2 c2 Hw2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hk2 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hm2 & A12).
assert (Hpp2 : In (pp, 19744) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm2) Hpp1).
assert (R2_2 : getr regs2 2 = w64 R).
{ rewrite (Hk2 (2%bv) ltac:(vm_compute; lia)
    ltac:(cbn [In]; intros [X|[]]; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X)).
  exact R1_2. }
assert (R2_9 : getr regs2 9 = w64 R).
{ rewrite (Hk2 (9%bv) ltac:(vm_compute; lia)
    ltac:(cbn [In]; intros [X|[]]; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X)).
  exact R1_9. }
assert (R2_10 : getr regs2 10 = w64 kk).
{ rewrite (Hk2 (10%bv) ltac:(vm_compute; lia)
    ltac:(cbn [In]; intros [X|[]]; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X)).
  exact A10. }
assert (R2_11 : getr regs2 11 = w64 (shadow_addr (pp + 0x4d14))).
{ rewrite (Hk2 (11%bv) ltac:(vm_compute; lia)
    ltac:(cbn [In]; intros [X|[]]; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X)).
  exact A11. }
assert (Vcell2 : forall o v, 0 <= o -> o + 8 <= 0x200 -> val_mem rsegs (mrestrict (w_H W) memc) (R + o) 8 v ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (R + o) 8 v).
{ intros o v Ho1 Ho2 Hv. apply (w8_val_kept (w_H W1) mem1); [apply Vcell1; assumption|].
  intros y Hy. apply Hm2. }
assert (Vnent2 : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d14) 4 kk).
{ apply (w8_val_kept (w_H W1) mem1); [exact Vnent1|]. intros y Hy. apply Hm2. }
(* ---- C1b ---- *)
eapply SRr_mono.
{ exact (w8_runC1b STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k regs2 R pp F kk
    HJ2 HR16 ltac:(unfold T_SEG_STK, ASTACK; lia) HRhi ltac:(unfold T_SEG_STK, ASTACK, kHighMemBeg; lia)
    ltac:(lia) ltac:(lia) Hpp2 Hfresh R2_2 R2_9 R2_10 R2_11 A12
    (Vcell2 0xd8 _ ltac:(lia) ltac:(lia) Vd8) (Vcell2 0xe0 _ ltac:(lia) ltac:(lia) Ve0)
    (Vcell2 0x120 _ ltac:(lia) ltac:(lia) V120) (Vcell2 0x158 _ ltac:(lia) ltac:(lia) V158)
    Vnent2 Hkk). }
cbv beta. intros W3 c3 Hw3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hk3 & Hfr3 & Hperm3 & Hio3 & Hmo3 & Hm3 & HR3).
exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|].
split.
{ intros r Hr0 Hn. unfold w8_clobC in Hn.
  rewrite (Hk3 r Hr0 ltac:(cbn [In] in *; intros X; apply Hn; tauto)).
  rewrite (Hk2 r Hr0 ltac:(cbn [In] in *; intros [X|[]]; apply Hn; tauto)).
  apply Hk1; [exact Hr0 | cbn [In] in *; intros [X|[X|[]]]; apply Hn; tauto]. }
split; [rewrite Hfr3, Hfr2; exact Hfr1|].
split; [eapply Permutation_trans; [exact Hperm3|]; eapply Permutation_trans; [exact Hperm2 | exact Hperm1]|].
split; [eapply same_io_trans; [exact Hio1|]; eapply same_io_trans; [exact Hio2 | exact Hio3]|].
split.
{ pose proof (mle_station MT Sc S1 S2 0 0 MTL Hmo1 Hmo2) as HM12. rewrite Z.add_0_r in HM12.
  pose proof (mle_station MT Sc S2 S3 0 0 MTL HM12 Hmo3) as HM. rewrite Z.add_0_r in HM. exact HM. }
split.
{ intros a Ha Hn. rewrite (Hm3 a Ha Hn), (Hm2 a). apply Hm1; [exact Ha | intros X; exact X]. }
exact HR3.
Qed.

(* ======================================== run C0: 0x8190c -> 0x81978, `first` clear ======================================== *)
Lemma w8_runC0 : w8_runC0_stmt B MT.
Proof using MTL LAWS.
unfold w8_runC0_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pos kk HJ Hgeo H2 H9 V138 V150 Hkk.
pose proof w8_wx as Hwx. pose proof w8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgeo as (HR16 & HRlo & HRhi & HRhb & _).
unfold w8_geo in Hgeo. unfold T_SEG_STK, ASTACK, kHighMemBeg in HRlo, HRhb.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
set (E := Ereg regs (c0_extra kk)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 kk) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (HE : E = Ereg regs (c0_extra kk)) by reflexivity. clearbody E.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = kk) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (c0_extra kk)) E) by (rewrite HE; apply env_agree_refl).
assert (HS : st_ok rsegs E c0_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8190c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold c0_ss. apply (w8_entry _ _ regs (c0_extra kk) E); [exact HE| | | | |].
  - rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold c0_rR. apply Forall_cons; [|apply Forall_nil].
    apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val rsegs E _ R 0x138 8 (SLit 0) 0);
        [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V138 ].
    + apply (chunk_ok_val rsegs E _ R 0x150 8 (SOff 32 0) kk);
        [ exact (rl_den_atom E 32 kk E32 ltac:(lia)) | change (8 * Z.of_N 8) with 64; lia | lia | exact V150 ].
  - cbn. tauto.
  - split; [| split; [exact I | exact I]].
    cbn [c0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32.
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) ]. }
unfold cfg_at; change (w64 W8_RA1) with (Z_to_bv 64 0x8190c).
aj_run_to w8_tbl_ok HS HJ 0x81978.
all: lazymatch goal with
| |- awr_ok _ _ _ _ _ _ _ _ _ =>
  (* the one start region is read only *)
  change (ss_mem c0_ss) with [c0_rR];
  apply awr_ok_cons_ro; [unfold c0_rR; cbn [YP09.r_wlo YP09.r_whi]; lia|]; apply awr_ok_nil
| |- _ =>
  apply SRr_ret; red;
  exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (c0_extra kk) (w_H W) _ HS HAE);
          vm_compute; reflexivity|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply w8_same_io_wvb]|];
  split; [exact (mle_start MT Sc MTL)|];
  split;
  [ (* the run writes nothing *)
    let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (w8_kept_run E _ (w_H W) memc (ms_mem ms) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    change (ss_mem c0_ss) with [c0_rR] in Hr;
    destruct Hr as [<- | []]; unfold c0_rR in Hb; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia
  | (* a1 = k *)
    rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (11%bv : bv 5) HS);
    lazymatch type of HS with st_ok _ _ ?ssf _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssf) (11%bv : bv 5)) in
      change (sr_get (ss_regs ssf) (11%bv : bv 5)) with e end;
    exact (rl_den_atom E 32 kk E32 ltac:(lia)) ]
end.
Qed.
End c.
