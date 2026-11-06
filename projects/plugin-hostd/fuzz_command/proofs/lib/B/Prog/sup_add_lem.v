(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lemmas of send_message's own walk on plugin-hostd/fuzz_command's ASan image,
   ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v and A/ACk5.v at c8557374ad2e (cgif_close's frame-chain
   step and ng_chain): verbs_receive's allocator-event count is a count, the frame chain at the realigned stack
   pointer, and the stack bytes kept across the walk. The call rule for a callee that writes a program static and the
   transport lemmas its callers need (cl_callS_pg, ajournal_fp_widen, rec_repA_kept, aval_mem_kept_r ...) are the
   kit's, lib/A/Prog/PaCallPg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/send_message_l.v, with its module paths and module names changed; 69 of its 96 lines of code are new or changed and 85 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command: the lemmas every call stage uses.

   The frame chain of s0 at a program call. sup_add keeps its own frame pointer in s0 (0x8a43c `addi s0,sp,128`, the
   entry sp sp0) at every call, with the caller's ra and s0 saved at sp0 - 8 and sp0 - 16 (sa_frame); so the callee's
   afn_pre chain is the entry chain (afn_pre's achain at sp0) with the frame (sp0, ra, s0) pushed (YCbq.v achain_push),
   or the empty chain when sp0 lies within 16 bytes of the stack top. The journal from the entry keeps every byte at
   or above sp0: the call's footprint (g_rec, record.spill, the recorder's heap blocks) lies below alloc_ceiling <= sp0.
   This is the chain form of statement pass 5 (afn_pre's chain, not achain_any over astack_pres). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c sup_add_s0.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Open Scope Z_scope.

(* an 8-byte little-endian value read as a word *)
Lemma sa_rdword_aval : forall (rd : reader) a v, aval_mem rd a 8 v -> 0 <= v < 2 ^ 64 -> rdword rd a = Some v.
Proof.
intros rd a v H Hv. unfold rdword.
pose proof (H 0%nat ltac:(lia)) as E0. pose proof (H 1%nat ltac:(lia)) as E1.
pose proof (H 2%nat ltac:(lia)) as E2. pose proof (H 3%nat ltac:(lia)) as E3.
pose proof (H 4%nat ltac:(lia)) as E4. pose proof (H 5%nat ltac:(lia)) as E5.
pose proof (H 6%nat ltac:(lia)) as E6. pose proof (H 7%nat ltac:(lia)) as E7.
change (a + Z.of_nat 0) with (a + 0) in E0. change (a + Z.of_nat 1) with (a + 1) in E1.
change (a + Z.of_nat 2) with (a + 2) in E2. change (a + Z.of_nat 3) with (a + 3) in E3.
change (a + Z.of_nat 4) with (a + 4) in E4. change (a + Z.of_nat 5) with (a + 5) in E5.
change (a + Z.of_nat 6) with (a + 6) in E6. change (a + Z.of_nat 7) with (a + 7) in E7.
rewrite Z.add_0_r in E0.
rewrite E0, E1, E2, E3, E4, E5, E6, E7. f_equal. exact (YG0s.le_bytes8 v Hv).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* no byte at or above alloc_ceiling is in the call's footprint: g_rec and record.spill are image objects, the
   recorder's blocks O are live heap blocks *)
Lemma sa_fp_below : forall ly S (W : world SEGS) mem md (R : rstate) (O : list (Z * Z)) a,
AR SEGS B ly S W mem md -> rec_repA B ly S (rdW W mem) R O -> alloc_ceiling <= a -> ~ inFP (sa_FP O) a.
Proof using LAWS.
intros ly S W mem md R O a HAR (Q & HQ & HO) Ha Hin.
pose proof alloc_ceiling_value as Ec.
unfold sa_FP in Hin. rewrite !inFP_cons in Hin.
assert (C : ((A_G_REC + OFF_NCALLS + 4 <=? 2 ^ 32) && (A_G_REC + OFF_ANSWER + 8 <=? 2 ^ 32) &&
  (A_G_REC + OFF_STATE + 8 <=? 2 ^ 32) && (A_REC_SPILL + SC_SIZE <=? 2 ^ 32))%bool = true) by (vm_compute; reflexivity).
rewrite !Bool.andb_true_iff, !Z.leb_le in C.
destruct Hin as [Hr | [Hr | [Hr | [Hr | Hin]]]]; [lia .. |].
destruct Hin as ([p e] & Hpe & Hr). unfold ablocks_fp in Hpe. apply in_map_iff in Hpe as ([q n] & Eq & Hqn).
injection Eq as <- <-. cbn [fst snd] in Hr.
pose proof (lay_blocks_in _ _ _ _ _ _ HQ (q, n) (proj1 (HO (q, n)) Hqn)) as Hbl.
destruct (al_blocks _ _ LAWS ly S W mem md q n HAR Hbl) as (_ & _ & Hceil & _). lia.
Qed.

(* the frame chain of s0 = sp0 at a call of sup_add (callee entry sp sp' at least 16 below sp0) *)
Lemma sa_chain_at : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (R : rstate) (O : list (Z * Z))
lyc Sc (Wc : world SEGS) memc mdc k pos sp',
afn_pre SEGS B SUP_ADD_STK ly S W regs mem md ch ->
rec_repA B ly S (rdW W mem) R O ->
ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc memc mdc k ->
sa_frame (rdW Wc memc) (spZ regs) regs ->
sp' + 16 <= spZ regs ->
exists ch1, achain lyc (rdW Wc memc) sp' (spZ regs) ch1.
Proof using LAWS.
intros ly S W regs mem md ch R O lyc Sc Wc memc mdc k pos sp' HPRE HREP HJ HFR Hsp'.
pose proof HPRE as (HAR & _ & Hra & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop2 & Htop).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof alloc_ceiling_value as Ec.
destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch).
  apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_push ly (rdW W mem) (rdW Wc memc) (spZ regs) (s0Z regs) (raZ regs) ch sp' Hch).
  + lia.
  + intros a Ha. apply F1; [lia | lia |]. exact (sa_fp_below ly S W mem md R O a HAR HREP ltac:(lia)).
  + apply sa_rdword_aval;
    [|unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr].
    pose proof (HFR 0%nat 1 eq_refl) as H0. change (spZ regs - 8 - 8 * Z.of_nat 0) with (spZ regs - 8 - 0) in H0.
    rewrite Z.sub_0_r in H0. exact H0.
  + apply sa_rdword_aval;
    [|unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr].
    pose proof (HFR 1%nat 8 eq_refl) as H1. change (spZ regs - 8 - 8 * Z.of_nat 1) with (spZ regs - 8 - 8) in H1.
    replace (spZ regs - 16) with (spZ regs - 8 - 8) by lia. exact H1.
  + exact Hra.
  + lia.
  + apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as (q & Eq). exists (2 * q). lia.
  + exact Hlt.
  + exact Hsp'.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
End e.
End f.
End d.
