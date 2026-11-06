(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKit.v at a529a88a618 for reac-pw/fuzz_headamp image A: every address relocated (role image A -> headamp image A), the block pcs, the code table's range (1573 words: headamp's out-of-line slow blocks are four instructions long), module paths; kept_run from proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at a529a88a618 (role's cfg functions have no twin in headamp; same_io_wvb is HPgSteps'). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgPropKit.v, with its module paths and module names changed; 37 of its 105 lines of code are new or changed and 61 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKit.v at a529a88a6181 for reac-pw/fuzz_rate
   image A: rate's pcs and table range; the block post is lib/A/RtPgSteps.v rts_post (the same clauses as role's
   pa_post); kept_run is proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v's at a529a88a6181; same_io_wvb, the image's
   wx and segs_low facts are RtPgSteps' (same_io_wvb, rts_wx, rts_segs_low). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPropKit.v at 4725a2583bb7 for image B
   (fuzz_rate.asan-ubsan): image B's pcs and table range (0x80fb4 .. 0x82684), the image module AsanUbsan, the block
   post lib/AU/RtPgStepsB.v rtsb_post; pa_ becomes pab_ and kept_run pab_kept_run. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address below is measured on its unstripped
   twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): one turn of the property loop of
   LLVMFuzzerTestOneInput (0x8076c) outside the params Struct, piece by piece. Proves no function (kind: segment
   lemma): each lemma is a block of the entry function, from a fixed pc to one of its exits.

   THE BLOCKS (pod.h:397-412, the inlined pod_build loop `for (i = 0; i < nprops; i++)`)
     0x80fb4 N       `beqz t4` (what is left of the input); the sel byte (fuzz_u8 at the cursor s2: the UBSan
                     pointer test `bltu s9,s10` 0x80fbc with s9 = 1 and s10 = s2 + 1, the shadow check 0x80fcc whose
                     slow block 0x82594 is `blt; j report; j back`); `ld a0,0x110(s1)` the shape-7 flag; `beqz` 0x80ff0
                     -> 0x80ff4 (sh = 7) / 0x810a4.
     0x80ff4 SEL7    e into scope (13 shadow stores), memset(e.body, 0, 96) (0x8103c -> 0x51d54), e.size = e.type = 4,
                     the call pod_write_ent(pp, e) (0x81054 -> 0x83cc4), e out of scope, `j 0x8257c`.
     0x810a4 SELK    the key put32 (0x80001 when sel mod 4 <> 0, else 0x10003), the flags put32 0, seen' (a4),
                     first (R+0x160); `bnez` 0x811fc / `beqz` 0x81208 -> 0x81210 (params Struct) / 0x82398 (Int 7).
     0x82578 LATCH   a3 = seen (R+0x98); 0x8257c LATCH7: t0 = i + 1, s2 = s10, s6 = a3, `beq t0,np` -> 0x82688 (P1)
                     else `j 0x80fb4` (N).
   Each block is stated in the shape of a callee contract (lib/AU/RtPgStepsB.v rtsb_post: the journal without an
   event, every register outside clob kept, frames / blocks / I/O / meter kept), with the bytes it may write named by
   a set Ew and what it computes by a relation over the end world, registers and memory. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YO0f.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgStepsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments, as lib/AU/RtPgStepsB.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ---- the pcs ---- *)
Definition PAB_N : Z := 0x80fb4.
Definition PAB_SEL7 : Z := 0x80ff4.
Definition PAB_SELK : Z := 0x810a4.
Definition PAB_SELS : Z := 0x81210.
Definition PAB_SELI : Z := 0x82398.
Definition PAB_LATCH : Z := 0x82578.
Definition PAB_LATCH7 : Z := 0x8257c.
Definition PAB_P1 : Z := 0x82688.
(* the 1461 instruction words 0x80fb4 .. 0x82684: the property loop (its four blocks here, the Int-7 value pod, the
   params Struct and its pod loop) and the loop's out-of-line slow blocks 0x82594 .. 0x82684 *)
Definition pab_tbl : ctable := build_table rsegs PAB_N 1461 TEmpty.
Lemma pab_tbl_ok : table_ok rsegs pab_tbl.
Proof. apply build_table_ok0. unfold PAB_N. lia. Qed.

(* ---- the walk's context: env slot 32 is the shadow offset K; slots 33.. the block's own quantities ---- *)
Definition PABBx : sv := SOff 32 0.
Definition PABspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pab_extra (l : list Z) : list word := Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) l.
Lemma pab_extra_K : forall regs l, ew (Ereg regs (pab_extra l)) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros. reflexivity. Qed.

Section k. Context {fx : YK11.FPState}.
(* an 8-byte chunk from the cell's value *)
Lemma pab_chunk8 : forall E m base off v val,
sv_denot E v = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> val_mem rsegs m (base + off) 8 val ->
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 v)).
Proof.
intros E m base off v val Hv Hval Hw i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len cbyte] in Hi |- *.
exists (byte_of_word (sv_denot E v) i). split; [reflexivity|].
replace (base + off + i) with (base + off + Z.of_nat (Z.to_nat i)) by lia. rewrite (Hw (Z.to_nat i)) by lia.
f_equal. unfold byte_of_word, YO0f.le_byte. rewrite Hv, Z2Nat.id by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with 256.
change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small val (2 ^ 64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End k.

(* a run keeps every byte outside the zone its write windows lie in *)
Lemma pab_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.

(* ---- the walk's plumbing ---- *)
(* KE : every byte outside the zone Zn as at the block's start; a run whose write windows lie in Zn keeps it *)
Ltac pab_keep kwr :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (pab_kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the write windows of a state without one *)
Ltac pab_kwr_ro :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]); destruct Hr.
Ltac pab_run stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok pab_tbl_ok HS HJ SHOK PABspan stop; [awr_ok_tac | ] end.
Ltac pab_runb :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok pab_tbl_ok HS HJ SHOK PABspan; [awr_ok_tac | ] end.
Ltac pab_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok pab_tbl_ok HS SH PABspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* the value of register r at the end of a run, as the symbolic state holds it *)
Ltac pab_reg r :=
lazymatch goal with HS : st_ok ?sg ?E ?ssf (restrict ?H ?ms) |- context [getr (ms_regs ?ms) r] =>
rewrite (st_ok_restrict_reg sg H E ssf ms r HS);
let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end.
(* the leaf: rtsb_post's first eight clauses; the relation is left *)
Ltac pab_leaf extra :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  HAE : env_agree 32 (Ereg ?regs _) ?E, KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
apply SRr_ret;
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
split; [exact HJ|];
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs extra (w_H W) _ HS HAE); vm_compute; reflexivity|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha Hz; exact (KE a Ha Hz)|]
end.
