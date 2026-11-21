(* Modified by Theorem Labs, 2026-11: made from Reusable/YE01.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-10-29: taken from grant's no-file sink form,
   released lib/Reusable/YE01.v (projects/libreac/fuzz_grant/proofs/lib/Reusable/YE01.v), with fuzz_grant -> fuzz_identity.
   Required by the YE00 no-file form: asink_img_laws' ail_env_static now covers the ak_owned cells and
   gains ail_owned_core; aenv_of_core and asink_strs_kept are new. Measured before taking it: grant's
   version ADDS two declarations and removes NONE, so no identity consumer loses a name. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YE01.v, with its module paths changed; asink_img_laws states ail_env_static over the sink's own static cells (ak_owned) and has the law ail_owned_core (ak_owned holds the four cells astdio_env reads); the kept lemmas frame through aenv_of_core; asink_strs_kept keeps the file strings; and afopen_spec and aunlink_spec take asink_strs, which astdio_env no longer states. *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YE00_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YCbq_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.

From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YG0p_w.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Record asink_img_laws {SK : YI16.sink_head} (segs : list Segment) (B : asyms) (K : asink_syms) : Prop := mkAIL {
ail_head : ak_ofl_head K = AOFL_HEAD;
ail_env : forall a, aenv_addr K a -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4);
ail_env_off : forall a, aenv_addr K a -> AOFL_HEAD <= a < AOFL_HEAD + 8 \/ ~ (AOFL_HEAD <= a < AOFL_HEAD + 8);
ail_env_static : forall a, Exists (in_zr a) (ak_owned K) -> ~ (AOFL_HEAD <= a < AOFL_HEAD + 8);
ail_owned_core : forall a, aenv_core K a -> Exists (in_zr a) (ak_owned K);
ail_can_got : forall ly, In (z8 (ANum (ak_can_got K)) (ak_canary K)) (as_const B ly);
ail_meta : forall a, ak_meta_mem K <= a < ak_meta_mem K + 8 ->
in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\ a < AOFL_HEAD;
ail_meta_ptr : forall ly, In (z8 (ANum (ak_meta_ptr K)) (ak_meta_mem K)) (as_const B ly);
ail_errno_img : forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a;
ail_icells : forall ly c, In c (ak_icells K) -> In (z8 (ANum (fst c)) (snd c)) (as_const B ly)
}.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section J.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws segs B K.
Local Notation ajournal := (ajournal segs B).
Local Notation rd W mem := (mrestrict (w_H W) mem).
Definition ameta_inv (ly : alayout) (m : word -> option byte) (M : Z) : Prop :=
In (M, AMETA_SIZE) (ly_extra ly) /\ (forall a, in_img segs a -> a < M) /\ ameta_ok segs K m M.

Lemma ameta_ptr_of_AR : forall ly S W mem md,
AR segs B ly S W mem md -> val_mem segs (rd W mem) (ak_meta_ptr K) 8 (ak_meta_mem K).
Proof.
intros ly S W mem md HAR k Hk.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC.
pose proof (proj1 (Forall_forall _ _) HC _ (ail_meta_ptr _ _ _ AIL ly)) as Hc. unfold z8, c8, cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte segs (mrestrict (w_H W) mem) (ak_meta_ptr K + Z.of_nat k)) as [b|] eqn:E; [|discriminate Hc]. cbn in Hc.
injection Hc as Hc. f_equal. apply bv_eq. rewrite Hc, Z_to_bv_unsigned. symmetry.
change (YO0f.le_byte (ak_meta_mem K) 8 k) with (YG0f.le_byte (ak_meta_mem K) 8 k). unfold YG0f.le_byte.
unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.
End J.
End d.
