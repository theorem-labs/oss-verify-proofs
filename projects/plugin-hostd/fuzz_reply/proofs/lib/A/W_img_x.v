(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of lib/A/W_img.v's one ledger-stated lemma, fr_img_cover (W_img.v:46)
   (a Theorem Labs lane's step 1 of route (b), 2026-10-29). W_img.v is NOT edited.
   cgif's lemma reads the image cover off the ledger (ALedger's al_img). Over ARx the same cover follows from the laws'
   field 17 (YCbqG.v:170 ARx_img_law: ly_img covers every segment), so fr_img_cover_x needs no instance fact beyond
   AR_laws_x. It discharges W_kit_x.v's Section hypothesis IMGC at fuzz_reply's image A for every ARx with the laws. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YG00 YG0f YG0n YG0d YM05.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_tbl W_place W_kit W_img.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x frsegs B ARx hl.
(* W_img.v:46 fr_img_cover, from the laws' field 17 in place of the ledger *)
Lemma fr_img_cover_x : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S Hp W mem md HAR. destruct (alx_img _ _ _ LAWS ly S Hp W mem md HAR) as [Hseg _]. split.
- destruct (Hseg Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (Hseg Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
End c.
