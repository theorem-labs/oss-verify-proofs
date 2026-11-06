(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx form of FMgxaSeamShadow.v's AR lemmas (a Theorem Labs lane's GXA seam, step 2: the musl prefix),
   over the engine's allocator relation ARx and its laws YCbqG.AR_laws_x (top_x's ARX_laws gives them at reply's cf
   instance; FMgxaSeamARX.v restates that instance). FMgxaSeamShadow.v is not edited: its AR-free lemmas
   (musl_prefix_of_ra, zsh_rodata_of_tfib, ...) are used from it.

   The conversion is fuzz_preset's (PSnpSeamShadow.v at a working branch dad42dbecbc4, :58-59 and
   :161-181) of a Theorem Labs lane's FMgxaSeamShadow.v (3242941dc964, :150-189):
   - Section hypotheses: `Hypothesis LAWS : AR_laws tfibsegs B` (fm, implicit in AR) -> ARx, hl and
     `LAWS : YCbqG.AR_laws_x tfibsegs B ARx hl` (preset: the one field `alx_zshadow`, :58-59);
   - prefix_ra_of_AR (fm :150-161) -> prefix_ra_of_ARx (preset :161-171): AR's am_zshadow (through zshadow_ok and
     Forall_forall) -> the law alx_zshadow at the image's first zero-shadow range;
   - musl_prefix_of_AR (fm :163-169) and musl_prefix_of_ARU (fm :171-189) -> one lemma musl_prefix_of_ARx (preset
     :173-181): ARx holds of mem itself (no unpoison), so the ARU detour (al_client_img, ARU_shadow_out_block,
     ARU_view_out) has no counterpart.
   Reply's numerals are FMgxaSeamShadow.v's own: the first zero-shadow range (0x10000, 0x20eb0 - 0x10000) and musl's
   prefix at sym 0x1029e = 0x10b54 (sym_musl_prefix). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YG0q YA0n YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require AsanFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_IImgA FMgxaSeamBase FMgxaSeamShadow.
Import ListNotations.
Local Open Scope Z_scope.

Section ShX. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable hl : Z.
Hypothesis LAWS : YCbqG.AR_laws_x tfibsegs B ARx hl.

(* the nine prefix bytes lie in the image's first zero-shadow range, whose shadow reads 0 (alx_zshadow) *)
Lemma prefix_ra_of_ARx : forall ly S Hp W mem md,
  In (0x10000, 0x20eb0 - 0x10000) (as_zero_shadow B) -> ARx ly S Hp W mem md ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF 0x10b54 9.
Proof.
intros ly S Hp W mem md HIn HAR.
pose proof (YCbqG.alx_zshadow _ _ _ LAWS ly S Hp W mem md (0x10000, 0x20eb0 - 0x10000) HAR
  ltac:(unfold zero_shadow_ranges; right; exact HIn)) as HZ0.
cbn [fst snd] in HZ0.
apply (range_addressable_sub _ _ 0x10000 (0x20eb0 - 0x10000)); [| lia | lia].
apply zero_shadow_range; [reflexivity | reflexivity | exact HZ0].
Qed.

(* GXA's musl_prefix_addressable on the harness's store *)
Lemma musl_prefix_of_ARx : forall ly S Hp W mem md,
  In (0x10000, 0x20eb0 - 0x10000) (as_zero_shadow B) -> ARx ly S Hp W mem md ->
  @AsanFacts.musl_prefix_addressable A_img (cjstore (w_H W) mem).
Proof.
intros ly S Hp W mem md HIn HAR. apply musl_prefix_of_ra.
exact (prefix_ra_of_ARx ly S Hp W mem md HIn HAR).
Qed.

End ShX.
