(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: lemmas for the LINK of image B's skip_ws leaf walk (lib/B/Prog/skip_ws_x.v, B' = the #102 pin
   d663f82d7f48) to the caller-facing text tskip_ws_specX (lib/A/PRH_FnReader.v at the kit of record f97c8b2f046b, blob
   c30f1da6a2d1). The link itself, skip_ws_holds, is proved in lib/B/Prog/skip_ws_mn.v from skip_ws_x_holds_mnI: the text
   has the m-form post fpostWm, whose memnorm keep the plain leaf cannot give. This file holds the two lemmas it uses,
   skwb_skip_len and skwb_init. RELOCATED unchanged (no image numeral) from origin/cold/h-verbs-1-skip-union ad1c5072e3e7
   (blob 753c58f4cf41).
   THE INSTANCE: the text is image-parametric; image B's walks state it at (PA := PI_prog_B, PI := prh_img_B). The leaf
   is stated at the PER-FUNCTION listing PI_skip_ws, so the library fact is transported: PALibCore (PI := PI_prog_B) B
   gives PALibCore (PI := PI_skip_ws) B, because the two listings agree on A_OBJ 0 (the shadow-base GOT word) and
   A_OBJ 12 (the shadow-base cell) and carry the same image's symbol table (vm_compute of both sides). PALib is NOT
   usable at PI_skip_ws (its A_OBJ 1 field is refutable there), which is why both sides read PALibCore.
   THE CALL WINDOW: the text runs the journal at (STK_skip_ws + e) (spZ regs + e), the caller granting the e bytes above
   skip_ws's entry sp that hold its struct pj_in; the leaf is instantiated at that widened window, with
   FP = [(q, q + 8)], own = [], and the current state equal to the entry state, so the leaf's post journal IS
   fpostW's journal at ly' = ly, S' = S, Hp' = Hp, W' = W, k = 0.
   ASSUMED (a Section hypothesis, as the B walks' own files have it): AR_laws_x rsegs B ARx HL; discharged at the
   instance by lib/B/PALibB.v's exvi_eh_laws (lib/B/Prog/skip_ws_inst.v).
   Numerals: 16 is skip_ws's frame (LENGTH, pi_frame F_skip_ws of prh_img_B); 4 / 8 / 24 are the struct pj_in field
   widths (LENGTH); 2 ^ k are DERIVED bounds. No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16 YK06 YK04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_leaves.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import skip_ws_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* |skip x| <= |x| (PjGrammar.skip drops a prefix): the cursor the post names stays in [text, text + len] *)
Lemma skwb_skip_len : forall x : list Z, (length (PjGrammar.skip x) <= length x)%nat.
Proof.
induction x as [|b x IH]; cbn; [lia|]. destruct (PjGrammar.ws b); cbn; lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
Hypothesis TLP : PALibCore (PI := PI_prog_B) B.

(* the kit's start-of-walk journal at a WIDENED caller window: YCbqG.v ajournal_x_init's text over the window
   [sp - STK, sp + e) (the kit's own form is lib/Reusable/YCbqGcallW.v:269 ajournal_x_init_W), built
   with the journal's constructor YCbqG.ajx_intro; the stretch stores no trace (S' = S), so its wild-trace budget is
   closed by YCbqG.wild_part_same. *)
Lemma skwb_init : forall PST STK e FP ly S Hp W regs mem md ch,
afn_pre_x rsegs B ARx STK ly S Hp W regs mem md ch ->
0 <= e -> e mod 16 = 0 -> spZ regs + e <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + e -> apresent (w_H W) mem a) ->
ajournal_x (SK := SK) rsegs B PST ARx (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly S Hp W mem md 0.
Proof.
intros PST STK e FP ly S Hp W regs mem md ch
  (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) He0 He16 Hetop Hepres.
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
refine (ajx_intro (rc := rc) (SK := SK) (segs := rsegs) (B := B) (PST := PST) (ARx := ARx) (STK := STK + e)
  (sp0 := spZ regs + e) (FP := FP) (ly := ly) (S := S) (W := W) (mem := mem) (md := md) (own := []) (ly' := ly) (S' := S)
  (Hp' := Hp) (W' := W) (mem' := mem) (md' := md) (k := 0) (WS := []) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
- exact HAR.
- apply layout_le_refl.
- lia.
- apply wle_refl.
- apply aos_step_refl.
- reflexivity.
- lia.
- lia.
- intros; reflexivity.
- intros; reflexivity.
- intros; reflexivity.
- intros; reflexivity.
- intros p n i H1 H2; exfalso; exact (H2 H1).
- intros a Ha. destruct (Z.lt_ge_cases a (spZ regs)) as [Hlt|Hge]; [apply Hpres; lia | apply Hepres; lia].
- unfold astk_ok. split; [rewrite Z.add_mod by lia; rewrite Hal, He16; reflexivity|]. repeat split; lia.
- intros; reflexivity.
- exact HQT.
- apply wild_part_same.
Qed.

End b.
