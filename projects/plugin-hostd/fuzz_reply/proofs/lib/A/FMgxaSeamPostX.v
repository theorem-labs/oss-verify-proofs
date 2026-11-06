(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx form of FMgxaSeamPost.v's two AR lemmas (Section P, step 4: the allocator relation
   after the walk), over the engine's allocator relation ARx and its laws YCbqG.AR_laws_x. FMgxaSeamPost.v is not
   edited: its AR-free lemmas (outside_dec, win_view_out, win_visible, ...) are used from it.

   The conversion is fuzz_preset's (PSnpSeamPost.v at a working branch dad42dbecbc4, :213-255) of
   a Theorem Labs lane's FMgxaSeamPost.v (3242941dc964, :205-245):
   - `Hypothesis LAWS : AR_laws tfibsegs B` -> ARx, hl and `LAWS : YCbqG.AR_laws_x tfibsegs B ARx hl` (preset: the
     fields alx_frame and alx_stack, :213-215);
   - win_owned (fm :209-220, preset :219-230): ecall_preU -> FCiface.ecall_pre_x, AR's al_stack at
     `unpoison U mem` -> the law alx_stack at mem;
   - aru_of_window (fm :228-245) -> arx_of_window (preset :238-255): the post is ARx of the munrestricted store at
     the same Hp, by the law alx_frame in place of FMupoison.ARU_frame (whose premise was the full ARU). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK04 YK0i YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Mem Frame MState FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_IImgA FMgxa_bridge FMgxaSeamBase FMgxaSeamPost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module CJF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.

Section PX. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable hl : Z.
Hypothesis LAWS : YCbqG.AR_laws_x tfibsegs B ARx hl.

(* the window condition arx_of_window takes, from "each byte of Wn is on the stack or not owned"
   (scratch below sp: the stack holds no owned byte, alx_stack; dest_ok: ~ aowned) *)
Lemma win_owned_x : forall ly S Hp W regs mem md (Wn : list (Z * Z)),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> Exists (fun r => fst r <= a < snd r) Wn ->
     (ly_stk_lo ly <= a < ly_stk_hi ly) \/ ~ aowned B ly S a) ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> CJF.outside Wn a).
Proof.
intros ly S Hp W regs mem md Wn HPRE HW a Ha Hown.
destruct (outside_dec Wn a) as [Ho|HE]; [exact Ho|]. exfalso.
destruct (HW a Ha HE) as [Hs|Hn]; [|exact (Hn Hown)].
destruct HPRE as (HAR & _).
exact (YCbqG.alx_stack _ _ _ LAWS ly S Hp W mem md a HAR Hs Hown).
Qed.

(* 4. ARx after the walk.  The law alx_frame asks: every owned byte keeps its view, every visible byte stays visible,
   the model's maps are the same, the hidden band bytes are the old ones.  munch gives the first for an owned byte
   outside Wn, so the window premise is that no owned byte lies in Wn; wmono with the image's segments gives the
   second; the model does not change (md' = md); munrestrict gives the hidden bytes back. *)
Lemma arx_of_window : forall ly S Hp W regs mem md m' (Wn : list (Z * Z)),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md ->
  CJF.munch Wn (cjstore (w_H W) mem) m' ->
  CJF.wmono tfibsegs (cjstore (w_H W) mem) m' ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> CJF.outside Wn a) ->
  (* QMm W0' (a Theorem Labs lane): the window misses the image's kept bytes, which YCbqG's frame law keeps *)
  (forall a, 0 <= a < 2 ^ 64 -> YCbqG.kept_x tfibsegs B a -> CJF.outside Wn a) ->
  exists md', same_but_materialized md md' /\ ARx ly S Hp W (munrestrict (w_H W) mem m') md'.
Proof.
intros ly S Hp W regs mem md m' Wn HPRE MU WM OWN KEPTOUT.
exists md. split; [apply same_but_materialized_refl|].
destruct HPRE as (HAR & _).
apply (YCbqG.alx_frame _ _ _ LAWS ly S Hp W mem md (munrestrict (w_H W) mem m') md HAR).
- intros a Ha Hown. exact (win_view_out (w_H W) mem m' Wn MU a Ha (OWN a Ha Hown)).
- exact (win_visible (w_H W) mem m' WM).
- reflexivity.
- reflexivity.
- reflexivity.
- intros a _ Hh. unfold munrestrict. rewrite Hh. reflexivity.
- intros a Ha Hk. apply (munrestrict_out (w_H W) mem m' Wn (Z_to_bv 64 a) MU).
  rewrite CJMS.unsigned_lit by lia. exact (KEPTOUT a Ha Hk).
Qed.

End PX.
