From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Cells.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 YL0i YO03.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0 Contract FrameAPI MemNorm AllocSlots AllocRoom
  SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg Require Import SInv STac SGlue SMid.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

(* The cut-free form of the slot's cuts (agreement frame, SlotAgree.SRcf). The cap of the slot's bound is the
   agreement shape's (at most CAP_AG): a premise for each ghost, carried from the entry to every cut. *)
Definition capag (g : ghost) : Prop := sb_cap (g_b g) <= CAP_AG.

Section CInv.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition Hcut_cf (X : ghost -> config -> Prop) : Prop :=
  forall g c, capag g -> X g c -> SRcf B c (Post B APIf ra g).

End CInv.

Lemma room_cf_of : forall md b0 hb n, slot_room b0 -> sb_cap b0 <= CAP_AG ->
  (length hb <= 16)%nat -> 0 <= hb_bytes hb <= 2 ^ 24 -> 0 <= n <= 2 ^ 20 ->
  SRC_LIM_MIN <= vm_limit (m_vmmaps md) -> room_cf md (sb_hb b0 hb) n.
Proof.
  intros md b0 hb n HR HC Hlen HS Hn HL.
  pose proof (resb_room b0 hb n HR Hlen HS Hn) as RS.
  destruct HR as (H1 & H2 & H3 & H4).
  apply room_cf_of_limit; [unfold SRC_LIM_MIN in HL; exact HL | exact RS | | ];
    unfold sb_hb; cbn [sb_live sb_bytes sb_cap]; lia.
Qed.
