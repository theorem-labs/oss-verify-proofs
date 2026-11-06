From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i YO03.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm AllocSlots AllocRoom
  SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PSROcf.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

(* The cut-free form of the slot's cut statements (PInv.Hcut_o): the run from a cut writes the rest of the
   output, reaches the slot's post, and is cut-free. The slot's sbound has sb_cap <= CAP_AG (the agreement
   shape's room), a fact of the ghost; the malloc steps need it for room_cf. *)

(* room_cf at a slot malloc: the slot's room facts, the cap bound of the agreement shape, and the budget law. *)
(* The cut-free malloc room from the run limit of the agreement frame (SRC_LIM_MIN, zlib_limit) and the cap. *)
Lemma room_cf_slot : forall md b n, room_slots b n -> 0 <= sb_cap b <= CAP_AG -> sb_bytes b + n <= 2 ^ 29 ->
  SRC_LIM_MIN <= vm_limit (m_vmmaps md) -> room_cf md b n.
Proof.
  intros md b n HR Hc Hb Hv. apply room_cf_of_limit; [| exact HR | exact Hc | exact Hb].
  unfold SRC_LIM_MIN in Hv. exact Hv.
Qed.

Section SlotCF.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition Hcut_cf (X : ghost -> config -> Prop) (o : ghost -> list byte) : Prop :=
  forall g c, sb_cap (g_b g) <= CAP_AG -> X g c -> SROcf (ms_segs B) c (o g) (Post_o B APIf ra g).

End SlotCF.
