(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_g.v, with its module paths and module names changed; 100 of its 141 lines of code are new or changed and 17 lines of the source are left out. *)
(* The proofs of the plain bridge (Prog/T/SlotBridge.v): slot_world, harness_model_ok_stmt and slot_bridge.
   slot_world and the writability of the world across the call (the one clause of lib_post_g that the donor,
   fuzz_decode Prog/LLVMFuzzerTestOneInput_g.v llvm_post_g, closed vacuously because its G was []) are one image
   fact: every byte of [W_BASE_PLAIN, W_BASE_PLAIN + W_LEN) is a byte of the image's last PT_LOAD, which is writable
   and has its bytes (elf_snapshot zero-fills .bss to the page-rounded memsz), so in EVERY memory m the byte reads
   (Mem.mrd: m's byte, else the image's) and the write view (wview: m's byte, else the writable segment's) are
   Some there. world_ok checks it for the W_LEN addresses by computation, on the empty memory, which is what both
   functions fall back to where m has no byte.
   slot_bridge_holds is the donor's llvm_g_of_sr with two more steps: the world Bw from slot_world and the model
   premise llvm_model_ok Bw pl from harness_model_ok_stmt (timg_ok timg_plain by computation, length Bw by
   wm_len). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require TopOk.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem LLVMFuzzerTestOneInput_c
  SlotBridge.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the world in every memory ---- *)

Definition world_at_b (k : Z) : bool :=
  match Mem.mrd rsegs (fun _ => None) (Mem.wa (W_BASE_PLAIN + k)),
        wview rsegs (fun _ => None) (Mem.wa (W_BASE_PLAIN + k)) with
  | Some _, Some _ => true
  | _, _ => false
  end.

(* world_at_b at k, k + 1, ..., k + fuel - 1 (a Z counter: no unary index is converted). *)
Fixpoint world_from_b (k : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S f => world_at_b k && world_from_b (k + 1) f
  end.

Lemma world_from_sound : forall fuel k0, world_from_b k0 fuel = true ->
  forall k, k0 <= k < k0 + Z.of_nat fuel -> world_at_b k = true.
Proof.
  induction fuel as [|f IH]; intros k0 H k Hk; [lia|].
  cbn [world_from_b] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec k k0) as [->|Hne]; [exact H1|].
  apply (IH (k0 + 1) H2). lia.
Qed.

Lemma world_ok : world_from_b 0 (Z.to_nat W_LEN) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma world_img : forall k, 0 <= k < W_LEN ->
  Mem.mrd rsegs (fun _ => None) (Mem.wa (W_BASE_PLAIN + k)) <> None /\
  wview rsegs (fun _ => None) (Mem.wa (W_BASE_PLAIN + k)) <> None.
Proof.
  intros k Hk.
  pose proof (world_from_sound _ 0 world_ok k ltac:(rewrite Z2Nat.id by (unfold W_LEN; lia); lia)) as H.
  unfold world_at_b in H. revert H.
  destruct (Mem.mrd rsegs (fun _ => None) (Mem.wa (W_BASE_PLAIN + k)));
    destruct (wview rsegs (fun _ => None) (Mem.wa (W_BASE_PLAIN + k))); intros H; try discriminate H.
  split; discriminate.
Qed.

Lemma world_mrd : forall m k, 0 <= k < W_LEN -> Mem.mrd rsegs m (Mem.wa (W_BASE_PLAIN + k)) <> None.
Proof.
  intros m k Hk. destruct (world_img k Hk) as [H _]. unfold Mem.mrd in *.
  destruct (m (Mem.wa (W_BASE_PLAIN + k))); [discriminate | exact H].
Qed.

Lemma world_wview : forall m k, 0 <= k < W_LEN -> wview rsegs m (Mem.wa (W_BASE_PLAIN + k)) <> None.
Proof.
  intros m k Hk. destruct (world_img k Hk) as [_ H]. unfold wview in *.
  destruct (m (Mem.wa (W_BASE_PLAIN + k))); [discriminate | exact H].
Qed.

(* Every world address is writable in every memory. *)
Lemma world_writable : forall m a, W_BASE_PLAIN <= a < W_BASE_PLAIN + W_LEN -> writable_at rsegs m a.
Proof.
  intros m a Ha. unfold writable_at.
  replace a with (W_BASE_PLAIN + (a - W_BASE_PLAIN)) by lia.
  exact (world_wview m (a - W_BASE_PLAIN) ltac:(lia)).
Qed.

(* The bytes the memory holds at the world. *)
Definition world_of (m : word -> option byte) : list byte :=
  map (fun k => match Mem.mrd rsegs m (Mem.wa (W_BASE_PLAIN + Z.of_nat k)) with Some b => b | None => Z_to_bv 8 0 end)
    (seq 0 (Z.to_nat W_LEN)).

Lemma world_of_len : forall m, length (world_of m) = Z.to_nat W_LEN.
Proof. intros m. unfold world_of. rewrite length_map, length_seq. reflexivity. Qed.

Lemma world_of_wmem : forall m, wmem rsegs m (world_of m).
Proof.
  intros m. pose proof (world_of_len m) as HL.
  apply wm_intro; [| | exact HL].
  - split; [unfold W_BASE_PLAIN; lia|]. split; [rewrite HL; unfold W_BASE_PLAIN, W_LEN; lia|].
    intros i Hi. rewrite HL in Hi. unfold world_of. rewrite nth_error_map.
    rewrite (nth_error_nth' (seq 0 (Z.to_nat W_LEN)) 0%nat) by (rewrite length_seq; exact Hi).
    rewrite seq_nth by exact Hi. cbn [option_map Nat.add].
    pose proof (world_mrd m (Z.of_nat i) ltac:(unfold W_LEN in *; lia)) as H.
    destruct (Mem.mrd rsegs m (Mem.wa (W_BASE_PLAIN + Z.of_nat i))); [reflexivity | exfalso; exact (H eq_refl)].
  - split; [unfold W_BASE_PLAIN; lia|]. split; [unfold W_BASE_PLAIN, W_LEN; lia|].
    intros i Hi. exact (world_wview m i Hi).
Qed.

Lemma timg_plain_ok : timg_ok timg_plain.
Proof.
  constructor; unfold timg_plain;
    cbn [ti_io_send ti_io_recv ti_io_now ti_notice ti_spec_c24 ti_spec_pc ti_personalities]; lia.
Qed.

Theorem harness_model_ok_holds : harness_model_ok_stmt.
Proof. exact TopOk.harness_model_ok. Qed.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Theorem slot_world_holds : slot_world B API.
Proof. intros L A mem md _ _. exists (world_of mem). exact (world_of_wmem mem). Qed.

Lemma llvm_post_g : forall stk L A regs mem md p n b L' A' regs' mem' md',
  ms_segs B = rsegs ->
  Fs.fs_sorted (m_fs md) = true ->
  lib_post B API llvm_G stk L A regs mem md p L' A' regs' mem' md' ->
  sink_none B mem' md' ->
  ro_agree (ms_segs B) mem' ->
  res_ok_slots A' (lib_delta n b) ->
  (forall i, 0 <= i < n -> mbyte (ms_segs B) mem' (p + i) = mbyte (ms_segs B) mem (p + i)) ->
  lib_post_g B API llvm_G stk L A regs mem md p n b (LL 0 (m_fs md) []) L' A' regs' mem' md'.
Proof.
  intros stk L A regs mem md p n b L' A' regs' mem' md' Hsegs Hs
    (H1 & H2 & H3 & H4 & H5 & H6 & (vm' & Hmd) & H8 & H9 & H10 & H11 & H12) Hsk Hro Hr Hp.
  unfold lib_post_g.
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj _ (conj H8 (conj H9 (conj _ (conj _
    (conj H11 (conj H12 (conj eq_refl (conj eq_refl (conj Hs (conj Hsk (conj Hro (conj Hr Hp))))))))))))))))))).
  - exists vm', (m_fds md), (m_statpins md). split; [|reflexivity].
    rewrite Hmd. exact (with_vmmaps_os_upd vm' md).
  - intros a Ha Hso Hc He Hg. exact (H10 a Ha Hso Hc He Hg).
  - intros a (lo & len & Hin & Ha). destruct Hin as [E|[]]. injection E as <- <-.
    rewrite Hsegs. split; intros _; exact (world_writable _ a Ha).
Qed.

Theorem slot_bridge_holds : slot_bridge B API.
Proof.
  intros WALK HMO SW BI (LK & LR & LD) j Hj ra empty stk Hk Hra.
  unfold lib_contract_g.
  intros L A regs mem md p n pl b K Hpre GI Hrelro Hro Htask Hfrm HK.
  pose proof BI as (Hsegs & _). pose proof Hro as Hro'. rewrite Hsegs in Hro'.
  destruct Hpre as (Hlp & Hn & Hd & Hres & Hroom & Hsn & Hfd & Hfs & Hch & Hsp).
  destruct (SW L A mem md (proj1 Hlp) Hro) as (Bw & HW).
  assert (HM : llvm_model_ok Bw pl).
  { intros Ah HA. exact (HMO timg_plain Bw Ah pl timg_plain_ok (wm_len _ _ _ _ HW) HA). }
  apply (rz_conseq (ms_segs B) _ (K (LL 0 (m_fs md) []))); [| apply t_eq_sym, LK].
  apply (WALK BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Bw
    (conj Hlp (conj Hn (conj Hd (conj Hsn (conj Hsp (conj Hres (conj Hro' (conj Hrelro (conj GI
      (conj Hfrm (conj HW HM)))))))))))
    (LR b n Hroom)).
  intros c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & Hsk & Hr & Hp & Hro2 & HGI).
  apply HK. exists fx', L', A', regs', mem', md'.
  split; [exact Hc|]. split; [exact Hf|]. split; [| exact HGI].
  rewrite <- Hsegs in Hro2.
  apply llvm_post_g;
    [exact Hsegs | exact Hfs | exact Hpost | exact Hsk | exact Hro2 | rewrite LD; exact Hr | exact Hp].
Qed.

End K.
