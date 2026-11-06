(* AEntryRead.v - the entry image is READABLE at and above the entry sp: for every address from usp up to the entry
   page top, the start-up memory wrap_mem (YK11.v:2199-2208) is defined.  This is the [usp, ly_top) piece of the
   readable-stack clause a Theorem Labs lane reverted to (B's fr_lib_pre_cf STKR, lib/B/W_LLVMFuzzerTestOneInput_cut.v:265),
   and `ly_top <= page_ceil (usp + 1) <= entry_page_top` (AD1g.v:988 uTopRel) puts that whole range inside the page
   this file covers.

   It is NOT proved by unfolding LPS - LPS ships compiled, there is no StackLayout.v or Run.v source on the build
   VMs - but from three lemmas LPS already exports, found by Search:
     YK0n.stm_at                     stack_to_mem sp bytes addr = nth_error bytes i, for i < length bytes
     Run.entry_stack_image_top       usp + |entry_stack_image ..| = entry_page_top sp (build_stack_bytes ..)
     YK11.wrap_above_sp              at or above sp, wrap_mem is stack_to_mem over entry_stack_image
   The kit already has the twin BELOW the entry sp - YK1b.v:91 wrap_mem_window_defined on
   [sp - stack_max_size, sp) - so this file is the arm above it, and the two together cover
   [usp - 8 MiB, entry_page_top).  Nothing here is image data, so it holds for every unit. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0n YK1b.
Import ListNotations.
Local Open Scope Z_scope.

Section a.
Variable ph : PhdrInfo.
Variable sp : word.
Variables argv envp : list (list byte).
Variables uid hw : word.
Variable rnd : EntryDraw.
#[local] Notation IMG := (Run.entry_stack_image ph sp argv envp uid hw rnd).
#[local] Notation PTOP := (Run.entry_page_top sp (StackLayout.build_stack_bytes ph sp argv envp uid hw rnd)).

(* the entry image's bytes, by index: every index below its length reads *)
Lemma entry_img_nth : forall i, (i < length IMG)%nat -> exists b, nth_error IMG i = Some b.
Proof. intros i Hi. apply nth_error_Some in Hi. destruct (nth_error IMG i) as [b|]; [exists b; reflexivity|congruence]. Qed.

(* THE LEMMA: readable from the entry sp up to the entry page top *)
Lemma wrap_mem_entry_defined : forall x : word,
  bv_unsigned sp <= bv_unsigned x -> bv_unsigned x < PTOP ->
  wrap_mem ph sp argv envp uid hw rnd x <> None.
Proof.
  intros x Hlo Hhi.
  pose proof (Run.entry_stack_image_top ph sp argv envp uid hw rnd) as HT.
  set (i := Z.to_nat (bv_unsigned x - bv_unsigned sp)).
  assert (Hi : (i < length IMG)%nat) by (unfold i; lia).
  assert (Hai : bv_unsigned x = bv_unsigned sp + Z.of_nat i) by (unfold i; lia).
  rewrite (YK11.wrap_above_sp ph sp argv envp x uid hw rnd Hlo).
  rewrite (YK0n.stm_at sp IMG x i Hi Hai).
  destruct (entry_img_nth i Hi) as (b & Hb). rewrite Hb. discriminate.
Qed.

(* the same as a byte-range statement, the shape a consumer states at the entry *)
Lemma wrap_mem_entry_range : forall lo hi,
  bv_unsigned sp <= lo -> hi <= PTOP ->
  forall a, lo <= a < hi -> 0 <= a < 2 ^ 64 -> wrap_mem ph sp argv envp uid hw rnd (Z_to_bv 64 a) <> None.
Proof.
  intros lo hi Hlo Hhi a Ha Hr. apply wrap_mem_entry_defined; rewrite Z_to_bv_unsigned; unfold bv_wrap;
  change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_small by lia; lia.
Qed.
End a.
