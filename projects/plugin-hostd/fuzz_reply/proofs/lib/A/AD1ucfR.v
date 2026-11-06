From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0m YP09 YI04 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbq YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YA0nH YA0oR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0dcf YG0ncf YGcfExtra YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k AB1v AF0m AD1ycf AD1ucf.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* FINV (AD1ucf.v) at a world step that may hide more at DS (wle_in, YA0nH.v; wle' = wle_in RZ): every FINV
   fact is a byte value (val_mem, the zero bytes of the meta area), so it moves when the bytes FINV reads, the frame set
   of finv_frame (finv_img and the extra zones of ly), lie outside DS. *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* AD1ucf.v's Section-local constant unfolding, restated *)
Local Ltac kcst := unfold A_threaded, A_need_locks, A_ofl_lock, A_ofl_head, FF_canary, FF_got_canary,
FF_meta_ptr, FF_meta_mem, A_stdio_read, A_stdio_write, A_stdio_seek, A_stdio_close in *.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.

Lemma FINV_wle_in_off : forall (DS : Z -> Prop) (W W' : world tfibsegs) ly mem,
  wle_in tfibsegs DS W W' ->
  (forall a, finv_img a \/ Exists (in_zr a) (ly_extra ly) -> ~ DS (bv_unsigned (Z_to_bv 64 a))) ->
  FINV ly (w_H W) mem -> FINV ly (w_H W') mem.
Proof.
  intros DS W W' ly mem H Hn ((M & HX & Himg & Hok) & Henv & Hhead).
  assert (MV : forall a n v, (forall k, (k < n)%nat -> finv_img (a + Z.of_nat k) \/ Exists (in_zr (a + Z.of_nat k)) (ly_extra ly)) ->
    val_mem tfibsegs (mrestrict (w_H W) mem) a n v -> val_mem tfibsegs (mrestrict (w_H W') mem) a n v).
  { intros a n v Ha. apply (val_mem_wle_in_off tfibsegs DS W W' mem a n v H). intros k Hk. exact (Hn _ (Ha k Hk)). }
  destruct Hok as (H1 & H2 & H3 & H4 & H5 & HZ).
  split; [|split].
  - exists M. split; [exact HX|]. split; [exact Himg|]. split; [|split; [|split; [exact H3 | split; [exact H4 | split; [exact H5|]]]]].
    + apply MV; [|exact H1]. intros k Hk. left. unfold finv_img. (cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; first [lia | (left; lia) | (right; left; lia) | (right; right; lia) | (right; left; unfold aenv_addr in *; cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; lia)]).
    + apply MV; [|exact H2]. intros k Hk. left. unfold finv_img. (cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; first [lia | (left; lia) | (right; left; lia) | (right; right; lia) | (right; left; unfold aenv_addr in *; cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; lia)]).
    + intros a Ha. apply (mbyte_wle_in_off tfibsegs DS W W' mem a _ H); [|exact (HZ a Ha)].
      apply Hn. right. apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
  - destruct Henv as (E1 & E2 & E3 & (cv & Hcv & E4)). unfold astdio_env.
    split; [apply MV; [|exact E1]; intros k Hk; left; unfold finv_img; (cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; first [lia | (left; lia) | (right; left; lia) | (right; right; lia) | (right; left; unfold aenv_addr in *; cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; lia)])|].
    split; [apply MV; [|exact E2]; intros k Hk; left; unfold finv_img; (cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; first [lia | (left; lia) | (right; left; lia) | (right; right; lia) | (right; left; unfold aenv_addr in *; cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; lia)])|].
    split; [apply MV; [|exact E3]; intros k Hk; left; unfold finv_img; (cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; first [lia | (left; lia) | (right; left; lia) | (right; right; lia) | (right; left; unfold aenv_addr in *; cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; lia)])|].
    exists cv. split; [exact Hcv|]. apply MV; [|exact E4]. intros k Hk. left. unfold finv_img. (cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; first [lia | (left; lia) | (right; left; lia) | (right; right; lia) | (right; left; unfold aenv_addr in *; cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; lia)]).
  - apply MV; [|exact Hhead]. intros k Hk. left. unfold finv_img. (cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; first [lia | (left; lia) | (right; left; lia) | (right; right; lia) | (right; left; unfold aenv_addr in *; cbn -[Z.add Z.lt Z.le Z.of_nat] in *; kcst; lia)]).
Qed.
End b.
