(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateOverlay. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6 RefDeflSafeFB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition fb_buf_okP (buf : option Z) (len : Z) : Prop :=
  match buf with Some off => 0 <= off /\ off + len <= 65536 | None => True end.

(* [comment removed for export] *)
Lemma fb_buf_ok_core : forall s,
  0 <= ds_strstart s - ds_block_start s < 2 ^ 32 -> 0 <= ds_strstart s <= 2 * ds_w_size s -> ds_w_size s <= 32768 ->
  fb_buf_okP (fb_buf s) (fb_len s) /\ fb_len s = ds_strstart s - ds_block_start s
  /\ (0 <= ds_block_start s -> fb_buf s = Some (ds_block_start s)) /\ (ds_block_start s < 0 -> fb_buf s = None).
Proof.
  intros s Hd Hs Hw. unfold fb_buf_okP, fb_buf, fb_len.
  assert (E64 : wrap64 (ds_strstart s - ds_block_start s) = ds_strstart s - ds_block_start s) by (apply wrap64_id; lia).
  rewrite E64. destruct (Z.leb_spec 0 (ds_block_start s)) as [B|B].
  - assert (E32 : wrap32 (ds_block_start s) = ds_block_start s) by (apply wrap32_id; lia).
    rewrite E32. split; [split; lia|]. split; [reflexivity|]. split; [intros _; reflexivity | intros; lia].
  - split; [exact I|]. split; [reflexivity|]. split; [intros; lia | intros _; reflexivity].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

