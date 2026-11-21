(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Zg_infl_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_ikit Z_infl_defs Z_infl_pure Z_updwin_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface ZChkAdl ZChecksum AdlerModel DeflateLz InflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition bZ_av8 := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Zg_infl_pure.bZ_av8.

(* [comment removed for export] *)
Definition adler32_z_spec_any := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Zg_infl_pure.adler32_z_spec_any.

(* [comment removed for export] *)
#[local] Transparent iout_bytes.
Lemma iout_prefix_bytes : forall m L rest0 c put, iout m L rest0 c put -> 0 <= put <= Z.of_nat (length rest0) ->
  bytes_at usegs m (il_NO L) (av8 (ic_outbuf c) put).
Proof.
  intros m L rest0 c put H Hp. unfold iout in H.
  pose proof (u8arr_sub_bytes m _ _ 0 (Z.to_nat put) H) as HB.
  rewrite Nat2Z.inj_0, Z.add_0_r in HB. cbn [skipn] in HB.
  unfold iout_bytes in HB. rewrite firstn_app, av8_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in HB by (rewrite av8_length; lia).
  apply HB. rewrite length_app, av8_length, length_skipn. lia.
Qed.
#[local] Opaque iout_bytes.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition av8_sub := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Zg_infl_pure.av8_sub.

Definition av8_prefix := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Zg_infl_pure.av8_prefix.

(* [comment removed for export] *)
#[local] Transparent iout_bytes.
Lemma iout_bytes_blit : forall rest0 c (src : arr) so put n,
  0 <= put -> 0 <= n -> put + n <= Z.of_nat (length rest0) -> put + n <= arr_len (ic_outbuf c) ->
  iout_bytes rest0 (icset_outbuf c (arr_blit (ic_outbuf c) put src so n)) (put + n)
  = firstn (Z.to_nat put) (iout_bytes rest0 c put) ++ map (Z_to_bv 8) (arr_slice src so n)
    ++ skipn (Z.to_nat put + Z.to_nat n) (iout_bytes rest0 c put).
Proof.
  intros rest0 c src so put n Hp Hn HR HA. unfold iout_bytes. cbn [ic_outbuf icset_outbuf].
  rewrite <- (av8_blit (ic_outbuf c) src put so n (put + n)) by lia.
  rewrite firstn_app, av8_length, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite (av8_prefix (ic_outbuf c) put (put + n)) by lia.
  rewrite firstn_all2 by (rewrite av8_length; lia).
  rewrite (skipn_all2 (av8 (ic_outbuf c) (put + n))) by (rewrite av8_length; lia).
  rewrite (skipn_app (Z.to_nat put + Z.to_nat n)), av8_length.
  rewrite (skipn_all2 (av8 (ic_outbuf c) put)) by (rewrite av8_length; lia).
  cbn [app]. rewrite <- !app_assoc. f_equal. f_equal.
  cbn [app]. rewrite skipn_skipn. f_equal. lia.
Qed.
#[local] Opaque iout_bytes.
