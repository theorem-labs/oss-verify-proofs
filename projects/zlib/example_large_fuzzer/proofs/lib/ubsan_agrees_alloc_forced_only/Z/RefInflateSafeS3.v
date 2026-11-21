(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateInit_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflate_runA.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeS1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeS2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac csplit := lazymatch goal with |- _ /\ _ => split; csplit | _ => idtac end.

Lemma init_u16_range : forall g base i, 0 <= init_u16 g base i < 65536.
Proof.
  intros g base i. unfold init_u16.
  pose proof (wrap8_range (g (base + 2 * i))). pose proof (wrap8_range (g (base + 2 * i + 1))). lia.
Qed.
Lemma init_u32_range : forall g base i, 0 <= init_u32 g base i < 2 ^ 32.
Proof.
  intros g base i. unfold init_u32.
  pose proof (init_u16_range g base (2 * i)). pose proof (init_u16_range g base (2 * i + 1)). lia.
Qed.

Lemma INV_fresh : forall init b wb, ir2_bad wb = false -> INV (ireset_s (s_pre init b wb)).
Proof.
  intros init b wb Hbad.
  pose proof (ir2_ranges wb Hbad) as (Rw & Rb & Rwb).
  assert (WZ : ir2_wb wb = 0 -> ir2_wrap wb <> 0).
  { unfold ir2_wb, ir2_wrap. destruct (Z.ltb_spec wb 0); [lia|]. intros _. rewrite Z.shiftr_div_pow2 by lia.
    assert (0 <= wb / 2 ^ 4) by (apply Z.div_pos; lia). lia. }
  unfold INV. unfold ireset_s, s_pre, is_of_oracle. sacc.
  split; [|split; [exact HB_0 | mred; sacc; split; [intros _; lia | intros X; exfalso; lia]]].
  (* zlib 1.4: s_pre reads the zero oracle (zmemzero), not [init] *)
  unfold CORE. sacc. unfold iarr_u16_of, iarr_u32_of. rewrite ?arr_len_init.
  pose proof (init_u32_range (fun _ => 0) (lay_length lay_ref) 0) as LR.
  repeat match goal with |- _ /\ _ => split end;
    first [ reflexivity | lia | exact LR
          | intros X; exfalso; first [exact (X eq_refl) | lia]
          | intros X0; split; [reflexivity | apply WZ; exact X0]
          | intros; lia ].
Qed.

