(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import LeptDefs LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Credit.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit} {LL : LeptLayout}.
Context {PINS : LeptPins}.

(* [comment removed for export] *)
Lemma W_calloc_psure : forall C A m md regs (cnt sz k p : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
  0 <= cnt < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= cnt * sz < 2 ^ 61 ->
  aroomP A (m_vmmaps md) k p -> 1 <= k -> alloc_margin (cnt * sz) + ROOM_CREDMAX <= p -> cnt * sz <= ROOM_NMAX ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = al_gp ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + CALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
      u res <> 0 -> live A res = None -> live A' res = Some (cnt * sz) -> live (c_A0 C) res = None ->
      (forall q, q <> res -> live A' q = live A q) ->
      (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0)) ->
      u res mod 16 = 0 -> u res + round16 (cnt * sz) <= alloc_top (c_vm C) ->
      POSTM C A s m m' ->
      aroomP A' vm' (k - 1) (p - alloc_cost (cnt * sz)) ->
      realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes al_segs (mkCfg (mkst regs al_calloc_pc m al_rom) md) S.
Proof.
  intros C A m md regs cnt sz k p ret s S CK HW H10 H11 Hcnt Hsz Hprod Hroom Hk Hp Hmax H1 Hret H4 H2 Hs16 Hlo Hhi HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. destruct (w_vm _ _ _ _ HW) as (V1 & V2 & V3 & V4).
  unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (Hs : 0 <= s < 2 ^ 64) by lia.
  eapply (ai_calloc_psure fx A m md regs cnt sz k p ret (c_sp0 C) (c_argv C) (c_envp C) S
            (w_inv _ _ _ _ HW) (w_pure _ _ _ _ HW) (w_env _ _ _ _ HW) H10 H11 Hcnt Hsz Hprod Hroom Hk Hp Hmax H1 (pin_ret _ Hret) H4).
  - rewrite H2, u_Z2bv by lia. exact Hs16.
  - rewrite H2, u_Z2bv by lia. rewrite V2. lia.
  - rewrite H2, u_Z2bv by lia. lia.
  - rewrite H2. intros a Ha. rewrite u_Z2bv in Ha by lia. exact (W_call_win C A m md s (1024 + 32) CK HW ltac:(lia) Hhi a Ha).
  - intros A' m' vm' regs' res Hinv' Hres Hcs R1 R2 R3 R4 Rnew R6 Hfr Hlive Hdef E1 E2 E3 E4 Hroom'.
    rewrite H2, u_Z2bv in Hfr by lia.
    destruct (keep_new C A A' res _ (w_keep _ _ _ _ HW) R2 R3 R4) as [Hkeep' Hres0].
    destruct (W_after_call C A m md A' m' vm' s (1024 + 32) CK HW ltac:(lia) ltac:(lia) Hhi
                Hinv' Hkeep' Hfr (fun q k0 i L Hi => Hlive q k0 i (w_keep _ _ _ _ HW q k0 L) Hi) Hdef E1 E2 E3 E4) as [HW' F].
    destruct (ai_live_hull A' m' vm' res (cnt * sz) Hinv' R3) as (_ & AL16 & TOP & _).
    rewrite E2, V2 in TOP.
    exact (HK A' m' vm' regs' res HW' Hres Hcs R1 R2 R3 Hres0 R4 R6 AL16 TOP (conj F Hlive) Hroom').
Qed.

End Credit.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
