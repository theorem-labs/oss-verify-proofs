(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import HeapIface HeapIfaceA LibIface LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeTopAL.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Eb0DrvLibL Eb0DrvLibInit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNTALCB.
Section CHK.
Variables (STK : Z) (FRAMES LEAK : Z -> Z) (CREDIT : Z -> credit).
Hypothesis STKok : 4096 <= STK <= 2 ^ 20 /\ STK mod 8 = 0.
Hypothesis CREDok : forall n, 0 <= n -> 0 <= fst (CREDIT n) /\ 0 <= snd (CREDIT n).
Hypothesis FRok : forall k, In k [0; 1; 2; 3; 4; 5] -> 0 <= LEAK k /\ 4 * LEAK k + FRAMES k <= ff_cap k.

Lemma lib_layout_b L : Eb0DrvLibL.drv_lib_layoutA (PNTAL.TopLayA_b STK FRAMES LEAK CREDIT L) L.
Proof.
  constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact STKok.
  - reflexivity.
  - intros iv Hin. cbn [PNTAL.TopLayA_b lla_foot] in Hin. rewrite PNTAL.foot_b_eq in Hin. unfold Eb0DrvLibL.LIB_HOLES.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd];
      first [ (eexists _, _; split; [cbn [In]; left; reflexivity | lia])
            | (eexists _, _; split; [cbn [In]; right; left; reflexivity | lia])
            | (eexists _, _; split; [cbn [In]; right; right; left; reflexivity | lia]) ]|]). destruct Hin.
  - intros iv Hin. cbn [PNTAL.TopLayA_a PNTAL.TopLayA_b lla_junk] in Hin. destruct Hin.
  - exact CREDok.
  - exact FRok.
Qed.

Lemma lib_cells_b L : Eb0DrvLibInit.drv_lib_cellsA (PNTAL.TopLayA_b STK FRAMES LEAK CREDIT L).
Proof.
  constructor; try reflexivity.
  - intros iv Hin. cbn [PNTAL.TopLayA_b lla_init_img] in Hin. unfold Eb0DrvLibInit.LIBINIT_IMG.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd];
      first [ (eexists _, _; split; [cbn [In]; left; reflexivity | lia])
            | (eexists _, _; split; [cbn [In]; right; left; reflexivity | lia])
            | (eexists _, _; split; [cbn [In]; right; right; left; reflexivity | lia])
            | (eexists _, _; split; [cbn [In]; right; right; right; left; reflexivity | lia])
            | (eexists _, _; split; [cbn [In]; right; right; right; right; left; reflexivity | lia]) ]|]). destruct Hin.
  - cbn. lia.
  - intros iv Hin. cbn [PNTAL.TopLayA_b lla_initc] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd]; lia|]). destruct Hin.
Qed.

End CHK.
End PNTALCB.
