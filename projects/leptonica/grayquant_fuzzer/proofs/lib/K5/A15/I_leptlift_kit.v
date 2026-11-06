(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.G3 Require Import LeptFormats LeptShapes.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout RT_iface RT_gaps_iface FX_lib F_pop_arg F_achk F_printf_iface I_leptfmt I_leptargs I_leptimg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition is_s (k : lkind) : bool := match k with LK_s => true | _ => false end.

(* [comment removed for export] *)
Lemma lept_fmts_img : forall fmt kinds, In (fmt, kinds) LEPT_FMTS ->
  exists f ks t0 sh, In (fmt, (f, ks, (t0, sh))) LEPT_IMG /\ kinds = map is_s (map (fun it => fst (fst it)) sh).
Proof.
  intros fmt kinds Hin. unfold LEPT_FMTS in Hin.
  repeat (destruct Hin as [Hin|Hin];
          [injection Hin as <- <-; do 4 eexists; split; [unfold LEPT_IMG; repeat (first [left; reflexivity | right]) | reflexivity]|]).
  destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma va7_area : forall m ap w1 w2 w3 w4 w5 w6 w7, rw_cells asegs m ap [C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7] ->
  va_area m ap [w1; w2; w3; w4; w5; w6; w7].
Proof. intros m ap w1 w2 w3 w4 w5 w6 w7 [[_ H] _]. unfold va_area. cbn [u64s cells_bytes cbytes] in *. rewrite !app_nil_r in H. exact H. Qed.

Lemma va7_slots : forall m ap w1 w2 w3 w4 w5 w6 w7, rw_cells asegs m ap [C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7] ->
  forall i w, nth_error [w1; w2; w3; w4; w5; w6; w7] i = Some w -> ro_cells asegs m (ap + 8 * Z.of_nat i) [C8 w].
Proof.
  intros m ap w1 w2 w3 w4 w5 w6 w7 [[_ H] _] i w Hi. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H.
  assert (G : forall (pre : list word) (x : word) (post : list word) a, bytes_at asegs m a (u64s (pre ++ x :: post)) ->
            ro_cells asegs m (a + 8 * Z.of_nat (length pre)) [C8 x]).
  { induction pre as [|p pre IH]; intros x post a B; cbn [app u64s length] in B |- *.
    - apply bytes_at_app in B. destruct B as [B _]. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      replace (a + 8 * Z.of_nat 0) with a by lia. exact B.
    - apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le8 in B. specialize (IH x post _ B).
      replace (a + 8 * Z.of_nat (S (length pre))) with (a + Z.of_nat 8 + 8 * Z.of_nat (length pre)) by lia. exact IH. }
  assert (HB : bytes_at asegs m ap (u64s [w1; w2; w3; w4; w5; w6; w7])) by (cbn [u64s]; rewrite ?app_nil_r; exact H).
  do 7 (destruct i as [|i]; [injection Hi as <-;
        first [ exact (G [] _ _ ap HB) | exact (G [_] _ _ ap HB) | exact (G [_;_] _ _ ap HB) | exact (G [_;_;_] _ _ ap HB)
              | exact (G [_;_;_;_] _ _ ap HB) | exact (G [_;_;_;_;_] _ _ ap HB) | exact (G [_;_;_;_;_;_] _ _ ap HB) ]|]).
  destruct i; discriminate Hi.
Qed.
