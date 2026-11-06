(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec StepTac.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Fixpoint wbytes_list (m : word -> option byte) (L : list (Z * list byte)) : word -> option byte :=
  match L with
  | [] => m
  | p :: L' => wbytes (wbytes_list m L') (Z_to_bv 64 (fst p)) (snd p)
  end.
Definition layer_out (za : Z) (n : nat) (p : Z * list byte) : Prop :=
  (0 <= fst p < 2^64 /\ fst p + Z.of_nat (length (snd p)) <= 2^64 /\
   (za + Z.of_nat n <= fst p \/ fst p + Z.of_nat (length (snd p)) <= za))%Z.
Lemma rdn_wbytes_list_out : forall segs L m (za : Z) n,
  (0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64)%Z ->
  Forall (layer_out za n) L ->
  rdn segs (wbytes_list m L) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs L m za n Ha HL. induction HL as [|p L' Hp HL' IH]; [reflexivity|].
  destruct p as [zb bs]. cbn [wbytes_list fst snd]. unfold layer_out in Hp. cbn [fst snd] in Hp.
  rewrite rdn_wbytes_out; [exact IH | | |]; rewrite ?u_Z2bv by lia; lia.
Qed.
Ltac pf_snoc acc p := lazymatch acc with
  | nil => constr:(cons p nil)
  | cons ?x ?t => let t' := pf_snoc t p in constr:(cons x t')
  end.
Ltac pf_forall := repeat (apply Forall_cons; [assumption|]); apply Forall_nil.
Ltac pf_fin segs za n M0 base acc :=
  lazymatch acc with
  | nil => fail 1 "peel_fast: nothing to peel"
  | _ =>
      change (rdn segs M0 (Z_to_bv 64 za) n) with (rdn segs (wbytes_list base acc) (Z_to_bv 64 za) n);
      rewrite (rdn_wbytes_list_out segs acc base za n) by (first [ pf_forall | lia ]);
      repeat match goal with H : layer_out _ _ _ |- _ => clear H end
  end.
Ltac pf_go side segs za n M0 M acc :=
  lazymatch M with
  | wbytes ?M' (Z_to_bv 64 ?zb) ?bs =>
      first [ assert (layer_out za n (zb, bs)) by (unfold layer_out; cbn [fst snd]; side);
              let acc' := pf_snoc acc (zb, bs) in pf_go side segs za n M0 M' acc'
            | pf_fin segs za n M0 M acc ]
  | _ => pf_fin segs za n M0 M acc
  end.

Ltac peel_fast_by side :=
  lazymatch goal with
  | |- context [rdn ?segs ?M0 (Z_to_bv 64 ?za) ?n] =>
      lazymatch M0 with wbytes _ _ _ => idtac end;
      pf_go side segs za n M0 M0 (@nil (Z * list byte))
  end.

