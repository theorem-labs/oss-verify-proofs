(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ0i YQ02 YQ07 YQ08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00 YI02 YI01 YP14 YI08 YI0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition EregB (regs : bvmap 5 word) (extra : list word) (blobs : list (list byte)) : env :=
mkEnv (fun i => if (i <? 32)%nat then getr regs (Z_to_bv 5 (Z.of_nat i)) else nth (i - 32) extra (Z_to_bv 64 0))
(fun d => nth d blobs []).
Lemma ew_EregB : forall regs extra blobs k, ew (EregB regs extra blobs) k = ew (Ereg regs extra) k.
Proof. reflexivity. Qed.

Lemma ew_EregB_nat : forall regs extra blobs k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew (EregB regs extra blobs) k = getr regs rr.
Proof. intros. rewrite ew_EregB. apply ew_Ereg_nat. assumption. Qed.
Lemma EregB_vals : forall regs (vals : list Z) blobs j v,
nth_error vals j = Some v -> ew (EregB regs (map (Z_to_bv 64) vals) blobs) (32 + j) = Z_to_bv 64 v.
Proof. intros regs vals blobs j v Hj. rewrite ew_EregB. rewrite <- (app_nil_r (map (Z_to_bv 64) vals)). apply Ereg_vals. exact Hj. Qed.
Lemma regs_ok_EregB : forall regs extra blobs, regs_ok (EregB regs extra blobs) sr_atoms regs.
Proof.
intros regs extra blobs. apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
[ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
cbn [sv_denot];
first [ rewrite getr_zero; reflexivity
| rewrite Z.add_0_r, ew_EregB, ew_Ereg_lt by lia;
match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr regs ?x)) =>
let y := eval vm_compute in x in change x with y end;
rewrite Z_to_bv_bv_unsigned; reflexivity ]
| ]).
destruct Hr.
Qed.
Section c.
Variable segs : list Segment.
Lemma bytes_of_present : forall (m : word -> option byte) a n,
(forall i, 0 <= i < Z.of_nat n -> exists b, mbyte segs m (a + i) = Some b) ->
exists bs, length bs = n /\ forall i, (i < n)%nat -> mbyte segs m (a + Z.of_nat i) = nth_error bs i.
Proof.
intros m a n H.
exists (map (fun i => match mbyte segs m (a + Z.of_nat i) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
split; [rewrite length_map, length_seq; reflexivity|].
intros i Hi. rewrite nth_error_map. rewrite (nth_error_nth' _ 0%nat) by (rewrite length_seq; exact Hi).
rewrite seq_nth by exact Hi. cbn [option_map Nat.add].
destruct (H (Z.of_nat i) ltac:(lia)) as [b Hb]. rewrite Hb. reflexivity.
Qed.
Lemma chunk_ok_data : forall E m base off d (bs : list byte),
ed E d = bs -> (forall i, (i < length bs)%nat -> mbyte segs m (base + off + Z.of_nat i) = nth_error bs i) ->
chunk_ok segs E m base (mkChunk off (CData d 0 (Z.of_nat (length bs)))).
Proof.
intros E m base off d bs Hd Hbs i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *. rewrite Hd, Z.add_0_l.
destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hb.
- exists b. split; [reflexivity|]. rewrite <- Hb, <- (Hbs (Z.to_nat i)) by (apply nth_error_Some; rewrite Hb; discriminate). rewrite Z2Nat.id by lia. reflexivity.
- exfalso. apply nth_error_None in Hb. lia.
Qed.

End c.
