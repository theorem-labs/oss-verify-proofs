(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import BrRegs.
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Bridge_BrBase () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.BrRegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.ITree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Nodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "stdpp.bitvector.definitions."], [["1bool"; "1false"; "2and"; "2eq"; "2ex"; "3machine_state"; "4is_x0"; "0P"; "5ms_eqv"; "6evt"; "6msteps"; "7nret"; "7resp"; "8areg"; "8at_node"; "8node"]; ["9msteps"; "0a"; "0b"; "0ms"; "0ms'"; "0ms1"; "0ms1'"; "0n"; "0r"; "0rsp"; "0segs"; ":bv"]]).
Section WithSegs.
Variable segs : list Segment.
Lemma cj_msteps_cat : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrBase "<'5':vJr2r1%43321'@r3%23615p041pQ6:1pQ4;1").
Proof.
intros a b H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH].
- apply CatSim.mst_refl.
- eapply CatSim.mst_step; [exact Hsvc | exact Hstep | exact IH].
Qed.
Lemma impl_bind_inv : forall {A B} (t : itree node A) (f : A -> itree node B) Q ms,
impl segs (at_node segs) (ITree.bind _ t f) Q ms ->
impl segs (at_node segs) t (fun r ms' => impl segs (at_node segs) (f r) Q ms') ms.
Proof.
intros A B t. induction t as [r | n k IH]; intros f Q ms H; cbn in *.
- apply evt_done. exact H.
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. apply IH. apply Hk.
Qed.
Lemma impl_ebind_inv : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) Q ms,
impl segs (at_node segs) (ebind t f) (epost Q) ms ->
impl segs (at_node segs) t
(fun r ms' => match r with Ok a => impl segs (at_node segs) (f a) (epost Q) ms' | Unr => True end) ms.
Proof.
intros A B t f Q ms H. unfold ebind in H. apply impl_bind_inv in H.
eapply impl_mono; [exact H|]. intros [|a] ms'; cbn; auto.
Qed.
Lemma impl_vis_inv : forall {A} n (k : resp -> itree node A) Q ms,
impl segs (at_node segs) (Vis n k) Q ms ->
evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp, impl segs (at_node segs) (k rsp) Q (nret ms1 rsp)) ms.
Proof. intros A n k Q ms H. exact H. Qed.
Lemma impl_enode_inv : forall {A} n (pl : resp -> option A) Q ms,
impl segs (at_node segs) (enode n pl) (epost Q) ms ->
evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp a, pl rsp = Some a -> evt segs (Q a) (nret ms1 rsp)) ms.
Proof.
intros A n pl Q ms H. cbn in H. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp a E. specialize (Hk rsp). rewrite E in Hk. exact Hk.
Qed.
Lemma areg_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrBase "K'5'Ky5%211&8r3r2%3221'3'0&6%115(1%53421yR0%>11&=r5%221=r4%421?%=3631p091p0@1pQBE1pQ:I1pQ8J1").
Proof. intros ms ms' r (HR & _) Hr. unfold areg. apply HR, Hr. Qed.
Lemma at_node_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrBase "B'?'5&8r2r1%3221&>vJr4r3%43321r5%63513p031p091pQ:>1pQ8?1pQ@A1").
Proof.
intros n ms ms' Heqv Hat. pose proof Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
destruct n; cbn [at_node] in *; rewrite <- ?Hsvc, <- ?Hm, <- ?Hro;
repeat (rewrite <- (areg_eqv ms ms' _ Heqv) by (vm_compute; reflexivity)); exact Hat.
Qed.
Lemma nret_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrBase "?'5&<&8r3r2%3221&;r4%2214%3265%8221p061pQD;1pQ:=1pQ8>1").
Proof. intros ms ms' rsp H. unfold nret. apply advance_past_svc_eqv, apply_effect_eqv, H. Qed.
Lemma evt_eqv_transfer : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrBase "N'5!p021&8r2r1%3221&9vJr4r3%43321'4'2r7%11;'@r5%23:1=%62=1%7251qQ>E1%:2F1qQ<G1%<2H1p0>1p0D1pQ:K1pQ8L1p@K1").
Proof.
intros P ms ms' Heqv (ms1 & Hms & HP).
destruct (msteps_eqv segs ms ms1 (cj_msteps_cat _ _ Hms) ms' Heqv) as (ms1' & Hms' & Heqv1).
exists ms1, ms1'. auto.
Qed.
End WithSegs.
