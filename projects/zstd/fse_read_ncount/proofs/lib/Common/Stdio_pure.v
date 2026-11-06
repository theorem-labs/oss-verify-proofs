(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel SFW1_lemmas.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Lemma sx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.
Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010<9536388762.2000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
intros segs m a n1 n2 H1 H2. unfold wr_at. split.
- intros (Ha & Hb & H). Local Ltac2 Set LiaHints.tbl := fun () => "00>0>15538427734.1216044545734.1017101216130.1220927221579.1026981515745.1026983613675.134844197302.16 51508892605.1654736999318.1354743291548.1057036176010.1661783614061.1063513398541.127651745753.13 00000700>00E00L00P00T00Z00`00a00b00c00g00h00mS2H22HiS2H22HbS2H12HiS2H12HaS2HaS2HaS2Hi1HS2Hi1HFFSS2HbSS3Hb'".
repeat split; try lia.
+ intros i Hi. apply H. lia.
+ intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
- intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
intros i Hi. destruct (Z.lt_ge_cases i n1).
+ apply HA. lia.
+ replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=60118175065.560305986344.5000001002SS".
rewrite wr_at_app by lia. rewrite bytes_at_app.
split.
- intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sx32_neg : forall w : word, (2147483648 <= bv_unsigned w mod 4294967296)%Z ->
(9223372036854775808 <= bv_unsigned (sx32 w))%Z.
Proof.
intros w H. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq.
pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
change (2^64)%Z with 18446744073709551616%Z in *.
Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>25234281524.2400000IS1H1R2H02H12H52H63H103H11".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition boxed (P : Prop) : Prop := P.
Ltac src_now SRC SEPS MU LSB :=
unfold boxed in SRC;
lazymatch goal with
| |- bytes_at _ ?m' ?S (to_bytes ?s) =>
destruct SEPS as [-> | [SEP1 SEP2]];
[ apply bytes_at_nil; lia
| apply (bytes_at_transport _ _ _ m' _ _ SRC MU); cbn [disjoint_from]; rewrite LSB; unfold zlength in SEP1, SEP2; lia ]
end.
Section WithSegs.
Variable segs : list Segment.
Context {St : Type}.
#[using="Type"] Lemma implM_from_evt : forall {A} (c : M St A) s Q ms,
evt segs (fun ms' => implM segs c s Q ms') ms -> implM segs c s Q ms.
Proof. intros A c s Q ms H. unfold implM in *. apply impl_from_evt. exact H. Qed.
#[using="Type"] Lemma impl_post_evt' : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
impl segs (at_node segs) t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') ->
impl segs (at_node segs) t Q' ms.
Proof.
induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.
Section So.
Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
#[using="Type"] Lemma implM_rdso : forall {A} (f : stdout_st -> @M St A) (s : St) Q ms,
implM segs (f (get_so s)) s Q ms -> implM segs (Monad.mbind (rd_so get_so) f) s Q ms.
Proof. intros A f s Q ms H. exact H. Qed.
#[using="Type"] Lemma implM_updso : forall {A} (g : stdout_st -> stdout_st) (f : unit -> @M St A) (s : St) Q ms,
implM segs (f tt) (set_so (g (get_so s)) s) Q ms -> implM segs (Monad.mbind (upd_so get_so set_so g) f) s Q ms.
Proof. intros A g f s Q ms H. exact H. Qed.
End So.
End WithSegs.
Lemma rw_cells_recast : forall segs m A cs cs',
rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
rw_cells segs m A cs'.
Proof. intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma bv_eqb_refl : forall {n} (x : bv n), bv_eqb x x = true.
Proof. intros n x. unfold bv_eqb. apply Z.eqb_refl. Qed.
Ltac if_refl :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv iota
end.
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
