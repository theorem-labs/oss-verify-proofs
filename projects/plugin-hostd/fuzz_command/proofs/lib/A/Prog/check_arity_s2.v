(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the shared blocks of the recorder calls of plugin-hostd/fuzz_command.asan
   (recorder.c:205-227, :252-277), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the seed, the region and fact
   tables and the walk style of cgif_close) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/RecBTemplate.v, with its module names changed; 222 of its 269 lines of code are new or changed and 141 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_arity_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition ca_zsh_b (a : Z) : bool :=
existsb (fun r => (fst r <=? a) && (a + 8 <=? fst r + snd r) && (fst r mod 8 =? 0)) Tfib_zero_shadow.
Definition ca_cells : list (Z * Z) :=
map (fun c => match c with ACell (ANum x) 1 (AV (ANum y)) => (x, y) | _ => (0, 0) end) Tfib_const_shadow.
Definition ca_csh_b (a v : Z) : bool :=
existsb (fun p => (fst p =? SHADOW_OFF + a / 8) && (snd p =? v)) ca_cells.

Lemma ca_cells_in : forall x y, In (x, y) ca_cells -> x <> 0 -> In (z1 (ANum x) y) Tfib_const_shadow.
Proof.
intros x y Hin Hx. unfold ca_cells in Hin. apply in_map_iff in Hin as ([ca cw cv] & Heq & Hc).
destruct ca; try (injection Heq as E1 E2; subst; contradiction).
destruct cw as [|[|cw]]; try (injection Heq as E1 E2; subst; contradiction).
destruct cv as [e|m v]; [|injection Heq as E1 E2; subst; contradiction].
destruct e; try (injection Heq as E1 E2; subst; contradiction).
injection Heq as E1 E2. subst. exact Hc.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Lemma ca_shadow_byte : forall ly S (W : world SEGS) mem md a v,
AR SEGS B ly S W mem md -> a mod 8 = 0 -> 0 <= a -> 0 <= v < 256 ->
((v =? 0) && ca_zsh_b a || ca_csh_b a v)%bool = true ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + a / 8) = Some (Z_to_bv 8 v).
Proof.
intros ly S W mem md a v HAR Ha Ha0 Hv Hb.
apply orb_true_iff in Hb. destruct Hb as [Hz | Hc].
- apply andb_true_iff in Hz as [Hv0 Hz]. apply Z.eqb_eq in Hv0. subst v.
  unfold ca_zsh_b in Hz. apply existsb_exists in Hz as (r & Hr & Hc).
  apply andb_true_iff in Hc as [Hc Hr8]. apply andb_true_iff in Hc as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply Z.eqb_eq in Hr8.
  pose proof (ca_zsh_range B HB ly S W mem md r a 1 HAR Hr Hr8 Ha Hlo ltac:(lia) ltac:(lia) 0 ltac:(lia)) as H.
  rewrite Z.add_0_r in H. exact H.
- unfold ca_csh_b in Hc. apply existsb_exists in Hc as ([x y] & Hin & Hc). cbn [fst snd] in Hc.
  apply andb_true_iff in Hc as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst x y.
  apply (ca_const_byte B HB ly S W mem md _ v HAR); [|exact Hv].
  apply in_or_app. right. apply ca_cells_in; [exact Hin|].
  pose proof (Z.div_pos a 8 Ha0 ltac:(lia)). unfold SHADOW_OFF. lia.
Qed.

Ltac ca_sh_step HAR :=
lazymatch goal with |- YP09.mbyte _ _ (SHADOW_OFF + ?A / 8 + Z.of_nat ?I) = Some (Z_to_bv 8 ?V) =>
replace (SHADOW_OFF + A / 8 + Z.of_nat I) with (SHADOW_OFF + (A + 8 * Z.of_nat I) / 8) by (vm_compute; reflexivity);
apply (ca_shadow_byte _ _ _ _ _ _ _ HAR); [vm_compute; reflexivity | vm_compute; discriminate | cbn [nth]; lia | vm_compute; reflexivity]
end.
Lemma ca_synsh_mbyte_0 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 8)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 0 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 0) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_1 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 1)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 1 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 1) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|i]; [ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_2 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 2)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 2 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 2) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|i]]; [ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_3 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 3)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 3 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 3) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|[|i]]]; [ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_4 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 3)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 4 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 4) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|[|i]]]; [ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_5 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 4)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 5 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 5) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|[|[|i]]]]; [ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_6 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 3)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 6 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 6) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|[|i]]]; [ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_7 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 5)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 7 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 7) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|[|[|[|i]]]]]; [ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_8 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 11)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 8 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 8) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]; [ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_9 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 2)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 9 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 9) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|i]]; [ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_10 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 6)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 10 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 10) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|[|[|[|[|i]]]]]]; [ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_11 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 1)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 11 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 11) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|i]; [ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_12 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 2)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 12 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 12) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|i]]; [ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_13 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 4)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 13 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 13) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|[|[|i]]]]; [ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_14 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 5)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 14 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 14) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|[|[|[|i]]]]]; [ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_15 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 1)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 15 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 15) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|i]; [ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_16 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 1)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 16 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 16) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|i]; [ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_17 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 1)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 17 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 17) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|i]; [ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_18 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 2)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 18 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 18) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|i]]; [ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_19 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 2)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 19 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 19) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|i]]; [ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_20 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 3)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 20 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 20) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|[|[|i]]]; [ca_sh_step HAR | ca_sh_step HAR | ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte_21 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, (i < 1)%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr 21 / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh 21) 0)).
Proof.
intros ly S W mem md HAR i Hi. cbn [ca_syn_sh ca_syn_addr nth].
destruct i as [|i]; [ca_sh_step HAR| lia].
Qed.

Lemma ca_synsh_mbyte : forall k ly S (W : world SEGS) mem md, (k < 22)%nat -> AR SEGS B ly S W mem md ->
forall i, (i < length (ca_syn_sh k))%nat ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + ca_syn_addr k / 8 + Z.of_nat i) = Some (Z_to_bv 8 (nth i (ca_syn_sh k) 0)).
Proof.
intros k ly S W mem md Hk HAR i Hi.
destruct k as [|k]; [exact (ca_synsh_mbyte_0 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_1 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_2 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_3 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_4 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_5 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_6 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_7 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_8 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_9 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_10 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_11 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_12 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_13 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_14 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_15 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_16 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_17 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_18 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_19 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_20 ly S W mem md HAR i Hi)|].
destruct k as [|k]; [exact (ca_synsh_mbyte_21 ly S W mem md HAR i Hi)|].
lia.
Qed.

Lemma ca_gpsh_mbyte : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall i, 0 <= i < 66 -> YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + 0x14b64 + i) = Some (Z_to_bv 8 0).
Proof.
intros ly S W mem md HAR i Hi.
assert (Hb : existsb (fun r => (fst r =? 0x22da0) && (snd r =? 0xa5d30 - 0x22da0)) Tfib_zero_shadow = true)
by (vm_compute; reflexivity).
apply existsb_exists in Hb as ([r1 r2] & Hr & Heq). cbn [fst snd] in Heq.
apply andb_true_iff in Heq as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst r1 r2.
replace (SHADOW_OFF + 0x14b64 + i) with (SHADOW_OFF + CA_GP / 8 + i) by (unfold CA_GP; reflexivity).
apply (ca_zsh_range B HB ly S W mem md _ CA_GP 66 HAR Hr); cbn [fst snd]; unfold CA_GP; first [reflexivity | lia].
Qed.

End e.
End f.
End d.
