(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10-29: new file for libreac/fuzz_scene (asan). The start-up certificate
   lib/A/SceneBCert.v (a working branch e89cf69d744) at scene's concrete record B := TfibB
   (lib/A/AD2l.v). SceneBCert's only Section hypothesis, `HB : TfibSyms B` (SceneBCert.v:202), is discharged
   by `TfibB_syms`; nothing here is a hypothesis. *)

(*   `scene_bcert_TfibB` is the certificate's content at TfibB: the two blanket facts the walks take
   (`img_shadow_vis`, `globs_marked` over the five registered globals, SceneBCert.v section 11), the
   check_step shadow cells (R2's HB_C_CS), the four `in_zs` ranges, the owned redzone tails and the four
   runtime cell addresses. `scene_z_tt_TfibB` (HB_Z_TT, the zero range (0x20e00, 0x28)) and `scene_c_pl_TfibB`
   (HB_C_PL, the eight placeholder-redzone shadow cells) are SceneBCert's `scene_z_tt` and `scene_c_pl` at
   TfibB, stated as the certificate states them. `TfibB_HRO_TT`, `TfibB_HRO_PL` and `TfibB_HRO_PLGOT` are the
   entry statement's HRO_TT, HRO_PL and HRO_PLGOT premises at TfibB, each by computation on a closed term.

   No Axiom, no admit, no Admitted. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YG00 YG0a YG01 YG0f YG0n YG0d YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AF0l AF0m.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import SceneRo.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import SceneBCert AD2l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The two facts every walk takes as hypotheses, at scene's B. *)
Theorem scene_img_shadow_vis_TfibB : forall segs, img_shadow_vis segs TfibB.
Proof. exact (scene_img_shadow_vis TfibB TfibB_syms). Qed.

Theorem scene_globs_marked_TfibB : forall segs, globs_marked segs TfibB SCENE_GLOBS.
Proof. exact (scene_globs_marked TfibB TfibB_syms). Qed.

(* SceneBCert's content at TfibB, with no hypothesis left. *)
Theorem scene_bcert_TfibB :
  (forall segs, img_shadow_vis segs TfibB) /\
  (forall segs, globs_marked segs TfibB SCENE_GLOBS) /\
  (forall ly,
    In (z1 (ANum (shadow_addr 0x20d80 + 1)) 4) (as_const TfibB ly) /\
    In (z1 (ANum (shadow_addr 0x20d80 + 2)) 0xf9) (as_const TfibB ly) /\
    In (z1 (ANum (shadow_addr 0x20d80 + 3)) 0xf9) (as_const TfibB ly) /\
    In (z1 (ANum (shadow_addr 0x20da0 + 6)) 2) (as_const TfibB ly) /\
    Forall (fun i => In (z1 (ANum (shadow_addr 0x20da0 + i)) 0xf9) (as_const TfibB ly)) [7; 8; 9; 10; 11]) /\
  in_zs TfibB 0x20d80 8 /\ in_zs TfibB 0x20da0 48 /\ in_zs TfibB 0x20e20 8 /\ in_zs TfibB 0x20e80 8904 /\
  incl SCENE_RZ_OWNED (as_owned_static TfibB) /\
  (forall ly : alayout,
    as_shadow_cell TfibB = 0xa37f8 /\ as_uar_cell TfibB = 0xa3800 /\
    as_got_shadow TfibB = 0x9b710 /\ as_got_uar TfibB = 0x9b768).
Proof.
split; [exact scene_img_shadow_vis_TfibB|].
split; [exact scene_globs_marked_TfibB|].
split; [exact (scene_cs_shadow TfibB TfibB_syms)|].
split; [exact (scene_zs_trailer TfibB TfibB_syms)|].
split; [exact (scene_zs_cframe TfibB TfibB_syms)|].
split; [exact (scene_zs_kl1 TfibB TfibB_syms)|].
split; [exact (scene_zs_placeholder TfibB TfibB_syms)|].
split; [exact (scene_owned_rz TfibB TfibB_syms)|].
intro ly. split; [exact (scene_shadow_cell_addr TfibB TfibB_syms ly)|].
split; [exact (scene_uar_cell_addr TfibB TfibB_syms ly)|].
split; [exact (scene_got_shadow_addr TfibB TfibB_syms ly) | exact (scene_got_uar_addr TfibB TfibB_syms ly)].
Qed.

(* HB_Z_TT at TfibB: SceneBCert.v's `scene_z_tt` (e89cf69d744), in a Theorem Labs lane's frozen wide form. *)
Theorem scene_z_tt_TfibB : in_zs TfibB (0x20e20 - 0x20) (0x20 + (12 - 12 mod 8)).
Proof. exact (scene_z_tt TfibB TfibB_syms). Qed.

(* HB_C_PL at TfibB: SceneBCert.v's `scene_c_pl` (e89cf69d744), the eight 0xf9 cells from shadow 0x7fffc629. *)
Theorem scene_c_pl_TfibB : forall ly, Forall (fun c => In c (as_const TfibB ly))
  (map (fun k => z1 (ANum (0x7fffc629 + Z.of_nat k)) 0xf9) (seq 0 8)).
Proof. exact (scene_c_pl TfibB TfibB_syms). Qed.

End b.

(* ---- the entry statement's minimal HRO_TT premise, at TfibB ----------------------------
   The twelve bytes [0x20e20, 0x20e2c) (the check_step trailer window) are in no owned-static row
   of B and not in B's errno word. Owned rows nearest the window: (0x20dd2, 0x2e), which ends at
   0x20e00, and (0x20e2c, 0x14), which starts at 0x20e2c (AF0m.v:899); errno is TFIB_ERRNO
   0x5d66f4 (AF0m.v:21). *)
Definition own_hit (a : Z) (r : Z * Z) : bool := ((fst r <=? a) && (a <? fst r + snd r))%bool.
Definition hro_tt_ok (i : Z) : bool :=
  (negb (existsb (own_hit (0x20e20 + i)) (as_owned_static TfibB)) &&
   negb ((as_errno TfibB <=? 0x20e20 + i) && (0x20e20 + i <? as_errno TfibB + 4)))%bool.
Lemma hro_tt_chk : forallb hro_tt_ok (map Z.of_nat (seq 0 12)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma TfibB_HRO_TT : forall i, 0 <= i < 12 ->
  ~ Exists (in_zr (0x20e20 + i)) (as_owned_static TfibB) /\
  ~ (as_errno TfibB <= 0x20e20 + i < as_errno TfibB + 4).
Proof.
intros i Hi.
assert (Hin : In i (map Z.of_nat (seq 0 12))).
{ apply in_map_iff. exists (Z.to_nat i). split; [apply Z2Nat.id; lia|]. apply in_seq. lia. }
pose proof (proj1 (forallb_forall _ _) hro_tt_chk i Hin) as Hb. unfold hro_tt_ok in Hb.
apply andb_prop in Hb as [H1 H2]. apply negb_true_iff in H1. apply negb_true_iff in H2.
split.
- intro HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
  assert (Ht : existsb (own_hit (0x20e20 + i)) (as_owned_static TfibB) = true).
  { apply existsb_exists. exists r. split; [exact Hr|]. unfold own_hit.
    apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Ht in H1. discriminate H1.
- intros [Ha Hc].
  assert (Ht : ((as_errno TfibB <=? 0x20e20 + i) && (0x20e20 + i <? as_errno TfibB + 4))%bool = true).
  { apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Ht in H2. discriminate H2.
Qed.

(* ---- the entry statement's HRO_PL and HRO_PLGOT premises, at TfibB --------------------
   a Theorem Labs lane be134c66f29 lib/A/P_LLVMFuzzerTestOneInput.v:212-216 states them over A_reac_scene_placeholder,
   LLVMF_SCENE_BYTES and VAL (A_OBJ 4). None of those names is reachable from this file without the statement file
   or the program-walk listing (lib/A/Prog/{PaTable, SceneAddr, SceneCode, SceneImg, ...}, absent from this
   branch), so both lemmas are stated over the literal values, which the names are equal to:
     - A_reac_scene_placeholder := 0x20e80 and LLVMF_SCENE_BYTES := 8904 are Definitions (statement :128-129), so
       `TfibB_HRO_PL` has HRO_PL's type at B := TfibB up to unfolding them;
     - VAL (A_OBJ 4) = pa_val PI_scene 245 = scene_val 245 = scene_obj 4 = 0x9c388 (PaTable.v:15, SceneImg.v:60,
       SceneCode.v:28-29, SceneAddr.v:56, all at be134c66f29): the .got word holding 0x20e80.
   The length is the descriptor's 8904, NOT the ELF st_size 11136. Zero margin above, in both: the owned row
   (0x23148, 0x8b8) starts at 0x20e80 + 8904 and (0x9c390, 0x10) starts at 0x9c388 + 8 (AF0m.v:898-899). *)
Definition hro_ok (a : Z) : bool :=
  (negb (existsb (own_hit a) (as_owned_static TfibB)) &&
   negb ((as_errno TfibB <=? a) && (a <? as_errno TfibB + 4)))%bool.

Lemma hro_of_chk : forall base n, 0 <= n ->
  forallb (fun i => hro_ok (base + i)) (map Z.of_nat (seq 0 (Z.to_nat n))) = true ->
  forall i, 0 <= i < n ->
  ~ Exists (in_zr (base + i)) (as_owned_static TfibB) /\
  ~ (as_errno TfibB <= base + i < as_errno TfibB + 4).
Proof.
intros base n Hn H i Hi.
assert (Hin : In i (map Z.of_nat (seq 0 (Z.to_nat n)))).
{ apply in_map_iff. exists (Z.to_nat i). split; [apply Z2Nat.id; lia|]. apply in_seq. lia. }
pose proof (proj1 (forallb_forall _ _) H i Hin) as Hb. cbv beta in Hb. unfold hro_ok in Hb.
apply andb_prop in Hb as [H1 H2]. apply negb_true_iff in H1. apply negb_true_iff in H2.
split.
- intro HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
  assert (Ht : existsb (own_hit (base + i)) (as_owned_static TfibB) = true).
  { apply existsb_exists. exists r. split; [exact Hr|]. unfold own_hit.
    apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Ht in H1. discriminate H1.
- intros [Ha Hc].
  assert (Ht : ((as_errno TfibB <=? base + i) && (base + i <? as_errno TfibB + 4))%bool = true).
  { apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Ht in H2. discriminate H2.
Qed.

(* The 8904-address check, one closed term; its two timings are in the build log. *)
Lemma hro_pl_chk : forallb (fun i => hro_ok (0x20e80 + i)) (map Z.of_nat (seq 0 (Z.to_nat 8904))) = true.
Proof. Time vm_compute. reflexivity. Time Qed.
Lemma hro_plgot_chk : forallb (fun i => hro_ok (0x9c388 + i)) (map Z.of_nat (seq 0 (Z.to_nat 8))) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma TfibB_HRO_PL : forall i, 0 <= i < 8904 ->
  ~ Exists (in_zr (0x20e80 + i)) (as_owned_static TfibB) /\
  ~ (as_errno TfibB <= 0x20e80 + i < as_errno TfibB + 4).
Proof. exact (hro_of_chk 0x20e80 8904 ltac:(lia) hro_pl_chk). Qed.

Lemma TfibB_HRO_PLGOT : forall i, 0 <= i < 8 ->
  ~ Exists (in_zr (0x9c388 + i)) (as_owned_static TfibB) /\
  ~ (as_errno TfibB <= 0x9c388 + i < as_errno TfibB + 4).
Proof. exact (hro_of_chk 0x9c388 8 ltac:(lia) hro_plgot_chk). Qed.

Print Assumptions TfibB_syms.
Print Assumptions scene_bcert_TfibB.
Print Assumptions TfibB_HRO_TT.
Print Assumptions scene_z_tt_TfibB.
Print Assumptions scene_c_pl_TfibB.
Print Assumptions TfibB_HRO_PL.
Print Assumptions TfibB_HRO_PLGOT.
