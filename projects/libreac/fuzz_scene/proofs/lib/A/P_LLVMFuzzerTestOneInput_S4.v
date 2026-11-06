(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: SEGMENT S4 of the ASan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput,
   i.e. `seg_S4_stmt` of lib/A/P_LLVMFuzzerTestOneInput_seg.v at the asan table `scene_geom_asan`: the
   whole_transfer guard at 0x82d74, the malloc at 0x82d90, the loop entry at k = 0, the closure of the 343-turn
   loop over the S3 hypothesis, the got / declared checks, the bcmp at 0x82e9c, the free at 0x82ea8, and the
   no-transfer arm that jumps straight to C5.  rule 24: no function is proved here; this is one segment of one
   function's run. *)

(*   The walk is a CONCRETE machine walk: `SRr_step` (lib/Reusable/YA0n.v:133) over `RiscvSemantics.step`, with the
   instruction words taken from the position-abstract listing (lib/A/Prog/SceneList.v) through
   ScenePaLib.pa_fetch_pw, and the three runtime calls taken by their journal rules (amalloc04_rule_triv,
   aj_bcmp_at, afree04_rule_triv).  There is no symbolic state and no `st_ok_pi`: the segment is 35 straight
   instructions and three calls, and every fact a cut carries is a semantic fact about (ly, S, W, regs, mem, md),
   so it is carried across a step by the journal and across a call by `acall_kept`.

   GATE 6h: the sink head is this section's own `SK`, and the theorem names it explicitly.  It is never left to
   instance resolution: the statement quantifies over EVERY sink head, so it holds in particular for scene's own
   (asan ofl_head 0x5f6e90), and no global sink instance can be silently selected. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0f.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16 YN2e.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q YN01.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import
PaRun PaShadow PaStep PaJournal SceneSyms SceneList SceneAddr SceneCode ScenePa ScenePaLib
SceneBase SceneFrame SceneImg YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx P_LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section S4.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
#[local] Notation TPI := (@pl_tpi scene_listing PL_scene).

(* ================================================================================================
   The step machinery: one lemma per instruction form of this segment.
   ================================================================================================ *)

Lemma s4_fetch : forall k w, plookup TPI k = Some (PW w) ->
fetch_word SEGS (Z_to_bv 64 (BASE + k)) = Some (Z_to_bv 32 w).
Proof. intros k w H. exact (pa_fetch_pw k w H). Qed.

Lemma s4_unrestrict_mkst : forall (H : word -> bool) full regs pc m rom,
unrestrict H full (mkst regs pc m rom) = mkst regs pc (munrestrict H full m) rom.
Proof. intros. unfold unrestrict, mkst. cbn. reflexivity. Qed.

(* One machine step whose result is again a (regs, pc, mem) triple with the same memory. *)
Lemma s4_reg : forall (W : world SEGS) regs k mem md regs' k' Q,
RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (seg_rom SEGS))
= MachineOk (mkst regs' (Z_to_bv 64 (BASE + k')) (mrestrict (w_H W) mem) (seg_rom SEGS)) ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + k')) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md regs' k' Q Hs HK.
eapply (SRr_step SEGS pa_wx W (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 (BASE + k')) (mrestrict (w_H W) mem) (seg_rom SEGS)) md Q).
- reflexivity.
- rewrite restrict_mkst_fx. exact Hs.
- intros md' Hm. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. exact (HK md' Hm).
Qed.

(* the same with an arbitrary target pc (a call) *)
Lemma s4_step_at : forall (W : world SEGS) regs k mem md regs' pc' Q,
RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (seg_rom SEGS))
= MachineOk (mkst regs' pc' (mrestrict (w_H W) mem) (seg_rom SEGS)) ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs' pc' mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md regs' pc' Q Hs HK.
eapply (SRr_step SEGS pa_wx W (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS))
(mkst regs' pc' (mrestrict (w_H W) mem) (seg_rom SEGS)) md Q).
- reflexivity.
- rewrite restrict_mkst_fx. exact Hs.
- intros md' Hm. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. exact (HK md' Hm).
Qed.

Lemma s4_pc4 : forall k, v_addi (Z_to_bv 64 (BASE + k)) 4 = Z_to_bv 64 (BASE + (k + 4)).
Proof. intros k. rewrite YCbn.v_addi_lit. f_equal. lia. Qed.

Lemma s4_opimm : forall (W : world SEGS) regs k mem md Q w op rd rs (imm : bv 12) v,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (OpImm op rd rs imm, 4%Z) -> bv_eqb rd 0 = false ->
alu64 op (getr regs rs) (sext 64 imm) = v ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd v) (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w op rd rs imm v Hpl He Hd Hrd Hv HK.
eapply s4_reg; [|exact HK].
rewrite (step_opimm_gen SEGS regs _ _ _ (Z_to_bv 32 w) op rd rs imm (s4_fetch k w Hpl) He Hd).
rewrite Hrd, Hv, s4_pc4. reflexivity.
Qed.

Lemma s4_opimm32 : forall (W : world SEGS) regs k mem md Q w rd0 rs0 (imm : bv 12) rd rs zi v,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (OpImm32 rd0 rs0 imm, 4%Z) ->
rd0 = rd -> rs0 = rs -> bv_signed imm = zi -> bv_eqb rd 0 = false ->
v_addiw (getr regs rs) zi = v ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd v) (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w rd0 rs0 imm rd rs zi v Hpl He Hd Erd Ers Ezi Hrd Hv HK.
subst rd0 rs0 zi.
eapply s4_reg; [|exact HK].
rewrite (step_addiw SEGS regs _ _ _ (Z_to_bv 32 w) rd rs imm (s4_fetch k w Hpl) He Hd).
rewrite Hrd, Hv, s4_pc4. reflexivity.
Qed.

Lemma s4_lui : forall (W : world SEGS) regs k mem md Q w rd0 (imm : bv 20) rd zi v,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Lui rd0 imm, 4%Z) ->
rd0 = rd -> Z.shiftl (bv_signed imm) 12 = zi -> bv_eqb rd 0 = false ->
v_lui zi = v ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd v) (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w rd0 imm rd zi v Hpl He Hd Erd Ezi Hrd Hv HK.
subst rd0 zi.
eapply s4_reg; [|exact HK].
rewrite (step_lui SEGS regs _ _ _ (Z_to_bv 32 w) rd imm (s4_fetch k w Hpl) He Hd).
rewrite Hrd, Hv, s4_pc4. reflexivity.
Qed.

Lemma s4_mv : forall (W : world SEGS) regs k mem md Q w rd0 rs0 (imm : bv 12) rd rs zi v,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd0 rs0 imm, 4%Z) ->
rd0 = rd -> rs0 = rs -> bv_signed imm = zi -> bv_eqb rd 0 = false ->
v_addi (getr regs rs) zi = v ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd v) (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w rd0 rs0 imm rd rs zi v Hpl He Hd Erd Ers Ezi Hrd Hv HK.
subst rd0 rs0 zi.
eapply s4_reg; [|exact HK].
rewrite (step_addi SEGS regs _ _ _ (Z_to_bv 32 w) rd rs imm (s4_fetch k w Hpl) He Hd).
rewrite Hrd, Hv, s4_pc4. reflexivity.
Qed.

Lemma s4_add : forall (W : world SEGS) regs k mem md Q w rd rs1 rs2 v,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Op ALU_ADD rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
v_add (getr regs rs1) (getr regs rs2) = v ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd v) (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w rd rs1 rs2 v Hpl He Hd Hrd Hv HK.
eapply s4_reg; [|exact HK].
rewrite (step_add SEGS regs _ _ _ (Z_to_bv 32 w) rd rs1 rs2 (s4_fetch k w Hpl) He Hd).
rewrite Hrd, Hv, s4_pc4. reflexivity.
Qed.

Lemma s4_branch : forall (W : world SEGS) regs k mem md Q w c rs1 rs2 (imm : bv 13),
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Branch c rs1 rs2 imm, 4%Z) ->
(branch_taken c (getr regs rs1) (getr regs rs2) = true -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + bv_signed imm))) mem (seg_rom SEGS)) md') Q) ->
(branch_taken c (getr regs rs1) (getr regs rs2) = false -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w c rs1 rs2 imm Hpl He Hd HT HF.
destruct (branch_taken c (getr regs rs1) (getr regs rs2)) eqn:Hb.
- eapply s4_reg; [|exact (HT eq_refl)].
rewrite (step_branch_tk_gen SEGS regs _ _ _ (Z_to_bv 32 w) c rs1 rs2 imm (s4_fetch k w Hpl) He Hd Hb).
unfold btgt. rewrite YCbn.v_addi_lit.
replace (BASE + k + bv_signed imm) with (BASE + (k + bv_signed imm)) by lia. reflexivity.
- eapply s4_reg; [|exact (HF eq_refl)].
rewrite (step_branch_ft_gen SEGS regs _ _ _ (Z_to_bv 32 w) c rs1 rs2 imm (s4_fetch k w Hpl) He Hd Hb).
rewrite s4_pc4. reflexivity.
Qed.

(* the same, with the branch offset given as a literal (so no evar ever reaches a computation) *)
Lemma s4_branch_off : forall (W : world SEGS) regs k mem md Q w c r1 r2 (imm : bv 13) rs1 rs2 off,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Branch c r1 r2 imm, 4%Z) ->
r1 = rs1 -> r2 = rs2 -> bv_signed imm = off ->
(branch_taken c (getr regs rs1) (getr regs rs2) = true -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + off))) mem (seg_rom SEGS)) md') Q) ->
(branch_taken c (getr regs rs1) (getr regs rs2) = false -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w c r1 r2 imm rs1 rs2 off Hpl He Hd E1 E2 Hoff HT HF.
subst r1 r2.
apply (s4_branch W regs k mem md Q w c rs1 rs2 imm Hpl He Hd); rewrite ?Hoff; assumption.
Qed.

Lemma s4_andi : forall (W : world SEGS) regs k mem md Q w rd0 rs0 (imm : bv 12) rd rs zi v,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (OpImm ALU_AND rd0 rs0 imm, 4%Z) ->
rd0 = rd -> rs0 = rs -> bv_signed imm = zi -> bv_eqb rd 0 = false ->
v_andi (getr regs rs) zi = v ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd v) (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w rd0 rs0 imm rd rs zi v Hpl He Hd Erd Ers Ezi Hrd Hv HK.
subst rd0 rs0 zi.
eapply s4_reg; [|exact HK].
rewrite (step_andi SEGS regs _ _ _ (Z_to_bv 32 w) rd rs imm (s4_fetch k w Hpl) He Hd).
rewrite Hrd, Hv, s4_pc4. reflexivity.
Qed.

(* a jal to a listing symbol: the slot's certificate gives the decode and the target *)
Lemma s4_call : forall (W : world SEGS) regs k mem md Q s (rd : bv 5),
plookup TPI k = Some (PCall s rd) ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd (Z_to_bv 64 (BASE + (k + 4)))) (Z_to_bv 64 (SIGMA s))
mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q s rd Hpl HK.
rewrite <- (@pl_tpi_eq scene_listing PL_scene) in Hpl.
pose proof (cert_slot ssym (clookup (@pa_tbl _ scene_listing PI_scene))
(@pa_val _ scene_listing PI_scene) (@pa_sigma _ scene_listing PI_scene) scene_listing
(@pa_cert _ scene_listing PI_scene) k (PCall s rd) Hpl) as (Hck & Hk0 & Hk4).
unfold pi_slot_check in Hck.
destruct (clookup (@pa_tbl _ scene_listing PI_scene) (BASE + k)) as [wz|] eqn:Hf; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as (Hsz & Hck).
destruct i; try discriminate Hck.
apply andb_prop in Hck as (Hck & Htgt). apply andb_prop in Hck as (Hrdeq & Hrd0).
apply Z.eqb_eq in Hsz. apply Z.eqb_eq in Htgt.
apply reg_eqb_eq in Hrdeq. apply Bool.negb_true_iff in Hrd0. subst.
eapply s4_step_at; [|exact HK].
rewrite (step_jal_link SEGS regs _ _ _ (Z_to_bv 32 wz) _ _
(pa_fetch_ok _ _ Hf) ltac:(eapply not_ecall_of_decode; [exact Hdec | discriminate]) Hdec).
assert (E0 : (0%bv : bv 5) = Z_to_bv 5 0) by (apply bv_eq; reflexivity).
rewrite E0, Hrd0. unfold btgt. rewrite !YCbn.v_addi_lit.
replace (BASE + k + 4) with (BASE + (k + 4)) by lia.
f_equal. f_equal. apply zv_zcanon_eq. rewrite <- Htgt. unfold zcanon, M64.
symmetry. apply Z.mod_mod. lia.
Qed.

Lemma s4_ld : forall (W : world SEGS) regs k mem md Q w rd0 rs0 (imm : bv 12) rd rs zi a v,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd0 rs0 imm, 4%Z) ->
rd0 = rd -> rs0 = rs -> bv_signed imm = zi -> bv_eqb rd 0 = false ->
bv_unsigned (getr regs rs) + zi = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
rdword (aview SEGS (w_H W) mem) a = Some v ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd (Z_to_bv 64 v)) (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w rd0 rs0 imm rd rs zi a v Hpl He Hd Erd Ers Ezi Hrd Ha Ha0 Ha8 Hrw HK.
subst rd0 rs0 zi.
pose proof (val_mem_of_rdword SEGS (w_H W) mem a v Hrw) as Hv.
destruct (word_mem_ld SEGS (mrestrict (w_H W) mem) a v Hv Ha0 Ha8) as (bs & Hbs & Hval).
eapply s4_reg; [|exact HK].
rewrite (step_ld SEGS regs _ _ _ (Z_to_bv 32 w) rd rs imm bs (Z_to_bv 64 v) (s4_fetch k w Hpl) He Hd
ltac:(unfold v_addi; rewrite Ha; exact Hbs) Hval).
rewrite Hrd, s4_pc4. reflexivity.
Qed.

Lemma s4_mr_mu : forall (H : word -> bool) full m x, mrestrict H (munrestrict H full m) x = mrestrict H m x.
Proof. intros H full m x. unfold mrestrict, munrestrict. destruct (H x); reflexivity. Qed.

Lemma s4_mr_eq : forall (H : word -> bool) m1 m2 x, m1 x = m2 x -> mrestrict H m1 x = mrestrict H m2 x.
Proof. intros H m1 m2 x E. unfold mrestrict. destruct (H x); [reflexivity | exact E]. Qed.

Lemma s4_mr_some : forall (H : word -> bool) m x, H x = false -> mrestrict H m x = m x.
Proof. intros H m x E. unfold mrestrict. rewrite E. reflexivity. Qed.

Lemma s4_mr_none : forall (H : word -> bool) m x, H x = true -> mrestrict H m x = None.
Proof. intros H m x E. unfold mrestrict. rewrite E. reflexivity. Qed.

(* A doubleword store into a window every byte of which is present.  The memory the walk goes on with is
   characterised pointwise; no clause names the written function. *)
Definition s4_wr (W : world SEGS) (mem mem' : word -> option byte) (a v : Z) : Prop :=
(forall x : word, w_H W x = true -> mem' x = mem x) /\
(forall x : word, bv_unsigned x < a \/ a + 8 <= bv_unsigned x ->
mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) /\
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
rdword (aview SEGS (w_H W) mem') a = Some v.

Lemma s4_wr_view : forall W mem mem' a v b,
s4_wr W mem mem' a v -> 0 <= b < 2 ^ 64 -> (b < a \/ a + 8 <= b) ->
aview SEGS (w_H W) mem' b = aview SEGS (w_H W) mem b.
Proof.
intros W mem mem' a v b (_ & H2 & _ & _) Hb Hout.
unfold aview, mbyte.
rewrite (H2 (Z_to_bv 64 b) ltac:(rewrite Z_to_bv_unsigned; unfold bv_wrap;
change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_small by lia; lia)).
reflexivity.
Qed.

Lemma s4_wr_word : forall W mem mem' a v b w,
s4_wr W mem mem' a v -> 0 <= b -> b + 8 <= 2 ^ 64 -> (b + 8 <= a \/ a + 8 <= b) ->
rdword (aview SEGS (w_H W) mem) b = Some w -> rdword (aview SEGS (w_H W) mem') b = Some w.
Proof.
intros W mem mem' a v b w HW Hb0 Hb8 Hout Hrw.
rewrite <- Hrw. apply rdword_ext. intros i Hi.
apply (s4_wr_view W mem mem' a v (b + i) HW); lia.
Qed.

Lemma s4_wr_pres : forall W mem mem' a v x,
s4_wr W mem mem' a v -> apresent (w_H W) mem x -> apresent (w_H W) mem' x.
Proof. intros W mem mem' a v x (_ & _ & H3 & _) Hp. eapply apresent_grows; [exact H3 | exact Hp]. Qed.

Lemma s4_sd : forall (W : world SEGS) regs k mem md Q w r1 r2 (imm : bv 12) rs1 rs2 zi a,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Store SZ8 r1 r2 imm, 4%Z) ->
r1 = rs1 -> r2 = rs2 -> bv_signed imm = zi ->
bv_unsigned (getr regs rs1) + zi = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
(forall i, 0 <= i < 8 -> apresent (w_H W) mem (a + i)) ->
(forall mem' md', same_but_materialized md md' -> s4_wr W mem mem' a (bv_unsigned (getr regs rs2)) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + 4))) mem' (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w r1 r2 imm rs1 rs2 zi a Hpl He Hd E1 E2 Ezi Ha Ha0 Ha8 Hpres HK.
subst r1 r2 zi.
pose proof (bv_unsigned_in_range 64 (getr regs rs2)) as HV.
change (bv_modulus 64) with (2 ^ 64) in HV.
set (bs := word_to_le_bytes 8 (getr regs rs2)).
assert (Hlen : length bs = 8%nat) by apply length_N_to_le_bytes.
assert (Hav : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
assert (Hst : RiscvSemantics.store_ok SEGS (mrestrict (w_H W) mem) (Z_to_bv 64 a) 8%nat = true).
{ apply (writable_store_ok SEGS (mrestrict (w_H W) mem) a 8%nat ltac:(cbn; lia) ltac:(cbn; lia)).
intros x Hx. apply (apresent_writable SEGS (w_H W) mem x).
replace x with (a + (x - a)) by lia. apply Hpres. cbn in Hx. lia. }
eapply (SRr_step SEGS pa_wx W (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS))
(mkst regs (v_addi (Z_to_bv 64 (BASE + k)) 4)
(wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) bs) (seg_rom SEGS)) md Q).
- reflexivity.
- rewrite restrict_mkst_fx.
exact (step_sd_at SEGS regs _ _ _ (Z_to_bv 32 w) rs1 rs2 imm (Z_to_bv 64 a) (getr regs rs2)
(s4_fetch k w Hpl) He Hd ltac:(unfold v_addi; rewrite Ha; reflexivity) eq_refl Hst).
- intros md' Hm. cbn [ms_mem mkst]. rewrite s4_unrestrict_mkst, s4_pc4.
apply (HK (munrestrict (w_H W) mem (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) bs)) md' Hm).
assert (Hout : forall x : word, bv_unsigned x < a \/ a + 8 <= bv_unsigned x ->
wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) bs x = mrestrict (w_H W) mem x).
{ intros x [Hx|Hx].
- apply wbytes_below; [rewrite Hlen, Hav; cbn; lia | rewrite Hav; lia].
- apply wbytes_above; rewrite Hlen, Hav; cbn; lia. }
split; [|split; [|split]].
+ intros x Hx. unfold munrestrict. rewrite Hx. reflexivity.
+ intros x Hx. rewrite s4_mr_mu. destruct (w_H W x) eqn:EH.
* rewrite !(s4_mr_none _ _ _ EH). reflexivity.
* rewrite !(s4_mr_some _ _ _ EH). rewrite (Hout x Hx). apply s4_mr_some. exact EH.
+ intros x Hx. rewrite s4_mr_mu. destruct (w_H W x) eqn:EH.
* exfalso. apply Hx. apply s4_mr_none. exact EH.
* rewrite (s4_mr_some _ _ _ EH).
apply (wbytes_grows bs (mrestrict (w_H W) mem) (Z_to_bv 64 a) x). exact Hx.
+ apply rdword_of_val_mem; [|exact HV].
intros kk Hkk.
assert (Hx : 0 <= a + Z.of_nat kk < 2 ^ 64) by lia.
assert (HHf : w_H W (Z_to_bv 64 (a + Z.of_nat kk)) = false).
{ exact (proj1 (Hpres (Z.of_nat kk) ltac:(lia))). }
replace (mbyte SEGS (mrestrict (w_H W)
(munrestrict (w_H W) mem (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) bs))) (a + Z.of_nat kk))
with (mbyte SEGS (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) bs) (a + Z.of_nat kk))
by (unfold mbyte, mrestrict, munrestrict; rewrite HHf; reflexivity).
rewrite (wbytes_mbyte SEGS bs (mrestrict (w_H W) mem) a (a + Z.of_nat kk) ltac:(lia)
ltac:(rewrite Hlen; cbn; lia) Hx).
rewrite Hlen. cbn [Z.of_nat].
replace ((a <=? a + Z.of_nat kk) && (a + Z.of_nat kk <? a + Z.of_nat 8))%bool with true
by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; cbn; lia]).
replace (Z.to_nat (a + Z.of_nat kk - a)) with kk by lia.
unfold bs. rewrite <- (Z_to_bv_bv_unsigned _ (getr regs rs2)) at 1.
rewrite (word_to_le_bytes_nth 8 (bv_unsigned (getr regs rs2)) kk Hkk HV).
reflexivity.
Qed.

(* ================================================================================================
   Small facts the segment uses everywhere.
   ================================================================================================ *)

Lemma s4_bv_small : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hz.
Qed.

Lemma s4_base_lo : 0x10000 <= BASE /\ 0 <= BASE /\ BASE + 2 ^ 40 < 2 ^ 64 /\ BASE mod 4 = 0.
Proof.
pose proof (@pa_base_lo _ scene_listing PL_scene PI_scene) as H1.
pose proof (@pa_B_ok _ scene_listing PI_scene) as (H2 & H3 & H4). auto.
Qed.

Lemma s4_ret : forall k, 0 <= k < 2 ^ 40 -> k mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 (BASE + k)).
Proof. intros k H1 H2. exact (ret_ok_codeptr_v k H1 H2). Qed.

Lemma s4_ra4096 : forall k, 0 <= k < 2 ^ 40 -> 4096 <= bv_unsigned (Z_to_bv 64 (BASE + k)).
Proof.
intros k Hk. pose proof s4_base_lo as (Hb1 & Hb2 & Hb3 & _).
rewrite s4_bv_small by lia. lia.
Qed.

(* every byte of a present range is a byte list *)
Lemma s4_u8s_roundtrip : forall l : list Z, bytes_ok l -> u8s (map (fun z => Z_to_bv 8 z) l) = l.
Proof.
intros l Hl. induction l as [|z l IH]; [reflexivity|].
inversion Hl as [|z' l' Hz Hl']; subst. cbn [map u8s] in *. unfold u8s in *. cbn [map].
rewrite IH by exact Hl'. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.

Lemma s4_block_bytes : forall (W : world SEGS) mem p n, 0 <= n ->
(forall a, p <= a < p + n -> apresent (w_H W) mem a) ->
exists l : list byte, Z.of_nat (length l) = n /\ garr8 SEGS (mrestrict (w_H W) mem) p (u8s l).
Proof.
intros W mem p n Hn Hp.
destruct (garr8_of_present SEGS (mrestrict (w_H W) mem) p (Z.to_nat n)) as (l0 & Hlen & Hg).
{ intros a Ha. destruct (Hp a ltac:(lia)) as (HH & b & Hb).
  exists b. unfold mrestrict. rewrite HH. exact Hb. }
exists (map (fun z => Z_to_bv 8 z) l0). split.
- rewrite length_map, Hlen. lia.
- rewrite (s4_u8s_roundtrip l0 (garr8_bytes_ok SEGS _ _ _ Hg)). exact Hg.
Qed.

Lemma s4_aview_garr8 : forall (W : world SEGS) mem p l j,
garr8 SEGS (mrestrict (w_H W) mem) p l -> (j < length l)%nat ->
aview SEGS (w_H W) mem (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W mem p l j Hg Hj.
pose proof (garr8_mbyte SEGS (mrestrict (w_H W) mem) p l j Hg Hj) as Hm.
destruct (Hg j Hj) as (_ & Hr).
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

Lemma s4_aview_pres : forall (W : world SEGS) mem a,
apresent (w_H W) mem a -> aview SEGS (w_H W) mem a <> None.
Proof. intros W mem a Hp. apply (aview_some_of_apresent SEGS). exact Hp. Qed.



(* ================================================================================================
   The segment's hypotheses: exactly the facts about B and about the walk's constants that
   lib/A/P_LLVMFuzzerTestOneInput.v's Section h fixes and that S4 uses.
   ================================================================================================ *)
Variable B : asyms.
Variable WK : swalk.
#[local] Notation IM := (@scene_geom_asan rc).
#[local] Notation LAWS := (AR_laws_ok SEGS B).

Hypothesis TL : @PALib rc scene_listing (@PI_scene rc) B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
(* the budgets, in the form Section h states them (LLVMF_EV = 6, LLVMF_NMAX = 65535,
   LLVMF_SPDROP = 240) *)
Hypothesis HEV : 6 <= sw_ev WK.
Hypothesis HLIVE : 2 * 65535 <= sw_live WK.
Hypothesis HSTK : 240 + ASTACK <= sw_stk WK.
(* The walk's read-only window is the listing's: every cut states `arodata_okS` over sw_rlo / sw_rhi, and S4
   crosses three runtime calls, after each of which the clause is re-established through the journal's image
   clause, which needs the window to be in the image (pa_relro_img). *)
(* A Theorem Labs lane's ruling 04:04Z: segment-Section binding, discharged by the composition *)
Hypothesis HWRLO : sw_rlo WK = pa_relro_lo.
(* A Theorem Labs lane's ruling 04:04Z: segment-Section binding, discharged by the composition *)
Hypothesis HWRHI : sw_rhi WK = pa_relro_hi.

(* A Theorem Labs lane's allocation-trace instance, at the six measured return addresses *)
Hypothesis HTRACE : rt_trace_in_stmt SEGS (sw_ra WK)
(pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
(BASE + 0x328) (BASE + 0x51c) (BASE + 0x640) (BASE + 0x634) (BASE + 0x7b0) (BASE + 0x7b8)
(as_universe B).

Ltac s4geom := cbn [vat scene_geom_asan
sg_cid sg_frame sg_off_blki sg_off_mac sg_off_blk sg_off_expect sg_blk_n sg_mac_n sg_scene_n sg_nturns
sg_sh_blki_lo sg_sh_blki_hi sg_sh_blk_lo sg_sh_blk_hi
sg_pc_c3 sg_pc_t sg_pc_tx sg_pc_c5
sg3_F sg3_Fb sg3_shF sg3_sp1 sg3_sp0 sg3_blki sg3_expect sg3_nprime sg3_flags sg3_step
sg3_shexp sg3_Fsp sg3_mac sg3_body sg3_nn
sgT_got sgT_k sgT_shF sgT_sp1 sgT_sp0 sgT_blki sgT_srcA sgT_srcB sgT_f8 sgT_n1 sgT_extra
sgT_nagain sgT_again sgT_body sgT_decl sgT_nprime sgT_Fsp sgT_mac sgT_shexp sgT_expect sgT_Fb
sgT_nn sgT_body2 sgTX_got2
sg5_F sg5_shF sg5_sp1 sg5_sp0 sg5_nprime sg5_expect sg5_shexp sg5_Fsp sg5_mac sg5_body sg5_nn] in *.

(* ================================================================================================
   The no-transfer arm: C3's facts are C5's facts, with a0 clobbered and nothing else changed.
   ================================================================================================ *)
Lemma s4_sj_mat : forall cx ly3 S3 W3 mem3 md3 md' ev,
same_but_materialized md3 md' ->
@sc_j rc SK SEGS B ameter_triv WK IM cx ly3 S3 W3 mem3 md3 ev ->
@sc_j rc SK SEGS B ameter_triv WK IM cx ly3 S3 W3 mem3 md' ev.
Proof.
intros cx ly3 S3 W3 mem3 md3 md' ev Hmat (HJ1 & HJ2 & HJ3).
split; [|split; [exact HJ2 | exact HJ3]].
rewrite (same_but_materialized_wvb md3 md' Hmat).
apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ1.
Qed.

Lemma s4_C5_of_C3 : forall cx ly3 S3 W3 regs3 mem3 md3 md' bs body bb (regs' : bvmap 5 word),
@cut_C3 rc SK SEGS B ameter_triv WK IM cx ly3 S3 W3 regs3 mem3 md3 bs body bb ->
@sc_j rc SK SEGS B ameter_triv WK IM cx ly3 S3 W3 mem3 md' 1 ->
(forall r : bv 5, r <> 10%bv -> getr regs' r = getr regs3 r) ->
@cut_C5 rc SK SEGS B ameter_triv WK IM cx ly3 S3 W3 regs' mem3 md' bs body bb 1.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 md' bs body bb regs' HC3 HJ' Hreg.
destruct HC3 as (HJ & Hab & Hbb & Hblk & Hlen & Hbody & HF & Hsav & Hshbg & Hsh1 & Hob & Hom &
Himg & Hin & Hnn & Hmac & Vsp0 & Vsp1 & VF & VFb & VFsp & VshF & Vblki & Vexp & Vmac & Vshexp &
Vbody & Vnn & Vnp & Vfl & Vst).
unfold cut_C5. s4geom.
split; [lia|]. split; [exact HJ'|].
split; [rewrite Hab; apply Permutation_refl|].
split; [exact Hbb|]. split; [exact Hblk|]. split; [exact Hlen|]. split; [exact Hbody|].
split; [exact HF|]. split; [exact Hsav|]. split; [exact Hshbg|]. split; [exact Hsh1|].
split; [exact Hob|]. split; [exact Hom|].
split.
{ unfold sc_img in *. destruct Himg as (Hsp & Hgp & Htp & Hro).
  split; [unfold spZ in *; rewrite (Hreg 2%bv ltac:(reg_neq_tac)); exact Hsp|].
  split; [rewrite (Hreg 3%bv ltac:(reg_neq_tac)); exact Hgp|].
  split; [rewrite (Hreg 4%bv ltac:(reg_neq_tac)); exact Htp | exact Hro]. }
split; [exact Hin|]. split; [exact Hnn|]. split; [exact Hmac|].
split; [rewrite (Hreg RV_s0 ltac:(reg_neq_tac)); exact Vsp0|].
split; [rewrite (Hreg RV_s1 ltac:(reg_neq_tac)); exact Vsp1|].
split; [rewrite (Hreg RV_s7 ltac:(reg_neq_tac)); exact VF|].
split; [exact VFsp|].
split; [rewrite (Hreg RV_s3 ltac:(reg_neq_tac)); exact VshF|].
split; [exact Vexp|]. split; [exact Vmac|]. split; [exact Vshexp|].
split; [exact Vbody|]. split; [exact Vnn|].
rewrite (Hreg RV_s8 ltac:(reg_neq_tac)); exact Vnp.
Qed.

(* ================================================================================================
   The loop, closed over the S3 turn hypothesis: 343 - k turns remain, so induct on that.
   ================================================================================================ *)
Lemma s4_loop : forall cx POST,
(forall k, 0 <= k < sg_nturns IM ->
(k + 1 < sg_nturns IM -> @sc_from_T fx rc SK SEGS B ameter_triv WK IM cx POST (k + 1)) ->
@sc_from_TX fx rc SK SEGS B ameter_triv WK IM cx POST ->
@sc_from_T fx rc SK SEGS B ameter_triv WK IM cx POST k) ->
@sc_from_TX fx rc SK SEGS B ameter_triv WK IM cx POST ->
forall k, 0 <= k < sg_nturns IM -> @sc_from_T fx rc SK SEGS B ameter_triv WK IM cx POST k.
Proof.
intros cx POST HTURN HTX.
assert (Hall : forall (m : nat) k, 0 <= k < sg_nturns IM -> sg_nturns IM - k <= Z.of_nat m ->
@sc_from_T fx rc SK SEGS B ameter_triv WK IM cx POST k).
{ induction m as [|m IH]; intros k Hk Hm.
  - exfalso. cbn [Z.of_nat] in Hm. lia.
  - apply (HTURN k Hk); [|exact HTX].
    intros Hlt. apply IH; [lia|]. rewrite Nat2Z.inj_succ in Hm. lia. }
intros k Hk. apply (Hall (Z.to_nat (sg_nturns IM - k)) k Hk). rewrite Z2Nat.id by lia. lia.
Qed.

(* ================================================================================================
   The guard at C3: `flags & 2` and `n' = 8904`.  Both failing arms jump to C5; the passing arm
   reaches the spill pair at BASE + 0x510 with a0 = 8904.
   ================================================================================================ *)
Lemma s4_from_C3 : forall cx POST ly3 S3 W3 regs3 mem3 md3 bs body bb,
@sc_from_C5 fx rc SK SEGS B ameter_triv WK IM cx POST ->
(forall (regsG : bvmap 5 word) md',
@sc_j rc SK SEGS B ameter_triv WK IM cx ly3 S3 W3 mem3 md' 1 ->
(forall r : bv 5, r <> 10%bv -> getr regsG r = getr regs3 r) ->
getr regsG 10%bv = Z_to_bv 64 8904 ->
Z.land (bs 0) 2 <> 0 -> sc_nprime IM bs = 8904 ->
SRr SEGS W3 (mkCfg (mkst regsG (Z_to_bv 64 (BASE + 1296)) mem3 (seg_rom SEGS)) md') POST) ->
@cut_C3 rc SK SEGS B ameter_triv WK IM cx ly3 S3 W3 regs3 mem3 md3 bs body bb ->
SRr SEGS W3 (cfg_at SEGS (sg_pc_c3 IM) regs3 mem3 md3) POST.
Proof.
intros cx POST ly3 S3 W3 regs3 mem3 md3 bs body bb HC5 HT HC3.
pose proof HC3 as HC3k.
destruct HC3k as (HJ & Hab & Hbb & Hblk & Hlen & Hbody & HF & Hsav & Hshbg & Hsh1 & Hob & Hom &
Himg & Hin & Hnn & Hmac & Vsp0 & Vsp1 & VF & VFb & VFsp & VshF & Vblki & Vexp & Vmac & Vshexp &
Vbody & Vnn & Vnp & Vfl & Vst).
s4geom.
assert (Hbs0 : 0 <= bs 0 < 256) by (destruct (Hin 0 ltac:(lia)) as (H1 & _); exact H1).
assert (Hfl : bv_unsigned (getr regs3 RV_a1) = bs 0).
{ rewrite Vfl. apply s4_bv_small. unfold sc_flags. lia. }
assert (Hnp0 : 0 <= sc_nprime IM bs < 2 ^ 64).
{ destruct (Hin 1 ltac:(lia)) as (H1 & _). destruct (Hin 2 ltac:(lia)) as (H2 & _).
  unfold sc_nprime, sc_u16. cbn [sg_scene_n scene_geom_asan].
  destruct (Z.land (bs 0) 1 =? 0); lia. }
assert (Hnpv : bv_unsigned (getr regs3 RV_s8) = sc_nprime IM bs).
{ rewrite Vnp. apply s4_bv_small. exact Hnp0. }
unfold cfg_at.
replace (BASE + AF_LLVMFuzzerTestOneInput + SEG_C3_off) with (BASE + 1276)
by (unfold AF_LLVMFuzzerTestOneInput, SEG_C3_off; lia).
(* 0x82d74  andi a0,a1,2 *)
eapply (s4_andi W3 regs3 1276 mem3 md3 POST 0x25f513 _ _ _ 10%bv RV_a1 2 (Z_to_bv 64 (Z.land (bs 0) 2)));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| unfold v_andi; rewrite Hfl; repeat f_equal; vm_compute; reflexivity | ].
intros md1 Hm1. replace (1276 + 4) with 1280 by lia.
(* 0x82d78  beqz a0, +0x138  -> C5 *)
eapply (s4_branch_off W3 _ 1280 mem3 md1 POST 0x12050c63 BC_EQ _ _ _ 10%bv 0%bv 312);
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | | ].
- intros Hb md2 Hm2. replace (1280 + 312) with 1592 by lia.
  replace (BASE + 1592) with (BASE + AF_LLVMFuzzerTestOneInput + SEG_C5_off)
  by (unfold AF_LLVMFuzzerTestOneInput, SEG_C5_off; lia).
  apply (HC5 ly3 S3 W3 _ mem3 md2 bs body bb 1).
  apply (s4_C5_of_C3 cx ly3 S3 W3 regs3 mem3 md3 md2 bs body bb _ HC3
  (s4_sj_mat cx ly3 S3 W3 mem3 md1 md2 1 Hm2 (s4_sj_mat cx ly3 S3 W3 mem3 md3 md1 1 Hm1 HJ))).
  intros r Hr. rewrite (getr_other regs3 10%bv _ r Hr). reflexivity.
- intros Hb md2 Hm2.
  rewrite (getr_same regs3 10%bv _ ltac:(reg_neq_tac)) in Hb.
  rewrite getr_zero in Hb. rewrite (branch_eq_lit _ 0 ltac:(lia)) in Hb.
  assert (Hland : Z.land (bs 0) 2 <> 0).
  { intros Hc. rewrite Hc in Hb. vm_compute in Hb. discriminate Hb. }
  clear Hb. replace (1280 + 4) with 1284 by lia.
  (* 0x82d7c  lui a0,2 *)
  eapply (s4_lui W3 _ 1284 mem3 md2 POST 0x00002537 _ _ 10%bv 8192 (Z_to_bv 64 8192));
  [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | ].
  intros md3' Hm3. replace (1284 + 4) with 1288 by lia.
  (* 0x82d80  addiw a0,a0,0x2c8 *)
  eapply (s4_opimm32 W3 _ 1288 mem3 md3' POST 0x2c85051b _ _ _ 10%bv 10%bv 712 (Z_to_bv 64 8904));
  [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity
  | rewrite (getr_same _ 10%bv _ ltac:(reg_neq_tac)); vm_compute; reflexivity | ].
  intros md4 Hm4. replace (1288 + 4) with 1292 by lia.
  (* 0x82d84  bne s8,a0, +0x12c  -> C5 *)
  eapply (s4_branch_off W3 _ 1292 mem3 md4 POST 0x12ac1663 BC_NE _ _ _ RV_s8 10%bv 300);
  [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | vm_compute; reflexivity | | ].
  + intros Hb2 md5 Hm5. replace (1292 + 300) with 1592 by lia.
    replace (BASE + 1592) with (BASE + AF_LLVMFuzzerTestOneInput + SEG_C5_off)
    by (unfold AF_LLVMFuzzerTestOneInput, SEG_C5_off; lia).
    apply (HC5 ly3 S3 W3 _ mem3 md5 bs body bb 1).
    apply (s4_C5_of_C3 cx ly3 S3 W3 regs3 mem3 md3 md5 bs body bb _ HC3
    (s4_sj_mat cx ly3 S3 W3 mem3 md4 md5 1 Hm5 (s4_sj_mat cx ly3 S3 W3 mem3 md3' md4 1 Hm4
    (s4_sj_mat cx ly3 S3 W3 mem3 md2 md3' 1 Hm3 (s4_sj_mat cx ly3 S3 W3 mem3 md1 md2 1 Hm2
    (s4_sj_mat cx ly3 S3 W3 mem3 md3 md1 1 Hm1 HJ)))))).
    intros r Hr. rewrite !(getr_other _ 10%bv _ r Hr). reflexivity.
  + intros Hb2 md5 Hm5.
    rewrite (getr_same _ 10%bv _ ltac:(reg_neq_tac)) in Hb2.
    rewrite !(getr_other _ 10%bv _ RV_s8 ltac:(reg_neq_tac)) in Hb2.
    rewrite (branch_ne_lit _ 8904 ltac:(lia)) in Hb2.
    apply Bool.negb_false_iff, Z.eqb_eq in Hb2.
    rewrite Hnpv in Hb2.
    replace (1292 + 4) with 1296 by lia.
    apply (HT _ md5
    (s4_sj_mat cx ly3 S3 W3 mem3 md4 md5 1 Hm5 (s4_sj_mat cx ly3 S3 W3 mem3 md3' md4 1 Hm4
    (s4_sj_mat cx ly3 S3 W3 mem3 md2 md3' 1 Hm3 (s4_sj_mat cx ly3 S3 W3 mem3 md1 md2 1 Hm2
    (s4_sj_mat cx ly3 S3 W3 mem3 md3 md1 1 Hm1 HJ)))))).
    * intros r Hr. rewrite !(getr_other _ 10%bv _ r Hr). reflexivity.
    * rewrite (getr_same _ 10%bv _ ltac:(reg_neq_tac)). reflexivity.
    * exact Hland.
    * exact Hb2.
Qed.

(* ================================================================================================
   THE TAIL, 0x82e74 .. 0x82eb0 (k = 0x5fc .. 0x638): the loop exit.  cut_TX carries got = 8904 in
   BOTH s4 and s8 and the declared slot [s1+0x40] = 8904, so the two `bne` checks are DECIDED;
   `again` holds b in full (SceneTM.scT_again_all at k = 343), so the bcmp of `again` against `body`
   returns 0 and the `bnez` is refuted; the free of `again` takes the block list back to a
   permutation of the entry's plus `body`, and `ld s8,8(s1)` reloads n' = 8904.  Lands at C5, ev = 3.
   The call discharges and the C5 rebuild follow the asan-ubsan twin's `s4_tail`
   (at f9686f30a06, lib/AU/P_LLVMFuzzerTestOneInput_S4.v:271-791); the walk
   itself is concrete, through this file's step lemmas, where the twin's is symbolic.
   ================================================================================================ *)
Lemma s4_TX : forall cx POST,
@sc_base rc SEGS B ameter_triv WK cx ->
@sc_from_C5 fx rc SK SEGS B ameter_triv WK IM cx POST ->
@sc_from_TX fx rc SK SEGS B ameter_triv WK IM cx POST.
Proof.
intros cx POST HBASE HC5 ly3 S3 W3 regs3 mem3 md3 bs body again b HTX.
(* ---- the entry facts ---- *)
pose proof HBASE as (HBASE0 & HSP1).
pose proof HBASE0 as (HPRE & HraW & Hp10 & Hp11 & Hpn0 & Hfr0 & Hev0 & Hlive0 & HROD0 & HSINK0 &
Hfd0 & Hfs0 & HMO0).
pose proof HPRE as (HAR0 & Hra & Hra0 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof s4_base_lo as (HB0 & HB1 & HB2 & HB3).
assert (HES : ESTACK = 4096) by reflexivity.
assert (HAS : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTKb.
assert (HO : c_sp1 cx = spZ (c_regs cx) - 224 \/ c_sp1 cx = spZ (c_regs cx) - 240).
{ revert HSP1 Hal16. clear. intros HSP1 Hal16. rewrite HSP1. Z.div_mod_to_equations. lia. }
assert (HOmod : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
{ destruct HO as [HOx | HOx]; rewrite HOx;
  [replace (spZ (c_regs cx) - 224 - spZ (c_regs cx)) with (-224) by lia
  |replace (spZ (c_regs cx) - 240 - spZ (c_regs cx)) with (-240) by lia]; reflexivity. }
(* ---- the cut ---- *)
destruct HTX as (HT & HgotX & Hgot2).
pose proof HT as (Hk & Hwhole & HJj & Hab & Hbbnd & HokB & HokA & Hsepab & Hlenb & Hgb & Hjaex &
Hfrm & Hsav & Hshbg & Hshblki & HopB & HopM & Himg & Hinput & Hmacb & Rsp0 & Rsp1 & RFsp & RshF &
Rblki & RsrcA & RsrcB & Rmac & Rshexp & Rbody & Ragain & Rnprime & Rgot & Rkk & Rdecl & Rn1 & Rext &
Rnag & Rexp & RFb & Rnn & Rbody2 & Rf8).
pose proof HJj as (HJ & Hfrs3 & Hmle).
destruct Hjaex as (ja & Hjalen & Hgagain).
pose proof Himg as (Hsp3 & Hgp3 & Htp3 & HROD3).
pose proof HokA as (HA4096 & HAzone & HAceil & HA16 & HAwr & HAftok).
pose proof HokB as (HB4096 & HBzone & HBceil & HB16 & HBwr & HBftok).
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & Hnev3 & Hk3 & HK1 & HK2 & HK3 & HK4 & _ & HPRES3 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
change (sg_scene_n IM) with 8904 in *. change (sg_nturns IM) with 343 in *.
change (sg_cid IM) with 8 in *.
assert (HRS : req_size 8904 = 8904) by reflexivity.
rewrite HRS in HAceil, HBceil.
pose proof (zone2_band _ _ HAzone) as HAz2. rewrite HRS in HAz2.
pose proof (zone2_band _ _ HBzone) as HBz2. rewrite HRS in HBz2.
assert (Hsp1lo : alloc_ceiling + 16384 <= c_sp1 cx) by lia.
assert (Hsp1hi : c_sp1 cx + 96 <= spZ (c_regs cx)) by lia.
assert (Hsp1top : spZ (c_regs cx) <= 2 ^ 47) by lia.
(* b fills again in full at the exit *)
assert (Hlenb' : length b = 8904%nat) by (apply Nat2Z.inj; rewrite Hlenb; reflexivity).
assert (Hja0 : ja = [])
by (apply length_zero_iff_nil; apply Nat2Z.inj; rewrite Hjalen, scT_off_343; reflexivity).
assert (Hfa : firstn (Z.to_nat (scT_off 343)) b = b)
by (rewrite scT_off_343; replace (Z.to_nat 8904) with 8904%nat by reflexivity;
    apply firstn_all2; lia).
rewrite Hfa, Hja0, app_nil_r in Hgagain.
assert (HinA : In (again, 8904) (ablocks B ly3 S3))
by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (HinB : In (body, 8904) (ablocks B ly3 S3))
by (rewrite Hab; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (Hown3 : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (HVA : forall i, 0 <= i < 8904 ->
aview SEGS (w_H W3) mem3 (again + i) = Some (nth (Z.to_nat i) (u8s b) 0)).
{ intros i Hi. destruct (garr8_nthZ SEGS _ _ _ i Hgagain ltac:(lia)
    ltac:(unfold u8s; rewrite length_map; lia)) as (Hv & Hr).
  exact (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr). }
assert (HVB : forall i, 0 <= i < 8904 ->
aview SEGS (w_H W3) mem3 (body + i) = Some (nth (Z.to_nat i) (u8s b) 0)).
{ intros i Hi. destruct (garr8_nthZ SEGS _ _ _ i Hgb ltac:(lia)
    ltac:(unfold u8s; rewrite length_map; lia)) as (Hv & Hr).
  exact (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr). }
(* ---- the cut's registers and spill slots, as plain equations (the table's rows are literal) ---- *)
assert (V_s0 : getr regs3 (8%bv : bv 5) = Z_to_bv 64 (spZ (c_regs cx))) by exact Rsp0.
assert (V_s1 : getr regs3 (9%bv : bv 5) = Z_to_bv 64 (c_sp1 cx)) by exact Rsp1.
assert (V_s3 : getr regs3 (19%bv : bv 5) = Z_to_bv 64 (shadow_addr (sc_F SEGS IM cx))) by exact RshF.
assert (V_s8 : getr regs3 (24%bv : bv 5) = Z_to_bv 64 8904) by exact Hgot2.
assert (M_np : rdword (aview SEGS (w_H W3) mem3) (c_sp1 cx + 8) = Some 8904) by exact Rnprime.
assert (M_F16 : rdword (aview SEGS (w_H W3) mem3) (c_sp1 cx + 16) = Some (sc_F SEGS IM cx))
by exact RFsp.
assert (M_exp : rdword (aview SEGS (w_H W3) mem3) (c_sp1 cx + 24) = Some (sc_F SEGS IM cx + 224))
by exact Rexp.
assert (M_shexp : rdword (aview SEGS (w_H W3) mem3) (c_sp1 cx + 32)
= Some (shadow_addr (sc_F SEGS IM cx) + 28)) by exact Rshexp.
assert (M_Fb : rdword (aview SEGS (w_H W3) mem3) (c_sp1 cx + 40) = Some (sc_F SEGS IM cx))
by exact RFb.
assert (M_mac : rdword (aview SEGS (w_H W3) mem3) (c_sp1 cx + 48) = Some (sc_F SEGS IM cx + 112))
by exact Rmac.
assert (M_nn : rdword (aview SEGS (w_H W3) mem3) (c_sp1 cx + 56) = Some (sc_nn IM bs)) by exact Rnn.
assert (M_decl : rdword (aview SEGS (w_H W3) mem3) (c_sp1 cx + 64) = Some 8904) by exact Rdecl.
assert (M_again : rdword (aview SEGS (w_H W3) mem3) (c_sp1 cx + 80) = Some again) by exact Ragain.
assert (M_body : rdword (aview SEGS (w_H W3) mem3) (c_sp1 cx + 88) = Some body) by exact Rbody.
(* ---- the walk, 0x5fc .. 0x624 ---- *)
unfold cfg_at. cbn [sg_pc_tx scene_geom_asan].
replace (BASE + AF_LLVMFuzzerTestOneInput + SEG_TX_off) with (BASE + 1532)
by (unfold AF_LLVMFuzzerTestOneInput, SEG_TX_off; lia).
change (w64 (BASE + 1532)) with (Z_to_bv 64 (BASE + 1532)).
(* 0x82e74  lui a0,2 *)
eapply (s4_lui W3 regs3 1532 mem3 md3 POST 0x00002537 _ _ 10%bv 8192 (Z_to_bv 64 8192));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity | ].
intros mA hA. replace (1532 + 4) with 1536 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem3 _ mA 2 hA HJj) as J1.
(* 0x82e78  addiw a0,a0,0x2c8 *)
eapply (s4_opimm32 W3 _ 1536 mem3 mA POST 0x2c85051b _ _ _ 10%bv 10%bv 712 (Z_to_bv 64 8904));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| rewrite (getr_same _ 10%bv _ ltac:(reg_neq_tac)); vm_compute; reflexivity | ].
intros mB hB. replace (1536 + 4) with 1540 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem3 _ mB 2 hB J1) as J2.
(* 0x82e7c  ld s7,0x10(s1) *)
eapply (s4_ld W3 _ 1540 mem3 mB POST 0x0104bb83 _ _ _ 23%bv 9%bv 16
(c_sp1 cx + 16) (sc_F SEGS IM cx));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac];
  rewrite V_s1, s4_bv_small by lia; reflexivity
| lia | lia | exact M_F16 | ].
intros mC hC. replace (1540 + 4) with 1544 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem3 _ mC 2 hC J2) as J3.
(* 0x82e80  ld a1,0x58(s1) *)
eapply (s4_ld W3 _ 1544 mem3 mC POST 0x0584b583 _ _ _ 11%bv 9%bv 88 (c_sp1 cx + 88) body);
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac];
  rewrite V_s1, s4_bv_small by lia; reflexivity
| lia | lia | exact M_body | ].
intros mD hD. replace (1544 + 4) with 1548 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem3 _ mD 2 hD J3) as J4.
(* 0x82e84  bne s8,a0 -> abort: REFUTED, got = 8904 in s8 and 8904 in a0 *)
eapply (s4_branch_off W3 _ 1548 mem3 mD POST 0x2cac1063 BC_NE _ _ _ 24%bv 10%bv 704);
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | | ].
{ intros Hb mX hX. exfalso.
  repeat first [rewrite getr_other in Hb by reg_neq_tac | rewrite getr_same in Hb by reg_neq_tac].
  rewrite V_s8, (branch_ne_lit _ 8904 ltac:(lia)), s4_bv_small in Hb by lia.
  vm_compute in Hb. discriminate Hb. }
intros Hb mE hE. clear Hb. replace (1548 + 4) with 1552 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem3 _ mE 2 hE J4) as J5.
(* 0x82e88  ld a2,0x40(s1) *)
eapply (s4_ld W3 _ 1552 mem3 mE POST 0x0404b603 _ _ _ 12%bv 9%bv 64 (c_sp1 cx + 64) 8904);
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac];
  rewrite V_s1, s4_bv_small by lia; reflexivity
| lia | lia | exact M_decl | ].
intros mF hF. replace (1552 + 4) with 1556 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem3 _ mF 2 hF J5) as J6.
(* 0x82e8c  bne a2,a0 -> abort: REFUTED, declared = 8904 *)
eapply (s4_branch_off W3 _ 1556 mem3 mF POST 0x2aa61c63 BC_NE _ _ _ 12%bv 10%bv 696);
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | | ].
{ intros Hb2 mX hX. exfalso.
  repeat first [rewrite getr_other in Hb2 by reg_neq_tac | rewrite getr_same in Hb2 by reg_neq_tac].
  rewrite (branch_ne_lit _ 8904 ltac:(lia)), s4_bv_small in Hb2 by lia.
  vm_compute in Hb2. discriminate Hb2. }
intros Hb2 mG hG. clear Hb2. replace (1556 + 4) with 1560 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem3 _ mG 2 hG J6) as J7.
(* 0x82e90  lui a0,2 *)
eapply (s4_lui W3 _ 1560 mem3 mG POST 0x00002537 _ _ 10%bv 8192 (Z_to_bv 64 8192));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity | ].
intros mH hH. replace (1560 + 4) with 1564 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem3 _ mH 2 hH J7) as J8.
(* 0x82e94  addiw a2,a0,0x2c8 *)
eapply (s4_opimm32 W3 _ 1564 mem3 mH POST 0x2c85061b _ _ _ 12%bv 10%bv 712 (Z_to_bv 64 8904));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| rewrite (getr_same _ 10%bv _ ltac:(reg_neq_tac)); vm_compute; reflexivity | ].
intros mI hI. replace (1564 + 4) with 1568 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem3 _ mI 2 hI J8) as J9.
(* 0x82e98  ld a0,0x50(s1) *)
eapply (s4_ld W3 _ 1568 mem3 mI POST 0x0504b503 _ _ _ 10%bv 9%bv 80 (c_sp1 cx + 80) again);
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac];
  rewrite V_s1, s4_bv_small by lia; reflexivity
| lia | lia | exact M_again | ].
intros mJ hJ. replace (1568 + 4) with 1572 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem3 _ mJ 2 hJ J9) as J10.
(* 0x82e9c  jal __wrap_bcmp *)
eapply (s4_call W3 _ 1572 mem3 mJ POST SS___interceptor_trampoline_bcmp 1%bv);
[vm_compute; reflexivity | ].
intros mK hK. replace (1572 + 4) with 1576 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem3 _ mK 2 hK J10) as J11.
pose proof (proj1 J11) as HJK.
(* ---- bcmp(again, body, 8904) ---- *)
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA SS___interceptor_trampoline_bcmp) ABCMP W3 rg mm
    (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(8, c_fpos cx)] ly3 S3 mdx 2 again body 8904 (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + 1576))) end.
  - exact HJK.
  - repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac]; reflexivity.
  - repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac]; reflexivity.
  - repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac]; reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - unfold spZ.
    repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
    unfold spZ in Hsp3. rewrite Hsp3. lia.
  - exact HOmod.
  - lia.
  - lia.
  - repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac];
    exact Hgp3.
  - repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac];
    exact Htp3.
  - rewrite (getr_same _ 1%bv _ ltac:(reg_neq_tac)); reflexivity.
  - apply s4_ret; [lia | reflexivity].
  - intros a Ha. split.
    + replace a with (again + (a - again)) by lia. rewrite (HVA (a - again) ltac:(lia)). discriminate.
    + unfold spZ.
      repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
      unfold spZ in Hsp3. rewrite Hsp3. lia.
  - intros a Ha. split.
    + replace a with (body + (a - body)) by lia. rewrite (HVB (a - body) ltac:(lia)). discriminate.
    + unfold spZ.
      repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
      unfold spZ in Hsp3. rewrite Hsp3. lia.
  - intros a Ha. lia.
  - intros a Ha. lia.
  - exact (amem_range_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 again 8904 again 8904 HAR3 HinA
      ltac:(lia) ltac:(rewrite HRS; lia)).
  - exact (amem_range_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 body 8904 body 8904 HAR3 HinB
      ltac:(lia) ltac:(rewrite HRS; lia)).
  - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 again 8904 again 8904 HAR3 HinA
      ltac:(lia) ltac:(rewrite HRS; lia)).
  - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 again 8904 again 8904
      HAR3 HinA ltac:(lia) ltac:(rewrite HRS; lia) ltac:(lia)).
  - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 body 8904 body 8904 HAR3 HinB
      ltac:(lia) ltac:(rewrite HRS; lia)).
  - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 body 8904 body 8904
      HAR3 HinB ltac:(lia) ltac:(rewrite HRS; lia) ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & KMc0 & KPres).
(* again holds b in full, so the compare is equal *)
assert (Hv0 : v = w64 0).
{ apply (proj2 Hcmp). intros i Hi. rewrite (HVA i Hi), (HVB i Hi). reflexivity. }
assert (KMc : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 2 * ESTACK <= a < c_sp1 cx) ->
aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. apply KMc0; [exact Ha | lia]. }
(* the callee-saved registers the rest of the tail reads *)
assert (HPr : forall (n : Z) (r : bv 5), acallee_saved n -> Z_to_bv 5 n = r ->
getr regs2 r = getr regs2 r) by (intros; reflexivity).
clear HPr.
assert (Q2 : getr regs2 (2%bv : bv 5) = getr regs3 (2%bv : bv 5)).
{ pose proof (HP2 2 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 2) with (2%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  reflexivity. }
assert (Q3 : getr regs2 (3%bv : bv 5) = w64 (as_gp B)).
{ pose proof (HP2 3 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 3) with (3%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact Hgp3. }
assert (Q4 : getr regs2 (4%bv : bv 5) = w64 (as_tp B)).
{ pose proof (HP2 4 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 4) with (4%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact Htp3. }
assert (Q8 : getr regs2 (8%bv : bv 5) = Z_to_bv 64 (spZ (c_regs cx))).
{ pose proof (HP2 8 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 8) with (8%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact V_s0. }
assert (Q9 : getr regs2 (9%bv : bv 5) = Z_to_bv 64 (c_sp1 cx)).
{ pose proof (HP2 9 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 9) with (9%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact V_s1. }
assert (Q19 : getr regs2 (19%bv : bv 5) = Z_to_bv 64 (shadow_addr (sc_F SEGS IM cx))).
{ pose proof (HP2 19 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 19) with (19%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact V_s3. }
assert (Q23 : getr regs2 (23%bv : bv 5) = Z_to_bv 64 (sc_F SEGS IM cx)).
{ pose proof (HP2 23 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 23) with (23%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  reflexivity. }
assert (SAV2 : forall j, 0 <= j < 13 ->
rdword (aview SEGS (w_H W3) mem2) (spZ (c_regs cx) - 8 - 8 * j)
= Some (bv_unsigned (getr (c_regs cx) (nth (Z.to_nat j) sc_saved_regs 0%bv)))).
{ intros j Hj.
  rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) mem2) _);
  [exact (Hsav j Hj) | intros kk Hkk; apply KMc; lia]. }
assert (M_again2 : rdword (aview SEGS (w_H W3) mem2) (c_sp1 cx + 80) = Some again).
{ rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) mem2) _);
  [exact M_again | intros kk Hkk; apply KMc; lia]. }
(* 0x82ea0  bnez a0 -> abort: REFUTED, the compare is 0 *)
eapply (s4_branch_off W3 regs2 1576 mem2 md2 POST 0x2a051263 BC_NE _ _ _ 10%bv 0%bv 676);
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | | ].
{ intros Hb3 mX hX. exfalso.
  rewrite Hv, Hv0, getr_zero, (branch_ne_lit _ 0 ltac:(lia)) in Hb3.
  vm_compute in Hb3. discriminate Hb3. }
intros Hb3 mL hL. clear Hb3. replace (1576 + 4) with 1580 by lia.
assert (SJL : @sc_j rc SK SEGS B ameter_triv WK IM cx ly3 S3 W3 mem2 md2 2).
{ unfold sc_j. split; [exact HJ2 | split; [exact Hfrs3 | exact Hmle]]. }
pose proof (s4_sj_mat cx ly3 S3 W3 mem2 _ mL 2 hL SJL) as JL1.
(* 0x82ea4  ld a0,0x50(s1) *)
eapply (s4_ld W3 regs2 1580 mem2 mL POST 0x0504b503 _ _ _ 10%bv 9%bv 80 (c_sp1 cx + 80) again);
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| rewrite Q9, s4_bv_small by lia; reflexivity
| lia | lia | exact M_again2 | ].
intros mM hM. replace (1580 + 4) with 1584 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem2 _ mM 2 hM JL1) as JL2.
(* 0x82ea8  jal __wrap_free *)
eapply (s4_call W3 _ 1584 mem2 mM POST SS___interceptor_trampoline_free 1%bv);
[vm_compute; reflexivity | ].
intros mN hN. replace (1584 + 4) with 1588 by lia.
pose proof (s4_sj_mat cx ly3 S3 W3 mem2 _ mN 2 hN JL2) as JL3.
pose proof (proj1 JL3) as HJN.
rewrite (pal_free B TL).
(* ---- free(again) ---- *)
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  eapply (afree04_rule_triv SEGS B pa_segs_low (pal_env B TL) LAWS ML AFREE W3 rg mm
    (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(8, c_fpos cx)] ly3 S3 mdx 2 again 8904 (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + 1588)) (rt_ch cx)) end.
  - exact HJN.
  - exact HinA.
  - repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac]; reflexivity.
  - unfold spZ.
    repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
    rewrite Q2. unfold spZ in Hsp3. rewrite Hsp3. lia.
  - exact HOmod.
  - lia.
  - lia.
  - repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac]; exact Q3.
  - repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac]; exact Q4.
  - rewrite (getr_same _ 1%bv _ ltac:(reg_neq_tac)); reflexivity.
  - apply s4_ret; [lia | reflexivity].
  - lia.
  - eapply (achain_chain_pre ly3 (aview SEGS (w_H W3) mem2) (c_sp1 cx) (spZ (c_regs cx))).
    + unfold rt_ch.
      destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hf0 | Hf0].
      * eapply (achain_ly_top (c_ly cx) ly3); [exact Etop|].
        eapply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx))
          (aview SEGS (w_H W3) mem2) (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) []
          (c_sp1 cx) Hch ltac:(lia)).
        { intros a Ha. rewrite (KMc a ltac:(lia) ltac:(lia)). apply HK1; lia. }
        { replace (spZ (c_regs cx) - 8) with (spZ (c_regs cx) - 8 - 8 * 0) by lia.
          exact (SAV2 0 ltac:(lia)). }
        { replace (spZ (c_regs cx) - 16) with (spZ (c_regs cx) - 8 - 8 * 1) by lia.
          exact (SAV2 1 ltac:(lia)). }
        { exact Hra0. }
        { lia. }
        { revert Hal16. clear. intros. Z.div_mod_to_equations. lia. }
        { lia. }
        { lia. }
      * left. split; [right; left; lia | reflexivity].
    + unfold spZ.
      repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
      rewrite Q2. unfold spZ in Hsp3. rewrite Hsp3. lia.
    + unfold s0Z.
      repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
      rewrite Q8, s4_bv_small by lia. reflexivity.
    + unfold raZ. rewrite (getr_same _ 1%bv _ ltac:(reg_neq_tac)), s4_bv_small by lia. lia.
  - lazymatch goal with |- In _ _ =>
    apply (HTRACE (pc_free_ra0 (as_code B)) (BASE + 1588) _ cx HraW) end.
    + unfold raZ. rewrite (getr_same _ 1%bv _ ltac:(reg_neq_tac)), s4_bv_small by lia. reflexivity.
    + right. split; [reflexivity|]. left. lia.
  - exact HAftok.
  - exact I. }
cbv beta. intros W4 c4 Hwle4
  (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Hl1 & Hl2) & Hfrs4 & KPT & _).
pose proof KPT as (KT1 & KT2 & KT3 & KT4 & KT5 & KT6).
pose proof (proj1 HJ4) as HAR4.
assert (Hown4 : In (8, c_fpos cx) (frames S4)) by (rewrite Hfrs4; exact Hown3).
(* ---- the block list after the free ---- *)
assert (HPERM : Permutation (ablocks B ly4 S4) (ablocks B (c_ly cx) (c_S cx) ++ [(body, 8904)])).
{ apply (Permutation_cons_inv (a := (again, 8904))).
  apply (Permutation_trans (l' := l1 ++ (again, 8904) :: l2));
  [ rewrite Hl2; apply Permutation_middle
  | rewrite <- Hl1, Hab; apply Permutation_sym; apply Permutation_cons_append ]. }
assert (HBB4 : blocks_bytes S4 <= blocks_bytes (c_S cx) + req_size 8904).
{ rewrite (blocks_bytes_bsum B ly4 S4), (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
  rewrite (bsum_perm _ _ HPERM), bsum_app. cbn [bsum fold_right snd]. rewrite HRS. lia. }
(* ---- the memory transports from the cut's state to the state after the free ---- *)
assert (KSTK : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (c_sp1 cx - ASTACK <= a < c_sp1 cx) ->
aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite (KT1 a Ha ltac:(lia)). apply KMc; lia. }
assert (KBLK : forall i, 0 <= i < 8904 ->
aview SEGS (w_H W4) mem4 (body + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite (KT2 body 8904 i HinB ltac:(rewrite HRS; lia) ltac:(rewrite HRS; lia)).
  apply KMc; lia. }
assert (HFB : fs_frame_bytes 8 = 16384) by reflexivity.
assert (EF3 : frame_addr ly3 8 (c_fpos cx) = sc_F SEGS IM cx).
{ unfold sc_F, rt_F, frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  rewrite EF. reflexivity. }
assert (EF4 : frame_addr ly4 8 (c_fpos cx) = sc_F SEGS IM cx).
{ pose proof HJ4 as (_ & Hly4 & _). unfold sc_F, rt_F, frame_addr.
  pose proof Hly4 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
pose proof (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hown3) as (HF32 & _ & _ & _).
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hown3)
  as (HF4096 & HFceil & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 again 8904 8 (c_fpos cx) HAR3 HinA Hown3)
  as HdA.
unfold zdisjoint in HdA. cbn [fst snd] in HdA.
rewrite EF3 in HF32, HF4096, HFceil, HdA. rewrite HFB in HFceil, HdA. rewrite HRS in HdA.
assert (HSL : 2147450880 <= shadow_addr (sc_F SEGS IM cx)
/\ shadow_addr (sc_F SEGS IM cx) + 2048 <= 17594333462528).
{ assert (HQ : forall F, 4096 <= F -> F + 16384 <= 140737479966720 ->
    2147450880 <= shadow_addr F /\ shadow_addr F + 2048 <= 17594333462528)
    by (intros F H1 H2; unfold shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply HQ; lia. }
assert (HF8 : sc_F SEGS IM cx mod 8 = 0).
{ assert (HQ : forall F, F mod 32 = 0 -> F mod 8 = 0)
    by (intros F HF; Z.div_mod_to_equations; lia).
  apply HQ; exact HF32. }
assert (OPENIDX : forall F off len i, F mod 8 = 0 -> (F + off) mod 8 = 0 -> 0 <= off -> 0 <= len ->
off + len <= 16384 -> 0 <= i < (len + 7) / 8 ->
shadow_addr F <= shadow_of_addr SHADOW_OFF (F + off) + i < shadow_addr F + 2048)
by (intros F off len i H1 H2 H3 H4 H5 H6; unfold shadow_addr, shadow_of_addr;
    Z.div_mod_to_equations; lia).
assert (KFRM : forall a, (sc_F SEGS IM cx <= a < sc_F SEGS IM cx + 16384 \/
  shadow_addr (sc_F SEGS IM cx) <= a < shadow_addr (sc_F SEGS IM cx) + 2048) ->
aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha.
  rewrite (KT4 8 (c_fpos cx) a Hown3);
  [ apply KMc; lia
  | unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF3, HFB;
    change (16384 / 8) with 2048; exact Ha
  | cbv beta; rewrite ?HRS; destruct Ha as [Ha|Ha]; lia ]. }
assert (SPILL : forall aa vv, c_sp1 cx <= aa -> aa + 8 <= spZ (c_regs cx) ->
rdword (aview SEGS (w_H W3) mem3) aa = Some vv -> rdword (aview SEGS (w_H W4) mem4) aa = Some vv).
{ intros aa vv Hsa Hsb Hsr.
  rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W4) mem4) aa); [exact Hsr|].
  intros kk Hkk. apply KSTK; lia. }
assert (SHR : forall lo hi vv, 0 <= lo -> hi <= 2048 ->
sc_shr SEGS IM cx W3 mem3 lo hi vv -> sc_shr SEGS IM cx W4 mem4 lo hi vv).
{ intros lo hi vv Hlo Hhi Hsh o Ho. rewrite KFRM; [exact (Hsh o Ho) | right; lia]. }
assert (OPEN : forall off len, 0 <= off -> 0 <= len -> off + len <= 16384 ->
sc_open SEGS IM cx W3 mem3 off len -> sc_open SEGS IM cx W4 mem4 off len).
{ intros off len Ho Hl Hol (Hp & Hn & Hc). split; [exact Hp|]. split; [exact Hn|].
  intros i Hi. rewrite KFRM; [exact (Hc i Hi)|]. right.
  exact (OPENIDX (sc_F SEGS IM cx) off len i HF8 Hp Ho Hl Hol Hi). }
assert (GMOVE : forall (Wa Wb : world SEGS) (ma mb : word -> option byte) a l,
(forall j, 0 <= j < Z.of_nat (length l) ->
   aview SEGS (w_H Wb) mb (a + j) = aview SEGS (w_H Wa) ma (a + j)) ->
garr8 SEGS (mrestrict (w_H Wa) ma) a l -> garr8 SEGS (mrestrict (w_H Wb) mb) a l).
{ intros Wa Wb ma mb a l Hkp Hg j Hj. destruct (Hg j Hj) as (Hvv & Hrr). split; [|exact Hrr].
  apply (val_mem_moved SEGS (w_H Wa) (w_H Wb) ma mb (a + Z.of_nat j) (a + Z.of_nat j) 1%nat);
  [|exact Hvv]. intros kk Hkk. rewrite <- !Z.add_assoc. apply Hkp. lia. }
assert (HROF : arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W4) mem4)).
{ intros a Hro Hown Herr.
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a).
  - exact (HROD0 a Hro Hown Herr).
  - destruct Hro as [(sg & Hsg & _ & Hr) | Hgot]; [exists sg; split; [exact Hsg | exact Hr]|].
    rewrite HWRLO, HWRHI in Hgot. exact (pa_relro_img a Hgot).
  - exact Hown.
  - exact Herr.
  - exact (fp_spares_closed [] a sink_closed_nil). }
pose proof (al_frames _ _ LAWS ly4 S4 W4 mem4 md4 8 (c_fpos cx) HAR4 Hown4)
  as (_ & _ & HFb4 & HFsh4).
(* ---- the callee-saved registers after the free ---- *)
assert (G2 : getr regs4 (2%bv : bv 5) = getr regs3 (2%bv : bv 5)).
{ pose proof (HP4 2 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 2) with (2%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact Q2. }
assert (G3 : getr regs4 (3%bv : bv 5) = w64 (as_gp B)).
{ pose proof (HP4 3 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 3) with (3%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact Q3. }
assert (G4 : getr regs4 (4%bv : bv 5) = w64 (as_tp B)).
{ pose proof (HP4 4 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 4) with (4%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact Q4. }
assert (G8 : getr regs4 (8%bv : bv 5) = Z_to_bv 64 (spZ (c_regs cx))).
{ pose proof (HP4 8 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 8) with (8%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact Q8. }
assert (G9 : getr regs4 (9%bv : bv 5) = Z_to_bv 64 (c_sp1 cx)).
{ pose proof (HP4 9 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 9) with (9%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact Q9. }
assert (G19 : getr regs4 (19%bv : bv 5) = Z_to_bv 64 (shadow_addr (sc_F SEGS IM cx))).
{ pose proof (HP4 19 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 19) with (19%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact Q19. }
assert (G23 : getr regs4 (23%bv : bv 5) = Z_to_bv 64 (sc_F SEGS IM cx)).
{ pose proof (HP4 23 ltac:(cbv [acallee_saved]; lia)) as HQ.
  replace (Z_to_bv 5 23) with (23%bv : bv 5) in HQ by (apply bv_eq; vm_compute; reflexivity).
  rewrite HQ. repeat first [rewrite getr_other by reg_neq_tac | rewrite getr_same by reg_neq_tac].
  exact Q23. }
(* 0x82eac  ld s8,8(s1) reloads n' = 8904 *)
eapply (s4_ld W4 regs4 1588 mem4 md4 POST 0x0084bc03 _ _ _ 24%bv 9%bv 8 (c_sp1 cx + 8) 8904);
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| rewrite G9, s4_bv_small by lia; reflexivity
| lia | lia | apply SPILL; [lia | lia | exact M_np] | ].
intros mO hO. replace (1588 + 4) with 1592 by lia.
(* ---- the cut C5 at 0x82eb0, ev = 3 ---- *)
assert (SJ4 : @sc_j rc SK SEGS B ameter_triv WK IM cx ly4 S4 W4 mem4 md4 3).
{ unfold sc_j. split; [exact HJ4 | split; [rewrite Hfrs4; exact Hfrs3 | exact I]]. }
pose proof (s4_sj_mat cx ly4 S4 W4 mem4 md4 mO 3 hO SJ4) as SJ5.
assert (HNP : sc_nprime IM bs = 8904) by exact (proj2 Hwhole).
assert (HNN : sc_nn IM bs = 8904) by (unfold sc_nn; rewrite HNP; reflexivity).
assert (V8f : getr (regupd regs4 (24%bv : bv 5) (Z_to_bv 64 8904)) (8%bv : bv 5)
= Z_to_bv 64 (spZ (c_regs cx)))
by (rewrite (getr_other regs4 (24%bv : bv 5) _ (8%bv : bv 5) ltac:(reg_neq_tac)); exact G8).
assert (V9f : getr (regupd regs4 (24%bv : bv 5) (Z_to_bv 64 8904)) (9%bv : bv 5)
= Z_to_bv 64 (c_sp1 cx))
by (rewrite (getr_other regs4 (24%bv : bv 5) _ (9%bv : bv 5) ltac:(reg_neq_tac)); exact G9).
assert (V19f : getr (regupd regs4 (24%bv : bv 5) (Z_to_bv 64 8904)) (19%bv : bv 5)
= Z_to_bv 64 (shadow_addr (sc_F SEGS IM cx)))
by (rewrite (getr_other regs4 (24%bv : bv 5) _ (19%bv : bv 5) ltac:(reg_neq_tac)); exact G19).
assert (V23f : getr (regupd regs4 (24%bv : bv 5) (Z_to_bv 64 8904)) (23%bv : bv 5)
= Z_to_bv 64 (sc_F SEGS IM cx))
by (rewrite (getr_other regs4 (24%bv : bv 5) _ (23%bv : bv 5) ltac:(reg_neq_tac)); exact G23).
assert (V24f : getr (regupd regs4 (24%bv : bv 5) (Z_to_bv 64 8904)) (24%bv : bv 5)
= Z_to_bv 64 8904) by (apply getr_same; reg_neq_tac).
assert (V2f : spZ (regupd regs4 (24%bv : bv 5) (Z_to_bv 64 8904)) = c_sp1 cx).
{ unfold spZ. rewrite (getr_other regs4 (24%bv : bv 5) _ (2%bv : bv 5) ltac:(reg_neq_tac)), G2.
  unfold spZ in Hsp3. exact Hsp3. }
assert (V3f : getr (regupd regs4 (24%bv : bv 5) (Z_to_bv 64 8904)) (3%bv : bv 5) = w64 (as_gp B))
by (rewrite (getr_other regs4 (24%bv : bv 5) _ (3%bv : bv 5) ltac:(reg_neq_tac)); exact G3).
assert (V4f : getr (regupd regs4 (24%bv : bv 5) (Z_to_bv 64 8904)) (4%bv : bv 5) = w64 (as_tp B))
by (rewrite (getr_other regs4 (24%bv : bv 5) _ (4%bv : bv 5) ltac:(reg_neq_tac)); exact G4).
replace (BASE + 1592) with (BASE + AF_LLVMFuzzerTestOneInput + SEG_C5_off)
by (unfold AF_LLVMFuzzerTestOneInput, SEG_C5_off; lia).
apply (HC5 ly4 S4 W4 _ mem4 mO bs body b 3).
unfold cut_C5.
split; [lia|].
split; [exact SJ5|].
split; [rewrite HNN; exact HPERM|].
split; [rewrite HNN; exact HBB4|].
split; [rewrite HNN; exact HokB|].
split; [rewrite HNN; exact Hlenb|].
split.
{ apply (GMOVE W3 W4 mem3 mem4 body (u8s b)); [| exact Hgb].
  intros j Hj. unfold u8s in Hj. rewrite length_map, Hlenb' in Hj. apply KBLK. lia. }
split.
{ pose proof Hfrm as (Hflag & _ & _).
  split; [| split].
  - rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W4) mem4) _); [exact Hflag|].
    intros kk Hkk. apply KFRM. left. change (fs_frame_bytes (sg_cid IM)) with 16384. lia.
  - intros a Ha. rewrite <- EF4 in Ha. exact (proj1 (HFb4 a Ha)).
  - intros a Ha. change (fs_frame_bytes (sg_cid IM) / 8) with 2048 in Ha. rewrite <- EF4 in Ha.
    assert (Hi : 0 <= a - shadow_addr (frame_addr ly4 8 (c_fpos cx)) < fs_frame_bytes 8 / 8)
      by (change (fs_frame_bytes 8 / 8) with 2048; lia).
    pose proof (proj1 (HFsh4 _ Hi)) as Hq.
    replace (shadow_addr (frame_addr ly4 8 (c_fpos cx))
      + (a - shadow_addr (frame_addr ly4 8 (c_fpos cx)))) with a in Hq by lia.
    exact Hq. }
split; [intros j Hj; apply SPILL; [lia | lia | exact (Hsav j Hj)]|].
split.
{ unfold sc_shbg in Hshbg |- *. rewrite Forall_forall in Hshbg |- *. intros t Ht.
  pose proof (Hshbg t Ht) as Ht'.
  cbn [sg_sh_bg scene_geom_asan In] in Ht.
  apply SHR; [| | exact Ht'];
  repeat (destruct Ht as [<- | Ht]; [cbn [fst snd]; lia |]); destruct Ht. }
split; [apply SHR; [cbn; lia | cbn; lia | exact Hshblki]|].
split; [apply OPEN; [cbn; lia | cbn; lia | cbn; lia | exact HopB]|].
split; [apply OPEN; [cbn; lia | cbn; lia | cbn; lia | exact HopM]|].
split; [split; [exact V2f | split; [exact V3f | split; [exact V4f | exact HROF]]]|].
split; [exact Hinput|].
split; [rewrite HNN; lia|].
split.
{ apply (GMOVE W3 W4 mem3 mem4 _ (sc_macb bs)); [| exact Hmacb].
  intros j Hj. unfold sc_macb in Hj. cbn [length] in Hj.
  change (sg_off_mac IM) with 112. apply KFRM. left. lia. }
split; [exact V8f|].
split; [exact V9f|].
split; [exact V23f|].
split; [apply SPILL; [lia | lia | exact M_Fb]|].
split; [exact V19f|].
split; [apply SPILL; [lia | lia | exact M_exp]|].
split; [apply SPILL; [lia | lia | exact M_mac]|].
split; [apply SPILL; [lia | lia | exact M_shexp]|].
split; [apply SPILL; [lia | lia | exact M_body]|].
split; [apply SPILL; [lia | lia | exact M_nn]|].
rewrite HNP. exact V24f.
Qed.

(* ================================================================================================
   HELPERS FOR THE ENTRY BLOCK.  s4h_chain, s4h_garr8_moved, s4h_shadow_lo and s4h_open_idx are the
   asan-ubsan twin's s4_chain / s4_garr8_moved / s4_shadow_lo / s4_open_idx (at
   f9686f30a06, lib/AU/P_LLVMFuzzerTestOneInput_S4.v:133-174, :247-264), themselves cgif A/ACf5.v:172-186
   rt_chain; copied, not imported.
   ================================================================================================ *)
Ltac s4hrg := repeat (rewrite getr_other by reg_neq_tac).

Lemma s4h_matj : forall STK sp0 FP ly S (W0 : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc mdc' k,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc Wc memc mdc k ->
same_but_materialized mdc mdc' ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc Wc memc mdc' k.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc Wc memc mdc mdc' k HJ Hm.
rewrite (same_but_materialized_wvb mdc mdc' Hm).
apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma s4h_presj : forall STK sp0 FP ly S (W0 : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k a,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc Wc memc mdc k ->
sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc a.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc Wc memc mdc k a HJ Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact (Hp a Ha).
Qed.

(* a doubleword store into the real-stack window keeps the journal *)
Lemma s4h_sdj : forall STK sp0 ly S (W0 : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k memc' mdc' a v,
ajournal SEGS B STK sp0 [] ly S W0 mem md own lyc Sc Wc memc mdc k ->
same_but_materialized mdc mdc' -> s4_wr Wc memc memc' a v ->
sp0 - STK <= a -> a + 8 <= sp0 ->
ajournal SEGS B STK sp0 [] ly S W0 mem md own lyc Sc Wc memc' mdc' k.
Proof.
intros STK sp0 ly S W0 mem md own lyc Sc Wc memc mdc k memc' mdc' a v HJ Hm (H1 & H2 & H3 & _) Hlo Hhi.
eapply (ajournal_exec SEGS B LAWS pa_segs_low STK sp0 [] ly S W0 mem md own lyc Sc Wc memc mdc k
memc' mdc' (fun x => a <= x < a + 8) HJ).
- intros x Hx. apply H2. lia.
- exact H3.
- exact H1.
- exact Hm.
- intros b Hb. left. lia.
Qed.

(* the read-only bytes travel along the journal: FP is empty, so every image byte is a spare *)
Lemma s4h_arodata : forall STK sp0 ly S (W0 : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k,
ajournal SEGS B STK sp0 [] ly S W0 mem md own lyc Sc Wc memc mdc k ->
arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W0) mem) ->
arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H Wc) memc).
Proof.
intros STK sp0 ly S W0 mem md own lyc Sc Wc memc mdc k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Himg : in_img SEGS a).
{ destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
  apply (@pa_relro_img _ scene_listing PI_scene). rewrite HWRLO, HWRHI in Hgot. exact Hgot. }
rewrite (F3 a Himg Ho He (fp_spares_closed [] a sink_closed_nil)).
exact (HR a Hro Ho He).
Qed.

Lemma s4h_garr8_moved : forall (W W' : world SEGS) (m m' : word -> option byte) a l,
(forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W') m' (a + j) = aview SEGS (w_H W) m (a + j)) ->
garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W') m') a l.
Proof.
intros W W' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
apply (val_mem_moved SEGS (w_H W) (w_H W') m m' (a + Z.of_nat j) (a + Z.of_nat j) 1%nat); [|exact Hv].
intros k Hk1. rewrite <- !Z.add_assoc. apply Hk. lia.
Qed.

Lemma s4h_shadow_lo : forall F, 4096 <= F -> F + 16384 <= 0x7fffff800000 ->
2147450880 <= shadow_addr F /\ shadow_addr F + 2048 <= 17594333462528.
Proof. intros F H1 H2. unfold shadow_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.

Lemma s4h_open_idx : forall F off len i, F mod 8 = 0 -> (F + off) mod 8 = 0 -> 0 <= off -> 0 <= len ->
off + len <= 16384 -> 0 <= i < (len + 7) / 8 ->
shadow_addr F <= shadow_of_addr SHADOW_OFF (F + off) + i < shadow_addr F + 2048.
Proof. intros F off len i H1 H2 H3 H4 H5 H6. unfold shadow_addr, shadow_of_addr. Z.div_mod_to_equations. lia. Qed.

Lemma s4h_chain : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) mem3 md3 ev (regsT : bvmap 5 word),
afn_pre SEGS B (sw_stk WK) (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] ->
c_sp1 cx = 32 * ((spZ (c_regs cx) - 224) / 32) ->
ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(sg_cid IM, c_fpos cx)] ly3 S3 W3 mem3 md3 ev ->
sc_saves SEGS cx W3 mem3 ->
spZ regsT = c_sp1 cx -> s0Z regsT = spZ (c_regs cx) -> 4096 <= raZ regsT ->
chain_pre ly3 (aview SEGS (w_H W3) mem3) regsT (rt_ch cx).
Proof.
intros cx ly3 S3 W3 mem3 md3 ev regsT HPRE HSP1 HJ HSAV Hsp Hs0 Hra4.
pose proof HPRE as (HAR & Hra & Hra0 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & _ & _ & HK1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (HO : c_sp1 cx = spZ (c_regs cx) - 224 \/ c_sp1 cx = spZ (c_regs cx) - 240).
{ revert HSP1 Hal16. clear. intros HSP1 Hal16. rewrite HSP1. Z.div_mod_to_equations. lia. }
assert (HSTK0 : 240 + ASTACK <= sw_stk WK) by exact HSTK.
assert (HASTK : ASTACK = 16384) by reflexivity.
assert (HS0 : rdword (aview SEGS (w_H W3) mem3) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx))).
{ replace (spZ (c_regs cx) - 8) with (spZ (c_regs cx) - 8 - 8 * 0) by lia. exact (HSAV 0 ltac:(lia)). }
assert (HS1 : rdword (aview SEGS (w_H W3) mem3) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ replace (spZ (c_regs cx) - 16) with (spZ (c_regs cx) - 8 - 8 * 1) by lia. exact (HSAV 1 ltac:(lia)). }
unfold rt_ch.
destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hf0 | Hf0].
- eapply (achain_chain_pre ly3 (aview SEGS (w_H W3) mem3) (c_sp1 cx) (spZ (c_regs cx)));
  [| lia | exact Hs0 | exact Hra4].
  eapply (achain_ly_top (c_ly cx) ly3); [exact Etop |].
  eapply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W3) mem3)
    (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] (c_sp1 cx) Hch ltac:(lia)).
  + intros a Ha. apply HK1; lia.
  + exact HS0.
  + exact HS1.
  + exact Hra0.
  + lia.
  + revert Hal16. clear. intros. Z.div_mod_to_equations. lia.
  + lia.
  + lia.
- eapply (achain_chain_pre ly3 (aview SEGS (w_H W3) mem3) (c_sp1 cx) (spZ (c_regs cx)));
  [| lia | exact Hs0 | exact Hra4].
  left. split; [right; left; lia | reflexivity].
Qed.
(* ================================================================================================
   THE ENTRY BLOCK of the whole_transfer arm, asan 0x82d88 .. 0x82dc4 (k = 0x510 .. 0x54c): the two
   spills, the malloc of 8904 bytes, the refuted null test, the init block, and the entry to the loop
   head at k = 0.
   ================================================================================================ *)
Lemma s4_T_entry : forall cx POST ly3 S3 W3 regs3 mem3 md3 bs body bb (regsG : bvmap 5 word) md',
@sc_base rc SEGS B ameter_triv WK cx ->
@cut_C3 rc SK SEGS B ameter_triv WK IM cx ly3 S3 W3 regs3 mem3 md3 bs body bb ->
@sc_j rc SK SEGS B ameter_triv WK IM cx ly3 S3 W3 mem3 md' 1 ->
(forall r : bv 5, r <> 10%bv -> getr regsG r = getr regs3 r) ->
getr regsG 10%bv = Z_to_bv 64 8904 ->
Z.land (bs 0) 2 <> 0 -> sc_nprime IM bs = 8904 ->
@sc_from_T fx rc SK SEGS B ameter_triv WK IM cx POST 0 ->
SRr SEGS W3 (mkCfg (mkst regsG (Z_to_bv 64 (BASE + 1296)) mem3 (seg_rom SEGS)) md') POST.
Proof.
intros cx POST ly3 S3 W3 regs3 mem3 md3 bs body bb regsG mdE HBASE HC3 HJE Hreg Ha0 Hland Hnp HfromT.
(* ---- the entry facts ---- *)
pose proof HBASE as (HBASE0 & HSP1).
pose proof HBASE0 as (HPRE & HraW & Hp10 & Hp11 & Hpn0 & Hfr0 & Hev0 & Hlive0 & HROD0 & HSINK0 & Hfd0 & Hfs0 & HMO0).
pose proof HPRE as (HAR0 & Hra1 & Hra0 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof s4_base_lo as (HB1 & HB2 & HB3 & HB4).
assert (HAS : ASTACK = 16384) by reflexivity.
assert (HMM : MALLOC_MAX = 268435456) by reflexivity.
assert (HLM : LIVE_MAX = 17179869184) by reflexivity.
assert (HEM : EV_MAX = 8192) by reflexivity.
assert (HO : c_sp1 cx = spZ (c_regs cx) - 224 \/ c_sp1 cx = spZ (c_regs cx) - 240).
{ revert HSP1 Hal16. clear. intros HSP1 Hal16. rewrite HSP1. Z.div_mod_to_equations. lia. }
assert (HOmod : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
{ destruct HO as [HOx | HOx]; rewrite HOx;
  [replace (spZ (c_regs cx) - 224 - spZ (c_regs cx)) with (-224) by lia
  |replace (spZ (c_regs cx) - 240 - spZ (c_regs cx)) with (-240) by lia]; reflexivity. }
(* ---- the cut's facts ---- *)
destruct HC3 as (HJ3 & Hab & Hbb & Hblk & Hlen & Hgbody & Hfrm & Hsav & Hshbg & Hshblki & HopB & HopM &
Himg & Hinput & Hnnb & Hmacb & Vsp0 & Vsp1 & VF & VFb & VFsp & VshF & Vblki & Vexp & Vmac & Vshexp &
Vbody & Vnn & Vnp & Vfl & Vst).
clear HJ3.
pose proof HJE as (HJ & Hfrs3 & Hmle).
pose proof Himg as (Hsp3 & Hgp3 & Htp3 & HROD3).
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & Hnev3 & Hk3 & HK1 & HK2 & HK3 & HK4 & _ & HPRES3 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EFly & _ & _ & Etop & Eslo & Eshi & _).
s4geom.
cbv [RV_s0 RV_s1 RV_s2 RV_s3 RV_s4 RV_s5 RV_s6 RV_s7 RV_s8 RV_s9 RV_s10 RV_s11 RV_a1 RV_a5 RV_a6 RV_a7] in *.
unfold w64 in *.
assert (HNN : sc_nn IM bs = 8904) by (unfold sc_nn; rewrite Hnp; reflexivity).
assert (HRS : req_size 8904 = 8904) by reflexivity.
rewrite HNN in Hbb, Hlen, Hnnb, Vnn, Hab, Hblk.
rewrite HRS in Hbb.
pose proof Hblk as (HB4096 & HBzone & HBceil & HB16 & HBwr & HBftok).
rewrite HRS in HBceil.
(* ---- the frame ---- *)
assert (Hown3 : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EF3 : frame_addr ly3 8 (c_fpos cx) = sc_F SEGS IM cx).
{ unfold sc_F, rt_F, frame_addr. cbn [sg_cid scene_geom_asan]. rewrite EFly. reflexivity. }
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 mdE 8 (c_fpos cx) HAR3 Hown3) as (HF4096 & HFceil & HFapp).
pose proof (al_frames _ _ LAWS ly3 S3 W3 mem3 mdE 8 (c_fpos cx) HAR3 Hown3) as (HF32 & _ & _ & _).
assert (HFB : fs_frame_bytes 8 = 16384) by reflexivity.
rewrite EF3 in HF4096, HFceil, HFapp, HF32. rewrite HFB in HFceil.
assert (HF8 : sc_F SEGS IM cx mod 8 = 0).
{ revert HF32. generalize (sc_F SEGS IM cx). clear. intros F HF. Z.div_mod_to_equations. lia. }
pose proof (s4h_shadow_lo (sc_F SEGS IM cx) HF4096 ltac:(lia)) as (HSL1 & HSL2).
(* ---- the stack geometry ---- *)
assert (HCS : alloc_ceiling + ASTACK <= c_sp1 cx) by (destruct HO; lia).
assert (HS96 : c_sp1 cx + 96 <= spZ (c_regs cx) - 104) by (destruct HO; lia).
assert (HSP47 : spZ (c_regs cx) <= 2 ^ 47) by lia.
assert (HPOW : 2 ^ 47 < 2 ^ 64) by (vm_compute; reflexivity).
assert (HSPZ : bv_unsigned (getr regs3 2%bv) = c_sp1 cx) by exact Hsp3.
assert (HBR : 0 <= BASE + 1308 < 2 ^ 64) by lia.
assert (HC64 : 0 <= c_sp1 cx < 2 ^ 64) by lia.
assert (HF64 : 0 <= sc_F SEGS IM cx < 2 ^ 64) by lia.
assert (HF3264 : 0 <= sc_F SEGS IM cx + 32 < 2 ^ 64) by lia.
assert (HSP064 : 0 <= spZ (c_regs cx) < 2 ^ 64) by lia.
(* ================================================================================================
   0x82d88  sd s8,8(s1)    [sp1+8] = n' = 8904
   ================================================================================================ *)
eapply (s4_sd W3 regsG 1296 mem3 mdE POST 0x0184b423 _ _ _ 9%bv 24%bv 8 (c_sp1 cx + 8));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity
| rewrite (Hreg 9%bv ltac:(reg_neq_tac)), Vsp1, (s4_bv_small (c_sp1 cx) ltac:(lia)); reflexivity
| lia | lia
| intros i Hi; eapply s4h_presj; [exact HJ | lia] | ].
intros m1 md1 Hm1 Hw1. replace (1296 + 4) with 1300 by lia.
assert (HJ1 : ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
(c_md cx) [(8, c_fpos cx)] ly3 S3 W3 m1 md1 1)
by (eapply s4h_sdj; [exact HJ | exact Hm1 | exact Hw1 | lia | lia]).
(* ================================================================================================
   0x82d8c  sd s7,0x10(s1)   [sp1+0x10] = F
   ================================================================================================ *)
eapply (s4_sd W3 regsG 1300 m1 md1 POST 0x0174b823 _ _ _ 9%bv 23%bv 16 (c_sp1 cx + 16));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity
| rewrite (Hreg 9%bv ltac:(reg_neq_tac)), Vsp1, (s4_bv_small (c_sp1 cx) ltac:(lia)); reflexivity
| lia | lia
| intros i Hi; eapply s4h_presj; [exact HJ1 | lia] | ].
intros m2 md2 Hm2 Hw2. replace (1300 + 4) with 1304 by lia.
assert (HJ2 : ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
(c_md cx) [(8, c_fpos cx)] ly3 S3 W3 m2 md2 1)
by (eapply s4h_sdj; [exact HJ1 | exact Hm2 | exact Hw2 | lia | lia]).
(* the two stored words, and the saves, at m2 *)
assert (Vn1 : rdword (aview SEGS (w_H W3) m2) (c_sp1 cx + 8) = Some 8904).
{ eapply (s4_wr_word W3 m1 m2 _ _ _ _ Hw2); [lia | lia | lia |].
  pose proof (proj2 (proj2 (proj2 Hw1))) as Hv.
  rewrite (Hreg 24%bv ltac:(reg_neq_tac)), Vnp, Hnp, (s4_bv_small 8904 ltac:(lia)) in Hv. exact Hv. }
assert (VFm : rdword (aview SEGS (w_H W3) m2) (c_sp1 cx + 16) = Some (sc_F SEGS IM cx)).
{ pose proof (proj2 (proj2 (proj2 Hw2))) as Hv.
  rewrite (Hreg 23%bv ltac:(reg_neq_tac)), VF, (s4_bv_small (sc_F SEGS IM cx) ltac:(lia)) in Hv. exact Hv. }
assert (HSAV2 : sc_saves SEGS cx W3 m2).
{ intros j Hj. eapply (s4_wr_word W3 m1 m2 _ _ _ _ Hw2); [lia | lia | lia |].
  eapply (s4_wr_word W3 mem3 m1 _ _ _ _ Hw1); [lia | lia | lia |]. exact (Hsav j Hj). }
(* ================================================================================================
   0x82d90  jal __wrap_malloc, a0 = 8904
   ================================================================================================ *)
eapply (s4_call W3 regsG 1304 m2 md2 POST SS___interceptor_trampoline_malloc 1%bv);
[vm_compute; reflexivity | ].
intros md4 Hm4. replace (1304 + 4) with 1308 by lia.
assert (HJ2' : ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
(c_md cx) [(8, c_fpos cx)] ly3 S3 W3 m2 md4 1) by (eapply s4h_matj; [exact HJ2 | exact Hm4]).
rewrite (pal_malloc B TL).
pose proof (amalloc04_rule_triv SEGS B pa_segs_low (pal_env B TL) LAWS ML AMALLOC) as MALLOC4.
eapply SRr_bind.
{ eapply (MALLOC4 W3 (regupd regsG 1%bv (Z_to_bv 64 (BASE + 1308))) m2
    (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(8, c_fpos cx)] ly3 S3 md4 1 8904 (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + 1308)) (rt_ch cx)).
  - exact HJ2'.
  - rewrite getr_other by reg_neq_tac. exact Ha0.
  - lia.
  - lia.
  - unfold spZ. rewrite getr_other by reg_neq_tac. rewrite (Hreg 2%bv ltac:(reg_neq_tac)).
    unfold spZ in Hsp3. rewrite Hsp3. lia.
  - exact HOmod.
  - destruct HO; lia.
  - destruct HO; lia.
  - rewrite getr_other by reg_neq_tac. rewrite (Hreg 3%bv ltac:(reg_neq_tac)). exact Hgp3.
  - rewrite getr_other by reg_neq_tac. rewrite (Hreg 4%bv ltac:(reg_neq_tac)). exact Htp3.
  - rewrite getr_same by reg_neq_tac. reflexivity.
  - apply s4_ret; [lia | reflexivity].
  - lia.
  - eapply (s4h_chain cx ly3 S3 W3 m2 md4 1); [exact HPRE | exact HSP1 | exact HJ2' | exact HSAV2 | | |].
    + unfold spZ. rewrite getr_other by reg_neq_tac. rewrite (Hreg 2%bv ltac:(reg_neq_tac)).
      unfold spZ in Hsp3. exact Hsp3.
    + unfold s0Z. rewrite getr_other by reg_neq_tac. rewrite (Hreg 8%bv ltac:(reg_neq_tac)), Vsp0.
      apply s4_bv_small. lia.
    + unfold raZ. rewrite getr_same by reg_neq_tac. rewrite (s4_bv_small (BASE + 1308) HBR). lia.
  - apply (HTRACE (pc_malloc_ra0 (as_code B)) (BASE + 1308)
      (regupd regsG 1%bv (Z_to_bv 64 (BASE + 1308))) cx HraW
      ltac:(unfold raZ; rewrite getr_same by reg_neq_tac; exact (s4_bv_small (BASE + 1308) HBR))).
    left. split; [reflexivity|]. right. left. lia.
  - exact I. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md5 & res & -> & HJ5 & HP2 & Hr10 & Hfrs2 & Hres & Hab2 & KPT & _).
unfold w64 in *.
pose proof KPT as (KT1 & KT2 & KT3 & KT4 & KT5 & KT6).
assert (HAR2 : AR SEGS B ly2 S2 W2 mem2 md5) by exact (proj1 HJ5).
assert (HinR : In (res, 8904) (ablocks B ly2 S2))
by (rewrite Hab2; apply in_or_app; right; left; reflexivity).
assert (HinB3 : In (body, 8904) (ablocks B ly3 S3))
by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (HinB2 : In (body, 8904) (ablocks B ly2 S2))
by (rewrite Hab2; apply in_or_app; left; exact HinB3).
pose proof (al_blocks _ _ LAWS ly2 S2 W2 mem2 md5 res 8904 HAR2 HinR)
as (HR16 & HR4096 & HRceil & HRapp & HRpres & _ & HRn).
rewrite HRS in HRceil, HRapp, HRpres.
(* the registers the callee kept *)
assert (HPr : forall (n : Z) (r : bv 5), acallee_saved n -> bv_unsigned r = n -> getr regs2 r = getr regs3 r).
{ intros n r Hn Hr. pose proof (HP2 n Hn) as HQ.
  replace (Z_to_bv 5 n) with r in HQ by (apply bv_eq; rewrite Z_to_bv_unsigned, Hr;
    unfold bv_wrap; rewrite Z.mod_small; [reflexivity | rewrite <- Hr; apply bv_unsigned_in_range]).
  rewrite HQ, getr_other, (Hreg r); [reflexivity | |].
  - intros Hc. rewrite Hc in Hr. cbv in Hr. cbv [acallee_saved] in Hn. lia.
  - intros Hc. rewrite Hc in Hr. cbv in Hr. cbv [acallee_saved] in Hn. lia. }
assert (R2 : getr regs2 2%bv = Z_to_bv 64 (c_sp1 cx)).
{ rewrite (HPr 2 2%bv ltac:(cbv [acallee_saved]; lia) eq_refl).
  apply bv_eq. rewrite (s4_bv_small (c_sp1 cx) HC64). exact Hsp3. }
assert (R3 : getr regs2 3%bv = Z_to_bv 64 (as_gp B))
by (rewrite (HPr 3 3%bv ltac:(cbv [acallee_saved]; lia) eq_refl); exact Hgp3).
assert (R4 : getr regs2 4%bv = Z_to_bv 64 (as_tp B))
by (rewrite (HPr 4 4%bv ltac:(cbv [acallee_saved]; lia) eq_refl); exact Htp3).
assert (R8 : getr regs2 8%bv = Z_to_bv 64 (spZ (c_regs cx)))
by (rewrite (HPr 8 8%bv ltac:(cbv [acallee_saved]; lia) eq_refl); exact Vsp0).
assert (R9 : getr regs2 9%bv = Z_to_bv 64 (c_sp1 cx))
by (rewrite (HPr 9 9%bv ltac:(cbv [acallee_saved]; lia) eq_refl); exact Vsp1).
assert (R19 : getr regs2 19%bv = Z_to_bv 64 (shadow_addr (sc_F SEGS IM cx)))
by (rewrite (HPr 19 19%bv ltac:(cbv [acallee_saved]; lia) eq_refl); exact VshF).
assert (R25 : getr regs2 25%bv = Z_to_bv 64 (sc_F SEGS IM cx + 32))
by (rewrite (HPr 25 25%bv ltac:(cbv [acallee_saved]; lia) eq_refl); exact Vblki).
(* ================================================================================================
   0x82d94  sd a0,0x50(s1)   [sp1+0x50] = again
   ================================================================================================ *)
eapply (s4_sd W2 regs2 1308 mem2 md5 POST 0x04a4b823 _ _ _ 9%bv 10%bv 80 (c_sp1 cx + 80));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity
| rewrite R9, (s4_bv_small (c_sp1 cx) HC64); reflexivity
| lia | lia
| intros i Hi; eapply s4h_presj; [exact HJ5 | lia] | ].
intros m4 md6 Hm6 Hw3. replace (1308 + 4) with 1312 by lia.
assert (HJ6 : ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
(c_md cx) [(8, c_fpos cx)] ly2 S2 W2 m4 md6 2)
by (eapply s4h_sdj; [exact HJ5 | exact Hm6 | exact Hw3 | lia | lia]).
assert (Vagain : rdword (aview SEGS (w_H W2) m4) (c_sp1 cx + 80) = Some res).
{ pose proof (proj2 (proj2 (proj2 Hw3))) as Hv. rewrite Hr10, (s4_bv_small res ltac:(lia)) in Hv. exact Hv. }
(* ================================================================================================
   0x82d98  beqz a0, +0x3ac   (the null arm, refuted by 4096 <= res)
   ================================================================================================ *)
eapply (s4_branch_off W2 regs2 1312 m4 md6 POST 0x3a050663 BC_EQ _ _ _ 10%bv 0%bv 940);
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | | ].
- intros Hb md7 Hm7. exfalso.
  rewrite getr_zero, (branch_eq_lit _ 0 ltac:(lia)), Hr10, (s4_bv_small res ltac:(lia)) in Hb.
  apply Z.eqb_eq in Hb. lia.
- intros Hb md7 Hm7. clear Hb. replace (1312 + 4) with 1316 by lia.
(* ================================================================================================
   0x82d9c  mv s4,zero     got = 0
   ================================================================================================ *)
eapply (s4_mv W2 regs2 1316 m4 md7 POST 0x00000a13 _ _ _ 20%bv 0%bv 0 (Z_to_bv 64 0));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| unfold v_addi; rewrite getr_zero; apply bv_eq; vm_compute; reflexivity | ].
intros md8 Hm8. replace (1316 + 4) with 1320 by lia.
(* ================================================================================================
   0x82da0  mv s6,zero     k = 0
   ================================================================================================ *)
eapply (s4_mv W2 _ 1320 m4 md8 POST 0x00000b13 _ _ _ 22%bv 0%bv 0 (Z_to_bv 64 0));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| unfold v_addi; rewrite getr_zero; apply bv_eq; vm_compute; reflexivity | ].
intros md9 Hm9. replace (1320 + 4) with 1324 by lia.
assert (HJ9 : ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
(c_md cx) [(8, c_fpos cx)] ly2 S2 W2 m4 md9 2)
by (eapply s4h_matj; [eapply s4h_matj; [eapply s4h_matj; [exact HJ6 | exact Hm7] | exact Hm8] | exact Hm9]).
(* ================================================================================================
   0x82da4  sd zero,0x40(s1)   declared = 0
   ================================================================================================ *)
eapply (s4_sd W2 _ 1324 m4 md9 POST 0x0404b023 _ _ _ 9%bv 0%bv 64 (c_sp1 cx + 64));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity
| s4hrg; rewrite R9, (s4_bv_small (c_sp1 cx) HC64); reflexivity
| lia | lia
| intros i Hi; eapply s4h_presj; [exact HJ9 | lia] | ].
intros m5 md10 Hm10 Hw4. replace (1324 + 4) with 1328 by lia.
assert (HJ10 : ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
(c_md cx) [(8, c_fpos cx)] ly2 S2 W2 m5 md10 2)
by (eapply s4h_sdj; [exact HJ9 | exact Hm10 | exact Hw4 | lia | lia]).
assert (Vdecl : rdword (aview SEGS (w_H W2) m5) (c_sp1 cx + 64) = Some 0).
{ pose proof (proj2 (proj2 (proj2 Hw4))) as Hv. rewrite getr_zero in Hv.
  rewrite (s4_bv_small 0 ltac:(lia)) in Hv. exact Hv. }
(* ================================================================================================
   0x82da8  addi a0,s9,7    a0 = blk.i + 7
   ================================================================================================ *)
eapply (s4_mv W2 _ 1328 m5 md10 POST 0x007c8513 _ _ _ 10%bv 25%bv 7 (Z_to_bv 64 (sc_F SEGS IM cx + 39)));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| unfold v_addi; s4hrg; rewrite R25, (s4_bv_small (sc_F SEGS IM cx + 32) HF3264); f_equal; lia | ].
intros md11 Hm11. replace (1328 + 4) with 1332 by lia.
(* ================================================================================================
   0x82dac  sd a0,0x48(s1)   [sp1+0x48] = blk.i + 7
   ================================================================================================ *)
eapply (s4_sd W2 _ 1332 m5 md11 POST 0x04a4b423 _ _ _ 9%bv 10%bv 72 (c_sp1 cx + 72));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity
| s4hrg; rewrite R9, (s4_bv_small (c_sp1 cx) HC64); reflexivity
| lia | lia
| intros i Hi; eapply s4h_presj; [eapply s4h_matj; [exact HJ10 | exact Hm11] | lia] | ].
intros m6 md12 Hm12 Hw5. replace (1332 + 4) with 1336 by lia.
assert (HJ12 : ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
(c_md cx) [(8, c_fpos cx)] ly2 S2 W2 m6 md12 2)
by (eapply s4h_sdj; [eapply s4h_matj; [exact HJ10 | exact Hm11] | exact Hm12 | exact Hw5 | lia | lia]).
assert (VsrcA : rdword (aview SEGS (w_H W2) m6) (c_sp1 cx + 72) = Some (sc_F SEGS IM cx + 39)).
{ pose proof (proj2 (proj2 (proj2 Hw5))) as Hv.
  rewrite getr_same in Hv by reg_neq_tac.
  rewrite (s4_bv_small (sc_F SEGS IM cx + 39) ltac:(lia)) in Hv. exact Hv. }
(* ================================================================================================
   0x82db0  addi s7,s9,9    s7 = blk.i + 9
   ================================================================================================ *)
eapply (s4_mv W2 _ 1336 m6 md12 POST 0x009c8b93 _ _ _ 23%bv 25%bv 9 (Z_to_bv 64 (sc_F SEGS IM cx + 41)));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| unfold v_addi; s4hrg; rewrite R25, (s4_bv_small (sc_F SEGS IM cx + 32) HF3264); f_equal; lia | ].
intros md13 Hm13. replace (1336 + 4) with 1340 by lia.
(* ================================================================================================
   0x82db4  lui a0,2
   ================================================================================================ *)
eapply (s4_lui W2 _ 1340 m6 md13 POST 0x00002537 _ _ 10%bv 8192 (Z_to_bv 64 8192));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity | ].
intros md14 Hm14. replace (1340 + 4) with 1344 by lia.
(* ================================================================================================
   0x82db8  addi s5,zero,-8    the poison byte
   ================================================================================================ *)
eapply (s4_mv W2 _ 1344 m6 md14 POST 0xff800a93 _ _ _ 21%bv 0%bv (-8) (Z_to_bv 64 (2 ^ 64 - 8)));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| unfold v_addi; rewrite getr_zero; apply bv_eq; vm_compute; reflexivity | ].
intros md15 Hm15. replace (1344 + 4) with 1348 by lia.
(* ================================================================================================
   0x82dbc  addiw s11,a0,0x2c8    s11 = 8904
   ================================================================================================ *)
eapply (s4_opimm32 W2 _ 1348 m6 md15 POST 0x2c850d9b _ _ _ 27%bv 10%bv 712 (Z_to_bv 64 8904));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| s4hrg; rewrite getr_same by reg_neq_tac; apply bv_eq; vm_compute; reflexivity | ].
intros md16 Hm16. replace (1348 + 4) with 1352 by lia.
(* ================================================================================================
   0x82dc0  addiw s2,a0,0x2c9    s2 = 8905
   ================================================================================================ *)
eapply (s4_opimm32 W2 _ 1352 m6 md16 POST 0x2c95091b _ _ _ 18%bv 10%bv 713 (Z_to_bv 64 8905));
[vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| s4hrg; rewrite getr_same by reg_neq_tac; apply bv_eq; vm_compute; reflexivity | ].
intros md17 Hm17. replace (1352 + 4) with 1356 by lia.
assert (HJF : ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
(c_md cx) [(8, c_fpos cx)] ly2 S2 W2 m6 md17 2)
by (eapply s4h_matj; [eapply s4h_matj; [eapply s4h_matj; [eapply s4h_matj;
   [eapply s4h_matj; [exact HJ12 | exact Hm13] | exact Hm14] | exact Hm15] | exact Hm16] | exact Hm17]).
(* ================================================================================================
   THE MEMORY TRANSPORTS from the C3 state (W3, mem3) to the loop head's (W2, m6).
   ================================================================================================ *)
assert (KPRE : forall a, 0 <= a < 2 ^ 64 -> (a < c_sp1 cx + 8 \/ c_sp1 cx + 24 <= a) ->
aview SEGS (w_H W3) m2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn.
  assert (D2 : a < c_sp1 cx + 16 \/ c_sp1 cx + 16 + 8 <= a) by lia.
  assert (D1 : a < c_sp1 cx + 8 \/ c_sp1 cx + 8 + 8 <= a) by lia.
  rewrite (s4_wr_view W3 m1 m2 _ _ a Hw2 Ha D2). exact (s4_wr_view W3 mem3 m1 _ _ a Hw1 Ha D1). }
assert (KPOST : forall a, 0 <= a < 2 ^ 64 -> (a < c_sp1 cx + 64 \/ c_sp1 cx + 88 <= a) ->
aview SEGS (w_H W2) m6 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn.
  assert (D5 : a < c_sp1 cx + 72 \/ c_sp1 cx + 72 + 8 <= a) by lia.
  assert (D4 : a < c_sp1 cx + 64 \/ c_sp1 cx + 64 + 8 <= a) by lia.
  assert (D3 : a < c_sp1 cx + 80 \/ c_sp1 cx + 80 + 8 <= a) by lia.
  rewrite (s4_wr_view W2 m5 m6 _ _ a Hw5 Ha D5), (s4_wr_view W2 m4 m5 _ _ a Hw4 Ha D4).
  exact (s4_wr_view W2 mem2 m4 _ _ a Hw3 Ha D3). }
assert (KT1' : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (c_sp1 cx - ASTACK <= a < c_sp1 cx) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) m2 a).
{ intros a Ha Hn. apply (KT1 a Ha). intros Hc. apply Hn. lia. }
(* the two blocks and the frame are apart *)
assert (EF2 : frame_addr ly2 8 (c_fpos cx) = sc_F SEGS IM cx).
{ pose proof HJ5 as (_ & Hly2 & _). pose proof Hly2 as (_ & _ & _ & _ & _ & EF2x & _).
  unfold sc_F, rt_F, frame_addr. cbn [sg_cid scene_geom_asan]. rewrite EF2x. reflexivity. }
assert (Hown2 : In (8, c_fpos cx) (frames S2)) by (rewrite Hfrs2; exact Hown3).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md5 res 8904 8 (c_fpos cx) HAR2 HinR Hown2) as HdF.
unfold zdisjoint in HdF. cbn [fst snd] in HdF. rewrite EF2, HFB, HRS in HdF.
assert (Habs : ablocks B ly2 S2 = ablocks B (c_ly cx) (c_S cx) ++ (body, 8904) :: ([] ++ (res, 8904) :: []))
by (rewrite Hab2, Hab, <- app_assoc; reflexivity).
pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 md5 (body, 8904) (res, 8904)
(ablocks B (c_ly cx) (c_S cx)) [] [] HAR2 Habs) as HdB.
unfold zdisjoint, block_rng in HdB. cbn [fst snd] in HdB. rewrite HRS in HdB.
assert (HRoff : off_img res 8904).
{ pose proof (blk_off_imgP B ly2 S2 W2 mem2 md5 res 8904 HAR2 HinR) as Hz. rewrite HRS in Hz. exact Hz. }
assert (HRzone : zone2 res 8904).
{ split; [exact HRoff|]. destruct HRapp as (_ & Hq). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hq. lia. }
assert (KT4' : forall a, (sc_F SEGS IM cx <= a < sc_F SEGS IM cx + 16384 \/
shadow_addr (sc_F SEGS IM cx) <= a < shadow_addr (sc_F SEGS IM cx) + 2048) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) m2 a).
{ intros a Ha. apply (KT4 8 (c_fpos cx) a Hown3).
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF3, HFB. change (16384 / 8) with 2048. exact Ha.
  - intros Hc. cbv beta in Hc. rewrite HRS in Hc. destruct (zone2_band _ _ HRzone) as [Hz | Hz]; lia. }
assert (KT2' : forall i, 0 <= i < 8904 ->
aview SEGS (w_H W2) mem2 (body + i) = aview SEGS (w_H W3) m2 (body + i)).
{ intros i Hi. apply (KT2 body 8904 i HinB3); [rewrite HRS; lia|].
  intros Hc. cbv beta in Hc. rewrite HRS in Hc. lia. }
(* the three combined transports *)
assert (KFR : forall a, (sc_F SEGS IM cx <= a < sc_F SEGS IM cx + 16384 \/
shadow_addr (sc_F SEGS IM cx) <= a < shadow_addr (sc_F SEGS IM cx) + 2048) ->
aview SEGS (w_H W2) m6 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. assert (Hb : 0 <= a < 2 ^ 64) by lia.
  assert (H2 : a < c_sp1 cx + 64 \/ c_sp1 cx + 88 <= a) by lia.
  assert (H1 : a < c_sp1 cx + 8 \/ c_sp1 cx + 24 <= a) by lia.
  rewrite (KPOST a Hb H2), (KT4' a Ha). exact (KPRE a Hb H1). }
assert (KBOD : forall i, 0 <= i < 8904 ->
aview SEGS (w_H W2) m6 (body + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. assert (Hb : 0 <= body + i < 2 ^ 64) by lia.
  assert (H2 : body + i < c_sp1 cx + 64 \/ c_sp1 cx + 88 <= body + i) by lia.
  assert (H1 : body + i < c_sp1 cx + 8 \/ c_sp1 cx + 24 <= body + i) by lia.
  rewrite (KPOST _ Hb H2), (KT2' i Hi). exact (KPRE _ Hb H1). }
assert (KHI : forall a, c_sp1 cx <= a -> a < spZ (c_regs cx) ->
(a < c_sp1 cx + 8 \/ c_sp1 cx + 24 <= a) -> (a < c_sp1 cx + 64 \/ c_sp1 cx + 88 <= a) ->
aview SEGS (w_H W2) m6 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha1 Ha2 H1 H2. assert (Hb : 0 <= a < 2 ^ 64) by lia.
  assert (Hc : alloc_ceiling <= a < 2 ^ 64) by lia.
  assert (Hn : ~ (c_sp1 cx - ASTACK <= a < c_sp1 cx)) by lia.
  rewrite (KPOST a Hb H2), (KT1' a Hc Hn). exact (KPRE a Hb H1). }
assert (RDK : forall a v, c_sp1 cx <= a -> a + 8 <= spZ (c_regs cx) ->
(a + 8 <= c_sp1 cx + 8 \/ c_sp1 cx + 24 <= a) -> (a + 8 <= c_sp1 cx + 64 \/ c_sp1 cx + 88 <= a) ->
rdword (aview SEGS (w_H W3) mem3) a = Some v -> rdword (aview SEGS (w_H W2) m6) a = Some v).
{ intros a v Ha1 Ha2 H1 H2 Hr.
  rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) m6) a); [exact Hr|].
  intros kk Hkk. apply KHI; lia. }
assert (RDM : forall a v, c_sp1 cx <= a -> a + 8 <= spZ (c_regs cx) ->
(a + 8 <= c_sp1 cx + 64 \/ c_sp1 cx + 88 <= a) ->
rdword (aview SEGS (w_H W3) m2) a = Some v -> rdword (aview SEGS (w_H W2) m6) a = Some v).
{ intros a v Ha1 Ha2 H2 Hr.
  rewrite (rdword_ext (aview SEGS (w_H W3) m2) (aview SEGS (w_H W2) m6) a); [exact Hr|].
  intros kk Hkk. assert (Hb : 0 <= a + kk < 2 ^ 64) by lia.
  assert (G2 : a + kk < c_sp1 cx + 64 \/ c_sp1 cx + 88 <= a + kk) by lia.
  assert (Hc : alloc_ceiling <= a + kk < 2 ^ 64) by lia.
  assert (Hn : ~ (c_sp1 cx - ASTACK <= a + kk < c_sp1 cx)) by lia.
  rewrite (KPOST _ Hb G2). exact (KT1' _ Hc Hn). }
assert (RDF : forall a v, sc_F SEGS IM cx <= a -> a + 8 <= sc_F SEGS IM cx + 16384 ->
rdword (aview SEGS (w_H W3) mem3) a = Some v -> rdword (aview SEGS (w_H W2) m6) a = Some v).
{ intros a v Ha1 Ha2 Hr.
  rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) m6) a); [exact Hr|].
  intros kk Hkk. apply KFR. left. lia. }
(* the three slots this block wrote, at the loop head *)
assert (Vagain6 : rdword (aview SEGS (w_H W2) m6) (c_sp1 cx + 80) = Some res).
{ eapply (s4_wr_word W2 m5 m6 _ _ _ _ Hw5); [lia | lia | lia |].
  eapply (s4_wr_word W2 m4 m5 _ _ _ _ Hw4); [lia | lia | lia |]. exact Vagain. }
assert (Vdecl6 : rdword (aview SEGS (w_H W2) m6) (c_sp1 cx + 64) = Some 0).
{ eapply (s4_wr_word W2 m5 m6 _ _ _ _ Hw5); [lia | lia | lia |]. exact Vdecl. }
(* presence at the loop head *)
pose proof (al_blocks _ _ LAWS ly2 S2 W2 m6 md17 res 8904 (proj1 HJF) HinR)
as (_ & _ & _ & _ & HRpres6 & _ & _).
rewrite HRS in HRpres6.
pose proof (al_frames _ _ LAWS ly2 S2 W2 m6 md17 8 (c_fpos cx) (proj1 HJF) Hown2) as (_ & _ & HFb6 & HFsh6).
rewrite EF2, HFB in HFb6, HFsh6.
(* the new block is fresh, so every byte of it is writable and its token is vacuous *)
assert (HAftok : aftok [] (ablocks B (c_ly cx) (c_S cx)) (res, 8904))
by (eapply (aftok_new_block SEGS B LAWS); [exact HJ2' | exact HAR2 | exact Hab2 | lia]).
assert (HnotIn : ~ In (res, 8904) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hin. apply (inFP_nil (res + 0)). apply (HAftok Hin 0). cbn [snd]. rewrite HRS. lia. }
(* the shadow and frame-object transports *)
assert (SHR : forall lo hi vv, 0 <= lo -> hi <= 2048 ->
sc_shr SEGS IM cx W3 mem3 lo hi vv -> sc_shr SEGS IM cx W2 m6 lo hi vv).
{ intros lo hi vv Hlo Hhi Hsh o Ho.
  assert (Hin : sc_F SEGS IM cx <= shadow_addr (sc_F SEGS IM cx) + o < sc_F SEGS IM cx + 16384 \/
  shadow_addr (sc_F SEGS IM cx) <= shadow_addr (sc_F SEGS IM cx) + o
  < shadow_addr (sc_F SEGS IM cx) + 2048) by (right; lia).
  rewrite (KFR _ Hin). exact (Hsh o Ho). }
assert (OPEN : forall off len, 0 <= off -> 0 <= len -> off + len <= 16384 ->
sc_open SEGS IM cx W3 mem3 off len -> sc_open SEGS IM cx W2 m6 off len).
{ intros off len Ho Hl Hol (Hp & Hn & Hc). split; [exact Hp|]. split; [exact Hn|].
  intros i Hi.
  assert (Hin : sc_F SEGS IM cx <= shadow_of_addr SHADOW_OFF (sc_F SEGS IM cx + off) + i
  < sc_F SEGS IM cx + 16384 \/
  shadow_addr (sc_F SEGS IM cx) <= shadow_of_addr SHADOW_OFF (sc_F SEGS IM cx + off) + i
  < shadow_addr (sc_F SEGS IM cx) + 2048)
  by (right; exact (s4h_open_idx (sc_F SEGS IM cx) off len i HF8 Hp Ho Hl Hol Hi)).
  rewrite (KFR _ Hin). exact (Hc i Hi). }
(* ================================================================================================
   THE CUT at the loop head, k = 0.
   ================================================================================================ *)
replace (Z_to_bv 64 (BASE + 1356)) with (Z_to_bv 64 (sg_pc_t IM))
by (cbn [sg_pc_t scene_geom_asan]; unfold SEG_T_off, AF_LLVMFuzzerTestOneInput; f_equal; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R _ ?M _) ?MD) _ =>
change (SRr SEGS W2 (cfg_at SEGS (sg_pc_t IM) R M MD) POST);
apply (HfromT ly2 S2 W2 R M MD bs body res bb) end.
unfold cut_T. s4geom.
split; [lia|].
split; [split; [exact Hland | rewrite Hnp; reflexivity]|].
split; [split; [exact HJF | split; [rewrite Hfrs2; exact Hfrs3 | exact I]]|].
split; [rewrite Hab2, Hab; reflexivity|].
split.
{ rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B (c_ly cx) (c_S cx)), Hab2, Hab, !bsum_app.
  cbn [bsum fold_right snd]. rewrite HRS. lia. }
split; [exact Hblk|].
split.
{ unfold sc_blk_ok. split; [lia|]. split; [rewrite HRS; exact HRzone|].
  split; [rewrite HRS; lia|]. split; [exact HR16|]. split.
  - intros blc lyq ownq i Hin Hi. right. right. left. exists res, 8904.
    split; [exact Hin|]. split; [exact HnotIn|]. rewrite HRS in Hi |- *. lia.
  - exact HAftok. }
split; [lia|].
split; [exact Hlen|].
split.
{ apply (s4h_garr8_moved W3 W2 mem3 m6 body (u8s bb)); [| exact Hgbody].
  intros j Hj. unfold u8s in Hj. rewrite length_map, Hlen in Hj. apply KBOD. lia. }
split.
{ rewrite scT_off_0. cbn [Z.to_nat firstn app].
  destruct (s4_block_bytes W2 m6 res 8904 ltac:(lia) ltac:(intros a Ha; exact (proj1 (HRpres6 a Ha))))
  as (l & Hl & Hg).
  exists l. split; [lia | exact Hg]. }
split.
{ pose proof Hfrm as (Hflag & _ & _). cbn [sg_cid scene_geom_asan] in Hflag. rewrite HFB in Hflag.
  unfold sc_frame. cbn [sg_cid scene_geom_asan]. rewrite HFB. change (16384 / 8) with 2048.
  split; [apply RDF; [lia | lia | exact Hflag]|].
  split; [intros a Ha; exact (proj1 (HFb6 a Ha))|].
  intros a Ha.
  assert (Hi : 0 <= a - shadow_addr (sc_F SEGS IM cx) < 16384 / 8)
  by (change (16384 / 8) with 2048; lia).
  pose proof (proj1 (HFsh6 _ Hi)) as Hq.
  replace (shadow_addr (sc_F SEGS IM cx) + (a - shadow_addr (sc_F SEGS IM cx))) with a in Hq by lia.
  exact Hq. }
split; [intros j Hj; apply RDK; [lia | lia | lia | lia | exact (Hsav j Hj)]|].
split.
{ unfold sc_shbg in Hshbg |- *. rewrite Forall_forall in Hshbg |- *. intros t Ht.
  pose proof (Hshbg t Ht) as Ht'. cbn [sg_sh_bg scene_geom_asan In] in Ht.
  apply SHR; [| | exact Ht'];
  repeat (destruct Ht as [<- | Ht]; [cbn [fst snd]; lia |]); destruct Ht. }
split; [apply SHR; [lia | lia | exact Hshblki]|].
split; [apply OPEN; [lia | lia | lia | exact HopB]|].
split; [apply OPEN; [lia | lia | lia | exact HopM]|].
split.
{ split; [unfold spZ; s4hrg; rewrite R2; exact (s4_bv_small (c_sp1 cx) HC64)|].
  split; [s4hrg; exact R3|]. split; [s4hrg; exact R4|].
  eapply s4h_arodata; [exact HJF | exact HROD0]. }
split; [exact Hinput|].
split.
{ apply (s4h_garr8_moved W3 W2 mem3 m6 _ (sc_macb bs)); [| exact Hmacb].
  intros j Hj. unfold sc_macb in Hj. cbn [length] in Hj. apply KFR. left. lia. }
split; [s4hrg; exact R8|].
split; [s4hrg; exact R9|].
split; [apply RDM; [lia | lia | lia | exact VFm]|].
split; [s4hrg; exact R19|].
split; [s4hrg; exact R25|].
split; [replace (sc_F SEGS IM cx + 32 + 7) with (sc_F SEGS IM cx + 39) by lia; exact VsrcA|].
split; [s4hrg; rewrite getr_same by reg_neq_tac; f_equal; lia|].
split; [apply RDK; [lia | lia | lia | lia | exact Vmac]|].
split; [apply RDK; [lia | lia | lia | lia | exact Vshexp]|].
split; [apply RDK; [lia | lia | lia | lia | exact Vbody]|].
split; [exact Vagain6|].
split; [apply RDM; [lia | lia | lia | exact Vn1]|].
split; [rewrite scT_off_0; s4hrg; rewrite getr_same by reg_neq_tac; reflexivity|].
split; [s4hrg; rewrite getr_same by reg_neq_tac; reflexivity|].
split; [cbn [Z.eqb]; exact Vdecl6|].
split; [s4hrg; rewrite getr_same by reg_neq_tac; reflexivity|].
split; [constructor; [cbn [fst snd vat] | constructor]; rewrite getr_same by reg_neq_tac; reflexivity|].
split; [exact I|].
split; [apply RDK; [lia | lia | lia | lia | exact Vexp]|].
split; [apply RDK; [lia | lia | lia | lia | exact VFsp]|].
split; [rewrite HNN; apply RDK; [lia | lia | lia | lia | exact Vnn]|].
split; [exact I|].
s4hrg. rewrite getr_same by reg_neq_tac. reflexivity.
Qed.


(* ================================================================================================
   S4 = the guard, the malloc block and the loop entry (s4_T_entry), the 343-turn loop closed over
   the S3 hypothesis (s4_loop), and the tail from the loop exit to C5 (s4_TX).
   ================================================================================================ *)
Theorem scene_S4 : @seg_S4_stmt fx rc SK SEGS B ameter_triv WK IM.
Proof.
intros cx POST HBASE HTURN HC5 ly3 S3 W3 regs3 mem3 md3 bs body bb HC3.
assert (HTX : @sc_from_TX fx rc SK SEGS B ameter_triv WK IM cx POST)
by exact (s4_TX cx POST HBASE HC5).
apply (s4_from_C3 cx POST ly3 S3 W3 regs3 mem3 md3 bs body bb HC5); [|exact HC3].
intros regsG md' HJ' Hreg Ha0 Hland Hnp.
exact (s4_T_entry cx POST ly3 S3 W3 regs3 mem3 md3 bs body bb regsG md' HBASE HC3 HJ' Hreg Ha0
Hland Hnp (s4_loop cx POST HTURN HTX 0 ltac:(cbn [sg_nturns scene_geom_asan]; lia))).
Qed.

End S4.
