(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_grant/proofs/lib/A/Prog/KindOfLink1.v. *)
(* kind_of_link1 (fuzz_scene.asan 0x84778, 29 instructions): the contract of the ASan build's code and its walk.
   The function reads no memory and has no frame: it compares a0 with constants and returns Pau's
   KL1 of it (lib/Prog/RcKind.v:6) in a0.
   Ported from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/KindOfLink1.v (at
   d98082bd58b): the module paths and the listing's names changed, and RET takes PL_scene. lib/Prog/GrantModel
   is not imported (fuzz_scene has no GrantModel): the statement uses only RcKind.KL1, and the walk states
   GrantModel's signed64_small (lib/Prog/GrantModel.v:28 of fuzz_grant) here, with the same proof.
   Numbers: fuzz_scene.asan, sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026
   (projects/libreac/fuzz_scene/harness.yaml at c8557374ad2e); symbols from the .symtab of
   unstripped/fuzz_scene/fuzz_scene.asan, whose bytes at 0x84778..0x847ec equal the pinned image's.
   - kind_of_link1 = 0x84778, st_size 116 = 29 instructions (no compressed instruction).
   - LLVMFuzzerTestOneInput = 0x82878 = the listing's base (SceneAddr.v scene_text), so
     AF_kind_of_link1 = 0x84778 - 0x82878 = 0x1f00 (SceneList.v:22; slots SceneList.v:2009-2037).
   - No addi sp in 0x84778..0x847e8 and no call: no frame, so KIND_OF_LINK1_STK = ESTACK.
   - The constants it compares (its 29 words equal those of fuzz_grant.asan's kind_of_link1):
     li a1 127 @0x84778, 129 @0x84780, 128 @0x84788, 129 @0x84790, 1 @0x847a4, 16 @0x847ac,
     130 @0x847bc, 132 @0x847c4, beqz a0 @0x847a0; it returns 7 @0x84798, 10 @0x847b4, 9 @0x847cc,
     2 @0x847d4, 13 @0x847dc, 3 @0x847e4: the cases of KL1, compared signed (bge/blt) on all 64 bits.
     They enter the walk through the listing's PW words, not through the statement.
   - The only caller: reac_ctrl_parse (0x83dd8), jal at 0x842ec, return site 0x842f0. The statement
     takes any return address (afn_pre), so no return site is named. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcKind.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The signed value of a 64-bit word given by its unsigned value. *)
Definition sx64 (v : Z) : Z := if v <? 2 ^ 63 then v else v - 2 ^ 64.
(* fuzz_grant's lib/Prog/GrantModel.v:28, stated here: fuzz_scene has no GrantModel. *)
Lemma signed64_small : forall z, -9223372036854775808 <= z < 9223372036854775808 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
change (bv_modulus 64) with 18446744073709551616. change (bv_half_modulus 64) with 9223372036854775808.
rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.
Lemma bt_ge_Sg : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros E a b. first [reflexivity | cbn [branch_taken]; unfold bv_lts, Sg; reflexivity]. Qed.
Lemma bt_lt_Sg : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. first [reflexivity | cbn [branch_taken]; unfold bv_lts, Sg; reflexivity]. Qed.
Lemma signed_lit64 : forall v, 0 <= v < 2 ^ 64 -> bv_signed (Z_to_bv 64 v) = sx64 v.
Proof.
intros v Hv. unfold sx64. destruct (Z.ltb_spec v (2 ^ 63)) as [Hlt | Hge].
- apply signed64_small. lia.
- replace (Z_to_bv 64 v) with (Z_to_bv 64 (v - 2 ^ 64)); [apply signed64_small; lia|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
replace (v - 2 ^ 64) with (v + (-1) * bv_modulus 64) by (change (bv_modulus 64) with (2 ^ 64); lia).
rewrite Z.mod_add by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity.
Qed.
Lemma Sg_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> Sg E (SOff n 0) = sx64 v.
Proof. intros E n v H Hv. unfold Sg. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. apply signed_lit64. exact Hv. Qed.
Lemma Sg_lit : forall E z, 0 <= z < 2 ^ 63 -> Sg E (SLit z) = z.
Proof. intros E z Hz. unfold Sg. cbn [sv_denot]. apply signed64_small. lia. Qed.
Local Ltac zbool :=
repeat match goal with
| H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
| H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
end.
(* Turn the branch conditions of the path into facts on b, the value in a0. *)
Local Ltac branch_facts E E10 Hb :=
repeat match goal with
| H : branch_taken _ (sv_denot E _) (sv_denot E _) = _ |- _ =>
first [rewrite bt_ge_Sg in H | rewrite bt_lt_Sg in H | rewrite branch_eq_U in H | rewrite branch_ne_U in H];
rewrite ?(Sg_atom E 10 _ E10 Hb), ?(U_atom E 10 _ E10 Hb) in H;
rewrite ?Sg_lit, ?U_lit in H by lia
end.
(* The memory is untouched: each run's frame (no writable window) keeps every byte. *)
Local Ltac upd_mem :=
repeat match goal with
| H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H
| H : mem_grows _ _ |- _ => clear H
end;
lazymatch goal with
| HF : frame_of _ ?rs ?m1 ?m2, HM : forall x, ?m1 x = ?m0 x |- _ =>
let HM' := fresh "HM" in
assert (HM' : forall x, m2 x = m0 x)
by (intros x; transitivity (m1 x); [|exact (HM x)]; apply HF; let rs' := eval vm_compute in rs in change rs with rs';
intros (r & Hr & _); destruct Hr);
clear HM HF; rename HM' into HM
end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: no frame of its own,
   ESTACK for the runtime's use. *)
Definition A_kind_of_link1P : Z := BASE + AF_kind_of_link1.
Definition KIND_OF_LINK1_STK : Z := ESTACK.
(* The run's span: the shadow base is the model's SHADOW_OFF (lib/Reusable/YG0f.v), not an image number. *)
Definition SB_KL1 : Z := SHADOW_OFF.
Definition Bx_KL1 : sv := SLit SB_KL1.
Definition Bspan_KL1 : Z * Z := (SB_KL1, SB_KL1 + 2 ^ 44 - 1).
Definition ss_kl1 : sstate := mkSS AF_kind_of_link1 sr_atoms [] None (mkFacts [] [] []).
Section h.
Variable B : asyms.
Definition tkind_of_link1_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (b : Z) : world SEGS -> config -> Prop :=
apost_base SEGS B KIND_OF_LINK1_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 (KL1 b) /\ ly' = ly /\ S' = S /\ W' = W /\ (forall x, mem' x = mem x) /\
Permutation (ablocks B ly' S') (ablocks B ly S)).
Definition tkind_of_link1_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (b : Z),
afn_pre SEGS B KIND_OF_LINK1_STK ly S W regs mem md ch ->
getr regs 10 = w64 b -> 0 <= b < 2 ^ 64 ->
SRr SEGS W (cfg_at SEGS A_kind_of_link1P regs mem md) (tkind_of_link1_post regs ly S W mem md b).
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_scene) (PI := PI).
Lemma kl1_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_kl1 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_kind_of_link1)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx_KL1 [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem. split; [|constructor].
rewrite restrict_mkst_fx. unfold ss_kl1. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.
Theorem pb_kind_of_link1 : tkind_of_link1_spec.
Proof.
unfold tkind_of_link1_spec.
intros ly S W regs mem md ch b HPRE H10 Hb.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (kl1_entry W regs mem) as [HS SHOK].
pose proof (ajournal_init SEGS B KIND_OF_LINK1_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 b) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HM : forall x, mem x = mem x) by reflexivity.
clear HE.
unfold cfg_at, A_kind_of_link1P. change (w64 (BASE + AF_kind_of_link1)) with (Z_to_bv 64 (BASE + AF_kind_of_link1)).
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HM : forall x, _ x = mem x |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold tkind_of_link1_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]|];
split; [rewrite R10; unfold w64; f_equal; branch_facts E E10 Hb;
unfold KL1, sx64 in *;
repeat match goal with H : context [if ?c then _ else _] |- _ => destruct c eqn:? end;
repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end;
zbool; lia|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [exact HM | apply Permutation_refl]
end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK Bspan_KL1; [first [apply awr_ok_nil | awr_ok_tac] |];
upd_mem;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx_KL1 [] ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bx_KL1 Bspan_KL1 (@nil shent) (start K Bx_KL1 Bspan_KL1 (@nil shent) ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' Bspan_KL1; [go | go]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end end in
go.
Qed.
End h.
End f.
End d.
