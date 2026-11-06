(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry seat, the run and the return adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v for libreac/fuzz_grant's reac_grant_alloc_fits; the contract and the value lemmas are new. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) walk of reac_grant_alloc_fits. The entry seat, the run and the return are ported from lib/A/Prog/GrantAllocFits.v at a working branch 5aae1e8a0ce (blob 2aa4587fd27). The contract is lib/B/Prog/GrantBContracts.v's restatement of image A's. The walk is new for image B: image B's code differs from image A's. Image B's 60 bytes at 0x85518 equal image U's (fuzz_grant.ubsan) 0x152f4 byte for byte, while image A's 0x8483c is 36 bytes with no branch, so this file adds the branch driver (lib/B/Prog/KindOfLink1.v's) and refutes both guards of the trap 0x85550. *)
(* reac_grant_alloc_fits (image B fuzz_grant.asan-ubsan 0x85518, 15 instructions): the walk of the contract
   tb_reac_grant_alloc_fits_spec (lib/B/Prog/GrantBContracts.v).
   Image B's code (bytes read from fuzz_grant.asan-ubsan, unstripped twin 5a5ee7c02b4e):
     0x85518 mv a2,a0            0x85534 addw a1,a2,a1       0x85548 slti a0,a0,48
     0x8551c li a0,0             0x85538 bne a1,a0,0x85550   0x8554c ret
     0x85520 bltz a2,0x8554c     0x8553c sext.w a1,a0        0x85550 unimp
     0x85524 addiw a3,a1,-41     0x85540 addiw a0,a0,-1
     0x85528 li a4,-40           0x85544 bge a0,a1,0x85550
     0x8552c bltu a3,a4,0x8554c
     0x85530 add a0,a2,a1
   It is byte-identical to image U's 0x152f4 (fuzz_grant.ubsan, lib/U/Prog/reac_grant_alloc_fits.v). It is NOT
   code-identical to image A's 0x8483c (fuzz_grant.asan, lib/A/Prog/GrantAllocFits.v): image A's 9 instructions
   have no branch and no trap, so this walk keeps image A's entry and return shape and adds the branch driver.
   The walk splits at the four branches. The two return-0 branches (0x85520 base < 0, 0x8552c width outside
   1..40) end at the `ret`. The two guards of the trap `unimp` 0x85550 (0x85538: the 32-bit sum differs from the
   64-bit sum; 0x85544: sext32 (sum - 1) >= sext32 sum) are refuted: both are reached with 0 <= base and
   1 <= width <= 40, so the premise gives base + width < 2 ^ 31 and each guard is false. The fall-through
   returns slti (sext32 (sum - 1)) 48, which is fits base width. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* lia needs zify's euclidean-division flag true for `mod`; this file sets it so itself, whatever its Require closure leaves.
   Local: a file that Requires this one keeps its own setting. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- the arithmetic of the four branches and of the returned value ---------------------------------------- *)
Lemma gf_bt_ge_Sg : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros E a b. first [reflexivity | cbn [branch_taken]; unfold bv_lts, Sg; reflexivity]. Qed.
Lemma gf_bt_lt_Sg : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. first [reflexivity | cbn [branch_taken]; unfold bv_lts, Sg; reflexivity]. Qed.
Lemma gf_U_atom_mod : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
intros E n v H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, bv_wrap, M64.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Local Ltac zbool :=
repeat match goal with
| H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
| H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
end.
Local Ltac unwrap :=
unfold bv_swrap, bv_wrap, zcanon, M64 in *;
try change (bv_modulus 64) with (2 ^ 64) in *; try change (bv_modulus 32) with (2 ^ 32) in *;
try change (bv_half_modulus 64) with (2 ^ 63) in *; try change (bv_half_modulus 32) with (2 ^ 31) in *.
(* 0x85520 bltz a2 (a2 = a0 = base). *)
Lemma gf_base_t : forall E base, ew E 10 = Z_to_bv 64 base -> int32 base ->
  branch_taken BC_LT (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = true -> base < 0.
Proof.
intros E base H Hb Hc. unfold int32 in Hb.
rewrite gf_bt_lt_Sg, !S_of_U, (gf_U_atom_mod E 10 base H), U_SLit in Hc. zbool. unwrap. lia.
Qed.
Lemma gf_base_f : forall E base, ew E 10 = Z_to_bv 64 base -> int32 base ->
  branch_taken BC_LT (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = false -> 0 <= base.
Proof.
intros E base H Hb Hc. unfold int32 in Hb.
rewrite gf_bt_lt_Sg, !S_of_U, (gf_U_atom_mod E 10 base H), U_SLit in Hc. zbool. unwrap. lia.
Qed.
(* 0x85524 addiw a3,a1,-41; 0x85528 li a4,-40; 0x8552c bltu a3,a4. *)
Lemma gf_width_t : forall E width, ew E 11 = Z_to_bv 64 width -> int32 width ->
  branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 11 0) (SLit (-41)))) (sv_denot E (SLit 18446744073709551576)) = true ->
  ~ (1 <= width <= 40).
Proof.
intros E width H Hw Hc. unfold int32 in Hw.
rewrite branch_ltu_U, (U_SLit E 18446744073709551576), U_of_S, S_SAluw, (gf_U_atom_mod E 11 width H), U_SLit in Hc.
cbn [zalu_raw] in Hc. zbool. unwrap. lia.
Qed.
Lemma gf_width_f : forall E width, ew E 11 = Z_to_bv 64 width -> int32 width ->
  branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 11 0) (SLit (-41)))) (sv_denot E (SLit 18446744073709551576)) = false ->
  1 <= width <= 40.
Proof.
intros E width H Hw Hc. unfold int32 in Hw.
rewrite branch_ltu_U, (U_SLit E 18446744073709551576), U_of_S, S_SAluw, (gf_U_atom_mod E 11 width H), U_SLit in Hc.
cbn [zalu_raw] in Hc. zbool. unwrap. lia.
Qed.
(* The trap guard 0x85538 bne a1,a0 (addw a1 = sext32 (base + width), add a0 = base + width): false. *)
Lemma gf_ne_dead : forall E base width, ew E 10 = Z_to_bv 64 base -> ew E 11 = Z_to_bv 64 width ->
  0 <= base -> 1 <= width <= 40 -> base + width < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SAluw ALU_ADD (SOff 10 0) (SOff 11 0))) (sv_denot E (SAlu ALU_ADD (SOff 10 0) (SOff 11 0))) = true ->
  False.
Proof.
intros E base width H10 H11 Hb Hw Hs Hc.
rewrite branch_ne_U, (U_of_S E (SAluw ALU_ADD (SOff 10 0) (SOff 11 0))), S_SAluw, U_SAlu,
  (U_atom E 10 base H10 ltac:(lia)), (U_atom E 11 width H11 ltac:(lia)) in Hc.
cbn [zalu_raw] in Hc. zbool. unwrap. lia.
Qed.
(* The trap guard 0x85544 bge a0,a1 (a0 = sext32 (sum - 1), a1 = sext32 sum): false. *)
Lemma gf_ge_dead : forall E base width, ew E 10 = Z_to_bv 64 base -> ew E 11 = Z_to_bv 64 width ->
  0 <= base -> 1 <= width <= 40 -> base + width < 2 ^ 31 ->
  branch_taken BC_GE
    (sv_denot E (SAluw ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 11 0)) (SLit (-1))))
    (sv_denot E (SAluw ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 11 0)) (SLit 0))) = true ->
  False.
Proof.
intros E base width H10 H11 Hb Hw Hs Hc.
rewrite gf_bt_ge_Sg, !S_SAluw, U_SAlu, (U_atom E 10 base H10 ltac:(lia)), (U_atom E 11 width H11 ltac:(lia)),
  !U_SLit in Hc.
cbn [zalu_raw] in Hc. zbool. unwrap. lia.
Qed.
(* a0 at the fall-through `ret`: 0x85548 slti a0,a0,48 over a0 = sext32 (base + width - 1). *)
Lemma gf_res : forall E base width, ew E 10 = Z_to_bv 64 base -> ew E 11 = Z_to_bv 64 width ->
  0 <= base -> 1 <= width <= 40 -> base + width < 2 ^ 31 ->
  U E (SAlu ALU_SLT (SAluw ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 11 0)) (SLit (-1))) (SLit 48)) = Z.b2z (fits base width).
Proof.
intros E base width H10 H11 Hb Hw Hs.
rewrite (U_SAlu E ALU_SLT), (U_SLit E 48), U_of_S, S_SAluw, (U_SAlu E ALU_ADD),
  (U_atom E 10 base H10 ltac:(lia)), (U_atom E 11 width H11 ltac:(lia)), U_SLit.
cbn [zalu_raw]. unfold fits.
rewrite (proj2 (Z.leb_le 1 width)), (proj2 (Z.leb_le width 40)), (proj2 (Z.leb_le 0 base)) by lia. cbn [andb].
destruct (Z.leb_spec (base + width) 48); cbn [Z.b2z]; unwrap;
match goal with |- context [if ?c then _ else _] => destruct c eqn:? end; zbool; lia.
Qed.
(* a0 at the two return-0 branches. *)
Lemma gf_zero : forall E base width, base < 0 \/ ~ (1 <= width <= 40) -> U E (SLit 0) = Z.b2z (fits base width).
Proof.
intros E base width H. rewrite U_SLit.
replace (fits base width) with false; [reflexivity|].
unfold fits. destruct (Z.leb_spec 1 width), (Z.leb_spec width 40), (Z.leb_spec 0 base); cbn [andb]; try reflexivity; lia.
Qed.
(* Turn the branch conditions of the path into facts on base and width; close a trap path. *)
Local Ltac gf_facts E E10 E11 Hb Hw Hs :=
repeat match goal with
| H : branch_taken BC_LT (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = true |- _ =>
  apply (gf_base_t E _ E10 Hb) in H
| H : branch_taken BC_LT (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = false |- _ =>
  apply (gf_base_f E _ E10 Hb) in H
| H : branch_taken BC_LTU _ _ = true |- _ => apply (gf_width_t E _ E11 Hw) in H
| H : branch_taken BC_LTU _ _ = false |- _ => apply (gf_width_f E _ E11 Hw) in H
| H : branch_taken BC_NE _ _ = true |- _ =>
  exfalso; exact (gf_ne_dead E _ _ E10 E11 ltac:(lia) ltac:(lia) (Hs ltac:(lia) ltac:(lia)) H)
| H : branch_taken BC_NE _ _ = false |- _ => clear H
| H : branch_taken BC_GE _ _ = true |- _ =>
  exfalso; exact (gf_ge_dead E _ _ E10 E11 ltac:(lia) ltac:(lia) (Hs ltac:(lia) ltac:(lia)) H)
| H : branch_taken BC_GE _ _ = false |- _ => clear H
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
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* The walk's shadow base (GrantBContracts.SB) and the function's entry state on image B's listing. *)
Definition Bx_GF : sv := SLit SB.
Definition Bspan_GF : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ss_gf : sstate := mkSS AF_reac_grant_alloc_fits sr_atoms [] None (mkFacts [] [] []).
Section h.
Variable B : asyms.
Section l.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Lemma gf_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_gf (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_grant_alloc_fits)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx_GF [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem. split; [|constructor].
rewrite restrict_mkst_fx. unfold ss_gf. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.
Lemma gf_walk : tb_reac_grant_alloc_fits_spec B.
Proof.
unfold tb_reac_grant_alloc_fits_spec.
intros ly S W regs mem md ch base width HPRE H10 H11 Hb Hw Hs.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (gf_entry W regs mem) as [HS SHOK].
pose proof (ajournal_init SEGS B STK_reac_grant_alloc_fits [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 base) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 width) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HM : forall x, mem x = mem x) by reflexivity.
clear HE.
unfold cfg_at.
change (w64 (BASE + AF_reac_grant_alloc_fits)) with (Z_to_bv 64 (BASE + AF_reac_grant_alloc_fits)).
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HM : forall x, _ x = mem x |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
pose proof (st_ok_pi_restrict_reg _ E ssx msc (10%bv : bv 5) HS) as R10;
let r10 := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
replace (sr_get (ss_regs ssx) (10%bv : bv 5)) with r10 in R10 by (vm_compute; reflexivity);
prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold tb_reac_grant_alloc_fits_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]|];
split; [rewrite R10, denot_lit_U;
  first [ rewrite (gf_res E base width E10 E11 ltac:(lia) ltac:(lia) (Hs ltac:(lia) ltac:(lia)))
        | rewrite (gf_zero E base width ltac:(lia)) ];
  reflexivity|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [exact HM | apply Permutation_refl]
end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK Bspan_GF; [first [apply awr_ok_nil | awr_ok_tac] |];
upd_mem;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx_GF [] ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bx_GF Bspan_GF (@nil shent) (start K Bx_GF Bspan_GF (@nil shent) ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' Bspan_GF; gf_facts E E10 E11 Hb Hw Hs; go
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end end in
go.
Qed.
End l.
Theorem pb_reac_grant_alloc_fits : walk_reac_grant_alloc_fits B.
Proof. intros HL. exact (gf_walk HL). Qed.
End h.
End f.
End d.
