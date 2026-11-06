(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry seat, the run and the return adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v for libreac/fuzz_grant's reac_grant_alloc_fits; the contract and the value lemmas are new. *)
(* reac_grant_alloc_fits (fuzz_grant.asan 0x8483c, 9 instructions): the contract of the
   ASan build's code and its walk. The function reads no memory and has no frame: it
   returns Pau's fits base width (1 <= width <= 40, 0 <= base, base + width <= 48) in a0,
   for the int32 arguments base (a0) and width (a1). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaJournal GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* a0 at the return, as the walk computes it:
   (~(base <s 0) & (sext32 (width - 1) <u 40)) & (sext32 (width + base) <s 49). *)
Definition FITS_A : sv := SAlu ALU_SLT (SOff 10 0) (SLit 0).
Definition FITS_T : sv := SAlu ALU_SLTU (SAluw ALU_ADD (SOff 11 0) (SLit (-1))) (SLit 40).
Definition FITS_C : sv := SAlu ALU_SLT (SAluw ALU_ADD (SOff 11 0) (SOff 10 0)) (SLit 49).
Definition FITS_L : sv := SAlu ALU_AND (SAlu ALU_XOR FITS_A (SLit (-1))) FITS_T.
Definition FITS_R : sv := SAlu ALU_AND FITS_L FITS_C.
Lemma U_atom_mod : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
intros E n v H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, bv_wrap, M64.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Local Ltac zbool :=
repeat match goal with
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
| H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
| H : (_ && _) = false |- _ => apply Bool.andb_false_iff in H; destruct H
end.
(* Split every if of the goal on its condition and close each case by linear arithmetic. *)
Local Ltac ifs_lia := repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end; zbool; lia.
Local Ltac unwrap :=
unfold bv_swrap, bv_wrap, zcanon, M64 in *;
try change (bv_modulus 64) with (2 ^ 64) in *; try change (bv_modulus 32) with (2 ^ 32) in *;
try change (bv_half_modulus 64) with (2 ^ 63) in *; try change (bv_half_modulus 32) with (2 ^ 31) in *.
Lemma fits_A : forall E base, ew E 10 = Z_to_bv 64 base -> int32 base -> U E FITS_A = if base <? 0 then 1 else 0.
Proof.
intros E base H Hb. unfold FITS_A, int32 in *. rewrite U_SAlu, (U_atom_mod E 10 base H), U_SLit. cbn [zalu_raw].
unwrap. ifs_lia.
Qed.
Lemma fits_T : forall E width, ew E 11 = Z_to_bv 64 width -> int32 width ->
U E FITS_T = if (1 <=? width) && (width <=? 40) then 1 else 0.
Proof.
intros E width H Hw. unfold FITS_T, int32 in *.
rewrite U_SAlu, (U_SLit E 40), U_of_S, S_SAluw, (U_atom_mod E 11 width H), U_SLit. cbn [zalu_raw].
unwrap. ifs_lia.
Qed.
Lemma fits_L : forall E base width, ew E 10 = Z_to_bv 64 base -> ew E 11 = Z_to_bv 64 width -> int32 base -> int32 width ->
U E FITS_L = Z.b2z ((0 <=? base) && (1 <=? width) && (width <=? 40)).
Proof.
intros E base width H10 H11 Hb Hw. unfold FITS_L.
rewrite (U_SAlu E ALU_AND), (U_SAlu E ALU_XOR), (fits_A E base H10 Hb), (fits_T E width H11 Hw), U_SLit.
destruct (Z.ltb_spec base 0); [replace (0 <=? base) with false by (symmetry; apply Z.leb_gt; lia)
| replace (0 <=? base) with true by (symmetry; apply Z.leb_le; lia)];
destruct (1 <=? width), (width <=? 40); reflexivity.
Qed.
Lemma fits_C : forall E base width, ew E 10 = Z_to_bv 64 base -> ew E 11 = Z_to_bv 64 width ->
0 <= base < 2 ^ 31 -> 1 <= width <= 40 -> base + width < 2 ^ 31 ->
U E FITS_C = if base + width <=? 48 then 1 else 0.
Proof.
intros E base width H10 H11 Hb Hw Hs. unfold FITS_C.
rewrite U_SAlu, (U_SLit E 49), U_of_S, S_SAluw, (U_atom_mod E 11 width H11), (U_atom_mod E 10 base H10). cbn [zalu_raw].
unwrap. ifs_lia.
Qed.
Lemma fits_value : forall E base width, ew E 10 = Z_to_bv 64 base -> ew E 11 = Z_to_bv 64 width ->
int32 base -> int32 width -> (0 <= base -> 1 <= width <= 40 -> base + width < 2 ^ 31) ->
U E FITS_R = Z.b2z (fits base width).
Proof.
intros E base width H10 H11 Hb Hw Hs. unfold FITS_R, fits.
rewrite (U_SAlu E ALU_AND FITS_L FITS_C), (fits_L E base width H10 H11 Hb Hw).
destruct (Z.leb_spec 0 base) as [H0 | H0]; destruct (Z.leb_spec 1 width) as [H1 | H1];
destruct (Z.leb_spec width 40) as [H2 | H2]; cbn [andb Z.b2z zalu_raw];
rewrite ?andb_false_r; try (rewrite Z.land_0_l; reflexivity).
rewrite (fits_C E base width H10 H11 ltac:(unfold int32 in Hb; lia) ltac:(lia) (Hs H0 (conj H1 H2))).
destruct (base + width <=? 48); reflexivity.
Qed.
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
(* The function's address in the image and the stack it needs: no frame of its own,
   ESTACK for the runtime's use. *)
Definition A_reac_grant_alloc_fitsP : Z := BASE + AF_reac_grant_alloc_fits.
Definition REAC_GRANT_ALLOC_FITS_STK : Z := ESTACK.
Definition SB_GF : Z := 0x7fff8000.
Definition Bx_GF : sv := SLit SB_GF.
Definition Bspan_GF : Z * Z := (SB_GF, SB_GF + 2 ^ 44 - 1).
Definition ss_gf : sstate := mkSS AF_reac_grant_alloc_fits sr_atoms [] None (mkFacts [] [] []).
Section h.
Variable B : asyms.
Definition treac_grant_alloc_fits_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (base width : Z)
: world SEGS -> config -> Prop :=
apost_base SEGS B REAC_GRANT_ALLOC_FITS_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 (Z.b2z (fits base width)) /\ ly' = ly /\ S' = S /\ W' = W /\ (forall x, mem' x = mem x) /\
Permutation (ablocks B ly' S') (ablocks B ly S)).
Definition treac_grant_alloc_fits_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (base width : Z),
afn_pre SEGS B REAC_GRANT_ALLOC_FITS_STK ly S W regs mem md ch ->
getr regs 10 = w64 base -> getr regs 11 = w64 width ->
int32 base -> int32 width -> (0 <= base -> 1 <= width <= 40 -> base + width < 2 ^ 31) ->
SRr SEGS W (cfg_at SEGS A_reac_grant_alloc_fitsP regs mem md)
(treac_grant_alloc_fits_post regs ly S W mem md base width).
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
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
Theorem pb_reac_grant_alloc_fits : treac_grant_alloc_fits_spec.
Proof.
unfold treac_grant_alloc_fits_spec.
intros ly S W regs mem md ch base width HPRE H10 H11 Hb Hw Hs.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (gf_entry W regs mem) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_GRANT_ALLOC_FITS_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 base) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 width) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HM : forall x, mem x = mem x) by reflexivity.
clear HE.
unfold cfg_at, A_reac_grant_alloc_fitsP.
change (w64 (BASE + AF_reac_grant_alloc_fits)) with (Z_to_bv 64 (BASE + AF_reac_grant_alloc_fits)).
paj_run_tok RUN HS HJ SHOK Bspan_GF; [first [apply awr_ok_nil | awr_ok_tac] |].
upd_mem.
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
pose proof (st_ok_pi_restrict_reg _ E ssx msc (10%bv : bv 5) HS) as R10;
replace (sr_get (ss_regs ssx) (10%bv : bv 5)) with FITS_R in R10 by (vm_compute; reflexivity);
prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold treac_grant_alloc_fits_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]|];
split; [rewrite R10, denot_lit_U, (fits_value E base width E10 E11 Hb Hw Hs); reflexivity|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [exact HM | apply Permutation_refl]
end.
Qed.
End h.
End f.
End d.
