(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:104-108;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 358-361,
   386-392, 532-535, for libreac/fuzz_identity's ASan build (lib/A). *)
(* reac_box_family_stem (fuzz_identity.asan 0x829c4, 24 slots to 0x82a20): the contract of the
   ASan build's code and its walk. The function takes a 16-byte frame on the machine stack and
   stores ra in it. For the family f (a0, an int) with 1 <= f <= 3 it reads the 8-byte entry f - 1
   of the read-only table switch.table.reac_box_family_stem (object 17), after the memory-checking
   shadow test of that entry, and returns it in a0; for any other f it returns the address of the
   string "REAC" (object 18). Its only caller is LLVMFuzzerTestOneInput (the call at 0x81898), which
   passes no buffer: the function writes only its own frame, so the contract is in the
   afn_pre / apost_base form. Stack: 16 + ESTACK. Events: none (the journal's k is 0). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow IdentSyms IdentList IdentPa.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaJournal IdentPaLib IdentBase IdentRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 16-byte frame and
   ESTACK for the runtime's use (the only call, at 0x82a20, is the error path). *)
Definition A_reac_box_family_stemP : Z := BASE + AF_reac_box_family_stem.
Definition REAC_BOX_FAMILY_STEM_STK : Z := 16 + ESTACK.
(* The value returned for the family f when the table holds t1, t2, t3. *)
Definition stem_sel (f t1 t2 t3 : Z) : Z :=
  if f =? 1 then t1 else if f =? 2 then t2 else if f =? 3 then t3 else VAL (A_OBJ 18).
(* The walk's symbolic state at entry: the frame below sp (atom 2), the GOT slot of the shadow
   base (object 1, holding the address of object 30), the shadow cell (object 30, holding the
   shadow base, atom 35) and the table (object 17, its entries atoms 32, 33, 34). *)
Definition SB_FS : Z := 0x7fff8000.
Definition Bx_FS : sv := SOff 35 0.
Definition Bspan_FS : Z * Z := (SB_FS, SB_FS + 2 ^ 44 - 1).
Definition tbl_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 17)) 0 24 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
Definition fs_regions : smem := [stack_region 16; got_regionP; bcell_regionP 35; tbl_region].
Definition fs_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (A_OBJ 17, mkAF IMG_LO (IMG_TOP - 8) 0); (35%nat, mkAF SB_FS SB_FS 0)] [] [].
Definition ss_fs : sstate := mkSS AF_reac_box_family_stem sr_atoms fs_regions None fs_facts.
Definition fs_SH : list shent := [mkSHE (A_OBJ 17) 0 24].
Definition fs_extra (t1 t2 t3 : Z) : list word := map (Z_to_bv 64) [t1; t2; t3; SB_FS].
Definition EF (regs : bvmap 5 word) (t1 t2 t3 : Z) : env := Eimg (Ereg regs (fs_extra t1 t2 t3)).
Lemma val_mem_mod64 : forall m a v, val_mem SEGS m a 8 v -> val_mem SEGS m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte.
assert (P : 2 ^ (8 * Z.of_nat 8) = 2 ^ 64) by reflexivity. rewrite !P.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma Z_to_bv_mod64 : forall t, Z_to_bv 64 (t mod 2 ^ 64) = Z_to_bv 64 t.
Proof.
intros t. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
Section h.
Variable B : asyms.
Definition treac_box_family_stem_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r : Z)
: world SEGS -> config -> Prop :=
apost_base SEGS B REAC_BOX_FAMILY_STEM_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 r /\ ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S)).
(* f is the int in a0; t1, t2, t3 are the three entries of the table (object 17), and the table's
   24 bytes lie in a range the memory-checking runtime leaves marked usable (IdentRo's in_zs). *)
Definition treac_box_family_stem_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (f t1 t2 t3 : Z),
afn_pre SEGS B REAC_BOX_FAMILY_STEM_STK ly S W regs mem md ch ->
getr regs 10 = w64 f -> - 2 ^ 31 <= f < 2 ^ 31 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 17)) 8 t1 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 17) + 8) 8 t2 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 17) + 16) 8 t3 ->
in_zs B (VAL (A_OBJ 17)) 24 ->
SRr SEGS W (cfg_at SEGS A_reac_box_family_stemP regs mem md)
(treac_box_family_stem_post regs ly S W mem md (stem_sel f t1 t2 t3)).
(* The walk (slots 0x829c4 .. 0x82a1c; 0x82a20 is the error-path call of __asan_report_load8).
   For f = 1, 2, 3 the walk pins a0 to f: the bounds test at 0x829d4 is then decided, the
   shadow-base loads at 0x829dc (GOT slot, object 1) and 0x829e4 (shadow cell, object 30) read
   the cells PALib names, the shadow test of the entry at 0x829fc/0x82a00 is covered by the
   shadow entry of the table (in_zs, through IdentRo's ro_usable), and 0x82a04 loads t_f from the
   table's region. For any other f the bounds test is open: its fall-through contradicts f's
   range, and its target 0x82a0c returns object 18. *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
(* The table lies apart from the GOT slot and the shadow cell (an image fact). *)
Hypothesis TBLSEP :
(VAL (A_OBJ 17) + 24 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 17)) /\
(VAL (A_OBJ 17) + 24 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= VAL (A_OBJ 17)).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_ident) (PI := PI).
Lemma fs_entry : forall ly S W (regs : bvmap 5 word) mem md ch (t1 t2 t3 : Z),
afn_pre SEGS B REAC_BOX_FAMILY_STEM_STK ly S W regs mem md ch ->
0 <= t1 < 2 ^ 64 -> 0 <= t2 < 2 ^ 64 -> 0 <= t3 < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 17)) 8 t1 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 17) + 8) 8 t2 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 17) + 16) 8 t3 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 17)) 24 ->
st_ok_pi SEGS VAL (EF regs t1 t2 t3) ss_fs
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_family_stem)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx_FS fs_SH (EF regs t1 t2 t3) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch t1 t2 t3 HPRE R1 R2 R3 V1 V2 V3 HRA.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_FAMILY_STEM_STK = 4112) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 17 ltac:(lia)) as HtblR.
pose proof TBLSEP as [Ts1 Ts30].
rewrite restrict_mkst_fx.
set (E := EF regs t1 t2 t3).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EF; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (fs_extra t1 t2 t3)) n)
by (intros n Hn; subst E; unfold EF; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 t1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 t2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 t3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB_FS) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EF; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; unfold EF; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO17 : ew E (A_OBJ 17) = Z_to_bv 64 (VAL (A_OBJ 17))) by (subst E; unfold EF; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 1)) as Rg1. pose proof (pa_val_range (A_OBJ 30)) as Rg30. pose proof (pa_val_range (A_OBJ 17)) as Rg17.
split.
- unfold ss_fs. apply pa_entry_st_ok_full.
+ subst E. unfold EF. apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold fs_regions, stack_region, got_regionP, bcell_regionP, tbl_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1 Rg1). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite EO30, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EO30 Rg30). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 Bx_FS SB_FS);
[cbn [sv_denot Bx_FS]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_FS; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB (A_OBJ 17) (VAL (A_OBJ 17)) EO17 Rg17). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 17)) 0 8 (SOff 32 0) t1);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact V1.
-- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 17)) 8 8 (SOff 33 0) t2);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V2].
-- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 17)) 16 8 (SOff 34 0) t3);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V3].
+ apply pairwise_disjoint_of_extents. unfold fs_regions, stack_region, got_regionP, bcell_regionP, tbl_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1 Rg1), (VB (A_OBJ 30) (VAL (A_OBJ 30)) EO30 Rg30), (VB (A_OBJ 17) (VAL (A_OBJ 17)) EO17 Rg17).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hceil C1 WS HcellR HgcD HgotR HtblR Ts1 Ts30. clear. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [fs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, EO17, E35, !unsigned_lit_small by (unfold SB_FS; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 WS Hal16 HtblR. clear. unfold SB_FS. intros.
repeat split; lia.
- unfold sh_ok, fs_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E Bx_FS (A_OBJ 17) (VAL (A_OBJ 17)) 24 (VAL (A_OBJ 17)) 0 24 HRA).
+ unfold U, Bx_FS. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB_FS; lia). reflexivity.
+ exact (U_img_atom E HEI (A_OBJ 17) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF. lia.
Qed.
(* The bounds test at 0x829d4 for an f outside 1..3: 2 <u (f - 1 as an int). *)
Lemma fs_bltu_other : forall E f, ew E 10 = Z_to_bv 64 f -> - 2 ^ 31 <= f < 2 ^ 31 -> ~ (1 <= f <= 3) ->
branch_taken BC_LTU (sv_denot E (SLit 2)) (sv_denot E (SAluw ALU_ADD (SOff 10 0) (SLit (-1)))) = true.
Proof.
intros E f H Hf Hn. rewrite branch_ltu_U, U_SLit, U_of_S, S_SAluw, U_SOff, U_SLit, H, Z.add_0_r, Z_to_bv_unsigned.
cbn [zalu_raw]. apply Z.ltb_lt.
assert (A1 : zcanon (bv_wrap 64 f) mod 2 ^ 32 = f mod 2 ^ 32).
{ unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia.
Z.div_mod_to_equations; lia. }
replace (zcanon (-1) mod 2 ^ 32) with (2 ^ 32 - 1) by reflexivity.
replace (zcanon 2) with 2 by reflexivity.
rewrite A1. unfold bv_swrap, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
destruct (Z_lt_le_dec f 1); Z.div_mod_to_equations; lia.
Qed.
Theorem pb_reac_box_family_stem : treac_box_family_stem_spec.
Proof.
unfold treac_box_family_stem_spec.
intros ly S W regs mem md ch f t1 t2 t3 HPRE H10 Hf V1 V2 V3 HZS.
pose proof (ro_usable SEGS B LAWS ly S W mem md (VAL (A_OBJ 17)) 24 (proj1 HPRE) HZS) as HRA.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
set (u1 := t1 mod 2 ^ 64). set (u2 := t2 mod 2 ^ 64). set (u3 := t3 mod 2 ^ 64).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (subst u1; apply Z.mod_pos_bound; lia).
assert (Ru2 : 0 <= u2 < 2 ^ 64) by (subst u2; apply Z.mod_pos_bound; lia).
assert (Ru3 : 0 <= u3 < 2 ^ 64) by (subst u3; apply Z.mod_pos_bound; lia).
destruct (fs_entry ly S W regs mem md ch u1 u2 u3 HPRE Ru1 Ru2 Ru3
(val_mem_mod64 _ _ _ V1) (val_mem_mod64 _ _ _ V2) (val_mem_mod64 _ _ _ V3) HRA) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_BOX_FAMILY_STEM_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (EF regs u1 u2 u3) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EF; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (fs_extra u1 u2 u3)) n)
by (intros n Hn; subst E; unfold EF; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 u1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 u2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 u3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E259 : ew E 259%nat = Z_to_bv 64 (VAL (A_OBJ 18))) by (subst E; unfold EF; exact (Eimg_img _ 259%nat ltac:(unfold A_TEXT, A_LIM; lia))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (fs_extra u1 u2 u3)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at, A_reac_box_family_stemP.
change (w64 (BASE + AF_reac_box_family_stem)) with (Z_to_bv 64 (BASE + AF_reac_box_family_stem)).
(* The walk's tactics. RV: a0 at the return is the table entry (atoms 32, 33, 34) or object 18.
   leaf_ret: the return at 0x82a1c builds apost_base from the journal. dead: a branch side the
   walk cannot reach (decided literals, or the bounds test against f's range). go: run to the
   next stop and dispatch. pin: a0 is the literal f. *)
let RV := idtac;
first [ rewrite E32; change (stem_sel 1 t1 t2 t3) with t1; unfold w64; subst u1; apply Z_to_bv_mod64
| rewrite E33; change (stem_sel 2 t1 t2 t3) with t2; unfold w64; subst u2; apply Z_to_bv_mod64
| rewrite E34; change (stem_sel 3 t1 t2 t3) with t3; unfold w64; subst u3; apply Z_to_bv_mod64
| rewrite E259; unfold stem_sel;
destruct (Z.eqb_spec f 1); [lia|]; destruct (Z.eqb_spec f 2); [lia|]; destruct (Z.eqb_spec f 3); [lia|]; reflexivity ] in
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold treac_box_family_stem_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (fs_extra u1 u2 u3) HS); [exact HAE | vm_compute; reflexivity]|];
split; [cbn [ms_regs]; rewrite R10; RV|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; apply Permutation_refl
end in
let dead := idtac;
lazymatch goal with
| Hc : branch_taken _ (sv_denot _ (SLit _)) (sv_denot _ (SLit _)) = _ |- _ => exfalso; vm_compute in Hc; discriminate Hc
| Hc : branch_taken _ _ _ = _ |- _ => exfalso; rewrite (fs_bltu_other E f E10 Hf ltac:(lia)) in Hc; discriminate Hc
end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK Bspan_FS; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |];
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx_FS fs_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bx_FS Bspan_FS fs_SH (start K Bx_FS Bspan_FS fs_SH ss) end in
let pc := eval vm_compute in (ss_pc ss) in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' Bspan_FS; [first [solve [dead] | go] | first [solve [dead] | go]]
| _ => idtac "STUCK" pc why; fail
end
end end in
let pin v :=
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss0 ?ms0 |- _ =>
let HP := fresh "HP" in
pose proof (st_ok_pi_pin_reg' Ex ss0 ms0 (10%bv : bv 5) v HS ltac:(cbn [ms_regs restrict mkst]; exact H10) eq_refl) as HP;
clear HS; rename HP into HS;
lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ => let ss2 := eval vm_compute in ss1 in change ss1 with ss2 in HS end
end in
assert (C : f = 1 \/ f = 2 \/ f = 3 \/ ~ (1 <= f <= 3)) by lia;
destruct C as [-> | [-> | [-> | HN]]];
[ pin constr:(1%Z); go | pin constr:(2%Z); go | pin constr:(3%Z); go | go ].
Qed.
End h.
End f.
End d.
