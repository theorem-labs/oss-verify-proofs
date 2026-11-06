(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:156-159;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-277;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 332-335, 358-363, for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 208-211. *)
(* check_str (fuzz_identity.asan-ubsan 0x82830, 31 slots): the contract of the ASan+UBSan build's code and its
   walk, the B twin of lib/A/Prog/check_str.v (same names, same statement; the module path distinguishes them).
   The function takes a 16-byte frame, returns at once when r < 0, and otherwise aborts unless r < c, traps
   (UBSan pointer overflow, 0x8284c -> 0x8289c) unless o + r does not wrap, reads the shadow byte of o + r
   (ASan load1, with __asan_report_load1 at 0x828a8 on the error path), aborts unless o[r] = 0, calls the strlen
   wrapper on o and aborts unless it answers r. Differences from the A walk: the UBSan branch at 0x8284c (A has
   none), the shadow cell is object 31 of the B listing (A: 30), and the symbols/listing are the B ones. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef WrapRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition CBx : sv := SOff 32 0.
Definition cs_extra (r o : Z) : list word := map (Z_to_bv 64) [SB; o + r].
Definition str_region : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition cs_regions : smem := [stack_region 16; got_regionP; bcell_regionP 32; str_region].
Definition cs_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0 (2 ^ 31 - 1) 0); (32%nat, mkAF SB SB 0); (33%nat, mkAF 1 (2 ^ 47 - 1) 0)]
[] [(SAlu ALU_ADD (SOff 11 0) (SOff 10 0), SOff 33 0)].
Definition ss_cs : sstate := mkSS AF_check_str sr_atoms cs_regions None cs_facts.
Definition cs_SH : list shent := [mkSHE 33 0 1].
Definition ss_csn : sstate := mkSS AF_check_str sr_atoms [stack_region 16] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Definition cs_wins_ok (rs : smem) : bool :=
forallb (fun rg => (YP09.r_whi rg <=? YP09.r_wlo rg) ||
match YP09.r_base rg with Some 2%nat => (YP09.r_wlo rg =? -16) && (YP09.r_whi rg =? 0) | _ => false end) rs.
Lemma cs_nwr : forall Ex rs a, cs_wins_ok rs = true -> ~ (bv_unsigned (ew Ex 2) - 16 <= a < bv_unsigned (ew Ex 2)) -> ~ in_wrange Ex rs a.
Proof.
intros Ex rs a Hok Hn (rg & Hin & Ha). unfold cs_wins_ok in Hok. rewrite forallb_forall in Hok. specialize (Hok rg Hin).
apply orb_prop in Hok. destruct Hok as [Hw | Hb].
- apply Z.leb_le in Hw. lia.
- destruct (YP09.r_base rg) as [[|[|[|n]]]|] eqn:Eb; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1, H2. cbn [base_val] in Ha. lia.
Qed.
Lemma cs_blt : forall E v, ew E 10 = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 ->
branch_taken BC_LT (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof.
intros E v H Hv. rewrite YO0c.branch_lt.
change (bv_unsigned (sv_denot E (SOff 10 0))) with (U E (SOff 10 0)). change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)).
rewrite U_SOff, U_SLit, H, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, YO0b.s64. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.add_0_r, Z.mod_mod by lia. change (0 mod 2 ^ 64) with 0. change (0 <? 2 ^ 63) with true.
destruct (Z.ltb_spec v 0) as [Hn | Hp].
- replace (v mod 2 ^ 64) with (v + 2 ^ 64) by (apply Z.mod_unique with (-1); lia).
destruct (Z.ltb_spec (v + 2 ^ 64) (2 ^ 63)); [lia|]. apply Z.ltb_lt. lia.
- rewrite Z.mod_small by lia. destruct (Z.ltb_spec v (2 ^ 63)); [|lia]. apply Z.ltb_ge. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Definition A_check_strP : Z := BASE + AF_check_str.
Definition CHECK_STR_STK : Z := 16 + 2 * ESTACK.
Definition CE (regs : bvmap 5 word) (r o : Z) : env := Eimg (Ereg regs (cs_extra r o)).
Definition tcheck_str_ok (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (r o c : Z) : Prop :=
r < c /\ 0 < o /\ (o + r + 1 <= IMG_LO \/ IMG_TOP <= o) /\
first_byte SEGS W mem o (r + 1) 0 r /\
(forall a, o <= a <= o + r -> ~ (spZ regs - CHECK_STR_STK <= a < spZ regs)) /\
amem_range o (r + 1) /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF o (r + 1) /\
shadow_hull_vis (aview SEGS (w_H W) mem) o (r + 1) /\
(forall a, o + r < a < o + r - (o + r) mod 8 + 8 -> aview SEGS (w_H W) mem a <> None).
Lemma cs_kept_fr : forall Ex rs H (m m' : word -> option byte) a,
frame_of Ex rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange Ex rs a ->
aview SEGS H m' a = aview SEGS H m a.
Proof. intros Ex rs H m m' a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.
Lemma cs_val_mem1 : forall H mem a, aview SEGS H mem a = Some 0 -> val_mem SEGS (mrestrict H mem) a 1 0.
Proof.
intros H mem a Hz j Hj. assert (j = 0%nat) by lia. subst j.
destruct (aview_byte SEGS H mem (a + Z.of_nat 0) 0 ltac:(rewrite Z.add_0_r; exact Hz)) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
Lemma cs_aro_kept : forall (B : asyms) (W : world SEGS) mem mem' lo,
aro_unowned SEGS B (aview SEGS (w_H W) mem) -> IMG_TOP <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < lo + 16) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
aro_unowned SEGS B (aview SEGS (w_H W) mem').
Proof.
intros B W mem mem' lo HR Hlo HK. apply (aro_unowned_keep SEGS B _ _ HR). intros a (sg & Hsg & Hw & Ha) _ _.
assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Ha]). pose proof (pa_img_range a Hi).
apply HK; lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IB___interceptor_trampoline_strlen).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Definition tcheck_str_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md : world SEGS -> config -> Prop :=
apost_base SEGS B CHECK_STR_STK [] regs ly S W mem md 0
(fun ly' S' W' _ _ _ => ly' = ly /\ S' = S /\ W' = W).
Definition tcheck_str_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r o c : Z),
afn_pre SEGS B CHECK_STR_STK ly S W regs mem md ch ->
aro_unowned SEGS B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 r -> getr regs 11 = w64 o -> getr regs 12 = w64 c ->
- 2 ^ 31 <= r < 2 ^ 31 -> 0 <= c < 2 ^ 64 ->
(0 <= r -> tcheck_str_ok W regs mem r o c) ->
SRr SEGS W (cfg_at SEGS A_check_strP regs mem md) (tcheck_str_post regs ly S W mem md).
Lemma cs_entry : forall ly S W (regs : bvmap 5 word) mem md ch r o,
afn_pre SEGS B CHECK_STR_STK ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 o -> 0 <= r < 2 ^ 31 ->
0 < o -> (o + r + 1 <= IMG_LO \/ IMG_TOP <= o) ->
(forall a, o <= a <= o + r -> ~ (spZ regs - CHECK_STR_STK <= a < spZ regs)) ->
amem_range o (r + 1) ->
aview SEGS (w_H W) mem (o + r) = Some 0 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF o (r + 1) ->
st_ok_pi SEGS VAL (CE regs r o) ss_cs (restrict (w_H W) (mkst regs (Z_to_bv 64 A_check_strP) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBx cs_SH (CE regs r o) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r o HPRE H10 H11 Hr Ho Himg Hwin Hamr Hnul Hras.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_STR_STK = 8208) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 31 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (Hwin (o + r) ltac:(lia)) as Hw1.
unfold amem_range in Hamr. rewrite C4, C5, C3 in Hamr.
rewrite restrict_mkst_fx.
set (E := CE regs r o).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cs_extra r o)) n) by (intros n Hn; subst E; unfold CE; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (o + r)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eg : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold CE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ec : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31))) by (subst E; unfold CE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 1)) as Vg. pose proof (pa_val_range (A_OBJ 31)) as Vc.
split.
- unfold ss_cs, A_check_strP. apply pa_entry_st_ok_full.
+ subst E. unfold CE. apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cs_regions, stack_region, got_regionP, bcell_regionP, str_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
[cbn [sv_denot]; rewrite Ec, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) Ec) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 31)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 33%nat (o + r) E33) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (o + r) 0 1 (SLit 0) 0); [reflexivity | cbn; lia | lia |].
rewrite Z.add_0_r. exact (cs_val_mem1 _ _ _ Hnul).
+ apply pairwise_disjoint_of_extents. unfold cs_regions, stack_region, got_regionP, bcell_regionP, str_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) Ec) by lia.
rewrite (VB 33%nat (o + r) E33) by lia. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 WS Hstk0 HgotR HcellR HgcD Himg Hw1 Ho Hr. clear. intros.
repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [cs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hal16 Hslo Hshi H47 Hceil C1 WS Hstk0 Hamr Ho Hr. clear. unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; lia.
* cbn [cs_facts f_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 11 o E11), (U_atom E 10 r E10), (U_atom E 33 (o + r) E33) by lia.
unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity.
- unfold sh_ok, cs_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E CBx 33 o (r + 1) (o + r) 0 1 Hras).
+ unfold CBx. rewrite (U_atom E 32 SB E32) by (unfold SB; lia). reflexivity.
+ exact (U_atom E 33 (o + r) E33 ltac:(lia)).
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF. lia.
Qed.
Lemma cs_entry_neg : forall ly S W (regs : bvmap 5 word) mem md ch r o,
afn_pre SEGS B CHECK_STR_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (CE regs r o) ss_csn (restrict (w_H W) (mkst regs (Z_to_bv 64 A_check_strP) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBx [] (CE regs r o) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r o HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_STR_STK = 8208) by reflexivity.
rewrite restrict_mkst_fx.
set (E := CE regs r o).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cs_extra r o)) n) by (intros n Hn; subst E; unfold CE; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split; [|apply Forall_nil].
unfold ss_csn, A_check_strP. apply pa_entry_st_ok_full.
- subst E. unfold CE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor].
intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. cbn. repeat constructor.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16. revert Hal16 Hslo Hshi H47 Hceil C1 WS Hstk0. clear. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Lemma cs_strlen_at : forall W (regsT : bvmap 5 word) memT ly S W0 mem md mdc sp0 o r,
ajournal SEGS B CHECK_STR_STK sp0 [] ly S W0 mem md [] ly S W memT mdc 0 ->
getr regsT 10 = w64 o -> spZ regsT = sp0 - 16 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> YK0s.ret_ok (getr regsT 1) ->
0 < o -> 0 <= r < 2 ^ 31 ->
first_byte SEGS W memT o (r + 1) 0 r ->
(forall a, o <= a <= o + r -> ~ (sp0 - CHECK_STR_STK <= a < sp0)) ->
amem_range o (r + 1) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF o (r + 1) ->
shadow_hull_vis (aview SEGS (w_H W) memT) o (r + 1) ->
(forall a, o + r < a < o + r - (o + r) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
aro_unowned SEGS B (aview SEGS (w_H W) memT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_strlen)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B CHECK_STR_STK sp0 [] ly S W0 mem md [] ly S W mem2 md2 0 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 r /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 16 - 2 * ESTACK <= a < sp0 - 16) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT ly S W0 mem md mdc sp0 o r HJ Ha0 Hsp Hgp Htp Hraw Ho Hr Hfb Hwin Hamr Hras Hhull Hslack Hrom.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : CHECK_STR_STK = 8208) by reflexivity.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof Hamr as Hamr'. unfold amem_range in Hamr'. rewrite C4, C5, C3 in Hamr'.
assert (HPRE : ecall_pre SEGS B ly S W regsT memT mdc).
{ split; [exact HAR|]. split; [exact Hraw|]. split; [rewrite Hsp, Zminus_mod, Hal16; reflexivity|].
split; [rewrite Hsp; lia|]. split; [rewrite Hsp; lia|].
split; [intros a Ha; apply Hpres; rewrite Hsp in Ha; lia|]. split; [exact Hgp | exact Htp]. }
assert (Hsrc : src_ok SEGS W regsT memT o (r + 1)).
{ intros a Ha. split; [|rewrite Hsp; pose proof (Hwin a ltac:(lia)); lia].
destruct Hfb as (_ & Hlt & Hat). destruct (Z.lt_ge_cases a (o + r)) as [Hl | Hg].
- destruct (Hlt (a - o) ltac:(lia)) as (b & Hb & _). replace a with (o + (a - o)) by lia. rewrite Hb. discriminate.
- replace a with (o + r) by lia. rewrite (Hat ltac:(lia)). discriminate. }
eapply SRr_mono.
{ exact (ASTRLEN ly S W regsT memT mdc o r HPRE ltac:(rewrite Hsp; lia)
ltac:(intros a Ha; apply Hpres; rewrite Hsp in Ha; lia) Ha0 Ho ltac:(lia) ltac:(lia) ltac:(lia) Hfb Hsrc
ltac:(intros a Ha; rewrite Hsp; pose proof (Hwin a Ha); lia) Hamr Hras Hhull Hslack Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low CHECK_STR_STK sp0 [] ly S W0 mem md [] ly S W memT mdc 0 mem2 md2
(fun a => sp0 - 16 - 2 * ESTACK <= a < sp0 - 16) S [] HJ).
- intros a Ha Hna. apply (Hfr a Ha). rewrite Hsp. exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha. left. left. lia.
- exact HAR2.
- reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [|exact Hpres2].
intros a Ha Hn. apply (Hfr a Ha). rewrite Hsp. exact Hn.
Qed.
Ltac cs_agree HAE :=
split; [ intros nn Hnn; repeat first [ rewrite ew_havoc_old by lia | rewrite ew_ewset_other by lia ]; exact (proj1 HAE nn Hnn)
| cbn [ed ewset havoc]; exact (proj2 HAE) ].
Ltac cs_ret :=
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ (restrict (w_H ?W) ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAE : env_agree 32 (Ereg ?regs ?extra) _, E1 : ew _ 1 = getr _ 1, Hra : YK0s.ret_ok _,
Hsegs : forall a, in_img _ a -> 0 <= a < kLowMemEnd |- _ =>
let R1 := fresh "R1" in
prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold tcheck_str_post, apost_base;
do 5 eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs extra HS); [cs_agree HAE | vm_compute; reflexivity]|];
split; [reflexivity|]; split; reflexivity
end.
Ltac cs_kill :=
lazymatch goal with Hc : branch_taken ?cc (sv_denot ?Ex ?a) (sv_denot ?Ex ?b) = _ |- _ =>
exfalso;
first
[ lazymatch cc with BC_LT => idtac end;
lazymatch goal with E10 : ew _ 10 = Z_to_bv 64 ?r |- _ =>
let X := fresh "X" in assert (X : ew Ex 10 = Z_to_bv 64 r) by (cbn [ew ewset havoc Nat.eqb Nat.ltb]; exact E10);
rewrite (cs_blt Ex r X ltac:(lia)) in Hc;
destruct (Z.ltb_spec r 0); first [discriminate Hc | lia] end
| lazymatch cc with BC_GEU => idtac end;
lazymatch goal with E10 : ew _ 10 = Z_to_bv 64 ?r, E12 : ew _ 12 = Z_to_bv 64 ?c |- _ =>
let X := fresh "X" in let Y := fresh "Y" in
assert (X : ew Ex 10 = Z_to_bv 64 r) by (cbn [ew ewset havoc Nat.eqb Nat.ltb]; exact E10);
assert (Y : ew Ex 12 = Z_to_bv 64 c) by (cbn [ew ewset havoc Nat.eqb Nat.ltb]; exact E12);
rewrite branch_geu_U, (U_atom Ex 10 r X), (U_atom Ex 12 c Y) in Hc by lia;
destruct (Z.ltb_spec r c); first [discriminate Hc | lia] end
| lazymatch cc with BC_NE => idtac end;
lazymatch goal with X204 : ew Ex 204 = Z_to_bv 64 ?r, X10 : ew Ex 10 = Z_to_bv 64 ?r |- _ =>
rewrite branch_ne_U, (U_atom Ex 204 r X204), (U_atom Ex 10 r X10) in Hc by lia;
rewrite Z.eqb_refl in Hc; discriminate Hc end
(* B only: the UBSan pointer-overflow trap at 0x8289c. a0 = not o, and the branch is taken only if
   2 ^ 64 - 1 - o < r, which the read range o .. o + r (amem_range) rules out. *)
| lazymatch cc with BC_LTU => idtac end;
lazymatch goal with E11 : ew _ 11 = Z_to_bv 64 ?o, E10 : ew _ 10 = Z_to_bv 64 ?r, HA : amem_range ?o (?r + 1) |- _ =>
let X := fresh "X" in let Y := fresh "Y" in let Z0 := fresh "Z0" in
assert (X : ew Ex 11 = Z_to_bv 64 o) by (cbn [ew ewset havoc Nat.eqb Nat.ltb]; exact E11);
assert (Y : ew Ex 10 = Z_to_bv 64 r) by (cbn [ew ewset havoc Nat.eqb Nat.ltb]; exact E10);
pose proof HA as Z0; unfold amem_range in Z0;
rewrite branch_ltu_U, U_SAlu in Hc; cbn [zalu_raw] in Hc;
rewrite (U_atom Ex 11 o X) in Hc by zlia;
rewrite (U_atom Ex 10 r Y) in Hc by lia;
rewrite U_SLit in Hc;
replace (zcanon (-1)) with (2 ^ 64 - 1) in Hc by (vm_compute; reflexivity);
rewrite lxor_allones in Hc by zlia;
rewrite zcanon_id in Hc by (unfold M64; zlia);
destruct (Z.ltb_spec (2 ^ 64 - 1 - o) r); first [discriminate Hc | zlia] end ]
end.
Ltac cs_keep :=
try lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ ?m1),
KEEP : forall a, _ -> ~ (spZ ?regs - 16 <= a < _) -> aview _ (w_H ?W) ?m0 a = aview _ _ ?mem a,
Usp : bv_unsigned (ew _ 2) = spZ _ |- _ =>
let K2 := fresh "KEEP" in
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
intros a Ha Hw; rewrite (cs_kept_fr Ex rs (w_H W) m0 m1 a HFr Ha); [exact (KEEP a Ha Hw)|]; apply cs_nwr;
[vm_compute; reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb]; rewrite Usp; exact Hw]);
clear KEEP; rename K2 into KEEP
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac cs_go :=
lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
Usp : bv_unsigned (ew _ 2) = spZ _ |- _ =>
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb]; rewrite ?ew_ewset_other by lia; exact Usp |];
cs_keep;
lazymatch goal with
| HS' : st_ok _ _ (setpc _ _) (restrict _ _) |- _ => idtac
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ ?Bx ?SH _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bx Bspan SH (start K Bx Bspan SH ss) end in
lazymatch why with
| SR_jalr _ => cs_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' Bspan; [ first [ cs_kill | cs_go ] | first [ cs_kill | cs_go ] ]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end end.
Theorem pb_check_str : tcheck_str_spec.
Proof.
unfold tcheck_str_spec.
intros ly S W regs mem md ch r o c HPRE HROM H10 H11 H12 Hr Hcr HOK.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof (ajournal_init SEGS B CHECK_STR_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : CHECK_STR_STK = 8208) by reflexivity.
remember (CE regs r o) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold CE; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cs_extra r o)) n) by (intros n Hn; subst E; unfold CE; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cs_extra r o)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
by (intros; reflexivity).
unfold cfg_at. change (w64 A_check_strP) with (Z_to_bv 64 A_check_strP).
destruct (Z_lt_le_dec r 0) as [NEG | POS].
- destruct (cs_entry_neg ly S W regs mem md ch r o HPRE) as [HS SHOK]. rewrite <- HE in HS, SHOK. clear HE EL.
cs_go.
- destruct (HOK POS) as (Hrc & Ho & Himg & Hfb & Hwin & Hamr & Hras & Hhull & Hslack).
destruct (cs_entry ly S W regs mem md ch r o HPRE H10 H11 ltac:(lia) Ho Himg Hwin Hamr
ltac:(destruct Hfb as (_ & _ & Hn); apply Hn; lia) Hras) as [HS SHOK].
rewrite <- HE in HS, SHOK. clear HE EL.
cs_go.
pose proof Hamr as Hamr'. unfold amem_range in Hamr'. rewrite C4, C5, C3 in Hamr'.
pose proof (Z.mod_pos_bound (o + r) 8 ltac:(lia)) as M8. pose proof (Z.div_mod (o + r) 8 ltac:(lia)) as D8.
pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16.
lazymatch goal with HS : st_ok _ ?E1 _ (restrict _ ?ms1), HEI1 : img_env _ _ ?E1 |- _ =>
prreg HS (10%bv : bv 5) Ra0; prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2;
prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
rewrite E11 in Ra0; rewrite E3 in Q3; rewrite E4 in Q4; rewrite Usp in Q2;
assert (HspT : spZ (ms_regs ms1) = spZ regs - 16) by (unfold spZ in *; rewrite Q2; rewrite unsigned_lit_small; lia);
pmkst HS;
eapply SRr_bind;
[ apply (cs_strlen_at W (ms_regs ms1) (ms_mem ms1) ly S W mem md _ (spZ regs) o r HJ Ra0 HspT
ltac:(rewrite Q3; exact Hgp) ltac:(rewrite Q4; exact Htp)
ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) Ho ltac:(lia));
[ destruct Hfb as (Hk & Hlt & Hat); split; [exact Hk|]; split;
[ intros i Hi; rewrite KEEP; [exact (Hlt i Hi) | lia | pose proof (Hwin (o + i) ltac:(lia)); lia]
| intros Hl; rewrite KEEP; [exact (Hat Hl) | lia | pose proof (Hwin (o + r) ltac:(lia)); lia] ]
| exact Hwin
| exact Hamr
| apply (range_addressable_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem ms1)) (spZ regs - 16) (spZ regs) o (r + 1));
[ intros s Hs Hn; apply KEEP; [exact Hs | exact Hn] | lia | lia | lia | exact Hras ]
| apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem ms1)) (spZ regs - 16) (spZ regs) o (r + 1));
[ intros s Hs Hn; apply KEEP; [exact Hs | exact Hn] | lia | lia | lia | lia | exact Hhull ]
| intros a Ha; rewrite KEEP; [exact (Hslack a Ha) | lia | pose proof (Hwin (o + r) ltac:(lia)); lia]
| apply (cs_aro_kept B W mem (ms_mem ms1) (spZ regs - 16) HROM); [lia | intros a Ha Hn; apply KEEP; [exact Ha | lia]] ]
| cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in
let md2 := fresh "md2" in let HJ2 := fresh "HJ2" in let HP2 := fresh "HP2" in let Ha02 := fresh "Ha02" in
let Hfr2 := fresh "Hfr2" in let Hpres2 := fresh "Hpres2" in let Hpp := fresh "Hpp" in
intros W2 c2 _ Hpp; destruct Hpp as (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hfr2 & Hpres2);
let HS2 := fresh "HS2" in
jafter_call_keep_pi HS 200%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2;
lazymatch type of HS2 with ?Qk -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Qk);
[ apply Forall_cons; [|apply Forall_nil]; cbn [ms_mem restrict];
eapply region_kept_aview; [cbn [ew ewset]; exact Usp | intros a Ha; apply Hfr2; lia | exact Hpres2]
| specialize (HS2 HQ); clear HQ ] end;
rewrite <- restrict_mkst_fx in HS2;
rewrite Q1;
lazymatch type of HS2 with st_ok_pi _ _ ?E2 _ _ =>
let HEI2 := fresh "HEI" in let SHOK2 := fresh "SHOK" in
assert (HEI2 : img_env VAL A_LIM E2) by (apply img_env_havoc; [exact HEI1 | apply Nat.leb_le; reflexivity]);
assert (SHOK2 : sh_ok SEGS CBx [] E2 (mrestrict (w_H W) mem2)) by (apply Forall_nil);
assert (X10 : ew E2 10 = Z_to_bv 64 r) by (cbn [ew ewset havoc Nat.eqb Nat.ltb]; exact E10);
assert (X204 : ew E2 204 = Z_to_bv 64 r) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.sub nth map CLOB]; rewrite Ha02; reflexivity)
end;
clear HS HJ KEEP; try clear SHOK;
cs_go ]
end.
Qed.
End h.
End f.
End d.
