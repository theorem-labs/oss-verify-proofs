(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI1v UI4l UI21 UI2m UI3t UI5o UI5l YI6b UI5n UI20 UI1d UI2l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2o UI2p UI2q UI2r.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI2s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FL_DT    : Z := Eval vm_compute in (ubs0_A_flushFrame + 0x764).
Definition FL_DMRET : Z := Eval vm_compute in (ubs0_A_flushFrame + 0x77c).
Definition FL_DCL   : Z := Eval vm_compute in (ubs0_A_flushFrame + 0x7d0).
Definition FL_DCRET : Z := Eval vm_compute in (ubs0_A_flushFrame + 0x810).
Definition FL_DCX   : Z := Eval vm_compute in (ubs0_A_flushFrame + 0x820).
Definition dc_facts : list (nat * afact) :=
[ (24%nat, mkAF 1 65535 0); (21%nat, mkAF 1 65535 0); (23%nat, mkAF 0 65535 0); (8%nat, mkAF 4096 CEIL_MAX 0);
(22%nat, mkAF (2^64 - 1 - CEIL_MAX) (2^64 - 1 - 4096) 0); (19%nat, mkAF 0 4294967295 0); (9%nat, mkAF 4096 CEIL_MAX 0);
(25%nat, mkAF 0 4294967295 0); (27%nat, mkAF 1 65535 0); (32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 4096 CEIL_MAX 0) ].
Definition dc_conds : list acond := [ mkAC BC_GEU (SOff 32 0) (SOff 9 0); mkAC BC_GEU (SOff 33 0) (SOff 32 0) ].
Definition dc_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 9 0) (SOff 25 0), SOff 32 0); (SAlu ALU_ADD (SOff 23 0) (SOff 32 0), SOff 33 0) ].
Definition ss_dcl : sstate :=
mkSS FL_DCL (sr_set sr_atoms 26%bv (SLit 1)) [] None (mkFacts dc_facts dc_conds dc_alias).
Definition dt_stk : list YP09.chunk :=
fl_stk_saved 32 ++ [mkChunk 112 (CVal 8 (SOff 45 0)); mkChunk 120 (CVal 8 (SOff 46 0));
mkChunk 72 (CVal 8 (SOff 47 0)); mkChunk 80 (CVal 8 (SOff 48 0)); mkChunk 104 (CVal 8 (SOff 27 0));
mkChunk 96 (CVal 8 (SOff 53 0)); mkChunk 56 (CVal 8 (SOff 49 0)); mkChunk 32 (CVal 8 (SOff 50 0));
mkChunk 16 (CVal 8 (SOff 51 0)); mkChunk 24 (CVal 8 (SOff 52 0))].
Definition dt_facts : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (9%nat, mkAF 4096 CEIL_MAX 0); (27%nat, mkAF 1 65535 0);
(19%nat, mkAF 1 65535 0); (22%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65535 0); (53%nat, mkAF 0 65535 0) ].
Definition ss_dt : sstate :=
mkSS FL_DT sr_atoms [ YP09.mkRegion (Some 2%nat) 0 272 40 72 dt_stk ] None (mkFacts dt_facts [] []).
Definition dcx_stk : list YP09.chunk :=
fl_stk_saved 32 ++ [mkChunk 112 (CVal 8 (SOff 45 0)); mkChunk 120 (CVal 8 (SOff 46 0));
mkChunk 72 (CVal 8 (SOff 47 0)); mkChunk 80 (CVal 8 (SOff 48 0)); mkChunk 104 (CVal 8 (SOff 27 0));
mkChunk 96 (CVal 8 (SOff 53 0)); mkChunk 56 (CVal 8 (SOff 49 0)); mkChunk 32 (CVal 8 (SOff 50 0));
mkChunk 16 (CVal 8 (SOff 51 0)); mkChunk 24 (CVal 8 (SOff 52 0));
mkChunk 40 (CVal 8 (SOff 54 0)); mkChunk 48 (CVal 8 (SOff 55 0)); mkChunk 64 (CVal 8 (SOff 56 0))].
Definition ss_dcx : sstate :=
mkSS FL_DCX sr_atoms [ YP09.mkRegion (Some 2%nat) 0 272 0 0 dcx_stk ;
YP09.mkRegion (Some 46%nat) 20 24 0 0 [mkChunk 20 (CVal 4 (SOff 57 0))] ] None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (46%nat, mkAF 4096 (CEIL_MAX - 40) 3);
(57%nat, mkAF 0 4294967295 0) ] [] []).
Lemma land1_low32_dt : forall x, 0 <= x -> Z.land x 1 = Z.land (x mod 2 ^ 32) 1.
Proof using.
intros x Hx. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
destruct (Z.ltb_spec n 32) as [Hlt|Hge].
- rewrite <- (Z.mod_pow2_bits_low x 32 n) by lia. reflexivity.
- assert (Hmb : Z.testbit 1 n = false) by (apply Z.bits_above_log2; [lia|]; cbn; lia). rewrite Hmb, !Bool.andb_false_r. reflexivity.
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis RAWADDX : rawadd_specX API.
Section e.
Variables (fimg N pNew Nn W w h top left : Z).
Hypothesis Hfimg0 : 4096 <= fimg. Hypothesis Hfimg1 : fimg + N <= alloc_ceiling.
Hypothesis Hn0 : 4096 <= pNew. Hypothesis Hn1 : pNew + Nn <= alloc_ceiling.
Hypothesis Hw : 1 <= w. Hypothesis Hl0 : 0 <= left. Hypothesis Hlw : left + w <= W. Hypothesis HW : W <= 65535.
Hypothesis Hh : 1 <= h. Hypothesis Hh1 : h <= 65535. Hypothesis Ht0 : 0 <= top. Hypothesis Hth : (top + h) * W <= N.
Hypothesis HNn : Nn = h * w. Hypothesis HN : N < 2 ^ 32.
Hypothesis Dif : fimg + N <= pNew \/ pNew + Nn <= fimg.
Definition DC_KEPT : list reg := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 27]%bv.
Definition dcopy_post (k : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (c' : config) : Prop :=
exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_DCX) mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\
(forall x : word, bv_unsigned x < pNew + k * w \/ pNew + Nn <= bv_unsigned x -> mem' x = memc x) /\
(forall r j, k <= r < h -> 0 <= j < w -> mbyte ubs0segs mem' (pNew + r * w + j) = mbyte ubs0segs memc (fimg + left + (top + r) * W + j)) /\
(forall r : reg, In r DC_KEPT -> getr regs' r = getr regs r).
Lemma fl_dcopy : forall (n : nat) (k : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc,
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
In (pNew, Nn) (blocks Lc Ac) -> In (fimg, N) (blocks Lc Ac) ->
(forall blc i, In (pNew, Nn) blc -> 0 <= i < Nn -> wr_byte STK sp0 FP (blocks L A) blc (pNew + i)) ->
0 <= k -> k + Z.of_nat n = h -> (1 <= n)%nat ->
getr regs 24 = Z_to_bv 64 (Z.of_nat n) -> getr regs 26 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 w -> getr regs 23 = Z_to_bv 64 left ->
getr regs 8 = Z_to_bv 64 pNew -> getr regs 22 = Z_to_bv 64 (2 ^ 64 - 1 - pNew) -> getr regs 19 = Z_to_bv 64 (k * w) ->
getr regs 9 = Z_to_bv 64 fimg -> getr regs 25 = Z_to_bv 64 ((top + k) * W) -> getr regs 27 = Z_to_bv 64 W ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 FL_DCL) memc (seg_rom ubs0segs)) mdc) (dcopy_post k STK sp0 FP L A mem md Lc Ac mdc regs memc).
Proof using Dif HN HNn HW Hfimg0 Hfimg1 Hh1 Hl0 Hlw Hn0 Hn1 Ht0 Hth Hw IMG.
intros n. induction n as [|n IH]; intros k STK sp0 FP L A mem md Lc Ac mdc regs memc HJ Hnew Hfi Hwr Hk Hkn Hn G24 G26 G21 G23 G8 G22 G19 G9 G25 G27; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
assert (W1 : 1 <= W) by (clear - Hw Hl0 Hlw; lia).
assert (HkW : (top + k) * W + left + w <= N) by (clear - Hk Hkn Hn Hth Hlw Hl0 Hw W1 Ht0; nia).
assert (Hkw : k * w + w <= Nn) by (rewrite HNn; clear - Hk Hkn Hn Hw; nia).
assert (Hhw : h * w <= 65535 * 65535) by (clear - Hh1 Hw Hlw HW Hl0 Hk Hkn; nia).
set (E := Ereg regs (map (Z_to_bv 64) [fimg + (top + k) * W; fimg + left + (top + k) * W] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (E32 : ew E 32 = Z_to_bv 64 (fimg + (top + k) * W)) by (subst E; apply (Ereg_vals regs _ [] 0%nat); reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (fimg + left + (top + k) * W)) by (subst E; apply (Ereg_vals regs _ [] 1%nat); reflexivity).
assert (B25 : 0 <= (top + k) * W <= 4294967295) by (clear - Hk Ht0 W1 HkW HN Hl0 Hw; nia).
assert (B22 : 0 <= k * w /\ pNew + k * w <= alloc_ceiling) by (clear - Hk Hw Hkw Hn1; nia).
assert (B19 : fimg + left + (top + k) * W + w <= alloc_ceiling) by (clear - HkW Hfimg1 B25; lia).
assert (B19w : k * w + w <= 4294967295) by (clear - Hkw HNn Hhw; lia).
assert (HFA : atoms_ok E dc_facts).
{ unfold dc_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HE 24%nat 24%bv eq_refl), (HE 21%nat 21%bv eq_refl), (HE 23%nat 23%bv eq_refl), (HE 8%nat 8%bv eq_refl), (HE 22%nat 22%bv eq_refl),
(HE 19%nat 19%bv eq_refl), (HE 9%nat 9%bv eq_refl), (HE 25%nat 25%bv eq_refl), (HE 27%nat 27%bv eq_refl), E32, E33,
G24, G21, G23, G8, G22, G19, G9, G25, G27.
clear - Hk Hkn Hn Hw Hlw Hl0 HW Hn0 Hn1 Hfimg0 Hfimg1 B19 B19w Ht0 Hh1 Hac W1 B25 B22.
rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (U9 : U E (SOff 9 0) = fimg) by (apply U_atom; [rewrite (HE 9%nat 9%bv eq_refl); exact G9 | clear - Hfimg0 B19 B25 Hl0 Hw Hac; lia]).
assert (U32 : U E (SOff 32 0) = fimg + (top + k) * W) by (apply U_atom; [exact E32 | clear - Hfimg0 B19 B25 Hl0 Hw Hac; lia]).
assert (U33 : U E (SOff 33 0) = fimg + left + (top + k) * W) by (apply U_atom; [exact E33 | clear - Hfimg0 B19 B25 Hl0 Hw Hac; lia]).
assert (HCD : conds_ok E dc_conds).
{ unfold dc_conds. cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite !branch_geu_U, U9, U32, U33.
split; [|split; [|exact I]]; apply Bool.negb_true_iff, Z.ltb_ge; clear - B25 Hl0; lia. }
assert (HAL : alias_ok E dc_alias).
{ unfold dc_alias. cbn [alias_ok]. split; [|split; [|exact I]]; apply U_inj.
- rewrite U32. apply U_add_small; [exact U9 | apply U_atom; [rewrite (HE 25%nat 25%bv eq_refl); exact G25 | clear - B25; lia] | clear - Hfimg0; lia | clear - B25; lia | clear - Hfimg1 B19 B25 Hac Hl0 Hw; lia].
- rewrite U33. transitivity (left + (fimg + (top + k) * W)); [| clear; lia].
apply U_add_small; [apply U_atom; [rewrite (HE 23%nat 23%bv eq_refl); exact G23 | clear - Hl0 Hlw HW Hw; lia] | exact U32 | clear - Hl0; lia | clear - Hfimg0 B25; lia | clear - Hfimg1 B19 B25 Hac Hl0 Hw; lia]. }
assert (HS : st_ok ubs0segs E ss_dcl (mkst regs (Z_to_bv 64 FL_DCL) memc (seg_rom ubs0segs))).
{ unfold ss_dcl. apply entry_st_ok_full; [| vm_compute; reflexivity | constructor | exact I | split; [exact HFA | split; [exact HCD | exact HAL]]].
apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx | exact G26]. }
clear HFA HCD HAL.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_DCL) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_memcpy. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
assert (M0 : getr (ms_regs msc) 10 = Z_to_bv 64 (pNew + k * w));
[ rewrite (st_ok_reg ubs0segs Ec ssc msc 10%bv HS); eval_sr_get; apply denot_of_U';
apply U_add_small;
[ apply U_atom; [rewrite (HE 8%nat 8%bv eq_refl); exact G8 | clear - Hn0 B22 Hac; lia]
| apply U_atom; [rewrite (HE 19%nat 19%bv eq_refl); exact G19 | clear - B22 B19w Hw; lia]
| clear - Hn0; lia | clear - B22; lia | clear - B22 Hac; lia ] | ] end.
jreg HS (11%bv:reg) as M1. rewrite E33 in M1.
jreg HS (12%bv:reg) as M2. rewrite (HE 21%nat 21%bv eq_refl), G21 in M2.
jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ ubs0_memcpy) with (d := pNew + k * w) (src := fimg + left + (top + k) * W) (n := w);
[ exact HS | reflexivity | reflexivity | exact HJ | exact M0 | exact M1 | exact M2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | clear - Hw; lia | clear - Hn0 Hk Hw; nia | clear - Hfimg0 Hl0 Hk Ht0 W1; nia
| clear - Hn1 Hkw Hk Hw Hac; nia | clear - Hfimg1 HkW Hac; lia | | | | ].
- intros j Hj. cbn [ms_mem mkst]. unfold present. rewrite K1. replace (pNew + k * w + j) with (pNew + (k * w + j)) by lia.
apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pNew Nn (k * w + j) HHc Hnew ltac:(clear - Hj Hkw Hk Hw; nia))).
- intros j Hj. apply (present_mbyte ubs0_msyms). unfold present. rewrite K1. replace (fimg + left + (top + k) * W + j) with (fimg + ((top + k) * W + left + j)) by lia.
apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N ((top + k) * W + left + j) HHc Hfi ltac:(clear - Hj HkW Hk Ht0 W1 Hl0; nia))).
- clear - Dif HkW Hkw B22 B25 Hl0. lia.
- intros a Ha. replace a with (pNew + (a - pNew)) by lia. apply (Hwr (blocks Lc Ac) (a - pNew) Hnew). clear - Ha Hkw Hk Hw; nia. }
cbv beta. intros c' (regs5 & mem5 & -> & HJ5 & Hd10 & Hfr5 & Hout5 & Hgr5 & Hcpy5). clear HJ.
cbn [ms_regs ms_mem mkst] in Hfr5, Hout5, Hgr5, Hcpy5, HJ5.
jafter_stretch_keep HS 34%nat regs5 mem5 MEMCPY_CLOB FL_DCRET ([] : list nat) HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr5 : P); [| assert (HKm5 : Q); [| specialize (HS2 HKr5 HKm5); clear HKr5 HKm5]] end.
{ intros rr Hrr. apply Hfr5. exact Hrr. }
{ constructor. }
clear HS. rename HS2 into HS.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 FL_DCRET) mem5 (seg_rom ubs0segs))) in HJ5.
assert (K5 : forall x : word, bv_unsigned x < pNew + k * w \/ pNew + Nn <= bv_unsigned x -> mem5 x = memc x).
{ intros x Hx. rewrite (Hout5 x) by (clear - Hx Hkw Hk Hw; nia). apply K1. }
set (E2 := havoc E 34 (map (getr regs5) MEMCPY_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
jrun LAWS ubs0tbl_ok HS HJ5. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K6 : forall x, ms_mem ms0 x = mem5 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch ubs0tbl HS.
-
rewrite branch_ne_U, U_lit in Hc by lia.
rewrite (U_atom_off _ 24 (Z.of_nat (Datatypes.S n)) (-1)) in Hc by first [subst E2; ew_havocA; rewrite (HE 24%nat 24%bv eq_refl); exact G24 | lia].
assert (Hm1 : (1 <= n)%nat) by (destruct (Z.eqb_spec (Z.of_nat (Datatypes.S n) + -1) 0); [discriminate Hc | lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ5 FL_DCL. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K7 : forall x, ms_mem ms1 x = mem5 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K6. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ DC_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (k + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ HJ5 Hnew Hfi Hwr ltac:(clear - Hk; lia) ltac:(clear - Hkn; lia) Hm1).
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 24%nat 24%bv eq_refl), G24, unsigned_lit_small by lia; f_equal; lia).
- reg_nowF HS ltac:(reflexivity).
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 22%bv ltac:(cbv; auto 20)). exact G22.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 19%bv HS) end. eval_sr_get. apply denot_of_U'.
rewrite (U_add_small E2 _ _ (k * w) w); [clear; nia | | | clear - B22; lia | clear - Hw; lia | clear - B19w; lia].
+ apply U_atom; [subst E2; ew_havocA; rewrite (HE 19%nat 19%bv eq_refl); exact G19 | clear - B22 B19w Hw; lia].
+ apply U_atom; [subst E2; ew_havocA; rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - Hw Hlw HW Hl0; lia].
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- assert (B25' : (top + k) * W + W = (top + (k + 1)) * W /\ (top + (k + 1)) * W <= N) by (clear - Hk Hkn Hm1 Hth W1 Ht0; nia).
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 25%bv HS) end. eval_sr_get. apply denot_of_U'.
rewrite (U_add_small E2 _ _ ((top + k) * W) W); [clear - B25'; lia | | | clear - B25; lia | clear - W1; lia | clear - B25 HW; lia].
+ apply U_atom; [subst E2; ew_havocA; rewrite (HE 25%nat 25%bv eq_refl); exact G25 | clear - B25; lia].
+ apply U_atom; [subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - W1 HW; lia].
- rewrite (HKR 27%bv ltac:(cbv; auto 20)). exact G27. }
cbv beta. intros c' (regs' & mem' & -> & HJ' & K' & C' & HK'). exists regs', mem'.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros x Hx; rewrite (K' x) by (clear - Hx Hk Hw; nia); rewrite K7; apply (K5 x Hx)|].
split.
{ intros r j Hr Hj. destruct (Z.eq_dec r k) as [-> | Hrk].
-
transitivity (mbyte ubs0segs (ms_mem ms1) (pNew + k * w + j)).
{ unfold mbyte. rewrite (K' (Z_to_bv 64 (pNew + k * w + j))) by (rewrite unsigned_lit_small by (clear - Hj Hk Hkw Hn0 Hn1 Hac; nia); left; clear - Hj; nia). reflexivity. }
rewrite (mbyte_of_eq _ _ _ _ K7), (Hcpy5 j Hj). apply mbyte_of_eq. exact K1.
- rewrite (C' r j ltac:(clear - Hr Hrk; lia) Hj). unfold mbyte. rewrite K7, K5; [reflexivity|].
rewrite unsigned_lit_small by (clear - Hr Hj Hk Hfimg0 Hfimg1 Hth Hlw Hl0 Ht0 Hac HW W1 Hkn; nia).
clear - Dif Hr Hj Hk Hkn Hth Hlw Hl0 Ht0 W1 HNn Hw. nia. }
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
-
rewrite branch_ne_U, U_lit in Hc by lia.
rewrite (U_atom_off _ 24 (Z.of_nat (Datatypes.S n)) (-1)) in Hc by first [subst E2; ew_havocA; rewrite (HE 24%nat 24%bv eq_refl); exact G24 | lia].
assert (Hm : n = 0%nat) by (destruct (Z.eqb_spec (Z.of_nat (Datatypes.S n) + -1) 0); [lia | discriminate Hc]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ5 FL_DCX. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K7 : forall x, ms_mem ms1 x = mem5 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K6. }
clear HF HG.
apply SR_ret. exists (ms_regs ms1), (ms_mem ms1).
split; [rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl); reflexivity|]. split; [exact HJ5|].
split; [intros x Hx; rewrite K7; apply (K5 x Hx)|].
split.
{ intros r j Hr Hj. assert (Hrk : r = k) by (clear - Hr Hkn Hn Hm; lia). subst r.
rewrite (mbyte_of_eq _ _ _ _ K7), (Hcpy5 j Hj). apply mbyte_of_eq. exact K1. }
intros rr Hrr. lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
exact (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ DC_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity) rr Hrr) end.
Qed.
End e.
Lemma dt_window : forall (memc mem' : word -> option byte) (fimg pNew W : Z) (HH : nat) (PIX : list Z) (w h top lf : Z),
garr8 ubs0segs memc fimg PIX -> 1 <= W -> length PIX = (Z.to_nat W * HH)%nat ->
1 <= w -> 0 <= lf -> lf + w <= W -> 1 <= h -> 0 <= top -> top + h <= Z.of_nat HH ->
(forall r j, 0 <= r < h -> 0 <= j < w -> mbyte ubs0segs mem' (pNew + r * w + j) = mbyte ubs0segs memc (fimg + lf + (top + r) * W + j)) ->
garr8 ubs0segs mem' pNew (YO07.window W PIX w h top lf) /\ Z.of_nat (length (YO07.window W PIX w h top lf)) = w * h.
Proof using.
intros memc mem' fimg pNew W HH PIX w h top lf Himg HW Hlen Hw Hl0 Hlw Hh Ht0 Hth Hc.
destruct (window_spec (Z.to_nat W) HH PIX w h top lf ltac:(lia) Hlen Hw Hl0 ltac:(rewrite Z2Nat.id by lia; exact Hlw) Hh Ht0 Hth) as [Hl Hnth].
rewrite Z2Nat.id in Hnth by lia. rewrite Z2Nat.id in Hl by lia.
split; [| rewrite Hl; lia].
apply garr8_intro. intros jn Hjn. rewrite Hl in Hjn.
assert (Hk : 0 <= Z.of_nat jn < w * h) by lia.
replace jn with (Z.to_nat (Z.of_nat jn)) at 2 3 4 by lia.
rewrite (Hnth (Z.of_nat jn) Hk).
assert (Hr : 0 <= Z.of_nat jn / w < h) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hj : 0 <= Z.of_nat jn mod w < w) by (apply Z.mod_pos_bound; lia).
assert (Hdm : Z.of_nat jn = w * (Z.of_nat jn / w) + Z.of_nat jn mod w) by (apply Z.div_mod; lia).
replace (pNew + Z.of_nat jn) with (pNew + (Z.of_nat jn / w) * w + Z.of_nat jn mod w) by lia.
rewrite (Hc (Z.of_nat jn / w) (Z.of_nat jn mod w) Hr Hj).
assert (Hidx : 0 <= (top + Z.of_nat jn / w) * W + lf + Z.of_nat jn mod w /\ (Z.to_nat ((top + Z.of_nat jn / w) * W + lf + Z.of_nat jn mod w) < length PIX)%nat).
{ split; [nia|]. rewrite Hlen. assert ((top + Z.of_nat jn / w) * W + lf + Z.of_nat jn mod w < W * Z.of_nat HH) by nia. nia. }
replace (fimg + lf + (top + Z.of_nat jn / w) * W + Z.of_nat jn mod w) with (fimg + Z.of_nat (Z.to_nat ((top + Z.of_nat jn / w) * W + lf + Z.of_nat jn mod w))) by lia.
split; [apply (garr8_mbyte ubs0segs memc fimg PIX); [exact Himg | exact (proj2 Hidx)] | ].
exact (proj2 (Himg (Z.to_nat ((top + Z.of_nat jn / w) * W + lf + Z.of_nat jn mod w)) (proj2 Hidx))).
Qed.
Definition dt_pre L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st) (gen1 : Z)
(rest FP : list (Z * Z)) (tv np u23 u24 u25 w h top left : Z) : Prop :=
let sp0 := spZ regs0 in
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc /\ st_init_done Ac = true /\
YK0s.ret_ok (getr regs0 1) /\ sp0 mod 16 = 0 /\ getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) /\
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) /\ cgif_wf s N /\ (i = 1%nat \/ i = 2%nat) /\ nth_error (cg_frames s) i = Some (Some f) /\
nth_error (cg_frames s) (i - 1) = Some (Some b) /\
fl_fp FP s f /\
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ rest) /\ 0 <= tv < 2 ^ 64 /\ 0 <= np <= 65535 /\
0 <= u23 < 2 ^ 64 /\ 0 <= u24 < 2 ^ 64 /\ 0 <= u25 < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W s /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H s /\
fl_saved_ok memc sp0 regs0 /\
word_mem ubs0segs memc (sp0 - 272 + 112) g /\ word_mem ubs0segs memc (sp0 - 272 + 120) (fr_ptr f) /\
word_mem ubs0segs memc (sp0 - 272 + 72) tv /\ word_mem ubs0segs memc (sp0 - 272 + 80) (cg_H s) /\
word_mem ubs0segs memc (sp0 - 272 + 104) (cg_W s) /\ word_mem ubs0segs memc (sp0 - 272 + 96) top /\
word_mem ubs0segs memc (sp0 - 272 + 56) (Z.land (fr_attr f) 1) /\
word_mem ubs0segs memc (sp0 - 272 + 32) u23 /\ word_mem ubs0segs memc (sp0 - 272 + 16) u24 /\
word_mem ubs0segs memc (sp0 - 272 + 24) u25 /\
getr regs1 2 = Z_to_bv 64 (sp0 - 272) /\ getr regs1 9 = Z_to_bv 64 (fr_img f) /\
getr regs1 18 = Z_to_bv 64 (fr_ptr b) /\ getr regs1 27 = Z_to_bv 64 (cg_W s) /\ getr regs1 20 = Z_to_bv 64 np /\
getr regs1 26 = Z_to_bv 64 left /\ getr regs1 19 = Z_to_bv 64 w /\ getr regs1 22 = Z_to_bv 64 h /\
fl_untouched regs0 regs1.
Lemma fl_dt :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f b : frame_st)
(rest FP FPw : list (Z * Z)) (tv np u23 u24 u25 w h top left : Z)
(S GPAL : list Z) (cur befr : YO07.frame) (brb bc : rbound),
let G := gcfg_of s GPAL in
let gen1 := fl_gen3 G cur (Some befr) in
dt_pre L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b gen1 rest FP tv np u23 u24 u25 w h top left ->
fl_sink g s N rest FP FPw S L A mem md (spZ regs0) ->
fl_vals memc s N f (Some b) GPAL cur (Some befr) ->
u23 = fr_disp f -> u24 = Z.land (fr_attr f) 4 -> u25 = (if fl_hasAlpha G cur then 1 else 0) ->
np = fl_npal G cur -> tv mod 256 = YO07.f_trans cur ->
YO07.flag (fl_gen3 G cur (Some befr)) 2 = true -> fl_dims G cur (Some befr) = (w, h, top, left) ->
res_ok Ac bc -> room bc (h * w) -> rawadd_room (rb_malloc bc (h * w)) (h * w) ->
rb_le (rb_free (rawadd_rb (rb_malloc bc (h * w))) (h * w)) (flush_rb brb) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_DT) memc (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur (Some befr) brb L A mem md).
Proof using IMG RAWADDX.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f b rest FP FPw tv np u23 u24 u25 w h top left S GPAL cur befr brb bc G gen1
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hi & Hf & Hb & HFP & HB & Htv & Hnp & Hu23 & Hu24 & Hu25
& Hw & Hl0 & Hlw & Hh & Ht0 & Hth & HSV & W112 & W120 & W72 & W80 & W104 & W96 & W56 & W32 & W16 & W24
& G2 & G9 & G18 & G27 & G20 & G26 & G19 & G22 & G3 & G4)
HSINK HVALS Xu23 Xu24 Xu25 Xnp Xtv0 XG2 XDA HRq HRM HRR HRB.
assert (FLD : fl_w G cur (Some befr) = w /\ fl_h G cur (Some befr) = h /\ fl_top G cur (Some befr) = top /\ fl_left G cur (Some befr) = left /\
fl_tmp G cur (Some befr) = YO07.window (cg_W s) (YO07.f_img cur) w h top left).
{ unfold fl_tmp, fl_w, fl_h, fl_top, fl_left. rewrite XG2, XDA. repeat split; reflexivity. }
destruct FLD as (Fw & Fh & Ftop & Fleft & Ftmp). unfold G in Ftmp.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity. assert (ASv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & Hgone & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & Hfwf).
set (sp0 := spZ regs0) in *.
set (s1 := flush_upd s i gen1 (rw_cur s)) in Hat. set (f1 := set_fr_gen f gen1).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hbin : In (Some b) (cg_frames s)) by (eapply nth_error_In; exact Hb).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hf1in : In (Some f1) (cg_frames s1)) by (rewrite Hfr1; eapply nth_error_In; apply nth_error_list_set_same; exact Hilt).
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg). destruct (Hfgeom b Hbin) as (Hq0 & Hq1 & Hqg).
destruct (fl_img_geom0 API Lc Ac memc mdc g s N _ f HH0 HB Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
pose proof (Rf 2%nat (fr_attr f) eq_refl) as Rfattr. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfattr.
assert (Himgfin : In (fr_img f, N) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. left. apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | right; left; reflexivity]. }
set (u := Z.land (fr_attr f) 1) in *. assert (Ru : 0 <= u <= 1) by (subst u; destruct (land1_cases (fr_attr f) ltac:(clear - Rfattr; lia)); lia).
assert (Hwh : 1 <= h * w /\ h * w <= N) by (rewrite HN; clear - Hw Hlw Hl0 Hh Hth Ht0; nia).
set (vals := fl_saved_vals regs0 ++ [g; fr_ptr f; tv; cg_H s; u; u23; u24; u25; top]).
set (E := Ereg regs1 (map (Z_to_bv 64) vals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HA : forall j v, nth_error vals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HK : forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. apply HA. subst vals. rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate. }
assert (HV : forall n j v, n = (45 + j)%nat -> nth_error [g; fr_ptr f; tv; cg_H s; u; u23; u24; u25; top] j = Some v -> ew E n = Z_to_bv 64 v).
{ intros n j v -> Hj. replace (45 + j)%nat with (32 + (13 + j))%nat by lia. apply HA. subst vals. rewrite nth_error_app2 by (cbn; lia). replace (13 + j - length (fl_saved_vals regs0))%nat with j by (cbn; lia). exact Hj. }
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 272 40 72 dt_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
unfold dt_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK j v Hj)|].
repeat (apply Forall_cons); [..|apply Forall_nil].
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, (HV 45%nat 0%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hg0 Hg1 Hac HGSv; lia | cbn; lia | apply val_mem_word_mem; exact W112].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_ptr f)); [cbn [sv_denot]; rewrite Z.add_0_r, (HV 46%nat 1%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hp0 Hp1 Hac HFRv; lia | cbn; lia | apply val_mem_word_mem; exact W120].
- eapply (chunk_ok_val _ _ _ _ _ _ _ tv); [cbn [sv_denot]; rewrite Z.add_0_r, (HV 47%nat 2%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; exact Htv | cbn; lia | apply val_mem_word_mem; exact W72].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_H s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HV 48%nat 3%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - RH; lia | cbn; lia | apply val_mem_word_mem; exact W80].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_W s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - RW; lia | cbn; lia | apply val_mem_word_mem; exact W104].
- eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, (HV 53%nat 8%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Ht0 Hth Hh RH; lia | cbn; lia | apply val_mem_word_mem; exact W96].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u); [cbn [sv_denot]; rewrite Z.add_0_r, (HV 49%nat 4%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Ru; lia | cbn; lia | apply val_mem_word_mem; exact W56].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u23); [cbn [sv_denot]; rewrite Z.add_0_r, (HV 50%nat 5%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; exact Hu23 | cbn; lia | apply val_mem_word_mem; exact W32].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u24); [cbn [sv_denot]; rewrite Z.add_0_r, (HV 51%nat 6%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; exact Hu24 | cbn; lia | apply val_mem_word_mem; exact W16].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u25); [cbn [sv_denot]; rewrite Z.add_0_r, (HV 52%nat 7%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; exact Hu25 | cbn; lia | apply val_mem_word_mem; exact W24]. }
assert (HFA : atoms_ok E dt_facts).
{ unfold dt_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, (HE 9%nat 9%bv eq_refl), (HE 27%nat 27%bv eq_refl), (HE 19%nat 19%bv eq_refl), (HE 22%nat 22%bv eq_refl),
(HE 26%nat 26%bv eq_refl), (HV 53%nat 8%nat _ eq_refl eq_refl), G9, G27, G19, G22, G26.
clear - Hceil Hsp063 Hal16 Hw Hl0 Hlw Hh Ht0 Hth RW RH Him0 Him1 Hwh HNle HFSv Hac.
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; try (replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16). }
assert (HS : st_ok ubs0segs E ss_dt (mkst regs1 (Z_to_bv 64 FL_DT) memc (seg_rom ubs0segs))).
{ unfold ss_dt. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; exact I]]. }
clear HR0 HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_DT) memc (seg_rom ubs0segs))) in HJ.
assert (WR : forall E0 cs rs blc, bv_unsigned (ew E0 2) = sp0 - 272 -> Forall (fun r => r_whi r <= r_wlo r) rs ->
wr_ok E0 (YP09.mkRegion (Some 2%nat) 0 272 40 72 cs :: rs) FLUSH_STK sp0 FP (blocks L A) blc).
{ intros E0 cs rs blc H2 Hrs. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
induction Hrs as [|r rs' Hr Hrs' IHrs]; [apply wr_ok_nil | apply wr_ok_cons_ro; [exact Hr | exact IHrs]]. }
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc. { apply WR; [exact HU2 | constructor]. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 + 40 <= a < sp0 - 272 + 72) -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs memc a).
{ intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?HU2; lia |]); destruct Hr. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
assert (Hm10 : getr (ms_regs msc) 10 = Z_to_bv 64 (h * w));
[ rewrite (st_ok_reg ubs0segs Ec ssc msc 10%bv HS); eval_sr_get; apply denot_of_U'; rewrite Z.mul_comm;
apply (U_mul_small' E _ _ w h);
[ rewrite U_and_lit by (clear; lia); rewrite (U_atom _ 19 w ltac:(rewrite (HE 19%nat 19%bv eq_refl); exact G19)) by (clear - Hw Hlw Hl0 RW; lia); apply land_ffff; clear - Hw Hlw Hl0 RW; lia
| rewrite U_and_lit by (clear; lia); rewrite (U_atom _ 22 h ltac:(rewrite (HE 22%nat 22%bv eq_refl); exact G22)) by (clear - Hh Hth Ht0 RH; lia); apply land_ffff; clear - Hh Hth Ht0 RH; lia
| clear - Hw; lia | clear - Hh; lia | clear - Hwh HNle; lia ] | ] end.
jreg HS (2%bv:reg) as Hm2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hm2.
jreg HS (4%bv:reg) as Hm4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hm4. jreg HS (1%bv:reg) as Hmra.
assert (Hspm : (sp0 - 272) mod 16 = 0) by (replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := h * w) (spc := sp0 - 272);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hm10 | exact HRq | exact HRM
| exact Hm2 | clear - Hceil Hsp063 HFSv Hac; lia | exact Hspm | clear - HFSv ASv; lia | clear; lia | exact Hm4 | exact Hmra | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & pNew & -> & HJ3 & Hid3 & HP3 & Hi10 & Hres & Hkeep3 & Hhi3 & HRq3). clear HJ.
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
jafter_call_keep HS 54%nat regs3 mem3 HP3 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi3 | lia | lia | clear - HFSv ASv; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq58. cbn [ms_regs mkst] in Hq58. rewrite Hi10 in Hq58. symmetry in Hq58.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ((exists bb m, In (bb, m) (blocks Lc Ac) /\ bb <= a < bb + m) \/ sp0 - 272 <= a) -> ~ (sp0 - 272 + 40 <= a < sp0 - 272 + 72) ->
mbyte ubs0segs mem3 a = mbyte ubs0segs memc a).
{ intros a Ha Hwa Hna. rewrite <- (K1 a Ha Hna). destruct Hwa as [(bb & m & Hbm & Hab) | Hwa].
- replace a with (bb + (a - bb)) by lia. apply (Hkeep3 bb m (a - bb) Hbm). lia.
- apply (proj1 (Hhi3 a ltac:(clear - Ha Hwa Hceil HFSv Hac; lia) ltac:(clear - Hwa Hna ASv; lia))). }
assert (KBof : forall m, (forall a, 0 <= a < 2 ^ 64 -> ((exists bb mm, In (bb, mm) (blocks Lc Ac) /\ bb <= a < bb + mm) \/ sp0 - 272 <= a) -> ~ (sp0 - 272 + 40 <= a < sp0 - 272 + 72) -> mbyte ubs0segs m a = mbyte ubs0segs memc a) ->
forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> mbyte ubs0segs m (bb + k) = mbyte ubs0segs memc (bb + k)).
{ intros m K bb nn k Hbn Hk. assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1].
apply K; [clear - R0 R1 Hk Hac; lia | left; exists bb, nn; split; [exact Hbn' | clear - Hk; lia] | clear - R0 R1 Hk Hceil HFSv Hac; lia]. }
assert (CGAT : forall m, (forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> mbyte ubs0segs m (bb + k) = mbyte ubs0segs memc (bb + k)) ->
cgif_at m g (flush_upd s i gen1 (rw_cur s))).
{ intros m KB. split; [| split].
- rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s)). eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KB g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia]].
- change (cg_raw (flush_upd s i gen1 (rw_cur s))) with (cg_raw s).
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply (KB (cg_raw s) RAW_SIZE k); [right; left; reflexivity | clear - Hk HRWv; lia]].
- intros x Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i gen1 (rw_cur s) f x Hf Hx) as [-> | [Hin _]].
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB (fr_ptr f) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif0 g s N f _ _ Hfin). left. reflexivity.
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply (KB (fr_ptr x) FRAME_SIZE k); [| clear - Hk HFRv; lia]].
apply (frame_blocks_in_cgif0 g s N x _ _ Hin). left. reflexivity. }
destruct Hres as (Hnz & Hi16 & (b1 & b2 & Hbl3 & Hblc3) & Hwr3).
-
set (Nn := h * w) in *.
assert (Hnewin : In (pNew, Nn) (blocks L3 A3)) by (rewrite Hbl3; apply in_app_iff; right; left; reflexivity).
destruct (blocks_range _ _ LAWS L3 A3 mem3 md3 pNew Nn HH3 Hnewin) as [Hn0 Hn1].
assert (Hsub3 : forall bb, In bb (blocks Lc Ac) -> In bb (blocks L3 A3)).
{ intros bb Hbb. rewrite Hbl3. rewrite Hblc3 in Hbb. apply in_app_iff in Hbb. apply in_app_iff. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; right; exact Hbb]. }
assert (Hsepn : forall y, In y (blocks Lc Ac) -> pNew + Nn <= fst y \/ fst y + snd y <= pNew).
{ intros y Hy. apply (heap_sep _ _ LAWS L3 A3 mem3 md3 b1 (pNew, Nn) b2 y HH3 Hbl3). rewrite <- Hblc3. exact Hy. }
assert (Hnew_notc : ~ In (pNew, Nn) (blocks Lc Ac)) by (rewrite Hblc3; exact (fresh_not_in API L3 A3 mem3 md3 b1 b2 pNew Nn HH3 Hbl3 ltac:(clear - Hwh; lia))).
assert (Hnew_fp : In (pNew, Nn) (blocks L A) -> forall k, 0 <= k < Nn -> inFP FP (pNew + k)) by (intros Hin k Hk; exact (Hgone pNew Nn k Hin Hnew_notc Hk)).
assert (HB3 : Permutation (blocks L3 A3) ((pNew, Nn) :: cgif_blocks0 g s N ++ rest)).
{ rewrite Hbl3. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc3. exact HB. }
add_fact HS 58%nat (mkAF 4096 CEIL_MAX 4).
2:{ rewrite Hq58, unsigned_lit_small by lia. change (2 ^ 4) with 16. clear - Hn0 Hn1 Hi16 Hac Hwh. repeat split; lia. }
jrun_to LAWS ubs0tbl_ok HS HJ3 FL_DCL. { apply WR; [ew_havocA; exact HU2 | constructor]. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 + 40 <= a < sp0 - 272 + 72) -> mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs mem3 a).
{ intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havocA; rewrite ?HU2; lia |]); destruct Hr. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ec ?ssx _ =>
pose proof (st_region_chunks ubs0segs Ec ssx ms0 0 _ 2%nat (sp0 - 272) HS eq_refl eq_refl ltac:(ew_havocA; exact HU2)) as Hcs end.
cbn [r_chunks] in Hcs.
assert (W40 : word_mem ubs0segs (ms_mem ms0) (sp0 - 272 + 40) w).
{ apply (chunk_word _ _ _ 40 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 40 (CVal 8 (SOff 19 0))) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))));
[cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 19%nat 19%bv eq_refl), G19, Z_to_bv_bv_unsigned; reflexivity | clear - Hw Hlw Hl0 RW; lia]. }
assert (W48 : word_mem ubs0segs (ms_mem ms0) (sp0 - 272 + 48) left).
{ apply (chunk_word _ _ _ 48 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 48 (CVal 8 (SOff 26 0))) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))));
[cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity | clear - Hl0 Hlw Hw RW; lia]. }
assert (W64 : word_mem ubs0segs (ms_mem ms0) (sp0 - 272 + 64) h).
{ apply (chunk_word _ _ _ 64 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 64 (CVal 8 (SOff 22 0))) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))));
[cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE 22%nat 22%bv eq_refl), G22, Z_to_bv_bv_unsigned; reflexivity | clear - Ht0 Hth Hh RH; lia]. }
assert (W56' : word_mem ubs0segs (ms_mem ms0) (sp0 - 272 + 56) u).
{ apply (chunk_word _ _ _ 56 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 56 (CVal 8 (SOff 49 0))) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))));
[cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HV 49%nat 4%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | clear - Ru; lia]. }
clear Hcs.
lazymatch type of HS with st_ok _ ?Ec ?ssx ?msx =>
assert (RG : forall (r : reg) n wv, sr_get (ss_regs ssx) r = SOff n 0 -> ew Ec n = wv -> getr (ms_regs msx) r = wv)
by (intros r n wv Hr Hv; rewrite (st_ok_reg ubs0segs Ec ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hv);
assert (Q24 : getr (ms_regs msx) 24 = Z_to_bv 64 (Z.of_nat (Z.to_nat h)));
[ rewrite (st_ok_reg ubs0segs Ec ssx msx 24%bv HS); eval_sr_get; apply denot_of_U'; rewrite U_and_lit by (clear; lia);
rewrite (U_atom Ec 22 h ltac:(ew_havocA; rewrite (HE 22%nat 22%bv eq_refl); exact G22)) by (clear - Hh Hth Ht0 RH; lia); rewrite land_ffff by (clear - Hh Hth Ht0 RH; lia); clear - Hh; lia | ];
assert (Q26 : getr (ms_regs msx) 26 = Z_to_bv 64 1) by (rewrite (st_ok_reg ubs0segs Ec ssx msx 26%bv HS); reflexivity);
assert (Q21 : getr (ms_regs msx) 21 = Z_to_bv 64 w);
[ rewrite (st_ok_reg ubs0segs Ec ssx msx 21%bv HS); eval_sr_get; apply denot_of_U'; rewrite U_and_lit by (clear; lia);
rewrite (U_atom Ec 19 w ltac:(ew_havocA; rewrite (HE 19%nat 19%bv eq_refl); exact G19)) by (clear - Hw Hlw Hl0 RW; lia); apply land_ffff; clear - Hw Hlw Hl0 RW; lia | ];
assert (Q23 : getr (ms_regs msx) 23 = Z_to_bv 64 left);
[ rewrite (st_ok_reg ubs0segs Ec ssx msx 23%bv HS); eval_sr_get; apply denot_of_U'; rewrite U_and_lit by (clear; lia);
rewrite (U_atom Ec 26 left ltac:(ew_havocA; rewrite (HE 26%nat 26%bv eq_refl); exact G26)) by (clear - Hw Hlw Hl0 RW; lia); apply land_ffff; clear - Hw Hlw Hl0 RW; lia | ];
assert (Q22 : getr (ms_regs msx) 22 = Z_to_bv 64 (2 ^ 64 - 1 - pNew));
[ rewrite (st_ok_reg ubs0segs Ec ssx msx 22%bv HS); eval_sr_get; apply denot_of_U';
apply (U_not Ec 58 pNew); [exact Hq58 | clear - Hn0 Hn1 Hac Hwh; lia] | ];
assert (Q19 : getr (ms_regs msx) 19 = Z_to_bv 64 (0 * w)) by (rewrite (st_ok_reg ubs0segs Ec ssx msx 19%bv HS); reflexivity);
assert (Q25 : getr (ms_regs msx) 25 = Z_to_bv 64 ((top + 0) * cg_W s));
[ rewrite (st_ok_reg ubs0segs Ec ssx msx 25%bv HS); eval_sr_get; apply denot_of_U';
rewrite Z.add_0_r; apply (U_mul_small' _ _ _ top (cg_W s));
[ rewrite U_and_lit by (clear; lia); rewrite (U_atom Ec 53 top ltac:(ew_havocA; exact (HV 53%nat 8%nat _ eq_refl eq_refl))) by (clear - Ht0 Hth Hh RH; lia); apply land_ffff; clear - Ht0 Hth Hh RH; lia
| apply (U_atom _ 27); [ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - RW; lia]
| exact Ht0 | clear - RW; lia | clear - Ht0 Hth Hh RW RH; nia ] | ] end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_dcopy (fr_img f) N pNew Nn (cg_W s) w h top left Him0 Him1 Hn0 Hn1 Hw Hl0 Hlw ltac:(clear - RW; lia) ltac:(clear - Hh Hth Ht0 RH; lia) Ht0
ltac:(rewrite HN; clear - Hth HW1; nia) eq_refl ltac:(clear - HNle; lia) ltac:(pose proof (Hsepn _ Himgfin) as X; cbn [fst snd] in X; clear - X; lia)
(Z.to_nat h) 0 FLUSH_STK sp0 FP L A mem md L3 A3 md3 _ _ HJ3 Hnewin (Hsub3 _ Himgfin));
[ intros blc k Hblc Hk; exact (Hwr3 blc k Hblc Hk) | clear; lia | clear - Hh; lia | clear - Hh; lia
| exact Q24 | exact Q26 | exact Q21 | exact Q23 | apply (RG 8%bv 58%nat); [reflexivity | exact Hq58] | exact Q22 | exact Q19
| apply (RG 9%bv 9%nat); [reflexivity | ew_havocA; rewrite (HE 9%nat 9%bv eq_refl); exact G9] | exact Q25
| apply (RG 27%bv 27%nat); [reflexivity | ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27] ]. all: fail. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & K4' & C4 & HK4).
assert (K4 : forall x : word, bv_unsigned x < pNew \/ pNew + Nn <= bv_unsigned x -> mem4 x = ms_mem ms0 x) by (intros x Hx; apply K4'; clear - Hx; lia). clear K4'.
assert (KS4 : forall a, sp0 - 272 <= a < sp0 -> mbyte ubs0segs mem4 a = mbyte ubs0segs (ms_mem ms0) a).
{ intros a Ha. unfold mbyte. rewrite (K4 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by (clear - Ha Hceil Hsp063 HFSv Hac; lia); clear - Ha Hn1 Hceil HFSv Hac; lia). reflexivity. }
assert (KS0 : forall a, sp0 - 272 <= a < sp0 -> ~ (sp0 - 272 + 40 <= a < sp0 - 272 + 72) -> mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs memc a).
{ intros a Ha Hna. rewrite (K3 a ltac:(clear - Ha Hceil Hsp063 HFSv Hac; lia) Hna). apply K2; [clear - Ha Hceil Hsp063 HFSv Hac; lia | right; clear - Ha; lia | exact Hna]. }
assert (WK : forall a v, 0 <= a -> a + 8 <= 272 -> (a + 8 <= 40 \/ 72 <= a) -> word_mem ubs0segs memc (sp0 - 272 + a) v -> word_mem ubs0segs mem4 (sp0 - 272 + a) v).
{ intros a v Ha0 Ha1 Hna Hv k Hk. rewrite <- (Hv k Hk). rewrite KS4 by (clear - Ha0 Ha1 Hk; lia). apply KS0; clear - Ha0 Ha1 Hna Hk; lia. }
assert (WK0 : forall a v, 0 <= a -> a + 8 <= 272 -> word_mem ubs0segs (ms_mem ms0) (sp0 - 272 + a) v -> word_mem ubs0segs mem4 (sp0 - 272 + a) v).
{ intros a v Ha0 Ha1 Hv k Hk. rewrite <- (Hv k Hk). apply KS4. clear - Ha0 Ha1 Hk; lia. }
assert (HSV4 : fl_saved_ok mem4 sp0 regs0).
{ apply (fl_saved_ok_kept memc); [exact HSV|]. intros a Ha. rewrite KS4 by (clear - Ha; lia). apply KS0; clear - Ha; lia. }
assert (KB4' : forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> mbyte ubs0segs mem4 (bb + k) = mbyte ubs0segs memc (bb + k)).
{ intros bb nn k Hbn Hk.
assert (Hbn' : In (bb, nn) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc bb nn HH0 Hbn') as [R0 R1]. pose proof (Hsepn _ Hbn') as X. cbn [fst snd] in X.
unfold mbyte at 1. rewrite (K4 (Z_to_bv 64 (bb + k))) by (rewrite unsigned_lit_small by (clear - R0 R1 Hk Hac; lia); clear - X Hk; lia). fold (mbyte ubs0segs (ms_mem ms0) (bb + k)).
rewrite (K3 (bb + k) ltac:(clear - R0 R1 Hk Hac; lia) ltac:(clear - R0 R1 Hk Hceil HFSv Hac; lia)).
apply K2; [clear - R0 R1 Hk Hac; lia | left; exists bb, nn; split; [exact Hbn' | clear - Hk; lia] | clear - R0 R1 Hk Hceil HFSv Hac; lia]. }
pose proof (CGAT mem4 KB4') as (_ & _ & Hfrs4). pose proof (Hfrs4 f1 Hf1in) as Hfobj4. change (fr_ptr f1) with (fr_ptr f) in Hfobj4.
pose proof (obj_at_nth ubs0segs mem4 (fr_ptr f) LAY_Frame (frame_vals f1) 3 (20, 4%N) gen1 Hfobj4 eq_refl eq_refl) as [Vgen Rgen]. cbn [fst snd Z.of_N N.to_nat] in Vgen, Rgen.
set (vals4 := fl_saved_vals regs0 ++ [g; fr_ptr f; tv; cg_H s; u; u23; u24; u25; top; w; left; h; gen1]).
set (E4 := Ereg regs4 (map (Z_to_bv 64) vals4 ++ [])).
assert (HE4 : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E4 n = getr regs4 rr) by (intros; subst E4; apply ew_Ereg_nat; assumption).
assert (HA4 : forall j v, nth_error vals4 j = Some v -> ew E4 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E4; apply Ereg_vals; exact Hj).
assert (HK4s : forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E4 (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. apply HA4. subst vals4. rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate. }
assert (HV4 : forall n j v, n = (45 + j)%nat -> nth_error [g; fr_ptr f; tv; cg_H s; u; u23; u24; u25; top; w; left; h; gen1] j = Some v -> ew E4 n = Z_to_bv 64 v).
{ intros n j v -> Hj. replace (45 + j)%nat with (32 + (13 + j))%nat by lia. apply HA4. subst vals4. rewrite nth_error_app2 by (cbn; lia). replace (13 + j - length (fl_saved_vals regs0))%nat with j by (cbn; lia). exact Hj. }
assert (G4_2 : getr regs4 2 = Z_to_bv 64 (sp0 - 272)) by (rewrite (HK4 2%bv ltac:(cbv; auto 20)); apply (RG 2%bv 2%nat); [reflexivity | ew_havocA; rewrite (HE 2%nat 2%bv eq_refl); exact G2]).
assert (G4_8 : getr regs4 8 = Z_to_bv 64 pNew) by (rewrite (HK4 8%bv ltac:(cbv; auto 20)); apply (RG 8%bv 58%nat); [reflexivity | exact Hq58]).
assert (G4_27 : getr regs4 27 = Z_to_bv 64 (cg_W s)) by (rewrite (HK4 27%bv ltac:(cbv; auto 20)); apply (RG 27%bv 27%nat); [reflexivity | ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27]).
assert (HU4_2 : bv_unsigned (ew E4 2) = sp0 - 272) by (rewrite (HE4 2%nat 2%bv eq_refl), G4_2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HU4_46 : bv_unsigned (ew E4 46) = fr_ptr f) by (rewrite (HV4 46%nat 1%nat _ eq_refl eq_refl); apply unsigned_lit_small; clear - Hp0 Hp1 Hac HFRv; lia).
assert (HR4 : region_ok ubs0segs E4 mem4 (YP09.mkRegion (Some 2%nat) 0 272 0 0 dcx_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU4_2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold dcx_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E4 mem4 sp0 regs0 32 HSV4); intros j v Hj; exact (HK4s j v Hj)|].
repeat (apply Forall_cons); [..|apply Forall_nil].
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 45%nat 0%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hg0 Hg1 Hac HGSv; lia | cbn; lia | apply val_mem_word_mem; apply WK; [clear; lia | clear; lia | clear; lia | exact W112]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_ptr f)); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 46%nat 1%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hp0 Hp1 Hac HFRv; lia | cbn; lia | apply val_mem_word_mem; apply WK; [clear; lia | clear; lia | clear; lia | exact W120]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ tv); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 47%nat 2%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; exact Htv | cbn; lia | apply val_mem_word_mem; apply WK; [clear; lia | clear; lia | clear; lia | exact W72]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_H s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 48%nat 3%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - RH; lia | cbn; lia | apply val_mem_word_mem; apply WK; [clear; lia | clear; lia | clear; lia | exact W80]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (cg_W s)); [cbn [sv_denot]; rewrite Z.add_0_r, (HE4 27%nat 27%bv eq_refl), G4_27, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - RW; lia | cbn; lia | apply val_mem_word_mem; apply WK; [clear; lia | clear; lia | clear; lia | exact W104]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 53%nat 8%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Ht0 Hth Hh RH; lia | cbn; lia | apply val_mem_word_mem; apply WK; [clear; lia | clear; lia | clear; lia | exact W96]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 49%nat 4%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Ru; lia | cbn; lia | apply val_mem_word_mem; apply WK0; [clear; lia | clear; lia | exact W56']].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u23); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 50%nat 5%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; exact Hu23 | cbn; lia | apply val_mem_word_mem; apply WK; [clear; lia | clear; lia | clear; lia | exact W32]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u24); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 51%nat 6%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; exact Hu24 | cbn; lia | apply val_mem_word_mem; apply WK; [clear; lia | clear; lia | clear; lia | exact W16]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u25); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 52%nat 7%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; exact Hu25 | cbn; lia | apply val_mem_word_mem; apply WK; [clear; lia | clear; lia | clear; lia | exact W24]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ w); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 54%nat 9%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hw Hlw Hl0 RW; lia | cbn; lia | apply val_mem_word_mem; apply WK0; [clear; lia | clear; lia | exact W40]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ left); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 55%nat 10%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hl0 Hlw Hw RW; lia | cbn; lia | apply val_mem_word_mem; apply WK0; [clear; lia | clear; lia | exact W48]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ h); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 56%nat 11%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Ht0 Hth Hh RH; lia | cbn; lia | apply val_mem_word_mem; apply WK0; [clear; lia | clear; lia | exact W64]]. }
assert (HR5 : region_ok ubs0segs E4 mem4 (YP09.mkRegion (Some 46%nat) 20 24 0 0 [mkChunk 20 (CVal 4 (SOff 57 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU4_46.
split; [clear - Hp0; lia|]. split; [clear - Hp1 Hac HFRv; lia|]. split; [intros o Ho; lia|].
constructor; [| constructor]. eapply (chunk_ok_val _ _ _ _ _ _ _ gen1); [cbn [sv_denot]; rewrite Z.add_0_r, (HV4 57%nat 12%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; reflexivity | cbn; exact Rgen | cbn; lia | exact Vgen]. }
assert (HFA4 : atoms_ok E4 [ (2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (46%nat, mkAF 4096 (CEIL_MAX - 40) 3);
(57%nat, mkAF 0 4294967295 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU4_2, HU4_46, (HV4 57%nat 12%nat _ eq_refl eq_refl).
assert (Hp8 : fr_ptr f mod 8 = 0).
{ pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr f) FRAME_SIZE HH0 ltac:(apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | left; reflexivity]) ltac:(lia)) as (_ & _ & H16).
clear - H16. apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide; [lia|]. destruct H16 as [q Hq]. exists (q * 2). lia. }
rewrite !unsigned_lit_small by (clear - Rgen; cbn in Rgen; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hceil Hsp063 Hal16 HFSv HFRv Hac Hp0 Hp1 Hp8 Rgen. cbn in Rgen. repeat split; try lia. replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HPD4 : pairwise_disjoint E4 (ss_mem ss_dcx)).
{ cbn [ss_mem ss_dcx pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU4_2, HU4_46.
clear - Hp1 Hceil HFSv HFRv Hac. repeat split; try exact I; lia. }
assert (HS4 : st_ok ubs0segs E4 ss_dcx (mkst regs4 (Z_to_bv 64 FL_DCX) mem4 (seg_rom ubs0segs))).
{ unfold ss_dcx. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR4 | constructor; [exact HR5 | constructor]] | exact HPD4 | split; [exact HFA4 | split; exact I]]. }
clear HR4 HR5 HFA4 HPD4.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 FL_DCX) mem4 (seg_rom ubs0segs))) in HJ4.
jrun_to LAWS ubs0tbl_ok HS4 HJ4 FL_T. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K5 : forall x, ms_mem ms1 x = mem4 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (KB4 : forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> mbyte ubs0segs (ms_mem ms1) (bb + k) = mbyte ubs0segs memc (bb + k)).
{ intros bb nn k Hbn Hk. rewrite (mbyte_of_eq _ _ _ _ K5). exact (KB4' bb nn k Hbn Hk). }
lazymatch type of HS4 with st_ok _ _ ?ssx ?msx =>
assert (RG4 : forall (r : reg) n wv, sr_get (ss_regs ssx) r = SOff n 0 -> ew E4 n = wv -> getr (ms_regs msx) r = wv)
by (intros r n wv Hr Hv; rewrite (st_ok_reg ubs0segs E4 ssx msx r HS4), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E4 sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs0segs E4 ssx msx r HS4), Hr; reflexivity) end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS4 eq_refl). cbn [ss_pc].
assert (PRE : t2_pre API L A mem md regs0 (ms_regs ms1) L3 A3 (ms_mem ms1) md3 g N s i f gen1 rest FP [(pNew, Nn)] pNew Nn tv w h top left).
{ split; [exact HJ4|]. split; [exact Hid3|]. split; [exact Hra0|]. split; [exact Hal16|]. split; [exact Htp0|].
split; [apply CGAT; exact KB4|].
split; [exact Hwf|]. split; [exact Hi|]. split; [exact Hf|]. split; [exact HFP|]. split; [exact HB3|].
split; [right; split; [reflexivity | split; [clear - Hnz; exact Hnz | clear; subst Nn; lia]]|]. split; [exact Hnew_fp|].
split; [exact Hw|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh|]. split; [exact Ht0|]. split; [exact Hth|]. split; [exact Htv|].
split; [apply (fl_saved_ok_kept mem4); [exact HSV4 | intros a Ha; apply mbyte_of_eq; exact K5]|].
split; [apply (RG4 9%bv 47%nat _ eq_refl); exact (HV4 47%nat 2%nat _ eq_refl eq_refl)|].
split; [apply (RG4 2%bv 2%nat _ eq_refl); rewrite (HE4 2%nat 2%bv eq_refl); exact G4_2|].
split; [intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K5); apply (WK 112 g ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) W112 k Hk)|].
split; [intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K5); apply (WK 120 (fr_ptr f) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) W120 k Hk)|].
split; [apply (RG4 8%bv 8%nat _ eq_refl); rewrite (HE4 8%nat 8%bv eq_refl); exact G4_8|].
split; [intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K5); apply (WK0 56 u ltac:(clear; lia) ltac:(clear; lia) W56' k Hk)|].
split; [apply (RG4 27%bv 27%nat _ eq_refl); rewrite (HE4 27%nat 27%bv eq_refl); exact G4_27|].
split; [intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K5); apply (WK 104 (cg_W s) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) W104 k Hk)|].
split; [apply (RG4 19%bv 48%nat _ eq_refl); exact (HV4 48%nat 3%nat _ eq_refl eq_refl)|].
split; [apply (RG4 16%bv 56%nat _ eq_refl); exact (HV4 56%nat 11%nat _ eq_refl eq_refl)|].
split; [apply (RG4 23%bv 54%nat _ eq_refl); exact (HV4 54%nat 9%nat _ eq_refl eq_refl)|].
split; [intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K5); apply (WK 96 top ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) W96 k Hk)|].
split; [apply (RG4 22%bv 55%nat _ eq_refl); exact (HV4 55%nat 10%nat _ eq_refl eq_refl)|].
split; [apply (RG4 3%bv 3%nat _ eq_refl); rewrite (HE4 3%nat 3%bv eq_refl), (HK4 3%bv ltac:(cbv; auto 20)); apply (RG 3%bv 3%nat); [reflexivity | ew_havocA; rewrite (HE 3%nat 3%bv eq_refl); exact G3]
| apply (RG4 4%bv 4%nat _ eq_refl); rewrite (HE4 4%nat 4%bv eq_refl), (HK4 4%bv ltac:(cbv; auto 20)); apply (RG 4%bv 4%nat); [reflexivity | ew_havocA; rewrite (HE 4%nat 4%bv eq_refl); exact G4] ]. }
assert (Hnz' : (pNew =? 0) = false) by (apply Z.eqb_neq; exact Hnz).
pose proof HVALS as (_ & HVf & _ & _). pose proof HVf as (_ & _ & _ & _ & _ & _ & _ & XVI & XVIl & _).
destruct (dt_window memc (ms_mem ms1) (fr_img f) pNew (cg_W s) (Z.to_nat (cg_H s)) (YO07.f_img cur) w h top left XVI HW1
ltac:(apply Nat2Z.inj; rewrite Nat2Z.inj_mul, !Z2Nat.id by (clear - HW1 HH1; lia); rewrite XVIl; exact HN)
Hw Hl0 Hlw Hh Ht0 ltac:(rewrite Z2Nat.id by (clear - HH1; lia); exact Hth)) as [XWIN XWINL].
{ intros r j Hr Hj. rewrite (mbyte_of_eq _ _ _ _ K5). rewrite (C4 r j Hr Hj).
assert (HrW : 0 <= (top + r) * cg_W s /\ (top + r) * cg_W s + cg_W s <= N).
{ clear - Hr Hth Ht0 HW1 HN Hh. split; [nia|]. rewrite HN. replace ((top + r) * cg_W s + cg_W s) with ((top + r + 1) * cg_W s) by lia.
rewrite (Z.mul_comm (cg_W s) (cg_H s)). apply Z.mul_le_mono_nonneg_r; lia. }
rewrite (K3 (fr_img f + left + (top + r) * cg_W s + j) ltac:(clear - Hj Him0 Him1 Hlw Hl0 HrW Hac HNle; lia) ltac:(clear - Hj Him0 Him1 Hlw Hl0 HrW Hac HNle Hceil HFSv; lia)).
apply K2; [clear - Hj Him0 Him1 Hlw Hl0 HrW Hac HNle; lia | left; exists (fr_img f), N; split; [exact Himgfin | clear - Hj Hlw Hl0 HrW; lia] | clear - Hj Him0 Him1 Hlw Hl0 HrW Hac HNle Hceil HFSv; lia]. }
apply (fl_trans API IMG RAWADDX L A mem md regs0 (ms_regs ms1) L3 A3 (ms_mem ms1) md3 g N s i f rest FP FPw [(pNew, Nn)] pNew Nn tv w h top left np
S GPAL cur (Some b) (Some befr) brb (rb_malloc bc (h * w)) u25 PRE (bv_unsigned (getr (ms_regs ms1) 11))).
+ symmetry. apply Z_to_bv_bv_unsigned.
+ apply u64_range_getr.
+ apply (RG4 20%bv 20%nat _ eq_refl). rewrite (HE4 20%nat 20%bv eq_refl), (HK4 20%bv ltac:(cbv; auto 20)). apply (RG 20%bv 20%nat); [reflexivity | ew_havocA; rewrite (HE 20%nat 20%bv eq_refl); exact G20].
+ exact Hnp.
+ intros _. exists b, befr. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hb|]. apply (RG4 18%bv 18%nat _ eq_refl). rewrite (HE4 18%nat 18%bv eq_refl), (HK4 18%bv ltac:(cbv; auto 20)). apply (RG 18%bv 18%nat); [reflexivity | ew_havocA; rewrite (HE 18%nat 18%bv eq_refl); exact G18].
+ exact (nth_error_nth (cg_frames s) (i - 1)%nat None Hb).
+ exact HSINK.
+ eapply fl_vals_kept; [| exact HVALS]. intros a0 n0 k Hin Hk. rewrite (mbyte_of_eq _ _ _ _ K5). apply (KB4' a0 n0 k); [| exact Hk].
exact (fl_vblocks_sub g s N f (Some b) i Hf ltac:(right; exists (i - 1)%nat; exact Hb) _ Hin).
+ apply (RG4 14%bv 50%nat _ eq_refl). rewrite <- Xu23. exact (HV4 50%nat 5%nat _ eq_refl eq_refl).
+ apply (RG4 15%bv 52%nat _ eq_refl). exact (HV4 52%nat 7%nat _ eq_refl eq_refl).
+ rewrite <- Xu23. intros k Hk. rewrite (mbyte_of_eq _ _ _ _ K5). apply (WK 32 u23 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) W32 k Hk).
+ rewrite <- Xu24. intros k Hk. rewrite (mbyte_of_eq _ _ _ _ K5). apply (WK 16 u24 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) W16 k Hk).
+ intros k Hk. rewrite (mbyte_of_eq _ _ _ _ K5). apply (WK 24 u25 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) W24 k Hk).
+ exact Xu25.
+ symmetry. exact Fw. + symmetry. exact Fh. + symmetry. exact Ftop. + symmetry. exact Fleft.
+
rewrite (RGX 11%bv (SExt true 32 (SOff 57 0)) eq_refl). change (bv_unsigned (sv_denot E4 (SExt true 32 (SOff 57 0)))) with (U E4 (SExt true 32 (SOff 57 0))).
rewrite land1_low32_dt by (pose proof (U_range E4 (SExt true 32 (SOff 57 0))); lia).
rewrite (U_sext32_low E4 57 gen1 (HV4 57%nat 12%nat _ eq_refl eq_refl)) by (clear - Rgen; cbn in Rgen; lia).
clear. subst gen1 G. unfold fl_trans_on, YO07.flag. rewrite Bool.negb_true_iff, Z.eqb_neq. tauto.
+ exact Xnp.
+ exact Xtv0.
+ rewrite Hnz', Ftmp. exact XWIN.
+ rewrite Ftmp, XWINL. reflexivity.
+ exact HRq3.
+ intros Hz. exfalso. exact (Hnz Hz).
+ intros _. split; [rewrite (Z.mul_comm w h); exact HRR | exact HRB].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
