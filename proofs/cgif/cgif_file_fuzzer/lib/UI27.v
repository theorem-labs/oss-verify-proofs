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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a YI06 UI5b YI09 YI08 YI0r UI1w UI1v UI4l UI21 UI5o UI5l YI6b UI5n UI20 UI1d UI2l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2o UI2p UI2q UI24 UI2d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI26.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition f2l_ZX : sv := SAlu ALU_SRL (SAlu ALU_SLL (SOff 25 0) (SLit 32)) (SLit 32).
Definition f2l_facts : list (nat * afact) :=
[ (27%nat, mkAF 1 65535 0); (19%nat, mkAF 1 65534 0); (23%nat, mkAF 0 65533 0); (8%nat, mkAF 0 65533 0);
(9%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 4096 CEIL_MAX 0); (32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 4096 CEIL_MAX 0) ].
Definition f2l_conds : list acond := [ mkAC BC_GEU (SOff 32 0) (SOff 9 0); mkAC BC_GEU (SOff 33 0) (SOff 20 0) ].
Definition f2l_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 9 0) f2l_ZX, SOff 32 0); (SAlu ALU_ADD f2l_ZX (SOff 20 0), SOff 33 0) ].
Definition ss_f2l : sstate :=
mkSS FL_F2L (sr_set (sr_set (sr_set sr_atoms 22%bv (SLit 65535)) 24%bv (SLit 1)) 26%bv (SLit 1)) [] None
(mkFacts f2l_facts f2l_conds f2l_alias).
Definition F2_KEPT : list reg := [2; 3; 4; 8; 9; 18; 20; 21; 23; 27]%bv.
Definition ss_f2 (z : bool) : sstate :=
mkSS FL_F2 sr_atoms
[ YP09.mkRegion (Some 2%nat) 80 88 80 80 [mkChunk 80 (CVal 8 (SOff 32 1))] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (32%nat, mkAF 0 65534 0); (8%nat, mkAF 0 65534 0);
(9%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 4096 CEIL_MAX 0) ]
[mkAC BC_NE (SOff 8 0) (SOff 32 1); mkAC (if z then BC_GEU else BC_LTU) (SAlu ALU_AND (SOff 8 0) (SLit 65535)) (SAlu ALU_AND (SOff 32 0) (SLit 65535))] []).
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Section c.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Definition f2_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top : Z) (c' : config) : Prop :=
exists regs' mem' hrow,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F3) mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
top <= hrow < H /\ getr regs' 19 = Z_to_bv 64 hrow /\ getr regs' 8 = Z_to_bv 64 top /\ getr regs' 27 = Z_to_bv 64 W /\
(forall r : reg, In r F2_KEPT -> getr regs' r = getr regs r) /\
(exists cb, 0 <= cb < W /\ DIFb mem0 fimg bimg (hrow * W + cb)) /\ (forall p, (hrow + 1) * W <= p < N -> ~ DIFb mem0 fimg bimg p).
Lemma fl_f2lV : forall (n : nat) (i v : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top : Z),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
v mod 2 ^ 32 = W * i -> 0 <= v < 2 ^ 64 ->
0 <= top -> top + Z.of_nat n = i -> (1 <= n)%nat -> i < H ->
getr regs 19 = Z_to_bv 64 i -> getr regs 25 = Z_to_bv 64 v -> getr regs 22 = Z_to_bv 64 65535 -> getr regs 23 = Z_to_bv 64 top ->
getr regs 24 = Z_to_bv 64 1 -> getr regs 26 = Z_to_bv 64 1 ->
getr regs 9 = Z_to_bv 64 fimg -> getr regs 20 = Z_to_bv 64 bimg -> getr regs 27 = Z_to_bv 64 W -> getr regs 8 = Z_to_bv 64 top ->
(exists c0, 0 <= c0 < W /\ DIFb mem0 fimg bimg (top * W + c0)) -> (forall p, (i + 1) * W <= p < N -> ~ DIFb mem0 fimg bimg p) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 FL_F2L) memc (seg_rom ubs0segs)) mdc) (f2_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top).
Proof using HC IMG.
intros n. induction n as [|n IH]; intros i v STK sp0 FP L A mem md Lc Ac mdc regs memc top HJ K0 Hfi Hbi Hvmod Hv Ht0 Htn Hn HiH
G19 G25 G22 G23 G24 G26 G9 G20 G27 G8 HWT HEQ; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HiW : W <= W * i /\ W * i + W <= N) by (rewrite HN; clear - Ht0 Htn Hn HiH HW; nia).
assert (Hi64 : 0 <= i < 2 ^ 64 /\ i <= 65534 /\ 0 <= top < 2 ^ 64) by (clear - Ht0 Htn Hn HiH HH; lia).
set (E := Ereg regs (map (Z_to_bv 64) [fimg + W * i; bimg + W * i] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (fimg + W * i)) by (subst E; apply (Ereg_vals regs [fimg + W * i; bimg + W * i] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 (bimg + W * i)) by (subst E; apply (Ereg_vals regs [fimg + W * i; bimg + W * i] [] 1%nat); reflexivity).
assert (HE9 : ew E 9 = Z_to_bv 64 fimg) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE20 : ew E 20 = Z_to_bv 64 bimg) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (ZX : U E f2l_ZX = W * i).
{ unfold f2l_ZX. rewrite U_zext32_mod, (U_atom E 25 v) by first [rewrite (HE 25%nat 25%bv eq_refl); exact G25 | exact Hv]. exact Hvmod. }
assert (HFA : atoms_ok E f2l_facts).
{ unfold f2l_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE32, HE33, HE9, HE20, (HE 27%nat 27%bv eq_refl), (HE 19%nat 19%bv eq_refl), (HE 23%nat 23%bv eq_refl), (HE 8%nat 8%bv eq_refl), G27, G19, G23, G8.
rewrite !unsigned_lit_small by (clear - Ht0 Htn Hn HiH HiW HW HH HNle Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac; lia). change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - HW HH Ht0 Htn Hn HiH HiW Hfimg0 Hfimg1 Hbimg0 Hbimg1 HNle Hac. repeat split; lia. }
assert (HCO : conds_ok E f2l_conds).
{ unfold f2l_conds. cbn [conds_ok]. split; [|split; [|exact I]].
- apply (cond_geu E 32 0 9 0 (fimg + W * i) fimg HE32 HE9); clear - HiW HW Hfimg0 Hfimg1 Hac; lia.
- apply (cond_geu E 33 0 20 0 (bimg + W * i) bimg HE33 HE20); clear - HiW HW Hbimg0 Hbimg1 Hac; lia. }
assert (HAL : alias_ok E f2l_alias).
{ unfold f2l_alias. cbn [alias_ok]. split; [|split; [|exact I]].
- assert (UA : U E (SAlu ALU_ADD (SOff 9 0) f2l_ZX) = fimg + W * i).
{ apply (U_add_small E _ _ fimg (W * i)); [apply U_atom; [exact HE9 | clear - Hfimg0 Hfimg1 HiW HW Hac; lia] | exact ZX | clear - Hfimg0; lia | clear - HiW HW; lia | clear - Hfimg1 HiW Hac HW; lia]. }
apply U_inj. rewrite UA, (U_atom E 32 (fimg + W * i) HE32) by (clear - Hfimg0 Hfimg1 HiW Hac HW; lia). reflexivity.
- assert (UA : U E (SAlu ALU_ADD f2l_ZX (SOff 20 0)) = W * i + bimg).
{ apply (U_add_small E _ _ (W * i) bimg); [exact ZX | apply U_atom; [exact HE20 | clear - Hbimg0 Hbimg1 HiW HW Hac; lia] | clear - HiW HW; lia | clear - Hbimg0; lia | clear - Hbimg1 HiW Hac HW; lia]. }
apply U_inj. rewrite UA, (U_atom E 33 (bimg + W * i) HE33) by (clear - Hbimg0 Hbimg1 HiW Hac HW; lia). clear; lia. }
assert (HS : st_ok ubs0segs E ss_f2l (mkst regs (Z_to_bv 64 FL_F2L) memc (seg_rom ubs0segs))).
{ unfold ss_f2l. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact G22] | intros X; discriminate X | exact G24] | intros X; discriminate X | exact G26].
- vm_compute; reflexivity.
- constructor.
- cbn [pairwise_disjoint]; exact I.
- split; [exact HFA | split; [exact HCO | exact HAL]]. }
clear HFA HCO HAL.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F2L) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_memcmp. { apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha0. rewrite HE32 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite HE33 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 27%nat 27%bv eq_refl), G27 in Ha2.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc ss_f2l].
eapply SR_bind.
{ apply (memcmp_callDV API mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC
STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) (W * i) FL_F2R HJ (KD_eq _ _ _ _ K0 K1) Hfi Hbi ltac:(clear - HiW HW; lia) ltac:(clear - HiW; lia) Ha0 Ha1 Ha2).
rewrite Hra. apply (ret_ok_even (Z_to_bv 64 FL_F2R)). vm_compute. reflexivity. }
cbv beta. intros c' (regs2 & r & -> & Hr10 & Rr & Hwit & Hfr2 & Hzero).
jafter_stretch_keep HS 34%nat regs2 (ms_mem ms) BCMP_CLOB FL_F2R ([] : list nat) HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor. }
clear HS. rename HS2 into HS.
change (ms_mem ms) with (ms_mem (mkst regs2 (Z_to_bv 64 FL_F2R) (ms_mem ms) (seg_rom ubs0segs))) in HJ.
set (E2 := havoc E 34 (map (getr regs2) BCMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (HE2_34 : ew E2 34 = Z_to_bv 64 r).
{ subst E2. pose proof (ew_havoc_new E 34 (map (getr regs2) BCMP_CLOB) 0 (Z_to_bv 64 0) ltac:(cbn; lia)) as X.
replace (34 + 0)%nat with 34%nat in X by reflexivity. rewrite X. cbn [nth map BCMP_CLOB]. exact Hr10. }
assert (EXIT : forall ss ms' hrow, st_ok ubs0segs E2 ss ms' -> ss_pc ss = FL_F3 -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) F2_KEPT = true ->
top <= hrow < H -> getr (ms_regs ms') 19 = Z_to_bv 64 hrow ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall z, ms_mem ms' z = memc z) ->
(exists cb, 0 <= cb < W /\ DIFb mem0 fimg bimg (hrow * W + cb)) -> (forall p, (hrow + 1) * W <= p < N -> ~ DIFb mem0 fimg bimg p) ->
f2_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top (mkCfg ms' mdc)).
{ intros ss ms' hrow HS' Hpc Hrv Hkl Hh Q19 HJ' K' VWx VNx. exists (ms_regs ms'), (ms_mem ms'), hrow.
assert (HKx : forall rr : reg, In rr F2_KEPT -> getr (ms_regs ms') rr = getr regs rr) by (intros rr Hrr; subst E E2; exact (regs_kept_of_st_ok ubs0segs _ ss ms' regs _ F2_KEPT HS' EA1 Hkl rr Hrr)).
split; [rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hh|]. split; [exact Q19|].
split; [rewrite (HKx 8%bv ltac:(cbv; auto 20)); exact G8|].
split; [rewrite (HKx 27%bv ltac:(cbv; auto 20)); exact G27|].
split; [exact HKx|]. split; [exact VWx | exact VNx]. }
jbranch ubs0tbl HS.
-
assert (Hne : r <> 0).
{ intros Hz. rewrite branch_ne_U, U_lit, (U_atom E2 34 0) in Hc; [discriminate Hc | rewrite HE2_34, Hz; reflexivity | clear; lia | clear; lia]. }
destruct (Hwit Hne) as (cb & Hcb & Hdif). replace (W * i + cb) with (i * W + cb) in Hdif by (clear; lia).
clear Hc. jrun_to LAWS ubs0tbl_ok HS HJ FL_F3. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ i HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Ht0 Htn Hn HiH; lia)); [| exact HJ | | exists cb; split; [exact Hcb | exact Hdif] | exact HEQ].
+ reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 19%nat 19%bv eq_refl), G19, Z_to_bv_bv_unsigned; reflexivity).
+ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
-
assert (Hz : r = 0).
{ destruct (Z.eq_dec r 0) as [Hz | Hnz]; [exact Hz|]. exfalso.
rewrite branch_ne_U, U_lit, (U_atom E2 34 (r mod 2 ^ 64)) in Hc; [| rewrite HE2_34; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_mod by lia; reflexivity | apply Z.mod_pos_bound; lia | clear; lia].
destruct (Z.eqb_spec (r mod 2 ^ 64) 0) as [E0 | _]; [|discriminate Hc].
destruct (Z.lt_ge_cases r 0); [rewrite <- (Z.mod_unique r (2 ^ 64) (-1) (2 ^ 64 + r)) in E0 by lia; lia | rewrite Z.mod_small in E0 by lia; lia]. }
assert (HEQ1 : forall p, i * W <= p < N -> ~ DIFb mem0 fimg bimg p).
{ intros p Hp. destruct (Z.lt_ge_cases p ((i + 1) * W)) as [Hlt | Hge]; [| apply HEQ; lia].
replace p with (W * i + (p - W * i)) by (clear; lia). apply (Hzero Hz). clear - Hp Hlt. lia. }
clear Hc. jrun LAWS ubs0tbl_ok HS HJ. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
jbranch ubs0tbl HS.
+
rewrite branch_ltu_U, U_and_lit, (U_atom E2 23 top), (U_atom_off E2 19 i (-1)), land_ffff in Hc
by first [subst E2; ew_havocA; first [rewrite (HE 23%nat 23%bv eq_refl); exact G23 | rewrite (HE 19%nat 19%bv eq_refl); exact G19] | clear - Hi64 Htn Hn; lia].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.ltb_spec top (i + -1)) as [Hl|Hl]; [clear - Htn Hl; lia | discriminate Hc]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ FL_F2L. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms1 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ F2_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR;
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg ubs0segs Ef ssf msf rq HS), Hrq; reflexivity) end.
set (v' := U E2 (SAluw ALU_SUB (SOff 25 0) (SOff 27 0))).
assert (Hv' : 0 <= v' < 2 ^ 64) by (apply U_range).
assert (Hv'mod : v' mod 2 ^ 32 = W * (i - 1)).
{ subst v'. rewrite U_subw_mod32, (U_atom E2 25 v), (U_atom E2 27 W) by first [subst E2; ew_havocA; first [rewrite (HE 25%nat 25%bv eq_refl); exact G25 | rewrite (HE 27%nat 27%bv eq_refl); exact G27] | clear - Hv HW; lia].
rewrite <- Zminus_mod_idemp_l, Hvmod. replace (W * i - W) with (W * (i - 1)) by (clear; lia). apply Z.mod_small. clear - HiW HNle HW; lia. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i - 1) v' STK sp0 FP L A mem md Lc Ac mdc _ _ top HJ (KD_eq _ _ _ _ K0 K3) Hfi Hbi Hv'mod Hv' Ht0 ltac:(clear - Htn; lia) Hn1 ltac:(clear - HiH; lia));
[| | | | | | | | | | exact HWT | intros p Hp; apply HEQ1; clear - Hp; lia].
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 19%nat 19%bv eq_refl), G19, unsigned_lit_small by (clear - Hi64; lia); f_equal; clear; lia).
- rewrite (RGX 25%bv _ eq_refl). eval_sr_get. apply denot_of_U'. reflexivity.
- reg_nowF HS ltac:(reflexivity).
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(reflexivity).
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 20%bv ltac:(cbv; auto 20)). exact G20.
- rewrite (HKR 27%bv ltac:(cbv; auto 20)). exact G27.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8. }
cbv beta. intros c' (regs' & mem' & hrow & -> & HJ' & K' & Hh & Q19 & Q8 & Q27 & HK' & VW' & VN'). exists regs', mem', hrow.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K3|]. split; [exact Hh|]. split; [exact Q19|]. split; [exact Q8|]. split; [exact Q27|].
split; [intros rr Hrr; rewrite (HK' rr Hrr); apply (HKR rr Hrr)|]. split; [exact VW' | exact VN'].
+
rewrite branch_ltu_U, U_and_lit, (U_atom E2 23 top), (U_atom_off E2 19 i (-1)), land_ffff in Hc
by first [subst E2; ew_havocA; first [rewrite (HE 23%nat 23%bv eq_refl); exact G23 | rewrite (HE 19%nat 19%bv eq_refl); exact G19] | clear - Hi64 Htn Hn; lia].
assert (Hit : i - 1 = top) by (destruct (Z.ltb_spec top (i + -1)) as [Hl|Hl]; [discriminate Hc | clear - Htn Hn Hl; lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ FL_F3. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ top HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Ht0 HiH Hit; lia)); [| exact HJ | | exact HWT | intros p Hp; apply HEQ1; clear - Hp Hit HW; nia].
* reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 8%nat 8%bv eq_refl), G8, Z_to_bv_bv_unsigned; reflexivity).
* intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2.
Qed.
Definition F2S_KEPT : list reg := [2; 3; 4; 8; 9; 18; 20; 27]%bv.
Definition f2s_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top : Z) (c' : config) : Prop :=
exists regs' mem' hrow,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F3) mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
top <= hrow < H /\ getr regs' 19 = Z_to_bv 64 hrow /\ getr regs' 8 = Z_to_bv 64 top /\ getr regs' 21 = Z_to_bv 64 top /\ getr regs' 27 = Z_to_bv 64 W /\
(forall r : reg, In r F2S_KEPT -> getr regs' r = getr regs r) /\
(exists cb, 0 <= cb < W /\ DIFb mem0 fimg bimg (hrow * W + cb)) /\ (forall p, (hrow + 1) * W <= p < N -> ~ DIFb mem0 fimg bimg p).
Lemma fl_f2V : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top : Z),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
spv = sp0 - 272 -> 272 <= STK -> 0 <= top < H ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 20 = Z_to_bv 64 bimg -> getr regs 27 = Z_to_bv 64 W -> getr regs 8 = Z_to_bv 64 top ->
(exists c0, 0 <= c0 < W /\ DIFb mem0 fimg bimg (top * W + c0)) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 FL_F2) memc (seg_rom ubs0segs)) mdc) (f2s_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top).
Proof using HC IMG.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc top HJ K0 Hfi Hbi Hspv HSTK Htop G2 G9 G20 G27 G8 HWT.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC memc K0) as (_ & _ & _ & _ & _ & WHm & _).
set (E := Ereg regs (map (Z_to_bv 64) [H - 1] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (H - 1)) by (subst E; apply (Ereg_vals regs [H - 1] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 80 88 80 80 [mkChunk 80 (CVal 8 (SOff 32 1))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val _ _ _ _ _ _ _ H); [cbn [sv_denot]; rewrite HE32, unsigned_lit_small by lia; f_equal; lia | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WHm]. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (32%nat, mkAF 0 65534 0); (8%nat, mkAF 0 65534 0);
(9%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 4096 CEIL_MAX 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE32, (HE 27%nat 27%bv eq_refl), (HE 8%nat 8%bv eq_refl), (HE 9%nat 9%bv eq_refl), (HE 20%nat 20%bv eq_refl), G27, G8, G9, G20.
assert (HN1 : 1 <= N) by (rewrite HN; clear - HW HH; nia).
rewrite !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. clear - Hsp0 Hsp1 Hsp16 HW HH Htop Hfimg0 Hfimg1 Hbimg0 Hbimg1 HN1 Hac. repeat split; lia. }
assert (HCF : forall z : bool, (if z then top = H - 1 else top < H - 1) ->
conds_ok E [mkAC BC_NE (SOff 8 0) (SOff 32 1); mkAC (if z then BC_GEU else BC_LTU) (SAlu ALU_AND (SOff 8 0) (SLit 65535)) (SAlu ALU_AND (SOff 32 0) (SLit 65535))]).
{ intros z Hz. cbn [conds_ok]. split; [| split; [| exact I]]; unfold acond_ok; cbn [ac_c ac_a ac_b].
- rewrite branch_ne_U, (U_atom E 8 top), (U_atom_off E 32 (H - 1) 1) by first [exact HE32 | rewrite (HE 8%nat 8%bv eq_refl); exact G8 | clear - Htop HH; lia].
destruct (Z.eqb_spec top (H - 1 + 1)); [clear - Htop e; lia | reflexivity].
- destruct z; rewrite ?branch_geu_U, ?branch_ltu_U, !U_and_lit, (U_atom E 8 top), (U_atom E 32 (H - 1)), !land_ffff by first [exact HE32 | rewrite (HE 8%nat 8%bv eq_refl); exact G8 | clear - Htop HH; lia];
(destruct (Z.ltb_spec top (H - 1)) as [Hl|Hl]; cbn [negb]; first [reflexivity | exfalso; clear - Hz Hl; lia]). }
assert (MK : forall z : bool, (if z then top = H - 1 else top < H - 1) -> st_ok ubs0segs E (ss_f2 z) (mkst regs (Z_to_bv 64 FL_F2) memc (seg_rom ubs0segs))).
{ intros z Hz. unfold ss_f2. subst E. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; destruct z; reflexivity | constructor; [exact HR | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; [exact (HCF z Hz) | exact I]]]. }
clear HR HFA HCF.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F2) memc (seg_rom ubs0segs))) in HJ.
assert (EXIT : forall ss ms' hrow, st_ok ubs0segs E ss ms' -> ss_pc ss = FL_F3 -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) F2S_KEPT = true ->
top <= hrow < H -> getr (ms_regs ms') 19 = Z_to_bv 64 hrow -> getr (ms_regs ms') 8 = Z_to_bv 64 top -> getr (ms_regs ms') 21 = Z_to_bv 64 top -> getr (ms_regs ms') 27 = Z_to_bv 64 W ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall z, ms_mem ms' z = memc z) ->
(exists cb, 0 <= cb < W /\ DIFb mem0 fimg bimg (hrow * W + cb)) -> (forall p, (hrow + 1) * W <= p < N -> ~ DIFb mem0 fimg bimg p) ->
f2s_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top (mkCfg ms' mdc)).
{ intros ss ms' hrow HS' Hpc Hrv Hkl Hh Q19 Q8 Q21 Q27 HJ' K' VWx VNx. exists (ms_regs ms'), (ms_mem ms'), hrow.
split; [rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hh|].
split; [exact Q19|]. split; [exact Q8|]. split; [exact Q21|]. split; [exact Q27|].
split; [intros rr Hrr; subst E; exact (regs_kept_of_st_ok ubs0segs _ ss ms' regs _ F2S_KEPT HS' (env_agree_refl _ _) Hkl rr Hrr)|]. split; [exact VWx | exact VNx]. }
destruct (Z.eq_dec top (H - 1)) as [Hte | Hte].
-
pose proof (MK true Hte) as HS. clear MK.
jrun_to LAWS ubs0tbl_ok HS HJ FL_F3. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
apply SR_ret. apply (EXIT _ _ (H - 1) HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Hte Htop; lia)); [| | | | exact HJ | exact K1 | rewrite <- Hte; exact HWT | intros p Hp; exfalso; rewrite HN in Hp; clear - Hp HW; nia].
+ reg_nowF HS ltac:(rewrite HE32, Z_to_bv_bv_unsigned; reflexivity).
+ reg_nowF HS ltac:(rewrite (HE 8%nat 8%bv eq_refl), G8, Z_to_bv_bv_unsigned; reflexivity).
+ reg_nowF HS ltac:(rewrite (HE 8%nat 8%bv eq_refl), G8, Z_to_bv_bv_unsigned; reflexivity).
+ reg_nowF HS ltac:(rewrite (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity).
-
assert (Htl : top < H - 1) by (clear - Htop Hte; lia).
pose proof (MK false Htl) as HS. clear MK.
jrun_to LAWS ubs0tbl_ok HS HJ FL_F2L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (regs_kept_of_st_ok ubs0segs E ssx msx regs _ F2S_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssx) rq = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg ubs0segs E ssx msx rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssx) rq = sv -> getr (ms_regs msx) rq = sv_denot E sv)
by (intros rq sv Hrq; rewrite (st_ok_reg ubs0segs E ssx msx rq HS), Hrq; reflexivity) end.
assert (HiW : 0 <= W * (H - 1) /\ W * (H - 1) + W <= N) by (rewrite HN; clear - HW HH; nia).
assert (Q21 : getr (ms_regs ms) 21 = Z_to_bv 64 top) by (apply (RG 21%bv 8%nat _ eq_refl); rewrite (HE 8%nat 8%bv eq_refl); exact G8).
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (fl_f2lV (Z.to_nat (H - 1 - top)) (H - 1) (W * (H - 1)) STK sp0 FP L A mem md Lc Ac mdc _ _ top HJ (KD_eq _ _ _ _ K0 K1) Hfi Hbi ltac:(apply Z.mod_small; clear - HiW HNle HW; lia) ltac:(clear - HiW HNle HW; lia)
ltac:(clear - Htop; lia) ltac:(clear - Htl; lia) ltac:(clear - Htl; lia) ltac:(clear; lia));
[| | | | | | | | | | exact HWT | intros p Hp; exfalso; rewrite HN in Hp; clear - Hp HW; nia].
- apply (RG 19%bv 32%nat _ eq_refl). exact HE32.
- rewrite (RGX 25%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite (Z.mul_comm W (H - 1)). apply (U_mul_small' E _ _ (H - 1) W); [apply (U_atom E 32 (H - 1) HE32); clear - HH; lia | apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - HH; lia | clear - HW; lia | clear - HiW HNle HW; nia].
- rewrite (RGX 22%bv (SLit 65535) eq_refl). reflexivity.
- rewrite (RGX 23%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite U_and_lit, (U_atom E 8 top) by first [rewrite (HE 8%nat 8%bv eq_refl); exact G8 | clear - Htop HH; lia]. apply land_ffff. clear - Htop HH; lia.
- rewrite (RGX 24%bv (SLit 1) eq_refl). reflexivity.
- rewrite (RGX 26%bv (SLit 1) eq_refl). reflexivity.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 20%bv ltac:(cbv; auto 20)). exact G20.
- rewrite (HKR 27%bv ltac:(cbv; auto 20)). exact G27.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8. }
cbv beta. intros c' (regs2 & mem2 & hrow & -> & HJ2 & K2 & Hh2 & Q19 & Q8 & Q27 & HK2 & VW2 & VN2). exists regs2, mem2, hrow.
split; [reflexivity|]. split; [exact HJ2|]. split; [intros z; rewrite K2; apply K1|]. split; [exact Hh2|]. split; [exact Q19|]. split; [exact Q8|].
split; [rewrite (HK2 21%bv ltac:(cbv; auto 20)); exact Q21|]. split; [exact Q27|].
split; [intros rr Hrr; rewrite (HK2 rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)); apply (HKR rr Hrr)|]. split; [exact VW2 | exact VN2].
Qed.
End c.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
