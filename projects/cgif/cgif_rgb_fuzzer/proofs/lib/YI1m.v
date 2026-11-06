(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YO3l YI00 YI02 YI01 YI03
YI1e YI1c YI39 YI1i YI59 YI56 YI0x YI57
YI1h YI16 YI1z YI1k YI21 YI22 YI23 YI1j YI1s YI1l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_f2l : sstate :=
mkSS FL_F2L (sr_set sr_atoms 19%bv (SLit 65535))
[ YQ0b.mkRegion (Some 2%nat) 80 88 80 80 [] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (20%nat, mkAF 1 65534 0); (24%nat, mkAF 0 65533 0); (26%nat, mkAF 0 65534 0);
(22%nat, mkAF 4096 CEIL_MAX 0); (23%nat, mkAF 4096 CEIL_MAX 0) ] [] []).
Definition F2_KEPT : list reg := [2; 3; 4; 8; 9; 18; 22; 23; 26; 21; 27]%bv.
Definition ss_f2 (z : bool) : sstate :=
mkSS FL_F2 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 64 112 64 88 [mkChunk 96 (CVal 8 (SOff 32 1))] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (32%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0);
(22%nat, mkAF 4096 CEIL_MAX 0); (23%nat, mkAF 4096 CEIL_MAX 0) ]
[mkAC BC_NE (SOff 26 0) (SOff 32 1); mkAC (if z then BC_GEU else BC_LTU) (SAlu ALU_AND (SOff 26 0) (SLit 65535)) (SAlu ALU_AND (SOff 32 0) (SLit 65535))] []).
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Section c.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Definition f2_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top : Z) (c' : config) : Prop :=
exists regs' mem' hrow,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F3) mem' (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
top <= hrow < H /\ getr regs' 20 = Z_to_bv 64 hrow /\ getr regs' 21 = Z_to_bv 64 top /\ getr regs' 27 = Z_to_bv 64 W /\
(forall r : reg, In r F2_KEPT -> getr regs' r = getr regs r).
Lemma fl_f2l : forall (n : nat) (i v : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top : Z),
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
v mod 2 ^ 32 = W * i -> 0 <= v < 2 ^ 64 ->
0 <= top -> top + Z.of_nat n = i -> (1 <= n)%nat -> i < H ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 19 = Z_to_bv 64 65535 -> getr regs 27 = Z_to_bv 64 W -> getr regs 20 = Z_to_bv 64 i ->
getr regs 22 = Z_to_bv 64 fimg -> getr regs 24 = Z_to_bv 64 top -> getr regs 23 = Z_to_bv 64 bimg -> getr regs 25 = Z_to_bv 64 v -> getr regs 26 = Z_to_bv 64 top ->
getr regs 21 = Z_to_bv 64 top ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 FL_F2L) memc (seg_rom src2segs)) mdc) (f2_post STK sp0 FP L A mem md Lc Ac mdc regs memc top).
Proof.
intros n. induction n as [|n IH]; intros i v STK sp0 FP L A mem md Lc Ac mdc regs memc top HJ K0 Hfi Hbi Hvmod Hv Ht0 Htn Hn HiH
G2 G19 G27 G20 G22 G24 G23 G25 G26 G21; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HiW : W <= W * i /\ W * i + W <= N) by (rewrite HN; clear - Ht0 Htn Hn HiH HW; nia).
assert (Hi64 : 0 <= i < 2 ^ 64 /\ i <= 65534 /\ 0 <= top < 2 ^ 64) by (clear - Ht0 Htn Hn HiH HH; lia).
set (E := Ereg regs ([] : list word)).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR : region_ok src2segs E memc (YQ0b.mkRegion (Some 2%nat) 80 88 80 80 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia| constructor]. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (20%nat, mkAF 1 65534 0); (24%nat, mkAF 0 65533 0); (26%nat, mkAF 0 65534 0);
(22%nat, mkAF 4096 CEIL_MAX 0); (23%nat, mkAF 4096 CEIL_MAX 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, (HE 27%nat 27%bv eq_refl), (HE 20%nat 20%bv eq_refl), (HE 24%nat 24%bv eq_refl), (HE 26%nat 26%bv eq_refl), (HE 22%nat 22%bv eq_refl), (HE 23%nat 23%bv eq_refl), G27, G20, G24, G26, G22, G23.
rewrite !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hsp0 Hsp1 Hsp16 HW HH Ht0 Htn Hn HiH HiW Hfimg0 Hfimg1 Hbimg0 Hbimg1 HNle Hac. repeat split; lia. }
assert (RE : regs_ok E (sr_set sr_atoms 19%bv (SLit 65535)) regs) by (apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact G19]).
assert (HS : st_ok src2segs E ss_f2l (mkst regs (Z_to_bv 64 FL_F2L) memc (seg_rom src2segs))).
{ unfold ss_f2l. subst E. apply entry_st_ok_full; [exact RE | vm_compute; reflexivity | constructor; [exact HR | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; exact I]]. }
clear HR HFA RE.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F2L) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_memcmp. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (ZX : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 25 0) (SLit 32)) (SLit 32)) = W * i).
{ rewrite U_zext32_mod, (U_atom E 25 v) by first [rewrite (HE 25%nat 25%bv eq_refl); exact G25 | exact Hv]. exact Hvmod. }
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssx) rq = sv -> getr (ms_regs msx) rq = sv_denot E sv)
by (intros rq sv Hrq; rewrite (st_ok_reg src2segs E ssx msx rq HS), Hrq; reflexivity) end.
assert (Ha0 : getr (ms_regs ms) 10 = Z_to_bv 64 (fimg + W * i)).
{ rewrite (RGX 10%bv _ eq_refl). eval_sr_get. apply denot_of_U'. apply (U_add_small E _ _ fimg (W * i)); [apply U_atom; [rewrite (HE 22%nat 22%bv eq_refl); exact G22 | clear - Hfimg0 Hfimg1 HiW HW Hac; lia] | exact ZX | clear - Hfimg0; lia | clear - HiW HW; lia | clear - Hfimg1 HiW Hac HW; lia]. }
assert (Ha1 : getr (ms_regs ms) 11 = Z_to_bv 64 (bimg + W * i)).
{ rewrite (RGX 11%bv _ eq_refl). eval_sr_get. apply denot_of_U'. apply (U_add_small E _ _ bimg (W * i)); [apply U_atom; [rewrite (HE 23%nat 23%bv eq_refl); exact G23 | clear - Hbimg0 Hbimg1 HiW HW Hac; lia] | exact ZX | clear - Hbimg0; lia | clear - HiW HW; lia | clear - Hbimg1 HiW Hac HW; lia]. }
jreg HS (12%bv:reg) as Ha2. rewrite (HE 27%nat 27%bv eq_refl), G27 in Ha2.
jreg HS (1%bv:reg) as Hra. clear RGX.
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc ss_f2l].
eapply SR_bind.
{ apply (memcmp_callD API mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC
STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) (W * i) FL_F2R HJ (KD_eq _ _ _ _ K0 K1) Hfi Hbi ltac:(clear - HiW HW; lia) ltac:(clear - HiW; lia)).
- rewrite Ha0. f_equal.
- rewrite Ha1. f_equal.
- exact Ha2.
- rewrite Hra. apply (ret_ok_even (Z_to_bv 64 FL_F2R)). vm_compute. reflexivity. }
cbv beta. intros c' (regs2 & r & -> & Hr10 & Rr & Hwit & Hfr2).
jafter_stretch_keep HS 33%nat regs2 (ms_mem ms) BCMP_CLOB FL_F2R [0%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor].
eapply (region_kept_out src2segs _ _ _ _ 0 0); [intros z _; reflexivity | apply mem_grows_of_eq; intros z; reflexivity
| cbn [r_base r_lo base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU2; lia
| intros a Ha; clear; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
change (ms_mem ms) with (ms_mem (mkst regs2 (Z_to_bv 64 FL_F2R) (ms_mem ms) (seg_rom src2segs))) in HJ.
set (E2 := havoc E 33 (map (getr regs2) BCMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (EXIT : forall ss ms' hrow, st_ok src2segs E2 ss ms' -> ss_pc ss = FL_F3 -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) F2_KEPT = true ->
top <= hrow < H -> getr (ms_regs ms') 20 = Z_to_bv 64 hrow ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall z, ms_mem ms' z = memc z) ->
f2_post STK sp0 FP L A mem md Lc Ac mdc regs memc top (mkCfg ms' mdc)).
{ intros ss ms' hrow HS' Hpc Hrv Hkl Hh Q20 HJ' K'. exists (ms_regs ms'), (ms_mem ms'), hrow.
assert (HKx : forall rr : reg, In rr F2_KEPT -> getr (ms_regs ms') rr = getr regs rr) by (intros rr Hrr; subst E E2; exact (regs_kept_of_st_ok src2segs _ ss ms' regs _ F2_KEPT HS' EA1 Hkl rr Hrr)).
split; [rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hh|]. split; [exact Q20|].
split; [rewrite (HKx 21%bv ltac:(cbv; auto 20)); exact G21|].
split; [rewrite (HKx 27%bv ltac:(cbv; auto 20)); exact G27|].
exact HKx. }
jbranch src2tbl HS.
-
clear Hc. jrun_to LAWS src2tbl_ok HS HJ FL_F3. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ i HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Ht0 Htn Hn HiH; lia)); [| exact HJ |].
+ reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 20%nat 20%bv eq_refl), G20, Z_to_bv_bv_unsigned; reflexivity).
+ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
-
clear Hc. jrun LAWS src2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
jbranch src2tbl HS.
+
rewrite branch_ltu_U, U_and_lit, (U_atom E2 24 top), (U_atom_off E2 20 i (-1)), land_ffff in Hc
by first [subst E2; ew_havocA; first [rewrite (HE 24%nat 24%bv eq_refl); exact G24 | rewrite (HE 20%nat 20%bv eq_refl); exact G20] | clear - Hi64 Htn Hn; lia].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.ltb_spec top (i + -1)) as [Hl|Hl]; [clear - Htn Hl; lia | discriminate Hc]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ FL_F2L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms1 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs _ F2_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR;
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg src2segs Ef ssf msf rq HS), Hrq; reflexivity) end.
set (v' := U E2 (SAluw ALU_SUB (SOff 25 0) (SOff 27 0))).
assert (Hv' : 0 <= v' < 2 ^ 64) by (apply U_range).
assert (Hv'mod : v' mod 2 ^ 32 = W * (i - 1)).
{ subst v'. rewrite U_subw_mod32, (U_atom E2 25 v), (U_atom E2 27 W) by first [subst E2; ew_havocA; first [rewrite (HE 25%nat 25%bv eq_refl); exact G25 | rewrite (HE 27%nat 27%bv eq_refl); exact G27] | clear - Hv HW; lia].
rewrite <- Zminus_mod_idemp_l, Hvmod. replace (W * i - W) with (W * (i - 1)) by (clear; lia). apply Z.mod_small. clear - HiW HNle HW; lia. }
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i - 1) v' STK sp0 FP L A mem md Lc Ac mdc _ _ top HJ (KD_eq _ _ _ _ K0 K3) Hfi Hbi Hv'mod Hv' Ht0 ltac:(clear - Htn; lia) Hn1 ltac:(clear - HiH; lia)).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (RGX 19%bv (SLit 65535) eq_refl). reflexivity.
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity).
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 20%nat 20%bv eq_refl), G20, unsigned_lit_small by (clear - Hi64; lia); f_equal; clear; lia).
- rewrite (HKR 22%bv ltac:(cbv; auto 20)). exact G22.
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 24%nat 24%bv eq_refl), G24, Z_to_bv_bv_unsigned; reflexivity).
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- rewrite (RGX 25%bv _ eq_refl). eval_sr_get. apply denot_of_U'. reflexivity.
- rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact G26.
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21. }
cbv beta. intros c' (regs' & mem' & hrow & -> & HJ' & K' & Hh & Q20 & Q21 & Q27 & HK'). exists regs', mem', hrow.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K3|]. split; [exact Hh|]. split; [exact Q20|]. split; [exact Q21|]. split; [exact Q27|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
rewrite branch_ltu_U, U_and_lit, (U_atom E2 24 top), (U_atom_off E2 20 i (-1)), land_ffff in Hc
by first [subst E2; ew_havocA; first [rewrite (HE 24%nat 24%bv eq_refl); exact G24 | rewrite (HE 20%nat 20%bv eq_refl); exact G20] | clear - Hi64 Htn Hn; lia].
assert (Hit : i - 1 = top) by (destruct (Z.ltb_spec top (i + -1)) as [Hl|Hl]; [discriminate Hc | clear - Htn Hn Hl; lia]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ FL_F3. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ top HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Ht0 HiH Hit; lia)); [| exact HJ |].
* reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity).
* intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2.
Qed.
Definition F2S_KEPT : list reg := [2; 3; 4; 8; 9; 18; 22; 23; 26; 27]%bv.
Definition f2s_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (top : Z) (c' : config) : Prop :=
exists regs' mem' hrow,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F3) mem' (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KD mem0 spv mem' /\
top <= hrow < H /\ getr regs' 20 = Z_to_bv 64 hrow /\ getr regs' 21 = Z_to_bv 64 top /\ getr regs' 27 = Z_to_bv 64 W /\
(forall r : reg, In r F2S_KEPT -> getr regs' r = getr regs r).
Lemma fl_f2 : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top : Z),
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
spv = sp0 - 272 -> 272 <= STK -> 0 <= top < H ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 22 = Z_to_bv 64 fimg -> getr regs 23 = Z_to_bv 64 bimg -> getr regs 27 = Z_to_bv 64 W -> getr regs 26 = Z_to_bv 64 top ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 FL_F2) memc (seg_rom src2segs)) mdc) (f2s_post STK sp0 FP L A mem md Lc Ac mdc regs top).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc top HJ K0 Hfi Hbi Hspv HSTK Htop G2 G22 G23 G27 G26.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
assert (Hstw : forall a, spv <= a < spv + 88 -> writable_at src2segs memc a).
{ intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hw) & _). apply Hw. clear - Ha Hspv HSTK. lia. }
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC memc K0) as (_ & _ & _ & _ & _ & WHm).
set (E := Ereg regs (map (Z_to_bv 64) [H - 1] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (H - 1)) by (subst E; apply (Ereg_vals regs [H - 1] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR : region_ok src2segs E memc (YQ0b.mkRegion (Some 2%nat) 64 112 64 88 [mkChunk 96 (CVal 8 (SOff 32 1))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
constructor; [|constructor]. eapply (chunk_ok_val _ _ _ _ _ _ _ H); [cbn [sv_denot]; rewrite HE32, unsigned_lit_small by lia; f_equal; lia | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WHm]. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (32%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0);
(22%nat, mkAF 4096 CEIL_MAX 0); (23%nat, mkAF 4096 CEIL_MAX 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE32, (HE 27%nat 27%bv eq_refl), (HE 26%nat 26%bv eq_refl), (HE 22%nat 22%bv eq_refl), (HE 23%nat 23%bv eq_refl), G27, G26, G22, G23.
assert (HN1 : 1 <= N) by (rewrite HN; clear - HW HH; nia).
rewrite !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. clear - Hsp0 Hsp1 Hsp16 HW HH Htop Hfimg0 Hfimg1 Hbimg0 Hbimg1 HN1 Hac. repeat split; lia. }
assert (HCF : forall z : bool, (if z then top = H - 1 else top < H - 1) ->
conds_ok E [mkAC BC_NE (SOff 26 0) (SOff 32 1); mkAC (if z then BC_GEU else BC_LTU) (SAlu ALU_AND (SOff 26 0) (SLit 65535)) (SAlu ALU_AND (SOff 32 0) (SLit 65535))]).
{ intros z Hz. cbn [conds_ok]. split; [| split; [| exact I]]; unfold acond_ok; cbn [ac_c ac_a ac_b].
- rewrite branch_ne_U, (U_atom E 26 top), (U_atom_off E 32 (H - 1) 1) by first [exact HE32 | rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Htop HH; lia].
destruct (Z.eqb_spec top (H - 1 + 1)); [clear - Htop e; lia | reflexivity].
- destruct z; rewrite ?branch_geu_U, ?branch_ltu_U, !U_and_lit, (U_atom E 26 top), (U_atom E 32 (H - 1)), !land_ffff by first [exact HE32 | rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Htop HH; lia];
(destruct (Z.ltb_spec top (H - 1)) as [Hl|Hl]; cbn [negb]; first [reflexivity | exfalso; clear - Hz Hl; lia]). }
assert (MK : forall z : bool, (if z then top = H - 1 else top < H - 1) -> st_ok src2segs E (ss_f2 z) (mkst regs (Z_to_bv 64 FL_F2) memc (seg_rom src2segs))).
{ intros z Hz. unfold ss_f2. subst E. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; destruct z; reflexivity | constructor; [exact HR | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; [exact (HCF z Hz) | exact I]]]. }
clear HR HFA HCF.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F2) memc (seg_rom src2segs))) in HJ.
assert (EXIT : forall ss ms' hrow, st_ok src2segs E ss ms' -> ss_pc ss = FL_F3 -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) F2S_KEPT = true ->
top <= hrow < H -> getr (ms_regs ms') 20 = Z_to_bv 64 hrow -> getr (ms_regs ms') 21 = Z_to_bv 64 top -> getr (ms_regs ms') 27 = Z_to_bv 64 W ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> KD mem0 spv (ms_mem ms') ->
f2s_post STK sp0 FP L A mem md Lc Ac mdc regs top (mkCfg ms' mdc)).
{ intros ss ms' hrow HS' Hpc Hrv Hkl Hh Q20 Q21 Q27 HJ' K'. exists (ms_regs ms'), (ms_mem ms'), hrow.
split; [rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hh|].
split; [exact Q20|]. split; [exact Q21|]. split; [exact Q27|].
intros rr Hrr. subst E. exact (regs_kept_of_st_ok src2segs _ ss ms' regs _ F2S_KEPT HS' (env_agree_refl _ _) Hkl rr Hrr). }
destruct (Z.eq_dec top (H - 1)) as [Hte | Hte].
-
pose proof (MK true Hte) as HS. clear MK.
jrun_to LAWS src2tbl_ok HS HJ FL_F3. { eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (K1 : KD mem0 spv (ms_mem ms)).
{ apply (KD_frame _ _ _ _ K0). intros a Ha Hna1 Hna2 Hna3. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU2. clear - Hna2. lia. }
clear HF HG.
apply SR_ret. apply (EXIT _ _ (H - 1) HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Hte Htop; lia)); [| | | exact HJ | exact K1].
+ reg_nowF HS ltac:(rewrite HE32, Z_to_bv_bv_unsigned; reflexivity).
+ reg_nowF HS ltac:(rewrite (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity).
+ reg_nowF HS ltac:(rewrite (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity).
-
assert (Htl : top < H - 1) by (clear - Htop Hte; lia).
pose proof (MK false Htl) as HS. clear MK.
jrun_to LAWS src2tbl_ok HS HJ FL_F2L. { eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (K1 : KD mem0 spv (ms_mem ms)).
{ apply (KD_frame _ _ _ _ K0). intros a Ha Hna1 Hna2 Hna3. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU2. clear - Hna2. lia. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks src2segs E ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs;
pose proof (regs_kept_of_st_ok src2segs E ssx msx regs _ F2S_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssx) rq = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg src2segs E ssx msx rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssx) rq = sv -> getr (ms_regs msx) rq = sv_denot E sv)
by (intros rq sv Hrq; rewrite (st_ok_reg src2segs E ssx msx rq HS), Hrq; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (HiW : 0 <= W * (H - 1) /\ W * (H - 1) + W <= N) by (rewrite HN; clear - HW HH; nia).
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (fl_f2l (Z.to_nat (H - 1 - top)) (H - 1) (W * (H - 1)) STK sp0 FP L A mem md Lc Ac mdc _ _ top HJ K1 Hfi Hbi ltac:(apply Z.mod_small; clear - HiW HNle HW; lia) ltac:(clear - HiW HNle HW; lia)
ltac:(clear - Htop; lia) ltac:(clear - Htl; lia) ltac:(clear - Htl; lia) ltac:(clear; lia)).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (RGX 19%bv (SLit 65535) eq_refl). reflexivity.
- rewrite (HKR 27%bv ltac:(cbv; auto 20)). exact G27.
- apply (RG 20%bv 32%nat _ eq_refl). exact HE32.
- rewrite (HKR 22%bv ltac:(cbv; auto 20)). exact G22.
- rewrite (RGX 24%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite U_and_lit, (U_atom E 26 top) by first [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Htop HH; lia]. apply land_ffff. clear - Htop HH; lia.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- rewrite (RGX 25%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite (Z.mul_comm W (H - 1)). apply (U_mul_small' E _ _ (H - 1) W); [apply (U_atom E 32 (H - 1) HE32); clear - HH; lia | apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - HH; lia | clear - HW; lia | clear - HiW HNle HW; nia].
- rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact G26.
- reg_nowF HS ltac:(rewrite (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity). }
cbv beta. intros c' (regs2 & mem2 & hrow & -> & HJ2 & K2 & Hh2 & Q20 & Q21 & Q27 & HK2). exists regs2, mem2, hrow.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact (KD_eq _ _ _ _ K1 K2)|]. split; [exact Hh2|]. split; [exact Q20|]. split; [exact Q21|]. split; [exact Q27|].
intros rr Hrr. rewrite (HK2 rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). apply (HKR rr Hrr).
Qed.
End c.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
