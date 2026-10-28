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
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b
YI06 UI5b YI09 YI08 YI0r YI0o UI1w UI3p UI3m UI3t
UI3w UI4j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w UI2v UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma U_sext32_high : forall E a r, U E a = r -> 2 ^ 31 <= r < 2 ^ 32 ->
U E (SExt true 32 a) = r - 2 ^ 32 + 2 ^ 64.
Proof using.
intros E a r Ha Hr. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small r) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
change (2 ^ 32 / 2) with (2 ^ 31).
replace ((r + 2 ^ 31) mod 2 ^ 32) with (r + 2 ^ 31 - 2 ^ 32).
2:{ replace (r + 2 ^ 31) with ((r + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) at 2 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
unfold zcanon, M64. replace (r + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((r - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Definition entry_ss (fs : list (nat * afact)) : sstate :=
mkSS ubs0_A_cgif_raw_addframe sr_atoms
[ YP09.mkRegion (Some 2%nat) (-144) 0 (-144) 0 [] ;
YP09.mkRegion (Some 11%nat) 0 40 0 0 (obj_chunks_gen LAY_RawFrameConfig 32 lits_RFC) ;
YP09.mkRegion (Some 10%nat) 0 RAW_SIZE 0 0 (obj_chunks_gen LAY_Raw 43 lits_Raw) ;
YP09.mkRegion (Some 44%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 52 lits_CGIF) ]
None
(mkFacts (fs ++ [ (2%nat, mkAF (CEIL_MIN + 8704) (2^63) 4); (11%nat, mkAF (CEIL_MIN + 8704) (2^63 - 40) 3);
(10%nat, mkAF 4096 (CEIL_MAX - 48) 4); (44%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(34%nat, mkAF 0 (2^32-1) 0); (40%nat, mkAF 0 65535 0) ]) [] []).
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Variables (IMGV LCTV : list Z).
Definition at_A (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (c' : config) : Prop :=
exists regs1 mem1,
c' = mkCfg (mkst regs1 (Z_to_bv 64 PC_A) mem1 (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L A mem1 md /\
ra_regs regs1 cx /\ getr regs1 19 = Z_to_bv 64 (c_fattr cx) /\ getr regs1 23 = Z_to_bv 64 (c_slct cx) /\
objs_at mem1 cx (c_rcur cx) /\ frame_savedN ubs0_msyms 12 regs0 mem1 (spZ regs0).
Lemma ra_entry_R :
forall cx L A (regs0 : bvmap 5 word) mem md (b : rbound),
rcx_pre cx -> ra_origin cx regs0 ->
fn_pre ubs0_msyms MR RAWADD_STK L A regs0 mem md -> st_init_done A = true -> res_ok A b ->
getr regs0 10 = Z_to_bv 64 (c_raw cx) -> getr regs0 11 = Z_to_bv 64 (c_cfp cx) ->
objs_at mem cx (c_rcur cx) -> Permutation (blocks L A) (c_blocks cx) ->
SR ubs0segs (mkCfg (mkst regs0 (Z_to_bv 64 ubs0_A_cgif_raw_addframe) mem (seg_rom ubs0segs)) md)
(fun c' => ra_postR API [(c_raw cx + 40, c_raw cx + 44)] (ra_exitX cx IMGV LCTV) (fun s => res_ok s (rawadd_rb b)) cx L A mem md regs0 c' \/
(c_slct cx <= 256 /\ (c_rcur cx = 0 \/ c_rcur cx = 6) /\ at_A cx L A mem md regs0 c')).
Proof using IMG.
intros cx L A regs0 mem md b Hcx HO HPRE Hid HRq G10 G11 Hobjs HB.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof (objs_fields_ok _ _ _ Hobjs) as HFO.
pose proof Hobjs as (OC & OR & OG).
pose proof Hcx as (Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47).
pose proof HFO as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
assert (Hrawin : In (c_raw cx, RAW_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
set (sp := spZ regs0) in *.
remember (Ereg regs0 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs0 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs0 cx (c_rcur cx) []) as HX. pose proof (E_rv regs0 cx (c_rcur cx) []) as HY. pose proof (E_gv regs0 cx (c_rcur cx) [] LG) as HZ.
rewrite <- HE0 in HX, HY, HZ.
assert (HE2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HE10 : ew E 10 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE11 : ew E 11 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 (c_fattr cx)) by (apply (HX 2%nat); reflexivity).
assert (HE40 : ew E 40 = Z_to_bv 64 (c_slct cx)) by (apply (HX 8%nat); reflexivity).
assert (HE51 : ew E 51 = Z_to_bv 64 (c_rcur cx)) by (apply (HY 8%nat); reflexivity).
assert (MKS : forall lo hi, lo <= c_rcur cx <= hi ->
st_ok ubs0segs E (entry_ss [(51%nat, mkAF lo hi 0)]) (mkst regs0 (Z_to_bv 64 ubs0_A_cgif_raw_addframe) mem (seg_rom ubs0segs))).
{ intros lo hi Hlh. subst E. unfold entry_ss. apply entry_st_ok; rewrite <- ?HE0.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack ubs0segs _ mem 2 sp); [exact HE2 | lia | lia | intros a Ha; apply Hstw; lia].
+ eapply (region_ok_obj_gen ubs0segs _ mem 11 (c_cfp cx)); [rewrite HE11; apply unsigned_lit_small; lia | lia | lia | exact OC | reflexivity | exact HX | | intros i Hi; lia].
intros j z Hj. do 11 (destruct j as [|j]; [discriminate Hj|]). destruct j; discriminate Hj.
+ eapply (region_ok_obj_gen ubs0segs _ mem 10 (c_raw cx)); [rewrite HE10; apply unsigned_lit_small; lia | lia | lia | exact OR | reflexivity | exact HY | apply lits_Raw_ok; reflexivity | intros i Hi; lia].
+ eapply (region_ok_obj_gen ubs0segs _ mem 44 (c_g cx)); [rewrite HE44; apply unsigned_lit_small; lia | lia | lia | exact OG | reflexivity | exact HZ | apply (lits_CGIF_ok _ Hwfn Hfile) | intros i Hi; lia].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE10, HE11, HE44, !unsigned_lit_small by lia. repeat split; lia.
- cbn [atoms_ok app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE11, HE44, HE34, HE40, HE51, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; first [assumption | lia]. }
pose proof (journal_init ubs0_msyms MR RAWADD_STK [(c_raw cx + 40, c_raw cx + 44)] L A regs0 mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs0 (Z_to_bv 64 ubs0_A_cgif_raw_addframe) mem (seg_rom ubs0segs))) in HJ.
fold sp in HJ.
Ltac wr HE2 := eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
Ltac early_ret HS HJ HE HE0 HE2 Hra Hid OR HRq QT :=
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
[ exact (proj1 (heap_model _ _ (aa_laws _) _ _ _ _ (proj1 HJ)))
| exact (proj1 (proj2 (heap_model _ _ (aa_laws _) _ _ _ _ (proj1 HJ))))
| left; unfold ra_postR;
let HPR := fresh "HPR" in
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HPR;
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lf ?Af _ ?mdf =>
exists Lf, Af, (ms_regs msf), (ms_mem msf), mdf, (bv_unsigned (getr (ms_regs msf) 10)) end end;
eexists; split;
[ let Q := fresh "Q" in (jreg HS (1%bv:reg) as Q); rewrite Q, (HE 1%nat 1%bv eq_refl), Hra; reflexivity
| split; [exact HJ|]; split; [exact HPR|]; split; [exact Hid|]; split; [rewrite Z_to_bv_bv_unsigned; reflexivity|];
split; [ cbn [ms_mem mkst]; eapply obj_at_transport_range; [exact OR | exact (proj1 LAY_Raw_ok) |];
(let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H))
| split; [apply Permutation_refl | split; [QT | apply ra_rb_entry; exact HRq]] ] ] ].
assert (Hcases : c_rcur cx = 0 \/ c_rcur cx = 6 \/ (1 <= c_rcur cx <= 5) \/ (7 <= c_rcur cx < 2 ^ 31) \/ (2 ^ 31 <= c_rcur cx < 2 ^ 32)) by lia.
destruct Hcases as [Hr0 | [Hr6 | [Hr15 | [Hr7 | Hr31]]]].
-
pose proof (MKS 0 0 ltac:(lia)) as HS. clear MKS.
jrun LAWS ubs0tbl_ok HS HJ; [wr HE2|].
jbranch ubs0tbl HS.
{ exfalso. rewrite branch_ne_U, (U_atom _ 51 (c_rcur cx) HE51), U_lit in Hc by lia. rewrite Hr0 in Hc. discriminate Hc. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJ; [wr HE2|].
jbranch ubs0tbl HS.
+
rewrite branch_ltu_U, (U_atom _ 40 (c_slct cx) HE40), U_lit in Hc by lia.
assert (Hsl : c_slct cx <= 256) by (destruct (Z.ltb_spec (c_slct cx) 257); [lia | discriminate]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ PC_A; [wr HE2|].
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret. right.
split; [exact Hsl|]. split; [left; exact Hr0|].
lazymatch goal with |- at_A _ _ _ _ _ _ (mkCfg ?msx _) => exists (ms_regs msx), (ms_mem msx) end.
split; [reflexivity|]. cbn [ms_regs ms_mem mkst]. split; [exact HJ|].
split.
{ unfold ra_regs. repeat split.
- jreg HS (2%bv:reg) as Q. rewrite Q. cbn [sv_denot]. rewrite HE2. unfold c_spe in *. f_equal. subst sp. lia.
- jreg HS (8%bv:reg) as Q. rewrite Q. exact HE10.
- jreg HS (9%bv:reg) as Q. rewrite Q. exact HE11.
- jreg HS (4%bv:reg) as Q. rewrite Q, (HE 4%nat 4%bv eq_refl), Htp, Htpv. reflexivity.
- jreg HS (3%bv:reg) as Q. rewrite Q, (HE 3%nat 3%bv eq_refl). exact Hgp0.
- jreg HS (27%bv:reg) as Q. rewrite Q, (HE 27%nat 27%bv eq_refl). exact H27o. }
split; [jreg HS (19%bv:reg) as Q; rewrite Q; exact HE34|].
split; [jreg HS (23%bv:reg) as Q; rewrite Q; exact HE40|].
split.
{ cbn [ms_mem]. eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
cbn [ms_mem].
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (frame_savedN_of_region ubs0_msyms 12 E1);
[ eapply (st_ok_region_nth E1 ss1 ms1 0%nat); [exact HS | reflexivity]
| exact HE2
| intros rr d Hrd; cbv [SAVEDN SAVED firstn In] in Hrd;
repeat (destruct Hrd as [Hrd | Hrd];
[ injection Hrd as <- <-; eexists; split; [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply HE; reflexivity] | ]);
destruct Hrd ] end.
+
rewrite branch_ltu_U, (U_atom _ 40 (c_slct cx) HE40), U_lit in Hc by lia.
assert (Hsl : 257 <= c_slct cx) by (destruct (Z.ltb_spec (c_slct cx) 257); [discriminate | lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ PC_ST; [wr HE2|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs0 _ [3; 4; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (2%bv:reg) as Q2. jreg HS (8%bv:reg) as Q8. jreg HS (18%bv:reg) as Q18.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono; [| cbv beta; intros c' Hc'; left; exact Hc'].
lazymatch goal with |- SR _ (mkCfg (mkst ?rx _ ?mx _) _) _ => eapply (ra_st_R API IMG [(c_raw cx + 40, c_raw cx + 44)] (ra_exitX cx IMGV LCTV) (fun s => res_ok s (rawadd_rb b)) cx L A mem md L A md regs0 rx mx (c_rcur cx)) end;
[ exact Hcx | exact HO | exact HJ | exact Hid | apply ra_rb_entry; exact HRq | apply Permutation_refl | exact Hrawin | | | | apply HK; cbv; tauto | apply HK; cbv; tauto | apply HK; cbv; tauto | rewrite Q8; exact HE10 | exact Q18
| intros a Ha; exists (c_raw cx + 40, c_raw cx + 44); split; [left; reflexivity | cbn; lia]
| apply exitX_badlct; [first [left; assumption | right; assumption] | lia | cbn [sv_denot]; vm_compute; reflexivity] ]; cbn [ms_regs ms_mem mkst].
* cbn [ms_mem]. eapply obj_at_transport_range; [exact OR | exact (proj1 LAY_Raw_ok) |].
intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H).
* cbn [ms_mem].
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (frame_savedN_of_region ubs0_msyms 12 E1);
[ eapply (st_ok_region_nth E1 ss1 ms1 0%nat); [exact HS | reflexivity]
| exact HE2
| intros rr d Hrd; cbv [SAVEDN SAVED firstn In] in Hrd;
repeat (destruct Hrd as [Hrd | Hrd];
[ injection Hrd as <- <-; eexists; split; [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply HE; reflexivity] | ]);
destruct Hrd ] end.
* rewrite Q2. cbn [sv_denot]. rewrite HE2. f_equal. subst sp. lia.
-
pose proof (MKS 6 6 ltac:(lia)) as HS. clear MKS.
jrun LAWS ubs0tbl_ok HS HJ; [wr HE2|].
jbranch ubs0tbl HS.
2:{ exfalso. rewrite branch_eq_U, (U_atom _ 51 (c_rcur cx) HE51), U_lit in Hc by lia. rewrite Hr6 in Hc. discriminate Hc. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJ; [wr HE2|].
jbranch ubs0tbl HS.
+
rewrite branch_ltu_U, (U_atom _ 40 (c_slct cx) HE40), U_lit in Hc by lia.
assert (Hsl : c_slct cx <= 256) by (destruct (Z.ltb_spec (c_slct cx) 257); [lia | discriminate]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ PC_A; [wr HE2|].
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret. right.
split; [exact Hsl|]. split; [right; exact Hr6|].
lazymatch goal with |- at_A _ _ _ _ _ _ (mkCfg ?msx _) => exists (ms_regs msx), (ms_mem msx) end.
split; [reflexivity|]. cbn [ms_regs ms_mem mkst]. split; [exact HJ|].
split.
{ unfold ra_regs. repeat split.
- jreg HS (2%bv:reg) as Q. rewrite Q. cbn [sv_denot]. rewrite HE2. unfold c_spe in *. f_equal. subst sp. lia.
- jreg HS (8%bv:reg) as Q. rewrite Q. exact HE10.
- jreg HS (9%bv:reg) as Q. rewrite Q. exact HE11.
- jreg HS (4%bv:reg) as Q. rewrite Q, (HE 4%nat 4%bv eq_refl), Htp, Htpv. reflexivity.
- jreg HS (3%bv:reg) as Q. rewrite Q, (HE 3%nat 3%bv eq_refl). exact Hgp0.
- jreg HS (27%bv:reg) as Q. rewrite Q, (HE 27%nat 27%bv eq_refl). exact H27o. }
split; [jreg HS (19%bv:reg) as Q; rewrite Q; exact HE34|].
split; [jreg HS (23%bv:reg) as Q; rewrite Q; exact HE40|].
split.
{ cbn [ms_mem]. eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
cbn [ms_mem].
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (frame_savedN_of_region ubs0_msyms 12 E1);
[ eapply (st_ok_region_nth E1 ss1 ms1 0%nat); [exact HS | reflexivity]
| exact HE2
| intros rr d Hrd; cbv [SAVEDN SAVED firstn In] in Hrd;
repeat (destruct Hrd as [Hrd | Hrd];
[ injection Hrd as <- <-; eexists; split; [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply HE; reflexivity] | ]);
destruct Hrd ] end.
+
rewrite branch_ltu_U, (U_atom _ 40 (c_slct cx) HE40), U_lit in Hc by lia.
assert (Hsl : 257 <= c_slct cx) by (destruct (Z.ltb_spec (c_slct cx) 257); [discriminate | lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ PC_ST; [wr HE2|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs0 _ [3; 4; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (2%bv:reg) as Q2. jreg HS (8%bv:reg) as Q8. jreg HS (18%bv:reg) as Q18.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono; [| cbv beta; intros c' Hc'; left; exact Hc'].
lazymatch goal with |- SR _ (mkCfg (mkst ?rx _ ?mx _) _) _ => eapply (ra_st_R API IMG [(c_raw cx + 40, c_raw cx + 44)] (ra_exitX cx IMGV LCTV) (fun s => res_ok s (rawadd_rb b)) cx L A mem md L A md regs0 rx mx (c_rcur cx)) end;
[ exact Hcx | exact HO | exact HJ | exact Hid | apply ra_rb_entry; exact HRq | apply Permutation_refl | exact Hrawin | | | | apply HK; cbv; tauto | apply HK; cbv; tauto | apply HK; cbv; tauto | rewrite Q8; exact HE10 | exact Q18
| intros a Ha; exists (c_raw cx + 40, c_raw cx + 44); split; [left; reflexivity | cbn; lia]
| apply exitX_badlct; [first [left; assumption | right; assumption] | lia | cbn [sv_denot]; vm_compute; reflexivity] ]; cbn [ms_regs ms_mem mkst].
* cbn [ms_mem]. eapply obj_at_transport_range; [exact OR | exact (proj1 LAY_Raw_ok) |].
intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H).
* cbn [ms_mem].
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (frame_savedN_of_region ubs0_msyms 12 E1);
[ eapply (st_ok_region_nth E1 ss1 ms1 0%nat); [exact HS | reflexivity]
| exact HE2
| intros rr d Hrd; cbv [SAVEDN SAVED firstn In] in Hrd;
repeat (destruct Hrd as [Hrd | Hrd];
[ injection Hrd as <- <-; eexists; split; [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply HE; reflexivity] | ]);
destruct Hrd ] end.
* rewrite Q2. cbn [sv_denot]. rewrite HE2. f_equal. subst sp. lia.
-
pose proof (MKS 1 5 ltac:(lia)) as HS. clear MKS.
jrun LAWS ubs0tbl_ok HS HJ; [wr HE2|].
early_ret HS HJ HE HE0 HE2 Hra Hid OR HRq ltac:(idtac; apply exitX_prev; [lia | lia | lia |]; (jreg HS (10%bv:reg) as QA0); rewrite QA0, HE51, unsigned_lit_small by lia; destruct (Z.ltb_spec (c_rcur cx) (2 ^ 31)); [reflexivity | lia]).
-
pose proof (MKS 7 (2 ^ 31 - 1) ltac:(lia)) as HS. clear MKS.
jrun LAWS ubs0tbl_ok HS HJ; [wr HE2|].
early_ret HS HJ HE HE0 HE2 Hra Hid OR HRq ltac:(idtac; apply exitX_prev; [lia | lia | lia |]; (jreg HS (10%bv:reg) as QA0); rewrite QA0, HE51, unsigned_lit_small by lia; destruct (Z.ltb_spec (c_rcur cx) (2 ^ 31)); [reflexivity | lia]).
-
pose proof (MKS (2 ^ 31) (2 ^ 32 - 1) ltac:(lia)) as HS. clear MKS.
jrun LAWS ubs0tbl_ok HS HJ; [wr HE2|].
jbranch ubs0tbl HS.
{ exfalso. rewrite branch_eq_U, (U_sext32_high _ _ (c_rcur cx) (U_atom _ 51 (c_rcur cx) HE51 ltac:(lia)) ltac:(lia)), U_lit in Hc by lia.
destruct (Z.eqb_spec (c_rcur cx - 2 ^ 32 + 2 ^ 64) 6); [lia | discriminate Hc]. }
clear Hc. jrun LAWS ubs0tbl_ok HS HJ; [wr HE2|].
jbranch ubs0tbl HS.
2:{ exfalso. rewrite branch_ne_U, (U_sext32_high _ _ (c_rcur cx) (U_atom _ 51 (c_rcur cx) HE51 ltac:(lia)) ltac:(lia)), U_lit in Hc by lia.
destruct (Z.eqb_spec (c_rcur cx - 2 ^ 32 + 2 ^ 64) 0); [lia | discriminate Hc]. }
clear Hc. jrun LAWS ubs0tbl_ok HS HJ; [wr HE2|].
early_ret HS HJ HE HE0 HE2 Hra Hid OR HRq ltac:(idtac; apply exitX_prev; [lia | lia | lia |];
(lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 => pose proof (st_ok_reg segs E1 ss1 ms1 (10%bv:reg) HS) as QB0; eval_sr_get_in QB0 end); rewrite QB0;
lazymatch goal with |- bv_unsigned (sv_denot ?Ex ?e) = ?rhs => change (U Ex e = rhs) end;
rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SLit, (U_sext32_high _ _ (c_rcur cx) (U_atom _ 51 (c_rcur cx) HE51 ltac:(lia)) ltac:(lia)); change (zcanon 0) with 0;
rewrite Z.add_0_r, zcanon_id by (unfold M64; lia); destruct (Z.ltb_spec (c_rcur cx) (2 ^ 31)); [lia | reflexivity]).
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
