(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m
YI00 YI02 YI01 YI03 YI04 UI1e UI2m UI26 UI2r
UI2s UO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition pow2_ok (s p : Z) : Prop := (s = 0 -> p = 0) /\ (s <> 0 -> 1 <= p <= 8 /\ s <= 2 ^ p).
Definition ssA (fs : list (nat * afact)) : sstate := ra_ssW PC_A sr_atoms 0 0 [] false fs [] [].
Definition PC_M : Z := RA0 + 0x90.
Definition ssM (fs : list (nat * afact)) : sstate := ra_ssW PC_M sr_atoms 37 47 [] false fs [] [].
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition at_B (cx : ra_cx) L A mem md L1 A1 md1 (regs0 : bvmap 5 word) (c' : config) : Prop :=
exists regs1 mem1 (p : Z),
c' = mkCfg (mkst regs1 (Z_to_bv 64 PC_B) mem1 (seg_rom ubs2segs)) md1 /\
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 /\
ra_regs regs1 cx /\ getr regs1 19 = Z_to_bv 64 (c_fattr cx) /\ getr regs1 23 = Z_to_bv 64 (c_slct cx) /\
getr regs1 22 = Z_to_bv 64 (c_cfp cx + 30) /\
getr regs1 24 = Z_to_bv 64 p /\ pow2_ok (c_slct cx) p /\
getr regs1 11 = Z_to_bv 64 (if c_slct cx =? 0 then c_raw cx + 32 else c_cfp cx + 30) /\
objs_at mem1 cx (c_rcur cx) /\ frame_savedN ubs2_msyms 12 regs0 mem1 (spZ regs0).
Definition at_M (cx : ra_cx) L A mem md L1 A1 md1 (regs0 : bvmap 5 word) (c' : config) : Prop :=
exists regs3 mem3,
c' = mkCfg (mkst regs3 (Z_to_bv 64 PC_M) mem3 (seg_rom ubs2segs)) md1 /\
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem3 md1 /\
ra_regs regs3 cx /\ getr regs3 19 = Z_to_bv 64 (c_fattr cx) /\ getr regs3 23 = Z_to_bv 64 (c_slct cx) /\
getr regs3 22 = Z_to_bv 64 (c_cfp cx + 30) /\
objs_at mem3 cx (c_rcur cx) /\ frame_savedN ubs2_msyms 12 regs0 mem3 (spZ regs0).
Lemma ra_memset :
forall cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 ->
ra_regs regs1 cx -> getr regs1 19 = Z_to_bv 64 (c_fattr cx) -> getr regs1 23 = Z_to_bv 64 (c_slct cx) ->
objs_at mem1 cx (c_rcur cx) -> frame_savedN ubs2_msyms 12 regs0 mem1 (spZ regs0) ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_A) mem1 (seg_rom ubs2segs)) md1)
(at_M cx L A mem md L1 A1 md1 regs0).
Proof.
intros cx L A mem md L1 A1 md1 regs0 regs1 mem1 Hcx HO HJ HR G19 G23 Hobjs HFS.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof (objs_fields_ok _ _ _ Hobjs) as HFO.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv) & Hslct).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hstw. cbn beta in Hstw.
remember (Ereg regs1 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HS : st_ok ubs2segs E (ssA []) (mkst regs1 (Z_to_bv 64 PC_A) mem1 (seg_rom ubs2segs))).
{ subst E. unfold ssA.
apply (ra_st_okW cx (c_rcur cx) regs1 [] mem1 PC_A sr_atoms 0 0 false [] [] [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_Ereg.
- intros a Ha. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- constructor.
- constructor.
- constructor. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_A) mem1 (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memset; [eapply ra_wr_okW; [exact HE2 | lia | lia | intros X; lia | left; cbn; lia]|].
jreg HS (10%bv:reg) as Ma0. rewrite HE2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
jreg HS (22%bv:reg) as M22.
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [2; 3; 4; 8; 9; 19; 23; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
assert (MEQ0 : forall x : word, ms_mem ms x = mem1 x).
{ intros x. lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) x) end. }
eapply SR_bind.
{ lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset_spec E1 ss1 ms1 _ _ _ _ _ _ _ _ _ _ (c_sp cx + 38) 0 9);
[ exact HS | reflexivity | reflexivity | exact HJ | first [exact Ma0 | rewrite Ma0; f_equal; lia] | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ] end.
- intros i Hi. destruct (writable_off_img_present mem1 (c_sp cx + 38 + i) ltac:(lia) ltac:(unfold in_img1; lia) ltac:(apply Hstw; lia)) as [b Hb].
exists b. rewrite MEQ0. exact Hb.
- intros a Ha. left. lia. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hz3).
cbn [ms_regs ms_mem] in Hfr3, Hout3, Hgr3, HJ3.
assert (F : forall r : reg, In r [2; 3; 4; 8; 9; 19; 23; 27]%bv -> getr regs3 r = getr regs1 r).
{ intros r Hr. rewrite (Hfr3 r). { apply HK. exact Hr. }
cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
assert (G22 : getr regs3 22 = Z_to_bv 64 (c_cfp cx + 30)).
{ rewrite (Hfr3 22%bv) by (vm_compute; reflexivity). rewrite M22. cbn [sv_denot]. rewrite HE9, unsigned_lit_small by lia. reflexivity. }
assert (MEQ3 : forall a, ~ (c_sp cx + 38 <= a < c_sp cx + 47) -> 0 <= a < 2 ^ 64 -> mbyte ubs2segs mem3 a = mbyte ubs2segs mem1 a).
{ intros a Ha Ha'. apply mbyte_eq_of1'. rewrite (Hout3 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). apply MEQ0. }
apply SR_ret. exists regs3, mem3. split; [reflexivity|]. split; [exact HJ3|].
split; [unfold ra_regs; rewrite !F by (cbv; tauto); repeat split; assumption|].
split; [rewrite F by (cbv; tauto); exact G19|].
split; [rewrite F by (cbv; tauto); exact G23|].
split; [exact G22|].
split.
- eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; apply MEQ3; lia.
- eapply (frame_savedN_kept ubs2_msyms 12); [lia | exact HFS|]. intros a Ha. apply MEQ3; lia.
Qed.
Lemma ra_pow2 :
forall cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 ->
ra_regs regs1 cx -> getr regs1 19 = Z_to_bv 64 (c_fattr cx) -> getr regs1 23 = Z_to_bv 64 (c_slct cx) ->
objs_at mem1 cx (c_rcur cx) -> frame_savedN ubs2_msyms 12 regs0 mem1 (spZ regs0) ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_A) mem1 (seg_rom ubs2segs)) md1)
(at_B cx L A mem md L1 A1 md1 regs0).
Proof.
intros cx L A mem md L1 A1 md1 regs0 regs1 mem1 Hcx HO HJ1 HR1 G19a G23a Hobjs1 HFS1.
eapply SR_bind; [exact (ra_memset cx L A mem md L1 A1 md1 regs0 regs1 mem1 Hcx HO HJ1 HR1 G19a G23a Hobjs1 HFS1)|].
cbv beta. intros c1 (regs3 & mem3 & -> & HJ & HR & G19 & G23 & G22 & Hobjs & HFS).
clear HJ1 HR1 G19a G23a Hobjs1 HFS1.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof (objs_fields_ok _ _ _ Hobjs) as HFO.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv) & Hslct).
pose proof HFO as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hstw. cbn beta in Hstw.
remember (Ereg regs3 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs3 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE19 : ew E 19 = Z_to_bv 64 (c_fattr cx)) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE22 : ew E 22 = Z_to_bv 64 (c_cfp cx + 30)) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE23 : ew E 23 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (MKS : forall lo hi, lo <= c_slct cx <= hi ->
st_ok ubs2segs E (ssM [(23%nat, mkAF lo hi 0); (19%nat, mkAF 0 (2^32-1) 0)]) (mkst regs3 (Z_to_bv 64 PC_M) mem3 (seg_rom ubs2segs))).
{ intros lo hi Hlh. subst E. unfold ssM.
apply (ra_st_okW cx (c_rcur cx) regs3 [] mem3 PC_M sr_atoms 37 47 false [] _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_Ereg.
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE23, HE19, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 PC_M) mem3 (seg_rom ubs2segs))) in HJ.
Ltac wr HE2 := eapply ra_wr_okW; [exact HE2 | lia | lia | intros X; lia | left; cbn; lia].
Ltac finish HS HJ HE HE0 HE2 HE8 HE9 HE19 HE22 HE23 Hobjs HFS Htpv F2 Hk p :=
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch goal with |- at_B _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) => exists (ms_regs msx), (ms_mem msx), p end;
split; [reflexivity|]; cbn [ms_regs ms_mem mkst]; split; [exact HJ|];
split; [ split; [| split; [| split; [|split; [|split]]]];
[ let Q := fresh "Q" in (jreg HS (2%bv:reg) as Q); rewrite Q, <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2; reflexivity
| let Q := fresh "Q" in (jreg HS (8%bv:reg) as Q); rewrite Q; exact HE8
| let Q := fresh "Q" in (jreg HS (9%bv:reg) as Q); rewrite Q; exact HE9
| let Q := fresh "Q" in (jreg HS (4%bv:reg) as Q); rewrite Q, (HE 4%nat 4%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (3%bv:reg) as Q); rewrite Q, (HE 3%nat 3%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (27%bv:reg) as Q); rewrite Q, (HE 27%nat 27%bv eq_refl); assumption ] |];
split; [let Q := fresh "Q" in (jreg HS (19%bv:reg) as Q); rewrite Q; exact HE19|];
split; [let Q := fresh "Q" in (jreg HS (23%bv:reg) as Q); rewrite Q; first [exact HE23 | rewrite Hk; reflexivity]|];
split; [let Q := fresh "Q" in (jreg HS (22%bv:reg) as Q); rewrite Q; exact HE22|];
split; [let Q := fresh "Q" in (jreg HS (24%bv:reg) as Q); rewrite Q; reflexivity|];
split; [split; intros; [lia | split; [lia | cbn; lia]]|];
split; [let Q := fresh "Q" in (jreg HS (11%bv:reg) as Q); rewrite Q; cbn [sv_denot]; rewrite ?HE8, ?HE9, ?HE22, ?unsigned_lit_small by lia;
lazymatch goal with |- _ = Z_to_bv 64 (if ?s =? 0 then _ else _) => destruct (Z.eqb_spec s 0); [first [reflexivity | lia] | first [reflexivity | lia]] end|];
split; [ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)
| eapply (frame_savedN_kept ubs2_msyms 12); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H) ].
assert (Hcases : c_slct cx = 0 \/ c_slct cx = 1 \/ c_slct cx = 2 \/ (3 <= c_slct cx <= 4) \/ (5 <= c_slct cx <= 8) \/ (9 <= c_slct cx <= 16) \/
(17 <= c_slct cx <= 32) \/ (33 <= c_slct cx <= 64) \/ (65 <= c_slct cx <= 128) \/ (129 <= c_slct cx <= 256)) by lia.
destruct Hcases as [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | Hk]]]]]]]]].
-
pose proof (MKS 0 0 ltac:(lia)) as HS. clear MKS.
assert (G23' : getr regs3 23 = Z_to_bv 64 0) by (rewrite G23, Hk; reflexivity). pin_reg' HS (23%bv:reg) 0 G23'.
jrun_to LAWS ubs2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE19 HE22 HE23 Hobjs HFS Htpv F2 Hk 0.
- pose proof (MKS 1 1 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE19 HE22 HE23 Hobjs HFS Htpv F2 Hk 1.
- pose proof (MKS 2 2 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE19 HE22 HE23 Hobjs HFS Htpv F2 Hk 1.
- pose proof (MKS 3 4 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE19 HE22 HE23 Hobjs HFS Htpv F2 Hk 2.
- pose proof (MKS 5 8 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE19 HE22 HE23 Hobjs HFS Htpv F2 Hk 3.
- pose proof (MKS 9 16 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE19 HE22 HE23 Hobjs HFS Htpv F2 Hk 4.
- pose proof (MKS 17 32 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE19 HE22 HE23 Hobjs HFS Htpv F2 Hk 5.
- pose proof (MKS 33 64 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE19 HE22 HE23 Hobjs HFS Htpv F2 Hk 6.
- pose proof (MKS 65 128 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE19 HE22 HE23 Hobjs HFS Htpv F2 Hk 7.
- pose proof (MKS 129 256 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs2tbl_ok HS HJ PC_B; [wr HE2|].
finish HS HJ HE HE0 HE2 HE8 HE9 HE19 HE22 HE23 Hobjs HFS Htpv F2 Hk 8.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
