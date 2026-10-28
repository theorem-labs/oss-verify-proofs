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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 UI1e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition WDB_HEAD : Z := Eval vm_compute in (ubs2_A_cgif_raw_newgif + 0x21c).
Definition WDB_EXIT : Z := Eval vm_compute in (ubs2_A_cgif_raw_newgif + 0x238).
Definition WDB_CLOB : list reg := [1; 6; 10; 11; 12; 13; 22; 23]%bv.
Definition ss_wdb : sstate :=
mkSS WDB_HEAD (sr_set (sr_set sr_atoms 23%bv (SLit 0)) 21%bv (SLit ubs2_A_cgif_writecb))
[ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ;
YQ0b.mkRegion (Some 20%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 32 lits_CGIF) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + 16) (2^63) 4);
(20%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 3);
(22%nat, mkAF 1 65536 0) ] [] []).

Lemma frame_of_win : forall E r rs m m' b (x : word),
frame_of E (r :: rs) m m' ->
forallb (fun r' => r_whi r' <=? r_wlo r') rs = true ->
base_val E (r_base r) = b ->
(bv_unsigned x < b + r_wlo r \/ b + r_whi r <= bv_unsigned x) -> m' x = m x.
Proof.
intros E r rs m m' b x HF Hro Hb Hx. apply HF. intros (r' & [<-|Hin] & Ha); [lia|].
pose proof (proj1 (forallb_forall _ _) Hro r' Hin) as H. cbn beta in H. apply Z.leb_le in H. lia.
Qed.
Lemma wdb_kept_in : forall r : reg, reg_in r WDB_CLOB = false -> r = 0%bv \/ r = 21%bv \/
In r ([2; 3; 4; 5; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 24; 25; 26; 27; 28; 29; 30; 31]%bv : list reg).
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]).
destruct Hin.
Qed.
Lemma wdb_loop : forall (k : nat) (n : Z) regs memc STK sp0 FP L A mem md Lc Ac mdc g gvals spc,
Z.of_nat k = n -> 1 <= n <= 65536 ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
obj_at ubs2segs memc g LAY_CGIF gvals ->
nth_error gvals CG_wfn = Some ubs2_A_writecb -> nth_error gvals CG_file = Some 0 ->
4096 <= g -> g + CGIF_SIZE <= alloc_ceiling -> g mod 16 = 0 ->
getr regs 2 = Z_to_bv 64 spc -> spc mod 16 = 0 -> sp0 - STK <= spc - 16 -> spc <= sp0 -> sp0 < 2 ^ 63 ->
getr regs 20 = Z_to_bv 64 g -> getr regs 23 = Z_to_bv 64 0 ->
getr regs 21 = Z_to_bv 64 ubs2_A_cgif_writecb -> getr regs 22 = Z_to_bv 64 n ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 WDB_HEAD) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 WDB_EXIT) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\
(forall r, reg_in r WDB_CLOB = false -> getr regs' r = getr regs r) /\
getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 0 /\
(forall x : word, bv_unsigned x < spc - 16 \/ spc <= bv_unsigned x -> mem' x = memc x) /\
mem_grows memc mem').
Proof.
induction k as [|k IH]; intros n regs memc STK sp0 FP L A mem md Lc Ac mdc g gvals spc Hk Hn HJ Hobj Hwfn Hfile Hg0 Hg1 Hg16
H2 Hal Hlo Hhi H63 H20 H21 H22 H23; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGS : CGIF_SIZE = 96) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63' & Hstw) & _).
assert (HE2 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 2 = Z_to_bv 64 spc) by (rewrite (ew_Ereg_nat regs _ 2 2%bv) by (vm_compute; reflexivity); exact H2).
assert (HE20 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 20 = Z_to_bv 64 g) by (rewrite (ew_Ereg_nat regs _ 20 20%bv) by (vm_compute; reflexivity); exact H20).
assert (HE23 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ [])) 22 = Z_to_bv 64 n) by (rewrite (ew_Ereg_nat regs _ 22 22%bv) by (vm_compute; reflexivity); exact H23).
assert (HS : st_ok ubs2segs (Ereg regs (map (Z_to_bv 64) gvals ++ [])) ss_wdb (mkst regs (Z_to_bv 64 WDB_HEAD) memc (seg_rom ubs2segs))).
{ apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H21] | intros X; discriminate X | cbn [sv_denot]; exact H22].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs2segs _ memc 2 spc); [rewrite HE2; apply unsigned_lit_small; lia | lia | lia |].
intros a Ha. apply Hstw. lia.
+ eapply (region_ok_obj_gen ubs2segs _ memc 20 g); [ | lia | lia | exact Hobj | reflexivity | | apply (lits_CGIF_ok gvals Hwfn Hfile) | intros i Hi; lia].
* rewrite HE20. apply unsigned_lit_small. lia.
* intros j v Hj. apply Ereg_vals. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE20, !unsigned_lit_small by lia. repeat split. lia.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE20, HE23, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (g mod 8 = 0) by (rewrite (Znumtheory.Zmod_div_mod 8 16 g); [rewrite Hg16; reflexivity | lia | lia | exists 2; reflexivity]).
repeat split; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 WDB_HEAD) memc (seg_rom ubs2segs))) in HJ.
jrun LAWS ubs2tbl_ok HS HJ.
{ wr_norm. eapply wr_ok_cons_win; [reflexivity | rewrite HE2; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jbranch ubs2tbl HS.
-
rewrite branch_ne_U, (U_atom_off _ 22 n (-1)), U_lit in Hc by (first [exact HE23 | lia]).
assert (Hn2 : 2 <= n) by (destruct (Z.eqb_spec (n + -1) 0); [discriminate | lia]). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ WDB_HEAD.
{ wr_norm. eapply wr_ok_cons_win; [reflexivity | rewrite HE2; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [2; 3; 4; 5; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 24; 25; 26; 27; 28; 29; 30; 31]%bv HS
(env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (22%bv:reg) as Hn23. rewrite HE23 in Hn23.
jreg HS (23%bv:reg) as Hn21. jreg HS (21%bv:reg) as Hn22. jreg HS (20%bv:reg) as Hn20. rewrite HE20 in Hn20.
jreg HS (2%bv:reg) as Hn2'. rewrite HE2 in Hn2'.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (n - 1) _ _ STK sp0 FP L A mem md Lc Ac mdc g gvals spc); [lia | lia | exact HJ | | exact Hwfn | exact Hfile | lia | lia
| exact Hg16 | exact Hn2' | exact Hal | exact Hlo | exact Hhi | exact H63 | exact Hn20 | exact Hn21 | exact Hn22 | rewrite Hn23, unsigned_lit_small by lia; f_equal; lia ].
eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) |].
intros i Hi. cbn [ms_mem] in HF, HF0. unfold mbyte.
rewrite (frame_of_win _ _ _ _ _ spc (Z_to_bv 64 (g + i)) HF0 eq_refl); [| cbn [base_val r_base]; rewrite HE2; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia].
rewrite (frame_of_win _ _ _ _ _ spc (Z_to_bv 64 (g + i)) HF eq_refl); [reflexivity| cbn [base_val r_base]; rewrite HE2; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HK3 & H21' & H23' & Hout3 & Hgr3).
exists regs3, mem3. split; [reflexivity|]. split; [exact HJ3|]. split; [|split; [exact H21'|split; [exact H23'|split]]].
+ intros r Hr. rewrite (HK3 r Hr). destruct (wdb_kept_in r Hr) as [->|[->|Hin]]; [rewrite !getr_zero; reflexivity | rewrite Hn22, H22; reflexivity | apply HK; exact Hin].
+ intros x Hx. rewrite (Hout3 x Hx). cbn [ms_mem] in HF, HF0.
rewrite (frame_of_win _ _ _ _ _ spc x HF0 eq_refl); [| cbn [base_val r_base]; rewrite HE2; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; lia].
rewrite (frame_of_win _ _ _ _ _ spc x HF eq_refl); [reflexivity | cbn [base_val r_base]; rewrite HE2; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; lia].
+ eapply mem_grows_trans; [|exact Hgr3]. cbn [ms_mem] in HG, HG0. eapply mem_grows_trans; [exact HG | exact HG0].
-
rewrite branch_ne_U, (U_atom_off _ 22 n (-1)), U_lit in Hc by (first [exact HE23 | lia]).
assert (Hn1 : n = 1) by (destruct (Z.eqb_spec (n + -1) 0); [lia | discriminate]). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ WDB_EXIT.
{ wr_norm. eapply wr_ok_cons_win; [reflexivity | rewrite HE2; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [2; 3; 4; 5; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 24; 25; 26; 27; 28; 29; 30; 31]%bv HS
(env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HK.
jreg HS (22%bv:reg) as Hn23. rewrite HE23, unsigned_lit_small in Hn23 by lia.
jreg HS (23%bv:reg) as Hn21. jreg HS (21%bv:reg) as Hn22.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SR_ret. eexists _, _. split; [reflexivity|]. split; [exact HJ|].
split; [|split; [exact Hn21 | split; [rewrite Hn23; f_equal; lia | split]]].
+ intros r Hr. destruct (wdb_kept_in r Hr) as [->|[->|Hin]]; [rewrite !getr_zero; reflexivity | rewrite Hn22, H22; reflexivity | apply HK; exact Hin].
+ intros x Hx. cbn [ms_mem] in HF, HF0.
rewrite (frame_of_win _ _ _ _ _ spc x HF0 eq_refl); [| cbn [base_val r_base]; rewrite HE2; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; lia].
rewrite (frame_of_win _ _ _ _ _ spc x HF eq_refl); [reflexivity | cbn [base_val r_base]; rewrite HE2; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; lia].
+ cbn [ms_mem] in HG, HG0. eapply mem_grows_trans; [exact HG | exact HG0].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
