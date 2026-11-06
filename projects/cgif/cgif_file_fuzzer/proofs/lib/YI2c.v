(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3a YI06 YI5b YI09 YI08 YI0r YI1w YI1v YI4l YI21 YI5o YI5l YI6b YI5n YI20 YI1d YI2l.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI25 YI2o YI2p YI24.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI5c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_s1i : sstate :=
mkSS FL_S1I sr_atoms
[ YP09.mkRegion (Some 24%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 32 0))] ;
YP09.mkRegion (Some 25%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))] ]
None (mkFacts [ (24%nat, mkAF 4096 (CEIL_MAX - 1) 0); (25%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(27%nat, mkAF 1 65535 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0) ] [] []).
Lemma wrap64_nzV : forall v, -256 < v < 256 -> v <> 0 -> zcanon (bv_wrap 64 v + 0) <> 0.
Proof. intros v Hv Hnz. unfold zcanon, bv_wrap, M64. cbn [bv_modulus]. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia.
intros Hm. apply (Z.mod_divide v (2 ^ 64)) in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0 \/ q <= -1 \/ q >= 1) by lia. nia. Qed.
Lemma cmpPixel_fn_rangeV : forall cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef a b,
-256 < cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef a b < 256.
Proof. intros. unfold cmpPixel_fn. repeat (destruct (_ : bool); try lia). apply memcmp_spec_range. Qed.
Definition S1I_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 26]%bv.
Definition s1o_facts : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (32%nat, mkAF 1 65535 0); (33%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0) ].
Definition s1o_mem : list YP09.region :=
[ YP09.mkRegion (Some 2%nat) 88 104 88 96 [mkChunk 88 (CVal 8 (SOff 33 0)); mkChunk 96 (CVal 8 (SOff 32 0))] ].
Definition ss_s1o : sstate := mkSS FL_S1O sr_atoms s1o_mem None (mkFacts ((27%nat, mkAF 1 65535 0) :: s1o_facts) [] []).
Definition ss_s1e (pc : Z) : sstate := mkSS pc sr_atoms s1o_mem None (mkFacts s1o_facts [] []).
Definition S1O_KEPT : list reg := [2; 3; 4; 8; 9; 18; 21; 22]%bv.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Section f.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Let CMP := CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef.
Definition s1i_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (i : Z) (c' : config) : Prop :=
exists regs' mem' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom src0segs)) mdc /\
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KD mem0 spv mem' /\ (forall x, mem' x = memc x) /\
((pc' = FL_S1F /\ exists c, 0 <= c < W /\ CMP (i * W + c) <> 0) \/ (pc' = FL_S1X /\   forall c2, 0 <= c2 < W -> CMP (i * W + c2) = 0)) /\
(forall r : reg, In r S1I_KEPT -> getr regs' r = getr regs r).
Lemma fl_s1iV : forall (n : nat) (c : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (i : Z),
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= i < H -> 0 <= c -> c + Z.of_nat n = W -> (1 <= n)%nat ->
getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 24 = Z_to_bv 64 (fimg + (i * W + c)) -> getr regs 25 = Z_to_bv 64 (bimg + (i * W + c)) -> getr regs 27 = Z_to_bv 64 (Z.of_nat n) ->
(forall c2, 0 <= c2 < c -> CMP (i * W + c2) = 0) ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 FL_S1I) memc (seg_rom src0segs)) mdc) (s1i_postV STK sp0 FP L A mem md Lc Ac mdc regs memc i).
Proof.
intros n. induction n as [|n IH]; intros c STK sp0 FP L A mem md Lc Ac mdc regs memc i HJ K0 Hfi Hbi Hi Hcge Hcn Hn G8 G9 G18 G24 G25 G27 HEQ; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
assert (Hp : 0 <= i * W + c /\ i * W + c + Z.of_nat (Datatypes.S n) <= N) by (rewrite HN; clear - Hi Hcge Hcn Hn HW; nia).
set (p := i * W + c) in *. assert (Hpdef : p = i * W + c) by reflexivity. clearbody p.
set (bc := byte_at memc (fimg + p)). set (bb := byte_at memc (bimg + p)).
pose proof (byte_at_range memc (fimg + p)) as Rbc. pose proof (byte_at_range memc (bimg + p)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [bc; bb] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 bc) by (subst E; apply (Ereg_vals regs [bc; bb] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 bb) by (subst E; apply (Ereg_vals regs [bc; bb] [] 1%nat); reflexivity).
assert (HU24 : bv_unsigned (ew E 24) = fimg + p) by (rewrite (HE 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; clear - Hp Hfimg0 Hfimg1 Hac; lia).
assert (HU25 : bv_unsigned (ew E 25) = bimg + p) by (rewrite (HE 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; clear - Hp Hbimg0 Hbimg1 Hac; lia).
assert (HFA : atoms_ok E [ (24%nat, mkAF 4096 (CEIL_MAX - 1) 0); (25%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(27%nat, mkAF 1 65535 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU24, HU25, HE32, HE33, (HE 27%nat 27%bv eq_refl), G27.
clear - Hp Hn Hcn Hcge HW Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (HS : st_ok src0segs E ss_s1i (mkst regs (Z_to_bv 64 FL_S1I) memc (seg_rom src0segs))).
{ unfold ss_s1i. subst E. apply entry_st_ok; [vm_compute; reflexivity | | | exact HFA].
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU24.
split; [lia|]. split; [clear - Hp Hfimg1 Hac Hn; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(clear - Hp Hn; lia))).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU25.
split; [lia|]. split; [clear - Hp Hbimg1 Hac Hn; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(clear - Hp Hn; lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU24, HU25.
repeat split; try exact I. clear - Dfb Hp Hn. lia. }
clear HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S1I) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_cmpPixel. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha0. rewrite (HE 8%nat 8%bv eq_refl), G8 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite (HE 9%nat 9%bv eq_refl), G9 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 18%nat 18%bv eq_refl), G18 in Ha2.
jreg HS (13%bv:reg) as Ha3. rewrite HE32 in Ha3. jreg HS (14%bv:reg) as Ha4. rewrite HE33 in Ha4.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (Hbq : forall a, byte_at (ms_mem ms) a = byte_at memc a) by (intros a; unfold byte_at; rewrite (mbyte_of_eq _ _ _ _ K1); reflexivity).
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc ss_s1i].
eapply SR_bind.
{ apply (cmp_callD API IMG mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC
STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) p FL_S1R HJ (KD_eq _ _ _ _ K0 K1) ltac:(clear - Hp Hn; lia) Ha0 Ha1 Ha2).
- rewrite Hbq. exact Ha3.
- rewrite Hbq. exact Ha4.
- rewrite Hra. apply (ret_ok_even (Z_to_bv 64 FL_S1R)). vm_compute. reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hmem2 & Hres & Hfr2). clear HJ.
assert (K2 : KD mem0 spv mem2) by (apply (KD_eq _ _ _ _ (KD_eq _ _ _ _ K0 K1) Hmem2)).
jafter_stretch_keep HS 34%nat regs2 mem2 CMP_CLOB FL_S1R [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor]];
(eapply (region_kept_out src0segs _ _ _ _ 0 0); [intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU24, ?HU25; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU24, ?HU25; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_S1R) mem2 (seg_rom src0segs))) in HJ2.
set (E2 := havoc E 34 (map (getr regs2) CMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (EXIT : forall ss ms' pc', st_ok src0segs E2 ss ms' -> ss_pc ss = pc' -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) S1I_KEPT = true ->
((pc' = FL_S1F /\ exists c0, 0 <= c0 < W /\ CMP (i * W + c0) <> 0) \/ (pc' = FL_S1X /\ forall c2, 0 <= c2 < W -> CMP (i * W + c2) = 0)) ->
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall x, ms_mem ms' x = mem2 x) ->
s1i_postV STK sp0 FP L A mem md Lc Ac mdc regs memc i (mkCfg ms' mdc)).
{ intros ss ms' pc' HS' Hpc Hrv Hkl Hpc' HJ' K'. exists (ms_regs ms'), (ms_mem ms'), pc'.
split; [rewrite (st_ok_mkst src0segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact (KD_eq _ _ _ _ K2 K')|].
split; [intros x; rewrite (K' x), (Hmem2 x); apply K1|]. split; [exact Hpc'|].
intros rr Hrr. subst E E2. exact (regs_kept_of_st_ok src0segs _ ss ms' regs _ S1I_KEPT HS' EA1 Hkl rr Hrr). }
jbranch src0tbl HS.
-
assert (Hne : CMP p <> 0).
{ intros Hz. rewrite branch_ne_U, U_lit, (U_atom E2 36 0) in Hc; [discriminate Hc | | clear; lia | clear; lia].
subst E2. change 36%nat with (34 + 2)%nat. rewrite (ew_havoc_new E 34 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) by (cbn; lia).
cbn [nth map CMP_CLOB]. rewrite Hres. unfold CMP in Hz. rewrite Hz. reflexivity. }
clear Hc. jrun_to LAWS src0tbl_ok HS HJ2 FL_S1F. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_S1F HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [| exact HJ2 |].
+ left. split; [reflexivity|]. exists c. split; [clear - Hcge Hcn Hn; lia | rewrite <- Hpdef; exact Hne].
+ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity.
-
assert (Hz : CMP p = 0).
{ destruct (Z.eq_dec (CMP p) 0) as [Hz|Hnz]; [exact Hz | exfalso].
rewrite branch_ne_U, U_lit, U_SOff in Hc by (clear; lia). subst E2. change 36%nat with (34 + 2)%nat in Hc.
rewrite (ew_havoc_new E 34 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) in Hc by (cbn; lia). cbn [nth map CMP_CLOB] in Hc. rewrite Hres, Z_to_bv_unsigned in Hc.
pose proof (cmpPixel_fn_rangeV cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef (byte_at mem0 (fimg + p)) (byte_at mem0 (bimg + p))) as Rr.
pose proof (wrap64_nzV _ Rr Hnz) as X. destruct (Z.eqb_spec (zcanon (bv_wrap 64 (CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef p) + 0)) 0) as [Hq|Hq]; [exact (X Hq) | discriminate Hc]. }
assert (HEQ1 : forall c2, 0 <= c2 < c + 1 -> CMP (i * W + c2) = 0).
{ intros c2 Hc2. destruct (Z.eq_dec c2 c) as [-> | Hne2]; [rewrite <- Hpdef; exact Hz | apply HEQ; clear - Hc2 Hne2; lia]. }
clear Hc. jrun LAWS src0tbl_ok HS HJ2. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall x, ms_mem ms0 x = mem2 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch src0tbl HS.
+
rewrite branch_ne_U, U_lit in Hc by lia.
rewrite (U_atom_off _ 27 (Z.of_nat (Datatypes.S n)) (-1)) in Hc by first [subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27 | lia].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.eqb_spec (Z.of_nat (Datatypes.S n) + -1) 0); [discriminate Hc | lia]). clear Hc.
jrun_to LAWS src0tbl_ok HS HJ2 FL_S1I. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K4 : forall x, ms_mem ms1 x = mem2 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs _ S1I_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (c + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ i HJ2 (KD_eq _ _ _ _ K2 K4) Hfi Hbi Hi ltac:(clear - Hcge; lia) ltac:(clear - Hcn; lia) Hn1).
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite HU24; f_equal; subst p; lia).
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite HU25; f_equal; subst p; lia).
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl), G27, unsigned_lit_small by lia; f_equal; lia).
- exact HEQ1. }
cbv beta. intros c' (regs' & mem' & pc' & -> & HJ' & K' & Keq' & Hpc' & HK'). exists regs', mem', pc'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [intros x; rewrite (Keq' x), (K4 x), (Hmem2 x); apply K1|]. split; [exact Hpc'|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
assert (Hn0 : n = 0%nat).
{ rewrite branch_ne_U, U_lit in Hc by lia.
rewrite (U_atom_off _ 27 (Z.of_nat (Datatypes.S n)) (-1)) in Hc by first [subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27 | lia].
destruct (Z.eqb_spec (Z.of_nat (Datatypes.S n) + -1) 0) as [Hq|Hq]; [clear - Hq; lia | discriminate Hc]. }
clear Hc. jrun_to LAWS src0tbl_ok HS HJ2 FL_S1X. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_S1X HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [right; split; [reflexivity | intros c2 Hc2; apply HEQ1; clear - Hc2 Hcn Hn0; lia] | exact HJ2 |].
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3.
Qed.
Definition s1o_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (c' : config) : Prop :=
exists regs' mem' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom src0segs)) mdc /\
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KD mem0 spv mem' /\
((pc' = FL_S2 /\ exists top c, 0 <= top < H /\ 0 <= c < W /\ CMP (top * W + c) <> 0 /\
getr regs' 26 = Z_to_bv 64 top /\ word_mem src0segs mem' (spv + 88) top /\ getr regs' 27 = Z_to_bv 64 W /\ getr regs' 14 = Z_to_bv 64 H /\
(forall p, 0 <= p < top * W -> CMP p = 0))
\/ (pc' = FL_IDENT /\ getr regs' 27 = Z_to_bv 64 W /\ (forall p, 0 <= p < N -> CMP p = 0))) /\
(forall r : reg, In r S1O_KEPT -> getr regs' r = getr regs r).
Lemma mk_s1o : forall (head : bool) pc (regs : bvmap 5 word) m i,
KD mem0 spv m -> (forall a, spv + 88 <= a < spv + 96 -> writable_at src0segs m a) ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 26 = Z_to_bv 64 i -> word_mem src0segs m (spv + 88) i -> 0 <= i <= 65534 ->
(head = true -> getr regs 27 = Z_to_bv 64 W /\ pc = FL_S1O) ->
st_ok src0segs (Ereg regs (map (Z_to_bv 64) [H; i] ++ [])) (if head then ss_s1o else ss_s1e pc) (mkst regs (Z_to_bv 64 pc) m (seg_rom src0segs)).
Proof.
intros head pc regs m i K Hwr G2 G26 W88 Hi Hhead. dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC m K) as (_ & _ & _ & _ & _ & WHm).
set (E := Ereg regs (map (Z_to_bv 64) [H; i] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 H) by (subst E; apply (Ereg_vals regs [H; i] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 i) by (subst E; apply (Ereg_vals regs [H; i] [] 1%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR : Forall (region_ok src0segs E m) s1o_mem).
{ unfold s1o_mem. constructor; [|constructor]. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
constructor; [|constructor; [|constructor]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ i); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W88].
- eapply (chunk_ok_val _ _ _ _ _ _ _ H); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WHm]. }
assert (HFA : atoms_ok E s1o_facts).
{ unfold s1o_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE32, HE33, (HE 26%nat 26%bv eq_refl), G26.
rewrite !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. clear - Hsp0 Hsp1 Hsp16 HW HH Hi Hac. repeat split; lia. }
destruct head.
- destruct (Hhead eq_refl) as [G27 ->]. unfold ss_s1o. subst E. apply entry_st_ok; [vm_compute; reflexivity | exact HR | cbn [pairwise_disjoint all_disjoint]; split; exact I |].
apply (atoms_ok_app _ [(27%nat, mkAF 1 65535 0)]); [| exact HFA].
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (HE 27%nat 27%bv eq_refl), G27, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR HW. repeat split; lia.
- unfold ss_s1e. subst E. apply entry_st_ok; [vm_compute; reflexivity | exact HR | cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA].
Qed.
Lemma fl_s1oV : forall (n : nat) (i : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc,
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
spv = sp0 - 272 -> 272 <= STK ->
0 <= i -> i + Z.of_nat n = H -> (1 <= n)%nat ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 19 = Z_to_bv 64 (fimg + i * W) -> getr regs 20 = Z_to_bv 64 (bimg + i * W) ->
getr regs 26 = Z_to_bv 64 i -> word_mem src0segs memc (spv + 88) i -> getr regs 27 = Z_to_bv 64 W ->
(forall p, 0 <= p < i * W -> CMP p = 0) ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 FL_S1O) memc (seg_rom src0segs)) mdc) (s1o_postV STK sp0 FP L A mem md Lc Ac mdc regs).
Proof.
intros n. induction n as [|n IH]; intros i STK sp0 FP L A mem md Lc Ac mdc regs memc HJ K0 Hfi Hbi Hspv HSTK Hi0 Hin Hn G2 G8 G9 G18 G19 G20 G26 W88 G27 HEQ; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HiW : 0 <= i * W /\ i * W + W <= N) by (rewrite HN; clear - Hi0 Hin Hn HW; nia).
assert (WRS : forall m', journal src0_msyms MR STK sp0 FP L A mem md Lc Ac m' mdc -> forall a, spv + 88 <= a < spv + 96 -> writable_at src0segs m' a).
{ intros m' HJm a Ha. pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _). apply Hstw. clear - Ha Hspv HSTK. lia. }
assert (WRT : forall E0 cs, bv_unsigned (ew E0 2) = spv ->
wr_ok E0 [YP09.mkRegion (Some 2%nat) 88 104 88 96 cs] STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 cs H2. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia | apply wr_ok_nil]. }
assert (KDF : forall E0 cs (m m' : word -> option byte), bv_unsigned (ew E0 2) = spv -> KD mem0 spv m ->
frame_of E0 [YP09.mkRegion (Some 2%nat) 88 104 88 96 cs] m m' -> KD mem0 spv m').
{ intros E0 cs m m' H2 Km HFx. apply (KD_frame _ _ _ _ Km). intros a Ha Hna1 Hna2 Hna3. apply (mbyte_of_frame _ _ _ _ a HFx Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | []]; cbn [r_base r_wlo r_whi base_val]; rewrite H2; clear - Hna2; lia. }
pose proof (mk_s1o true FL_S1O regs memc i K0 (WRS _ HJ) G2 G26 W88 ltac:(clear - Hi0 Hin Hn HH; lia) ltac:(intros _; split; [exact G27 | reflexivity])) as HS. cbn [negb] in HS.
set (E := Ereg regs (map (Z_to_bv 64) [H; i] ++ [])) in HS.
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 H) by (subst E; apply (Ereg_vals regs [H; i] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 i) by (subst E; apply (Ereg_vals regs [H; i] [] 1%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S1O) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ FL_S1I. { apply WRT. exact HU2. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2 K0 HF) as K1. clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks src0segs E ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hv; rewrite (st_ok_reg src0segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hv) end.
cbn [r_chunks] in Hcs.
assert (W88a : word_mem src0segs (ms_mem ms) (spv + 88) i).
{ apply (chunk_word E _ _ 88 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 88 (CVal 8 (SOff 33 0))) ltac:(cbn [In]; tauto))); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, Z_to_bv_bv_unsigned; reflexivity | clear - Hi0 Hin Hn HH; lia]. }
clear Hcs.
assert (Q23 : getr (ms_regs ms) 23 = Z_to_bv 64 W) by (apply (RG 23%bv 27%nat _ eq_refl); rewrite (HE 27%nat 27%bv eq_refl); exact G27).
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc ss_s1o].
eapply SR_bind.
{ eapply (fl_s1iV (Z.to_nat W) 0 STK sp0 FP L A mem md Lc Ac mdc _ _ i HJ K1 Hfi Hbi ltac:(clear - Hi0 Hin Hn; lia) ltac:(clear; lia) ltac:(clear - HW; lia) ltac:(clear - HW; lia)).
- apply (RG 8%bv 8%nat _ eq_refl). rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- apply (RG 9%bv 9%nat _ eq_refl). rewrite (HE 9%nat 9%bv eq_refl). exact G9.
- apply (RG 18%bv 18%nat _ eq_refl). rewrite (HE 18%nat 18%bv eq_refl). exact G18.
- apply (RG 24%bv 19%nat _ eq_refl). rewrite (HE 19%nat 19%bv eq_refl), G19. f_equal. clear; lia.
- apply (RG 25%bv 20%nat _ eq_refl). rewrite (HE 20%nat 20%bv eq_refl), G20. f_equal. clear; lia.
- apply (RG 27%bv 27%nat _ eq_refl). rewrite (HE 27%nat 27%bv eq_refl), G27. f_equal. clear - HW; lia.
- intros c2 Hc2; exfalso; clear - Hc2; lia. }
cbv beta. intros c' (regs' & mem' & pc' & -> & HJ' & K' & Keq' & Hpc' & HK'').
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR0 end.
assert (HK' : forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26]%bv -> getr regs' r = getr regs r).
{ intros rr Hrr. rewrite (HK'' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). apply (HKR0 rr Hrr). }
assert (G23' : getr regs' 23 = Z_to_bv 64 W) by (rewrite (HK'' 23%bv ltac:(cbv; auto 50)); exact Q23).
assert (W88' : word_mem src0segs mem' (spv + 88) i) by (intros k Hk; unfold mbyte; rewrite (Keq' _); apply (W88a k Hk)).
clear HJ HS RG HK'' HKR0 K1 Q23 W88a Keq' ms.
assert (G2' : getr regs' 2 = Z_to_bv 64 spv) by (rewrite (HK' 2%bv ltac:(cbv; auto 50)); exact G2).
assert (G26' : getr regs' 26 = Z_to_bv 64 i) by (rewrite (HK' 26%bv ltac:(cbv; auto 50)); exact G26).
set (E' := Ereg regs' (map (Z_to_bv 64) [H; i] ++ [])).
assert (HE' : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E' m = getr regs' rr) by (intros; subst E'; apply ew_Ereg_nat; assumption).
assert (HE32' : ew E' 32 = Z_to_bv 64 H) by (subst E'; apply (Ereg_vals regs' [H; i] [] 0%nat); reflexivity).
assert (HE33' : ew E' 33 = Z_to_bv 64 i) by (subst E'; apply (Ereg_vals regs' [H; i] [] 1%nat); reflexivity).
assert (HU2' : bv_unsigned (ew E' 2) = spv) by (rewrite (HE' 2%nat 2%bv eq_refl), G2'; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (EXIT : forall ss ms' pc'', st_ok src0segs E' ss ms' -> ss_pc ss = pc'' -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) S1O_KEPT = true ->
((pc'' = FL_S2 /\ exists top c, 0 <= top < H /\ 0 <= c < W /\ CMP (top * W + c) <> 0 /\
getr (ms_regs ms') 26 = Z_to_bv 64 top /\ word_mem src0segs (ms_mem ms') (spv + 88) top /\ getr (ms_regs ms') 27 = Z_to_bv 64 W /\ getr (ms_regs ms') 14 = Z_to_bv 64 H /\ (forall p, 0 <= p < top * W -> CMP p = 0))
\/ (pc'' = FL_IDENT /\ getr (ms_regs ms') 27 = Z_to_bv 64 W /\ (forall p, 0 <= p < N -> CMP p = 0))) ->
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> KD mem0 spv (ms_mem ms') ->
s1o_postV STK sp0 FP L A mem md Lc Ac mdc regs (mkCfg ms' mdc)).
{ intros ss ms' pc'' HS' Hpc Hrv Hkl Hpc'' HJ'' K''. exists (ms_regs ms'), (ms_mem ms'), pc''.
split; [rewrite (st_ok_mkst src0segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ''|]. split; [exact K''|]. split; [exact Hpc''|].
intros rr Hrr. rewrite <- (HK' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). subst E'. exact (regs_kept_of_st_ok src0segs _ ss ms' regs' _ S1O_KEPT HS' (env_agree_refl _ _) Hkl rr Hrr). }
assert (CW88 : forall ss ms' e val, st_ok src0segs E' ss ms' ->
(exists rg0, nth_error (ss_mem ss) 0 = Some rg0 /\ r_base rg0 = Some 2%nat /\ In (mkChunk 88 (CVal 8 e)) (r_chunks rg0)) ->
sv_denot E' e = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> word_mem src0segs (ms_mem ms') (spv + 88) val).
{ intros ss ms' e val HS' (rg0 & Hrg0 & Hb0 & Hin88) He Hval.
pose proof (st_region_chunks src0segs E' ss ms' 0 rg0 2%nat spv HS' Hrg0 Hb0 HU2') as Hcs0.
exact (chunk_word E' _ _ 88 _ _ (proj1 (Forall_forall _ _) Hcs0 _ Hin88) He Hval). }
destruct Hpc' as [[-> (c0 & Hc0 & Hne)] | [-> HROW]].
-
pose proof (mk_s1o false FL_S1F regs' mem' i K' (WRS _ HJ') G2' G26' W88' ltac:(clear - Hi0 Hin Hn HH; lia) ltac:(intros X; discriminate X)) as HS. cbn [negb] in HS. fold E' in HS.
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 FL_S1F) mem' (seg_rom src0segs))) in HJ'.
jrun LAWS src0tbl_ok HS HJ'. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K' HF) as K2. clear HF HG.
jbranch src0tbl HS.
+ clear Hc. jrun_to LAWS src0tbl_ok HS HJ' FL_S2. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K2 HF) as K3. clear HF HG.
apply SR_ret. apply (EXIT _ _ FL_S2 HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [| exact HJ' | exact K3].
left. split; [reflexivity|]. exists i, c0. split; [clear - Hi0 Hin Hn; lia|]. split; [exact Hc0|]. split; [exact Hne|].
split; [reg_nowF HS ltac:(rewrite (HE' 26%nat 26%bv eq_refl), G26', unsigned_lit_small by (clear - Hi0 Hin Hn HH; lia); reflexivity)|].
split; [apply (CW88 _ _ (SOff 33 0) i HS); [eexists; split; [reflexivity|]; split; [reflexivity|]; cbn [r_chunks In]; tauto | cbn [sv_denot]; rewrite Z.add_0_r, HE33', Z_to_bv_bv_unsigned; reflexivity | clear - Hi0 Hin Hn HH; lia]|].
split; [reg_nowF HS ltac:(rewrite (HE' 23%nat 23%bv eq_refl), G23', Z_to_bv_bv_unsigned; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite HE32', unsigned_lit_small by (clear - HH; lia); reflexivity) | exact HEQ].
+ exfalso. rewrite branch_ne_U, (U_atom E' 26 i), (U_atom E' 32 H) in Hc;
[| exact HE32' | clear - HH; lia | rewrite (HE' 26%nat 26%bv eq_refl); exact G26' | clear - Hi0 Hin Hn HH; lia].
destruct (Z.eqb_spec i H); [clear - Hin Hn e; lia | discriminate Hc].
-
assert (HEQ1 : forall p, 0 <= p < (i + 1) * W -> CMP p = 0).
{ intros p Hp. destruct (Z.lt_ge_cases p (i * W)) as [Hlt|Hge]; [apply HEQ; clear - Hp Hlt; lia|]. replace p with (i * W + (p - i * W)) by (clear; lia). apply HROW. clear - Hp Hge. lia. }
pose proof (mk_s1o false FL_S1X regs' mem' i K' (WRS _ HJ') G2' G26' W88' ltac:(clear - Hi0 Hin Hn HH; lia) ltac:(intros X; discriminate X)) as HS. cbn [negb] in HS. fold E' in HS.
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 FL_S1X) mem' (seg_rom src0segs))) in HJ'.
jrun LAWS src0tbl_ok HS HJ'. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K' HF) as K2. clear HF HG.
jbranch src0tbl HS.
+
assert (HiH : i + 1 = H).
{ rewrite branch_eq_U, (U_atom_off E' 33 i 1), (U_atom E' 32 H) in Hc;
[| exact HE32' | clear - HH; lia | exact HE33' | clear - Hi0 Hin Hn HH; lia | clear - Hi0 Hin Hn HH; lia].
destruct (Z.eqb_spec (i + 1) H) as [Hq|Hq]; [exact Hq | discriminate Hc]. }
clear Hc. jrun_to LAWS src0tbl_ok HS HJ' FL_IDENT. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K2 HF) as K3. clear HF HG.
apply SR_ret. apply (EXIT _ _ FL_IDENT HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [right; split; [reflexivity | split; [reg_nowF HS ltac:(rewrite (HE' 23%nat 23%bv eq_refl), G23', Z_to_bv_bv_unsigned; reflexivity) | intros p Hp; apply HEQ1; rewrite HN, <- HiH in Hp; clear - Hp; nia]] | exact HJ' | exact K3].
+
rewrite branch_eq_U, (U_atom_off E' 33 i 1), (U_atom E' 32 H) in Hc;
[| exact HE32' | clear - HH; lia | exact HE33' | clear - Hi0 Hin Hn HH; lia | clear - Hi0 Hin Hn HH; lia].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.eqb_spec (i + 1) H); [discriminate Hc | clear - Hin Hn n0; lia]). clear Hc.
jrun_to LAWS src0tbl_ok HS HJ' FL_S1O. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K2 HF) as K3. clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs' _ S1O_KEPT HS ltac:(subst E'; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR end.
assert (W88n : word_mem src0segs (ms_mem ms0) (spv + 88) (i + 1)).
{ apply (CW88 _ _ (SOff 33 1) (i + 1) HS); [eexists; split; [reflexivity|]; split; [reflexivity|]; cbn [r_chunks In]; tauto | cbn [sv_denot]; rewrite HE33', unsigned_lit_small by (clear - Hi0 Hin Hn HH; lia); reflexivity | clear - Hi0 Hin Hn HH; lia]. }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ HJ' K3 Hfi Hbi Hspv HSTK ltac:(clear - Hi0; lia) ltac:(clear - Hin; lia) Hn1).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2'.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)), (HK' 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)), (HK' 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)), (HK' 18%bv ltac:(cbv; auto 50)). exact G18.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src0segs Ec ssc msc 19%bv HS) end. eval_sr_get. apply denot_of_U'. replace (fimg + (i + 1) * W) with (fimg + i * W + W) by (clear; lia).
apply (U_add_small E' _ _ (fimg + i * W) W); [apply U_atom; [rewrite (HE' 19%nat 19%bv eq_refl), (HK' 19%bv ltac:(cbv; auto 50)); exact G19 | clear - HiW Hfimg0 Hfimg1 HW Hac; lia]
| apply U_atom; [rewrite (HE' 23%nat 23%bv eq_refl); exact G23' | clear - HW; lia] | clear - HiW Hfimg0; lia | clear - HW; lia | clear - HiW Hfimg0 Hfimg1 HW Hac; nia].
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src0segs Ec ssc msc 20%bv HS) end. eval_sr_get. apply denot_of_U'. replace (bimg + (i + 1) * W) with (bimg + i * W + W) by (clear; lia).
apply (U_add_small E' _ _ (bimg + i * W) W); [apply U_atom; [rewrite (HE' 20%nat 20%bv eq_refl), (HK' 20%bv ltac:(cbv; auto 50)); exact G20 | clear - HiW Hbimg0 Hbimg1 HW Hac; lia]
| apply U_atom; [rewrite (HE' 23%nat 23%bv eq_refl); exact G23' | clear - HW; lia] | clear - HiW Hbimg0; lia | clear - HW; lia | clear - HiW Hbimg0 Hbimg1 HW Hac; nia].
- reg_nowF HS ltac:(rewrite (HE' 26%nat 26%bv eq_refl), G26', unsigned_lit_small by (clear - Hi0 Hin Hn HH; lia); reflexivity).
- exact W88n.
- reg_nowF HS ltac:(rewrite (HE' 23%nat 23%bv eq_refl), G23', Z_to_bv_bv_unsigned; reflexivity).
- exact HEQ1. }
cbv beta. intros c' (regs'' & mem'' & pc'' & -> & HJ'' & K'' & Hpc'' & HK''). exists regs'', mem'', pc''.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact K''|]. split; [exact Hpc''|].
intros rr Hrr. rewrite (HK'' rr Hrr), (HKR rr Hrr). apply HK'. clear - Hrr. cbv in Hrr. cbv. intuition.
Qed.
End f.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
