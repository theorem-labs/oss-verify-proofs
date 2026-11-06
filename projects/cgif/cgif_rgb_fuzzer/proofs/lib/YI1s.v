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
YI1h YI16 YI1z YI1k YI21 YI22 YI23 YI1j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_zext32_mod : forall E a, U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) = U E a mod 2 ^ 32.
Proof.
intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_sll_lit by lia. rewrite U_SLit.
change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftr_div_pow2 by lia.
pose proof (U_range E a) as Hr.
replace ((U E a * 2 ^ 32) mod 2 ^ 64) with ((U E a mod 2 ^ 32) * 2 ^ 32).
2:{ change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.mul_mod_distr_r by lia. reflexivity. }
rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound (U E a) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma U_subw_mod32 : forall E a b, U E (SAluw ALU_SUB a b) mod 2 ^ 32 = (U E a - U E b) mod 2 ^ 32.
Proof.
intros E a b. rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw].
unfold bv_swrap, bv_wrap. cbn [bv_modulus bv_half_modulus].
change (2 ^ Z.of_N 64) with (2 ^ 32 * 2 ^ 32). change (2 ^ Z.of_N 32) with (2 ^ 32).
set (x := U E a). set (y := U E b).
rewrite (Z.mod_mod_divide _ (2 ^ 32 * 2 ^ 32) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
rewrite Zminus_mod_idemp_l. replace (x mod 2 ^ 32 - y mod 2 ^ 32 + bv_half_modulus 32 - bv_half_modulus 32) with (x mod 2 ^ 32 - y mod 2 ^ 32) by lia.
rewrite <- Zminus_mod. reflexivity.
Qed.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_s2i : sstate :=
mkSS FL_S2I sr_atoms
[ YQ0b.mkRegion (Some 25%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 32 0))] ;
YQ0b.mkRegion (Some 19%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))] ]
None (mkFacts [ (25%nat, mkAF 4096 (CEIL_MAX - 1) 0); (19%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(27%nat, mkAF 1 65535 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0) ] [] []).
Definition S2I_KEPT : list reg := [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 26; 23]%bv.
Definition s2o_facts : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (33%nat, mkAF 1 65535 0); (35%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65533 0); (34%nat, mkAF 1 65534 0) ].
Definition s2o_hi : list YQ0b.chunk :=
[mkChunk 80 (CVal 8 (SOff 32 0)); mkChunk 72 (CVal 8 (SOff 26 0)); mkChunk 88 (CVal 8 (SOff 26 0)); mkChunk 96 (CVal 8 (SOff 33 0)); mkChunk 104 (CVal 8 (SOff 35 0))].
Definition s2o_lo : list YQ0b.chunk := [mkChunk 56 (CVal 8 (SOff 26 1))].
Definition s2e_hi : list YQ0b.chunk := s2o_hi ++ [mkChunk 64 (CVal 8 (SOff 34 1))].
Definition s2e_regs : list sv := sr_set (sr_set (sr_set sr_atoms 24%bv (SLit 65535)) 20%bv (SOff 34 0)) 23%bv (SOff 34 0).
Definition s2o_regs : list sv := sr_set (sr_set s2e_regs 12%bv (SOff 34 1)) 27%bv (SOff 35 0).
Definition ss_s2o : sstate := mkSS FL_S2O s2o_regs [ YQ0b.mkRegion (Some 2%nat) 64 112 64 88 s2o_hi ; YQ0b.mkRegion (Some 2%nat) 56 64 56 64 s2o_lo ] None (mkFacts s2o_facts [] []).
Definition ss_s2e (pc : Z) : sstate := mkSS pc s2e_regs [ YQ0b.mkRegion (Some 2%nat) 64 112 64 88 s2e_hi ; YQ0b.mkRegion (Some 2%nat) 56 64 56 64 s2o_lo ] None (mkFacts s2o_facts [] []).
Definition S2O_KEPT : list reg := [2; 3; 4; 8; 9; 18; 21; 22; 26]%bv.
Definition ss_s2 : sstate :=
mkSS FL_S2 (sr_set sr_atoms 14%bv (SOff 32 1))
[ YQ0b.mkRegion (Some 2%nat) 64 104 64 88 [mkChunk 88 (CVal 8 (SOff 26 0)); mkChunk 96 (CVal 8 (SOff 32 1))] ;
YQ0b.mkRegion (Some 2%nat) 56 64 56 64 [] ; YQ0b.mkRegion (Some 2%nat) 104 112 104 112 [] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (32%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0) ] [] []).
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Section h.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Let CMP := CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef.
Definition s2i_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (c' : config) : Prop :=
exists regs' mem' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall x, mem' x = memc x) /\
(pc' = FL_S2F \/ pc' = FL_S2X) /\
(forall r : reg, In r S2I_KEPT -> getr regs' r = getr regs r).
Lemma fl_s2i : forall (n : nat) (c : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (i : Z),
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= i < H -> 0 <= c -> c + Z.of_nat n = W -> (1 <= n)%nat ->
getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 25 = Z_to_bv 64 (fimg + (i * W + c)) -> getr regs 19 = Z_to_bv 64 (bimg + (i * W + c)) -> getr regs 27 = Z_to_bv 64 (Z.of_nat n) ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S2I) memc (seg_rom src2segs)) mdc) (s2i_post STK sp0 FP L A mem md Lc Ac mdc regs memc).
Proof.
intros n. induction n as [|n IH]; intros c STK sp0 FP L A mem md Lc Ac mdc regs memc i HJ K0 Hfi Hbi Hi Hcge Hcn Hn G8 G9 G18 G25 G19 G27; [lia|].
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
assert (HU25 : bv_unsigned (ew E 25) = fimg + p) by (rewrite (HE 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; clear - Hp Hfimg0 Hfimg1 Hac; lia).
assert (HU19 : bv_unsigned (ew E 19) = bimg + p) by (rewrite (HE 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; clear - Hp Hbimg0 Hbimg1 Hac; lia).
assert (HFA : atoms_ok E [ (25%nat, mkAF 4096 (CEIL_MAX - 1) 0); (19%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(27%nat, mkAF 1 65535 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU25, HU19, HE32, HE33, (HE 27%nat 27%bv eq_refl), G27.
clear - Hp Hn Hcn Hcge HW Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (HS : st_ok src2segs E ss_s2i (mkst regs (Z_to_bv 64 FL_S2I) memc (seg_rom src2segs))).
{ unfold ss_s2i. subst E. apply entry_st_ok; [vm_compute; reflexivity | | | exact HFA].
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU25.
split; [lia|]. split; [clear - Hp Hfimg1 Hac Hn; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(clear - Hp Hn; lia))).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU19.
split; [lia|]. split; [clear - Hp Hbimg1 Hac Hn; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(clear - Hp Hn; lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU25, HU19.
repeat split; try exact I. clear - Dfb Hp Hn. lia. }
clear HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S2I) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_cmpPixel. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
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
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc ss_s2i].
eapply SR_bind.
{ apply (cmp_callD API IMG mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC
STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) p FL_S2R HJ (KD_eq _ _ _ _ K0 K1) ltac:(clear - Hp Hn; lia) Ha0 Ha1 Ha2).
- rewrite Hbq. exact Ha3.
- rewrite Hbq. exact Ha4.
- rewrite Hra. apply (ret_ok_even (Z_to_bv 64 FL_S2R)). vm_compute. reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hmem2 & Hres & Hfr2). clear HJ.
assert (K2 : KD mem0 spv mem2) by (apply (KD_eq _ _ _ _ (KD_eq _ _ _ _ K0 K1) Hmem2)).
jafter_stretch_keep HS 34%nat regs2 mem2 CMP_CLOB FL_S2R [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor]];
(eapply (region_kept_out src2segs _ _ _ _ 0 0); [intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU25, ?HU19; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU25, ?HU19; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_S2R) mem2 (seg_rom src2segs))) in HJ2.
set (E2 := havoc E 34 (map (getr regs2) CMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (EXIT : forall ss ms' pc', st_ok src2segs E2 ss ms' -> ss_pc ss = pc' -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) S2I_KEPT = true ->
(pc' = FL_S2F \/ pc' = FL_S2X) ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall x, ms_mem ms' x = memc x) ->
s2i_post STK sp0 FP L A mem md Lc Ac mdc regs memc (mkCfg ms' mdc)).
{ intros ss ms' pc' HS' Hpc Hrv Hkl Hpc' HJ' K'. exists (ms_regs ms'), (ms_mem ms'), pc'.
split; [rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hpc'|].
intros rr Hrr. subst E E2. exact (regs_kept_of_st_ok src2segs _ ss ms' regs _ S2I_KEPT HS' EA1 Hkl rr Hrr). }
jbranch src2tbl HS.
-
clear Hc. jrun_to LAWS src2tbl_ok HS HJ2 FL_S2F. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_S2F HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [left; reflexivity | exact HJ2 |].
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. rewrite Hmem2. apply K1.
-
clear Hc. jrun LAWS src2tbl_ok HS HJ2. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall x, ms_mem ms0 x = mem2 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch src2tbl HS.
+
rewrite branch_ne_U, U_lit in Hc by lia.
rewrite (U_atom_off _ 27 (Z.of_nat (Datatypes.S n)) (-1)) in Hc by first [subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27 | lia].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.eqb_spec (Z.of_nat (Datatypes.S n) + -1) 0); [discriminate Hc | lia]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ2 FL_S2I. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K4 : forall x, ms_mem ms1 x = mem2 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs _ S2I_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (c + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ i HJ2 (KD_eq _ _ _ _ K2 K4) Hfi Hbi Hi ltac:(clear - Hcge; lia) ltac:(clear - Hcn; lia) Hn1).
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite HU25; f_equal; subst p; lia).
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite HU19; f_equal; subst p; lia).
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl), G27, unsigned_lit_small by lia; f_equal; lia). }
cbv beta. intros c' (regs' & mem' & pc' & -> & HJ' & K' & Hpc' & HK'). exists regs', mem', pc'.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros x; rewrite K', K4, Hmem2; apply K1|]. split; [exact Hpc'|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
clear Hc. jrun_to LAWS src2tbl_ok HS HJ2 FL_S2X. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_S2X HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [right; reflexivity | exact HJ2 |].
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. rewrite K3, Hmem2. apply K1.
Qed.
Definition s2o_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (top : Z) (c' : config) : Prop :=
exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_S3) mem' (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KD mem0 spv mem' /\
(exists hrow, top <= hrow < H /\ getr regs' 14 = Z_to_bv 64 (hrow + 1)) /\
getr regs' 27 = Z_to_bv 64 W /\ getr regs' 24 = Z_to_bv 64 65535 /\ word_mem src2segs mem' (spv + 88) top /\
(forall r : reg, In r S2O_KEPT -> getr regs' r = getr regs r).
Lemma mk_s2o : forall (head : bool) pc (regs : bvmap 5 word) m (top i v : Z),
KD mem0 spv m -> (forall a, spv + 56 <= a < spv + 88 -> writable_at src2segs m a) ->
word_mem src2segs m (spv + 80) v -> word_mem src2segs m (spv + 72) top -> word_mem src2segs m (spv + 56) (top + 1) ->
word_mem src2segs m (spv + 88) top -> word_mem src2segs m (spv + 104) W ->
(head = false -> word_mem src2segs m (spv + 64) (i + 1)) ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 24 = Z_to_bv 64 65535 -> getr regs 20 = Z_to_bv 64 i -> getr regs 23 = Z_to_bv 64 i -> getr regs 26 = Z_to_bv 64 top ->
(head = true -> getr regs 12 = Z_to_bv 64 (i + 1) /\ getr regs 27 = Z_to_bv 64 W /\ pc = FL_S2O) ->
0 <= top -> top < i -> i <= 65534 -> 0 <= v < 2 ^ 64 ->
st_ok src2segs (Ereg regs (map (Z_to_bv 64) [v; H; i; W] ++ [])) (if head then ss_s2o else ss_s2e pc) (mkst regs (Z_to_bv 64 pc) m (seg_rom src2segs)).
Proof.
intros head pc regs m top i v K Hwr W80 W72 W56 W88 W104 Hexit G2 G24 G20 G23 G26 Hhead Ht0 Hti Hi Hv. dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC m K) as (_ & _ & _ & _ & _ & WHm).
set (E := Ereg regs (map (Z_to_bv 64) [v; H; i; W] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 v) by (subst E; apply (Ereg_vals regs [v; H; i; W] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 H) by (subst E; apply (Ereg_vals regs [v; H; i; W] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 i) by (subst E; apply (Ereg_vals regs [v; H; i; W] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 W) by (subst E; apply (Ereg_vals regs [v; H; i; W] [] 3%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (CKh : Forall (chunk_ok src2segs E m spv) s2o_hi).
{ unfold s2o_hi. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ v); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W80].
- eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W72].
- eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W88].
- eapply (chunk_ok_val _ _ _ _ _ _ _ H); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WHm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W104]. }
assert (CKl : Forall (chunk_ok src2segs E m spv) s2o_lo).
{ unfold s2o_lo. constructor; [|constructor].
eapply (chunk_ok_val _ _ _ _ _ _ _ (top + 1)); [cbn [sv_denot]; rewrite (HE 26%nat 26%bv eq_refl), G26, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W56]. }
assert (HPD : forall c1 c2, pairwise_disjoint E [ YQ0b.mkRegion (Some 2%nat) 64 112 64 88 c1 ; YQ0b.mkRegion (Some 2%nat) 56 64 56 64 c2 ]).
{ intros c1 c2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2. repeat split; try exact I. lia. }
assert (HFA : atoms_ok E s2o_facts).
{ unfold s2o_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE33, HE35, HE34, (HE 26%nat 26%bv eq_refl), G26.
rewrite !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. clear - Hsp0 Hsp1 Hsp16 HW HH Hi Ht0 Hti Hac. repeat split; lia. }
assert (RE : regs_ok E s2e_regs regs).
{ unfold s2e_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact G24] | intros X; discriminate X |] | intros X; discriminate X |].
- cbn [sv_denot]. rewrite Z.add_0_r, HE34, unsigned_lit_small by lia. exact G20.
- cbn [sv_denot]. rewrite Z.add_0_r, HE34, unsigned_lit_small by lia. exact G23. }
destruct head.
- destruct (Hhead eq_refl) as (G12 & G27 & ->). unfold ss_s2o. subst E. apply entry_st_ok_full; [| vm_compute; reflexivity | | exact (HPD _ _) | split; [exact HFA | split; exact I]].
+ unfold s2o_regs. apply regs_ok_pin; [apply regs_ok_pin; [exact RE | intros X; discriminate X |] | intros X; discriminate X |].
* cbn [sv_denot]. rewrite HE34, unsigned_lit_small by lia. exact G12.
* cbn [sv_denot]. rewrite Z.add_0_r, HE35, unsigned_lit_small by lia. exact G27.
+ constructor; [|constructor; [|constructor]]; unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]; rewrite HU2.
* split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|exact CKh].
* split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|exact CKl].
- pose proof (Hexit eq_refl) as W64. unfold ss_s2e. subst E. apply entry_st_ok_full; [exact RE | vm_compute; reflexivity | | exact (HPD _ _) | split; [exact HFA | split; exact I]].
constructor; [|constructor; [|constructor]]; unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]; rewrite HU2.
+ split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
unfold s2e_hi. apply Forall_app. split; [exact CKh|]. constructor; [|constructor].
eapply (chunk_ok_val _ _ _ _ _ _ _ (i + 1)); [cbn [sv_denot]; rewrite HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W64].
+ split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|exact CKl].
Qed.
Lemma fl_s2o : forall (n : nat) (i v : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top : Z),
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
spv = sp0 - 272 -> 272 <= STK ->
word_mem src2segs memc (spv + 80) v -> v mod 2 ^ 32 = W * i -> 0 <= v < 2 ^ 64 ->
word_mem src2segs memc (spv + 72) top -> word_mem src2segs memc (spv + 56) (top + 1) ->
word_mem src2segs memc (spv + 88) top -> word_mem src2segs memc (spv + 104) W ->
0 <= top -> top + Z.of_nat n = i -> (1 <= n)%nat -> i < H ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 21 = Z_to_bv 64 bimg -> getr regs 22 = Z_to_bv 64 fimg -> getr regs 24 = Z_to_bv 64 65535 -> getr regs 27 = Z_to_bv 64 W ->
getr regs 26 = Z_to_bv 64 top -> getr regs 20 = Z_to_bv 64 i -> getr regs 23 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 (i + 1) ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S2O) memc (seg_rom src2segs)) mdc) (s2o_post STK sp0 FP L A mem md Lc Ac mdc regs top).
Proof.
intros n. induction n as [|n IH]; intros i v STK sp0 FP L A mem md Lc Ac mdc regs memc top HJ K0 Hfi Hbi Hspv HSTK W80 Hvmod Hv W72 W56 W88 W104 Ht0 Htn Hn HiH
G2 G8 G9 G18 G21 G22 G24 G27 G26 G20 G23 G12; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HiW : W <= W * i /\ W * i + W <= N) by (rewrite HN; clear - Ht0 Htn Hn HiH HW; nia).
assert (WRS : forall m', journal src2_msyms MR STK sp0 FP L A mem md Lc Ac m' mdc -> forall a, spv + 56 <= a < spv + 88 -> writable_at src2segs m' a).
{ intros m' HJm a Ha. pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _). apply Hstw. clear - Ha Hspv HSTK. lia. }
assert (WRT : forall E0 c0 c1, bv_unsigned (ew E0 2) = spv ->
wr_ok E0 [YQ0b.mkRegion (Some 2%nat) 64 112 64 88 c0; YQ0b.mkRegion (Some 2%nat) 56 64 56 64 c1] STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 c0 c1 H2. repeat (eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia |]). apply wr_ok_nil. }
assert (KDF : forall E0 c0 c1 (m m' : word -> option byte), bv_unsigned (ew E0 2) = spv -> KD mem0 spv m ->
frame_of E0 [YQ0b.mkRegion (Some 2%nat) 64 112 64 88 c0; YQ0b.mkRegion (Some 2%nat) 56 64 56 64 c1] m m' -> KD mem0 spv m').
{ intros E0 c0 c1 m m' H2 Km HFx. apply (KD_frame _ _ _ _ Km). intros a Ha Hna1 Hna2 Hna3. apply (mbyte_of_frame _ _ _ _ a HFx Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | [<- | []]]; cbn [r_base r_wlo r_whi base_val]; rewrite H2; clear - Hna2; lia. }
pose proof (mk_s2o true FL_S2O regs memc top i v K0 (WRS _ HJ) W80 W72 W56 W88 W104 ltac:(intros X; discriminate X) G2 G24 G20 G23 G26
ltac:(intros _; split; [exact G12 | split; [exact G27 | reflexivity]]) Ht0 ltac:(clear - Htn Hn; lia) ltac:(clear - HiH HH; lia) Hv) as HS.
cbv beta iota in HS.
set (E := Ereg regs (map (Z_to_bv 64) [v; H; i; W] ++ [])) in HS.
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 v) by (subst E; apply (Ereg_vals regs [v; H; i; W] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 H) by (subst E; apply (Ereg_vals regs [v; H; i; W] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 i) by (subst E; apply (Ereg_vals regs [v; H; i; W] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 W) by (subst E; apply (Ereg_vals regs [v; H; i; W] [] 3%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S2O) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ FL_S2I. { apply WRT. exact HU2. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ _ HU2 K0 HF) as K1. clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks src2segs E ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs;
pose proof (st_region_chunks src2segs E ssx msx 1 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs1;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg src2segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg src2segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs, Hcs1. pose proof (proj2 (Forall_app _ _ _) (conj Hcs Hcs1)) as Hcs2. clear Hcs Hcs1. rename Hcs2 into Hcs. rewrite <- ?app_assoc in Hcs. cbn [app] in Hcs.
lazymatch type of Hcs with Forall _ ?cs =>
assert (CW : forall off e val, In (mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> word_mem src2segs (ms_mem ms) (spv + off) val)
by (intros off e val Hin He Hval; exact (chunk_word E _ _ off _ _ (proj1 (Forall_forall _ _) Hcs _ Hin) He Hval)) end.
assert (Hi64 : 0 <= i < 2 ^ 64 /\ 0 <= i + 1 < 2 ^ 64 /\ 0 <= top < 2 ^ 64 /\ 0 <= top + 1 < 2 ^ 64) by (clear - Ht0 Htn Hn HiH HH; lia).
assert (W80' : word_mem src2segs (ms_mem ms) (spv + 80) v) by (apply (CW 80 (SOff 32 0)); [cbn [In]; tauto | cbn [sv_denot]; rewrite Z.add_0_r, HE32, Z_to_bv_bv_unsigned; reflexivity | exact Hv]).
assert (W72' : word_mem src2segs (ms_mem ms) (spv + 72) top) by (apply (CW 72 (SOff 26 0)); [cbn [In]; tauto | cbn [sv_denot]; rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity | clear - Hi64; lia]).
assert (W88' : word_mem src2segs (ms_mem ms) (spv + 88) top) by (apply (CW 88 (SOff 26 0)); [cbn [In]; tauto | cbn [sv_denot]; rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity | clear - Hi64; lia]).
assert (W104' : word_mem src2segs (ms_mem ms) (spv + 104) W) by (apply (CW 104 (SOff 35 0)); [cbn [In]; tauto | cbn [sv_denot]; rewrite Z.add_0_r, HE35, Z_to_bv_bv_unsigned; reflexivity | clear - HW; lia]).
assert (W56' : word_mem src2segs (ms_mem ms) (spv + 56) (top + 1)) by (apply (CW 56 (SOff 26 1)); [cbn [In]; tauto | cbn [sv_denot]; rewrite (HE 26%nat 26%bv eq_refl), G26, unsigned_lit_small by (clear - Hi64; lia); reflexivity | clear - Hi64; lia]).
assert (W64' : word_mem src2segs (ms_mem ms) (spv + 64) (i + 1)) by (apply (CW 64 (SOff 34 1)); [cbn [In]; tauto | cbn [sv_denot]; rewrite HE34, unsigned_lit_small by (clear - Hi64; lia); reflexivity | clear - Hi64; lia]).
clear CW Hcs.
assert (Q24 : getr (ms_regs ms) 24 = Z_to_bv 64 65535) by (rewrite (RGX 24%bv (SLit 65535) eq_refl); reflexivity).
assert (Q20 : getr (ms_regs ms) 20 = Z_to_bv 64 i) by (rewrite (RGX 20%bv (SOff 34 0) eq_refl); cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity).
assert (Q23 : getr (ms_regs ms) 23 = Z_to_bv 64 i) by (rewrite (RGX 23%bv (SOff 34 0) eq_refl); cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity).
assert (ZX : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 32 0) (SLit 32)) (SLit 32)) = W * i).
{ rewrite U_zext32_mod, (U_atom E 32 v HE32 Hv). exact Hvmod. }
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc ss_s2o].
eapply SR_bind.
{ eapply (fl_s2i (Z.to_nat W) 0 STK sp0 FP L A mem md Lc Ac mdc _ _ i HJ K1 Hfi Hbi ltac:(clear - Ht0 Htn Hn HiH; lia) ltac:(clear; lia) ltac:(clear - HW; lia) ltac:(clear - HW; lia)).
- apply (RG 8%bv 8%nat _ eq_refl). rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- apply (RG 9%bv 9%nat _ eq_refl). rewrite (HE 9%nat 9%bv eq_refl). exact G9.
- apply (RG 18%bv 18%nat _ eq_refl). rewrite (HE 18%nat 18%bv eq_refl). exact G18.
- rewrite (RGX 25%bv _ eq_refl). eval_sr_get. apply denot_of_U'. replace (i * W + 0) with (W * i) by (clear; lia). apply (U_add_small E _ _ fimg (W * i)); [apply U_atom; [rewrite (HE 22%nat 22%bv eq_refl); exact G22 | clear - Hfimg0 Hfimg1 HiW HW Hac; lia] | exact ZX | clear - Hfimg0; lia | clear - HiW HW; lia | clear - Hfimg1 HiW Hac HW; lia].
- rewrite (RGX 19%bv _ eq_refl). eval_sr_get. apply denot_of_U'. replace (i * W + 0) with (W * i) by (clear; lia). apply (U_add_small E _ _ bimg (W * i)); [apply U_atom; [rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - Hbimg0 Hbimg1 HiW HW Hac; lia] | exact ZX | clear - Hbimg0; lia | clear - HiW HW; lia | clear - Hbimg1 HiW Hac HW; lia].
- apply (RG 27%bv 35%nat _ eq_refl). rewrite HE35. f_equal. clear - HW; lia. }
cbv beta. intros c' (regs' & mem' & pc' & -> & HJ' & Kmem' & Hpc' & HK'').
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs _ S2O_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR0 end.
assert (HK' : forall r : reg, In r S2O_KEPT -> getr regs' r = getr regs r) by (intros rr Hrr; rewrite (HK'' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)); apply (HKR0 rr Hrr)).
assert (G24' : getr regs' 24 = Z_to_bv 64 65535) by (rewrite (HK'' 24%bv ltac:(cbv; auto 50)); exact Q24).
assert (G20' : getr regs' 20 = Z_to_bv 64 i) by (rewrite (HK'' 20%bv ltac:(cbv; auto 50)); exact Q20).
assert (G23' : getr regs' 23 = Z_to_bv 64 i) by (rewrite (HK'' 23%bv ltac:(cbv; auto 50)); exact Q23).
clear HJ HS RG RGX HK'' HKR0 Q24 Q20 Q23.
assert (G2' : getr regs' 2 = Z_to_bv 64 spv) by (rewrite (HK' 2%bv ltac:(cbv; auto 50)); exact G2).
assert (G26' : getr regs' 26 = Z_to_bv 64 top) by (rewrite (HK' 26%bv ltac:(cbv; auto 50)); exact G26).
assert (K' : KD mem0 spv mem') by (exact (KD_eq _ _ _ _ K1 Kmem')).
assert (WK : forall a val, word_mem src2segs (ms_mem ms) a val -> word_mem src2segs mem' a val) by (intros a val Hw k Hk; rewrite (mbyte_of_eq _ _ _ _ Kmem'); apply Hw; exact Hk).
pose proof (WK _ _ W80') as W80m. pose proof (WK _ _ W72') as W72m. pose proof (WK _ _ W56') as W56m. pose proof (WK _ _ W88') as W88m. pose proof (WK _ _ W104') as W104m. pose proof (WK _ _ W64') as W64m.
clear K1 WK W80' W72' W56' W88' W104' W64' Kmem' ms.
set (E' := Ereg regs' (map (Z_to_bv 64) [v; H; i; W] ++ [])).
assert (HE' : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E' m = getr regs' rr) by (intros; subst E'; apply ew_Ereg_nat; assumption).
assert (HE32' : ew E' 32 = Z_to_bv 64 v) by (subst E'; apply (Ereg_vals regs' [v; H; i; W] [] 0%nat); reflexivity).
assert (HE33' : ew E' 33 = Z_to_bv 64 H) by (subst E'; apply (Ereg_vals regs' [v; H; i; W] [] 1%nat); reflexivity).
assert (HE34' : ew E' 34 = Z_to_bv 64 i) by (subst E'; apply (Ereg_vals regs' [v; H; i; W] [] 2%nat); reflexivity).
assert (HE35' : ew E' 35 = Z_to_bv 64 W) by (subst E'; apply (Ereg_vals regs' [v; H; i; W] [] 3%nat); reflexivity).
assert (HU2' : bv_unsigned (ew E' 2) = spv) by (rewrite (HE' 2%nat 2%bv eq_refl), G2'; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (CW88 : forall ss ms', st_ok src2segs E' ss ms' ->
(exists rg0, nth_error (ss_mem ss) 0 = Some rg0 /\ r_base rg0 = Some 2%nat /\ In (mkChunk 88 (CVal 8 (SOff 26 0))) (r_chunks rg0)) ->
word_mem src2segs (ms_mem ms') (spv + 88) top).
{ intros ss ms' HS' (rg0 & Hrg0 & Hb0 & Hin88).
pose proof (st_region_chunks src2segs E' ss ms' 0 rg0 2%nat spv HS' Hrg0 Hb0 HU2') as Hcs0.
apply (chunk_word E' _ _ 88 _ _ (proj1 (Forall_forall _ _) Hcs0 _ Hin88)); [cbn [sv_denot]; rewrite Z.add_0_r, (HE' 26%nat 26%bv eq_refl), G26', Z_to_bv_bv_unsigned; reflexivity | clear - Hi64; lia]. }
assert (EXIT : forall ss ms' hrow, st_ok src2segs E' ss ms' -> ss_pc ss = FL_S3 -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) S2O_KEPT = true ->
top <= hrow < H -> getr (ms_regs ms') 14 = Z_to_bv 64 (hrow + 1) -> sr_get (ss_regs ss) 27%bv = SOff 35 0 -> sr_get (ss_regs ss) 24%bv = SLit 65535 ->
word_mem src2segs (ms_mem ms') (spv + 88) top ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> KD mem0 spv (ms_mem ms') ->
s2o_post STK sp0 FP L A mem md Lc Ac mdc regs top (mkCfg ms' mdc)).
{ intros ss ms' hrow HS' Hpc Hrv Hkl Hh G14 Q27 Q24 W88x HJ'' K''. exists (ms_regs ms'), (ms_mem ms').
split; [rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ''|]. split; [exact K''|].
split; [exists hrow; split; [exact Hh | exact G14]|].
split; [rewrite (st_ok_reg src2segs E' ss ms' 27%bv HS'), Q27; cbn [sv_denot]; rewrite Z.add_0_r, HE35', Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (st_ok_reg src2segs E' ss ms' 24%bv HS'), Q24; reflexivity|]. split; [exact W88x|].
intros rr Hrr. rewrite <- (HK' rr Hrr). subst E'. exact (regs_kept_of_st_ok src2segs _ ss ms' regs' _ S2O_KEPT HS' (env_agree_refl _ _) Hkl rr Hrr). }
destruct Hpc' as [-> | ->].
-
pose proof (mk_s2o false FL_S2F regs' mem' top i v K' (WRS _ HJ') W80m W72m W56m W88m W104m ltac:(intros _; exact W64m)
G2' G24' G20' G23' G26' ltac:(intros X; discriminate X) Ht0 ltac:(clear - Htn Hn; lia) ltac:(clear - HiH HH; lia) Hv) as HS.
cbv beta iota in HS. fold E' in HS.
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 FL_S2F) mem' (seg_rom src2segs))) in HJ'.
jrun_to LAWS src2tbl_ok HS HJ' FL_S3. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ _ HU2' K' HF) as K2. clear HF HG.
apply SR_ret. apply (EXIT _ _ i HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Ht0 Htn Hn HiH; lia)); [| reflexivity | reflexivity | | exact HJ' | exact K2].
+ reg_nowF HS ltac:(rewrite HE34', unsigned_lit_small by (clear - Hi64; lia); reflexivity).
+ apply (CW88 _ _ HS). eexists. split; [reflexivity|]. split; [reflexivity|]. cbn [r_chunks In]. tauto.
-
pose proof (mk_s2o false FL_S2X regs' mem' top i v K' (WRS _ HJ') W80m W72m W56m W88m W104m ltac:(intros _; exact W64m)
G2' G24' G20' G23' G26' ltac:(intros X; discriminate X) Ht0 ltac:(clear - Htn Hn; lia) ltac:(clear - HiH HH; lia) Hv) as HS.
cbv beta iota in HS. fold E' in HS.
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 FL_S2X) mem' (seg_rom src2segs))) in HJ'.
jrun LAWS src2tbl_ok HS HJ'. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ _ HU2' K' HF) as K2. clear HF HG.
jbranch src2tbl HS.
+
rewrite branch_ltu_U, U_and_lit, (U_atom E' 26 top), (U_atom_off E' 34 i (-1)), land_ffff in Hc
by first [exact HE34' | (rewrite (HE' 26%nat 26%bv eq_refl); exact G26') | (clear - Hi64 Htn Hn HiH HH Ht0; lia)].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.ltb_spec top (i + -1)) as [Hl|Hl]; [clear - Htn Hl; lia | discriminate Hc]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ' FL_S2O. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ _ HU2' K2 HF) as K3. clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks src2segs E' ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2') as Hcs;
pose proof (st_region_chunks src2segs E' ssx msx 1 _ 2%nat spv HS eq_refl eq_refl HU2') as Hcs1;
pose proof (regs_kept_of_st_ok src2segs E' ssx msx regs' _ S2O_KEPT HS ltac:(subst E'; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E' nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg src2segs E' ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E' sv)
by (intros r sv Hr; rewrite (st_ok_reg src2segs E' ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs, Hcs1. pose proof (proj2 (Forall_app _ _ _) (conj Hcs Hcs1)) as Hcs2. clear Hcs Hcs1. rename Hcs2 into Hcs. rewrite <- ?app_assoc in Hcs. cbn [app] in Hcs.
lazymatch type of Hcs with Forall _ ?cs =>
assert (CW : forall off e val, In (mkChunk off (CVal 8 e)) cs -> sv_denot E' e = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> word_mem src2segs (ms_mem ms0) (spv + off) val)
by (intros off e val Hin He Hval; exact (chunk_word E' _ _ off _ _ (proj1 (Forall_forall _ _) Hcs _ Hin) He Hval)) end.
set (v' := U E' (SAluw ALU_SUB (SOff 32 0) (SOff 35 0))).
assert (Hv' : 0 <= v' < 2 ^ 64) by (apply U_range).
assert (Hv'mod : v' mod 2 ^ 32 = W * (i - 1)).
{ subst v'. rewrite U_subw_mod32, (U_atom E' 32 v HE32' Hv), (U_atom E' 35 W HE35') by (clear - HW; lia).
rewrite <- Zminus_mod_idemp_l, Hvmod. replace (W * i - W) with (W * (i - 1)) by (clear; lia). apply Z.mod_small. clear - HiW HNle HW; lia. }
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
assert (W80n : word_mem src2segs (ms_mem ms0) (spv + 80) v') by (apply (CW 80 (SAluw ALU_SUB (SOff 32 0) (SOff 35 0))); [cbn [In]; tauto | apply denot_of_U'; reflexivity | exact Hv']).
assert (W72n : word_mem src2segs (ms_mem ms0) (spv + 72) top) by (apply (CW 72 (SOff 26 0)); [cbn [In]; tauto | cbn [sv_denot]; rewrite Z.add_0_r, (HE' 26%nat 26%bv eq_refl), G26', Z_to_bv_bv_unsigned; reflexivity | clear - Hi64; lia]).
assert (W88n : word_mem src2segs (ms_mem ms0) (spv + 88) top) by (apply (CW 88 (SOff 26 0)); [cbn [In]; tauto | cbn [sv_denot]; rewrite Z.add_0_r, (HE' 26%nat 26%bv eq_refl), G26', Z_to_bv_bv_unsigned; reflexivity | clear - Hi64; lia]).
assert (W104n : word_mem src2segs (ms_mem ms0) (spv + 104) W) by (apply (CW 104 (SOff 35 0)); [cbn [In]; tauto | cbn [sv_denot]; rewrite Z.add_0_r, HE35', Z_to_bv_bv_unsigned; reflexivity | clear - HW; lia]).
assert (W56n : word_mem src2segs (ms_mem ms0) (spv + 56) (top + 1)) by (apply (CW 56 (SOff 26 1)); [cbn [In]; tauto | cbn [sv_denot]; rewrite (HE' 26%nat 26%bv eq_refl), G26', unsigned_lit_small by (clear - Hi64; lia); reflexivity | clear - Hi64; lia]).
eapply SR_mono.
{ eapply (IH (i - 1) v' STK sp0 FP L A mem md Lc Ac mdc _ _ top HJ' K3 Hfi Hbi Hspv HSTK W80n Hv'mod Hv' W72n W56n W88n W104n Ht0 ltac:(clear - Htn; lia) Hn1 ltac:(clear - HiH; lia)).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2'.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)), (HK' 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)), (HK' 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)), (HK' 18%bv ltac:(cbv; auto 50)). exact G18.
- rewrite (HKR 21%bv ltac:(cbv; auto 20)), (HK' 21%bv ltac:(cbv; auto 50)). exact G21.
- rewrite (HKR 22%bv ltac:(cbv; auto 20)), (HK' 22%bv ltac:(cbv; auto 50)). exact G22.
- rewrite (RGX 24%bv (SLit 65535) eq_refl). reflexivity.
- apply (RG 27%bv 35%nat _ eq_refl). exact HE35'.
- rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact G26'.
- rewrite (RGX 20%bv (SOff 34 (-1)) eq_refl). cbn [sv_denot]. rewrite HE34', unsigned_lit_small by (clear - Hi64; lia). f_equal.
- rewrite (RGX 23%bv (SOff 34 (-1)) eq_refl). cbn [sv_denot]. rewrite HE34', unsigned_lit_small by (clear - Hi64; lia). f_equal.
- rewrite (RGX 12%bv (SOff 34 0) eq_refl). cbn [sv_denot]. rewrite HE34', unsigned_lit_small by (clear - Hi64; lia). f_equal. clear; lia. }
cbv beta. intros c' (regs'' & mem'' & -> & HJ'' & K'' & Hh'' & Q27'' & Q24'' & W88'' & HK3). exists regs'', mem''.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact K''|]. split; [exact Hh''|]. split; [exact Q27''|]. split; [exact Q24''|]. split; [exact W88''|].
intros rr Hrr. rewrite (HK3 rr Hrr), (HKR rr Hrr). apply HK'. exact Hrr.
+
rewrite branch_ltu_U, U_and_lit, (U_atom E' 26 top), (U_atom_off E' 34 i (-1)), land_ffff in Hc
by first [exact HE34' | (rewrite (HE' 26%nat 26%bv eq_refl); exact G26') | (clear - Hi64 Htn Hn HiH HH Ht0; lia)].
assert (Hit : i - 1 = top) by (destruct (Z.ltb_spec top (i + -1)) as [Hl|Hl]; [discriminate Hc | clear - Htn Hn Hl; lia]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ' FL_S3. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ _ HU2' K2 HF) as K3. clear HF HG.
apply SR_ret. apply (EXIT _ _ top HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Ht0 HiH Hit; lia)); [| reflexivity | reflexivity | | exact HJ' | exact K3].
* reg_nowF HS ltac:(rewrite (HE' 26%nat 26%bv eq_refl), G26', unsigned_lit_small by (clear - Hi64; lia); reflexivity).
* apply (CW88 _ _ HS). eexists. split; [reflexivity|]. split; [reflexivity|]. cbn [r_chunks In]. tauto.
Qed.
Lemma fl_s2 : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top : Z),
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
spv = sp0 - 272 -> 272 <= STK -> 0 <= top < H ->
word_mem src2segs memc (spv + 88) top ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 21 = Z_to_bv 64 bimg -> getr regs 22 = Z_to_bv 64 fimg -> getr regs 27 = Z_to_bv 64 W -> getr regs 26 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 H ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S2) memc (seg_rom src2segs)) mdc) (s2o_post STK sp0 FP L A mem md Lc Ac mdc regs top).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc top HJ K0 Hfi Hbi Hspv HSTK Htop W88 G2 G8 G9 G18 G21 G22 G27 G26 G14.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
assert (WRS : forall m', journal src2_msyms MR STK sp0 FP L A mem md Lc Ac m' mdc -> forall a, spv + 56 <= a < spv + 112 -> writable_at src2segs m' a).
{ intros m' HJm a Ha. pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _). apply Hstw. clear - Ha Hspv HSTK. lia. }
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC memc K0) as (_ & _ & _ & _ & _ & WHm).
set (E := Ereg regs (map (Z_to_bv 64) [H - 1] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (H - 1)) by (subst E; apply (Ereg_vals regs [H - 1] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR : region_ok src2segs E memc (YQ0b.mkRegion (Some 2%nat) 64 104 64 88 [mkChunk 88 (CVal 8 (SOff 26 0)); mkChunk 96 (CVal 8 (SOff 32 1))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (WRS _ HJ); lia|].
constructor; [|constructor; [|constructor]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W88].
- eapply (chunk_ok_val _ _ _ _ _ _ _ H); [cbn [sv_denot]; rewrite HE32, unsigned_lit_small by lia; f_equal; lia | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WHm]. }
assert (HR1 : region_ok src2segs E memc (YQ0b.mkRegion (Some 2%nat) 56 64 56 64 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (WRS _ HJ); lia| constructor]. }
assert (HR2 : region_ok src2segs E memc (YQ0b.mkRegion (Some 2%nat) 104 112 104 112 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (WRS _ HJ); lia| constructor]. }
assert (HPD : pairwise_disjoint E (ss_mem ss_s2)).
{ cbn [ss_mem ss_s2 pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2. repeat split; try exact I; lia. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (32%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE32, (HE 27%nat 27%bv eq_refl), (HE 26%nat 26%bv eq_refl), G27, G26.
rewrite !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. clear - Hsp0 Hsp1 Hsp16 HW HH Htop Hac. repeat split; lia. }
assert (RE : regs_ok E (sr_set sr_atoms 14%bv (SOff 32 1)) regs).
{ apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |]. cbn [sv_denot]. rewrite HE32, unsigned_lit_small by lia. rewrite G14. f_equal. lia. }
assert (HS : st_ok src2segs E ss_s2 (mkst regs (Z_to_bv 64 FL_S2) memc (seg_rom src2segs))).
{ unfold ss_s2. apply entry_st_ok_full; [exact RE | vm_compute; reflexivity | constructor; [exact HR | constructor; [exact HR1 | constructor; [exact HR2 | constructor]]] | exact HPD | split; [exact HFA | split; exact I]]. }
clear HR HR1 HR2 HPD HFA RE.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S2) memc (seg_rom src2segs))) in HJ.
assert (WRT : forall E0 c0 c1 c2, bv_unsigned (ew E0 2) = spv ->
wr_ok E0 [YQ0b.mkRegion (Some 2%nat) 64 104 64 88 c0; YQ0b.mkRegion (Some 2%nat) 56 64 56 64 c1; YQ0b.mkRegion (Some 2%nat) 104 112 104 112 c2] STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 c0 c1 c2 H2. repeat (eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia |]). apply wr_ok_nil. }
assert (KDF : forall E0 c0 c1 c2 (m m' : word -> option byte), bv_unsigned (ew E0 2) = spv -> KD mem0 spv m ->
frame_of E0 [YQ0b.mkRegion (Some 2%nat) 64 104 64 88 c0; YQ0b.mkRegion (Some 2%nat) 56 64 56 64 c1; YQ0b.mkRegion (Some 2%nat) 104 112 104 112 c2] m m' -> KD mem0 spv m').
{ intros E0 c0 c1 c2 m m' H2 Km HFx. apply (KD_frame _ _ _ _ Km). intros a Ha Hna1 Hna2 Hna3. apply (mbyte_of_frame _ _ _ _ a HFx Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [r_base r_wlo r_whi base_val]; rewrite H2; clear - Hna2 Hna3; lia. }
jrun LAWS src2tbl_ok HS HJ. { apply WRT. exact HU2. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ _ _ HU2 K0 HF) as K1. clear HF HG.
assert (EXIT : forall E0 ss ms' hrow, st_ok src2segs E0 ss ms' -> env_agree 32 E E0 -> ss_pc ss = FL_S3 -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) S2O_KEPT = true ->
top <= hrow < H -> getr (ms_regs ms') 14 = Z_to_bv 64 (hrow + 1) -> getr (ms_regs ms') 27 = Z_to_bv 64 W -> sr_get (ss_regs ss) 24%bv = SLit 65535 ->
word_mem src2segs (ms_mem ms') (spv + 88) top ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> KD mem0 spv (ms_mem ms') ->
s2o_post STK sp0 FP L A mem md Lc Ac mdc regs top (mkCfg ms' mdc)).
{ intros E0 ss ms' hrow HS' HA Hpc Hrv Hkl Hh Q14 Q27 Q24 W88x HJ'' K''. exists (ms_regs ms'), (ms_mem ms').
split; [rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ''|]. split; [exact K''|].
split; [exists hrow; split; [exact Hh | exact Q14]|]. split; [exact Q27|].
split; [rewrite (st_ok_reg src2segs E0 ss ms' 24%bv HS'), Q24; reflexivity|]. split; [exact W88x|].
intros rr Hrr. subst E. exact (regs_kept_of_st_ok src2segs _ ss ms' regs _ S2O_KEPT HS' HA Hkl rr Hrr). }
jbranch src2tbl HS.
-
rewrite branch_geu_U, !U_and_lit, (U_atom E 26 top), (U_atom E 32 (H - 1)), !land_ffff in Hc
by first [exact HE32 | (rewrite (HE 26%nat 26%bv eq_refl); exact G26) | (clear - Htop HH; lia)].
assert (Hte : top = H - 1) by (destruct (Z.ltb_spec top (H - 1)) as [Hl|Hl]; [discriminate Hc | clear - Htop Hl; lia]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ FL_S3. { apply WRT. exact HU2. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ _ _ HU2 K1 HF) as K2. clear HF HG.
apply SR_ret. apply (EXIT _ _ _ (H - 1) HS (env_agree_refl _ _) eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Hte Htop; lia)); [| | reflexivity | | exact HJ | exact K2].
+ reg_nowF HS ltac:(rewrite HE32, unsigned_lit_small by (clear - HH; lia); f_equal; clear; lia).
+ reg_nowF HS ltac:(rewrite (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity).
+ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_region_chunks src2segs Ex ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs0 end.
cbn [r_chunks] in Hcs0.
apply (chunk_word E _ _ 88 _ _ (proj1 (Forall_forall _ _) Hcs0 (mkChunk 88 (CVal 8 (SOff 26 0))) ltac:(cbn [In]; tauto))); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity | clear - Htop HH; lia].
-
rewrite branch_geu_U, !U_and_lit, (U_atom E 26 top), (U_atom E 32 (H - 1)), !land_ffff in Hc
by first [exact HE32 | (rewrite (HE 26%nat 26%bv eq_refl); exact G26) | (clear - Htop HH; lia)].
assert (Htl : top < H - 1) by (destruct (Z.ltb_spec top (H - 1)) as [Hl|Hl]; [exact Hl | discriminate Hc]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ FL_S2O. { apply WRT. exact HU2. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ _ _ HU2 K1 HF) as K2. clear HF HG.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_region_chunks src2segs Ex ssx msx 0 _ 2%nat spv HS eq_refl eq_refl ltac:(ew_havocA; exact HU2)) as Hcs;
pose proof (st_region_chunks src2segs Ex ssx msx 1 _ 2%nat spv HS eq_refl eq_refl ltac:(ew_havocA; exact HU2)) as Hcs1;
pose proof (st_region_chunks src2segs Ex ssx msx 2 _ 2%nat spv HS eq_refl eq_refl ltac:(ew_havocA; exact HU2)) as Hcs1b;
pose proof (regs_kept_of_st_ok src2segs Ex ssx msx regs _ S2O_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew Ex nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg src2segs Ex ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot Ex sv)
by (intros r sv Hr; rewrite (st_ok_reg src2segs Ex ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs, Hcs1, Hcs1b. pose proof (proj2 (Forall_app _ _ _) (conj Hcs (proj2 (Forall_app _ _ _) (conj Hcs1 Hcs1b)))) as Hcs2. clear Hcs Hcs1 Hcs1b. rename Hcs2 into Hcs. rewrite <- ?app_assoc in Hcs. cbn [app] in Hcs.
lazymatch type of Hcs with Forall (chunk_ok _ ?Ex _ _) ?cs =>
assert (CW : forall off e val, In (mkChunk off (CVal 8 e)) cs -> sv_denot Ex e = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> word_mem src2segs (ms_mem ms0) (spv + off) val)
by (intros off e val Hin He Hval; exact (chunk_word Ex _ _ off _ _ (proj1 (Forall_forall _ _) Hcs _ Hin) He Hval)) end.
assert (HiW : 0 <= W * (H - 1) /\ W * (H - 1) + W <= N) by (rewrite HN; clear - HW HH; nia).
assert (W80n : word_mem src2segs (ms_mem ms0) (spv + 80) (W * (H - 1))).
{ apply (CW 80 (SMd M_MUL (SOff 27 0) (SOff 32 0))); [cbn [In]; tauto | | clear - HiW HNle HW; lia].
apply denot_of_U'. apply (U_mul_small' E _ _ W (H - 1)); [apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | apply (U_atom E 32 (H - 1) HE32); clear - HH; lia | clear - HW; lia | clear - HH; lia | clear - HiW HNle HW; lia]. }
assert (W72n : word_mem src2segs (ms_mem ms0) (spv + 72) top).
{ apply (CW 72 (SAlu ALU_AND (SOff 26 0) (SLit 65535))); [cbn [In]; tauto | | clear - Htop HH; lia].
apply denot_of_U'. rewrite U_and_lit, (U_atom E 26 top) by first [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Htop HH; lia]. apply land_ffff. clear - Htop HH; lia. }
assert (W56n : word_mem src2segs (ms_mem ms0) (spv + 56) (top + 1)).
{ apply (CW 56 (SOff 26 1)); [cbn [In]; tauto | cbn [sv_denot]; rewrite (HE 26%nat 26%bv eq_refl), G26, unsigned_lit_small by (clear - Htop HH; lia); reflexivity | clear - Htop HH; lia]. }
assert (W88n : word_mem src2segs (ms_mem ms0) (spv + 88) top).
{ apply (CW 88 (SOff 26 0)); [cbn [In]; tauto | cbn [sv_denot]; rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity | clear - Htop HH; lia]. }
assert (W104n : word_mem src2segs (ms_mem ms0) (spv + 104) W).
{ apply (CW 104 (SOff 27 0)); [cbn [In]; tauto | cbn [sv_denot]; rewrite Z.add_0_r, (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity | clear - HW; lia]. }
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (fl_s2o (Z.to_nat (H - 1 - top)) (H - 1) (W * (H - 1)) STK sp0 FP L A mem md Lc Ac mdc _ _ top HJ K2 Hfi Hbi Hspv HSTK W80n ltac:(apply Z.mod_small; clear - HiW HNle HW; lia) ltac:(clear - HiW HNle HW; lia) W72n W56n W88n W104n
ltac:(clear - Htop; lia) ltac:(clear - Htl; lia) ltac:(clear - Htl; lia) ltac:(clear; lia)).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 22%bv ltac:(cbv; auto 20)). exact G22.
- rewrite (RGX 24%bv (SLit 65535) eq_refl). reflexivity.
- apply (RG 27%bv 27%nat _ eq_refl). rewrite (HE 27%nat 27%bv eq_refl). exact G27.
- rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact G26.
- apply (RG 20%bv 32%nat _ eq_refl). exact HE32.
- apply (RG 23%bv 32%nat _ eq_refl). exact HE32.
- rewrite (RGX 12%bv (SOff 32 1) eq_refl). cbn [sv_denot]. rewrite HE32, unsigned_lit_small by (clear - HH; lia). first [reflexivity | f_equal; clear; lia]. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & K3 & Hh2 & Q27 & Q24 & W88x & HK2). exists regs2, mem2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact K3|]. split; [exact Hh2|]. split; [exact Q27|]. split; [exact Q24|]. split; [exact W88x|].
intros rr Hrr. rewrite (HK2 rr Hrr). apply (HKR rr Hrr).
Qed.
End h.
End S.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
