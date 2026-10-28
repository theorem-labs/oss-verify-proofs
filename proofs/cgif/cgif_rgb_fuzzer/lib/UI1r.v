(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3l YI00 YI02 YI01 YI03
UI1e UI1c UI39 UI1i UI59 UI56 YI0x UI57
UI1h UI16 UI1z UI1k UI22 UI1j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition s1i_stk : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) 88 128 88 88
[mkChunk 88 (CVal 8 (SLit 1)); mkChunk 104 (CVal 8 (SOff 36 0)); mkChunk 112 (CVal 8 (SOff 37 0)); mkChunk 120 (CVal 8 (SOff 38 0))].
Definition s1i_atoms : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (8%nat, mkAF 4096 (CEIL_MAX - 1) 0); (9%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(21%nat, mkAF 1 1 0); (22%nat, mkAF 0 65534 0); (34%nat, mkAF 4096 (CEIL_MAX - 1) 0); (35%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (36%nat, mkAF 1 65535 0) ].
Definition s1i_conds : list acond := [ mkAC BC_GEU (SOff 34 0) (SOff 26 0); mkAC BC_GEU (SOff 35 0) (SOff 19 0) ].
Definition s1i_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 25 0) (SOff 22 0), SOff 34 0); (SAlu ALU_ADD (SOff 24 0) (SOff 22 0), SOff 34 0);
(SAlu ALU_ADD (SOff 27 0) (SOff 22 0), SOff 35 0); (SAlu ALU_ADD (SOff 20 0) (SOff 22 0), SOff 35 0);
(SAlu ALU_XOR (SOff 23 0) (SLit 0), SLit 1) ].
Definition ss_s1i : sstate :=
mkSS FL_S1I sr_atoms
[ s1i_stk ; YQ0b.mkRegion (Some 34%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 32 0))] ;
YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))] ]
None (mkFacts s1i_atoms s1i_conds s1i_alias).
Definition S1I_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%bv.
Definition s1o_atoms : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (8%nat, mkAF 4096 (CEIL_MAX - 1) 0); (9%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(25%nat, mkAF 4096 (CEIL_MAX - 1) 0); (27%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(32%nat, mkAF 1 65535 0); (33%nat, mkAF 0 65534 0); (34%nat, mkAF 1 65535 0) ].
Definition s1o_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SOff 34 0)) (SOff 9 0), SOff 25 0);
(SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SOff 34 0)) (SOff 8 0), SOff 27 0);
(SAlu ALU_XOR (SAlu ALU_SLTU (SOff 27 0) (SOff 8 0)) (SLit (-1)), SLit (-1));
(SAlu ALU_XOR (SOff 23 0) (SLit 0), SLit 1) ].
Definition s1o_hd : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) 80 112 96 104
[mkChunk 80 (CVal 8 (SOff 32 0)); mkChunk 88 (CVal 8 (SLit 1)); mkChunk 104 (CVal 8 (SOff 34 0))].
Definition s1o_tl : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) 80 112 96 104
[mkChunk 80 (CVal 8 (SOff 32 0)); mkChunk 88 (CVal 8 (SLit 1)); mkChunk 96 (CVal 8 (SOff 33 0)); mkChunk 104 (CVal 8 (SOff 34 0))].
Definition ss_s1o : sstate :=
mkSS FL_S1O sr_atoms [s1o_hd] None
(mkFacts ((10%nat, mkAF 1 65535 0) :: (11%nat, mkAF 0 65534 0) :: s1o_atoms) [mkAC BC_GEU (SOff 25 0) (SOff 9 0)] s1o_alias).
Definition ss_s1e (pc : Z) : sstate := mkSS pc sr_atoms [s1o_tl] None (mkFacts s1o_atoms [] []).
Definition S1O_KEPT : list reg := [2; 3; 4; 8; 9; 18]%bv.
Lemma s1_chunk_word : forall E mem base off e v,
chunk_ok ubs2segs E mem base (mkChunk off (CVal 8 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
word_mem ubs2segs mem (base + off) v.
Proof.
intros E mem base off e v Hc He Hv. apply val_mem_word_mem.
eapply (val_of_chunk_ok ubs2segs E mem base off 8%N e); [exact Hc | exact He | cbn; lia | cbn; lia].
Qed.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Section d.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Let CMP := CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef.
Definition s1i_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (i : Z) (c' : config) : Prop :=
exists regs' mem' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KD mem0 spv mem' /\ (forall x, mem' x = memc x) /\
((pc' = FL_S1F /\ exists c, 0 <= c < W /\ CMP (i * W + c) <> 0) \/ pc' = FL_S1X) /\
(forall r : reg, In r S1I_KEPT -> getr regs' r = getr regs r).
Lemma fl_s1i : forall (n : nat) (c : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (i : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= i < H -> 0 <= c -> c + Z.of_nat n = W -> (1 <= n)%nat ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 18 = Z_to_bv 64 fhp -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 8 = Z_to_bv 64 bimg ->
getr regs 25 = Z_to_bv 64 (fimg + i * W) -> getr regs 24 = Z_to_bv 64 (fimg + i * W) -> getr regs 26 = Z_to_bv 64 (fimg + i * W) ->
getr regs 27 = Z_to_bv 64 (bimg + i * W) -> getr regs 20 = Z_to_bv 64 (bimg + i * W) -> getr regs 19 = Z_to_bv 64 (bimg + i * W) ->
getr regs 21 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 c ->
word_mem ubs2segs memc (spv + 88) 1 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S1I) memc (seg_rom ubs2segs)) mdc) (s1i_post STK sp0 FP L A mem md Lc Ac mdc regs memc i).
Proof.
intros n. induction n as [|n IH]; intros c STK sp0 FP L A mem md Lc Ac mdc regs memc i HJ K0 Hfi Hbi Hi Hcge Hcn Hn
G2 G18 G9 G8 G25 G24 G26 G27 G20 G19 G21 G23 G22 W88; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
assert (WKD : forall o v, 104 <= o <= 120 -> word_mem ubs2segs mem0 (spv + o) v -> word_mem ubs2segs memc (spv + o) v).
{ intros o v Ho Hw k Hk. rewrite (K0 (spv + o + Z.of_nat k)) by (clear - Ho Hk Hsp0 Hsp1 Hac; lia). apply Hw. exact Hk. }
pose proof (WKD 104 W ltac:(lia) WW0) as WWm. pose proof (WKD 112 g ltac:(lia) WG0) as WGm. pose proof (WKD 120 cfp ltac:(lia) WC0) as WCm.
assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HiW : 0 <= i * W /\ i * W + W <= N) by (rewrite HN; clear - Hi HW; nia).
assert (Hp : 0 <= i * W + c /\ i * W + c + Z.of_nat (Datatypes.S n) <= N) by (rewrite HN; clear - Hi Hcge Hcn Hn HW; nia).
set (p := i * W + c) in *. assert (Hpdef : p = i * W + c) by reflexivity. clearbody p.
set (bc := byte_at memc (fimg + p)). set (bb := byte_at memc (bimg + p)).
pose proof (byte_at_range memc (fimg + p)) as Rbc. pose proof (byte_at_range memc (bimg + p)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [bc; bb; fimg + p; bimg + p; W; g; cfp] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 bc) by (subst E; apply (Ereg_vals regs [bc; bb; fimg + p; bimg + p; W; g; cfp] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 bb) by (subst E; apply (Ereg_vals regs [bc; bb; fimg + p; bimg + p; W; g; cfp] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 (fimg + p)) by (subst E; apply (Ereg_vals regs [bc; bb; fimg + p; bimg + p; W; g; cfp] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 (bimg + p)) by (subst E; apply (Ereg_vals regs [bc; bb; fimg + p; bimg + p; W; g; cfp] [] 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 W) by (subst E; apply (Ereg_vals regs [bc; bb; fimg + p; bimg + p; W; g; cfp] [] 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 g) by (subst E; apply (Ereg_vals regs [bc; bb; fimg + p; bimg + p; W; g; cfp] [] 5%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 cfp) by (subst E; apply (Ereg_vals regs [bc; bb; fimg + p; bimg + p; W; g; cfp] [] 6%nat); reflexivity).
assert (ER : forall (m : nat) (rr : reg) v, Z.of_nat m = bv_unsigned rr -> getr regs rr = Z_to_bv 64 v -> ew E m = Z_to_bv 64 v)
by (intros m rr v Hm Hg; rewrite (HE m rr Hm); exact Hg).
pose proof (ER 2%nat 2%bv _ eq_refl G2) as HE2. pose proof (ER 8%nat 8%bv _ eq_refl G8) as HE8.
pose proof (ER 9%nat 9%bv _ eq_refl G9) as HE9. pose proof (ER 18%nat 18%bv _ eq_refl G18) as HE18.
pose proof (ER 19%nat 19%bv _ eq_refl G19) as HE19. pose proof (ER 20%nat 20%bv _ eq_refl G20) as HE20.
pose proof (ER 21%nat 21%bv _ eq_refl G21) as HE21. pose proof (ER 22%nat 22%bv _ eq_refl G22) as HE22.
pose proof (ER 23%nat 23%bv _ eq_refl G23) as HE23. pose proof (ER 24%nat 24%bv _ eq_refl G24) as HE24.
pose proof (ER 25%nat 25%bv _ eq_refl G25) as HE25. pose proof (ER 26%nat 26%bv _ eq_refl G26) as HE26.
pose proof (ER 27%nat 27%bv _ eq_refl G27) as HE27.
assert (HG : facts_ok E (mkFacts s1i_atoms s1i_conds s1i_alias)).
{ split; [|split].
- unfold s1i_atoms. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE8, HE9, HE21, HE22, HE34, HE35, HE32, HE33, HE36.
rewrite !unsigned_lit_small by (clear - Hp Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hsp0 Hsp1 Rbc Rbb HW Hcge Hcn Hac; lia).
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hp Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hsp0 Hsp1 Hsp16 Rbc Rbb HW Hcge Hcn Hn Hac. repeat split; lia.
- unfold s1i_conds. cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite !branch_geu_U.
rewrite (U_atom E 34 _ HE34), (U_atom E 26 _ HE26), (U_atom E 35 _ HE35), (U_atom E 19 _ HE19)
by lia.
split; [|split; [|exact I]]; apply Bool.negb_true_iff, Z.ltb_ge; clear - Hpdef Hcge; lia.
- unfold s1i_alias. cbn [f_alias alias_ok].
assert (B : 0 <= fimg + i * W /\ 0 <= bimg + i * W /\ fimg + i * W + c < 2 ^ 64 /\ bimg + i * W + c < 2 ^ 64 /\ 0 <= c)
by (clear - Hp HiW Hpdef Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac Hcge; lia).
split; [|split; [|split; [|split; [|split; [|exact I]]]]].
+ apply U_inj. rewrite (U_add_small E _ _ (fimg + i * W) c (U_atom E 25 _ HE25 ltac:(lia)) (U_atom E 22 _ HE22 ltac:(lia))) by lia.
rewrite (U_atom E 34 _ HE34) by lia. lia.
+ apply U_inj. rewrite (U_add_small E _ _ (fimg + i * W) c (U_atom E 24 _ HE24 ltac:(lia)) (U_atom E 22 _ HE22 ltac:(lia))) by lia.
rewrite (U_atom E 34 _ HE34) by lia. lia.
+ apply U_inj. rewrite (U_add_small E _ _ (bimg + i * W) c (U_atom E 27 _ HE27 ltac:(lia)) (U_atom E 22 _ HE22 ltac:(lia))) by lia.
rewrite (U_atom E 35 _ HE35) by lia. lia.
+ apply U_inj. rewrite (U_add_small E _ _ (bimg + i * W) c (U_atom E 20 _ HE20 ltac:(lia)) (U_atom E 22 _ HE22 ltac:(lia))) by lia.
rewrite (U_atom E 35 _ HE35) by lia. lia.
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 23 1 HE23 ltac:(lia)), !U_SLit. reflexivity. }
assert (HS : st_ok ubs2segs E ss_s1i (mkst regs (Z_to_bv 64 FL_S1I) memc (seg_rom ubs2segs))).
{ unfold ss_s1i. subst E. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | | exact HG].
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok, s1i_stk. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE2, unsigned_lit_small by (clear - Hsp0 Hsp1 Hac; lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
* eapply (chunk_ok_val _ _ _ _ _ _ _ 1); [reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W88].
* eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE36, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
apply val_mem_word_mem. exact WWm.
* eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE37, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
apply val_mem_word_mem. exact WGm.
* eapply (chunk_ok_val _ _ _ _ _ _ _ cfp); [cbn [sv_denot]; rewrite Z.add_0_r, HE38, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
apply val_mem_word_mem. exact WCm.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE34, unsigned_lit_small by (clear - Hp Hfimg0 Hfimg1 Hac; lia).
split; [lia|]. split; [clear - Hp Hfimg1 Hac Hn; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(clear - Hp Hn; lia))).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE35, unsigned_lit_small by (clear - Hp Hbimg0 Hbimg1 Hac; lia).
split; [lia|]. split; [clear - Hp Hbimg1 Hac Hn; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(clear - Hp Hn; lia))).
- unfold s1i_stk. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE34, HE35, !unsigned_lit_small by (clear - Hp Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hsp0 Hsp1 Hac; lia).
repeat split; try exact I; clear - Dfb Hp Hn Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hsp0 Hac; lia. }
clear HG.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S1I) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cmpPixel.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha0. rewrite HE37 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite HE38 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite HE18 in Ha2.
jreg HS (13%bv:reg) as Ha3. rewrite HE32 in Ha3. jreg HS (14%bv:reg) as Ha4. rewrite HE33 in Ha4.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (Hbq : forall a, byte_at (ms_mem ms) a = byte_at memc a) by (intros a; unfold byte_at; rewrite (mbyte_of_eq _ _ _ _ K1); reflexivity).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ apply (cmp_callD API IMG mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC
STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) p FL_S1R HJ (KD_eq _ _ _ _ K0 K1) ltac:(clear - Hp Hn; lia) Ha0 Ha1 Ha2).
- rewrite Hbq. exact Ha3.
- rewrite Hbq. exact Ha4.
- rewrite Hra. apply (ret_ok_even (Z_to_bv 64 FL_S1R)). vm_compute. reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hmem2 & Hres & Hfr2). clear HJ.
assert (K2 : KD mem0 spv mem2) by (apply (KD_eq _ _ _ _ (KD_eq _ _ _ _ K0 K1) Hmem2)).
jafter_stretch_keep HS 39%nat regs2 mem2 CMP_CLOB FL_S1R [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]];
(eapply (region_kept_out ubs2segs _ _ _ _ 0 0); [intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HE2, ?HE34, ?HE35, ?unsigned_lit_small by lia; lia
| cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HE2, ?HE34, ?HE35, ?unsigned_lit_small by lia; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_S1R) mem2 (seg_rom ubs2segs))) in HJ2.
set (E2 := havoc E 39 (map (getr regs2) CMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (EXIT : forall ss ms' pc', st_ok ubs2segs E2 ss ms' -> ss_pc ss = pc' -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) S1I_KEPT = true ->
((pc' = FL_S1F /\ exists c0, 0 <= c0 < W /\ CMP (i * W + c0) <> 0) \/ pc' = FL_S1X) ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall x, ms_mem ms' x = mem2 x) ->
s1i_post STK sp0 FP L A mem md Lc Ac mdc regs memc i (mkCfg ms' mdc)).
{ intros ss ms' pc' HS' Hpc Hrv Hkl Hpc' HJ' K'. exists (ms_regs ms'), (ms_mem ms'), pc'.
split; [rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact (KD_eq _ _ _ _ K2 K')|].
split; [intros x; rewrite (K' x), (Hmem2 x); apply K1|]. split; [exact Hpc'|].
intros rr Hrr. subst E E2. exact (regs_kept_of_st_ok ubs2segs _ ss ms' regs _ S1I_KEPT HS' EA1 Hkl rr Hrr). }
jbranch ubs2tbl HS.
-
assert (Hne : CMP p <> 0).
{ intros Hz. rewrite branch_ne_U, U_lit, (U_atom E2 41 0) in Hc; [discriminate Hc | | clear; lia | clear; lia].
subst E2. change 41%nat with (39 + 2)%nat. rewrite (ew_havoc_new E 39 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) by (cbn; lia).
cbn [nth map CMP_CLOB]. rewrite Hres. unfold CMP in Hz. rewrite Hz. reflexivity. }
clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ2 FL_S1F.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_S1F HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [| exact HJ2 |].
+ left. split; [reflexivity|]. exists c. split; [clear - Hcge Hcn Hn; lia | rewrite <- Hpdef; exact Hne].
+ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity.
-
clear Hc. jrun LAWS ubs2tbl_ok HS HJ2.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall x, ms_mem ms0 x = mem2 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch ubs2tbl HS.
+
rewrite branch_ne_U, (U_atom E2 36 W), (U_atom_off E2 22 c 1) in Hc
by first [subst E2; ew_havocA; first [exact HE36 | exact HE22] | lia].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.eqb_spec W (c + 1)); [discriminate Hc | lia]). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ2 FL_S1I.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K4 : forall x, ms_mem ms1 x = mem2 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs _ S1I_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (c + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ i HJ2 (KD_eq _ _ _ _ K2 K4) Hfi Hbi Hi ltac:(clear - Hcge; lia) ltac:(clear - Hcn; lia) Hn1).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 25%bv ltac:(cbv; auto 20)). exact G25.
- rewrite (HKR 24%bv ltac:(cbv; auto 20)). exact G24.
- rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact G26.
- rewrite (HKR 27%bv ltac:(cbv; auto 20)). exact G27.
- rewrite (HKR 20%bv ltac:(cbv; auto 20)). exact G20.
- rewrite (HKR 19%bv ltac:(cbv; auto 20)). exact G19.
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite HE22, unsigned_lit_small by lia; f_equal; lia).
- intros k Hk. unfold mbyte. rewrite (K4 _), (Hmem2 _), (K1 _). apply (W88 k Hk). }
cbv beta. intros c' (regs' & mem' & pc' & -> & HJ' & K' & Keq' & Hpc' & HK'). exists regs', mem', pc'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [intros x; rewrite (Keq' x), (K4 x), (Hmem2 x); apply K1|]. split; [exact Hpc'|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ2 FL_S1X.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_S1X HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [right; reflexivity | exact HJ2 |].
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3.
Qed.
Definition s1o_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (c' : config) : Prop :=
exists regs' mem' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KD mem0 spv mem' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 96 <= a < spv + 104) -> mbyte ubs2segs mem' a = mbyte ubs2segs memc a) /\
((pc' = FL_S2 /\ exists top c, 0 <= top < H /\ 0 <= c < W /\ CMP (top * W + c) <> 0 /\
getr regs' 26 = Z_to_bv 64 H /\ getr regs' 12 = Z_to_bv 64 top /\ getr regs' 13 = Z_to_bv 64 top /\ word_mem ubs2segs mem' (spv + 96) top)
\/ (pc' = FL_IDENT /\ getr regs' 10 = Z_to_bv 64 W)) /\
(forall r : reg, In r S1O_KEPT -> getr regs' r = getr regs r).
Lemma mk_s1o : forall (head : bool) pc (regs : bvmap 5 word) m i,
KD mem0 spv m -> (forall a, spv + 96 <= a < spv + 104 -> writable_at ubs2segs m a) ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 8 = Z_to_bv 64 bimg ->
getr regs 25 = Z_to_bv 64 (fimg + i * W) -> getr regs 27 = Z_to_bv 64 (bimg + i * W) -> getr regs 23 = Z_to_bv 64 1 ->
word_mem ubs2segs m (spv + 88) 1 -> 0 <= i < H ->
(head = true -> getr regs 10 = Z_to_bv 64 W /\ getr regs 11 = Z_to_bv 64 i /\ pc = FL_S1O) ->
(head = false -> word_mem ubs2segs m (spv + 96) i) ->
st_ok ubs2segs (Ereg regs (map (Z_to_bv 64) [H; i; W] ++ [])) (if head then ss_s1o else ss_s1e pc) (mkst regs (Z_to_bv 64 pc) m (seg_rom ubs2segs)).
Proof.
intros head pc regs m i K Hwr G2 G9 G8 G25 G27 G23 W88 Hi Hhd Htl. dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
assert (WKD : forall o v, (o = 80 \/ o = 104) -> word_mem ubs2segs mem0 (spv + o) v -> word_mem ubs2segs m (spv + o) v).
{ intros o v Ho Hw k Hk. rewrite (K (spv + o + Z.of_nat k)) by (clear - Ho Hk Hsp0 Hsp1 Hac; lia). apply Hw. exact Hk. }
pose proof (WKD 80 H ltac:(lia) WH0) as WHm. pose proof (WKD 104 W ltac:(lia) WW0) as WWm.
assert (HiW : 0 <= i * W /\ i * W + W <= N) by (rewrite HN; clear - Hi HW; nia).
set (E := Ereg regs (map (Z_to_bv 64) [H; i; W] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 H) by (subst E; apply (Ereg_vals regs [H; i; W] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 i) by (subst E; apply (Ereg_vals regs [H; i; W] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 W) by (subst E; apply (Ereg_vals regs [H; i; W] [] 2%nat); reflexivity).
assert (HE2 : ew E 2 = Z_to_bv 64 spv) by (rewrite (HE 2%nat 2%bv eq_refl); exact G2).
assert (HE8 : ew E 8 = Z_to_bv 64 bimg) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE9 : ew E 9 = Z_to_bv 64 fimg) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE23 : ew E 23 = Z_to_bv 64 1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE25 : ew E 25 = Z_to_bv 64 (fimg + i * W)) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (HE27 : ew E 27 = Z_to_bv 64 (bimg + i * W)) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (BND : CEIL_MIN <= spv <= 2 ^ 63 /\ spv mod 16 = 0 /\ 4096 <= fimg <= CEIL_MAX - 1 /\ 4096 <= bimg <= CEIL_MAX - 1 /\
4096 <= fimg + i * W <= CEIL_MAX - 1 /\ 4096 <= bimg + i * W <= CEIL_MAX - 1 /\ 1 <= H <= 65535 /\ 0 <= i <= 65534 /\ 1 <= W <= 65535)
by (clear - Hsp0 Hsp1 Hsp16 Hfimg0 Hfimg1 Hbimg0 Hbimg1 HiW HW HH Hi Hac; lia).
assert (HA : atoms_ok E s1o_atoms).
{ unfold s1o_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE8, HE9, HE25, HE27, HE32, HE33, HE34. rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. clear - BND. repeat split; lia. }
assert (HR : forall rg, rg = s1o_hd \/ (head = false /\ rg = s1o_tl) -> region_ok ubs2segs E m rg).
{ intros rg Hrg. assert (Hb : r_base rg = Some 2%nat /\ r_lo rg = 80 /\ r_hi rg = 112 /\ r_wlo rg = 96 /\ r_whi rg = 104)
by (destruct Hrg as [-> | [_ ->]]; repeat split; reflexivity).
destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5). unfold region_ok. rewrite Hb1, Hb2, Hb3, Hb4, Hb5. cbn [base_val].
rewrite HE2, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
assert (C80 : chunk_ok ubs2segs E m spv (mkChunk 80 (CVal 8 (SOff 32 0)))).
{ eapply (chunk_ok_val _ _ _ _ _ _ _ H); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
apply val_mem_word_mem. exact WHm. }
assert (C88 : chunk_ok ubs2segs E m spv (mkChunk 88 (CVal 8 (SLit 1)))).
{ eapply (chunk_ok_val _ _ _ _ _ _ _ 1); [reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W88]. }
assert (C104 : chunk_ok ubs2segs E m spv (mkChunk 104 (CVal 8 (SOff 34 0)))).
{ eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
apply val_mem_word_mem. exact WWm. }
destruct Hrg as [-> | [Hh ->]]; cbn [r_chunks s1o_hd s1o_tl].
- constructor; [exact C80|]. constructor; [exact C88|]. constructor; [exact C104|]. constructor.
- constructor; [exact C80|]. constructor; [exact C88|]. constructor; [|constructor; [exact C104|constructor]].
eapply (chunk_ok_val _ _ _ _ _ _ _ i); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
apply val_mem_word_mem. exact (Htl Hh). }
destruct head.
- destruct (Hhd eq_refl) as (G10 & G11 & ->). unfold ss_s1o.
apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [apply HR; left; reflexivity | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I |].
fold E. split; [| split].
+ cbn [f_atoms atoms_ok]. split; [| split; [| exact HA]]; unfold afact_ok; cbn [af_lo af_hi af_al2];
rewrite (HE 10%nat 10%bv eq_refl) || rewrite (HE 11%nat 11%bv eq_refl); rewrite ?G10, ?G11, unsigned_lit_small by lia;
change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - BND; repeat split; lia.
+ cbn [f_conds conds_ok]. split; [| exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, (U_atom E 25 _ HE25), (U_atom E 9 _ HE9) by lia. apply Bool.negb_true_iff, Z.ltb_ge. lia.
+ unfold s1o_alias. cbn [f_alias alias_ok].
assert (HE11 : ew E 11 = Z_to_bv 64 i) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (UM : U E (SMd M_MUL (SOff 11 0) (SOff 34 0)) = i * W)
by (apply (U_mul_small' E _ _ i W (U_atom E 11 _ HE11 ltac:(lia)) (U_atom E 34 _ HE34 ltac:(lia))); nia).
split; [|split; [|split; [|split; [|exact I]]]].
* apply U_inj. rewrite (U_add_small E _ _ (i * W) fimg UM (U_atom E 9 _ HE9 ltac:(lia))) by lia.
rewrite (U_atom E 25 _ HE25) by lia. lia.
* apply U_inj. rewrite (U_add_small E _ _ (i * W) bimg UM (U_atom E 8 _ HE8 ltac:(lia))) by lia.
rewrite (U_atom E 27 _ HE27) by lia. lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 27 _ HE27), (U_atom E 8 _ HE8), !U_SLit by lia.
destruct (Z.ltb_spec (bimg + i * W) bimg); [lia|]. vm_compute. reflexivity.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 23 1 HE23 ltac:(lia)), !U_SLit. reflexivity.
- unfold ss_s1e.
apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [apply HR; right; split; reflexivity | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I |].
split; [exact HA | split; exact I].
Qed.
Lemma fl_s1o : forall (n : nat) (i : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc,
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
spv = sp0 - 272 -> 272 <= STK ->
0 <= i -> i + Z.of_nat n = H -> (1 <= n)%nat ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 18 = Z_to_bv 64 fhp -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 8 = Z_to_bv 64 bimg ->
getr regs 25 = Z_to_bv 64 (fimg + i * W) -> getr regs 24 = Z_to_bv 64 (fimg + i * W) ->
getr regs 27 = Z_to_bv 64 (bimg + i * W) -> getr regs 20 = Z_to_bv 64 (bimg + i * W) ->
getr regs 23 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 W -> getr regs 11 = Z_to_bv 64 i ->
word_mem ubs2segs memc (spv + 88) 1 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S1O) memc (seg_rom ubs2segs)) mdc) (s1o_post STK sp0 FP L A mem md Lc Ac mdc regs memc).
Proof.
intros n. induction n as [|n IH]; intros i STK sp0 FP L A mem md Lc Ac mdc regs memc HJ K0 Hfi Hbi Hspv HSTK Hi0 Hin Hn
G2 G18 G9 G8 G25 G24 G27 G20 G23 G10 G11 W88; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HiW : 0 <= i * W /\ i * W + W <= N) by (rewrite HN; clear - Hi0 Hin Hn HW; nia).
assert (WRS : forall m', journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac m' mdc -> forall a, spv + 96 <= a < spv + 104 -> writable_at ubs2segs m' a).
{ intros m' HJm a Ha. pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _). apply Hstw. clear - Ha Hspv HSTK. lia. }
assert (WRT : forall E0 cs, bv_unsigned (ew E0 2) = spv ->
wr_ok E0 [YQ0b.mkRegion (Some 2%nat) 80 112 96 104 cs] STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 cs H2. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia | apply wr_ok_nil]. }
assert (FRF : forall E0 cs (m m' : word -> option byte), bv_unsigned (ew E0 2) = spv ->
frame_of E0 [YQ0b.mkRegion (Some 2%nat) 80 112 96 104 cs] m m' ->
forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 96 <= a < spv + 104) -> mbyte ubs2segs m' a = mbyte ubs2segs m a).
{ intros E0 cs m m' H2 HFx a Ha Hna. apply (mbyte_of_frame _ _ _ _ a HFx Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | []]; cbn [r_base r_wlo r_whi base_val]; rewrite H2; exact Hna. }
assert (KDF : forall E0 cs (m m' : word -> option byte), bv_unsigned (ew E0 2) = spv -> KD mem0 spv m ->
frame_of E0 [YQ0b.mkRegion (Some 2%nat) 80 112 96 104 cs] m m' -> KD mem0 spv m').
{ intros E0 cs m m' H2 Km HFx. apply (KD_frame _ _ _ _ Km). intros a Ha Hna1 Hna2 Hna3 Hna4.
apply (FRF E0 cs m m' H2 HFx a Ha). clear - Hna4; lia. }
assert (WMF : forall (m m' : word -> option byte) o v,
(forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 96 <= a < spv + 104) -> mbyte ubs2segs m' a = mbyte ubs2segs m a) ->
(o + 8 <= 96 \/ 104 <= o) -> 0 <= o -> o + 8 <= 128 -> word_mem ubs2segs m (spv + o) v -> word_mem ubs2segs m' (spv + o) v).
{ intros m m' o v Hf Ho Ho0 Ho1 Hw k Hk. rewrite (Hf (spv + o + Z.of_nat k)) by (clear - Ho Ho0 Ho1 Hk Hsp0 Hsp1 Hac; lia). apply Hw. exact Hk. }
pose proof (mk_s1o true FL_S1O regs memc i K0 (WRS _ HJ) G2 G9 G8 G25 G27 G23 W88 ltac:(clear - Hi0 Hin Hn; lia)
ltac:(intros _; split; [exact G10 | split; [exact G11 | reflexivity]]) ltac:(intros X; discriminate X)) as HS.
cbn iota in HS.
set (E := Ereg regs (map (Z_to_bv 64) [H; i; W] ++ [])) in HS.
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S1O) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ FL_S1I. { apply WRT. exact HU2. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2 K0 HF) as K1. pose proof (FRF _ _ _ _ HU2 HF) as F1. clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs2segs E ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hv; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hv);
assert (RGL : forall (r : reg) z, sr_get (ss_regs ssx) r = SLit z -> getr (ms_regs msx) r = Z_to_bv 64 z)
by (intros r z Hr; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (W96a : word_mem ubs2segs (ms_mem ms) (spv + 96) i).
{ apply (s1_chunk_word E _ _ 96 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 96 (CVal 8 (SOff 11 0))) ltac:(cbn [In]; tauto)));
[cbn [sv_denot]; rewrite Z.add_0_r, (HE 11%nat 11%bv eq_refl), G11, unsigned_lit_small by (clear - Hi0 Hin Hn HH; lia); reflexivity
| clear - Hi0 Hin Hn HH; lia]. }
clear Hcs.
assert (W88a : word_mem ubs2segs (ms_mem ms) (spv + 88) 1) by (apply (WMF memc _ 88 1 F1); [lia | lia | lia | exact W88]).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_s1i (Z.to_nat W) 0 STK sp0 FP L A mem md Lc Ac mdc _ _ i HJ K1 Hfi Hbi ltac:(clear - Hi0 Hin Hn; lia) ltac:(clear; lia)
ltac:(clear - HW; lia) ltac:(clear - HW; lia)).
- apply (RG 2%bv 2%nat _ eq_refl). rewrite (HE 2%nat 2%bv eq_refl). exact G2.
- apply (RG 18%bv 18%nat _ eq_refl). rewrite (HE 18%nat 18%bv eq_refl). exact G18.
- apply (RG 9%bv 9%nat _ eq_refl). rewrite (HE 9%nat 9%bv eq_refl). exact G9.
- apply (RG 8%bv 8%nat _ eq_refl). rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- apply (RG 25%bv 25%nat _ eq_refl). rewrite (HE 25%nat 25%bv eq_refl). exact G25.
- apply (RG 24%bv 24%nat _ eq_refl). rewrite (HE 24%nat 24%bv eq_refl). exact G24.
- apply (RG 26%bv 25%nat _ eq_refl). rewrite (HE 25%nat 25%bv eq_refl). exact G25.
- apply (RG 27%bv 27%nat _ eq_refl). rewrite (HE 27%nat 27%bv eq_refl). exact G27.
- apply (RG 20%bv 20%nat _ eq_refl). rewrite (HE 20%nat 20%bv eq_refl). exact G20.
- apply (RG 19%bv 27%nat _ eq_refl). rewrite (HE 27%nat 27%bv eq_refl). exact G27.
- apply (RGL 21%bv 1 eq_refl).
- apply (RG 23%bv 23%nat _ eq_refl). rewrite (HE 23%nat 23%bv eq_refl). exact G23.
- apply (RGL 22%bv 0 eq_refl).
- exact W88a. }
cbv beta. intros c' (regs' & mem' & pc' & -> & HJ' & K' & Keq' & Hpc' & HK'').
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs _ [2; 3; 4; 8; 9; 18; 20; 23; 24; 25; 27]%bv HS
ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR0 end.
assert (HK' : forall r : reg, In r [2; 3; 4; 8; 9; 18; 20; 23; 24; 25; 27]%bv -> getr regs' r = getr regs r).
{ intros rr Hrr. rewrite (HK'' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). apply (HKR0 rr Hrr). }
assert (W96' : word_mem ubs2segs mem' (spv + 96) i) by (intros k Hk; unfold mbyte; rewrite (Keq' _); apply (W96a k Hk)).
assert (W88' : word_mem ubs2segs mem' (spv + 88) 1) by (intros k Hk; unfold mbyte; rewrite (Keq' _); apply (W88a k Hk)).
assert (F' : forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 96 <= a < spv + 104) -> mbyte ubs2segs mem' a = mbyte ubs2segs memc a).
{ intros a Ha Hna. rewrite (mbyte_of_eq _ _ _ _ Keq'). apply F1; assumption. }
clear HJ HS RG RGL HK'' HKR0 K1 F1 W96a W88a Keq'.
assert (G2' : getr regs' 2 = Z_to_bv 64 spv) by (rewrite (HK' 2%bv ltac:(cbv; auto 50)); exact G2).
assert (G18' : getr regs' 18 = Z_to_bv 64 fhp) by (rewrite (HK' 18%bv ltac:(cbv; auto 50)); exact G18).
assert (G9' : getr regs' 9 = Z_to_bv 64 fimg) by (rewrite (HK' 9%bv ltac:(cbv; auto 50)); exact G9).
assert (G8' : getr regs' 8 = Z_to_bv 64 bimg) by (rewrite (HK' 8%bv ltac:(cbv; auto 50)); exact G8).
assert (G25' : getr regs' 25 = Z_to_bv 64 (fimg + i * W)) by (rewrite (HK' 25%bv ltac:(cbv; auto 50)); exact G25).
assert (G24' : getr regs' 24 = Z_to_bv 64 (fimg + i * W)) by (rewrite (HK' 24%bv ltac:(cbv; auto 50)); exact G24).
assert (G27' : getr regs' 27 = Z_to_bv 64 (bimg + i * W)) by (rewrite (HK' 27%bv ltac:(cbv; auto 50)); exact G27).
assert (G20' : getr regs' 20 = Z_to_bv 64 (bimg + i * W)) by (rewrite (HK' 20%bv ltac:(cbv; auto 50)); exact G20).
assert (G23' : getr regs' 23 = Z_to_bv 64 1) by (rewrite (HK' 23%bv ltac:(cbv; auto 50)); exact G23).
set (E' := Ereg regs' (map (Z_to_bv 64) [H; i; W] ++ [])).
assert (HE' : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E' m = getr regs' rr) by (intros; subst E'; apply ew_Ereg_nat; assumption).
assert (HE32' : ew E' 32 = Z_to_bv 64 H) by (subst E'; apply (Ereg_vals regs' [H; i; W] [] 0%nat); reflexivity).
assert (HE33' : ew E' 33 = Z_to_bv 64 i) by (subst E'; apply (Ereg_vals regs' [H; i; W] [] 1%nat); reflexivity).
assert (HE34' : ew E' 34 = Z_to_bv 64 W) by (subst E'; apply (Ereg_vals regs' [H; i; W] [] 2%nat); reflexivity).
assert (HU2' : bv_unsigned (ew E' 2) = spv) by (rewrite (HE' 2%nat 2%bv eq_refl), G2'; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (EXIT : forall ss ms' pc'', st_ok ubs2segs E' ss ms' -> ss_pc ss = pc'' -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) S1O_KEPT = true ->
((pc'' = FL_S2 /\ exists top c, 0 <= top < H /\ 0 <= c < W /\ CMP (top * W + c) <> 0 /\
getr (ms_regs ms') 26 = Z_to_bv 64 H /\ getr (ms_regs ms') 12 = Z_to_bv 64 top /\ getr (ms_regs ms') 13 = Z_to_bv 64 top /\
word_mem ubs2segs (ms_mem ms') (spv + 96) top)
\/ (pc'' = FL_IDENT /\ getr (ms_regs ms') 10 = Z_to_bv 64 W)) ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> KD mem0 spv (ms_mem ms') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 96 <= a < spv + 104) -> mbyte ubs2segs (ms_mem ms') a = mbyte ubs2segs memc a) ->
s1o_post STK sp0 FP L A mem md Lc Ac mdc regs memc (mkCfg ms' mdc)).
{ intros ss ms' pc'' HS' Hpc Hrv Hkl Hpc'' HJ'' K'' F''. exists (ms_regs ms'), (ms_mem ms'), pc''.
split; [rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ''|]. split; [exact K''|].
split; [exact F''|]. split; [exact Hpc''|].
intros rr Hrr. rewrite <- (HK' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). subst E'.
exact (regs_kept_of_st_ok ubs2segs _ ss ms' regs' _ S1O_KEPT HS' (env_agree_refl _ _) Hkl rr Hrr). }
assert (CW96 : forall ss ms' e val, st_ok ubs2segs E' ss ms' ->
(exists rg0, nth_error (ss_mem ss) 0 = Some rg0 /\ r_base rg0 = Some 2%nat /\ In (mkChunk 96 (CVal 8 e)) (r_chunks rg0)) ->
sv_denot E' e = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> word_mem ubs2segs (ms_mem ms') (spv + 96) val).
{ intros ss ms' e val HS' (rg0 & Hrg0 & Hb0 & Hin96) He Hval.
pose proof (st_region_chunks ubs2segs E' ss ms' 0 rg0 2%nat spv HS' Hrg0 Hb0 HU2') as Hcs0.
exact (s1_chunk_word E' _ _ 96 _ _ (proj1 (Forall_forall _ _) Hcs0 _ Hin96) He Hval). }
destruct Hpc' as [[-> (c0 & Hc0 & Hne)] | ->].
-
pose proof (mk_s1o false FL_S1F regs' mem' i K' (WRS _ HJ') G2' G9' G8' G25' G27' G23' W88' ltac:(clear - Hi0 Hin Hn; lia)
ltac:(intros X; discriminate X) ltac:(intros _; exact W96')) as HS.
cbn iota in HS. fold E' in HS.
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 FL_S1F) mem' (seg_rom ubs2segs))) in HJ'.
jrun LAWS ubs2tbl_ok HS HJ'. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K' HF) as K2. pose proof (FRF _ _ _ _ HU2' HF) as F2. clear HF HG.
jbranch ubs2tbl HS.
+ clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ' FL_S2. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K2 HF) as K3. pose proof (FRF _ _ _ _ HU2' HF) as F3. clear HF HG.
apply SR_ret. apply (EXIT _ _ FL_S2 HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [| exact HJ' | exact K3 |].
* left. split; [reflexivity|]. exists i, c0. split; [clear - Hi0 Hin Hn; lia|]. split; [exact Hc0|]. split; [exact Hne|].
split; [reg_nowF HS ltac:(rewrite HE32', unsigned_lit_small by (clear - HH; lia); reflexivity)|].
split; [reg_nowF HS ltac:(rewrite HE33', unsigned_lit_small by (clear - Hi0 Hin Hn HH; lia); reflexivity)|].
split; [reg_nowF HS ltac:(rewrite HE33', unsigned_lit_small by (clear - Hi0 Hin Hn HH; lia); reflexivity)|].
apply (CW96 _ _ (SOff 33 0) i HS); [eexists; split; [reflexivity|]; split; [reflexivity|]; cbn [r_chunks In]; tauto
| cbn [sv_denot]; rewrite Z.add_0_r, HE33', Z_to_bv_bv_unsigned; reflexivity | clear - Hi0 Hin Hn HH; lia].
* intros a Ha Hna. rewrite (F3 a Ha Hna), (F2 a Ha Hna). apply F'; assumption.
+ exfalso. rewrite branch_ne_U, (U_atom E' 32 H), (U_atom E' 33 i) in Hc
by first [exact HE32' | exact HE33' | clear - Hi0 Hin Hn HH; lia].
destruct (Z.eqb_spec H i); [clear - Hin Hn e; lia | discriminate Hc].
-
pose proof (mk_s1o false FL_S1X regs' mem' i K' (WRS _ HJ') G2' G9' G8' G25' G27' G23' W88' ltac:(clear - Hi0 Hin Hn; lia)
ltac:(intros X; discriminate X) ltac:(intros _; exact W96')) as HS.
cbn iota in HS. fold E' in HS.
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 FL_S1X) mem' (seg_rom ubs2segs))) in HJ'.
jrun LAWS ubs2tbl_ok HS HJ'. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K' HF) as K2. pose proof (FRF _ _ _ _ HU2' HF) as F2. clear HF HG.
jbranch ubs2tbl HS.
+ rewrite branch_ne_U, (U_atom_off E' 33 i 1), (U_atom E' 32 H) in Hc
by first [exact HE32' | exact HE33' | clear - Hi0 Hin Hn HH; lia].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.eqb_spec (i + 1) H); [discriminate Hc | lia]). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ' FL_S1O. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K2 HF) as K3. pose proof (FRF _ _ _ _ HU2' HF) as F3. clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs' _ S1O_KEPT HS ltac:(subst E'; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ HJ' K3 Hfi Hbi Hspv HSTK ltac:(clear - Hi0; lia) ltac:(clear - Hin; lia) Hn1).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2'.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18'.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9'.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8'.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 25%bv HS) end. eval_sr_get. apply denot_of_U'.
replace (fimg + (i + 1) * W) with (fimg + i * W + W) by (clear; lia).
apply (U_add_small E' _ _ (fimg + i * W) W); [apply U_atom; [rewrite (HE' 25%nat 25%bv eq_refl); exact G25' | clear - HiW HW Hfimg0 Hfimg1 Hac; lia]
| apply U_atom; [exact HE34' | clear - HW; lia] | clear - HiW Hfimg0; lia | clear - HW; lia | clear - HiW Hfimg0 Hfimg1 HW Hac; lia].
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 24%bv HS) end. eval_sr_get. apply denot_of_U'.
replace (fimg + (i + 1) * W) with (fimg + i * W + W) by (clear; lia).
apply (U_add_small E' _ _ (fimg + i * W) W); [apply U_atom; [rewrite (HE' 24%nat 24%bv eq_refl); exact G24' | clear - HiW HW Hfimg0 Hfimg1 Hac; lia]
| apply U_atom; [exact HE34' | clear - HW; lia] | clear - HiW Hfimg0; lia | clear - HW; lia | clear - HiW Hfimg0 Hfimg1 HW Hac; lia].
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 27%bv HS) end. eval_sr_get. apply denot_of_U'.
replace (bimg + (i + 1) * W) with (bimg + i * W + W) by (clear; lia).
apply (U_add_small E' _ _ (bimg + i * W) W); [apply U_atom; [rewrite (HE' 27%nat 27%bv eq_refl); exact G27' | clear - HiW HW Hbimg0 Hbimg1 Hac; lia]
| apply U_atom; [exact HE34' | clear - HW; lia] | clear - HiW Hbimg0; lia | clear - HW; lia | clear - HiW Hbimg0 Hbimg1 HW Hac; lia].
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 20%bv HS) end. eval_sr_get. apply denot_of_U'.
replace (bimg + (i + 1) * W) with (bimg + i * W + W) by (clear; lia).
apply (U_add_small E' _ _ (bimg + i * W) W); [apply U_atom; [rewrite (HE' 20%nat 20%bv eq_refl); exact G20' | clear - HiW HW Hbimg0 Hbimg1 Hac; lia]
| apply U_atom; [exact HE34' | clear - HW; lia] | clear - HiW Hbimg0; lia | clear - HW; lia | clear - HiW Hbimg0 Hbimg1 HW Hac; lia].
- reg_nowF HS ltac:(rewrite (HE' 23%nat 23%bv eq_refl), G23', Z_to_bv_bv_unsigned; reflexivity).
- reg_nowF HS ltac:(rewrite HE34', Z_to_bv_bv_unsigned; reflexivity).
- reg_nowF HS ltac:(rewrite HE33', unsigned_lit_small by (clear - Hi0 Hin Hn HH; lia); reflexivity).
- apply (WMF mem' _ 88 1); [intros a Ha Hna; rewrite (F3 a Ha Hna), (F2 a Ha Hna); reflexivity | lia | lia | lia | exact W88']. }
cbv beta. intros c' (regs'' & mem'' & pc'' & -> & HJ'' & K'' & F'' & Hpc'' & HK''). exists regs'', mem'', pc''.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact K''|].
split; [intros a Ha Hna; rewrite (F'' a Ha Hna), (F3 a Ha Hna), (F2 a Ha Hna); apply F'; assumption|].
split; [exact Hpc''|].
intros rr Hrr. rewrite (HK'' rr Hrr), (HKR rr Hrr). apply HK'. clear - Hrr. cbv in Hrr. cbv. intuition.
+ clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ' FL_IDENT. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K2 HF) as K3. pose proof (FRF _ _ _ _ HU2' HF) as F3. clear HF HG.
apply SR_ret. apply (EXIT _ _ FL_IDENT HS eq_refl eq_refl ltac:(vm_compute; reflexivity));
[right; split; [reflexivity | reg_nowF HS ltac:(rewrite HE34', Z_to_bv_bv_unsigned; reflexivity)] | exact HJ' | exact K3 |].
intros a Ha Hna. rewrite (F3 a Ha Hna), (F2 a Ha Hna). apply F'; assumption.
Qed.
End d.
End S.
End b.
