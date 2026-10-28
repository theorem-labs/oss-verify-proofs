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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2o UI2p UI24.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition s1i_stk : list YP09.chunk :=
[mkChunk 88 (CVal 8 (SLit 1)); mkChunk 104 (CVal 8 (SOff 36 0)); mkChunk 112 (CVal 8 (SOff 37 0)); mkChunk 120 (CVal 8 (SOff 38 0))].
Definition s1i_atoms : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (8%nat, mkAF 4096 CEIL_MAX 0); (9%nat, mkAF 4096 CEIL_MAX 0);
(21%nat, mkAF 1 1 0); (23%nat, mkAF 1 1 0);
(34%nat, mkAF 4096 (CEIL_MAX - 1) 0); (35%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (36%nat, mkAF 1 65535 0) ].
Definition s1i_conds : list acond :=
[ mkAC BC_GEU (SOff 34 0) (SOff 26 0); mkAC BC_GEU (SOff 35 0) (SOff 19 0) ].
Definition s1i_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 25 0) (SOff 22 0), SOff 34 0); (SAlu ALU_ADD (SOff 24 0) (SOff 22 0), SOff 34 0);
(SAlu ALU_ADD (SOff 27 0) (SOff 22 0), SOff 35 0); (SAlu ALU_ADD (SOff 20 0) (SOff 22 0), SOff 35 0);
(SAlu ALU_XOR (SOff 23 0) (SLit 0), SLit 1) ].
Definition ss_s1i : sstate :=
mkSS FL_S1I sr_atoms
[ YP09.mkRegion (Some 2%nat) 88 128 88 88 s1i_stk ;
YP09.mkRegion (Some 34%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 32 0))] ;
YP09.mkRegion (Some 35%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))] ]
None (mkFacts s1i_atoms s1i_conds s1i_alias).
Lemma wrap64_nzV : forall v, -256 < v < 256 -> v <> 0 -> zcanon (bv_wrap 64 v + 0) <> 0.
Proof using. intros v Hv Hnz. unfold zcanon, bv_wrap, M64. cbn [bv_modulus]. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia.
intros Hm. apply (Z.mod_divide v (2 ^ 64)) in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0 \/ q <= -1 \/ q >= 1) by lia. nia. Qed.
Lemma cmpPixel_fn_rangeV : forall cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef a b,
-256 < cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef a b < 256.
Proof using. intros. unfold cmpPixel_fn. repeat (destruct (_ : bool); try lia). apply memcmp_spec_range. Qed.
Definition S1I_KEPT : list reg := [2; 3; 4; 8; 9; 18; 20; 21; 23; 24; 25; 27]%bv.
Definition s1o_facts : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (32%nat, mkAF 1 65535 0); (33%nat, mkAF 0 65534 0); (34%nat, mkAF 1 65535 0) ].
Definition s1o_hfacts : list (nat * afact) :=
[ (8%nat, mkAF 4096 CEIL_MAX 0); (9%nat, mkAF 4096 CEIL_MAX 0); (10%nat, mkAF 1 65535 0);
(25%nat, mkAF 4096 CEIL_MAX 0); (27%nat, mkAF 4096 CEIL_MAX 0); (23%nat, mkAF 1 1 0) ].
Definition s1o_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SOff 34 0)) (SOff 9 0), SOff 25 0);
(SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SOff 34 0)) (SOff 8 0), SOff 27 0);
(SAlu ALU_XOR (SAlu ALU_SLTU (SOff 27 0) (SOff 8 0)) (SLit (-1)), SLit (-1)); (SAlu ALU_XOR (SOff 23 0) (SLit 0), SLit 1) ].
Definition s1o_mem (cs : list YP09.chunk) : list YP09.region := [ YP09.mkRegion (Some 2%nat) 80 112 96 104 cs ].
Definition s1o_hstk : list YP09.chunk := [mkChunk 88 (CVal 8 (SLit 1)); mkChunk 104 (CVal 8 (SOff 34 0))].
Definition s1o_estk : list YP09.chunk :=
[mkChunk 80 (CVal 8 (SOff 32 0)); mkChunk 88 (CVal 8 (SLit 1)); mkChunk 96 (CVal 8 (SOff 33 0)); mkChunk 104 (CVal 8 (SOff 34 0))].
Definition ss_s1o : sstate :=
mkSS FL_S1O sr_atoms (s1o_mem s1o_hstk) None (mkFacts (s1o_facts ++ s1o_hfacts) [mkAC BC_GEU (SOff 25 0) (SOff 9 0)] s1o_alias).
Definition ss_s1e (pc : Z) : sstate := mkSS pc sr_atoms (s1o_mem s1o_estk) None (mkFacts s1o_facts [] []).
Definition S1O_KEPT : list reg := [2; 3; 4; 8; 9; 18]%bv.
Lemma word_mem_eq : forall (m m' : word -> option byte) a v, (forall x, m' x = m x) -> word_mem ubs0segs m a v -> word_mem ubs0segs m' a v.
Proof using. intros m m' a v Heq Hw k Hk. rewrite (mbyte_of_eq _ _ _ _ Heq). apply Hw. exact Hk. Qed.
Lemma U_zext16_shifts : forall E a, U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 48)) (SLit 48)) = U E a mod 2 ^ 16.
Proof using.
intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
change (Z.land (zcanon 48) 63) with 48. pose proof (U_range E a) as [R0 R1].
rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon at 2. unfold M64.
replace (2 ^ 64) with (2 ^ 16 * 2 ^ 48) at 1 by reflexivity.
rewrite Z.mul_mod_distr_r by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
pose proof (Z.mod_pos_bound (U E a) (2 ^ 16) ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Section f.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Let CMP := CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef.
Definition s1i_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (i : Z) (c' : config) : Prop :=
exists regs' mem' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KD mem0 spv mem' /\ (forall x, mem' x = memc x) /\
((pc' = FL_S1F /\ exists c, 0 <= c < W /\ CMP (i * W + c) <> 0) \/ (pc' = FL_S1X /\   forall c2, 0 <= c2 < W -> CMP (i * W + c2) = 0)) /\
(forall r : reg, In r S1I_KEPT -> getr regs' r = getr regs r).
Lemma fl_s1iV : forall (n : nat) (c : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (i : Z),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= i < H -> 0 <= c -> c + Z.of_nat n = W -> (1 <= n)%nat ->
word_mem ubs0segs memc (spv + 88) 1 ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 bimg -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 24 = Z_to_bv 64 (fimg + i * W) -> getr regs 25 = Z_to_bv 64 (fimg + i * W) -> getr regs 26 = Z_to_bv 64 (fimg + i * W) ->
getr regs 27 = Z_to_bv 64 (bimg + i * W) -> getr regs 20 = Z_to_bv 64 (bimg + i * W) -> getr regs 19 = Z_to_bv 64 (bimg + i * W) ->
getr regs 21 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 c ->
(forall c2, 0 <= c2 < c -> CMP (i * W + c2) = 0) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 FL_S1I) memc (seg_rom ubs0segs)) mdc) (s1i_postV STK sp0 FP L A mem md Lc Ac mdc regs memc i).
Proof using HC IMG.
intros n. induction n as [|n IH]; intros c STK sp0 FP L A mem md Lc Ac mdc regs memc i HJ K0 Hfi Hbi Hi Hcge Hcn Hn W88
G2 G8 G9 G18 G24 G25 G26 G27 G20 G19 G21 G23 G22 HEQ; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC memc K0)
as (_ & _ & _ & _ & _ & WHm & WWm & WGm & WCm).
assert (Hp : 0 <= i * W + c /\ i * W + c + Z.of_nat (Datatypes.S n) <= N) by (rewrite HN; clear - Hi Hcge Hcn Hn HW; nia).
assert (HiW : 0 <= i * W /\ i * W + W <= N) by (rewrite HN; clear - Hi HW; nia).
set (p := i * W + c) in *. assert (Hpdef : p = i * W + c) by reflexivity. clearbody p.
set (bc := byte_at memc (fimg + p)). set (bb := byte_at memc (bimg + p)).
pose proof (byte_at_range memc (fimg + p)) as Rbc. pose proof (byte_at_range memc (bimg + p)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [bc; bb; fimg + p; bimg + p; W; g; cfp] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HA : forall j v, nth_error [bc; bb; fimg + p; bimg + p; W; g; cfp] j = Some v -> ew E (32 + j) = Z_to_bv 64 v)
by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HE32 : ew E 32 = Z_to_bv 64 bc) by (apply (HA 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 bb) by (apply (HA 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 (fimg + p)) by (apply (HA 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 (bimg + p)) by (apply (HA 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 W) by (apply (HA 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 g) by (apply (HA 5%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 cfp) by (apply (HA 6%nat); reflexivity).
assert (UR : forall (r : reg) (k : nat) v, Z.of_nat k = bv_unsigned r -> getr regs r = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff k 0) = v)
by (intros r k v Hk Hg Hv; apply U_atom; [rewrite (HE k r Hk); exact Hg | exact Hv]).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HU34 : bv_unsigned (ew E 34) = fimg + p) by (rewrite HE34; apply unsigned_lit_small; clear - Hp Hfimg0 Hfimg1 Hac; lia).
assert (HU35 : bv_unsigned (ew E 35) = bimg + p) by (rewrite HE35; apply unsigned_lit_small; clear - Hp Hbimg0 Hbimg1 Hac; lia).
assert (RfW : 4096 <= fimg + i * W /\ fimg + i * W + W <= alloc_ceiling) by (clear - HiW Hfimg0 Hfimg1; lia).
assert (RbW : 4096 <= bimg + i * W /\ bimg + i * W + W <= alloc_ceiling) by (clear - HiW Hbimg0 Hbimg1; lia).
assert (HFA : facts_ok E (mkFacts s1i_atoms s1i_conds s1i_alias)).
{ split; [| split].
- unfold s1i_atoms. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU34, HU35, HE32, HE33, HE36, (HE 8%nat 8%bv eq_refl), (HE 9%nat 9%bv eq_refl), (HE 21%nat 21%bv eq_refl), (HE 23%nat 23%bv eq_refl), G8, G9, G21, G23.
clear - Hsp0 Hsp1 Hsp16 Hp Hn HW Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac.
rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia.
- unfold s1i_conds. cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite !branch_geu_U.
rewrite (U_atom E 34 (fimg + p) HE34), (U_atom E 35 (bimg + p) HE35), (UR 26%bv 26%nat (fimg + i * W) eq_refl G26), (UR 19%bv 19%nat (bimg + i * W) eq_refl G19)
by (clear - Hp HiW HW Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac; lia).
split; [| split; [| exact I]]; apply Bool.negb_true_iff; apply Z.ltb_ge; clear - Hpdef Hcge; lia.
- unfold s1i_alias. cbn [f_alias alias_ok].
assert (A1 : forall (ra : reg) (ka : nat) base, Z.of_nat ka = bv_unsigned ra -> getr regs ra = Z_to_bv 64 (base + i * W) -> 0 <= base -> base + p < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff ka 0) (SOff 22 0)) = Z_to_bv 64 (base + p)).
{ intros ra ka base Hk Hg Hb Hbp. apply denot_of_U'. rewrite (U_add_small E _ _ (base + i * W) c).
- rewrite Hpdef. lia.
- exact (UR ra ka _ Hk Hg ltac:(clear - Hb Hbp Hpdef Hcge HiW; lia)).
- exact (UR 22%bv 22%nat c eq_refl G22 ltac:(clear - Hbp Hb Hpdef Hcge HiW; lia)).
- clear - Hb HiW; lia.
- exact Hcge.
- clear - Hb Hbp Hpdef; lia. }
assert (B34 : sv_denot E (SOff 34 0) = Z_to_bv 64 (fimg + p)) by (cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity).
assert (B35 : sv_denot E (SOff 35 0) = Z_to_bv 64 (bimg + p)) by (cbn [sv_denot]; rewrite Z.add_0_r, HE35, Z_to_bv_bv_unsigned; reflexivity).
split; [rewrite B34; apply (A1 25%bv 25%nat fimg eq_refl G25); clear - Hfimg0 Hfimg1 Hp Hac; lia|].
split; [rewrite B34; apply (A1 24%bv 24%nat fimg eq_refl G24); clear - Hfimg0 Hfimg1 Hp Hac; lia|].
split; [rewrite B35; apply (A1 27%bv 27%nat bimg eq_refl G27); clear - Hbimg0 Hbimg1 Hp Hac; lia|].
split; [rewrite B35; apply (A1 20%bv 20%nat bimg eq_refl G20); clear - Hbimg0 Hbimg1 Hp Hac; lia|].
split; [| exact I].
rewrite (denot_of_U' E (SAlu ALU_XOR (SOff 23 0) (SLit 0)) 1); [reflexivity|].
rewrite U_SAlu, (UR 23%bv 23%nat 1 eq_refl G23), U_lit by lia. reflexivity. }
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 88 128 88 88 s1i_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; lia|].
unfold s1i_stk. constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ 1); [reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W88].
- eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE36, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - HW; lia | cbn; lia | apply val_mem_word_mem; exact WWm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE37, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - G0 G1 Hac; unfold CGIF_SIZE in G1; lia | cbn; lia | apply val_mem_word_mem; exact WGm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ cfp); [cbn [sv_denot]; rewrite Z.add_0_r, HE38, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - C0 C1 Hac; lia | cbn; lia | apply val_mem_word_mem; exact WCm]. }
assert (HR1 : region_ok ubs0segs E memc (YP09.mkRegion (Some 34%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU34.
split; [lia|]. split; [clear - Hp Hfimg1 Hac Hn; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(clear - Hp Hn; lia))). }
assert (HR2 : region_ok ubs0segs E memc (YP09.mkRegion (Some 35%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU35.
split; [lia|]. split; [clear - Hp Hbimg1 Hac Hn; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(clear - Hp Hn; lia))). }
assert (HPD : pairwise_disjoint E (ss_mem ss_s1i)).
{ cbn [ss_mem ss_s1i pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU34, HU35.
repeat split; try exact I; clear - Dfb Hp Hn Hsp0 Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac; lia. }
assert (HS : st_ok ubs0segs E ss_s1i (mkst regs (Z_to_bv 64 FL_S1I) memc (seg_rom ubs0segs))).
{ unfold ss_s1i. subst E. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | exact HFA].
constructor; [exact HR0 | constructor; [exact HR1 | constructor; [exact HR2 | constructor]]]. }
clear HR0 HR1 HR2 HPD HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S1I) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cmpPixel.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha0. rewrite HE37 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite HE38 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 18%nat 18%bv eq_refl), G18 in Ha2.
jreg HS (13%bv:reg) as Ha3. rewrite HE32 in Ha3. jreg HS (14%bv:reg) as Ha4. rewrite HE33 in Ha4.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (Hbq : forall a, byte_at (ms_mem ms) a = byte_at memc a) by (intros a; unfold byte_at; rewrite (mbyte_of_eq _ _ _ _ K1); reflexivity).
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc ss_s1i].
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
(eapply (region_kept_out ubs0segs _ _ _ _ 0 0); [intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; rewrite ?HU2, ?HU34, ?HU35; clear - Hsp0 Hp Hfimg0 Hbimg0 Hac; lia
| cbn [r_base r_hi base_val]; rewrite ?HU2, ?HU34, ?HU35; clear - Hsp1 Hp Hn Hfimg1 Hbimg1 Hac; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_S1R) mem2 (seg_rom ubs0segs))) in HJ2.
set (E2 := havoc E 39 (map (getr regs2) CMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (EXIT : forall ss ms' pc', st_ok ubs0segs E2 ss ms' -> ss_pc ss = pc' -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) S1I_KEPT = true ->
((pc' = FL_S1F /\ exists c0, 0 <= c0 < W /\ CMP (i * W + c0) <> 0) \/ (pc' = FL_S1X /\ forall c2, 0 <= c2 < W -> CMP (i * W + c2) = 0)) ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall x, ms_mem ms' x = mem2 x) ->
s1i_postV STK sp0 FP L A mem md Lc Ac mdc regs memc i (mkCfg ms' mdc)).
{ intros ss ms' pc' HS' Hpc Hrv Hkl Hpc' HJ' K'. exists (ms_regs ms'), (ms_mem ms'), pc'.
split; [rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact (KD_eq _ _ _ _ K2 K')|].
split; [intros x; rewrite (K' x), (Hmem2 x); apply K1|]. split; [exact Hpc'|].
intros rr Hrr. subst E E2. exact (regs_kept_of_st_ok ubs0segs _ ss ms' regs _ S1I_KEPT HS' EA1 Hkl rr Hrr). }
jbranch ubs0tbl HS.
-
assert (Hne : CMP p <> 0).
{ intros Hz. rewrite branch_ne_U, U_lit, (U_atom E2 41 0) in Hc; [discriminate Hc | | clear; lia | clear; lia].
subst E2. change 41%nat with (39 + 2)%nat. rewrite (ew_havoc_new E 39 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) by (cbn; lia).
cbn [nth map CMP_CLOB]. rewrite Hres. unfold CMP in Hz. rewrite Hz. reflexivity. }
clear Hc. jrun_to LAWS ubs0tbl_ok HS HJ2 FL_S1F.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_S1F HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [| exact HJ2 |].
+ left. split; [reflexivity|]. exists c. split; [clear - Hcge Hcn Hn; lia | rewrite <- Hpdef; exact Hne].
+ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity.
-
assert (Hz : CMP p = 0).
{ destruct (Z.eq_dec (CMP p) 0) as [Hz|Hnz]; [exact Hz | exfalso].
rewrite branch_ne_U, U_lit, U_SOff in Hc by (clear; lia). subst E2. change 41%nat with (39 + 2)%nat in Hc.
rewrite (ew_havoc_new E 39 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) in Hc by (cbn; lia). cbn [nth map CMP_CLOB] in Hc. rewrite Hres, Z_to_bv_unsigned in Hc.
pose proof (cmpPixel_fn_rangeV cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef (byte_at mem0 (fimg + p)) (byte_at mem0 (bimg + p))) as Rr.
pose proof (wrap64_nzV _ Rr Hnz) as X. destruct (Z.eqb_spec (zcanon (bv_wrap 64 (CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef p) + 0)) 0) as [Hq|Hq]; [exact (X Hq) | discriminate Hc]. }
assert (HEQ1 : forall c2, 0 <= c2 < c + 1 -> CMP (i * W + c2) = 0).
{ intros c2 Hc2. destruct (Z.eq_dec c2 c) as [-> | Hne2]; [rewrite <- Hpdef; exact Hz | apply HEQ; clear - Hc2 Hne2; lia]. }
clear Hc. jrun LAWS ubs0tbl_ok HS HJ2.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K3 : forall x, m2 x = mem2 x) by (intros x; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x); reflexivity) end.
clear HF HG.
assert (U36 : U E2 (SOff 36 0) = W) by (apply U_atom; [subst E2; ew_havocA; exact HE36 | clear - HW; lia]).
assert (U22 : U E2 (SOff 22 1) = c + 1) by (apply U_atom_off; [subst E2; ew_havocA; rewrite (HE 22%nat 22%bv eq_refl); exact G22 | clear - Hcge Hcn HW; lia | clear - Hcge Hcn HW; lia]).
jbranch ubs0tbl HS.
+
rewrite branch_ne_U, U36, U22 in Hc.
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.eqb_spec W (c + 1)); [discriminate Hc | clear - Hcn n0; lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 FL_S1I.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K4 : forall x, m2 x = mem2 x) by (intros x; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x); apply K3);
assert (K5 : forall x, m2 x = memc x) by (intros x; rewrite (K4 x), (Hmem2 x); apply K1) end.
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%bv HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (c + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ i HJ2 (KD_eq _ _ _ _ K2 K4) Hfi Hbi Hi ltac:(clear - Hcge; lia) ltac:(clear - Hcn; lia) Hn1
(word_mem_eq _ _ _ _ K5 W88)).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- rewrite (HKR 24%bv ltac:(cbv; auto 20)). exact G24.
- rewrite (HKR 25%bv ltac:(cbv; auto 20)). exact G25.
- rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact G26.
- rewrite (HKR 27%bv ltac:(cbv; auto 20)). exact G27.
- rewrite (HKR 20%bv ltac:(cbv; auto 20)). exact G20.
- rewrite (HKR 19%bv ltac:(cbv; auto 20)). exact G19.
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 22%nat 22%bv eq_refl), G22, unsigned_lit_small by (clear - Hcge Hcn HW; lia); reflexivity).
- exact HEQ1. }
cbv beta. intros c' (regs' & mem' & pc' & -> & HJ' & K' & Keq' & Hpc' & HK'). exists regs', mem', pc'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [intros x; rewrite (Keq' x); apply K5|]. split; [exact Hpc'|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr). clear - Hrr. cbv in Hrr. cbv. intuition.
+
assert (Hn0 : n = 0%nat).
{ rewrite branch_ne_U, U36, U22 in Hc. destruct (Z.eqb_spec W (c + 1)) as [Hq|Hq]; [clear - Hq Hcn; lia | discriminate Hc]. }
clear Hc. jrun_to LAWS ubs0tbl_ok HS HJ2 FL_S1X.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_S1X HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [right; split; [reflexivity | intros c2 Hc2; apply HEQ1; clear - Hc2 Hcn Hn0; lia] | exact HJ2 |].
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3.
Qed.
Definition s1o_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (c' : config) : Prop :=
exists regs' mem' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KD mem0 spv mem' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 96 <= a < spv + 104) -> mbyte ubs0segs mem' a = mbyte ubs0segs memc a) /\
((pc' = FL_S2 /\ exists top c, 0 <= top < H /\ 0 <= c < W /\ CMP (top * W + c) <> 0 /\
getr regs' 12 = Z_to_bv 64 top /\ getr regs' 13 = Z_to_bv 64 top /\ getr regs' 26 = Z_to_bv 64 H /\ word_mem ubs0segs mem' (spv + 96) top /\
(forall p, 0 <= p < top * W -> CMP p = 0))
\/ (pc' = FL_IDENT /\ getr regs' 10 = Z_to_bv 64 W /\ (forall p, 0 <= p < N -> CMP p = 0))) /\
(forall r : reg, In r S1O_KEPT -> getr regs' r = getr regs r).
Lemma mk_s1o : forall (head : bool) pc (regs : bvmap 5 word) m i,
KD mem0 spv m -> (forall a, spv + 96 <= a < spv + 104 -> writable_at ubs0segs m a) ->
getr regs 2 = Z_to_bv 64 spv -> word_mem ubs0segs m (spv + 88) 1 -> 0 <= i < H ->
(head = false -> word_mem ubs0segs m (spv + 96) i) ->
(head = true -> pc = FL_S1O /\ getr regs 10 = Z_to_bv 64 W /\ getr regs 11 = Z_to_bv 64 i /\ getr regs 23 = Z_to_bv 64 1 /\
getr regs 8 = Z_to_bv 64 bimg /\ getr regs 9 = Z_to_bv 64 fimg /\ getr regs 25 = Z_to_bv 64 (fimg + i * W) /\ getr regs 27 = Z_to_bv 64 (bimg + i * W)) ->
st_ok ubs0segs (Ereg regs (map (Z_to_bv 64) [H; i; W] ++ [])) (if head then ss_s1o else ss_s1e pc) (mkst regs (Z_to_bv 64 pc) m (seg_rom ubs0segs)).
Proof using HC.
intros head pc regs m i K Hwr G2 W88 Hi Hexit Hhead. dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC m K)
as (_ & _ & _ & _ & _ & WHm & WWm & _ & _).
assert (HiW : 0 <= i * W /\ i * W + W <= N) by (rewrite HN; clear - Hi HW; nia).
set (E := Ereg regs (map (Z_to_bv 64) [H; i; W] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 H) by (subst E; apply (Ereg_vals regs [H; i; W] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 i) by (subst E; apply (Ereg_vals regs [H; i; W] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 W) by (subst E; apply (Ereg_vals regs [H; i; W] [] 2%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HFA : atoms_ok E s1o_facts).
{ unfold s1o_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE32, HE33, HE34.
rewrite !unsigned_lit_small by (clear - HH HW Hi; lia). change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hsp0 Hsp1 Hsp16 HW HH Hi Hac. repeat split; lia. }
assert (C88 : chunk_ok ubs0segs E m spv (mkChunk 88 (CVal 8 (SLit 1))))
by (eapply (chunk_ok_val _ _ _ _ _ _ _ 1); [reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W88]).
assert (C104 : chunk_ok ubs0segs E m spv (mkChunk 104 (CVal 8 (SOff 34 0))))
by (eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - HW; lia | cbn; lia | apply val_mem_word_mem; exact WWm]).
assert (RG0 : forall cs, Forall (chunk_ok ubs0segs E m spv) cs -> Forall (region_ok ubs0segs E m) (s1o_mem cs)).
{ intros cs Hcs. unfold s1o_mem. constructor; [|constructor]. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply Hwr; lia | exact Hcs]. }
destruct head.
- destruct (Hhead eq_refl) as (-> & G10 & G11 & G23 & G8 & G9 & G25 & G27).
assert (UR : forall (r : reg) (k : nat) v, Z.of_nat k = bv_unsigned r -> getr regs r = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff k 0) = v)
by (intros r k v Hk Hg Hv; apply U_atom; [rewrite (HE k r Hk); exact Hg | exact Hv]).
assert (U9 : U E (SOff 9 0) = fimg) by (apply (UR 9%bv); [reflexivity | exact G9 | clear - HiW HW Hfimg0 Hfimg1 Hac; lia]).
assert (U8 : U E (SOff 8 0) = bimg) by (apply (UR 8%bv); [reflexivity | exact G8 | clear - HiW HW Hbimg0 Hbimg1 Hac; lia]).
assert (U25 : U E (SOff 25 0) = fimg + i * W) by (apply (UR 25%bv); [reflexivity | exact G25 | clear - HiW HW Hfimg0 Hfimg1 Hac; lia]).
assert (U27 : U E (SOff 27 0) = bimg + i * W) by (apply (UR 27%bv); [reflexivity | exact G27 | clear - HiW HW Hbimg0 Hbimg1 Hac; lia]).
assert (U23 : U E (SOff 23 0) = 1) by (apply (UR 23%bv); [reflexivity | exact G23 | lia]).
assert (UM : U E (SMd M_MUL (SOff 11 0) (SOff 34 0)) = i * W).
{ apply (U_mul_small' E _ _ i W); [apply (UR 11%bv); [reflexivity | exact G11 | clear - Hi HH; lia] | apply U_atom; [exact HE34 | clear - HW; lia] | lia | lia | clear - HiW HW HNle; lia]. }
assert (A1 : forall (b : nat) base, U E (SOff b 0) = base -> 0 <= base -> base + i * W < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SOff 34 0)) (SOff b 0)) = Z_to_bv 64 (base + i * W)).
{ intros b base Hb Hb0 Hb1. apply denot_of_U'. rewrite (U_add_small E _ _ (i * W) base UM Hb ltac:(lia) Hb0 ltac:(lia)). lia. }
unfold ss_s1o. subst E. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity
| apply RG0; unfold s1o_hstk; constructor; [exact C88 | constructor; [exact C104 | constructor]] | cbn [pairwise_disjoint all_disjoint]; split; exact I |].
split; [apply atoms_ok_app; [exact HFA|] | split].
+ unfold s1o_hfacts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HE 8%nat 8%bv eq_refl), (HE 9%nat 9%bv eq_refl), (HE 10%nat 10%bv eq_refl), (HE 25%nat 25%bv eq_refl), (HE 27%nat 27%bv eq_refl), (HE 23%nat 23%bv eq_refl),
G8, G9, G10, G25, G27, G23.
rewrite !unsigned_lit_small by (clear - HiW HW Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac; lia).
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. clear - HiW HW Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac. repeat split; lia.
+ cbn [f_conds conds_ok]. split; [| exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, U25, U9.
apply Bool.negb_true_iff; apply Z.ltb_ge. clear - HiW. lia.
+ unfold s1o_alias. cbn [f_alias alias_ok].
split; [rewrite (A1 9%nat fimg U9 ltac:(lia) ltac:(clear - HiW HW Hfimg1 Hac; lia)); symmetry; apply denot_of_U'; exact U25|].
split; [rewrite (A1 8%nat bimg U8 ltac:(lia) ltac:(clear - HiW HW Hbimg1 Hac; lia)); symmetry; apply denot_of_U'; exact U27|].
split; [rewrite (denot_of_U' _ (SLit (-1)) (2 ^ 64 - 1)) by (rewrite U_SLit; reflexivity);
apply denot_of_U'; rewrite U_SAlu, U_SAlu, U27, U8, U_SLit; cbn [zalu_raw];
destruct (Z.ltb_spec (bimg + i * W) bimg) as [Hlt|Hge]; [clear - HiW Hlt; lia | reflexivity]|].
split; [| exact I].
rewrite (denot_of_U' _ (SAlu ALU_XOR (SOff 23 0) (SLit 0)) 1); [reflexivity|]. rewrite U_SAlu, U23, U_lit by lia. reflexivity.
- pose proof (Hexit eq_refl) as W96.
assert (C80 : chunk_ok ubs0segs E m spv (mkChunk 80 (CVal 8 (SOff 32 0))))
by (eapply (chunk_ok_val _ _ _ _ _ _ _ H); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - HH; lia | cbn; lia | apply val_mem_word_mem; exact WHm]).
assert (C96 : chunk_ok ubs0segs E m spv (mkChunk 96 (CVal 8 (SOff 33 0))))
by (eapply (chunk_ok_val _ _ _ _ _ _ _ i); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Hi HH; lia | cbn; lia | apply val_mem_word_mem; exact W96]).
unfold ss_s1e. subst E. apply entry_st_ok; [vm_compute; reflexivity
| apply RG0; unfold s1o_estk; constructor; [exact C80 | constructor; [exact C88 | constructor; [exact C96 | constructor; [exact C104 | constructor]]]]
| cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA].
Qed.
Lemma fl_s1oV : forall (n : nat) (i : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc,
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
spv = sp0 - 272 -> 272 <= STK ->
0 <= i -> i + Z.of_nat n = H -> (1 <= n)%nat ->
word_mem ubs0segs memc (spv + 88) 1 ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 bimg -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 24 = Z_to_bv 64 (fimg + i * W) -> getr regs 25 = Z_to_bv 64 (fimg + i * W) ->
getr regs 27 = Z_to_bv 64 (bimg + i * W) -> getr regs 20 = Z_to_bv 64 (bimg + i * W) ->
getr regs 23 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 i -> getr regs 10 = Z_to_bv 64 W ->
(forall p, 0 <= p < i * W -> CMP p = 0) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 FL_S1O) memc (seg_rom ubs0segs)) mdc) (s1o_postV STK sp0 FP L A mem md Lc Ac mdc regs memc).
Proof using HC IMG.
intros n. induction n as [|n IH]; intros i STK sp0 FP L A mem md Lc Ac mdc regs memc HJ K0 Hfi Hbi Hspv HSTK Hi0 Hin Hn W88
G2 G8 G9 G18 G24 G25 G27 G20 G23 G11 G10 HEQ; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HiW : 0 <= i * W /\ i * W + W <= N) by (rewrite HN; clear - Hi0 Hin Hn HW; nia).
assert (HiH : 0 <= i < H) by (clear - Hi0 Hin Hn; lia).
assert (WRS : forall m', journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac m' mdc -> forall a, spv + 96 <= a < spv + 104 -> writable_at ubs0segs m' a).
{ intros m' HJm a Ha. pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _). apply Hstw. clear - Ha Hspv HSTK. lia. }
assert (WRT : forall E0 cs, bv_unsigned (ew E0 2) = spv ->
wr_ok E0 [YP09.mkRegion (Some 2%nat) 80 112 96 104 cs] STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 cs H2. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia | apply wr_ok_nil]. }
assert (KFR : forall E0 cs (m m' : word -> option byte), bv_unsigned (ew E0 2) = spv ->
frame_of E0 [YP09.mkRegion (Some 2%nat) 80 112 96 104 cs] m m' ->
forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 96 <= a < spv + 104) -> mbyte ubs0segs m' a = mbyte ubs0segs m a).
{ intros E0 cs m m' H2 HFx a Ha Hna. apply (mbyte_of_frame _ _ _ _ a HFx Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | []]; cbn [r_base r_wlo r_whi base_val]; rewrite H2; clear - Hna; lia. }
assert (KDF : forall E0 cs (m m' : word -> option byte), bv_unsigned (ew E0 2) = spv -> KD mem0 spv m ->
frame_of E0 [YP09.mkRegion (Some 2%nat) 80 112 96 104 cs] m m' -> KD mem0 spv m').
{ intros E0 cs m m' H2 Km HFx. apply (KD_frame _ _ _ _ Km). intros a Ha Hna1 Hna2 Hna3 Hna4. apply (KFR E0 cs m m' H2 HFx a Ha). clear - Hna4. lia. }
pose proof (mk_s1o true FL_S1O regs memc i K0 (WRS _ HJ) G2 W88 HiH ltac:(intros X; discriminate X)
ltac:(intros _; split; [reflexivity | repeat (split; [assumption|]); assumption])) as HS. cbn [negb] in HS.
set (E := Ereg regs (map (Z_to_bv 64) [H; i; W] ++ [])) in HS.
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S1O) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ FL_S1I. { apply WRT. exact HU2. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2 K0 HF) as K1. pose proof (KFR _ _ _ _ HU2 HF) as F1. clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs0segs E ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hv; rewrite (st_ok_reg ubs0segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hv);
assert (RGL : forall (r : reg) z, sr_get (ss_regs ssx) r = SLit z -> getr (ms_regs msx) r = Z_to_bv 64 z)
by (intros r z Hr; rewrite (st_ok_reg ubs0segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (W96 : word_mem ubs0segs (ms_mem ms) (spv + 96) i).
{ apply (chunk_word E _ _ 96 (SOff 11 0) i (proj1 (Forall_forall _ _) Hcs (mkChunk 96 (CVal 8 (SOff 11 0))) ltac:(cbn [In]; tauto)));
[cbn [sv_denot]; rewrite Z.add_0_r, (HE 11%nat 11%bv eq_refl), G11, Z_to_bv_bv_unsigned; reflexivity | clear - HiH HH; lia]. }
assert (W88a : word_mem ubs0segs (ms_mem ms) (spv + 88) 1).
{ apply (chunk_word E _ _ 88 (SLit 1) 1 (proj1 (Forall_forall _ _) Hcs (mkChunk 88 (CVal 8 (SLit 1))) ltac:(cbn [In]; tauto))); [reflexivity | lia]. }
clear Hcs.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_s1iV (Z.to_nat W) 0 STK sp0 FP L A mem md Lc Ac mdc _ _ i HJ K1 Hfi Hbi HiH ltac:(clear; lia) ltac:(clear - HW; lia) ltac:(clear - HW; lia) W88a).
- apply (RG 2%bv 2%nat _ eq_refl). rewrite (HE 2%nat 2%bv eq_refl). exact G2.
- apply (RG 8%bv 8%nat _ eq_refl). rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- apply (RG 9%bv 9%nat _ eq_refl). rewrite (HE 9%nat 9%bv eq_refl). exact G9.
- apply (RG 18%bv 18%nat _ eq_refl). rewrite (HE 18%nat 18%bv eq_refl). exact G18.
- apply (RG 24%bv 24%nat _ eq_refl). rewrite (HE 24%nat 24%bv eq_refl). exact G24.
- apply (RG 25%bv 25%nat _ eq_refl). rewrite (HE 25%nat 25%bv eq_refl). exact G25.
- apply (RG 26%bv 25%nat _ eq_refl). rewrite (HE 25%nat 25%bv eq_refl). exact G25.
- apply (RG 27%bv 27%nat _ eq_refl). rewrite (HE 27%nat 27%bv eq_refl). exact G27.
- apply (RG 20%bv 20%nat _ eq_refl). rewrite (HE 20%nat 20%bv eq_refl). exact G20.
- apply (RG 19%bv 27%nat _ eq_refl). rewrite (HE 27%nat 27%bv eq_refl). exact G27.
- apply (RGL 21%bv 1 eq_refl).
- apply (RG 23%bv 23%nat _ eq_refl). rewrite (HE 23%nat 23%bv eq_refl). exact G23.
- apply (RGL 22%bv 0 eq_refl).
- intros c2 Hc2; exfalso; clear - Hc2; lia. }
cbv beta. intros c' (regs' & mem' & pc' & -> & HJ' & K' & Keq' & Hpc' & HK'').
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ [2; 3; 4; 8; 9; 18; 20; 23; 24; 25; 27]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR0 end.
assert (HK' : forall r : reg, In r [2; 3; 4; 8; 9; 18; 20; 23; 24; 25; 27]%bv -> getr regs' r = getr regs r).
{ intros rr Hrr. rewrite (HK'' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). apply (HKR0 rr Hrr). }
assert (W88' : word_mem ubs0segs mem' (spv + 88) 1) by (apply (word_mem_eq _ _ _ _ Keq' W88a)).
assert (W96' : word_mem ubs0segs mem' (spv + 96) i) by (apply (word_mem_eq _ _ _ _ Keq' W96)).
assert (F' : forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 96 <= a < spv + 104) -> mbyte ubs0segs mem' a = mbyte ubs0segs memc a).
{ intros a Ha Hna. rewrite (mbyte_of_eq _ _ _ _ Keq'). exact (F1 a Ha Hna). }
clear HJ HS RG RGL HK'' HKR0 K1 F1 W88a W96 Keq'.
assert (G2' : getr regs' 2 = Z_to_bv 64 spv) by (rewrite (HK' 2%bv ltac:(cbv; auto 50)); exact G2).
set (E' := Ereg regs' (map (Z_to_bv 64) [H; i; W] ++ [])).
assert (HE' : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E' m = getr regs' rr) by (intros; subst E'; apply ew_Ereg_nat; assumption).
assert (HE32' : ew E' 32 = Z_to_bv 64 H) by (subst E'; apply (Ereg_vals regs' [H; i; W] [] 0%nat); reflexivity).
assert (HE33' : ew E' 33 = Z_to_bv 64 i) by (subst E'; apply (Ereg_vals regs' [H; i; W] [] 1%nat); reflexivity).
assert (HE34' : ew E' 34 = Z_to_bv 64 W) by (subst E'; apply (Ereg_vals regs' [H; i; W] [] 2%nat); reflexivity).
assert (HU2' : bv_unsigned (ew E' 2) = spv) by (rewrite (HE' 2%nat 2%bv eq_refl), G2'; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (EXIT : forall ss ms' pc'', st_ok ubs0segs E' ss ms' -> ss_pc ss = pc'' -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) S1O_KEPT = true ->
((pc'' = FL_S2 /\ exists top c, 0 <= top < H /\ 0 <= c < W /\ CMP (top * W + c) <> 0 /\
getr (ms_regs ms') 12 = Z_to_bv 64 top /\ getr (ms_regs ms') 13 = Z_to_bv 64 top /\ getr (ms_regs ms') 26 = Z_to_bv 64 H /\
word_mem ubs0segs (ms_mem ms') (spv + 96) top /\ (forall p, 0 <= p < top * W -> CMP p = 0))
\/ (pc'' = FL_IDENT /\ getr (ms_regs ms') 10 = Z_to_bv 64 W /\ (forall p, 0 <= p < N -> CMP p = 0))) ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> KD mem0 spv (ms_mem ms') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 96 <= a < spv + 104) -> mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
s1o_postV STK sp0 FP L A mem md Lc Ac mdc regs memc (mkCfg ms' mdc)).
{ intros ss ms' pc'' HS' Hpc Hrv Hkl Hpc'' HJ'' K'' F''. exists (ms_regs ms'), (ms_mem ms'), pc''.
split; [rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ''|]. split; [exact K''|]. split; [exact F''|]. split; [exact Hpc''|].
intros rr Hrr. rewrite <- (HK' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). subst E'.
exact (regs_kept_of_st_ok ubs0segs _ ss ms' regs' _ S1O_KEPT HS' (env_agree_refl _ _) Hkl rr Hrr). }
assert (CWs : forall ss ms' off e val, st_ok ubs0segs E' ss ms' ->
(exists rg0, nth_error (ss_mem ss) 0 = Some rg0 /\ r_base rg0 = Some 2%nat /\ In (mkChunk off (CVal 8 e)) (r_chunks rg0)) ->
sv_denot E' e = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> word_mem ubs0segs (ms_mem ms') (spv + off) val).
{ intros ss ms' off e val HS' (rg0 & Hrg0 & Hb0 & Hinc) He Hval.
pose proof (st_region_chunks ubs0segs E' ss ms' 0 rg0 2%nat spv HS' Hrg0 Hb0 HU2') as Hcs0.
exact (chunk_word E' _ _ off _ _ (proj1 (Forall_forall _ _) Hcs0 _ Hinc) He Hval). }
destruct Hpc' as [[-> (c0 & Hc0 & Hne)] | [-> HROW]].
-
pose proof (mk_s1o false FL_S1F regs' mem' i K' (WRS _ HJ') G2' W88' HiH ltac:(intros _; exact W96') ltac:(intros X; discriminate X)) as HS.
cbn [negb] in HS. fold E' in HS.
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 FL_S1F) mem' (seg_rom ubs0segs))) in HJ'.
jrun LAWS ubs0tbl_ok HS HJ'. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K' HF) as K2. pose proof (KFR _ _ _ _ HU2' HF) as F2. clear HF HG.
assert (U32 : U E' (SOff 32 0) = H) by (apply U_atom; [exact HE32' | clear - HH; lia]).
assert (U33 : U E' (SOff 33 0) = i) by (apply U_atom; [exact HE33' | clear - HiH HH; lia]).
jbranch ubs0tbl HS.
+ clear Hc. jrun_to LAWS ubs0tbl_ok HS HJ' FL_S2. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K2 HF) as K3. pose proof (KFR _ _ _ _ HU2' HF) as F3. clear HF HG.
apply SR_ret. apply (EXIT _ _ FL_S2 HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [| exact HJ' | exact K3 |].
* left. split; [reflexivity|]. exists i, c0. split; [exact HiH|]. split; [exact Hc0|]. split; [exact Hne|].
split; [reg_nowF HS ltac:(rewrite HE33', Z_to_bv_bv_unsigned; reflexivity)|].
split; [first [reg_nowF HS ltac:(rewrite HE33', Z_to_bv_bv_unsigned; reflexivity)
| lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 13%bv HS) end; eval_sr_get;
apply denot_of_U'; rewrite U_zext16_shifts, U33; apply Z.mod_small; clear - HiH HH; lia]|].
split; [reg_nowF HS ltac:(rewrite HE32', Z_to_bv_bv_unsigned; reflexivity)|].
split; [apply (CWs _ _ 96 (SOff 33 0) i HS); [eexists; split; [reflexivity|]; split; [reflexivity|]; cbn [r_chunks In]; tauto
| cbn [sv_denot]; rewrite Z.add_0_r, HE33', Z_to_bv_bv_unsigned; reflexivity | clear - HiH HH; lia] | exact HEQ].
* intros a Ha Hna. rewrite (F3 a Ha Hna), (F2 a Ha Hna). exact (F' a Ha Hna).
+ exfalso. first [rewrite branch_ne_U, U32, U33 in Hc | rewrite branch_ne_U, U32, U_zext16_shifts, U33, Z.mod_small in Hc by (clear - HiH HH; lia)].
destruct (Z.eqb_spec H i); [clear - HiH e; lia | discriminate Hc].
-
assert (HEQ1 : forall p, 0 <= p < (i + 1) * W -> CMP p = 0).
{ intros p Hp. destruct (Z.lt_ge_cases p (i * W)) as [Hlt|Hge]; [apply HEQ; clear - Hp Hlt; lia|]. replace p with (i * W + (p - i * W)) by (clear; lia). apply HROW. clear - Hp Hge. lia. }
pose proof (mk_s1o false FL_S1X regs' mem' i K' (WRS _ HJ') G2' W88' HiH ltac:(intros _; exact W96') ltac:(intros X; discriminate X)) as HS.
cbn [negb] in HS. fold E' in HS.
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 FL_S1X) mem' (seg_rom ubs0segs))) in HJ'.
jrun LAWS ubs0tbl_ok HS HJ'. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K' HF) as K2. pose proof (KFR _ _ _ _ HU2' HF) as F2. clear HF HG.
assert (U32 : U E' (SOff 32 0) = H) by (apply U_atom; [exact HE32' | clear - HH; lia]).
assert (U33 : U E' (SOff 33 1) = i + 1) by (apply U_atom_off; [exact HE33' | clear - HiH HH; lia | clear - HiH HH; lia]).
jbranch ubs0tbl HS.
+
rewrite branch_ne_U, U33, U32 in Hc.
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.eqb_spec (i + 1) H); [discriminate Hc | clear - Hin Hn n0; lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ' FL_S1O. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K2 HF) as K3. pose proof (KFR _ _ _ _ HU2' HF) as F3. clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs0segs Ef ssf msf regs' _ [2; 3; 4; 8; 9; 18; 23]%bv HS ltac:(subst E'; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR end.
lazymatch type of HS with st_ok _ _ _ ?msf =>
assert (W88n : word_mem ubs0segs (ms_mem msf) (spv + 88) 1)
by (apply (CWs _ _ 88 (SLit 1) 1 HS); [eexists; split; [reflexivity|]; split; [reflexivity|]; cbn [r_chunks In]; tauto | reflexivity | lia]) end.
assert (U24 : U E' (SOff 24 0) = fimg + i * W) by (apply U_atom; [rewrite (HE' 24%nat 24%bv eq_refl), (HK' 24%bv ltac:(cbv; auto 50)); exact G24 | clear - HiW HW Hfimg0 Hfimg1 Hac; lia]).
assert (U25 : U E' (SOff 25 0) = fimg + i * W) by (apply U_atom; [rewrite (HE' 25%nat 25%bv eq_refl), (HK' 25%bv ltac:(cbv; auto 50)); exact G25 | clear - HiW HW Hfimg0 Hfimg1 Hac; lia]).
assert (U27 : U E' (SOff 27 0) = bimg + i * W) by (apply U_atom; [rewrite (HE' 27%nat 27%bv eq_refl), (HK' 27%bv ltac:(cbv; auto 50)); exact G27 | clear - HiW HW Hbimg0 Hbimg1 Hac; lia]).
assert (U20 : U E' (SOff 20 0) = bimg + i * W) by (apply U_atom; [rewrite (HE' 20%nat 20%bv eq_refl), (HK' 20%bv ltac:(cbv; auto 50)); exact G20 | clear - HiW HW Hbimg0 Hbimg1 Hac; lia]).
assert (U34 : U E' (SOff 34 0) = W) by (apply U_atom; [exact HE34' | clear - HW; lia]).
assert (NXT : forall (k : nat) base, U E' (SOff k 0) = base + i * W -> 4096 <= base -> base + N <= alloc_ceiling ->
sv_denot E' (SAlu ALU_ADD (SOff k 0) (SOff 34 0)) = Z_to_bv 64 (base + (i + 1) * W)).
{ intros k base Hk Hb0 Hb1. apply denot_of_U'. rewrite (U_add_small E' _ _ (base + i * W) W Hk U34) by (clear - HiW HW Hb0 Hb1 Hac; lia). nia. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ HJ' K3 Hfi Hbi Hspv HSTK ltac:(clear - Hi0; lia) ltac:(clear - Hin; lia) Hn1 W88n).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2'.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)), (HK' 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)), (HK' 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)), (HK' 18%bv ltac:(cbv; auto 50)). exact G18.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 24%bv HS) end. eval_sr_get.
apply (NXT 24%nat fimg U24 Hfimg0 Hfimg1).
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 25%bv HS) end. eval_sr_get.
apply (NXT 25%nat fimg U25 Hfimg0 Hfimg1).
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 27%bv HS) end. eval_sr_get.
apply (NXT 27%nat bimg U27 Hbimg0 Hbimg1).
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 20%bv HS) end. eval_sr_get.
apply (NXT 20%nat bimg U20 Hbimg0 Hbimg1).
- rewrite (HKR 23%bv ltac:(cbv; auto 20)), (HK' 23%bv ltac:(cbv; auto 50)). exact G23.
- reg_nowF HS ltac:(rewrite HE33', unsigned_lit_small by (clear - HiH HH; lia); reflexivity).
- reg_nowF HS ltac:(rewrite HE34', Z_to_bv_bv_unsigned; reflexivity).
- exact HEQ1. }
cbv beta. intros c' (regs'' & mem'' & pc'' & -> & HJ'' & K'' & F'' & Hpc'' & HK''). exists regs'', mem'', pc''.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact K''|].
split; [intros a Ha Hna; rewrite (F'' a Ha Hna), (F3 a Ha Hna), (F2 a Ha Hna); exact (F' a Ha Hna)|]. split; [exact Hpc''|].
intros rr Hrr. rewrite (HK'' rr Hrr), (HKR rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). apply HK'. clear - Hrr. cbv in Hrr. cbv. intuition.
+
assert (HiH1 : i + 1 = H).
{ rewrite branch_ne_U, U33, U32 in Hc. destruct (Z.eqb_spec (i + 1) H) as [Hq|Hq]; [exact Hq | discriminate Hc]. }
clear Hc. jrun_to LAWS ubs0tbl_ok HS HJ' FL_IDENT. { apply WRT. exact HU2'. }
cbn [ms_mem mkst] in HF.
pose proof (KDF _ _ _ _ HU2' K2 HF) as K3. pose proof (KFR _ _ _ _ HU2' HF) as F3. clear HF HG.
apply SR_ret. apply (EXIT _ _ FL_IDENT HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [| exact HJ' | exact K3 |].
* right. split; [reflexivity|]. split; [reg_nowF HS ltac:(rewrite HE34', Z_to_bv_bv_unsigned; reflexivity)|].
intros p Hp. apply HEQ1. rewrite HiH1. rewrite HN in Hp. clear - Hp. nia.
* intros a Ha Hna. rewrite (F3 a Ha Hna), (F2 a Ha Hna). exact (F' a Ha Hna).
Qed.
End f.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
