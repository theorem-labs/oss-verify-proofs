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
UI1h UI16 UI1z UI1k UI21 UI22 UI23 UI1j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
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
Lemma U_notv : forall E v, U E (SAlu ALU_XOR v (SLit (-1))) = 2 ^ 64 - 1 - U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-1)) with (2 ^ 64 - 1).
pose proof (U_range E v) as Hr. unfold M64 in Hr. rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma word_mem_tr : forall (m m' : word -> option byte) a v,
word_mem ubs2segs m a v -> (forall k, 0 <= k < 8 -> mbyte ubs2segs m' (a + k) = mbyte ubs2segs m (a + k)) -> word_mem ubs2segs m' a v.
Proof. intros m m' a v Hw Hk k Hk8. rewrite Hk by lia. apply Hw. exact Hk8. Qed.
Definition s2i_facts : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (19%nat, mkAF 4096 CEIL_MAX 0); (25%nat, mkAF 4096 CEIL_MAX 0); (27%nat, mkAF 0 65534 0);
(24%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 4097) 0); (20%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 4097) 0);
(23%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 4097) 0); (22%nat, mkAF 0 99999999 0);
(32%nat, mkAF 1 65535 0); (33%nat, mkAF 4096 CEIL_MAX 0); (34%nat, mkAF 4096 CEIL_MAX 0);
(35%nat, mkAF 4096 CEIL_MAX 0); (36%nat, mkAF 4096 CEIL_MAX 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0) ].
Definition s2i_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 19 0) (SOff 27 0), SOff 35 0); (SAlu ALU_ADD (SOff 25 0) (SOff 27 0), SOff 36 0) ].
Definition s2i_stk : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) 104 128 104 104 [mkChunk 104 (CVal 8 (SOff 32 0)); mkChunk 112 (CVal 8 (SOff 33 0)); mkChunk 120 (CVal 8 (SOff 34 0))].
Definition ss_s2i : sstate :=
mkSS FL_S2I sr_atoms
[ s2i_stk ; YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 37 0))] ;
YQ0b.mkRegion (Some 36%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 38 0))] ] None
(mkFacts s2i_facts [] s2i_alias).
Definition S2I_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv.
Definition s2o_hi : list YQ0b.chunk :=
[mkChunk 8 (CVal 8 (SOff 32 0)); mkChunk 40 (CVal 8 (SLit 65535)); mkChunk 80 (CVal 8 (SOff 33 0)); mkChunk 88 (CVal 8 (SOff 32 0));
mkChunk 96 (CVal 8 (SOff 32 0)); mkChunk 104 (CVal 8 (SOff 12 0)); mkChunk 112 (CVal 8 (SOff 34 0)); mkChunk 120 (CVal 8 (SOff 35 0))].
Definition s2o_facts : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (10%nat, mkAF 1 65534 0); (12%nat, mkAF 1 65535 0);
(21%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 4097) 0); (32%nat, mkAF 0 65533 0); (33%nat, mkAF 1 65535 0);
(34%nat, mkAF 4096 CEIL_MAX 0); (35%nat, mkAF 4096 CEIL_MAX 0) ].
Definition ss_s2o : sstate :=
mkSS FL_S2O sr_atoms [ YQ0b.mkRegion (Some 2%nat) 8 128 64 72 s2o_hi ] None
(mkFacts s2o_facts [mkAC BC_GEU (SOff 21 0) (SMd M_MUL (SOff 12 0) (SOff 10 0))] []).
Definition ss_s2x : sstate :=
mkSS FL_S2X sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 8 112 8 8 [mkChunk 8 (CVal 8 (SOff 32 0)); mkChunk 40 (CVal 8 (SLit 65535)); mkChunk 88 (CVal 8 (SOff 32 0)); mkChunk 104 (CVal 8 (SOff 33 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (26%nat, mkAF 1 65534 0); (32%nat, mkAF 0 65533 0); (33%nat, mkAF 1 65535 0) ] [] []).
Definition ss_s2f : sstate :=
mkSS FL_S2F sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 64 112 64 64 [mkChunk 64 (CVal 8 (SOff 34 0)); mkChunk 88 (CVal 8 (SOff 32 0)); mkChunk 104 (CVal 8 (SOff 33 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (34%nat, mkAF 2 65535 0); (32%nat, mkAF 0 65533 0); (33%nat, mkAF 1 65535 0) ] [] []).
Definition s2_regions : smem :=
[ YQ0b.mkRegion (Some 2%nat) 8 16 8 16 [] ; YQ0b.mkRegion (Some 2%nat) 40 48 40 48 [] ; YQ0b.mkRegion (Some 2%nat) 88 96 88 96 [] ;
YQ0b.mkRegion (Some 2%nat) 80 88 80 80 [mkChunk 80 (CVal 8 (SOff 26 0))] ;
YQ0b.mkRegion (Some 2%nat) 96 112 96 96 [mkChunk 96 (CVal 8 (SOff 12 0)); mkChunk 104 (CVal 8 (SOff 32 0))] ].
Definition ss_s2 (z : bool) : sstate :=
mkSS FL_S2 sr_atoms s2_regions None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (12%nat, mkAF 0 65534 0); (26%nat, mkAF 1 65535 0); (32%nat, mkAF 1 65535 0) ]
[ mkAC (if z then BC_GEU else BC_LTU) (SAlu ALU_AND (SOff 12 0) (SLit 65535)) (SAlu ALU_AND (SOff 26 (-1)) (SLit 65535)) ] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Section h.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Let CMP := CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef.
Definition s2i_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (c' : config) : Prop :=
exists regs' mem' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall x, mem' x = memc x) /\
(pc' = FL_S2F \/ pc' = FL_S2X) /\
(forall r : reg, In r S2I_KEPT -> getr regs' r = getr regs r).
Lemma fl_s2i : forall (n : nat) (x : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (i : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= i < H -> 0 <= x -> x + Z.of_nat n = W -> (1 <= n)%nat ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 19 = Z_to_bv 64 (fimg + i * W) -> getr regs 25 = Z_to_bv 64 (bimg + i * W) -> getr regs 27 = Z_to_bv 64 x ->
getr regs 24 = Z_to_bv 64 (2 ^ 64 - 1 - (fimg + i * W)) -> getr regs 20 = Z_to_bv 64 (2 ^ 64 - 1 - (bimg + i * W)) ->
getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - bimg) -> getr regs 22 = Z_to_bv 64 (i * W) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S2I) memc (seg_rom ubs2segs)) mdc) (s2i_post STK sp0 FP L A mem md Lc Ac mdc regs memc).
Proof.
intros n. induction n as [|n IH]; intros x STK sp0 FP L A mem md Lc Ac mdc regs memc i HJ K0 Hfi Hbi Hi Hx Hxn Hn G2 G18 G19 G25 G27 G24 G20 G23 G22; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGS : CGIF_SIZE = 96) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC memc K0) as (_ & _ & _ & _ & _ & _ & WWm & WGm & WCm).
assert (HiW : 0 <= i * W /\ i * W + W <= N) by (rewrite HN; clear - Hi HW; nia).
set (p := i * W + x) in *. assert (Hpdef : p = i * W + x) by reflexivity. clearbody p.
assert (Hp : 0 <= p /\ p + 1 <= N) by (clear - Hpdef HiW Hx Hxn Hn; lia).
set (bc := byte_at memc (fimg + p)). set (bb := byte_at memc (bimg + p)).
pose proof (byte_at_range memc (fimg + p)) as Rbc. pose proof (byte_at_range memc (bimg + p)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [W; g; cfp; fimg + p; bimg + p; bc; bb] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 W) by (subst E; apply (Ereg_vals regs [W; g; cfp; fimg + p; bimg + p; bc; bb] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 g) by (subst E; apply (Ereg_vals regs [W; g; cfp; fimg + p; bimg + p; bc; bb] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 cfp) by (subst E; apply (Ereg_vals regs [W; g; cfp; fimg + p; bimg + p; bc; bb] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 (fimg + p)) by (subst E; apply (Ereg_vals regs [W; g; cfp; fimg + p; bimg + p; bc; bb] [] 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 (bimg + p)) by (subst E; apply (Ereg_vals regs [W; g; cfp; fimg + p; bimg + p; bc; bb] [] 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 bc) by (subst E; apply (Ereg_vals regs [W; g; cfp; fimg + p; bimg + p; bc; bb] [] 5%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 bb) by (subst E; apply (Ereg_vals regs [W; g; cfp; fimg + p; bimg + p; bc; bb] [] 6%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HU35 : bv_unsigned (ew E 35) = fimg + p) by (rewrite HE35; apply unsigned_lit_small; clear - Hp Hfimg0 Hfimg1 Hac; lia).
assert (HU36 : bv_unsigned (ew E 36) = bimg + p) by (rewrite HE36; apply unsigned_lit_small; clear - Hp Hbimg0 Hbimg1 Hac; lia).
assert (HE19 : ew E 19 = Z_to_bv 64 (fimg + i * W)) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE25 : ew E 25 = Z_to_bv 64 (bimg + i * W)) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (HE27 : ew E 27 = Z_to_bv 64 x) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (HFA : atoms_ok E s2i_facts).
{ unfold s2i_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HE19, HE25, HE27, (HE 24%nat 24%bv eq_refl), (HE 20%nat 20%bv eq_refl), (HE 23%nat 23%bv eq_refl), (HE 22%nat 22%bv eq_refl), G24, G20, G23, G22,
HE32, HE33, HE34, HU35, HU36, HE37, HE38.
clear - Hp Hpdef HiW Hi Hx Hxn Hn HW HH HNle Hfimg0 Hfimg1 Hbimg0 Hbimg1 G0 G1 C0 C1 Rbc Rbb Hsp0 Hsp1 Hsp16 Hac. assert (HGS : CGIF_SIZE = 96) by reflexivity.
rewrite !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (HAL : alias_ok E s2i_alias).
{ unfold s2i_alias. cbn [alias_ok]. split; [|split; [|exact I]].
- assert (HE35' : ew E 35 = Z_to_bv 64 (fimg + i * W + x)) by (rewrite HE35; f_equal; clear - Hpdef; lia).
apply (alias_add E 19 27 35 (fimg + i * W) x HE19 HE27 HE35'); clear - Hp Hpdef HiW Hx Hfimg0 Hfimg1 Hac; lia.
- assert (HE36' : ew E 36 = Z_to_bv 64 (bimg + i * W + x)) by (rewrite HE36; f_equal; clear - Hpdef; lia).
apply (alias_add E 25 27 36 (bimg + i * W) x HE25 HE27 HE36'); clear - Hp Hpdef HiW Hx Hbimg0 Hbimg1 Hac; lia. }
assert (HR0 : region_ok ubs2segs E memc s2i_stk).
{ unfold region_ok, s2i_stk. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [clear - Hsp0 Hsp1 Hac; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WWm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WGm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ cfp); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WCm]. }
assert (HR1 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 37 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU35.
split; [lia|]. split; [clear - Hp Hfimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE37, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(clear - Hp; lia))). }
assert (HR2 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 36%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 38 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU36.
split; [lia|]. split; [clear - Hp Hbimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE38, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(clear - Hp; lia))). }
assert (HPD : pairwise_disjoint E (ss_mem ss_s2i)).
{ unfold ss_s2i, s2i_stk. cbn [ss_mem pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite ?HU2, ?HU35, ?HU36.
repeat split; try exact I; clear - Dfb Hp Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hsp0 Hac HU2 HU35 HU36; lia. }
assert (HS : st_ok ubs2segs E ss_s2i (mkst regs (Z_to_bv 64 FL_S2I) memc (seg_rom ubs2segs))).
{ unfold ss_s2i. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor; [exact HR2 | constructor]]] | exact HPD | split; [exact HFA | split; [exact I | exact HAL]]]. }
clear HR0 HR1 HR2 HPD HFA HAL.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S2I) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cmpPixel. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha0. rewrite HE33 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite HE34 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 18%nat 18%bv eq_refl), G18 in Ha2.
jreg HS (13%bv:reg) as Ha3. rewrite HE37 in Ha3. jreg HS (14%bv:reg) as Ha4. rewrite HE38 in Ha4.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (Hbq : forall a, byte_at (ms_mem ms) a = byte_at memc a) by (intros a; unfold byte_at; rewrite (mbyte_of_eq _ _ _ _ K1); reflexivity).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc ss_s2i].
eapply SR_bind.
{ apply (cmp_callD API IMG mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC
STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) p FL_S2R HJ (KD_eq _ _ _ _ K0 K1) ltac:(clear - Hp; lia) Ha0 Ha1 Ha2).
- rewrite Hbq. exact Ha3.
- rewrite Hbq. exact Ha4.
- rewrite Hra. apply (ret_ok_even (Z_to_bv 64 FL_S2R)). vm_compute. reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hmem2 & Hres & Hfr2). clear HJ.
jafter_stretch_keep HS 39%nat regs2 mem2 CMP_CLOB FL_S2R [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]];
(eapply (region_kept_out ubs2segs _ _ _ _ 0 0); [intros z _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU2, ?HU35, ?HU36; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU2, ?HU35, ?HU36; clear - Hp Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hsp0 Hsp1 Hac; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_S2R) mem2 (seg_rom ubs2segs))) in HJ2.
set (E2 := havoc E 39 (map (getr regs2) CMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (EXIT : forall ss ms' pc', st_ok ubs2segs E2 ss ms' -> ss_pc ss = pc' -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) S2I_KEPT = true ->
(pc' = FL_S2F \/ pc' = FL_S2X) ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall x, ms_mem ms' x = memc x) ->
s2i_post STK sp0 FP L A mem md Lc Ac mdc regs memc (mkCfg ms' mdc)).
{ intros ss ms' pc' HS' Hpc Hrv Hkl Hpc' HJ' K'. exists (ms_regs ms'), (ms_mem ms'), pc'.
split; [rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hpc'|].
intros rr Hrr. subst E E2. exact (regs_kept_of_st_ok ubs2segs _ ss ms' regs _ S2I_KEPT HS' EA1 Hkl rr Hrr). }
jbranch ubs2tbl HS.
-
clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ2 FL_S2F. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_S2F HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [left; reflexivity | exact HJ2 |].
intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. rewrite Hmem2. apply K1.
-
clear Hc. jrun LAWS ubs2tbl_ok HS HJ2. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms0 z = mem2 z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch ubs2tbl HS.
+
rewrite branch_ne_U, (U_atom E2 32 W), (U_atom_off E2 27 x 1) in Hc
by first [subst E2; ew_havocA; first [exact HE32 | exact HE27] | clear - Hx Hxn Hn HW; lia].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.eqb_spec W (x + 1)); [discriminate Hc | clear - Hxn n0; lia]). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ2 FL_S2I. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K4 : forall z, ms_mem ms1 z = mem2 z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs _ S2I_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
assert (K5 : forall z, ms_mem ms1 z = memc z) by (intros z; rewrite K4, Hmem2; apply K1).
eapply SR_mono.
{ eapply (IH (x + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ i HJ2 (KD_eq _ _ _ _ K0 K5) Hfi Hbi Hi ltac:(clear - Hx; lia) ltac:(clear - Hxn; lia) Hn1).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- rewrite (HKR 19%bv ltac:(cbv; auto 20)). exact G19.
- rewrite (HKR 25%bv ltac:(cbv; auto 20)). exact G25.
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite HE27, unsigned_lit_small by (clear - Hx Hxn Hn HW; lia); reflexivity).
- rewrite (HKR 24%bv ltac:(cbv; auto 20)). exact G24.
- rewrite (HKR 20%bv ltac:(cbv; auto 20)). exact G20.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- rewrite (HKR 22%bv ltac:(cbv; auto 20)). exact G22. }
cbv beta. intros c' (regs' & mem' & pc' & -> & HJ' & K' & Hpc' & HK'). exists regs', mem', pc'.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K5|]. split; [exact Hpc'|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ2 FL_S2X. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ FL_S2X HS eq_refl eq_refl ltac:(vm_compute; reflexivity)); [right; reflexivity | exact HJ2 |].
intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. rewrite K3, Hmem2. apply K1.
Qed.
Definition s2o_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top : Z) (c' : config) : Prop :=
exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_S3) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KD mem0 spv mem' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 8 <= a < spv + 16) -> ~ (spv + 40 <= a < spv + 48) -> ~ (spv + 64 <= a < spv + 72) -> ~ (spv + 88 <= a < spv + 96) -> mbyte ubs2segs mem' a = mbyte ubs2segs memc a) /\
(exists hrow, top <= hrow < H /\ getr regs' 26 = Z_to_bv 64 (hrow + 1)) /\
getr regs' 12 = Z_to_bv 64 W /\ getr regs' 13 = Z_to_bv 64 top /\
getr regs' 21 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) /\ getr regs' 23 = Z_to_bv 64 (2 ^ 64 - 1 - bimg) /\
word_mem ubs2segs mem' (spv + 96) top /\ (forall r : reg, In r [2; 3; 4; 8; 9; 18]%bv -> getr regs' r = getr regs r).
Lemma fl_s2o : forall (n : nat) (i : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
spv = sp0 - 272 -> 272 <= STK ->
word_mem ubs2segs memc (spv + 8) top -> word_mem ubs2segs memc (spv + 40) 65535 ->
word_mem ubs2segs memc (spv + 88) top -> word_mem ubs2segs memc (spv + 96) top ->
0 <= top -> top + Z.of_nat n = i -> (1 <= n)%nat -> i < H ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 bimg -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) -> getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - bimg) ->
getr regs 10 = Z_to_bv 64 i -> getr regs 16 = Z_to_bv 64 (i + 1) -> getr regs 12 = Z_to_bv 64 W ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S2O) memc (seg_rom ubs2segs)) mdc) (s2o_post STK sp0 FP L A mem md Lc Ac mdc regs memc top).
Proof.
intros n. induction n as [|n IH]; intros i STK sp0 FP L A mem md Lc Ac mdc regs memc top HJ K0 Hfi Hbi Hspv HSTK W8 W40 W88 W96 Ht0 Htn Hn HiH
G2 G8 G9 G18 G21 G23 G10 Ga6 G12; [lia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGS : CGIF_SIZE = 96) by reflexivity.
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC memc K0) as (_ & _ & _ & _ & _ & WHm & WWm & WGm & WCm).
assert (Hi64 : 1 <= i <= 65534 /\ 0 <= top <= 65533 /\ top < i) by (clear - Ht0 Htn Hn HiH HH; lia).
assert (HiW : 0 <= i * W /\ i * W + W <= N) by (rewrite HN; clear - Hi64 HiH HW; nia).
assert (WRS : forall m', journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac m' mdc -> forall a, spv + 8 <= a < spv + 128 -> writable_at ubs2segs m' a).
{ intros m' HJm a Ha. pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _). apply Hstw. clear - Ha Hspv HSTK. lia. }
set (E := Ereg regs (map (Z_to_bv 64) [top; H; g; cfp] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 top) by (subst E; apply (Ereg_vals regs [top; H; g; cfp] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 H) by (subst E; apply (Ereg_vals regs [top; H; g; cfp] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 g) by (subst E; apply (Ereg_vals regs [top; H; g; cfp] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 cfp) by (subst E; apply (Ereg_vals regs [top; H; g; cfp] [] 3%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
pose proof (HE 8%nat 8%bv eq_refl) as HE8. rewrite G8 in HE8.
pose proof (HE 9%nat 9%bv eq_refl) as HE9. rewrite G9 in HE9.
pose proof (HE 10%nat 10%bv eq_refl) as HE10. rewrite G10 in HE10.
pose proof (HE 12%nat 12%bv eq_refl) as HE12. rewrite G12 in HE12.
pose proof (HE 16%nat 16%bv eq_refl) as HE16. rewrite Ga6 in HE16.
pose proof (HE 21%nat 21%bv eq_refl) as HE21. rewrite G21 in HE21.
pose proof (HE 23%nat 23%bv eq_refl) as HE23. rewrite G23 in HE23.
assert (UWI : U E (SMd M_MUL (SOff 12 0) (SOff 10 0)) = i * W).
{ replace (i * W) with (W * i) by (clear; lia). apply (U_mul_small' E _ _ W i); [apply (U_atom E 12 W HE12) | apply (U_atom E 10 i HE10) | | | ]; clear - HW Hi64; nia. }
assert (UF : U E (SAlu ALU_ADD (SOff 9 0) (SMd M_MUL (SOff 12 0) (SOff 10 0))) = fimg + i * W).
{ apply (U_add_small E _ _ fimg (i * W)); [apply (U_atom E 9 fimg HE9) | exact UWI | | | ]; clear - Hfimg0 Hfimg1 HiW Hac HW; lia. }
assert (UB : U E (SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 12 0) (SOff 10 0))) = bimg + i * W).
{ apply (U_add_small E _ _ bimg (i * W)); [apply (U_atom E 8 bimg HE8) | exact UWI | | | ]; clear - Hbimg0 Hbimg1 HiW Hac HW; lia. }
assert (HR : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 8 128 64 72 s2o_hi)).
{ unfold region_ok, s2o_hi. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [clear - Hsp0 Hsp1 Hac; lia|]. split; [intros o Ho; apply (WRS _ HJ); lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W8].
- eapply (chunk_ok_val _ _ _ _ _ _ _ 65535); [reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W40].
- eapply (chunk_ok_val _ _ _ _ _ _ _ H); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WHm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W88].
- eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W96].
- eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE12, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WWm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WGm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ cfp); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WCm]. }
assert (HFA : atoms_ok E s2o_facts).
{ unfold s2o_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HE10, HE12, HE21, HE32, HE33, HE34, HE35.
rewrite !unsigned_lit_small by (clear - Hi64 HW HH G0 G1 C0 C1 Hfimg0 Hfimg1 Hac HGS HiW; lia).
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hi64 HW HH HiH G0 G1 C0 C1 Hfimg0 Hfimg1 Hsp0 Hsp1 Hsp16 Hac HGS HiW. repeat split; lia. }
assert (HCO : conds_ok E [mkAC BC_GEU (SOff 21 0) (SMd M_MUL (SOff 12 0) (SOff 10 0))]).
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, UWI, (U_atom E 21 (2 ^ 64 - 1 - fimg) HE21) by (clear - Hfimg0 Hfimg1 Hac HiW HW; lia).
apply negb_true_iff, Z.ltb_ge. clear - HiW Hfimg0 Hfimg1 Hac HW; lia. }
assert (HPD : pairwise_disjoint E (ss_mem ss_s2o)) by (unfold ss_s2o; cbn [ss_mem pairwise_disjoint all_disjoint]; repeat split; try exact I).
assert (HS : st_ok ubs2segs E ss_s2o (mkst regs (Z_to_bv 64 FL_S2O) memc (seg_rom ubs2segs))).
{ unfold ss_s2o. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR | constructor] | exact HPD | split; [exact HFA | split; [exact HCO | exact I]]]. }
clear HR HPD HFA HCO.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S2O) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ FL_S2I.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (FR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 64 <= a < spv + 72) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hna. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr. destruct Hr as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite HU2. clear - Hna; lia. }
assert (K1 : KD mem0 spv (ms_mem ms)) by (apply (KD_frame _ _ _ _ K0); intros a Ha _ _ Hn3 _; apply FR1; assumption).
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs2segs E ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs;
pose proof (regs_kept_of_st_ok ubs2segs E ssx msx regs _ [2; 3; 4; 8; 9; 18; 21; 23]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR0;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (W64 : word_mem ubs2segs (ms_mem ms) (spv + 64) (i + 1)).
{ apply (chunk_word E _ _ 64 (SOff 16 0) _ (proj1 (Forall_forall _ _) Hcs _ ltac:(cbn [In]; tauto))); [cbn [sv_denot]; rewrite Z.add_0_r, HE16, Z_to_bv_bv_unsigned; reflexivity | clear - Hi64; lia]. }
clear Hcs.
assert (Q26 : getr (ms_regs ms) 26 = Z_to_bv 64 i) by (apply (RG 26%bv 10%nat _ eq_refl); exact HE10).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_s2i (Z.to_nat W) 0 STK sp0 FP L A mem md Lc Ac mdc _ _ i HJ K1 Hfi Hbi ltac:(clear - Hi64 HiH; lia) ltac:(clear; lia) ltac:(clear - HW; lia) ltac:(clear - HW; lia)).
- rewrite (HKR0 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (HKR0 18%bv ltac:(cbv; auto 20)). exact G18.
- rewrite (RGX 19%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UF.
- rewrite (RGX 25%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UB.
- rewrite (RGX 27%bv _ eq_refl). eval_sr_get. reflexivity.
- rewrite (RGX 24%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite U_notv, UF. reflexivity.
- rewrite (RGX 20%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite U_notv, UB. reflexivity.
- rewrite (HKR0 23%bv ltac:(cbv; auto 20)). exact G23.
- rewrite (RGX 22%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UWI. }
cbv beta. intros c' (regs' & mem' & pc' & -> & HJ' & Kmem' & Hpc' & HK'').
assert (HKO : forall r : reg, In r [2; 3; 4; 8; 9; 18; 21; 23]%bv -> getr regs' r = getr regs r)
by (intros rr Hrr; rewrite (HK'' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)); apply (HKR0 rr Hrr)).
assert (G26' : getr regs' 26 = Z_to_bv 64 i) by (rewrite (HK'' 26%bv ltac:(cbv; auto 50)); exact Q26).
clear HJ HS RG RGX HK'' HKR0 Q26.
assert (K' : KD mem0 spv mem') by (exact (KD_eq _ _ _ _ K1 Kmem')).
assert (FRM : forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 64 <= a < spv + 72) -> mbyte ubs2segs mem' a = mbyte ubs2segs memc a)
by (intros a Ha Hna; rewrite (mbyte_of_eq _ _ _ _ Kmem'); apply FR1; assumption).
assert (W8m : word_mem ubs2segs mem' (spv + 8) top) by (apply (word_mem_tr memc); [exact W8 | intros k Hk; apply FRM; clear - Hk Hsp0 Hsp1 Hac; lia]).
assert (W40m : word_mem ubs2segs mem' (spv + 40) 65535) by (apply (word_mem_tr memc); [exact W40 | intros k Hk; apply FRM; clear - Hk Hsp0 Hsp1 Hac; lia]).
assert (W88m : word_mem ubs2segs mem' (spv + 88) top) by (apply (word_mem_tr memc); [exact W88 | intros k Hk; apply FRM; clear - Hk Hsp0 Hsp1 Hac; lia]).
assert (W96m : word_mem ubs2segs mem' (spv + 96) top) by (apply (word_mem_tr memc); [exact W96 | intros k Hk; apply FRM; clear - Hk Hsp0 Hsp1 Hac; lia]).
assert (W64m : word_mem ubs2segs mem' (spv + 64) (i + 1)) by (apply (word_mem_tr (ms_mem ms)); [exact W64 | intros k Hk; apply (mbyte_of_eq _ _ _ _ Kmem')]).
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC mem' K') as (_ & _ & _ & _ & _ & _ & WWm' & _ & _).
clear FR1 K1 W64 Kmem'.
assert (EXIT : forall extra ss ms' hrow, st_ok ubs2segs (Ereg regs' extra) ss ms' -> ss_pc ss = FL_S3 -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 8; 9; 18; 21; 23]%bv = true ->
top <= hrow < H ->
getr (ms_regs ms') 26 = Z_to_bv 64 (hrow + 1) -> getr (ms_regs ms') 12 = Z_to_bv 64 W -> getr (ms_regs ms') 13 = Z_to_bv 64 top ->
(forall z, ms_mem ms' z = mem' z) -> journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
s2o_post STK sp0 FP L A mem md Lc Ac mdc regs memc top (mkCfg ms' mdc)).
{ intros extra ss ms' hrow HS' Hpc Hrv Hkl Hh Q26 Q12 Q13 Kq HJq.
pose proof (regs_kept_of_st_ok ubs2segs _ ss ms' regs' extra _ HS' (env_agree_refl _ _) Hkl) as Kr.
exists (ms_regs ms'), (ms_mem ms').
split; [rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc; reflexivity|].
split; [exact HJq|]. split; [exact (KD_eq _ _ _ _ K' Kq)|].
split; [intros a Ha Hn1 Hn2 Hn3 Hn4; rewrite (mbyte_of_eq _ _ _ _ Kq); apply FRM; assumption|].
split; [exists hrow; split; [exact Hh | exact Q26]|].
split; [exact Q12|]. split; [exact Q13|].
split; [rewrite (Kr 21%bv ltac:(cbv; auto 20)), (HKO 21%bv ltac:(cbv; auto 20)); exact G21|].
split; [rewrite (Kr 23%bv ltac:(cbv; auto 20)), (HKO 23%bv ltac:(cbv; auto 20)); exact G23|].
split; [apply (word_mem_tr mem'); [exact W96m | intros k Hk; apply (mbyte_of_eq _ _ _ _ Kq)]|].
intros rr Hrr. assert (Hrr' : In rr [2; 3; 4; 8; 9; 18; 21; 23]%bv) by (clear - Hrr; cbv in Hrr; cbv; intuition).
rewrite (Kr rr Hrr'). apply (HKO rr Hrr'). }
destruct Hpc' as [-> | ->].
-
set (E' := Ereg regs' (map (Z_to_bv 64) [top; W; i + 1] ++ [])).
assert (HE' : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E' m = getr regs' rr) by (intros; subst E'; apply ew_Ereg_nat; assumption).
assert (HE'32 : ew E' 32 = Z_to_bv 64 top) by (subst E'; apply (Ereg_vals regs' [top; W; i + 1] [] 0%nat); reflexivity).
assert (HE'33 : ew E' 33 = Z_to_bv 64 W) by (subst E'; apply (Ereg_vals regs' [top; W; i + 1] [] 1%nat); reflexivity).
assert (HE'34 : ew E' 34 = Z_to_bv 64 (i + 1)) by (subst E'; apply (Ereg_vals regs' [top; W; i + 1] [] 2%nat); reflexivity).
assert (G2' : getr regs' 2 = Z_to_bv 64 spv) by (rewrite (HKO 2%bv ltac:(cbv; auto 20)); exact G2).
assert (HU2' : bv_unsigned (ew E' 2) = spv) by (rewrite (HE' 2%nat 2%bv eq_refl), G2'; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HFA' : atoms_ok E' [ (2%nat, mkAF CEIL_MIN (2^63) 4); (34%nat, mkAF 2 65535 0); (32%nat, mkAF 0 65533 0); (33%nat, mkAF 1 65535 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2', HE'32, HE'33, HE'34.
rewrite !unsigned_lit_small by (clear - Hi64 HW HiH HH; lia). change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hi64 HW HH HiH Hsp0 Hsp1 Hsp16 Hac. repeat split; lia. }
assert (HR' : region_ok ubs2segs E' mem' (YQ0b.mkRegion (Some 2%nat) 64 112 64 64 [mkChunk 64 (CVal 8 (SOff 34 0)); mkChunk 88 (CVal 8 (SOff 32 0)); mkChunk 104 (CVal 8 (SOff 33 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2'.
split; [lia|]. split; [clear - Hsp0 Hsp1 Hac; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (i + 1)); [cbn [sv_denot]; rewrite Z.add_0_r, HE'34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W64m].
* eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, HE'32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W88m].
* eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE'33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WWm'].
}
assert (HS : st_ok ubs2segs E' ss_s2f (mkst regs' (Z_to_bv 64 FL_S2F) mem' (seg_rom ubs2segs))).
{ unfold ss_s2f. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR' | constructor] | cbn [pairwise_disjoint all_disjoint]; repeat split; try exact I | split; [exact HFA' | split; exact I]]. }
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 FL_S2F) mem' (seg_rom ubs2segs))) in HJ'.
jrun_to LAWS ubs2tbl_ok HS HJ' FL_S3. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => pose proof (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) as K2 end.
clear HF HG.
apply SR_ret. apply (EXIT _ _ _ i HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Hi64 HiH; lia)); [| | | exact K2 | exact HJ'].
+ reg_nowF HS ltac:(rewrite HE'34, Z_to_bv_bv_unsigned; reflexivity).
+ reg_nowF HS ltac:(rewrite HE'33, Z_to_bv_bv_unsigned; reflexivity).
+ reg_nowF HS ltac:(rewrite HE'32, Z_to_bv_bv_unsigned; reflexivity).
-
set (E' := Ereg regs' (map (Z_to_bv 64) [top; W] ++ [])).
assert (HE' : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E' m = getr regs' rr) by (intros; subst E'; apply ew_Ereg_nat; assumption).
assert (HE'32 : ew E' 32 = Z_to_bv 64 top) by (subst E'; apply (Ereg_vals regs' [top; W] [] 0%nat); reflexivity).
assert (HE'33 : ew E' 33 = Z_to_bv 64 W) by (subst E'; apply (Ereg_vals regs' [top; W] [] 1%nat); reflexivity).
assert (HE'26 : ew E' 26 = Z_to_bv 64 i) by (rewrite (HE' 26%nat 26%bv eq_refl); exact G26').
assert (G2' : getr regs' 2 = Z_to_bv 64 spv) by (rewrite (HKO 2%bv ltac:(cbv; auto 20)); exact G2).
assert (HU2' : bv_unsigned (ew E' 2) = spv) by (rewrite (HE' 2%nat 2%bv eq_refl), G2'; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HFA' : atoms_ok E' [ (2%nat, mkAF CEIL_MIN (2^63) 4); (26%nat, mkAF 1 65534 0); (32%nat, mkAF 0 65533 0); (33%nat, mkAF 1 65535 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2', HE'26, HE'32, HE'33.
rewrite !unsigned_lit_small by (clear - Hi64 HW HiH HH; lia). change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Hi64 HW HH HiH Hsp0 Hsp1 Hsp16 Hac. repeat split; lia. }
assert (HR' : region_ok ubs2segs E' mem' (YQ0b.mkRegion (Some 2%nat) 8 112 8 8 [mkChunk 8 (CVal 8 (SOff 32 0)); mkChunk 40 (CVal 8 (SLit 65535)); mkChunk 88 (CVal 8 (SOff 32 0)); mkChunk 104 (CVal 8 (SOff 33 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2'.
split; [lia|]. split; [clear - Hsp0 Hsp1 Hac; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
* eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, HE'32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W8m].
* eapply (chunk_ok_val _ _ _ _ _ _ _ 65535); [reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W40m].
* eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, HE'32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W88m].
* eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE'33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WWm'].
}
assert (HS : st_ok ubs2segs E' ss_s2x (mkst regs' (Z_to_bv 64 FL_S2X) mem' (seg_rom ubs2segs))).
{ unfold ss_s2x. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR' | constructor] | cbn [pairwise_disjoint all_disjoint]; repeat split; try exact I | split; [exact HFA' | split; exact I]]. }
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 FL_S2X) mem' (seg_rom ubs2segs))) in HJ'.
jrun LAWS ubs2tbl_ok HS HJ'. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => pose proof (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) as K2 end.
clear HF HG.
jbranch ubs2tbl HS.
+
rewrite branch_geu_U, U_and_lit, (U_atom E' 32 top), (U_atom_off E' 26 i (-1)), land_ffff in Hc
by first [exact HE'32 | exact HE'26 | (clear - Hi64; lia)].
assert (Hit : i - 1 = top) by (destruct (Z.ltb_spec top (i + -1)) as [Hl|Hl]; [discriminate Hc | clear - Hi64 Hl; lia]). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ' FL_S3. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => pose proof (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) as K3 end.
clear HF HG.
apply SR_ret. apply (EXIT _ _ _ top HS eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Hi64 HiH; lia)); [| | | intros z; rewrite K3; apply K2 | exact HJ'].
* reg_nowF HS ltac:(rewrite HE'26, Z_to_bv_bv_unsigned; f_equal; clear - Hit; lia).
* reg_nowF HS ltac:(rewrite HE'33, Z_to_bv_bv_unsigned; reflexivity).
* reg_nowF HS ltac:(rewrite HE'32, Z_to_bv_bv_unsigned; reflexivity).
+
rewrite branch_geu_U, U_and_lit, (U_atom E' 32 top), (U_atom_off E' 26 i (-1)), land_ffff in Hc
by first [exact HE'32 | exact HE'26 | (clear - Hi64; lia)].
assert (Hn1 : (1 <= n)%nat) by (destruct (Z.ltb_spec top (i + -1)) as [Hl|Hl]; [clear - Htn Hl; lia | discriminate Hc]). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ' FL_S2O. { apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => pose proof (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) as K3 end.
clear HF HG.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (regs_kept_of_st_ok ubs2segs Ex ssx msx regs' _ [2; 3; 4; 8; 9; 18; 21; 23]%bv HS ltac:(subst E'; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (K4 : forall z, ms_mem msx z = mem' z) by (intros z; rewrite K3; apply K2) end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i - 1) STK sp0 FP L A mem md Lc Ac mdc _ _ top HJ' (KD_eq _ _ _ _ K' K4) Hfi Hbi Hspv HSTK
(word_mem_tr _ _ _ _ W8m (fun k _ => mbyte_of_eq _ _ _ _ K4)) (word_mem_tr _ _ _ _ W40m (fun k _ => mbyte_of_eq _ _ _ _ K4))
(word_mem_tr _ _ _ _ W88m (fun k _ => mbyte_of_eq _ _ _ _ K4)) (word_mem_tr _ _ _ _ W96m (fun k _ => mbyte_of_eq _ _ _ _ K4))
Ht0 ltac:(clear - Htn; lia) Hn1 ltac:(clear - HiH; lia)).
* rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2'.
* rewrite (HKR 8%bv ltac:(cbv; auto 20)), (HKO 8%bv ltac:(cbv; auto 20)). exact G8.
* rewrite (HKR 9%bv ltac:(cbv; auto 20)), (HKO 9%bv ltac:(cbv; auto 20)). exact G9.
* rewrite (HKR 18%bv ltac:(cbv; auto 20)), (HKO 18%bv ltac:(cbv; auto 20)). exact G18.
* rewrite (HKR 21%bv ltac:(cbv; auto 20)), (HKO 21%bv ltac:(cbv; auto 20)). exact G21.
* rewrite (HKR 23%bv ltac:(cbv; auto 20)), (HKO 23%bv ltac:(cbv; auto 20)). exact G23.
* reg_nowF HS ltac:(rewrite HE'26, unsigned_lit_small by (clear - Hi64; lia); first [reflexivity | f_equal; clear; lia]).
* reg_nowF HS ltac:(rewrite HE'26, Z_to_bv_bv_unsigned; f_equal; clear; lia).
* reg_nowF HS ltac:(rewrite HE'33, Z_to_bv_bv_unsigned; reflexivity). }
cbv beta. intros c' (regs'' & mem'' & -> & HJ'' & K'' & SF'' & Hh'' & Q12'' & Q13'' & Q21'' & Q23'' & W96'' & HK3). exists regs'', mem''.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact K''|].
split; [intros a Ha Hn1' Hn2 Hn3 Hn4; rewrite (SF'' a Ha Hn1' Hn2 Hn3 Hn4), (mbyte_of_eq _ _ _ _ K4); apply FRM; assumption|].
split; [exact Hh''|]. split; [exact Q12''|]. split; [exact Q13''|]. split; [exact Q21''|]. split; [exact Q23''|]. split; [exact W96''|].
intros rr Hrr. assert (Hrr' : In rr [2; 3; 4; 8; 9; 18; 21; 23]%bv) by (clear - Hrr; cbv in Hrr; cbv; intuition).
rewrite (HK3 rr Hrr), (HKR rr Hrr'). apply (HKO rr Hrr').
Qed.
Lemma fl_s2 : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
spv = sp0 - 272 -> 272 <= STK -> 0 <= top < H ->
word_mem ubs2segs memc (spv + 96) top ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 18 = Z_to_bv 64 fhp -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 8 = Z_to_bv 64 bimg ->
getr regs 26 = Z_to_bv 64 H -> getr regs 12 = Z_to_bv 64 top -> getr regs 13 = Z_to_bv 64 top ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S2) memc (seg_rom ubs2segs)) mdc) (s2o_post STK sp0 FP L A mem md Lc Ac mdc regs memc top).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc top HJ K0 Hfi Hbi Hspv HSTK Htop W96 G2 G18 G9 G8 G26 G12 G13.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGS : CGIF_SIZE = 96) by reflexivity.
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC memc K0) as (_ & _ & _ & _ & _ & WHm & WWm & _ & _).
assert (HN0 : 0 <= N) by (rewrite HN; clear - HW HH; nia).
assert (WRS : forall m', journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac m' mdc -> forall a, spv + 8 <= a < spv + 112 -> writable_at ubs2segs m' a).
{ intros m' HJm a Ha. pose proof HJm as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _). apply Hstw. clear - Ha Hspv HSTK. lia. }
set (E := Ereg regs (map (Z_to_bv 64) [W] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 W) by (subst E; apply (Ereg_vals regs [W] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
pose proof (HE 8%nat 8%bv eq_refl) as HE8. rewrite G8 in HE8.
pose proof (HE 9%nat 9%bv eq_refl) as HE9. rewrite G9 in HE9.
pose proof (HE 12%nat 12%bv eq_refl) as HE12. rewrite G12 in HE12.
pose proof (HE 13%nat 13%bv eq_refl) as HE13. rewrite G13 in HE13.
pose proof (HE 26%nat 26%bv eq_refl) as HE26. rewrite G26 in HE26.
assert (HRS : Forall (region_ok ubs2segs E memc) s2_regions).
{ unfold s2_regions. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]];
unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]; rewrite HU2;
(split; [lia|]); (split; [clear - Hsp0 Hsp1 Hac; lia|]).
- split; [intros o Ho; apply (WRS _ HJ); lia | constructor].
- split; [intros o Ho; apply (WRS _ HJ); lia | constructor].
- split; [intros o Ho; apply (WRS _ HJ); lia | constructor].
- split; [intros o Ho; lia|]. constructor; [|constructor].
eapply (chunk_ok_val _ _ _ _ _ _ _ H); [cbn [sv_denot]; rewrite Z.add_0_r, HE26, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WHm].
- split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, HE12, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W96].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact WWm]. }
assert (HPD : pairwise_disjoint E s2_regions).
{ unfold s2_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite ?HU2. repeat split; try exact I; lia. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4); (12%nat, mkAF 0 65534 0); (26%nat, mkAF 1 65535 0); (32%nat, mkAF 1 65535 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE12, HE26, HE32.
rewrite !unsigned_lit_small by (clear - Htop HW HH; lia). change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
clear - Htop HW HH Hsp0 Hsp1 Hsp16 Hac. repeat split; lia. }
assert (HCz : forall z : bool, (if z then H - 1 <= top else top < H - 1) ->
conds_ok E [ mkAC (if z then BC_GEU else BC_LTU) (SAlu ALU_AND (SOff 12 0) (SLit 65535)) (SAlu ALU_AND (SOff 26 (-1)) (SLit 65535)) ]).
{ intros z Hz. cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
destruct z; [rewrite branch_geu_U | rewrite branch_ltu_U];
rewrite !U_and_lit, (U_atom E 12 top), (U_atom_off E 26 H (-1)), !land_ffff by first [exact HE12 | exact HE26 | clear - Htop HH; lia];
[apply negb_true_iff, Z.ltb_ge | apply Z.ltb_lt]; clear - Hz; lia. }
assert (HSz : forall z : bool, (if z then H - 1 <= top else top < H - 1) -> st_ok ubs2segs E (ss_s2 z) (mkst regs (Z_to_bv 64 FL_S2) memc (seg_rom ubs2segs))).
{ intros z Hz. unfold ss_s2. apply entry_st_ok_full; [apply regs_ok_Ereg | destruct z; vm_compute; reflexivity | exact HRS | exact HPD | split; [exact HFA | split; [exact (HCz z Hz) | exact I]]]. }
clear HRS HPD HFA HCz.
assert (WRT : forall E0, bv_unsigned (ew E0 2) = spv -> wr_ok E0 s2_regions STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 H2. unfold s2_regions.
eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia |].
eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia |].
eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (FRG : forall m', frame_of E s2_regions memc m' -> forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 8 <= a < spv + 16) -> ~ (spv + 40 <= a < spv + 48) -> ~ (spv + 88 <= a < spv + 96) ->
mbyte ubs2segs m' a = mbyte ubs2segs memc a).
{ intros m' HFx a Ha H1 H2 H3. apply (mbyte_of_frame _ _ _ _ a HFx Ha). intros r Hr. unfold s2_regions in Hr. cbv [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [r_base r_wlo r_whi base_val]; rewrite HU2; clear - H1 H2 H3; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S2) memc (seg_rom ubs2segs))) in HJ.
destruct (Z_lt_ge_dec top (H - 1)) as [Hlt | Hge].
-
pose proof (HSz false Hlt) as HS. clear HSz.
jrun_to LAWS ubs2tbl_ok HS HJ FL_S2O. { apply WRT. exact HU2. }
cbn [ms_mem mkst] in HF.
pose proof (FRG _ HF) as FR1.
assert (K1 : KD mem0 spv (ms_mem ms)) by (apply (KD_frame _ _ _ _ K0); intros a Ha Hn1 Hn2 Hn3 Hn4; apply FR1; [exact Ha | exact Hn1 | clear - Hn2; lia | clear - Hn4; lia]).
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs2segs E ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hc0;
pose proof (st_region_chunks ubs2segs E ssx msx 1 _ 2%nat spv HS eq_refl eq_refl HU2) as Hc1;
pose proof (st_region_chunks ubs2segs E ssx msx 2 _ 2%nat spv HS eq_refl eq_refl HU2) as Hc2;
pose proof (regs_kept_of_st_ok ubs2segs E ssx msx regs _ [2; 3; 4; 8; 9; 18]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hc0, Hc1, Hc2.
assert (W8n : word_mem ubs2segs (ms_mem ms) (spv + 8) top).
{ apply (chunk_word E _ _ 8 (SAlu ALU_AND (SOff 12 0) (SLit 65535)) _ (proj1 (Forall_forall _ _) Hc0 _ ltac:(cbn [In]; tauto))); [| clear - Htop HH; lia].
apply denot_of_U'. rewrite U_and_lit, (U_atom E 12 top HE12) by (clear - Htop HH; lia). apply land_ffff. clear - Htop HH; lia. }
assert (W40n : word_mem ubs2segs (ms_mem ms) (spv + 40) 65535).
{ apply (chunk_word E _ _ 40 (SLit 65535) _ (proj1 (Forall_forall _ _) Hc1 _ ltac:(cbn [In]; tauto))); [reflexivity | lia]. }
assert (W88n : word_mem ubs2segs (ms_mem ms) (spv + 88) top).
{ apply (chunk_word E _ _ 88 (SOff 13 0) _ (proj1 (Forall_forall _ _) Hc2 _ ltac:(cbn [In]; tauto))); [cbn [sv_denot]; rewrite Z.add_0_r, HE13, Z_to_bv_bv_unsigned; reflexivity | clear - Htop HH; lia]. }
assert (W96n : word_mem ubs2segs (ms_mem ms) (spv + 96) top) by (apply (word_mem_tr memc); [exact W96 | intros k Hk; apply FR1; clear - Hk Hsp0 Hsp1 Hac; lia]).
clear Hc0 Hc1 Hc2.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (fl_s2o (Z.to_nat (H - 1 - top)) (H - 1) STK sp0 FP L A mem md Lc Ac mdc _ _ top HJ K1 Hfi Hbi Hspv HSTK W8n W40n W88n W96n
ltac:(clear - Htop; lia) ltac:(clear - Hlt Htop; lia) ltac:(clear - Hlt; lia) ltac:(clear; lia)).
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- rewrite (RGX 21%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite U_notv, (U_atom E 9 fimg HE9) by (clear - Hfimg0 Hfimg1 Hac HN0; lia). reflexivity.
- rewrite (RGX 23%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite U_notv, (U_atom E 8 bimg HE8) by (clear - Hbimg0 Hbimg1 Hac HN0; lia). reflexivity.
- reg_nowF HS ltac:(rewrite HE26, unsigned_lit_small by (clear - HH; lia); first [reflexivity | f_equal; clear; lia]).
- reg_nowF HS ltac:(rewrite HE26, Z_to_bv_bv_unsigned; f_equal; clear; lia).
- reg_nowF HS ltac:(rewrite HE32, Z_to_bv_bv_unsigned; reflexivity). }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & K2 & SF2 & Hh2 & Q12 & Q13 & Q21 & Q23 & W96x & HK2). exists regs2, mem2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact K2|].
split; [intros a Ha Hn1 Hn2 Hn3 Hn4; rewrite (SF2 a Ha Hn1 Hn2 Hn3 Hn4); apply FR1; assumption|].
split; [exact Hh2|]. split; [exact Q12|]. split; [exact Q13|]. split; [exact Q21|]. split; [exact Q23|]. split; [exact W96x|].
intros rr Hrr. rewrite (HK2 rr Hrr). apply (HKR rr Hrr).
-
assert (Hte : top = H - 1) by (clear - Hge Htop; lia).
assert (Hge' : H - 1 <= top) by (clear - Hge; lia). pose proof (HSz true Hge') as HS. clear HSz.
jrun_to LAWS ubs2tbl_ok HS HJ FL_S3. { apply WRT. exact HU2. }
cbn [ms_mem mkst] in HF.
pose proof (FRG _ HF) as FR1.
assert (K1 : KD mem0 spv (ms_mem ms)) by (apply (KD_frame _ _ _ _ K0); intros a Ha Hn1 Hn2 Hn3 Hn4; apply FR1; [exact Ha | exact Hn1 | clear - Hn2; lia | clear - Hn4; lia]).
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (regs_kept_of_st_ok ubs2segs E ssx msx regs _ [2; 3; 4; 8; 9; 18]%bv HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; reflexivity) end.
apply SR_ret. exists (ms_regs ms), (ms_mem ms).
split; [rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl); reflexivity|].
split; [exact HJ|]. split; [exact K1|].
split; [intros a Ha Hn1 Hn2 Hn3 Hn4; apply FR1; assumption|].
split; [exists (H - 1); split; [clear - Hte Htop; lia | reg_nowF HS ltac:(rewrite HE26, Z_to_bv_bv_unsigned; f_equal; clear; lia)]|].
split; [reg_nowF HS ltac:(rewrite HE32, Z_to_bv_bv_unsigned; reflexivity)|].
split; [reg_nowF HS ltac:(rewrite HE13, Z_to_bv_bv_unsigned; reflexivity)|].
split; [rewrite (RGX 21%bv _ eq_refl); eval_sr_get; apply denot_of_U'; rewrite U_notv, (U_atom E 9 fimg HE9) by (clear - Hfimg0 Hfimg1 Hac HN0; lia); reflexivity|].
split; [rewrite (RGX 23%bv _ eq_refl); eval_sr_get; apply denot_of_U'; rewrite U_notv, (U_atom E 8 bimg HE8) by (clear - Hbimg0 Hbimg1 Hac HN0; lia); reflexivity|].
split; [apply (word_mem_tr memc); [exact W96 | intros k Hk; apply FR1; clear - Hk Hsp0 Hsp1 Hac; lia]|].
intros rr Hrr. apply (HKR rr Hrr).
Qed.
End h.
End S.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
