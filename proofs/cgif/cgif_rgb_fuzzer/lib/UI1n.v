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
UI1h UI16 UI1z UI1k UI21 UI22 UI23
UI1j UI1s UI1t UI1l.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition XS3 : sv := SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 16 1) (SLit 65535)) (SOff 12 0)) (SLit 1).
Definition f3l_facts : list (nat * afact) :=
[ (14%nat, mkAF 0 99999999 0); (16%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0); (17%nat, mkAF 0 99999999 0);
(10%nat, mkAF 0 99999999 0); (12%nat, mkAF 1 65535 0); (11%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 4097) 0);
(8%nat, mkAF 0 65534 0); (9%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 4096 CEIL_MAX 0); (27%nat, mkAF 1 65535 0);
(32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 4096 CEIL_MAX 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ].
Definition f3l_conds : list acond := [ mkAC BC_GEU (SOff 33 0) (SOff 20 0) ].
Definition f3l_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 20 0) (SOff 14 0), SOff 33 0); (SAlu ALU_ADD (SOff 9 0) (SOff 14 0), SOff 32 0) ].
Definition ss_f3l : sstate :=
mkSS FL_F3L (sr_set (sr_set sr_atoms 15%bv (SLit 65535)) 13%bv (SLit 1))
[ YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ;
YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))] ] None
(mkFacts f3l_facts f3l_conds f3l_alias).
Definition F3_KEPT : list reg := [2; 3; 4; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv.
Definition X0 : sv := SAlu ALU_SRL (SAlu ALU_SLL (SMd M_MUL (SOff 21 0) (SOff 27 0)) (SLit 32)) (SLit 32).
Definition ss_f3 : sstate :=
mkSS FL_F3 sr_atoms [] None
(mkFacts [ (21%nat, mkAF 0 65534 0); (8%nat, mkAF 0 65534 0); (19%nat, mkAF 0 65534 0); (27%nat, mkAF 1 65535 0);
(9%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 4096 CEIL_MAX 0); (32%nat, mkAF 4096 CEIL_MAX 0) ]
[ mkAC BC_GEU (SOff 32 0) (SOff 9 0) ] [ (SAlu ALU_ADD (SOff 9 0) X0, SOff 32 0) ]).
Definition F3S_KEPTV : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 27]%bv.
Definition F3S_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 27]%bv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma f3_hgt : forall t r k, k mod 2 ^ 64 = 2 ^ 64 - 1 -> 0 <= t <= r -> r < 65535 ->
(((t * (k mod 2 ^ 64)) mod 2 ^ 64 + 1 mod 2 ^ 64) mod 2 ^ 64 + r) mod 2 ^ 64 = r + 1 - t.
Proof using. intros t r k Hk Ht Hr. rewrite Hk. lia. Qed.
Lemma f3_top_hgt : forall t r k1 k2 s, k1 mod 2 ^ 64 = 2 ^ 64 - 2 ^ 48 -> k2 mod 2 ^ 64 = 2 ^ 48 -> s = 48 -> 0 <= t <= r -> r < 65535 ->
(Z.shiftr ((((t * (k1 mod 2 ^ 64)) mod 2 ^ 64 + k2 mod 2 ^ 64) mod 2 ^ 64 + Z.shiftl r s mod 2 ^ 64) mod 2 ^ 64) s mod 2 ^ 64 + t) mod 2 ^ 64 = t + (r + 1 - t).
Proof using. intros t r k1 k2 s Hk1 Hk2 Hs Ht Hr. rewrite Hk1, Hk2, Hs, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Section b.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Definition f3l_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top h c0 : Z) (c' : config) : Prop :=
exists regs' mem' left,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F4) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
0 <= left <= c0 /\ getr regs' 26 = Z_to_bv 64 left /\ getr regs' 10 = Z_to_bv 64 (top * W) /\
(forall r : reg, In r F3_KEPT -> getr regs' r = getr regs r) /\
((exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + left)) /\ (forall i2 x2, top <= i2 < top + h -> 0 <= x2 < left -> ~ DIFb mem0 fimg bimg (i2 * W + x2))).
Lemma fl_f3l : forall (n : nat) (i x : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top h c0 : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top -> 1 <= h -> top + h <= H -> 0 <= c0 < W -> DIFb mem0 fimg bimg (top * W + c0) ->
top <= i < top + h -> 0 <= x <= c0 ->
(c0 - x) * h + (top + h - 1 - i) < Z.of_nat n ->
getr regs 14 = Z_to_bv 64 (i * W + x) -> getr regs 16 = Z_to_bv 64 i -> getr regs 26 = Z_to_bv 64 x -> getr regs 17 = Z_to_bv 64 (i * W) ->
getr regs 10 = Z_to_bv 64 (top * W) -> getr regs 12 = Z_to_bv 64 (top + h) -> getr regs 15 = Z_to_bv 64 65535 ->
getr regs 11 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) -> getr regs 13 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 top ->
getr regs 9 = Z_to_bv 64 fimg -> getr regs 20 = Z_to_bv 64 bimg -> getr regs 27 = Z_to_bv 64 W ->
(forall i2 x2, top <= i2 < top + h -> (0 <= x2 < x \/ (x2 = x /\ i2 < i)) -> ~ DIFb mem0 fimg bimg (i2 * W + x2)) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_F3L) memc (seg_rom ubs2segs)) mdc) (f3l_post STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0).
Proof using HC IMG.
intros n. induction n as [|n IH]; intros i x STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 HJ K0 Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi Hx Hfuel
G14 Gi16 G26 G17 G10 G12 G15 G11 G13 G8 G9 G20 G27 HINV; [exfalso; clear - Hfuel Hi Hh Hc0 Hx; nia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
set (p := i * W + x).
assert (Hp : 0 <= p /\ p + 1 <= N) by (subst p; rewrite HN; clear - Hi Hx Hc0 Ht0 Hh Hth HW; nia).
assert (HiW : 0 <= i * W /\ i * W + W <= N /\ 0 <= top * W /\ top * W + W <= N) by (rewrite HN; clear - Hi Ht0 Hh Hth HW; nia).
set (bc := byte_at memc (fimg + p)). set (bb := byte_at memc (bimg + p)).
pose proof (byte_at_range memc (fimg + p)) as Rbc. pose proof (byte_at_range memc (bimg + p)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [fimg + p; bimg + p; bc; bb] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (fimg + p)) by (subst E; apply (Ereg_vals regs [fimg + p; bimg + p; bc; bb] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 (bimg + p)) by (subst E; apply (Ereg_vals regs [fimg + p; bimg + p; bc; bb] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 bc) by (subst E; apply (Ereg_vals regs [fimg + p; bimg + p; bc; bb] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 bb) by (subst E; apply (Ereg_vals regs [fimg + p; bimg + p; bc; bb] [] 3%nat); reflexivity).
assert (HU32 : bv_unsigned (ew E 32) = fimg + p) by (rewrite HE32; apply unsigned_lit_small; clear - Hp Hfimg0 Hfimg1 Hac; lia).
assert (HU33 : bv_unsigned (ew E 33) = bimg + p) by (rewrite HE33; apply unsigned_lit_small; clear - Hp Hbimg0 Hbimg1 Hac; lia).
assert (HE14 : ew E 14 = Z_to_bv 64 p) by (rewrite (HE 14%nat 14%bv eq_refl); exact G14).
assert (HE9 : ew E 9 = Z_to_bv 64 fimg) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE20 : ew E 20 = Z_to_bv 64 bimg) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HFA : atoms_ok E f3l_facts).
{ unfold f3l_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU32, HU33, HE34, HE35, HE14, HE9, HE20, (HE 16%nat 16%bv eq_refl), (HE 26%nat 26%bv eq_refl), (HE 17%nat 17%bv eq_refl), (HE 10%nat 10%bv eq_refl),
(HE 12%nat 12%bv eq_refl), (HE 11%nat 11%bv eq_refl), (HE 8%nat 8%bv eq_refl), (HE 27%nat 27%bv eq_refl), Gi16, G26, G17, G10, G12, G11, G8, G27.
clear - Hp Hi Hx Hc0 Ht0 Hh Hth HW HH HiW HNle Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (HCO : conds_ok E f3l_conds).
{ unfold f3l_conds. cbn [conds_ok]. split; [|exact I].
apply (cond_geu E 33 0 20 0 (bimg + p) bimg HE33 HE20); clear - Hp Hbimg0 Hbimg1 Hac; lia. }
assert (HAL : alias_ok E f3l_alias).
{ unfold f3l_alias. cbn [alias_ok]. split; [|split; [|exact I]].
- apply (alias_add E 20 14 33 bimg p HE20 HE14 HE33); clear - Hp Hbimg0 Hbimg1 Hac; lia.
- apply (alias_add E 9 14 32 fimg p HE9 HE14 HE32); clear - Hp Hfimg0 Hfimg1 Hac; lia. }
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU32.
split; [lia|]. split; [clear - Hp Hfimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(clear - Hp; lia))). }
assert (HR1 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [clear - Hp Hbimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(clear - Hp; lia))). }
assert (HPD : pairwise_disjoint E (ss_mem ss_f3l)).
{ cbn [ss_mem ss_f3l pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU32, HU33.
repeat split; try exact I. clear - Dfb Hp. lia. }
assert (HS : st_ok ubs2segs E ss_f3l (mkst regs (Z_to_bv 64 FL_F3L) memc (seg_rom ubs2segs))).
{ unfold ss_f3l. apply entry_st_ok_full; [| vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor]] | exact HPD | split; [exact HFA | split; [exact HCO | exact HAL]]].
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact G15] | intros X; discriminate X | exact G13]. }
clear HR0 HR1 HPD HFA HCO HAL.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F3L) memc (seg_rom ubs2segs))) in HJ.
assert (EXIT : forall ss ms', st_ok ubs2segs E ss ms' -> ss_pc ss = FL_F4 -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) F3_KEPT = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall z, ms_mem ms' z = memc z) ->
((exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + x)) /\ (forall i2 x2, top <= i2 < top + h -> 0 <= x2 < x -> ~ DIFb mem0 fimg bimg (i2 * W + x2))) ->
f3l_post STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 (mkCfg ms' mdc)).
{ intros ss ms' HS' Hpc Hrv Hkl Q26 HJ' K' HV. exists (ms_regs ms'), (ms_mem ms'), x.
assert (HKx : forall rr : reg, In rr F3_KEPT -> getr (ms_regs ms') rr = getr regs rr) by (intros rr Hrr; subst E; exact (regs_kept_of_st_ok ubs2segs _ ss ms' regs _ F3_KEPT HS' (env_agree_refl _ _) Hkl rr Hrr)).
split; [rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [clear - Hx; lia|].
split; [rewrite (st_ok_reg ubs2segs E ss ms' 26%bv HS'), Q26; cbn [sv_denot]; rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (HKx 10%bv ltac:(cbv; auto 50)); exact G10|].
split; [exact HKx | exact HV]. }
jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch ubs2tbl HS.
-
assert (HD : DIFb mem0 fimg bimg p).
{ rewrite branch_ne_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
unfold DIFb. rewrite <- (byte_at_KD mem0 spv memc (fimg + p) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + p) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [discriminate Hc | exact Hq]. }
clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ FL_F4. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) eq_refl HJ).
+ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
+ split; [exists i; split; [exact Hi | exact HD] | intros i2 x2 Hi2 Hx2; apply (HINV i2 x2 Hi2); left; exact Hx2].
-
assert (HNE : ~ DIFb mem0 fimg bimg p).
{ rewrite branch_ne_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
unfold DIFb. rewrite <- (byte_at_KD mem0 spv memc (fimg + p) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + p) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [intros Hne; exact (Hne Hq) | discriminate Hc]. }
assert (Hxc : x < c0).
{ destruct (Z.eq_dec x c0) as [Hxe|Hxe]; [exfalso | clear - Hx Hxe; lia].
destruct (Z.eq_dec i top) as [Hit|Hit].
+ apply HNE. subst p. rewrite Hit, Hxe. exact Hwit.
+ apply (HINV top c0 ltac:(clear - Hh Ht0; lia)); [right; split; [exact (eq_sym Hxe) | clear - Hi Hit; lia] | exact Hwit]. }
clear Hc. jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
assert (UX : forall wr : Z, U E XS3 = wr -> 0 <= wr <= 1 -> x + wr <= c0 ->
U E (SAlu ALU_AND (SAlu ALU_ADD (SOff 26 0) XS3) (SLit 65535)) = x + wr /\ U E (SAlu ALU_ADD (SOff 26 0) XS3) = x + wr).
{ intros wr Hwr Rw Rx.
assert (UA : U E (SAlu ALU_ADD (SOff 26 0) XS3) = x + wr).
{ apply (U_add_small E _ _ x wr); [apply (U_atom E 26 x); [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Hx Hc0 HW; lia] | exact Hwr | clear - Hx; lia | clear - Rw; lia | clear - Rx Hc0 HW; lia]. }
split; [| exact UA]. rewrite U_and_lit, UA by (clear; lia). apply land_ffff. clear - Hx Rw Rx Hc0 HW; lia. }
jbranch ubs2tbl HS.
+
rewrite branch_geu_U, U_and_lit, (U_atom_off E 16 i 1), (U_atom E 12 (top + h)), land_ffff in Hc
by first [rewrite (HE 16%nat 16%bv eq_refl); exact Gi16 | rewrite (HE 12%nat 12%bv eq_refl); exact G12 | clear - Hi Ht0 Hth HH Hh; lia].
assert (Hwr : top + h <= i + 1) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [discriminate Hc | exact Hl]). clear Hc.
assert (UXS : U E XS3 = 1).
{ unfold XS3. rewrite U_xor1_sltu, U_and_lit, (U_atom_off E 16 i 1), (U_atom E 12 (top + h)), land_ffff
by first [rewrite (HE 16%nat 16%bv eq_refl); exact Gi16 | rewrite (HE 12%nat 12%bv eq_refl); exact G12 | clear - Hi Ht0 Hth HH Hh; lia].
destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [exfalso; clear - Hl Hwr; lia | reflexivity]. }
destruct (UX 1 UXS ltac:(clear; lia) ltac:(clear - Hxc; lia)) as [UAND UADD].
jrun_to LAWS ubs2tbl_ok HS HJ FL_F3L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms1 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs _ F3_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssf) rq = SOff nn 0 -> ew Ef nn = wv -> getr (ms_regs msf) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg ubs2segs Ef ssf msf rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg ubs2segs Ef ssf msf rq HS), Hrq; reflexivity) end.
assert (HINV' : forall i2 x2, top <= i2 < top + h -> (0 <= x2 < x + 1 \/ (x2 = x + 1 /\ i2 < top)) -> ~ DIFb mem0 fimg bimg (i2 * W + x2)).
{ intros i2 x2 Hi2 Hx2. destruct (Z.eq_dec x2 x) as [Ex|Ex].
- destruct (Z.eq_dec i2 i) as [Ei|Ei]; [rewrite Ei, Ex; exact HNE | apply (HINV i2 x2 Hi2); right; clear - Ex Ei Hi2 Hwr Hi; lia].
- apply (HINV i2 x2 Hi2). left. clear - Hx2 Ex Hi2; lia. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH top (x + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K3) Hfi Hbi Ht0 Hh Hth Hc0 Hwit ltac:(clear - Hh Ht0; lia) ltac:(clear - Hx Hxc; lia)
ltac:(clear - Hfuel Hwr Hi Hh Hx Hxc; nia)); [| | | | | | | | | | | | | exact HINV'].
- rewrite (RGX 14%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite U_zext32_mod.
rewrite (U_add_small E _ _ (top * W) (x + 1)); [apply Z.mod_small; clear - HiW Hx Hxc Hc0 HW HNle; nia | apply (U_atom E 10 (top * W)); [rewrite (HE 10%nat 10%bv eq_refl); exact G10 | clear - HiW HNle HW; lia] | exact UAND | clear - HiW; lia | clear - Hx; lia | clear - HiW Hx Hxc Hc0 HW HNle; nia].
- apply (RG 16%bv 8%nat _ eq_refl). rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- rewrite (RGX 26%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UADD.
- apply (RG 17%bv 10%nat _ eq_refl). rewrite (HE 10%nat 10%bv eq_refl). exact G10.
- rewrite (HKR 10%bv ltac:(cbv; auto 50)). exact G10.
- rewrite (HKR 12%bv ltac:(cbv; auto 50)). exact G12.
- rewrite (RGX 15%bv (SLit 65535) eq_refl). reflexivity.
- rewrite (HKR 11%bv ltac:(cbv; auto 50)). exact G11.
- rewrite (RGX 13%bv (SLit 1) eq_refl). reflexivity.
- rewrite (HKR 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR 20%bv ltac:(cbv; auto 50)). exact G20.
- rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact G27. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q26 & Q10 & HK' & HV'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K3|]. split; [exact Hl|]. split; [exact Q26|]. split; [exact Q10|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
rewrite branch_geu_U, U_and_lit, (U_atom_off E 16 i 1), (U_atom E 12 (top + h)), land_ffff in Hc
by first [rewrite (HE 16%nat 16%bv eq_refl); exact Gi16 | rewrite (HE 12%nat 12%bv eq_refl); exact G12 | clear - Hi Ht0 Hth HH Hh; lia].
assert (Hnw : i + 1 < top + h) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [exact Hl | discriminate Hc]). clear Hc.
assert (UXS : U E XS3 = 0).
{ unfold XS3. rewrite U_xor1_sltu, U_and_lit, (U_atom_off E 16 i 1), (U_atom E 12 (top + h)), land_ffff
by first [rewrite (HE 16%nat 16%bv eq_refl); exact Gi16 | rewrite (HE 12%nat 12%bv eq_refl); exact G12 | clear - Hi Ht0 Hth HH Hh; lia].
destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [reflexivity | exfalso; clear - Hl Hnw; lia]. }
destruct (UX 0 UXS ltac:(clear; lia) ltac:(clear - Hx; lia)) as [UAND UADD]. rewrite Z.add_0_r in UAND, UADD.
jrun_to LAWS ubs2tbl_ok HS HJ FL_F3L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms1 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs _ F3_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg ubs2segs Ef ssf msf rq HS), Hrq; reflexivity) end.
assert (UROW : U E (SAlu ALU_ADD (SOff 17 0) (SOff 27 0)) = (i + 1) * W).
{ replace ((i + 1) * W) with (i * W + W) by (clear; lia).
apply (U_add_small E _ _ (i * W) W); [apply (U_atom E 17 (i * W)); [rewrite (HE 17%nat 17%bv eq_refl); exact G17 | clear - HiW HNle HW; lia]
| apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - HiW; lia | clear - HW; lia | clear - HiW HNle HW; lia]. }
assert (HiW1 : (i + 1) * W + W <= N) by (rewrite HN; clear - Hnw Hth Ht0 Hi HW; nia).
assert (HINV' : forall i2 x2, top <= i2 < top + h -> (0 <= x2 < x \/ (x2 = x /\ i2 < i + 1)) -> ~ DIFb mem0 fimg bimg (i2 * W + x2)).
{ intros i2 x2 Hi2 Hx2. destruct (Z.eq_dec i2 i) as [Ei|Ei].
- destruct (Z.eq_dec x2 x) as [Ex|Ex]; [rewrite Ei, Ex; exact HNE | apply (HINV i2 x2 Hi2); left; clear - Hx2 Ex; lia].
- apply (HINV i2 x2 Hi2). clear - Hx2 Ei; lia. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) x STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K3) Hfi Hbi Ht0 Hh Hth Hc0 Hwit ltac:(clear - Hi Hnw; lia) ltac:(clear - Hx; lia)
ltac:(clear - Hfuel; lia)); [| | | | | | | | | | | | | exact HINV'].
- rewrite (RGX 14%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite U_zext32_mod.
rewrite (U_add_small E _ _ ((i + 1) * W) x); [apply Z.mod_small; clear - HiW1 Hi Ht0 Hx Hc0 HW HNle; nia | exact UROW | exact UAND | clear - HiW1 Hi Ht0 HW; nia | clear - Hx; lia | clear - HiW1 Hi Ht0 Hx Hc0 HW HNle; nia].
- rewrite (RGX 16%bv (SOff 16 1) eq_refl). cbn [sv_denot]. rewrite (HE 16%nat 16%bv eq_refl), Gi16, unsigned_lit_small by (clear - Hi Ht0 Hth HH; lia). reflexivity.
- rewrite (RGX 26%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UADD.
- rewrite (RGX 17%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UROW.
- rewrite (HKR 10%bv ltac:(cbv; auto 50)). exact G10.
- rewrite (HKR 12%bv ltac:(cbv; auto 50)). exact G12.
- rewrite (RGX 15%bv (SLit 65535) eq_refl). reflexivity.
- rewrite (HKR 11%bv ltac:(cbv; auto 50)). exact G11.
- rewrite (RGX 13%bv (SLit 1) eq_refl). reflexivity.
- rewrite (HKR 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR 20%bv ltac:(cbv; auto 50)). exact G20.
- rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact G27. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q26 & Q10 & HK' & HV'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K3|]. split; [exact Hl|]. split; [exact Q26|]. split; [exact Q10|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
Qed.
Definition f3_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top h c0 : Z) (c' : config) : Prop :=
exists regs' mem' left,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F4) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
0 <= left <= c0 /\ getr regs' 26 = Z_to_bv 64 left /\ getr regs' 10 = Z_to_bv 64 (top * W) /\ getr regs' 22 = Z_to_bv 64 h /\
getr regs' 12 = Z_to_bv 64 (top + h) /\ getr regs' 11 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) /\
(forall r : reg, In r F3S_KEPTV -> getr regs' r = getr regs r) /\
((exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + left)) /\ (forall i2 x2, top <= i2 < top + h -> 0 <= x2 < left -> ~ DIFb mem0 fimg bimg (i2 * W + x2))).
Lemma fl_f3V : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top hrow c0 : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top <= hrow -> hrow < H -> 0 <= c0 < W -> DIFb mem0 fimg bimg (top * W + c0) ->
getr regs 19 = Z_to_bv 64 hrow -> getr regs 8 = Z_to_bv 64 top -> getr regs 21 = Z_to_bv 64 top ->
getr regs 9 = Z_to_bv 64 fimg -> getr regs 20 = Z_to_bv 64 bimg -> getr regs 27 = Z_to_bv 64 W ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_F3) memc (seg_rom ubs2segs)) mdc) (f3_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top (hrow + 1 - top) c0).
Proof using HC IMG.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc top hrow c0 HJ K0 Hfi Hbi Htop Hhr Hc0 Hwit G19 G8 G21 G9 G20 G27.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
set (h := hrow + 1 - top).
assert (Hh : 1 <= h /\ top + h <= H /\ h <= 65535) by (subst h; clear - Htop Hhr HH; lia).
assert (Hp : 0 <= top * W /\ top * W + W <= N) by (rewrite HN; clear - Htop Hhr HW; nia).
set (E := Ereg regs (map (Z_to_bv 64) [fimg + top * W] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (fimg + top * W)) by (subst E; apply (Ereg_vals regs [fimg + top * W] [] 0%nat); reflexivity).
assert (HE9 : ew E 9 = Z_to_bv 64 fimg) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE8 : ew E 8 = Z_to_bv 64 top) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE19 : ew E 19 = Z_to_bv 64 hrow) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE21 : ew E 21 = Z_to_bv 64 top) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (HE27 : ew E 27 = Z_to_bv 64 W) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (UMUL : U E (SMd M_MUL (SOff 21 0) (SOff 27 0)) = top * W).
{ apply (U_mul_small' E _ _ top W); [apply (U_atom E 21 top HE21); clear - Htop Hhr HH; lia | apply (U_atom E 27 W HE27); clear - HW; lia | clear - Htop; lia | clear - HW; lia | clear - Hp HNle HW; nia]. }
assert (UX0 : U E X0 = top * W).
{ unfold X0. rewrite U_zext32_mod, UMUL. apply Z.mod_small. clear - Hp HNle HW; lia. }
assert (HFA : facts_ok E (ss_facts ss_f3)).
{ split; [| split].
- cbn [ss_facts ss_f3 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE32, HE9, HE8, HE19, HE21, HE27, (HE 20%nat 20%bv eq_refl), G20.
clear - Hp Htop Hhr HW HH HNle Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- cbn [ss_facts ss_f3 f_conds conds_ok]. split; [|exact I].
apply (cond_geu E 32 0 9 0 (fimg + top * W) fimg HE32 HE9); clear - Hp Hfimg0 Hfimg1 HW Hac; lia.
- cbn [ss_facts ss_f3 f_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite UX0, (U_atom E 9 fimg HE9), (U_atom E 32 (fimg + top * W) HE32) by (clear - Hp Hfimg0 Hfimg1 HW Hac; lia).
apply zcanon_id. unfold M64. clear - Hp Hfimg0 Hfimg1 HW Hac; lia. }
assert (HS : st_ok ubs2segs E ss_f3 (mkst regs (Z_to_bv 64 FL_F3) memc (seg_rom ubs2segs))).
{ unfold ss_f3. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor | cbn [pairwise_disjoint]; exact I | exact HFA]. }
clear HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F3) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ FL_F3L. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs _ F3S_KEPTV HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssf) rq = SOff nn 0 -> ew Ef nn = wv -> getr (ms_regs msf) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg ubs2segs Ef ssf msf rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg ubs2segs Ef ssf msf rq HS), Hrq; reflexivity) end.
assert (Q22 : getr (ms_regs ms) 22 = Z_to_bv 64 h).
{ rewrite (RGX 22%bv _ eq_refl). eval_sr_get. apply denot_of_U'.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SLit, (U_atom E 8 top HE8), (U_atom E 19 hrow HE19) by (clear - Htop Hhr HH; lia).
subst h. unfold zcanon, M64. apply f3_hgt; [reflexivity | clear - Htop Hhr HH; lia | clear - Htop Hhr HH; lia]. }
assert (Q12 : getr (ms_regs ms) 12 = Z_to_bv 64 (top + h)).
{ rewrite (RGX 12%bv _ eq_refl). eval_sr_get. apply denot_of_U'.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SLit, (U_atom E 8 top HE8), (U_atom E 19 hrow HE19), (U_atom E 21 top HE21) by (clear - Htop Hhr HH; lia).
subst h. unfold zcanon, M64. apply f3_top_hgt; [reflexivity | reflexivity | reflexivity | clear - Htop Hhr HH; lia | clear - Htop Hhr HH; lia]. }
assert (Q11 : getr (ms_regs ms) 11 = Z_to_bv 64 (2 ^ 64 - 1 - fimg)).
{ rewrite (RGX 11%bv _ eq_refl). eval_sr_get. apply denot_of_U'. apply (U_not E 9 fimg HE9). clear - Hfimg0 Hfimg1 Hac Hp HW; lia. }
assert (Q10 : getr (ms_regs ms) 10 = Z_to_bv 64 (top * W)) by (rewrite (RGX 10%bv _ eq_refl); eval_sr_get; apply denot_of_U'; exact UMUL).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (fl_f3l (Datatypes.S (Z.to_nat (c0 * h + h))) top 0 STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K1) Hfi Hbi ltac:(clear - Htop; lia) ltac:(clear - Hh; lia) ltac:(clear - Hh; lia) Hc0 Hwit
ltac:(clear - Hh; lia) ltac:(clear - Hc0; lia) ltac:(clear - Hc0 Hh; nia)).
- rewrite (RGX 14%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite Z.add_0_r. exact UX0.
- apply (RG 16%bv 8%nat _ eq_refl). exact HE8.
- rewrite (RGX 26%bv (SLit 0) eq_refl). reflexivity.
- rewrite (RGX 17%bv _ eq_refl). eval_sr_get. rewrite denot_add0. apply denot_of_U'. exact UMUL.
- exact Q10.
- exact Q12.
- rewrite (RGX 15%bv (SLit 65535) eq_refl). reflexivity.
- exact Q11.
- rewrite (RGX 13%bv (SLit 1) eq_refl). reflexivity.
- rewrite (HKR 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR 20%bv ltac:(cbv; auto 50)). exact G20.
- rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact G27.
- intros i2 x2 Hi2 Hx2. exfalso. clear - Hi2 Hx2. lia. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q26 & Q10' & HK' & HV'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K1|]. split; [exact Hl|]. split; [exact Q26|]. split; [exact Q10'|].
split; [rewrite (HK' 22%bv ltac:(cbv; auto 50)); exact Q22|].
split; [rewrite (HK' 12%bv ltac:(cbv; auto 50)); exact Q12|].
split; [rewrite (HK' 11%bv ltac:(cbv; auto 50)); exact Q11|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). apply (HKR rr Hrr).
Qed.
Definition f3_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top h c0 : Z) (c' : config) : Prop :=
exists regs' mem' left,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F4) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
0 <= left <= c0 /\ getr regs' 26 = Z_to_bv 64 left /\ getr regs' 10 = Z_to_bv 64 (top * W) /\ getr regs' 22 = Z_to_bv 64 h /\
getr regs' 12 = Z_to_bv 64 (top + h) /\ getr regs' 11 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) /\
(forall r : reg, In r F3S_KEPT -> getr regs' r = getr regs r).
Lemma fl_f3 : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top hrow c0 : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top <= hrow -> hrow < H -> 0 <= c0 < W -> DIFb mem0 fimg bimg (top * W + c0) ->
getr regs 19 = Z_to_bv 64 hrow -> getr regs 8 = Z_to_bv 64 top -> getr regs 21 = Z_to_bv 64 top -> getr regs 9 = Z_to_bv 64 fimg ->
getr regs 20 = Z_to_bv 64 bimg -> getr regs 27 = Z_to_bv 64 W -> getr regs 2 = Z_to_bv 64 spv ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_F3) memc (seg_rom ubs2segs)) mdc) (f3_post STK sp0 FP L A mem md Lc Ac mdc regs memc top (hrow + 1 - top) c0).
Proof using HC IMG.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc top hrow c0 HJ K0 Hfi Hbi Htop Hhr Hc0 Hwit G19 G8 G21 G9 G20 G27 G2.
eapply SR_mono; [eapply (fl_f3V STK sp0 FP L A mem md Lc Ac mdc regs memc top hrow c0); eassumption |].
intros c' (regs' & mem' & left & Hc & HJ' & Hm & Hl & Q26 & Q10 & Q22 & Q12 & Q11 & HK & _).
exists regs', mem', left. repeat (split; [assumption |]).
intros r Hr. apply HK. unfold F3S_KEPT in Hr. unfold F3S_KEPTV. cbn [In] in Hr |- *. tauto.
Qed.
End b.
End S.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
