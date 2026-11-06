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
YI1h YI16 YI1z YI1k YI21 YI22 YI23
YI1j YI1s YI1t YI1l YI1n.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_zext32_add_sll : forall E a b, U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL a (SLit 32)) (SAlu ALU_SLL b (SLit 32))) (SLit 32)) = (U E a + U E b) mod 2 ^ 32.
Proof.
intros E a b. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_sll_lit by lia. rewrite U_SLit.
change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftr_div_pow2 by lia.
pose proof (U_range E a) as Ha. pose proof (U_range E b) as Hb. unfold zcanon, M64.
set (x := U E a) in *. set (y := U E b) in *.
change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
rewrite <- Zplus_mod. replace (x * 2 ^ 32 + y * 2 ^ 32) with ((x + y) * 2 ^ 32) by lia.
rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. pose proof (Z.mod_pos_bound (x + y) (2 ^ 32) ltac:(lia)). lia.
Qed.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition XS4 : sv := SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 13 1) (SLit 65535)) (SOff 21 0)) (SLit 1).
Definition AD4 (wrap : bool) : sv :=
SAlu ALU_SRL (SAlu ALU_SLL
(SAlu ALU_ADD (if wrap then SOff 10 0 else SAlu ALU_ADD (SOff 15 0) (SOff 27 0)) (SAlu ALU_AND (SAlu ALU_SUB (SOff 11 0) XS4) (SLit 65535)))
(SLit 32)) (SLit 32).
Definition f4l_alias (wrap : bool) : list (sv * sv) := [ (SAlu ALU_ADD (SOff 22 0) (AD4 wrap), SOff 32 0); (SAlu ALU_ADD (SOff 23 0) (AD4 wrap), SOff 33 0) ].
Definition f4l_facts : list (nat * afact) :=
[ (13%nat, mkAF 0 65534 0); (11%nat, mkAF 0 65534 0); (21%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65534 0); (27%nat, mkAF 1 65535 0);
(10%nat, mkAF 0 4294967295 0); (15%nat, mkAF 0 4294967295 0);
(32%nat, mkAF 4096 (CEIL_MAX - 1) 0); (33%nat, mkAF 4096 (CEIL_MAX - 1) 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ].
Definition ss_f4l (wrap : bool) : sstate :=
mkSS FL_F4L (sr_set sr_atoms 12%bv (SLit 65535))
[ YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ;
YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))] ] None
(mkFacts f4l_facts [mkAC (if wrap then BC_GEU else BC_LTU) (SAlu ALU_AND (SOff 13 1) (SLit 65535)) (SOff 21 0)] (f4l_alias wrap)).
Definition F4_KEPT : list reg := [2; 3; 4; 5; 8; 9; 10; 18; 19; 24; 22; 25; 23; 27; 26; 20]%bv.
Definition X4a : sv := SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 32)) (SAlu ALU_SLL (SOff 37 0) (SLit 32))) (SLit 32).
Definition ss_f4 : sstate :=
mkSS FL_F4 (sr_set (sr_set sr_atoms 27%bv (SOff 37 1)) 21%bv (SOff 26 0))
[ YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ;
YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))] ] None
(mkFacts [ (37%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0); (5%nat, mkAF 1 65535 0); (10%nat, mkAF 0 4294967295 0);
(32%nat, mkAF 4096 (CEIL_MAX - 1) 0); (33%nat, mkAF 4096 (CEIL_MAX - 1) 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ] []
[ (SAlu ALU_ADD (SOff 22 0) X4a, SOff 32 0); (SAlu ALU_ADD (SOff 23 0) X4a, SOff 33 0) ]).
Definition F4S_KEPT : list reg := [2; 3; 4; 5; 8; 9; 10; 18; 19; 24; 22; 25; 23; 26; 20]%bv.
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Section e.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Definition f4l_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top c0 : Z) (c' : config) : Prop :=
exists regs' mem' xr,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F4F) mem' (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
c0 <= xr < W /\ getr regs' 11 = Z_to_bv 64 xr /\
(forall r : reg, In r F4_KEPT -> getr regs' r = getr regs r).
Lemma fl_f4l : forall (n : nat) (i x : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top h c0 : Z),
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top -> 1 <= h -> top + h <= H -> 0 <= c0 < W -> DIFb mem0 fimg bimg (top * W + c0) ->
top <= i < top + h -> c0 < x < W ->
(x - c0) * h + (top + h - 1 - i) < Z.of_nat n ->
getr regs 10 = Z_to_bv 64 (top * W) -> getr regs 21 = Z_to_bv 64 (top + h) -> getr regs 12 = Z_to_bv 64 65535 -> getr regs 13 = Z_to_bv 64 i ->
getr regs 15 = Z_to_bv 64 (i * W) -> getr regs 22 = Z_to_bv 64 fimg -> getr regs 23 = Z_to_bv 64 bimg -> getr regs 27 = Z_to_bv 64 W ->
getr regs 26 = Z_to_bv 64 top -> getr regs 11 = Z_to_bv 64 x ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 FL_F4L) memc (seg_rom src2segs)) mdc) (f4l_post STK sp0 FP L A mem md Lc Ac mdc regs memc top c0).
Proof.
intros n. induction n as [|n IH]; intros i x STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 HJ K0 Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi Hx Hfuel
G10 G21 G12 G13 G15 G22 G23 G27 G26 G11; [exfalso; clear - Hfuel Hi Hh Hc0 Hx; nia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
set (wrap := top + h <=? i + 1).
set (i' := if wrap then top else i + 1). set (x' := if wrap then x - 1 else x).
assert (Hi' : top <= i' < top + h /\ c0 <= x' < W /\ (wrap = true -> top + h <= i + 1) /\ (wrap = false -> i + 1 < top + h)).
{ subst i' x' wrap. destruct (Z.leb_spec (top + h) (i + 1)) as [Hl|Hl]; (split; [| split; [| split; intros HH'; try discriminate HH']]); clear - Hi Hx Hh Hl; lia. }
destruct Hi' as (Hi' & Hx' & Hwt & Hwf).
set (p := i' * W + x').
assert (Hp : 0 <= p /\ p + 1 <= N) by (subst p; rewrite HN; clear - Hi' Hx' Hc0 Ht0 Hh Hth HW; nia).
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
assert (UXS : U E XS4 = if wrap then 1 else 0).
{ unfold XS4. rewrite U_xor1_sltu, U_and_lit, (U_atom_off E 13 i 1), (U_atom E 21 (top + h)), land_ffff
by first [rewrite (HE 13%nat 13%bv eq_refl); exact G13 | rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - Hi Ht0 Hth HH Hh; lia].
destruct wrap; [destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [exfalso; specialize (Hwt eq_refl); clear - Hwt Hl; lia | reflexivity]
| destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [reflexivity | exfalso; specialize (Hwf eq_refl); clear - Hwf Hl; lia]]. }
assert (UXm : U E (SAlu ALU_SUB (SOff 11 0) XS4) = x').
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite UXS, (U_atom E 11 x) by first [rewrite (HE 11%nat 11%bv eq_refl); exact G11 | clear - Hx Hc0 HW; lia].
subst x'. destruct wrap; (rewrite zcanon_id; [clear; lia | unfold M64; clear - Hx Hc0 HW; lia]). }
assert (UX' : U E (SAlu ALU_AND (SAlu ALU_SUB (SOff 11 0) XS4) (SLit 65535)) = x').
{ rewrite U_and_lit by (clear; lia). rewrite UXm. apply land_ffff. clear - Hx' Hc0 HW; lia. }
assert (UAD : U E (AD4 wrap) = p).
{ unfold AD4. rewrite U_zext32_mod. rewrite (U_add_small E _ _ (i' * W) x'); [apply Z.mod_small; clear - Hp HNle; subst p; lia | | exact UX' | clear - Hi' Ht0 HW; nia | clear - Hx' Hc0; lia | clear - Hp HNle; subst p; lia].
subst i'. destruct wrap.
- apply (U_atom E 10 (top * W)); [rewrite (HE 10%nat 10%bv eq_refl); exact G10 | clear - HiW HNle HW; lia].
- rewrite (U_add_small E _ _ (i * W) W); [clear; lia | apply (U_atom E 15 (i * W)); [rewrite (HE 15%nat 15%bv eq_refl); exact G15 | clear - HiW HNle HW; lia] | apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - HiW; lia | clear - HW; lia | clear - HiW HNle HW; lia]. }
assert (HFA : facts_ok E (ss_facts (ss_f4l wrap))).
{ split; [| split].
- cbn [ss_facts ss_f4l f_atoms]. unfold f4l_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU32, HU33, HE34, HE35, (HE 13%nat 13%bv eq_refl), (HE 11%nat 11%bv eq_refl), (HE 21%nat 21%bv eq_refl), (HE 26%nat 26%bv eq_refl), (HE 27%nat 27%bv eq_refl), (HE 10%nat 10%bv eq_refl), (HE 15%nat 15%bv eq_refl),
G13, G11, G21, G26, G27, G10, G15.
clear - Hp Hi Hx Hc0 Ht0 Hh Hth HW HH HiW HNle Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- cbn [ss_facts ss_f4l f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
destruct wrap; rewrite ?branch_geu_U, ?branch_ltu_U, U_and_lit, (U_atom_off E 13 i 1), (U_atom E 21 (top + h)), land_ffff
by first [rewrite (HE 13%nat 13%bv eq_refl); exact G13 | rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - Hi Ht0 Hth HH Hh; lia];
destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; cbn [negb]; first [reflexivity | exfalso; specialize (Hwt eq_refl); clear - Hwt Hl; lia | exfalso; specialize (Hwf eq_refl); clear - Hwf Hl; lia].
- cbn [ss_facts ss_f4l f_alias f4l_alias alias_ok]. split; [| split; [| exact I]].
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite UAD, (U_atom E 22 fimg), (U_atom E 32 (fimg + p) HE32); [| clear - Hp Hfimg0 Hfimg1 Hac; lia | rewrite (HE 22%nat 22%bv eq_refl); exact G22 | clear - Hp Hfimg0 Hfimg1 Hac; lia].
apply zcanon_id. unfold M64. clear - Hp Hfimg0 Hfimg1 Hac; lia.
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite UAD, (U_atom E 23 bimg), (U_atom E 33 (bimg + p) HE33); [| clear - Hp Hbimg0 Hbimg1 Hac; lia | rewrite (HE 23%nat 23%bv eq_refl); exact G23 | clear - Hp Hbimg0 Hbimg1 Hac; lia].
apply zcanon_id. unfold M64. clear - Hp Hbimg0 Hbimg1 Hac; lia. }
assert (HR0 : region_ok src2segs E memc (YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU32.
split; [lia|]. split; [clear - Hp Hfimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(clear - Hp; lia))). }
assert (HR1 : region_ok src2segs E memc (YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [clear - Hp Hbimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(clear - Hp; lia))). }
assert (HPD : pairwise_disjoint E (ss_mem (ss_f4l wrap))).
{ cbn [ss_mem ss_f4l pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU32, HU33.
repeat split; try exact I. clear - Dfb Hp. lia. }
assert (HS : st_ok src2segs E (ss_f4l wrap) (mkst regs (Z_to_bv 64 FL_F4L) memc (seg_rom src2segs))).
{ unfold ss_f4l. apply entry_st_ok_full; [| vm_compute; destruct wrap; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor]] | exact HPD | exact HFA].
apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact G12]. }
clear HR0 HR1 HPD HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F4L) memc (seg_rom src2segs))) in HJ.
assert (EXIT : forall ss ms' xr, st_ok src2segs E ss ms' -> ss_pc ss = FL_F4F -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) F4_KEPT = true ->
c0 <= xr < W -> getr (ms_regs ms') 11 = Z_to_bv 64 xr ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall z, ms_mem ms' z = memc z) ->
f4l_post STK sp0 FP L A mem md Lc Ac mdc regs memc top c0 (mkCfg ms' mdc)).
{ intros ss ms' xr HS' Hpc Hrv Hkl Hl Q11 HJ' K'. exists (ms_regs ms'), (ms_mem ms'), xr.
split; [rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hl|]. split; [exact Q11|].
intros rr Hrr. subst E. exact (regs_kept_of_st_ok src2segs _ ss ms' regs _ F4_KEPT HS' (env_agree_refl _ _) Hkl rr Hrr). }
destruct wrap.
-
jrun LAWS src2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch src2tbl HS.
+
assert (Hxc : c0 < x').
{ destruct (Z.eq_dec x' c0) as [Hxe|Hxe]; [exfalso | clear - Hx' Hxe; lia].
rewrite branch_eq_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
assert (Hit : i' = top) by reflexivity.
apply Hwit. unfold DIFb. replace (top * W + c0) with p by (subst p; rewrite Hit, Hxe; reflexivity).
rewrite <- (byte_at_KD mem0 spv memc (fimg + p) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + p) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [exact Hq | discriminate Hc]. }
clear Hc.
jrun_to LAWS src2tbl_ok HS HJ FL_F4L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs _ F4_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssf) rq = SOff nn 0 -> ew Ef nn = wv -> getr (ms_regs msf) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg src2segs Ef ssf msf rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg src2segs Ef ssf msf rq HS), Hrq; reflexivity) end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH i' x' STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K2) Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi' ltac:(clear - Hx' Hxc; lia)
ltac:(subst i' x'; cbn; specialize (Hwt eq_refl); clear - Hfuel Hwt Hi Hh Hx; nia)).
- apply (RG 10%bv 10%nat _ eq_refl). rewrite (HE 10%nat 10%bv eq_refl). exact G10.
- apply (RG 21%bv 21%nat _ eq_refl). rewrite (HE 21%nat 21%bv eq_refl). exact G21.
- rewrite (RGX 12%bv (SLit 65535) eq_refl). reflexivity.
- apply (RG 13%bv 26%nat _ eq_refl). rewrite (HE 26%nat 26%bv eq_refl). exact G26.
- apply (RG 15%bv 10%nat _ eq_refl). rewrite (HE 10%nat 10%bv eq_refl). exact G10.
- rewrite (HKR 22%bv ltac:(cbv; auto 50)). exact G22.
- rewrite (HKR 23%bv ltac:(cbv; auto 50)). exact G23.
- rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact G27.
- rewrite (HKR 26%bv ltac:(cbv; auto 50)). exact G26.
- rewrite (RGX 11%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UXm. }
cbv beta. intros c' (regs' & mem' & xr & -> & HJ' & K' & Hl & Q11 & HK'). exists regs', mem', xr.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K2|]. split; [exact Hl|]. split; [exact Q11|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
clear Hc. jrun_to LAWS src2tbl_ok HS HJ FL_F4F. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ x' HS eq_refl eq_refl ltac:(vm_compute; reflexivity) Hx'); [| exact HJ |].
* lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src2segs Ec ssc msc 11%bv HS) end. eval_sr_get. apply denot_of_U'. exact UXm.
* intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
-
jrun LAWS src2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch src2tbl HS.
+
assert (Hxc : c0 < x').
{ destruct (Z.eq_dec x' c0) as [Hxe|Hxe]; [exfalso | clear - Hx' Hxe; lia].
rewrite branch_eq_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
subst x'. cbn in Hxe. clear - Hx Hxe. lia.
}
clear Hc.
jrun_to LAWS src2tbl_ok HS HJ FL_F4L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs _ F4_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssf) rq = SOff nn 0 -> ew Ef nn = wv -> getr (ms_regs msf) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg src2segs Ef ssf msf rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg src2segs Ef ssf msf rq HS), Hrq; reflexivity) end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH i' x' STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K2) Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi' ltac:(clear - Hx' Hxc; lia)
ltac:(subst i' x'; cbn; specialize (Hwf eq_refl); clear - Hfuel Hwf Hi Hh Hx; nia)).
- apply (RG 10%bv 10%nat _ eq_refl). rewrite (HE 10%nat 10%bv eq_refl). exact G10.
- apply (RG 21%bv 21%nat _ eq_refl). rewrite (HE 21%nat 21%bv eq_refl). exact G21.
- rewrite (RGX 12%bv (SLit 65535) eq_refl). reflexivity.
- rewrite (RGX 13%bv (SOff 13 1) eq_refl). cbn [sv_denot]. rewrite (HE 13%nat 13%bv eq_refl), G13, unsigned_lit_small by (clear - Hi Ht0 Hth HH; lia). reflexivity.
- rewrite (RGX 15%bv _ eq_refl). eval_sr_get. apply denot_of_U'. cbn. rewrite (U_add_small E _ _ (i * W) W); [clear; lia | apply (U_atom E 15 (i * W)); [rewrite (HE 15%nat 15%bv eq_refl); exact G15 | clear - HiW HNle HW; lia] | apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - HiW; lia | clear - HW; lia | clear - HiW HNle HW; lia].
- rewrite (HKR 22%bv ltac:(cbv; auto 50)). exact G22.
- rewrite (HKR 23%bv ltac:(cbv; auto 50)). exact G23.
- rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact G27.
- rewrite (HKR 26%bv ltac:(cbv; auto 50)). exact G26.
- rewrite (RGX 11%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UXm. }
cbv beta. intros c' (regs' & mem' & xr & -> & HJ' & K' & Hl & Q11 & HK'). exists regs', mem', xr.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K2|]. split; [exact Hl|]. split; [exact Q11|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
clear Hc. jrun_to LAWS src2tbl_ok HS HJ FL_F4F. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ x' HS eq_refl eq_refl ltac:(vm_compute; reflexivity) Hx'); [| exact HJ |].
* lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src2segs Ec ssc msc 11%bv HS) end. eval_sr_get. apply denot_of_U'. exact UXm.
* intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
Qed.
Definition f4_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (c0 : Z) (c' : config) : Prop :=
exists regs' mem' xr,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F4F) mem' (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
c0 <= xr < W /\ getr regs' 11 = Z_to_bv 64 xr /\ getr regs' 27 = Z_to_bv 64 W /\
(forall r : reg, In r F4S_KEPT -> getr regs' r = getr regs r).
Lemma fl_f4 : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top h c0 : Z),
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top -> 1 <= h -> top + h <= H -> 0 <= c0 < W -> DIFb mem0 fimg bimg (top * W + c0) ->
getr regs 5 = Z_to_bv 64 h -> getr regs 10 = Z_to_bv 64 (top * W) -> getr regs 21 = Z_to_bv 64 top -> getr regs 22 = Z_to_bv 64 fimg -> getr regs 23 = Z_to_bv 64 bimg ->
getr regs 27 = Z_to_bv 64 W -> getr regs 26 = Z_to_bv 64 top ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 FL_F4) memc (seg_rom src2segs)) mdc) (f4_post STK sp0 FP L A mem md Lc Ac mdc regs memc c0).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 HJ K0 Hfi Hbi Ht0 Hh Hth Hc0 Hwit G5 G10 G21 G22 G23 G27 G26.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
assert (Hp : 0 <= top * W /\ top * W + W <= N) by (rewrite HN; clear - Ht0 Hh Hth HW; nia).
set (p := top * W + (W - 1)).
set (bc := byte_at memc (fimg + p)). set (bb := byte_at memc (bimg + p)).
pose proof (byte_at_range memc (fimg + p)) as Rbc. pose proof (byte_at_range memc (bimg + p)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [fimg + p; bimg + p; bc; bb; 0; W - 1] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (fimg + p)) by (subst E; apply (Ereg_vals regs [fimg + p; bimg + p; bc; bb; 0; W - 1] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 (bimg + p)) by (subst E; apply (Ereg_vals regs [fimg + p; bimg + p; bc; bb; 0; W - 1] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 bc) by (subst E; apply (Ereg_vals regs [fimg + p; bimg + p; bc; bb; 0; W - 1] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 bb) by (subst E; apply (Ereg_vals regs [fimg + p; bimg + p; bc; bb; 0; W - 1] [] 3%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 (W - 1)) by (subst E; apply (Ereg_vals regs [fimg + p; bimg + p; bc; bb; 0; W - 1] [] 5%nat); reflexivity).
assert (HU32 : bv_unsigned (ew E 32) = fimg + p) by (rewrite HE32; apply unsigned_lit_small; subst p; clear - Hp Hfimg0 Hfimg1 Hac HW; lia).
assert (HU33 : bv_unsigned (ew E 33) = bimg + p) by (rewrite HE33; apply unsigned_lit_small; subst p; clear - Hp Hbimg0 Hbimg1 Hac HW; lia).
assert (UX : U E X4a = p).
{ unfold X4a. rewrite U_zext32_add_sll, (U_atom E 10 (top * W)), (U_atom E 37 (W - 1) HE37); [| clear - HW; lia | rewrite (HE 10%nat 10%bv eq_refl); exact G10 | clear - Hp HNle HW; lia].
apply Z.mod_small. subst p. clear - Hp HNle HW; lia. }
assert (HFA : facts_ok E (ss_facts ss_f4)).
{ split; [| split; [exact I|]].
- cbn [ss_facts ss_f4 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU32, HU33, HE34, HE35, HE37, (HE 26%nat 26%bv eq_refl), (HE 5%nat 5%bv eq_refl), (HE 10%nat 10%bv eq_refl), G26, G5, G10.
clear - Hp Ht0 Hh Hth HW HH Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac HNle. subst p. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- cbn [ss_facts ss_f4 f_alias alias_ok]. split; [| split; [| exact I]].
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite UX, (U_atom E 22 fimg), (U_atom E 32 (fimg + p) HE32); [| subst p; clear - Hp Hfimg0 Hfimg1 Hac HW; lia | rewrite (HE 22%nat 22%bv eq_refl); exact G22 | subst p; clear - Hp Hfimg0 Hfimg1 Hac HW; lia].
apply zcanon_id. unfold M64. subst p; clear - Hp Hfimg0 Hfimg1 Hac HW; lia.
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite UX, (U_atom E 23 bimg), (U_atom E 33 (bimg + p) HE33); [| subst p; clear - Hp Hbimg0 Hbimg1 Hac HW; lia | rewrite (HE 23%nat 23%bv eq_refl); exact G23 | subst p; clear - Hp Hbimg0 Hbimg1 Hac HW; lia].
apply zcanon_id. unfold M64. subst p; clear - Hp Hbimg0 Hbimg1 Hac HW; lia. }
assert (HR0 : region_ok src2segs E memc (YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU32.
split; [lia|]. split; [subst p; clear - Hp Hfimg1 Hac HW; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(subst p; clear - Hp HW; lia))). }
assert (HR1 : region_ok src2segs E memc (YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [subst p; clear - Hp Hbimg1 Hac HW; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(subst p; clear - Hp HW; lia))). }
assert (HPD : pairwise_disjoint E (ss_mem ss_f4)).
{ cbn [ss_mem ss_f4 pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU32, HU33.
repeat split; try exact I. subst p. clear - Dfb Hp HW. lia. }
assert (RE : regs_ok E (sr_set (sr_set sr_atoms 27%bv (SOff 37 1)) 21%bv (SOff 26 0)) regs).
{ apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
- cbn [sv_denot]. rewrite HE37, unsigned_lit_small by (clear - HW; lia). rewrite G27. f_equal. clear; lia.
- cbn [sv_denot]. rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned. exact G21. }
assert (HS : st_ok src2segs E ss_f4 (mkst regs (Z_to_bv 64 FL_F4) memc (seg_rom src2segs))).
{ unfold ss_f4. apply entry_st_ok_full; [exact RE | vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor]] | exact HPD | exact HFA]. }
clear HR0 HR1 HPD HFA RE.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F4) memc (seg_rom src2segs))) in HJ.
jrun LAWS src2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (EXIT : forall E0 ss ms' xr, st_ok src2segs E0 ss ms' -> env_agree 32 E E0 -> ss_pc ss = FL_F4F -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) F4S_KEPT = true ->
c0 <= xr < W -> getr (ms_regs ms') 11 = Z_to_bv 64 xr -> getr (ms_regs ms') 27 = Z_to_bv 64 W ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall z, ms_mem ms' z = memc z) ->
f4_post STK sp0 FP L A mem md Lc Ac mdc regs memc c0 (mkCfg ms' mdc)).
{ intros E0 ss ms' xr HS' HA Hpc Hrv Hkl Hl Q11 Q27 HJ' K'. exists (ms_regs ms'), (ms_mem ms'), xr.
split; [rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hl|]. split; [exact Q11|]. split; [exact Q27|].
intros rr Hrr. subst E. exact (regs_kept_of_st_ok src2segs _ ss ms' regs _ F4S_KEPT HS' HA Hkl rr Hrr). }
jbranch src2tbl HS.
-
clear Hc. jrun_to LAWS src2tbl_ok HS HJ FL_F4F. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ _ (W - 1) HS (env_agree_refl _ _) eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Hc0; lia)); [| | exact HJ |].
+ reg_nowF HS ltac:(rewrite HE37, Z_to_bv_bv_unsigned; reflexivity).
+ reg_nowF HS ltac:(rewrite HE37, unsigned_lit_small by (clear - HW; lia); f_equal; clear; lia).
+ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
-
assert (Hc0p : c0 < W - 1).
{ destruct (Z.eq_dec c0 (W - 1)) as [Hz|Hz]; [exfalso | clear - Hc0 Hz; lia].
rewrite branch_ne_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
apply Hwit. unfold DIFb. rewrite Hz. fold p.
rewrite <- (byte_at_KD mem0 spv memc (fimg + p) K0) by (subst p; clear - Hp Hfimg0 Hfimg1 Hsp0 Hac HW; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + p) K0) by (subst p; clear - Hp Hbimg0 Hbimg1 Hsp0 Hac HW; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [exact Hq | discriminate Hc]. }
clear Hc.
jrun_to LAWS src2tbl_ok HS HJ FL_F4L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs _ F4S_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssf) rq = SOff nn 0 -> ew Ef nn = wv -> getr (ms_regs msf) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg src2segs Ef ssf msf rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg src2segs Ef ssf msf rq HS), Hrq; reflexivity) end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (fl_f4l (Datatypes.S (Z.to_nat ((W - 1 - c0) * h + h))) top (W - 1) STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K2) Hfi Hbi Ht0 Hh Hth Hc0 Hwit
ltac:(clear - Hh; lia) ltac:(clear - Hc0p Hc0; lia) ltac:(clear - Hc0 Hh; nia)).
- rewrite (HKR 10%bv ltac:(cbv; auto 50)). exact G10.
- rewrite (RGX 21%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite (Z.add_comm top h).
apply (U_add_small E _ _ h top); [apply (U_atom E 5 h); [rewrite (HE 5%nat 5%bv eq_refl); exact G5 | clear - Hh Hth Ht0 HH; lia] | apply (U_atom E 26 top); [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Ht0 Hth Hh HH; lia] | clear - Hh; lia | clear - Ht0; lia | clear - Ht0 Hth Hh HH; lia].
- rewrite (RGX 12%bv (SLit 65535) eq_refl). reflexivity.
- apply (RG 13%bv 26%nat _ eq_refl). rewrite (HE 26%nat 26%bv eq_refl). exact G26.
- apply (RG 15%bv 10%nat _ eq_refl). rewrite (HE 10%nat 10%bv eq_refl). exact G10.
- rewrite (HKR 22%bv ltac:(cbv; auto 50)). exact G22.
- rewrite (HKR 23%bv ltac:(cbv; auto 50)). exact G23.
- rewrite (RGX 27%bv (SOff 37 1) eq_refl). cbn [sv_denot]. rewrite HE37, unsigned_lit_small by (clear - HW; lia). f_equal. clear; lia.
- rewrite (HKR 26%bv ltac:(cbv; auto 50)). exact G26.
- apply (RG 11%bv 37%nat _ eq_refl). exact HE37. }
assert (Q27 : getr (ms_regs ms0) 27 = Z_to_bv 64 W) by (rewrite (RGX 27%bv (SOff 37 1) eq_refl); cbn [sv_denot]; rewrite HE37, unsigned_lit_small by (clear - HW; lia); f_equal; clear; lia).
cbv beta. intros c' (regs' & mem' & xr & -> & HJ' & K' & Hl & Q11 & HK'). exists regs', mem', xr.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K2|]. split; [exact Hl|]. split; [exact Q11|]. split; [rewrite (HK' 27%bv ltac:(cbv; auto 50)); exact Q27|].
intros rr Hrr. rewrite (HK' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). apply (HKR rr Hrr).
Qed.
End e.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
