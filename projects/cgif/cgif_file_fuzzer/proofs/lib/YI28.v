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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI25 YI2o YI2p YI2q YI24 YI2d YI2e YI26.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI5c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition XS3 : sv := SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 13 1) (SLit 65535)) (SOff 11 0)) (SLit 1).
Definition AD3 (wrap : bool) : sv :=
SAlu ALU_SRL (SAlu ALU_SLL
(SAlu ALU_ADD (if wrap then SOff 10 0 else SAlu ALU_ADD (SOff 15 0) (SOff 27 0)) (SAlu ALU_AND (SAlu ALU_ADD (SOff 20 0) XS3) (SLit 65535)))
(SLit 32)) (SLit 32).
Definition f3l_alias (wrap : bool) : list (sv * sv) := [ (SAlu ALU_ADD (SOff 22 0) (AD3 wrap), SOff 32 0); (SAlu ALU_ADD (SOff 23 0) (AD3 wrap), SOff 33 0) ].
Definition f3l_facts : list (nat * afact) :=
[ (13%nat, mkAF 0 65534 0); (20%nat, mkAF 0 65534 0); (11%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65534 0); (27%nat, mkAF 1 65535 0);
(10%nat, mkAF 0 4294967295 0); (15%nat, mkAF 0 4294967295 0);
(32%nat, mkAF 4096 (CEIL_MAX - 1) 0); (33%nat, mkAF 4096 (CEIL_MAX - 1) 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ].
Definition ss_f3l (wrap : bool) : sstate :=
mkSS FL_F3L (sr_set sr_atoms 12%bv (SLit 65535))
[ YP09.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ;
YP09.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))] ] None
(mkFacts f3l_facts [mkAC (if wrap then BC_GEU else BC_LTU) (SAlu ALU_AND (SOff 13 1) (SLit 65535)) (SOff 11 0)] (f3l_alias wrap)).
Definition F3_KEPT : list reg := [2; 3; 4; 5; 8; 9; 18; 19; 25; 21; 22; 24; 23; 27; 26]%bv.
Definition X0 : sv := SAlu ALU_SRL (SAlu ALU_SLL (SMd M_MUL (SOff 26 0) (SOff 27 0)) (SLit 32)) (SLit 32).
Definition ss_f3 : sstate :=
mkSS FL_F3 (sr_set (sr_set sr_atoms 21%bv (SOff 26 0)) 20%bv (SAlu ALU_ADD (SOff 26 0) (SOff 36 0)))
[ YP09.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ;
YP09.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))] ] None
(mkFacts [ (27%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65534 0); (36%nat, mkAF 0 65534 0);
(32%nat, mkAF 4096 (CEIL_MAX - 1) 0); (33%nat, mkAF 4096 (CEIL_MAX - 1) 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ] []
[ (SAlu ALU_ADD (SOff 22 0) X0, SOff 32 0); (SAlu ALU_ADD (SOff 23 0) X0, SOff 33 0) ]).
Definition F3S_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]%bv.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Section b.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Definition f3l_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top h c0 : Z) (c' : config) : Prop :=
exists regs' mem' left,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F4) mem' (seg_rom src0segs)) mdc /\
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
0 <= left <= c0 /\ getr regs' 20 = Z_to_bv 64 left /\ getr regs' 10 = Z_to_bv 64 (top * W) /\
(forall r : reg, In r F3_KEPT -> getr regs' r = getr regs r) /\
((exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + left)) /\ (forall i2 x2, top <= i2 < top + h -> 0 <= x2 < left -> ~ DIFb mem0 fimg bimg (i2 * W + x2))).
Lemma fl_f3lV : forall (n : nat) (i x : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top h c0 : Z),
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top -> 1 <= h -> top + h <= H -> 0 <= c0 < W -> DIFb mem0 fimg bimg (top * W + c0) ->
top <= i < top + h -> 0 <= x < c0 ->
(c0 - x) * h + (top + h - 1 - i) < Z.of_nat n ->
getr regs 10 = Z_to_bv 64 (top * W) -> getr regs 11 = Z_to_bv 64 (top + h) -> getr regs 12 = Z_to_bv 64 65535 -> getr regs 13 = Z_to_bv 64 i ->
getr regs 15 = Z_to_bv 64 (i * W) -> getr regs 22 = Z_to_bv 64 fimg -> getr regs 23 = Z_to_bv 64 bimg -> getr regs 27 = Z_to_bv 64 W ->
getr regs 26 = Z_to_bv 64 top -> getr regs 20 = Z_to_bv 64 x ->
(forall i2 x2, top <= i2 < top + h -> (0 <= x2 < x \/ (x2 = x /\ i2 <= i)) -> ~ DIFb mem0 fimg bimg (i2 * W + x2)) ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 FL_F3L) memc (seg_rom src0segs)) mdc) (f3l_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0).
Proof.
intros n. induction n as [|n IH]; intros i x STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 HJ K0 Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi Hx Hfuel
G10 G11 G12 G13 G15 G22 G23 G27 G26 G20 HINV; [exfalso; clear - Hfuel Hi Hh Hc0 Hx; nia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
set (wrap := top + h <=? i + 1).
set (i' := if wrap then top else i + 1). set (x' := if wrap then x + 1 else x).
assert (Hi' : top <= i' < top + h /\ 0 <= x' <= c0 /\ (wrap = true -> top + h <= i + 1) /\ (wrap = false -> i + 1 < top + h)).
{ subst i' x' wrap. destruct (Z.leb_spec (top + h) (i + 1)) as [Hl|Hl]; (split; [| split; [| split; intros HH'; try discriminate HH']]); clear - Hi Hx Hh Hl; lia. }
destruct Hi' as (Hi' & Hx' & Hwt & Hwf).
assert (HSTEP : (x' = x + 1 /\ i' = top /\ top + h <= i + 1) \/ (x' = x /\ i' = i + 1 /\ i + 1 < top + h)).
{ subst i' x' wrap. destruct (Z.leb_spec (top + h) (i + 1)) as [Hl|Hl]; [left | right]; clear - Hl; lia. }
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
assert (UXS : U E XS3 = if wrap then 1 else 0).
{ unfold XS3. rewrite U_xor1_sltu, U_and_lit, (U_atom_off E 13 i 1), (U_atom E 11 (top + h)), land_ffff
by first [rewrite (HE 13%nat 13%bv eq_refl); exact G13 | rewrite (HE 11%nat 11%bv eq_refl); exact G11 | clear - Hi Ht0 Hth HH Hh; lia].
destruct wrap; [destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [exfalso; specialize (Hwt eq_refl); clear - Hwt Hl; lia | reflexivity]
| destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [reflexivity | exfalso; specialize (Hwf eq_refl); clear - Hwf Hl; lia]]. }
assert (UX' : U E (SAlu ALU_AND (SAlu ALU_ADD (SOff 20 0) XS3) (SLit 65535)) = x').
{ rewrite U_and_lit by (clear; lia). rewrite (U_add_small E _ _ x (if wrap then 1 else 0)); [| apply (U_atom E 20 x); [rewrite (HE 20%nat 20%bv eq_refl); exact G20 | clear - Hx Hc0 HW; lia] | exact UXS | clear - Hx; lia | destruct wrap; clear; lia | destruct wrap; clear - Hx Hc0 HW; lia].
subst x'. rewrite land_ffff by (destruct wrap; clear - Hx Hc0 HW; lia). destruct wrap; clear; lia. }
assert (UAD : U E (AD3 wrap) = p).
{ unfold AD3. rewrite U_zext32_mod. rewrite (U_add_small E _ _ (i' * W) x'); [apply Z.mod_small; clear - Hp HNle; subst p; lia | | exact UX' | clear - Hi' Ht0 HW; nia | clear - Hx'; lia | clear - Hp HNle; subst p; lia].
subst i'. destruct wrap.
- apply (U_atom E 10 (top * W)); [rewrite (HE 10%nat 10%bv eq_refl); exact G10 | clear - HiW HNle HW; lia].
- rewrite (U_add_small E _ _ (i * W) W); [clear; lia | apply (U_atom E 15 (i * W)); [rewrite (HE 15%nat 15%bv eq_refl); exact G15 | clear - HiW HNle HW; lia] | apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - HiW; lia | clear - HW; lia | clear - HiW HNle HW; lia]. }
assert (HFA : facts_ok E (ss_facts (ss_f3l wrap))).
{ split; [| split].
- cbn [ss_facts ss_f3l f_atoms]. unfold f3l_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU32, HU33, HE34, HE35, (HE 13%nat 13%bv eq_refl), (HE 20%nat 20%bv eq_refl), (HE 11%nat 11%bv eq_refl), (HE 26%nat 26%bv eq_refl), (HE 27%nat 27%bv eq_refl), (HE 10%nat 10%bv eq_refl), (HE 15%nat 15%bv eq_refl),
G13, G20, G11, G26, G27, G10, G15.
clear - Hp Hi Hx Hc0 Ht0 Hh Hth HW HH HiW HNle Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- cbn [ss_facts ss_f3l f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
destruct wrap; rewrite ?branch_geu_U, ?branch_ltu_U, U_and_lit, (U_atom_off E 13 i 1), (U_atom E 11 (top + h)), land_ffff
by first [rewrite (HE 13%nat 13%bv eq_refl); exact G13 | rewrite (HE 11%nat 11%bv eq_refl); exact G11 | clear - Hi Ht0 Hth HH Hh; lia];
destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; cbn [negb]; first [reflexivity | exfalso; specialize (Hwt eq_refl); clear - Hwt Hl; lia | exfalso; specialize (Hwf eq_refl); clear - Hwf Hl; lia].
- cbn [ss_facts ss_f3l f_alias f3l_alias alias_ok]. split; [| split; [| exact I]].
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite UAD, (U_atom E 22 fimg), (U_atom E 32 (fimg + p) HE32); [| clear - Hp Hfimg0 Hfimg1 Hac; lia | rewrite (HE 22%nat 22%bv eq_refl); exact G22 | clear - Hp Hfimg0 Hfimg1 Hac; lia].
apply zcanon_id. unfold M64. clear - Hp Hfimg0 Hfimg1 Hac; lia.
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite UAD, (U_atom E 23 bimg), (U_atom E 33 (bimg + p) HE33); [| clear - Hp Hbimg0 Hbimg1 Hac; lia | rewrite (HE 23%nat 23%bv eq_refl); exact G23 | clear - Hp Hbimg0 Hbimg1 Hac; lia].
apply zcanon_id. unfold M64. clear - Hp Hbimg0 Hbimg1 Hac; lia. }
assert (HR0 : region_ok src0segs E memc (YP09.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU32.
split; [lia|]. split; [clear - Hp Hfimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(clear - Hp; lia))). }
assert (HR1 : region_ok src0segs E memc (YP09.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [clear - Hp Hbimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(clear - Hp; lia))). }
assert (HPD : pairwise_disjoint E (ss_mem (ss_f3l wrap))).
{ cbn [ss_mem ss_f3l pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU32, HU33.
repeat split; try exact I. clear - Dfb Hp. lia. }
assert (HS : st_ok src0segs E (ss_f3l wrap) (mkst regs (Z_to_bv 64 FL_F3L) memc (seg_rom src0segs))).
{ unfold ss_f3l. apply entry_st_ok_full; [| vm_compute; destruct wrap; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor]] | exact HPD | exact HFA].
apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact G12]. }
clear HR0 HR1 HPD HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F3L) memc (seg_rom src0segs))) in HJ.
assert (EXIT : forall ss ms' left, st_ok src0segs E ss ms' -> ss_pc ss = FL_F4 -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) F3_KEPT = true ->
0 <= left <= c0 -> ((exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + left)) /\ (forall i2 x2, top <= i2 < top + h -> 0 <= x2 < left -> ~ DIFb mem0 fimg bimg (i2 * W + x2))) ->
getr (ms_regs ms') 20 = Z_to_bv 64 left -> sr_get (ss_regs ss) 10%bv = SOff 10 0 ->
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall z, ms_mem ms' z = memc z) ->
f3l_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 (mkCfg ms' mdc)).
{ intros ss ms' left HS' Hpc Hrv Hkl Hl HV Q20 Q10 HJ' K'. exists (ms_regs ms'), (ms_mem ms'), left.
split; [rewrite (st_ok_mkst src0segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hl|]. split; [exact Q20|].
split; [rewrite (st_ok_reg src0segs E ss ms' 10%bv HS'), Q10; cbn [sv_denot]; rewrite Z.add_0_r, (HE 10%nat 10%bv eq_refl), G10, Z_to_bv_bv_unsigned; reflexivity|].
split; [| exact HV]. intros rr Hrr. subst E. exact (regs_kept_of_st_ok src0segs _ ss ms' regs _ F3_KEPT HS' (env_agree_refl _ _) Hkl rr Hrr). }
destruct wrap.
-
jrun LAWS src0tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch src0tbl HS.
+
assert (Hxc : x' < c0).
{ destruct (Z.eq_dec x' c0) as [Hxe|Hxe]; [exfalso | clear - Hx' Hxe; lia].
rewrite branch_eq_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
assert (Hit : i' = top) by reflexivity.
apply Hwit. unfold DIFb. replace (top * W + c0) with p by (subst p; rewrite Hit, Hxe; reflexivity).
rewrite <- (byte_at_KD mem0 spv memc (fimg + p) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + p) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [exact Hq | discriminate Hc]. }
assert (HNE : ~ DIFb mem0 fimg bimg p).
{ rewrite branch_eq_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
unfold DIFb. rewrite <- (byte_at_KD mem0 spv memc (fimg + p) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + p) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [intros Hne; exact (Hne Hq) | discriminate Hc]. }
assert (HINV' : forall i2 x2, top <= i2 < top + h -> (0 <= x2 < x' \/ (x2 = x' /\ i2 <= i')) -> ~ DIFb mem0 fimg bimg (i2 * W + x2)).
{ intros i2 x2 Hi2 Hx2. destruct (Z.eq_dec i2 i') as [Ei|Ei];
[destruct (Z.eq_dec x2 x') as [Ex|Ex]; [rewrite Ei, Ex; exact HNE | apply (HINV i2 x2 Hi2); clear - HSTEP Hx2 Hi2 Hi Ei Ex; lia]
| apply (HINV i2 x2 Hi2); clear - HSTEP Hx2 Hi2 Hi Ei; lia]. }
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ FL_F3L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs _ F3_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssf) rq = SOff nn 0 -> ew Ef nn = wv -> getr (ms_regs msf) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg src0segs Ef ssf msf rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg src0segs Ef ssf msf rq HS), Hrq; reflexivity) end.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH i' x' STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K2) Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi' ltac:(clear - Hx' Hxc; lia)
ltac:(subst i' x'; cbn; specialize (Hwt eq_refl); clear - Hfuel Hwt Hi Hh Hx; nia)).
- apply (RG 10%bv 10%nat _ eq_refl). rewrite (HE 10%nat 10%bv eq_refl). exact G10.
- apply (RG 11%bv 11%nat _ eq_refl). rewrite (HE 11%nat 11%bv eq_refl). exact G11.
- rewrite (RGX 12%bv (SLit 65535) eq_refl). reflexivity.
- apply (RG 13%bv 26%nat _ eq_refl). rewrite (HE 26%nat 26%bv eq_refl). exact G26.
- apply (RG 15%bv 10%nat _ eq_refl). rewrite (HE 10%nat 10%bv eq_refl). exact G10.
- rewrite (HKR 22%bv ltac:(cbv; auto 50)). exact G22.
- rewrite (HKR 23%bv ltac:(cbv; auto 50)). exact G23.
- rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact G27.
- rewrite (HKR 26%bv ltac:(cbv; auto 50)). exact G26.
- rewrite (RGX 20%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite (U_add_small E _ _ x 1);
[subst x'; cbn; clear; lia | apply (U_atom E 20 x); [rewrite (HE 20%nat 20%bv eq_refl); exact G20 | clear - Hx Hc0 HW; lia] | exact UXS | clear - Hx; lia | clear; lia | clear - Hx Hc0 HW; lia].
- exact HINV'. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q20 & Q10 & HK' & HV'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K2|]. split; [exact Hl|]. split; [exact Q20|]. split; [exact Q10|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
assert (HVX : (exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + x')) /\ (forall i2 x2, top <= i2 < top + h -> 0 <= x2 < x' -> ~ DIFb mem0 fimg bimg (i2 * W + x2))).
{ split; [exists i'; split; [exact Hi'|] | intros i2 x2 Hi2 Hx2; apply (HINV i2 x2 Hi2); clear - HSTEP Hx2 Hi2 Hi; lia].
rewrite branch_eq_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
change (i' * W + x') with p. unfold DIFb. rewrite <- (byte_at_KD mem0 spv memc (fimg + p) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + p) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [discriminate Hc | exact Hq]. }
clear Hc. jrun_to LAWS src0tbl_ok HS HJ FL_F4. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ x' HS eq_refl eq_refl ltac:(vm_compute; reflexivity) Hx' HVX); [| reflexivity | exact HJ |].
* lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src0segs Ec ssc msc 20%bv HS) end. eval_sr_get. apply denot_of_U'. rewrite (U_add_small E _ _ x 1);
[subst x'; cbn; clear; lia | apply (U_atom E 20 x); [rewrite (HE 20%nat 20%bv eq_refl); exact G20 | clear - Hx Hc0 HW; lia] | exact UXS | clear - Hx; lia | clear; lia | clear - Hx Hc0 HW; lia].
* intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
-
jrun LAWS src0tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch src0tbl HS.
+
assert (Hxc : x' < c0).
{ destruct (Z.eq_dec x' c0) as [Hxe|Hxe]; [exfalso | clear - Hx' Hxe; lia].
rewrite branch_eq_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
subst x'. cbn in Hxe. clear - Hx Hxe. lia.
}
assert (HNE : ~ DIFb mem0 fimg bimg p).
{ rewrite branch_eq_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
unfold DIFb. rewrite <- (byte_at_KD mem0 spv memc (fimg + p) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + p) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [intros Hne; exact (Hne Hq) | discriminate Hc]. }
assert (HINV' : forall i2 x2, top <= i2 < top + h -> (0 <= x2 < x' \/ (x2 = x' /\ i2 <= i')) -> ~ DIFb mem0 fimg bimg (i2 * W + x2)).
{ intros i2 x2 Hi2 Hx2. destruct (Z.eq_dec i2 i') as [Ei|Ei];
[destruct (Z.eq_dec x2 x') as [Ex|Ex]; [rewrite Ei, Ex; exact HNE | apply (HINV i2 x2 Hi2); clear - HSTEP Hx2 Hi2 Hi Ei Ex; lia]
| apply (HINV i2 x2 Hi2); clear - HSTEP Hx2 Hi2 Hi Ei; lia]. }
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ FL_F3L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs _ F3_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssf) rq = SOff nn 0 -> ew Ef nn = wv -> getr (ms_regs msf) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg src0segs Ef ssf msf rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg src0segs Ef ssf msf rq HS), Hrq; reflexivity) end.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH i' x' STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K2) Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi' ltac:(clear - Hx' Hxc; lia)
ltac:(subst i' x'; cbn; specialize (Hwf eq_refl); clear - Hfuel Hwf Hi Hh Hx; nia)).
- apply (RG 10%bv 10%nat _ eq_refl). rewrite (HE 10%nat 10%bv eq_refl). exact G10.
- apply (RG 11%bv 11%nat _ eq_refl). rewrite (HE 11%nat 11%bv eq_refl). exact G11.
- rewrite (RGX 12%bv (SLit 65535) eq_refl). reflexivity.
- rewrite (RGX 13%bv (SOff 13 1) eq_refl). cbn [sv_denot]. rewrite (HE 13%nat 13%bv eq_refl), G13, unsigned_lit_small by (clear - Hi Ht0 Hth HH; lia). reflexivity.
- rewrite (RGX 15%bv _ eq_refl). eval_sr_get. apply denot_of_U'. cbn. rewrite (U_add_small E _ _ (i * W) W); [clear; lia | apply (U_atom E 15 (i * W)); [rewrite (HE 15%nat 15%bv eq_refl); exact G15 | clear - HiW HNle HW; lia] | apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - HiW; lia | clear - HW; lia | clear - HiW HNle HW; lia].
- rewrite (HKR 22%bv ltac:(cbv; auto 50)). exact G22.
- rewrite (HKR 23%bv ltac:(cbv; auto 50)). exact G23.
- rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact G27.
- rewrite (HKR 26%bv ltac:(cbv; auto 50)). exact G26.
- rewrite (RGX 20%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite (U_add_small E _ _ x 0);
[subst x'; cbn; clear; lia | apply (U_atom E 20 x); [rewrite (HE 20%nat 20%bv eq_refl); exact G20 | clear - Hx Hc0 HW; lia] | exact UXS | clear - Hx; lia | clear; lia | clear - Hx Hc0 HW; lia].
- exact HINV'. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q20 & Q10 & HK' & HV'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K2|]. split; [exact Hl|]. split; [exact Q20|]. split; [exact Q10|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
assert (HVX : (exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + x')) /\ (forall i2 x2, top <= i2 < top + h -> 0 <= x2 < x' -> ~ DIFb mem0 fimg bimg (i2 * W + x2))).
{ split; [exists i'; split; [exact Hi'|] | intros i2 x2 Hi2 Hx2; apply (HINV i2 x2 Hi2); clear - HSTEP Hx2 Hi2 Hi; lia].
rewrite branch_eq_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
change (i' * W + x') with p. unfold DIFb. rewrite <- (byte_at_KD mem0 spv memc (fimg + p) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + p) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [discriminate Hc | exact Hq]. }
clear Hc. jrun_to LAWS src0tbl_ok HS HJ FL_F4. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ x' HS eq_refl eq_refl ltac:(vm_compute; reflexivity) Hx' HVX); [| reflexivity | exact HJ |].
* lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src0segs Ec ssc msc 20%bv HS) end. eval_sr_get. apply denot_of_U'. rewrite (U_add_small E _ _ x 0);
[subst x'; cbn; clear; lia | apply (U_atom E 20 x); [rewrite (HE 20%nat 20%bv eq_refl); exact G20 | clear - Hx Hc0 HW; lia] | exact UXS | clear - Hx; lia | clear; lia | clear - Hx Hc0 HW; lia].
* intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
Qed.
Definition f3_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top h c0 : Z) (c' : config) : Prop :=
exists regs' mem' left,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F4) mem' (seg_rom src0segs)) mdc /\
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
0 <= left <= c0 /\ getr regs' 20 = Z_to_bv 64 left /\ getr regs' 10 = Z_to_bv 64 (top * W) /\ getr regs' 5 = Z_to_bv 64 h /\ getr regs' 21 = Z_to_bv 64 top /\
(forall r : reg, In r F3S_KEPT -> getr regs' r = getr regs r) /\
((exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + left)) /\ (forall i2 x2, top <= i2 < top + h -> 0 <= x2 < left -> ~ DIFb mem0 fimg bimg (i2 * W + x2))).
Lemma fl_f3V : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top hrow c0 : Z),
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top <= hrow -> hrow < H -> 0 <= c0 < W -> DIFb mem0 fimg bimg (top * W + c0) ->
getr regs 21 = Z_to_bv 64 top -> getr regs 20 = Z_to_bv 64 hrow -> getr regs 22 = Z_to_bv 64 fimg -> getr regs 23 = Z_to_bv 64 bimg ->
getr regs 27 = Z_to_bv 64 W -> getr regs 26 = Z_to_bv 64 top ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 FL_F3) memc (seg_rom src0segs)) mdc) (f3_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top (hrow + 1 - top) c0).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc top hrow c0 HJ K0 Hfi Hbi Htop Hhr Hc0 Hwit G21 G20 G22 G23 G27 G26.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
set (h := hrow + 1 - top).
assert (Hh : 1 <= h /\ top + h <= H /\ h <= 65535) by (subst h; clear - Htop Hhr HH; lia).
assert (Hp : 0 <= top * W /\ top * W + W <= N) by (rewrite HN; clear - Htop Hhr HW; nia).
set (bc := byte_at memc (fimg + top * W)). set (bb := byte_at memc (bimg + top * W)).
pose proof (byte_at_range memc (fimg + top * W)) as Rbc. pose proof (byte_at_range memc (bimg + top * W)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [fimg + top * W; bimg + top * W; bc; bb; h - 1] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (fimg + top * W)) by (subst E; apply (Ereg_vals regs [fimg + top * W; bimg + top * W; bc; bb; h - 1] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 (bimg + top * W)) by (subst E; apply (Ereg_vals regs [fimg + top * W; bimg + top * W; bc; bb; h - 1] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 bc) by (subst E; apply (Ereg_vals regs [fimg + top * W; bimg + top * W; bc; bb; h - 1] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 bb) by (subst E; apply (Ereg_vals regs [fimg + top * W; bimg + top * W; bc; bb; h - 1] [] 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 (h - 1)) by (subst E; apply (Ereg_vals regs [fimg + top * W; bimg + top * W; bc; bb; h - 1] [] 4%nat); reflexivity).
assert (HU32 : bv_unsigned (ew E 32) = fimg + top * W) by (rewrite HE32; apply unsigned_lit_small; clear - Hp Hfimg0 Hfimg1 Hac HW; lia).
assert (HU33 : bv_unsigned (ew E 33) = bimg + top * W) by (rewrite HE33; apply unsigned_lit_small; clear - Hp Hbimg0 Hbimg1 Hac HW; lia).
assert (UX0 : U E X0 = top * W).
{ unfold X0. rewrite U_zext32_mod. rewrite (U_mul_small' E _ _ top W); [apply Z.mod_small; clear - Hp HNle HW; lia | apply (U_atom E 26 top); [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Htop Hhr HH; lia] | apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - Htop; lia | clear - HW; lia | clear - Hp HNle HW; lia]. }
assert (HFA : facts_ok E (ss_facts ss_f3)).
{ split; [| split; [exact I|]].
- cbn [ss_facts ss_f3 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU32, HU33, HE34, HE35, HE36, (HE 27%nat 27%bv eq_refl), (HE 26%nat 26%bv eq_refl), G27, G26.
clear - Hp Htop Hhr Hh HW HH Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- cbn [ss_facts ss_f3 f_alias alias_ok]. split; [| split; [| exact I]].
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite UX0, (U_atom E 22 fimg), (U_atom E 32 (fimg + top * W) HE32); [| clear - Hp Hfimg0 Hfimg1 Hac HW; lia | rewrite (HE 22%nat 22%bv eq_refl); exact G22 | clear - Hp Hfimg0 Hfimg1 Hac HW; lia].
apply zcanon_id. unfold M64. clear - Hp Hfimg0 Hfimg1 Hac HW; lia.
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite UX0, (U_atom E 23 bimg), (U_atom E 33 (bimg + top * W) HE33); [| clear - Hp Hbimg0 Hbimg1 Hac HW; lia | rewrite (HE 23%nat 23%bv eq_refl); exact G23 | clear - Hp Hbimg0 Hbimg1 Hac HW; lia].
apply zcanon_id. unfold M64. clear - Hp Hbimg0 Hbimg1 Hac HW; lia. }
assert (HR0 : region_ok src0segs E memc (YP09.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU32.
split; [lia|]. split; [clear - Hp Hfimg1 Hac HW; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N (top * W) HHc Hfi ltac:(clear - Hp HW; lia))). }
assert (HR1 : region_ok src0segs E memc (YP09.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [clear - Hp Hbimg1 Hac HW; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N (top * W) HHc Hbi ltac:(clear - Hp HW; lia))). }
assert (HPD : pairwise_disjoint E (ss_mem ss_f3)).
{ cbn [ss_mem ss_f3 pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU32, HU33.
repeat split; try exact I. clear - Dfb Hp HW. lia. }
assert (RE : regs_ok E (sr_set (sr_set sr_atoms 21%bv (SOff 26 0)) 20%bv (SAlu ALU_ADD (SOff 26 0) (SOff 36 0))) regs).
{ apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
- cbn [sv_denot]. rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, unsigned_lit_small by (clear - Htop Hhr HH; lia). exact G21.
- rewrite G20. symmetry. apply denot_of_U'. replace hrow with (top + (h - 1)) by (subst h; clear; lia).
apply (U_add_small E _ _ top (h - 1)); [apply (U_atom E 26 top); [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Htop Hhr HH; lia] | apply (U_atom E 36 (h - 1) HE36); clear - Hh; lia | clear - Htop; lia | clear - Hh; lia | clear - Htop Hh HH; lia]. }
assert (HS : st_ok src0segs E ss_f3 (mkst regs (Z_to_bv 64 FL_F3) memc (seg_rom src0segs))).
{ unfold ss_f3. apply entry_st_ok_full; [exact RE | vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor]] | exact HPD | exact HFA]. }
clear HR0 HR1 HPD HFA RE.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F3) memc (seg_rom src0segs))) in HJ.
jrun LAWS src0tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (EXIT : forall E0 ss ms' left, st_ok src0segs E0 ss ms' -> env_agree 32 E E0 -> ss_pc ss = FL_F4 -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) F3S_KEPT = true ->
0 <= left <= c0 -> ((exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + left)) /\ (forall i2 x2, top <= i2 < top + h -> 0 <= x2 < left -> ~ DIFb mem0 fimg bimg (i2 * W + x2))) ->
getr (ms_regs ms') 20 = Z_to_bv 64 left -> getr (ms_regs ms') 10 = Z_to_bv 64 (top * W) -> getr (ms_regs ms') 5 = Z_to_bv 64 h -> getr (ms_regs ms') 21 = Z_to_bv 64 top ->
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall z, ms_mem ms' z = memc z) ->
f3_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 (mkCfg ms' mdc)).
{ intros E0 ss ms' left HS' HA Hpc Hrv Hkl Hl HV Q20 Q10 Q5 Q21 HJ' K'. exists (ms_regs ms'), (ms_mem ms'), left.
split; [rewrite (st_ok_mkst src0segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hl|].
split; [exact Q20|]. split; [exact Q10|]. split; [exact Q5|]. split; [exact Q21|].
split; [| exact HV]. intros rr Hrr. subst E. exact (regs_kept_of_st_ok src0segs _ ss ms' regs _ F3S_KEPT HS' HA Hkl rr Hrr). }
jbranch src0tbl HS.
-
assert (HV0 : (exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + 0)) /\ (forall i2 x2, top <= i2 < top + h -> 0 <= x2 < 0 -> ~ DIFb mem0 fimg bimg (i2 * W + x2))).
{ split; [exists top; split; [clear - Hh; lia|] | intros i2 x2 _ Hx2; exfalso; clear - Hx2; lia].
rewrite branch_ne_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
rewrite Z.add_0_r. unfold DIFb. rewrite <- (byte_at_KD mem0 spv memc (fimg + top * W) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac HW; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + top * W) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac HW; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [discriminate Hc | exact Hq]. }
clear Hc. jrun_to LAWS src0tbl_ok HS HJ FL_F4. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ _ 0 HS (env_agree_refl _ _) eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(clear - Hc0; lia) HV0); [| | | | exact HJ |].
+ reg_nowF HS ltac:(reflexivity).
+ lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src0segs Ec ssc msc 10%bv HS) end. eval_sr_get. apply denot_of_U'.
apply (U_mul_small' E _ _ top W); [apply (U_atom E 26 top); [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Htop Hhr HH; lia] | apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - Htop; lia | clear - HW; lia | clear - Hp HNle HW; lia].
+ reg_nowF HS ltac:(rewrite HE36, unsigned_lit_small by (clear - Hh; lia); f_equal; clear; lia).
+ reg_nowF HS ltac:(rewrite (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity).
+ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1.
-
assert (Hc0p : 0 < c0).
{ destruct (Z.eq_dec c0 0) as [Hz|Hz]; [exfalso | clear - Hc0 Hz; lia].
rewrite branch_ne_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
apply Hwit. unfold DIFb. rewrite Hz, Z.add_0_r.
rewrite <- (byte_at_KD mem0 spv memc (fimg + top * W) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac HW; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + top * W) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac HW; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [exact Hq | discriminate Hc]. }
assert (HINV0 : forall i2 x2, top <= i2 < top + h -> (0 <= x2 < 0 \/ (x2 = 0 /\ i2 <= top)) -> ~ DIFb mem0 fimg bimg (i2 * W + x2)).
{ intros i2 x2 Hi2 Hx2. assert (Ei : i2 = top /\ x2 = 0) by (clear - Hi2 Hx2; lia). destruct Ei as [-> ->].
rewrite branch_ne_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
rewrite Z.add_0_r. unfold DIFb. rewrite <- (byte_at_KD mem0 spv memc (fimg + top * W) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac HW; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + top * W) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac HW; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [intros Hne; exact (Hne Hq) | discriminate Hc]. }
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ FL_F3L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs _ F3S_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssf) rq = SOff nn 0 -> ew Ef nn = wv -> getr (ms_regs msf) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg src0segs Ef ssf msf rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg src0segs Ef ssf msf rq HS), Hrq; reflexivity) end.
assert (Q10 : getr (ms_regs ms0) 10 = Z_to_bv 64 (top * W)).
{ rewrite (RGX 10%bv _ eq_refl). eval_sr_get. apply denot_of_U'.
apply (U_mul_small' E _ _ top W); [apply (U_atom E 26 top); [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Htop Hhr HH; lia] | apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - Htop; lia | clear - HW; lia | clear - Hp HNle HW; lia]. }
assert (Q5 : getr (ms_regs ms0) 5 = Z_to_bv 64 h).
{ rewrite (RGX 5%bv (SOff 36 1) eq_refl). cbn [sv_denot]. rewrite HE36, unsigned_lit_small by (clear - Hh; lia). f_equal. clear; lia. }
assert (Q21 : getr (ms_regs ms0) 21 = Z_to_bv 64 top) by (apply (RG 21%bv 26%nat _ eq_refl); rewrite (HE 26%nat 26%bv eq_refl); exact G26).
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (fl_f3lV (Datatypes.S (Z.to_nat (c0 * h + h))) top 0 STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K2) Hfi Hbi ltac:(clear - Htop; lia) ltac:(clear - Hh; lia) ltac:(clear - Hh; lia) Hc0 Hwit
ltac:(clear - Hh; lia) ltac:(clear - Hc0p; lia) ltac:(clear - Hc0 Hh; nia)).
- exact Q10.
- rewrite (RGX 11%bv _ eq_refl). eval_sr_get. apply denot_of_U'. replace (top + h) with ((top + 1) + (h - 1)) by (clear; lia).
apply (U_add_small E _ _ (top + 1) (h - 1)); [apply (U_atom_off E 26 top 1); [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Htop Hhr HH; lia | clear - Htop Hhr HH; lia] | apply (U_atom E 36 (h - 1) HE36); clear - Hh; lia | clear - Htop; lia | clear - Hh; lia | clear - Htop Hh HH; lia].
- rewrite (RGX 12%bv (SLit 65535) eq_refl). reflexivity.
- apply (RG 13%bv 26%nat _ eq_refl). rewrite (HE 26%nat 26%bv eq_refl). exact G26.
- rewrite (RGX 15%bv _ eq_refl). eval_sr_get. rewrite denot_add0. apply denot_of_U'.
apply (U_mul_small' E _ _ top W); [apply (U_atom E 26 top); [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Htop Hhr HH; lia] | apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - Htop; lia | clear - HW; lia | clear - Hp HNle HW; lia].
- rewrite (HKR 22%bv ltac:(cbv; auto 50)). exact G22.
- rewrite (HKR 23%bv ltac:(cbv; auto 50)). exact G23.
- rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact G27.
- rewrite (HKR 26%bv ltac:(cbv; auto 50)). exact G26.
- rewrite (RGX 20%bv (SLit 0) eq_refl). reflexivity.
- exact HINV0. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q20 & Q10' & HK' & HV'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K2|]. split; [exact Hl|]. split; [exact Q20|]. split; [exact Q10'|].
split; [rewrite (HK' 5%bv ltac:(cbv; auto 50)); exact Q5|]. split; [rewrite (HK' 21%bv ltac:(cbv; auto 50)); exact Q21|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). apply (HKR rr Hrr).
Qed.
End b.
End S.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
