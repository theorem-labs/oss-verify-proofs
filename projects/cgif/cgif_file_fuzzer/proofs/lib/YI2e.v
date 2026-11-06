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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI25 YI2o YI2p YI2q YI24 YI2d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI5c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma wrap64_nz : forall v, -256 < v < 256 -> v <> 0 -> zcanon (bv_wrap 64 v + 0) <> 0.
Proof. intros v Hv Hnz. unfold zcanon, bv_wrap, M64. cbn [bv_modulus]. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia.
intros Hm. apply (Z.mod_divide v (2 ^ 64)) in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0 \/ q <= -1 \/ q >= 1) by lia. nia. Qed.
Lemma cmpPixel_fn_range : forall cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef a b,
-256 < cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef a b < 256.
Proof.
intros. unfold cmpPixel_fn.
repeat (destruct (_ : bool); try lia). apply memcmp_spec_range.
Qed.
Lemma U_xor1_sltu : forall E a b, U E (SAlu ALU_XOR (SAlu ALU_SLTU a b) (SLit 1)) = if U E a <? U E b then 0 else 1.
Proof.
intros E a b. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
destruct (U E a <? U E b); reflexivity.
Qed.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition XaddrW (aw ai ax : nat) : sv :=
SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff ai 0) (SLit 65535)) (SOff aw 0)) (SAlu ALU_AND (SOff ax 0) (SLit 65535))) (SLit 32)) (SLit 32).
Definition Xaddr (ai ax : nat) : sv := XaddrW 25 ai ax.
Lemma U_XaddrW : forall E aw ai ax i x W, ew E ai = Z_to_bv 64 i -> ew E ax = Z_to_bv 64 x -> ew E aw = Z_to_bv 64 W ->
0 <= i < 65536 -> 0 <= x < 65536 -> 0 <= W < 65536 -> i * W + x < 2 ^ 32 -> U E (XaddrW aw ai ax) = i * W + x.
Proof.
intros E aw ai ax i x W Hi Hx HW Ri Rx RW Hs. unfold XaddrW. rewrite U_zext32_mod.
rewrite (U_add_small E _ _ (i * W) x); [apply Z.mod_small; nia | | | nia | lia | nia].
- apply (U_mul_small' E _ _ i W); [| apply (U_atom _ aw W HW); lia | lia | lia | nia].
rewrite U_and_lit, (U_atom _ ai i Hi) by lia. apply land_ffff. lia.
- rewrite U_and_lit, (U_atom _ ax x Hx) by lia. apply land_ffff. lia.
Qed.
Lemma U_Xaddr : forall E ai ax i x W, ew E ai = Z_to_bv 64 i -> ew E ax = Z_to_bv 64 x -> ew E 25 = Z_to_bv 64 W ->
0 <= i < 65536 -> 0 <= x < 65536 -> 0 <= W < 65536 -> i * W + x < 2 ^ 32 -> U E (Xaddr ai ax) = i * W + x.
Proof. intros E ai ax. exact (U_XaddrW E 25 ai ax). Qed.
Definition s3_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 22 0) (XaddrW 27 19 20), SOff 32 0); (SAlu ALU_ADD (SOff 21 0) (XaddrW 27 19 20), SOff 33 0) ].
Definition ss_s3l : sstate :=
mkSS FL_S3L (sr_set sr_atoms 24%bv (SLit 65535))
[ YP09.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ;
YP09.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))] ] None
(mkFacts [ (19%nat, mkAF 0 65534 0); (20%nat, mkAF 0 65534 0); (27%nat, mkAF 1 65535 0); (23%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65534 0);
(32%nat, mkAF 4096 (CEIL_MAX - 1) 0); (33%nat, mkAF 4096 (CEIL_MAX - 1) 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ] [] s3_alias).
Definition S3L_KEPT : list reg := [2; 3; 4; 8; 9; 18; 21; 22; 23; 26]%bv.
Definition ss_s3 : sstate :=
mkSS FL_S3 (sr_set (sr_set sr_atoms 24%bv (SLit 65535)) 14%bv (SAlu ALU_ADD (SOff 26 0) (SOff 32 0)))
[ YP09.mkRegion (Some 2%nat) 8 16 8 16 [] ; YP09.mkRegion (Some 2%nat) 88 96 88 88 [mkChunk 88 (CVal 8 (SOff 26 0))] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (32%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65534 0) ] [] []).
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Section e.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Let CMP := CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef.
Definition s3l_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top h c0 : Z) (c' : config) : Prop :=
exists regs' mem' left,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_S4L) mem' (seg_rom src0segs)) mdc /\
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
0 <= left <= c0 /\ getr regs' 20 = Z_to_bv 64 left /\ getr regs' 19 = Z_to_bv 64 (W - 1) /\
getr regs' 27 = Z_to_bv 64 top /\ getr regs' 24 = Z_to_bv 64 65535 /\ getr regs' 25 = Z_to_bv 64 W /\
(forall r : reg, In r S3L_KEPT -> getr regs' r = getr regs r) /\
((exists i2, top <= i2 < top + h /\ CMP (i2 * W + left) <> 0) /\ (forall i2 x2, top <= i2 < top + h -> 0 <= x2 < left -> CMP (i2 * W + x2) = 0)).
Lemma fl_s3lV : forall (n : nat) (i x : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top h c0 : Z),
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top -> 1 <= h -> top + h <= H -> 0 <= c0 < W -> CMP (top * W + c0) <> 0 ->
top <= i < top + h -> 0 <= x -> (x < c0 \/ (x = c0 /\ i = top)) ->
(c0 - x) * h + (top + h - 1 - i) < Z.of_nat n ->
getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 19 = Z_to_bv 64 i -> getr regs 21 = Z_to_bv 64 bimg -> getr regs 23 = Z_to_bv 64 (top + h) -> getr regs 22 = Z_to_bv 64 fimg ->
getr regs 24 = Z_to_bv 64 65535 -> getr regs 27 = Z_to_bv 64 W -> getr regs 26 = Z_to_bv 64 top -> getr regs 20 = Z_to_bv 64 x ->
(forall i2 x2, top <= i2 < top + h -> (0 <= x2 < x \/ (x2 = x /\ i2 < i)) -> CMP (i2 * W + x2) = 0) ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 FL_S3L) memc (seg_rom src0segs)) mdc) (s3l_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0).
Proof.
intros n. induction n as [|n IH]; intros i x STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 HJ K0 Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi Hx0 Hinv Hfuel
G8 G9 G18 G19 G21 G23 G22 G24 G27 G26 G20 HINV; [exfalso; clear - Hfuel Hinv Hi Hh Hc0 Hx0; nia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
assert (Hxc : x <= c0) by (clear - Hinv; lia).
assert (Hp : 0 <= i * W + x /\ i * W + x + 1 <= N) by (rewrite HN; clear - Hi Hx0 Hxc Hc0 Ht0 Hh Hth HW; nia).
set (p := i * W + x) in *.
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
assert (HX : U E (XaddrW 27 19 20) = p).
{ subst p. apply (U_XaddrW E 27 19 20 i x W); [rewrite (HE 19%nat 19%bv eq_refl); exact G19 | rewrite (HE 20%nat 20%bv eq_refl); exact G20 | rewrite (HE 27%nat 27%bv eq_refl); exact G27
| clear - Hi Ht0 Hth HH; lia | clear - Hx0 Hxc Hc0 HW; lia | clear - HW; lia | clear - Hp HNle; lia]. }
assert (HFA : facts_ok E (ss_facts ss_s3l)).
{ split; [| split; [exact I|]].
- cbn [ss_facts ss_s3l f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU32, HU33, HE34, HE35, (HE 19%nat 19%bv eq_refl), (HE 20%nat 20%bv eq_refl), (HE 27%nat 27%bv eq_refl), (HE 23%nat 23%bv eq_refl), (HE 26%nat 26%bv eq_refl), G19, G20, G27, G23, G26.
clear - Hp Hi Hx0 Hxc Hc0 Ht0 Hh Hth HW HH Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- cbn [ss_facts ss_s3l f_alias s3_alias alias_ok]. split; [| split; [| exact I]].
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite HX, (U_atom E 22 fimg), (U_atom E 32 (fimg + p) HE32); [| clear - Hp Hfimg0 Hfimg1 Hac; lia | rewrite (HE 22%nat 22%bv eq_refl); exact G22 | clear - Hp Hfimg0 Hfimg1 Hac; lia].
apply zcanon_id. unfold M64. clear - Hp Hfimg0 Hfimg1 Hac; lia.
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite HX, (U_atom E 21 bimg), (U_atom E 33 (bimg + p) HE33); [| clear - Hp Hbimg0 Hbimg1 Hac; lia | rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - Hp Hbimg0 Hbimg1 Hac; lia].
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
assert (HPD : pairwise_disjoint E (ss_mem ss_s3l)).
{ cbn [ss_mem ss_s3l pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU32, HU33.
repeat split; try exact I. clear - Dfb Hp. lia. }
assert (HS : st_ok src0segs E ss_s3l (mkst regs (Z_to_bv 64 FL_S3L) memc (seg_rom src0segs))).
{ unfold ss_s3l. apply entry_st_ok_full; [| vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor]] | exact HPD | exact HFA].
apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact G24]. }
clear HR0 HR1 HPD.
clear HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S3L) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ src0_A_cmpPixel. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha0. rewrite (HE 8%nat 8%bv eq_refl), G8 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite (HE 9%nat 9%bv eq_refl), G9 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 18%nat 18%bv eq_refl), G18 in Ha2.
jreg HS (13%bv:reg) as Ha3. rewrite HE34 in Ha3. jreg HS (14%bv:reg) as Ha4. rewrite HE35 in Ha4.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (Hbq : forall a, byte_at (ms_mem ms) a = byte_at memc a) by (intros a; unfold byte_at; rewrite (mbyte_of_eq _ _ _ _ K1); reflexivity).
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc ss_s3l].
eapply SR_bind.
{ apply (cmp_callD API IMG mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC
STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) p FL_S3R HJ (KD_eq _ _ _ _ K0 K1) ltac:(clear - Hp; lia) Ha0 Ha1 Ha2).
- rewrite Hbq. exact Ha3.
- rewrite Hbq. exact Ha4.
- rewrite Hra. apply (ret_ok_even (Z_to_bv 64 FL_S3R)). vm_compute. reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hmem2 & Hres & Hfr2). clear HJ.
assert (K2 : forall z, mem2 z = memc z) by (intros z; rewrite Hmem2; apply K1).
jafter_stretch_keep HS 36%nat regs2 mem2 CMP_CLOB FL_S3R [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor]];
(eapply (region_kept_out src0segs _ _ _ _ 0 0); [intros z _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU32, ?HU33; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU32, ?HU33; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_S3R) mem2 (seg_rom src0segs))) in HJ2.
set (E2 := havoc E 36 (map (getr regs2) CMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
jbranch src0tbl HS.
-
assert (Hne : CMP p <> 0).
{ intros Hz. rewrite branch_ne_U, U_lit, (U_atom E2 38 0) in Hc; [discriminate Hc | | clear; lia | clear; lia].
subst E2. change 38%nat with (36 + 2)%nat. rewrite (ew_havoc_new E 36 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) by (cbn; lia).
cbn [nth map CMP_CLOB]. rewrite Hres. unfold CMP in Hz. rewrite Hz. reflexivity. }
clear Hc. jrun_to LAWS src0tbl_ok HS HJ2 FL_S4L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
apply SR_ret. exists (ms_regs ms0), (ms_mem ms0), x.
split; [rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl); reflexivity|]. split; [exact HJ2|]. split; [exact K3|]. split; [clear - Hx0 Hxc; lia|].
split; [reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 20%nat 20%bv eq_refl), G20, Z_to_bv_bv_unsigned; reflexivity)|].
split; [reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl), G27, unsigned_lit_small by (clear - HW; lia); reflexivity)|].
split; [reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity)|].
split; [reg_nowF HS ltac:(reflexivity)|].
split; [reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl), G27, Z_to_bv_bv_unsigned; reflexivity)|].
split; [intros rr Hrr; subst E E2; lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf => exact (regs_kept_of_st_ok src0segs Ef ssf msf regs _ S3L_KEPT HS EA1 ltac:(vm_compute; reflexivity) rr Hrr) end|].
split; [exists i; split; [exact Hi | exact Hne] | intros i2 x2 Hi2 Hx2; apply (HINV i2 x2 Hi2); left; exact Hx2].
-
assert (Hz : CMP p = 0).
{ destruct (Z.eq_dec (CMP p) 0) as [Hz|Hnz]; [exact Hz | exfalso].
rewrite branch_ne_U, U_lit, U_SOff in Hc by (clear; lia). subst E2. change 38%nat with (36 + 2)%nat in Hc.
rewrite (ew_havoc_new E 36 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) in Hc by (cbn; lia). cbn [nth map CMP_CLOB] in Hc. rewrite Hres, Z_to_bv_unsigned in Hc.
pose proof (cmpPixel_fn_range cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef (byte_at mem0 (fimg + p)) (byte_at mem0 (bimg + p))) as Rr.
pose proof (wrap64_nz _ Rr Hnz) as X. destruct (Z.eqb_spec (zcanon (bv_wrap 64 (CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef p) + 0)) 0) as [Hq|Hq]; [exact (X Hq) | discriminate Hc]. }
clear Hc.
assert (Hxlt : x < c0) by (destruct Hinv as [Hl | [Hxe Hie]]; [exact Hl | exfalso; apply Hwit; subst p; rewrite <- Hxe, <- Hie; exact Hz]).
jrun LAWS src0tbl_ok HS HJ2. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
jbranch src0tbl HS.
+
rewrite branch_geu_U, (U_atom_off E2 19 i 1), (U_atom E2 23 (top + h)) in Hc
by first [subst E2; ew_havocA; first [rewrite (HE 19%nat 19%bv eq_refl); exact G19 | rewrite (HE 23%nat 23%bv eq_refl); exact G23] | clear - Hi Ht0 Hth HH Hh; lia].
assert (Hwrap : i + 1 = top + h) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [discriminate Hc | clear - Hl Hi; lia]). clear Hc.
assert (HINVw : forall i2 x2, top <= i2 < top + h -> (0 <= x2 < x + 1 \/ (x2 = x + 1 /\ i2 < top)) -> CMP (i2 * W + x2) = 0).
{ intros i2 x2 Hi2 Hx2. destruct (Z.eq_dec i2 i) as [Ei|Ei];
[destruct (Z.eq_dec x2 x) as [Ex|Ex]; [rewrite Ei, Ex; exact Hz | apply (HINV i2 x2 Hi2); clear - Hx2 Hi2 Hi Ei Ex Hwrap; lia]
| apply (HINV i2 x2 Hi2); clear - Hx2 Hi2 Hi Ei Hwrap; lia]. }
jrun_to LAWS src0tbl_ok HS HJ2 FL_S3L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K4 : forall z, ms_mem ms1 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs _ (27%bv :: S3L_KEPT) HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH top (x + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ2 (KD_eq _ _ _ _ K0 K4) Hfi Hbi Ht0 Hh Hth Hc0 Hwit
ltac:(clear - Hh; lia) ltac:(clear - Hx0; lia) ltac:(clear - Hxlt; lia) ltac:(clear - Hfuel Hwrap Hxlt Hh; nia)).
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity).
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- rewrite (HKR 22%bv ltac:(cbv; auto 20)). exact G22.
- reg_nowF HS ltac:(reflexivity).
- rewrite (HKR 27%bv ltac:(cbv; auto 20)). exact G27.
- rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact G26.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src0segs Ec ssc msc 20%bv HS) end. eval_sr_get. apply denot_of_U'.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_xor1_sltu, (U_atom_off E2 19 i 1), (U_atom E2 23 (top + h)), (U_atom E2 20 x)
by first [subst E2; ew_havocA; first [rewrite (HE 19%nat 19%bv eq_refl); exact G19 | rewrite (HE 23%nat 23%bv eq_refl); exact G23 | rewrite (HE 20%nat 20%bv eq_refl); exact G20] | clear - Hi Ht0 Hth HH Hh Hx0 Hxc Hc0 HW; lia].
destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [clear - Hl Hwrap; lia|]. apply zcanon_id. unfold M64. clear - Hx0 Hxc Hc0 HW; lia.
- exact HINVw. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q20 & Q19 & Q27 & Q24 & Q25 & HK' & HV'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K4|]. split; [exact Hl|]. split; [exact Q20|]. split; [exact Q19|]. split; [exact Q27|]. split; [exact Q24|]. split; [exact Q25|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr (or_intror Hrr)).
+
rewrite branch_geu_U, (U_atom_off E2 19 i 1), (U_atom E2 23 (top + h)) in Hc
by first [subst E2; ew_havocA; first [rewrite (HE 19%nat 19%bv eq_refl); exact G19 | rewrite (HE 23%nat 23%bv eq_refl); exact G23] | clear - Hi Ht0 Hth HH Hh; lia].
assert (Hdown : i + 1 < top + h) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [exact Hl | discriminate Hc]). clear Hc.
assert (HINVd : forall i2 x2, top <= i2 < top + h -> (0 <= x2 < x \/ (x2 = x /\ i2 < i + 1)) -> CMP (i2 * W + x2) = 0).
{ intros i2 x2 Hi2 Hx2. destruct (Z.eq_dec i2 i) as [Ei|Ei];
[destruct (Z.eq_dec x2 x) as [Ex|Ex]; [rewrite Ei, Ex; exact Hz | apply (HINV i2 x2 Hi2); clear - Hx2 Hi2 Hi Ei Ex Hdown; lia]
| apply (HINV i2 x2 Hi2); clear - Hx2 Hi2 Hi Ei Hdown; lia]. }
jrun_to LAWS src0tbl_ok HS HJ2 FL_S3L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K4 : forall z, ms_mem ms1 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs _ (27%bv :: S3L_KEPT) HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) x STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ2 (KD_eq _ _ _ _ K0 K4) Hfi Hbi Ht0 Hh Hth Hc0 Hwit
ltac:(clear - Hi Hdown; lia) Hx0 ltac:(left; exact Hxlt) ltac:(clear - Hfuel Hdown Hxlt Hh Hi; nia)).
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 19%nat 19%bv eq_refl), G19, unsigned_lit_small by (clear - Hi Ht0 Hth HH; lia); reflexivity).
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- rewrite (HKR 22%bv ltac:(cbv; auto 20)). exact G22.
- reg_nowF HS ltac:(reflexivity).
- rewrite (HKR 27%bv ltac:(cbv; auto 20)). exact G27.
- rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact G26.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src0segs Ec ssc msc 20%bv HS) end. eval_sr_get. apply denot_of_U'.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_xor1_sltu, (U_atom_off E2 19 i 1), (U_atom E2 23 (top + h)), (U_atom E2 20 x)
by first [subst E2; ew_havocA; first [rewrite (HE 19%nat 19%bv eq_refl); exact G19 | rewrite (HE 23%nat 23%bv eq_refl); exact G23 | rewrite (HE 20%nat 20%bv eq_refl); exact G20] | clear - Hi Ht0 Hth HH Hh Hx0 Hxc Hc0 HW; lia].
destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [| clear - Hl Hdown; lia]. rewrite Z.add_0_r. apply zcanon_id. unfold M64. clear - Hx0 Hxc Hc0 HW; lia.
- exact HINVd. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q20 & Q19 & Q27 & Q24 & Q25 & HK' & HV'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K4|]. split; [exact Hl|]. split; [exact Q20|]. split; [exact Q19|]. split; [exact Q27|]. split; [exact Q24|]. split; [exact Q25|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr (or_intror Hrr)).
Qed.
Definition S3_KEPT : list reg := [2; 3; 4; 8; 9; 18; 21; 22; 26]%bv.
Definition s3_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (top hrow c0 : Z) (c' : config) : Prop :=
exists regs' mem' left,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_S4L) mem' (seg_rom src0segs)) mdc /\
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KD mem0 spv mem' /\ word_mem src0segs mem' (spv + 8) (hrow + 1 - top) /\
0 <= left <= c0 /\ getr regs' 20 = Z_to_bv 64 left /\ getr regs' 19 = Z_to_bv 64 (W - 1) /\
getr regs' 27 = Z_to_bv 64 top /\ getr regs' 24 = Z_to_bv 64 65535 /\ getr regs' 25 = Z_to_bv 64 W /\ getr regs' 23 = Z_to_bv 64 (hrow + 1) /\
(forall r : reg, In r S3_KEPT -> getr regs' r = getr regs r) /\
((exists i2, top <= i2 < top + (hrow + 1 - top) /\ CMP (i2 * W + left) <> 0) /\ (forall i2 x2, top <= i2 < top + (hrow + 1 - top) -> 0 <= x2 < left -> CMP (i2 * W + x2) = 0)).
Lemma fl_s3V : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top hrow c0 : Z),
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
spv = sp0 - 272 -> 272 <= STK -> 0 <= top <= hrow -> hrow < H -> 0 <= c0 < W -> CMP (top * W + c0) <> 0 ->
word_mem src0segs memc (spv + 88) top ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 21 = Z_to_bv 64 bimg -> getr regs 22 = Z_to_bv 64 fimg -> getr regs 24 = Z_to_bv 64 65535 -> getr regs 27 = Z_to_bv 64 W ->
getr regs 26 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 (hrow + 1) ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 FL_S3) memc (seg_rom src0segs)) mdc) (s3_postV STK sp0 FP L A mem md Lc Ac mdc regs top hrow c0).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc top hrow c0 HJ K0 Hfi Hbi Hspv HSTK Htop Hhr Hc0 Hwit W88 G2 G8 G9 G18 G21 G22 G24 G27 G26 G14.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
set (h := hrow + 1 - top).
assert (Hh : 1 <= h /\ top + h <= H /\ h <= 65535) by (subst h; clear - Htop Hhr HH; lia).
set (E := Ereg regs (map (Z_to_bv 64) [h] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 h) by (subst E; apply (Ereg_vals regs [h] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (Hstw : forall a, spv <= a < spv + 88 -> writable_at src0segs memc a).
{ intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hw) & _). apply Hw. clear - Ha Hspv HSTK. lia. }
assert (HR : region_ok src0segs E memc (YP09.mkRegion (Some 2%nat) 8 16 8 16 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | constructor]. }
assert (HR1 : region_ok src0segs E memc (YP09.mkRegion (Some 2%nat) 88 96 88 88 [mkChunk 88 (CVal 8 (SOff 26 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia |]. constructor; [|constructor].
eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 26%nat 26%bv eq_refl), G26, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W88]. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 1 65535 0); (32%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65534 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE32, (HE 27%nat 27%bv eq_refl), (HE 26%nat 26%bv eq_refl), G27, G26.
rewrite !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. clear - Hsp0 Hsp1 Hsp16 HW HH Htop Hhr Hh Hac. repeat split; lia. }
assert (RE : regs_ok E (sr_set (sr_set sr_atoms 24%bv (SLit 65535)) 14%bv (SAlu ALU_ADD (SOff 26 0) (SOff 32 0))) regs).
{ apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact G24] | intros X; discriminate X |].
rewrite G14. symmetry. apply denot_of_U'. replace (hrow + 1) with (top + h) by (subst h; clear; lia). apply (U_add_small E _ _ top h); [apply (U_atom E 26 top); [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | lia] | apply (U_atom E 32 h HE32); lia | lia | lia | lia]. }
assert (HPD : pairwise_disjoint E (ss_mem ss_s3)).
{ cbn [ss_mem ss_s3 pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2. repeat split; try exact I; lia. }
assert (HS : st_ok src0segs E ss_s3 (mkst regs (Z_to_bv 64 FL_S3) memc (seg_rom src0segs))).
{ unfold ss_s3. apply entry_st_ok_full; [exact RE | vm_compute; reflexivity | constructor; [exact HR | constructor; [exact HR1 | constructor]] | exact HPD | split; [exact HFA | split; exact I]]. }
clear HR HR1 HFA RE HPD.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S3) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ FL_S3L. { eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia | apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]]. }
cbn [ms_mem mkst] in HF.
assert (K1 : KD mem0 spv (ms_mem ms)).
{ apply (KD_frame _ _ _ _ K0). intros a Ha Hna1 Hna2 Hna3. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | [<- | []]]; cbn [r_base r_wlo r_whi base_val]; rewrite HU2; clear - Hna1; lia. }
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks src0segs E ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs;
pose proof (regs_kept_of_st_ok src0segs E ssx msx regs _ (27%bv :: S3_KEPT) HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg src0segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg src0segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (W8 : word_mem src0segs (ms_mem ms) (spv + 8) h).
{ apply (chunk_word E _ _ 8 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 8 (CVal 8 (SOff 32 0))) ltac:(cbn [In]; tauto))); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, Z_to_bv_bv_unsigned; reflexivity | clear - Hh; lia]. }
assert (Q23 : getr (ms_regs ms) 23 = Z_to_bv 64 (hrow + 1)).
{ rewrite (RGX 23%bv _ eq_refl). eval_sr_get. apply denot_of_U'. replace (hrow + 1) with (top + h) by (subst h; clear; lia).
apply (U_add_small E _ _ top h); [apply (U_atom E 26 top); [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | lia] | apply (U_atom E 32 h HE32); lia | lia | lia | lia]. }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (fl_s3lV (Datatypes.S (Z.to_nat (c0 * h + h))) top 0 STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ K1 Hfi Hbi ltac:(clear - Htop; lia) ltac:(clear - Hh; lia) ltac:(clear - Hh; lia) Hc0 Hwit
ltac:(clear - Hh; lia) ltac:(clear; lia) ltac:(clear - Hc0; lia) ltac:(clear - Hc0 Hh; nia)).
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- apply (RG 19%bv 26%nat _ eq_refl). rewrite (HE 26%nat 26%bv eq_refl). exact G26.
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite Q23. f_equal. subst h; clear; lia.
- rewrite (HKR 22%bv ltac:(cbv; auto 20)). exact G22.
- rewrite (RGX 24%bv (SLit 65535) eq_refl). reflexivity.
- rewrite (HKR 27%bv ltac:(cbv; auto 20)). exact G27.
- rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact G26.
- rewrite (RGX 20%bv (SLit 0) eq_refl). reflexivity.
- intros i2 x2 Hi2 Hx2; exfalso; clear - Hi2 Hx2; lia. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q20 & Q19 & Q27 & Q24 & Q25 & HK' & HV'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact (KD_eq _ _ _ _ K1 K')|]. split; [subst h; intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K'); apply W8; exact Hk|].
split; [exact Hl|]. split; [exact Q20|]. split; [exact Q19|]. split; [exact Q27|]. split; [exact Q24|]. split; [exact Q25|]. split; [rewrite (HK' 23%bv ltac:(cbv; auto 20)); exact Q23|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). apply (HKR rr (or_intror Hrr)).
Qed.
End e.
End S.
End d.
