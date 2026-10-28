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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2o UI2p UI2q UI24 UI2d UI2e UI26 UI28.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma U_zext32_add_sll : forall E a b, U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL a (SLit 32)) (SAlu ALU_SLL b (SLit 32))) (SLit 32)) = (U E a + U E b) mod 2 ^ 32.
Proof using.
intros E a b. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_sll_lit by lia. rewrite U_SLit.
change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftr_div_pow2 by lia.
pose proof (U_range E a) as Ha. pose proof (U_range E b) as Hb. unfold zcanon, M64.
set (x := U E a) in *. set (y := U E b) in *.
change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
rewrite <- Zplus_mod. replace (x * 2 ^ 32 + y * 2 ^ 32) with ((x + y) * 2 ^ 32) by lia.
rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. pose proof (Z.mod_pos_bound (x + y) (2 ^ 32) ltac:(lia)). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma f4_wm1 : forall w k s, k mod 2 ^ 64 = 2 ^ 64 - 2 ^ 48 -> s = 48 -> 1 <= w <= 65535 ->
Z.shiftr ((Z.shiftl w s mod 2 ^ 64 + k mod 2 ^ 64) mod 2 ^ 64) s mod 2 ^ 64 = w - 1.
Proof using.
intros w k s Hk Hs Hw. rewrite Hk, Hs, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. lia.
Qed.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition XS4 : sv := SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 16 1) (SLit 65535)) (SOff 12 0)) (SLit 1).
Definition f4l_facts : list (nat * afact) :=
[ (5%nat, mkAF 0 99999999 0); (16%nat, mkAF 0 65534 0); (13%nat, mkAF 0 65534 0); (17%nat, mkAF 0 99999999 0);
(10%nat, mkAF 0 99999999 0); (12%nat, mkAF 1 65535 0); (11%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 4097) 0);
(14%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 4097) 0);
(8%nat, mkAF 0 65534 0); (9%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 4096 CEIL_MAX 0); (27%nat, mkAF 1 65535 0);
(32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 4096 CEIL_MAX 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ].
Definition f4l_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 20 0) (SOff 5 0), SOff 33 0); (SAlu ALU_ADD (SOff 9 0) (SOff 5 0), SOff 32 0) ].
Definition ss_f4l : sstate :=
mkSS FL_F4L (sr_set sr_atoms 15%bv (SLit 65535))
[ YP09.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ;
YP09.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))] ] None
(mkFacts f4l_facts [] f4l_alias).
Definition F4_KEPT : list reg := [2; 3; 4; 8; 9; 10; 11; 12; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition X4 : sv := SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 27 0) (SLit 48)) (SLit (- 2 ^ 48))) (SLit 48))) (SLit 32)) (SLit 32).
Definition ss_f4 : sstate :=
mkSS FL_F4 sr_atoms [] None
(mkFacts [ (10%nat, mkAF 0 99999999 0); (11%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 4097) 0); (12%nat, mkAF 1 65535 0);
(8%nat, mkAF 0 65534 0); (9%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 4096 CEIL_MAX 0); (27%nat, mkAF 1 65535 0) ]
[ mkAC BC_GEU (SOff 11 0) X4 ] []).
Definition F4S_KEPT : list reg := [2; 3; 4; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Section e.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Definition f4l_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top h c0 : Z) (c' : config) : Prop :=
exists regs' mem' xr,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F4F) mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
c0 <= xr < W /\ getr regs' 13 = Z_to_bv 64 xr /\
(forall r : reg, In r F4_KEPT -> getr regs' r = getr regs r) /\
((exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + xr)) /\ (forall i2 x2, top <= i2 < top + h -> xr < x2 < W -> ~ DIFb mem0 fimg bimg (i2 * W + x2))).
Lemma fl_f4lV : forall (n : nat) (i x : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top h c0 : Z),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top -> 1 <= h -> top + h <= H -> 0 <= c0 < W -> DIFb mem0 fimg bimg (top * W + c0) ->
top <= i < top + h -> c0 <= x < W ->
(x - c0) * h + (top + h - 1 - i) < Z.of_nat n ->
getr regs 5 = Z_to_bv 64 (i * W + x) -> getr regs 16 = Z_to_bv 64 i -> getr regs 13 = Z_to_bv 64 x -> getr regs 17 = Z_to_bv 64 (i * W) ->
getr regs 10 = Z_to_bv 64 (top * W) -> getr regs 12 = Z_to_bv 64 (top + h) -> getr regs 15 = Z_to_bv 64 65535 ->
getr regs 11 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) -> getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1 - bimg) -> getr regs 8 = Z_to_bv 64 top ->
getr regs 9 = Z_to_bv 64 fimg -> getr regs 20 = Z_to_bv 64 bimg -> getr regs 27 = Z_to_bv 64 W ->
(forall i2 x2, top <= i2 < top + h -> (x < x2 < W \/ (x2 = x /\ i2 < i)) -> ~ DIFb mem0 fimg bimg (i2 * W + x2)) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 FL_F4L) memc (seg_rom ubs0segs)) mdc) (f4l_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0).
Proof using HC IMG.
intros n. induction n as [|n IH]; intros i x STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 HJ K0 Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi Hx Hfuel
G5 Gi16 G13 G17 G10 G12 G15 G11 G14 G8 G9 G20 G27 HINV; [exfalso; clear - Hfuel Hi Hh Hc0 Hx; nia|].
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
assert (HE5 : ew E 5 = Z_to_bv 64 p) by (rewrite (HE 5%nat 5%bv eq_refl); exact G5).
assert (HE9 : ew E 9 = Z_to_bv 64 fimg) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE20 : ew E 20 = Z_to_bv 64 bimg) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HFA : atoms_ok E f4l_facts).
{ unfold f4l_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU32, HU33, HE34, HE35, HE5, HE9, HE20, (HE 16%nat 16%bv eq_refl), (HE 13%nat 13%bv eq_refl), (HE 17%nat 17%bv eq_refl), (HE 10%nat 10%bv eq_refl),
(HE 12%nat 12%bv eq_refl), (HE 11%nat 11%bv eq_refl), (HE 14%nat 14%bv eq_refl), (HE 8%nat 8%bv eq_refl), (HE 27%nat 27%bv eq_refl), Gi16, G13, G17, G10, G12, G11, G14, G8, G27.
clear - Hp Hi Hx Hc0 Ht0 Hh Hth HW HH HiW HNle Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (HAL : alias_ok E f4l_alias).
{ unfold f4l_alias. cbn [alias_ok]. split; [|split; [|exact I]].
- apply (alias_add E 20 5 33 bimg p HE20 HE5 HE33); clear - Hp Hbimg0 Hbimg1 Hac; lia.
- apply (alias_add E 9 5 32 fimg p HE9 HE5 HE32); clear - Hp Hfimg0 Hfimg1 Hac; lia. }
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU32.
split; [lia|]. split; [clear - Hp Hfimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(clear - Hp; lia))). }
assert (HR1 : region_ok ubs0segs E memc (YP09.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [clear - Hp Hbimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(clear - Hp; lia))). }
assert (HPD : pairwise_disjoint E (ss_mem ss_f4l)).
{ cbn [ss_mem ss_f4l pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU32, HU33.
repeat split; try exact I. clear - Dfb Hp. lia. }
assert (HS : st_ok ubs0segs E ss_f4l (mkst regs (Z_to_bv 64 FL_F4L) memc (seg_rom ubs0segs))).
{ unfold ss_f4l. apply entry_st_ok_full; [| vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor]] | exact HPD | split; [exact HFA | split; [exact I | exact HAL]]].
apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact G15]. }
clear HR0 HR1 HPD HFA HAL.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F4L) memc (seg_rom ubs0segs))) in HJ.
assert (EXIT : forall ss ms', st_ok ubs0segs E ss ms' -> ss_pc ss = FL_F4F -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) F4_KEPT = true -> sr_get (ss_regs ss) 13%bv = SOff 13 0 ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall z, ms_mem ms' z = memc z) ->
((exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + x)) /\ (forall i2 x2, top <= i2 < top + h -> x < x2 < W -> ~ DIFb mem0 fimg bimg (i2 * W + x2))) ->
f4l_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 (mkCfg ms' mdc)).
{ intros ss ms' HS' Hpc Hrv Hkl Q13 HJ' K' HV. exists (ms_regs ms'), (ms_mem ms'), x.
split; [rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|]. split; [exact Hx|].
split; [rewrite (st_ok_reg ubs0segs E ss ms' 13%bv HS'), Q13; cbn [sv_denot]; rewrite Z.add_0_r, (HE 13%nat 13%bv eq_refl), G13, Z_to_bv_bv_unsigned; reflexivity|].
split; [| exact HV]. intros rr Hrr. subst E. exact (regs_kept_of_st_ok ubs0segs _ ss ms' regs _ F4_KEPT HS' (env_agree_refl _ _) Hkl rr Hrr). }
jrun LAWS ubs0tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
jbranch ubs0tbl HS.
-
assert (HD : DIFb mem0 fimg bimg p).
{ rewrite branch_ne_U, (U_atom E 34 bc HE34), (U_atom E 35 bb HE35) in Hc by (clear - Rbc Rbb; lia).
unfold DIFb. rewrite <- (byte_at_KD mem0 spv memc (fimg + p) K0) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac; lia).
rewrite <- (byte_at_KD mem0 spv memc (bimg + p) K0) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac; lia).
fold bc bb. destruct (Z.eqb_spec bc bb) as [Hq|Hq]; [discriminate Hc | exact Hq]. }
clear Hc. jrun_to LAWS ubs0tbl_ok HS HJ FL_F4F. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
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
assert (Hxc : c0 < x).
{ destruct (Z.eq_dec x c0) as [Hxe|Hxe]; [exfalso | clear - Hx Hxe; lia].
destruct (Z.eq_dec i top) as [Hit|Hit].
+ apply HNE. subst p. rewrite Hit, Hxe. exact Hwit.
+ apply (HINV top c0 ltac:(clear - Hh Ht0; lia)); [right; split; [exact (eq_sym Hxe) | clear - Hi Hit; lia] | exact Hwit]. }
clear Hc. jrun LAWS ubs0tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K2 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K1. }
clear HF HG.
assert (UX : forall wr : Z, U E XS4 = wr -> 0 <= wr <= 1 -> c0 <= x - wr ->
U E (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) XS4) (SLit 65535)) = x - wr /\ U E (SAlu ALU_SUB (SOff 13 0) XS4) = x - wr).
{ intros wr Hwr Rw Rx.
assert (UA : U E (SAlu ALU_SUB (SOff 13 0) XS4) = x - wr).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite Hwr, (U_atom E 13 x) by first [rewrite (HE 13%nat 13%bv eq_refl); exact G13 | clear - Hx Hc0 HW; lia].
apply zcanon_id. unfold M64. clear - Rx Rw Hc0 Hx HW; lia. }
split; [| exact UA]. rewrite U_and_lit, UA by (clear; lia). apply land_ffff. clear - Hx Rw Rx Hc0 HW; lia. }
jbranch ubs0tbl HS.
+
rewrite branch_geu_U, U_and_lit, (U_atom_off E 16 i 1), (U_atom E 12 (top + h)), land_ffff in Hc
by first [rewrite (HE 16%nat 16%bv eq_refl); exact Gi16 | rewrite (HE 12%nat 12%bv eq_refl); exact G12 | clear - Hi Ht0 Hth HH Hh; lia].
assert (Hwr : top + h <= i + 1) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [discriminate Hc | exact Hl]). clear Hc.
assert (UXS : U E XS4 = 1).
{ unfold XS4. rewrite U_xor1_sltu, U_and_lit, (U_atom_off E 16 i 1), (U_atom E 12 (top + h)), land_ffff
by first [rewrite (HE 16%nat 16%bv eq_refl); exact Gi16 | rewrite (HE 12%nat 12%bv eq_refl); exact G12 | clear - Hi Ht0 Hth HH Hh; lia].
destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [exfalso; clear - Hl Hwr; lia | reflexivity]. }
destruct (UX 1 UXS ltac:(clear; lia) ltac:(clear - Hxc; lia)) as [UAND UADD].
jrun_to LAWS ubs0tbl_ok HS HJ FL_F4L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms1 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ F4_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssf) rq = SOff nn 0 -> ew Ef nn = wv -> getr (ms_regs msf) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg ubs0segs Ef ssf msf rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg ubs0segs Ef ssf msf rq HS), Hrq; reflexivity) end.
assert (HINV' : forall i2 x2, top <= i2 < top + h -> (x - 1 < x2 < W \/ (x2 = x - 1 /\ i2 < top)) -> ~ DIFb mem0 fimg bimg (i2 * W + x2)).
{ intros i2 x2 Hi2 Hx2. destruct (Z.eq_dec x2 x) as [Ex|Ex].
- destruct (Z.eq_dec i2 i) as [Ei|Ei]; [rewrite Ei, Ex; exact HNE | apply (HINV i2 x2 Hi2); right; clear - Ex Ei Hi2 Hwr Hi; lia].
- apply (HINV i2 x2 Hi2). left. clear - Hx2 Ex Hi2; lia. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH top (x - 1) STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K3) Hfi Hbi Ht0 Hh Hth Hc0 Hwit ltac:(clear - Hh Ht0; lia) ltac:(clear - Hx Hxc; lia)
ltac:(clear - Hfuel Hwr Hi Hh Hx Hxc; nia)); [| | | | | | | | | | | | | exact HINV'].
- rewrite (RGX 5%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite U_zext32_mod.
rewrite (U_add_small E _ _ (top * W) (x - 1)); [apply Z.mod_small; clear - HiW Hx Hxc Hc0 HW HNle; nia | apply (U_atom E 10 (top * W)); [rewrite (HE 10%nat 10%bv eq_refl); exact G10 | clear - HiW HNle HW; lia] | exact UAND | clear - HiW; lia | clear - Hx Hxc Hc0; lia | clear - HiW Hx Hxc Hc0 HW HNle; nia].
- apply (RG 16%bv 8%nat _ eq_refl). rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- rewrite (RGX 13%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UADD.
- apply (RG 17%bv 10%nat _ eq_refl). rewrite (HE 10%nat 10%bv eq_refl). exact G10.
- rewrite (HKR 10%bv ltac:(cbv; auto 50)). exact G10.
- rewrite (HKR 12%bv ltac:(cbv; auto 50)). exact G12.
- rewrite (RGX 15%bv (SLit 65535) eq_refl). reflexivity.
- rewrite (HKR 11%bv ltac:(cbv; auto 50)). exact G11.
- rewrite (HKR 14%bv ltac:(cbv; auto 50)). exact G14.
- rewrite (HKR 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR 20%bv ltac:(cbv; auto 50)). exact G20.
- rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact G27. }
cbv beta. intros c' (regs' & mem' & xr & -> & HJ' & K' & Hl & Q13 & HK' & HV'). exists regs', mem', xr.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K3|]. split; [exact Hl|]. split; [exact Q13|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
rewrite branch_geu_U, U_and_lit, (U_atom_off E 16 i 1), (U_atom E 12 (top + h)), land_ffff in Hc
by first [rewrite (HE 16%nat 16%bv eq_refl); exact Gi16 | rewrite (HE 12%nat 12%bv eq_refl); exact G12 | clear - Hi Ht0 Hth HH Hh; lia].
assert (Hnw : i + 1 < top + h) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [exact Hl | discriminate Hc]). clear Hc.
assert (UXS : U E XS4 = 0).
{ unfold XS4. rewrite U_xor1_sltu, U_and_lit, (U_atom_off E 16 i 1), (U_atom E 12 (top + h)), land_ffff
by first [rewrite (HE 16%nat 16%bv eq_refl); exact Gi16 | rewrite (HE 12%nat 12%bv eq_refl); exact G12 | clear - Hi Ht0 Hth HH Hh; lia].
destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [reflexivity | exfalso; clear - Hl Hnw; lia]. }
destruct (UX 0 UXS ltac:(clear; lia) ltac:(clear - Hx; lia)) as [UAND UADD]. rewrite Z.sub_0_r in UAND, UADD.
jrun_to LAWS ubs0tbl_ok HS HJ FL_F4L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms1 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ F4_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg ubs0segs Ef ssf msf rq HS), Hrq; reflexivity) end.
assert (UROW : U E (SAlu ALU_ADD (SOff 17 0) (SOff 27 0)) = (i + 1) * W).
{ replace ((i + 1) * W) with (i * W + W) by (clear; lia).
apply (U_add_small E _ _ (i * W) W); [apply (U_atom E 17 (i * W)); [rewrite (HE 17%nat 17%bv eq_refl); exact G17 | clear - HiW HNle HW; lia]
| apply (U_atom E 27 W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | clear - HW; lia] | clear - HiW; lia | clear - HW; lia | clear - HiW HNle HW; lia]. }
assert (HiW1 : (i + 1) * W + W <= N) by (rewrite HN; clear - Hnw Hth Ht0 Hi HW; nia).
assert (HINV' : forall i2 x2, top <= i2 < top + h -> (x < x2 < W \/ (x2 = x /\ i2 < i + 1)) -> ~ DIFb mem0 fimg bimg (i2 * W + x2)).
{ intros i2 x2 Hi2 Hx2. destruct (Z.eq_dec i2 i) as [Ei|Ei].
- destruct (Z.eq_dec x2 x) as [Ex|Ex]; [rewrite Ei, Ex; exact HNE | apply (HINV i2 x2 Hi2); left; clear - Hx2 Ex; lia].
- apply (HINV i2 x2 Hi2). clear - Hx2 Ei; lia. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) x STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K3) Hfi Hbi Ht0 Hh Hth Hc0 Hwit ltac:(clear - Hi Hnw; lia) ltac:(clear - Hx; lia)
ltac:(clear - Hfuel; lia)); [| | | | | | | | | | | | | exact HINV'].
- rewrite (RGX 5%bv _ eq_refl). eval_sr_get. apply denot_of_U'. rewrite U_zext32_mod.
rewrite (U_add_small E _ _ ((i + 1) * W) x); [apply Z.mod_small; clear - HiW1 Hi Ht0 Hx Hc0 HW HNle; nia | exact UROW | exact UAND | clear - HiW1 Hi Ht0 HW; nia | clear - Hx Hc0; lia | clear - HiW1 Hi Ht0 Hx Hc0 HW HNle; nia].
- rewrite (RGX 16%bv (SOff 16 1) eq_refl). cbn [sv_denot]. rewrite (HE 16%nat 16%bv eq_refl), Gi16, unsigned_lit_small by (clear - Hi Ht0 Hth HH; lia). reflexivity.
- rewrite (RGX 13%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UADD.
- rewrite (RGX 17%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UROW.
- rewrite (HKR 10%bv ltac:(cbv; auto 50)). exact G10.
- rewrite (HKR 12%bv ltac:(cbv; auto 50)). exact G12.
- rewrite (RGX 15%bv (SLit 65535) eq_refl). reflexivity.
- rewrite (HKR 11%bv ltac:(cbv; auto 50)). exact G11.
- rewrite (HKR 14%bv ltac:(cbv; auto 50)). exact G14.
- rewrite (HKR 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR 20%bv ltac:(cbv; auto 50)). exact G20.
- rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact G27. }
cbv beta. intros c' (regs' & mem' & xr & -> & HJ' & K' & Hl & Q13 & HK' & HV'). exists regs', mem', xr.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K3|]. split; [exact Hl|]. split; [exact Q13|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
Qed.
Definition f4_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top h c0 : Z) (c' : config) : Prop :=
exists regs' mem' xr,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_F4F) mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
c0 <= xr < W /\ getr regs' 13 = Z_to_bv 64 xr /\ getr regs' 27 = Z_to_bv 64 W /\
(forall r : reg, In r F4S_KEPT -> getr regs' r = getr regs r) /\
((exists i2, top <= i2 < top + h /\ DIFb mem0 fimg bimg (i2 * W + xr)) /\ (forall i2 x2, top <= i2 < top + h -> xr < x2 < W -> ~ DIFb mem0 fimg bimg (i2 * W + x2))).
Lemma fl_f4V : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top h c0 : Z),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top -> 1 <= h -> top + h <= H -> 0 <= c0 < W -> DIFb mem0 fimg bimg (top * W + c0) ->
getr regs 10 = Z_to_bv 64 (top * W) -> getr regs 11 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) -> getr regs 12 = Z_to_bv 64 (top + h) ->
getr regs 8 = Z_to_bv 64 top -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 20 = Z_to_bv 64 bimg -> getr regs 27 = Z_to_bv 64 W ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 FL_F4) memc (seg_rom ubs0segs)) mdc) (f4_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0).
Proof using HC IMG.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 HJ K0 Hfi Hbi Ht0 Hh Hth Hc0 Hwit G10 G11 G12 G8 G9 G20 G27.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
assert (Hp : 0 <= top * W /\ top * W + W <= N) by (rewrite HN; clear - Ht0 Hh Hth HW; nia).
set (E := Ereg regs ([] : list word)).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE10 : ew E 10 = Z_to_bv 64 (top * W)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE27 : ew E 27 = Z_to_bv 64 W) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (HE20 : ew E 20 = Z_to_bv 64 bimg) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (UWM : U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 27 0) (SLit 48)) (SLit (- 2 ^ 48))) (SLit 48)) = W - 1).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SLit, (U_atom E 27 W HE27) by (clear - HW; lia). unfold zcanon, M64.
apply f4_wm1; [reflexivity | reflexivity | clear - HW; lia]. }
assert (UX4 : U E X4 = top * W + (W - 1)).
{ unfold X4. rewrite U_zext32_mod.
rewrite (U_add_small E _ _ (top * W) (W - 1)); [apply Z.mod_small; clear - Hp HNle HW; lia | apply (U_atom E 10 (top * W) HE10); clear - Hp HNle HW; lia | exact UWM | clear - Hp; lia | clear - HW; lia | clear - Hp HNle HW; lia]. }
assert (HFA : facts_ok E (ss_facts ss_f4)).
{ split; [| split].
- cbn [ss_facts ss_f4 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE10, HE27, HE20, (HE 11%nat 11%bv eq_refl), (HE 12%nat 12%bv eq_refl), (HE 8%nat 8%bv eq_refl), (HE 9%nat 9%bv eq_refl), G11, G12, G8, G9.
clear - Hp Ht0 Hh Hth HW HH HNle Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- cbn [ss_facts ss_f4 f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, UX4, (U_atom E 11 (2 ^ 64 - 1 - fimg)) by first [rewrite (HE 11%nat 11%bv eq_refl); exact G11 | clear - Hp Hfimg0 Hfimg1 Hac HW; lia].
destruct (Z.ltb_spec (2 ^ 64 - 1 - fimg) (top * W + (W - 1))) as [Hl|Hl]; [exfalso; clear - Hl Hp HNle HW Hfimg1 Hac; lia | reflexivity].
- cbn [ss_facts ss_f4 f_alias alias_ok]. exact I. }
assert (HS : st_ok ubs0segs E ss_f4 (mkst regs (Z_to_bv 64 FL_F4) memc (seg_rom ubs0segs))).
{ unfold ss_f4. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor | cbn [pairwise_disjoint]; exact I | exact HFA]. }
clear HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_F4) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ FL_F4L. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ F4S_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (rq : reg) nn wv, sr_get (ss_regs ssf) rq = SOff nn 0 -> ew Ef nn = wv -> getr (ms_regs msf) rq = wv)
by (intros rq nn wv Hrq Hvv; rewrite (st_ok_reg ubs0segs Ef ssf msf rq HS), Hrq; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (rq : reg) sv, sr_get (ss_regs ssf) rq = sv -> getr (ms_regs msf) rq = sv_denot Ef sv)
by (intros rq sv Hrq; rewrite (st_ok_reg ubs0segs Ef ssf msf rq HS), Hrq; reflexivity) end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (fl_f4lV (Datatypes.S (Z.to_nat ((W - 1 - c0) * h + h))) top (W - 1) STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ (KD_eq _ _ _ _ K0 K1) Hfi Hbi Ht0 Hh Hth Hc0 Hwit
ltac:(clear - Hh; lia) ltac:(clear - Hc0; lia) ltac:(clear - Hc0 Hh; nia)).
- rewrite (RGX 5%bv _ eq_refl). eval_sr_get. apply denot_of_U'. exact UX4.
- apply (RG 16%bv 8%nat _ eq_refl). rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- rewrite (RGX 13%bv (SOff 27 (-1)) eq_refl). cbn [sv_denot]. rewrite HE27, unsigned_lit_small by (clear - HW; lia). reflexivity.
- apply (RG 17%bv 10%nat _ eq_refl). exact HE10.
- rewrite (HKR 10%bv ltac:(cbv; auto 50)). exact G10.
- rewrite (HKR 12%bv ltac:(cbv; auto 50)). exact G12.
- rewrite (RGX 15%bv (SLit 65535) eq_refl). reflexivity.
- rewrite (HKR 11%bv ltac:(cbv; auto 50)). exact G11.
- rewrite (RGX 14%bv _ eq_refl). eval_sr_get. apply denot_of_U'. apply (U_not E 20 bimg HE20). clear - Hbimg0 Hbimg1 Hac Hp HW; lia.
- rewrite (HKR 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR 20%bv ltac:(cbv; auto 50)). exact G20.
- rewrite (HKR 27%bv ltac:(cbv; auto 50)). exact G27.
- intros i2 x2 Hi2 Hx2. exfalso. clear - Hi2 Hx2. lia. }
cbv beta. intros c' (regs' & mem' & xr & -> & HJ' & K' & Hl & Q13 & HK' & HV'). exists regs', mem', xr.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K1|]. split; [exact Hl|]. split; [exact Q13|].
split; [rewrite (HK' 27%bv ltac:(cbv; auto 50)), (HKR 27%bv ltac:(cbv; auto 50)); exact G27|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). apply (HKR rr Hrr).
Qed.
End e.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
