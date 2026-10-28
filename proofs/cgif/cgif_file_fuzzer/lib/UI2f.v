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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2o UI2p UI2q UI24 UI2d UI2e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition s4_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 9 0) (SOff 10 0), SOff 32 0); (SAlu ALU_ADD (SOff 8 0) (SOff 10 0), SOff 33 0) ].
Definition s4_stk : list YP09.chunk :=
[mkChunk 96 (CVal 8 (SOff 36 0)); mkChunk 104 (CVal 8 (SOff 37 0)); mkChunk 112 (CVal 8 (SOff 38 0)); mkChunk 120 (CVal 8 (SOff 39 0))].
Definition s4_atoms : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (10%nat, mkAF 0 (2^32 - 1) 0);
(21%nat, mkAF (2^64 - 1 - CEIL_MAX) (2^64 - 1 - 4096) 0); (23%nat, mkAF (2^64 - 1 - CEIL_MAX) (2^64 - 1 - 4096) 0);
(32%nat, mkAF 4096 (CEIL_MAX - 1) 0); (33%nat, mkAF 4096 (CEIL_MAX - 1) 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ].
Definition ss_s4l : sstate :=
mkSS FL_S4L sr_atoms
[ YP09.mkRegion (Some 2%nat) 96 128 96 96 s4_stk ;
YP09.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ;
YP09.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))] ] None
(mkFacts s4_atoms [] s4_alias).
Definition S4L_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 26; 27]%bv.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Section c.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Let CMP := CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef.
Definition s4l_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top h c0 : Z) (c' : config) : Prop :=
exists regs' mem' xr,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_S4F) mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
c0 <= xr < W /\ getr regs' 25 = Z_to_bv 64 xr /\
(forall r : reg, In r S4L_KEPT -> getr regs' r = getr regs r) /\
((exists i2, top <= i2 < top + h /\ CMP (i2 * W + xr) <> 0) /\ (forall i2 x2, top <= i2 < top + h -> xr < x2 < W -> CMP (i2 * W + x2) = 0)).
Lemma fl_s4lV : forall (n : nat) (i x : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top h c0 : Z),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top -> 1 <= h -> top + h <= H -> 0 <= c0 < W -> CMP (top * W + c0) <> 0 ->
top <= i < top + h -> x < W -> (c0 < x \/ (x = c0 /\ i = top)) ->
(x - c0) * h + (top + h - 1 - i) < Z.of_nat n ->
word_mem ubs0segs memc (spv + 96) top ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 bimg -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) -> getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - bimg) ->
getr regs 20 = Z_to_bv 64 i -> getr regs 25 = Z_to_bv 64 x -> getr regs 10 = Z_to_bv 64 (i * W + x) ->
getr regs 19 = Z_to_bv 64 65535 -> getr regs 24 = Z_to_bv 64 (top + h) ->
(forall i2 x2, top <= i2 < top + h -> (x < x2 < W \/ (x2 = x /\ i2 < i)) -> CMP (i2 * W + x2) = 0) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 FL_S4L) memc (seg_rom ubs0segs)) mdc) (s4l_postV STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0).
Proof using HC IMG.
intros n. induction n as [|n IH]; intros i x STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 HJ K0 Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi Hx Hinv Hfuel W96
G2 G8 G9 G18 G21 G23 G20 G25 G10 G19 G24 HINV; [exfalso; clear - Hfuel Hinv Hi Hh Hc0 Hx; nia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC memc K0)
as (_ & _ & _ & _ & _ & WHm & WWm & WGm & WCm).
assert (Hxc : c0 <= x) by (clear - Hinv; lia).
assert (Hx0 : 0 <= x) by (clear - Hxc Hc0; lia).
assert (Hp : 0 <= i * W + x /\ i * W + x + 1 <= N) by (rewrite HN; clear - Hi Hx0 Hx Ht0 Hh Hth HW; nia).
set (p := i * W + x) in *. assert (Hpdef : p = i * W + x) by reflexivity. clearbody p.
assert (Hp32 : p < 2 ^ 32) by (clear - Hp HNle; lia). assert (HN32 : N <= 2 ^ 32) by (clear - HNle; lia).
set (bc := byte_at memc (fimg + p)). set (bb := byte_at memc (bimg + p)).
pose proof (byte_at_range memc (fimg + p)) as Rbc. pose proof (byte_at_range memc (bimg + p)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [fimg + p; bimg + p; bc; bb; top; W; g; cfp] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HA : forall j v, nth_error [fimg + p; bimg + p; bc; bb; top; W; g; cfp] j = Some v -> ew E (32 + j) = Z_to_bv 64 v)
by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HE32 : ew E 32 = Z_to_bv 64 (fimg + p)) by (apply (HA 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 (bimg + p)) by (apply (HA 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 bc) by (apply (HA 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 bb) by (apply (HA 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 top) by (apply (HA 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 W) by (apply (HA 5%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 g) by (apply (HA 6%nat); reflexivity).
assert (HE39 : ew E 39 = Z_to_bv 64 cfp) by (apply (HA 7%nat); reflexivity).
assert (UR : forall (r : reg) (k : nat) v, Z.of_nat k = bv_unsigned r -> getr regs r = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff k 0) = v)
by (intros r k v Hk Hg Hv; apply U_atom; [rewrite (HE k r Hk); exact Hg | exact Hv]).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HU32 : bv_unsigned (ew E 32) = fimg + p) by (rewrite HE32; apply unsigned_lit_small; clear - Hp Hfimg0 Hfimg1 Hac; lia).
assert (HU33 : bv_unsigned (ew E 33) = bimg + p) by (rewrite HE33; apply unsigned_lit_small; clear - Hp Hbimg0 Hbimg1 Hac; lia).
assert (HFA : facts_ok E (mkFacts s4_atoms [] s4_alias)).
{ split; [| split; [exact I|]].
- unfold s4_atoms. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU32, HU33, HE34, HE35, (HE 10%nat 10%bv eq_refl), (HE 21%nat 21%bv eq_refl), (HE 23%nat 23%bv eq_refl), G10, G21, G23.
clear - Hsp0 Hsp1 Hsp16 Hp Hp32 Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- unfold s4_alias. cbn [f_alias alias_ok].
split; [| split; [| exact I]].
+ rewrite (denot_of_U' E (SOff 32 0) (fimg + p)) by (apply U_atom; [exact HE32 | clear - Hp Hfimg0 Hfimg1 Hac; lia]).
apply denot_of_U'. rewrite (U_add_small E _ _ fimg p); [reflexivity | apply (UR 9%bv); [reflexivity | exact G9 | clear - Hfimg0 Hfimg1 Hp Hac; lia]
| apply (UR 10%bv); [reflexivity | exact G10 | clear - Hp Hp32; lia] | clear - Hfimg0; lia | clear - Hp; lia | clear - Hp Hfimg1 Hac; lia].
+ rewrite (denot_of_U' E (SOff 33 0) (bimg + p)) by (apply U_atom; [exact HE33 | clear - Hp Hbimg0 Hbimg1 Hac; lia]).
apply denot_of_U'. rewrite (U_add_small E _ _ bimg p); [reflexivity | apply (UR 8%bv); [reflexivity | exact G8 | clear - Hbimg0 Hbimg1 Hp Hac; lia]
| apply (UR 10%bv); [reflexivity | exact G10 | clear - Hp Hp32; lia] | clear - Hbimg0; lia | clear - Hp; lia | clear - Hp Hbimg1 Hac; lia]. }
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 96 128 96 96 s4_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; lia|].
unfold s4_stk. constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, HE36, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Ht0 Hh Hth HH; lia | cbn; lia | apply val_mem_word_mem; exact W96].
- eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE37, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - HW; lia | cbn; lia | apply val_mem_word_mem; exact WWm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE38, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - G0 G1 Hac; unfold CGIF_SIZE in G1; lia | cbn; lia | apply val_mem_word_mem; exact WGm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ cfp); [cbn [sv_denot]; rewrite Z.add_0_r, HE39, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - C0 C1 Hac; lia | cbn; lia | apply val_mem_word_mem; exact WCm]. }
assert (HR1 : region_ok ubs0segs E memc (YP09.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU32.
split; [lia|]. split; [clear - Hp Hfimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(clear - Hp; lia))). }
assert (HR2 : region_ok ubs0segs E memc (YP09.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [clear - Hp Hbimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(clear - Hp; lia))). }
assert (HPD : pairwise_disjoint E (ss_mem ss_s4l)).
{ cbn [ss_mem ss_s4l pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU32, HU33.
repeat split; try exact I; clear - Dfb Hp Hsp0 Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac; lia. }
assert (HS : st_ok ubs0segs E ss_s4l (mkst regs (Z_to_bv 64 FL_S4L) memc (seg_rom ubs0segs))).
{ unfold ss_s4l. subst E. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | exact HFA].
constructor; [exact HR0 | constructor; [exact HR1 | constructor; [exact HR2 | constructor]]]. }
clear HR0 HR1 HR2 HPD HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S4L) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cmpPixel.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha0. rewrite HE38 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite HE39 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 18%nat 18%bv eq_refl), G18 in Ha2.
jreg HS (13%bv:reg) as Ha3. rewrite HE34 in Ha3. jreg HS (14%bv:reg) as Ha4. rewrite HE35 in Ha4.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (Hbq : forall a, byte_at (ms_mem ms) a = byte_at memc a) by (intros a; unfold byte_at; rewrite (mbyte_of_eq _ _ _ _ K1); reflexivity).
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc ss_s4l].
eapply SR_bind.
{ apply (cmp_callD API IMG mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC
STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) p FL_S4R HJ (KD_eq _ _ _ _ K0 K1) ltac:(clear - Hp; lia) Ha0 Ha1 Ha2).
- rewrite Hbq. exact Ha3.
- rewrite Hbq. exact Ha4.
- rewrite Hra. apply (ret_ok_even (Z_to_bv 64 FL_S4R)). vm_compute. reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hmem2 & Hres & Hfr2). clear HJ.
assert (K2 : forall z, mem2 z = memc z) by (intros z; rewrite Hmem2; apply K1).
jafter_stretch_keep HS 40%nat regs2 mem2 CMP_CLOB FL_S4R [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]];
(eapply (region_kept_out ubs0segs _ _ _ _ 0 0); [intros z _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; rewrite ?HU2, ?HU32, ?HU33; clear - Hsp0 Hp Hfimg0 Hbimg0 Hac; lia
| cbn [r_base r_hi base_val]; rewrite ?HU2, ?HU32, ?HU33; clear - Hsp1 Hp Hfimg1 Hbimg1 Hac; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_S4R) mem2 (seg_rom ubs0segs))) in HJ2.
set (E2 := havoc E 40 (map (getr regs2) CMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
jbranch ubs0tbl HS.
-
assert (Hne : CMP p <> 0).
{ intros Hz. rewrite branch_ne_U, U_lit, (U_atom E2 42 0) in Hc; [discriminate Hc | | clear; lia | clear; lia].
subst E2. change 42%nat with (40 + 2)%nat. rewrite (ew_havoc_new E 40 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) by (cbn; lia).
cbn [nth map CMP_CLOB]. rewrite Hres. unfold CMP in Hz. rewrite Hz. reflexivity. }
clear Hc. jrun_to LAWS ubs0tbl_ok HS HJ2 FL_S4F.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K3 : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K2) end.
clear HF HG.
apply SR_ret. lazymatch type of HS with st_ok _ _ _ ?msf => exists (ms_regs msf), (ms_mem msf), x end.
split; [rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl); reflexivity|]. split; [exact HJ2|]. split; [exact K3|]. split; [clear - Hxc Hx; lia|].
split; [reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 25%nat 25%bv eq_refl), G25, Z_to_bv_bv_unsigned; reflexivity)|].
split; [intros rr Hrr; subst E E2; lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf => exact (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ S4L_KEPT HS EA1 ltac:(vm_compute; reflexivity) rr Hrr) end|].
split; [exists i; split; [exact Hi | rewrite <- Hpdef; exact Hne] | intros i2 x2 Hi2 Hx2; apply (HINV i2 x2 Hi2); left; exact Hx2].
-
assert (Hz : CMP p = 0).
{ destruct (Z.eq_dec (CMP p) 0) as [Hz|Hnz]; [exact Hz | exfalso].
rewrite branch_ne_U, U_lit, U_SOff in Hc by (clear; lia). subst E2. change 42%nat with (40 + 2)%nat in Hc.
rewrite (ew_havoc_new E 40 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) in Hc by (cbn; lia). cbn [nth map CMP_CLOB] in Hc. rewrite Hres, Z_to_bv_unsigned in Hc.
pose proof (cmpPixel_fn_range cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef (byte_at mem0 (fimg + p)) (byte_at mem0 (bimg + p))) as Rr.
pose proof (wrap64_nz _ Rr Hnz) as X. destruct (Z.eqb_spec (zcanon (bv_wrap 64 (CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef p) + 0)) 0) as [Hq|Hq]; [exact (X Hq) | discriminate Hc]. }
clear Hc.
assert (Hxlt : c0 < x) by (destruct Hinv as [Hl | [Hxe Hie]]; [exact Hl | exfalso; apply Hwit; rewrite <- Hxe, <- Hie, <- Hpdef; exact Hz]).
jrun LAWS ubs0tbl_ok HS HJ2.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K3 : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K2) end.
clear HF HG.
assert (U19 : U E2 (SOff 19 0) = 65535) by (apply U_atom; [subst E2; ew_havocA; rewrite (HE 19%nat 19%bv eq_refl); exact G19 | lia]).
assert (U20 : U E2 (SOff 20 1) = i + 1)
by (apply U_atom_off; [subst E2; ew_havocA; rewrite (HE 20%nat 20%bv eq_refl); exact G20 | clear - Hi Ht0 Hth HH Hh; lia | clear - Hi Ht0 Hth HH Hh; lia]).
assert (U24 : U E2 (SOff 24 0) = top + h) by (apply U_atom; [subst E2; ew_havocA; rewrite (HE 24%nat 24%bv eq_refl); exact G24 | clear - Ht0 Hth HH Hh; lia]).
assert (U25 : U E2 (SOff 25 0) = x) by (apply U_atom; [subst E2; ew_havocA; rewrite (HE 25%nat 25%bv eq_refl); exact G25 | clear - Hx0 Hx HW; lia]).
assert (U36 : U E2 (SOff 36 0) = top) by (apply U_atom; [subst E2; ew_havocA; exact HE36 | clear - Ht0 Hth HH Hh; lia]).
assert (U37 : U E2 (SOff 37 0) = W) by (apply U_atom; [subst E2; ew_havocA; exact HE37 | clear - HW; lia]).
assert (U21 : U E2 (SOff 21 0) = 2 ^ 64 - 1 - fimg)
by (apply U_atom; [subst E2; ew_havocA; rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - Hfimg0 Hfimg1 Hp Hac; lia]).
assert (UAND : forall a v, U E2 a = v -> 0 <= v < 65536 -> U E2 (SAlu ALU_AND a (SOff 19 0)) = v).
{ intros a v Ha Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U19, land_ffff by exact Hv. apply zcanon_id. unfold M64. lia. }
assert (UA : U E2 (SAlu ALU_AND (SOff 20 1) (SOff 19 0)) = i + 1) by (apply UAND; [exact U20 | clear - Hi Ht0 Hth HH Hh; lia]).
assert (UX : U E2 (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 20 1) (SOff 19 0)) (SOff 24 0)) (SLit 1)) = if i + 1 <? top + h then 0 else 1)
by (rewrite U_xor1_sltu, UA, U24; reflexivity).
assert (UADDR : forall row row' x', U E2 row = row' -> 0 <= row' < 65536 -> forall s, U E2 s = x' -> 0 <= x' < W -> row' * W + x' < 2 ^ 32 ->
U E2 (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND row (SOff 19 0)) (SOff 37 0)) (SAlu ALU_AND s (SOff 19 0))) (SLit 32)) (SLit 32))
= row' * W + x').
{ intros row row' x' Hrow Rrow s Hs Rs Rsum. rewrite U_zext32_mod.
rewrite (U_add_small E2 _ _ (row' * W) x'); [apply Z.mod_small; clear - Rrow Rs Rsum HW; nia | | | clear - Rrow HW; nia | clear - Rs; lia | clear - Rsum Rs; lia].
- apply (U_mul_small' E2 _ _ row' W); [apply UAND; [exact Hrow | exact Rrow] | exact U37 | clear - Rrow; lia | clear - HW; lia | clear - Rrow HW; nia].
- apply UAND; [exact Hs | clear - Rs HW; lia]. }
jbranch ubs0tbl HS.
+
rewrite branch_geu_U, UA, U24 in Hc.
assert (Hwrap : i + 1 = top + h) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [discriminate Hc | clear - Hl Hi; lia]). clear Hc.
assert (US : U E2 (SAlu ALU_SUB (SOff 25 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 20 1) (SOff 19 0)) (SOff 24 0)) (SLit 1))) = x - 1).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U25, UX. destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [clear - Hl Hwrap; lia|].
apply zcanon_id. unfold M64. clear - Hxlt Hc0 Hx HW; lia. }
assert (HINVw : forall i2 x2, top <= i2 < top + h -> (x - 1 < x2 < W \/ (x2 = x - 1 /\ i2 < top)) -> CMP (i2 * W + x2) = 0).
{ intros i2 x2 Hi2 Hx2. destruct (Z.eq_dec i2 i) as [Ei|Ei];
[destruct (Z.eq_dec x2 x) as [Ex|Ex]; [rewrite Ei, Ex, <- Hpdef; exact Hz | apply (HINV i2 x2 Hi2); clear - Hx2 Hi2 Hi Ei Ex Hwrap; lia]
| apply (HINV i2 x2 Hi2); clear - Hx2 Hi2 Hi Ei Hwrap; lia]. }
assert (Rsum : top * W + (x - 1) < 2 ^ 32) by (clear - Hp32 Hpdef Hi HW Hxlt Hc0 Ht0; nia).
pose proof (UADDR _ _ (x - 1) U36 ltac:(clear - Ht0 Hth HH Hh; lia) _ US ltac:(clear - Hxlt Hc0 Hx; lia) Rsum) as UAD.
jrun LAWS ubs0tbl_ok HS HJ2.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K3b : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K3) end.
clear HF HG.
jbranch ubs0tbl HS; [exfalso; rewrite branch_ltu_U, U21, UAD in Hc; apply Z.ltb_lt in Hc; clear - Hc Rsum Hfimg0 Hfimg1 Hp Hac; lia |].
jrun_to LAWS ubs0tbl_ok HS HJ2 FL_S4L.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K4 : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K3b);
assert (W96' : word_mem ubs0segs m2 (spv + 96) top) by (intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K4); exact (W96 k Hk)) end.
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ S4L_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH top (x - 1) STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ2 (KD_eq _ _ _ _ K0 K4) Hfi Hbi Ht0 Hh Hth Hc0 Hwit
ltac:(clear - Hh Ht0; lia) ltac:(clear - Hx; lia) ltac:(clear - Hxlt; lia) ltac:(clear - Hfuel Hwrap Hxlt Hh; nia) W96').
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 20%bv HS) end. eval_sr_get.
apply denot_of_U'. exact U36.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 25%bv HS) end. eval_sr_get.
apply denot_of_U'. exact US.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 10%bv HS) end. eval_sr_get.
apply denot_of_U'. exact UAD.
- rewrite (HKR 19%bv ltac:(cbv; auto 20)). exact G19.
- rewrite (HKR 24%bv ltac:(cbv; auto 20)). exact G24.
- exact HINVw. }
cbv beta. intros c' (regs' & mem' & xr & -> & HJ' & K' & Hl & Q25 & HK' & HV'). exists regs', mem', xr.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K4|]. split; [exact Hl|]. split; [exact Q25|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
rewrite branch_geu_U, UA, U24 in Hc.
assert (Hdown : i + 1 < top + h) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [exact Hl | discriminate Hc]). clear Hc.
assert (US : U E2 (SAlu ALU_SUB (SOff 25 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 20 1) (SOff 19 0)) (SOff 24 0)) (SLit 1))) = x).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U25, UX. destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [|clear - Hl Hdown; lia].
rewrite Z.sub_0_r. apply zcanon_id. unfold M64. clear - Hx0 Hx HW; lia. }
assert (HINVd : forall i2 x2, top <= i2 < top + h -> (x < x2 < W \/ (x2 = x /\ i2 < i + 1)) -> CMP (i2 * W + x2) = 0).
{ intros i2 x2 Hi2 Hx2. destruct (Z.eq_dec i2 i) as [Ei|Ei];
[destruct (Z.eq_dec x2 x) as [Ex|Ex]; [rewrite Ei, Ex, <- Hpdef; exact Hz | apply (HINV i2 x2 Hi2); clear - Hx2 Hi2 Hi Ei Ex Hdown; lia]
| apply (HINV i2 x2 Hi2); clear - Hx2 Hi2 Hi Ei Hdown; lia]. }
assert (HiN : (i + 1) * W + x < N) by (rewrite HN; clear - Hdown Hth Hx HW Hi Ht0 Hh; nia).
assert (Rsum : (i + 1) * W + x < 2 ^ 32) by (clear - HiN HN32; lia).
pose proof (UADDR _ _ x U20 ltac:(clear - Hi Ht0 Hth HH Hh; lia) _ US ltac:(clear - Hx0 Hx; lia) Rsum) as UAD.
jrun LAWS ubs0tbl_ok HS HJ2.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K3b : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K3) end.
clear HF HG.
jbranch ubs0tbl HS; [exfalso; rewrite branch_ltu_U, U21, UAD in Hc; apply Z.ltb_lt in Hc; clear - Hc Rsum Hfimg0 Hfimg1 Hp Hac; lia |].
jrun_to LAWS ubs0tbl_ok HS HJ2 FL_S4L.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K4 : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K3b);
assert (W96' : word_mem ubs0segs m2 (spv + 96) top) by (intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K4); exact (W96 k Hk)) end.
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ S4L_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) x STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ2 (KD_eq _ _ _ _ K0 K4) Hfi Hbi Ht0 Hh Hth Hc0 Hwit
ltac:(clear - Hi Hdown; lia) Hx ltac:(left; exact Hxlt) ltac:(clear - Hfuel Hdown Hxlt Hh Hi; nia) W96').
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 20%bv HS) end. eval_sr_get.
apply denot_of_U'. exact U20.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 25%bv HS) end. eval_sr_get.
apply denot_of_U'. exact US.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs0segs Ec ssc msc 10%bv HS) end. eval_sr_get.
apply denot_of_U'. exact UAD.
- rewrite (HKR 19%bv ltac:(cbv; auto 20)). exact G19.
- rewrite (HKR 24%bv ltac:(cbv; auto 20)). exact G24.
- exact HINVd. }
cbv beta. intros c' (regs' & mem' & xr & -> & HJ' & K' & Hl & Q25 & HK' & HV'). exists regs', mem', xr.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K4|]. split; [exact Hl|]. split; [exact Q25|].
split; [| exact HV']. intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
Qed.
End c.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
