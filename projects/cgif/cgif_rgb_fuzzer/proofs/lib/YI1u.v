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
YI1h YI16 YI1z YI1k YI21 YI22 YI23 YI1j YI1s YI1t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition s4_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 22 0) (Xaddr 27 19), SOff 32 0); (SAlu ALU_ADD (SOff 21 0) (Xaddr 27 19), SOff 33 0) ].
Definition ss_s4l : sstate :=
mkSS FL_S4L (sr_set sr_atoms 24%bv (SLit 65535))
[ YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ;
YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))] ] None
(mkFacts [ (27%nat, mkAF 0 65534 0); (19%nat, mkAF 0 65534 0); (25%nat, mkAF 1 65535 0); (23%nat, mkAF 1 65535 0); (26%nat, mkAF 0 65534 0);
(32%nat, mkAF 4096 (CEIL_MAX - 1) 0); (33%nat, mkAF 4096 (CEIL_MAX - 1) 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ] [] s4_alias).
Definition S4L_KEPT : list reg := [2; 3; 4; 8; 9; 18; 21; 23; 22; 25; 26; 20]%bv.
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Section c.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Let CMP := CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef.
Definition s4l_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (c0 : Z) (c' : config) : Prop :=
exists regs' mem' xr,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_S4F) mem' (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
c0 <= xr < W /\ getr regs' 19 = Z_to_bv 64 xr /\
(forall r : reg, In r S4L_KEPT -> getr regs' r = getr regs r).
Lemma fl_s4l : forall (n : nat) (i x : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top h c0 : Z),
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top -> 1 <= h -> top + h <= H -> 0 <= c0 < W -> CMP (top * W + c0) <> 0 ->
top <= i < top + h -> x < W -> (c0 < x \/ (x = c0 /\ i = top)) ->
(x - c0) * h + (top + h - 1 - i) < Z.of_nat n ->
getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 27 = Z_to_bv 64 i -> getr regs 21 = Z_to_bv 64 bimg -> getr regs 23 = Z_to_bv 64 (top + h) -> getr regs 22 = Z_to_bv 64 fimg ->
getr regs 24 = Z_to_bv 64 65535 -> getr regs 25 = Z_to_bv 64 W -> getr regs 26 = Z_to_bv 64 top -> getr regs 19 = Z_to_bv 64 x ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S4L) memc (seg_rom src2segs)) mdc) (s4l_post STK sp0 FP L A mem md Lc Ac mdc regs memc c0).
Proof.
intros n. induction n as [|n IH]; intros i x STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 HJ K0 Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi Hx0 Hinv Hfuel
G8 G9 G18 G27 G21 G23 G22 G24 G25 G26 G19; [exfalso; clear - Hfuel Hinv Hi Hh Hc0 Hx0; nia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
assert (Hxc : c0 <= x) by (clear - Hinv; lia).
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
assert (HX : U E (Xaddr 27 19) = p).
{ subst p. apply (U_Xaddr E 27 19 i x W); [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | rewrite (HE 19%nat 19%bv eq_refl); exact G19 | rewrite (HE 25%nat 25%bv eq_refl); exact G25
| clear - Hi Ht0 Hth HH; lia | clear - Hx0 Hxc Hc0 HW; lia | clear - HW; lia | clear - Hp HNle; lia]. }
assert (HFA : facts_ok E (ss_facts ss_s4l)).
{ split; [| split; [exact I|]].
- cbn [ss_facts ss_s4l f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU32, HU33, HE34, HE35, (HE 27%nat 27%bv eq_refl), (HE 19%nat 19%bv eq_refl), (HE 25%nat 25%bv eq_refl), (HE 23%nat 23%bv eq_refl), (HE 26%nat 26%bv eq_refl), G27, G19, G25, G23, G26.
clear - Hp Hi Hx0 Hxc Hc0 Ht0 Hh Hth HW HH Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- cbn [ss_facts ss_s4l f_alias s4_alias alias_ok]. split; [| split; [| exact I]].
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite HX, (U_atom E 22 fimg), (U_atom E 32 (fimg + p) HE32); [| clear - Hp Hfimg0 Hfimg1 Hac; lia | rewrite (HE 22%nat 22%bv eq_refl); exact G22 | clear - Hp Hfimg0 Hfimg1 Hac; lia].
apply zcanon_id. unfold M64. clear - Hp Hfimg0 Hfimg1 Hac; lia.
+ apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite HX, (U_atom E 21 bimg), (U_atom E 33 (bimg + p) HE33); [| clear - Hp Hbimg0 Hbimg1 Hac; lia | rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - Hp Hbimg0 Hbimg1 Hac; lia].
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
assert (HPD : pairwise_disjoint E (ss_mem ss_s4l)).
{ cbn [ss_mem ss_s4l pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU32, HU33.
repeat split; try exact I. clear - Dfb Hp. lia. }
assert (HS : st_ok src2segs E ss_s4l (mkst regs (Z_to_bv 64 FL_S4L) memc (seg_rom src2segs))).
{ unfold ss_s4l. apply entry_st_ok_full; [| vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HR1 | constructor]] | exact HPD | exact HFA].
apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact G24]. }
clear HR0 HR1 HPD.
clear HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S4L) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ src2_A_cmpPixel. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
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
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc ss_s4l].
eapply SR_bind.
{ apply (cmp_callD API IMG mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC
STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) p FL_S4R HJ (KD_eq _ _ _ _ K0 K1) ltac:(clear - Hp; lia) Ha0 Ha1 Ha2).
- rewrite Hbq. exact Ha3.
- rewrite Hbq. exact Ha4.
- rewrite Hra. apply (ret_ok_even (Z_to_bv 64 FL_S4R)). vm_compute. reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hmem2 & Hres & Hfr2). clear HJ.
assert (K2 : forall z, mem2 z = memc z) by (intros z; rewrite Hmem2; apply K1).
jafter_stretch_keep HS 36%nat regs2 mem2 CMP_CLOB FL_S4R [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor]];
(eapply (region_kept_out src2segs _ _ _ _ 0 0); [intros z _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU32, ?HU33; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU32, ?HU33; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_S4R) mem2 (seg_rom src2segs))) in HJ2.
set (E2 := havoc E 36 (map (getr regs2) CMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
jbranch src2tbl HS.
-
clear Hc. jrun_to LAWS src2tbl_ok HS HJ2 FL_S4F. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
apply SR_ret. exists (ms_regs ms0), (ms_mem ms0), x.
split; [rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl); reflexivity|]. split; [exact HJ2|]. split; [exact K3|]. split; [clear - Hx0 Hxc; lia|].
split; [reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 19%nat 19%bv eq_refl), G19, Z_to_bv_bv_unsigned; reflexivity)|].
intros rr Hrr. subst E E2. lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf => exact (regs_kept_of_st_ok src2segs Ef ssf msf regs _ S4L_KEPT HS EA1 ltac:(vm_compute; reflexivity) rr Hrr) end.
-
assert (Hz : CMP p = 0).
{ destruct (Z.eq_dec (CMP p) 0) as [Hz|Hnz]; [exact Hz | exfalso].
rewrite branch_ne_U, U_lit, U_SOff in Hc by (clear; lia). subst E2. change 38%nat with (36 + 2)%nat in Hc.
rewrite (ew_havoc_new E 36 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) in Hc by (cbn; lia). cbn [nth map CMP_CLOB] in Hc. rewrite Hres, Z_to_bv_unsigned in Hc.
pose proof (cmpPixel_fn_range cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef (byte_at mem0 (fimg + p)) (byte_at mem0 (bimg + p))) as Rr.
pose proof (wrap64_nz _ Rr Hnz) as X. destruct (Z.eqb_spec (zcanon (bv_wrap 64 (CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef p) + 0)) 0) as [Hq|Hq]; [exact (X Hq) | discriminate Hc]. }
clear Hc.
assert (Hxlt : c0 < x) by (destruct Hinv as [Hl | [Hxe Hie]]; [exact Hl | exfalso; apply Hwit; subst p; rewrite <- Hxe, <- Hie; exact Hz]).
jrun LAWS src2tbl_ok HS HJ2. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K3 : forall z, ms_mem ms0 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF HG.
jbranch src2tbl HS.
+
rewrite branch_geu_U, (U_atom_off E2 27 i 1), (U_atom E2 23 (top + h)) in Hc
by first [subst E2; ew_havocA; first [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | rewrite (HE 23%nat 23%bv eq_refl); exact G23] | clear - Hi Ht0 Hth HH Hh; lia].
assert (Hwrap : i + 1 = top + h) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [discriminate Hc | clear - Hl Hi; lia]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ2 FL_S4L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K4 : forall z, ms_mem ms1 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs _ S4L_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH top (x - 1) STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ2 (KD_eq _ _ _ _ K0 K4) Hfi Hbi Ht0 Hh Hth Hc0 Hwit
ltac:(clear - Hh; lia) ltac:(clear - Hx0; lia) ltac:(clear - Hxlt; lia) ltac:(clear - Hfuel Hwrap Hxlt Hh; nia)).
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 26%nat 26%bv eq_refl), G26, Z_to_bv_bv_unsigned; reflexivity).
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- rewrite (HKR 22%bv ltac:(cbv; auto 20)). exact G22.
- reg_nowF HS ltac:(reflexivity).
- rewrite (HKR 25%bv ltac:(cbv; auto 20)). exact G25.
- rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact G26.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src2segs Ec ssc msc 19%bv HS) end. eval_sr_get. apply denot_of_U'.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_xor1_sltu, (U_atom_off E2 27 i 1), (U_atom E2 23 (top + h)), (U_atom E2 19 x)
by first [subst E2; ew_havocA; first [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | rewrite (HE 23%nat 23%bv eq_refl); exact G23 | rewrite (HE 19%nat 19%bv eq_refl); exact G19] | clear - Hi Ht0 Hth HH Hh Hx0 Hxc Hc0 HW; lia].
destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [clear - Hl Hwrap; lia|]. apply zcanon_id. unfold M64. clear - Hx0 Hxlt Hc0 HW; lia. }
cbv beta. intros c' (regs' & mem' & xr & -> & HJ' & K' & Hl & Q19 & HK'). exists regs', mem', xr.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K4|]. split; [exact Hl|]. split; [exact Q19|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
rewrite branch_geu_U, (U_atom_off E2 27 i 1), (U_atom E2 23 (top + h)) in Hc
by first [subst E2; ew_havocA; first [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | rewrite (HE 23%nat 23%bv eq_refl); exact G23] | clear - Hi Ht0 Hth HH Hh; lia].
assert (Hdown : i + 1 < top + h) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [exact Hl | discriminate Hc]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ2 FL_S4L. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K4 : forall z, ms_mem ms1 z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs Ef ssf msf regs _ S4L_KEPT HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) x STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ2 (KD_eq _ _ _ _ K0 K4) Hfi Hbi Ht0 Hh Hth Hc0 Hwit
ltac:(clear - Hi Hdown; lia) Hx0 ltac:(left; exact Hxlt) ltac:(clear - Hfuel Hdown Hxlt Hh Hi; nia)).
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- reg_nowF HS ltac:(subst E2; ew_havocA; rewrite (HE 27%nat 27%bv eq_refl), G27, unsigned_lit_small by (clear - Hi Ht0 Hth HH; lia); reflexivity).
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- rewrite (HKR 22%bv ltac:(cbv; auto 20)). exact G22.
- reg_nowF HS ltac:(reflexivity).
- rewrite (HKR 25%bv ltac:(cbv; auto 20)). exact G25.
- rewrite (HKR 26%bv ltac:(cbv; auto 20)). exact G26.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg src2segs Ec ssc msc 19%bv HS) end. eval_sr_get. apply denot_of_U'.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_xor1_sltu, (U_atom_off E2 27 i 1), (U_atom E2 23 (top + h)), (U_atom E2 19 x)
by first [subst E2; ew_havocA; first [rewrite (HE 27%nat 27%bv eq_refl); exact G27 | rewrite (HE 23%nat 23%bv eq_refl); exact G23 | rewrite (HE 19%nat 19%bv eq_refl); exact G19] | clear - Hi Ht0 Hth HH Hh Hx0 Hxc Hc0 HW; lia].
destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [| clear - Hl Hdown; lia]. rewrite Z.sub_0_r. apply zcanon_id. unfold M64. clear - Hx0 Hxc Hc0 HW; lia. }
cbv beta. intros c' (regs' & mem' & xr & -> & HJ' & K' & Hl & Q19 & HK'). exists regs', mem', xr.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K4|]. split; [exact Hl|]. split; [exact Q19|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
Qed.
End c.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
