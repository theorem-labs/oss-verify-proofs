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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI4l UI21 UI2m UI5o UI5l YI6b UI5n UI20 UI1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI1n UI1e UI1f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0b UI1o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition AF_D2 : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x384).
Definition AF_LCRET : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x3a0).
Definition AF_FREE2 : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x4ac).
Definition AF_FREE1 : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x4b4).
Definition AF_D1B : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x358).
Definition AF_TIDX : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x34c).
Definition cond_a1 (z1 : bool) : acond := mkAC (if z1 then BC_EQ else BC_NE) (SAlu ALU_AND (SExt false 8 (SOff 46 0)) (SLit 1)) (SLit 0).
Definition ss_D2 (z1 : bool) : sstate :=
mkSS AF_D2 sr_atoms
(YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) :: af_Rcf ::
(if z1 then [] else [YP09.mkRegion (Some 18%nat) 0 16 0 8 [mkChunk 8 (CVal 8 (SOff 68 0))]]))
None (mkFacts (af_facts ++ cf_facts) [cond_a1 z1] []).
End c.
Ltac reg_nowG HS tac :=
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
lazymatch goal with |- getr _ ?rr = _ =>
let T := fresh "T" in
pose proof (st_ok_reg ubs0segs Ec ssc msc rr HS) as T; eval_sr_get_in T; cbn [sv_denot] in T;
repeat (rewrite ew_havoc_old in T; [|nat_lt_lit]); rewrite ?Z.add_0_r in T;
cbn [ms_regs mkst] in T; cbn [ms_regs mkst]; rewrite T; clear T; tac
end
end.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma af_D2 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z))
(i : nat) (op : option frame_st) (nf img' ctidx : Z) (cfp lpal lpa img fattr fgen delay nlp tidx t4 : Z)
(GPAL IMGv LPALv : list Z) (gs gs1 gsF : YO07.gif_st) (bc bF : rbound),
let sp0 := spZ regs0 in
let CB := (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) in
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
(i = 1%nat \/ i = 2%nat) ->
nth_error (cg_frames s) i = Some None -> nth_error (cg_frames s) (i - 1) = Some op ->
(i = 2%nat -> op <> None) ->
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
obj_at ubs0segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
obj_at ubs0segs memc nf LAY_FrameConfig [lpal; img'; fattr; fgen; delay; nlp; ctidx] ->
(forall a, g <= a < g + CGIF_SIZE -> inFP FP a) ->
(forall f a, In (Some f) (cg_frames s) -> fr_ptr f <= a < fr_ptr f + FRAME_SIZE -> inFP FP a) ->
(forall blc k, In (nf, FRAME_SIZE) blc -> 0 <= k < FRAME_SIZE -> wr_byte ADDFRAME_STK sp0 FP (blocks L A) blc (nf + k)) ->
(In (nf, FRAME_SIZE) (blocks L A) -> forall i, 0 <= i < FRAME_SIZE -> inFP FP (nf + i)) ->
(In (img', N) (blocks L A) -> forall i, 0 <= i < N -> inFP FP (img' + i)) ->
Permutation (blocks Lc Ac) ((nf, FRAME_SIZE) :: (img', N) :: cgif_blocks0 g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
getr regs1 18 = Z_to_bv 64 nf ->
getr regs1 19 = Z_to_bv 64 t4 -> 0 <= t4 < 2 ^ 64 ->
getr regs1 20 = Z_to_bv 64 (Z.of_nat i) ->
af_untouched regs0 regs1 ->
cg_gen s = cg_gen s0 -> cg_file s = cg_file s0 -> t4 = Z.land fattr 4 ->
af_sink g s0 s N rest FP (concat (YO07.s_out gsF)) L A mem md ->
af_hdr memc s GPAL gs1 -> YO07.s_rcur gsF = YO07.s_rcur gs1 -> YO07.s_ihead gsF = Z.of_nat i ->
af_slots memc s N gs1 (fun k => k <> i) ->
(forall k, (k < 3)%nat -> k <> i -> k <> (i - 1)%nat -> qslot gsF k = qslot gs1 k) ->
qslot gsF (i - 1)%nat = (if YO07.flag fattr 2 then YO07.omap (fun f => YO07.set_disp (YO07.set_gen f (YO07.clr (YO07.f_gen f) 2)) 8) (if YO07.flag (cg_attr s) 8 then YO07.omap (fun f => YO07.set_disp (YO07.set_gen f (YO07.clr (YO07.f_gen f) 3)) 8) (qslot gs1 (i - 1)%nat) else qslot gs1 (i - 1)%nat) else (if YO07.flag (cg_attr s) 8 then YO07.omap (fun f => YO07.set_disp (YO07.set_gen f (YO07.clr (YO07.f_gen f) 3)) 8) (qslot gs1 (i - 1)%nat) else qslot gs1 (i - 1)%nat)) ->
YO07.s_cur gsF = YO07.C_OK -> qslot gsF i = Some (YO07.new_frame (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv) ->
garr8 ubs0segs memc img' IMGv -> Z.of_nat (length IMGv) = N ->
(Z.land fattr 1 <> 0 -> garr8 ubs0segs memc lpa LPALv /\ Z.of_nat (length LPALv) = 3 * nlp) ->
(Z.land fattr 6 <> 0 -> ctidx = tidx) ->
Z.of_nat (length (concat (YO07.s_out gsF))) <= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N ->
res_ok Ac bc -> (Z.land fattr 1 <> 0 -> room bc (3 * nlp)) -> rb_le (if Z.land fattr 1 =? 0 then bc else rb_malloc bc (3 * nlp)) bF ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_D2) memc (seg_rom ubs0segs)) mdc) (af_postX API regs0 g N s0 CB rest GPAL gs gsF bF L A mem md).
Proof using IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP i op nf img' ctidx cfp lpal lpa img fattr fgen delay nlp tidx t4 GPAL IMGv LPALv gs gs1 gsF bc bF sp0 CB
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hgeom Hi Hinone Hiop Hi2 HnoCT Hcf Hcf8 Hcflo Hcfhi Hlpa Hnf7 HFPg HFPfr HWnf Hnf_fresh Himg_fresh HB HSV
G2 G8 G9 G18 G19 Rt4 G20 HUT
Xgen Xfile Xt4 XSK XH1 XRC XIH XS XQ XP XC XI XIMG XIL XLPA XCT XLEN XRq XRM XRF.
pose proof XSK as (XSK1 & XSK2 & XFIN & XSK4 & XSK5 & HFPX). apply hideP_i in XCT.
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (HB' : Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ ((nf, FRAME_SIZE) :: (img', N) :: CB ++ rest))).
{ eapply Permutation_trans; [exact HB|].
change ((nf, FRAME_SIZE) :: (img', N) :: cgif_blocks0 g s N ++ CB ++ rest) with ([(nf, FRAME_SIZE); (img', N)] ++ (cgif_blocks0 g s N ++ (CB ++ rest))).
change (cgif_blocks0 g s N ++ (nf, FRAME_SIZE) :: (img', N) :: CB ++ rest) with (cgif_blocks0 g s N ++ ([(nf, FRAME_SIZE); (img', N)] ++ (CB ++ rest))).
apply Permutation_app_swap_app. }
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB') as (_ & _ & (Hg0 & Hg1 & Hg16)).
assert (Hnfin : In (nf, FRAME_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Himgin : In (img', N) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc nf FRAME_SIZE HH0 Hnfin ltac:(lia)) as (Hn0 & Hn1 & Hn16).
assert (Hnsep : forall y, In y (cgif_blocks0 g s N) -> nf + FRAME_SIZE <= fst y \/ fst y + snd y <= nf).
{ intros y Hy. apply (heap_sep_perm _ _ LAWS Lc Ac memc mdc (nf, FRAME_SIZE) ((img', N) :: cgif_blocks0 g s N ++ CB ++ rest) y HH0 HB).
right. apply in_app_iff. left. exact Hy. }
assert (Hcgr : forall b n, In (b, n) (cgif_blocks0 g s N) -> 4096 <= b /\ b + n <= alloc_ceiling).
{ intros b n Hbn. apply (blocks_range _ _ LAWS Lc Ac memc mdc b n HH0). apply (Permutation_in _ (Permutation_sym HB')). apply in_app_iff. left. exact Hbn. }
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf.
pose proof (Rcf 0%nat lpal eq_refl) as Rlpal. pose proof (Rcf 2%nat fattr eq_refl) as Rfattr. pose proof (Rcf 5%nat nlp eq_refl) as Rnlp.
cbn [nth snd LAY_FrameConfig Z.of_N] in Rlpal, Rfattr, Rnlp.
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s [img']).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s [img'] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s [img'] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HKr regs1 regs0 lpal img fattr fgen delay nlp tidx s [img'] : forall n j r, _ -> _ -> ew E n = _) as HKr.
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s [img'] : forall n j v, _ -> _ -> ew E n = _) as HC.
pose proof (af_HM regs1 regs0 lpal img fattr fgen delay nlp tidx s [img'] : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = nf) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cfp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HE49 : ew E 49 = Z_to_bv 64 nlp) by (exact (HC 49%nat 5%nat nlp eq_refl eq_refl)).
assert (HE68 : ew E 68 = Z_to_bv 64 img') by (exact (HM 68%nat 0%nat img' eq_refl eq_refl)).
assert (Rimg' : 0 <= img' < 2 ^ 64).
{ pose proof (obj_at_range _ _ _ _ _ Hnf7 1%nat img' eq_refl) as R. cbn [nth snd LAY_FrameConfig Z.of_N] in R. exact R. }
pose proof (af_Rcf_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [img'] memc cfp HU9 ltac:(lia) ltac:(lia) Hcf) as HRcf.
pose proof (cf_facts_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [img'] memc cfp Hcf) as HFC.
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
assert (HFA : atoms_ok E af_facts).
{ cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, (HE 8%nat 8%bv eq_refl), G8, (HE 9%nat 9%bv eq_refl), G9, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (GOE1 : forall E' ss ms' Lx Ax mdx (lpal' : Z) (NBx : list (Z * Z)),
st_ok ubs0segs E' ss ms' -> ss_pc ss = AF_E -> ss_resv ss = None -> st_init_done Ax = true ->
getr (ms_regs ms') 2 = Z_to_bv 64 (sp0 - 64) -> getr (ms_regs ms') 8 = Z_to_bv 64 g -> getr (ms_regs ms') 9 = Z_to_bv 64 cfp ->
getr (ms_regs ms') 18 = Z_to_bv 64 nf -> getr (ms_regs ms') 19 = Z_to_bv 64 t4 -> getr (ms_regs ms') 20 = Z_to_bv 64 (Z.of_nat i) ->
getr (ms_regs ms') 3 = getr regs0 3 -> getr (ms_regs ms') 4 = getr regs0 4 -> getr (ms_regs ms') 23 = getr regs0 23 -> getr (ms_regs ms') 24 = getr regs0 24 ->
getr (ms_regs ms') 25 = getr regs0 25 -> getr (ms_regs ms') 26 = getr regs0 26 -> getr (ms_regs ms') 27 = getr regs0 27 ->
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lx Ax (ms_mem ms') mdx ->
cgif_at (ms_mem ms') g s -> obj_at ubs0segs (ms_mem ms') cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
obj_at ubs0segs (ms_mem ms') nf LAY_FrameConfig [lpal'; img'; fattr; fgen; delay; nlp; ctidx] ->
NBx = (if Z.land fattr 1 =? 0 then [] else [(lpal', 3 * nlp)]) ->
Permutation (blocks Lx Ax) (((nf, FRAME_SIZE) :: (img', N) :: NBx) ++ cgif_blocks0 g s N ++ CB ++ rest) ->
af_saved_ok (ms_mem ms') sp0 regs0 ->
res_ok Ax bF -> garr8 ubs0segs (ms_mem ms') img' IMGv ->
(Z.land fattr 1 <> 0 -> garr8 ubs0segs (ms_mem ms') lpal' LPALv /\ Z.of_nat (length LPALv) = 3 * nlp) ->
af_hdr (ms_mem ms') s GPAL gs1 -> af_slots (ms_mem ms') s N gs1 (fun k => k <> i) ->
SR ubs0segs (mkCfg ms' mdx) (af_postX API regs0 g N s0 CB rest GPAL gs gsF bF L A mem md)).
{ intros E' ss ms' Lx Ax mdx lpal' NBx HS' Hpc Hrv Hidx Q2 Q8 Q9 Q18 Q19 Q20 Q3 Q4 Q23 Q24 Q25 Q26 Q27 HJ' Hat' Hcf' Hnf' HNB HB2 HSV' XRq' XIMG' XLP' XH' XS'.
rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc. subst NBx.
eapply (af_E1 API IMG L A mem md regs0 (ms_regs ms') Lx Ax (ms_mem ms') mdx g N s0 s CB rest FP i op nf lpal' img' ctidx cfp lpal img fattr fgen delay nlp tidx t4
GPAL IMGv LPALv gs gs1 gsF bF);
try assumption.
- split; [exact Q3 | split; [exact Q4 | split; [exact Q23 | split; [exact Q24 | split; [exact Q25 | split; [exact Q26 | exact Q27]]]]]].
- exact (proj1 (af_sink_at API ADDFRAME_STK sp0 g s0 s N rest FP _ L A mem md Lx Ax (ms_mem ms') mdx HJ' XSK)). }
destruct (Z.eq_dec (Z.land fattr 1) 0) as [Hz1|Hz1].
-
assert (HCT : conds_ok E [cond_a1 true]).
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok, cond_a1. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, U_and_lit, U_lit by lia.
rewrite U_zext, (U_atom _ 46 fattr (HC 46%nat 2%nat fattr eq_refl eq_refl)) by lia. change (Z.of_N 8) with 8. rewrite land_low_mod by lia. rewrite Hz1. reflexivity. }
assert (HS : st_ok ubs0segs E (ss_D2 true) (mkst regs1 (Z_to_bv 64 AF_D2) memc (seg_rom ubs0segs))).
{ assert (HPDt : pairwise_disjoint E (ss_mem (ss_D2 true))).
{ cbn [ss_mem ss_D2]. unfold af_Rcf. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU9. clear - Hceil Hcflo HASv Hac. repeat split; lia. }
unfold ss_D2. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HRcf | constructor]] | exact HPDt |].
split; [apply atoms_ok_app; [exact HFA | exact HFC] | split; [exact HCT | exact I]]. }
clear HR0 HFA HCT.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_D2) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ AF_E. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hmem : forall a, mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs memc a).
{ intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
apply (GOE1 _ _ _ Lc Ac mdc lpal [] HS eq_refl eq_refl Hid).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 2%nat 2%bv eq_refl); exact G2).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 8%nat 8%bv eq_refl); exact G8).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 18%nat 18%bv eq_refl); exact G18).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
+ exact HJ.
+ eapply (cgif_at_kept0 memc (ms_mem ms) g s N (blocks Lc Ac)); [exact HB' | exact Hat | intros b n k Hb Hk; apply Hmem].
+ eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply Hmem].
+ eapply obj_at_transport_range; [exact Hnf7 | exact lay_inside_FrameConfig | intros k Hk; apply Hmem].
+ rewrite Hz1. reflexivity.
+ exact HB.
+ apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply Hmem].
+ replace (Z.land fattr 1 =? 0) with true in XRF by (symmetry; apply Z.eqb_eq; exact Hz1). exact (res_ok_mono _ _ _ XRF XRq).
+ eapply garr8_frame; [exact XIMG | intros a _; apply Hmem].
+ intros H1. exfalso. exact (H1 Hz1).
+ apply (af_hdr_kept memc); [intros _ k _; apply Hmem | exact XH1].
+ apply (af_slots_kept memc); [intros; apply Hmem | exact XS].
-
assert (HCF : conds_ok E [cond_a1 false]).
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok, cond_a1. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, U_and_lit, U_lit by lia.
rewrite U_zext, (U_atom _ 46 fattr (HC 46%nat 2%nat fattr eq_refl eq_refl)) by lia. change (Z.of_N 8) with 8. rewrite land_low_mod by lia.
destruct (Z.eqb_spec (Z.land fattr 1) 0); [lia | reflexivity]. }
assert (HR1 : region_ok ubs0segs E memc (YP09.mkRegion (Some 18%nat) 0 16 0 8 [mkChunk 8 (CVal 8 (SOff 68 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc nf FRAME_SIZE o HH0 Hnfin ltac:(lia))). }
constructor; [|constructor].
eapply (chunk_ok_val _ _ _ _ _ _ _ img'); [cbn [sv_denot]; rewrite Z.add_0_r, HE68, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
pose proof Hnf7 as Hn7. cbn [obj_at LAY_FrameConfig] in Hn7. unfold field_ok in Hn7. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in Hn7.
exact (proj1 (proj1 (proj2 Hn7))). }
assert (HPD : pairwise_disjoint E (ss_mem (ss_D2 false))).
{ cbn [ss_mem ss_D2]. unfold af_Rcf. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU9, HU18.
clear - Hceil Hcflo HASv Hac Hn0 Hn1 HFSv. repeat split; lia. }
assert (HS : st_ok ubs0segs E (ss_D2 false) (mkst regs1 (Z_to_bv 64 AF_D2) memc (seg_rom ubs0segs))).
{ unfold ss_D2. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR0 | constructor; [exact HRcf | constructor; [exact HR1 | constructor]]] | exact HPD |].
split; [apply atoms_ok_app; [exact HFA | exact HFC] | split; [exact HCF | exact I]]. }
clear HR0 HR1 HFA HCF HPD.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_D2) memc (seg_rom ubs0segs))) in HJ.
assert (Hlpain : In (lpa, 3 * nlp) (blocks Lc Ac)).
{ eapply blocks_perm_in; [exact HB|]. right. right. apply in_app_iff. right. apply in_app_iff. left. subst CB.
destruct (Z.eqb_spec (Z.land fattr 1) 0); [lia|]. right. left. reflexivity. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc lpa (3 * nlp) HH0 Hlpain) as [Hlpa0 Hlpa1].
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. eapply wr_ok_cons_gen with (k := 18%nat); [reflexivity | exact HU18 | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. replace a with (nf + (a - nf)) by lia. apply HWnf; [exact Hnfin | lia]. }
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs0segs Ec ssc msc 10%bv HS) as Hr10; eval_sr_get_in Hr10;
first [ rewrite (denot_mul3' _ 49 nlp HE49) in Hr10 by lia | rewrite (denot_mul3 _ 49 nlp HE49) in Hr10 by lia ] end.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4. jreg HS (1%bv:reg) as Hra1.
assert (Hspm : (sp0 - 64) mod 16 = 0) by (replace (sp0 - 64) with (sp0 + (-4) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := 3 * nlp) (spc := sp0 - 64) (b := bc);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hr10 | exact XRq | exact (XRM Hz1)
| exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hra1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs3 & mem3 & md3 & l3 & -> & HJ3 & Hid3 & HP3 & Hg10 & Hres & Hkeep3 & Hhi3 & HRq3). clear HJ.
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
assert (Hsub3 : forall b, In b (blocks Lc Ac) -> In b (blocks L2 A2)).
{ intros b Hb. destruct Hres as (_ & _ & (b1 & b2 & Hbl2 & Hblc) & _).
rewrite Hbl2. rewrite Hblc in Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
jafter_call_keep HS 84%nat regs3 mem3 HP3 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 9); [ew_havocA; exact HU9 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 18 nf FRAME_SIZE); [reflexivity | ew_havocA; exact HU18 | intros k Hk; apply (Hkeep3 _ _ _ Hnfin Hk) | | cbn; lia | cbn; lia].
cbn [r_wlo r_whi]. intros k Hk. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem3 md3 nf FRAME_SIZE k HH3 (Hsub3 _ Hnfin) ltac:(lia))). }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq72. cbn [ms_regs mkst] in Hq72. rewrite Hg10 in Hq72. symmetry in Hq72.
cbn [ms_mem mkst] in HF.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> (a < nf \/ nf + 8 <= a) ->
((exists b m, In (b, m) (blocks Lc Ac) /\ b <= a < b + m) \/ (alloc_ceiling <= a /\ ~ (sp0 - 64 - ALLOC_STACK <= a < sp0 - 64))) ->
mbyte ubs0segs mem3 a = mbyte ubs0segs memc a).
{ intros a Ha W1 Hw. transitivity (mbyte ubs0segs (ms_mem ms) a).
- destruct Hw as [(b & m & Hbm & Hab) | [Hhi Hno]].
+ replace a with (b + (a - b)) by lia. apply (Hkeep3 b m (a - b) Hbm). lia.
+ apply (proj1 (Hhi3 a ltac:(clear - Ha Hhi; lia) Hno)).
- clear - HF Ha W1 HU2 HU9 HU18. mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU9, ?HU18; lia). reflexivity. }
clear HF.
destruct Hres as (Hnz & Hl16 & (b1 & b2 & Hbl2 & Hblc) & Hwr3).
+
assert (Hl3in : In (l3, 3 * nlp) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
destruct (blocks_range _ _ LAWS L2 A2 mem3 md3 l3 (3 * nlp) HH3 Hl3in) as [Hl30 Hl31].
assert (Hsep3 : forall y, In y (blocks Lc Ac) -> l3 + 3 * nlp <= fst y \/ fst y + snd y <= l3).
{ intros y Hy. apply (heap_sep _ _ LAWS L2 A2 mem3 md3 b1 (l3, 3 * nlp) b2 y HH3 Hbl2). rewrite <- Hblc. exact Hy. }
pose proof (Hsep3 _ Hnfin) as Hsep_nl. cbn [fst snd] in Hsep_nl.
pose proof (Hsep3 _ Hlpain) as Hsep_pl. cbn [fst snd] in Hsep_pl.
add_fact HS 88%nat (mkAF 4096 CEIL_MAX 4).
2:{ rewrite Hq72, unsigned_lit_small by lia. change (2 ^ 4) with 16. clear - Hl30 Hl31 Hl16 Rnlp Hac. lia. }
jrun_to LAWS ubs0tbl_ok HS HJ3 ubs0_A_memcpy.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. eapply wr_ok_cons_gen with (k := 18%nat); [reflexivity | ew_havocA; exact HU18 | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. replace a with (nf + (a - nf)) by lia. apply HWnf; [exact (Hsub3 _ Hnfin) | lia]. }
jreg HS (10%bv:reg) as M0. rewrite Hq72 in M0.
jreg HS (11%bv:reg) as M1. rewrite (HC 44%nat 0%nat lpal eq_refl eq_refl), <- Hlpa in M1.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs0segs Ec ssc msc 12%bv HS) as M2; eval_sr_get_in M2;
first [ rewrite (denot_mul3' _ 49 nlp) in M2 by first [lia | ew_havocA; exact HE49]
| rewrite (denot_mul3 _ 49 nlp) in M2 by first [lia | ew_havocA; exact HE49] ] end.
jreg HS (1%bv:reg) as Mra.
cbn [ms_mem mkst] in HF.
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> (a < nf \/ nf + 8 <= a) -> mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs mem3 a).
{ intros a Ha W1. clear - HF Ha W1 HU2 HU9 HU18. mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU9, ?HU18; lia). reflexivity. }
clear HF.
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ ubs0_memcpy) with (d := l3) (src := lpa) (n := 3 * nlp);
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact M0 | exact M1 | exact M2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | clear - Hsep_pl; lia | ].
- intros k Hk. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem3 md3 l3 (3 * nlp) k HH3 Hl3in Hk)).
- intros k Hk. apply (present_mbyte ubs0_msyms). match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem3 md3 lpa (3 * nlp) k HH3 (Hsub3 _ Hlpain) Hk)).
- intros a Ha. apply (Hwr3 (blocks L2 A2) (a - l3) Hl3in ltac:(lia)) || (replace a with (l3 + (a - l3)) by lia; apply (Hwr3 (blocks L2 A2) (a - l3) Hl3in); lia). }
cbv beta. intros c' (regs5 & mem5 & -> & HJ5 & Hd10 & Hfr5 & Hout5 & Hgr5 & Hcpy5). clear HJ3.
jafter_stretch_keep HS 100%nat regs5 mem5 MEMCPY_CLOB AF_E [0%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr5 : P); [| assert (HKm5 : Q); [| specialize (HS2 HKr5 HKm5); clear HKr5 HKm5]] end.
{ intros rr Hrr. apply Hfr5. exact Hrr. }
{ constructor; [|constructor; [|constructor]].
- eapply region_kept_out; [exact Hout5 | exact Hgr5 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU2; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU2; intros a Ha; clear - Ha Hl31 Hceil HASv Hac; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout5 | exact Hgr5 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU18; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU18; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU18; intros a Ha; clear - Ha Hsep_nl HFSv; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (ALL : forall a, 0 <= a < 2 ^ 64 -> (a < nf \/ nf + 8 <= a) -> (a < l3 \/ l3 + 3 * nlp <= a) ->
((exists b m, In (b, m) (blocks Lc Ac) /\ b <= a < b + m) \/ sp0 - 64 <= a) ->
mbyte ubs0segs mem5 a = mbyte ubs0segs memc a).
{ intros a Ha W1 W2 Hw. unfold mbyte at 1. rewrite (Hout5 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ha; exact W2). fold (mbyte ubs0segs (ms_mem ms0) a).
rewrite (K4 a Ha W1). apply (K3 a Ha W1). destruct Hw as [Hw|Hw]; [left; exact Hw | right]. clear - Hw Hceil HASv HALv. lia. }
apply (GOE1 _ _ _ L2 A2 md3 l3 [(l3, 3 * nlp)] HS eq_refl eq_refl Hid3).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 2%nat 2%bv eq_refl); exact G2).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 8%nat 8%bv eq_refl); exact G8).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 18%nat 18%bv eq_refl); exact G18).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
* exact HJ5.
* eapply (cgif_at_kept0 memc _ g s N (cgif_blocks0 g s N ++ []) []); [apply Permutation_refl | exact Hat |].
intros b n k Hb Hk. rewrite app_nil_r in Hb. pose proof (Hcgr _ _ Hb) as [R0 R1]. pose proof (Hnsep _ Hb) as X1. cbn [fst snd] in X1.
assert (Ib : In (b, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB')); apply in_app_iff; left; exact Hb).
pose proof (Hsep3 _ Ib) as X2. cbn [fst snd] in X2.
apply ALL; [clear - Hk R0 R1 Hac; lia | clear - Hk X1 HFSv; lia | clear - Hk X2; lia | left; exists b, n; split; [exact Ib | lia]].
* eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply ALL; [clear - Hk Hcflo Hcfhi Hceil HASv Hac; lia | clear - Hk Hcflo Hceil Hn1 HASv HFSv Hac; lia | clear - Hk Hcflo Hceil Hl31 HASv Hac; lia | right; clear - Hk Hcflo; lia].
* eapply (obj_at_upd ubs0segs memc mem5 nf LAY_FrameConfig 32 _ _ [0%nat] [(0, 8)] Hnf7 lay_inside_FrameConfig); [vm_compute; reflexivity | reflexivity | | |].
-- intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 _].
apply ALL; [clear - Hk Hn0 Hn1 Hac HFSv; lia | clear - W1; lia | clear - Hk Hsep_nl HFSv; lia | left; exists nf, FRAME_SIZE; split; [exact Hnfin | clear - Hk HFSv; lia]].
-- intros j f v' [<-|[]] Hf Hv'. cbn in Hf, Hv'. injection Hf as <-. injection Hv' as <-.
lazymatch type of HS with st_ok _ ?Ef _ _ => replace nf with (bv_unsigned (ew Ef 18)) by (ew_havocA; exact HU18) end.
eapply (st_field ubs0segs _ _ _ 1%nat _ 18%nat _ 0 8%N (SOff 88 0) l3 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
cbn [sv_denot]. ew_havocA. rewrite Z.add_0_r, Hq72, unsigned_lit_small by lia. reflexivity.
-- intros j Hj. do 7 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; left; reflexivity] |]). reflexivity.
* destruct (Z.eqb_spec (Z.land fattr 1) 0); [lia | reflexivity].
* rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. rewrite <- Hblc.
eapply Permutation_trans; [apply perm_skip; exact HB|].
change (((nf, FRAME_SIZE) :: (img', N) :: [(l3, 3 * nlp)]) ++ cgif_blocks0 g s N ++ CB ++ rest) with ((nf, FRAME_SIZE) :: (img', N) :: (l3, 3 * nlp) :: (cgif_blocks0 g s N ++ CB ++ rest)).
eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
* apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha.
apply ALL; [clear - Ha Hceil Hsp063 HASv Hac; lia | clear - Ha Hceil Hn1 HASv HFSv Hac; lia | clear - Ha Hceil Hl31 HASv Hac; lia | right; clear - Ha; lia].
*
replace (Z.land fattr 1 =? 0) with false in XRF by (symmetry; apply Z.eqb_neq; exact Hz1). exact (res_ok_mono _ _ _ XRF HRq3).
*
pose proof (Hsep3 _ Himgin) as Xi3. cbn [fst snd] in Xi3.
assert (Xin : nf + FRAME_SIZE <= img' \/ img' + N <= nf).
{ pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (nf, FRAME_SIZE) _ (img', N) HH0 HB ltac:(left; reflexivity)) as Y. cbn [fst snd] in Y. exact Y. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 Himgin) as [Ri0 Ri1].
eapply garr8_frame; [exact XIMG|]. intros a Ha. rewrite XIL in Ha.
apply ALL; [clear - Ha Ri0 Ri1 Hac; lia | clear - Ha Xin HFSv; lia | clear - Ha Xi3; lia | left; exists img', N; split; [exact Himgin | clear - Ha; lia]].
*
intros _. destruct (XLPA Hz1) as [XG XGL]. split; [| exact XGL].
apply (garr8_copy ubs0segs (ms_mem ms0) mem5 lpa l3 LPALv); [| intros j Hj; rewrite XGL in Hj; exact (Hcpy5 j Hj)].
assert (Xpn : nf + FRAME_SIZE <= lpa \/ lpa + 3 * nlp <= nf).
{ pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (nf, FRAME_SIZE) _ (lpa, 3 * nlp) HH0 HB
ltac:(right; apply in_app_iff; right; apply in_app_iff; left; subst CB; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz1 ltac:(assumption)) | right; left; reflexivity])) as Y.
cbn [fst snd] in Y. exact Y. }
eapply garr8_frame; [exact XG|]. intros a Ha. rewrite XGL in Ha. rewrite (K4 a) by (clear - Ha Hlpa0 Hlpa1 Hac Xpn HFSv; lia).
apply K3; [clear - Ha Hlpa0 Hlpa1 Hac; lia | clear - Ha Xpn HFSv; lia | left; exists lpa, (3 * nlp); split; [exact Hlpain | clear - Ha; lia]].
*
apply (af_hdr_kept memc); [| exact XH1]. intros Hz k Hk.
assert (Hpb : In (cg_pal s, 3 * cg_ngp s) (cgif_blocks0 g s N)) by (unfold cgif_blocks0; right; right; apply in_app_iff; left; unfold pal_blocks; rewrite Hz; left; reflexivity).
pose proof (Hcgr _ _ Hpb) as [R0 R1]. pose proof (Hnsep _ Hpb) as X1. cbn [fst snd] in X1.
assert (Ib : In (cg_pal s, 3 * cg_ngp s) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB')); apply in_app_iff; left; exact Hpb).
pose proof (Hsep3 _ Ib) as X2. cbn [fst snd] in X2.
apply ALL; [clear - Hk R0 R1 Hac; lia | clear - Hk X1 HFSv; lia | clear - Hk X2; lia | left; exists (cg_pal s), (3 * cg_ngp s); split; [exact Ib | lia]].
*
pose proof Hwf as (Hlen' & _).
apply (af_slots_kept memc); [| exact XS]. intros k f Hk _ Hn a n j Hin Hj.
assert (Hvb : In (a, n) (cgif_blocks0 g s N)).
{ unfold cgif_blocks0. right. right. apply in_app_iff. right. apply (af_fvb_sub N (cg_frames s)). apply in_flat_map. exists (Some f).
split; [rewrite <- Hn; apply nth_In; rewrite Hlen'; exact Hk | exact Hin]. }
pose proof (Hcgr _ _ Hvb) as [R0 R1]. pose proof (Hnsep _ Hvb) as X1. cbn [fst snd] in X1.
assert (Ib : In (a, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB')); apply in_app_iff; left; exact Hvb).
pose proof (Hsep3 _ Ib) as X2. cbn [fst snd] in X2.
apply ALL; [clear - Hj R0 R1 Hac; lia | clear - Hj X1 HFSv; lia | clear - Hj X2; lia | left; exists a, n; split; [exact Ib | lia]].
Qed.
Definition LAY_NF6 : layout_t := [(0, 8%N); (16, 4%N); (20, 4%N); (24, 2%N); (26, 2%N); (28, 1%N)].
Definition ss_D1b : sstate :=
mkSS AF_D1B sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ; af_Rg None None None None ;
YP09.mkRegion (Some 18%nat) 8 16 8 16 [] ; af_Rcf ]
None (mkFacts (af_facts ++ [(58%nat, mkAF 0 65535 0); (59%nat, mkAF 0 65535 0)]) [] []).
Lemma af_D1b :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z))
(i : nat) (op : option frame_st) (nf ctidx : Z) (cfp lpal lpa img fattr fgen delay nlp tidx t4 : Z)
(GPAL IMGv LPALv : list Z) (gs gs1 gsF : YO07.gif_st) (bc bF : rbound),
let sp0 := spZ regs0 in
let CB := (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) in
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
(i = 1%nat \/ i = 2%nat) ->
nth_error (cg_frames s) i = Some None -> nth_error (cg_frames s) (i - 1) = Some op ->
(i = 2%nat -> op <> None) ->
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
obj_at ubs0segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
obj_at ubs0segs memc nf LAY_NF6 [lpal; fattr; fgen; delay; nlp; ctidx] ->
(forall a, g <= a < g + CGIF_SIZE -> inFP FP a) ->
(forall f a, In (Some f) (cg_frames s) -> fr_ptr f <= a < fr_ptr f + FRAME_SIZE -> inFP FP a) ->
(forall blc k, In (nf, FRAME_SIZE) blc -> 0 <= k < FRAME_SIZE -> wr_byte ADDFRAME_STK sp0 FP (blocks L A) blc (nf + k)) ->
(In (nf, FRAME_SIZE) (blocks L A) -> forall i, 0 <= i < FRAME_SIZE -> inFP FP (nf + i)) ->
Permutation (blocks Lc Ac) ((nf, FRAME_SIZE) :: cgif_blocks0 g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
getr regs1 18 = Z_to_bv 64 nf ->
getr regs1 19 = Z_to_bv 64 t4 -> 0 <= t4 < 2 ^ 64 ->
getr regs1 20 = Z_to_bv 64 (Z.of_nat i) ->
af_untouched regs0 regs1 ->
cg_gen s = cg_gen s0 -> cg_file s = cg_file s0 -> t4 = Z.land fattr 4 ->
af_sink g s0 s N rest FP (concat (YO07.s_out gsF)) L A mem md ->
af_hdr memc s GPAL gs1 -> YO07.s_rcur gsF = YO07.s_rcur gs1 -> YO07.s_ihead gsF = Z.of_nat i ->
af_slots memc s N gs1 (fun k => k <> i) ->
(forall k, (k < 3)%nat -> k <> i -> k <> (i - 1)%nat -> qslot gsF k = qslot gs1 k) ->
qslot gsF (i - 1)%nat = (if YO07.flag fattr 2 then YO07.omap (fun f => YO07.set_disp (YO07.set_gen f (YO07.clr (YO07.f_gen f) 2)) 8) (if YO07.flag (cg_attr s) 8 then YO07.omap (fun f => YO07.set_disp (YO07.set_gen f (YO07.clr (YO07.f_gen f) 3)) 8) (qslot gs1 (i - 1)%nat) else qslot gs1 (i - 1)%nat) else (if YO07.flag (cg_attr s) 8 then YO07.omap (fun f => YO07.set_disp (YO07.set_gen f (YO07.clr (YO07.f_gen f) 3)) 8) (qslot gs1 (i - 1)%nat) else qslot gs1 (i - 1)%nat)) ->
YO07.s_cur gsF = YO07.C_OK -> qslot gsF i = Some (YO07.new_frame (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv) ->
garr8 ubs0segs memc img IMGv -> Z.of_nat (length IMGv) = N ->
(Z.land fattr 1 <> 0 -> garr8 ubs0segs memc lpa LPALv /\ Z.of_nat (length LPALv) = 3 * nlp) ->
(Z.land fattr 6 <> 0 -> ctidx = tidx) ->
Z.of_nat (length (concat (YO07.s_out gsF))) <= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N ->
res_ok Ac bc -> room bc N -> (Z.land fattr 1 <> 0 -> room (rb_malloc bc N) (3 * nlp)) ->
rb_le (if Z.land fattr 1 =? 0 then rb_malloc bc N else rb_malloc (rb_malloc bc N) (3 * nlp)) bF ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_D1B) memc (seg_rom ubs0segs)) mdc) (af_postX API regs0 g N s0 CB rest GPAL gs gsF bF L A mem md).
Proof using IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP i op nf ctidx cfp lpal lpa img fattr fgen delay nlp tidx t4 GPAL IMGv LPALv gs gs1 gsF bc bF sp0 CB
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hgeom Hi Hinone Hiop Hi2 HnoCT Hcf Hcf8 Hcflo Hcfhi Hlpa Hnf6 HFPg HFPfr HWnf Hnf_fp HB HSV
G2 G8 G9 G18 G19 Rt4 G20 HUT
Xgen Xfile Xt4 XSK XH1 XRC XIH XS XQ XP XC XI XIMG0 XIL XLPA XCT XLEN XRq XRM1 XRM2 XRF.
apply hideP_i in XCT.
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & Hgone & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
assert (HB' : Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ ((nf, FRAME_SIZE) :: CB ++ rest))).
{ eapply Permutation_trans; [exact HB|]. apply Permutation_middle. }
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB') as (_ & _ & (Hg0 & Hg1 & Hg16)).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB' | left; reflexivity]).
assert (Hnfin : In (nf, FRAME_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Himgin : In (img, N) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HB)). right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc nf FRAME_SIZE HH0 Hnfin ltac:(lia)) as (Hn0 & Hn1 & Hn16).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc img N HH0 Himgin) as [Him0 Him1].
assert (Hnsep : forall y, In y (cgif_blocks0 g s N) -> nf + FRAME_SIZE <= fst y \/ fst y + snd y <= nf).
{ intros y Hy. apply (heap_sep_perm _ _ LAWS Lc Ac memc mdc (nf, FRAME_SIZE) (cgif_blocks0 g s N ++ CB ++ rest) y HH0 HB). apply in_app_iff. left. exact Hy. }
pose proof (Hnsep _ ltac:(left; reflexivity)) as Hsep_ng. cbn [fst snd] in Hsep_ng.
assert (Hcgr : forall b n, In (b, n) (cgif_blocks0 g s N) -> 4096 <= b /\ b + n <= alloc_ceiling).
{ intros b n Hbn. apply (blocks_range _ _ LAWS Lc Ac memc mdc b n HH0). apply (Permutation_in _ (Permutation_sym HB')). apply in_app_iff. left. exact Hbn. }
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf.
pose proof (Rcf 0%nat lpal eq_refl) as Rlpal. pose proof (Rcf 1%nat img eq_refl) as Rimg. pose proof (Rcf 2%nat fattr eq_refl) as Rfattr. pose proof (Rcf 5%nat nlp eq_refl) as Rnlp.
cbn [nth snd LAY_FrameConfig Z.of_N] in Rlpal, Rimg, Rfattr, Rnlp.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s []).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s [] : forall n j v, _ -> _ -> ew E n = _) as HC.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = nf) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cfp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
pose proof (af_Rcf_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc cfp HU9 ltac:(lia) ltac:(lia) Hcf) as HRcf.
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
pose proof (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [] memc g None None None None HU8 ltac:(lia) ltac:(lia) Hobj I I I I) as HR1.
assert (HR2 : region_ok ubs0segs E memc (YP09.mkRegion (Some 18%nat) 8 16 8 16 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc nf FRAME_SIZE o HH0 Hnfin ltac:(lia))). }
assert (HPD : pairwise_disjoint E (ss_mem ss_D1b)).
{ cbn [ss_mem ss_D1b]. unfold af_Rg, af_Rcf. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8, HU9, HU18. clear - Hg1 Hn1 Hsep_ng Hceil Hcflo HASv HGSv HFSv Hac. repeat split; lia. }
assert (HFA : atoms_ok E af_facts).
{ cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, (HE 9%nat 9%bv eq_refl), G9, unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HFA2 : atoms_ok E [(58%nat, mkAF 0 65535 0); (59%nat, mkAF 0 65535 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HX 58%nat 7%nat _ eq_refl eq_refl), (HX 59%nat 8%nat _ eq_refl eq_refl), !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (HS : st_ok ubs0segs E ss_D1b (mkst regs1 (Z_to_bv 64 AF_D1B) memc (seg_rom ubs0segs))).
{ unfold ss_D1b. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | split; [apply atoms_ok_app; [exact HFA | exact HFA2] | split; exact I]].
constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor; [exact HRcf|]. constructor. }
clear HR0 HR1 HR2 HPD HFA.
assert (Hspm : (sp0 - 64) mod 16 = 0) by (replace (sp0 - 64) with (sp0 + (-4) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_D1B) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen with (k := 18%nat); [reflexivity | exact HU18 | | apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. replace a with (nf + (a - nf)) by lia. apply HWnf; [exact Hnfin | lia]. }
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs0segs Ec ssc msc 10%bv HS) as Hr10; eval_sr_get_in Hr10; rewrite ?denot_add0 in Hr10;
first [ rewrite (denot_mul_atoms _ 59 58 (cg_H s) (cg_W s) (HX 59%nat 8%nat _ eq_refl eq_refl) (HX 58%nat 7%nat _ eq_refl eq_refl)) in Hr10 by (clear - RW RH HN HNle; nia)
| rewrite (denot_mul_atoms _ 58 59 (cg_W s) (cg_H s) (HX 58%nat 7%nat _ eq_refl eq_refl) (HX 59%nat 8%nat _ eq_refl eq_refl)) in Hr10 by (clear - RW RH HN HNle; nia) ] end.
replace (cg_H s * cg_W s) with N in Hr10 by (clear - HN; lia). replace (cg_W s * cg_H s) with N in Hr10 by (clear - HN; lia).
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4. jreg HS (1%bv:reg) as Hra1.
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> (a < nf + 8 \/ nf + 16 <= a) -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs memc a).
{ intros a Ha W1. clear - HF Ha W1 HU2 HU8 HU9 HU18. mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity. }
clear HF.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := N) (spc := sp0 - 64) (b := bc);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hr10 | exact XRq | exact XRM1
| exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hra1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L3 & A3 & regs3 & mem3 & md3 & img' & -> & HJ3 & Hid3 & HP3 & Hi10 & Hres & Hkeep3 & Hhi3 & HRq3). clear HJ.
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
assert (Hsub3 : forall b, In b (blocks Lc Ac) -> In b (blocks L3 A3)).
{ intros b Hb. destruct Hres as (_ & _ & (b1 & b2 & Hbl2 & Hblc) & _).
rewrite Hbl2. rewrite Hblc in Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
jafter_call_keep HS 68%nat regs3 mem3 HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
4:{ eapply (region_kept_stack ubs0segs _ _ _ 9); [ew_havocA; exact HU9 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia]. }
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro ubs0segs _ _ _ 8); [ew_havocA; exact HU8 | exact Hgin | exact Hkeep3 | cbn; lia | cbn; lia | cbn; lia].
- eapply (region_kept_live _ _ _ _ 18 nf FRAME_SIZE); [reflexivity | ew_havocA; exact HU18 | intros k Hk; apply (Hkeep3 _ _ _ Hnfin Hk) | | cbn; lia | cbn; lia].
cbn [r_wlo r_whi]. intros k Hk. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem3 md3 nf FRAME_SIZE k HH3 (Hsub3 _ Hnfin) ltac:(lia))). }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq72. cbn [ms_regs mkst] in Hq72. rewrite Hi10 in Hq72. symmetry in Hq72.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> (a < nf + 8 \/ nf + 16 <= a) ->
((exists b m, In (b, m) (blocks Lc Ac) /\ b <= a < b + m) \/ sp0 - 64 <= a) ->
mbyte ubs0segs mem3 a = mbyte ubs0segs memc a).
{ intros a Ha W1 Hw. rewrite <- (K1 a Ha W1). destruct Hw as [(b & m & Hbm & Hab) | Hw].
- replace a with (b + (a - b)) by lia. apply (Hkeep3 b m (a - b) Hbm). lia.
- apply (proj1 (Hhi3 a ltac:(clear - Ha Hw Hceil HASv Hac; lia) ltac:(clear - Hw; lia))). }
destruct Hres as (Hnz & Hi16 & (b1 & b2 & Hbl3 & Hblc3) & Hwr3).
-
assert (Himgin3 : In (img', N) (blocks L3 A3)) by (rewrite Hbl3; apply in_app_iff; right; left; reflexivity).
destruct (blocks_range _ _ LAWS L3 A3 mem3 md3 img' N HH3 Himgin3) as [Hi0 Hi1].
assert (Hsepi : forall y, In y (blocks Lc Ac) -> img' + N <= fst y \/ fst y + snd y <= img').
{ intros y Hy. apply (heap_sep _ _ LAWS L3 A3 mem3 md3 b1 (img', N) b2 y HH3 Hbl3). rewrite <- Hblc3. exact Hy. }
pose proof (Hsepi _ Hnfin) as Hsep_in. cbn [fst snd] in Hsep_in.
pose proof (Hsepi _ Himgin) as Hsep_ii. cbn [fst snd] in Hsep_ii.
pose proof (Hsepi _ Hgin) as Hsep_ig. cbn [fst snd] in Hsep_ig.
assert (Himg_notc : ~ In (img', N) (blocks Lc Ac)) by (rewrite Hblc3; exact (fresh_not_in API L3 A3 mem3 md3 b1 b2 img' N HH3 Hbl3 ltac:(clear - HN HW1 HH1; nia))).
assert (Himg_fp : In (img', N) (blocks L A) -> forall k, 0 <= k < N -> inFP FP (img' + k)) by (intros Hin k Hk; exact (Hgone img' N k Hin Himg_notc Hk)).
add_fact HS 72%nat (mkAF 4096 CEIL_MAX 4).
2:{ rewrite Hq72, unsigned_lit_small by lia. change (2 ^ 4) with 16. clear - Hi0 Hi1 Hi16 Hac HN HW1 HH1. nia. }
jrun_to LAWS ubs0tbl_ok HS HJ3 ubs0_A_memcpy.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen with (k := 18%nat); [reflexivity | ew_havocA; exact HU18 | | apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. replace a with (nf + (a - nf)) by lia. apply HWnf; [exact (Hsub3 _ Hnfin) | lia]. }
jreg HS (10%bv:reg) as M0. rewrite Hq72 in M0.
jreg HS (11%bv:reg) as M1. rewrite (HC 45%nat 1%nat img eq_refl eq_refl) in M1.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs0segs Ec ssc msc 12%bv HS) as M2; eval_sr_get_in M2; rewrite ?denot_add0 in M2;
first [ rewrite (denot_mul_atoms _ 59 58 (cg_H s) (cg_W s)) in M2 by first [clear - RW RH HN HNle; nia | ew_havocA; apply (HX 59%nat 8%nat _ eq_refl eq_refl) | ew_havocA; apply (HX 58%nat 7%nat _ eq_refl eq_refl)]
| rewrite (denot_mul_atoms _ 58 59 (cg_W s) (cg_H s)) in M2 by first [clear - RW RH HN HNle; nia | ew_havocA; apply (HX 58%nat 7%nat _ eq_refl eq_refl) | ew_havocA; apply (HX 59%nat 8%nat _ eq_refl eq_refl)] ] end.
replace (cg_H s * cg_W s) with N in M2 by (clear - HN; lia). replace (cg_W s * cg_H s) with N in M2 by (clear - HN; lia).
jreg HS (1%bv:reg) as Mra.
cbn [ms_mem mkst] in HF.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> (a < nf + 8 \/ nf + 16 <= a) -> mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs mem3 a).
{ intros a Ha W1. clear - HF Ha W1 HU2 HU8 HU9 HU18. mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU9, ?HU18; lia). reflexivity. }
clear HF.
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ ubs0_memcpy) with (d := img') (src := img) (n := N);
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact M0 | exact M1 | exact M2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | clear - Hsep_ii; lia | ].
- intros k Hk. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem3 md3 img' N k HH3 Himgin3 Hk)).
- intros k Hk. apply (present_mbyte ubs0_msyms). match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem3 md3 img N k HH3 (Hsub3 _ Himgin) Hk)).
- intros a Ha. replace a with (img' + (a - img')) by lia. apply (Hwr3 (blocks L3 A3) (a - img') Himgin3). lia. }
cbv beta. intros c' (regs5 & mem5 & -> & HJ5 & Hd10 & Hfr5 & Hout5 & Hgr5 & Hcpy5). clear HJ3.
jafter_stretch_keep HS 84%nat regs5 mem5 MEMCPY_CLOB AF_D2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr5 : P); [| assert (HKm5 : Q); [| specialize (HS2 HKr5 HKm5); clear HKr5 HKm5]] end.
{ intros rr Hrr. apply Hfr5. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout5 | exact Hgr5 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU2; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU2; intros a Ha; clear - Ha Hi1 Hceil HASv Hac; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout5 | exact Hgr5 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU8; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU8; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU8; intros a Ha; clear - Ha Hsep_ig HGSv; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout5 | exact Hgr5 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU18; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU18; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU18; intros a Ha; clear - Ha Hsep_in HFSv; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (ALL : forall a, 0 <= a < 2 ^ 64 -> (a < nf + 8 \/ nf + 16 <= a) -> (a < img' \/ img' + N <= a) ->
((exists b m, In (b, m) (blocks Lc Ac) /\ b <= a < b + m) \/ sp0 - 64 <= a) ->
mbyte ubs0segs mem5 a = mbyte ubs0segs memc a).
{ intros a Ha W1 W2 Hw. unfold mbyte at 1. rewrite (Hout5 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by exact Ha; exact W2). fold (mbyte ubs0segs (ms_mem ms0) a).
rewrite (K3 a Ha W1). apply (K2 a Ha W1 Hw). }
eapply (af_D2 L A mem md regs0 regs5 L3 A3 mem5 md3 g N s0 s rest FP i op nf img' ctidx cfp lpal lpa img fattr fgen delay nlp tidx t4 GPAL IMGv LPALv gs gs1 gsF (rb_malloc bc N) bF);
[ exact HJ5 | exact Hid3 | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact Hi | exact Hinone | exact Hiop | exact Hi2 | exact HnoCT
| | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | | exact HFPg | exact HFPfr | exact HWnf | exact Hnf_fp | exact Himg_fp | | | | | | | | | |
| exact Xgen | exact Xfile | exact Xt4 | exact XSK | | exact XRC | exact XIH | | exact XQ | exact XP | exact XC | exact XI | | exact XIL | | unfold hideP in XCT; exact XCT | exact XLEN
| exact HRq3 | exact XRM2 | exact XRF ].
+ eapply (cgif_at_kept0 memc _ g s N (cgif_blocks0 g s N ++ []) []); [apply Permutation_refl | exact Hat |].
intros b n k Hb Hk. rewrite app_nil_r in Hb. pose proof (Hcgr _ _ Hb) as [R0 R1]. pose proof (Hnsep _ Hb) as X1. cbn [fst snd] in X1.
assert (Ib : In (b, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB')); apply in_app_iff; left; exact Hb).
pose proof (Hsepi _ Ib) as X2. cbn [fst snd] in X2.
apply ALL; [clear - Hk R0 R1 Hac; lia | clear - Hk X1 HFSv; lia | clear - Hk X2; lia | left; exists b, n; split; [exact Ib | lia]].
+ eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply ALL; [clear - Hk Hcflo Hcfhi Hceil HASv Hac; lia | clear - Hk Hcflo Hceil Hn1 HASv HFSv Hac; lia | clear - Hk Hcflo Hceil Hi1 HASv Hac; lia | right; clear - Hk Hcflo; lia].
+
apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
assert (T6 : forall j6 f6 v6, nth_error LAY_NF6 j6 = Some f6 -> nth_error [lpal; fattr; fgen; delay; nlp; ctidx] j6 = Some v6 -> field_ok ubs0segs mem5 nf f6 v6).
{ intros j6 f6 v6 Hf6 Hv6. eapply field_ok_kept; [exact (obj_at_fields ubs0segs _ _ _ _ Hnf6 j6 f6 v6 Hf6 Hv6)|].
assert (Hr6 : fst f6 + Z.of_N (snd f6) <= 8 \/ 16 <= fst f6) by (do 6 (destruct j6 as [|j6]; [cbn in Hf6; injection Hf6 as <-; cbn; lia|]); destruct j6; discriminate Hf6).
assert (Hr6' : 0 <= fst f6 /\ fst f6 + Z.of_N (snd f6) <= 40) by (do 6 (destruct j6 as [|j6]; [cbn in Hf6; injection Hf6 as <-; cbn; lia|]); destruct j6; discriminate Hf6).
intros k Hk. apply ALL; [clear - Hk Hr6' Hn0 Hn1 HFSv Hac; lia | clear - Hk Hr6; lia | clear - Hk Hr6' Hsep_in HFSv; lia | left; exists nf, FRAME_SIZE; split; [exact Hnfin | clear - Hk Hr6' HFSv; lia]]. }
destruct j as [|[|[|[|[|[|[|j]]]]]]]; [ | | | | | | | destruct j; discriminate Hf]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-.
* exact (T6 0%nat _ _ eq_refl eq_refl).
* lazymatch type of HS with st_ok _ ?Ef _ _ => replace nf with (bv_unsigned (ew Ef 18)) by (ew_havocA; exact HU18) end.
eapply (st_field ubs0segs _ _ _ 2%nat _ 18%nat _ 8 8%N (SOff 72 0) img' HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
cbn [sv_denot]. ew_havocA. rewrite Z.add_0_r, Hq72, unsigned_lit_small by lia. reflexivity.
* exact (T6 1%nat _ _ eq_refl eq_refl).
* exact (T6 2%nat _ _ eq_refl eq_refl).
* exact (T6 3%nat _ _ eq_refl eq_refl).
* exact (T6 4%nat _ _ eq_refl eq_refl).
* exact (T6 5%nat _ _ eq_refl eq_refl).
+ rewrite Hbl3. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. rewrite <- Hblc3.
eapply Permutation_trans; [apply perm_skip; exact HB|]. apply perm_swap.
+ apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha.
apply ALL; [clear - Ha Hceil Hsp063 HASv Hac; lia | clear - Ha Hceil Hn1 HASv HFSv Hac; lia | clear - Ha Hceil Hi1 HASv Hac; lia | right; clear - Ha; lia].
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 2%nat 2%bv eq_refl); exact G2).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 8%nat 8%bv eq_refl); exact G8).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 18%nat 18%bv eq_refl); exact G18).
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19).
+ exact Rt4.
+ reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20).
+ split; [|split; [|split; [|split; [|split; [|split]]]]].
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
* reg_nowG HS ltac:(ew_havocA; rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27).
+
apply (af_hdr_kept memc); [| exact XH1]. intros Hz k Hk.
assert (Hpb : In (cg_pal s, 3 * cg_ngp s) (cgif_blocks0 g s N)) by (unfold cgif_blocks0; right; right; apply in_app_iff; left; unfold pal_blocks; rewrite Hz; left; reflexivity).
pose proof (Hcgr _ _ Hpb) as [R0 R1]. pose proof (Hnsep _ Hpb) as X1. cbn [fst snd] in X1.
assert (Ib : In (cg_pal s, 3 * cg_ngp s) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB')); apply in_app_iff; left; exact Hpb).
pose proof (Hsepi _ Ib) as X2. cbn [fst snd] in X2.
apply ALL; [clear - Hk R0 R1 Hac; lia | clear - Hk X1 HFSv; lia | clear - Hk X2; lia | left; exists (cg_pal s), (3 * cg_ngp s); split; [exact Ib | lia]].
+
apply (af_slots_kept memc); [| exact XS]. intros k f Hk _ Hn a n j Hin Hj.
assert (Hvb : In (a, n) (cgif_blocks0 g s N)).
{ unfold cgif_blocks0. right. right. apply in_app_iff. right. apply (af_fvb_sub N (cg_frames s)). apply in_flat_map. exists (Some f).
split; [rewrite <- Hn; apply nth_In; rewrite Hlen; exact Hk | exact Hin]. }
pose proof (Hcgr _ _ Hvb) as [R0 R1]. pose proof (Hnsep _ Hvb) as X1. cbn [fst snd] in X1.
assert (Ib : In (a, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB')); apply in_app_iff; left; exact Hvb).
pose proof (Hsepi _ Ib) as X2. cbn [fst snd] in X2.
apply ALL; [clear - Hj R0 R1 Hac; lia | clear - Hj X1 HFSv; lia | clear - Hj X2; lia | left; exists a, n; split; [exact Ib | lia]].
+
apply (garr8_copy ubs0segs (ms_mem ms0) mem5 img img' IMGv); [| intros j Hj; rewrite XIL in Hj; exact (Hcpy5 j Hj)].
assert (Xpn : nf + FRAME_SIZE <= img \/ img + N <= nf).
{ pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (nf, FRAME_SIZE) _ (img, N) HH0 HB ltac:(apply in_app_iff; right; apply in_app_iff; left; left; reflexivity)) as Y.
cbn [fst snd] in Y. exact Y. }
eapply garr8_frame; [exact XIMG0|]. intros a Ha. rewrite XIL in Ha. rewrite (K3 a) by (clear - Ha Him0 Him1 Hac Xpn HFSv; lia).
apply K2; [clear - Ha Him0 Him1 Hac; lia | clear - Ha Xpn HFSv; lia | left; exists img, N; split; [exact Himgin | clear - Ha; lia]].
+
intros H1. destruct (XLPA H1) as [XG XGL]. split; [| exact XGL].
assert (Hlpain : In (lpa, 3 * nlp) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HB)). right. apply in_app_iff. right. apply in_app_iff. left. subst CB.
destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (H1 ltac:(assumption))|]. right. left. reflexivity. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 Hlpain) as [Rl0 Rl1].
pose proof (Hsepi _ Hlpain) as X2. cbn [fst snd] in X2.
assert (Xpn : nf + FRAME_SIZE <= lpa \/ lpa + 3 * nlp <= nf).
{ pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (nf, FRAME_SIZE) _ (lpa, 3 * nlp) HH0 HB
ltac:(apply in_app_iff; right; apply in_app_iff; left; subst CB; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (H1 ltac:(assumption)) | right; left; reflexivity])) as Y.
cbn [fst snd] in Y. exact Y. }
eapply garr8_frame; [exact XG|]. intros a Ha. rewrite XGL in Ha.
apply ALL; [clear - Ha Rl0 Rl1 Hac; lia | clear - Ha Xpn HFSv; lia | clear - Ha X2; lia | left; exists lpa, (3 * nlp); split; [exact Hlpain | clear - Ha; lia]].
Qed.
Definition af_Rcf4 : YP09.region :=
YP09.mkRegion (Some 9%nat) 0 32 0 0 (mkChunk 24 (CVal 4 (SOff 68 0)) :: obj_chunks_gen LAY_FrameConfig 44 []).
Definition ss_D1 : sstate :=
mkSS AF_D sr_atoms [ YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) ; af_Rcf4 ] None
(mkFacts (af_facts ++ cf_facts ++ [(68%nat, mkAF 0 4294967295 0)]) [] []).
Lemma af_D1 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z))
(i : nat) (op : option frame_st) (cfp lpal lpa img fattr fgen delay nlp tidx t4 : Z)
(GPAL IMGv LPALv : list Z) (gs gs1 gsF : YO07.gif_st) (bc bF : rbound),
let sp0 := spZ regs0 in
let CB := (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) in
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
(i = 1%nat \/ i = 2%nat) ->
nth_error (cg_frames s) i = Some None -> nth_error (cg_frames s) (i - 1) = Some op ->
(i = 2%nat -> op <> None) ->
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
obj_at ubs0segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
(forall a, g <= a < g + CGIF_SIZE -> inFP FP a) ->
(forall f a, In (Some f) (cg_frames s) -> fr_ptr f <= a < fr_ptr f + FRAME_SIZE -> inFP FP a) ->
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
getr regs1 19 = Z_to_bv 64 t4 -> 0 <= t4 < 2 ^ 64 -> getr regs1 20 = Z_to_bv 64 (Z.of_nat i) ->
af_untouched regs0 regs1 ->
cg_gen s = cg_gen s0 -> cg_file s = cg_file s0 -> t4 = Z.land fattr 4 ->
af_sink g s0 s N rest FP (concat (YO07.s_out gsF)) L A mem md ->
af_hdr memc s GPAL gs1 -> YO07.s_rcur gsF = YO07.s_rcur gs1 -> YO07.s_ihead gsF = Z.of_nat i ->
af_slots memc s N gs1 (fun k => k <> i) ->
(forall k, (k < 3)%nat -> k <> i -> k <> (i - 1)%nat -> qslot gsF k = qslot gs1 k) ->
qslot gsF (i - 1)%nat = (if YO07.flag fattr 2 then YO07.omap (fun f => YO07.set_disp (YO07.set_gen f (YO07.clr (YO07.f_gen f) 2)) 8) (if YO07.flag (cg_attr s) 8 then YO07.omap (fun f => YO07.set_disp (YO07.set_gen f (YO07.clr (YO07.f_gen f) 3)) 8) (qslot gs1 (i - 1)%nat) else qslot gs1 (i - 1)%nat) else (if YO07.flag (cg_attr s) 8 then YO07.omap (fun f => YO07.set_disp (YO07.set_gen f (YO07.clr (YO07.f_gen f) 3)) 8) (qslot gs1 (i - 1)%nat) else qslot gs1 (i - 1)%nat)) ->
YO07.s_cur gsF = YO07.C_OK -> qslot gsF i = Some (YO07.new_frame (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv) ->
garr8 ubs0segs memc img IMGv -> Z.of_nat (length IMGv) = N ->
(Z.land fattr 1 <> 0 -> garr8 ubs0segs memc lpa LPALv /\ Z.of_nat (length LPALv) = 3 * nlp) ->
Z.of_nat (length (concat (YO07.s_out gsF))) <= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N ->
res_ok Ac bc -> room bc 40 -> room (rb_malloc bc 40) N -> (Z.land fattr 1 <> 0 -> room (rb_malloc (rb_malloc bc 40) N) (3 * nlp)) ->
rb_le (if Z.land fattr 1 =? 0 then rb_malloc (rb_malloc bc 40) N else rb_malloc (rb_malloc (rb_malloc bc 40) N) (3 * nlp)) bF ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_D) memc (seg_rom ubs0segs)) mdc) (af_postX API regs0 g N s0 CB rest GPAL gs gsF bF L A mem md).
Proof using IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP i op cfp lpal lpa img fattr fgen delay nlp tidx t4 GPAL IMGv LPALv gs gs1 gsF bc bF sp0 CB
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hgeom Hi Hinone Hiop Hi2 HnoCT Hcf Hcf8 Hcflo Hcfhi Hlpa HFPg HFPfr HB HSV
G2 G8 G9 G19 Rt4 G20 HUT
Xgen Xfile Xt4 XSK XH1 XRC XIH XS XQ XP XC XI XIMG0 XIL XLPA XLEN XRq XRM0 XRM1 XRM2 XRF.
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & Hgone & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & _).
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as (_ & _ & (Hg0 & Hg1 & Hg16)).
assert (Hcgr : forall b n, In (b, n) (cgif_blocks0 g s N) -> 4096 <= b /\ b + n <= alloc_ceiling).
{ intros b n Hbn. apply (blocks_range _ _ LAWS Lc Ac memc mdc b n HH0). apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. left. exact Hbn. }
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf.
pose proof (Rcf 0%nat lpal eq_refl) as Rlpal. pose proof (Rcf 2%nat fattr eq_refl) as Rfattr. pose proof (Rcf 3%nat fgen eq_refl) as Rfgen.
pose proof (Rcf 4%nat delay eq_refl) as Rdelay. pose proof (Rcf 5%nat nlp eq_refl) as Rnlp. pose proof (Rcf 6%nat tidx eq_refl) as Rtidx.
cbn [nth snd LAY_FrameConfig Z.of_N] in Rlpal, Rfattr, Rfgen, Rdelay, Rnlp, Rtidx.
set (dn := delay + 65536 * nlp).
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s [dn]).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s [dn] : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s [dn] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s [dn] : forall n j v, _ -> _ -> ew E n = _) as HC.
pose proof (af_HM regs1 regs0 lpal img fattr fgen delay nlp tidx s [dn] : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HE68 : ew E 68 = Z_to_bv 64 dn) by (exact (HM 68%nat 0%nat dn eq_refl eq_refl)).
assert (Rdn : 0 <= dn < 2 ^ 32) by (subst dn; clear - Rdelay Rnlp; lia).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cfp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
pose proof (af_Rcf_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [dn] memc cfp HU9 ltac:(lia) ltac:(lia) Hcf) as HR2'.
assert (HR2 : region_ok ubs0segs E memc af_Rcf4).
{ unfold af_Rcf in HR2'. unfold af_Rcf4, region_ok in HR2' |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in HR2' |- *.
destruct HR2' as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. constructor; [|exact R4].
rewrite HU9. eapply (chunk_ok_val _ _ _ _ _ _ _ dn); [cbn [sv_denot]; rewrite Z.add_0_r, HE68, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
pose proof Hcf as Hc7. cbn [obj_at LAY_FrameConfig] in Hc7. unfold field_ok in Hc7. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in Hc7.
destruct Hc7 as (_ & _ & _ & _ & (F4 & _) & (F5 & _) & _).
apply (val_mem_wh_join ubs0segs memc (cfp + 24) delay nlp F4); [replace (cfp + 24 + 2) with (cfp + 26) by lia; exact F5 | lia | lia]. }
clear HR2'.
assert (HPD : pairwise_disjoint E (ss_mem ss_D1)).
{ cbn [ss_mem ss_D1]. unfold af_Rcf4. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU9. clear - Hceil Hcflo HASv Hac. repeat split; lia. }
assert (HFA : atoms_ok E af_facts).
{ cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, (HE 8%nat 8%bv eq_refl), G8, HU9, unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
pose proof (cf_facts_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s [dn] memc cfp Hcf) as HFC.
assert (HS : st_ok ubs0segs E ss_D1 (mkst regs1 (Z_to_bv 64 AF_D) memc (seg_rom ubs0segs))).
{ assert (HF68 : atoms_ok E [(68%nat, mkAF 0 4294967295 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE68, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
unfold ss_D1. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | split; [apply atoms_ok_app; [exact HFA | apply atoms_ok_app; [exact HFC | exact HF68]] | split; exact I]].
constructor; [exact HR0|]. constructor; [exact HR2|]. constructor. }
clear HR0 HR2 HPD HFA.
assert (Hspm : (sp0 - 64) mod 16 = 0) by (replace (sp0 - 64) with (sp0 + (-4) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_D) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4. jreg HS (1%bv:reg) as Hra1.
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs memc a).
{ intros a. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := 40) (spc := sp0 - 64) (b := bc);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hr10 | exact XRq | exact XRM0
| exact Hr2 | lia | exact Hspm | lia | lia | exact Hr4 | exact Hra1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & nf & -> & HJ2 & Hid2 & HP2 & Hg10 & Hres & Hkeep2 & Hhi2 & HRq2). clear HJ.
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep2, Hhi2. cbn [ms_regs ms_mem mkst] in HP2, Hkeep2, Hhi2, HJ2.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
jafter_call_keep HS 84%nat regs2 mem2 HP2 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 9); [ew_havocA; exact HU9 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq72. cbn [ms_regs mkst] in Hq72. rewrite Hg10 in Hq72. symmetry in Hq72.
assert (K2 : forall a, 0 <= a < 2 ^ 64 ->
((exists b m, In (b, m) (blocks Lc Ac) /\ b <= a < b + m) \/ sp0 - 64 <= a) ->
mbyte ubs0segs mem2 a = mbyte ubs0segs memc a).
{ intros a Ha Hw. rewrite <- (K1 a). destruct Hw as [(b & m & Hbm & Hab) | Hw].
- replace a with (b + (a - b)) by lia. apply (Hkeep2 b m (a - b) Hbm). lia.
- apply (proj1 (Hhi2 a ltac:(clear - Ha Hw Hceil HASv Hac; lia) ltac:(clear - Hw; lia))). }
destruct Hres as (Hnz & Hnf16 & (b1 & b2 & Hbl2 & Hblc) & Hwr2).
-
assert (Hnfin2 : In (nf, FRAME_SIZE) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 nf FRAME_SIZE HH2 Hnfin2 ltac:(lia)) as (Hn0 & Hn1 & _).
assert (Hnf_notc : ~ In (nf, FRAME_SIZE) (blocks Lc Ac)) by (rewrite Hblc; exact (fresh_not_in API L2 A2 mem2 md2 b1 b2 nf FRAME_SIZE HH2 Hbl2 ltac:(lia))).
assert (Hnf_fp : In (nf, FRAME_SIZE) (blocks L A) -> forall k, 0 <= k < FRAME_SIZE -> inFP FP (nf + k)) by (intros Hin k Hk; exact (Hgone nf FRAME_SIZE k Hin Hnf_notc Hk)).
assert (Hsepn : forall y, In y (blocks Lc Ac) -> nf + FRAME_SIZE <= fst y \/ fst y + snd y <= nf).
{ intros y Hy. apply (heap_sep _ _ LAWS L2 A2 mem2 md2 b1 (nf, FRAME_SIZE) b2 y HH2 Hbl2). rewrite <- Hblc. exact Hy. }
add_fact HS 88%nat (mkAF 4096 (CEIL_MAX - 40) 4).
2:{ rewrite Hq72, unsigned_lit_small by lia. change (2 ^ 4) with 16. clear - Hn0 Hn1 Hnf16 HFSv Hac. lia. }
af_add_region HS (YP09.mkRegion (Some 88%nat) 0 40 0 40 []).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite Hq72, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [| constructor].
intros o Ho. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem2 md2 nf FRAME_SIZE o HH2 Hnfin2 ltac:(lia))). }
2:{ cbn [ss_mem all_disjoint]. unfold af_Rcf4, extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite ?HU2, ?HU9, ?Hq72, ?unsigned_lit_small by lia.
clear - Hn1 Hceil Hcflo HASv HFSv Hac. repeat split; lia. }
jrun LAWS ubs0tbl_ok HS HJ2.
{ eapply wr_ok_cons_gen with (k := 88%nat); [reflexivity | ew_havocA; rewrite Hq72; apply unsigned_lit_small; lia | | apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. replace a with (nf + (a - nf)) by lia. apply (Hwr2 (blocks L2 A2) (a - nf) Hnfin2). lia. }
assert (GO : forall ss ms' (ctidx : Z),
st_ok ubs0segs (havoc E 84 (map (getr regs2) CLOB)) ss ms' -> ss_pc ss = AF_D1B -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 18%bv = SOff 88 0 ->
sr_get (ss_regs ss) 19%bv = SOff 19 0 -> sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 -> sr_get (ss_regs ss) 25%bv = SOff 25 0 ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs0_msyms MR ADDFRAME_STK sp0 FP L A mem md L2 A2 (ms_mem ms') md2 ->
(forall a, 0 <= a < 2 ^ 64 -> (a < nf \/ nf + 40 <= a) -> mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs mem2 a) ->
obj_at ubs0segs (ms_mem ms') nf LAY_NF6 [lpal; fattr; fgen; delay; nlp; ctidx] ->
(Z.land fattr 6 <> 0 -> ctidx = tidx) ->
SR ubs0segs (mkCfg ms' md2) (af_postX API regs0 g N s0 CB rest GPAL gs gsF bF L A mem md)).
{ intros ss ms' ctidx HS' Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q23 Q24 Q25 Q26 Q27 HJ' K3 Hnf6 XCT.
rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew (havoc E 84 (map (getr regs2) CLOB)) n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg ubs0segs _ ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
assert (ALL : forall a, 0 <= a < 2 ^ 64 -> (a < nf \/ nf + 40 <= a) ->
((exists b m, In (b, m) (blocks Lc Ac) /\ b <= a < b + m) \/ sp0 - 64 <= a) ->
mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a).
{ intros a Ha W1 Hw. rewrite (K3 a Ha W1). apply (K2 a Ha Hw). }
eapply (af_D1b L A mem md regs0 (ms_regs ms') L2 A2 (ms_mem ms') md2 g N s0 s rest FP i op nf ctidx cfp lpal lpa img fattr fgen delay nlp tidx t4 GPAL IMGv LPALv gs gs1 gsF (rb_malloc bc 40) bF);
[ exact HJ' | exact Hid2 | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact Hi | exact Hinone | exact Hiop | exact Hi2 | exact HnoCT
| | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact Hnf6 | exact HFPg | exact HFPfr | exact Hwr2 | exact Hnf_fp | | | | | | | | | |
| exact Xgen | exact Xfile | exact Xt4 | exact XSK | | exact XRC | exact XIH | | exact XQ | exact XP | exact XC | exact XI | | exact XIL | | exact XCT | exact XLEN
| exact HRq2 | exact XRM1 | exact XRM2 | exact XRF ].
- eapply (cgif_at_kept0 memc _ g s N (cgif_blocks0 g s N ++ []) []); [apply Permutation_refl | exact Hat |].
intros b n k Hb Hk. rewrite app_nil_r in Hb. pose proof (Hcgr _ _ Hb) as [R0 R1].
assert (Ib : In (b, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hb).
pose proof (Hsepn _ Ib) as X1. cbn [fst snd] in X1.
apply ALL; [clear - Hk R0 R1 Hac; lia | clear - Hk X1 HFSv; lia | left; exists b, n; split; [exact Ib | lia]].
- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply ALL; [clear - Hk Hcflo Hcfhi Hceil HASv Hac; lia | clear - Hk Hcflo Hceil Hn1 HASv HFSv Hac; lia | right; clear - Hk Hcflo; lia].
- rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. rewrite <- Hblc. apply perm_skip. exact HB.
- apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha.
apply ALL; [clear - Ha Hceil Hsp063 HASv Hac; lia | clear - Ha Hceil Hn1 HASv HFSv Hac; lia | right; clear - Ha; lia].
- apply (RG _ _ _ Q2). ew_havocA. rewrite (HE 2%nat 2%bv eq_refl). exact G2.
- apply (RG _ _ _ Q8). ew_havocA. rewrite (HE 8%nat 8%bv eq_refl). exact G8.
- apply (RG _ _ _ Q9). ew_havocA. rewrite (HE 9%nat 9%bv eq_refl). exact G9.
- apply (RG _ _ _ Q18). exact Hq72.
- apply (RG _ _ _ Q19). ew_havocA. rewrite (HE 19%nat 19%bv eq_refl). exact G19.
- exact Rt4.
- apply (RG _ _ _ Q20). ew_havocA. rewrite (HE 20%nat 20%bv eq_refl). exact G20.
- split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3); ew_havocA; rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4); ew_havocA; rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23); ew_havocA; rewrite (HE 23%nat 23%bv eq_refl); exact G23
| apply (RG _ _ _ Q24); ew_havocA; rewrite (HE 24%nat 24%bv eq_refl); exact G24
| apply (RG _ _ _ Q25); ew_havocA; rewrite (HE 25%nat 25%bv eq_refl); exact G25
| apply (RG _ _ _ Q26); ew_havocA; rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27); ew_havocA; rewrite (HE 27%nat 27%bv eq_refl); exact G27 ].
-
apply (af_hdr_kept memc); [| exact XH1]. intros Hz k Hk.
assert (Hpb : In (cg_pal s, 3 * cg_ngp s) (cgif_blocks0 g s N)) by (unfold cgif_blocks0; right; right; apply in_app_iff; left; unfold pal_blocks; rewrite Hz; left; reflexivity).
pose proof (Hcgr _ _ Hpb) as [R0 R1].
assert (Ib : In (cg_pal s, 3 * cg_ngp s) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hpb).
pose proof (Hsepn _ Ib) as X1. cbn [fst snd] in X1.
apply ALL; [clear - Hk R0 R1 Hac; lia | clear - Hk X1 HFSv; lia | left; exists (cg_pal s), (3 * cg_ngp s); split; [exact Ib | lia]].
-
apply (af_slots_kept memc); [| exact XS]. intros k f Hk _ Hn a n j Hin Hj.
assert (Hvb : In (a, n) (cgif_blocks0 g s N)).
{ unfold cgif_blocks0. right. right. apply in_app_iff. right. apply (af_fvb_sub N (cg_frames s)). apply in_flat_map. exists (Some f).
split; [rewrite <- Hn; apply nth_In; rewrite Hlen; exact Hk | exact Hin]. }
pose proof (Hcgr _ _ Hvb) as [R0 R1].
assert (Ib : In (a, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hvb).
pose proof (Hsepn _ Ib) as X1. cbn [fst snd] in X1.
apply ALL; [clear - Hj R0 R1 Hac; lia | clear - Hj X1 HFSv; lia | left; exists a, n; split; [exact Ib | lia]].
-
assert (Himgin : In (img, N) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 Himgin) as [Ri0 Ri1]. pose proof (Hsepn _ Himgin) as X1. cbn [fst snd] in X1.
eapply garr8_frame; [exact XIMG0|]. intros a Ha. rewrite XIL in Ha.
apply ALL; [clear - Ha Ri0 Ri1 Hac; lia | clear - Ha X1 HFSv; lia | left; exists img, N; split; [exact Himgin | clear - Ha; lia]].
-
intros H1. destruct (XLPA H1) as [XG XGL]. split; [| exact XGL].
assert (Hlpain : In (lpa, 3 * nlp) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. right. apply in_app_iff. left. subst CB.
destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (H1 ltac:(assumption))|]. right. left. reflexivity. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 Hlpain) as [Rl0 Rl1]. pose proof (Hsepn _ Hlpain) as X1. cbn [fst snd] in X1.
eapply garr8_frame; [exact XG|]. intros a Ha. rewrite XGL in Ha.
apply ALL; [clear - Ha Rl0 Rl1 Hac; lia | clear - Ha X1 HFSv; lia | left; exists lpa, (3 * nlp); split; [exact Hlpain | clear - Ha; lia]]. }
assert (NF5 : forall ss ms', st_ok ubs0segs (havoc E 84 (map (getr regs2) CLOB)) ss ms' ->
(exists rg, nth_error (ss_mem ss) 0 = Some rg /\ r_base rg = Some 88%nat /\
incl [mkChunk 0 (CVal 8 (SOff 44 0)); mkChunk 16 (CVal 4 (SExt true 32 (SOff 46 0))); mkChunk 20 (CVal 4 (SExt true 32 (SOff 47 0)));
mkChunk 24 (CVal 4 (SExt true 32 (SOff 68 0)))] (r_chunks rg)) ->
forall j f v, nth_error LAY_NF6 j = Some f -> nth_error [lpal; fattr; fgen; delay; nlp] j = Some v -> field_ok ubs0segs (ms_mem ms') nf f v).
{ intros ss ms' HS' (rg & Hrg & Hb & Hincl) j f v Hf Hv.
assert (HU72 : bv_unsigned (ew (havoc E 84 (map (getr regs2) CLOB)) 88) = nf) by (rewrite Hq72; apply unsigned_lit_small; lia).
assert (V4 : val_mem ubs0segs (ms_mem ms') (nf + 24) 4 dn).
{ pose proof (st_field_low ubs0segs _ _ _ 0%nat _ 88%nat nf 24 4%N (SExt true 32 (SOff 68 0)) (2 ^ 32) HS' Hrg Hb ltac:(apply Hincl; cbv; auto 10) HU72 ltac:(cbn; lia) eq_refl) as [V _].
cbn [fst snd] in V. replace (U (havoc E 84 (map (getr regs2) CLOB)) (SExt true 32 (SOff 68 0)) mod 2 ^ 32) with dn in V; [exact V|].
symmetry. apply U_sext32_low; [ew_havocA; exact HE68 | lia]. }
destruct (val_mem_wh_split ubs0segs _ _ _ _ V4 ltac:(lia) ltac:(lia)) as [VD VN].
destruct j as [|[|[|[|[|j]]]]]; [ | | | | | destruct j; discriminate Hv]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-.
- rewrite <- HU72. eapply (st_field ubs0segs _ _ _ 0%nat _ 88%nat _ 0 8%N (SOff 44 0) lpal HS' Hrg Hb); [apply Hincl; cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
cbn [sv_denot]. ew_havocA. rewrite Z.add_0_r, (HC 44%nat 0%nat _ eq_refl eq_refl), unsigned_lit_small by lia. reflexivity.
- rewrite <- HU72. replace fattr with (U (havoc E 84 (map (getr regs2) CLOB)) (SExt true 32 (SOff 46 0)) mod 2 ^ (8 * Z.of_N 4%N)).
2:{ change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). apply U_sext32_low; [ew_havocA; exact (HC 46%nat 2%nat _ eq_refl eq_refl) | lia]. }
eapply (st_field_low ubs0segs _ _ _ 0%nat _ 88%nat _ 16 4%N _ _ HS' Hrg Hb); [apply Hincl; cbv; auto 10 | reflexivity | cbn; lia | reflexivity].
- rewrite <- HU72. replace fgen with (U (havoc E 84 (map (getr regs2) CLOB)) (SExt true 32 (SOff 47 0)) mod 2 ^ (8 * Z.of_N 4%N)).
2:{ change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). apply U_sext32_low; [ew_havocA; exact (HC 47%nat 3%nat _ eq_refl eq_refl) | lia]. }
eapply (st_field_low ubs0segs _ _ _ 0%nat _ 88%nat _ 20 4%N _ _ HS' Hrg Hb); [apply Hincl; cbv; auto 10 | reflexivity | cbn; lia | reflexivity].
- split; [exact VD | cbn; lia].
- split; [cbn [fst snd]; replace (nf + 26) with (nf + 24 + 2) by lia; exact VN | cbn; lia]. }
jbranch ubs0tbl HS.
+
assert (Xc6 : Z.land fattr 6 = 0).
{ clear - Hc HC Rfattr. rewrite branch_eq_U, U_and_lit, U_lit in Hc by lia. apply Z.eqb_eq in Hc. rewrite <- (land_low_mod _ 6 32) in Hc by lia.
lazymatch type of Hc with context [U ?Ex _] => rewrite (U_sext32_low Ex 46 fattr ltac:(ew_havocA; exact (HC 46%nat 2%nat fattr eq_refl eq_refl)) ltac:(lia)) in Hc end. exact Hc. }
clear Hc. jrun_to LAWS ubs0tbl_ok HS HJ2 AF_D1B.
{ wr_norm. eapply wr_ok_cons_gen with (k := 88%nat); [reflexivity | ew_havocA; rewrite Hq72; apply unsigned_lit_small; lia | | apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. replace a with (nf + (a - nf)) by lia. apply (Hwr2 (blocks L2 A2) (a - nf) Hnfin2). lia. }
cbn [ms_mem mkst] in HF, HF0.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> (a < nf \/ nf + 40 <= a) -> mbyte ubs0segs (ms_mem ms1) a = mbyte ubs0segs mem2 a).
{ intros a Ha W1. assert (HU72 : bv_unsigned (ew (havoc E 84 (map (getr regs2) CLOB)) 88) = nf) by (rewrite Hq72; apply unsigned_lit_small; lia).
clear - HF HF0 Ha W1 HU2 HU9 HU72.
mb_frame_with HF0 ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU9, ?HU72; lia). mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU9, ?HU72; lia). reflexivity. }
apply (GO _ _ (byte_at (ms_mem ms1) (nf + 28)) HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ2 K3); [| intros H6; exfalso; exact (H6 Xc6)].
apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|j]]]]]]; [ .. | destruct j; discriminate Hv];
first [ apply (NF5 _ _ HS ltac:(eexists; split; [reflexivity | split; [reflexivity | apply incl_chunks_sound; vm_compute; reflexivity]]) _ f v Hf Hv)
| cbn in Hf, Hv; injection Hf as <-; injection Hv as <-; apply field_byte_any;
apply (proj1 (heap_blocks _ _ LAWS L2 A2 (ms_mem ms1) md2 nf FRAME_SIZE 28 (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) Hnfin2 ltac:(lia))) ].
+
clear Hc. jrun_to LAWS ubs0tbl_ok HS HJ2 AF_D1B.
{ wr_norm. eapply wr_ok_cons_gen with (k := 88%nat); [reflexivity | ew_havocA; rewrite Hq72; apply unsigned_lit_small; lia | | apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. replace a with (nf + (a - nf)) by lia. apply (Hwr2 (blocks L2 A2) (a - nf) Hnfin2). lia. }
cbn [ms_mem mkst] in HF, HF0.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> (a < nf \/ nf + 40 <= a) -> mbyte ubs0segs (ms_mem ms1) a = mbyte ubs0segs mem2 a).
{ intros a Ha W1. assert (HU72 : bv_unsigned (ew (havoc E 84 (map (getr regs2) CLOB)) 88) = nf) by (rewrite Hq72; apply unsigned_lit_small; lia).
clear - HF HF0 Ha W1 HU2 HU9 HU72.
mb_frame_with HF0 ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU9, ?HU72; lia). mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU9, ?HU72; lia). reflexivity. }
apply (GO _ _ tidx HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ2 K3); [| intros _; reflexivity].
apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|j]]]]]]; [ .. | destruct j; discriminate Hv];
first [ apply (NF5 _ _ HS ltac:(eexists; split; [reflexivity | split; [reflexivity | apply incl_chunks_sound; vm_compute; reflexivity]]) _ f v Hf Hv)
| cbn in Hf, Hv; injection Hf as <-; injection Hv as <-;
assert (HU72 : bv_unsigned (ew (havoc E 84 (map (getr regs2) CLOB)) 88) = nf) by (rewrite Hq72; apply unsigned_lit_small; lia); rewrite <- HU72;
eapply (st_field ubs0segs _ _ _ 0%nat _ 88%nat _ 28 1%N (SOff 50 0) tidx HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia];
cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HC 50%nat 6%nat _ eq_refl eq_refl), unsigned_lit_small by lia; reflexivity ].
Qed.
End S.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
