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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI39 UI1i UI20 UI59 UI56 YI0x UI57
UI1h UI1g UI16 UI19 UI17.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition E1_g (i : nat) (p : option Z) : list YQ0b.region :=
if Nat.eqb i 1 then
[ af_Rg_part 0 8 0 0 p None None None; af_Rg_part 8 16 8 16 None None None None;
af_Rg_part 16 88 0 0 None None None None; af_Rg_part 92 96 92 96 None None None None ]
else
[ af_Rg_part 0 16 0 0 None p None None; af_Rg_part 16 24 16 24 None None None None;
af_Rg_part 24 88 0 0 None None None None; af_Rg_part 92 96 92 96 None None None None ].
Definition E1_regions (i : nat) (p : option Z) (prev : bool) : list YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32) :: E1_g i p ++
[ YQ0b.mkRegion (Some 18%nat) 32 34 32 34 [] ] ++
(if prev then [ af_Rfr_part (50 + i) 68 20 24 20 24 ; af_Rfr_part (50 + i) 68 32 33 32 33 ] else []).
Definition cond_a8 (z8 : bool) : acond := mkAC (if z8 then BC_EQ else BC_NE) (SAlu ALU_AND (SExt false 8 (SOff 56 0)) (SLit 8)) (SLit 0).
Definition ss_E1 (i : nat) (p : option Z) (prev z8 : bool) : sstate :=
mkSS AF_E (sr_set sr_atoms 20%bv (SLit (Z.of_nat i))) (E1_regions i p prev) None
(mkFacts (af_facts ++ (if prev then [((50 + i)%nat, mkAF 4096 (CEIL_MAX - 40) 4)] else [])) [cond_a8 z8] []).
Definition fnew (nf lpal' img' fattr fgen delay nlp ctidx d tb : Z) : frame_st :=
mkFrame nf lpal' img' fattr fgen delay nlp ctidx d tb.
Lemma LAY_Frame_split : LAY_Frame = LAY_FrameConfig ++ [(32, 1%N); (33, 1%N)].
Proof. reflexivity. Qed.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Lemma af_E1 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (CB rest FP : list (Z * Z))
(i : nat) (op : option frame_st) (nf lpal' img' ctidx : Z) (cfp lpal img fattr fgen delay nlp tidx t4 : Z),
let sp0 := spZ regs0 in
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 ->
cgif_at memc g s -> cgif_wf s N -> same_geom s s0 ->
(i = 1%nat \/ i = 2%nat) ->
nth_error (cg_frames s) i = Some None -> nth_error (cg_frames s) (i - 1) = Some op ->
(i = 2%nat -> op <> None) ->
(Z.land fattr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
obj_at ubs2segs memc cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cfp mod 8 = 0 -> sp0 <= cfp -> cfp + 32 <= 2 ^ 63 ->
obj_at ubs2segs memc nf LAY_FrameConfig [lpal'; img'; fattr; fgen; delay; nlp; ctidx] ->
(forall a, g <= a < g + CGIF_SIZE -> inFP FP a) ->
(forall f a, In (Some f) (cg_frames s) -> fr_ptr f <= a < fr_ptr f + FRAME_SIZE -> inFP FP a) ->
(forall blc k, In (nf, FRAME_SIZE) blc -> 0 <= k < FRAME_SIZE -> wr_byte ADDFRAME_STK sp0 FP (blocks L A) blc (nf + k)) ->
Permutation (blocks Lc Ac) (((nf, FRAME_SIZE) :: (img', N) :: (if Z.land fattr 1 =? 0 then [] else [(lpal', 3 * nlp)])) ++ cgif_blocks g s N ++ CB ++ rest) ->
af_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 64) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfp ->
getr regs1 18 = Z_to_bv 64 nf -> getr regs1 19 = Z_to_bv 64 t4 -> 0 <= t4 < 2 ^ 64 ->
getr regs1 20 = Z_to_bv 64 (Z.of_nat i) ->
af_untouched regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_E) memc (seg_rom ubs2segs)) mdc) (af_post API regs0 g N s0 CB rest FP L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s CB rest FP i op nf lpal' img' ctidx cfp lpal img fattr fgen delay nlp tidx t4 sp0
HJ Hid Hra0 Hal16 Hat Hwf Hgeom Hi Hinone Hiop Hi2 HnoCT Hcf Hcf8 Hcflo Hcfhi Hnf7 HFPg HFPfr HWnf HB HSV G2 G8 G9 G18 G19 Rt4 G20 HUT.
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & _ & _ & _ & _ & _ & _ & Hfwf).
set (NB := (nf, FRAME_SIZE) :: (img', N) :: (if Z.land fattr 1 =? 0 then [] else [(lpal', 3 * nlp)])) in HB.
assert (HB' : Permutation (blocks Lc Ac) (cgif_blocks g s N ++ (NB ++ CB ++ rest))).
{ eapply Permutation_trans; [exact HB|]. rewrite app_assoc. rewrite (app_assoc (cgif_blocks g s N)). apply Permutation_app; [apply Permutation_app_comm | apply Permutation_refl]. }
destruct (af_cgif_geom API Lc Ac memc mdc g s N (NB ++ CB ++ rest) HH0 HB') as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB' | left; reflexivity]).
assert (Hnfin : In (nf, FRAME_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc nf FRAME_SIZE HH0 Hnfin ltac:(lia)) as (Hn0 & Hn1 & Hn16).
assert (Hnsep : forall y, In y (cgif_blocks g s N) -> nf + FRAME_SIZE <= fst y \/ fst y + snd y <= nf).
{ intros y Hy. apply (heap_sep_perm _ _ LAWS Lc Ac memc mdc (nf, FRAME_SIZE) (((img', N) :: (if Z.land fattr 1 =? 0 then [] else [(lpal', 3 * nlp)])) ++ cgif_blocks g s N ++ CB ++ rest) y HH0 HB).
apply in_app_iff. right. apply in_app_iff. left. exact Hy. }
pose proof (Hnsep (g, CGIF_SIZE) ltac:(left; reflexivity)) as Hng. cbn [fst snd] in Hng.
pose proof (Hnsep (cg_raw s, RAW_SIZE) ltac:(right; left; reflexivity)) as Hnr. cbn [fst snd] in Hnr.
assert (Hnfr : forall f, In (Some f) (cg_frames s) -> nf + FRAME_SIZE <= fr_ptr f \/ fr_ptr f + FRAME_SIZE <= nf).
{ intros f Hf. apply (Hnsep (fr_ptr f, FRAME_SIZE)). unfold cgif_blocks. right. right. apply in_app_iff. right. apply af_frames_blocks_ptr_in. exact Hf. }
pose proof Hat as (Hobj & Hraw & Hfrs).
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf.
pose proof (Rcf 2%nat fattr eq_refl) as Rfattr. cbn [nth snd LAY_FrameConfig Z.of_N] in Rfattr.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg.
pose proof (Rg 5%nat (cg_attr s) eq_refl) as Rattr. cbn [nth snd LAY_CGIF Z.of_N] in Rattr.
set (more := match op with Some fp => frame_vals fp | None => [] end).
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s more).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HKr regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n j r, _ -> _ -> ew E n = _) as HKr.
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n j v, _ -> _ -> ew E n = _) as HC.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (af_HM regs1 regs0 lpal img fattr fgen delay nlp tidx s more : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cfp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = nf) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 0 64 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc sp0 regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
assert (Hgw : forall k, 0 <= k < CGIF_SIZE -> writable_at ubs2segs memc (g + k)).
{ intros k Hk. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE k HH0 Hgin ltac:(lia))). }
assert (HRG : forall lo hi wlo whi p, 0 <= lo -> hi <= 96 -> 0 <= wlo -> whi <= 96 ->
pin_ok p 0 ->
(p = None \/ op = None) ->
region_ok ubs2segs E memc (if Nat.eqb i 1 then af_Rg_part lo hi wlo whi p None None None else af_Rg_part lo hi wlo whi None p None None)).
{ intros lo hi wlo whi p Hlo Hhi Hwlo Hwhi Hp Hpn.
assert (P : pin_ok p (frame_ptr (nth (i - 1) (cg_frames s) None))).
{ destruct Hpn as [-> | Hop]; [exact I|]. subst op. rewrite (nth_error_nth _ _ _ Hiop). exact Hp. }
destruct Hi as [-> | ->]; cbn [Nat.eqb]; cbn [Nat.sub] in P;
(apply (af_Rg_part_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s more memc g); [exact HU8 | lia | lia | exact Hobj | | | | | lia | lia | intros k Hk; apply Hgw; lia]);
first [exact P | exact I]. }
assert (HR5 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 18%nat) 32 34 32 34 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc nf FRAME_SIZE o HH0 Hnfin ltac:(lia))). }
assert (HFA : atoms_ok E af_facts).
{ cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU9. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
repeat split; try lia.
replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HA8 : U E (SAlu ALU_AND (SExt false 8 (SOff 56 0)) (SLit 8)) = Z.land (cg_attr s) 8).
{ rewrite U_and_lit by lia. rewrite U_zext, (U_atom _ 56 (cg_attr s) (HX 56%nat 5%nat _ eq_refl eq_refl)) by lia.
change (2 ^ Z.of_N 8) with (2 ^ 8). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. f_equal. }
assert (CONT : forall ss ms' (s1 : cgif_st) (fn : frame_st) (op1 : option frame_st),
st_ok ubs2segs E ss ms' -> ss_pc ss = AF_E2 -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 10%bv = SOff 8 (8 * Z.of_nat i) -> sr_get (ss_regs ss) 18%bv = SOff 18 0 ->
sr_get (ss_regs ss) 19%bv = SOff 19 0 -> sr_get (ss_regs ss) 20%bv = SLit (Z.of_nat i) -> sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 ->
sr_get (ss_regs ss) 25%bv = SOff 25 0 -> sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
journal ubs2_msyms MR ADDFRAME_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
cgif_at (ms_mem ms') g s1 -> cgif_wf s1 N -> same_geom s1 s0 ->
nth_error (cg_frames s1) i = Some (Some fn) -> fr_ptr fn = nf ->
nth_error (cg_frames s1) (i - 1) = Some op1 -> (forall fp1, op1 = Some fp1 -> exists fp0, op = Some fp0 /\ fr_ptr fp1 = fr_ptr fp0) ->
Permutation (cgif_blocks g s1 N) (NB ++ cgif_blocks g s N) ->
obj_at ubs2segs (ms_mem ms') cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
af_saved_ok (ms_mem ms') sp0 regs0 ->
SR ubs2segs (mkCfg ms' mdc) (af_post API regs0 g N s0 CB rest FP L A mem md)).
{ intros ss ms' s1 fn op1 HS' Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q10 Q18 Q19 Q20 Q23 Q24 Q25 Q26 Q27 HJ' Hat' Hwf' Hgeom' Hifn Hptr Hiop1 Hop1 Hblk Hcf' HSV'.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hw. rewrite (st_ok_reg ubs2segs E ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hw. }
eapply (af_E2 API IMG L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s1 CB rest FP i fn op1 cfp lpal img fattr fgen delay nlp tidx t4);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Hat' | exact Hwf' | exact Hgeom' | exact Hi | exact Hifn | exact Hiop1 | exact Hcf' | exact Hcf8 | exact Hcflo | exact Hcfhi
| exact HFPg
| intros fp a Hfp Ha; destruct (Hop1 fp Hfp) as (fp0 & Hfp0 & Hpp); subst op;
apply (HFPfr fp0); [eapply nth_error_In; exact Hiop | rewrite <- Hpp; exact Ha]
| rewrite Hptr; exact HWnf
| eapply Permutation_trans; [exact HB|]; rewrite app_assoc; apply Permutation_app; [apply Permutation_sym; exact Hblk | apply Permutation_refl]
| exact HSV'
| apply (RG _ _ _ Q2); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| apply (RG _ _ _ Q8); rewrite (HE 8%nat 8%bv eq_refl); exact G8
| apply (RG _ _ _ Q9); rewrite (HE 9%nat 9%bv eq_refl); exact G9
| apply (RG _ _ _ Q18); rewrite (HE 18%nat 18%bv eq_refl), Hptr; exact G18
| apply (RG _ _ _ Q19); rewrite (HE 19%nat 19%bv eq_refl); exact G19
| exact Rt4
| rewrite (st_ok_reg ubs2segs E ss ms' 20%bv HS'), Q20; cbn [sv_denot]; reflexivity
| rewrite (st_ok_reg ubs2segs E ss ms' 10%bv HS'), Q10; cbn [sv_denot]; rewrite HU8; reflexivity
| split; [|split; [|split; [|split; [|split; [|split]]]]]; [ apply (RG _ _ _ Q3); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q23); rewrite (HE 23%nat 23%bv eq_refl); exact G23
| apply (RG _ _ _ Q24); rewrite (HE 24%nat 24%bv eq_refl); exact G24
| apply (RG _ _ _ Q25); rewrite (HE 25%nat 25%bv eq_refl); exact G25
| apply (RG _ _ _ Q26); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ] ]. }
assert (HWR : forall p prev blc, In (g, CGIF_SIZE) blc -> In (nf, FRAME_SIZE) blc ->
(prev = true -> exists fp, op = Some fp /\ In (fr_ptr fp, FRAME_SIZE) blc /\ bv_unsigned (ew E (50 + i)) = fr_ptr fp) ->
wr_ok E (E1_regions i p prev) ADDFRAME_STK sp0 FP (blocks L A) blc).
{ intros p prev blc Hg' Hn' Hp'. unfold E1_regions.
apply wr_ok_cons_ro; [cbn; lia|].
assert (WG : forall lo hi wlo whi a b c d rs, 0 <= wlo -> whi <= 96 ->
wr_ok E rs ADDFRAME_STK sp0 FP (blocks L A) blc -> wr_ok E (af_Rg_part lo hi wlo whi a b c d :: rs) ADDFRAME_STK sp0 FP (blocks L A) blc).
{ intros lo hi wlo whi a b c d rs Hwlo Hwhi Hrs. eapply wr_ok_cons_block with (m := CGIF_SIZE);
[ reflexivity | exact HU8 | exact Hg' | cbn [r_wlo af_Rg_part]; exact Hwlo | cbn [r_whi af_Rg_part]; clear - Hwhi HGSv; lia | cbn [r_wlo r_whi af_Rg_part]; intros x Hx; apply HFPg; clear - Hx Hwlo Hwhi HGSv; lia | exact Hrs ]. }
assert (WT : forall rs, wr_ok E rs ADDFRAME_STK sp0 FP (blocks L A) blc ->
wr_ok E ((YQ0b.mkRegion (Some 18%nat) 32 34 32 34 []) :: rs) ADDFRAME_STK sp0 FP (blocks L A) blc).
{ intros rs Hrs. eapply wr_ok_cons_gen with (k := 18%nat); [reflexivity | exact HU18 | | exact Hrs].
cbn [r_wlo r_whi]. intros a Ha. replace a with (nf + (a - nf)) by lia. apply HWnf; [exact Hn' | lia]. }
assert (WP : forall lo hi rs, prev = true -> 0 <= lo -> hi <= 40 -> wr_ok E rs ADDFRAME_STK sp0 FP (blocks L A) blc ->
wr_ok E (af_Rfr_part (50 + i) 68 lo hi lo hi :: rs) ADDFRAME_STK sp0 FP (blocks L A) blc).
{ intros lo hi rs Hpv Hlo Hhi Hrs. destruct (Hp' Hpv) as (fp & Hop & Hb & Hu).
- eapply wr_ok_cons_block with (m := FRAME_SIZE);
[ reflexivity | exact Hu | exact Hb | cbn [r_wlo af_Rfr_part]; exact Hlo | cbn [r_whi af_Rfr_part]; clear - Hhi HFSv; lia | cbn [r_wlo r_whi af_Rfr_part]; intros a Ha; apply (HFPfr fp); [subst op; eapply nth_error_In; exact Hiop | clear - Ha Hlo Hhi HFSv; lia] | exact Hrs ]. }
assert (WE : wr_ok E (if prev then [af_Rfr_part (50 + i) 68 20 24 20 24; af_Rfr_part (50 + i) 68 32 33 32 33] else []) ADDFRAME_STK sp0 FP (blocks L A) blc).
{ destruct prev; [| apply wr_ok_nil]. apply (WP 20 24); [reflexivity | lia | lia |]. apply (WP 32 33); [reflexivity | lia | lia |]. apply wr_ok_nil. }
unfold E1_g. destruct (Nat.eqb i 1); cbn [app]; do 4 (apply WG; [lia | lia |]); apply WT; exact WE. }
destruct (Z.eq_dec (Z.land (cg_attr s) 8) 0) as [Hz8|Hz8].
-
assert (HCT : conds_ok E [cond_a8 true]).
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok, cond_a8. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, HA8, U_lit, Hz8 by lia. reflexivity. }
assert (HPD : pairwise_disjoint E (E1_regions i None false)).
{ clear - Hi HU2 HU8 HU18 Hng Hg1 Hn1 Hceil HASv Hac HGSv HFSv.
unfold E1_regions, E1_g. destruct Hi as [-> | ->]; cbn [Nat.eqb app]; unfold af_Rg_part; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val];
rewrite ?HU2, ?HU8, ?HU18; repeat split; lia. }
assert (HS : st_ok ubs2segs E (ss_E1 i None false true) (mkst regs1 (Z_to_bv 64 AF_E) memc (seg_rom ubs2segs))).
{ unfold ss_E1. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H; discriminate H | cbn [sv_denot]; rewrite G20; reflexivity].
- destruct Hi as [-> | ->]; vm_compute; reflexivity.
- unfold E1_regions. constructor; [exact HR0|]. unfold E1_g. destruct Hi as [-> | ->]; cbn [Nat.eqb app];
(constructor; [apply HRG; cbn; first [exact I | left; reflexivity | lia] |]);
(constructor; [apply HRG; cbn; first [exact I | left; reflexivity | lia] |]);
(constructor; [apply HRG; cbn; first [exact I | left; reflexivity | lia] |]);
(constructor; [apply HRG; cbn; first [exact I | left; reflexivity | lia] |]);
(constructor; [exact HR5 | constructor]).
- exact HPD.
- split; [rewrite app_nil_r; exact HFA | split; [exact HCT | exact I]]. }
clear HPD HCT HR0 HR5 HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_E) memc (seg_rom ubs2segs))) in HJ.
destruct Hi as [-> | ->].
+ jrun_to LAWS ubs2tbl_ok HS HJ AF_E2. { wr_norm. apply (HWR None false); [exact Hgin | exact Hnfin | intros H0; discriminate H0]. }
cbn [ms_mem mkst] in HF.
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> (a < g + 8 \/ g + 16 <= a) -> (a < g + 92 \/ g + 96 <= a) -> (a < nf + 32 \/ nf + 34 <= a) ->
mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha W1 W2 W3. clear - HF Ha W1 W2 W3 HU2 HU8 HU18.
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU18; lia). reflexivity. }
clear HF.
set (tb := byte_at (ms_mem ms) (nf + 33)).
set (f1 := fnew nf lpal' img' fattr fgen delay nlp ctidx 4 tb).
assert (Hnewf : obj_at ubs2segs (ms_mem ms) nf LAY_Frame (frame_vals f1)).
{ rewrite LAY_Frame_split. apply (proj2 (obj_at_app ubs2segs (ms_mem ms) nf LAY_FrameConfig [(32, 1%N); (33, 1%N)] [lpal'; img'; fattr; fgen; delay; nlp; ctidx] [4; tb] ltac:(reflexivity))). split.
- eapply obj_at_transport_range; [exact Hnf7 | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hng Hn0 Hn1 HGSv HFSv Hac; lia.
- cbn [obj_at]. split; [|split; [|exact I]].
+ rewrite <- HU18. replace 4 with (U E (SLit 4) mod 256) at 2 by reflexivity.
eapply (st_field_byte0 ubs2segs E _ _ 5%nat _ 18%nat _ 32 2%N (SLit 4) HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn; lia | cbn; lia].
+ subst tb. apply field_byte_any. apply (proj1 (heap_blocks _ _ LAWS Lc Ac (ms_mem ms) mdc nf FRAME_SIZE 33 (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hnfin ltac:(lia))). }
apply (CONT _ _ (set_ihead (upd_frame s 1 f1) 1) f1 op HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
* split; [|split].
-- rewrite cgif_vals_set_ihead_ls, (cgif_vals_ins_frame s 1 f1) by lia.
eapply (obj_at_upd ubs2segs memc (ms_mem ms) g LAY_CGIF CGIF_SIZE (cgif_vals s) _ [1%nat; 16%nat] [(8, 16); (92, 96)] Hobj (proj1 LAY_CGIF_ok));
[vm_compute; reflexivity | reflexivity | | |].
++ intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 Hw]. apply in_wins_cons_false in Hw as [W2 _].
apply KEPT; clear - Hk W1 W2 Hng HGSv HFSv Hg0 Hg1 Hac; lia.
++ intros j f v' [<-|[<-|[]]] Hf Hv'; cbn in Hf, Hv'; injection Hf as <-; injection Hv' as <-.
** rewrite <- HU8. eapply (st_field ubs2segs E _ _ 2%nat _ 8%nat _ 8 8%N (SOff 18 0) nf HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HU18. reflexivity.
** rewrite <- HU8. eapply (st_field ubs2segs E _ _ 4%nat _ 8%nat _ 92 4%N (SLit 1) 1 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia].
++ intros j Hj. do 17 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; cbv; auto] |]). reflexivity.
-- rewrite cg_raw_set_ihead, cg_raw_upd_frame.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros k Hk. apply KEPT; clear - Hk Hrg Hnr HGSv HRSv HFSv Hr0 Hr1 Hac; lia.
-- rewrite cg_frames_set_ihead. apply (frames_at_upd memc (ms_mem ms) s 1 None f1 Hfrs Hinone Hnewf).
intros j x Hj Hne k Hk.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & X2).
pose proof (Hnfr x ltac:(eapply nth_error_In; exact Hj)) as X3.
apply KEPT; clear - Hk X0 X1 X2 X3 HGSv HFSv Hac; lia.
* apply cgif_wf_set_ihead; [| left; reflexivity].
apply (cgif_wf_ins_frame s N 1 f1 Hwf Hinone). split; [exact HnoCT | left; reflexivity].
* apply same_geom_set_ihead, same_geom_upd_frame. exact Hgeom.
* rewrite cg_frames_set_ihead. apply (nth_error_upd_frame_same s 1 None f1 Hinone).
* reflexivity.
* rewrite cg_frames_set_ihead, nth_error_upd_frame_other by lia. exact Hiop.
* intros fp1 ->. exists fp1. split; reflexivity.
* rewrite cgif_blocks_set_ihead. apply (cgif_blocks_ins_frame g s N 1 f1 Hinone).
* eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hcflo Hcfhi Hceil Hg1 Hn1 HASv HGSv HFSv Hac; lia.
* apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply KEPT; clear - Ha Hceil Hsp063 Hg1 Hn1 HASv HGSv HFSv Hac; lia.
+
jrun_to LAWS ubs2tbl_ok HS HJ AF_E2. { wr_norm. apply (HWR None false); [exact Hgin | exact Hnfin | intros H0; discriminate H0]. }
cbn [ms_mem mkst] in HF.
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> (a < g + 16 \/ g + 24 <= a) -> (a < g + 92 \/ g + 96 <= a) -> (a < nf + 32 \/ nf + 34 <= a) ->
mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha W1 W2 W3. clear - HF Ha W1 W2 W3 HU2 HU8 HU18.
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU18; lia). reflexivity. }
clear HF.
set (tb := byte_at (ms_mem ms) (nf + 33)).
set (f1 := fnew nf lpal' img' fattr fgen delay nlp ctidx 4 tb).
assert (Hnewf : obj_at ubs2segs (ms_mem ms) nf LAY_Frame (frame_vals f1)).
{ rewrite LAY_Frame_split. apply (proj2 (obj_at_app ubs2segs (ms_mem ms) nf LAY_FrameConfig [(32, 1%N); (33, 1%N)] [lpal'; img'; fattr; fgen; delay; nlp; ctidx] [4; tb] ltac:(reflexivity))). split.
- eapply obj_at_transport_range; [exact Hnf7 | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hng Hn0 Hn1 HGSv HFSv Hac; lia.
- cbn [obj_at]. split; [|split; [|exact I]].
+ rewrite <- HU18. replace 4 with (U E (SLit 4) mod 256) at 2 by reflexivity.
eapply (st_field_byte0 ubs2segs E _ _ 5%nat _ 18%nat _ 32 2%N (SLit 4) HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn; lia | cbn; lia].
+ subst tb. apply field_byte_any. apply (proj1 (heap_blocks _ _ LAWS Lc Ac (ms_mem ms) mdc nf FRAME_SIZE 33 (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hnfin ltac:(lia))). }
apply (CONT _ _ (set_ihead (upd_frame s 2 f1) 2) f1 op HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
* split; [|split].
-- rewrite cgif_vals_set_ihead_ls, (cgif_vals_ins_frame s 2 f1) by lia.
eapply (obj_at_upd ubs2segs memc (ms_mem ms) g LAY_CGIF CGIF_SIZE (cgif_vals s) _ [2%nat; 16%nat] [(16, 24); (92, 96)] Hobj (proj1 LAY_CGIF_ok));
[vm_compute; reflexivity | reflexivity | | |].
++ intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 Hw]. apply in_wins_cons_false in Hw as [W2 _].
apply KEPT; clear - Hk W1 W2 Hng HGSv HFSv Hg0 Hg1 Hac; lia.
++ intros j f v' [<-|[<-|[]]] Hf Hv'; cbn in Hf, Hv'; injection Hf as <-; injection Hv' as <-.
** rewrite <- HU8. eapply (st_field ubs2segs E _ _ 2%nat _ 8%nat _ 16 8%N (SOff 18 0) nf HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HU18. reflexivity.
** rewrite <- HU8. eapply (st_field ubs2segs E _ _ 4%nat _ 8%nat _ 92 4%N (SLit 2) 2 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia].
++ intros j Hj. do 17 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; cbv; auto] |]). reflexivity.
-- rewrite cg_raw_set_ihead, cg_raw_upd_frame.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros k Hk. apply KEPT; clear - Hk Hrg Hnr HGSv HRSv HFSv Hr0 Hr1 Hac; lia.
-- rewrite cg_frames_set_ihead. apply (frames_at_upd memc (ms_mem ms) s 2 None f1 Hfrs Hinone Hnewf).
intros j x Hj Hne k Hk.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & X2).
pose proof (Hnfr x ltac:(eapply nth_error_In; exact Hj)) as X3.
apply KEPT; clear - Hk X0 X1 X2 X3 HGSv HFSv Hac; lia.
* apply cgif_wf_set_ihead; [| right; split; [reflexivity | rewrite (nth_upd_frame_other s 2 1) by lia; rewrite (nth_error_nth _ _ _ Hiop); apply Hi2; reflexivity]].
apply (cgif_wf_ins_frame s N 2 f1 Hwf Hinone). split; [exact HnoCT | left; reflexivity].
* apply same_geom_set_ihead, same_geom_upd_frame. exact Hgeom.
* rewrite cg_frames_set_ihead. apply (nth_error_upd_frame_same s 2 None f1 Hinone).
* reflexivity.
* rewrite cg_frames_set_ihead, nth_error_upd_frame_other by lia. exact Hiop.
* intros fp1 ->. exists fp1. split; reflexivity.
* rewrite cgif_blocks_set_ihead. apply (cgif_blocks_ins_frame g s N 2 f1 Hinone).
* eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hcflo Hcfhi Hceil Hg1 Hn1 HASv HGSv HFSv Hac; lia.
* apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply KEPT; clear - Ha Hceil Hsp063 Hg1 Hn1 HASv HGSv HFSv Hac; lia.
-
assert (HCF : conds_ok E [cond_a8 false]).
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok, cond_a8. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, HA8, U_lit by lia.
destruct (Z.eqb_spec (Z.land (cg_attr s) 8) 0); [lia | reflexivity]. }
destruct op as [fp|].
+
assert (Hfpin : In (Some fp) (cg_frames s)) by (eapply nth_error_In; exact Hiop).
destruct (Hfgeom fp Hfpin) as (Hp0 & Hp1 & Hpg).
destruct (af_frame_geom API Lc Ac memc mdc g s N (NB ++ CB ++ rest) fp HH0 HB' Hfpin) as (Hpblk & _ & _).
pose proof (af_raw_frame_sep API Lc Ac memc mdc g s N (NB ++ CB ++ rest) fp HH0 HB' Hfpin) as Hpr_raw.
pose proof (Hnfr fp Hfpin) as Hnp.
assert (HUp : bv_unsigned (ew E (50 + i)) = fr_ptr fp).
{ rewrite (HX (50 + i)%nat (i - 1)%nat (fr_ptr fp) ltac:(lia)); [apply unsigned_lit_small; lia|].
destruct Hi as [-> | ->]; cbn; rewrite (nth_error_nth' _ None) in Hiop by (rewrite Hlen; lia); injection Hiop as Hn; rewrite Hn; reflexivity. }
assert (HR6 : forall lo hi, 0 <= lo -> hi <= 40 -> region_ok ubs2segs E memc (af_Rfr_part (50 + i) 68 lo hi lo hi)).
{ intros lo hi Hlo Hhi. eapply (af_Rfr_part_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s more memc (50 + i) (fr_ptr fp) fp 68);
[exact HUp | reflexivity | lia | lia | exact (Hfrs fp Hfpin) | lia | intros j v Hj; subst more; rewrite Nat.sub_diag; exact Hj | exact Hlo | exact Hhi |].
intros k Hk. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_ptr fp) FRAME_SIZE k HH0 Hpblk ltac:(lia))). }
assert (HPD : pairwise_disjoint E (E1_regions i None true)).
{ clear - Hi HU2 HU8 HU18 HUp Hng Hnp Hpg Hg1 Hn1 Hp1 Hceil HASv Hac HGSv HFSv.
unfold E1_regions, E1_g. destruct Hi as [-> | ->]; cbn [Nat.eqb app]; unfold af_Rg_part, af_Rfr_part; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val];
rewrite ?HU2, ?HU8, ?HU18, ?HUp; repeat split; lia. }
assert (HFA2 : atoms_ok E (af_facts ++ [((50 + i)%nat, mkAF 4096 (CEIL_MAX - 40) 4)])).
{ apply atoms_ok_app; [exact HFA|].
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HUp. change (2 ^ 4) with 16.
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fp) FRAME_SIZE HH0 Hpblk ltac:(lia)) as (_ & _ & Hp16).
repeat split; lia. }
assert (HS : st_ok ubs2segs E (ss_E1 i None true false) (mkst regs1 (Z_to_bv 64 AF_E) memc (seg_rom ubs2segs))).
{ unfold ss_E1. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H; discriminate H | cbn [sv_denot]; rewrite G20; reflexivity].
- destruct Hi as [-> | ->]; vm_compute; reflexivity.
- unfold E1_regions. constructor; [exact HR0|]. unfold E1_g. destruct Hi as [-> | ->]; cbn [Nat.eqb app];
(constructor; [apply HRG; cbn; first [exact I | left; reflexivity | lia] |]);
(constructor; [apply HRG; cbn; first [exact I | left; reflexivity | lia] |]);
(constructor; [apply HRG; cbn; first [exact I | left; reflexivity | lia] |]);
(constructor; [apply HRG; cbn; first [exact I | left; reflexivity | lia] |]);
(constructor; [exact HR5 |]); (constructor; [apply HR6; lia|]); (constructor; [apply HR6; lia|]); constructor.
- exact HPD.
- split; [exact HFA2 | split; [exact HCF | exact I]]. }
clear HPD HCF HR0 HR5 HR6 HFA HFA2.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_E) memc (seg_rom ubs2segs))) in HJ.
destruct Hi as [-> | ->]; cbn [Nat.add] in HUp.
* jrun_to LAWS ubs2tbl_ok HS HJ AF_E2.
{ wr_norm. apply (HWR None true); [exact Hgin | exact Hnfin | intros _; exists fp; split; [reflexivity | split; [exact Hpblk | exact HUp]]]. }
cbn [ms_mem mkst] in HF.
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> (a < g + 8 \/ g + 16 <= a) -> (a < g + 92 \/ g + 96 <= a) -> (a < nf + 32 \/ nf + 34 <= a) ->
(a < fr_ptr fp + 20 \/ fr_ptr fp + 24 <= a) -> (a < fr_ptr fp + 32 \/ fr_ptr fp + 33 <= a) ->
mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha W1 W2 W3 W4 W5. clear - HF Ha W1 W2 W3 W4 W5 HU2 HU8 HU18 HUp.
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU18, ?HUp; lia). reflexivity. }
clear HF.
set (tb := byte_at (ms_mem ms) (nf + 33)).
set (f1 := fnew nf lpal' img' fattr fgen delay nlp ctidx 8 tb).
lazymatch type of HS with st_ok _ _ _ ?msf =>
set (gen' := U E (SAlu ALU_AND (SExt false 32 (SOff 71 0)) (SLit (-4))) mod 2 ^ 32) end.
set (fp' := set_fr_gen_disp fp gen' 8).
assert (Hnewf : obj_at ubs2segs (ms_mem ms) nf LAY_Frame (frame_vals f1)).
{ rewrite LAY_Frame_split. apply (proj2 (obj_at_app ubs2segs (ms_mem ms) nf LAY_FrameConfig [(32, 1%N); (33, 1%N)] [lpal'; img'; fattr; fgen; delay; nlp; ctidx] [8; tb] ltac:(reflexivity))). split.
- eapply obj_at_transport_range; [exact Hnf7 | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hng Hnp Hn0 Hn1 HGSv HFSv Hac; lia.
- cbn [obj_at]. split; [|split; [|exact I]].
+ rewrite <- HU18. eapply (st_field ubs2segs E _ _ 5%nat _ 18%nat _ 32 1%N (SLit 8) 8 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia].
+ subst tb. apply field_byte_any. apply (proj1 (heap_blocks _ _ LAWS Lc Ac (ms_mem ms) mdc nf FRAME_SIZE 33 (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hnfin ltac:(lia))). }
assert (Hnewp : obj_at ubs2segs (ms_mem ms) (fr_ptr fp') LAY_Frame (frame_vals fp')).
{ subst fp'. cbn [fr_ptr set_fr_gen_disp].
eapply (obj_at_upd ubs2segs memc (ms_mem ms) (fr_ptr fp) LAY_Frame FRAME_SIZE (frame_vals fp) _ [3%nat; 7%nat] [(20, 24); (32, 33)] (Hfrs fp Hfpin) (proj1 LAY_Frame_ok));
[vm_compute; reflexivity | reflexivity | | |].
- intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 Hw]. apply in_wins_cons_false in Hw as [W2 _].
apply KEPT; clear - Hk W1 W2 Hnp Hpg HGSv HFSv Hp0 Hp1 Hac; lia.
- intros j f v' [<-|[<-|[]]] Hf Hv'; cbn in Hf, Hv'; injection Hf as <-; injection Hv' as <-.
+ rewrite <- HUp. eapply (st_field_low ubs2segs E _ _ 6%nat _ 51%nat _ 20 4%N _ _ HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn; lia | reflexivity].
+ rewrite <- HUp. eapply (st_field ubs2segs E _ _ 7%nat _ 51%nat _ 32 1%N (SLit 8) 8 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia].
- intros j Hj. do 9 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; cbv; auto] |]). reflexivity. }
apply (CONT _ _ (set_ihead (upd_frame (upd_frame s 1 f1) 0 fp') 1) f1 (Some fp') HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
-- split; [|split].
++ rewrite cgif_vals_set_ihead_ls, (cgif_vals_upd_frame _ 0 fp fp') by (first [rewrite nth_error_upd_frame_other by lia; exact Hiop | reflexivity]).
rewrite (cgif_vals_ins_frame s 1 f1) by lia.
eapply (obj_at_upd ubs2segs memc (ms_mem ms) g LAY_CGIF CGIF_SIZE (cgif_vals s) _ [1%nat; 16%nat] [(8, 16); (92, 96)] Hobj (proj1 LAY_CGIF_ok));
[vm_compute; reflexivity | reflexivity | | |].
** intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 Hw]. apply in_wins_cons_false in Hw as [W2 _].
apply KEPT; clear - Hk W1 W2 Hng Hpg HGSv HFSv Hg0 Hg1 Hac; lia.
** intros j f v' [<-|[<-|[]]] Hf Hv'; cbn in Hf, Hv'; injection Hf as <-; injection Hv' as <-.
{ rewrite <- HU8. eapply (st_field ubs2segs E _ _ 2%nat _ 8%nat _ 8 8%N (SOff 18 0) nf HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HU18. reflexivity. }
{ rewrite <- HU8. eapply (st_field ubs2segs E _ _ 4%nat _ 8%nat _ 92 4%N (SLit 1) 1 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia]. }
** intros j Hj. do 17 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; cbv; auto] |]). reflexivity.
++ rewrite cg_raw_set_ihead, !cg_raw_upd_frame.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros k Hk. apply KEPT; clear - Hk Hrg Hnr Hpr_raw HGSv HRSv HFSv Hr0 Hr1 Hac; lia.
++ rewrite cg_frames_set_ihead. apply (frames_at_upd2 memc (ms_mem ms) s 1 0 None f1 (Some fp) fp' Hfrs Hinone Hiop ltac:(lia) Hnewf Hnewp).
intros j x Hj Hj1 Hj2 k Hk.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & X2).
pose proof (Hnfr x ltac:(eapply nth_error_In; exact Hj)) as X3.
pose proof (af_frames_sep API Lc Ac memc mdc g s N (NB ++ CB ++ rest) 0 j fp x HH0 HB' Hiop Hj ltac:(clear - Hj2; lia)) as X4.
apply KEPT; clear - Hk X0 X1 X2 X3 X4 HGSv HFSv Hac; lia.
-- apply cgif_wf_set_ihead; [| left; reflexivity].
apply (cgif_wf_upd_frame _ N 0 fp fp'); [apply (cgif_wf_ins_frame s N 1 f1 Hwf Hinone) | rewrite nth_error_upd_frame_other by lia; exact Hiop |].
++ split; [exact HnoCT | right; reflexivity].
++ rewrite cg_attr_upd_frame. split; [| right; reflexivity]. cbn [fp' set_fr_gen_disp fr_attr]. exact (proj1 (Hfwf fp Hfpin)).
-- apply same_geom_set_ihead, same_geom_upd_frame, same_geom_upd_frame. exact Hgeom.
-- rewrite cg_frames_set_ihead, nth_error_upd_frame_other by lia. apply (nth_error_upd_frame_same s 1 None f1 Hinone).
-- reflexivity.
-- rewrite cg_frames_set_ihead. apply (nth_error_upd_frame_same _ 0 (Some fp) fp'). rewrite nth_error_upd_frame_other by lia. exact Hiop.
-- intros fp1 Hfp1. injection Hfp1 as <-. exists fp. split; reflexivity.
-- rewrite cgif_blocks_set_ihead, (cgif_blocks_upd_frame _ _ N 0 fp fp') by (first [rewrite nth_error_upd_frame_other by lia; exact Hiop | reflexivity]).
apply (cgif_blocks_ins_frame g s N 1 f1 Hinone).
-- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hcflo Hcfhi Hceil Hg1 Hn1 Hp1 HASv HGSv HFSv Hac; lia.
-- apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply KEPT; clear - Ha Hceil Hsp063 Hg1 Hn1 Hp1 HASv HGSv HFSv Hac; lia.
*
jrun_to LAWS ubs2tbl_ok HS HJ AF_E2.
{ wr_norm. apply (HWR None true); [exact Hgin | exact Hnfin | intros _; exists fp; split; [reflexivity | split; [exact Hpblk | exact HUp]]]. }
cbn [ms_mem mkst] in HF.
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> (a < g + 16 \/ g + 24 <= a) -> (a < g + 92 \/ g + 96 <= a) -> (a < nf + 32 \/ nf + 34 <= a) ->
(a < fr_ptr fp + 20 \/ fr_ptr fp + 24 <= a) -> (a < fr_ptr fp + 32 \/ fr_ptr fp + 33 <= a) ->
mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha W1 W2 W3 W4 W5. clear - HF Ha W1 W2 W3 W4 W5 HU2 HU8 HU18 HUp.
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU18, ?HUp; lia). reflexivity. }
clear HF.
set (tb := byte_at (ms_mem ms) (nf + 33)).
set (f1 := fnew nf lpal' img' fattr fgen delay nlp ctidx 8 tb).
lazymatch type of HS with st_ok _ _ _ ?msf =>
set (gen' := U E (SAlu ALU_AND (SExt false 32 (SOff 71 0)) (SLit (-4))) mod 2 ^ 32) end.
set (fp' := set_fr_gen_disp fp gen' 8).
assert (Hnewf : obj_at ubs2segs (ms_mem ms) nf LAY_Frame (frame_vals f1)).
{ rewrite LAY_Frame_split. apply (proj2 (obj_at_app ubs2segs (ms_mem ms) nf LAY_FrameConfig [(32, 1%N); (33, 1%N)] [lpal'; img'; fattr; fgen; delay; nlp; ctidx] [8; tb] ltac:(reflexivity))). split.
- eapply obj_at_transport_range; [exact Hnf7 | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hng Hnp Hn0 Hn1 HGSv HFSv Hac; lia.
- cbn [obj_at]. split; [|split; [|exact I]].
+ rewrite <- HU18. eapply (st_field ubs2segs E _ _ 5%nat _ 18%nat _ 32 1%N (SLit 8) 8 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia].
+ subst tb. apply field_byte_any. apply (proj1 (heap_blocks _ _ LAWS Lc Ac (ms_mem ms) mdc nf FRAME_SIZE 33 (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hnfin ltac:(lia))). }
assert (Hnewp : obj_at ubs2segs (ms_mem ms) (fr_ptr fp') LAY_Frame (frame_vals fp')).
{ subst fp'. cbn [fr_ptr set_fr_gen_disp].
eapply (obj_at_upd ubs2segs memc (ms_mem ms) (fr_ptr fp) LAY_Frame FRAME_SIZE (frame_vals fp) _ [3%nat; 7%nat] [(20, 24); (32, 33)] (Hfrs fp Hfpin) (proj1 LAY_Frame_ok));
[vm_compute; reflexivity | reflexivity | | |].
- intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 Hw]. apply in_wins_cons_false in Hw as [W2 _].
apply KEPT; clear - Hk W1 W2 Hnp Hpg HGSv HFSv Hp0 Hp1 Hac; lia.
- intros j f v' [<-|[<-|[]]] Hf Hv'; cbn in Hf, Hv'; injection Hf as <-; injection Hv' as <-.
+ rewrite <- HUp. eapply (st_field_low ubs2segs E _ _ 6%nat _ 52%nat _ 20 4%N _ _ HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | cbn; lia | reflexivity].
+ rewrite <- HUp. eapply (st_field ubs2segs E _ _ 7%nat _ 52%nat _ 32 1%N (SLit 8) 8 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia].
- intros j Hj. do 9 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; cbv; auto] |]). reflexivity. }
apply (CONT _ _ (set_ihead (upd_frame (upd_frame s 2 f1) 1 fp') 2) f1 (Some fp') HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
-- split; [|split].
++ rewrite cgif_vals_set_ihead_ls, (cgif_vals_upd_frame _ 1 fp fp') by (first [rewrite nth_error_upd_frame_other by lia; exact Hiop | reflexivity]).
rewrite (cgif_vals_ins_frame s 2 f1) by lia.
eapply (obj_at_upd ubs2segs memc (ms_mem ms) g LAY_CGIF CGIF_SIZE (cgif_vals s) _ [2%nat; 16%nat] [(16, 24); (92, 96)] Hobj (proj1 LAY_CGIF_ok));
[vm_compute; reflexivity | reflexivity | | |].
** intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 Hw]. apply in_wins_cons_false in Hw as [W2 _].
apply KEPT; clear - Hk W1 W2 Hng Hpg HGSv HFSv Hg0 Hg1 Hac; lia.
** intros j f v' [<-|[<-|[]]] Hf Hv'; cbn in Hf, Hv'; injection Hf as <-; injection Hv' as <-.
{ rewrite <- HU8. eapply (st_field ubs2segs E _ _ 2%nat _ 8%nat _ 16 8%N (SOff 18 0) nf HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HU18. reflexivity. }
{ rewrite <- HU8. eapply (st_field ubs2segs E _ _ 4%nat _ 8%nat _ 92 4%N (SLit 2) 2 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia]. }
** intros j Hj. do 17 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; cbv; auto] |]). reflexivity.
++ rewrite cg_raw_set_ihead, !cg_raw_upd_frame.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros k Hk. apply KEPT; clear - Hk Hrg Hnr Hpr_raw HGSv HRSv HFSv Hr0 Hr1 Hac; lia.
++ rewrite cg_frames_set_ihead. apply (frames_at_upd2 memc (ms_mem ms) s 2 1 None f1 (Some fp) fp' Hfrs Hinone Hiop ltac:(lia) Hnewf Hnewp).
intros j x Hj Hj1 Hj2 k Hk.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & X2).
pose proof (Hnfr x ltac:(eapply nth_error_In; exact Hj)) as X3.
pose proof (af_frames_sep API Lc Ac memc mdc g s N (NB ++ CB ++ rest) 1 j fp x HH0 HB' Hiop Hj ltac:(clear - Hj2; lia)) as X4.
apply KEPT; clear - Hk X0 X1 X2 X3 X4 HGSv HFSv Hac; lia.
-- apply cgif_wf_set_ihead; [| right; split; [reflexivity | unfold upd_frame at 1; unfold set_frames; cbn [cg_frames]; rewrite nth_list_set_same; [discriminate|]; unfold upd_frame, set_frames; cbn [cg_frames]; rewrite length_list_set, Hlen; lia]].
apply (cgif_wf_upd_frame _ N 1 fp fp'); [apply (cgif_wf_ins_frame s N 2 f1 Hwf Hinone) | rewrite nth_error_upd_frame_other by lia; exact Hiop |].
++ split; [exact HnoCT | right; reflexivity].
++ rewrite cg_attr_upd_frame. split; [| right; reflexivity]. cbn [fp' set_fr_gen_disp fr_attr]. exact (proj1 (Hfwf fp Hfpin)).
-- apply same_geom_set_ihead, same_geom_upd_frame, same_geom_upd_frame. exact Hgeom.
-- rewrite cg_frames_set_ihead, nth_error_upd_frame_other by lia. apply (nth_error_upd_frame_same s 2 None f1 Hinone).
-- reflexivity.
-- rewrite cg_frames_set_ihead. apply (nth_error_upd_frame_same _ 1 (Some fp) fp'). rewrite nth_error_upd_frame_other by lia. exact Hiop.
-- intros fp1 Hfp1. injection Hfp1 as <-. exists fp. split; reflexivity.
-- rewrite cgif_blocks_set_ihead, (cgif_blocks_upd_frame _ _ N 1 fp fp') by (first [rewrite nth_error_upd_frame_other by lia; exact Hiop | reflexivity]).
apply (cgif_blocks_ins_frame g s N 2 f1 Hinone).
-- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hcflo Hcfhi Hceil Hg1 Hn1 Hp1 HASv HGSv HFSv Hac; lia.
-- apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply KEPT; clear - Ha Hceil Hsp063 Hg1 Hn1 Hp1 HASv HGSv HFSv Hac; lia.
+
assert (HPD : pairwise_disjoint E (E1_regions i (Some 0) false)).
{ clear - Hi HU2 HU8 HU18 Hng Hg1 Hn1 Hceil HASv Hac HGSv HFSv.
unfold E1_regions, E1_g. destruct Hi as [-> | ->]; cbn [Nat.eqb app]; unfold af_Rg_part; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val];
rewrite ?HU2, ?HU8, ?HU18; repeat split; lia. }
assert (HS : st_ok ubs2segs E (ss_E1 i (Some 0) false false) (mkst regs1 (Z_to_bv 64 AF_E) memc (seg_rom ubs2segs))).
{ unfold ss_E1. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H; discriminate H | cbn [sv_denot]; rewrite G20; reflexivity].
- destruct Hi as [-> | ->]; vm_compute; reflexivity.
- unfold E1_regions. constructor; [exact HR0|]. unfold E1_g. destruct Hi as [-> | ->]; cbn [Nat.eqb app];
(constructor; [apply HRG; cbn; first [exact I | reflexivity | right; reflexivity | lia] |]);
(constructor; [apply HRG; cbn; first [exact I | reflexivity | right; reflexivity | lia] |]);
(constructor; [apply HRG; cbn; first [exact I | reflexivity | right; reflexivity | lia] |]);
(constructor; [apply HRG; cbn; first [exact I | reflexivity | right; reflexivity | lia] |]);
(constructor; [exact HR5 | constructor]).
- exact HPD.
- split; [rewrite app_nil_r; exact HFA | split; [exact HCF | exact I]]. }
clear HPD HCF HR0 HR5 HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_E) memc (seg_rom ubs2segs))) in HJ.
destruct Hi as [-> | ->].
* jrun_to LAWS ubs2tbl_ok HS HJ AF_E2. { wr_norm. apply (HWR (Some 0) false); [exact Hgin | exact Hnfin | intros H0; discriminate H0]. }
cbn [ms_mem mkst] in HF.
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> (a < g + 8 \/ g + 16 <= a) -> (a < g + 92 \/ g + 96 <= a) -> (a < nf + 32 \/ nf + 34 <= a) ->
mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha W1 W2 W3. clear - HF Ha W1 W2 W3 HU2 HU8 HU18.
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU18; lia). reflexivity. }
clear HF.
set (tb := byte_at (ms_mem ms) (nf + 33)).
set (f1 := fnew nf lpal' img' fattr fgen delay nlp ctidx 8 tb).
assert (Hnewf : obj_at ubs2segs (ms_mem ms) nf LAY_Frame (frame_vals f1)).
{ rewrite LAY_Frame_split. apply (proj2 (obj_at_app ubs2segs (ms_mem ms) nf LAY_FrameConfig [(32, 1%N); (33, 1%N)] [lpal'; img'; fattr; fgen; delay; nlp; ctidx] [8; tb] ltac:(reflexivity))). split.
- eapply obj_at_transport_range; [exact Hnf7 | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hng Hn0 Hn1 HGSv HFSv Hac; lia.
- cbn [obj_at]. split; [|split; [|exact I]].
+ rewrite <- HU18. eapply (st_field ubs2segs E _ _ 5%nat _ 18%nat _ 32 1%N (SLit 8) 8 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia].
+ subst tb. apply field_byte_any. apply (proj1 (heap_blocks _ _ LAWS Lc Ac (ms_mem ms) mdc nf FRAME_SIZE 33 (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hnfin ltac:(lia))). }
apply (CONT _ _ (set_ihead (upd_frame s 1 f1) 1) f1 None HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
-- split; [|split].
++ rewrite cgif_vals_set_ihead_ls, (cgif_vals_ins_frame s 1 f1) by lia.
eapply (obj_at_upd ubs2segs memc (ms_mem ms) g LAY_CGIF CGIF_SIZE (cgif_vals s) _ [1%nat; 16%nat] [(8, 16); (92, 96)] Hobj (proj1 LAY_CGIF_ok));
[vm_compute; reflexivity | reflexivity | | |].
** intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 Hw]. apply in_wins_cons_false in Hw as [W2 _].
apply KEPT; clear - Hk W1 W2 Hng HGSv HFSv Hg0 Hg1 Hac; lia.
** intros j f v' [<-|[<-|[]]] Hf Hv'; cbn in Hf, Hv'; injection Hf as <-; injection Hv' as <-.
{ rewrite <- HU8. eapply (st_field ubs2segs E _ _ 2%nat _ 8%nat _ 8 8%N (SOff 18 0) nf HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HU18. reflexivity. }
{ rewrite <- HU8. eapply (st_field ubs2segs E _ _ 4%nat _ 8%nat _ 92 4%N (SLit 1) 1 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia]. }
** intros j Hj. do 17 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; cbv; auto] |]). reflexivity.
++ rewrite cg_raw_set_ihead, cg_raw_upd_frame.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros k Hk. apply KEPT; clear - Hk Hrg Hnr HGSv HRSv HFSv Hr0 Hr1 Hac; lia.
++ rewrite cg_frames_set_ihead. apply (frames_at_upd memc (ms_mem ms) s 1 None f1 Hfrs Hinone Hnewf).
intros j x Hj Hne k Hk.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & X2).
pose proof (Hnfr x ltac:(eapply nth_error_In; exact Hj)) as X3.
apply KEPT; clear - Hk X0 X1 X2 X3 HGSv HFSv Hac; lia.
-- apply cgif_wf_set_ihead; [| left; reflexivity].
apply (cgif_wf_ins_frame s N 1 f1 Hwf Hinone). split; [exact HnoCT | right; reflexivity].
-- apply same_geom_set_ihead, same_geom_upd_frame. exact Hgeom.
-- rewrite cg_frames_set_ihead. apply (nth_error_upd_frame_same s 1 None f1 Hinone).
-- reflexivity.
-- rewrite cg_frames_set_ihead, nth_error_upd_frame_other by lia. exact Hiop.
-- intros fp1 Hfp1. discriminate Hfp1.
-- rewrite cgif_blocks_set_ihead. apply (cgif_blocks_ins_frame g s N 1 f1 Hinone).
-- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hcflo Hcfhi Hceil Hg1 Hn1 HASv HGSv HFSv Hac; lia.
-- apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply KEPT; clear - Ha Hceil Hsp063 Hg1 Hn1 HASv HGSv HFSv Hac; lia.
*
jrun_to LAWS ubs2tbl_ok HS HJ AF_E2. { wr_norm. apply (HWR (Some 0) false); [exact Hgin | exact Hnfin | intros H0; discriminate H0]. }
cbn [ms_mem mkst] in HF.
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> (a < g + 16 \/ g + 24 <= a) -> (a < g + 92 \/ g + 96 <= a) -> (a < nf + 32 \/ nf + 34 <= a) ->
mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha W1 W2 W3. clear - HF Ha W1 W2 W3 HU2 HU8 HU18.
mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU8, ?HU18; lia). reflexivity. }
clear HF.
set (tb := byte_at (ms_mem ms) (nf + 33)).
set (f1 := fnew nf lpal' img' fattr fgen delay nlp ctidx 8 tb).
assert (Hnewf : obj_at ubs2segs (ms_mem ms) nf LAY_Frame (frame_vals f1)).
{ rewrite LAY_Frame_split. apply (proj2 (obj_at_app ubs2segs (ms_mem ms) nf LAY_FrameConfig [(32, 1%N); (33, 1%N)] [lpal'; img'; fattr; fgen; delay; nlp; ctidx] [8; tb] ltac:(reflexivity))). split.
- eapply obj_at_transport_range; [exact Hnf7 | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hng Hn0 Hn1 HGSv HFSv Hac; lia.
- cbn [obj_at]. split; [|split; [|exact I]].
+ rewrite <- HU18. eapply (st_field ubs2segs E _ _ 5%nat _ 18%nat _ 32 1%N (SLit 8) 8 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia].
+ subst tb. apply field_byte_any. apply (proj1 (heap_blocks _ _ LAWS Lc Ac (ms_mem ms) mdc nf FRAME_SIZE 33 (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hnfin ltac:(lia))). }
apply (CONT _ _ (set_ihead (upd_frame s 2 f1) 2) f1 None HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HJ).
-- split; [|split].
++ rewrite cgif_vals_set_ihead_ls, (cgif_vals_ins_frame s 2 f1) by lia.
eapply (obj_at_upd ubs2segs memc (ms_mem ms) g LAY_CGIF CGIF_SIZE (cgif_vals s) _ [2%nat; 16%nat] [(16, 24); (92, 96)] Hobj (proj1 LAY_CGIF_ok));
[vm_compute; reflexivity | reflexivity | | |].
** intros k Hk Hw. apply in_wins_cons_false in Hw as [W1 Hw]. apply in_wins_cons_false in Hw as [W2 _].
apply KEPT; clear - Hk W1 W2 Hng HGSv HFSv Hg0 Hg1 Hac; lia.
** intros j f v' [<-|[<-|[]]] Hf Hv'; cbn in Hf, Hv'; injection Hf as <-; injection Hv' as <-.
{ rewrite <- HU8. eapply (st_field ubs2segs E _ _ 2%nat _ 8%nat _ 16 8%N (SOff 18 0) nf HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HU18. reflexivity. }
{ rewrite <- HU8. eapply (st_field ubs2segs E _ _ 4%nat _ 8%nat _ 92 4%N (SLit 2) 2 HS); [reflexivity | reflexivity | cbv; auto 10 | reflexivity | reflexivity | cbn; lia | cbn; lia]. }
** intros j Hj. do 17 (destruct j as [|j]; [first [reflexivity | exfalso; apply Hj; cbv; auto] |]). reflexivity.
++ rewrite cg_raw_set_ihead, cg_raw_upd_frame.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) |].
intros k Hk. apply KEPT; clear - Hk Hrg Hnr HGSv HRSv HFSv Hr0 Hr1 Hac; lia.
++ rewrite cg_frames_set_ihead. apply (frames_at_upd memc (ms_mem ms) s 2 None f1 Hfrs Hinone Hnewf).
intros j x Hj Hne k Hk.
destruct (Hfgeom x ltac:(eapply nth_error_In; exact Hj)) as (X0 & X1 & X2).
pose proof (Hnfr x ltac:(eapply nth_error_In; exact Hj)) as X3.
apply KEPT; clear - Hk X0 X1 X2 X3 HGSv HFSv Hac; lia.
-- apply cgif_wf_set_ihead; [| exfalso; apply (Hi2 eq_refl); reflexivity].
apply (cgif_wf_ins_frame s N 2 f1 Hwf Hinone). split; [exact HnoCT | right; reflexivity].
-- apply same_geom_set_ihead, same_geom_upd_frame. exact Hgeom.
-- rewrite cg_frames_set_ihead. apply (nth_error_upd_frame_same s 2 None f1 Hinone).
-- reflexivity.
-- rewrite cg_frames_set_ihead, nth_error_upd_frame_other by lia. exact Hiop.
-- intros fp1 Hfp1. discriminate Hfp1.
-- rewrite cgif_blocks_set_ihead. apply (cgif_blocks_ins_frame g s N 2 f1 Hinone).
-- eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig |].
intros k Hk. apply KEPT; clear - Hk Hcflo Hcfhi Hceil Hg1 Hn1 HASv HGSv HFSv Hac; lia.
-- apply (af_saved_ok_kept memc); [exact HSV|]. intros a Ha. apply KEPT; clear - Ha Hceil Hsp063 Hg1 Hn1 HASv HGSv HFSv Hac; lia.
Qed.
End S.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
