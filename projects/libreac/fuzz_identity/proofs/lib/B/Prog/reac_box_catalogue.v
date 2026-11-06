(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* reac_box_catalogue of fuzz_identity.asan-ubsan (build B), at BASE + AF_reac_box_catalogue = 0x83a30: the
   contract and its walk. It mirrors lib/A/Prog/reac_box_catalogue.v
   line for line. reac_box_catalogue stores the box count 11 through its pointer argument, 8 bytes
   of its caller's memory, so it is stated in cgif's caller-journal form (IdentBCJ.v: twr_ok, tcj_kept).
   Measured on the B listing:
   21 slots (A: 18); 0x83a30 `addi sp,sp,-16` is a 16-byte frame, so CAT_STK = 16 + ESTACK; no call is made.
   0x83a38 `beqz a0` (a0 = 0 goes to the return) is decided by the pointer fact of a0 (4096 <= pR).
   0x83a3c..0x83a40 is the UBSan alignment check of the store: a1 = a0 & 7, and a1 <> 0 goes to the trap
   (`unimp`) at 0x83a7c. The pointer fact of a0 carries pR mod 8 = 0 (the premise `pR mod 8 = 0`, which A's
   contract already has), so the engine computes a1 = 0 and the trap is not reached.
   0x83a5c `bnez` of the shadow byte at shadow_addr pR goes to __asan_report_store8 (0x83a80); cat_pR_ok and
   pR mod 8 = 0 give a zero shadow byte, so it is not taken. The result is BOX_CATALOGUE, object 28 = 0x9b520.
   The B differences from A: the listing (identb_listing, PL_identb), CAT_OBJ = A_OBJ 28 (A: A_OBJ 27), the
   shadow cell object A_OBJ 31 (A: A_OBJ 30, IdentBPaLib.v pal_cell), and the shape of the statement:
   tcat_spec : Prop holds BASE + AF_reac_box_catalogue and pa_relro_lo, pa_relro_hi in the statement (the
   CONVENTIONS form), where A's tcat_spec takes them as the parameters (a rlo rhi). No premise changes. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBCJ YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC4b YC81.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma cat_mod4096_mod8 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (4096 * (x / 4096)) with (512 * (x / 4096) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma cat_sub_mod8 : forall x y, x mod 8 = 0 -> y mod 8 = 0 -> (x - y) mod 8 = 0.
Proof.
intros x y Hx Hy. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod y 8 ltac:(lia)) as Dy.
rewrite Hx, Z.add_0_r in Dx. rewrite Hy, Z.add_0_r in Dy.
replace (x - y) with ((x / 8 - y / 8) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Definition CAT_OBJ : nat := A_OBJ 28.
Definition BOX_COUNT : Z := 11.
Definition CAT_STK : Z := 16 + ESTACK.
Definition EV_CAT : Z := 0.
Definition CatBx : sv := SOff 32 0.
Definition cat_regions : smem :=
[ YP09.mkRegion (Some 10%nat) 0 8 0 8 []; stack_region 16; got_regionP; bcell_regionP 32 ].
Definition cat_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 8) 3); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_cat : sstate := mkSS AF_reac_box_catalogue sr_atoms cat_regions None cat_facts.
Definition cat_SH : list shent := [ mkSHE 10 0 8 ].
Definition cat_extra : list word := [Z_to_bv 64 SB].
Definition EC (regs : bvmap 5 word) : env := Eimg (Ereg regs cat_extra).
Section e.
Variable B : asyms.
Definition cat_pR_ok (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (pR : Z) : Prop :=
(exists cid pos, In (cid, pos) (frames Sc) /\ (forall a, pR <= a < pR + 8 -> in_zr a (frame_rng lyc (cid, pos))) /\
aview SEGS (w_H W) memc (shadow_addr pR) = Some 0)
\/ (ly_stk_lo lyc <= pR /\ pR + 8 <= ly_stk_hi lyc).
Definition tcat_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (pR : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 (k + EV_CAT) /\
aregs_preserved regs regs2 /\
getr regs2 10 = w64 (VAL CAT_OBJ) /\
val_mem SEGS (mrestrict (w_H W2) mem2) pR 8 BOX_COUNT /\
tcj_kept B CAT_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => pR <= a < pR + 8).
Definition tcat_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (pR : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 pR ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CAT_STK -> spZ regs <= sp0 ->
pR mod 8 = 0 -> (spZ regs <= pR \/ pR + 8 <= spZ regs - CAT_STK) ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) pR 8 ->
cat_pR_ok lyc Sc W memc pR ->
st_nev Sc + EV_CAT <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_catalogue) regs memc mdc)
(tcat_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pR).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Lemma cat_frame_zone_lo : forall ly S W mem md cid pos a,
AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
4096 <= a < alloc_ceiling.
Proof.
intros ly S W mem md cid pos a HAR Hin Hr.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (YCbq.shadow_addr_bounds (frame_addr ly cid pos) ltac:(lia)) as S1.
pose proof (YCbq.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia)) as S2.
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as S3.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. lia.
Qed.
Lemma cat_pR_where : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k pR,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
cat_pR_ok lyc Sc W memc pR ->
4096 <= pR /\ pR + 8 <= 2 ^ 47 /\ (pR + 8 <= IMG_LO \/ IMG_TOP <= pR) /\
(pR + 8 <= kLowShadowBeg \/ kHighMemBeg <= pR).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k pR HJc HpRok.
pose proof HJc as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HpRok as [(cid & pos & Hin & Hrng & _) | (Hlo & Hhi)].
- destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
  pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Himg.
  pose proof (Hrng pR ltac:(lia)) as Ha1. pose proof (Hrng (pR + 7) ltac:(lia)) as Ha2.
  unfold frame_rng, in_zr in Ha1, Ha2. cbn [fst snd] in Ha1, Ha2.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfh.
  split; [lia|]. split; [lia|]. split; [lia|]. unfold kLowShadowBeg, kHighMemBeg. lia.
- pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & _ & _ & Hhb).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  rewrite Elo in Hlo. rewrite Ehi in Hhi. rewrite Elo in Hhb.
  unfold kHighMemBeg in *. split; [lia|]. split; [lia|]. split; [lia|]. unfold kLowShadowBeg. lia.
Qed.
Lemma cat_pR_addressable : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k pR,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
cat_pR_ok lyc Sc W memc pR -> pR mod 8 = 0 ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF pR 8.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k pR HJc HpRok HpR8.
pose proof HJc as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct HpRok as [(cid & pos & Hin & Hrng & Hz0) | (Hlo & Hhi)].
- apply zero_shadow_range; [exact HpR8 | reflexivity |].
  intros i Hi. change (8 / 8) with 1 in Hi. assert (Hi0 : i = 0) by lia. subst i.
  replace (shadow_of_addr SHADOW_OFF pR + 0) with (shadow_addr pR)
    by (unfold shadow_of_addr, shadow_addr; lia).
  exact Hz0.
- pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
  pose proof (al_zshadow _ _ LAWS lyc Sc W memc mdc (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
    HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
  unfold page_aligned in Hpal, Hpah.
  eapply range_addressable_sub;
  [ apply zero_shadow_range;
    [ exact (cat_mod4096_mod8 _ Hpal)
    | exact (cat_sub_mod8 _ _ (cat_mod4096_mod8 _ Hpah) (cat_mod4096_mod8 _ Hpal))
    | exact Hz ]
  | lia | lia ].
Qed.
Lemma cat_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) pR,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 pR ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CAT_STK -> spZ regs <= sp0 ->
pR mod 8 = 0 -> (spZ regs <= pR \/ pR + 8 <= spZ regs - CAT_STK) ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) pR 8 ->
cat_pR_ok lyc Sc W memc pR ->
st_ok_pi SEGS VAL (EC regs) ss_cat
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_catalogue)) memc (seg_rom SEGS)))
/\ sh_ok SEGS CatBx cat_SH (EC regs) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR HJc H10 Hal16 Hwlo Hwhi HpR8 HpRside HpRw HpRok.
pose proof HJc as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cat_pR_where STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k pR HJc HpRok)
  as (HpR4096 & HpR47 & HpRimg & HpRband).
pose proof (cat_pR_addressable STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k pR HJc HpRok HpR8) as HRA.
assert (HCS : CAT_STK = 4112) by reflexivity.
assert (Hsplo : 2 ^ 46 <= spZ regs) by lia.
assert (Hsphi : spZ regs <= 2 ^ 47) by lia.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 31 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
rewrite restrict_mkst_fx.
set (E := EC regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs cat_extra) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 pR)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E1o : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E31 : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31)))
by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (UpR : bv_unsigned (ew E 10) = pR) by (rewrite E10; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (UBx : U E CatBx = SHADOW_OFF).
{ unfold CatBx. rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
  rewrite zcanon_id by (unfold SB, M64; lia). reflexivity. }
assert (U10 : U E (SOff 10 0) = pR).
{ rewrite U_SOff, E10, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
split.
- unfold ss_cat. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cat_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite UpR. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (proj2 (HpRw (pR + o) ltac:(lia)))).
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * cbn [base_val]. rewrite E1o, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
      [cbn [sv_denot]; rewrite E31, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 31)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * cbn [base_val]. rewrite E31, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 31)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 31)) 0 8 CatBx SB);
      [cbn [sv_denot CatBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold cat_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite UpR, Usp, E1o, E31, !unsigned_lit_small
      by (pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 31)); lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cat_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, UpR, USB.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
- unfold sh_ok, cat_SH. constructor; [|constructor].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite UBx, U10. rewrite <- (aview_rd_of SEGS).
  split.
  + replace (8 - 0) with 8 by lia. rewrite Z.add_0_r. exact HRA.
  + intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.add_0_r in Ha.
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Theorem pb_reac_box_catalogue : tcat_spec.
Proof.
unfold tcat_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR
HJc HROD Hra Hra4 Hgp Htp H10 Hal16 Hwlo Hwhi HpR8 HpRside HpRw HpRok Hev.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJc as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & G5 & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (cat_pR_where STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k pR HJc HpRok)
  as (HpR4096 & HpR47 & HpRimg & HpRband).
assert (HCS : CAT_STK = 4112) by reflexivity.
assert (Hsplo : 2 ^ 46 <= spZ regs) by lia.
assert (Hsphi : spZ regs <= 2 ^ 47) by lia.
destruct (cat_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR
  HJc H10 Hal16 Hwlo Hwhi HpR8 HpRside HpRw HpRok) as [HS SHOK].
remember (EC regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs cat_extra) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 pR)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E28 : ew E 269%nat = Z_to_bv 64 (VAL 269%nat))
by (apply (img_env_atomP E 269%nat HEI); unfold A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs cat_extra) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (UpR : bv_unsigned (ew E 10) = pR) by (rewrite E10; apply unsigned_lit_small; lia).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_reac_box_catalogue)) with (Z_to_bv 64 (BASE + AF_reac_box_catalogue)).
paj_run_tok RUN HS HJc SHOK Bspan;
[ lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat pR);
  [ reflexivity
  | cbn [ew ewset Nat.eqb]; exact UpR
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exact (proj1 (HpRw a ltac:(lia)))
  |];
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [ reflexivity
  | cbn [ew ewset Nat.eqb]; rewrite Usp; lia
  | cbn [YP09.r_wlo]; lia
  | cbn [YP09.r_whi]; lia
  |];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  apply awr_ok_nil
| ].
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HFr : frame_of _ _ _ _ |- _ =>
  assert (VpR : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) (pR + 0) (N.to_nat 8) BOX_COUNT);
  [ pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msc) 0%nat _ HS eq_refl) as HR0;
    cbn [restrict ms_mem] in HR0;
    eapply (field_of_region E _ 10%nat pR _ _ _ _ _ 0 8%N _ BOX_COUNT HR0);
    [ exact UpR
    | cbn; first [ left; reflexivity | right; left; reflexivity ]
    | first [ reflexivity | cbn [sv_denot]; unfold BOX_COUNT; reflexivity ]
    | unfold BOX_COUNT; zside
    | zside ]
  | ]
end.
rewrite Z.add_0_r in VpR. change (N.to_nat 8) with 8%nat in VpR.
lazymatch goal with
| HS : st_ok_pi _ _ _ _ (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc2)) |- _ =>
  assert (HKEEP : forall a, 0 <= a < 2 ^ 64 ->
    ~ (pR <= a < pR + 8) -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) memc a);
  [ intros a Ha HnP HnS;
    refine (kept_of_frame Ex rs (w_H W) memc (ms_mem msc)
      (fun x => (pR <= x < pR + 8) \/ (spZ regs - 16 <= x < spZ regs)) HFr _ a Ha _);
    [ intros bb wlo whi x Hin Hr;
      cbn [windows map cat_regions stack_region got_regionP bcell_regionP
           YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
      destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <- <-;
      cbn [base_val] in Hr;
      first [ rewrite UpR in Hr; left; lia
            | rewrite Usp in Hr; right; lia
            | exfalso; lia ]
    | intros [Hq | Hq]; [exact (HnP Hq) | exact (HnS Hq)] ]
  | ]
end.
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HG : mem_grows _ _ |- _ =>
  prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat'; split; [reflexivity|];
  exists (ms_regs msc), (ms_mem msc); eexists;
  split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
  split;
  [ replace (k + EV_CAT) with k by (unfold EV_CAT; lia);
    apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ |];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs cat_extra HS); [exact HAE | vm_compute; reflexivity]|];
  split;
  [ cbn [ms_regs]; unfold CAT_OBJ, A_OBJ, w64; cbn [Nat.add]; rewrite R10;
    first [ exact E28 | reflexivity ] |];
  split; [cbn [ms_mem]; exact VpR|];
  unfold tcj_kept; cbn [ms_mem];
  split;
  [ intros a Ha Hw HnP; apply HKEEP; [lia | exact HnP | lia] |];
  split;
  [ intros bb m i Hin Hi HnP;
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb m HAR Hin) as (_ & Hb4096 & Hbceil & _);
    apply HKEEP; [lia | exact HnP | lia] |];
  split;
  [ intros a Him Hns He; pose proof (pa_img_range a Him) as HaI;
    apply HKEEP; [lia | lia | lia] |];
  split;
  [ intros cid pos a Hin Hr HnP;
    pose proof (cat_frame_zone_lo lyc Sc W memc mdc cid pos a HAR Hin Hr) as Hlo;
    apply HKEEP; [lia | exact HnP | lia] |];
  split;
  [ intros a Ha Hw Hp; exact (apresent_grows (w_H W) memc (ms_mem msc) a HG Hp) |];
  intros a Ha; apply (apresent_grows (w_H W) memc (ms_mem msc) a HG); apply Hpres;
  lia
end.
Qed.
End e.
End d.
End b.
