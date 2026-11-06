(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:49-57;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACan.v:337-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-147, 156-161;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:193-195, for libreac/fuzz_identity's ASan build (lib/A). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentRo IdentProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC1g YC1h YC81 YC4b YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name reac_box_name_cuts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma rbn1_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma rbn1_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite rbn1_land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma rbn1_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Ltac rbn1_rreg_by HS r v pf H :=
lazymatch type of HS with st_ok_pi _ ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg _ Hh Ex _ ms r HS) _); change (sv_denot Ex e = v); exact pf) | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf)  end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Lemma rbn1_slot_of_region : forall E m spe cs lo hi wlo whi od e v,
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2) = spe -> In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (spe + od) 8 v.
Proof.
intros E m spe cs lo hi wlo whi od e v (_ & _ & _ & Hcs) H2 Hc He Hv.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite H2 in Hck.
change 8%nat with (N.to_nat 8). exact (val_of_chunk_ok SEGS E m spe od 8%N e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Definition rbn1_regions : smem :=
  [ YP09.mkRegion (Some 2%nat) (-288) 16 (-288) 0
      [YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0))];
    got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition rbn1_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_rbn1 : sstate := mkSS AF_reac_box_name sr_atoms rbn1_regions None rbn1_facts.
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM3 : astack_malloc_realizes SEGS B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis TLF : PALibF B.
Definition rbn1_extra (display display_len : Z) : list word :=
  map (Z_to_bv 64) [SB; as_uar_cell B; display; display_len].
Definition ERB1 (regs : bvmap 5 word) (display display_len : Z) : env :=
  Eimg (Ereg regs (rbn1_extra display display_len)).
Lemma regs_ok_ERB1 : forall regs d dl, regs_ok (ERB1 regs d dl) sr_atoms regs.
Proof.
intros. unfold ERB1. apply (regs_ok_agree 32 (Ereg regs (rbn1_extra d dl))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn1_entry : forall lyc Sc W memc mdc ch (regs : bvmap 5 word) (display display_len : Z),
  afn_pre SEGS B REAC_BOX_NAME_STK lyc Sc W regs memc mdc ch ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs) 8 display -> 0 <= display < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs + 8) 8 display_len -> 0 <= display_len < 2 ^ 64 ->
  st_ok_pi SEGS VAL (ERB1 regs display display_len) ss_rbn1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name)) memc (seg_rom SEGS))).
Proof.
intros lyc Sc W memc mdc ch regs display display_len HPRE Md Rd Mdl Rdl.
pose proof HPRE as (HAR & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & Hpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hob0.
pose proof (pa_obj_img 1%nat ltac:(lia)) as Hob1.
pose proof (pa_obj_img 30%nat ltac:(lia)) as Hob30.
pose proof (palf_uar_img B TLF) as Huar.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := ERB1 regs display display_len).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (rbn1_extra display display_len)) m)
by (intros m Hm; subst E; unfold ERB1; apply Eimg_low; exact Hm).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 display) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 display_len) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; unfold ERB1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold ERB1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30)))
by (subst E; unfold ERB1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as VR0. pose proof (pa_val_range (A_OBJ 1)) as VR1.
pose proof (pa_val_range (A_OBJ 30)) as VR30.
unfold ss_rbn1, rbn1_regions. apply pa_entry_st_ok_full.
- apply regs_ok_ERB1.
- vm_compute. reflexivity.
- unfold got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split.
    -- intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    -- constructor; [|constructor; [|constructor]].
       ++ apply (chunk_ok_val SEGS E _ (spZ regs) 0 8 _ display);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          change (N.to_nat 8) with 8%nat. rewrite Z.add_0_r. exact Md.
       ++ apply (chunk_ok_val SEGS E _ (spZ regs) 8 8 _ display_len);
          [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          change (N.to_nat 8) with 8%nat. exact Mdl.
  * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
    [cbn [sv_denot]; rewrite EO30, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  * rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EO30) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 33 0) (as_uar_cell B));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
  * rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1);
    [reflexivity | lia | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
  rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EO30) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- unfold rbn1_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
          split; [lia|]; split; [exact Hal16 | lia]|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by (unfold SB; lia);
          rewrite Z.pow_0_r; split; [unfold SB; lia|]; split; [apply Z.mod_1_r | unfold SB; lia]|].
  exact I.
Qed.
Lemma rbn1_kept_frame : forall E rs H (m m' : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo hi HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn1_frame_of_region : forall E m spe cs (regs : bvmap 5 word),
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-288) 16 (-288) 0 cs) -> bv_unsigned (ew E 2) = spe ->
  (forall j r, nth_error rbn_saved_regs j = Some r ->
     In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  (forall r, 0 <= r < 32 -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r)) ->
  forall j r, nth_error rbn_saved_regs j = Some r ->
    val_mem SEGS m (spe - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
intros E m spe cs regs HR Hsp Hin Hew j r Hj.
assert (Hr : 0 <= r < 32).
{ apply nth_error_In in Hj. unfold rbn_saved_regs in Hj. cbn [In] in Hj. lia. }
replace (spe - 8 - 8 * Z.of_nat j) with (spe + (-8 - 8 * Z.of_nat j)) by lia.
apply (rbn1_slot_of_region E m spe cs (-288) 16 (-288) 0 (-8 - 8 * Z.of_nat j) (SOff (Z.to_nat r) 0)
  (bv_unsigned (getr regs (Z_to_bv 5 r))) HR Hsp (Hin j r Hj)).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite (Hew r Hr). symmetry. apply Z_to_bv_bv_unsigned.
- apply bv_unsigned_in_range.
Qed.
Theorem rbn_seg1 : rbn_seg1_stmt B G.
Proof.
intros [lyc Sc W regs memc mdc ch f said i o name name_len token token_len display display_len sd] HX.
unfold rbn_cx, rbm_args, rbn_SP in HX.
cbn [ri_lyc ri_Sc ri_W ri_regs ri_memc ri_mdc ri_ch ri_f ri_said ri_i ri_o ri_name ri_name_len ri_token
  ri_token_len ri_display ri_display_len ri_sd] in HX |- *.
destruct HX as (HPRE & Hro & H10 & Rf & H11 & Rsaid & H12 & Ri & H13 & Ro & H14 & Rn & H15 & Rnl & H16 & Rt &
  H17 & Rtl & Hp16 & Md & Rd & Mdl & Rdl & Himg & Hargs & Hfrl & Hev & Hlv).
set (FP := rbn_fp name name_len token token_len display display_len).
pose proof (ajournal_init SEGS B REAC_BOX_NAME_STK FP lyc Sc W regs memc mdc ch HPRE) as HJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@SRr_run_pi_AJ fx _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call fx _ _ _ _ _ B LAWS) as RUNC.
pose proof (@SRr_run_to_pi_AJ fx _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (paj_branch (L := ident_listing) (PI := PI)) as BR.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) &
  Hpres & Hch & HQT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp47 : spZ regs <= 2 ^ 47) by (clear - Hshi H47; lia).
assert (Hcs : alloc_ceiling + REAC_BOX_NAME_STK <= spZ regs) by (clear - Hceil Hslo; lia).
assert (Hac : 0x7fff7f800000 <= alloc_ceiling) by (clear - C1; lia).
pose proof (rbn1_entry lyc Sc W memc mdc ch regs display display_len HPRE Md Rd Mdl Rdl) as HS.
remember (ERB1 regs display display_len) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (rbn1_extra display display_len)) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; clear - Hn; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; unfold ERB1; rewrite Eimg_low by (unfold A_TEXT; clear - WS; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E35 : ew E 35 = Z_to_bv 64 display_len)
  by (subst E; unfold ERB1; rewrite Eimg_low by (unfold A_TEXT; clear - WS; lia); exact (ew_Ereg_extra regs _ 3)).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_reac_box_name)) with (Z_to_bv 64 (BASE + AF_reac_box_name)).
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite Usp, Z.add_0_r; reflexivity | cbn; clear - WS; lia | cbn; clear - WS; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; clear - WS; lia|]). apply awr_ok_nil. }
pose proof (rbn1_kept_frame _ _ _ _ _ (spZ regs - 288) (spZ regs) HFr
  ltac:(intros a (r & Hr & Hw); unfold ss_rbn1, rbn1_regions in Hr; cbn [ss_mem In] in Hr;
        repeat destruct Hr as [<- | Hr]; try destruct Hr;
        unfold got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP in Hw;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp in Hw; clear - Hw; lia)) as K1.
rename HG into G1. clear HF HFr.
set (A := 32 * ((spZ regs + -288) / 32)).
destruct (rbn1_sp1_facts (spZ regs + -288) ltac:(clear - Hcs WS Hac; lia)
  ltac:(rewrite <- Zplus_mod_idemp_l, Hal; reflexivity))
  as (HAr & HAal & HAal16). fold A in HAr, HAal, HAal16.
pmkst HS.
rbn1_rreg_by HS (2%bv : bv 5) (Z_to_bv 64 A)
  (rbn1_denot_and_m32 E 2 (spZ regs) (-288) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(clear - Hcs WS Hac; lia) ltac:(clear - Hsp47; lia)
    ltac:(unfold spZ; apply bv_unsigned_in_range)) R2.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pose proof (count_cid_le_length 3 (frames Sc)) as Hcnt.
assert (Hfs3 : fs_frames 3 = 2048) by reflexivity.
rewrite (palf_sm3 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (aj_stack_malloc_at SEGS B LAWS Hsegs (pal_env B TL) ML SMP 3 ASM3 ltac:(clear - WS; lia) W rg mm
    REAC_BOX_NAME_STK (spZ regs) FP lyc Sc W memc mdc [] lyc Sc _ 0 (A - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by (clear - HAr Hcs WS Hac Hsp47; lia). clear - HAr; lia.
  - rewrite <- Zminus_mod_idemp_l, HAal16, <- Zminus_mod_idemp_r, Hal. reflexivity.
  - clear - HAr; lia.
  - rewrite Hes, WS. clear - HAr; lia.
  - rewrite R3. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [clear - WS; lia | reflexivity].
  - rewrite Hfs3. clear - Hcnt Hfrl; lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK).
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (3, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply (proj1 HK);
    [clear - Ha Hcs WS Hac Hsp47; lia | rewrite Hes; clear - Ha HAr; lia].
  - intros _. apply (apresent_writable SEGS). apply HJpres2. clear - Ha WS; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ev2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; clear - WS; lia]).
assert (OLD : forall n, (n < 36)%nat -> ew Ev2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (E40 : ew Ev2 40 = getr regs2 10)
  by (rewrite HE2; exact (ew_havoc_new E 36 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbn; clear - WS; lia))).
assert (Usp2 : bv_unsigned (ew Ev2 2) = spZ regs) by (rewrite OLD by (clear - WS; lia); exact Usp).
assert (HFr0 : 4096 <= frame_addr lyc 3 pos /\ frame_addr lyc 3 pos + 512 <= alloc_ceiling)
  by (rewrite Hfb3 in HFceil; clear - HF4096 HFceil; lia).
assert (Hacu : alloc_ceiling <= 0x7fffff800000) by (clear - C1; lia).
clear HE2.
paj_run_to_sh RUNTOP HS HJ2 9188.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off Ev2 _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite Usp2, Z.add_0_r; reflexivity | cbn; clear - WS; lia | cbn; clear - WS; lia |].
  apply awr_ok_nil. }
pose proof (rbn1_kept_frame _ _ _ _ _ (spZ regs - 288) (spZ regs) HFr
  ltac:(intros a (r & Hr & Hw); cbn [ss_mem In] in Hr;
        repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp2 in Hw; clear - Hw; lia)) as K2.
rename HG into G2. clear HF HFr.
psrr_branch_pi RUNP BR HS.
2: { exfalso. cbn [branch_taken sv_denot] in Hc. rewrite E40, Ha0 in Hc. unfold w64 in Hc.
     rewrite unsigned_lit_small, Z.add_0_r in Hc by (clear - HFr0 Hacu; lia).
     apply negb_false_iff in Hc. apply bv_eqb_eq in Hc. apply (f_equal bv_unsigned) in Hc.
     rewrite !unsigned_lit_small in Hc by (clear - HFr0 Hacu; lia). clear - Hc HFr0; lia. }
paj_run_to_sh RUNTOP HS HJ2 9188.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off Ev2 _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite Usp2, Z.add_0_r; reflexivity | cbn; clear - WS; lia | cbn; clear - WS; lia |].
  apply awr_ok_nil. }
pose proof (rbn1_kept_frame _ _ _ _ _ (spZ regs - 288) (spZ regs) HFr
  ltac:(intros a (r & Hr & Hw); cbn [ss_mem In add_cond] in Hr;
        repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp2 in Hw; clear - Hw; lia)) as K3.
rename HG into G3. clear HF HFr.
apply SRr_ret.
pmkst HS.
assert (Gsp : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (EA : sv_denot Ev2 (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32))) = Z_to_bv 64 A)
  by (apply rbn1_denot_and_m32; [rewrite OLD, E2 by (clear - WS; lia); symmetry; apply Z_to_bv_bv_unsigned
       | clear - Hcs WS Hac; lia | clear - Hsp47; lia
       | unfold spZ; apply bv_unsigned_in_range]).
rbn1_rreg_by HS (2%bv : bv 5) (Z_to_bv 64 A) EA G2r.
assert (EA9 : sv_denot Ev2 (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 A).
{ change (alu64 ALU_ADD (sv_denot Ev2 (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32)))) (Z_to_bv 64 0) = Z_to_bv 64 A).
  rewrite EA, alu_add_small by (unfold M64; clear - HAr Hcs WS Hac Hsp47; lia). f_equal; clear - WS; lia. }
rbn1_rreg_by HS (9%bv : bv 5) (Z_to_bv 64 A) EA9 G9r.
assert (GR : forall (r : bv 5) n, getr (ms_regs ms1) r = ew Ev2 n -> (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  getr (ms_regs ms1) r = getr regs r).
{ intros r n Hr Hn Hnr. rewrite Hr, OLD by (clear - Hn; lia). apply EE. exact Hnr. }
prreg HS (3%bv : bv 5) G3r. prreg HS (4%bv : bv 5) G4r. prreg HS (8%bv : bv 5) G8r.
prreg HS (12%bv : bv 5) G12r. prreg HS (13%bv : bv 5) G13r. prreg HS (15%bv : bv 5) G15r.
prreg HS (16%bv : bv 5) G16r. prreg HS (19%bv : bv 5) G19r. prreg HS (20%bv : bv 5) G20r.
prreg HS (22%bv : bv 5) G22r. prreg HS (23%bv : bv 5) G23r. prreg HS (24%bv : bv 5) G24r.
prreg HS (25%bv : bv 5) G25r. prreg HS (26%bv : bv 5) G26r. prreg HS (27%bv : bv 5) G27r.
apply (GR _ 3%nat) in G3r; [|clear - WS; lia|reflexivity]. apply (GR _ 4%nat) in G4r; [|clear - WS; lia|reflexivity].
rewrite OLD, (EE 2%nat 2%bv eq_refl) in G8r by (clear - WS; lia).
rewrite OLD, (EE 12%nat 12%bv eq_refl) in G12r by (clear - WS; lia).
rewrite OLD, (EE 13%nat 13%bv eq_refl) in G13r by (clear - WS; lia).
rewrite OLD, (EE 15%nat 15%bv eq_refl) in G15r by (clear - WS; lia).
rewrite OLD, (EE 11%nat 11%bv eq_refl) in G20r by (clear - WS; lia).
rewrite OLD, (EE 16%nat 16%bv eq_refl) in G23r by (clear - WS; lia).
rewrite OLD, (EE 14%nat 14%bv eq_refl) in G24r by (clear - WS; lia).
rewrite OLD, (EE 10%nat 10%bv eq_refl) in G25r by (clear - WS; lia).
rewrite OLD, (EE 17%nat 17%bv eq_refl) in G27r by (clear - WS; lia).
rewrite OLD, E35 in G16r by (clear - WS; lia). rewrite OLD, E32 in G22r by (clear - WS; lia).
rewrite E40, Ha0 in G19r, G26r.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
exists pos, (ms_regs ms1), lyc, S2, (ms_mem ms1), (with_vm_backing (m_vm_lazy md2) mat1 md2).
split.
{ unfold rbn_cfg, cfg_at, w64.
  replace (BASE + AF_reac_box_name + RBN_P2) with (BASE + 9188)
    by (clear - WS; unfold AF_reac_box_name, RBN_P2; lia).
  reflexivity. }
unfold rbn_st2, rbn_mid, rbn_rbase, rbn_kept, rbn_inblk, rbn_shadow_at, rbn_A, rbn_F, rbn_FL, rbn_SH, rbn_SP,
  rbn_FPX.
cbn [ri_lyc ri_Sc ri_W ri_regs ri_memc ri_mdc ri_ch ri_f ri_said ri_i ri_o ri_name ri_name_len ri_token
  ri_token_len ri_display ri_display_len ri_sd].
fold A. fold FP.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 288 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hn. rewrite (K3 a Ha Hn). exact (K2 a Ha Hn). }
split.
{ split; [reflexivity|]. split; [exact HJ2|]. split; [rewrite Eab; apply Permutation_refl|].
  split.
  { intros a Hro0 Ho He.
    assert (Hia : in_img SEGS a)
      by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
    pose proof (Hsegs a Hia) as Hlow.
    rewrite (KR a) by (clear - Hlow Hcs WS C1 C2 C3 C4 C5; lia).
    rewrite (proj1 (proj2 (proj2 HK)) a Hia Ho He).
    rewrite (K1 a) by (clear - Hlow Hcs WS C1 C2 C3 C4 C5; lia).
    exact (Hro a Hro0 Ho He). }
  split.
  { intros a _ (q & N & Hq & Hqa) _.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR Hq) as (_ & Hb4 & Hbc & _).
    assert (Hj : 0 <= a - q < req_size N) by (clear - Hqa; unfold req_size; destruct (Z.eqb_spec N 0); lia).
    assert (Hab : 4096 <= q + (a - q) < alloc_ceiling) by (clear - Hb4 Hbc Hj; lia).
    replace a with (q + (a - q)) by ring.
    rewrite (KR (q + (a - q))) by (clear - Hab Hcs WS C1 C2 C3 C4 C5; lia).
    rewrite (proj1 (proj2 HK) q N (a - q) Hq Hj) by (intros []).
    rewrite (K1 (q + (a - q))) by (clear - Hab Hcs WS C1 C2 C3 C4 C5; lia). reflexivity. }
  split.
  { unfold rbn_frame, rbn_SP. cbn [ri_regs].
    apply (rbn1_frame_of_region Ev2 _ (spZ regs) _ regs HR0 Usp2).
    - intros j r Hj. unfold rbn_saved_regs in Hj.
      do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [In]; repeat (first [left; reflexivity | right])|]).
      cbn in Hj. destruct j; discriminate.
    - intros r Hr. rewrite OLD by (clear - Hr; lia). apply EE. rewrite Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 5) with 32. rewrite Z.mod_small by (clear - Hr; lia). clear - Hr; lia. }
  split.
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem2 (ms_mem ms1)).
    - intros k0 Hk0. apply KR; rewrite Hfb3 in HFceil; clear - Hk0 HFceil HF4096 Hcs WS C1 C2 C3 C4 C5; lia.
    - rewrite Hfb3 in Hflag. replace (frame_addr lyc 3 pos + 504) with (frame_addr lyc 3 pos + 512 - 8) by ring.
      exact (val_mem_of_rdword SEGS _ _ _ _ Hflag). }
  intros j Hj. cbn [length repeat] in Hj.
  assert (Hsh : 0 <= shadow_addr (frame_addr lyc 3 pos) + j < alloc_ceiling).
  { unfold shadow_addr, SHADOW_OFF.
    assert (HFle : frame_addr lyc 3 pos <= alloc_ceiling) by (clear - HFr0; lia).
    pose proof (Z.div_le_mono (frame_addr lyc 3 pos) alloc_ceiling 8 ltac:(clear - WS; lia) HFle) as D4.
    pose proof (Z.div_mod alloc_ceiling 8 ltac:(clear - WS; lia)) as D5.
    pose proof (Z.mod_pos_bound alloc_ceiling 8 ltac:(clear - WS; lia)) as M5.
    pose proof (Z.div_pos (frame_addr lyc 3 pos) 8 ltac:(clear - HFr0; lia) ltac:(clear - WS; lia)) as D6.
    clear - D4 D5 M5 D6 Hj HFr0 C1. lia. }
  unfold rbn_F. cbn [ri_lyc].
  rewrite (KR (shadow_addr (frame_addr lyc 3 pos) + j)) by (clear - Hsh Hcs WS C1 C2 C3 C4 C5; lia).
  rewrite nth_repeat. unfold zero_shadow, shadow_of_addr in Hz. rewrite Hfb3 in Hz. change (512 / 8) with 64 in Hz.
  apply Hz. clear - Hj; lia. }
split.
{ split; [exact G2r|]. split; [rewrite G3r; exact Hgp|]. split; [rewrite G4r; exact Htp|].
  split; [rewrite G8r; unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|]. split; [exact G9r|].
  split; [exact G19r | rewrite G22r; reflexivity]. }
split; [exact G26r|].
split; [rewrite G20r; exact H11|]. split; [rewrite G23r; exact H16|]. split; [rewrite G24r; exact H14|].
split; [rewrite G25r; exact H10|]. split; [rewrite G27r; exact H17|].
split; [rewrite G12r; exact H12|]. split; [rewrite G13r; exact H13|].
split; [rewrite G15r; exact H15 | exact G16r].
Qed.
End h.
End f.
End d.
