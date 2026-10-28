(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition FLBx : sv := SOff 32 0.
Definition FLBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition fl_extra (hw : Z) (s : cgif_st) (f : frame_st) (uar : Z) : list word := map (Z_to_bv 64) (SB :: tcgif_vals hw s ++ frame_vals f ++ [uar]).
Definition fl_g_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 33 []).
Definition fl_cur_region : YP09.region := YP09.mkRegion (Some 11%nat) 0 FRAME_SIZE 20 24 (obj_chunks_gen LAY_Frame 50 []).
Definition fl_regions0 : smem :=
[ stack_region 384; got_regionP; bcell_regionP 32; uar_got_regionP 59; uar_cell_regionP 59; fl_g_region; fl_cur_region ].
Definition fl_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, HPTR 4); (11%nat, HPTR 4); (32%nat, mkAF SB SB 0);
(36%nat, mkAF 0 (2^64 - 1) 0); (38%nat, mkAF 0 (2^32 - 1) 0); (39%nat, mkAF 0 (2^32 - 1) 0);
(40%nat, mkAF 1 65535 0); (41%nat, mkAF 1 65535 0); (42%nat, mkAF 0 65535 0); (43%nat, mkAF 0 65535 0);
(46%nat, HPTR 4); (48%nat, mkAF 0 (2^32 - 1) 0); (49%nat, mkAF 0 (2^32 - 1) 0);
(50%nat, mkAF 0 (2^64 - 1) 0); (51%nat, HPTR 4); (52%nat, mkAF 0 (2^32 - 1) 0); (53%nat, mkAF 0 (2^32 - 1) 0);
(54%nat, mkAF 0 65535 0); (55%nat, mkAF 0 65535 0); (56%nat, mkAF 0 255 0); (57%nat, mkAF 0 255 0); (58%nat, mkAF 0 255 0);
(59%nat, mkAF 0x10000 0x5fb000 2) ].
Definition ss_fl0 : sstate := mkSS AF_asan3_flushFrame sr_atoms fl_regions0 None (mkFacts fl_atoms0 [] []).
Section FL.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables wfn hw : Z.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Lemma fl_cblocks_in : forall g s N i f,
nth_error (cg_frames s) i = Some (Some f) ->
In (g, CGIF_SIZE) (cgif_blocks g s N) /\ In (cg_raw s, RAW_SIZE) (cgif_blocks g s N) /\
In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s N) /\ In (fr_img f, N) (cgif_blocks g s N).
Proof.
intros g s N i f Hf.
assert (Hfi : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
unfold cgif_blocks. split; [left; reflexivity|]. split; [right; left; reflexivity|].
assert (Hfb : forall x, In x (frame_blocks N f) -> In x ((g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s))).
{ intros x Hx. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hfi | exact Hx]. }
split; [apply Hfb; left; reflexivity | apply Hfb; right; left; reflexivity].
Qed.
Lemma fl_blocks_in : forall ly S g s N i f rest,
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) ->
nth_error (cg_frames s) i = Some (Some f) ->
In (g, CGIF_SIZE) (ablocks B ly S) /\ In (cg_raw s, RAW_SIZE) (ablocks B ly S) /\
In (fr_ptr f, FRAME_SIZE) (ablocks B ly S) /\ In (fr_img f, N) (ablocks B ly S).
Proof.
intros ly S g s N i f rest HP Hf.
assert (Hsub : forall x, In x (cgif_blocks g s N) -> In x (ablocks B ly S)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hx. }
assert (Hfi : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
unfold cgif_blocks in Hsub.
split; [apply Hsub; left; reflexivity|]. split; [apply Hsub; right; left; reflexivity|].
assert (Hfb : forall x, In x (frame_blocks N f) -> In x (ablocks B ly S)).
{ intros x Hx. apply Hsub. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hfi | exact Hx]. }
split; [apply Hfb; left; reflexivity | apply Hfb; right; left; reflexivity].
Qed.
Lemma fl_entry : forall W ly S regs mem md ch g s N i f rest,
afn_pre SEGS B TFLUSH_STK ly S W regs mem md ch ->
getr regs 10 = w64 g ->
tcgif_at SEGS wfn hw (mrestrict (w_H W) mem) g s -> cgif_wf s N ->
nth_error (cg_frames s) i = Some (Some f) ->
getr regs 11 = w64 (fr_ptr f) ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (fl_extra hw s f (as_uar_cell B)))) ss_fl0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_asan3_flushFrame)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch g s N i f rest HPRE H10 HAT HWF Hf H11 HPerm.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TFLUSH_STK = 17440) by reflexivity.
destruct (fl_blocks_in ly S g s N i f rest HPerm Hf) as (Hing & Hraw_in & Hcur_in & Himg_in).
destruct HAT as (Og & Oraw & Ofr).
assert (Hfi : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
pose proof (Ofr f Hfi) as Oc.
destruct HWF as (Hlen3 & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr f) FRAME_SIZE HAR Hcur_in) as (Hc16 & Hc4096 & Hcceil & Hcrh_ia & Hcpres & _). pose proof (proj1 Hcrh_ia) as Hcrh.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hcur_in) as Hcrh_img.
destruct (al_blocks _ _ LAWS ly S W mem md (fr_img f) N HAR Himg_in) as (Hi16 & Hi4096 & Hiceil & Hirh_ia & _ & _). pose proof (proj1 Hirh_ia) as Hirh.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Himg_in) as Hirh_img.
destruct (al_blocks _ _ LAWS ly S W mem md (cg_raw s) RAW_SIZE HAR Hraw_in) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & _ & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hraw_in) as Hrh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size RAW_SIZE) with 48 in *. change (req_size FRAME_SIZE) with 40 in *.
assert (Hqi : 1 <= req_size N) by (unfold req_size; destruct (Z.eqb_spec N 0); lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ g CGIF_SIZE (fr_ptr f) FRAME_SIZE HAR Hing Hcur_in ltac:(unfold CGIF_SIZE, FRAME_SIZE; intros X; injection X; lia)) as Sgc.
unfold zdisjoint, block_rng in Sgc. cbn [fst snd] in Sgc. change (req_size CGIF_SIZE) with 96 in Sgc. change (req_size FRAME_SIZE) with 40 in Sgc.
pose proof Og as Og'. cbn [obj_at LAY_CGIF tcgif_vals] in Og'.
destruct Og' as ([_ R0] & [_ R1] & [_ R2] & [_ R3] & [_ R4] & [_ R5] & [_ R6] & [_ R7] & [_ R8] & [_ R9] & [_ R10] & [_ R11] & [_ R12] & [_ R13] & [_ R14] & [_ R15] & [_ R16] & _).
cbn [fst snd N.to_nat Z.of_N] in R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14, R15, R16.
pose proof Oc as Oc'. cbn [obj_at LAY_Frame LAY_FrameConfig frame_vals app] in Oc'.
destruct Oc' as ([_ Q0] & [_ Q1] & [_ Q2] & [_ Q3] & [_ Q4] & [_ Q5] & [_ Q6] & [_ Q7] & [_ Q8] & _).
cbn [fst snd N.to_nat Z.of_N] in Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with (2 ^ 32) in *. change (2 ^ (8 * 2)) with 65536 in *. change (2 ^ (8 * 1)) with 256 in *.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (fl_extra hw s f (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (fr_ptr f)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall j, (j < 28)%nat -> ew E (32 + j) = nth j (fl_extra hw s f (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (exact (EX 0%nat ltac:(lia))).
pose proof (EX 27%nat ltac:(lia)) as E59. cbn [Nat.add nth fl_extra map app tcgif_vals frame_vals] in E59.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (EG : forall j v, nth_error (tcgif_vals hw s) j = Some v -> ew E (33 + j) = Z_to_bv 64 v).
{ intros j v Hj. pose proof (nth_error_nth _ j 0 Hj) as Hn.
assert (Hlt : (j < length (tcgif_vals hw s))%nat).
{ destruct (Nat.lt_ge_cases j (length (tcgif_vals hw s))) as [Hl|Hge]; [exact Hl|]. rewrite (proj2 (nth_error_None _ _) Hge) in Hj. discriminate. }
change (length (tcgif_vals hw s)) with 17%nat in Hlt.
replace (33 + j)%nat with (32 + Datatypes.S j)%nat by lia. rewrite (EX (Datatypes.S j) ltac:(lia)). unfold fl_extra.
rewrite map_nth. cbn [nth]. rewrite app_nth1 by exact Hlt. rewrite Hn. reflexivity. }
assert (EF : forall j v, nth_error (frame_vals f) j = Some v -> ew E (50 + j) = Z_to_bv 64 v).
{ intros j v Hj. pose proof (nth_error_nth _ j 0 Hj) as Hn.
assert (Hlt : (j < 9)%nat).
{ destruct (Nat.lt_ge_cases j (length (frame_vals f))) as [Hl|Hge]; [exact Hl|]. rewrite (proj2 (nth_error_None _ _) Hge) in Hj. discriminate. }
replace (50 + j)%nat with (32 + Datatypes.S (17 + j))%nat by lia. rewrite (EX (Datatypes.S (17 + j))%nat ltac:(lia)). unfold fl_extra.
rewrite map_nth. cbn [nth]. rewrite app_nth2 by (cbn; lia). change (length (tcgif_vals hw s)) with 17%nat.
replace (17 + j - 17)%nat with j by lia. rewrite app_nth1 by (change (length (frame_vals f)) with 9%nat; exact Hlt). rewrite Hn. reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_fl0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold fl_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 59 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E59, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB 59%nat (as_uar_cell B) E59) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
+ unfold fl_g_region. apply (region_ok_obj_gen SEGS E _ 10 g CGIF_SIZE 0 0 LAY_CGIF (tcgif_vals hw s) 33 []);
[rewrite E10; apply unsigned_lit_small; lia | lia | unfold CGIF_SIZE; lia | exact Og | vm_compute; reflexivity
| intros j v Hj; exact (EG j v Hj) | intros j z Hj; destruct j; discriminate | intros o Ho; lia].
+ unfold fl_cur_region. apply (region_ok_obj_gen SEGS E _ 11 (fr_ptr f) FRAME_SIZE 20 24 LAY_Frame (frame_vals f) 50 []);
[rewrite E11; apply unsigned_lit_small; lia | lia | unfold FRAME_SIZE; lia | exact Oc | vm_compute; reflexivity
| intros j v Hj; exact (EF j v Hj) | intros j z Hj; destruct j; discriminate
| intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hcpres (fr_ptr f + o) ltac:(lia)))].
- apply pairwise_disjoint_of_extents.
unfold fl_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, fl_g_region, fl_cur_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat g E10), (VB 11%nat (fr_ptr f) E11), (VB 59%nat (as_uar_cell B) E59) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp. unfold CGIF_SIZE, FRAME_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hcceil Hcrh Hcrh_img Hc4096 Sgc C1 C3 FFS Hstk0 Hob0 Hob1 Hob12 Huar Hsep. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : pa_val (A_OBJ _) + 8 <= _ \/ _ |- _ => clear H | H : as_uar_cell _ + 4 <= _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok fl_atoms0]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
pose proof (EG 3%nat _ eq_refl) as E36. pose proof (EG 5%nat _ eq_refl) as E38. pose proof (EG 6%nat _ eq_refl) as E39.
pose proof (EG 7%nat _ eq_refl) as E40. pose proof (EG 8%nat _ eq_refl) as E41. pose proof (EG 9%nat _ eq_refl) as E42.
pose proof (EG 10%nat _ eq_refl) as E43. pose proof (EG 13%nat _ eq_refl) as E46. pose proof (EG 15%nat _ eq_refl) as E48.
pose proof (EG 16%nat _ eq_refl) as E49.
pose proof (EF 0%nat _ eq_refl) as E50. pose proof (EF 1%nat _ eq_refl) as E51. pose proof (EF 2%nat _ eq_refl) as E52.
pose proof (EF 3%nat _ eq_refl) as E53. pose proof (EF 4%nat _ eq_refl) as E54. pose proof (EF 5%nat _ eq_refl) as E55.
pose proof (EF 6%nat _ eq_refl) as E56. pose proof (EF 7%nat _ eq_refl) as E57. pose proof (EF 8%nat _ eq_refl) as E58.
cbn [Nat.add] in E36, E38, E39, E40, E41, E42, E43, E46, E48, E49, E50, E51, E52, E53, E54, E55, E56, E57, E58.
rewrite Usp, E10, E11, E32, E36, E38, E39, E40, E41, E42, E43, E46, E48, E49, E50, E51, E52, E53, E54, E55, E56, E57, E58, E59.
rewrite !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hcceil Hcrh Hcrh_img Hc4096 Hc16 Hiceil Hirh Hirh_img Hi4096 Hi16 Hqi Hrceil Hrh Hrh_img Hr4096 Hr16
R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 HW1 HH1 C1 C3 FFS Hstk0 Hal16 Huar Huar4. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End FL.
End b.
End a.
