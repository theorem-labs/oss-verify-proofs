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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC81 YC4b YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp AC8h ACh9 AChc ACh8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0c YC5d YC7z YC7x YC21 YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACh7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition cl_extraX (regs : bvmap 5 word) (g : Z) (s1 : cgif_st) (pf : Z) : list word := cl_extra regs g s1 ++ [Z_to_bv 64 pf].
Definition cl_objX : YP09.region :=
YP09.mkRegion (Some 32%nat) 0 CGIF_SIZE 88 92
[YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
YP09.mkChunk 24 (CVal 8 (SOff 39 0)); YP09.mkChunk 40 (CVal 4 (SOff 40 0));
YP09.mkChunk 72 (CVal 8 (SOff 36 0)); YP09.mkChunk 80 (CVal 8 (SOff 51 0)); YP09.mkChunk 88 (CVal 4 (SOff 37 0))].
Definition cl_regionsX (d : Z) (sv : bool) : smem := [cl_stack d sv; got_regionP; bcell_regionP 38; cl_objX].
Definition ss_clX (pc : Z) (sregs : list sv) (d : Z) (sv : bool) : sstate := mkSS pc sregs (cl_regionsX d sv) None (if sv then cl_facts_mid else cl_facts).
Definition FPcX (g : Z) (s : cgif_st) (N : Z) (pf : Z) : list (Z * Z) := FPc g s N ++ asink_fp pf.
Ltac awr_clX Usp E32u Hing HTS :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
first [ apply awr_ok_cons_ro; [cbn; lia|]
| eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -80); [reflexivity | rewrite Usp; lia | cbn; rewrite HTS; lia | cbn; lia |] ];
apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | exact E32u | exact Hing | cbn [YP09.r_wlo]; lia
| cbn [YP09.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; unfold FPcX, FPc, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| apply awr_ok_nil ] end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
#[local] Notation WFN_ADDR := (BASE + WFN_OFF).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable hw : Z.
Variable CTX : list (list Z).
Variable path pf : Z.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Definition cl_cxX ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (g : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z)) : Prop :=
afn_pre SEGS B TCLOSE_STK ly S W regs mem md ch /\
In (raZ regs :: spine ch) CTX /\ Z.of_nat (length (frames S)) <= 7 /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
getr regs 10 = w64 g /\
xcgif_at SEGS WFN_ADDR path hw pf (rdW W mem) g s /\ cgif_wf s N /\
Permutation (ablocks B ly S) (cgif_blocks g s N ++ (pf, FILE_BLOCK) :: rest) /\
st_nev S + (2 * EV_FLUSH + 16) <= EV_MAX /\ blocks_bytes S + LIVE_FLUSH <= LIVE_MAX.
Definition cl_xent ly S (W : world SEGS) mem md (s : cgif_st) (N aM : Z) (GPAL : list Z) (gs : YO07.gif_st) : Prop :=
pf <> 0 /\ cgif_relA SEGS K (rdW W mem) md s pf N GPAL gs /\
Z.of_nat (length (concat (YO07.s_out gs))) + CLOSE_OUT N <= SINK_MAX /\
ameta_inv SEGS K ly (rdW W mem) aM /\ mo_ok MT S (xm_close XN N).
Definition cl_postX ly S W (regs : bvmap 5 word) mem md (g : Z) (s : cgif_st) (N aM : Z) (rest : list (Z * Z)) (GPAL : list Z) (gs : YO07.gif_st) (kf : Z)
: world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TCLOSE_STK (spZ regs) (FPcX g s N pf) ly S W mem md [] ly' S' W' mem' md' kf /\
aregs_preserved regs regs' /\ Permutation (ablocks B ly' S') rest /\
asink_none SEGS K (rdW W' mem') md' /\
Fs.fs_lookup (m_fs md') sink_path = Some (bytes (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59])) /\
ameta_ok SEGS K (rdW W' mem') aM /\ mo_le MT S S' (xn_close XN N).
Lemma cl_postX_mono : forall ly S W regs mem md g s N aM rest GPAL gs kf kf' W' c',
cl_postX ly S W regs mem md g s N aM rest GPAL gs kf W' c' -> kf <= kf' -> cl_postX ly S W regs mem md g s N aM rest GPAL gs kf' W' c'.
Proof.
intros ly S W regs mem md g s N aM rest GPAL gs kf kf' W' c' (ly' & S' & regs' & mem' & md' & Hc & HJ & HP & HB) Hle.
exists ly', S', regs', mem', md'. split; [exact Hc|]. split; [exact (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hle)|]. exact (conj HP HB).
Qed.
Definition tcgif_at2X (m : word -> option byte) (g : Z) (s1 : cgif_st) : Prop :=
obj_at SEGS m g LAY_CGIF (xcgif_vals path hw pf s1) /\
(forall f, In (Some f) (cg_frames s1) -> obj_at SEGS m (fr_ptr f) LAY_Frame (frame_vals f)).
Definition tcgif_atIX (i : nat) (m : word -> option byte) (g : Z) (s1 : cgif_st) : Prop :=
obj_at SEGS m g LAY_CGIF (xcgif_vals path hw pf s1) /\
(forall j f, (i <= j)%nat -> nth_error (cg_frames s1) j = Some (Some f) -> obj_at SEGS m (fr_ptr f) LAY_Frame (frame_vals f)).
Definition cl_midX (OBJ : (word -> option byte) -> Z -> cgif_st -> Prop)
ly S W (regs : bvmap 5 word) mem md g s N (restc : list (Z * Z)) lyc Sc (Wc : world SEGS) memc mdc (k : Z) (s1 : cgif_st) (bl : list (Z * Z)) : Prop :=
ajournal SEGS B TCLOSE_STK (spZ regs) (FPcX g s N pf) ly S W mem md [] lyc Sc Wc memc mdc k /\ 0 <= k /\
cl_frame SEGS (mrestrict (w_H Wc) memc) (spZ regs) regs /\
OBJ (mrestrict (w_H Wc) memc) g s1 /\ cl_obj_ok g s s1 N /\
Permutation (ablocks B lyc Sc) (bl ++ restc).
Definition cl_xopen S (s : cgif_st) (GPAL : list Z) Sc (Wc : world SEGS) memc mdc (s1 : cgif_st) (SG : list Z) (acc room : Z) : Prop :=
asink_at SEGS K (rdW Wc memc) mdc pf SG /\ mo_le MT S Sc acc /\ Z.of_nat (length SG) + room <= SINK_MAX /\
gcfg_of s1 GPAL = gcfg_of s GPAL.
Definition cl_xclosed S Sc (Wc : world SEGS) memc mdc (KEY : list Z) (acc : Z) : Prop :=
asink_none SEGS K (rdW Wc memc) mdc /\ Fs.fs_lookup (m_fs mdc) sink_path = Some (bytes KEY) /\ mo_le MT S Sc acc.
Definition cl_x2 (m : word -> option byte) (s s1 : cgif_st) (N : Z) (GPAL : list Z) (gs : YO07.gif_st) : Prop :=
rc_int (rw_cur s1) = cl_rcur1 (gcfg_of s GPAL) gs /\ rw_attr s1 = raw_attr_of (cg_attr s1) /\
(Z.land (cg_attr s1) 4 = 0 -> garr8 SEGS m (cg_pal s1) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s1) /\
oframe_relbA SEGS false m N (nth 1 (cg_frames s1) None) (YO07.s_q1 gs) /\
oframe_relbA SEGS true m N (nth 2 (cg_frames s1) None) (YO07.s_q2 gs).
Definition cl_macc_b (N : Z) : Z := 2 * xn_flush XN N.
Definition cl_macc_fr (N i : Z) : Z := cl_macc_b N + mo_free MT + (mo_free MT + mo_free MT) + i * (3 * mo_free MT).
Definition cl_msum (N : Z) : Z := cl_macc_fr N 3 + 2 * mo_free MT.
Definition CL_B_stmtX : Prop :=
forall ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1,
cl_cxX ly S W regs mem md ch g s N rest -> cl_xent ly S W mem md s N aM GPAL gs ->
cl_midX (xcgif_at SEGS WFN_ADDR path hw pf) ly S W regs mem md g s N ((pf, FILE_BLOCK) :: rest) lyc Sc Wc memc mdc k s1 (cgif_blocks g s N) -> k <= 2 * EV_FLUSH ->
cl_regs_at B regs regs1 g -> getr regs1 20 = w64 SB ->
cl_xopen S s GPAL Sc Wc memc mdc s1 (concat (YO07.close_gif (gcfg_of s GPAL) gs)) (cl_macc_b N) 1 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CL_B)) memc (seg_rom SEGS)) mdc) (cl_postX ly S W regs mem md g s N aM rest GPAL gs (k + 16)).
Definition CL_IT1_stmtX : Prop :=
forall ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1,
cl_cxX ly S W regs mem md ch g s N rest -> cl_xent ly S W mem md s N aM GPAL gs ->
cl_midX (xcgif_at SEGS WFN_ADDR path hw pf) ly S W regs mem md g s N ((pf, FILE_BLOCK) :: rest) lyc Sc Wc memc mdc k s1 (cgif_blocks g s N) -> k <= 0 -> cg_cur s1 = 0 ->
cl_regs_at B regs regs1 g -> getr regs1 20 = w64 SB ->
getr regs1 18 = w64 (g + 8 * (1 - 1)) -> getr regs1 21 = w64 (g + 8 * 1) -> getr regs1 22 = w64 (SB + (g + 8 * 1) / 8) -> getr regs1 23 = w64 (3 - 1) ->
cl_xopen S s GPAL Sc Wc memc mdc s1 (concat (YO07.s_out gs)) 0 (CLOSE_OUT N) ->
YO07.s_cur gs = YO07.C_OK -> af_xlive SEGS (rdW Wc memc) s1 N GPAL gs ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CL_IT)) memc (seg_rom SEGS)) mdc) (cl_postX ly S W regs mem md g s N aM rest GPAL gs (k + (3 - 1) * EV_FLUSH + 16)).
Definition CL_IT2_stmtX : Prop :=
forall ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1,
cl_cxX ly S W regs mem md ch g s N rest -> cl_xent ly S W mem md s N aM GPAL gs ->
cl_midX (xcgif_at SEGS WFN_ADDR path hw pf) ly S W regs mem md g s N ((pf, FILE_BLOCK) :: rest) lyc Sc Wc memc mdc k s1 (cgif_blocks g s N) -> k <= (2 - 1) * EV_FLUSH -> cg_cur s1 = 0 ->
cl_regs_at B regs regs1 g -> getr regs1 20 = w64 SB ->
getr regs1 18 = w64 (g + 8 * (2 - 1)) -> getr regs1 21 = w64 (g + 8 * 2) -> getr regs1 22 = w64 (SB + (g + 8 * 2) / 8) -> getr regs1 23 = w64 (3 - 2) ->
cl_xopen S s GPAL Sc Wc memc mdc s1 (concat (YO07.s_out gs) ++ cl_bytes (gcfg_of s GPAL) (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs))
(xn_flush XN N) (2 * FRAME_OUT N + 1) ->
YO07.s_cur gs = YO07.C_OK -> cl_code (gcfg_of s GPAL) (YO07.s_rcur gs) (YO07.s_q1 gs) (YO07.s_q0 gs) = YO07.C_OK ->
cl_x2 (rdW Wc memc) s s1 N GPAL gs ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CL_IT)) memc (seg_rom SEGS)) mdc) (cl_postX ly S W regs mem md g s N aM rest GPAL gs (k + (3 - 2) * EV_FLUSH + 16)).
Definition CL_FR_stmtX (i : Z) : Prop :=
forall ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1,
cl_cxX ly S W regs mem md ch g s N rest -> cl_xent ly S W mem md s N aM GPAL gs ->
cl_midX (tcgif_atIX (Z.to_nat i)) ly S W regs mem md g s N rest lyc Sc Wc memc mdc k s1 (fr_blocks g s N (Z.to_nat i)) -> k <= 2 * EV_FLUSH + 3 + 3 * i ->
cl_regs_at B regs regs1 g ->
getr regs1 18 = w64 (- (8 * i)) -> getr regs1 20 = w64 (SB + (g + 8 * i) / 8) -> getr regs1 21 = w64 (-24) -> getr regs1 22 = w64 (g + 8 * i) ->
cl_xclosed S Sc Wc memc mdc (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59]) (cl_macc_fr N i) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CL_FR)) memc (seg_rom SEGS)) mdc) (cl_postX ly S W regs mem md g s N aM rest GPAL gs (k + 3 * (3 - i) + 2)).
Definition CL_AFTER_stmtX (i : Z) : Prop :=
forall ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1,
cl_cxX ly S W regs mem md ch g s N rest -> cl_xent ly S W mem md s N aM GPAL gs ->
cl_midX (tcgif_atIX (Datatypes.S (Z.to_nat i))) ly S W regs mem md g s N rest lyc Sc Wc memc mdc k s1 (fr_blocks g s N (Datatypes.S (Z.to_nat i))) ->
k <= 2 * EV_FLUSH + 6 + 3 * i ->
cl_regs_at B regs regs1 g ->
getr regs1 18 = w64 (- (8 * i)) -> getr regs1 20 = w64 (SB + (g + 8 * i) / 8) -> getr regs1 21 = w64 (-24) -> getr regs1 22 = w64 (g + 8 * i) ->
cl_xclosed S Sc Wc memc mdc (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59]) (cl_macc_fr N (i + 1)) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CL_RET_FREEFRAME)) memc (seg_rom SEGS)) mdc) (cl_postX ly S W regs mem md g s N aM rest GPAL gs (k + 3 * (2 - i) + 2)).
Lemma cl_seedX : forall pc sregs (sv : bool) W1 (regs regs1 : bvmap 5 word) mem1 ly1 S1 md1 lya sp0 g s1,
AR SEGS B ly1 S1 W1 mem1 md1 ->
In (g, CGIF_SIZE) (ablocks B ly1 S1) ->
astk_ok TCLOSE_STK lya sp0 -> (forall a, sp0 - TCLOSE_STK <= a < sp0 -> apresent (w_H W1) mem1 a) ->
bv_unsigned (getr regs1 2) = sp0 - 80 - (0) ->
regs_ok (Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) sregs regs1 ->
(sv = true -> cl_frame SEGS (mrestrict (w_H W1) mem1) sp0 regs) ->
obj_at SEGS (mrestrict (w_H W1) mem1) g LAY_CGIF (xcgif_vals path hw pf s1) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) (ss_clX pc sregs (0) sv)
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS Bxc cl_SH (Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs sv W1 regs regs1 mem1 ly1 S1 md1 lya sp0 g s1 HAR Hing Hstk Hpres Hsp HREG HFR HOBJ.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TCLOSE_STK = 17520) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (obj_at_length _ _ _ _ _ HOBJ) as HL. cbn in HL.
assert (FLD : forall j o n v, nth_error LAY_CGIF j = Some (o, n) -> nth_error (xcgif_vals path hw pf s1) j = Some v ->
val_mem SEGS (mrestrict (w_H W1) mem1) (g + o) (N.to_nat n) v /\ 0 <= v < 2 ^ (8 * Z.of_N n)).
{ intros j o n v Hj Hv. exact (obj_at_nth SEGS _ _ _ _ j (o, n) v HOBJ Hj Hv). }
pose proof (FLD 0%nat 0 8%N _ eq_refl eq_refl) as [V0 R0]. pose proof (FLD 1%nat 8 8%N _ eq_refl eq_refl) as [V1 R1].
pose proof (FLD 2%nat 16 8%N _ eq_refl eq_refl) as [V2 R2]. pose proof (FLD 13%nat 72 8%N _ eq_refl eq_refl) as [V13 R13].
pose proof (FLD 14%nat 80 8%N _ eq_refl eq_refl) as [V14 R14]. pose proof (FLD 15%nat 88 4%N _ eq_refl eq_refl) as [V15 R15].
pose proof (FLD 3%nat 24 8%N _ eq_refl eq_refl) as [V3 R3]. pose proof (FLD 5%nat 40 4%N _ eq_refl eq_refl) as [V5 R5].
cbn [nth_error xcgif_vals] in V0, R0, V1, R1, V2, R2, V13, R13, V14, R14, V15, R15, V3, R3, V5, R5.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) in *. pose proof pa_B_ok as HBASE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (cl_extraX regs g s1 pf) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 80 - (0)) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 33%nat ltac:(unfold A_TEXT; lia)) as E33. pose proof (ES 34%nat ltac:(unfold A_TEXT; lia)) as E34.
pose proof (ES 35%nat ltac:(unfold A_TEXT; lia)) as E35. pose proof (ES 36%nat ltac:(unfold A_TEXT; lia)) as E36. pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37.
pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 39%nat ltac:(unfold A_TEXT; lia)) as E39. pose proof (ES 40%nat ltac:(unfold A_TEXT; lia)) as E40. pose proof (ES 51%nat ltac:(unfold A_TEXT; lia)) as E51.
cbn [Nat.sub nth cl_extraX cl_extra cl_saved map app] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E51.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
split.
- unfold ss_clX, cl_regionsX. apply pa_entry_st_ok_full.
+ exact HREG.
+ destruct sv; vm_compute; reflexivity.
+ unfold cl_stack, got_regionP, bcell_regionP, cl_objX.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
*   cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply Hpres. destruct sv; lia. }
destruct sv; [| constructor].
lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
let j := eval compute in (n - 41)%nat in let r := eval compute in (nth j cl_saved 0) in
apply (chunk_ok_val SEGS E _ (sp0 - 80 - (0)) off 8 (SOff n 0) (bv_unsigned (ew E n)));
[ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| let HR := fresh in pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; clear - HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
| cbn; lia
| replace (sp0 - 80 - (0) + off) with (sp0 - 8 - 8 * Z.of_nat j) by lia;
rewrite (ES n ltac:(unfold A_TEXT; lia)); cbn [Nat.sub nth cl_extraX cl_extra map app]; exact (HFR eq_refl j r eq_refl) ] end.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 Bxc SB);
[cbn [sv_denot Bxc]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
*   rewrite (VB 32%nat g E32) by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (_ & _ & _ & _ & HP & _).
apply HP. change (req_size CGIF_SIZE) with 96. lia. }
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]]].
-- apply (chunk_ok_val SEGS E _ g 0 8 _ (frame_ptr (nth 0 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V0].
-- apply (chunk_ok_val SEGS E _ g 8 8 _ (frame_ptr (nth 1 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V1].
-- apply (chunk_ok_val SEGS E _ g 16 8 _ (frame_ptr (nth 2 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V2].
-- apply (chunk_ok_val SEGS E _ g 24 8 _ (cg_pal s1)); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V3].
-- apply (chunk_ok_val SEGS E _ g 40 4 _ (cg_attr s1)); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V5].
-- apply (chunk_ok_val SEGS E _ g 72 8 _ (cg_raw s1)); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V13].
-- apply (chunk_ok_val SEGS E _ g 80 8 _ pf); [cbn [sv_denot]; rewrite E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V14].
-- apply (chunk_ok_val SEGS E _ g 88 4 _ (cg_cur s1)); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V15].
+ apply pairwise_disjoint_of_extents. unfold cl_stack, got_regionP, bcell_regionP, cl_objX, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 32%nat g E32) by lia. rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). cbn [base_val]. rewrite E2.
unfold CGIF_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 C1 C3 HTS Hstk0 HcellR HgcD HgotR. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ destruct sv; (split; [|split; exact I]);
cbn [f_atoms atoms_ok cl_facts cl_facts_mid]; (split; [|split; [|split; [|exact I]]]);
unfold afact_ok, hfact; cbn [af_lo af_hi af_al2];
rewrite ?E2, ?E32, ?E38, ?unsigned_lit_small by (unfold SB; lia);
change (2 ^ 4) with 16; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hsp0al C1 C3 HTS Hstk0; clear; unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg; intros;
repeat match goal with |- _ /\ _ => split end; try lia;
replace (sp0 - 80 - (0)) with (sp0 + (-5) * 16) by lia; rewrite Z_mod_plus_full; exact Hsp0al.
- unfold sh_ok, cl_SH. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS ly1 S1 W1 mem1 md1 E Bxc 32 g CGIF_SIZE 0 CGIF_SIZE HAR Hing).
+ unfold U, Bxc. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
Qed.
Lemma cl_seed_entryX : forall pc sregs W1 (regs regs1 : bvmap 5 word) mem1 ly1 S1 md1 lya sp0 g s1,
AR SEGS B ly1 S1 W1 mem1 md1 ->
In (g, CGIF_SIZE) (ablocks B ly1 S1) ->
astk_ok TCLOSE_STK lya sp0 -> (forall a, sp0 - TCLOSE_STK <= a < sp0 -> apresent (w_H W1) mem1 a) ->
bv_unsigned (getr regs1 2) = sp0 - 80 - (-80) ->
regs_ok (Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) sregs regs1 ->
obj_at SEGS (mrestrict (w_H W1) mem1) g LAY_CGIF (xcgif_vals path hw pf s1) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) (ss_clX pc sregs (-80) false)
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS Bxc cl_SH (Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs W1 regs regs1 mem1 ly1 S1 md1 lya sp0 g s1 HAR Hing Hstk Hpres Hsp HREG HOBJ.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TCLOSE_STK = 17520) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (obj_at_length _ _ _ _ _ HOBJ) as HL. cbn in HL.
assert (FLD : forall j o n v, nth_error LAY_CGIF j = Some (o, n) -> nth_error (xcgif_vals path hw pf s1) j = Some v ->
val_mem SEGS (mrestrict (w_H W1) mem1) (g + o) (N.to_nat n) v /\ 0 <= v < 2 ^ (8 * Z.of_N n)).
{ intros j o n v Hj Hv. exact (obj_at_nth SEGS _ _ _ _ j (o, n) v HOBJ Hj Hv). }
pose proof (FLD 0%nat 0 8%N _ eq_refl eq_refl) as [V0 R0]. pose proof (FLD 1%nat 8 8%N _ eq_refl eq_refl) as [V1 R1].
pose proof (FLD 2%nat 16 8%N _ eq_refl eq_refl) as [V2 R2]. pose proof (FLD 13%nat 72 8%N _ eq_refl eq_refl) as [V13 R13].
pose proof (FLD 14%nat 80 8%N _ eq_refl eq_refl) as [V14 R14]. pose proof (FLD 15%nat 88 4%N _ eq_refl eq_refl) as [V15 R15].
pose proof (FLD 3%nat 24 8%N _ eq_refl eq_refl) as [V3 R3]. pose proof (FLD 5%nat 40 4%N _ eq_refl eq_refl) as [V5 R5].
cbn [nth_error xcgif_vals] in V0, R0, V1, R1, V2, R2, V13, R13, V14, R14, V15, R15, V3, R3, V5, R5.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) in *. pose proof pa_B_ok as HBASE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (cl_extraX regs g s1 pf) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 80 - (-80)) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 33%nat ltac:(unfold A_TEXT; lia)) as E33. pose proof (ES 34%nat ltac:(unfold A_TEXT; lia)) as E34.
pose proof (ES 35%nat ltac:(unfold A_TEXT; lia)) as E35. pose proof (ES 36%nat ltac:(unfold A_TEXT; lia)) as E36. pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37.
pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 39%nat ltac:(unfold A_TEXT; lia)) as E39. pose proof (ES 40%nat ltac:(unfold A_TEXT; lia)) as E40. pose proof (ES 51%nat ltac:(unfold A_TEXT; lia)) as E51.
cbn [Nat.sub nth cl_extraX cl_extra cl_saved map app] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E51.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
split.
- unfold ss_clX, cl_regionsX. apply pa_entry_st_ok_full.
+ exact HREG.
+ vm_compute. reflexivity.
+ unfold cl_stack, got_regionP, bcell_regionP, cl_objX.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
*   cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
constructor.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 Bxc SB);
[cbn [sv_denot Bxc]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
*   rewrite (VB 32%nat g E32) by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (_ & _ & _ & _ & HP & _).
apply HP. change (req_size CGIF_SIZE) with 96. lia. }
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]]].
-- apply (chunk_ok_val SEGS E _ g 0 8 _ (frame_ptr (nth 0 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V0].
-- apply (chunk_ok_val SEGS E _ g 8 8 _ (frame_ptr (nth 1 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V1].
-- apply (chunk_ok_val SEGS E _ g 16 8 _ (frame_ptr (nth 2 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V2].
-- apply (chunk_ok_val SEGS E _ g 24 8 _ (cg_pal s1)); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V3].
-- apply (chunk_ok_val SEGS E _ g 40 4 _ (cg_attr s1)); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V5].
-- apply (chunk_ok_val SEGS E _ g 72 8 _ (cg_raw s1)); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V13].
-- apply (chunk_ok_val SEGS E _ g 80 8 _ pf); [cbn [sv_denot]; rewrite E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V14].
-- apply (chunk_ok_val SEGS E _ g 88 4 _ (cg_cur s1)); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V15].
+ apply pairwise_disjoint_of_extents. unfold cl_stack, got_regionP, bcell_regionP, cl_objX, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 32%nat g E32) by lia. rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). cbn [base_val]. rewrite E2.
unfold CGIF_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 C1 C3 HTS Hstk0 HcellR HgcD HgotR. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; exact I].
cbn [f_atoms atoms_ok cl_facts]. unfold afact_ok, hfact. cbn [af_lo af_hi af_al2].
rewrite E2, E32, E38, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hsp0al C1 C3 HTS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; try lia.
replace (sp0 - 80 - (-80)) with sp0 by lia. exact Hsp0al.
- unfold sh_ok, cl_SH. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS ly1 S1 W1 mem1 md1 E Bxc 32 g CGIF_SIZE 0 CGIF_SIZE HAR Hing).
+ unfold U, Bxc. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
Qed.
Lemma tcgif_at2X_kept : forall H H' m m' g s1,
tcgif_at2X (mrestrict H m) g s1 -> blk_kept H H' m m' g 96 ->
(forall f, In (Some f) (cg_frames s1) -> blk_kept H H' m m' (fr_ptr f) 40) ->
tcgif_at2X (mrestrict H' m') g s1.
Proof.
intros H H' m m' g s1 [Hg Hf] Kg Kf. split.
- exact (obj_at_blk_kept H H' m m' g LAY_CGIF _ 96 Hg lay_inside_CGIF Kg).
- intros f Hin. exact (obj_at_blk_kept H H' m m' (fr_ptr f) LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame (Kf f Hin)).
Qed.
Lemma xcgif_at_kept : forall H H' m m' g s1,
xcgif_at SEGS WFN_ADDR path hw pf (mrestrict H m) g s1 -> blk_kept H H' m m' g 96 -> blk_kept H H' m m' (cg_raw s1) 48 ->
(forall f, In (Some f) (cg_frames s1) -> blk_kept H H' m m' (fr_ptr f) 40) ->
xcgif_at SEGS WFN_ADDR path hw pf (mrestrict H' m') g s1.
Proof.
intros H H' m m' g s1 (Hg & Hr & Hf) Kg Kr Kf. split; [|split].
- exact (obj_at_blk_kept H H' m m' g LAY_CGIF _ 96 Hg lay_inside_CGIF Kg).
- exact (obj_at_blk_kept H H' m m' (cg_raw s1) LAY_Raw _ 48 Hr lay_inside_Raw Kr).
- intros f Hin. exact (obj_at_blk_kept H H' m m' (fr_ptr f) LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame (Kf f Hin)).
Qed.
Lemma xcgif_at_2 : forall m g s1, xcgif_at SEGS WFN_ADDR path hw pf m g s1 -> tcgif_at2X m g s1.
Proof. intros m g s1 (Hg & _ & Hf). exact (conj Hg Hf). Qed.
Lemma tcgif_atIX_0 : forall m g s1, xcgif_at SEGS WFN_ADDR path hw pf m g s1 -> tcgif_atIX 0 m g s1.
Proof. intros m g s1 (Hg & _ & Hf). split; [exact Hg|]. intros j f _ Hj. apply Hf. eapply nth_error_In. exact Hj. Qed.
Lemma tcgif_atIX_le : forall i j m g s1, (i <= j)%nat -> tcgif_atIX i m g s1 -> tcgif_atIX j m g s1.
Proof. intros i j m g s1 Hij [Hg Hf]. split; [exact Hg|]. intros jj f Hjj. apply Hf. lia. Qed.
Lemma tcgif_atIX_kept : forall i H H' m m' g s1,
tcgif_atIX i (mrestrict H m) g s1 -> blk_kept H H' m m' g 96 ->
(forall j f, (i <= j)%nat -> nth_error (cg_frames s1) j = Some (Some f) -> blk_kept H H' m m' (fr_ptr f) 40) ->
tcgif_atIX i (mrestrict H' m') g s1.
Proof.
intros i H H' m m' g s1 [Hg Hf] Kg Kf. split.
- exact (obj_at_blk_kept H H' m m' g LAY_CGIF _ 96 Hg lay_inside_CGIF Kg).
- intros j f Hij Hj. exact (obj_at_blk_kept H H' m m' (fr_ptr f) LAY_Frame _ 40 (Hf j f Hij Hj) lay_inside_Frame (Kf j f Hij Hj)).
Qed.
End e.
End c.
End b.
