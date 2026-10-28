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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8a ACjr ACj3 ACh9 AChb ACk4 ACk5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YC5d YC7z YC7x YC21 YC85 YC86 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI17 YE02 YC5n YC5l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACk0 ACk2 ACk3 ACjo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjy ACjz.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {NP : ng_params}.
#[local] Notation hw := (@ngp_hw NP).
#[local] Notation CTX := (@ngp_ctx NP).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma awr_byte_callee1 : forall STK STK' sp sp' (bl0 bl0' blc : list (Z * Z)) lyq lyq' a,
awr_byte STK' sp' [] bl0' blc lyq' [] a -> sp - STK <= sp' - STK' -> sp' <= sp -> (forall b, In b bl0 -> In b bl0') ->
awr_byte STK sp [] bl0 blc lyq [] a.
Proof.
intros STK STK' sp sp' bl0 bl0' blc lyq lyq' a [H | [[Hf _] | [(b & n & Hin & Hn0 & Hb) | (c & p & Hin & _)]]] H1 H2 Hsub.
- left. lia.
- exfalso. exact (inFP_nil _ Hf).
- right; right; left. exists b, n. split; [exact Hin|]. split; [intros Hc; exact (Hn0 (Hsub _ Hc)) | exact Hb].
- destruct Hin.
Qed.
Lemma awr_byte_calleeX : forall STK STK' sp sp' FP FP' (bl0 bl0' blc : list (Z * Z)) lyq lyq' a,
awr_byte STK' sp' FP' bl0' blc lyq' [] a -> sp - STK <= sp' - STK' -> sp' <= sp -> (forall b, In b bl0 -> In b bl0') -> ~ inFP FP' a ->
awr_byte STK sp FP bl0 blc lyq [] a.
Proof.
intros STK STK' sp sp' FP FP' bl0 bl0' blc lyq lyq' a [H | [[Hf _] | [(b & n & Hin & Hn0 & Hb) | (c & p & Hin & _)]]] H1 H2 Hsub HnF.
- left. lia.
- exfalso. exact (HnF Hf).
- right; right; left. exists b, n. split; [exact Hin|]. split; [intros Hc; exact (Hn0 (Hsub _ Hc)) | exact Hb].
- destruct Hin.
Qed.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Variable CTXR : list (list Z).
Hypothesis HCTXR : forall l, In l CTX -> In ((BASE + 0x398) :: l) CTXR.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis TLF : PALibF B.
Hypothesis Rhw : 0 <= hw < 2 ^ 64.
Hypothesis HGOT3 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 3)) 8 (BASE + 0).
Hypothesis HU : forall c t, In c CTX -> In t (ng_traces B c) -> In t (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Local Notation code := (as_code B).
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Variable XN : xnums.
Hypothesis HXN : forall ngp, 0 <= ngp <= 65535 -> ng_msum MT ngp <= xn_newgif XN ngp.
Hypothesis HXM : forall ngp, 0 <= ngp <= 65535 -> ng_msum MT ngp <= xm_newgif XN ngp.
Hypothesis RAWNEWX : trawnew_specX SEGS K B MT (SIGMA AS_cgif_raw_newgif) CTXR (BASE + 0x614) hw pa_relro_lo pa_relro_hi.
Variable ra_fc1 ra_fc2 : Z.
Hypothesis AFCLOSE : afclose_spec SEGS B K (SIGMA AS_fclose) ra_fc1 ra_fc2 pa_relro_lo pa_relro_hi.
Hypothesis HUfc1 : In [pc_free_ra0 code; ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 code; ra_fc2] (as_universe B).
Hypothesis AFM : afile_meter SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Lemma ng_P1X : NG_P1_stmtX B K MT XN.
Proof.
intros ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 E W3 ly3 S3 ms3 md3 k fpos pf g pal HCTX HXE HCFG HE0 HEX E52 Rg Rp HNOW HW0 HH0 Ha4 Epala HGPAL HS.
destruct HEX as [HE E42]. pose proof HXE as (HGP & HSNK0 & HFD0 & HAM0 & HMOK). destruct (HGP Ha4) as [HG0 HGl].
ng_facts HCTX HCFG HE0 HE.
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3 & Hg4096 & Hp4096 & Hpf4096 & Tg & Ag & Tp & Ap & Tpf & Apf & HSINK & MLE3).
pose proof (req_size_pos (3 * ngp) ltac:(clear - CR28; lia)) as [Hrq1 Hrq2].
ng_frame HJ3 Hfrs3.
assert (Rngp : 0 <= ngp <= 65535) by (clear - CR28; lia).
assert (Rpath : 0x10000 <= ak_path K < 0x5fb000).
{ apply (pa_img_range (ak_path K)). apply (proj1 (ail_env _ _ _ AIL (ak_path K) ltac:(unfold aenv_addr; right; right; right; left; lia))). }
assert (Hpf_in : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pf FILE_BLOCK HAR3 Hpf_in) as (Hpf16 & _ & Hpfceil & Hp_ia & _ & _).
pose proof (blk_off_imgP _ _ _ _ _ _ pf FILE_BLOCK HAR3 Hpf_in) as Hph_img. change (req_size FILE_BLOCK) with 1264 in Hpfceil, Hph_img, Hp_ia. unfold off_img in Hph_img.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pf FILE_BLOCK 1 fpos HAR3 Hpf_in Hfin3) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (req_size FILE_BLOCK) with 1264 in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite ?EFA3 in HdPF. fold F in HdPF.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pf FILE_BLOCK cid pos HAR3 Hpf_in HfinS3) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. change (req_size FILE_BLOCK) with 1264 in HdPC. rewrite ?EFA3 in HdPC.
pose proof HFhigh_img as HFoffX. unfold off_img in HFoffX.
assert (XF : xfacts ((alloc_ceiling + TNEWGIFX_STK <= spZ regs /\ TNEWGIFX_STK = 18816 /\ 140735332483072 <= alloc_ceiling <= 140737479966720 /\
(F + 128 <= 65536 \/ 6270976 <= F) /\ 4096 <= F /\ F + 128 <= alloc_ceiling /\ 512 <= F / 8) /\
pf + 1264 <= alloc_ceiling /\ 4096 <= pf /\ (pf + 1264 <= 65536 \/ 6270976 <= pf) /\
(pf + 1264 <= cfgp \/ cfgp + 48 <= pf) /\ 4096 <= cfgp /\ (pf + 1264 <= F \/ F + 128 <= pf)))
by (apply xfacts_i; clear - Hceil Hslo FFS C1 HFoffX HF4096 HFceil HF8lo Hpfceil Hpf4096 Hph_img HdPC HdPF Hflo Hfhi Hf4096; lia).
clear HdPC HdPF Hph_img HFoffX. change (in_app pf 1264) with (xfacts (in_app pf 1264)) in Hp_ia.
assert (Hg_in : In (g, 96) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
assert (Hp_in : In (pal, 3 * ngp) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pal (3 * ngp) HAR3 Hp_in) as (Hp16 & _ & Hpceil & Hph_ia & Hppres3 & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR3 Hp_in) as Hph_img.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pal (3 * ngp) 1 fpos HAR3 Hp_in Hfin3) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA3 in HdPF. fold F in HdPF.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pal (3 * ngp) cid pos HAR3 Hp_in HfinS3) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. rewrite EFA3 in HdPC.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR3 Hg_in) as (Hg16 & _ & Hgceil & Hgh_ia & Hgpres3 & _). pose proof (proj1 Hgh_ia) as Hgh. change (req_size 96) with 96 in Hgceil, Hgpres3.
pose proof (blk_off_imgP _ _ _ _ _ _ g 96 HAR3 Hg_in) as Hgh_img.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ g 96 1 fpos HAR3 Hg_in Hfin3) as HdGF.
unfold zdisjoint in HdGF. cbn [fst snd] in HdGF. change (req_size 96) with 96 in HdGF. change (fs_frame_bytes 1) with 128 in HdGF. rewrite EFA3 in HdGF. fold F in HdGF.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ g 96 cid pos HAR3 Hg_in HfinS3) as HdGC.
unfold zdisjoint in HdGC. cbn [fst snd] in HdGC. change (req_size 96) with 96 in HdGC. rewrite EFA3 in HdGC.
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ pf FILE_BLOCK g 96 HAR3 Hpf_in Hg_in ltac:(unfold FILE_BLOCK; intros X; injection X; lia)) as HdXG.
unfold zdisjoint in HdXG. cbn [fst snd] in HdXG. change (req_size FILE_BLOCK) with 1264 in HdXG.
change (req_size 96) with 96 in HdXG. pose proof Hgh_img as HGoffX. unfold off_img in HGoffX. change (req_size 96) with 96 in HGoffX.
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (P /\ (pf + 1264 <= g \/ g + 96 <= pf) /\ 4096 <= g /\ g + 96 <= alloc_ceiling /\ (g + 96 <= 65536 \/ 6270976 <= g)))
by (apply xfacts_i; split; [exact XF | clear - HdXG Hg4096 Hgceil HGoffX; lia]); clear XF HGoffX HdXG; rename XF2 into XF end.
pose proof (sep_blocks SEGS B LAWS ly3 S3 _ _ _ pf FILE_BLOCK pal (3 * ngp) HAR3 Hpf_in Hp_in ltac:(unfold FILE_BLOCK; intros X; injection X; clear; lia)) as HdXP.
unfold zdisjoint in HdXP. cbn [fst snd] in HdXP. change (req_size FILE_BLOCK) with 1264 in HdXP.
assert (HPermPG : Permutation (ablocks B ly3 S3) ((pal, 3 * ngp) :: (g, 96) :: (ablocks B ly S ++ [(pf, FILE_BLOCK)]))).
{ rewrite Eab3, <- app_assoc. cbn [app]. apply Permutation_sym.
apply (Permutation_trans (perm_swap (g, 96) (pal, 3 * ngp) (ablocks B ly S ++ [(pf, FILE_BLOCK)]))).
change ((g, 96) :: (pal, 3 * ngp) :: (ablocks B ly S ++ [(pf, FILE_BLOCK)])) with ([(g, 96); (pal, 3 * ngp)] ++ (ablocks B ly S ++ [(pf, FILE_BLOCK)])). apply Permutation_app_comm. }
pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 _ _ _ (pal, 3 * ngp) (g, 96) _ HAR3 HPermPG) as HdXPG.
unfold zdisjoint, block_rng in HdXPG. cbn [fst snd] in HdXPG. change (req_size 96) with 96 in HdXPG.
pose proof Hph_img as HPoffX. unfold off_img in HPoffX.
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (P /\ (pf + 1264 <= pal \/ pal + req_size (3 * ngp) <= pf) /\ 4096 <= pal /\ pal + req_size (3 * ngp) <= alloc_ceiling /\
(pal + req_size (3 * ngp) <= 65536 \/ 6270976 <= pal) /\ 3 * ngp <= req_size (3 * ngp) /\
(pal + req_size (3 * ngp) <= F \/ F + 128 <= pal) /\ (pal + req_size (3 * ngp) <= g \/ g + 96 <= pal)))
by (apply xfacts_i; split; [exact XF | clear - HdXP Hp4096 Hpceil HPoffX Hrq2 HdPF HdXPG; lia]);
clear XF HPoffX HdXP HdXPG; rename XF2 into XF end.
pose proof Hph_ia as Hpal_ia. change (in_app pal (req_size (3 * ngp))) with (xfacts (in_app pal (req_size (3 * ngp)))) in Hpal_ia.
pose proof HPerm as HPermA. rewrite Ha4 in HPermA. cbn [Z.eqb app] in HPermA.
assert (Hpala_in : In (pala, 3 * ngp) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPermA|]; left; reflexivity).
assert (Hpala3 : In (pala, 3 * ngp) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; apply in_app_iff; left; apply in_app_iff; left; exact Hpala_in).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pala (3 * ngp) HAR Hpala_in) as (_ & Hpala4096 & _).
nbox_seps.
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
reshok_bx HS 35%nat.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK NBspan.
all: try (slim; oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
xsink_stretch HFr HSINK. xgarr_stretch HFr HGPAL. clear_frames.
set (sgct := ngp).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 516 F cs lo hi wlo whi 32 8%N (SOff A_TEXT 1556) (BASE + 0x614) HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(apply codeptr_val; first [assumption | hei_prove]) ltac:(clear - PBASE; lia) ltac:(cbn; lia)) as Vwfn;
pose proof (field_of_region Ex _ 516 F cs lo hi wlo whi 40 8%N (SOff 550 0) g HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; clear - Hg4096 Hgceil C1; lia) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 516 F cs lo hi wlo whi 48 8%N (SOff 32 0) pal0 HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; clear - CR0; lia) ltac:(cbn; lia)) as Vgct;
pose proof (field_of_region Ex _ 516 F cs lo hi wlo whi 56 4%N _ (ng_rattr attr) HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto)
ltac:(rewrite denot_lit_U; f_equal; apply (U_ng_rattr _ 33 attr); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E33 | exact CR16])
ltac:(pose proof (ng_rattr_range attr ltac:(clear - CR16; lia)); cbn; lia) ltac:(cbn; lia)) as Vrat;
let gh off e n v Hn Rv V := pose proof (field_of_region_any Ex _ 516 F cs lo hi wlo whi off 2%N e HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
change (bv_unsigned (sv_denot Ex e)) with (U Ex e) in V; change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16) in V;
rewrite (U_sext16_mod Ex (SOff n 0) v ltac:(apply (U_atom Ex n v); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Hn | clear - Rv; lia]) Rv) in V in
gh 60 (SExt true 16 (SOff 36 0)) 36%nat Wd E36 CR24 VW;
gh 62 (SExt true 16 (SOff 37 0)) 37%nat Hd E37 CR26 VH;
gh 66 (SExt true 16 (SOff 39 0)) 39%nat loops E39 CR30 Vlp
end; clear HRc | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 516 F cs lo hi wlo whi 32 8%N (SOff A_TEXT 1556) (BASE + 0x614) HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(apply codeptr_val; first [assumption | hei_prove]) ltac:(clear - PBASE; lia) ltac:(cbn; lia)) as Vwfn;
pose proof (field_of_region Ex _ 516 F cs lo hi wlo whi 40 8%N (SOff 550 0) g HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; clear - Hg4096 Hgceil C1; lia) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 516 F cs lo hi wlo whi 48 8%N (SOff 32 0) pal0 HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; clear - CR0; lia) ltac:(cbn; lia)) as Vgct;
pose proof (field_of_region Ex _ 516 F cs lo hi wlo whi 56 4%N _ (ng_rattr attr) HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto)
ltac:(rewrite denot_lit_U; f_equal; apply (U_ng_rattr _ 33 attr); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E33 | exact CR16])
ltac:(pose proof (ng_rattr_range attr ltac:(clear - CR16; lia)); cbn; lia) ltac:(cbn; lia)) as Vrat;
let gh off e n v Hn Rv V := pose proof (field_of_region_any Ex _ 516 F cs lo hi wlo whi off 2%N e HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
change (bv_unsigned (sv_denot Ex e)) with (U Ex e) in V; change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16) in V;
rewrite (U_sext16_mod Ex (SOff n 0) v ltac:(apply (U_atom Ex n v); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Hn | clear - Rv; lia]) Rv) in V in
gh 60 (SExt true 16 (SOff 36 0)) 36%nat Wd E36 CR24 VW;
gh 62 (SExt true 16 (SOff 37 0)) 37%nat Hd E37 CR26 VH;
gh 66 (SExt true 16 (SOff 39 0)) 39%nat loops E39 CR30 Vlp
end; clear HRc  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 516 F cs lo hi wlo whi 64 2%N (SOff 38 0) ngp HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; clear - CR28; lia) ltac:(cbn; lia)) as Vsg end; clear HRc | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 516 F cs lo hi wlo whi 64 2%N (SOff 38 0) ngp HRc
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; clear - CR28; lia) ltac:(cbn; lia)) as Vsg end; clear HRc  end.
cbn [N.to_nat] in Vwfn, Vctx, Vgct, Vrat, VW, VH, Vlp, Vsg.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (Ocfg : obj_at SEGS (mrestrict (w_H W3) (ms_mem msX)) (F + 32) LAY_RawConfig [(BASE + 0x614); g; pal0; ng_rattr attr; Wd; Hd; sgct; loops]) | st_ok _ _ _ (restrict _ ?msX) =>
assert (Ocfg : obj_at SEGS (mrestrict (w_H W3) (ms_mem msX)) (F + 32) LAY_RawConfig [(BASE + 0x614); g; pal0; ng_rattr attr; Wd; Hd; sgct; loops])  end.
{ cbn [obj_at LAY_RawConfig]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N].
pose proof (ng_rattr_range attr ltac:(clear - CR16; lia)) as Hrr.
replace (F + 32 + 0) with (F + 32) by lia. replace (F + 32 + 8) with (F + 40) by lia. replace (F + 32 + 16) with (F + 48) by lia.
replace (F + 32 + 24) with (F + 56) by lia. replace (F + 32 + 28) with (F + 60) by lia. replace (F + 32 + 30) with (F + 62) by lia.
replace (F + 32 + 32) with (F + 64) by lia. replace (F + 32 + 34) with (F + 66) by lia.
repeat split; try assumption; clear - Hrr CR0 CR16 CR24 CR26 CR28 CR30 Hg4096 Hgceil C1 sgct PBASE; cbv delta [sgct]; lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 550%nat in let i := eval vm_compute in i in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
assert (HB79 : bv_unsigned (ew Ex 550) = g) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg; apply unsigned_lit_small; clear - Hg4096 Hgceil C1; lia);
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 550%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi 56 8%N (SLit hw) hw HRg HB79 ltac:(cbn; tauto) eq_refl ltac:(clear - Rhw; zside) ltac:(cbn; lia)) as Gwfn;
pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi 64 8%N (SLit 0) 0 HRg HB79 ltac:(cbn; tauto) eq_refl ltac:(zside) ltac:(cbn; lia)) as Gctx;
pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi 80 8%N (SOff 52 0) pf HRg HB79 ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E52)
ltac:(cbn; clear - Hpf4096 Hpfceil C1; lia) ltac:(cbn; lia)) as Gfile
end; clear HRg | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 550%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
assert (HB79 : bv_unsigned (ew Ex 550) = g) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg; apply unsigned_lit_small; clear - Hg4096 Hgceil C1; lia);
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 550%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi 56 8%N (SLit hw) hw HRg HB79 ltac:(cbn; tauto) eq_refl ltac:(clear - Rhw; zside) ltac:(cbn; lia)) as Gwfn;
pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi 64 8%N (SLit 0) 0 HRg HB79 ltac:(cbn; tauto) eq_refl ltac:(zside) ltac:(cbn; lia)) as Gctx;
pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi 80 8%N (SOff 52 0) pf HRg HB79 ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E52)
ltac:(cbn; clear - Hpf4096 Hpfceil C1; lia) ltac:(cbn; lia)) as Gfile
end; clear HRg  end.
cbn [N.to_nat] in Gwfn, Gctx, Gfile.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi ?cs) =>
assert (ZS5 : forall j, 4 <= j <= 8 -> val_mem SEGS (mrestrict (w_H W3) (ms_mem msX)) (SB + F / 8 + j) 1 0);
[ let j := fresh "j" in let Hj := fresh "Hj" in let Hj5 := fresh "Hj5" in intros j Hj;
assert (Hj5 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by (clear - Hj; lia);
destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]];
(eapply (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi _ 1%N (SLit 0) 0 HRfs);
[evalE AG | cbn; tauto | reflexivity | cbn; lia | cbn; lia])
| ] end;
clear HRfs;
assert (HRA40 : range_addressable (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 32) 40);
[ apply zero_shadow_range; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | reflexivity |];
let ii := fresh "ii" in let Hii := fresh "Hii" in
intros ii Hii; change (40 / 8) with 5 in Hii; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF;
replace (SB + (F + 32) / 8 + ii) with (SB + F / 8 + (4 + ii)) by (rewrite HFq at 2; rewrite HF8; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
apply (aview_of_val_mem1 SEGS); [apply ZS5; clear - Hii; lia | clear; lia]
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi ?cs) =>
assert (ZS5 : forall j, 4 <= j <= 8 -> val_mem SEGS (mrestrict (w_H W3) (ms_mem msX)) (SB + F / 8 + j) 1 0);
[ let j := fresh "j" in let Hj := fresh "Hj" in let Hj5 := fresh "Hj5" in intros j Hj;
assert (Hj5 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by (clear - Hj; lia);
destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]];
(eapply (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi _ 1%N (SLit 0) 0 HRfs);
[evalE AG | cbn; tauto | reflexivity | cbn; lia | cbn; lia])
| ] end;
clear HRfs;
assert (HRA40 : range_addressable (aview SEGS (w_H W3) (ms_mem msX)) SHADOW_OFF (F + 32) 40);
[ apply zero_shadow_range; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | reflexivity |];
let ii := fresh "ii" in let Hii := fresh "Hii" in
intros ii Hii; change (40 / 8) with 5 in Hii; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF;
replace (SB + (F + 32) / 8 + ii) with (SB + F / 8 + (4 + ii)) by (rewrite HFq at 2; rewrite HF8; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
apply (aview_of_val_mem1 SEGS); [apply ZS5; clear - Hii; lia | clear; lia]
| ]  end.
assert (HEVc : st_nev S3 + EV_RAWNEW <= EV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _). unfold EV_RAWNEW. rewrite HEV in Hev. clear - Hnev3 Hk3 Hev. lia. }
assert (HLIVEc : blocks_bytes S3 + 2 ^ 16 <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), Eab3, !bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. unfold LIVE_NEWGIF in Hlive. unfold FILE_BLOCK. clear - Hlive CR28. lia. }
pose (restX := (pal, 3 * ngp) :: ablocks B ly S).
assert (HBL : Permutation (ablocks B ly3 S3) ((g, CGIF_SIZE) :: (pf, FILE_BLOCK) :: restX)).
{ subst restX. rewrite Eab3, <- !app_assoc. cbn [app]. apply Permutation_sym.
change ((g, CGIF_SIZE) :: (pf, FILE_BLOCK) :: (pal, 3 * ngp) :: ablocks B ly S) with ([(g, 96); (pf, FILE_BLOCK); (pal, 3 * ngp)] ++ ablocks B ly S).
eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app_head. apply perm_swap. }
assert (HnPF : ~ In (pf, FILE_BLOCK) (ablocks B ly S)).
{ intros Hin0. pose proof (Tpf Hin0 0 ltac:(cbn [fst snd]; change (req_size FILE_BLOCK) with 1264; clear; lia)) as Hq. cbn [fst snd] in Hq. apply inFP_token in Hq. clear - Hq Hpf4096. lia. }
assert (HMOKc : mo_ok MT S3 (mo_malloc MT RAW_SIZE)).
{ apply (mok_station MT S S3 (xm_newgif XN ngp) (ng_macc3 MT ngp) _ MLAW HMOK MLE3); [apply (mo_malloc_nonneg MT MLAW); unfold RAW_SIZE; clear; lia|].
pose proof (HXM ngp Rngp) as Hx. unfold ng_msum, ng_macc3 in Hx.
pose proof (mo_malloc_nonneg MT MLAW (3 * ngp) ltac:(clear - Rngp; lia)) as M3. pose proof (mo_free_nonneg MT MLAW) as M5. try unfold ng_macc3. clear - Hx M3 M5. lia. }
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wc ?memc _ _ =>
assert (HGPALA : garr8 SEGS (mrestrict (w_H Wc) memc) pala GPAL) end.
{ apply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pala (3 * ngp) pala GPAL HJ3 Hpala_in Hpala3);
[ clear; lia | rewrite HGl; clear - Hrq2; lia | intros a Ha Hn; apply inFP_token in Hn; clear - Ha Hn Hpala4096; lia | exact HG0 ]. }
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
ng_chain HS HJ3 AG EE.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (HspX : spZ (ms_regs msX) = spZ regs - 192) by (unfold spZ at 1; rewrite Rsp; evalE AG; clear; lia) | st_ok _ _ _ (restrict _ ?msX) =>
assert (HspX : spZ (ms_regs msX) = spZ regs - 192) by (unfold spZ at 1; rewrite Rsp; evalE AG; clear; lia)  end.
pose proof (proj1 (proj2 HJ3)) as HLY3. pose proof HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssX (restrict _ ?msX) =>
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdX) _ =>
eapply SRr_bind;
[ eapply (aj_callS SEGS B LAWS pa_segs_low W3 Ex (abs_ss VAL ssX) msX TNEWGIFX_STK (spZ regs) [sink_token] ly S W mem md [(1, fpos)] ly3 S3 mdX k
TRAWNEW_STK (asink_fp pf) EV_RAWNEW (-192) (ew Ex 2) (Z_to_bv 64 (BASE + 0x398)) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => exists res : Z, getr regs2 10 = w64 res /\
mo_le MT S3 S2 (mo_malloc MT RAW_SIZE) /\
((res = 0 /\ 256 < sgct /\ Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
asink_at SEGS K (mrestrict (w_H W2) mem2) md2 pf []) \/
(res <> 0 /\ sgct <= 256 /\
Permutation (ablocks B ly2 S2) ((res, RAW_SIZE) :: ablocks B ly3 S3) /\
(forall blc i, In (res, RAW_SIZE) blc -> 0 <= i < RAW_SIZE ->
awr_byte TRAWNEW_STK (spZ regs - 192) (asink_fp pf) (ablocks B ly3 S3) blc ly2 [] (res + i)) /\
aftok (asink_fp pf) (ablocks B ly3 S3) (res, RAW_SIZE) /\
obj_at SEGS (mrestrict (w_H W2) mem2) res LAY_Raw [(BASE + 0x614); g; pal0; ng_rattr attr; Wd; Hd; sgct; loops; R_PENDING] /\
asink_at SEGS K (mrestrict (w_H W2) mem2) md2 pf ([] ++ YO07.raw_header Wd Hd sgct GPAL (ng_rattr attr) loops)))) HS eq_refl HJ3);
[ rewrite Rsp; cbn [sv_denot]; reflexivity
| reflexivity
| evalE AG
| reflexivity
| clear; lia
| unfold TRAWNEW_STK, ASTACK; clear; lia
| rewrite FFS; unfold TRAWNEW_STK, ASTACK; clear; lia
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| apply ret_ok_codeptr_v; [clear; lia | reflexivity]
| rewrite unsigned_lit_small by (clear - PBASE PBLO; lia); clear - PBASE PBLO; lia
| unfold s0Z; rewrite Rs0; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
replace (spZ regs + -192) with (spZ regs - 192) by (clear - PBASE PBLO; lia); exact (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1)
| intros HPRE1; eapply SRr_mono;
[ pose proof (RAWNEWX ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch) (F + 32) g pal0 (ng_rattr attr) Wd Hd sgct loops 0 pf pala (3 * ngp) restX [] GPAL HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 (SIGMA AS_cgif_raw_newgif)) with (Z_to_bv 64 (SIGMA AS_cgif_raw_newgif)) in CALL;
apply CALL; clear CALL;
[ unfold spZ; rewrite Rsp; evalE AG; first [rewrite Z.add_mod by (clear - PBASE PBLO; lia) | rewrite Zminus_mod]; rewrite Hal32; reflexivity
| unfold raZ at 1; rewrite Rra, unsigned_lit_small by (clear - PBASE PBLO; lia); cbn [spine map fst snd]; fold (spine ch); apply HCTXR; exact Hctx
| rewrite Hfrs3; cbn [length]; clear - Hroom; lia
| exact (arodata_ok_journalP _ _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HROD)
| rewrite Ra0; cbn [sv_denot]; evalE AG
| split; [exists 1, fpos; split; [exact Hfin3 | split; [clear; lia | rewrite EFA3; fold F; split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult | change (fs_frame_bytes 1) with 128; clear; lia]]]
| split; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | exact HRA40]]
| exact Ocfg
| exact HBL
| exact Gwfn | exact Gctx | clear; lia | exact Gfile
| clear - Hpf4096; lia | exact HSINK | cbn [length]; unfold HDR_OUT, SINK_MAX; clear; lia
| intros _; split; [subst restX; right; exact Hpala_in | split; [exact Hpala | split; [cbv delta [sgct]; clear; lia | split; [exact HGPALA | cbv delta [sgct]; rewrite HGl; clear; lia]]]]
| exact HEVc | exact HLIVEc | exact HMOKc ]
| cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HPc & res & Hres & MLEc & HK4);
exists ly4, S4, regs4, mem4, md4; split; [rewrite Rra; reflexivity|]; split; [exact HJc|]; split; [exact HPc|]; exists res; split; [exact Hres | split; [exact MLEc | rewrite ?HspX in HK4; exact HK4]] ]
|
intros a Ha; apply in_asink_fp in Ha; destruct Ha as [Ha | Ha];
[ right; exists pf, FILE_BLOCK; split; [exact Hpf_in | split; [exact HnPF | change (req_size FILE_BLOCK) with 1264; unfold FILE_BLOCK in Ha; exact Ha]]
| left; exists sink_token; split; [left; reflexivity | exact Ha] ] ]
| ] end | st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdX) _ =>
eapply SRr_bind;
[ eapply (aj_callS SEGS B LAWS pa_segs_low W3 Ex ssX msX TNEWGIFX_STK (spZ regs) [sink_token] ly S W mem md [(1, fpos)] ly3 S3 mdX k
TRAWNEW_STK (asink_fp pf) EV_RAWNEW (-192) (ew Ex 2) (Z_to_bv 64 (BASE + 0x398)) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => exists res : Z, getr regs2 10 = w64 res /\
mo_le MT S3 S2 (mo_malloc MT RAW_SIZE) /\
((res = 0 /\ 256 < sgct /\ Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
asink_at SEGS K (mrestrict (w_H W2) mem2) md2 pf []) \/
(res <> 0 /\ sgct <= 256 /\
Permutation (ablocks B ly2 S2) ((res, RAW_SIZE) :: ablocks B ly3 S3) /\
(forall blc i, In (res, RAW_SIZE) blc -> 0 <= i < RAW_SIZE ->
awr_byte TRAWNEW_STK (spZ regs - 192) (asink_fp pf) (ablocks B ly3 S3) blc ly2 [] (res + i)) /\
aftok (asink_fp pf) (ablocks B ly3 S3) (res, RAW_SIZE) /\
obj_at SEGS (mrestrict (w_H W2) mem2) res LAY_Raw [(BASE + 0x614); g; pal0; ng_rattr attr; Wd; Hd; sgct; loops; R_PENDING] /\
asink_at SEGS K (mrestrict (w_H W2) mem2) md2 pf ([] ++ YO07.raw_header Wd Hd sgct GPAL (ng_rattr attr) loops)))) HS eq_refl HJ3);
[ rewrite Rsp; cbn [sv_denot]; reflexivity
| reflexivity
| evalE AG
| reflexivity
| clear; lia
| unfold TRAWNEW_STK, ASTACK; clear; lia
| rewrite FFS; unfold TRAWNEW_STK, ASTACK; clear; lia
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| apply ret_ok_codeptr_v; [clear; lia | reflexivity]
| rewrite unsigned_lit_small by (clear - PBASE PBLO; lia); clear - PBASE PBLO; lia
| unfold s0Z; rewrite Rs0; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
replace (spZ regs + -192) with (spZ regs - 192) by (clear - PBASE PBLO; lia); exact (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1)
| intros HPRE1; eapply SRr_mono;
[ pose proof (RAWNEWX ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch) (F + 32) g pal0 (ng_rattr attr) Wd Hd sgct loops 0 pf pala (3 * ngp) restX [] GPAL HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 (SIGMA AS_cgif_raw_newgif)) with (Z_to_bv 64 (SIGMA AS_cgif_raw_newgif)) in CALL;
apply CALL; clear CALL;
[ unfold spZ; rewrite Rsp; evalE AG; first [rewrite Z.add_mod by (clear - PBASE PBLO; lia) | rewrite Zminus_mod]; rewrite Hal32; reflexivity
| unfold raZ at 1; rewrite Rra, unsigned_lit_small by (clear - PBASE PBLO; lia); cbn [spine map fst snd]; fold (spine ch); apply HCTXR; exact Hctx
| rewrite Hfrs3; cbn [length]; clear - Hroom; lia
| exact (arodata_ok_journalP _ _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HROD)
| rewrite Ra0; cbn [sv_denot]; evalE AG
| split; [exists 1, fpos; split; [exact Hfin3 | split; [clear; lia | rewrite EFA3; fold F; split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult | change (fs_frame_bytes 1) with 128; clear; lia]]]
| split; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | exact HRA40]]
| exact Ocfg
| exact HBL
| exact Gwfn | exact Gctx | clear; lia | exact Gfile
| clear - Hpf4096; lia | exact HSINK | cbn [length]; unfold HDR_OUT, SINK_MAX; clear; lia
| intros _; split; [subst restX; right; exact Hpala_in | split; [exact Hpala | split; [cbv delta [sgct]; clear; lia | split; [exact HGPALA | cbv delta [sgct]; rewrite HGl; clear; lia]]]]
| exact HEVc | exact HLIVEc | exact HMOKc ]
| cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HPc & res & Hres & MLEc & HK4);
exists ly4, S4, regs4, mem4, md4; split; [rewrite Rra; reflexivity|]; split; [exact HJc|]; split; [exact HPc|]; exists res; split; [exact Hres | split; [exact MLEc | rewrite ?HspX in HK4; exact HK4]] ]
|
intros a Ha; apply in_asink_fp in Ha; destruct Ha as [Ha | Ha];
[ right; exists pf, FILE_BLOCK; split; [exact Hpf_in | split; [exact HnPF | change (req_size FILE_BLOCK) with 1264; unfold FILE_BLOCK in Ha; exact Ha]]
| left; exists sink_token; split; [left; reflexivity | exact Ha] ] ]
| ] end  end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & res & Ha04 & MLEc & Hres).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0 ZS5 HRA40.
pose proof (proj1 HJ4) as HAR4. aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (EFL4 : forall c p, flag_addr ly4 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA4 c p) as X; unfold frame_addr in X; lia).
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs4 & _). cbn [app] in Hfrs4.
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact HfinS3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR4 HfinS4) as (_ & _ & HCpres4 & _). rewrite EFA4 in HCpres4.
destruct Hres as [(Hres0 & Hsg256 & HPerm4 & HSINK4) | (Hresnz & Hsg & HPerm4 & Araw & Traw & Oraw & HSINK4)].
+
exact (@ng_P1X_B0 fx rc SK PI RO NP B TL LAWS ML ASF FFL TLF Rhw HGOT3 HU K AIL MT MLAW MLAWF XN HXN HXM ra_fc1 ra_fc2 AFCLOSE HUfc1 HUfc2 AFM AFREE4 ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 E W3 ly3 S3 ms3 md3 k fpos pf g pal HPRE Hal32 Hctx Hroom Htop32 HROD Hcfg HWH Hpala HPerm Hev Hlive HXE Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA EE E10 E32 Usp AG E33 E34 E35 E36 E37 E38 E39 E40 RF E528 E529 E41 HEI E42 E52 Rg Rp Hk3 Hfrs3 Eab3 Hg4096 Hp4096 Hpf4096 Tg Ag Tp Ap Tpf Apf MLE3 HW0 HH0 Ha4 Epala HGP HSNK0 HFD0 HAM0 HMOK HG0 HGl Hwx Hsegs HAR Hra Hra4 Hgp Htp Hstk Hpres Hch HQT Hal16 Hstk0 Hceil Hslo Hshi H47 Hbot Htop Htop2 C1 C2 C3 C4 C5 FFS HEV Hes Has Hf4096 Hfceil Hfhigh Hfhigh_img E241 E242 E244 E253 Hob241 Hob242 Hob244 Hob253 Huar Huar4 CV0 CR0 CV8 CR8 CV16 CR16 CV20 CR20 CV24 CR24 CV26 CR26 CV28 CR28 CV30 CR30 CV32 CR32 CV40 CR40 HcT Hrq1 Hrq2 HAR3 EFA3 EFL3 Hfin3 HfinS3 HFal HFhi HFpres3 HFSpres3 HFapp_img HF4096 HFceil HFhigh HFhigh_img HFq HF8 HF8lo HF8hi fl1 fl2 Efl HdFC Rngp Rpath Hpf_in Hpf16 Hpfceil Hp_ia Hg_in Hp_in Hp16 Hpceil Hph_ia Hppres3 Hph Hph_img HdPF HdPC Hg16 Hgceil Hgh_ia Hgpres3 Hgh Hgh_img HdGF HdGC HPermPG XF Hpal_ia HPermA Hpala_in Hpala3 Hpala4096 E10' w w0 w1 w2 w3 ms mat HEI0 HS SHOK HJ3 HSINK HGPAL Vwfn Vctx Vgct Vrat VW VH Vlp Vsg Ocfg HB79 Gwfn Gctx Gfile HEVc HLIVEc HBL HnPF HMOKc HGPALA Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0 HspX HLY3 Etop3 W4 Hwle4 ly4 S4 regs4 mem4 md4 HJ4 HJc HP4 res Ha04 MLEc Hres0 Hsg256 HPerm4 HSINK4 HAR4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4 EFA4 EFL4 Hfrs4 Hfin4 HfinS4 HFpres4 HFSpres4 HCpres4).
+
exact (@ng_P1X_B1 fx rc SK PI NP B LAWS ML ASF FFL Rhw K AIL MT MLAW MLAWF XN HXN ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 E W3 ly3 S3 ms3 md3 k fpos pf g pal HPRE Hal32 Hctx Hroom Htop32 HROD Hcfg HWH Hpala HPerm Hev Hlive HXE Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA EE E10 E32 Usp AG E33 E34 E35 E36 E37 E38 E39 E40 RF E528 E529 E41 HEI E42 E52 Rg Rp Hk3 Hfrs3 Eab3 Hg4096 Hp4096 Hpf4096 Tg Ag Tp Ap Tpf Apf MLE3 HW0 HH0 Ha4 Epala HGP HSNK0 HFD0 HAM0 HMOK HG0 HGl Hwx Hsegs HAR Hra Hra4 Hgp Htp Hstk Hpres Hch HQT Hal16 Hstk0 Hceil Hslo Hshi H47 Hbot Htop Htop2 C1 C2 C3 C4 C5 FFS HEV Hes Has Hf4096 Hfceil Hfhigh Hfhigh_img E241 E242 E244 E253 Hob241 Hob242 Hob244 Hob253 Huar Huar4 CV0 CR0 CV8 CR8 CV16 CR16 CV20 CR20 CV24 CR24 CV26 CR26 CV28 CR28 CV30 CR30 CV32 CR32 CV40 CR40 HcT Hrq1 Hrq2 HAR3 EFA3 EFL3 Hfin3 HfinS3 HFal HFhi HFpres3 HFSpres3 HFapp_img HF4096 HFceil HFhigh HFhigh_img HFq HF8 HF8lo HF8hi fl1 fl2 Efl HdFC Rngp Rpath Hpf_in Hpf16 Hpfceil Hp_ia Hg_in Hp_in Hp16 Hpceil Hph_ia Hppres3 Hph Hph_img HdPF HdPC Hg16 Hgceil Hgh_ia Hgpres3 Hgh Hgh_img HdGF HdGC HPermPG XF Hpal_ia HPermA Hpala_in Hpala3 Hpala4096 E10' w w0 w1 w2 w3 ms mat HEI0 HS SHOK HJ3 HSINK HGPAL Vwfn Vctx Vgct Vrat VW VH Vlp Vsg Ocfg HB79 Gwfn Gctx Gfile HEVc HLIVEc HBL HnPF HMOKc HGPALA Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0 HspX HLY3 Etop3 W4 Hwle4 ly4 S4 regs4 mem4 md4 HJ4 HJc HP4 res Ha04 MLEc Hresnz Hsg HPerm4 Araw Traw Oraw HSINK4 HAR4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4 EFA4 EFL4 Hfrs4 Hfin4 HfinS4 HFpres4 HFSpres4 HCpres4).
Qed.
End h. End f.
End d.
