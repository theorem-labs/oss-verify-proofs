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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8a ACjr ACk4 ACk5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YC5d YC7z YC7x YC21 YC85 YC86 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI17 YE02 YC5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACk0 ACk2 ACk3.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma ngG_land_low_mod : forall x m k, 0 <= k -> 0 <= m < 2 ^ k -> Z.land (x mod 2 ^ k) m = Z.land x m.
Proof.
intros x m k Hk Hm. rewrite <- (Z.land_ones x k) by lia. rewrite <- Z.land_assoc. f_equal.
rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Ltac ng_attr4_hc Hc E33 attr LM :=
rewrite branch_ne_U, U_and_lit in Hc by lia;
first [ lazymatch type of Hc with context [U ?Ex (SExt false 32 (SOff 33 0))] =>
rewrite (U_zext Ex 32 (SOff 33 0)), (U_atom Ex 33 attr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)) in Hc;
replace (U Ex (SLit 0)) with 0 in Hc by reflexivity;
change (Z.of_N 32) with 32 in Hc; rewrite (LM attr 4 32) in Hc by (first [lia | change (2 ^ 32) with 4294967296; lia]) end
| lazymatch type of Hc with context [U ?Ex (SOff 33 0)] =>
rewrite (U_atom Ex 33 attr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)) in Hc;
replace (U Ex (SLit 0)) with 0 in Hc by reflexivity end ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
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
Section e.
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
Lemma ng_GX : NG_P1_stmtX B K MT XN -> NG_G_stmtX B K MT XN.
Proof.
intros NGP1 ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 E W3 ly3 S3 ms3 md3 k fpos pf g pal HCTX HXE HCFG HE0 HEX E52 Rg Rp HNOW HW0 HH0 Ha4 Epala HS.
destruct HEX as [HE E42]. pose proof HXE as (HGP & HSNK0 & HFD0 & HAM0 & HMOK). destruct (HGP Ha4) as [HG0 HGl].
ng_facts HCTX HCFG HE0 HE.
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3 & Hg4096 & Hp4096 & Hpf4096 & Tg & Ag & Tp & Ap & Tpf & Apf & HSINK & MLE3).
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
pose proof (req_size_pos (3 * ngp) ltac:(clear - CR28; lia)) as [Hrq1 Hrq2].
rewrite Ha4 in HPerm. cbn [Z.eqb app] in HPerm.
assert (Hpala_in : In (pala, 3 * ngp) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity).
assert (HPerm3 : Permutation (ablocks B ly3 S3) ((pal, 3 * ngp) :: (g, 96) :: (pala, 3 * ngp) :: rest ++ [(pf, FILE_BLOCK)])).
{ rewrite Eab3, <- app_assoc. cbn [app]. apply Permutation_sym.
apply (Permutation_trans (perm_swap (g, 96) (pal, 3 * ngp) _)).
change ((g, 96) :: (pal, 3 * ngp) :: (pala, 3 * ngp) :: rest ++ [(pf, FILE_BLOCK)]) with ([(g, 96); (pal, 3 * ngp)] ++ (((pala, 3 * ngp) :: rest) ++ [(pf, FILE_BLOCK)])).
eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app; [apply Permutation_app; [apply Permutation_sym; exact HPerm | apply Permutation_refl] | apply Permutation_refl]. }
assert (Hp_in : In (pal, 3 * ngp) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; left; reflexivity).
assert (Hg_in : In (g, 96) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; left; reflexivity).
assert (Hpala3 : In (pala, 3 * ngp) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR3 Hg_in) as (Hg16 & _ & Hgceil & Hgh_ia & Hgpres3 & _). pose proof (proj1 Hgh_ia) as Hgh. change (req_size 96) with 96 in Hgceil, Hgpres3.
pose proof (blk_off_imgP _ _ _ _ _ _ g 96 HAR3 Hg_in) as Hgh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pal (3 * ngp) HAR3 Hp_in) as (Hp16 & _ & Hpceil & Hph_ia & Hppres3 & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR3 Hp_in) as Hph_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pala (3 * ngp) HAR3 Hpala3) as (_ & Hpala4096 & Hpalaceil & Hpalah_ia & Hpalapres3 & _). pose proof (proj1 Hpalah_ia) as Hpalah.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR3 Hpala3) as Hpalah_img.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ g 96 1 fpos HAR3 Hg_in Hfin3) as HdGF.
unfold zdisjoint in HdGF. cbn [fst snd] in HdGF. change (req_size 96) with 96 in HdGF. change (fs_frame_bytes 1) with 128 in HdGF. rewrite EFA3 in HdGF. fold F in HdGF.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ g 96 cid pos HAR3 Hg_in HfinS3) as HdGC.
unfold zdisjoint in HdGC. cbn [fst snd] in HdGC. change (req_size 96) with 96 in HdGC. rewrite EFA3 in HdGC.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pal (3 * ngp) 1 fpos HAR3 Hp_in Hfin3) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA3 in HdPF. fold F in HdPF.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pal (3 * ngp) cid pos HAR3 Hp_in HfinS3) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. rewrite EFA3 in HdPC.
pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 _ _ _ (pal, 3 * ngp) (g, 96) _ HAR3 HPerm3) as HdPG.
unfold zdisjoint, block_rng in HdPG. cbn [fst snd] in HdPG. change (req_size 96) with 96 in HdPG.
pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 _ _ _ (pal, 3 * ngp) (pala, 3 * ngp) _ HAR3 (Permutation_trans HPerm3 (perm_skip _ (perm_swap _ _ _)))) as HdPP.
unfold zdisjoint, block_rng in HdPP. cbn [fst snd] in HdPP.
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ pf FILE_BLOCK g 96 HAR3 Hpf_in Hg_in ltac:(unfold FILE_BLOCK; intros X; injection X; lia)) as HdXG.
unfold zdisjoint in HdXG. cbn [fst snd] in HdXG. change (req_size FILE_BLOCK) with 1264 in HdXG.
change (req_size 96) with 96 in HdXG.
pose proof (sep_blocks SEGS B LAWS ly3 S3 _ _ _ pf FILE_BLOCK pal (3 * ngp) HAR3 Hpf_in Hp_in ltac:(unfold FILE_BLOCK; intros X; injection X; clear; lia)) as HdXP.
unfold zdisjoint in HdXP. cbn [fst snd] in HdXP. change (req_size FILE_BLOCK) with 1264 in HdXP.
pose proof Hgh_img as HGoffX. unfold off_img in HGoffX. change (req_size 96) with 96 in HGoffX. pose proof Hph_img as HPoffX. unfold off_img in HPoffX.
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (P /\ ((pf + 1264 <= g \/ g + 96 <= pf) /\ 4096 <= g /\ g + 96 <= alloc_ceiling /\ (g + 96 <= 65536 \/ 6270976 <= g)) /\
(pf + 1264 <= pal \/ pal + req_size (3 * ngp) <= pf) /\ 4096 <= pal /\ pal + req_size (3 * ngp) <= alloc_ceiling /\
(pal + req_size (3 * ngp) <= 65536 \/ 6270976 <= pal) /\ 3 * ngp <= req_size (3 * ngp) /\
(pal + req_size (3 * ngp) <= F \/ F + 128 <= pal) /\ (pal + req_size (3 * ngp) <= g \/ g + 96 <= pal)))
by (apply xfacts_i; split; [exact XF | clear - HdXG HdXP Hg4096 Hgceil HGoffX Hp4096 Hpceil HPoffX Hrq2 HdPF HdPG; lia]);
clear XF HGoffX HPoffX HdXG HdXP; rename XF2 into XF end.
pose proof Hph_ia as Hpal_ia. change (in_app pal (req_size (3 * ngp))) with (xfacts (in_app pal (req_size (3 * ngp)))) in Hpal_ia.
nbox_seps.
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
reshok_bx HS 35%nat.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK NBspan.
all: try (slim; obl_blk HJ3 Rg E35 Hg_in).
all: try (slim; oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
xsink_stretch HFr HSINK. clear_frames.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
change (Z_to_bv 64 333176) with (Z_to_bv 64 (SIGMA AS_asan_memcpy)).
assert (Qps : pala + 3 * ngp <= spZ regs - 192 - ESTACK) by (unfold ESTACK; clear - Hpalaceil Hrq2 Hslo Hceil FFS; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pala (3 * ngp) (proj1 HJ3) Hpala3) as (_ & _ & _ & _ & HpalapresX & _).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AMEMCPY _ (ms_regs msX) (ms_mem msX) TNEWGIFX_STK (spZ regs) [sink_token] ly S W mem md [(1, fpos)]
ly3 S3 _ _ pal pala (3 * ngp) (-192) (Z_to_bv 64 (BASE + 0x2d0)) HJ3) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rp. reflexivity.
- rewrite Ra1. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 32%nat) by lia. rewrite E32, Epala. reflexivity.
- rewrite Ra2. lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
transitivity (sv_denot Ex (SMd M_MUL (SOff 38 0) (SLit 3)));
[ cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_mul3 Ex 38 ngp ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38) ltac:(clear - CR28; lia)) ] | st_ok _ ?Ex _ _ =>
transitivity (sv_denot Ex (SMd M_MUL (SOff 38 0) (SLit 3)));
[ cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_mul3 Ex 38 ngp ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38) ltac:(clear - CR28; lia)) ]  end.
- clear - CR28; lia. - clear - Hp4096; lia. - clear - Hpceil Hrq2 C1; lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- intros a Ha. split; [replace a with (pal + (a - pal)) by lia; apply Ap; [exact Hp_in | clear - Ha Hrq2; lia] | unfold ESTACK; clear - Ha Hpceil Hrq2 Hslo Hceil FFS; lia].
- apply (amem_range_of_block SEGS B LAWS ly3 S3 _ _ _ pal (3 * ngp) _ _ (proj1 HJ3) Hp_in); clear - Hrq2; lia.
- apply (range_addressable_of_block SEGS B LAWS ly3 S3 _ _ _ pal (3 * ngp) _ _ (proj1 HJ3) Hp_in); clear - Hrq2; lia.
- intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 _ _ _ pal (3 * ngp) _ _ (proj1 HJ3) Hp_in); clear - Hrq2 Hn0; lia.
- split; [clear - Hpala4096; lia|]. split; [clear - Hpalaceil Hrq2 C1; lia|]. split.
{ intros a Ha. split; [| unfold spZ; rewrite Rsp; evalE AG].
apply (aview_some_of_apresent SEGS). apply (proj1 (HpalapresX a ltac:(clear - Ha Hrq2; lia))). }
split; [nunbox HdPP; clear - HdPP Hrq2; lia|].
split; [apply (amem_range_of_block SEGS B LAWS ly3 S3 _ _ _ pala (3 * ngp) _ _ (proj1 HJ3) Hpala3); clear - Hrq2; lia|]. split.
+ apply (range_addressable_of_block SEGS B LAWS ly3 S3 _ _ _ pala (3 * ngp) _ _ (proj1 HJ3) Hpala3); clear - Hrq2; lia.
+ intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 _ _ _ pala (3 * ngp) _ _ (proj1 HJ3) Hpala3); clear - Hrq2 Hn0; lia. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & HSM4).
xsink_intrin Hfr4 HSM4 HSINK. clear HSM4.
assert (HGPAL : garr8 SEGS (mrestrict (w_H W3) mem4) pal GPAL).
{ lazymatch type of Heff with forall i, _ -> aview _ _ _ _ = aview _ _ ?memT _ =>
apply (garr8_aview SEGS (w_H W3) (w_H W3) memT mem4 pala pal GPAL);
[ intros i Hi; apply Heff; rewrite HGl in Hi; exact Hi
| apply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pala (3 * ngp) pala GPAL HJ3 Hpala_in Hpala3);
[ clear; lia | rewrite HGl; clear - Hrq2; lia
| intros a Ha Hn; apply inFP_token in Hn; clear - Ha Hn Hpala4096; lia | exact HG0 ] ] end. }
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
nunbox HdPG. nunbox HdPF. nunbox HdPC.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptI Hfr4 Hpres4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
nbox HdPG. nbox HdPF. nbox HdPC.
reshok_bx HS 35%nat. clear_frames.
clear E10'. lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => assert (E10' : ew Ex 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10) | st_ok _ ?Ex _ _ => assert (E10' : ew Ex 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10)  end.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ4 SHOK NBspan 0x324.
all: try (slim; oblFX HJ4 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
xsink_stretch HFr HSINK. xgarr_stretch HFr HGPAL. clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK NBspan.
1: { exfalso. ng_attr4_hc Hc E33 attr ngG_land_low_mod. rewrite Ha4 in Hc. cbn in Hc. discriminate Hc. }
clear Hc.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ4 SHOK NBspan 0x324.
all: try (slim; oblFX HJ4 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
xsink_stretch HFr HSINK. xgarr_stretch HFr HGPAL. clear_frames.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NP1X in HS;
eapply (NGP1 ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 Ev W3 ly3 S3 msv _ k fpos pf g pal);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [rewrite Ha4; cbn [Z.eqb app]; exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| exact HXE
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [split; [intros n Hn; rewrite !ew_ewset_other by lia; apply AG; exact Hn | repeat split; rewrite ?ew_ewset_other by lia; first [assumption | hei_prove]] | rewrite ?ew_ewset_other by lia; exact E42]
| rewrite ?ew_ewset_other by lia; exact E52
| rewrite !ew_ewset_other by lia; exact Rg | rewrite !ew_ewset_other by lia; exact Rp
| split; [exact HJ4 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hg4096 | split; [exact Hp4096 | split; [exact Hpf4096 | split; [exact Tg | split; [exact Ag | split; [exact Tp | split; [exact Ap | split; [exact Tpf | split; [exact Apf | split; [exact HSINK | exact MLE3]]]]]]]]]]]]]]
| exact HW0 | exact HH0 | exact Ha4 | exact Epala
| exact HGPAL
| exact HS ] | st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NP1X in HS;
eapply (NGP1 ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 Ev W3 ly3 S3 msv _ k fpos pf g pal);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [rewrite Ha4; cbn [Z.eqb app]; exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| exact HXE
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [split; [intros n Hn; rewrite !ew_ewset_other by lia; apply AG; exact Hn | repeat split; rewrite ?ew_ewset_other by lia; first [assumption | hei_prove]] | rewrite ?ew_ewset_other by lia; exact E42]
| rewrite ?ew_ewset_other by lia; exact E52
| rewrite !ew_ewset_other by lia; exact Rg | rewrite !ew_ewset_other by lia; exact Rp
| split; [exact HJ4 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hg4096 | split; [exact Hp4096 | split; [exact Hpf4096 | split; [exact Tg | split; [exact Ag | split; [exact Tp | split; [exact Ap | split; [exact Tpf | split; [exact Apf | split; [exact HSINK | exact MLE3]]]]]]]]]]]]]]
| exact HW0 | exact HH0 | exact Ha4 | exact Epala
| exact HGPAL
| exact HS ]  end.
exact Hctx.
Qed.
End e. End d.
End b.
