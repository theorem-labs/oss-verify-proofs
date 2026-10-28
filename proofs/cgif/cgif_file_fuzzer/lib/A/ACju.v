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
Lemma ngK_land_low_mod : forall x m k, 0 <= k -> 0 <= m < 2 ^ k -> Z.land (x mod 2 ^ k) m = Z.land x m.
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
Lemma ng_KX : NG_P0_stmtX B K MT XN -> NG_G_stmtX B K MT XN -> NG_K_stmtX B K MT XN.
Proof.
intros NGP0 NGG ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 E W3 ly3 S3 ms3 md3 k fpos pf g HCTX HXE HCFG HE0 HEX E52 Rg HNOW HW0 HH0 HS.
destruct HEX as [HE E42]. pose proof HXE as (HGP & HSNK0 & HFD0 & HAM0 & HMOK).
ng_facts HCTX HCFG HE0 HE.
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3 & Hg4096 & Hpf4096 & Tg & Ag & Tpf & Apf & HSINK & MLE3).
ng_frame HJ3 Hfrs3.
assert (Rngp : 0 <= ngp <= 65535) by (clear - CR28; lia).
assert (Rpath : 0x10000 <= ak_path K < 0x5fb000).
{ apply (pa_img_range (ak_path K)). apply (proj1 (ail_env _ _ _ AIL (ak_path K) ltac:(unfold aenv_addr; right; right; right; left; lia))). }
assert (Hpf_in : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
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
assert (Hg_in : In (g, 96) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR3 Hg_in) as (Hg16 & _ & Hgceil & Hgh_ia & Hgpres3 & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g 96 HAR3 Hg_in) as Hgh_img.
change (req_size 96) with 96 in Hgceil, Hgpres3, Hgh_img.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ g 96 1 fpos HAR3 Hg_in Hfin3) as HdGF.
unfold zdisjoint in HdGF. cbn [fst snd] in HdGF. change (req_size 96) with 96 in HdGF. change (fs_frame_bytes 1) with 128 in HdGF. rewrite EFA3 in HdGF. fold F in HdGF.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ g 96 cid pos HAR3 Hg_in HfinS3) as HdGC.
unfold zdisjoint in HdGC. cbn [fst snd] in HdGC. change (req_size 96) with 96 in HdGC. rewrite EFA3 in HdGC.
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ pf FILE_BLOCK g 96 HAR3 Hpf_in Hg_in ltac:(unfold FILE_BLOCK; intros X; injection X; lia)) as HdXG.
unfold zdisjoint in HdXG. cbn [fst snd] in HdXG. change (req_size FILE_BLOCK) with 1264 in HdXG.
change (req_size 96) with 96 in HdXG. pose proof Hgh_img as HGoffX. unfold off_img in HGoffX.
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (P /\ (pf + 1264 <= g \/ g + 96 <= pf) /\ 4096 <= g /\ g + 96 <= alloc_ceiling /\ (g + 96 <= 65536 \/ 6270976 <= g)))
by (apply xfacts_i; split; [exact XF | clear - HdXG Hg4096 Hgceil HGoffX; lia]); clear XF HGoffX HdXG; rename XF2 into XF end.
nbox_seps.
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
reshok_bx HS 35%nat.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK NBspan; [slim; oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | slim; awrR AG fpos F EFA3 |]. xsink_stretch HFr HSINK. clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK NBspan.
-
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK NBspan 0x324.
all: try (slim; oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
xsink_stretch HFr HSINK. clear_frames.
rewrite branch_ne_U, U_and_lit in Hc by lia.
lazymatch type of Hc with context [U ?Ex (SExt false 8 (SOff 33 0))] =>
rewrite (U_zext Ex 8 (SOff 33 0)), (U_atom Ex 33 attr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)) in Hc;
replace (U Ex (SLit 0)) with 0 in Hc by reflexivity end.
change (Z.of_N 8) with 8 in Hc. rewrite (ngK_land_low_mod attr 4 8) in Hc by (first [lia | change (2 ^ 8) with 256; lia]).
assert (Ha4 : Z.land attr 4 <> 0) by (intros Hz; rewrite Hz in Hc; cbn in Hc; discriminate Hc).
clear Hc.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK NBspan.
2: { exfalso. ng_attr4_hc Hc E33 attr ngK_land_low_mod. destruct (Z.eqb_spec (Z.land attr 4) 0) as [Hz|Hz]; [exact (Ha4 Hz) | cbn in Hc; discriminate Hc]. }
clear Hc.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK NBspan 0x324.
all: try (slim; oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
xsink_stretch HFr HSINK. clear_frames.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NP0X in HS;
eapply (NGP0 ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 Ev W3 ly3 S3 msv _ k fpos pf g);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| exact HXE
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [split; [intros n Hn; rewrite !ew_ewset_other by lia; apply AG; exact Hn | repeat split; rewrite ?ew_ewset_other by lia; first [assumption | hei_prove]] | rewrite ?ew_ewset_other by lia; exact E42]
| rewrite ?ew_ewset_other by lia; exact E52
| rewrite !ew_ewset_other by lia; exact Rg
| split; [exact HJ3 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hg4096 | split; [exact Hpf4096 | split; [exact Tg | split; [exact Ag | split; [exact Tpf | split; [exact Apf | split; [exact HSINK | exact MLE3]]]]]]]]]]]
| exact HW0 | exact HH0 | exact Ha4
| exact HS ] | st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NP0X in HS;
eapply (NGP0 ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 Ev W3 ly3 S3 msv _ k fpos pf g);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| exact HXE
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [split; [intros n Hn; rewrite !ew_ewset_other by lia; apply AG; exact Hn | repeat split; rewrite ?ew_ewset_other by lia; first [assumption | hei_prove]] | rewrite ?ew_ewset_other by lia; exact E42]
| rewrite ?ew_ewset_other by lia; exact E52
| rewrite !ew_ewset_other by lia; exact Rg
| split; [exact HJ3 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hg4096 | split; [exact Hpf4096 | split; [exact Tg | split; [exact Ag | split; [exact Tpf | split; [exact Apf | split; [exact HSINK | exact MLE3]]]]]]]]]]]
| exact HW0 | exact HH0 | exact Ha4
| exact HS ]  end.
exact Hctx.
-
rewrite branch_ne_U, U_and_lit in Hc by lia.
lazymatch type of Hc with context [U ?Ex (SExt false 8 (SOff 33 0))] =>
rewrite (U_zext Ex 8 (SOff 33 0)), (U_atom Ex 33 attr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)) in Hc;
replace (U Ex (SLit 0)) with 0 in Hc by reflexivity end.
change (Z.of_N 8) with 8 in Hc. rewrite (ngK_land_low_mod attr 4 8) in Hc by (first [lia | change (2 ^ 8) with 256; lia]).
assert (Ha4 : Z.land attr 4 = 0) by (destruct (Z.eqb_spec (Z.land attr 4) 0) as [Hz|Hz]; [exact Hz | cbn in Hc; discriminate Hc]). clear Hc.
rewrite Ha4 in HPerm. cbn [Z.eqb app] in HPerm.
assert (Hpala_in : In (pala, 3 * ngp) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pala (3 * ngp) HAR Hpala_in) as (_ & Hpala4096 & Hpalaceil & _ & _ & _).
pose proof (req_size_pos (3 * ngp) ltac:(clear - CR28; lia)) as [Hrq1 Hrq2].
assert (Epala : pala = pal0).
{ apply (f_equal bv_unsigned) in Hpala. rewrite !unsigned_lit_small in Hpala by lia. exact Hpala. }
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK NBspan; [slim; oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | slim; awrR AG fpos F EFA3 |]. xsink_stretch HFr HSINK. clear_frames.
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 KgotB KcellB KguarB KuarB VgrB.
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
assert (Qceil : alloc_ceiling <= spZ regs) by lia. assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
assert (Qtop : spZ regs < ly_top ly - 16) by lia. assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia. assert (Qsp : spZ regs - 192 + 16 <= spZ regs) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msX) a = aview SEGS (w_H W) mem a)
by (intros a Ha; pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia]) | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msX) a = aview SEGS (w_H W) mem a)
by (intros a Ha; pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia])  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp)
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp)
| ]  end.
pmkst HS.
ppcs.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (amalloc04_sub SEGS B LAWS Hsegs MT AMALLOC4 _ (ms_regs msX) (ms_mem msX) TNEWGIFX_STK (spZ regs) [sink_token] ly S W mem md [(1, fpos)]
ly3 S3 _ k (3 * ngp) (-192) (Z_to_bv 64 (BASE + 0x284)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- rewrite Ra0. lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
transitivity (sv_denot Ex (SMd M_MUL (SOff 38 0) (SLit 3)));
[ cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_mul3 Ex 38 ngp ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38) ltac:(clear - CR28; lia)) ] | st_ok _ ?Ex _ _ =>
transitivity (sv_denot Ex (SMd M_MUL (SOff 38 0) (SLit 3)));
[ cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_mul3 Ex 38 ngp ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38) ltac:(clear - CR28; lia)) ]  end.
- rewrite HMM. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, !bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. unfold LIVE_NEWGIF, LIVE_MAX, FILE_BLOCK in *. lia.
- unfold spZ. rewrite Rsp. evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _). rewrite HEV in Hev. unfold EV_MAX in *. lia.
- pose proof (proj1 (proj2 HJ3)) as HLY3. pose proof HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
apply (achain_chain_pre ly3 _ (spZ regs - 192) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; evalE AG
| unfold s0Z; rewrite Rs0; evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia.
apply (HU _ _ Hctx); cbn [ng_traces In]; repeat (first [left; reflexivity | right]).
-
apply (mok_station MT S S3 (xm_newgif XN ngp) (ng_macc2 MT) _ MLAW HMOK MLE3); [apply (mo_malloc_nonneg MT MLAW); clear - Rngp; lia|].
pose proof (HXM ngp Rngp) as Hx. unfold ng_msum, ng_macc3 in Hx.
pose proof (mo_malloc_nonneg MT MLAW RAW_SIZE ltac:(unfold RAW_SIZE; lia)) as M4.
pose proof (mo_free_nonneg MT MLAW) as M5. clear - Hx M4 M5. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & pal & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hp4096 & Eab4 & HK4 & MLE4 & HJt4).
assert (Hpf_in4 : In (pf, FILE_BLOCK) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hpf_in).
xsink_sub HJt4 HSINK Hpf_in Hpf_in4. clear HJt4.
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
unfold ASTACK in HK4. replace (spZ regs + -192 - 16384) with (spZ regs - 16576) in HK4 by lia. replace (spZ regs + -192) with (spZ regs - 192) in HK4 by lia.
pose proof (proj1 HJ4) as HAR4. aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (EFL4 : forall c p, flag_addr ly4 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA4 c p) as X; unfold frame_addr in X; lia).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact HfinS3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
idtac.
assert (Hp_in : In (pal, 3 * ngp) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
assert (Hg_in4 : In (g, 96) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hg_in).
assert (Hpala4 : In (pala, 3 * ngp) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; rewrite Eab3; apply in_app_iff; left; apply in_app_iff; left; exact Hpala_in).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pal (3 * ngp) HAR4 Hp_in) as (Hp16 & _ & Hpceil & Hph_ia & Hppres4 & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR4 Hp_in) as Hph_img.
pose proof (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal (3 * ngp) HJ3 HAR4 ltac:(rewrite Eab4; reflexivity) ltac:(lia)) as Tp.
assert (Ap : forall blc lyq ownq i, In (pal, 3 * ngp) blc -> 0 <= i < req_size (3 * ngp) -> awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc lyq ownq (pal + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal (3 * ngp) blc i lyq ownq HJ3 HAR4 ltac:(rewrite Eab4; reflexivity) ltac:(lia) Hbl Hi). }
pose proof (sep_block_frame SEGS B LAWS ly4 S4 _ _ _ pal (3 * ngp) 1 fpos HAR4 Hp_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
pose proof (sep_block_frame SEGS B LAWS ly4 S4 _ _ _ pal (3 * ngp) cid pos HAR4 Hp_in HfinS4) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. rewrite EFA4 in HdPC.
assert (HPerm4 : Permutation (ablocks B ly4 S4) ((pal, 3 * ngp) :: (g, 96) :: (ablocks B ly S ++ [(pf, FILE_BLOCK)]))).
{ rewrite Eab4, Eab3, <- app_assoc. cbn [app]. apply Permutation_sym.
apply (Permutation_trans (perm_swap (g, 96) (pal, 3 * ngp) (ablocks B ly S ++ [(pf, FILE_BLOCK)]))).
change ((g, 96) :: (pal, 3 * ngp) :: (ablocks B ly S ++ [(pf, FILE_BLOCK)])) with ([(g, 96); (pal, 3 * ngp)] ++ (ablocks B ly S ++ [(pf, FILE_BLOCK)])). apply Permutation_app_comm. }
pose proof (sep_blocks_perm SEGS B LAWS ly4 S4 _ _ _ (pal, 3 * ngp) (g, 96) _ HAR4 HPerm4) as HdPG.
unfold zdisjoint, block_rng in HdPG. cbn [fst snd] in HdPG. change (req_size 96) with 96 in HdPG.
assert (HErF : forall a, F <= a < F + 128 -> ~ (pal <= a < pal + req_size (3 * ngp))) by (intros a Ha; clear - Ha HdPF; lia).
pose proof (sep_blocks SEGS B LAWS ly4 S4 _ _ _ pf FILE_BLOCK pal (3 * ngp) HAR4 Hpf_in4 Hp_in ltac:(unfold FILE_BLOCK; intros X; injection X; clear; lia)) as HdPP.
unfold zdisjoint in HdPP. cbn [fst snd] in HdPP. change (req_size FILE_BLOCK) with 1264 in HdPP.
pose proof Hph_img as HPoffX. unfold off_img in HPoffX.
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (P /\ (pf + 1264 <= pal \/ pal + req_size (3 * ngp) <= pf) /\ 4096 <= pal /\ pal + req_size (3 * ngp) <= alloc_ceiling /\ (pal + req_size (3 * ngp) <= 65536 \/ 6270976 <= pal) /\ 3 * ngp <= req_size (3 * ngp)))
by (apply xfacts_i; split; [exact XF | clear - HdPP Hp4096 Hpceil HPoffX Hrq2; lia]); clear XF HPoffX HdPP; rename XF2 into XF end.
nbox HdPF. nbox HdPG.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptR HK4 HJ4 AG Usp E10 E32 HfinS3 I KgotB Kgot4 KcellB Kcell4 KguarB Kguar4 KuarB Kuar4 VgrB Vgr4 EFA3
| keptF HK4 AG RF E529 Hfin3 HFpres4 HFSpres4 HErF F EFA3
| eapply (region_kept_block_ajw2 SEGS _ LAWS); [exact HK4 | exact HAR4 | exact Hg_in4
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg; apply unsigned_lit_small; lia
| exact Hg_in | lia | change (req_size 96) with 96; lia | lia | lia | intros a Ha Hn; clear - Ha Hn HdPG; nunbox HdPG; lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
nbox HdPC.
prreg HS (10%bv : bv 5) Rp. cbn [ms_regs] in Rp. rewrite Ha04 in Rp. symmetry in Rp. unfold w64 in Rp.
lazymatch type of Rp with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rp, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NG1X in HS;
eapply (NGG ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 Ev W4 ly4 S4 msv _ (k + 1) fpos pf g pal);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [rewrite Ha4; cbn [Z.eqb app]; exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| exact HXE
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [split; [exact AG | repeat (split; [eassumption|]); eassumption] | exact E42]
| exact E52
| exact Rg | exact Rp
| split; [exact HJ4 | split; [clear - Hk3; lia | split; [rewrite Hfrs4; exact Hfrs3 | split; [rewrite Eab4, Eab3; reflexivity | split; [exact Hg4096 | split; [exact Hp4096 | split; [exact Hpf4096 | split; [exact Tg | split; [exact Ag | split; [exact Tp | split; [exact Ap | split; [exact Tpf | split; [exact Apf | split; [exact HSINK |]]]]]]]]]]]]]]
| exact HW0 | exact HH0 | exact Ha4 | exact Epala
| exact HS ] | st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NG1X in HS;
eapply (NGG ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 Ev W4 ly4 S4 msv _ (k + 1) fpos pf g pal);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [rewrite Ha4; cbn [Z.eqb app]; exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| exact HXE
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [split; [exact AG | repeat (split; [eassumption|]); eassumption] | exact E42]
| exact E52
| exact Rg | exact Rp
| split; [exact HJ4 | split; [clear - Hk3; lia | split; [rewrite Hfrs4; exact Hfrs3 | split; [rewrite Eab4, Eab3; reflexivity | split; [exact Hg4096 | split; [exact Hp4096 | split; [exact Hpf4096 | split; [exact Tg | split; [exact Ag | split; [exact Tp | split; [exact Ap | split; [exact Tpf | split; [exact Apf | split; [exact HSINK |]]]]]]]]]]]]]]
| exact HW0 | exact HH0 | exact Ha4 | exact Epala
| exact HS ]  end.
{ exact Hctx. }
{   unfold ng_macc3. exact (mle_station MT S S3 S4 _ _ MLAW MLE3 MLE4). }
Qed.
End e. End d.
End b.
