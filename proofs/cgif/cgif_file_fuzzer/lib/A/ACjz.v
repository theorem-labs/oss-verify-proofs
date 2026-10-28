(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Utf8.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
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
Section j.
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
Lemma ng_P1X_B1 :
forall (ly : alayout),
forall (S : astate),
forall (W : world SEGS),
forall (regs : bvmap 5 word),
forall (mem : word → option byte),
forall (md : Model),
forall (ch : list (Z * Z * Z)),
forall (cfgp pal0 pala attr gen Wd Hd ngp loops aM : Z),
forall (rest : list (Z * Z)),
forall (GPAL : list Z),
forall (cid pos : Z),
forall (E0 E : env),
forall (W3 : world SEGS),
forall (ly3 : alayout),
forall (S3 : astate),
forall (ms3 : machine_state),
forall (md3 : Model),
forall (k fpos pf g pal : Z),
forall (HPRE : afn_pre SEGS B TNEWGIFX_STK ly S W regs mem md ch),
forall (Hal32 : spZ regs mod 32 = 0),
forall (Hctx : In (raZ regs :: spine ch) CTX),
forall (Hroom : Z.of_nat (length (frames S)) <= 7),
forall (Htop32 : spZ regs + 32 <= ly_top ly),
forall (HROD : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem)),
forall (Hcfg : obj_at SEGS (mrestrict (w_H W) mem) cfgp LAY_Config [pal0; ak_path K; attr; gen; Wd; Hd; ngp; loops; hw; 0]),
forall (HWH : Wd * Hd <= 100000000),
forall (Hpala : Z_to_bv 64 pala = Z_to_bv 64 pal0),
forall (HPerm : Permutation (ablocks B ly S) ((if Z.land attr 4 =? 0 then [(pala, 3 * ngp)] else []) ++ rest)),
forall (Hev : st_nev S + EV_NEWGIF <= EV_MAX),
forall (Hlive : blocks_bytes S + LIVE_NEWGIF <= LIVE_MAX),
forall (HXE : ng_xent B K MT XN ly S W mem md pala attr ngp aM GPAL),
forall (Hfin : In (cid, pos) (frames S)),
forall (Hcid0 : 0 <= cid),
forall (Hfal : frame_addr ly cid pos mod 8 = 0),
forall (Hflo : frame_addr ly cid pos <= cfgp),
forall (Hfhi : cfgp + 48 <= frame_addr ly cid pos + fs_frame_bytes cid),
forall (Hcal : cfgp mod 8 = 0),
forall (HRA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF cfgp 48),
forall (EE : ∀ (n : nat) (r : Prelude.reg), Z.of_nat n = bv_unsigned r → ew E0 n = getr regs r),
forall (E10 : ew E0 10 = Z_to_bv 64 cfgp),
forall (E32 : ew E0 32 = Z_to_bv 64 pal0),
forall (Usp : bv_unsigned (ew E0 2) = spZ regs),
forall (AG : ∀ n : nat, (n < 33)%nat → ew E n = ew E0 n),
forall (E33 : ew E 33 = Z_to_bv 64 attr),
forall (E34 : ew E 34 = Z_to_bv 64 gen),
forall (E35 : ew E 35 = Z_to_bv 64 SB),
forall (E36 : ew E 36 = Z_to_bv 64 Wd),
forall (E37 : ew E 37 = Z_to_bv 64 Hd),
forall (E38 : ew E 38 = Z_to_bv 64 ngp),
forall (E39 : ew E 39 = Z_to_bv 64 loops),
forall (E40 : ew E 40 = Z_to_bv 64 0),
let F : Z := frame_addr ly 1 fpos in
forall (RF : ew E 516 = Z_to_bv 64 F),
let FL : Z := flag_addr ly 1 fpos in
forall (E528 : ew E 528 = Z_to_bv 64 FL),
forall (E529 : ew E 529 = Z_to_bv 64 (SB + F / 8)),
forall (E41 : ew E 41 = Z_to_bv 64 (as_uar_cell B)),
forall (HEI : img_env VAL A_LIM E),
forall (E42 : ew E 42 = Z_to_bv 64 (ak_path K)),
forall (E52 : ew E 52 = Z_to_bv 64 pf),
forall (Rg : ew E 550 = Z_to_bv 64 g),
forall (Rp : ew E 599 = Z_to_bv 64 pal),
forall (Hk3 : k <= 3),
forall (Hfrs3 : frames S3 = (1, fpos) :: frames S),
forall (Eab3 : ablocks B ly3 S3 = ((ablocks B ly S ++ [(pf, FILE_BLOCK)]) ++ [(g, 96)]) ++ [(pal, 3 * ngp)]),
forall (Hg4096 : 4096 <= g),
forall (Hp4096 : 4096 <= pal),
forall (Hpf4096 : 4096 <= pf),
forall (Tg : aftok [sink_token] (ablocks B ly S) (g, 96)),
forall (Ag : ∀ (blc : list (Z * Z)) (lyq : alayout) (ownq : list (Z * Z)) (i : Z), In (g, 96) blc → 0 <= i < 96 → awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc lyq ownq (g + i)),
forall (Tp : aftok [sink_token] (ablocks B ly S) (pal, 3 * ngp)),
forall (Ap : ∀ (blc : list (Z * Z)) (lyq : alayout) (ownq : list (Z * Z)) (i : Z), In (pal, 3 * ngp) blc → 0 <= i < req_size (3 * ngp) → awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc lyq ownq (pal + i)),
forall (Tpf : aftok [sink_token] (ablocks B ly S) (pf, FILE_BLOCK)),
forall (Apf : ∀ (blc : list (Z * Z)) (lyq : alayout) (ownq : list (Z * Z)) (i : Z), In (pf, FILE_BLOCK) blc → 0 <= i < req_size FILE_BLOCK → awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc lyq ownq (pf + i)),
forall (MLE3 : mo_le MT S S3 (ng_macc3 MT ngp)),
forall (HW0 : Wd ≠ 0),
forall (HH0 : Hd ≠ 0),
forall (Ha4 : Z.land attr 4 = 0),
forall (Epala : pala = pal0),
forall (HGP : Z.land attr 4 = 0 → garr8 SEGS (mrestrict (w_H W) mem) pala GPAL ∧ Z.of_nat (length GPAL) = 3 * ngp),
forall (HSNK0 : asink_none SEGS K (mrestrict (w_H W) mem) md),
forall (HFD0 : fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None),
forall (HAM0 : ameta_inv SEGS K ly (mrestrict (w_H W) mem) aM),
forall (HMOK : mo_ok MT S (xm_newgif XN ngp)),
forall (HG0 : garr8 SEGS (mrestrict (w_H W) mem) pala GPAL),
forall (HGl : Z.of_nat (length GPAL) = 3 * ngp),
forall (Hwx : wx_segs_nowrap SEGS),
forall (Hsegs : ∀ a : Z, in_img SEGS a → 0 <= a < kLowMemEnd),
forall (HAR : AR SEGS B ly S W mem md),
forall (Hra : ret_ok (getr regs 1)),
forall (Hra4 : 4096 <= raZ regs),
forall (Hgp : getr regs 3 = w64 (as_gp B)),
forall (Htp : getr regs 4 = w64 (as_tp B)),
forall (Hstk : astk_ok TNEWGIFX_STK ly (spZ regs)),
forall (Hpres : ∀ a : Z, spZ regs - TNEWGIFX_STK <= a < spZ regs → apresent (w_H W) mem a),
forall (Hch : achain ly (aview SEGS (w_H W) mem) (spZ regs) (s0Z regs) ch),
forall (HQT : qtight S),
forall (Hal16 : spZ regs mod 16 = 0),
forall (Hstk0 : 0 <= TNEWGIFX_STK),
forall (Hceil : alloc_ceiling <= ly_stk_lo ly),
forall (Hslo : ly_stk_lo ly + TNEWGIFX_STK <= spZ regs),
forall (Hshi : spZ regs <= ly_stk_hi ly),
forall (H47 : ly_stk_hi ly <= 2 ^ 47),
forall (Hbot : ly_bot ly + TNEWGIFX_STK < spZ regs + ASTACK),
forall (Htop : spZ regs <= ly_top ly),
forall (Htop2 : ly_top ly <= ly_stk_hi ly),
forall (C1 : 140735332483072 <= alloc_ceiling <= 140737479966720),
forall (C2 : kHighShadowEnd = 17594333495296),
forall (C3 : kHighMemBeg = 17594333495296),
forall (C4 : kHighMemEnd = 140737488355328),
forall (C5 : kLowMemEnd = 2147450880),
forall (FFS : TNEWGIFX_STK = 18816),
forall (HEV : EV_NEWGIF = 12),
forall (Hes : ESTACK = 4096),
forall (Has : ASTACK = 16384),
forall (Hf4096 : 4096 <= frame_addr ly cid pos),
forall (Hfceil : frame_addr ly cid pos + fs_frame_bytes cid <= alloc_ceiling),
forall (Hfhigh : in_app (frame_addr ly cid pos) (fs_frame_bytes cid)),
forall (Hfhigh_img : off_img (frame_addr ly cid pos) (fs_frame_bytes cid)),
forall (E241 : ew E 241 = Z_to_bv 64 (VAL 241)),
forall (E242 : ew E 242 = Z_to_bv 64 (VAL 242)),
forall (E244 : ew E 244 = Z_to_bv 64 (VAL 244)),
forall (E253 : ew E 253 = Z_to_bv 64 (VAL 253)),
forall (Hob241 : 65536 <= VAL 241 ∧ VAL 241 + 8 <= 6270976),
forall (Hob242 : 65536 <= VAL 242 ∧ VAL 242 + 8 <= 6270976),
forall (Hob244 : 65536 <= VAL 244 ∧ VAL 244 + 8 <= 6270976),
forall (Hob253 : 65536 <= VAL 253 ∧ VAL 253 + 8 <= 6270976),
forall (Huar : 65536 <= as_uar_cell B ∧ as_uar_cell B + 8 <= 6270976),
forall (Huar4 : as_uar_cell B mod 4 = 0),
forall (CV0 : val_mem SEGS (mrestrict (w_H W) mem) (cfgp + 0) (N.to_nat 8) pal0),
forall (CR0 : 0 <= pal0 < 2 ^ 64),
forall (CV8 : val_mem SEGS (mrestrict (w_H W) mem) (cfgp + 8) (N.to_nat 8) (ak_path K)),
forall (CR8 : 0 <= ak_path K < 2 ^ (8 * Z.of_N (8, 8%N).2)),
forall (CV16 : val_mem SEGS (mrestrict (w_H W) mem) (cfgp + 16) (N.to_nat 4) attr),
forall (CR16 : 0 <= attr < 2 ^ 32),
forall (CV20 : val_mem SEGS (mrestrict (w_H W) mem) (cfgp + 20) (N.to_nat 4) gen),
forall (CR20 : 0 <= gen < 2 ^ 32),
forall (CV24 : val_mem SEGS (mrestrict (w_H W) mem) (cfgp + 24) (N.to_nat 2) Wd),
forall (CR24 : 0 <= Wd < 65536),
forall (CV26 : val_mem SEGS (mrestrict (w_H W) mem) (cfgp + 26) (N.to_nat 2) Hd),
forall (CR26 : 0 <= Hd < 65536),
forall (CV28 : val_mem SEGS (mrestrict (w_H W) mem) (cfgp + 28) (N.to_nat 2) ngp),
forall (CR28 : 0 <= ngp < 65536),
forall (CV30 : val_mem SEGS (mrestrict (w_H W) mem) (cfgp + 30) (N.to_nat 2) loops),
forall (CR30 : 0 <= loops < 65536),
forall (CV32 : val_mem SEGS (mrestrict (w_H W) mem) (cfgp + 32) (N.to_nat 8) hw),
forall (CR32 : 0 <= hw < 2 ^ (8 * Z.of_N (32, 8%N).2)),
forall (CV40 : val_mem SEGS (mrestrict (w_H W) mem) (cfgp + 40) (N.to_nat 8) 0),
forall (CR40 : 0 <= 0 < 2 ^ (8 * Z.of_N (40, 8%N).2)),
forall (HcT : True),
forall (Hrq1 : 1 <= req_size (3 * ngp)),
forall (Hrq2 : 3 * ngp <= req_size (3 * ngp)),
forall (HAR3 : AR SEGS B ly3 S3 W3 (ms_mem ms3) md3),
forall (EFA3 : ∀ cid pos : Z, frame_addr ly3 cid pos = frame_addr ly cid pos),
forall (EFL3 : ∀ c p : Z, flag_addr ly3 c p = flag_addr ly c p),
forall (Hfin3 : In (1, fpos) (frames S3)),
forall (HfinS3 : In (cid, pos) (frames S3)),
forall (HFal : F mod 32 = 0),
forall (HFhi : 4096 <= F),
forall (HFpres3 : ∀ a : Z, F <= a < F + 128 → apresent (w_H W3) (ms_mem ms3) a ∧ ¬ aowned B ly3 S3 a),
forall (HFSpres3 : ∀ i : Z, 0 <= i < 16 → apresent (w_H W3) (ms_mem ms3) (shadow_addr F + i) ∧ ¬ aowned B ly3 S3 (shadow_addr F + i)),
forall (HFapp_img : off_img F 128),
forall (HF4096 : 4096 <= F),
forall (HFceil : F + 128 <= alloc_ceiling),
forall (HFhigh : in_app F 128),
forall (HFhigh_img : off_img F 128),
forall (HFq : F = 32 * (F / 32)),
forall (HF8 : F / 8 = 4 * (F / 32)),
forall (HF8lo : 512 <= F / 8),
forall (HF8hi : F / 8 < 17592186044416),
forall (fl1 fl2 : list (Z * Z)),
forall (Efl : frames S = fl1 ++ (cid, pos) :: fl2),
forall (HdFC : nboxed (F + 128 <= frame_addr ly cid pos ∨ frame_addr ly cid pos + fs_frame_bytes cid <= F)),
forall (Rngp : 0 <= ngp <= 65535),
forall (Rpath : 65536 <= ak_path K < 6270976),
forall (Hpf_in : In (pf, FILE_BLOCK) (ablocks B ly3 S3)),
forall (Hpf16 : pf mod 16 = 0),
forall (Hpfceil : pf + 1264 <= alloc_ceiling),
forall (Hp_ia : xfacts (in_app pf 1264)),
forall (Hg_in : In (g, 96) (ablocks B ly3 S3)),
forall (Hp_in : In (pal, 3 * ngp) (ablocks B ly3 S3)),
forall (Hp16 : pal mod 16 = 0),
forall (Hpceil : pal + req_size (3 * ngp) <= alloc_ceiling),
forall (Hph_ia : in_app pal (req_size (3 * ngp))),
forall (Hppres3 : ∀ a : Z, pal <= a < pal + req_size (3 * ngp) → apresent (w_H W3) (ms_mem ms3) a ∧ ¬ aowned B ly3 S3 a),
forall (Hph : 4096 <= pal),
forall (Hph_img : off_img pal (req_size (3 * ngp))),
forall (HdPF : nboxed (pal + req_size (3 * ngp) <= F ∨ F + 128 <= pal)),
forall (HdPC : nboxed (pal + req_size (3 * ngp) <= frame_addr ly cid pos ∨ frame_addr ly cid pos + fs_frame_bytes cid <= pal)),
forall (Hg16 : g mod 16 = 0),
forall (Hgceil : g + 96 <= alloc_ceiling),
forall (Hgh_ia : in_app g (req_size 96)),
forall (Hgpres3 : ∀ a : Z, g <= a < g + 96 → apresent (w_H W3) (ms_mem ms3) a ∧ ¬ aowned B ly3 S3 a),
forall (Hgh : 4096 <= g),
forall (Hgh_img : off_img g (req_size 96)),
forall (HdGF : nboxed (g + 96 <= F ∨ F + 128 <= g)),
forall (HdGC : nboxed (g + 96 <= frame_addr ly cid pos ∨ frame_addr ly cid pos + fs_frame_bytes cid <= g)),
forall (HPermPG : Permutation (ablocks B ly3 S3) ((pal, 3 * ngp) :: (g, 96) :: ablocks B ly S ++ [(pf, FILE_BLOCK)])),
forall (XF : xfacts
((((alloc_ceiling + TNEWGIFX_STK <= spZ regs ∧ TNEWGIFX_STK = 18816 ∧ 140735332483072 <= alloc_ceiling <= 140737479966720 ∧ (F + 128 <= 65536 ∨ 6270976 <= F) ∧ 4096 <= F ∧ F + 128 <= alloc_ceiling ∧ 512 <= F / 8)
∧ pf + 1264 <= alloc_ceiling ∧ 4096 <= pf ∧ (pf + 1264 <= 65536 ∨ 6270976 <= pf) ∧ (pf + 1264 <= cfgp ∨ cfgp + 48 <= pf) ∧ 4096 <= cfgp ∧ (pf + 1264 <= F ∨ F + 128 <= pf))
∧ (pf + 1264 <= g ∨ g + 96 <= pf) ∧ 4096 <= g ∧ g + 96 <= alloc_ceiling ∧ (g + 96 <= 65536 ∨ 6270976 <= g))
∧ (pf + 1264 <= pal ∨ pal + req_size (3 * ngp) <= pf)
∧ 4096 <= pal
∧ pal + req_size (3 * ngp) <= alloc_ceiling ∧ (pal + req_size (3 * ngp) <= 65536 ∨ 6270976 <= pal) ∧ 3 * ngp <= req_size (3 * ngp) ∧ (pal + req_size (3 * ngp) <= F ∨ F + 128 <= pal) ∧ (pal + req_size (3 * ngp) <= g ∨ g + 96 <= pal))),
forall (Hpal_ia : xfacts (in_app pal (req_size (3 * ngp)))),
forall (HPermA : Permutation (ablocks B ly S) ((pala, 3 * ngp) :: rest)),
forall (Hpala_in : In (pala, 3 * ngp) (ablocks B ly S)),
forall (Hpala3 : In (pala, 3 * ngp) (ablocks B ly3 S3)),
forall (Hpala4096 : 4096 <= pala),
forall (E10' : ew E 10 = Z_to_bv 64 cfgp),
forall (w w0 w1 w2 w3 : word),
forall (ms : machine_state),
forall (mat : list word),
forall (HEI0 : img_env VAL A_LIM (ewset (ewset (ewset (ewset (ewset E 631 w) 632 w0) 633 w1) 634 w2) 635 w3)),
forall (HS : st_ok SEGS (ewset (ewset (ewset (ewset (ewset E 631 w) 632 w0) 633 w1) 634 w2) 635 w3)
(setpc
(mkSS 920
[SLit 0; SOff 240 920; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 612 0; SOff 613 0; SOff 614 0; SOff 2 0; SOff 2 (-192); SOff 516 32; SOff 240 1556; SOff 635 0; SOff 630 0; SOff 619 0; SOff 620 0; SOff 621 0; SOff 622 0;
SOff 516 0; SOff 550 0; SOff 10 0; SOff 516 32; SOff 10 24; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 35 0); SOff 529 0; SOff 35 0; SOff 550 24; SOff 516 0; SOff 623 0; SOff 624 0; SOff 625 0; SOff 626 0]
[{|
r_base := Some 550%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 96;
r_chunks :=
[{| c_off := 24; YP09.c_val := CVal 8 (SOff 599 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SLit 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 34 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 39 0) |};
{| c_off := 56; YP09.c_val := CVal 8 (SLit match NP with
| {| ngp_hw := ngp_hw |} => ngp_hw
end) |};
{| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SLit 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SLit 1) |}]
|};
{|
r_base := Some 516%nat;
r_lo := 32;
r_hi := 72;
r_wlo := 32;
r_whi := 72;
r_chunks :=
[{| c_off := 66; YP09.c_val := CVal 2 (SExt true 16 (SOff 39 0)) |}; {| c_off := 40; YP09.c_val := CVal 8 (SOff 550 0) |}; {| c_off := 32; YP09.c_val := CVal 8 (SOff 240 1556) |};
{| c_off := 62; YP09.c_val := CVal 2 (SExt true 16 (SOff 37 0)) |}; {| c_off := 60; YP09.c_val := CVal 2 (SExt true 16 (SOff 36 0)) |}; {| c_off := 64; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 56; YP09.c_val := CVal 4 (SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL (SOff 33 0) (SLit 62)) (SLit 63)) (SAlu ALU_AND (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SLit 2))) |};
{| c_off := 48; YP09.c_val := CVal 8 (SOff 32 0) |}]
|}; {| r_base := Some 516%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |};
{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|}; {| r_base := Some 516%nat; r_lo := 72; r_hi := 128; r_wlo := 72; r_whi := 128; r_chunks := [{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{|
r_base := Some 2%nat;
r_lo := -192;
r_hi := 0;
r_wlo := -192;
r_whi := 0;
r_chunks :=
[{| c_off := -184; YP09.c_val := CVal 8 (SOff 10 28) |}; {| c_off := -192; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 28) (SLit 3)) (SOff 35 0)) |}; {| c_off := -168; YP09.c_val := CVal 8 (SOff 10 16) |};
{| c_off := -176; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 35 0)) |}; {| c_off := -152; YP09.c_val := CVal 8 (SAlu ALU_SRL (SOff 10 0) (SLit 3)) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 10 26) |}; {| c_off := -136; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 26) (SLit 3)) (SOff 35 0)) |};
{| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}] |};
{| r_base := Some 41%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 244%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 28; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 39 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SLit match NP with
| {| ngp_hw := ngp_hw |} => ngp_hw
end) |};
{| c_off := 40; YP09.c_val := CVal 8 (SLit 0) |}]
|}]
None
{|
f_atoms :=
[(599%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (550%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |}); (32%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(33%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 65536; af_hi := 6270976; af_al2 := 0 |})];
f_conds :=
[{| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SOff 33 0) (SLit 4); ac_b := SLit 0 |}; {| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SExt false 8 (SOff 33 0)) (SLit 4); ac_b := SLit 0 |}; {| ac_c := BC_NE; ac_a := SOff 37 0; ac_b := SLit 0 |};
{| ac_c := BC_NE; ac_a := SOff 36 0; ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)]
|})
(SIGMA AS_cgif_raw_newgif))
(restrict (w_H W3) ms)),
forall (SHOK : sh_ok SEGS (SOff 35 0) [{| she_m := 550; she_lo := 96; she_hi := 0 |}; {| she_m := 516; she_lo := 72; she_hi := 32 |}; {| she_m := 516; she_lo := 32; she_hi := 0 |}; {| she_m := 516; she_lo := 128; she_hi := 72 |}]
(ewset (ewset (ewset (ewset (ewset E 631 w) 632 w0) 633 w1) 634 w2) 635 w3) (mrestrict (w_H W3) (ms_mem ms))),
forall (HJ3 : ajournal SEGS B TNEWGIFX_STK (spZ regs) [sink_token] ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k),
forall (HSINK : asink_at SEGS K (mrestrict (w_H W3) (ms_mem ms)) (with_vm_backing (m_vm_lazy md3) mat md3) pf []),
forall (HGPAL : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) pal GPAL),
let sgct : Z := ngp in
forall (Vwfn : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (F + 32) (N.to_nat 8) (BASE + 1556)),
forall (Vctx : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (F + 40) (N.to_nat 8) g),
forall (Vgct : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (F + 48) (N.to_nat 8) pal0),
forall (Vrat : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (F + 56) (N.to_nat 4) (ng_rattr attr)),
forall (VW : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (F + 60) (N.to_nat 2) Wd),
forall (VH : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (F + 62) (N.to_nat 2) Hd),
forall (Vlp : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (F + 66) (N.to_nat 2) loops),
forall (Vsg : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (F + 64) (N.to_nat 2) ngp),
forall (Ocfg : obj_at SEGS (mrestrict (w_H W3) (ms_mem ms)) (F + 32) LAY_RawConfig [BASE + 1556; g; pal0; ng_rattr attr; Wd; Hd; sgct; loops]),
forall (HB79 : bv_unsigned (ew (ewset (ewset (ewset (ewset (ewset E 631 w) 632 w0) 633 w1) 634 w2) 635 w3) 550) = g),
forall (Gwfn : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (g + 56) (N.to_nat 8) hw),
forall (Gctx : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (g + 64) (N.to_nat 8) 0),
forall (Gfile : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (g + 80) (N.to_nat 8) pf),
forall (HEVc : st_nev S3 + EV_RAWNEW <= EV_MAX),
forall (HLIVEc : blocks_bytes S3 + 2 ^ 16 <= LIVE_MAX),
let restX : list (Z * Z) := (pal, 3 * ngp) :: ablocks B ly S in
forall (HBL : Permutation (ablocks B ly3 S3) ((g, CGIF_SIZE) :: (pf, FILE_BLOCK) :: restX)),
forall (HnPF : ¬ In (pf, FILE_BLOCK) (ablocks B ly S)),
forall (HMOKc : mo_ok MT S3 (mo_malloc MT RAW_SIZE)),
forall (HGPALA : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) pala GPAL),
forall (Kgot3 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12))),
forall (Kcell3 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (VAL (A_OBJ 12)) 8 SHADOW_OFF),
forall (Kguar3 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (VAL (A_OBJ 1)) 8 (as_uar_cell B)),
forall (Kuar3 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (as_uar_cell B) 4 1),
forall (Vgr3 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (VAL (A_OBJ 3)) 8 (BASE + 0)),
forall (Qceil : alloc_ceiling <= spZ regs),
forall (Qal8 : spZ regs mod 8 = 0),
forall (Qtop : spZ regs < ly_top ly - 16),
forall (Qtop64 : ly_top ly <= 2 ^ 64),
forall (Qsp : spZ regs - 192 + 16 <= spZ regs),
forall (Qra : 0 <= raZ regs < 2 ^ 64),
forall (Qs0 : 0 <= s0Z regs < 2 ^ 64),
forall (HspX : spZ (ms_regs ms) = spZ regs - 192),
forall (HLY3 : layout_le (length (st_secs S)) ly ly3),
forall (Etop3 : ly_top ly3 = ly_top ly),
forall (W4 : world SEGS),
forall (Hwle4 : wle W3 W4),
forall (ly4 : alayout),
forall (S4 : astate),
forall (regs4 : bvmap 5 word),
forall (mem4 : word → option byte),
forall (md4 : Model),
forall (HJ4 : ajournal SEGS B TNEWGIFX_STK (spZ regs) [sink_token] ly S W mem md [(1, fpos)] ly4 S4 W4 mem4 md4 (k + EV_RAWNEW)),
forall (HJc : ajournal SEGS B TRAWNEW_STK (spZ regs + -192) (asink_fp pf) ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) [] ly4 S4 W4 mem4 md4 EV_RAWNEW),
forall (HP4 : aregs_preserved (ms_regs ms) regs4),
forall (res : Z),
forall (Ha04 : getr regs4 10 = w64 res),
forall (MLEc : mo_le MT S3 S4 (mo_malloc MT RAW_SIZE)),
forall (Hresnz : res ≠ 0),
forall (Hsg : sgct <= 256),
forall (HPerm4 : Permutation (ablocks B ly4 S4) ((res, RAW_SIZE) :: ablocks B ly3 S3)),
forall (Araw : ∀ (blc : list (Z * Z)) (i : Z), In (res, RAW_SIZE) blc → 0 <= i < RAW_SIZE → awr_byte TRAWNEW_STK (spZ regs - 192) (asink_fp pf) (ablocks B ly3 S3) blc ly4 [] (res + i)),
forall (Traw : aftok (asink_fp pf) (ablocks B ly3 S3) (res, RAW_SIZE)),
forall (Oraw : obj_at SEGS (mrestrict (w_H W4) mem4) res LAY_Raw [BASE + 1556; g; pal0; ng_rattr attr; Wd; Hd; sgct; loops; R_PENDING]),
forall (HSINK4 : asink_at SEGS K (mrestrict (w_H W4) mem4) md4 pf ([] ++ YO07.raw_header Wd Hd sgct GPAL (ng_rattr attr) loops)),
forall (HAR4 : AR SEGS B ly4 S4 W4 mem4 md4),
forall (Kgot4 : val_mem SEGS (mrestrict (w_H W4) mem4) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12))),
forall (Kcell4 : val_mem SEGS (mrestrict (w_H W4) mem4) (VAL (A_OBJ 12)) 8 SHADOW_OFF),
forall (Kguar4 : val_mem SEGS (mrestrict (w_H W4) mem4) (VAL (A_OBJ 1)) 8 (as_uar_cell B)),
forall (Kuar4 : val_mem SEGS (mrestrict (w_H W4) mem4) (as_uar_cell B) 4 1),
forall (Vgr4 : val_mem SEGS (mrestrict (w_H W4) mem4) (VAL (A_OBJ 3)) 8 (BASE + 0)),
forall (EFA4 : ∀ cid pos : Z, frame_addr ly4 cid pos = frame_addr ly cid pos),
forall (EFL4 : ∀ c p : Z, flag_addr ly4 c p = flag_addr ly c p),
forall (Hfrs4 : frames S4 = frames S3),
forall (Hfin4 : In (1, fpos) (frames S4)),
forall (HfinS4 : In (cid, pos) (frames S4)),
forall (HFpres4 : ∀ a : Z, F <= a < F + 128 → apresent (w_H W4) mem4 a ∧ ¬ aowned B ly4 S4 a),
forall (HFSpres4 : ∀ i : Z, 0 <= i < 16 → apresent (w_H W4) mem4 (shadow_addr F + i) ∧ ¬ aowned B ly4 S4 (shadow_addr F + i)),
forall (HCpres4 : ∀ a : Z, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid → apresent (w_H W4) mem4 a ∧ ¬ aowned B ly4 S4 a),
SRr SEGS W4 {| cfg_ms := mkst regs4 (Z_to_bv 64 (BASE + 920)) mem4 (seg_rom SEGS); cfg_model := md4 |} (ng_postXB B K MT XN regs ly S W mem md attr gen Wd Hd sgct loops aM GPAL).
Proof.
intros ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 E W3 ly3 S3 ms3 md3 k fpos pf g pal HPRE Hal32 Hctx Hroom Htop32 HROD Hcfg HWH Hpala HPerm Hev Hlive HXE Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA EE E10 E32 Usp AG E33 E34 E35 E36 E37 E38 E39 E40 F RF FL E528 E529 E41 HEI E42 E52 Rg Rp Hk3 Hfrs3 Eab3 Hg4096 Hp4096 Hpf4096 Tg Ag Tp Ap Tpf Apf MLE3 HW0 HH0 Ha4 Epala HGP HSNK0 HFD0 HAM0 HMOK HG0 HGl Hwx Hsegs HAR Hra Hra4 Hgp Htp Hstk Hpres Hch HQT Hal16 Hstk0 Hceil Hslo Hshi H47 Hbot Htop Htop2 C1 C2 C3 C4 C5 FFS HEV Hes Has Hf4096 Hfceil Hfhigh Hfhigh_img E241 E242 E244 E253 Hob241 Hob242 Hob244 Hob253 Huar Huar4 CV0 CR0 CV8 CR8 CV16 CR16 CV20 CR20 CV24 CR24 CV26 CR26 CV28 CR28 CV30 CR30 CV32 CR32 CV40 CR40 HcT Hrq1 Hrq2 HAR3 EFA3 EFL3 Hfin3 HfinS3 HFal HFhi HFpres3 HFSpres3 HFapp_img HF4096 HFceil HFhigh HFhigh_img HFq HF8 HF8lo HF8hi fl1 fl2 Efl HdFC Rngp Rpath Hpf_in Hpf16 Hpfceil Hp_ia Hg_in Hp_in Hp16 Hpceil Hph_ia Hppres3 Hph Hph_img HdPF HdPC Hg16 Hgceil Hgh_ia Hgpres3 Hgh Hgh_img HdGF HdGC HPermPG XF Hpal_ia HPermA Hpala_in Hpala3 Hpala4096 E10' w w0 w1 w2 w3 ms mat HEI0 HS SHOK HJ3 HSINK HGPAL sgct Vwfn Vctx Vgct Vrat VW VH Vlp Vsg Ocfg HB79 Gwfn Gctx Gfile HEVc HLIVEc restX HBL HnPF HMOKc HGPALA Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0 HspX HLY3 Etop3 W4 Hwle4 ly4 S4 regs4 mem4 md4 HJ4 HJc HP4 res Ha04 MLEc Hresnz Hsg HPerm4 Araw Traw Oraw HSINK4 HAR4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4 EFA4 EFL4 Hfrs4 Hfin4 HfinS4 HFpres4 HFSpres4 HCpres4.
+
assert (Hr_in4 : In (res, RAW_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4 | left; reflexivity]).
assert (Hg_in4 : In (g, 96) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4 | right; exact Hg_in]).
assert (Hpf_in4 : In (pf, FILE_BLOCK) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4 | right; exact Hpf_in]).
clear HSINK. rename HSINK4 into HSINK. cbn [app] in HSINK.
assert (Hp_in4 : In (pal, 3 * ngp) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4 | right; exact Hp_in]).
assert (HGPAL4 : garr8 SEGS (mrestrict (w_H W4) mem4) pal GPAL).
{ apply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal (3 * ngp) pal GPAL HJc Hp_in Hp_in4);
[ clear; lia | rewrite HGl; clear - Hrq2; lia
| intros a Ha Hn; apply in_asink_fp in Hn; unfold FILE_BLOCK in Hn; rewrite HGl in Ha; clear - XF Ha Hn; unfold xfacts in XF; lia | exact HGPAL ]. }
clear HGPAL. rename HGPAL4 into HGPAL.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res RAW_SIZE HAR4 Hr_in4) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & Hrpres4 & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_imgP _ _ _ _ _ _ res RAW_SIZE HAR4 Hr_in4) as Hrh_img.
change (req_size RAW_SIZE) with 48 in Hrceil, Hrpres4, Hrh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR4 Hg_in4) as (_ & _ & _ & _ & Hgpres4 & _). change (req_size 96) with 96 in Hgpres4.
assert (HPerm4' : Permutation (ablocks B ly4 S4) ((res, RAW_SIZE) :: (g, CGIF_SIZE) :: (pf, FILE_BLOCK) :: restX)) by (eapply Permutation_trans; [exact HPerm4 | apply perm_skip; exact HBL]).
pose proof (sep_blocks_perm SEGS B LAWS ly4 S4 _ _ _ (res, RAW_SIZE) (g, CGIF_SIZE) _ HAR4 HPerm4') as HdRG.
unfold zdisjoint, block_rng in HdRG. cbn [fst snd] in HdRG. change (req_size RAW_SIZE) with 48 in HdRG. change (req_size CGIF_SIZE) with 96 in HdRG.
assert (HPerm4'' : Permutation (ablocks B ly4 S4) ((res, RAW_SIZE) :: (pal, 3 * ngp) :: (g, CGIF_SIZE) :: (pf, FILE_BLOCK) :: ablocks B ly S)).
{ eapply Permutation_trans; [exact HPerm4'|]. apply perm_skip. subst restX. apply Permutation_sym. apply (Permutation_middle [(g, CGIF_SIZE); (pf, FILE_BLOCK)] (ablocks B ly S) (pal, 3 * ngp)). }
pose proof (sep_blocks_perm SEGS B LAWS ly4 S4 _ _ _ (res, RAW_SIZE) (pal, 3 * ngp) _ HAR4 HPerm4'') as HdRP.
unfold zdisjoint, block_rng in HdRP. cbn [fst snd] in HdRP. change (req_size RAW_SIZE) with 48 in HdRP.
pose proof (sep_block_frame SEGS B LAWS ly4 S4 _ _ _ res RAW_SIZE 1 fpos HAR4 Hr_in4 Hfin4) as HdRF.
unfold zdisjoint in HdRF. cbn [fst snd] in HdRF. change (req_size RAW_SIZE) with 48 in HdRF. change (fs_frame_bytes 1) with 128 in HdRF. rewrite EFA4 in HdRF. fold F in HdRF.
pose proof (sep_block_frame SEGS B LAWS ly4 S4 _ _ _ res RAW_SIZE cid pos HAR4 Hr_in4 HfinS4) as HdRC.
unfold zdisjoint in HdRC. cbn [fst snd] in HdRC. change (req_size RAW_SIZE) with 48 in HdRC. rewrite EFA4 in HdRC.
pose proof (sep_blocks SEGS B LAWS ly4 S4 _ _ _ pf FILE_BLOCK res RAW_SIZE HAR4 Hpf_in4 Hr_in4 ltac:(unfold FILE_BLOCK, RAW_SIZE; intros X; injection X; clear; lia)) as HdXR.
unfold zdisjoint in HdXR. cbn [fst snd] in HdXR. change (req_size FILE_BLOCK) with 1264 in HdXR. change (req_size RAW_SIZE) with 48 in HdXR.
pose proof Hrh_img as HRoffX. unfold off_img in HRoffX.
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (P /\ (pf + 1264 <= res \/ res + 48 <= pf) /\ 4096 <= res /\ res + 48 <= alloc_ceiling /\ (res + 48 <= 65536 \/ 6270976 <= res)))
by (apply xfacts_i; split; [exact XF | clear - HdXR Hr4096 Hrceil HRoffX; lia]); clear XF HRoffX; rename XF2 into XF end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pf FILE_BLOCK HAR4 Hpf_in4) as (_ & _ & _ & _ & Hpfpres4 & _). change (req_size FILE_BLOCK) with 1264 in Hpfpres4.
assert (HnoPF : forall a, pf <= a < pf + 1264 -> ~ aowned B ly4 S4 a) by (intros a Ha; exact (proj2 (Hpfpres4 a Ha))).
nbox_seps.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptJ HJc HJ4 AG Usp E10 RF E529 Hfin3 HfinS3 FFS Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4 EFA3 HFpres4 HFSpres4 HCpres4 F ltac:(fpfile)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
prreg HS (10%bv : bv 5) Rr. cbn [ms_regs] in Rr. rewrite Ha04 in Rr. symmetry in Rr. unfold w64 in Rr.
lazymatch type of Rr with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rr, unsigned_lit_small by (clear - Hr4096 Hrceil C1; lia); change (2 ^ 4) with 16;
clear - Hr16 Hr4096 Hrceil Hrh C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ4 SHOK NBspan 0x418.
all: try (slim; obl_blk HJ4 Rg E35 Hg_in4).
all: try (slim; awrR AG fpos F EFA4).
lazymatch goal with HFr : frame_of _ _ _ _ |- _ => xsink_stretch HFr HSINK; xgarr_stretch HFr HGPAL end.
lazymatch goal with HFr : frame_of _ _ _ _ |- _ =>
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (g <= a < g + 96) \/ (F <= a < F + 128) \/ (spZ regs - 192 <= a < spZ regs)) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr; revert Hrr; evalE AG;
first [rewrite Rg | rewrite RF | idtac]; rewrite ?unsigned_lit_small by lia; intros Hrr; clear - Hrr; lia |]);
destruct Hin)) as UN1 end.
clear_frames.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 550%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow SEGS Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 550%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (ast_ok_set_region SEGS Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow SEGS Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
reshok_bx HS 35%nat.
assert (HnoG : forall a, g <= a < g + 96 -> ~ aowned B ly4 S4 a) by (intros a Ha; exact (proj2 (Hgpres4 a Ha))).
assert (HnoR : forall a, res <= a < res + 48 -> ~ aowned B ly4 S4 a) by (intros a Ha; exact (proj2 (Hrpres4 a Ha))).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pal (3 * ngp) HAR4 Hp_in4) as (_ & _ & _ & _ & Hppres4 & _).
assert (HnoP : forall a, pal <= a < pal + req_size (3 * ngp) -> ~ aowned B ly4 S4 a) by (intros a Ha; exact (proj2 (Hppres4 a Ha))).
exitNX RET RUNF HS HJ4 AG fpos F cfgp E528 E529 Hfin4 HfinS4 EE Hra HEV EFA4 EFL4
ltac:(idtac; lazymatch goal with HFr : frame_of _ _ (mrestrict _ (ms_mem _)) (mrestrict _ _) |- _ => xsink_stretch HFr HSINK; xgarr_stretch HFr HGPAL end).
exists g. split; [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite Rg; reflexivity|].
lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?mdx) ?matx ?mdx] =>
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mdx _ =>
pose proof (ajournal_materialize _ _ LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matx HJ4) as HJF end end.
split; [exact (proj2 (proj2 (ameta_inv_kept SEGS B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF HAM0)))|].
split.
{ unfold stack_free_state. apply (mo_le_set_fs_r MT MLAWF).
apply (mle_weaken MT S S4 (ng_macc3 MT ngp + mo_malloc MT RAW_SIZE) _ MLAW (mle_station MT S S3 S4 _ _ MLAW MLE3 MLEc)).
pose proof (HXN ngp Rngp) as Hx. unfold ng_msum, ng_macc3 in Hx.
pose proof (mo_malloc_nonneg MT MLAW (3 * ngp) ltac:(clear - Rngp; lia)) as M3. pose proof (mo_free_nonneg MT MLAW) as M5. try unfold ng_macc3. cbv delta [sgct]. clear - Hx M3 M5. lia. }
right. split; [clear - Hg4096; lia|].
split; [unfold g_sgct_ok, g_sgct, newgif_cfg; cbn [YO07.g_attr YO07.g_ngp]; unfold YO07.flag; rewrite Ha4; cbn [Z.eqb negb]; apply Bool.negb_true_iff; apply Z.ltb_ge; cbv delta [sgct] in Hsg; exact Hsg|].
exists (mkCgif [None; None; None] pal attr gen Wd Hd ngp loops res R_PENDING 1 pal0 (ng_rattr attr) loops R_PENDING), pf.
split.
{
split; [|split].
- lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 550%nat in let i := eval vm_compute in i in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W4) msX) i _ HS eq_refl) as HRgf; cbn [ms_mem restrict] in HRgf;
assert (HB79f : bv_unsigned (ew Ex 550) = g) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite Rg; apply unsigned_lit_small; clear - Hg4096 Hgceil C1; lia) | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 550%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W4) msX) i _ HS eq_refl) as HRgf; cbn [ms_mem restrict] in HRgf;
assert (HB79f : bv_unsigned (ew Ex 550) = g) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side; rewrite Rg; apply unsigned_lit_small; clear - Hg4096 Hgceil C1; lia)  end.
lazymatch type of HRgf with region_ok _ ?Ex _ (YP09.mkRegion (Some 550%nat) ?lo ?hi ?wlo ?whi ?cs) =>
let lit off n v Rt Q := pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi off n (SLit v) v HRgf HB79f ltac:(cbn; tauto) eq_refl ltac:(Rt) ltac:(cbn; lia)) as Q in
let atm off n e v He Rt Q := pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi off n e v HRgf HB79f ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by nat_side;
rewrite ?(AG 32%nat) by lia; rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(Rt) ltac:(cbn; lia)) as Q in
lit 0 8%N 0 ltac:(zside) Q0; lit 8 8%N 0 ltac:(zside) Q8; lit 16 8%N 0 ltac:(zside) Q16;
atm 24 8%N (SOff 599 0) pal Rp ltac:(cbn; clear - Hp4096 Hpceil Hrq1 C1; lia) Q24;
atm 32 8%N (SOff 42 0) (ak_path K) E42 ltac:(cbn; clear - Rpath; lia) Q32;
atm 40 4%N (SOff 33 0) attr E33 ltac:(cbn; clear - CR16; lia) Q40; atm 44 4%N (SOff 34 0) gen E34 ltac:(cbn; clear - CR20; lia) Q44;
atm 48 2%N (SOff 36 0) Wd E36 ltac:(cbn; clear - CR24; lia) Q48; atm 50 2%N (SOff 37 0) Hd E37 ltac:(cbn; clear - CR26; lia) Q50;
atm 52 2%N (SOff 38 0) ngp E38 ltac:(cbn; clear - CR28; lia) Q52; atm 54 2%N (SOff 39 0) loops E39 ltac:(cbn; clear - CR30; lia) Q54;
lit 56 8%N (@ngp_hw NP) ltac:(clear - Rhw; zside) Q56; lit 64 8%N 0 ltac:(zside) Q64;
lazymatch type of Rr with ew _ ?nr = _ => atm 72 8%N (SOff nr 0) res Rr ltac:(cbn; clear - Hr4096 Hrceil C1; lia) Q72 end;
atm 80 8%N (SOff 52 0) pf E52 ltac:(cbn; clear - Hpf4096 Hpfceil C1; lia) Q80;     lit 88 4%N R_PENDING ltac:(unfold R_PENDING; zside) Q88; lit 92 4%N 1 ltac:(zside) Q92
end.
cbn [N.to_nat] in Q0, Q8, Q16, Q24, Q32, Q40, Q44, Q48, Q50, Q52, Q54, Q56, Q64, Q72, Q80, Q88, Q92.
unfold xcgif_vals, cg_frames, cg_pal, cg_attr, cg_gen, cg_W, cg_H, cg_ngp, cg_loops, cg_raw, cg_cur, cg_ihead. cbn [nth frame_ptr obj_at LAY_CGIF].
unfold field_ok. cbn [fst snd N.to_nat Z.of_N].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536.
repeat split; try assumption;
first [unfold R_PENDING; clear - Rhw; lia | clear - CR0 CR16 CR20 CR24 CR26 CR28 CR30 Hg4096 Hgceil Hr4096 Hrceil C1 Rpath Hpf4096 Hpfceil; lia
| clear - Hp4096 Hpceil Hrq1 C1; lia
| match goal with |- ?G => idtac "OBJLEFT" G end].
-
lazymatch goal with HFr : frame_of _ _ _ _ |- _ =>
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (FL <= a < FL + 1) \/ (SB + F / 8 <= a < SB + F / 8 + 16) \/ (F <= a < F + 128) \/ (spZ regs - 192 <= a < spZ regs)) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr; revert Hrr; evalE AG;
first [rewrite Rg | rewrite RF | idtac]; rewrite ?unsigned_lit_small by lia; intros Hrr; clear - Hrr; lia |]);
destruct Hin)) as UN2 end.
lazymatch goal with |- obj_at _ (mrestrict _ ?mF) _ _ _ =>
assert (KR : blk_kept (w_H W4) (w_H W4) mem4 mF res 48) end.
{ intros i Hi.
assert (Hb : 0 <= res + i < 2 ^ 64) by (clear - Hi Hr4096 Hrceil C1; lia).
rewrite (UN2 (res + i) Hb).
- apply (UN1 (res + i) Hb). clear - Hi HdRG HdRF Hrceil Hceil Hslo FFS. nunbox HdRG. nunbox HdRF. lia.
- intros [Hq | Hq].
+ apply (proj2 (Hrpres4 (res + i) ltac:(clear - Hi; lia))). replace (res + i) with FL by (clear - Hq; lia). exact HFLown'.
+ clear - Hq Hi HdRF Hrceil Hceil Hslo FFS HFq HF8 HF8lo HFceil Hrh Hrh_ia C1 C3. nunbox HdRF. unfold SB in Hq. zone_lia. }
unfold YC20.traw_vals, traw_vals, rw_gct, rw_attr, cg_W, cg_H, raw_sgct, cg_attr, cg_ngp, rw_loops, rw_cur.
rewrite Ha4. cbn [Z.eqb].
exact (obj_at_blk_kept _ _ _ _ res LAY_Raw _ 48 Oraw lay_inside_Raw KR).
- intros f Hf. exfalso. cbn in Hf. destruct Hf as [Hf | [Hf | [Hf | []]]]; discriminate Hf. }
split.
{ unfold cgif_wf, cg_frames, cg_W, cg_H, cg_attr, cg_ngp, cg_ihead. cbn [length nth].
split; [reflexivity|]. split; [clear - HW0 CR24; lia|]. split; [clear - HH0 CR26; lia|]. split; [reflexivity|]. split; [exact HWH|].
split; [intros _; exact Hsg|].
split; [left; reflexivity|].
intros f Hf. exfalso. cbn in Hf. destruct Hf as [Hf | [Hf | [Hf | []]]]; discriminate Hf. }
split; [clear - Hpf4096; lia|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|].
split.
{
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly4 S4).
unfold cgif_blocks, pal_blocks, frames_blocks, cg_frames, cg_raw, cg_attr, cg_pal, cg_ngp.
rewrite Ha4. cbn [Z.eqb flat_map app].
eapply Permutation_trans; [exact HPerm4''|]. apply Permutation_sym. apply (Permutation_middle [(res, RAW_SIZE); (pal, 3 * ngp)] ((pf, FILE_BLOCK) :: ablocks B ly S) (g, CGIF_SIZE)). }
split.
{
intros b Hb. unfold cgif_blocks, pal_blocks, frames_blocks, cg_frames, cg_raw, cg_attr, cg_pal, cg_ngp in Hb.
rewrite Ha4 in Hb. cbn [Z.eqb flat_map app In] in Hb.
destruct Hb as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd].
* split; [exact Tg | intros blc i Hbl Hi; apply Ag; [exact Hbl | exact Hi]].
* assert (HnFr : forall i, 0 <= i < 48 -> ~ inFP (asink_fp pf) (res + i)).
{ intros i Hi Hn. apply in_asink_fp in Hn. unfold FILE_BLOCK in Hn. clear - Hn Hi HdXR Hr4096. nunbox HdXR. lia. }
split.
-- intros Hin0 i Hi. exfalso. change (req_size RAW_SIZE) with 48 in Hi. apply (HnFr i Hi). apply Traw; [| exact Hi]. rewrite Eab3. apply in_app_iff. left. apply in_app_iff. left. apply in_app_iff. left. exact Hin0.
-- intros blc i Hbl Hi. change (req_size RAW_SIZE) with 48 in Hi.
apply (awr_byte_calleeX TNEWGIFX_STK TRAWNEW_STK (spZ regs) (spZ regs - 192) [sink_token] (asink_fp pf) (ablocks B ly S) (ablocks B ly3 S3) blc ly4 ly4 (res + i));
[ apply Araw; [exact Hbl | unfold RAW_SIZE; exact Hi] | unfold TNEWGIFX_STK, AFOPEN_STK, TRAWNEW_STK, ASTACK; clear; lia | clear; lia
| intros x Hx; rewrite Eab3; apply in_app_iff; left; apply in_app_iff; left; apply in_app_iff; left; exact Hx | exact (HnFr i Hi) ].
* split; [exact Tp | intros blc i Hbl Hi; apply Ap; [exact Hbl | exact Hi]].
* split; [exact Tpf | intros blc i Hbl Hi; apply Apf; [exact Hbl | exact Hi]]. }
split.
{
unfold cgif_relA, gs_new. cbn [YO07.s_cur YO07.s_out YO07.s_rcur YO07.s_ihead YO07.s_q0 YO07.s_q1 YO07.s_q2 cg_cur cg_frames rw_cur rw_attr cg_attr cg_ihead cg_pal cg_ngp nth concat].
split; [split; [reflexivity | unfold cgif_occ; cbn [cg_frames nth YO07.s_q0 YO07.s_q1 YO07.s_q2]; repeat split; intros; reflexivity]|].
split.
{ rewrite app_nil_r. unfold YO07.flag. rewrite Ha4. cbn [Z.eqb negb].
rewrite <- (ng_rattr_model attr ltac:(clear - CR16; lia)). exact HSINK. }
intros _. split; [reflexivity|]. split; [apply ng_rattr_model; clear - CR16; lia|]. split; [reflexivity|].
split; [intros _; split; [exact HGPAL | exact HGl]|]. cbn [oframe_relbA]. repeat split. }
unfold gs_new. cbn [YO07.s_out concat]. rewrite app_nil_r. eapply Z.le_trans; [apply raw_header_length | unfold HDR_OUT; clear; lia].
unfold YO07.flag. rewrite Ha4. cbn [Z.eqb negb]. cbv delta [sgct] in Hsg. cbv delta [sgct]. clear - Hsg Rngp. lia.
Qed.
End j. End h.
End d.
