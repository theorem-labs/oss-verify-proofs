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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACab ACam ACai ACaj ACak ACal ACan ACag ACap.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section l.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section q.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Lemma asink_kept_small : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k f Sg,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP ->
In (f, FILE_BLOCK) (ablocks B ly S) ->
(forall i, 0 <= i < FILE_BLOCK -> ~ inFP FP (f + i)) ->
asink_at SEGS K (mrestrict (w_H W) mem) md f Sg ->
In (f, FILE_BLOCK) (ablocks B ly' S') /\ asink_at SEGS K (mrestrict (w_H W') mem') md' f Sg.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k f Sg HJ Hcl Hin HnF HA.
assert (Hin' : In (f, FILE_BLOCK) (ablocks B ly' S')).
{ assert (D : forall x y : Z * Z, {x = y} + {x <> y}).
{ intros [a1 b1] [a2 b2]. destruct (Z.eq_dec a1 a2) as [->|n]; [destruct (Z.eq_dec b1 b2) as [->|n]; [left; reflexivity|]|];
right; intros Hq; injection Hq; intros; apply n; assumption. }
destruct (in_dec D (f, FILE_BLOCK) (ablocks B ly' S')) as [Hy | Hn]; [exact Hy|].
exfalso. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
apply (HnF 0 ltac:(unfold FILE_BLOCK; lia)). apply (Hgone f FILE_BLOCK 0 Hin Hn). unfold req_size, FILE_BLOCK. cbn. lia. }
split; [exact Hin'|]. eapply (asink_at_kept SEGS B K AIL); [exact HJ | exact Hcl | exact Hin | exact Hin' | exact HnF | exact HA].
Qed.
Lemma xlift_journal : forall STK ly S W (regs : bvmap 5 word) mem md ch raw pf own ly' S' W' mem' md' k Sg,
afn_pre SEGS B STK ly S W regs mem md ch ->
ajournal SEGS B STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md own ly' S' W' mem' md' k ->
In (pf, FILE_BLOCK) (ablocks B ly S) -> (pf + 1264 <= raw \/ raw + 48 <= pf) -> 0 <= raw ->
asink_at SEGS K (mrestrict (w_H W) mem) md pf Sg ->
ajournal SEGS B STK (spZ regs) ((raw + 40, raw + 44) :: asink_fp pf) ly S W mem md own ly' S' W' mem' md' k /\
In (pf, FILE_BLOCK) (ablocks B ly' S') /\ asink_at SEGS K (mrestrict (w_H W') mem') md' pf Sg.
Proof.
intros STK ly S W regs mem md ch raw pf own ly' S' W' mem' md' k Sg HPRE HJ Hin Hsep Hraw HA.
assert (HnF : forall i, 0 <= i < FILE_BLOCK -> ~ inFP [(raw + 40, raw + 44)] (pf + i)).
{ intros i Hi (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold FILE_BLOCK in Hi. lia. }
destruct (asink_kept_small STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md own ly' S' W' mem' md' k pf Sg HJ
ltac:(apply sink_closed_pos; constructor; [cbn; lia | constructor]) Hin HnF HA) as [Hin' HA'].
split; [| split; [exact Hin' | exact HA']].
pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low STK (spZ regs) ((raw + 40, raw + 44) :: asink_fp pf) ly S W mem md [] ly S W mem md 0
STK (spZ regs) [(raw + 40, raw + 44)] own ly' S' W' mem' md' k
(ajournal_init SEGS B STK _ ly S W regs mem md ch HPRE) HJ ltac:(lia) ltac:(lia)
ltac:(intros a (r & [<- | []] & Hr); left; exists (raw + 40, raw + 44); split; [left; reflexivity | exact Hr])) as HJ'.
rewrite app_nil_r in HJ'. exact HJ'.
Qed.
Lemma asep_head : forall ly S W mem md b c rest,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (b :: rest) -> In c rest -> zdisjoint (block_rng b) (block_rng c).
Proof.
intros ly S W mem md b c rest HAR HP Hc. destruct (in_split _ _ Hc) as (r1 & r2 & ->).
eapply (sep_blocks_perm SEGS B LAWS ly S W mem md b c (r1 ++ r2)); [exact HAR|].
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym. apply Permutation_middle.
Qed.
End q.
Lemma denot_sext32_rc : forall Ex n r, ew Ex n = Z_to_bv 64 r -> 0 <= r < 2 ^ 32 -> sext 64 (bv_extract 0 32 (ew Ex n)) = Z_to_bv 64 (rc_int r).
Proof.
intros Ex n r HE Hr. pose proof (U_sext32 Ex (SOff n 0) r (U_atom Ex n r HE ltac:(lia)) Hr) as U1.
unfold U in U1. cbn [sv_denot] in U1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in U1.
apply bv_eq. rewrite U1. rewrite Z_to_bv_unsigned. unfold bv_wrap, rc_int. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.ltb_spec r (2 ^ 31)); [rewrite Z.mod_small by lia; reflexivity|].
replace ((r - 2 ^ 32) mod 2 ^ 64) with ((r - 2 ^ 32 + 1 * 2 ^ 64) mod 2 ^ 64) by (rewrite Z_mod_plus_full; reflexivity). rewrite Z.mod_small by lia. lia.
Qed.
Lemma ra_pal_pow_of_loop : forall Kq s, 0 <= Kq <= 8 -> s <= 2 ^ Kq -> 2 ^ Kq < 2 * s -> YO07.pal_pow s = Z.max Kq 1.
Proof.
intros Kq s HK Hs1 Hs2. rewrite Z.max_comm. apply YI0j.pal_pow_class; [lia | | | exact Hs1].
- intros ->. change (2 ^ 0) with 1 in Hs1. lia.
- intros HK0. assert (2 ^ Kq = 2 * 2 ^ (Kq - 1)) by (replace Kq with (Kq - 1 + 1) at 1 by lia; rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia). lia.
Qed.
Lemma denot_ra_flagsL : forall Ex kq Kq, ew Ex kq = Z_to_bv 64 Kq -> 0 <= Kq <= 8 ->
zext 64 (bv_extract 0 8 (alu64 ALU_OR (alu64 ALU_ADD (alu64 ALU_ADD (alu64 ALU_AND (ew Ex kq) (Z_to_bv 64 255))
(alu64 ALU_SLTU (alu64 ALU_AND (ew Ex kq) (Z_to_bv 64 255)) (Z_to_bv 64 1))) (Z_to_bv 64 (-1))) (Z_to_bv 64 128)))
= Z_to_bv 64 (128 + (Z.max Kq 1 - 1)).
Proof.
intros Ex kq Kq HE HK. rewrite HE.
assert (C : Kq = 0 \/ Kq = 1 \/ Kq = 2 \/ Kq = 3 \/ Kq = 4 \/ Kq = 5 \/ Kq = 6 \/ Kq = 7 \/ Kq = 8) by lia.
destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; apply bv_eq; vm_compute; reflexivity.
Qed.
Lemma denot_ra_flagsL_b : forall Ex kq Kq, ew Ex kq = Z_to_bv 64 Kq -> 0 <= Kq <= 8 ->
zext 64 (bv_extract 0 8 (alu64 ALU_OR (alu64 ALU_ADD (alu64 ALU_ADD (ew Ex kq) (alu64 ALU_SLTU (ew Ex kq) (Z_to_bv 64 1))) (Z_to_bv 64 (-1))) (Z_to_bv 64 128)))
= Z_to_bv 64 (128 + (Z.max Kq 1 - 1)).
Proof.
intros Ex kq Kq HE HK. rewrite HE.
assert (C : Kq = 0 \/ Kq = 1 \/ Kq = 2 \/ Kq = 3 \/ Kq = 4 \/ Kq = 5 \/ Kq = 6 \/ Kq = 7 \/ Kq = 8) by lia.
destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; apply bv_eq; vm_compute; reflexivity.
Qed.
Lemma ra_icl_of_loop : forall Kq s, 0 <= Kq <= 8 -> s <= 2 ^ Kq -> (2 ^ Kq < 2 * s \/ Kq = 0) -> YO07.calcInitCodeLen s = Z.max 2 Kq + 1.
Proof.
intros Kq s HK Hs1 Hs2. apply YI0k.icl_class; [lia | | | exact Hs1].
- intros ->. change (2 ^ 0) with 1 in Hs1. lia.
- intros HK0. destruct Hs2 as [Hs2 | Hs2]; [|lia].
assert (2 ^ Kq = 2 * 2 ^ (Kq - 1)) by (replace Kq with (Kq - 1 + 1) at 1 by lia; rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia). lia.
Qed.
Lemma np2_aux_le_fuel : forall fuel n p, p <= YO07.np2_aux fuel n p <= p + Z.of_nat fuel.
Proof.
induction fuel as [|fuel IH]; intros n p; cbn [YO07.np2_aux]; [lia|].
destruct (Z.ltb _ _); [|lia]. pose proof (IH n (p + 1)). lia.
Qed.
Lemma rx_iclen_bounds : forall cx, 3 <= rx_iclen cx <= 18.
Proof.
intros cx. unfold rx_iclen, YO07.calcInitCodeLen, YO07.calcNextPower2Ex.
pose proof (np2_aux_le_fuel 17 (rx_ne cx) 0). cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H.
destruct (Z.ltb_spec (YO07.np2_aux 17 (rx_ne cx) 0) 3); lia.
Qed.
Lemma rx_idl_range : forall cx, 4 <= rx_idl cx <= 2 ^ 17.
Proof.
intros cx. unfold rx_idl. pose proof (rx_iclen_bounds cx).
split; [change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia | apply Z.pow_le_mono_r; lia].
Qed.
Section u.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis MLAW : ameter_laws MT.
Hypothesis HXN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> mo_malloc MT N + xn_lzw XN N idl + 2 * mo_free MT <= xn_rawadd XN N.
Hypothesis HXMN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> 0 <= xn_lzw XN N idl <= xm_lzw XN N idl.
Lemma xnr_nonneg : forall N, 1 <= N <= 100000000 -> 0 <= xn_rawadd XN N.
Proof.
intros N HN. pose proof (HXN N 2 HN ltac:(lia)). pose proof (HXMN N 2 HN ltac:(lia)).
pose proof (mo_malloc_nonneg MT MLAW N ltac:(lia)). pose proof (mo_free_nonneg MT MLAW). lia.
Qed.
End u.
Lemma rx_ne_noanim : forall cx, rx_ganim cx = false -> rx_ne cx = rx_nc cx.
Proof. intros cx H. unfold rx_ne. rewrite (num_eff_spec _ _ _ _ _ (rx_nc cx)) by reflexivity. rewrite H. reflexivity. Qed.
Lemma rx_ne_notrans : forall cx, YO07.flag (c_fattr cx) 1 = false -> rx_ne cx = rx_nc cx.
Proof. intros cx H. unfold rx_ne. rewrite (num_eff_spec _ _ _ _ _ (rx_nc cx)) by reflexivity. rewrite H, Bool.andb_false_r. reflexivity. Qed.
Lemma rx_ne_lt : forall cx, c_tidx cx < rx_nc cx -> rx_ne cx = rx_nc cx.
Proof.
intros cx H. unfold rx_ne. rewrite (num_eff_spec _ _ _ _ _ (rx_nc cx)) by reflexivity.
replace (rx_nc cx <=? c_tidx cx) with false by (symmetry; apply Z.leb_gt; exact H). rewrite Bool.andb_false_r. reflexivity.
Qed.
Lemma rx_ne_bump : forall cx, rx_ganim cx = true -> YO07.flag (c_fattr cx) 1 = true -> rx_nc cx <= c_tidx cx -> rx_ne cx = c_tidx cx + 1.
Proof.
intros cx H1 H2 H3. unfold rx_ne. rewrite (num_eff_spec _ _ _ _ _ (rx_nc cx)) by reflexivity. rewrite H1, H2.
replace (rx_nc cx <=? c_tidx cx) with true by (symmetry; apply Z.leb_le; exact H3). reflexivity.
Qed.
End l.
End d.
Ltac xwrap H := lazymatch type of H with ?T => change T with (xfacts T) in H end.
Ltac xunwrap H := unfold xfacts in H.
Ltac ra_preludeX :=
let LAWS := rnLAWS in let TL := rnTL in let B := lazymatch goal with L : AR_laws _ ?Bv |- _ => Bv end in
let cx := fresh "cx" in let xx := fresh "xx" in
intros cx xx E k ly3 S3 W3 ms3 md3 HBASE HEE HJ3 Hfrs3 HINV HS;
destruct xx as [pf Sg IMG LCT];
destruct cx as [ly S W regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h topv leftv delay slct disp tidx Nimg rest cid pos fpos wfn hw uar E0];
pose proof HBASE as HBASE0;
unfold ra_baseX in HBASE; unfold ra_EX, ra_E in HEE; red in HINV; unfold INV_0, INV_X, INV_D, INV_T0, INV_Tf, INV_L, INV_M, XV_FI, XV_F, XV_E, XV_D, XV1, XLZW_ok, XLZW_M in HINV;
unfold ra_vals, ra_F, ra_FL in HBASE, HEE;
cbn [x_pf x_Sg x_IMG x_LCT] in HBASE, HEE, HINV |- *;
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_raw c_g c_cfp c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx c_Nimg c_rest c_cid c_pos c_fpos c_wfn c_hw c_uar c_E0] in HBASE, HEE, HJ3, Hfrs3, HINV |- *;
destruct HBASE as (HPRE & Hal32 & Hctx & Hroom & HROD & H10 & H11 & (Hfin & Hcid0 & Hfal & Hflo & Hfhi & Hcal & HRA) & Hcfg & Hraw & Hsg
& Mgw & Mgf & Rctx & Mg80 & Hw & Hh & HnP & HnPN & HPerm & Hlct & Hev & Hlive & EE & EX & Usp & Rwfn & Rhw & WFNX & Huar
& E56 & Hpf0 & Hpf_rest & HSINK0 & HSmax & HIMG & HIMGlen & HLCT & HLCTsep & HMOK);
subst uar;
destruct HEE as ((AG & EXE & RF & E528 & E529 & HEI) & E56E);
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : TRAWADD_STK = 17040) by reflexivity;
assert (HEV : EV_RAWADD = 27) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
assert (E10 : ew E0 10 = Z_to_bv 64 raw) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10);
assert (E11 : ew E0 11 = Z_to_bv 64 cfp) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11);
assert (E2 : ew E0 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl));
pose proof (EX 0%nat ltac:(lia)) as E32; cbn [Nat.add nth] in E32;
pose proof (EXE 1%nat ltac:(lia)) as E33;
pose proof (EXE 2%nat ltac:(lia)) as E34;
pose proof (EXE 3%nat ltac:(lia)) as E35;
pose proof (EXE 4%nat ltac:(lia)) as E36;
pose proof (EXE 5%nat ltac:(lia)) as E37;
pose proof (EXE 6%nat ltac:(lia)) as E38;
pose proof (EXE 7%nat ltac:(lia)) as E39;
pose proof (EXE 8%nat ltac:(lia)) as E40;
pose proof (EXE 9%nat ltac:(lia)) as E41;
pose proof (EXE 10%nat ltac:(lia)) as E42;
pose proof (EXE 11%nat ltac:(lia)) as E43;
pose proof (EXE 12%nat ltac:(lia)) as E44;
pose proof (EXE 13%nat ltac:(lia)) as E45;
pose proof (EXE 14%nat ltac:(lia)) as E46;
pose proof (EXE 15%nat ltac:(lia)) as E47;
pose proof (EXE 16%nat ltac:(lia)) as E48;
pose proof (EXE 17%nat ltac:(lia)) as E49;
pose proof (EXE 18%nat ltac:(lia)) as E50;
pose proof (EXE 19%nat ltac:(lia)) as E51;
pose proof (EXE 20%nat ltac:(lia)) as E52;
pose proof (EXE 21%nat ltac:(lia)) as E53;
pose proof (EXE 22%nat ltac:(lia)) as E54;
pose proof (EXE 23%nat ltac:(lia)) as E55;
cbn [Nat.add nth] in E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50, E51, E52, E53, E54, E55; clear EXE;
let Hc' := fresh "Hc'" in
pose proof Hcfg as Hc'; cbn [obj_at LAY_RawFrameConfig] in Hc';
destruct Hc' as ([_ Rlct] & [_ Rimg] & [_ Rfattr] & [_ Rw] & [_ Rh] & [_ Rtop] & [_ Rleft] & [_ Rdelay] & [_ Rslct] & [_ Rdisp] & [_ Rtidx] & _);
cbn [fst snd N.to_nat Z.of_N] in Rlct, Rimg, Rfattr, Rw, Rh, Rtop, Rleft, Rdelay, Rslct, Rdisp, Rtidx;
change (2 ^ (8 * 8)) with (2 ^ 64) in Rlct, Rimg; change (2 ^ (8 * 4)) with (2 ^ 32) in Rfattr;
change (2 ^ (8 * 2)) with 65536 in Rw, Rh, Rtop, Rleft, Rdelay, Rslct; change (2 ^ (8 * 1)) with 256 in Rdisp, Rtidx;
let Hr' := fresh "Hr'" in
pose proof Hraw as Hr'; cbn [obj_at LAY_Raw LAY_RawConfig app] in Hr';
destruct Hr' as (_ & [_ Rg] & [_ Rgct] & [_ Rrattr] & [_ RWd] & [_ RHd] & [_ Rsgct] & [_ Rloops] & [_ Rrcur] & _);
cbn [fst snd N.to_nat Z.of_N] in Rg, Rgct, Rrattr, RWd, RHd, Rsgct, Rloops, Rrcur;
change (2 ^ (8 * 8)) with (2 ^ 64) in Rg, Rgct; change (2 ^ (8 * 4)) with (2 ^ 32) in Rrattr, Rrcur;
change (2 ^ (8 * 2)) with 65536 in RWd, RHd, Rsgct, Rloops;
assert (Hraw_in : In (raw, RAW_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity);
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity);
assert (Himg_in : In (img, Nimg) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; right; left; reflexivity);
destruct (al_blocks _ _ LAWS ly S W mem md raw RAW_SIZE HAR Hraw_in) as (Hr16 & Hr4096 & Hrceil & [Hrh Hrapp] & Hrpres & _);
pose proof (blk_off_imgP _ _ _ _ _ _ raw RAW_SIZE HAR Hraw_in) as Hrh_img;
change (req_size RAW_SIZE) with 48 in Hrceil, Hrpres, Hrh;
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _); pose proof (proj1 Hgh_ia) as Hgh;
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img;
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh;
assert (Hpf_in : In (pf, FILE_BLOCK) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; right; right; exact Hpf_rest);
destruct (al_blocks _ _ LAWS ly S W mem md pf FILE_BLOCK HAR Hpf_in) as (Hp16 & Hp4096 & Hpceil & Hp_ia & Hppres & _);
pose proof (blk_off_imgP _ _ _ _ _ _ pf FILE_BLOCK HAR Hpf_in) as Hph_img;
change (req_size FILE_BLOCK) with 1264 in Hpceil, Hppres, Hp_ia, Hph_img;
xwrap Hpf0; xwrap Hp16; xwrap HSmax; xwrap HIMGlen; xwrap HLCT; xwrap HLCTsep;
destruct (frames_bounds _ _ LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
pose proof (proj1 HJ3) as HAR3;
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _);
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia);
assert (Hfin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity);
assert (HfinS3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hfin);
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFapp_img;
destruct (frames_bounds _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img;
change (fs_frame_bytes 1) with 128 in *; change (128 / 8) with 16 in HFSpres3; rewrite !EFA3 in *;
set (F := frame_addr ly 1 fpos) in *; set (FL := flag_addr ly 1 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    ;
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl);
pose proof (sep_frames_pos _ _ LAWS ly3 S3 _ _ _ (1, fpos) (cid, pos) [] fl1 fl2 HAR3 ltac:(rewrite Hfrs3, Efl; reflexivity)) as HdFC;
unfold zdisjoint, frame_rng in HdFC; cbn [fst snd] in HdFC; change (fs_frame_bytes 1) with 128 in HdFC; rewrite !EFA3 in HdFC; fold F in HdFC; box HdFC;
clear fl1 fl2 Efl;
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview _ (w_H W3) (ms_mem ms3) a = aview _ (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let F1 := fresh "F1" in intros a Ha;
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia);
let Kgot3 := fresh "Kgot3" in let Kcell3 := fresh "Kcell3" in let Kguar3 := fresh "Kguar3" in let Kuar3 := fresh "Kuar3" in let Vgr3 := fresh "Vgr3" in
aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
img_factsA E; img_hull_factsA.
Ltac ra_blocks3X Hraw3 Hing3 Hpf3 :=
let LAWS := rnLAWS in
lazymatch goal with HAR3 : AR _ ?B ?ly3 ?S3 ?W3 ?m3 ?md3, HdFC : context [frame_addr _ ?cid ?pos] |- _ =>
lazymatch type of Hraw3 with In (?raw, _) _ => lazymatch type of Hing3 with In (?g, _) _ =>
lazymatch goal with Hfin3 : In (1, ?fpos) (frames S3), HfinS3 : In (cid, pos) (frames S3), EFA3 : forall c p, frame_addr ly3 c p = _ |- _ =>
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR3 Hraw3) as (_ & _ & _ & _ & Hrpres3 & _);
change (req_size RAW_SIZE) with 48 in Hrpres3;
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR3 Hing3) as (_ & _ & _ & _ & Hgpres3 & _);
change (req_size CGIF_SIZE) with 96 in Hgpres3;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ raw RAW_SIZE 1 fpos HAR3 Hraw3 Hfin3) as HdFR;
unfold zdisjoint in HdFR; cbn [fst snd] in HdFR; change (req_size RAW_SIZE) with 48 in HdFR; change (fs_frame_bytes 1) with 128 in HdFR; rewrite EFA3 in HdFR;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ raw RAW_SIZE cid pos HAR3 Hraw3 HfinS3) as HdRC;
unfold zdisjoint in HdRC; cbn [fst snd] in HdRC; change (req_size RAW_SIZE) with 48 in HdRC; rewrite EFA3 in HdRC;
pose proof (sep_blocks _ _ LAWS ly3 S3 _ _ _ g CGIF_SIZE raw RAW_SIZE HAR3 Hing3 Hraw3 ltac:(unfold CGIF_SIZE, RAW_SIZE; intros X; injection X; lia)) as HdRG;
unfold zdisjoint in HdRG; cbn [fst snd] in HdRG; change (req_size RAW_SIZE) with 48 in HdRG; change (req_size CGIF_SIZE) with 96 in HdRG;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ g CGIF_SIZE 1 fpos HAR3 Hing3 Hfin3) as HdFG;
unfold zdisjoint in HdFG; cbn [fst snd] in HdFG; change (req_size CGIF_SIZE) with 96 in HdFG; change (fs_frame_bytes 1) with 128 in HdFG; rewrite EFA3 in HdFG;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ g CGIF_SIZE cid pos HAR3 Hing3 HfinS3) as HdGC;
unfold zdisjoint in HdGC; cbn [fst snd] in HdGC; change (req_size CGIF_SIZE) with 96 in HdGC; rewrite EFA3 in HdGC;
box HdFR; box HdRC; box HdRG; box HdFG; box HdGC;
let HdPF := fresh "HdPF" in let HdPC := fresh "HdPC" in let HdPR := fresh "HdPR" in let HdPG := fresh "HdPG" in
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ _ FILE_BLOCK 1 fpos HAR3 Hpf3 Hfin3) as HdPF;
unfold zdisjoint in HdPF; cbn [fst snd] in HdPF; change (req_size FILE_BLOCK) with 1264 in HdPF; change (fs_frame_bytes 1) with 128 in HdPF; rewrite EFA3 in HdPF;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ _ FILE_BLOCK cid pos HAR3 Hpf3 HfinS3) as HdPC;
unfold zdisjoint in HdPC; cbn [fst snd] in HdPC; change (req_size FILE_BLOCK) with 1264 in HdPC; rewrite EFA3 in HdPC;
pose proof (sep_blocks _ _ LAWS ly3 S3 _ _ _ _ FILE_BLOCK raw RAW_SIZE HAR3 Hpf3 Hraw3 ltac:(unfold FILE_BLOCK, RAW_SIZE; intros X; injection X; lia)) as HdPR;
unfold zdisjoint in HdPR; cbn [fst snd] in HdPR; change (req_size RAW_SIZE) with 48 in HdPR; change (req_size FILE_BLOCK) with 1264 in HdPR;
pose proof (sep_blocks _ _ LAWS ly3 S3 _ _ _ _ FILE_BLOCK g CGIF_SIZE HAR3 Hpf3 Hing3 ltac:(unfold FILE_BLOCK, CGIF_SIZE; intros X; injection X; lia)) as HdPG;
unfold zdisjoint in HdPG; cbn [fst snd] in HdPG; change (req_size CGIF_SIZE) with 96 in HdPG; change (req_size FILE_BLOCK) with 1264 in HdPG;
lazymatch type of Hpf3 with In (?pf, _) _ =>
lazymatch goal with Hpceil : pf + 1264 <= alloc_ceiling, Hp4096 : 4096 <= pf, Hph_img : off_img pf 1264, Hceil : alloc_ceiling <= ly_stk_lo ?lyv, Hslo : ly_stk_lo ?lyv + TRAWADD_STK <= spZ ?regs,
Hflo : frame_addr _ cid pos <= ?cfp, Hfhi : ?cfp + 40 <= _, HF4096 : 4096 <= ?F, HFceil : ?F + 128 <= alloc_ceiling, HFhigh_img : off_img ?F 128,
HF8lo : 512 <= ?F / 8, HF8hi : ?F / 8 < 17592186044416, Hr4096 : 4096 <= raw, Hrceil : raw + 48 <= alloc_ceiling, Hrh_img : off_img raw (req_size RAW_SIZE),
Hg4096 : 4096 <= g, Hgceil : g + 96 <= alloc_ceiling, C1 : _ <= alloc_ceiling <= _, Hf4096 : 4096 <= frame_addr _ cid pos, FFS : TRAWADD_STK = 17040 |- _ =>
fold F in HdPF;
let XF := fresh "XF" in
assert (XF : xfacts (pf + 1264 <= alloc_ceiling /\ 4096 <= pf /\ alloc_ceiling + TRAWADD_STK <= spZ regs /\ TRAWADD_STK = 17040 /\
140735332483072 <= alloc_ceiling <= 140737479966720 /\ (pf + 1264 <= 65536 \/ 6270976 <= pf) /\
(pf + 1264 <= cfp \/ cfp + 40 <= pf) /\ 4096 <= cfp /\
(pf + 1264 <= F \/ F + 128 <= pf) /\ 4096 <= F /\ F + 128 <= alloc_ceiling /\ (F + 128 <= 65536 \/ 6270976 <= F) /\ 512 <= F / 8 < 17592186044416 /\
(pf + 1264 <= raw \/ raw + 48 <= pf) /\ 4096 <= raw /\ raw + 48 <= alloc_ceiling /\ (raw + 48 <= 65536 \/ 6270976 <= raw) /\
(pf + 1264 <= g \/ g + 96 <= pf) /\ 4096 <= g /\ g + 96 <= alloc_ceiling))
by (apply xfacts_i; unfold off_img in HFhigh_img, Hrh_img, Hph_img; change (req_size RAW_SIZE) with 48 in Hrh_img;
clear - Hpceil Hp4096 Hceil Hslo FFS C1 Hph_img HdPC Hflo Hfhi Hf4096 HdPF HF4096 HFceil HFhigh_img HF8lo HF8hi HdPR Hr4096 Hrceil Hrh_img HdPG Hg4096 Hgceil; lia);
clear HdPC HdPF HdPR HdPG Hpceil Hp4096 Hph_img; try (lazymatch goal with Hpia : in_app pf 1264 |- _ => change (in_app pf 1264) with (xfacts (in_app pf 1264)) in Hpia end) end end
end end end end.
Ltac ra_handX RC HS :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (ra_postX _ _ _ ?B ?cxv ?xxv) =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (RC cxv xxv Ev _ _ _ W3 ms3 md3);
[ lazymatch goal with H0 : ra_baseX _ _ _ _ _ _ _ |- _ => exact H0 end
| repeat (lazymatch goal with |- ra_EX _ _ (havoc _ _ _) => apply ra_EX_havoc; [clear; cbn; lia|] | |- ra_EX _ _ (ewset _ _ _) => apply ra_EX_ewset; [clear; cbn; lia|] end);
split; [| cbn [x_pf]; assumption];
unfold ra_E, ra_F, ra_FL; cbn [c_ly c_fpos c_E0 c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx];
split; [assumption|]; split; [eapply ra_vals_of; eassumption|]; repeat (split; [eassumption|]); eassumption
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; unfold INV_0, INV_X, INV_D, INV_T0, INV_Tf, INV_L, INV_M, XC, XB, XV_FI, XV_F, XV_E, XV_D, XV1, XMET, XLZW_ok, XLZW_M, rx_ganim;
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_raw c_g c_cfp c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx c_Nimg c_rest c_cid c_pos c_fpos c_wfn c_hw c_uar c_E0 x_pf x_Sg x_IMG x_LCT]
| exact HS ] | st_ok _ ?Ev _ _ =>
eapply (RC cxv xxv Ev _ _ _ W3 ms3 md3);
[ lazymatch goal with H0 : ra_baseX _ _ _ _ _ _ _ |- _ => exact H0 end
| repeat (lazymatch goal with |- ra_EX _ _ (havoc _ _ _) => apply ra_EX_havoc; [clear; cbn; lia|] | |- ra_EX _ _ (ewset _ _ _) => apply ra_EX_ewset; [clear; cbn; lia|] end);
split; [| cbn [x_pf]; assumption];
unfold ra_E, ra_F, ra_FL; cbn [c_ly c_fpos c_E0 c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx];
split; [assumption|]; split; [eapply ra_vals_of; eassumption|]; repeat (split; [eassumption|]); eassumption
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; unfold INV_0, INV_X, INV_D, INV_T0, INV_Tf, INV_L, INV_M, XC, XB, XV_FI, XV_F, XV_E, XV_D, XV1, XMET, XLZW_ok, XLZW_M, rx_ganim;
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_raw c_g c_cfp c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx c_Nimg c_rest c_cid c_pos c_fpos c_wfn c_hw c_uar c_E0 x_pf x_Sg x_IMG x_LCT]
| exact HS ]  end end.
Definition xbfacts (P : Prop) : Prop := P.
Lemma xbfacts_i : forall P : Prop, P -> xbfacts P. Proof. intros P H. exact H. Qed.
Ltac xbb_facts Hbb4 HAR4 Hfin4 EFA4 Hbb4096 Hbbceil Hbbh_ia HdBR XBB Hpf_in :=
let LAWS := rnLAWS in let Bv := rnB in
lazymatch type of Hbb4 with In (?bb, ?Lbb) (ablocks _ ?ly4 ?S4) =>
lazymatch type of Hpf_in with In (?pf, FILE_BLOCK) _ =>
lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _), Fv := frame_addr _ 1 ?fpos : Z, HPerm4 : Permutation (ablocks _ ly4 S4) ((bb, Lbb) :: ?restb) |- _ =>
lazymatch type of HdBR with ACai.boxed ?sepR =>
let HdBF := fresh "HdBF" in let HdBP := fresh "HdBP" in
pose proof (sep_block_frame _ _ LAWS ly4 S4 _ _ _ bb Lbb 1 fpos HAR4 Hbb4 Hfin4) as HdBF;
unfold zdisjoint in HdBF; cbn [fst snd] in HdBF; change (fs_frame_bytes 1) with 128 in HdBF; rewrite EFA4 in HdBF; fold Fv in HdBF;
pose proof (asep_head Bv LAWS ly4 S4 _ _ _ (bb, Lbb) (pf, FILE_BLOCK) restb HAR4 HPerm4
ltac:(first [exact Hpf_in | apply in_app_iff; left; exact Hpf_in | match goal with Eab : ablocks _ _ _ = ablocks _ _ _ |- _ => rewrite <- Eab; exact Hpf_in end
| match goal with Hr : In (pf, FILE_BLOCK) _ |- _ => solve [repeat (first [exact Hr | right])] end])) as HdBP;
unfold zdisjoint, block_rng in HdBP; cbn [fst snd] in HdBP; change (req_size FILE_BLOCK) with 1264 in HdBP;
let Hrqb := fresh "Hrqb" in
assert (Hrqb : req_size Lbb = Lbb)
by (first [ assumption | unfold req_size; destruct (Z.eqb_spec Lbb 0) as [Hz | Hz]; [exfalso | reflexivity];
match goal with H : 1 <= ?M <= Lbb |- _ => clear - H Hz; lia | H : 1 <= Lbb |- _ => clear - H Hz; lia | H : 0 < Lbb |- _ => clear - H Hz; lia end ]);
assert (XBB : xbfacts (4096 <= bb /\ bb + req_size Lbb <= alloc_ceiling /\ (bb + req_size Lbb <= 2147450880 \/ 17594333495296 <= bb) /\
sepR /\ (Fv + 128 <= bb \/ bb + req_size Lbb <= Fv) /\ (pf + 1264 <= bb \/ bb + req_size Lbb <= pf) /\ req_size Lbb = Lbb))
by (apply xbfacts_i; pose proof Hbbh_ia as Hia; unfold in_app, kLowShadowBeg, kHighMemBeg in Hia; unfold ACai.boxed in HdBR;
clear - Hbb4096 Hbbceil Hia HdBR HdBF HdBP Hrqb; unfold SB in *; lia);
clear Hrqb;
clear HdBF HdBP end end end end.
Ltac xblk_station HJc :=
repeat match goal with HG : garr8 ?sg (mrestrict (w_H ?W3) ?m3) ?bb ?L, XBB : xbfacts (4096 <= ?bb /\ _), HML : xfacts (Z.of_nat (length ?L) <= req_size ?Lbb) |- _ =>
lazymatch type of HJc with ajournal _ ?Bv _ _ _ ?lyc ?Sc W3 m3 _ _ ?ly4 ?S4 ?W4 ?mem4 _ _ =>
lazymatch goal with Hbb3 : In (bb, Lbb) (ablocks Bv lyc Sc) |- _ =>
let HG2 := fresh "HG" in
assert (HG2 : garr8 sg (mrestrict (w_H W4) mem4) bb L);
[ eapply (garr8_journal_block_x sg Bv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bb Lbb bb L HJc);
[ exact Hbb3 | first [exact Hbb3 | match goal with H : In (bb, Lbb) (ablocks Bv ly4 S4) |- _ => exact H end]
| clear; lia | clear - HML; unfold xfacts in HML; lia
| let a := fresh "a" in let Ha := fresh "Ha" in let HF := fresh "HF" in
intros a Ha HF; apply in_asink_fp in HF; clear - XBB HML Ha HF; unfold xbfacts in XBB; unfold xfacts in HML; unfold FILE_BLOCK in HF; lia
| exact HG ]
| clear HG; rename HG2 into HG ] end end
end.
Ltac xwinB Hrr :=
let Hx := fresh "Hx" in intros Hx;
lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _), XBB : xbfacts (4096 <= _ /\ _), HML : xfacts (Z.of_nat (length _) <= req_size _) |- _ =>
clear - XF XBB HML Hrr Hx; unfold xbfacts in XBB; unfold xfacts in XF, HML; unfold SB in *; lia end.
Ltac xwin_loopB AG Hin Hrr :=
lazymatch type of Hin with
| False => destruct Hin
| _ \/ _ => let Hq := fresh "Hq" in let Hin2 := fresh "Hin" in
destruct Hin as [Hq | Hin2]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; first [exfalso; clear - Hrr; lia | evalE_in AG Hrr; xwinB Hrr] | xwin_loopB AG Hin2 Hrr]
end.
Ltac xblk_stretch HFr HG :=
let made := match goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => constr:(false) | _ => constr:(true) end in
lazymatch type of HFr with frame_of ?Ef _ _ _ =>
lazymatch made with true => let AG0 := fresh "AG0" in assert (AG0 : forall n, (n < 33)%nat -> ew Ef n = ew Ef n) by (intros; reflexivity) | false => idtac end end;
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
lazymatch goal with |- SRr _ _ (mkCfg ?msn _) _ =>
lazymatch type of HG with garr8 ?sg (mrestrict (w_H ?Wv) ?mo) ?bb ?L =>
let UNB := fresh "UNB" in let HG2 := fresh "HG" in
pose proof (kept_of_frame (segs:=sg) _ _ _ _ _ (fun x => ~ (bb <= x < bb + Z.of_nat (length L))) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
intros b wlo whi a Hin Hrr; vm_compute in Hin; xwin_loopB AG Hin Hrr)) as UNB;
cbn beta in UNB;
assert (HG2 : garr8 sg (mrestrict (w_H Wv) (ms_mem msn)) bb L);
[ apply (garr8_aview_kept sg (w_H Wv) (w_H Wv) mo (ms_mem msn) bb L); [| exact HG];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [ms_mem]; apply UNB;
[ lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _), XBB : xbfacts (4096 <= _ /\ _), HML : xfacts (Z.of_nat (length _) <= req_size _) |- _ => clear - XF XBB HML Ha; unfold xbfacts in XBB; unfold xfacts in XF, HML; lia end
| let Hn := fresh "Hn" in intros Hn; exact (Hn Ha) ]
| clear UNB HG; rename HG2 into HG; lazymatch made with true => clear AG | false => idtac end ] end end.
Ltac xbb_intro HPerm3 HLZ :=
let LAWS := rnLAWS in let Bv := rnB in let XBB := fresh "XBB" in let HML := fresh "HML" in
lazymatch type of HPerm3 with Permutation (ablocks _ ?ly3 ?S3) ((?bb, ?Lbb) :: ablocks _ ?ly ?S) =>
lazymatch goal with HAR3 : AR _ Bv ly3 S3 ?W3 ?m3 ?md3, Hfin3 : In (1, ?fpos) (frames S3), EFA3 : forall c p, frame_addr ly3 c p = frame_addr ly c p,
Hraw_in : In (?raw, RAW_SIZE) (ablocks Bv ly S), Hpf_in : In (?pf, FILE_BLOCK) (ablocks Bv ly S), E1059 : ew ?Ev 1059 = Z_to_bv 64 bb, E1060 : ew ?Ev 1060 = Z_to_bv 64 (?M mod 2 ^ 32), HM : 1 <= ?M <= Lbb |- _ =>
let Hbb3 := fresh "Hbb3" in let Hbb16 := fresh "Hbb16" in let Hbb4096' := fresh "Hbb4096'" in let Hbbceil := fresh "Hbbceil" in
let Hbbh_ia := fresh "Hbbh_ia" in let Hbbpres := fresh "Hbbpres3" in let HLbbmax := fresh "HLbbmax" in let HdBR := fresh "HdBR" in
assert (Hbb3 : In (bb, Lbb) (ablocks Bv ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; left; reflexivity);
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR3 Hbb3) as (Hbb16 & Hbb4096' & Hbbceil & Hbbh_ia & Hbbpres & _ & HLbbmax);
pose proof (asep_head Bv LAWS ly3 S3 _ _ _ (bb, Lbb) (raw, RAW_SIZE) _ HAR3 HPerm3 Hraw_in) as HdBR;
unfold zdisjoint, block_rng in HdBR; cbn [fst snd] in HdBR; change (req_size RAW_SIZE) with 48 in HdBR;
ACai.box HdBR;
xbb_facts Hbb3 HAR3 Hfin3 EFA3 Hbb4096' Hbbceil Hbbh_ia HdBR XBB Hpf_in;
let out := fresh "out" in let Hls := fresh "Hls" in let HGout := fresh "HGout" in let HMo := fresh "HMo" in
let HM16 := fresh "HM16" in
destruct HLZ as (out & Hls & HGout & HMo & HM16); cbn [c_w c_h] in HM16;
rewrite E1059, unsigned_lit_small in HGout by (let Q := fresh "Q" in pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as Q; lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ => clear - Hbb4096' Hbbceil XF Q; unfold xfacts in XF; lia end);
rewrite E1060, unsigned_lit_small in HMo by (clear; pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)); lia);
rewrite Z.mod_small in HMo by (clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia);
assert (HML : xfacts (Z.of_nat (length out) <= req_size Lbb)) by (let Q := fresh "Q" in apply xfacts_i; pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as Q; clear - HMo HM Q; lia);
clear Hbb16 Hbbpres end end.
Ltac mresX Hnz Ebl HK Hres :=
lazymatch type of HK with acall_kept ?sg ?Bq ?lyc ?Sc ?Wc ?memT ?W2 ?mem2 ?slo ?shi (fun a => ?res <= a < _) =>
lazymatch type of Ebl with ablocks _ ?ly ?S = _ =>
pose proof (@or_intror (res = 0 /\ ablocks Bq ly S = ablocks Bq lyc Sc /\ acall_kept sg Bq lyc Sc Wc memT W2 mem2 slo shi (fun _ => False)) _
(conj Hnz (conj Ebl HK))) as Hres end end.
Ltac xwinR Hrr :=
let Hx := fresh "Hx" in intros Hx;
first [ lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ => clear - XF Hrr Hx; unfold xfacts in XF; unfold SB in *; lia end
| lazymatch goal with Hno : forall x, ?r <= x < ?r + 48 -> ~ aowned _ _ _ x |- _ =>
lazymatch goal with Hown : aowned _ _ _ ?fl |- _ =>
let av := lazymatch type of Hx with _ <= ?a < _ => a end in
apply (Hno _ Hx); replace fl with av in Hown by (clear - Hrr; lia); exact Hown end end ].
Ltac xwin_loopR AG Hin Hrr :=
lazymatch type of Hin with
| False => destruct Hin
| _ \/ _ => let Hq := fresh "Hq" in let Hin2 := fresh "Hin" in
destruct Hin as [Hq | Hin2]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; first [exfalso; clear - Hrr; lia | evalE_in AG Hrr; xwinR Hrr] | xwin_loopR AG Hin2 Hrr]
end.
Ltac xval_stretch HFr V :=
let made := match goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => constr:(false) | _ => constr:(true) end in
lazymatch type of HFr with frame_of ?Ef _ _ _ =>
lazymatch made with true => let AG0 := fresh "AG0" in assert (AG0 : forall n, (n < 33)%nat -> ew Ef n = ew Ef n) by (intros; reflexivity) | false => idtac end end;
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
lazymatch goal with |- SRr _ _ (mkCfg ?msn _) _ =>
lazymatch type of V with val_mem ?sg (mrestrict (w_H ?Wv) ?mo) ?av ?n ?v =>
let UNR := fresh "UNR" in let V2 := fresh "V" in
pose proof (kept_of_frame (segs:=sg) _ _ _ _ _ (fun x => ~ (av <= x < av + Z.of_nat n)) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
intros b wlo whi a Hin Hrr; vm_compute in Hin; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; xwin_loopR AG Hin Hrr)) as UNR;
cbn beta in UNR;
assert (V2 : val_mem sg (mrestrict (w_H Wv) (ms_mem msn)) av n v);
[ apply (val_mem_kept sg _ _ _ _ av n v); [| exact V];
let kk := fresh "kk" in let Hkk := fresh "Hkk" in intros kk Hkk; cbn [ms_mem]; apply UNR;
[ lazymatch goal with XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ => clear - XF Hkk; unfold xfacts in XF; lia end
| let Hn := fresh "Hn" in intros Hn; apply Hn; clear - Hkk; lia ]
| clear UNR V; rename V2 into V; lazymatch made with true => clear AG | false => idtac end ] end end.
Ltac exitRAX RET RUNF HS HJx AG fpos F cfgp g E516 E517 Hfin HfinS HingX EE Hra HEV EFA EFL :=
let HFLpres' := fresh "HFLpres'" in let HFLown := fresh "HFLown'" in let HFLrng := fresh "HFLrng'" in
let HFpres' := fresh "HFpres'" in let HFSpres' := fresh "HFSpres'" in
let HCpres' := fresh "HCpres'" in let HGpres' := fresh "HGpres'" in
let HnoG := fresh "HnoG" in let HnoC := fresh "HnoC" in let HnoF := fresh "HnoF" in
let HFLni := fresh "HFLni" in let HnoP := fresh "HnoP" in let HPp := fresh "HPp" in
let FFL := rnFFL in let LAWS := rnLAWS in destruct (FFL _ _ _ _ _ 1 fpos (proj1 HJx) Hfin) as (HFLpres' & HFLown & HFLrng); rewrite ?EFL in HFLpres'; rewrite ?EFL in HFLown; rewrite ?EFL in HFLrng; fold F in HFLrng;
pose proof (proj2 (proj1 HFLrng)) as HFLni;
try (lazymatch goal with FLv := flag_addr _ 1 _ |- _ => fold FLv in HFLown; fold FLv in HFLni end);
lazymatch type of HFLown with aowned ?Bv ?lyx ?Sx _ =>
lazymatch goal with Hinf : In (?pfv, FILE_BLOCK) (ablocks Bv lyx Sx) |- _ =>
destruct (al_blocks _ _ LAWS _ _ _ _ _ pfv FILE_BLOCK (proj1 HJx) Hinf) as (_ & _ & _ & _ & HPp & _); change (req_size FILE_BLOCK) with 1264 in HPp;
assert (HnoP : forall x, pfv <= x < pfv + 1264 -> ~ aowned Bv lyx Sx x) by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; exact (proj2 (HPp x Hx))); clear HPp end end;
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJx) Hfin) as (_ & _ & HFpres' & HFSpres'); change (fs_frame_bytes 1) with 128 in HFpres', HFSpres';
change (128 / 8) with 16 in HFSpres'; rewrite ?EFA in HFpres'; rewrite ?EFA in HFSpres'; fold F in HFpres', HFSpres';
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ (proj1 HJx) HfinS) as (_ & _ & HCpres' & _); rewrite ?EFA in HCpres';
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE (proj1 HJx) HingX) as (_ & _ & _ & _ & HGpres' & _); change (req_size CGIF_SIZE) with 96 in HGpres';
lazymatch type of HGpres' with forall a, _ -> _ /\ ~ aowned ?B ?lyx ?Sx a =>
assert (HnoG : forall a, g <= a < g + 96 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HGpres' a Ha)));
assert (HnoC : forall a, cfgp <= a < cfgp + 40 -> ~ aowned B lyx Sx a) by (intros a Ha; apply (fun H => proj2 (HCpres' a H)); lia);
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HFpres' a Ha)));
try (match goal with Hin : In (?r, RAW_SIZE) (ablocks _ lyx Sx) |- _ =>
let HRp := fresh "HRp" in let HnoR := fresh "HnoR" in
destruct (al_blocks _ _ LAWS _ _ _ _ _ r RAW_SIZE (proj1 HJx) Hin) as (_ & _ & _ & _ & HRp & _); change (req_size RAW_SIZE) with 48 in HRp;
assert (HnoR : forall a, r <= a < r + 48 -> ~ aowned B lyx Sx a) by (intros a Ha; exact (proj2 (HRp a Ha))); clear HRp end) end;
fs_rwA HS E517 HFSpres';
add_flag_regionA HS AG E516 HFLpres' HFLrng HFLown HnoG HnoC HnoF;
paj_run_flag_sh RUNF HS HJx; [lia | wrangeRA AG fpos F EFA EFL | flag0A E516 EFL |];
(let HFr := lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => H end in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in
xsink_stretch HFr HSINK;
try (lazymatch goal with V : val_mem _ _ (_ + 40) 4 _ |- _ => xval_stretch HFr V end));
let R1 := fresh "R1" in let R10 := fresh "R10" in
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
let mat' := fresh "mat'" in intros mat'; unfold ra_postX, ra_post, apost_base;
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_raw c_g c_cfp c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx c_Nimg c_rest c_cid c_pos c_fpos c_wfn c_hw c_uar c_E0 x_pf x_Sg x_IMG x_LCT];
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end;
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|];
split; [cbn [ms_mem]; eapply (ajournal_mono_k _ _); [apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJx | rewrite HEV; lia]|];
split; [apply aregs_preserved_eqs; creg HS AG EE|];
rewrite R10.
Ltac xlift_exit HJ3 HSINK0 Hpf_in :=
let LAWS := rnLAWS in
lazymatch goal with AIL : asink_img_laws _ _ ?Kv, HPRE : afn_pre _ _ _ _ _ _ ?regs _ _ _, XF : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ =>
lazymatch type of HJ3 with ajournal _ ?Bv ?STK _ [(?raw + 40, _)] _ _ _ _ _ ?own ?ly2 ?S2 ?W2 ?mem2 ?md2 ?k =>
let H := fresh "HL" in let Hpf3' := fresh "Hpf3'" in
destruct (xlift_journal Bv LAWS Kv AIL STK _ _ _ regs _ _ _ raw _ own ly2 S2 W2 mem2 md2 k _ HPRE HJ3 Hpf_in
ltac:(clear - XF; unfold xfacts in XF; lia) ltac:(clear - XF; unfold xfacts in XF; lia) HSINK0) as (H & Hpf3' & HSINK);
clear HJ3; rename H into HJ3 end end.
Ltac oblFAX HJx HE10 HE35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 11 ?c)) ?len =>
lazymatch type of HE10 with _ = Z_to_bv 64 ?cfgp =>
first [ rewrite (U_atom_off Ex 11 cfgp c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia | lia]
| rewrite (U_atom Ex 11 cfgp); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE10 | lia] ];
eapply (obl_of_range _ _ _ Ex (SOff 40 0) _ len cfgp 40);
[ let L := rnLAWS in eapply (range_addressable_entry_frame _ _ L); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| first
[ let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; exfalso; exact (inFP_nil x Hx)
| lazymatch goal with Hr : ?raw + req_size RAW_SIZE <= kLowShadowBeg \/ _, Hia : xfacts (in_app ?pf 1264) |- forall x, inFP ((?raw + 40, ?raw + 44) :: asink_fp ?pf) x -> _ =>
let x := fresh "x" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hxr := fresh "Hxr" in
intros x (rg & [<- | Hrg] & Hxr);
[ cbn [fst snd] in Hxr; clear - Hr Hxr; change (req_size RAW_SIZE) with 48 in Hr;
let C2 := fresh "C2" in let C3 := fresh "C3" in
pose proof asan_consts as (_ & C2 & C3 & _ & _); unfold ASAN_CEIL in Hr; rewrite C2; rewrite C3 in Hr; unfold kLowShadowBeg in *; lia
| let Hia' := fresh "Hia'" in pose proof Hia as Hia'; unfold xfacts in Hia'; exact (asink_fp_off_shadow pf x Hia' (ex_intro _ rg (conj Hrg Hxr))) ]
end
| lazymatch goal with Hr : ?raw + req_size RAW_SIZE <= kLowShadowBeg \/ _ |- forall x, inFP [(?raw + 40, ?raw + 44)] x -> _ =>
let x := fresh "x" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hxr := fresh "Hxr" in
intros x (rg & [<- | []] & Hxr); cbn [fst snd] in Hxr; clear - Hr Hxr; change (req_size RAW_SIZE) with 48 in Hr;
let C2 := fresh "C2" in let C3 := fresh "C3" in
pose proof asan_consts as (_ & C2 & C3 & _ & _); unfold ASAN_CEIL in Hr; rewrite C2; rewrite C3 in Hr; unfold kLowShadowBeg in *; lia
end ]
| exact HAR | exact HRA]
| rewrite (U_atom Ex 40 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE35 | unfold SB; lia]
| lia | lia ] end end.
Ltac xk1 HXK EK HK1r HK1v :=
lazymatch type of EK with ew _ 662 = Z_to_bv 64 ?K1 =>
lazymatch goal with HXC : XC ?cxv |- _ =>
lazymatch type of HXK with ?sl <> 0 -> _ =>
assert (HK1v : sl <> 0 -> K1 = YO07.pal_pow sl)
by (let Hne := fresh "Hne" in let Q := fresh "Q" in let R := fresh "R" in let C := fresh "C" in
intros Hne; pose proof (HXK Hne) as Q; rewrite EK in Q; apply (f_equal bv_unsigned) in Q;
pose proof HXC as C; unfold XC in C; cbn [c_slct] in C;
pose proof (rx_pal_pow_range sl ltac:(clear - C; lia)) as R;
rewrite !unsigned_lit_small in Q by (clear - HK1r R; lia); exact Q);
clear HXK; xwrap HK1v end end end.
Lemma denot_and1_lbu : forall Ex n r, ew Ex n = Z_to_bv 64 r -> 0 <= r < 2 ^ 64 ->
sv_denot Ex (SAlu ALU_AND (SExt false 8 (SOff n 0)) (SLit 1)) = Z_to_bv 64 (Z.land (r mod 2 ^ 8) 1).
Proof.
intros Ex n r HE Hr. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SExt, U_SLit.
rewrite (U_atom Ex n r HE Hr). change (2 ^ Z.of_N 8) with (2 ^ 8).
pose proof (Z.mod_pos_bound r (2 ^ 8) ltac:(lia)) as Hm.
rewrite (zcanon_id (r mod 2 ^ 8)) by (unfold M64; lia). rewrite (zcanon_id 1) by (unfold M64; lia).
apply zcanon_id. unfold M64. pose proof (Z_land_upper (r mod 2 ^ 8) 1 ltac:(lia)). lia.
Qed.
Lemma denot_and1 : forall Ex n r, ew Ex n = Z_to_bv 64 r -> 0 <= r < 2 ^ 64 ->
sv_denot Ex (SAlu ALU_AND (SOff n 0) (SLit 1)) = Z_to_bv 64 (Z.land r 1).
Proof.
intros Ex n r HE Hr. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom Ex n r HE Hr). rewrite (zcanon_id 1) by (unfold M64; lia).
apply zcanon_id. unfold M64. pose proof (Z_land_upper r 1 ltac:(lia)). lia.
Qed.
Ltac xbit1 Hc En Rr Hb :=
lazymatch type of En with ew _ ?n = Z_to_bv 64 ?r =>
lazymatch type of Hc with branch_taken BC_EQ _ _ = ?b =>
let HcX := fresh "HcX" in
pose proof Hc as HcX; unfold branch_taken in HcX;
first [ erewrite (denot_and1_lbu _ n r) in HcX by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En | clear - Rr; lia]);
rewrite YI0k.land_low8_1 in HcX by (clear - Rr; lia)
| erewrite (denot_and1 _ n r) in HcX by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En | clear - Rr; lia]) ];
cbn [sv_denot] in HcX;
rewrite bv_eqb_unsigned, !unsigned_lit_small in HcX by (first [clear - Rr; pose proof (Z_land_upper r 1 ltac:(lia)); lia | clear; lia]);
pose proof HcX as Hb; clear HcX; xwrap Hb end end.
Ltac xltu Hc Ea Eb Hr :=
let HcX := fresh "HcX" in
pose proof Hc as HcX; unfold branch_taken in HcX; rewrite bv_ltu_unsigned in HcX; cbn [sv_denot] in HcX;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in HcX; rewrite ?ew_ewset_other in HcX by lia;
rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned in HcX; rewrite Ea, Eb in HcX; rewrite !unsigned_lit_small in HcX by lia;
pose proof HcX as Hr; clear HcX; xwrap Hr.
Ltac xnc E660 Hnc Rnc :=
let ncn := fresh "nc" in
lazymatch type of E660 with _ = Z_to_bv 64 ?v => remember v as ncn eqn:Hnc in E660 end;
lazymatch goal with HXC : XC _, Hsg : ?sg <= 256, Rsgct : 0 <= ?sg < _ |- _ =>
assert (Rnc : 0 <= ncn <= 256)
by (let C := fresh "C" in rewrite Hnc; unfold rx_nc; cbn [c_slct c_sgct]; pose proof HXC as C; unfold XC in C; cbn [c_slct] in C;
destruct (_ =? 0); clear - C Hsg Rsgct; lia) end.
Ltac xne E710 Hne Rne :=
let nen := fresh "ne" in
lazymatch type of E710 with _ = Z_to_bv 64 ?v => remember v as nen eqn:Hne in E710 end;
lazymatch goal with F251 : 0 <= bv_unsigned (ew _ 710) <= 256 /\ _ |- _ =>
assert (Rne : 0 <= nen <= 256)
by (let C := fresh "C" in pose proof (proj1 F251) as C; rewrite E710 in C;
rewrite unsigned_lit_small in C; [exact C|];
rewrite Hne; unfold rx_ne, num_eff, rx_nc; cbn [c_slct c_sgct c_tidx c_fattr c_rattr];
lazymatch goal with HXC : XC _, Hsg : ?sg <= 256, Rsgct : 0 <= ?sg < _, Rtidx : 0 <= ?ti < 256 |- _ =>
let C2 := fresh "C2" in pose proof HXC as C2; unfold XC in C2; cbn [c_slct] in C2;
repeat (destruct (_ =? 0)); cbn [negb]; destruct (_ && _); clear - C2 Hsg Rsgct Rtidx; lia end) end.
Lemma denot_and2 : forall Ex n r, ew Ex n = Z_to_bv 64 r -> 0 <= r < 2 ^ 64 ->
sv_denot Ex (SAlu ALU_AND (SOff n 0) (SLit 2)) = Z_to_bv 64 (Z.land r 2).
Proof.
intros Ex n r HE Hr. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom Ex n r HE Hr). rewrite (zcanon_id 2) by (unfold M64; lia).
apply zcanon_id. unfold M64. pose proof (Z_land_upper r 2 ltac:(lia)). lia.
Qed.
Lemma land1_bit_t : forall x, 0 <= x -> Z.land x 1 = x mod 2.
Proof. intros x Hx. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma mod2_odd_t : forall x, x mod 2 = Z.b2z (Z.odd x).
Proof. intros x. rewrite Zmod_odd. destruct (Z.odd x); reflexivity. Qed.
Lemma flag1_odd_t : forall x, 0 <= x -> YO07.flag x 1 = Z.odd x.
Proof. intros x Hx. unfold YO07.flag. rewrite land1_bit_t, mod2_odd_t by lia. destruct (Z.odd x); reflexivity. Qed.
Lemma denot_or_and1_t : forall E a b ra rb, ew E a = Z_to_bv 64 ra -> ew E b = Z_to_bv 64 rb -> 0 <= ra < 2 ^ 32 -> 0 <= rb < 2 ^ 32 ->
sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SExt true 32 (SOff a 0)) (SExt true 32 (SOff b 0))) (SLit 1))
= Z_to_bv 64 (Z.b2z (YO07.flag ra 1 || YO07.flag rb 1)).
Proof.
intros E a b ra rb Ha Hb Hra Hrb. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_sext32 E (SOff a 0) ra (U_atom E a ra Ha ltac:(lia)) Hra). rewrite (U_sext32 E (SOff b 0) rb (U_atom E b rb Hb ltac:(lia)) Hrb).
set (va := if ra <? 2 ^ 31 then ra else ra - 2 ^ 32 + 2 ^ 64). set (vb := if rb <? 2 ^ 31 then rb else rb - 2 ^ 32 + 2 ^ 64).
assert (Hva : 0 <= va /\ Z.odd va = Z.odd ra).
{ subst va. destruct (Z.ltb_spec ra (2 ^ 31)); [split; [lia | reflexivity]|]. split; [lia|].
replace (ra - 2 ^ 32 + 2 ^ 64) with (ra + 2 * (2 ^ 63 - 2 ^ 31)) by lia. rewrite Z.odd_add_mul_2. reflexivity. }
assert (Hvb : 0 <= vb /\ Z.odd vb = Z.odd rb).
{ subst vb. destruct (Z.ltb_spec rb (2 ^ 31)); [split; [lia | reflexivity]|]. split; [lia|].
replace (rb - 2 ^ 32 + 2 ^ 64) with (rb + 2 * (2 ^ 63 - 2 ^ 31)) by lia. rewrite Z.odd_add_mul_2. reflexivity. }
rewrite (zcanon_id 1) by (unfold M64; lia).
assert (Hz : 0 <= zcanon (Z.lor va vb)) by (apply zcanon_range || (unfold zcanon, M64; apply Z.mod_pos_bound; lia)).
rewrite (land1_bit_t _ Hz). rewrite mod2_odd_t.
assert (Ho : Z.odd (zcanon (Z.lor va vb)) = Z.odd (Z.lor va vb)).
{ unfold zcanon, M64. rewrite <- !Z.bit0_odd. rewrite <- (Z.mod_pow2_bits_low (Z.lor va vb) 64 0) by lia. reflexivity. }
rewrite Ho. rewrite <- Z.bit0_odd, Z.lor_spec, !Z.bit0_odd, (proj2 Hva), (proj2 Hvb), <- !flag1_odd_t by lia.
rewrite Bool.orb_comm. apply zcanon_id. unfold M64. destruct (_ || _); cbn; lia.
Qed.
Lemma denot_and1_sw : forall Ex n r, ew Ex n = Z_to_bv 64 r -> 0 <= r < 2 ^ 32 ->
sv_denot Ex (SAlu ALU_AND (SExt true 32 (SOff n 0)) (SLit 1)) = Z_to_bv 64 (Z.land r 1).
Proof.
intros Ex n r HE Hr. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_sext32 Ex (SOff n 0) r (U_atom Ex n r HE ltac:(lia)) Hr).
rewrite (zcanon_id 1) by (unfold M64; lia).
rewrite !land1_bit_t by (destruct (Z.ltb_spec r (2 ^ 31)); lia).
destruct (Z.ltb_spec r (2 ^ 31)).
- apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound r 2 ltac:(lia)). lia.
- replace (r - 2 ^ 32 + 2 ^ 64) with (r + (2 ^ 63 - 2 ^ 31) * 2) by lia. rewrite Z_mod_plus_full.
apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound r 2 ltac:(lia)). lia.
Qed.
Ltac xbit2 Hc En Rr HIL :=
lazymatch type of En with ew _ ?n = Z_to_bv 64 ?r =>
lazymatch type of Hc with branch_taken BC_NE _ _ = ?b =>
let HcX := fresh "HcX" in
pose proof Hc as HcX; unfold branch_taken in HcX;
erewrite (denot_and2 _ n r) in HcX by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En | clear - Rr; lia]);
cbn [sv_denot] in HcX;
rewrite bv_eqb_unsigned, !unsigned_lit_small in HcX by (first [clear - Rr; pose proof (Z_land_upper r 2 ltac:(lia)); lia | clear; lia]);
assert (HIL : YO07.flag r 2 = b) by (unfold YO07.flag; exact HcX); clear HcX end end.
Ltac xnums_for Fidl QM QN QMN :=
lazymatch goal with HXM : forall N0 idl0, _ -> _ -> mo_malloc ?MT N0 + xm_lzw ?XN N0 idl0 + _ <= _ |- _ =>
lazymatch goal with HXN : forall N0 idl0, _ -> _ -> mo_malloc MT N0 + xn_lzw XN N0 idl0 + _ <= _ |- _ =>
lazymatch goal with HXMN : forall N0 idl0, _ -> _ -> 0 <= xn_lzw XN N0 idl0 <= _ |- _ =>
lazymatch goal with HnP : ?wv * ?hv <= 100000000, Hw : 1 <= ?wv, Hh : 1 <= ?hv |- _ =>
let idv := lazymatch type of Fidl with 4 <= ?i <= 256 => i | 4 <= ?i <= 256 /\ _ => i end in
pose proof (HXM (wv * hv) idv ltac:(clear - HnP Hw Hh; nia) ltac:(clear - Fidl; lia)) as QM;
pose proof (HXN (wv * hv) idv ltac:(clear - HnP Hw Hh; nia) ltac:(clear - Fidl; lia)) as QN;
pose proof (HXMN (wv * hv) idv ltac:(clear - HnP Hw Hh; nia) ltac:(clear - Fidl; lia)) as QMN
end end end end.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma val_mem4_inj : forall segs (m : word -> option byte) a v v',
val_mem segs m a 4 v -> val_mem segs m a 4 v' -> 0 <= v < 2 ^ 32 -> 0 <= v' < 2 ^ 32 -> v = v'.
Proof.
intros segs m a v v' H H' R R'.
assert (E : forall k, (k < 4)%nat -> Z.shiftr v (8 * Z.of_nat k) mod 256 = Z.shiftr v' (8 * Z.of_nat k) mod 256).
{ intros k Hk. pose proof (H k Hk) as B. rewrite (H' k Hk) in B.
rewrite (le_byte_small v 4 k R Hk), (le_byte_small v' 4 k R' Hk) in B.
apply (f_equal (option_map (@bv_unsigned 8))) in B. cbn [option_map] in B. rewrite !Z_to_bv_unsigned in B.
unfold bv_wrap in B. change (bv_modulus 8) with 256 in B. injection B as B. symmetry. exact B. }
pose proof (E 0%nat ltac:(lia)) as E0. pose proof (E 1%nat ltac:(lia)) as E1. pose proof (E 2%nat ltac:(lia)) as E2. pose proof (E 3%nat ltac:(lia)) as E3.
cbn [Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ] in E0, E1, E2, E3. rewrite !Z.shiftr_div_pow2 in E0, E1, E2, E3 by lia.
change (2 ^ 0) with 1 in E0. change (2 ^ 8) with 256 in E1. change (2 ^ 16) with 65536 in E2. change (2 ^ 24) with 16777216 in E3.
rewrite !Z.div_1_r in E0. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma val_mem8_inj : forall segs H (mem : word -> option byte) a v v',
val_mem segs (mrestrict H mem) a 8 v -> val_mem segs (mrestrict H mem) a 8 v' -> 0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
intros segs H mem a v v' Hv Hv' R R'.
pose proof (rdword_of_val_mem segs H mem a v Hv R) as A. rewrite (rdword_of_val_mem segs H mem a v' Hv' R') in A. injection A as A. symmetry. exact A.
Qed.
Fixpoint byte_chunks (off : Z) (bs : list Z) : list YP09.chunk :=
match bs with [] => [] | b :: t => YP09.mkChunk off (CVal 1 (SLit b)) :: byte_chunks (off + 1) t end.
Fixpoint split_chunk (off : Z) (bs : list Z) (cs : list YP09.chunk) : list YP09.chunk :=
match cs with
| [] => []
| c :: t => if Z.eqb (YP09.c_off c) off then byte_chunks off bs ++ t else c :: split_chunk off bs t
end.
Lemma range_addressable_zero8' : forall (rd : Z -> option Z) Bs p,
rd (shadow_of_addr Bs p) = Some 0 -> p mod 8 = 0 -> range_addressable rd Bs p 8.
Proof.
intros rd Bs p Hz Hp. apply zero_shadow_range; [exact Hp | reflexivity |].
intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia. rewrite Z.add_0_r. exact Hz.
Qed.
Section z.
Context {segs : list Segment}.
Lemma val_mem8_byte : forall (m : word -> option byte) a v (i : nat), val_mem segs m a 8 v -> (i < 8)%nat ->
val_mem segs m (a + Z.of_nat i) 1 (YO0f.le_byte v 8 i).
Proof.
intros m a v i Hv Hi k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (Hv i Hi). f_equal. f_equal.
unfold YO0f.le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. change (2 ^ (8 * 1)) with 256.
rewrite Z.mod_mod by lia. symmetry. apply Z.mod_mod. lia.
Qed.
End z.
Ltac xidx_reg_off rs b off :=
lazymatch rs with
| YP09.mkRegion (Some b) ?lo ?hi _ _ _ :: ?rs' =>
let inb := eval vm_compute in (andb (Z.leb lo off) (Z.ltb off hi)) in
lazymatch inb with true => constr:(0%nat) | false => let i := xidx_reg_off rs' b off in constr:(S i) end
| _ :: ?rs' => let i := xidx_reg_off rs' b off in constr:(S i)
end.
Ltac xsplit8 HS off :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i := xidx_reg_off rsm 516%nat off in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
let HR := fresh "HRq" in let V8 := fresh "V8" in let HRO := fresh "HROq" in let HS3 := fresh "HS3" in
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i r HS ltac:(vm_compute; reflexivity)) as HR; cbn [ms_mem restrict] in HR;
lazymatch type of HR with region_ok _ _ ?m (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk off (CVal 8 (SLit ?c))] =>
pose proof (field_of_region Ev m 516 Fv cs lo hi wlo whi off 8%N (SLit c) c HR ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V8;
change (N.to_nat 8) with 8%nat in V8;
let bs := eval vm_compute in (map (YO0f.le_byte c 8) (seq 0 8)) in
let cs' := eval vm_compute in (split_chunk off bs cs) in
unfold region_ok in HR; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR; evalE_in AG HR;
assert (HRO : region_ok pa_segs Ev m (YP09.mkRegion (Some 516%nat) lo hi wlo whi cs'));
[ let Q1 := fresh "Q" in let Q2 := fresh "Q" in let Q3 := fresh "Q" in let Qc := fresh "Qc" in
pose proof HR as (Q1 & Q2 & Q3 & Qc);
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; evalE AG;
split; [exact Q1|]; split; [exact Q2|]; split; [exact Q3|];
repeat (apply Forall_cons); try apply Forall_nil;
first [ match goal with |- YP09.chunk_ok _ _ _ _ ?ck => exact (proj1 (Forall_forall _ _) Qc ck ltac:(cbn; tauto)) end
| lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SLit ?b))) =>
apply (chunk_ok_val pa_segs Ev m Fv o 1 (SLit b) b); [reflexivity | cbn; lia | cbn; lia |];
let j := eval vm_compute in (Z.to_nat (o - off)) in
replace (Fv + o) with (Fv + off + Z.of_nat j) by (cbn; lia);
exact (val_mem8_byte m (Fv + off) c j V8 ltac:(cbn; lia)) end
| match goal with |- ?g => idtac "xsplit8: chunk goal left" g end ]
| pose proof (ast_ok_pi_set_region Ev ssx (restrict Hw msx) i r (YP09.mkRegion (Some 516%nat) lo hi wlo whi cs')
HS ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity) HRO) as HS3;
clear HS HR V8 HRO; rename HS3 into HS; norm_ss HS ] end end end end.
Lemma lor1_byte : forall W, 0 <= W < 256 -> 0 <= Z.lor W 1 < 256.
Proof.
intros W HW.
assert (H0 : 0 <= Z.lor W 1) by (apply (proj2 (Z.lor_nonneg W 1)); lia).
assert (Hp : 0 < Z.lor W 1) by (destruct (Z.eq_dec W 0) as [->|]; [reflexivity | pose proof (Z.add_lor_land W 1); pose proof (Z_land_upper W 1 ltac:(lia)); lia]).
assert (Hl : Z.log2 (Z.lor W 1) < 8).
{ rewrite Z.log2_lor by lia. apply Z.max_lub_lt; [| cbn; lia].
destruct (Z.eq_dec W 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]. }
apply (proj2 (Z.log2_lt_pow2 (Z.lor W 1) 8 Hp)) in Hl. change (2 ^ 8) with 256 in Hl. lia.
Qed.
Lemma xb_or1 : forall E a W, ew E a = Z_to_bv 64 W -> 0 <= W < 256 ->
bv_unsigned (sv_denot E (SAlu ALU_OR (SOff a 0) (SLit 1))) mod 2 ^ (8 * Z.of_N 1) = Z.lor W 1.
Proof.
intros E a W Ha HW. change (bv_unsigned (sv_denot E ?[e]) mod _ = _) with (U E (SAlu ALU_OR (SOff a 0) (SLit 1)) mod 2 ^ (8 * Z.of_N 1) = Z.lor W 1).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E a W Ha ltac:(lia)), U_SLit.
pose proof (lor1_byte W HW) as HB.
unfold zcanon, M64. change (1 mod 2 ^ 64) with 1. change (2 ^ (8 * Z.of_N 1)) with 256.
rewrite (Z.mod_small (Z.lor W 1) (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.
Lemma val_mem2_bytes : forall segs (m : word -> option byte) a v, val_mem segs m a 2 v -> 0 <= v ->
val_mem segs m a 1 (v mod 256) /\ val_mem segs m (a + 1) 1 ((v / 256) mod 256).
Proof.
intros segs m a v Hv Hr.
assert (D : v mod 65536 = v mod 256 + 256 * ((v / 256) mod 256)).
{ change 65536 with (256 * 256). rewrite (Z.rem_mul_r v 256 256) by lia. reflexivity. }
split; intros k Hk; replace k with 0%nat by lia; cbn [Z.of_nat].
- rewrite (Hv 0%nat ltac:(lia)). f_equal. f_equal. unfold YO0f.le_byte. rewrite !Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite D.
rewrite (Z.mul_comm 256 ((v / 256) mod 256)), Z.mod_add by lia. rewrite !Z.mod_mod by lia. reflexivity.
- rewrite Z.add_0_r. change (a + 1) with (a + Z.of_nat 1). rewrite (Hv 1%nat ltac:(lia)). f_equal. f_equal. unfold YO0f.le_byte. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 1) with 8. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite D.
rewrite (Z.mul_comm 256 ((v / 256) mod 256)), Z.div_add by lia. rewrite (Z.div_small (v mod 256) 256) by (apply Z.mod_pos_bound; lia). rewrite Z.add_0_l.
rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma xw_s16 : forall E a W, ew E a = Z_to_bv 64 W -> 0 <= W < 65536 ->
bv_unsigned (sv_denot E (SExt true 16 (SOff a 0))) mod 2 ^ (8 * Z.of_N 2) = W.
Proof.
intros E a W Ha HW. change (bv_unsigned (sv_denot E ?[e]) mod _ = _) with (U E (SExt true 16 (SOff a 0)) mod 2 ^ (8 * Z.of_N 2) = W).
rewrite U_SExt. rewrite (U_atom E a W Ha ltac:(lia)).
unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N two_power_nat]. change (2 ^ (8 * 2)) with 65536.
change (2 ^ 16 / 2) with 32768. change (2 ^ 16) with 65536.
rewrite (Z.mod_small W 65536) by lia.
destruct (Z_lt_le_dec W 32768).
- rewrite (Z.mod_small (W + 32768) 65536) by lia. replace (W + 32768 - 32768) with W by lia. rewrite (Z.mod_small W (2^64)) by lia. apply Z.mod_small. lia.
- replace ((W + 32768) mod 65536) with (W + 32768 - 65536) by (rewrite <- (Z.mod_add _ (-1) 65536) by lia; rewrite Z.mod_small by lia; lia).
replace (W + 32768 - 65536 - 32768) with (W - 65536 + 0) by lia. rewrite Z.add_0_r.
rewrite <- (Z.mod_add (W - 65536) 1 (2 ^ 64)) by lia. rewrite (Z.mod_small _ (2 ^ 64)) by lia.
replace (W - 65536 + 1 * 2 ^ 64) with (W + (2 ^ 48 - 1) * 65536) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Ltac xhalf HR off Vlo Vhi :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of HR with region_ok _ ?Ev ?m (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk off (CVal 2 (SExt true 16 (SOff ?a 0)))] =>
let V := fresh "V2" in let Ha := fresh "Ha" in
pose proof (field_of_region_any Ev m 516 Fv cs lo hi wlo whi off 2%N (SExt true 16 (SOff a 0)) HR ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
change (N.to_nat 2) with 2%nat in V; xatom Ev a Ha;
lazymatch type of Ha with _ = Z_to_bv 64 ?W =>
rewrite (xw_s16 Ev a W Ha ltac:(lia)) in V;
destruct (val_mem2_bytes _ _ _ _ V ltac:(lia)) as [Vlo Vhi]; clear V Ha end end end end.
Ltac wcb_siteAX rs HS HWX HGA HRA HHV HJ3 HAR3 Hfin3 HfinS3 Hraw3 Hing3 Hfrs3 EFA3 EFL3 HFpres3 HFSpres3 Hrpres3 Hgpres3 HUP Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let EE := lazymatch goal with H : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew _ n = getr _ r |- _ => H end in
let Usp := lazymatch goal with H : bv_unsigned (ew _ 2) = spZ _ |- _ => H end in
let E0v := lazymatch type of EE with forall n r, _ -> ew ?E0v n = _ => E0v end in
let E32 := lazymatch goal with H : ew E0v 32 = Z_to_bv 64 _ |- _ => H end in
let E53 := lazymatch goal with H : ew _ 53 = Z_to_bv 64 _ |- _ => H end in
let E54 := lazymatch goal with H : ew _ 54 = Z_to_bv 64 _ |- _ => H end in
let E56 := lazymatch goal with H : ew _ 56 = Z_to_bv 64 _ |- _ => H end in
let Hch := lazymatch goal with H : achain _ _ _ _ _ |- _ => H end in
let Hal32 := lazymatch goal with H : spZ _ mod 32 = 0 |- _ => H end in
let Hra4 := lazymatch goal with H : 4096 <= raZ _ |- _ => H end in
let Hgp := lazymatch goal with H : getr _ 3 = w64 (as_gp _) |- _ => H end in
let Htp := lazymatch goal with H : getr _ 4 = w64 (as_tp _) |- _ => H end in
let FFS := lazymatch goal with H : TRAWADD_STK = _ |- _ => H end in
let HROD := lazymatch goal with H : arodata_okP _ _ _ _ _ |- _ => H end in
let WFN := lazymatch goal with H : twcbF_spec _ _ _ _ |- _ => H end in
let Rwfn := lazymatch type of WFN with twcbF_spec _ _ _ ?wf => lazymatch goal with H : 0 <= wf < 2 ^ 64 /\ wf mod 2 = 0 |- _ => H end end in
let HDEEP := lazymatch goal with H : forall c, In c ?T -> (2 <= length c)%nat |- _ => H end in
let Hctx := lazymatch type of HDEEP with forall c, In c ?T -> _ => lazymatch goal with H : In _ T |- _ => H end end in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in
let XF := lazymatch goal with H : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ => H end in
let LAWS := rnLAWS in let Bv := rnB in
lazymatch type of HJ3 with ajournal _ _ ?STK (spZ ?regs) ?FP ?ly ?S ?W ?mem ?md [(1, ?fpos)] ?ly3 ?S3 ?W3 _ ?md3 ?k =>
lazymatch type of HfinS3 with In (?cid, ?pos) _ =>
lazymatch type of Hing3 with In (?g, CGIF_SIZE) _ =>
lazymatch type of Hraw3 with In (?raw, RAW_SIZE) _ =>
lazymatch type of Hch with achain _ _ _ _ ?ch =>
lazymatch type of WFN with twcbF_spec _ ?Kv _ ?wfn =>
lazymatch type of E54 with _ = Z_to_bv 64 ?hw =>
lazymatch type of HSINK with asink_at _ _ _ _ ?pf ?SG =>
lazymatch type of HWX with ?n = Z.of_nat (length ?bs) /\ _ /\ _ /\ (?p + _ <= _ \/ _) /\ _ =>
let Hinf3 := lazymatch goal with H : In (pf, FILE_BLOCK) (ablocks _ ly3 S3) |- _ => H end in
lazymatch type of HFpres3 with forall a, ?F <= a < _ -> _ =>
let Hfin := lazymatch goal with H : In (cid, pos) (frames S) |- _ => H end in
let P2 := fresh "P2" in let Prs := fresh "Prs" in let P8 := fresh "P8" in let P10 := fresh "P10" in
let P1 := fresh "P1" in let P3 := fresh "P3" in let P4 := fresh "P4" in let P11 := fresh "P11" in let P12 := fresh "P12" in
let Hchne := fresh "Hchne" in let Qtop := fresh "Qtop" in let Qtop64 := fresh "Qtop64" in let Qceil := fresh "Qceil" in let Qal8 := fresh "Qal8" in
let Qra := fresh "Qra" in let Qs0 := fresh "Qs0" in let Vra := fresh "Vra" in let Vs0 := fresh "Vs0" in let HRr := fresh "HRr" in
let Hch1 := fresh "Hch1" in let Vhw := fresh "Vhw" in let Vctx := fresh "Vctx" in let Vpf := fresh "Vpf" in
let matj := fresh "mat" in let msj := fresh "msj" in let Emsj := fresh "Emsj" in let HS1 := fresh "HSj" in let HS2 := fresh "HS2" in
let W4 := fresh "W" in let c4 := fresh "c" in let Hwle4 := fresh "Hwle" in let ly4 := fresh "ly" in let S4 := fresh "S" in
let regs4 := fresh "regs" in let mem4 := fresh "mem" in let md4 := fresh "md" in
let HJ4 := fresh "HJ4" in let HJc := fresh "HJc" in let HP4 := fresh "HP4" in let Ha04 := fresh "Ha0c" in let HPb4 := fresh "HPb" in
let HRK := fresh "HRK" in let HEv := fresh "HEv" in
prreg HS (2%bv : bv 5) P2; prreg HS rs Prs; prreg HS (8%bv : bv 5) P8;
assert (Hchne : ch <> []) by (let Hn := fresh "Hn" in let Hd := fresh "Hdeep" in intros Hn; pose proof (HDEEP _ Hctx) as Hd; rewrite Hn in Hd; cbn in Hd; clear - Hd; lia);
assert (Qtop : spZ regs < ly_top ly - 16) by (destruct Hch as [[_ Hnil] | (Q1 & Q2 & _)]; [exfalso; exact (Hchne Hnil) | lia]);
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia;
assert (Qceil : alloc_ceiling <= spZ regs) by lia;
assert (Qal8 : spZ regs mod 8 = 0) by (let D := fresh "D" in pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult);
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (let Hq := fresh "Hq" in unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (let Hq := fresh "Hq" in unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i := match rsm with _ => idx_of_base_lo rsm 2%nat (-104) | _ => idx_of_base rsm 2%nat end in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRr
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(let Hq := fresh "Hq" in unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRr
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(let Hq := fresh "Hq" in unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0;
clear HRr;
assert (Hch1 : achain ly3 (aview pa_segs (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
let Etop := fresh "Etop" in
pose proof HJ3 as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _) & _);
apply (achain_ly_top ly ly3); [exact Etop|];
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)
(rdword_of_val_mem _ _ _ _ _ Vra Qra) (rdword_of_val_mem _ _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop ltac:(lia))
| ] end;
let i := idx_of_base rsm 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict mkst] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 56 8%N (SOff 54 0) hw HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E54, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vhw;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 64 8%N (SOff 52 0) (bv_unsigned (ew Ex 52)) HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity)
ltac:(let Q := fresh "Q" in pose proof (bv_unsigned_in_range 64 (ew Ex 52)) as Q; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Q; exact Q) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 80 8%N (SOff 56 0) pf HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E56, Z.add_0_r, unsigned_lit_small by (clear - XF; unfold xfacts in XF; lia); reflexivity)
ltac:(cbn; clear - XF; unfold xfacts in XF; lia) ltac:(cbn; lia)) as Vpf end;
clear HRr;
let pcj := eval vm_compute in (ss_pc ssx) in
let wj := eval vm_compute in (match plookup asan3_1_tpi pcj with Some (PW x) => x | _ => 0 end) in
let HEIx := rnHEI Ex in
eapply (SRr_jalr_call_pi (PL:=PL_asan3_1) W3 Ex ssx _ _ _ wj (1%bv : bv 5) rs wfn HEIx HS eq_refl);
[ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | rewrite Prs; exact E53 | exact (proj1 Rwfn) | exact (proj2 Rwfn) |];
clear HS; intros matj msj Emsj HS1;
prreg HS1 (1%bv : bv 5) P1; prreg HS1 (3%bv : bv 5) P3; prreg HS1 (4%bv : bv 5) P4; clear P8; prreg HS1 (8%bv : bv 5) P8; prreg HS1 (10%bv : bv 5) P10;
prreg HS1 (11%bv : bv 5) P11; prreg HS1 (12%bv : bv 5) P12;
clear P2; prreg HS1 (2%bv : bv 5) P2;
let HJm := fresh "HJm" in let Qsp := fresh "Qsp" in
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ =>
assert (HJm : ajournal pa_segs Bv STK (spZ regs) FP ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem msX) mdq k)
by (apply (ajournal_materialize _ Bv LAWS pa_segs_low); exact HJ3);
assert (Qsp : spZ (ms_regs msq) = spZ regs + -320)
by (unfold spZ at 1; rewrite P2; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia;
rewrite Z_to_bv_bv_unsigned || idtac; evalE AG);
rewrite Emsj at 1; rewrite Emsj in Qsp; cbn [ms_regs mkst] in Qsp;
rewrite Emsj in P1, P3, P4, P8, P10, P11, P12; cbn [ms_regs mkst] in P1, P3, P4, P8, P10, P11, P12;
eapply SRr_bind;
[ eapply (cl_callS Bv LAWS W3 _ (ms_mem msX) _ STK (spZ regs) FP ly S W mem md [(1, fpos)] ly3 S3 mdq k
WCBF_STK (asink_fp pf) 0 (-320) _ ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ getr regs2 10 = w64 0 /\ asink_at pa_segs Kv (mrestrict (w_H W2) mem2) md2 pf (SG ++ bs)) HJm Qsp);
[ reflexivity | lia | unfold WCBF_STK, YC20.WCB_STK, AFWRITE_STK; lia | rewrite FFS; unfold WCBF_STK, YC20.WCB_STK, AFWRITE_STK; lia
| rewrite P3; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite P4; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact P1 | apply ret_ok_codeptr_v; [lia | reflexivity] | rewrite unsigned_lit_small by lia; lia
| unfold s0Z; rewrite P8; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
replace (spZ regs + -320) with (spZ regs - 320) by lia; exact Hch1
| let HPRE1 := fresh "HPRE1" in let HC := fresh "HC" in
intros HPRE1; eapply SRr_mono;
[ pose proof (WFN W3 ly3 S3 _ _ _ ((spZ regs, raZ regs, s0Z regs) :: ch) g p n pf SG bs HPRE1) as HC; unfold cfg_at in HC;
lazymatch type of HS1 with st_ok _ _ ?sse _ => replace (w64 wfn) with (Z_to_bv 64 (ss_pc sse)) in HC by reflexivity end;
eapply HC;
[ rewrite P10; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; rewrite E32; reflexivity
| rewrite P11; first [ assumption | symmetry; assumption
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; evalE AG;
first [ reflexivity | assumption | symmetry; assumption | match goal with |- ?gl => idtac "wcb_siteAX: a1 goal left:" gl; fail end ] ]
| rewrite P12; first [ assumption | symmetry; assumption
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; evalE AG;
first [ reflexivity | assumption | symmetry; assumption | match goal with |- ?gl => idtac "wcb_siteAX: a2 goal left:" gl; fail end ] ]
| exact Hing3 | exact Vpf | exact Hinf3 | exact HSINK | exact HGA
| exact (proj1 HWX) | exact (proj1 (proj2 HWX))
| clear - HWX; rewrite ?app_nil_r in *; rewrite ?length_app in *; lia
| clear - HWX; unfold FILE_BLOCK in *; lia
| left; rewrite Qsp; clear - HWX XF; unfold xfacts in XF; unfold WCBF_STK, YC20.WCB_STK, AFWRITE_STK; lia
| clear - HWX; lia | exact (proj2 (proj2 (proj2 (proj2 (proj2 HWX)))))
| exact HRA | exact HHV ]
| cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in
intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJ1 & HP & Ha0 & HSINK2);
exists ly3, S3, regs2, mem2, md2; split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | ]]];
split; [reflexivity | split; [reflexivity | split; [exact Ha0 | exact HSINK2]]] ]
| let a := fresh "a" in let r := fresh "r" in let Hr1 := fresh "Hr1" in let Hr2 := fresh "Hr2" in
intros a (r & Hr1 & Hr2); left; exists r; split; [right; exact Hr1 | exact Hr2] ]
| ] end;
clear HJm Qsp;
clear P3 P4 P10 P11 P12 Vra Vs0 Vhw Vctx Vpf Hch1 Prs;
let Ely4 := fresh "Ely" in let ES4 := fresh "ES" in let HSINK4 := fresh "HSINK4" in
cbv beta; intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & (Ely4 & ES4 & Ha04 & HSINK4)); subst ly4 S4;
pose proof (Permutation_refl (ablocks Bv ly3 S3)) as HPb4;
(let HP4' := fresh "HP4'" in
lazymatch type of HS1 with st_ok _ _ _ (restrict ?Hw ?msy) =>
assert (HP4' : aregs_preserved (ms_regs (restrict Hw msy)) regs4) by (rewrite Emsj; cbn [ms_regs restrict mkst]; exact HP4); clear HP4; rename HP4' into HP4 end);
let K := run_K_hi HS1 in
lazymatch type of HS1 with st_ok _ _ ?ssy _ =>
let n := eval vm_compute in (length (ss_mem ssy)) in let idxs := eval vm_compute in (seq 0 n) in
jafter_call_keep_hi HS1 K regs4 (mrestrict (w_H W4) mem4) HP4 idxs HS2 end;
rewrite Emsj in HS2; cbn [ms_mem ms_regs restrict mkst] in HS2, HJc;
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3; aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
let HAR4 := fresh "HAR4" in let HFpres4 := fresh "HFpres4" in let HFSpres4 := fresh "HFSpres4" in let Hrpres4 := fresh "Hrpres4" in let Hgpres4 := fresh "Hgpres4" in let HUP4 := fresh "HUP4" in
let Kgot4 := fresh "Kgot4" in let Kcell4 := fresh "Kcell4" in let Kguar4 := fresh "Kguar4" in let Kuar4 := fresh "Kuar4" in let Vgr4 := fresh "Vgr4" in
pose proof (proj1 HJ4) as HAR4;
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin3) as (_ & _ & HFpres4 & HFSpres4); change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4;
change (128 / 8) with 16 in HFSpres4; rewrite !EFA3 in HFpres4, HFSpres4; fold F in HFpres4, HFSpres4;
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR4 Hraw3) as (_ & _ & _ & _ & Hrpres4 & _); change (req_size RAW_SIZE) with 48 in Hrpres4;
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR4 Hing3) as (_ & _ & _ & _ & Hgpres4 & _); change (req_size CGIF_SIZE) with 96 in Hgpres4;
assert (HUP4 : forall a, spZ regs <= a < 2 ^ 64 -> aview pa_segs (w_H W4) mem4 a = aview pa_segs (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let F1 := fresh "F1" in intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1;
[clear - Ha Qceil; lia | clear - Ha; lia]);
aconstsA HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4;
match type of HS2 with ?tq -> _ => assert (HRK : tq) end;
[ repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 516%nat F lo hi wlo whi _ 1 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; lia
| xFP | intros aa Haa; apply (fun H => proj1 (HFpres4 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_fshadow_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 529%nat (SB + F / 8) lo hi wlo whi _ 1 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia
| rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia
| xFP | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_subw (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat lo hi wlo whi _ raw RAW_SIZE HJc);
[ evalE AG | exact Hraw3 | exact Hraw3 | lia | change (req_size RAW_SIZE) with 48; lia
| xFP | intros aa Haa; apply (fun H => proj1 (Hrpres4 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub _ Bv); [exact HJc | exact HJ4 | evalE AG | lia | rewrite FFS; lia | lia | cbn; lia | cbn; lia]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 11%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 11%nat _ lo hi wlo whi _ cid pos HJc);
[ evalE AG | exact HfinS3 | rewrite EFA3; lia | rewrite EFA3; lia | xFP | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_sub _ Bv); [exact HJc | evalE AG | exact Hing3 | exact Hing3 | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia
| xFP ]
| |- _ => keptIA I I AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
end
| ];
specialize (HS2 HRK); clear HRK HS1; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
rebaseE HS AG HEv; clear HEv;
let HS0 := fresh "HS0" in
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msr) =>
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs mkst restrict]; exact Ha04) eq_refl) as HS0 end;
clear HS; rename HS0 into HS; norm_ss HS;
try (xblk_station HJc);
clear HJ3 HAR3 HFpres3 HFSpres3 Hrpres3 Hgpres3 HUP Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
clear HJc HP4 HPb4 Ha04 Hwle4 P1 P2 P8 Hchne Qtop Qtop64 Qceil Qal8 Qra Qs0 Emsj; try clear matj; clear HSINK;
rename HJ4 into HJ3; rename HAR4 into HAR3; rename HFpres4 into HFpres3; rename HFSpres4 into HFSpres3;
rename Hrpres4 into Hrpres3; rename Hgpres4 into Hgpres3; rename HUP4 into HUP;
rename Kgot4 into Kgot3; rename Kcell4 into Kcell3; rename Kguar4 into Kguar3; rename Kuar4 into Kuar3; rename Vgr4 into Vgr3;
rename HSINK4 into HSINK;
replace (k + 0) with k in HJ3 by lia; clear HWX HGA HRA HHV
end end end end end end end end end end end.
Ltac xgce_facts HS :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let LAWS := rnLAWS in let Bv := rnB in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
let HSINK := lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => H end in
let XF := lazymatch goal with H : xfacts (_ <= alloc_ceiling /\ 4096 <= _ /\ _) |- _ => H end in
let HSmax := lazymatch goal with H : xfacts (Z.of_nat (length _) + FRAME_OUT _ <= SINK_MAX) |- _ => H end in
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of HSINK with asink_at _ _ _ _ ?pf ?SG =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i0 := xidx_reg rsm 516%nat 58 in let i0 := eval vm_compute in i0 in let r0 := eval vm_compute in (nth i0 rsm got_regionP) in
let i2 := xidx_reg rsm 529%nat 0 in let i2 := eval vm_compute in i2 in let r2 := eval vm_compute in (nth i2 rsm got_regionP) in
let HR0 := fresh "HR0" in let HR2 := fresh "HR2" in
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict] in HR0;
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict] in HR2;
let V80 := fresh "V80" in let V81 := fresh "V81" in let V82 := fresh "V82" in let V83 := fresh "V83" in
let V84 := fresh "V84" in let V85 := fresh "V85" in let V86 := fresh "V86" in let V87 := fresh "V87" in
xbyte HR0 80 V80; xbyte HR0 81 V81; xbyte HR0 82 V82; xbyte HR0 83 V83; xhalf HR0 84 V84 V85; xbyte HR0 86 V86; xbyte HR0 87 V87;
try (lazymatch type of V83 with val_mem _ _ _ _ (bv_unsigned (sv_denot ?Eo (SAlu ALU_OR (SOff ?a 0) (SLit 1))) mod _) =>
let Ha := fresh "Ha" in let HB := fresh "HB83" in
xatom Eo a Ha; rewrite (xb_or1 Eo a _ Ha ltac:(lia)) in V83;
lazymatch type of V83 with val_mem _ _ _ _ (Z.lor ?dv 1) => pose proof (lor1_byte dv ltac:(lia)) as HB end; clear Ha end);
replace (Fv + 84 + 1) with (Fv + 85) in V85 by lia;
lazymatch type of HR0 with region_ok _ _ ?m _ =>
lazymatch type of V83 with val_mem _ _ _ _ ?b3 => lazymatch type of V84 with val_mem _ _ _ _ ?b4 => lazymatch type of V85 with val_mem _ _ _ _ ?b5 =>
lazymatch type of V86 with val_mem _ _ _ _ ?b6 =>
assert (HGA : garr8 pa_segs m (Fv + 80) [33; 249; 4; b3; b4; b5; b6; 0]) by xgarr8;
clear V80 V81 V82 V83 V84 V85 V86 V87 HR0;
let V10 := fresh "V10" in let Hsh10 := fresh "Hsh10" in let Hsa := fresh "Hsa" in
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 10 1%N (SLit 0) 0 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V10 end;
clear HR2;
pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V10 ltac:(lia)) as Hsh10;
let HFq := lazymatch goal with H : Fv = 32 * (Fv / 32) |- _ => H end in
let HF8 := lazymatch goal with H : Fv / 8 = 4 * (Fv / 32) |- _ => H end in
assert (Hsa : shadow_of_addr SHADOW_OFF (Fv + 80) = SB + Fv / 8 + 10)
by (unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; rewrite HFq at 1; rewrite HF8;
replace (32 * (Fv / 32) + 80) with ((4 * (Fv / 32) + 10) * 8) by lia; rewrite Z.div_mul by lia; lia);
assert (HRAX : range_addressable (aview pa_segs Hw (ms_mem msx)) SHADOW_OFF (Fv + 80) 8)
by (apply range_addressable_zero8'; [rewrite Hsa; exact Hsh10 | rewrite HFq; replace (32 * (Fv / 32) + 80) with ((4 * (Fv / 32) + 10) * 8) by lia; apply Z_mod_mult]);
clear V10 Hsh10 Hsa;
let HJ3 := lazymatch goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ (ms_mem msx) _ _ |- _ => H end in
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ _ _ _ =>
let Hfin3 := lazymatch goal with H : In (1, ?fp) (frames S3) |- _ => H end in
let EFA3 := lazymatch goal with H : forall c p, frame_addr ly3 c p = frame_addr _ c p |- _ => H end in
lazymatch type of Hfin3 with In (1, ?fpos) _ =>
assert (HHVX : shadow_hull_vis (aview pa_segs Hw (ms_mem msx)) (Fv + 80) 8)
by (eapply (shadow_hull_vis_of_frame pa_segs Bv LAWS ly3 S3 _ _ _ 1 fpos (Fv + 80) 8 (proj1 HJ3) Hfin3);
[rewrite EFA3; lia | rewrite EFA3; change (fs_frame_bytes 1) with 128; lia | lia]) end end;
let HFhigh := lazymatch goal with H : in_app Fv 128 |- _ => H end in
let HFceil := lazymatch goal with H : Fv + 128 <= alloc_ceiling |- _ => H end in
assert (HWX : 8 = Z.of_nat (length [33; 249; 4; b3; b4; b5; b6; 0]) /\ 1 <= 8 <= 2 ^ 30 /\ Z.of_nat (length SG) + 8 <= SINK_MAX /\
(Fv + 80 + 8 <= pf \/ pf + FILE_BLOCK <= Fv + 80) /\ 0 <= Fv + 80 /\ amem_range (Fv + 80) 8)
by (split; [reflexivity|]; split; [lia|];
split; [let Hw := match goal with H : 1 <= ?wv |- _ => lazymatch type of HSmax with context [FRAME_OUT (wv * _)] => H end end in
let Hh := match goal with H : 1 <= ?hv |- _ => lazymatch type of HSmax with context [FRAME_OUT (_ * hv)] => H end end in
clear - HSmax Hw Hh; unfold xfacts in HSmax; rewrite ?app_nil_r; unfold FRAME_OUT in HSmax; nia|];
split; [clear - XF; unfold xfacts in XF; unfold FILE_BLOCK; lia|]; split; [clear - XF; unfold xfacts in XF; lia|];
apply (amem_range_sub_app _ _ _ _ HFhigh HFceil); clear; lia)
end end end end end end end end.
