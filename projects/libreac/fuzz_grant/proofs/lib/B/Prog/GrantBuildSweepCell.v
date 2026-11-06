(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the cut lemma pb_bs_cell of reac_grant_build_sweep's cell loop, adapting the call-and-reseat walk pattern of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v and lib/A/AChf.v and the caller-journal call block of lib/YC20.v; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantBuildSweepCell.v at a working branch af735a950e2 (blob 9b8f3585871; the walk was ported from blob 4793f9e128e at a working branch eacc832ec38a, which differs from it by the licence header and six removed debug-guard lines): pb_bs_cell, the cut lemma of reac_grant_build_sweep's cell loop (0x85840, listing offset 19972), over image B's listing and walk layer. What image B changes against the image-A donor: the cell index is s7 (a literal in the cut) and the row index is s6 = SOff 620 p; the store's address is s8 + s6 = (F + 32) + (3c + p), which reaches the row region through bs_al's three aliases; there is a UBSan bound check `bgeu s6,s3` at 0x85850 (trap 0x85a3c), decided false by the cut's fact (620, 0 <= . <= 117); the column step reloads al and the width from the realigned frame's slots 40 and 56 and re-atomises the row, the row index and the column (atoms 619, 620, 621), where image A reads the two last off dead registers; and the cut carries arodata_okP, which this file transports with rod_img_kept / rod_acall_kept. *)
(* Modified by Theorem Labs, 2026-10: pb_bs_cell's proof boxes the context's disjunctions and alignment facts away from lia (bsc_box_all), a speed-up only; no statement changed. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC4b YC81 YC88 YCbw YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantSyms GrantList GrantAddr GrantTop GrantPa GrantPaLib GrantFrame GrantRo YC1g YC1h YC1i YC45 YC85
ACj1 ACbf GrantACjr GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel BuildSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBuildSweepLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* The cut's atom facts without the three the column step replaces (the row 619, the row index 620 and the
   column 621): what the state keeps while those atoms are havoc'd to the next column's values. *)
Definition bsc_FL0 (z : bool) : list (nat * afact) :=
(if z then [] else [(36%nat, mkAF 2 7 0)]) ++
[ (35%nat, mkAF (SB + 512) (SB + 17592186044416) 0); (34%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0);
(12%nat, mkAF 4096 140737479966720 3); (529%nat, mkAF (SB + 512) (SB + 17592186044416) 2);
(528%nat, HPTR 0); (516%nat, HPTR 5); (60%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5);
(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0) ].
(* The registers the column step gives fresh atoms before 619..621 are havoc'd: s2 and s11, which hold the old
   column and row index, and then the dead ones. *)
Definition bsc_deads_X : list (bv 5) := [18; 27; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 25; 28; 29; 30; 31]%bv.
(* ---- the preamble of a cut lemma ------------------------------------------ *)
(* Unpack a cut's three facts (bs_ctx, bs_env, bs_mem) into the names the walk tactics use: the entry facts
   (HPRE ..), the atoms' values (EE, E32 .. E621, E10 .. E13), the journal HJ2, the stack above sp HUP, the
   read-only data HROD3, the values HVALS, the table HOBJ, the own frame F (flag FL) and its bounds, its place
   off image B's own range HFIMG (frm_off_imgB), and al's frame (cid, pos) and its bounds. *)
Ltac bsc_cut_intro HCTX HENV HMEM ly S W mem md fpos S2 cid pos Ec ms3 md3 :=
let L := rnLAWS in
destruct HCTX as (HPRE & Hroom & Htop32 & HROD & H10 & H11 & H12 & H13 & Rs & Rmx & Htx & HTlen & H01 & HTL & HSB &
Hsn & Haln & Hw1 & Hb8 & Hbw & Hfin & Hcid0 & Hflo & Hfhi & Hal8 & Hfrs2 & Eab & (fS2 & ES2) & Hsp1 & Hsp1al);
destruct HENV as (HEI & EE & E32 & E33 & E34 & E35 & E36 & E60 & RF & E528 & E529 & E619 & E620 & E621);
destruct HMEM as (HJ2 & HUP & HROD3 & HVALS & HOBJ);
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof pa_B_ok as HBASE; pose proof pa_base_lo as HBLO;
assert (FFS : BSW_STK = 4832) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
lazymatch type of H10 with getr _ _ = w64 ?v => assert (E10 : ew Ec 10 = Z_to_bv 64 v) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10) end;
lazymatch type of H11 with getr _ _ = w64 ?v => assert (E11 : ew Ec 11 = Z_to_bv 64 v) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11) end;
lazymatch type of H12 with getr _ _ = w64 ?v => assert (E12 : ew Ec 12 = Z_to_bv 64 v) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12) end;
lazymatch type of H13 with getr _ _ = w64 ?v => assert (E13 : ew Ec 13 = Z_to_bv 64 v) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13) end;
lazymatch type of H10 with getr ?rg _ = _ => assert (Usp : bv_unsigned (ew Ec 2) = spZ rg) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity) end;
assert (AG : forall n, (n < 33)%nat -> ew Ec n = ew Ec n) by (intros; reflexivity);
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by (intros; reflexivity);
img_factsF Ec; img_hull_factsF;
pose proof (proj1 HJ2) as HAR2;
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity);
destruct (al_frames _ _ L _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres);
destruct (frames_bounds _ _ L _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img;
pose proof (frm_off_imgB _ ly S2 W (ms_mem ms3) md3 2 fpos HAR2 Hfin2) as HFIMG;
rewrite IMG_LO_B_val, IMG_TOP_B_val in HFIMG;
destruct (frames_bounds _ _ L ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
destruct (frame_al64 _ _ ly S W mem md cid pos HAR Hfin) as (Hf64 & Hfb64 & Hfb64');
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin);
let fl1 := fresh "fl1" in let fl2 := fresh "fl2" in let Efl := fresh "Efl" in
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl);
pose proof (sep_frames_pos _ _ L ly S2 _ _ _ (2, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC;
unfold zdisjoint, frame_rng in HdFC; cbn [fst snd] in HdFC;
destruct (al_blocks _ _ L ly S W mem md _ _ HAR Htx) as (_ & Htx4096 & Htxceil & Htxia & _);
change (req_size ATx.TX_SIZE) with 460 in Htxceil, Htxia;
pose proof Htx as HtxS2; rewrite <- Eab in HtxS2;
pose proof (sep_block_frame _ _ L ly S2 W _ _ _ _ 2 fpos HAR2 HtxS2 Hfin2) as HtxF;
unfold zdisjoint in HtxF; cbn [fst snd] in HtxF; change (req_size ATx.TX_SIZE) with 460 in HtxF;
change (fs_frame_bytes 2) with 256 in *;
let F := fresh "F" in let FL := fresh "FL" in
set (F := frame_addr ly 2 fpos) in *; set (FL := flag_addr ly 2 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia);
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
assert (HF8c : F / 8 + 32 <= 17592184995840) by (rewrite <- (Z.div_add F 32 8) by lia; apply Z.div_le_upper_bound; lia);
lazymatch type of H12 with getr _ _ = w64 ?al =>
assert (Hal512 : 512 <= al / 8 < 17592186044416) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia);
assert (Hal8d : al = 8 * (al / 8)) by (pose proof (Z.div_mod al 8 ltac:(lia)); lia) end.
(* awrFL's rule for the row region (base atom 619 = F + 32 + 3c, three bytes, inside the own frame F): use as
   `awrFL_with ltac:(idtac; bsc_row_rule AG fpos F EFA Hc Hw1) AG fpos F EFA`. *)
Ltac bsc_row_rule AG fpos F EFA Hc Hw1 :=
lazymatch goal with |- awr_ok _ (YP09.mkRegion (Some 619%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?cl, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 619%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
right; right; right; exists cl, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; fsb_lits; rewrite ?EFA; fold F; clear - Ha Hc Hw1; lia
| ] end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
(* the one program function the segment calls, as GrantBContracts.v states it *)
Hypothesis TEFF : C.tb_reac_headamp_tx_effective_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
(* Narrow the row region's writable window to the cells not yet written (offsets p..2, p read from s7), so that
   a run keeps the ones already written. *)
Ltac bsc_narrow HS :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let pv := eval vm_compute in (sr_get (ss_regs ssx) 23%bv) in
lazymatch pv with SLit ?p =>
let rs := eval vm_compute in (match ss_mem ssx with r :: rs => set_window r p 3 :: rs | [] => [] end) in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end end; norm_ss HS.
(* A register's symbolic value as it stands (prreg without the normalisation). *)
Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
(* The frame regions a call of reac_headamp_tx_effective keeps: the row (619), F's header and tail (516) and F's
   shadow (529, read-only over the call) in the own frame (2, fpos); al's two bytes (12) and al's shadow cell (35)
   in al's frame (cid, pos). *)
Ltac bsc_kept_frames HK AG Hfin2 HfinS2 HFp F Hf64 Hfb64 Hflo Hfhi :=
let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 619%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | exact Hfin2 | left; fsb_lits; fold F; lia
| intros a Ha Hn; exact Hn | intros a Ha; apply (proj1 (HFp a ltac:(lia))) ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | exact Hfin2 | left; fsb_lits; fold F; lia
| intros a Ha Hn; exact Hn | intros a Ha; apply (proj1 (HFp a ltac:(lia))) ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | exact Hfin2
| right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fsb_lits; fold F; unfold SB; lia
| intros a Ha Hn; exact Hn | intros a Ha; lia ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj _ _ _ _ _ _ _ _ _ _ _ _ 12%nat); [exact HK | evalE AG | exact HfinS2 | lia | lia | lia | intros a Ha Hn; exact Hn ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 35%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | exact HfinS2
| right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; unfold SB;
lazymatch type of Hflo with frame_addr ?l ?ci ?po <= ?x =>
let Hsf := fresh "Hsf" in
pose proof (shadow_in_frame (frame_addr l ci po) (fs_frame_bytes ci) x Hf64 Hfb64 ltac:(lia) ltac:(lia) ltac:(lia)) as Hsf end; lia
| intros a Ha Hn; exact Hn | intros a Ha; lia ]
end.
(* reac_headamp_tx_effective's second argument: (base + c) & 255 = base + c; the engine may or may not keep the
   `mv a1,s9`'s `+ 0`, so both shapes are proved. *)
Lemma bsc_ch_denot : forall E base c, ew E 33 = Z_to_bv 64 base -> ew E 621 = Z_to_bv 64 c ->
0 <= base -> 0 <= c -> base + c < 256 ->
sv_denot E (SAlu ALU_ADD bs_ch (SLit 0)) = Z_to_bv 64 (base + c).
Proof.
intros E b c Hb Hc Hb0 Hc0 Hbc. rewrite denot_lit_U. f_equal. unfold bs_ch.
rewrite !U_SAlu, ?U_SLit, (U_atom E 33 b Hb), (U_atom E 621 c Hc) by lia. cbn [zalu_raw].
rewrite ?(zcanon_id (b + c)) by (unfold M64; lia). change (zcanon 255) with 255. try change (zcanon 0) with 0.
rewrite land255_small by lia. rewrite ?Z.add_0_r, ?(zcanon_id (b + c)) by (unfold M64; lia). reflexivity.
Qed.
Lemma bsc_ch_denot0 : forall E base c, ew E 33 = Z_to_bv 64 base -> ew E 621 = Z_to_bv 64 c ->
0 <= base -> 0 <= c -> base + c < 256 ->
sv_denot E bs_ch = Z_to_bv 64 (base + c).
Proof.
intros E b c Hb Hc Hb0 Hc0 Hbc. rewrite denot_lit_U. f_equal. unfold bs_ch.
rewrite !U_SAlu, ?U_SLit, (U_atom E 33 b Hb), (U_atom E 621 c Hc) by lia. cbn [zalu_raw].
rewrite ?(zcanon_id (b + c)) by (unfold M64; lia). change (zcanon 255) with 255.
rewrite land255_small by lia. rewrite ?(zcanon_id (b + c)) by (unfold M64; lia). reflexivity.
Qed.
(* The values buffer after the cell's store: the first 3c + p values kept, and the stored byte the next one
   (BuildSweepModel's nth_sweep_vals). *)
Lemma bsc_vals : forall (H : word -> bool) (m m' : word -> option byte) F T tx base w c p,
0 <= c < w -> 0 <= p < 3 ->
garr8 SEGS (mrestrict H m) (F + 32) (map bv_unsigned (firstn (Z.to_nat (3 * c + p)) (sweep_vals T tx base (Z.to_nat w)))) ->
(forall a, F + 32 <= a < F + 32 + (3 * c + p) -> aview SEGS H m' a = aview SEGS H m a) ->
val_mem SEGS (mrestrict H m') (F + 32 + 3 * c + p) 1 (eff T tx (base + c) p) ->
garr8 SEGS (mrestrict H m') (F + 32) (map bv_unsigned (firstn (Z.to_nat (3 * c + p + 1)) (sweep_vals T tx base (Z.to_nat w)))).
Proof.
intros H m m' F T tx base w c p Hc Hp HG HK HV.
pose proof (OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.GroupaModel.eff_range T tx (base + c) p) as Hr.
assert (Hn : nth (Z.to_nat (3 * c + p)) (sweep_vals T tx base (Z.to_nat w)) (Z_to_bv 8 0) = Z_to_bv 8 (eff T tx (base + c) p)).
{ replace (Z.to_nat (3 * c + p)) with (3 * Z.to_nat c + Z.to_nat p)%nat by lia.
rewrite nth_sweep_vals by lia. rewrite !Z2Nat.id by lia. reflexivity. }
replace (Z.to_nat (3 * c + p + 1)) with (S (Z.to_nat (3 * c + p))) by lia.
rewrite (firstn_S_nth _ _ (Z_to_bv 8 0)) by (rewrite length_sweep_vals; lia).
rewrite map_app, Hn. cbn [map].
replace (bv_unsigned (Z_to_bv 8 (eff T tx (base + c) p))) with (eff T tx (base + c) p)
by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; symmetry; apply Z.mod_small; exact Hr).
apply (garr8_app1 SEGS (mrestrict H m) (mrestrict H m') (F + 32) _ _ HG).
- rewrite length_map, length_firstn, length_sweep_vals.
replace (F + 32 + Z.of_nat (Nat.min (Z.to_nat (3 * c + p)) (3 * Z.to_nat w))) with (F + 32 + 3 * c + p) by lia. exact HV.
- exact Hr.
- intros a Ha. apply (mbyte_of_aview SEGS). apply HK. rewrite length_map, length_firstn, length_sweep_vals in Ha. lia.
Qed.
(* The byte the cell's store left: the chunk at offset p of the row region (region 0), the value of the atom
   Eeff names. *)
Ltac bsc_vbyte HS AG Eeff F c T tx base Vbyte :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msX) =>
let HRrow := fresh "HRrow" in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wx) msX) 0 _ HS eq_refl) as HRrow; cbn [ms_mem restrict] in HRrow;
lazymatch type of HRrow with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk ?od (CVal 1 ?e)] =>
pose proof (field_of_region Ex _ 619 (F + 32 + 3 * c) cs lo hi wlo whi od 1%N e (eff T tx (base + c) od) HRrow
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Eeff, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; exact (OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.GroupaModel.eff_range T tx (base + c) od))
ltac:(cbn; lia)) as Vbyte end end; clear HRrow end.
(* The column step's branch `bne s2,a0` at 0x85878 compares c + 1 with the width. *)
Lemma bsc_br : forall E c w, ew E 621 = Z_to_bv 64 c -> ew E 34 = Z_to_bv 64 w -> 0 <= c < 2 ^ 62 -> 0 <= w < 2 ^ 62 ->
(U E (SOff 621 1) =? U E (SOff 34 0)) = (c + 1 =? w).
Proof. intros E c w Hc Hw Rc Rw. rewrite (U_atom_off E 621 c 1 Hc), (U_atom E 34 w Hw) by lia. reflexivity. Qed.
Lemma bsc_br' : forall E c w, ew E 621 = Z_to_bv 64 c -> ew E 34 = Z_to_bv 64 w -> 0 <= c < 2 ^ 62 -> 0 <= w < 2 ^ 62 ->
(U E (SOff 34 0) =? U E (SOff 621 1)) = (w =? c + 1).
Proof. intros E c w Hc Hw Rc Rw. rewrite (U_atom_off E 621 c 1 Hc), (U_atom E 34 w Hw) by lia. reflexivity. Qed.
(* Drop what the column step replaces: the row region, and the three atoms' facts and aliases. *)
Ltac bsc_drop_row HS RL FL0 :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs' := eval vm_compute in RL in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_submem Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end; norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let fa' := eval vm_compute in FL0 in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa' [] [] HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end; norm_ss HS.
(* Re-declare the three row aliases of bs_al at a cut. *)
Ltac bsc_add_aliases HS F cc HF0 HF1 Hcc :=
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (bs_alias_ok Ev F cc 2 ltac:(assumption) ltac:(assumption) ltac:(assumption)
HF0 HF1 Hcc ltac:(clear - HF0; lia))) as HS3; clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (bs_alias_ok Ev F cc 1 ltac:(assumption) ltac:(assumption) ltac:(assumption)
HF0 HF1 Hcc ltac:(clear - HF0; lia))) as HS3; clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (bs_alias_ok Ev F cc 0 ltac:(assumption) ltac:(assumption) ltac:(assumption)
HF0 HF1 Hcc ltac:(clear - HF0; lia))) as HS3; clear HS; rename HS3 into HS end; norm_ss HS.
(* Hide every disjunction and every `_ mod _ = _` fact of the context behind ACj1's `boxed`, so that lia no longer
   reads them. Measured on this proof: with the alignment facts visible, xlia took 36% of the tactic time; with
   them boxed, 5%. *)
Ltac bsc_box_all := repeat match goal with
| H : _ \/ _ |- _ => box H
| H : _ mod _ = _ |- _ => box H end.
Lemma pb_bs_cell : bs_cell_spec B.
Proof.
unfold bs_cell_spec.
intros z ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos c p Ec ms3 md3 Q HCTX Hc Hp HENV HS HMEM K1 K2 K3.
bsc_cut_intro HCTX HENV HMEM ly S W mem md fpos S2 cid pos Ec ms3 md3.
rewrite IMG_LO_B_val, IMG_TOP_B_val in Hob241, Hob242, Hob276, Hob277, Huar.
(* F's place off image B is a disjunction every full-context lia would split on; only the image-range carries
   below read it, so it is boxed here and unboxed there. *)
box HFIMG.
assert (HbF0 : 0 <= F) by (clear - HF4096; lia).
assert (HbF1 : F + 256 < 2 ^ 64) by (clear - HFceil C1; lia).
assert (Hsp1al16 : sp1 mod 16 = 0)
by (pose proof (Z.div_mod sp1 32 ltac:(lia)) as D; rewrite Hsp1al, Z.add_0_r in D; rewrite D;
replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia; apply Z_mod_mult).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Hsp8 : spZ regs mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hal16; [|lia]; destruct Hal16 as [q Hq]; exists (2 * q); lia).
assert (HKV : forall a, F + 32 <= a < F + 32 + (3 * c + p) -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros; reflexivity).
assert (HKT : forall a, tx <= a < tx + 460 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros; reflexivity).
assert (HIMG : forall a, 0x10000 <= a < 0x5fb000 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros; reflexivity).
(* From here on the disjunctions (HdFC, HtxF) and the alignment facts (Hal16, Hsp1al16, ...) are boxed; the steps
   that read them unbox them in their own cleared context. *)
bsc_box_all.
assert (Hp3 : p = 0 \/ p = 1 \/ p = 2) by lia.
destruct Hp3 as [Ep | [Ep | Ep]]; destruct z.
all: rewrite Ep in HS; norm_ss HS; bsc_narrow HS.
(* ---- to the call of reac_headamp_tx_effective (0x8584c) ---- *)
all: paj_run_shc RUNP RUNC HS HJ2; [awrFL_with ltac:(idtac; bsc_row_rule AG fpos F EFA0 Hc Hw1) AG fpos F EFA0 |].
all: upd_rngW HKV HFr ltac:(clear - Ha_rng Hc Hw1 Hp HF4096 HFceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 Ep Hc Hw1 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; revert Hrg_rng; evalE AG;
first [ (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)
| (intros Hrg_rng; match goal with |- ?g => idtac "HKVFAIL" g end; match type of Hrg_rng with ?t => idtac t end; match type of Ha_rng with ?t => idtac t end; fail 1) ]).
all: lazymatch goal with |- SRr _ _ _ _ => idtac | |- ?g => idtac "LEFTOVER" g; fail end.
all: upd_rngW HKT HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 Ep Hc Hw1 Htx4096 Htxceil Htxia HtxF HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; unbox; revert Hrg_rng; evalE AG;
first [ (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)
| (intros Hrg_rng; match goal with |- ?g => idtac "HKTFAIL" g end; match type of Hrg_rng with ?t => idtac t end; match type of Ha_rng with ?t => idtac t end; fail 1) ]).
all: lazymatch goal with |- SRr _ _ _ _ => idtac | |- ?g => idtac "LEFTOVER2" g; fail end.
all: upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 Ep Hc Hw1 HFIMG HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; unfold boxed in HFIMG; revert Hrg_rng; evalE AG;
first [ (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)
| (intros Hrg_rng; match goal with |- ?g => idtac "HIMGFAIL" g end; match type of Hrg_rng with ?t => idtac t end; match type of Ha_rng with ?t => idtac t end; fail 1) ]).
all: lazymatch goal with |- SRr _ _ _ _ => idtac | |- ?g => idtac "LEFTOVER3" g; fail end.
all: upd_aboveW HUP HFr AG; clear HF HFr HG.
all: pose proof (rod_img_kept B W W _ _ HIMG HROD3) as HRODc.
all: prreg HS (10%bv : bv 5) Rb0; prreg_raw HS (11%bv : bv 5) Rb1; prreg HS (12%bv : bv 5) Rb2; prreg HS (1%bv : bv 5) Rbra;
prreg HS (2%bv : bv 5) Rbsp; prreg HS (3%bv : bv 5) Rbgp; prreg HS (4%bv : bv 5) Rbtp; prreg HS (8%bv : bv 5) Rbs0.
(* the call chain: the saved ra and s0 at sp - 8 and sp - 16 *)
all: lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msY) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msY) 7 _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; try rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qra) ltac:(cbn; lia)) as Vra2;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; try rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qs0) ltac:(cbn; lia)) as Vs02
end; clear HRstk;
assert (Hch2 : achain ly (aview SEGS (w_H W) (ms_mem msY)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch))
by (replace (spZ regs + -8) with (spZ regs - 8) in Vra2 by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs02 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch ltac:(lia) HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra2 Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs02 Qs0) Hra4 ltac:(lia) Hsp8 ltac:(lia) ltac:(lia)));
clear Vra2 Vs02 end.
all: lazymatch goal with |- SRr _ _ {| cfg_ms := ?msX; cfg_model := _ |} _ =>
assert (HTobj6 : obj_at SEGS (mrestrict (w_H W) (ms_mem msX)) tx ATx.LAY_TX (ATx.tx_vals T))
by (apply (obj_at_transport_range SEGS _ _ tx ATx.LAY_TX (ATx.tx_vals T) 460 HOBJ); [vm_compute; reflexivity|];
intros i Hi; apply (mbyte_of_aview SEGS); apply HKT; lia) end.
all: pmkst HS.
all: rewrite pa_sigma_reac_headamp_tx_effective.
all: fs_roF HS.
all: eapply SRr_bind; [ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (cl_callS B LAWS W (ms_regs msX) (ms_mem msX) _ BSW_STK (spZ regs) (C.tb_reac_grant_build_sweep_FP s al mx base w) ly S W mem md [(2, fpos)] ly S2 mdX 0
C.STK_reac_headamp_tx_effective [] 0 (sp1 - spZ regs) (getr (ms_regs msX) 1) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S2 /\ W' = W /\ getr regs' 10 = w64 (eff T tx (base + c) p) /\
(tx <> 0 -> obj_at SEGS (mrestrict (w_H W) mem') tx ATx.LAY_TX (ATx.tx_vals T))) HJ2) end;
[ unfold spZ at 1; rewrite Rbsp; evalE AG
| unbox; rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16; reflexivity
| lia
| unfold C.STK_reac_headamp_tx_effective; rewrite Hes; lia
| rewrite FFS; unfold C.STK_reac_headamp_tx_effective; rewrite Hes; lia
| rewrite Rbgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; try rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rbtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; try rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| reflexivity
| rewrite Rbra; apply ret_ok_codeptr_v; [lia | reflexivity]
| rewrite Rbra; pose proof pa_B_ok as HB; rewrite unsigned_lit_small by lia; lia
| replace (spZ regs + (sp1 - spZ regs)) with sp1 by lia;
replace (s0Z _) with (spZ regs) by (unfold s0Z; rewrite Rbs0; evalE AG); exact Hch2
| intros HPRE7;
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg ?pcx ?mm ?rom) ?mdd) _ =>
change (mkCfg (mkst rg pcx mm rom) mdd) with (cfg_at SEGS (BASE + AF_reac_headamp_tx_effective) rg mm mdd) end;
apply (TEFF ly S2 W _ _ _ _ tx (base + c) p T HPRE7);
[ rewrite Rb0; try rewrite (AG 13%nat) by lia; exact E13
| rewrite Rb1; first [ exact (bsc_ch_denot _ base c E33 E621 ltac:(lia) ltac:(lia) ltac:(lia))
| exact (bsc_ch_denot0 _ base c E33 E621 ltac:(lia) ltac:(lia) ltac:(lia)) ]
| rewrite Rb2, Ep; reflexivity
| lia | lia | exact HTlen
| right; split; [exact HtxS2 | exact HTobj6] ]
| let a := fresh "a" in let rg := fresh "rg" in intros a (rg & [] & _) ]
| ].
all: cbv beta; intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HJ7c & HP7 & (-> & -> & -> & Ha07 & HTobj7')).
all: assert (HTobj7 : obj_at SEGS (mrestrict (w_H W) mem7) tx ATx.LAY_TX (ATx.tx_vals T)) by (apply HTobj7'; lia); clear HTobj7'.
all: rewrite Rbra.
(* ---- after the call: what it kept ---- *)
all: lazymatch type of HJ7c with ajournal _ _ _ _ _ _ _ _ ?memc _ _ _ _ _ _ _ _ =>
assert (HK7 : acall_kept SEGS B ly S2 W memc W mem7 (spZ regs + (sp1 - spZ regs) - C.STK_reac_headamp_tx_effective) (spZ regs + (sp1 - spZ regs)) (fun _ => False))
by (eapply (acall_kept_of_journal SEGS B Hsegs); [exact HJ7c | exact (proj1 HJ2) | intros a (rg & [] & _) | intros b m i Hb _ _; exact Hb | exact sink_closed_nil]);
assert (KF7 : forall a, F <= a < F + 256 -> aview SEGS (w_H W) mem7 a = aview SEGS (w_H W) memc a)
by (pose proof HK7 as (_ & _ & _ & K74 & _); intros a Ha; apply (K74 2 fpos a Hfin2);
[left; unfold in_zr, frame_rng; cbn [fst snd]; fold F; change (fs_frame_bytes 2) with 256; lia | intros []]) end.
all: pose proof HK7 as (K71 & _).
all: pose proof (rod_acall_kept B ly S2 W W _ mem7 _ _ _ HK7 HRODc) as HRODd.
all: assert (HUP7 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem7 a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite <- (HUP a Ha); apply K71; lia).
all: clear HUP K71; rename HUP7 into HUP.
all: assert (HKV7 : forall a, F + 32 <= a < F + 32 + (3 * c + p) -> aview SEGS (w_H W) mem7 a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros a Ha; rewrite KF7 by lia; apply HKV; exact Ha).
all: clear HKV KF7 HKT HIMG HRODc; rename HKV7 into HKV.
all: assert (HKT : forall a, tx <= a < tx + 460 -> aview SEGS (w_H W) mem7 a = aview SEGS (w_H W) mem7 a) by (intros; reflexivity).
all: assert (HIMG : forall a, 0x10000 <= a < 0x5fb000 -> aview SEGS (w_H W) mem7 a = aview SEGS (w_H W) mem7 a) by (intros; reflexivity).
all: aconstsF HJ2 Qgot7p Qcell7p Qguar7p Quar7p; aconstsF HJ7 Qgot7 Qcell7 Qguar7 Quar7.
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ7) Hfin2) as (_ & _ & HFp7 & HFSp7).
all: fold F in HFp7, HFSp7; change (fs_frame_bytes 2 / 8) with 32 in HFSp7; change (fs_frame_bytes 2) with 256 in HFp7.
all: reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first [ bsc_kept_frames HK7 AG Hfin2 HfinS2 HFp7 F Hf64 Hfb64 Hflo Hfhi
| keptFL HK7 HJ7 AG Qgot7p Qgot7 Qcell7p Qcell7 Qguar7p Qguar7 Quar7p Quar7 ltac:(idtac; fail)
ltac:(idtac; match goal with |- apresent _ _ ?x => apply (proj1 (HFp7 x ltac:(lia))) end)
| match goal with |- ?g => idtac "KEEPFAIL" g end; fail ]).
all: fs_rwF HS E529 HFSp7.
(* ---- from the return (0x85850): the UBSan bound check and the store of the byte at F + 32 + 3c + p ---- *)
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
let a0v := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in
lazymatch a0v with SOff ?k 0 =>
prreg HS (10%bv : bv 5) Ra0;
assert (Eeff : ew Ev k = Z_to_bv 64 (eff T tx (base + c) p)) by (rewrite <- Ra0; exact Ha07) end end.
1-4: paj_run_to_sh RUNTOP HS HJ7 19972; [awrFL_with ltac:(idtac; bsc_row_rule AG fpos F EFA0 Hc Hw1) AG fpos F EFA0 |].
5,6: paj_run_sh RUNP HS HJ7; [awrFL_with ltac:(idtac; bsc_row_rule AG fpos F EFA0 Hc Hw1) AG fpos F EFA0 |].
(* ---- after the store: the written bytes, the table, the image and the caller's stack kept ---- *)
all: upd_rngW HKV HFr ltac:(clear - Ha_rng Hc Hw1 Hp HF4096 HFceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 Ep Hc Hw1 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: lazymatch goal with |- SRr _ _ _ _ => idtac | |- ?g => idtac "LEFTOVER-V" g; fail end.
all: upd_rngW HKT HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 Ep Hc Hw1 Htx4096 Htxceil Htxia HtxF HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; unbox; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: lazymatch goal with |- SRr _ _ _ _ => idtac | |- ?g => idtac "LEFTOVER-T" g; fail end.
all: upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 Ep Hc Hw1 HFIMG HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; unfold boxed in HFIMG; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: lazymatch goal with |- SRr _ _ _ _ => idtac | |- ?g => idtac "LEFTOVER-I" g; fail end.
all: upd_aboveW HUP HFr AG; clear HF HFr HG.
all: pose proof (rod_img_kept B W W _ _ HIMG HRODd) as HROD9.
all: subst p.
(* ---- p < 2: the next cell, ss_I (p + 1) ---- *)
1-4: bsc_vbyte HS AG Eeff F c T tx base Vbyte.
1-4: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ7) Hfin2) as (_ & _ & HFp8 & _).
1-4: (fold F in HFp8; change (fs_frame_bytes 2) with 256 in HFp8).
1-4: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx 0 r (set_window r 0 3) HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 3 (st_ok_pi_region_nth Ex ssx msx 0 r HS eq_refl)
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E619, unsigned_lit_small by lia;
let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFp8 (F + 32 + 3 * c + o) ltac:(lia)))))) as HS3;
clear HS; rename HS3 into HS end; norm_ss HS.
1-4: clear Eeff Ra0.
1-4: first [ bs_rejoin HS AG (bs_row :: bs_RL0 true) (bs_FL true 117 39) bs_al bs_deads_I 600%nat
| bs_rejoin HS AG (bs_row :: bs_RL0 false) (bs_FL false 117 39) bs_al bs_deads_I 600%nat ].
1-4: (ACj1.rebaseE HS AG HEv; clear HEv).
1-4: lazymatch type of K1 with _ -> forall _ _ _, _ -> st_ok_pi _ _ _ ?ssK _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx => first [change ssx with ssK in HS | idtac "SEATFAIL" ssx; fail] end end.
1-4: eapply (K1 ltac:(lia)); [ | exact HS | ]; [ (unfold bs_env;
split; [match goal with H : img_env _ _ ?Ev |- img_env _ _ ?Ev => exact H end|];
split; [let n := fresh "n" in let r := fresh "r" in let Hn := fresh "Hn" in let Hr := fresh "Hr" in
intros n r Hn; destruct (bv_unsigned_in_range _ r) as [_ Hr]; change (bv_modulus 5) with 32 in Hr;
try rewrite (AG n) by lia; apply EE; exact Hn|];
repeat (split; [first [assumption | (rewrite (AG 32%nat) by lia; exact E32)] |]);
first [assumption | (rewrite (AG 32%nat) by lia; exact E32)]) | (split; [exact HJ7|]; split; [exact HUP|]; split; [exact HROD9|]; split;
[ eapply (bsc_vals (w_H W) _ _ F T tx base w c); [exact Hc | lia | exact HVALS | exact HKV | exact Vbyte]
| apply (obj_at_transport_range SEGS _ _ tx ATx.LAY_TX (ATx.tx_vals T) 460 HTobj7); [vm_compute; reflexivity|];
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply (mbyte_of_aview SEGS); apply HKT; lia ]) ].
(* ---- p = 2: the column step and its branch `bne s2,a0` (0x85878) ---- *)
all: psrr_branch_pi RUNP BR HS.
(* The branch's direction, read off the run itself: taken (c + 1 < w) reaches the loop head 0x85820 (19940,
   ss_L); not taken (c + 1 = w) falls through `j` to the instruction after the loop 0x85890 (20052, ss_X). *)
all: first [ paj_run_to_sh RUNTOP HS HJ7 19940; [awrFL_with ltac:(idtac; bsc_row_rule AG fpos F EFA0 Hc Hw1) AG fpos F EFA0 |]
| paj_run_to_sh RUNTOP HS HJ7 20052; [awrFL_with ltac:(idtac; bsc_row_rule AG fpos F EFA0 Hc Hw1) AG fpos F EFA0 |] ].
all: upd_rngW HKV HFr ltac:(clear - Ha_rng Hc Hw1 Hp HF4096 HFceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 Hc Hw1 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: lazymatch goal with |- SRr _ _ _ _ => idtac | |- ?g => idtac "LEFTOVER-V2" g; fail end.
all: upd_rngW HKT HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 Hc Hw1 Htx4096 Htxceil Htxia HtxF HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; unbox; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: lazymatch goal with |- SRr _ _ _ _ => idtac | |- ?g => idtac "LEFTOVER-T2" g; fail end.
all: upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E619 Hc Hw1 HFIMG HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; unfold boxed in HFIMG; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: lazymatch goal with |- SRr _ _ _ _ => idtac | |- ?g => idtac "LEFTOVER-I2" g; fail end.
all: upd_aboveW HUP HFr AG; clear HF HFr HG.
all: clear HROD9; pose proof (rod_img_kept B W W _ _ HIMG HRODd) as HROD9.
all: prreg HS (18%bv : bv 5) R18; prreg HS (27%bv : bv 5) R27.
all: rewrite E621, unsigned_lit_small in R18 by lia; rewrite E620, unsigned_lit_small in R27 by lia.
all: bsc_vbyte HS AG Eeff F c T tx base Vbyte.
all: lazymatch type of HS with
| st_ok_pi _ _ _ (mkSS 19940 _ _ _ _) _ => assert (Hcw : c + 1 < w) by (match goal with H : branch_taken _ _ _ = _ |- _ => revert H end;
first [rewrite branch_ne_U | rewrite branch_eq_U];
rewrite ?(bsc_br _ c w E621 E34 ltac:(lia) ltac:(lia)), ?(bsc_br' _ c w E621 E34 ltac:(lia) ltac:(lia));
let Hb := fresh "Hb" in intros Hb; destruct (Z.eqb_spec (c + 1) w); destruct (Z.eqb_spec w (c + 1)); cbn in Hb; first [discriminate Hb | lia])
| st_ok_pi _ _ _ (mkSS 20052 _ _ _ _) _ => assert (Hcw : c + 1 = w) by (match goal with H : branch_taken _ _ _ = _ |- _ => revert H end;
first [rewrite branch_ne_U | rewrite branch_eq_U];
rewrite ?(bsc_br _ c w E621 E34 ltac:(lia) ltac:(lia)), ?(bsc_br' _ c w E621 E34 ltac:(lia) ltac:(lia));
let Hb := fresh "Hb" in intros Hb; destruct (Z.eqb_spec (c + 1) w); destruct (Z.eqb_spec w (c + 1)); cbn in Hb; first [discriminate Hb | lia])
end.
(* ---- the column step's re-atomisation: the row, the row index and the column of column c + 1 ---- *)
all: first [ bsc_drop_row HS (bs_RL0 true) (bsc_FL0 true) | bsc_drop_row HS (bs_RL0 false) (bsc_FL0 false) ].
all: clear E619 E620 E621 Eeff Ra0.
all: bs_havoc_regs HS 900%nat bsc_deads_X.
all: (ACj1.rebaseE HS AG HEv; clear HEv).
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi 619 Ev ssx msx
[Z_to_bv 64 (F + 32 + 3 * (c + 1)); Z_to_bv 64 (3 * (c + 1)); Z_to_bv 64 (c + 1)] HS
ltac:(cbn [length]; vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
all: lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 619%nat ?ws) _ _ =>
assert (E619 : ew (havoc Eo 619 ws) 619 = Z_to_bv 64 (F + 32 + 3 * (c + 1)))
by (exact (ew_havoc_new Eo 619 ws 0 (Z_to_bv 64 0) ltac:(cbn [length]; lia)));
assert (E620 : ew (havoc Eo 619 ws) 620 = Z_to_bv 64 (3 * (c + 1)))
by (exact (ew_havoc_new Eo 619 ws 1 (Z_to_bv 64 0) ltac:(cbn [length]; lia)));
assert (E621 : ew (havoc Eo 619 ws) 621 = Z_to_bv 64 (c + 1))
by (exact (ew_havoc_new Eo 619 ws 2 (Z_to_bv 64 0) ltac:(cbn [length]; lia))) end.
all: (ACj1.rebaseE HS AG HEv; clear HEv).
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (18%bv : bv 5) (SOff 621 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E621, Z.add_0_r, unsigned_lit_small by lia;
first [exact R18 | symmetry; exact R18 | (rewrite R18; first [reflexivity | f_equal; lia])])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (27%bv : bv 5) (SOff 620 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E620, Z.add_0_r, unsigned_lit_small by lia;
first [exact R27 | symmetry; exact R27 | (rewrite R27; first [reflexivity | f_equal; lia])])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
all: bs_havoc_regs HS 600%nat bs_deads.
all: (ACj1.rebaseE HS AG HEv; clear HEv).
(* taken: the next column's row, and the loop head ss_L *)
all: lazymatch type of HS with
| st_ok_pi _ _ _ (mkSS 19940 _ _ _ _) _ =>
(lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 619 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E619, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; clear - Hc Hcw Hw1 HF4096 HFceil C1; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 620 (mkAF 0 117 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E620, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; clear - Hc Hcw Hw1; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 621 (mkAF 0 39 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E621, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; clear - Hc Hcw Hw1; lia)) as HS3;
clear HS; rename HS3 into HS end);
(assert (Hbc : 0 <= c + 1 <= 40) by (clear - Hc Hw1; lia)); bsc_add_aliases HS F (c + 1) HbF0 HbF1 Hbc;
(lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E12'' : ew Ev 12 = Z_to_bv 64 al) by (rewrite (AG 12%nat) by lia; exact E12) end);
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ7) Hfin2) as (_ & _ & HFp8 & HFSp8);
fold F in HFp8; change (fs_frame_bytes 2) with 256 in HFp8;
(lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ bs_row HS eq_refl
ltac:(unfold region_ok, bs_row; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite E619, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFp8 (F + 32 + 3 * (c + 1) + o) ltac:(lia))) | apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, bs_row; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?E619, ?E35, ?E12'', ?E529, ?RF, ?E60; evalE AG; ulits; unfold SB;
clear - Hc Hcw Hw1 Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HF8c Hf4096 Hfceil Hfhigh HdFC Hflo Hfhi Hal512 Hal8d HF8 HFq Hob241 Hob242 Hob276 Hob277 Huar; unbox;
repeat split; first [zone_lia | match goal with |- ?g => idtac "ZFAILROW" g; fail end])) as HS3;
clear HS; rename HS3 into HS end);
norm_ss HS;
(lazymatch type of K2 with _ -> _ -> forall _ _ _, _ -> st_ok_pi _ _ _ ?ssK _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let fa' := eval vm_compute in (f_atoms (ss_facts ssK)) in
let al' := eval vm_compute in (f_alias (ss_facts ssK)) in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa' [] al' HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end end); norm_ss HS;
(lazymatch type of K2 with _ -> _ -> forall _ _ _, _ -> st_ok_pi _ _ _ ?ssK _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx => first [change ssx with ssK in HS | idtac "SEATFAIL-L" ssx; fail] end end);
eapply (K2 eq_refl Hcw); [ | exact HS | ]; [ (unfold bs_env;
split; [match goal with H : img_env _ _ ?Ev |- img_env _ _ ?Ev => exact H end|];
split; [let n := fresh "n" in let r := fresh "r" in let Hn := fresh "Hn" in let Hr := fresh "Hr" in
intros n r Hn; destruct (bv_unsigned_in_range _ r) as [_ Hr]; change (bv_modulus 5) with 32 in Hr;
try rewrite (AG n) by lia; apply EE; exact Hn|];
repeat (split; [first [assumption | (rewrite (AG 32%nat) by lia; exact E32)] |]);
first [assumption | (rewrite (AG 32%nat) by lia; exact E32)]) | replace (3 * (c + 1)) with (3 * c + 2 + 1) by lia; (split; [exact HJ7|]; split; [exact HUP|]; split; [exact HROD9|]; split;
[ eapply (bsc_vals (w_H W) _ _ F T tx base w c); [exact Hc | lia | exact HVALS | exact HKV | exact Vbyte]
| apply (obj_at_transport_range SEGS _ _ tx ATx.LAY_TX (ATx.tx_vals T) 460 HTobj7); [vm_compute; reflexivity|];
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply (mbyte_of_aview SEGS); apply HKT; lia ]) ]
| _ => idtac end.
(* not taken: the instruction after the loop, ss_X *)
all: rewrite Hcw in E619, E620, E621.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 619 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E619, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; clear - Hc Hcw Hw1 HF4096 HFceil C1; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 620 (mkAF 0 120 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E620, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; clear - Hc Hcw Hw1; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 621 (mkAF 0 40 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E621, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; clear - Hc Hcw Hw1; lia)) as HS3;
clear HS; rename HS3 into HS end.
all: assert (Hbc : 0 <= w <= 40) by (clear - Hw1; lia).
all: bsc_add_aliases HS F w HbF0 HbF1 Hbc.
all: (lazymatch type of K3 with _ -> _ -> forall _ _ _, _ -> st_ok_pi _ _ _ ?ssK _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let fa' := eval vm_compute in (f_atoms (ss_facts ssK)) in
let al' := eval vm_compute in (f_alias (ss_facts ssK)) in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa' [] al' HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end end); norm_ss HS.
all: (lazymatch type of K3 with _ -> _ -> forall _ _ _, _ -> st_ok_pi _ _ _ ?ssK _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx => first [change ssx with ssK in HS | idtac "SEATFAIL-X" ssx; fail] end end).
all: eapply (K3 eq_refl Hcw); [ | exact HS | ]; [ (unfold bs_env;
split; [match goal with H : img_env _ _ ?Ev |- img_env _ _ ?Ev => exact H end|];
split; [let n := fresh "n" in let r := fresh "r" in let Hn := fresh "Hn" in let Hr := fresh "Hr" in
intros n r Hn; destruct (bv_unsigned_in_range _ r) as [_ Hr]; change (bv_modulus 5) with 32 in Hr;
try rewrite (AG n) by lia; apply EE; exact Hn|];
repeat (split; [first [assumption | (rewrite (AG 32%nat) by lia; exact E32)] |]);
first [assumption | (rewrite (AG 32%nat) by lia; exact E32)]) | replace (3 * w) with (3 * c + 2 + 1) by lia; (split; [exact HJ7|]; split; [exact HUP|]; split; [exact HROD9|]; split;
[ eapply (bsc_vals (w_H W) _ _ F T tx base w c); [exact Hc | lia | exact HVALS | exact HKV | exact Vbyte]
| apply (obj_at_transport_range SEGS _ _ tx ATx.LAY_TX (ATx.tx_vals T) 460 HTobj7); [vm_compute; reflexivity|];
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply (mbyte_of_aview SEGS); apply HKT; lia ]) ].
Qed.
End e.
End d.
End b.
