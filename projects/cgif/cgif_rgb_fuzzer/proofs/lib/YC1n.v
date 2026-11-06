(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20 YI1k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC1z YC1y YC27 YC23 YC28 YC1w YC24 YC20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis ASM1 : astack_malloc_realizes trasegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law trasegs B.
Hypothesis FFL : frame_flag_lawP trasegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Hypothesis TRAWADD : trawadd_spec B.
Lemma fl_R4_aux : fl_from B ss_R5 (INV_R5 B) -> fl_from B ss_R4 (INV_R4 B).
Proof.
intros RR5. fl_prelude.
pose proof HINV as ((gen & E180 & Rgen) & E184 & (attr & E460 & Hattr) & E470 & (pt & w & h & top & left & tidx & img & E451 & E403 & E404 & E400 & E405 & E401 & E450 & Hrpt & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & Htidx & Hpt)).
unfold fl_tmpblk, fl_FP in Hpt. cbn [c_ly c_S c_regs c_f c_s] in Hpt.
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)).
{ intros x Hx. destruct Hpt as [(_ & _ & _ & Eab3) | (_ & _ & _ & (_ & _ & _ & Eab3 & _))]; rewrite Eab3; [exact Hx | apply in_app_iff; left; exact Hx]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
assert (Hraw3 : In (cg_raw s, RAW_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hraw_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
pose proof (sep_block_frame trasegs _ LAWS ly3 S3 _ _ _ (cg_raw s) RAW_SIZE 2 fpos HAR3 Hraw3 Hfin3) as HdFR.
unfold zdisjoint in HdFR; cbn [fst snd] in HdFR; change (req_size RAW_SIZE) with 48 in HdFR; change (fs_frame_bytes 2) with 256 in HdFR; rewrite EFA3 in HdFR. fold F in HdFR.
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr f) FRAME_SIZE HAR Hraw_in Hcur_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRC.
unfold zdisjoint in HdRC. cbn [fst snd] in HdRC. change (req_size RAW_SIZE) with 48 in HdRC. change (req_size FRAME_SIZE) with 40 in HdRC.
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE g CGIF_SIZE HAR Hraw_in Hing ltac:(unfold RAW_SIZE, CGIF_SIZE; intros X; injection X; lia)) as HdRG.
unfold zdisjoint in HdRG. cbn [fst snd] in HdRG. change (req_size RAW_SIZE) with 48 in HdRG. change (req_size CGIF_SIZE) with 96 in HdRG.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan A_cgif_raw_addframe.
all: try (oblG HJ3 E10n E32n Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia). clear_frames.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x87a0c) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0; exact Usp3) end.
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview trasegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem trasegs _ _ _ _ Vra Qra) (rdword_of_val_mem trasegs _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Htop32; lia) ltac:(clear - Hsp1; lia))
| ] end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s) RAW_SIZE (proj1 HJ3) Hraw3) as (_ & _ & _ & _ & Hrpres3 & _). change (req_size RAW_SIZE) with 48 in Hrpres3.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
destruct (obj_at_hole4 (mrestrict (w_H W) mem) (mrestrict (w_H Wx) (ms_mem msX)) (cg_raw s) LAY_Raw 48 (traw_vals g s) 8 40
Oraw ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
ltac:(intros j Hj Hnj; apply (mbyte_of_aview trasegs); pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
apply (F2 (cg_raw s) RAW_SIZE j Hraw_in Hraw3 ltac:(change (req_size RAW_SIZE) with 48; exact Hj));
intros (r & Hr & Ha); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; [clear - Ha Hj HdRC; lia | clear - Ha Hj Hnj; lia])
ltac:(intros j Hj; destruct (proj1 (Hrpres3 (cg_raw s + 40 + j) ltac:(clear - Hj; lia))) as [Hh [b Hb]];
unfold mbyte, mrestrict; cbn [ms_mem]; rewrite Hh; cbn; rewrite Hb; eexists; reflexivity))
as (rcX & HrcX & OrawX) end.
cbn [traw_vals list_set] in OrawX.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iF := idx_of_base rs 75%nat in let iF := eval vm_compute in iF in
let rF := eval vm_compute in (nth iF rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iF rF HS ltac:(vm_compute; reflexivity)) as HRF; cbn [ms_mem restrict] in HRF end.
assert (UF : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
Ltac fieldF HRF UF od w e V :=
lazymatch type of HRF with region_ok _ ?Ex _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region_any Ex _ 75 _ cs lo hi wlo whi od w e HRF UF ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
cbn [sv_denot] in V; rewrite ?ew_ewset_other, ?ew_havoc_old in V by nat_side;
try change (N.to_nat 8) with 8%nat in V; try change (N.to_nat 4) with 4%nat in V; try change (N.to_nat 2) with 2%nat in V; try change (N.to_nat 1) with 1%nat in V;
try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V; try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V;
try change (2 ^ (8 * Z.of_N 2)) with 65536 in V; try change (2 ^ (8 * Z.of_N 1)) with 256 in V end.
fieldF HRF UF 32 8%N (SOff 50 0) V0. fieldF HRF UF 40 8%N (SOff 450 0) V1.
lazymatch type of HRF with region_ok _ _ _ (YQ0b.mkRegion _ _ _ _ _ ?cs) =>
lazymatch cs with context [YQ0b.mkChunk 48 (CVal 4%N ?ea)] => fieldF HRF UF 48 4%N ea V2 end end.
fieldF HRF UF 52 2%N (SOff 398 0) V3. fieldF HRF UF 54 2%N (SOff 404 0) V4. fieldF HRF UF 56 2%N (SOff 400 0) V5. fieldF HRF UF 58 2%N (SOff 399 0) V6.
fieldF HRF UF 60 2%N (SExt true 16 (SOff 54 0)) V7. fieldF HRF UF 62 2%N (SOff 470 0) V8. fieldF HRF UF 64 1%N (SOff 57 0) V9. fieldF HRF UF 65 1%N (SOff 401 0) V10.
assert (Hqi : 1 <= req_size N) by (generalize HW1 HH1 HN; clear; intros; unfold req_size; destruct (Z.eqb_spec N 0); nia).
assert (Hwh0 : 0 <= w * h) by (apply Z.mul_nonneg_nonneg; clear - Hw1 Hh1; lia).
assert (Rimg : 0 <= img < 2 ^ 64) by (destruct Hpt as [(_ & -> & _) | (_ & -> & _ & (Hp1 & Hp2 & _))]; [clear - Hi4096 Hiceil Hqi C1; lia | clear - Hp1 Hp2 Hwh0; ceil; lia]).
assert (Rslct : 0 <= fl_slct (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 E0) < 65536) by (unfold fl_slct; destruct (fl_uselct _); cbn [c_f]; clear - Q5; lia).
rewrite (denot_atom_mod _ 50 (fr_lpal f) _ E50 ltac:(clear - Q0; lia)), Z.mod_small in V0 by (clear - Q0; lia).
rewrite (denot_atom_mod _ 450 img _ E450 Rimg), Z.mod_small in V1 by (exact Rimg).
rewrite (denot_atom_mod _ 398 w _ E403 ltac:(clear - Hw1 Hlw Hl0 R7; lia)), Z.mod_small in V3 by (clear - Hw1 Hlw Hl0 R7; lia).
rewrite (denot_atom_mod _ 404 h _ E404 ltac:(clear - Hh1 Hth Ht0 R8; lia)), Z.mod_small in V4 by (clear - Hh1 Hth Ht0 R8; lia).
rewrite (denot_atom_mod _ 400 top _ E400 ltac:(clear - Ht0 Hth R8 Hh1; lia)), Z.mod_small in V5 by (clear - Ht0 Hth R8 Hh1; lia).
rewrite (denot_atom_mod _ 399 left _ E405 ltac:(clear - Hl0 Hlw R7 Hw1; lia)), Z.mod_small in V6 by (clear - Hl0 Hlw R7 Hw1; lia).
rewrite (denot_atom_mod _ 470 _ _ E470 ltac:(clear - Rslct; lia)), Z.mod_small in V8 by (exact Rslct).
rewrite (denot_atom_mod _ 57 (fr_disp f) _ E57 ltac:(clear - Q7; lia)), Z.mod_small in V9 by (clear - Q7; lia).
rewrite (denot_atom_mod _ 401 tidx _ E401 ltac:(clear - Htidx; lia)) in V10. change (2 ^ (8 * 1)) with 256 in V10.
assert (Rtidx : 0 <= tidx mod 256 < 256) by (apply Z.mod_pos_bound; clear; lia).
lazymatch type of V2 with val_mem _ _ _ _ ?v => set (fattrv := v) in V2 end.
lazymatch type of V7 with val_mem _ _ _ _ ?v => set (delayv := v) in V7 end.
assert (Rfattr : 0 <= fattrv < 2 ^ 32) by (subst fattrv; apply Z.mod_pos_bound; clear; lia).
assert (Rdelay : 0 <= delayv < 2 ^ 16) by (subst delayv; apply Z.mod_pos_bound; clear; lia).
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (OcfgX : obj_at trasegs (mrestrict (w_H Wx) (ms_mem msX)) (F + 32) LAY_RawFrameConfig
[fr_lpal f; img; fattrv; w; h; top; left; delayv; fl_slct (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 E0); fr_disp f; tidx mod 256]) end.
{ cbn [obj_at LAY_RawFrameConfig]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N Pos.to_nat].
rewrite <- !Z.add_assoc. cbn [Z.add Pos.add].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536. change (2 ^ (8 * 1)) with 256.
split; [split; [exact V0 | clear - Q0; lia]|].
split; [split; [exact V1 | exact Rimg]|].
split; [split; [exact V2 | exact Rfattr]|].
split; [split; [exact V3 | clear - Hw1 Hlw Hl0 R7; lia]|]. split; [split; [exact V4 | clear - Hh1 Hth Ht0 R8; lia]|].
split; [split; [exact V5 | clear - Ht0 Hth R8 Hh1; lia]|]. split; [split; [exact V6 | clear - Hl0 Hlw R7 Hw1; lia]|].
split; [split; [exact V7 | clear - Rdelay; lia]|].
split; [split; [exact V8 | exact Rslct]|].
split; [split; [exact V9 | clear - Q7; lia]|]. split; [split; [exact V10 | exact Rtidx]|]. exact I. }
clear V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 HRF.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iG := idx_of_base rs 10%nat in let iG := eval vm_compute in iG in
let rG := eval vm_compute in (nth iG rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iG rG HS ltac:(vm_compute; reflexivity)) as HRG; cbn [ms_mem restrict] in HRG;
assert (UG : bv_unsigned (ew E 10) = g) by (rewrite E10n; apply unsigned_lit_small; clear - Hg4096 Hgceil C1; lia);
lazymatch type of HRG with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 10 g cs lo hi wlo whi 56 8%N (SOff 44 0) A_writecb HRG UG ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(unfold A_writecb; cbn; lia) ltac:(cbn; lia)) as Vwfn;
pose proof (field_of_region Ex _ 10 g cs lo hi wlo whi 64 8%N (SOff 45 0) 0 HRG UG ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 10 g cs lo hi wlo whi 80 8%N (SOff 47 0) 0 HRG UG ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vpfile end;
clear HRG UG end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iS := idx_of_base rs 88%nat in let iS := eval vm_compute in iS in
let rS := eval vm_compute in (nth iS rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iS rS HS ltac:(vm_compute; reflexivity)) as HRS; cbn [ms_mem restrict] in HRS;
assert (US : bv_unsigned (ew E 88) = SB + F / 8) by (rewrite E88; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia);
assert (ZS : forall od, In (YQ0b.mkChunk od (CVal 1 (SLit 0))) (YQ0b.r_chunks rS) -> aview trasegs (w_H W3) (ms_mem msX) (SB + F / 8 + od) = Some 0);
[ let od := fresh "od" in let Hod := fresh "Hod" in intros od Hod;
lazymatch type of HRS with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 88 (SB + F / 8) cs lo hi wlo whi od 1%N (SLit 0) 0 HRS US Hod eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vz end;
pose proof (Vz 0%nat ltac:(lia)) as Vz0; cbn [Z.of_nat] in Vz0; rewrite Z.add_0_r in Vz0;
unfold aview; rewrite Vz0; reflexivity
| clear HRS ] end.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (AF : afobj B ly3 S3 Wx (ms_mem msX) (F + 32) 40) end.
{ split; [|split].
- exists 2, fpos. split; [exact Hfin3|]. split; [clear; lia|]. rewrite EFA3. fold F. split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); apply Z_mod_mult|].
change (fs_frame_bytes 2) with 256. clear; lia.
- rewrite HFq. replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia). apply Z_mod_mult.
- apply zero_shadow_of_bytes; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); apply Z_mod_mult | reflexivity | clear; lia |].
intros j Hj. change (40 / 8) with 5 in Hj. rewrite <- SB_SHADOW_OFF.
replace ((F + 32) / 8) with (F / 8 + 4) by (rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia);
replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia); clear; lia).
replace (SB + (F / 8 + 4) + j) with (SB + F / 8 + (4 + j)) by (clear; lia).
assert (Hj5 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by (clear - Hj; lia).
destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]]; apply ZS; cbn; tauto. }
clear ZS.
assert (HBL : exists Nimg rest0, Permutation (ablocks B ly3 S3) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest0) /\
w * h <= Nimg /\ (Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0)).
{ destruct Hpt as [(Hp0 & Eimg & _ & Eab3) | (Hp1 & Eimg & _ & (_ & _ & _ & Eab3 & _))].
- destruct (flush_blocks_img0 g s N rest i f Hf) as (rest0 & HP0 & Hl0').
exists N, rest0. rewrite Eab3, Eimg. split; [exact (Permutation_trans HPerm HP0)|]. split; [|exact Hl0'].
rewrite HN. apply Z.mul_le_mono_nonneg; clear - Hw1 Hlw Hl0 Hh1 Hth Ht0; lia.
- destruct (flush_blocks_img1 g s N rest f pt (w * h) Hfi) as (rest0 & HP0 & Hl0').
exists (w * h), rest0. rewrite Eab3, Eimg. split; [|split; [clear; lia | exact Hl0']].
eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. eapply Permutation_trans; [apply perm_skip; exact HPerm | exact HP0]. }
destruct HBL as (Nimg & rest0 & HBL & HwN & Hlct).
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3' & _).
assert (HEVc : vev S3 + EV_RAWADD <= VEV_MAX).
{ replace EV_RAWADD with 27 by reflexivity. rewrite HEV in Hev.
destruct Hpt as [(_ & _ & Hk0 & _) | (_ & _ & Hk2 & _)]; [clear - Hnev3 Hev Hk0 | clear - Hnev3 Hev Hk2]; lia. }
assert (HLIVEc : blocks_bytes S3 + LIVE_RAWADD <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3). unfold LIVE_FLUSH in Hlive. unfold LIVE_RAWADD.
destruct Hpt as [(_ & _ & _ & Eab3) | (_ & _ & _ & (_ & _ & _ & Eab3 & _))]; rewrite Eab3.
- rewrite <- (blocks_bytes_bsum B ly S). clear - Hlive. lia.
- rewrite bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. rewrite HN in HNle.
assert (Hwh : w * h <= cg_W s * cg_H s) by (apply Z.mul_le_mono_nonneg; clear - Hw1 Hlw Hl0 Hh1 Hth Ht0; lia). clear - Hlive HNle Hwh Hwh0. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call trasegs B LAWS tra_segs_low W3 Ex ssX msX TFLUSH_STK (spZ regs) _ ly S W mem md [(2, fpos)] ly3 S3 mdX k
TRAWADD_STK [(cg_raw s + 40, cg_raw s + 44)] EV_RAWADD (sp1 - spZ regs) (ew Ex 2) (Z_to_bv 64 0x87a0c) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => exists res rcur' : Z, getr regs2 10 = w64 res /\ 0 <= res < 2 ^ 64 /\
obj_at trasegs (mrestrict (w_H W2) mem2) (cg_raw s) LAY_Raw [A_cgif_writecb; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rcur'] /\
Permutation (ablocks B ly2 S2) (ablocks B ly3 S3)) HS eq_refl HJ3);
[ first [ rewrite Rsp, E70; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Usp3; f_equal; clear; lia | match goal with |- ?g => idtac "AJ1" g end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ exact Usp3 | idtac "AJ3" ]
| first [ rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity | match goal with |- ?g => idtac "AJ4" g end ]
| first [ clear - Hsp1; lia | idtac "AJ5" ]
| first [ apply Zle_bool_imp_le; vm_compute; reflexivity | idtac "AJ6" ]
| first [ replace TRAWADD_STK with 17040 by reflexivity; rewrite FFS; clear - Hsp1; lia | match goal with |- ?g => idtac "AJ7" g end ]
| first [ rewrite Rgp, Ugp; exact Hgp | idtac "AJ8" ]
| first [ rewrite Rtp, Utp; exact Htp | idtac "AJ9" ]
| first [ exact Rra | idtac "AJ10" ]
| first [ apply ret_ok_even; vm_compute; reflexivity | idtac "AJ11" ]
| first [ rewrite unsigned_lit_small by (clear; lia); clear; lia | idtac "AJ12" ]
| first [ rewrite Es0X; replace (spZ regs + (sp1 - spZ regs)) with sp1 by (clear; lia); exact Hch1 | match goal with |- ?g => idtac "AJ13" g end ]
| first [ intros HPRE1; eapply SRr_mono;
[ first [ pose proof (TRAWADD ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch)
(cg_raw s) g (F + 32) (rw_gct s) (rw_attr s) (cg_W s) (cg_H s) (raw_sgct s) (rw_loops s) rcX 0
(fr_lpal f) img fattrv w h top left delayv (fl_slct (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 E0)) (fr_disp f) (tidx mod 256) Nimg rest0 HPRE1) as CALL | idtac "CALL-POSE" ];
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 A_cgif_raw_addframe) with (Z_to_bv 64 559760) in CALL;
first [ apply CALL | match goal with |- ?g => idtac "CALL-APPLY" g end; let t := type of CALL in idtac "CALL-TYPE" t ]; clear CALL;
[ first [ rewrite EspX; exact Hsp1al | idtac "CA1" ]
| first [ rewrite EraX; cbn [spine map fst snd]; apply ctx_flush_rawadd; exact Hctx | match goal with |- ?g => idtac "CA2" g end ]
| first [ rewrite Hfrs3; cbn [length]; clear - Hroom; lia | idtac "CA3" ]
| first [ eapply arodata_ok_journal; [exact HJ3 | exact HROD] | idtac "CA4" ]
| first [ rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E46 | match goal with |- ?g => idtac "CA5" g end ]
| first [ rewrite Ra1, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite UF; reflexivity | match goal with |- ?g => idtac "CA6" g end ]
| first [ exact AF | idtac "CA7" ]
| first [ exact OcfgX | match goal with |- ?g => idtac "CA8" g end ]
| first [ exact OrawX | match goal with |- ?g => idtac "CA9" g end ]
| first [ unfold raw_sgct; destruct (Z.eqb_spec (Z.land (cg_attr s) 4) 0); [apply Hngp; assumption | clear; lia] | idtac "CA10" ]
| first [ exact Vwfn | idtac "CA11" ]
| first [ exact Vctx | idtac "CA12" ]
| first [ clear; lia | idtac "CA13" ]
| first [ exact Vpfile | idtac "CA14" ]
| first [ exact Hw1 | idtac "CA15" ]
| first [ exact Hh1 | idtac "CA16" ]
| first [ rewrite HN in HNle; eapply Z.le_trans; [|exact HNle]; apply Z.mul_le_mono_nonneg; clear - Hw1 Hlw Hl0 Hh1 Hth Ht0; lia | idtac "CA17" ]
| first [ exact HwN | idtac "CA18" ]
| first [ exact HBL | idtac "CA19" ]
| first [ unfold fl_slct, fl_uselct; cbn [c_f]; destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0) as [Hz|Hz]; cbn [negb]; intros Hsl; [exfalso; clear - Hsl; lia|];
destruct (in_split _ _ (Hlct Hz)) as (l1 & l2 & El); exists (3 * fr_nlp f), (l1 ++ l2); split;
[rewrite El; apply Permutation_sym; apply Permutation_middle | clear; lia] | match goal with |- ?g => idtac "CA20" g end ]
| first [ exact HEVc | match goal with |- ?g => idtac "CA21" g end ]
| first [ exact HLIVEc | match goal with |- ?g => idtac "CA22" g end ] ]
| first [ cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HPc & res & rcur' & Hres & Hres64 & Oraw4 & HPerm4);
exists ly4, S4, regs4, mem4, md4; split; [rewrite Rra; reflexivity|]; split; [exact HJc|];
split; [exact HPc|]; exists res, rcur'; repeat (split; [assumption|]); exact HPerm4 | match goal with |- ?g => idtac "CALL-POST" g end ] ]
| idtac "AJ14" ]
| first [ intros a (r & Hr & Ha); left; cbn [In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Ha; split;
[ exists (cg_raw s + 40, cg_raw s + 44); split; [right; left; reflexivity | cbn [fst snd]; exact Ha]
| exists (cg_raw s), RAW_SIZE; split; [exact Hraw3 | change (req_size RAW_SIZE) with 48; clear - Ha; lia] ]
| match goal with |- ?g => idtac "AJ15" g end ] ]
| ] end end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & res & rcur' & Hres & Hres64 & Oraw4 & HPerm4).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HJc by (clear; lia).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra1 Vra Vs0 Hch1 OcfgX OrawX AF Vwfn Vctx Vpfile.
pose proof (proj1 HJ4) as HAR4.
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs4 & _). cbn [app] in Hfrs4.
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hing3).
assert (Hcur4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hcur3).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (2, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR4 Hcur4) as (_ & _ & _ & _ & Hcpres4 & _). change (req_size FRAME_SIZE) with 40 in Hcpres4.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4' & _).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (HnFP_lo : forall a, SB <= a < 17594333495296 -> ~ inFP [(cg_raw s + 40, cg_raw s + 44)] a)
by (intros a Ha (r & Hr & Hx); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Hx; clear - Ha Hx Hrh_ia C3; change (req_size RAW_SIZE) with 48 in Hrh_ia; unfold SB in Ha; zone_lia).
assert (HnFP_F : forall a, F <= a < F + 256 -> ~ inFP [(cg_raw s + 40, cg_raw s + 44)] a)
by (intros a Ha (r & Hr & Hx); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Hx; clear - Ha Hx HdFR; lia).
assert (HnFP_G : forall a, g <= a < g + 96 -> ~ inFP [(cg_raw s + 40, cg_raw s + 44)] a)
by (intros a Ha (r & Hr & Hx); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Hx; clear - Ha Hx HdRG; lia).
assert (HnFP_C : forall a, fr_ptr f <= a < fr_ptr f + 40 -> ~ inFP [(cg_raw s + 40, cg_raw s + 44)] a)
by (intros a Ha (r & Hr & Hx); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Hx; clear - Ha Hx HdRC; lia).
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFP_lo; clear - Ha HF8lo HF8c HFceil C1; ceil; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFP_F; clear - Ha; lia | intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub trasegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 70%nat); [exact HJc | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub trasegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJc | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_sub trasegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat _ _ _ _ _ g CGIF_SIZE HJc);
[ evalE AG | exact Hing3 | exact Hing4 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia | intros a Ha; apply HnFP_G; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_subw B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 11%nat _ _ _ _ _ (fr_ptr f) FRAME_SIZE HJc);
[ evalE AG | exact Hcur3 | exact Hcur4 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia
| intros a Ha; apply HnFP_C; clear - Ha; lia | intros a Ha; apply (proj1 (Hcpres4 a ltac:(clear - Ha; lia))) ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (10%bv : bv 5) Rres. rewrite Hres in Rres.
lazymatch goal with HS : st_ok _ _ _ _ |- _ => ra_join HS ss_R5 491%nat ([] : list (bv 5)) ltac:(idtac); fl_hand RR5 HS end.
split; [destruct Hpt as [(_ & _ & Hk0 & _) | (_ & _ & Hk2 & _)]; [clear - Hk0 | clear - Hk2]; lia|].
split; [exists res; split; [rewrite !ew_havoc_old by (clear; lia); symmetry; exact Rres | exact Hres64]|].
exists pt. cbn [c_ly c_S].
split; [rewrite !ew_havoc_old by (clear; lia); exact E451|]. split; [exact Hrpt|].
destruct Hpt as [(Hp0 & _ & _ & Eab3) | (Hp1 & _ & _ & (Hq1 & Hq2 & Hq3 & Eab3 & Hawr & Haft))].
- left. split; [exact Hp0|]. rewrite <- Eab3. exact HPerm4.
- right. split; [exact Hp1|]. exists (w * h). split; [exact Hwh0|]. split; [rewrite <- Eab3; exact HPerm4|]. exact Haft.
Qed.
Lemma fl_R4 : fl_from B ss_R5 (INV_R5 B) -> fl_from B ss_R4 (INV_R4 B).
Proof. exact fl_R4_aux. Qed.
End d.
End c.
