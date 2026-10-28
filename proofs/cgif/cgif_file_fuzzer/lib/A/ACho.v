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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACkc ACj4 ACj9.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7 ACj3.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACih ACii ACi4.
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
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis TLF : PALibF B.
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Variable wfn : Z.
Variable KS : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B KS.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Variable XN : xnums.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AFREEN4 : afree_null04_rule SEGS B MT.
Hypothesis HTR : forall (pcf ra : Z) (regsT regs : bvmap 5 word) ch,
In (raZ regs :: spine ch) CTX -> raZ regsT = ra ->
((pcf = pc_free_ra0 (as_code B) /\ ra = BASE + 0x2448) \/ (pcf = pc_malloc_ra0 (as_code B) /\ ra = BASE + 0x1fd4) \/
(pcf = pc_malloc_ra0 (as_code B) /\ ra = BASE + 0x2124)) ->
In (call_trace0 pcf regsT ((spZ regs, raZ regs, s0Z regs) :: ch)) (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma fl_R5X_aux : fl_fromX1 KS MT XN B CTX wfn ss_X (INV_XX KS MT XN B) -> fl_fromX1 KS MT XN B CTX wfn ss_R5 (INV_R5X KS MT XN B).
Proof.
intros RX. fl_preludeX.
pose proof HINV as (Hk3 & (res & E920 & Hres & ((code & bytes & HFL & Hcode & Vrc & HSINK3 & HLEN3) & (acc & MLE3 & HaccM & HaccN))) & E621X & (pt & E892 & Hrpt & Hpt)).
unfold fl_FPX in Hpt. cbn [c_ly c_S c_regs c_f c_s x_pf] in Hpt.
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)).
{ intros x Hx. destruct Hpt as [(_ & HP3) | (_ & (n & _ & HP3 & _))]; (eapply Permutation_in; [apply Permutation_sym; exact HP3|]); [exact Hx | apply in_app_iff; left; exact Hx]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (apply Hsub3; exact Hpf_in).
assert (Hraw3 : In (cg_raw s, RAW_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hraw_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
pose proof (sep_block_frame SEGS _ LAWS ly3 S3 _ _ _ (cg_raw s) RAW_SIZE 2 fpos HAR3 Hraw3 Hfin3) as HdFR.
unfold zdisjoint in HdFR; cbn [fst snd] in HdFR; change (req_size RAW_SIZE) with 48 in HdFR; change (fs_frame_bytes 2) with 256 in HdFR; rewrite EFA3 in HdFR. fold F in HdFR.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr f) FRAME_SIZE HAR Hraw_in Hcur_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRC.
unfold zdisjoint in HdRC. cbn [fst snd] in HdRC. change (req_size RAW_SIZE) with 48 in HdRC. change (req_size FRAME_SIZE) with 40 in HdRC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x528c8.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xsink_stretchF HFr HSINK3. xval_stretchF Vrc.
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
first [ clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia | revert Hrg; evalE AG; intros Hrg; clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia ] |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
clear_frames.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
prreg HS (10%bv : bv 5) Ra0.
lazymatch type of AG with forall n, _ -> ew ?Ebase n = _ => assert (Usp3 : bv_unsigned (ew Ebase 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia);
assert (EraX : raZ rg = (BASE + 0x2448)) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi Hob241 Hob242 Hob253 Huar; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS Hob241 Hob242 Hob253 Huar; lia) Qal8
ltac:(clear - Htop32 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia))
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS Hob241 Hob242 Hob253 Huar; lia) Qal8
ltac:(clear - Htop32 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia))
| ]  end.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3' & _).
assert (HEVc : st_nev S3 < EV_MAX).
{ replace EV_RAWADD with 27 in Hk3 by reflexivity. rewrite HEV in Hev. clear - Hnev3 Hev Hk3. lia. }
pmkst HS.
ppcs.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
apply (SRr_bind SEGS _ _
(fun W4 c4 => exists ly4 S4 regs4 mem4 md4,
c4 = mkCfg (mkst regs4 (Z_to_bv 64 (BASE + 0x2448)) mem4 (seg_rom SEGS)) md4 /\
ajournal SEGS B TFLUSH_STK (spZ regs) ((fr_ptr f + 20, fr_ptr f + 24) :: (cg_raw s + 40, cg_raw s + 44) :: asink_fp pf) ly S W mem md [(2, fpos)] ly4 S4 W4 mem4 md4 (k + 1) /\
aregs_preserved (ms_regs msX) regs4 /\ Permutation (ablocks B ly4 S4) (ablocks B ly S) /\ frames S4 = frames S3 /\
(exists Er : Z -> Prop, acall_kept SEGS B ly3 S3 W3 (ms_mem msX) W4 mem4 (sp1 - ASTACK) sp1 Er /\
(forall a, F <= a < F + 256 -> ~ Er a) /\ (forall a, SB <= a < 17594333495296 -> ~ Er a) /\
(forall a, g <= a < g + 96 -> ~ Er a) /\ (forall a, fr_ptr f <= a < fr_ptr f + 40 -> ~ Er a) /\
(forall a, cg_raw s <= a < cg_raw s + 48 -> ~ Er a)) /\
asink_at SEGS KS (mrestrict (w_H W4) mem4) md4 pf (Sg ++ bytes) /\ mo_le MT S S4 (acc + mo_free MT))) end.
{ destruct Hpt as [(Hp0 & HP3) | (Hp1 & (n & Hn0 & HP3 & Haft))].
-
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (afree_null04_sub SEGS B LAWS pa_segs_low MT AFREEN4 W3 (ms_regs msX) (ms_mem msX) TFLUSH_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly3 S3 mdX k (sp1 - spZ regs) (Z_to_bv 64 (BASE + 0x2448)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3)
| ] end.
+ rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite E892, Hp0. reflexivity.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
+ exact Rra.
+ apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
+ exact HEVc.
+ apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | exact Es0X | rewrite EraX; clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia].
+ apply (HTR (pc_free_ra0 (as_code B)) (BASE + 0x2448)); [exact Hctx | exact EraX | left; split; reflexivity].
+   eapply (mok_station MT S S3 _ acc); [exact MLAW | exact HMOK | exact MLE3 | exact (mo_free_nonneg MT MLAW) | exact HaccM].
+ cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPerm4 & Hfrs4 & HK & MLE4 & HJf).
exists ly4, S4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
assert (HPerm4' : Permutation (ablocks B ly4 S4) (ablocks B ly S)) by (eapply Permutation_trans; [exact HPerm4 | exact HP3]).
split; [exact HPerm4'|]. split; [exact Hfrs4|].
split. { exists (fun _ => False). replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia). split; [exact HK|].
repeat split; intros a _ Hn; exact Hn. }
split; [| exact (mle_station MT S S3 S4 _ _ MLAW MLE3 MLE4)].
eapply (asink_at_kept SEGS B KS AIL); [exact HJf | exact sink_closed_nil | exact Hpf3 | | | exact HSINK3].
* eapply Permutation_in; [apply Permutation_sym; exact HPerm4'|]. exact Hpf_in.
* intros ii Hii (r & [] & _).
-
assert (Hpt3 : In (pt, n) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HP3|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pt n HAR3 Hpt3) as (_ & _ & _ & Hph_ia & _ & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_imgP _ _ _ _ _ _ pt n HAR3 Hpt3) as Hpth_img.
pose proof (sep_block_frame SEGS _ LAWS ly3 S3 _ _ _ pt n 2 fpos HAR3 Hpt3 Hfin3) as HdFP.
unfold zdisjoint in HdFP; cbn [fst snd] in HdFP; change (fs_frame_bytes 2) with 256 in HdFP; rewrite EFA3 in HdFP. fold F in HdFP.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt n g CGIF_SIZE HAR3 HP3 Hing) as HdPG. change (req_size CGIF_SIZE) with 96 in HdPG.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt n (fr_ptr f) FRAME_SIZE HAR3 HP3 Hcur_in) as HdPC. change (req_size FRAME_SIZE) with 40 in HdPC.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W3 (ms_regs msX) (ms_mem msX) TFLUSH_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly3 S3 mdX k pt n (sp1 - spZ regs) (Z_to_bv 64 (BASE + 0x2448)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 Hpt3)
| ] end.
+ rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite E892. reflexivity.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
+ exact Rra.
+ apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
+ exact HEVc.
+ apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | exact Es0X | rewrite EraX; clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia].
+ apply (HTR (pc_free_ra0 (as_code B)) (BASE + 0x2448)); [exact Hctx | exact EraX | left; split; reflexivity].
+ exact Haft.
+   eapply (mok_station MT S S3 _ acc); [exact MLAW | exact HMOK | exact MLE3 | exact (mo_free_nonneg MT MLAW) | exact HaccM].
+ cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl3 & Ebl4) & Hfrs4 & HK & MLE4 & HJf).
exists ly4, S4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
assert (HPerm4' : Permutation (ablocks B ly4 S4) (ablocks B ly S)).
{ rewrite Ebl4; apply Permutation_sym; apply (@Permutation_cons_app_inv _ _ l1 l2 (pt, n)); rewrite <- Ebl3;
apply Permutation_sym; eapply Permutation_trans; [exact HP3 | apply Permutation_app_comm]. }
split; [exact HPerm4'|]. split; [exact Hfrs4|].
pose proof (req_size_pos n Hn0) as Hrq.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt n (cg_raw s) RAW_SIZE HAR3 HP3 Hraw_in) as HdPR. change (req_size RAW_SIZE) with 48 in HdPR.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt n pf FILE_BLOCK HAR3 HP3 Hpf_in) as HdPP. change (req_size FILE_BLOCK) with 1264 in HdPP.
split. { exists (fun a => pt <= a < pt + req_size n). replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia). split; [exact HK|].
split; [intros a Ha Hx; clear - Ha Hx HdFP Hob241 Hob242 Hob253 Huar; lia|]. split; [intros a Ha Hx; clear - Ha Hx Hph_ia Hrq C3 Hob241 Hob242 Hob253 Huar; unfold SB in Ha; zone_lia|].
split; [intros a Ha Hx; clear - Ha Hx HdPG Hob241 Hob242 Hob253 Huar; lia|]. split; [intros a Ha Hx; clear - Ha Hx HdPC Hob241 Hob242 Hob253 Huar; lia|].
intros a Ha Hx; clear - Ha Hx HdPR; lia. }
split; [| exact (mle_station MT S S3 S4 _ _ MLAW MLE3 MLE4)].
eapply (asink_at_kept SEGS B KS AIL); [exact HJf | apply sink_closed_ablocks_fp; constructor; [cbn; clear - Hph; lia | constructor] | exact Hpf3 | | | exact HSINK3].
* eapply Permutation_in; [apply Permutation_sym; exact HPerm4'|]. exact Hpf_in.
* intros ii Hii HFP. destruct (inFP_ablocks_fp_inv _ _ HFP) as (p' & n' & Hpn & Hpa). destruct Hpn as [Hpn | []]. injection Hpn as <- <-.
clear - Hii Hpa HdPP Hrq. unfold FILE_BLOCK in Hii. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPerm4 & Hfrs4 & (Er & HK & HErF & HErLo & HErG & HErC & HErR) & HSINK4 & MLE4).
assert (Vrc4 : val_mem SEGS (mrestrict (w_H W4) mem4) (cg_raw s + 40) 4 (code mod 2 ^ 32)).
{ lazymatch type of Vrc with val_mem _ (mrestrict ?Hh ?mo) _ _ _ =>
apply (val_mem_aview_kept_x SEGS Hh (w_H W4) mo mem4 (cg_raw s + 40) 4 (code mod 2 ^ 32)); [| exact Vrc] end.
intros x Hx. pose proof HK as (_ & K2 & _). replace x with (cg_raw s + (x - cg_raw s)) by lia.
apply (K2 (cg_raw s) RAW_SIZE (x - cg_raw s) Hraw3); [change (req_size RAW_SIZE) with 48; clear - Hx; lia|].
apply HErR. clear - Hx; lia. }
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1.
pose proof (proj1 HJ4) as HAR4.
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hing).
assert (Hcur4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hcur_in).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (2, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj SEGS _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hn; exact (HErLo a ltac:(clear - Ha HF8lo HF8c HFceil C1 Hob241 Hob242 Hob253 Huar; ceil; unfold SB in *; lia) Hn)
| intros a Ha; exfalso; clear - Ha Hob241 Hob242 Hob253 Huar; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj SEGS _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hn; exact (HErF a ltac:(clear - Ha Hob241 Hob242 Hob253 Huar; lia) Hn)
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha Hob241 Hob242 Hob253 Huar; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj SEGS _); [exact HK | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj SEGS _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgot3 | exact Kgot4 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kcell3 | exact Kcell4 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kguar3 | exact Kguar4 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 59%nat) _ _ _ _ _) =>
let AGx := lazymatch goal with A : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => A end in
let Bv := rnB in apply (region_kept_val_at Ex _ _ 59%nat (as_uar_cell Bv) 4 1); [evalE AGx | exact Kuar3 | exact Kuar4 | lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS _); [exact HK | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; exact (HErG a ltac:(clear - Ha Hob241 Hob242 Hob253 Huar; lia) Hn) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 SEGS B LAWS); [exact HK | exact HAR4 | exact Hcur4 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; exact (HErC a ltac:(clear - Ha Hob241 Hob242 Hob253 Huar; lia) Hn) ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
prreg HS (19%bv : bv 5) Q19;
ra_join HS ss_X 961%nat fl_X_deads_bv ltac:(idtac; ra_join_val HS 961%nat 0%nat Q19 E961); fl_handX RX HS end.
split; [replace EV_RAWADD with 27 in Hk3 by reflexivity; rewrite HEV; clear - Hk3 Hob241 Hob242 Hob253 Huar; lia|].
split.
{ exists res; split; [rewrite E961, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E920 | split; [exact Hres|]].
split.
- exists code, bytes. split; [exact HFL|]. split; [exact Hcode|]. split; [exact Vrc4|]. split; [exact HSINK4 | exact HLEN3].
- exists (acc + mo_free MT). split; [exact MLE4|]. clear - HaccM HaccN; lia. }
split; [cbn [c_ly c_S]; exact HPerm4|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X | exact I].
Qed.
Lemma fl_R5X : fl_fromX1 KS MT XN B CTX wfn ss_X (INV_XX KS MT XN B) -> fl_fromX1 KS MT XN B CTX wfn ss_R5 (INV_R5X KS MT XN B).
Proof. exact fl_R5X_aux. Qed.
End h.
End e.
End d.
