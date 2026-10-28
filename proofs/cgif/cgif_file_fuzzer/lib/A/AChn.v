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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACih ACi4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCi5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section m.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section o.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
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
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Variable CTXR : list (list Z).
Hypothesis TRAWADDX : trawadd_specX SEGS KS B MT XN (SIGMA AS_cgif_raw_addframe) CTXR wfn pa_relro_lo pa_relro_hi.
Hypothesis HXM : forall N M, 1 <= M <= N -> N <= 100000000 -> mo_malloc MT M + xm_rawadd XN M + mo_free MT <= xm_flush XN N.
Hypothesis HXN : forall N M, 1 <= M <= N -> N <= 100000000 -> mo_malloc MT M + xn_rawadd XN M + mo_free MT <= xn_flush XN N.
Hypothesis HXMN : forall M, 1 <= M <= 100000000 -> 0 <= xn_rawadd XN M <= xm_rawadd XN M.
Hypothesis HCTXR : forall l, In l CTX -> In ((BASE + 0x243c) :: l) CTXR.
Lemma fl_R4X_aux : fl_fromX1 KS MT XN B CTX wfn ss_R5 (INV_R5X KS MT XN B) -> fl_fromX0 KS MT XN B CTX wfn ss_R4 (INV_R4X MT B).
Proof.
intros RR5. fl_preludeX.
pose proof HINV as ((gen & E621 & Rgen) & E625 & (attr & E901 & Hattr & XATTR) & E911 & (pt & w & h & top & left & tidx & img & E892 & E844 & E845 & E841 & E846 & E842 & E891 & Hrpt & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & Htidx & Hpt & XD & XTI & XI & XI0 & XLEN & XMLE) & E621X).
pose proof HCUR as (XCa & XCg & XCd & XCn & XCct & XCdisp & XCt & XCimg & XClen & XClp). cbn in XCg.
assert (XFBNZ : forall fb, nth (i - 1) (cg_frames s) None = Some fb -> fr_ptr fb <> 0).
{ intros fb' Hfb'. destruct (fl_bef_in s i fb' Hi Hlen3 Hfb') as [_ Hfbi'].
destruct (fl_bef_blocks B ly S g s N rest fb' HPerm Hfbi') as (Hbin' & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb') FRAME_SIZE HAR Hbin') as (_ & Hb4096' & _). clear - Hb4096'. lia. }
destruct (fl_front_model (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) GPAL cur bef XCa XCg XCn ltac:(cbn [c_f]; clear - Q3; lia)
ltac:(unfold ACj6.fl_isfirst; cbn [c_i c_s]; apply (isfirst_of_opt _ bef);
[clear - HBEF; unfold oframe_relbA in HBEF; destruct (nth (i - 1) (cg_frames s) None), bef; first [exact I | destruct HBEF] | exact XFBNZ]))
as (XNPAL & XULCT & XALPHA & XSET & XGEN3).
cbn [c_s c_f c_i] in XNPAL, XULCT, XALPHA, XSET, XGEN3. clear XFBNZ.
assert (Hgen : gen = YI0f.fl_gen3 (gcfg_of s GPAL) cur bef).
{ apply zbv_inj64; [rewrite <- E621; exact E621X | clear - Rgen; lia |].
pose proof (fl_gen3_range (gcfg_of s GPAL) cur bef ltac:(rewrite <- XCg; clear - Q3; lia)) as G; clear - G Q3 XCg; lia. }
xpt_facts Hpt XPT.
unfold fl_tmpblkX, fl_FP0 in Hpt. cbn [c_ly c_S c_regs c_f c_s] in Hpt.
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)).
{ intros x Hx. destruct Hpt as [(_ & _ & _ & Eab3) | (_ & _ & _ & (_ & _ & _ & Eab3 & _))]; rewrite Eab3; [exact Hx | apply in_app_iff; left; exact Hx]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
assert (Hraw3 : In (cg_raw s, RAW_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hraw_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (apply Hsub3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
pose proof (sep_block_frame SEGS _ LAWS ly3 S3 _ _ _ (cg_raw s) RAW_SIZE 2 fpos HAR3 Hraw3 Hfin3) as HdFR.
unfold zdisjoint in HdFR; cbn [fst snd] in HdFR; change (req_size RAW_SIZE) with 48 in HdFR; change (fs_frame_bytes 2) with 256 in HdFR; rewrite EFA3 in HdFR. fold F in HdFR.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr f) FRAME_SIZE HAR Hraw_in Hcur_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRC.
unfold zdisjoint in HdRC. cbn [fst snd] in HdRC. change (req_size RAW_SIZE) with 48 in HdRC. change (req_size FRAME_SIZE) with 40 in HdRC.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE g CGIF_SIZE HAR Hraw_in Hing ltac:(unfold RAW_SIZE, CGIF_SIZE; intros X; injection X; lia)) as HdRG.
unfold zdisjoint in HdRG. cbn [fst snd] in HdRG. change (req_size RAW_SIZE) with 48 in HdRG. change (req_size CGIF_SIZE) with 96 in HdRG.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E10n E32n Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
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
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
lazymatch type of AG with forall n, _ -> ew ?Ebase n = _ => assert (Usp3 : bv_unsigned (ew Ebase 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia);
assert (EraX : raZ rg = (BASE + 0x243c)) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0; exact Usp3) end.
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
destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s) RAW_SIZE (proj1 HJ3) Hraw3) as (_ & _ & _ & _ & Hrpres3 & _). change (req_size RAW_SIZE) with 48 in Hrpres3.
lazymatch type of HS with context [restrict (w_H ?Wx) ?msX] =>
assert (OrawX : obj_at SEGS (mrestrict (w_H Wx) (ms_mem msX)) (cg_raw s) LAY_Raw (traw_vals wfn g s)) end.
{ eapply (aj_obj_kept B); [exact HJ3 | exact Hraw_in | exact Hraw3 | exact Oraw | vm_compute; reflexivity |].
change (req_size RAW_SIZE) with 48. intros j Hj (r & [<- | []] & Hr). cbn [fst snd] in Hr. clear - Hj Hr HdRC. lia. }
cbn [traw_vals] in OrawX.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iF := idx_of_base rs 516%nat in let iF := eval vm_compute in iF in
let rF := eval vm_compute in (nth iF rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) iF rF HS ltac:(vm_compute; reflexivity)) as HRF; cbn [ms_mem restrict] in HRF | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iF := idx_of_base rs 516%nat in let iF := eval vm_compute in iF in
let rF := eval vm_compute in (nth iF rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iF rF HS ltac:(vm_compute; reflexivity)) as HRF; cbn [ms_mem restrict] in HRF  end.
assert (UF : bv_unsigned (ew E 516) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia).
Ltac fieldF HRF UF od w e V :=
lazymatch type of HRF with region_ok _ ?Ex _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region_any Ex _ 516 _ cs lo hi wlo whi od w e HRF UF ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
cbn [sv_denot] in V; rewrite ?ew_ewset_other, ?ew_havoc_old in V by nat_side;
try change (N.to_nat 8) with 8%nat in V; try change (N.to_nat 4) with 4%nat in V; try change (N.to_nat 2) with 2%nat in V; try change (N.to_nat 1) with 1%nat in V;
try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V; try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V;
try change (2 ^ (8 * Z.of_N 2)) with 65536 in V; try change (2 ^ (8 * Z.of_N 1)) with 256 in V end.
fieldF HRF UF 32 8%N (SOff 50 0) V0. fieldF HRF UF 40 8%N (SOff 891 0) V1.
lazymatch type of HRF with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
lazymatch cs with context [YP09.mkChunk 48 (CVal 4%N ?ea)] => fieldF HRF UF 48 4%N ea V2 end end.
fieldF HRF UF 52 2%N (SOff 839 0) V3. fieldF HRF UF 54 2%N (SOff 845 0) V4. fieldF HRF UF 56 2%N (SOff 841 0) V5. fieldF HRF UF 58 2%N (SOff 840 0) V6.
fieldF HRF UF 60 2%N (SExt true 16 (SOff 54 0)) V7. fieldF HRF UF 62 2%N (SOff 911 0) V8. fieldF HRF UF 64 1%N (SOff 57 0) V9. fieldF HRF UF 65 1%N (SOff 842 0) V10.
assert (Hqi : 1 <= req_size N) by (generalize HW1 HH1 HN; clear; intros; unfold req_size; destruct (Z.eqb_spec N 0); nia).
assert (Hwh0 : 0 <= w * h) by (apply Z.mul_nonneg_nonneg; clear - Hw1 Hh1 Hob241 Hob242 Hob253 Huar; lia).
assert (Rimg : 0 <= img < 2 ^ 64) by (destruct Hpt as [(_ & -> & _) | (_ & -> & _ & (Hp1 & Hp2 & _))]; [clear - Hi4096 Hiceil Hqi C1 Hob241 Hob242 Hob253 Huar; lia | clear - Hp1 Hp2 Hwh0 Hob241 Hob242 Hob253 Huar; ceil; lia]).
assert (Rslct : 0 <= ACj7.fl_slct (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) < 65536) by (unfold ACj7.fl_slct; destruct (fl_uselct _); cbn [c_f]; clear - Q5 Hob241 Hob242 Hob253 Huar; lia).
rewrite (denot_atom_mod _ 50 (fr_lpal f) _ E50 ltac:(clear - Q0 Hob241 Hob242 Hob253 Huar; lia)), Z.mod_small in V0 by (clear - Q0 Hob241 Hob242 Hob253 Huar; lia).
rewrite (denot_atom_mod _ 891 img _ E891 Rimg), Z.mod_small in V1 by (exact Rimg).
rewrite (denot_atom_mod _ 839 w _ E844 ltac:(clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia)), Z.mod_small in V3 by (clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia).
rewrite (denot_atom_mod _ 845 h _ E845 ltac:(clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia)), Z.mod_small in V4 by (clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia).
rewrite (denot_atom_mod _ 841 top _ E841 ltac:(clear - Ht0 Hth R8 Hh1 Hob241 Hob242 Hob253 Huar; lia)), Z.mod_small in V5 by (clear - Ht0 Hth R8 Hh1 Hob241 Hob242 Hob253 Huar; lia).
rewrite (denot_atom_mod _ 840 left _ E846 ltac:(clear - Hl0 Hlw R7 Hw1 Hob241 Hob242 Hob253 Huar; lia)), Z.mod_small in V6 by (clear - Hl0 Hlw R7 Hw1 Hob241 Hob242 Hob253 Huar; lia).
rewrite (denot_atom_mod _ 911 _ _ E911 ltac:(clear - Rslct Hob241 Hob242 Hob253 Huar; lia)), Z.mod_small in V8 by (exact Rslct).
rewrite (denot_atom_mod _ 57 (fr_disp f) _ E57 ltac:(clear - Q7 Hob241 Hob242 Hob253 Huar; lia)), Z.mod_small in V9 by (clear - Q7 Hob241 Hob242 Hob253 Huar; lia).
rewrite (denot_atom_mod _ 842 tidx _ E842 ltac:(clear - Htidx Hob241 Hob242 Hob253 Huar; lia)) in V10. change (2 ^ (8 * 1)) with 256 in V10.
assert (Rtidx : 0 <= tidx mod 256 < 256) by (apply Z.mod_pos_bound; clear; lia).
lazymatch type of V2 with val_mem _ _ _ _ ?v => set (fattrv := v) in V2 end.
lazymatch type of V7 with val_mem _ _ _ _ ?v => set (delayv := v) in V7 end.
assert (Rfattr : 0 <= fattrv < 2 ^ 32) by (subst fattrv; apply Z.mod_pos_bound; clear; lia).
assert (Rdelay : 0 <= delayv < 2 ^ 16) by (subst delayv; apply Z.mod_pos_bound; clear; lia).
assert (Xfattr : fattrv = attr + (if YO07.flag (fr_attr f) 8 then 2 else 0)).
{ transitivity (U E (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_SRL (SExt true 32 (SOff 52 0)) (SLit 2)) (SLit 2)) (SOff 901 0)) mod 2 ^ 32); [reflexivity|].
rewrite (U_rattrX E 52 901 (fr_attr f) attr E52 ltac:(clear - Q2; lia) E901 ltac:(clear - Hattr; lia)). apply rattr_model. clear - Hattr; lia. }
assert (Xdelay : delayv = fr_delay f).
{ transitivity (U E (SExt true 16 (SOff 54 0)) mod 2 ^ 16); [reflexivity|]. apply (U_sext16_field E 54 (fr_delay f) E54). clear - Q4; lia. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (OcfgX : obj_at SEGS (mrestrict (w_H Wx) (ms_mem msX)) (F + 32) LAY_RawFrameConfig
[fr_lpal f; img; fattrv; w; h; top; left; delayv; ACj7.fl_slct (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0); fr_disp f; tidx mod 256]) | st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (OcfgX : obj_at SEGS (mrestrict (w_H Wx) (ms_mem msX)) (F + 32) LAY_RawFrameConfig
[fr_lpal f; img; fattrv; w; h; top; left; delayv; ACj7.fl_slct (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0); fr_disp f; tidx mod 256])  end.
{ cbn [obj_at LAY_RawFrameConfig]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N Pos.to_nat].
rewrite <- !Z.add_assoc. cbn [Z.add Pos.add].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536. change (2 ^ (8 * 1)) with 256.
split; [split; [exact V0 | clear - Q0 Hob241 Hob242 Hob253 Huar; lia]|].
split; [split; [exact V1 | exact Rimg]|].
split; [split; [exact V2 | exact Rfattr]|].
split; [split; [exact V3 | clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia]|]. split; [split; [exact V4 | clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia]|].
split; [split; [exact V5 | clear - Ht0 Hth R8 Hh1 Hob241 Hob242 Hob253 Huar; lia]|]. split; [split; [exact V6 | clear - Hl0 Hlw R7 Hw1 Hob241 Hob242 Hob253 Huar; lia]|].
split; [split; [exact V7 | clear - Rdelay Hob241 Hob242 Hob253 Huar; lia]|].
split; [split; [exact V8 | exact Rslct]|].
split; [split; [exact V9 | clear - Q7 Hob241 Hob242 Hob253 Huar; lia]|]. split; [split; [exact V10 | exact Rtidx]|]. exact I. }
clear V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 HRF.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iG := idx_of_base rs 10%nat in let iG := eval vm_compute in iG in
let rG := eval vm_compute in (nth iG rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) iG rG HS ltac:(vm_compute; reflexivity)) as HRG; cbn [ms_mem restrict] in HRG;
assert (UG : bv_unsigned (ew E 10) = g) by (rewrite E10n; apply unsigned_lit_small; clear - Hg4096 Hgceil C1 Hob241 Hob242 Hob253 Huar; lia);
lazymatch type of HRG with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 10 g cs lo hi wlo whi 56 8%N (SOff 44 0) hw HRG UG ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - R11; lia) ltac:(cbn; lia)) as Vwfn;
pose proof (field_of_region Ex _ 10 g cs lo hi wlo whi 64 8%N (SOff 45 0) 0 HRG UG ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 10 g cs lo hi wlo whi 80 8%N (SOff 47 0) pf HRG UG ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - XF; unfold xfacts in XF; lia) ltac:(cbn; lia)) as Vpfile end;
clear HRG UG | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iG := idx_of_base rs 10%nat in let iG := eval vm_compute in iG in
let rG := eval vm_compute in (nth iG rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iG rG HS ltac:(vm_compute; reflexivity)) as HRG; cbn [ms_mem restrict] in HRG;
assert (UG : bv_unsigned (ew E 10) = g) by (rewrite E10n; apply unsigned_lit_small; clear - Hg4096 Hgceil C1 Hob241 Hob242 Hob253 Huar; lia);
lazymatch type of HRG with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 10 g cs lo hi wlo whi 56 8%N (SOff 44 0) hw HRG UG ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - R11; lia) ltac:(cbn; lia)) as Vwfn;
pose proof (field_of_region Ex _ 10 g cs lo hi wlo whi 64 8%N (SOff 45 0) 0 HRG UG ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 10 g cs lo hi wlo whi 80 8%N (SOff 47 0) pf HRG UG ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - XF; unfold xfacts in XF; lia) ltac:(cbn; lia)) as Vpfile end;
clear HRG UG  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iS := idx_of_base rs 529%nat in let iS := eval vm_compute in iS in
let rS := eval vm_compute in (nth iS rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) iS rS HS ltac:(vm_compute; reflexivity)) as HRS; cbn [ms_mem restrict] in HRS;
assert (US : bv_unsigned (ew E 529) = SB + F / 8) by (rewrite E529; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi Hob241 Hob242 Hob253 Huar; lia);
assert (ZS : forall od, In (YP09.mkChunk od (CVal 1 (SLit 0))) (YP09.r_chunks rS) -> aview SEGS (w_H W3) (ms_mem msX) (SB + F / 8 + od) = Some 0);
[ let od := fresh "od" in let Hod := fresh "Hod" in intros od Hod;
lazymatch type of HRS with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi od 1%N (SLit 0) 0 HRS US Hod eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vz end;
pose proof (Vz 0%nat ltac:(lia)) as Vz0; cbn [Z.of_nat] in Vz0; rewrite Z.add_0_r in Vz0;
unfold aview; rewrite Vz0; reflexivity
| clear HRS ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iS := idx_of_base rs 529%nat in let iS := eval vm_compute in iS in
let rS := eval vm_compute in (nth iS rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iS rS HS ltac:(vm_compute; reflexivity)) as HRS; cbn [ms_mem restrict] in HRS;
assert (US : bv_unsigned (ew E 529) = SB + F / 8) by (rewrite E529; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi Hob241 Hob242 Hob253 Huar; lia);
assert (ZS : forall od, In (YP09.mkChunk od (CVal 1 (SLit 0))) (YP09.r_chunks rS) -> aview SEGS (w_H W3) (ms_mem msX) (SB + F / 8 + od) = Some 0);
[ let od := fresh "od" in let Hod := fresh "Hod" in intros od Hod;
lazymatch type of HRS with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi od 1%N (SLit 0) 0 HRS US Hod eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vz end;
pose proof (Vz 0%nat ltac:(lia)) as Vz0; cbn [Z.of_nat] in Vz0; rewrite Z.add_0_r in Vz0;
unfold aview; rewrite Vz0; reflexivity
| clear HRS ]  end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (AF : afobj SEGS B ly3 S3 Wx (ms_mem msX) (F + 32) 40) | st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (AF : afobj SEGS B ly3 S3 Wx (ms_mem msX) (F + 32) 40)  end.
{ split; [|split].
- exists 2, fpos. split; [exact Hfin3|]. split; [clear; lia|]. rewrite EFA3. fold F. split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); apply Z_mod_mult|].
change (fs_frame_bytes 2) with 256. clear; lia.
- rewrite HFq. replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia). apply Z_mod_mult.
- apply zero_shadow_of_bytes; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); apply Z_mod_mult | reflexivity | clear; lia |].
intros j Hj. change (40 / 8) with 5 in Hj. rewrite <- SB_SHADOW_OFF.
replace ((F + 32) / 8) with (F / 8 + 4) by (rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite Z_div_mult by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia);
replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite Z_div_mult by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); clear; lia).
replace (SB + (F / 8 + 4) + j) with (SB + F / 8 + (4 + j)) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
assert (Hj5 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by (clear - Hj Hob241 Hob242 Hob253 Huar; lia).
destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]]; apply ZS; cbn; tauto. }
clear ZS.
assert (HBL : exists Nimg rest0, Permutation (ablocks B ly3 S3) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: (pf, FILE_BLOCK) :: rest0) /\
w * h <= Nimg /\ (Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0)).
{ destruct Hpt as [(Hp0 & Eimg & _ & Eab3) | (Hp1 & Eimg & _ & (_ & _ & _ & Eab3 & _))].
- destruct (flush_blocks_imgX0 g s N rest i f pf Hf Hpf_rest) as (rest0 & HP0 & Hl0').
exists N, rest0. rewrite Eab3, Eimg. split; [exact (Permutation_trans HPerm HP0)|]. split; [|exact Hl0'].
rewrite HN. apply Z.mul_le_mono_nonneg; clear - Hw1 Hlw Hl0 Hh1 Hth Ht0 Hob241 Hob242 Hob253 Huar; lia.
- destruct (flush_blocks_imgX1 g s N rest f pt (w * h) pf Hfi Hpf_rest) as (rest0 & HP0 & Hl0').
exists (w * h), rest0. rewrite Eab3, Eimg. split; [|split; [clear; lia | exact Hl0']].
eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. eapply Permutation_trans; [apply perm_skip; exact HPerm | exact HP0]. }
destruct HBL as (Nimg & rest0 & HBL & HwN & Hlct).
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3' & _).
assert (HEVc : st_nev S3 + EV_RAWADD <= EV_MAX).
{ replace EV_RAWADD with 27 by reflexivity. rewrite HEV in Hev.
destruct Hpt as [(_ & _ & Hk0 & _) | (_ & _ & Hk2 & _)]; [clear - Hnev3 Hev Hk0 | clear - Hnev3 Hev Hk2]; lia. }
assert (HLIVEc : blocks_bytes S3 + LIVE_RAWADD <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3). unfold LIVE_FLUSH in Hlive. unfold LIVE_RAWADD.
destruct Hpt as [(_ & _ & _ & Eab3) | (_ & _ & _ & (_ & _ & _ & Eab3 & _))]; rewrite Eab3.
- rewrite <- (blocks_bytes_bsum B ly S). clear - Hlive. lia.
- rewrite bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. rewrite HN in HNle.
assert (Hwh : w * h <= cg_W s * cg_H s) by (apply Z.mul_le_mono_nonneg; clear - Hw1 Hlw Hl0 Hh1 Hth Ht0 Hob241 Hob242 Hob253 Huar; lia). clear - Hlive HNle Hwh Hwh0. lia. }
destruct (fl_lift_journal B LAWS KS AIL ly S W regs mem md ch (fr_ptr f) (cg_raw s) pf [(2, fpos)] ly3 S3 W3 _ _ k Sg HPRE HJ3 Hpf_in
ltac:(clear - XF; unfold xfacts in XF; lia) ltac:(clear - Hc4096; lia) HSINK0) as (HJ3X & _ & HSINK3).
assert (HwhN : w * h <= N) by (rewrite HN; apply Z.mul_le_mono_nonneg; clear - Hw1 Hlw Hl0 Hh1 Hth Ht0; lia).
assert (HdCI : fr_ptr f + 40 <= fr_img f \/ fr_img f + req_size N <= fr_ptr f).
{ destruct (frame_blocks_front g s N rest i f Hf) as (rci & HPci).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR (Permutation_trans HPerm HPci)) as Hd.
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd. change (req_size FRAME_SIZE) with 40 in Hd. exact Hd. }
assert (HdCL : Z.land (fr_attr f) 1 <> 0 -> fr_ptr f + 40 <= fr_lpal f \/ fr_lpal f + req_size (3 * fr_nlp f) <= fr_ptr f).
{ intros Hz. destruct (frame_blocks_front3 g s N rest i f Hf Hz) as (rcl & HPcl).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR (Permutation_trans HPerm HPcl)) as Hd.
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd. change (req_size FRAME_SIZE) with 40 in Hd. exact Hd. }
lazymatch type of HS with context [restrict (w_H ?Wx) ?msX] =>
assert (HIMG : garr8 SEGS (mrestrict (w_H Wx) (ms_mem msX)) img (ximg (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) (mkFLXX path pf Sg GPAL cur bef)));
[ destruct Hpt as [(Hp0 & Eimg & _ & Eab3) | (Hp1 & Eimg & _)];
[ rewrite Eimg, (XI0 Hp0);
eapply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fr_img f) N (fr_img f) (YO07.f_img cur) HJ3);
[ exact Himg_in | rewrite Eab3; exact Himg_in | clear; lia | rewrite XClen; clear - HN HW1 HH1; unfold req_size; destruct (Z.eqb_spec N 0); nia
| intros a Ha (r & Hr0 & Hr); cbn [In] in Hr0; destruct Hr0 as [<- | []]; cbn [fst snd] in Hr; clear - Ha Hr HdCI XClen HN HW1 HH1; unfold req_size in HdCI; destruct (Z.eqb_spec N 0); nia
| exact XCimg ]
| rewrite Eimg; exact (XI Hp1) ]
| assert (HLCT : Z.land (fr_attr f) 1 <> 0 -> garr8 SEGS (mrestrict (w_H Wx) (ms_mem msX)) (fr_lpal f) (YO07.f_lpal cur) /\ Z.of_nat (length (YO07.f_lpal cur)) = 3 * fr_nlp f);
[ intros Hz; destruct (XClp Hz) as [G0 L0]; split; [|exact L0];
destruct (fl_bef_blocks B ly S g s N rest f HPerm Hfi) as (_ & _ & Hlp_in); specialize (Hlp_in Hz);
assert (Hlp3 : In (fr_lpal f, 3 * fr_nlp f) (ablocks B ly3 S3)) by (apply Hsub3; exact Hlp_in);
eapply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fr_lpal f) (3 * fr_nlp f) (fr_lpal f) (YO07.f_lpal cur) HJ3);
[ exact Hlp_in | exact Hlp3 | clear; lia | rewrite L0; unfold req_size; destruct (Z.eqb_spec (3 * fr_nlp f) 0); lia
| intros a Ha (r & Hr0 & Hr); cbn [In] in Hr0; destruct Hr0 as [<- | []]; cbn [fst snd] in Hr; specialize (HdCL Hz); clear - Ha Hr HdCL L0 Q5; unfold req_size in HdCL; destruct (Z.eqb_spec (3 * fr_nlp f) 0); lia
| exact G0 ]
| ] ] end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_callS SEGS B LAWS pa_segs_low W3 Ex (abs_ss VAL ssX) msX TFLUSH_STK (spZ regs) _ ly S W mem md [(2, fpos)] ly3 S3 mdX k
TRAWADD_STK ((cg_raw s + 40, cg_raw s + 44) :: asink_fp pf) EV_RAWADD (sp1 - spZ regs) (ew Ex 2) (Z_to_bv 64 (BASE + 0x243c)) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => exists res rcur' : Z, getr regs2 10 = w64 res /\ 0 <= res < 2 ^ 64 /\
obj_at SEGS (mrestrict (w_H W2) mem2) (cg_raw s) LAY_Raw [wfn; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rcur'] /\
Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
(exists code bytes,
YO07.raw_addframe (YO07.flag (rw_attr s) 1) (raw_sgct s) (rc_int (rw_cur s)) (ximg (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) (mkFLXX path pf Sg GPAL cur bef)) fattrv w h top left delayv
(ACj7.fl_slct (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0)) (YO07.f_lpal cur) (fr_disp f) (tidx mod 256) = (code, bytes) /\
Z_to_bv 64 res = Z_to_bv 64 code /\ rcur' = code mod 2 ^ 32 /\
asink_at SEGS KS (mrestrict (w_H W2) mem2) md2 pf (Sg ++ bytes) /\
Z.of_nat (length bytes) <= FRAME_OUT (w * h)) /\
mo_le MT S3 S2 (xn_rawadd XN (w * h))) HS eq_refl HJ3X);
[ first [ rewrite Rsp, E60; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Usp3; f_equal; clear; lia | match goal with |- ?g => idtac "AJ1" g end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ exact Usp3 | idtac "AJ3" ]
| first [ rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity | match goal with |- ?g => idtac "AJ4" g end ]
| first [ clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | idtac "AJ5" ]
| first [ apply Zle_bool_imp_le; vm_compute; reflexivity | idtac "AJ6" ]
| first [ replace TRAWADD_STK with 17040 by reflexivity; rewrite FFS; clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | match goal with |- ?g => idtac "AJ7" g end ]
| first [ rewrite Rgp, Ugp; exact Hgp | idtac "AJ8" ]
| first [ rewrite Rtp, Utp; exact Htp | idtac "AJ9" ]
| first [ exact Rra | idtac "AJ10" ]
| first [ apply ret_ok_codeptr_v; [clear; lia | reflexivity] | idtac "AJ11" ]
| first [ rewrite unsigned_lit_small by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia | idtac "AJ12" ]
| first [ rewrite Es0X; replace (spZ regs + (sp1 - spZ regs)) with sp1 by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact Hch1 | match goal with |- ?g => idtac "AJ13" g end ]
| first [ intros HPRE1; eapply SRr_mono;
[ first [ pose proof (TRAWADDX ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch)
(cg_raw s) g (F + 32) (rw_gct s) (rw_attr s) (cg_W s) (cg_H s) (raw_sgct s) (rw_loops s) (rw_cur s) 0 pf path hw
(fr_lpal f) img fattrv w h top left delayv (ACj7.fl_slct (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0)) (fr_disp f) (tidx mod 256) Nimg rest0
Sg (ximg (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) (mkFLXX path pf Sg GPAL cur bef)) (YO07.f_lpal cur) HPRE1) as CALL | idtac "CALL-POSE" ];
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 (SIGMA AS_cgif_raw_addframe)) with (Z_to_bv 64 (SIGMA AS_cgif_raw_addframe)) in CALL;
first [ apply CALL | match goal with |- ?g => idtac "CALL-APPLY" g end; let t := type of CALL in idtac "CALL-TYPE" t ]; clear CALL;
[ first [ rewrite EspX; exact Hsp1al | idtac "CA1" ]
| first [ rewrite EraX; cbn [spine map fst snd]; apply HCTXR; exact Hctx | match goal with |- ?g => idtac "CA2" g end ]
| first [ rewrite Hfrs3; cbn [length]; clear - Hroom Hob241 Hob242 Hob253 Huar; lia | idtac "CA3" ]
| first [ exact (arodata_ok_journalP _ _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HROD) | idtac "CA4" ]
| first [ rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E46 | match goal with |- ?g => idtac "CA5" g end ]
| first [ rewrite Ra1, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite UF; reflexivity | match goal with |- ?g => idtac "CA6" g end ]
| first [ exact AF | idtac "CA7" ]
| first [ exact OcfgX | match goal with |- ?g => idtac "CA8" g end ]
| first [ exact OrawX | match goal with |- ?g => idtac "CA9" g end ]
| first [ unfold raw_sgct; destruct (Z.eqb_spec (Z.land (cg_attr s) 4) 0); [apply Hngp; assumption | clear; lia] | idtac "CA10" ]
| first [ exact Vwfn | idtac "CA11" ]
| first [ exact Rhw | idtac "CAhw" ]
| first [ exact Vctx | idtac "CA12" ]
| first [ clear; lia | idtac "CA13" ]
| first [ exact Vpfile | idtac "CA14" ]
| first [ clear - Hpf0; unfold xfacts in Hpf0; exact Hpf0 | idtac "CApf0" ]
| first [ exact HSINK3 | idtac "CAsink" ]
| first [ clear - HSmax HwhN Hwh0; unfold xfacts in HSmax; unfold FRAME_OUT in *; lia | idtac "CAsmax" ]
| first [ exact Hw1 | idtac "CA15" ]
| first [ exact Hh1 | idtac "CA16" ]
| first [ rewrite HN in HNle; eapply Z.le_trans; [|exact HNle]; apply Z.mul_le_mono_nonneg; clear - Hw1 Hlw Hl0 Hh1 Hth Ht0 Hob241 Hob242 Hob253 Huar; lia | idtac "CA17" ]
| first [ exact HwN | idtac "CA18" ]
| first [ exact HBL | idtac "CA19" ]
| first [ unfold ACj7.fl_slct, fl_uselct; cbn [c_f]; destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0) as [Hz|Hz]; cbn [negb]; intros Hsl; [exfalso; clear - Hsl Hob241 Hob242 Hob253 Huar; lia|];
destruct (in_split _ _ (Hlct Hz)) as (l1 & l2 & El); exists (3 * fr_nlp f), (l1 ++ l2); split;
[rewrite El; apply Permutation_sym; apply Permutation_middle | split; [clear; lia|]];
split; [exact (proj1 (HLCT Hz)) | rewrite (proj2 (HLCT Hz)); clear; lia] | match goal with |- ?g => idtac "CA20" g end ]
| first [ exact HIMG | idtac "CAimg" ]
| first [ exact XLEN | idtac "CAlen" ]
| first [ exact HEVc | match goal with |- ?g => idtac "CA21" g end ]
| first [ exact HLIVEc | match goal with |- ?g => idtac "CA22" g end ]
| first [ eapply (mok_station MT S S3 (xm_flush XN N) (xmacc MT pt (w * h)) _ MLAW HMOK XMLE);
[ pose proof (HXMN (w * h) ltac:(clear - Hw1 Hh1 Hwh0 HwhN HNle; nia)); clear - H; lia
| pose proof (HXM N (w * h) ltac:(clear - Hw1 Hh1 Hwh0 HwhN; nia) HNle) as BM;
pose proof (mo_malloc_nonneg MT MLAW (w * h) Hwh0) as M0; pose proof (mo_free_nonneg MT MLAW) as F0;
unfold xmacc; destruct (pt =? 0); clear - BM M0 F0; lia ] | match goal with |- ?g => idtac "CAmok" g end ] ]
| first [ cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HPc & res & rcur' & Hres & Hres64 & Oraw4 & HPerm4 & HX4 & MLE4);
exists ly4, S4, regs4, mem4, md4; split; [rewrite Rra; reflexivity|]; split; [exact HJc|];
split; [exact HPc|]; exists res, rcur'; split; [exact Hres|]; split; [exact Hres64|]; split; [exact Oraw4|]; split; [exact HPerm4|];
split; [exact HX4 | exact MLE4] | match goal with |- ?g => idtac "CALL-POST" g end ] ]
| idtac "AJ14" ]
| first [ intros a (r & Hr & Ha); left; exists r; split; [right; exact Hr | exact Ha] | match goal with |- ?g => idtac "AJ15" g end ] ]
| ] | st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_callS SEGS B LAWS pa_segs_low W3 Ex ssX msX TFLUSH_STK (spZ regs) _ ly S W mem md [(2, fpos)] ly3 S3 mdX k
TRAWADD_STK ((cg_raw s + 40, cg_raw s + 44) :: asink_fp pf) EV_RAWADD (sp1 - spZ regs) (ew Ex 2) (Z_to_bv 64 (BASE + 0x243c)) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => exists res rcur' : Z, getr regs2 10 = w64 res /\ 0 <= res < 2 ^ 64 /\
obj_at SEGS (mrestrict (w_H W2) mem2) (cg_raw s) LAY_Raw [wfn; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rcur'] /\
Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
(exists code bytes,
YO07.raw_addframe (YO07.flag (rw_attr s) 1) (raw_sgct s) (rc_int (rw_cur s)) (ximg (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) (mkFLXX path pf Sg GPAL cur bef)) fattrv w h top left delayv
(ACj7.fl_slct (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0)) (YO07.f_lpal cur) (fr_disp f) (tidx mod 256) = (code, bytes) /\
Z_to_bv 64 res = Z_to_bv 64 code /\ rcur' = code mod 2 ^ 32 /\
asink_at SEGS KS (mrestrict (w_H W2) mem2) md2 pf (Sg ++ bytes) /\
Z.of_nat (length bytes) <= FRAME_OUT (w * h)) /\
mo_le MT S3 S2 (xn_rawadd XN (w * h))) HS eq_refl HJ3X);
[ first [ rewrite Rsp, E60; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Usp3; f_equal; clear; lia | match goal with |- ?g => idtac "AJ1" g end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ exact Usp3 | idtac "AJ3" ]
| first [ rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity | match goal with |- ?g => idtac "AJ4" g end ]
| first [ clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | idtac "AJ5" ]
| first [ apply Zle_bool_imp_le; vm_compute; reflexivity | idtac "AJ6" ]
| first [ replace TRAWADD_STK with 17040 by reflexivity; rewrite FFS; clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | match goal with |- ?g => idtac "AJ7" g end ]
| first [ rewrite Rgp, Ugp; exact Hgp | idtac "AJ8" ]
| first [ rewrite Rtp, Utp; exact Htp | idtac "AJ9" ]
| first [ exact Rra | idtac "AJ10" ]
| first [ apply ret_ok_codeptr_v; [clear; lia | reflexivity] | idtac "AJ11" ]
| first [ rewrite unsigned_lit_small by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia | idtac "AJ12" ]
| first [ rewrite Es0X; replace (spZ regs + (sp1 - spZ regs)) with sp1 by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact Hch1 | match goal with |- ?g => idtac "AJ13" g end ]
| first [ intros HPRE1; eapply SRr_mono;
[ first [ pose proof (TRAWADDX ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch)
(cg_raw s) g (F + 32) (rw_gct s) (rw_attr s) (cg_W s) (cg_H s) (raw_sgct s) (rw_loops s) (rw_cur s) 0 pf path hw
(fr_lpal f) img fattrv w h top left delayv (ACj7.fl_slct (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0)) (fr_disp f) (tidx mod 256) Nimg rest0
Sg (ximg (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) (mkFLXX path pf Sg GPAL cur bef)) (YO07.f_lpal cur) HPRE1) as CALL | idtac "CALL-POSE" ];
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 (SIGMA AS_cgif_raw_addframe)) with (Z_to_bv 64 (SIGMA AS_cgif_raw_addframe)) in CALL;
first [ apply CALL | match goal with |- ?g => idtac "CALL-APPLY" g end; let t := type of CALL in idtac "CALL-TYPE" t ]; clear CALL;
[ first [ rewrite EspX; exact Hsp1al | idtac "CA1" ]
| first [ rewrite EraX; cbn [spine map fst snd]; apply HCTXR; exact Hctx | match goal with |- ?g => idtac "CA2" g end ]
| first [ rewrite Hfrs3; cbn [length]; clear - Hroom Hob241 Hob242 Hob253 Huar; lia | idtac "CA3" ]
| first [ exact (arodata_ok_journalP _ _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HROD) | idtac "CA4" ]
| first [ rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E46 | match goal with |- ?g => idtac "CA5" g end ]
| first [ rewrite Ra1, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite UF; reflexivity | match goal with |- ?g => idtac "CA6" g end ]
| first [ exact AF | idtac "CA7" ]
| first [ exact OcfgX | match goal with |- ?g => idtac "CA8" g end ]
| first [ exact OrawX | match goal with |- ?g => idtac "CA9" g end ]
| first [ unfold raw_sgct; destruct (Z.eqb_spec (Z.land (cg_attr s) 4) 0); [apply Hngp; assumption | clear; lia] | idtac "CA10" ]
| first [ exact Vwfn | idtac "CA11" ]
| first [ exact Rhw | idtac "CAhw" ]
| first [ exact Vctx | idtac "CA12" ]
| first [ clear; lia | idtac "CA13" ]
| first [ exact Vpfile | idtac "CA14" ]
| first [ clear - Hpf0; unfold xfacts in Hpf0; exact Hpf0 | idtac "CApf0" ]
| first [ exact HSINK3 | idtac "CAsink" ]
| first [ clear - HSmax HwhN Hwh0; unfold xfacts in HSmax; unfold FRAME_OUT in *; lia | idtac "CAsmax" ]
| first [ exact Hw1 | idtac "CA15" ]
| first [ exact Hh1 | idtac "CA16" ]
| first [ rewrite HN in HNle; eapply Z.le_trans; [|exact HNle]; apply Z.mul_le_mono_nonneg; clear - Hw1 Hlw Hl0 Hh1 Hth Ht0 Hob241 Hob242 Hob253 Huar; lia | idtac "CA17" ]
| first [ exact HwN | idtac "CA18" ]
| first [ exact HBL | idtac "CA19" ]
| first [ unfold ACj7.fl_slct, fl_uselct; cbn [c_f]; destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0) as [Hz|Hz]; cbn [negb]; intros Hsl; [exfalso; clear - Hsl Hob241 Hob242 Hob253 Huar; lia|];
destruct (in_split _ _ (Hlct Hz)) as (l1 & l2 & El); exists (3 * fr_nlp f), (l1 ++ l2); split;
[rewrite El; apply Permutation_sym; apply Permutation_middle | split; [clear; lia|]];
split; [exact (proj1 (HLCT Hz)) | rewrite (proj2 (HLCT Hz)); clear; lia] | match goal with |- ?g => idtac "CA20" g end ]
| first [ exact HIMG | idtac "CAimg" ]
| first [ exact XLEN | idtac "CAlen" ]
| first [ exact HEVc | match goal with |- ?g => idtac "CA21" g end ]
| first [ exact HLIVEc | match goal with |- ?g => idtac "CA22" g end ]
| first [ eapply (mok_station MT S S3 (xm_flush XN N) (xmacc MT pt (w * h)) _ MLAW HMOK XMLE);
[ pose proof (HXMN (w * h) ltac:(clear - Hw1 Hh1 Hwh0 HwhN HNle; nia)); clear - H; lia
| pose proof (HXM N (w * h) ltac:(clear - Hw1 Hh1 Hwh0 HwhN; nia) HNle) as BM;
pose proof (mo_malloc_nonneg MT MLAW (w * h) Hwh0) as M0; pose proof (mo_free_nonneg MT MLAW) as F0;
unfold xmacc; destruct (pt =? 0); clear - BM M0 F0; lia ] | match goal with |- ?g => idtac "CAmok" g end ] ]
| first [ cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HPc & res & rcur' & Hres & Hres64 & Oraw4 & HPerm4 & HX4 & MLE4);
exists ly4, S4, regs4, mem4, md4; split; [rewrite Rra; reflexivity|]; split; [exact HJc|];
split; [exact HPc|]; exists res, rcur'; split; [exact Hres|]; split; [exact Hres64|]; split; [exact Oraw4|]; split; [exact HPerm4|];
split; [exact HX4 | exact MLE4] | match goal with |- ?g => idtac "CALL-POST" g end ] ]
| idtac "AJ14" ]
| first [ intros a (r & Hr & Ha); left; exists r; split; [right; exact Hr | exact Ha] | match goal with |- ?g => idtac "AJ15" g end ] ]
| ]  end end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & res & rcur' & Hres & Hres64 & Oraw4 & HPerm4 & (code & bytes & HRA & Hcode & Hrcur & HSINK4 & HLEN4) & MLE4).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HJc by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
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
assert (HnFP_lo : forall a, SB <= a < 17594333495296 -> ~ inFP ((cg_raw s + 40, cg_raw s + 44) :: asink_fp pf) a)
by (intros a Ha (r & Hr & Hx); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd sink_token] in Hx;
[ clear - Ha Hx Hrh_ia C3; change (req_size RAW_SIZE) with 48 in Hrh_ia; unfold SB in Ha; zone_lia
| clear - Ha Hx Hp_ia C3; unfold xfacts in Hp_ia; unfold SB in Ha; unfold FILE_BLOCK in Hx; zone_lia
| clear - Ha Hx; unfold SB in Ha; lia ]).
assert (HnFP_F : forall a, F <= a < F + 256 -> ~ inFP ((cg_raw s + 40, cg_raw s + 44) :: asink_fp pf) a)
by (intros a Ha (r & Hr & Hx); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd sink_token] in Hx;
[ clear - Ha Hx HdFR; lia | clear - Ha Hx XF; unfold xfacts in XF; unfold FILE_BLOCK in Hx; lia | clear - Ha Hx XF; unfold xfacts in XF; lia ]).
assert (HnFP_G : forall a, g <= a < g + 96 -> ~ inFP ((cg_raw s + 40, cg_raw s + 44) :: asink_fp pf) a)
by (intros a Ha (r & Hr & Hx); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd sink_token] in Hx;
[ clear - Ha Hx HdRG; lia | clear - Ha Hx XF; unfold xfacts in XF; unfold FILE_BLOCK in Hx; lia | clear - Ha Hx XF; unfold xfacts in XF; lia ]).
assert (HnFP_C : forall a, fr_ptr f <= a < fr_ptr f + 40 -> ~ inFP ((cg_raw s + 40, cg_raw s + 44) :: asink_fp pf) a)
by (intros a Ha (r & Hr & Hx); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd sink_token] in Hx;
[ clear - Ha Hx HdRC; lia | clear - Ha Hx XF; unfold xfacts in XF; unfold FILE_BLOCK in Hx; lia | clear - Ha Hx XF; unfold xfacts in XF; lia ]).
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 529%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFP_lo; clear - Ha HF8lo HF8c HFceil C1 Hob241 Hob242 Hob253 Huar; ceil; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha Hob241 Hob242 Hob253 Huar; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 516%nat F _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFP_F; clear - Ha Hob241 Hob242 Hob253 Huar; lia | intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha Hob241 Hob242 Hob253 Huar; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 60%nat); [exact HJc | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJc | exact HJ4 | evalE AG | clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
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
eapply (region_kept_block_sub SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat _ _ _ _ _ g CGIF_SIZE HJc);
[ evalE AG | exact Hing3 | exact Hing4 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia | intros a Ha; apply HnFP_G; clear - Ha Hob241 Hob242 Hob253 Huar; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_subw B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 11%nat _ _ _ _ _ (fr_ptr f) FRAME_SIZE HJc);
[ evalE AG | exact Hcur3 | exact Hcur4 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia
| intros a Ha; apply HnFP_C; clear - Ha Hob241 Hob242 Hob253 Huar; lia | intros a Ha; apply (proj1 (Hcpres4 a ltac:(clear - Ha Hob241 Hob242 Hob253 Huar; lia))) ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
prreg HS (10%bv : bv 5) Rres. rewrite Hres in Rres.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => ra_join HS ss_R5 932%nat ([] : list (bv 5)) ltac:(idtac); fl_handX RR5 HS end.
split; [destruct Hpt as [(_ & _ & Hk0 & _) | (_ & _ & Hk2 & _)]; [clear - Hk0 | clear - Hk2]; lia|].
assert (HFL : YO07.flush_frame (gcfg_of s GPAL) (rc_int (rw_cur s)) cur bef = (code, bytes)).
{ rewrite (YI0f.flush_frame_split (gcfg_of s GPAL) cur bef (rc_int (rw_cur s))), <- HRA.
unfold YI0f.fl_w, YI0f.fl_h, YI0f.fl_top, YI0f.fl_left.
change (YI0f.fl_dims (gcfg_of s GPAL) cur bef) with (xdims (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) (mkFLXX path pf Sg GPAL cur bef)).
rewrite XD.
rewrite Hrwattr, flag_raw_attr_of, (raw_sgct_model s GPAL). cbn [YO07.g_attr YO07.g_ngp gcfg_of].
unfold ximg, xG. cbn [c_s x_GPAL x_cur x_bef].
rewrite Xfattr, XATTR, Xdelay, XCd, XCdisp, XTI. unfold xtidx, xhastr, xG, YI0f.fl_rattr. cbn [c_s c_f x_GPAL x_cur x_bef].
replace (ACj7.fl_slct (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0)) with (YI0f.fl_slct cur)
by (unfold ACj7.fl_slct, YI0f.fl_slct; cbn [c_f]; rewrite XULCT, XCn; reflexivity).
rewrite <- XCa. reflexivity. }
split.
{ exists res; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); symmetry; exact Rres | split; [exact Hres64|]].
split.
- exists code, bytes. split; [exact HFL|]. split; [exact Hcode|].
split; [cbn [obj_at LAY_Raw] in Oraw4; destruct Oraw4 as (_ & _ & _ & _ & _ & _ & _ & _ & [V8 _] & _); cbn [fst snd N.to_nat] in V8; rewrite <- Hrcur; exact V8|].
split; [exact HSINK4 | clear - HLEN4 HwhN Hwh0; unfold FRAME_OUT in *; lia].
- exists (xmacc MT pt (w * h) + xn_rawadd XN (w * h)). split; [exact (mle_station MT S S3 S4 _ _ MLAW XMLE MLE4)|].
pose proof (HXM N (w * h) ltac:(clear - Hw1 Hh1 Hwh0 HwhN; nia) HNle) as BM. pose proof (HXN N (w * h) ltac:(clear - Hw1 Hh1 Hwh0 HwhN; nia) HNle) as BN.
pose proof (HXMN (w * h) ltac:(clear - Hw1 Hh1 Hwh0 HwhN HNle; nia)) as BMN.
pose proof (mo_malloc_nonneg MT MLAW (w * h) Hwh0) as M0.
unfold xmacc; destruct (pt =? 0); clear - BM BN BMN M0; lia. }
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X|].
exists pt. cbn [c_ly c_S].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E892|]. split; [exact Hrpt|].
destruct Hpt as [(Hp0 & _ & _ & Eab3) | (Hp1 & _ & _ & (Hq1 & Hq2 & Hq3 & Eab3 & Hawr & Haft))].
- left. split; [exact Hp0|]. rewrite <- Eab3. exact HPerm4.
- right. split; [exact Hp1|]. exists (w * h). split; [exact Hwh0|]. split; [rewrite <- Eab3; exact HPerm4|].
eapply aftok_mono; [exact Haft|]. intros a (r & Hr & Hx). exists r. split; [|exact Hx].
unfold fl_FPX. cbn [c_f c_s x_pf]. cbn [In] in Hr. destruct Hr as [<- | []]. left. reflexivity.
Qed.
Lemma fl_R4X : fl_fromX1 KS MT XN B CTX wfn ss_R5 (INV_R5X KS MT XN B) -> fl_fromX0 KS MT XN B CTX wfn ss_R4 (INV_R4X MT B).
Proof. exact fl_R4X_aux. Qed.
End o.
End m.
End d.
