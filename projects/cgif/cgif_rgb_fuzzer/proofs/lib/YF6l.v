(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF6d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF6n YF6c YF6j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAME, SHADOW_OFF, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_IAL_FLAG, TFX_TP, TFX_TSD in *.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variables (p nn hb1 : Z) (q : qcache) (j1 j2 j3 : Z).
Variable ii : bool.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53100 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii.
Local Notation tr := (YF6n.tr ly regs0 ch).
Local Notation LENv := (YF6n.LENv ly regs0 ch).
Local Notation IMv := (YF6n.IMv p).
Local Notation HWv := (YF6n.HWv hb1).
Local Notation SPv := (YF6n.SPv p).
Local Notation N8v := (YF6n.N8v nn).
Local Notation CNT8v := (YF6n.CNT8v nn).
Local Notation QBFv := (YF6n.QBFv nn q).
Local Notation XW := (YF6n.XW ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E0 := (YF6n.E0 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation Er := (YF6n.Er ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E2 := (YF6n.E2 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E1 := (YF6n.E1 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E8 := (YF6n.E8 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E10 := (YF6n.E10 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E4 := (YF6n.E4 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaT := (YF6n.EaT ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaC := (YF6n.EaC ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaSB := (YF6n.EaSB ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaTOP := (YF6n.EaTOP ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaLEN := (YF6n.EaLEN ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaIM := (YF6n.EaIM ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaHW := (YF6n.EaHW ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaN := (YF6n.EaN ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaSHB := (YF6n.EaSHB ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaSP := (YF6n.EaSP ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaN8 := (YF6n.EaN8 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaCNT8 := (YF6n.EaCNT8 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaQBF := (YF6n.EaQBF ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaJ1 := (YF6n.EaJ1 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaJ2 := (YF6n.EaJ2 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaJ3 := (YF6n.EaJ3 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation AL := YF6n.AL.
Local Notation HB1MASK := (YF6n.HB1MASK hb1).
Local Notation PSTATIC := (YF6n.PSTATIC ly p nn).
Local Notation REG0 := YF6n.REG0.
Local Notation FFM := YF6n.FFM.
Local Notation SS0 := YF6n.SS0.
Local Notation LYB := (YF6n.LYB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation LYD := (YF6n.LYD W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation iv_vs_stack := (YF6n.iv_vs_stack W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation N8_ge := (YF6n.N8_ge W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation stack_ivs := (YF6n.stack_ivs W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation derived_ranges := (YF6n.derived_ranges W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation derived_align := (YF6n.derived_align W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WINT := (YF6n.WINT ly).
Local Notation WINB := (YF6n.WINB p).
Local Notation WIN := (YF6n.WIN ly regs0 p).
Local Notation WSKEL := YF6n.WSKEL.
Local Notation win_sub := YF6n.win_sub.
Local Notation win_sub_sound := (YF6n.win_sub_sound W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WSKEL_WIN := (YF6n.WSKEL_WIN W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation windows_WIN := (YF6n.windows_WIN W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation frame_WIN := (YF6n.frame_WIN W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN_zone := (YF6n.WIN_zone W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN_off := (YF6n.WIN_off W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN_not_high := (YF6n.WIN_not_high W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation all_disjoint_of_forall := (YF6n.all_disjoint_of_forall W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation kept_of_frame := (YF6n.kept_of_frame W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation kept_of_frame_hi := (YF6n.kept_of_frame_hi W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation kept_of_vframe := (YF6n.kept_of_vframe W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation p_ivs := (YF6n.p_ivs W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation SKEL_TAIL := YF6n.SKEL_TAIL.
Local Notation DZONE := (YF6n.DZONE ly).
Local Notation IZONE := YF6n.IZONE.
Local Notation tail_facts := (YF6n.tail_facts W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation MEQ := (YF6n.MEQ ly regs0 mem0 p).
Local Notation IAL_POST := (YF6n.IAL_POST W).
Local Notation MEQI := (YF6n.MEQI W ly regs0 mem0 p).
Local Notation MEQI_frame := (YF6n.MEQI_frame W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN2 := (YF6n.WIN2 ly regs0 p).
Local Notation WIN2_WIN := (YF6n.WIN2_WIN ly regs0 p).
Local Notation WSKEL2 := YF6n.WSKEL2.
Local Notation WSKEL2_WIN2 := (YF6n.WSKEL2_WIN2 W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation windows_WIN2 := (YF6n.windows_WIN2 W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation OBJQ := (YF6n.OBJQ regs0).
Local Notation MEQJ := (YF6n.MEQJ W ly regs0 mem0 p).
Local Notation MEQJ_frame := (YF6n.MEQJ_frame W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation memset_stretch := (YF6n.memset_stretch W ly regs0 mem0 md0 ch p nn hb1 q j1 j2 j3 ii mat0 FH).
Local Notation notWIN_img := (YF6n.notWIN_img W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_shb := (YF6n.notWIN_shb W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_Thead := (YF6n.notWIN_Thead W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_C := (YF6n.notWIN_C W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_NB := (YF6n.notWIN_NB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_SB := (YF6n.notWIN_SB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Hp10 Htp Hra Hra4096 Hsp Hsp_al Hch Hp IMG Hp_al Hnn Hhb1 Hhb1m Hp_static Hp_pres Hsh_pres Hqb Hjunk HIAL IA1 U1 SEED].
Local Notation off_T := (YF6n.off_T W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_C := (YF6n.off_C W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_NB := (YF6n.off_NB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_SB := (YF6n.off_SB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_P := (YF6n.off_P W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_P8 := (YF6n.off_P8 W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation pres_off_of_frame := (YF6n.pres_off_of_frame W).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; unfold kThreadObjSize; tac | img_apply off_C; tac | img_apply off_P8; tac | img_apply off_P; tac
| img_apply off_NB; unfold kNodesBlockSize; tac | img_apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Notation at_D1 := (YF6j.at_D1 W ly regs0 mem0 md0 ch p nn hb1 q j1 j2 j3).
Ltac show_regs HS := lazymatch type of HS with st_ok _ _ ?ss _ => let r := img_ev (ss_pc ss, ss_regs ss) in idtac r end.
Ltac show_skel HS := lazymatch type of HS with st_ok _ _ ?ss _ => let r := img_ev (combine (seq 0 (length (ss_mem ss))) (skeleton (ss_mem ss))) in idtac r end.
Ltac show_reg HS i := lazymatch type of HS with st_ok _ _ ?ss _ => let r := img_ev (nth i (ss_mem ss) (YQ0b.mkRegion None 0 0 0 0 [])) in idtac r end.
Definition EQ4a (m4 m : word -> option byte) : Prop := forall x : word, ~ WIN2 (bv_unsigned x) -> m x = m4 x.
Definition EQ4 (m4 m : word -> option byte) : Prop :=
forall x : word, ~ WIN2 (bv_unsigned x) -> ~ (SPv <= bv_unsigned x < SPv + CNT8v) -> m x = m4 x.
Lemma EQ4a_frame : forall (E : env) rs (m4 m m' : word -> option byte),
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL2 || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> EQ4a m4 m -> EQ4a m4 m'.
Proof. intros E rs m4 m m' HE Hb HF M x Hx. rewrite <- (M x Hx). img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WIN2 E rs _ HE Hb Hw). Qed.
Ltac eq4a_acc HE :=
match goal with
| M : EQ4a ?m4 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "EQ" in
pose proof (EQ4a_frame E rs m4 ma mb HE ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Lemma EQ4_frame : forall (E : env) rs (m4 m m' : word -> option byte),
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL2 || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> EQ4 m4 m -> EQ4 m4 m'.
Proof. intros E rs m4 m m' HE Hb HF M x Hx Hs. rewrite <- (M x Hx Hs). img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WIN2 E rs _ HE Hb Hw). Qed.
Ltac eq4_acc HE :=
match goal with
| M : EQ4 ?m4 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "EQ" in
pose proof (EQ4_frame E rs m4 ma mb HE ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Definition after_D1 (msD : machine_state) (E3 : env) (regs4 : bvmap 5 word) (mem4 : word -> option byte) : Prop :=
msD = mkst (ms_regs msD) (w64 (0x72fcc + D_2c4)) (ms_mem msD) (seg_rom tfxsegs) /\
(forall k, (k < aHAVf)%nat -> ew E3 k = ew E0 k) /\
st_ok tfxsegs E3 SS_B (restrict (w_H W) msD) /\
regs_preserved (ms_regs msD) regs4 /\
(forall x : word, ~ (sp0 - 2256 - DEP_STK <= bv_unsigned x < sp0 - 2256) -> ~ DZONE (bv_unsigned x) -> mem4 x = ms_mem msD x) /\
(forall a, apresent (w_H W) (ms_mem msD) a -> apresent (w_H W) mem4 a) /\
MEQI (ms_mem msD) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msD) a).
Definition EQS (m4 m : word -> option byte) : Prop :=
EQ4 m4 m /\ (forall x : word, SPv <= bv_unsigned x < SPv + CNT8v -> m x = Some (Z_to_bv 8 253)).
Lemma EQS_frame : forall (E : env) rs (m4 m m' : word -> option byte),
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL2 || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> EQS m4 m -> EQS m4 m'.
Proof.
intros E rs m4 m m' HE Hb HF [M S]. split.
- intros x Hx Hs. rewrite <- (M x Hx Hs). img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WIN2 E rs _ HE Hb Hw).
- intros x Hs. rewrite <- (S x Hs). img_apply HF. intros Hw. pose proof (WIN_zone _ (WIN2_WIN _ (windows_WIN2 E rs _ HE Hb Hw))) as (_ & Hh & _).
pose proof derived_ranges as DR. img_apply Hh. clear - Hs DR. numconst. zlia.
Qed.
Ltac eqs_acc HE :=
match goal with
| M : EQS ?m4 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "EQ" in
pose proof (EQS_frame E rs m4 ma mb HE ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Lemma denot_by_zev : forall (E : env) t v, svpure t = true -> 0 <= v < 2 ^ 64 -> zev (rho_of E) t = v -> sv_denot E t = Z_to_bv 64 v.
Proof.
intros E t v Hp Hv Hz. img_apply bv_eq. rewrite Z_to_bv_unsigned. img_change (bv_unsigned (sv_denot E t)) with (U E t).
rewrite (U_zev E t Hp), Hz. unfold bv_wrap, bv_modulus. img_change (2 ^ Z.of_N 64) with (2 ^ 64). symmetry. img_apply Z.mod_small. img_exact Hv.
Qed.
Definition at_ENQ (mem4 : word -> option byte) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists (ms : machine_state) mat (E5 : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
ms = mkst (ms_regs ms) (w64 (0x35dd8 + D_150)) (ms_mem ms) (seg_rom tfxsegs) /\
(forall k, (k < aHAVf)%nat -> ew E5 k = ew E0 k) /\
st_ok tfxsegs E5 SS_E (restrict (w_H W) ms) /\
EQS mem4 (ms_mem ms) /\ (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
img_apply U_eq_by_zev; [img_refl | img_refl |].
Lemma segCm1 : forall msD E3 regs4 mem4 mat4, after_D1 msD E3 regs4 mem4 ->
SRr tfxsegs W (mkCfg (mkst regs4 (w64 (0x35b08 + D_150)) mem4 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat4 md0)) (at_ENQ mem4).
Proof.
intros msD E3 regs4 mem4 mat4 (HshD & HEn3 & HS & HP4 & Hfr4 & Hpr4 & MEQD0 & PRESD).
open_FH. pose proof Hwx_tfa as Hwx. destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB. pose proof derived_ranges as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
set (XD := fun a : Z => (sp0 - 2256 - DEP_STK <= a < sp0 - 2256) \/ DZONE a).
assert (Hfr' : forall x : word, ~ XD (bv_unsigned x) -> mem4 x = ms_mem msD x).
{ intros x Hx. (subst XD; cbv beta). img_apply Hfr4; cbn beta in Hx; tauto. }
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := img_ev (ss_mem ss) in
lazymatch m with ?robj :: ?rscr :: ?rest =>
pose proof (st_ok_after_call tfxsegs 86 E3 ss ms0 regs4 (mrestrict (w_H W) mem4) (robj :: trim_lo rscr (-2256) :: rest) (0x35b08 + D_150) HS eq_refl
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (img_apply submem_keep; [img_try (img_apply subregion_refl)|]; img_apply submem_keep; [img_try (img_apply subregion_trim_lo) | img_try (img_apply submem_refl)]))
ltac:(img_try ((img_case; vm_compute); img_refl)) HP4) as HS1;
let rsv := img_ev (robj :: trim_lo rscr (-2256) :: rest) in
img_change (robj :: trim_lo rscr (-2256) :: rest) with rsv in HS1;
let ss2 := img_ev (ss_after_call ss rsv 86 (0x35b08 + D_150)) in
change (ss_after_call ss rsv 86 (0x35b08 + D_150)) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?r2 :: ?r3 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfxsegs E3 (mrestrict (w_H W) (ms_mem msD)) (mrestrict (w_H W) mem4)) (r0 :: r1 :: r2 :: r3 :: tail));
[ img_try (pose proof LYD as (_ & _ & (_ & _ & NBSTK) & (_ & SBSTK) & _); unfold zdisjoint in NBSTK, SBSTK; cbn [fst snd] in NBSTK, SBSTK;
constructor; [|constructor; [|constructor; [|constructor]]];
[ eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
rewrite (HEn3 2%nat ltac:((img_case; cbv); zlia)), E2; (subst XD; cbv beta); unfold YF6n.DZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo Hhi LB NBSTK SBSTK; numconst; zlia
| eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
rewrite (HEn3 2%nat ltac:((img_case; cbv); zlia)), E2; (subst XD; cbv beta); unfold YF6n.DZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo Hhi LB NBSTK SBSTK; numconst; zlia
| eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
rewrite (HEn3 37%nat ltac:((img_case; cbv); zlia)), EaIM; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia);
(subst XD; cbv beta); unfold YF6n.DZONE; intros a Ha; cbn beta; clear - Ha DR Usp Hlo LB; numconst; zlia
| eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
rewrite (HEn3 2%nat ltac:((img_case; cbv); zlia)), E2; (subst XD; cbv beta); unfold YF6n.DZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo Hhi LB NBSTK SBSTK; numconst; zlia
| img_apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by ((img_case; vm_compute); img_refl);
pose proof (tail_facts E3 r HEn3 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); intros a Ha; (subst XD; cbv beta); unfold YF6n.DZONE; cbn beta; clear - Ha Y1 Y2 Y3 Y4 Y6; numconst; zlia ])
| img_try (specialize (HS1 KEPT); clear KEPT) ]
end.
assert (PRES4 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem4 a) by (img_try (intros a Ha; apply Hpr4, PRESD, Ha)).
set (En4 := havoc E3 86 (map (getr regs4) CLOB)) in HS1.
assert (HEn4 : forall k, (k < aHAVf)%nat -> ew En4 k = ew E0 k) by (img_try (intros k Hk; (subst En4; cbv beta); unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; img_apply HEn3; img_exact Hk)).
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- 2256) (- ASTACK) (- 2256) [])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn4 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2;
split; [img_try (clear - Usp Hlo LB; numconst; zlia)|]; split; [img_try (clear - Usp Hlo LB; numconst; zlia)|];
split; [img_try (intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - Usp Hlo LB Ho; numconst; zlia) | img_apply PRES4; clear - Ho; numconst; zlia]) | img_try (constructor)]
| img_apply all_disjoint_of_forall; intros r' [<-|[<-|[<-|[<-|Hr']]]];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold ASTACK; zlia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold ASTACK; zlia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn4 37%nat ltac:(img_try ((img_case; cbv); zlia))), (HEn4 2%nat ltac:(img_try ((img_case; cbv); zlia))), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (img_try (clear - DR; numconst; zlia)); clear - DR Usp Hlo LB; numconst; zlia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold ASTACK; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_facts En4 r' HEn4 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn4 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2;
clear - Y1 Y2; unfold ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (EQ0 : EQ4a mem4 mem4) by (img_try (intros x _; img_refl)).
srr_run_to_sh tfxtbl_rrF_ok HS (0x35c28 + D_150). eq4a_acc HEn4.
assert (R38 : rho_of En4 38%nat = HWv) by (img_try (unfold rho_of; rewrite (HEn4 38%nat ltac:((img_case; cbv); zlia)), EaHW; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (T1V : zev (rho_of En4) T1term = 3 + 256 * hb1) by (img_try (img_apply T1_val; [img_try (img_exact Hhb1) | img_try (rewrite R38; img_refl)])).
assert (R39 : rho_of En4 39%nat = nn) by (img_try (unfold rho_of; rewrite (HEn4 39%nat ltac:((img_case; cbv); zlia)), EaN; unfold w64; img_apply unsigned_lit_small; clear - Hnn; zlia)).
set (SZt := SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SRL T1term (SLit 16)) (SLit 32)) (SOff 39%nat 0)).
assert (SIZEV : zev (rho_of En4) SZt = nn).
{ (subst SZt; cbv beta). cbn [zev]. rewrite T1V, R39. unfold zalu_raw.
img_change (Z.land (zcanon 16) 63) with 16. img_change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftr_div_pow2 by zlia. rewrite (Z.div_small (3 + 256 * hb1) (2 ^ 16)) by (img_try (clear - Hhb1; zlia)).
img_change (zcanon (Z.shiftl (zcanon 0) 32)) with 0. rewrite Z.add_0_r, (zcanon_id nn) by (img_try (clear - Hnn; unfold M64; zlia)). rewrite Z.lor_0_l.
img_apply zcanon_id. clear - Hnn; unfold M64; zlia. }
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 39%nat 0)) in HS; [| img_try (intros X; discriminate)
| img_try (pin_prep; fold T1term; fold SZt; rewrite SIZEV; cbn [zev]; rewrite R39, Z.add_0_r; img_apply zcanon_id; clear - Hnn; unfold M64; zlia)].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rrF_ok HS. eq4a_acc HEn4.
srr_branch_sh tfxtbl_rrF_ok HS.
{
assert (ZLO : p + N8v <= kLowShadowBeg).
{ rewrite branch_geu_U in Hc. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. revert Hc.
rewrite !U_SOff, (HEn4 40%nat ltac:(img_try ((img_case; cbv); zlia))), EaSHB, (HEn4 10%nat ltac:(img_try ((img_case; cbv); zlia))), E10, Hp10. unfold w64.
rewrite !unsigned_lit_small by (img_try (clear - DR; numconst; zlia)). rewrite !zcanon_id by (img_try (clear - DR; unfold M64; numconst; zlia)).
pose proof Hp as (_ & _ & ZC). pose proof N8_ge as [N8a _]. clear - ZC N8a. intros Hc. unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. zlia. }
clear Hc. srr_run_sh tfxtbl_rrF_ok HS. eq4a_acc HEn4.
pose proof derived_align as (_ & _ & N8al & _).
assert (N8V : zev (rho_of En4) (SAlu ALU_AND (SAlu ALU_ADD SZt (SLit 7)) (SLit (-8))) = N8v).
{ cbn [zev]. rewrite SIZEV. unfold zalu_raw. rewrite (zcanon_id 7) by (img_try (unfold M64; zlia)). rewrite (zcanon_id (nn + 7)) by (img_try (clear - Hnn; unfold M64; zlia)).
img_change (zcanon (-8)) with (2 ^ 64 - 8). rewrite land_m8_64 by (img_try (clear - Hnn; zlia)). unfold YF6n.N8v.
pose proof (Z.div_mod (nn + 7) 8 ltac:(img_try (zlia))). pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(img_try (zlia))). rewrite zcanon_id; [img_try (clear - Hnn H H0; zlia) | img_try (clear - Hnn H H0; unfold M64; zlia)]. }
assert (R42 : rho_of En4 42%nat = N8v) by (img_try (unfold rho_of; rewrite (HEn4 42%nat ltac:((img_case; cbv); zlia)), EaN8; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
apply (st_ok_pin_regU _ _ _ 11%bv (SOff 42%nat 0)) in HS; [| img_try (intros X; discriminate)
| img_try (pin_prep; fold T1term; fold SZt; etransitivity; [|symmetry; img_exact N8V]; cbn [zev]; rewrite R42, Z.add_0_r; img_apply zcanon_id; clear - DR; unfold M64; zlia)].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 15%bv (SLit 0)) in HS; [| img_try (intros X; discriminate)
| img_try (pin_prep; fold T1term; fold SZt;
change (zev (rho_of En4) (SLit 0) = zcanon (Z.land (zev (rho_of En4) (SAlu ALU_AND (SAlu ALU_ADD SZt (SLit 7)) (SLit (-8)))) (zev (rho_of En4) (SLit 7))));
rewrite N8V; cbn [zev]; rewrite (zcanon_id 7) by (unfold M64; zlia); rewrite land_7_mod by (clear - DR; zlia); rewrite N8al; img_refl)].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rrF_ok HS. eq4a_acc HEn4.
srr_branch_sh tfxtbl_rrF_ok HS.
2:{ exfalso. rewrite branch_geu_U in Hc. apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. revert Hc.
rewrite !U_zev by img_refl. cbn [zev zalu_raw]. unfold rho_of.
rewrite ?(HEn4 40%nat ltac:(img_try ((img_case; cbv); zlia))), ?(HEn4 10%nat ltac:(img_try ((img_case; cbv); zlia))), ?(HEn4 42%nat ltac:(img_try ((img_case; cbv); zlia))), ?EaSHB, ?E10, ?Hp10, ?EaN8. unfold w64. rewrite !unsigned_lit_small by (img_try (clear - DR; numconst; zlia)).
clear - ZLO DR. numconst. zcanon_simp. zlia. }
clear Hc. srr_run_sh tfxtbl_rrF_ok HS. eq4a_acc HEn4.
pose proof derived_align as (_ & P8 & _).
assert (R10 : rho_of En4 10%nat = p) by (img_try (unfold rho_of; rewrite (HEn4 10%nat ltac:((img_case; cbv); zlia)), E10, Hp10; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (R40 : rho_of En4 40%nat = SHADOW_OFF) by (img_try (unfold rho_of; rewrite (HEn4 40%nat ltac:((img_case; cbv); zlia)), EaSHB; unfold w64; img_apply unsigned_lit_small; numconst; zlia)).
assert (R41 : rho_of En4 41%nat = SPv) by (img_try (unfold rho_of; rewrite (HEn4 41%nat ltac:((img_case; cbv); zlia)), EaSP; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (R43 : rho_of En4 43%nat = CNT8v) by (img_try (unfold rho_of; rewrite (HEn4 43%nat ltac:((img_case; cbv); zlia)), EaCNT8; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (Ep : p = 8 * (p / 8)) by (img_try (clear - DR; zlia)).
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 41%nat 0)) in HS; [| img_try (intros X; discriminate)
| img_try (pin_prep; cbn [zev]; unfold zalu_raw; rewrite R10, R40, R41, !Z.add_0_r; img_change (Z.land (zcanon 3) 63) with 3;
rewrite (zcanon_id p) by (clear - DR; numconst; unfold M64; zlia); rewrite Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
unfold YF6n.SPv; numconst; zcanon_simp; clear - DR; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 43%nat 0)) in HS; [| img_try (intros X; discriminate)
| img_try (pin_prep; cbn [zev]; unfold zalu_raw; rewrite R10, R42, R43, !Z.add_0_r; img_change (Z.land (zcanon 3) 63) with 3;
rewrite (zcanon_id p) by (clear - DR; numconst; unfold M64; zlia); rewrite (zcanon_id (p + -8)) by (clear - DR; numconst; unfold M64; zlia);
rewrite (zcanon_id N8v) by (clear - DR; numconst; unfold M64; zlia); rewrite (zcanon_id (p + -8 + N8v)) by (clear - DR; numconst; unfold M64; zlia);
rewrite !Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8; rewrite (zcanon_id 1) by (unfold M64; zlia);
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DR))))))))) as EN8;
numconst; zcanon_simp; clear - DR Ep EN8; nia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msM end.
match goal with M : EQ4a mem4 (ms_mem msM) |- _ => rename M into EQM end.
assert (SHPRES : forall a, SPv <= a < SPv + CNT8v -> apresent (w_H W) (ms_mem msM) a).
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha DR; numconst; zlia)).
assert (NW : ~ WIN2 a) by (img_try (intros Hw; destruct (WIN_zone a (WIN2_WIN a Hw)) as (_ & Hnb & _); img_apply Hnb; clear - Ha DR; numconst; zlia)).
img_apply (apresent_same (w_H W) mem4). { img_apply EQM. rewrite unsigned_lit_small by img_exact Ra. img_exact NW. }
img_apply Hpr4. img_apply (apresent_same (w_H W) mem0).
{ img_apply (proj1 MEQD0); rewrite unsigned_lit_small by img_exact Ra; [img_try (intros Hw; destruct (WIN_zone a Hw) as (_ & Hnb & _); img_apply Hnb; clear - Ha DR; numconst; zlia)|].
unfold YF6n.IZONE. clear - Ha DR; numconst; zlia. }
img_apply Hsh_pres. img_exact Ha. }
rreg HS (11%bv : bv 5) RA1m.
eapply (memset_stretch 102 En4 _ _ _ SPv CNT8v (0x35db4 + D_150));
[ img_try (img_exact HS) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (rreg HS (10%bv : bv 5) R; rewrite R, (HEn4 41%nat ltac:((img_case; cbv); zlia)), EaSP; img_refl)
| img_try (rreg HS (12%bv : bv 5) R; rewrite R, (HEn4 43%nat ltac:((img_case; cbv); zlia)), EaCNT8; img_refl)
| img_try (rreg HS (1%bv : bv 5) R; rewrite R; img_refl)
| img_try (clear - DR; zlia) | img_try (clear - DR; numconst; zlia) | img_try (clear - DR; numconst; zlia) | img_refl | img_try (zlia)
| img_try (img_exact SHPRES)
| img_try (intros r Hr) | img_try (intros r a Hr) | img_try (intros r a Hr) | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|Hr]]]]];
[ cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn4 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn4 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn4 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn4 37%nat ltac:(img_try ((img_case; cbv); zlia))), EaIM; unfold w64; rewrite unsigned_lit_small by (img_try (clear - DR; numconst; zlia)); clear - DR; numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn4 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_facts En4 r HEn4 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7); clear - DR Y1 Y2 Y3 Y4 Y7; numconst; zlia ].
intros regs5 mem5 mat5 HS5 H10c Hfr5 Hpr5 Hfill. clear HS. rename HS5 into HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En5 := E) in HS; let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
assert (HEn5 : forall k, (k < aHAVf)%nat -> ew En5 k = ew E0 k) by (img_try (intros k Hk; (subst En5; cbv beta); unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; img_apply HEn4; img_exact Hk)).
assert (EQ5 : EQS mem4 mem5).
{ split; [img_try (intros x Hx Hs; rewrite (Hfr5 x Hs); img_exact (EQM x Hx))|]. intros x Hs. rewrite (Hfill x Hs), RA1m. img_refl. }
clear EQM.
apply (st_ok_forget_reg En5 _ _ 5%bv 108) in HS; [| img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl)].
apply (st_ok_forget_reg _ _ _ 7%bv 109) in HS; [| img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl)].
apply (st_ok_forget_reg _ _ _ 17%bv 110) in HS; [| img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl)].
apply (st_ok_forget_reg _ _ _ 28%bv 111) in HS; [| img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl)].
apply (st_ok_facts_leb tfxsegs _ _ _ YF6c.F_R) in HS; [| img_try ((img_case; vm_compute); img_refl)].
cbn [ms_regs restrict] in HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En6 := E) in HS; img_change ss with YF6c.SS_R in HS end.
assert (HEn6 : forall k, (k < aHAVf)%nat -> ew En6 k = ew E0 k) by (img_try (intros k Hk; (subst En6; cbv beta); unfold aHAVf in Hk; rewrite !ew_havoc_old by zlia; img_apply HEn5; img_exact Hk)).
clearbody En6. clear En5 HEn5.
srr_run_to_sh tfxtbl_rrF_ok HS (0x35dd8 + D_150). eqs_acc HEn6.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msE end.
match goal with M : EQS mem4 (ms_mem msE) |- _ => rename M into EQE end.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En6 _ _ HS eq_refl) as HshE; cbn [ss_pc] in HshE.
img_apply SRr_ret. split; [img_refl|].
eexists msE, _, En6. split; [img_refl|]. split; [img_try (img_exact HshE)|]. split; [img_try (img_exact HEn6)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact EQE)|].
assert (BV2 : bv_unsigned (ew En6 2) = sp0) by (img_try (rewrite (HEn6 2%nat ltac:((img_case; cbv); zlia)), E2; img_refl)).
intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2256)); [|img_try (destruct (Z_lt_le_dec a (sp0 - 2208)); [|destruct (Z_lt_le_dec a (sp0 - 64))])].
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha l; numconst; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 2 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha l l0; numconst; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia)) ].
- img_apply (apresent_same (w_H W) mem4); [|img_try (img_apply PRES4; img_exact Ha)]. img_apply (proj1 EQE); rewrite unsigned_lit_small by (img_try (clear - Ha Usp Hlo LB; numconst; zlia)).
+ intros Hw. unfold YF6n.WIN2, YF6n.WINT, YF6n.WINB in Hw. pose proof stack_ivs as (IT & _ & _ & _ & _ & IPP).
pose proof LYD as ((_ & _ & _ & _ & PSTK) & _). unfold zdisjoint in PSTK. cbn [fst snd] in PSTK.
clear - Hw Ha l0 l1 DR LB Hlo Hhi IT IPP PSTK. numconst. unfold sp0 in *. zlia.
+ clear - Ha l0 DR Hlo LB. numconst. zlia.
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 4 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha l1; numconst; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia)) ].
}
assert (ZHI : kHighMemBeg <= p - 16).
{ rewrite branch_geu_U in Hc. apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. revert Hc.
rewrite !U_SOff, (HEn4 40%nat ltac:(img_try ((img_case; cbv); zlia))), EaSHB, (HEn4 10%nat ltac:(img_try ((img_case; cbv); zlia))), E10, Hp10. unfold w64.
rewrite !unsigned_lit_small by (img_try (clear - DR; numconst; zlia)). rewrite !zcanon_id by (img_try (clear - DR; unfold M64; numconst; zlia)).
pose proof Hp as (_ & _ & ZC). pose proof N8_ge as [N8a _]. clear - ZC N8a. intros Hc. unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. zlia. }
clear Hc.
apply (st_ok_add_atom tfxsegs En4 _ _ 10%nat (mkAF (kHighMemBeg + 16) (CEIL_MAX - 16) 4)) in HS.
2:{ split; [|img_try (split; [|cbn [af_al2]; zlia])]; cbn [af_lo af_hi af_al2]; rewrite (HEn4 10%nat ltac:(img_try ((img_case; cbv); zlia))), E10, Hp10; unfold w64; rewrite unsigned_lit_small by (img_try (clear - DR; numconst; zlia)).
- pose proof Hp as (_ & ZB & _). pose proof derived_align as (P16 & _). clear - ZHI ZB DR P16. numconst. zlia.
- pose proof derived_align as (P16 & _). img_change (2 ^ 4) with 16. img_exact P16. }
lazymatch type of HS with st_ok _ _ ?ss _ => let ss2 := img_ev constr:(ss) in img_change ss with ss2 in HS end.
srr_run_sh tfxtbl_rrF_ok HS. eq4a_acc HEn4.
pose proof derived_align as (_ & _ & N8al & _).
assert (N8V : zev (rho_of En4) (SAlu ALU_AND (SAlu ALU_ADD SZt (SLit 7)) (SLit (-8))) = N8v).
{ cbn [zev]. rewrite SIZEV. unfold zalu_raw. rewrite (zcanon_id 7) by (img_try (unfold M64; zlia)). rewrite (zcanon_id (nn + 7)) by (img_try (clear - Hnn; unfold M64; zlia)).
img_change (zcanon (-8)) with (2 ^ 64 - 8). rewrite land_m8_64 by (img_try (clear - Hnn; zlia)). unfold YF6n.N8v.
pose proof (Z.div_mod (nn + 7) 8 ltac:(img_try (zlia))). pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(img_try (zlia))). rewrite zcanon_id; [img_try (clear - Hnn H H0; zlia) | img_try (clear - Hnn H H0; unfold M64; zlia)]. }
assert (R42 : rho_of En4 42%nat = N8v) by (img_try (unfold rho_of; rewrite (HEn4 42%nat ltac:((img_case; cbv); zlia)), EaN8; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
apply (st_ok_pin_regU _ _ _ 11%bv (SOff 42%nat 0)) in HS; [| img_try (intros X; discriminate)
| img_try (pin_prep; fold T1term; fold SZt; etransitivity; [|symmetry; img_exact N8V]; cbn [zev]; rewrite R42, Z.add_0_r; img_apply zcanon_id; clear - DR; unfold M64; zlia)].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 15%bv (SLit 0)) in HS; [| img_try (intros X; discriminate)
| img_try (pin_prep; fold T1term; fold SZt;
change (zev (rho_of En4) (SLit 0) = zcanon (Z.land (zev (rho_of En4) (SAlu ALU_AND (SAlu ALU_ADD SZt (SLit 7)) (SLit (-8)))) (zev (rho_of En4) (SLit 7))));
rewrite N8V; cbn [zev]; rewrite (zcanon_id 7) by (unfold M64; zlia); rewrite land_7_mod by (clear - DR; zlia); rewrite N8al; img_refl)].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rrF_ok HS. eq4a_acc HEn4.
srr_branch_sh tfxtbl_rrF_ok HS.
{ exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc. revert Hc.
rewrite !U_zev by img_refl. cbn [zev zalu_raw]. unfold rho_of.
rewrite ?(HEn4 10%nat ltac:(img_try ((img_case; cbv); zlia))), ?(HEn4 42%nat ltac:(img_try ((img_case; cbv); zlia))), ?E10, ?Hp10, ?EaN8. unfold w64. rewrite !unsigned_lit_small by (img_try (clear - DR; numconst; zlia)).
pose proof Hp as (_ & ZB & _). clear - ZB DR. numconst. zcanon_simp. zlia. }
clear Hc. srr_run_sh tfxtbl_rrF_ok HS. eq4a_acc HEn4.
pose proof derived_align as (_ & P8 & _).
assert (R10 : rho_of En4 10%nat = p) by (img_try (unfold rho_of; rewrite (HEn4 10%nat ltac:((img_case; cbv); zlia)), E10, Hp10; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (R40 : rho_of En4 40%nat = SHADOW_OFF) by (img_try (unfold rho_of; rewrite (HEn4 40%nat ltac:((img_case; cbv); zlia)), EaSHB; unfold w64; img_apply unsigned_lit_small; numconst; zlia)).
assert (R41 : rho_of En4 41%nat = SPv) by (img_try (unfold rho_of; rewrite (HEn4 41%nat ltac:((img_case; cbv); zlia)), EaSP; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; zlia)).
assert (R43 : rho_of En4 43%nat = CNT8v) by (img_try (unfold rho_of; rewrite (HEn4 43%nat ltac:((img_case; cbv); zlia)), EaCNT8; unfold w64; img_apply unsigned_lit_small; clear - DR; zlia)).
assert (Ep : p = 8 * (p / 8)) by (img_try (clear - DR; zlia)).
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 41%nat 0)) in HS; [| img_try (intros X; discriminate)
| img_try (pin_prep; cbn [zev]; unfold zalu_raw; rewrite R10, R40, R41, !Z.add_0_r; img_change (Z.land (zcanon 3) 63) with 3;
rewrite (zcanon_id p) by (clear - DR; numconst; unfold M64; zlia); rewrite Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
unfold YF6n.SPv; numconst; zcanon_simp; clear - DR; zlia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 43%nat 0)) in HS; [| img_try (intros X; discriminate)
| img_try (pin_prep; cbn [zev]; unfold zalu_raw; rewrite R10, R42, R43, !Z.add_0_r; img_change (Z.land (zcanon 3) 63) with 3;
rewrite (zcanon_id p) by (clear - DR; numconst; unfold M64; zlia); rewrite (zcanon_id (p + -8)) by (clear - DR; numconst; unfold M64; zlia);
rewrite (zcanon_id N8v) by (clear - DR; numconst; unfold M64; zlia); rewrite (zcanon_id (p + -8 + N8v)) by (clear - DR; numconst; unfold M64; zlia);
rewrite !Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8; rewrite (zcanon_id 1) by (unfold M64; zlia);
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DR))))))))) as EN8;
numconst; zcanon_simp; clear - DR Ep EN8; nia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msM end.
match goal with M : EQ4a mem4 (ms_mem msM) |- _ => rename M into EQM end.
assert (SHPRES : forall a, SPv <= a < SPv + CNT8v -> apresent (w_H W) (ms_mem msM) a).
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha DR; numconst; zlia)).
assert (NW : ~ WIN2 a) by (img_try (intros Hw; destruct (WIN_zone a (WIN2_WIN a Hw)) as (_ & Hnb & _); img_apply Hnb; clear - Ha DR; numconst; zlia)).
img_apply (apresent_same (w_H W) mem4). { img_apply EQM. rewrite unsigned_lit_small by img_exact Ra. img_exact NW. }
img_apply Hpr4. img_apply (apresent_same (w_H W) mem0).
{ img_apply (proj1 MEQD0); rewrite unsigned_lit_small by img_exact Ra; [img_try (intros Hw; destruct (WIN_zone a Hw) as (_ & Hnb & _); img_apply Hnb; clear - Ha DR; numconst; zlia)|].
unfold YF6n.IZONE. clear - Ha DR; numconst; zlia. }
img_apply Hsh_pres. img_exact Ha. }
rreg HS (11%bv : bv 5) RA1m.
eapply (memset_stretch 102 En4 _ _ _ SPv CNT8v (0x35db4 + D_150));
[ img_try (img_exact HS) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (rreg HS (10%bv : bv 5) R; rewrite R, (HEn4 41%nat ltac:((img_case; cbv); zlia)), EaSP; img_refl)
| img_try (rreg HS (12%bv : bv 5) R; rewrite R, (HEn4 43%nat ltac:((img_case; cbv); zlia)), EaCNT8; img_refl)
| img_try (rreg HS (1%bv : bv 5) R; rewrite R; img_refl)
| img_try (clear - DR; zlia) | img_try (clear - DR; numconst; zlia) | img_try (clear - DR; numconst; zlia) | img_refl | img_try (zlia)
| img_try (img_exact SHPRES)
| img_try (intros r Hr) | img_try (intros r a Hr) | img_try (intros r a Hr) | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|Hr]]]]];
[ cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn4 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn4 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn4 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn4 37%nat ltac:(img_try ((img_case; cbv); zlia))), EaIM; unfold w64; rewrite unsigned_lit_small by (img_try (clear - DR; numconst; zlia)); clear - DR; numconst; zlia
| cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite (HEn4 2%nat ltac:(img_try ((img_case; cbv); zlia))), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_facts En4 r HEn4 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7); clear - DR Y1 Y2 Y3 Y4 Y7; numconst; zlia ].
intros regs5 mem5 mat5 HS5 H10c Hfr5 Hpr5 Hfill. clear HS. rename HS5 into HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En5 := E) in HS; let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
assert (HEn5 : forall k, (k < aHAVf)%nat -> ew En5 k = ew E0 k) by (img_try (intros k Hk; (subst En5; cbv beta); unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; img_apply HEn4; img_exact Hk)).
assert (EQ5 : EQS mem4 mem5).
{ split; [img_try (intros x Hx Hs; rewrite (Hfr5 x Hs); img_exact (EQM x Hx))|]. intros x Hs. rewrite (Hfill x Hs), RA1m. img_refl. }
clear EQM.
apply (st_ok_forget_reg En5 _ _ 5%bv 108) in HS; [| img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl)].
apply (st_ok_forget_reg _ _ _ 7%bv 109) in HS; [| img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl)].
apply (st_ok_forget_reg _ _ _ 17%bv 110) in HS; [| img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl)].
apply (st_ok_forget_reg _ _ _ 28%bv 111) in HS; [| img_try (intros X; discriminate) | img_try ((img_case; vm_compute); img_refl)].
apply (st_ok_facts_leb tfxsegs _ _ _ YF6c.F_R) in HS; [| img_try ((img_case; vm_compute); img_refl)].
cbn [ms_regs restrict] in HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En6 := E) in HS; img_change ss with YF6c.SS_R in HS end.
assert (HEn6 : forall k, (k < aHAVf)%nat -> ew En6 k = ew E0 k) by (img_try (intros k Hk; (subst En6; cbv beta); unfold aHAVf in Hk; rewrite !ew_havoc_old by zlia; img_apply HEn5; img_exact Hk)).
clearbody En6. clear En5 HEn5.
srr_run_to_sh tfxtbl_rrF_ok HS (0x35dd8 + D_150). eqs_acc HEn6.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msE end.
match goal with M : EQS mem4 (ms_mem msE) |- _ => rename M into EQE end.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En6 _ _ HS eq_refl) as HshE; cbn [ss_pc] in HshE.
img_apply SRr_ret. split; [img_refl|].
eexists msE, _, En6. split; [img_refl|]. split; [img_try (img_exact HshE)|]. split; [img_try (img_exact HEn6)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact EQE)|].
assert (BV2 : bv_unsigned (ew En6 2) = sp0) by (img_try (rewrite (HEn6 2%nat ltac:((img_case; cbv); zlia)), E2; img_refl)).
intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2256)); [|img_try (destruct (Z_lt_le_dec a (sp0 - 2208)); [|destruct (Z_lt_le_dec a (sp0 - 64))])].
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha l; numconst; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 2 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha l l0; numconst; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia)) ].
- img_apply (apresent_same (w_H W) mem4); [|img_try (img_apply PRES4; img_exact Ha)]. img_apply (proj1 EQE); rewrite unsigned_lit_small by (img_try (clear - Ha Usp Hlo LB; numconst; zlia)).
+ intros Hw. unfold YF6n.WIN2, YF6n.WINT, YF6n.WINB in Hw. pose proof stack_ivs as (IT & _ & _ & _ & _ & IPP).
pose proof LYD as ((_ & _ & _ & _ & PSTK) & _). unfold zdisjoint in PSTK. cbn [fst snd] in PSTK.
clear - Hw Ha l0 l1 DR LB Hlo Hhi IT IPP PSTK. numconst. unfold sp0 in *. zlia.
+ clear - Ha l0 DR Hlo LB. numconst. zlia.
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 4 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2; clear - Ha l1; numconst; zlia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia)) ].
Qed.
End WK.
End b.
