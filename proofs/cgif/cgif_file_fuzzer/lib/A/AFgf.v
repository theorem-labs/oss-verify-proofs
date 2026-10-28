(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFeq AFgm AFfw AFgb AFgd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAME, SHADOW_OFF, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variables (p nn hb1 : Z) (q : qcache) (j1 j2 j3 : Z).
Variable ii : bool.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x5292c) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii.
Local Notation tr := (AFgm.tr ly regs0 ch).
Local Notation LENv := (AFgm.LENv ly regs0 ch).
Local Notation IMv := (AFgm.IMv p).
Local Notation HWv := (AFgm.HWv hb1).
Local Notation SPv := (AFgm.SPv p).
Local Notation N8v := (AFgm.N8v nn).
Local Notation CNT8v := (AFgm.CNT8v nn).
Local Notation QBFv := (AFgm.QBFv nn q).
Local Notation XW := (AFgm.XW ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E0 := (AFgm.E0 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation Er := (AFgm.Er ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E2 := (AFgm.E2 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E1 := (AFgm.E1 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E8 := (AFgm.E8 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E10 := (AFgm.E10 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation E4 := (AFgm.E4 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaT := (AFgm.EaT ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaC := (AFgm.EaC ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaSB := (AFgm.EaSB ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaTOP := (AFgm.EaTOP ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaLEN := (AFgm.EaLEN ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaIM := (AFgm.EaIM ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaHW := (AFgm.EaHW ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaN := (AFgm.EaN ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaSHB := (AFgm.EaSHB ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaSP := (AFgm.EaSP ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaN8 := (AFgm.EaN8 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaCNT8 := (AFgm.EaCNT8 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaQBF := (AFgm.EaQBF ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaJ1 := (AFgm.EaJ1 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaJ2 := (AFgm.EaJ2 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation EaJ3 := (AFgm.EaJ3 ly regs0 ch p nn hb1 q j1 j2 j3).
Local Notation AL := AFgm.AL.
Local Notation HB1MASK := (AFgm.HB1MASK hb1).
Local Notation PSTATIC := (AFgm.PSTATIC ly p nn).
Local Notation REG0 := AFgm.REG0.
Local Notation FFM := AFgm.FFM.
Local Notation SS0 := AFgm.SS0.
Local Notation LYB := (AFgm.LYB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation LYD := (AFgm.LYD W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation iv_vs_stack := (AFgm.iv_vs_stack W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation N8_ge := (AFgm.N8_ge W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation stack_ivs := (AFgm.stack_ivs W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation derived_ranges := (AFgm.derived_ranges W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation derived_align := (AFgm.derived_align W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WINT := (AFgm.WINT ly).
Local Notation WINB := (AFgm.WINB p).
Local Notation WIN := (AFgm.WIN ly regs0 p).
Local Notation WSKEL := AFgm.WSKEL.
Local Notation win_sub := AFgm.win_sub.
Local Notation win_sub_sound := (AFgm.win_sub_sound W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WSKEL_WIN := (AFgm.WSKEL_WIN W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation windows_WIN := (AFgm.windows_WIN W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation frame_WIN := (AFgm.frame_WIN W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN_zone := (AFgm.WIN_zone W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN_off := (AFgm.WIN_off W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN_not_high := (AFgm.WIN_not_high W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation all_disjoint_of_forall := (AFgm.all_disjoint_of_forall W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation kept_of_frame := (AFgm.kept_of_frame W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation kept_of_frame_hi := (AFgm.kept_of_frame_hi W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation kept_of_vframe := (AFgm.kept_of_vframe W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation p_ivs := (AFgm.p_ivs W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation SKEL_TAIL := AFgm.SKEL_TAIL.
Local Notation DZONE := (AFgm.DZONE ly).
Local Notation IZONE := AFgm.IZONE.
Local Notation tail_facts := (AFgm.tail_facts W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation MEQ := (AFgm.MEQ ly regs0 mem0 p).
Local Notation IAL_POST := (AFgm.IAL_POST W).
Local Notation MEQI := (AFgm.MEQI W ly regs0 mem0 p).
Local Notation MEQI_frame := (AFgm.MEQI_frame W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation WIN2 := (AFgm.WIN2 ly regs0 p).
Local Notation WIN2_WIN := (AFgm.WIN2_WIN ly regs0 p).
Local Notation WSKEL2 := AFgm.WSKEL2.
Local Notation WSKEL2_WIN2 := (AFgm.WSKEL2_WIN2 W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation windows_WIN2 := (AFgm.windows_WIN2 W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation OBJQ := (AFgm.OBJQ regs0).
Local Notation MEQJ := (AFgm.MEQJ W ly regs0 mem0 p).
Local Notation MEQJ_frame := (AFgm.MEQJ_frame W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation memset_stretch := (AFgm.memset_stretch W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_img := (AFgm.notWIN_img W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_shb := (AFgm.notWIN_shb W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_Thead := (AFgm.notWIN_Thead W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_C := (AFgm.notWIN_C W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_NB := (AFgm.notWIN_NB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation notWIN_SB := (AFgm.notWIN_SB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Hp10 Htp Hra Hra4096 Hsp Hsp_al Hch Hp IMG Hp_al Hnn Hhb1 Hhb1m Hp_static Hp_pres Hsh_pres Hqb Hjunk HIAL IA1 U1 SEED].
Local Notation off_T := (AFgm.off_T W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_C := (AFgm.off_C W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_NB := (AFgm.off_NB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_SB := (AFgm.off_SB W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_P := (AFgm.off_P W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation off_P8 := (AFgm.off_P8 W ly regs0 mem0 ch p nn hb1 q j1 j2 j3 ii FH).
Local Notation pres_off_of_frame := (AFgm.pres_off_of_frame W).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize; tac | apply off_C; tac | apply off_P8; tac | apply off_P; tac
| apply off_NB; unfold kNodesBlockSize; tac | apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Notation at_D1 := (AFgd.at_D1 W ly regs0 mem0 md0 ch p nn hb1 q j1 j2 j3).
Ltac show_regs HS := lazymatch type of HS with st_ok _ _ ?ss _ => let r := eval vm_compute in (ss_pc ss, ss_regs ss) in idtac r end.
Ltac show_skel HS := lazymatch type of HS with st_ok _ _ ?ss _ => let r := eval vm_compute in (combine (seq 0 (length (ss_mem ss))) (skeleton (ss_mem ss))) in idtac r end.
Ltac show_reg HS i := lazymatch type of HS with st_ok _ _ ?ss _ => let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in idtac r end.
Definition EQ4a (m4 m : word -> option byte) : Prop := forall x : word, ~ WIN2 (bv_unsigned x) -> m x = m4 x.
Definition EQ4 (m4 m : word -> option byte) : Prop :=
forall x : word, ~ WIN2 (bv_unsigned x) -> ~ (SPv <= bv_unsigned x < SPv + CNT8v) -> m x = m4 x.
Lemma EQ4a_frame : forall (E : env) rs (m4 m m' : word -> option byte),
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL2 || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> EQ4a m4 m -> EQ4a m4 m'.
Proof. intros E rs m4 m m' HE Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN2 E rs _ HE Hb Hw). Qed.
Ltac eq4a_acc HE :=
match goal with
| M : EQ4a ?m4 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "EQ" in
pose proof (EQ4a_frame E rs m4 ma mb HE ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Lemma EQ4_frame : forall (E : env) rs (m4 m m' : word -> option byte),
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL2 || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> EQ4 m4 m -> EQ4 m4 m'.
Proof. intros E rs m4 m m' HE Hb HF M x Hx Hs. rewrite <- (M x Hx Hs). apply HF. intros Hw. apply Hx. exact (windows_WIN2 E rs _ HE Hb Hw). Qed.
Ltac eq4_acc HE :=
match goal with
| M : EQ4 ?m4 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "EQ" in
pose proof (EQ4_frame E rs m4 ma mb HE ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Definition after_D1 (msD : machine_state) (E3 : env) (regs4 : bvmap 5 word) (mem4 : word -> option byte) : Prop :=
msD = mkst (ms_regs msD) (w64 0x724b0) (ms_mem msD) (seg_rom tfibsegs) /\
(forall k, (k < aHAVf)%nat -> ew E3 k = ew E0 k) /\
st_ok tfibsegs E3 SS_B (restrict (w_H W) msD) /\
regs_preserved (ms_regs msD) regs4 /\
(forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) -> ~ DZONE (bv_unsigned x) -> mem4 x = ms_mem msD x) /\
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
- intros x Hx Hs. rewrite <- (M x Hx Hs). apply HF. intros Hw. apply Hx. exact (windows_WIN2 E rs _ HE Hb Hw).
- intros x Hs. rewrite <- (S x Hs). apply HF. intros Hw. pose proof (WIN_zone _ (WIN2_WIN _ (windows_WIN2 E rs _ HE Hb Hw))) as (_ & Hh & _).
pose proof derived_ranges as DR. apply Hh. clear - Hs DR. numconst. zlia.
Qed.
Ltac eqs_acc HE :=
match goal with
| M : EQS ?m4 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "EQ" in
pose proof (EQS_frame E rs m4 ma mb HE ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Lemma denot_by_zev : forall (E : env) t v, svpure t = true -> 0 <= v < 2 ^ 64 -> zev (rho_of E) t = v -> sv_denot E t = Z_to_bv 64 v.
Proof.
intros E t v Hp Hv Hz. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (sv_denot E t)) with (U E t).
rewrite (U_zev E t Hp), Hz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). symmetry. apply Z.mod_small. exact Hv.
Qed.
Definition at_ENQ (mem4 : word -> option byte) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists (ms : machine_state) mat (E5 : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
ms = mkst (ms_regs ms) (w64 0x357d0) (ms_mem ms) (seg_rom tfibsegs) /\
(forall k, (k < aHAVf)%nat -> ew E5 k = ew E0 k) /\
st_ok tfibsegs E5 SS_E (restrict (w_H W) ms) /\
EQS mem4 (ms_mem ms) /\ (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |].
Lemma segCm1 : forall msD E3 regs4 mem4 mat4, after_D1 msD E3 regs4 mem4 ->
SRr tfibsegs W (mkCfg (mkst regs4 (w64 0x35500) mem4 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat4 md0)) (at_ENQ mem4).
Proof.
intros msD E3 regs4 mem4 mat4 (HshD & HEn3 & HS & HP4 & Hfr4 & Hpr4 & MEQD0 & PRESD).
open_FH. pose proof Hwx_tfa as Hwx. destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB. pose proof derived_ranges as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
set (XD := fun a : Z => (sp0 - 2176 - DEP_STK <= a < sp0 - 2176) \/ DZONE a).
assert (Hfr' : forall x : word, ~ XD (bv_unsigned x) -> mem4 x = ms_mem msD x).
{ intros x Hx. subst XD. apply Hfr4; cbn beta in Hx; tauto. }
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?robj :: ?rscr :: ?rest =>
pose proof (st_ok_after_call tfibsegs 86 E3 ss ms0 regs4 (mrestrict (w_H W) mem4) (robj :: trim_lo rscr (-2176) :: rest) 0x35500 HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_trim_lo | apply submem_refl])
ltac:(vm_compute; reflexivity) HP4) as HS1;
let rsv := eval vm_compute in (robj :: trim_lo rscr (-2176) :: rest) in
change (robj :: trim_lo rscr (-2176) :: rest) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 86 0x35500) in
change (ss_after_call ss rsv 86 0x35500) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?r2 :: ?r3 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E3 (mrestrict (w_H W) (ms_mem msD)) (mrestrict (w_H W) mem4)) (r0 :: r1 :: r2 :: r3 :: tail));
[ pose proof LYD as (_ & _ & (_ & _ & NBSTK) & (_ & SBSTK) & _); unfold zdisjoint in NBSTK, SBSTK; cbn [fst snd] in NBSTK, SBSTK;
constructor; [|constructor; [|constructor; [|constructor]]];
[ eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn3 2%nat ltac:(cbv; zlia)), E2; subst XD; unfold AFgm.DZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo Hhi LB NBSTK SBSTK; numconst; zlia
| eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn3 2%nat ltac:(cbv; zlia)), E2; subst XD; unfold AFgm.DZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo Hhi LB NBSTK SBSTK; numconst; zlia
| eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn3 37%nat ltac:(cbv; zlia)), EaIM; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia);
subst XD; unfold AFgm.DZONE; intros a Ha; cbn beta; clear - Ha DR Usp Hlo LB; numconst; zlia
| eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn3 2%nat ltac:(cbv; zlia)), E2; subst XD; unfold AFgm.DZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo Hhi LB NBSTK SBSTK; numconst; zlia
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts E3 r HEn3 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); intros a Ha; subst XD; unfold AFgm.DZONE; cbn beta; clear - Ha Y1 Y2 Y3 Y4 Y6; numconst; zlia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES4 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem4 a) by (intros a Ha; apply Hpr4, PRESD, Ha).
set (En4 := havoc E3 86 (map (getr regs4) CLOB)) in HS1.
assert (HEn4 : forall k, (k < aHAVf)%nat -> ew En4 k = ew E0 k) by (intros k Hk; subst En4; unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; apply HEn3; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- 2176) (- ASTACK) (- 2176) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2;
split; [clear - Usp Hlo LB; numconst; zlia|]; split; [clear - Usp Hlo LB; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Usp Hlo LB Ho; numconst; zlia) | apply PRES4; clear - Ho; numconst; zlia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|[<-|[<-|[<-|Hr']]]];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold ASTACK; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold ASTACK; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn4 37%nat ltac:(cbv; zlia)), (HEn4 2%nat ltac:(cbv; zlia)), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR Usp Hlo LB; numconst; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold ASTACK; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En4 r' HEn4 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (EQ0 : EQ4a mem4 mem4) by (intros x _; reflexivity).
srr_run_to_sh tfibtbl_rtF_ok HS 0x35620. eq4a_acc HEn4.
assert (R38 : rho_of En4 38%nat = HWv) by (unfold rho_of; rewrite (HEn4 38%nat ltac:(cbv; zlia)), EaHW; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (T1V : zev (rho_of En4) T1term = 3 + 256 * hb1) by (apply T1_val; [exact Hhb1 | rewrite R38; reflexivity]).
assert (R39 : rho_of En4 39%nat = nn) by (unfold rho_of; rewrite (HEn4 39%nat ltac:(cbv; zlia)), EaN; unfold w64; apply unsigned_lit_small; clear - Hnn; zlia).
set (SZt := SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SRL T1term (SLit 16)) (SLit 32)) (SOff 39%nat 0)).
assert (SIZEV : zev (rho_of En4) SZt = nn).
{ subst SZt. cbn [zev]. rewrite T1V, R39. unfold zalu_raw.
change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftr_div_pow2 by zlia. rewrite (Z.div_small (3 + 256 * hb1) (2 ^ 16)) by (clear - Hhb1; zlia).
change (zcanon (Z.shiftl (zcanon 0) 32)) with 0. rewrite Z.add_0_r, (zcanon_id nn) by (clear - Hnn; unfold M64; zlia). rewrite Z.lor_0_l.
apply zcanon_id. clear - Hnn; unfold M64; zlia. }
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 39%nat 0)) in HS; [| intros X; discriminate
| pin_prep; fold T1term; fold SZt; rewrite SIZEV; cbn [zev]; rewrite R39, Z.add_0_r; apply zcanon_id; clear - Hnn; unfold M64; zlia].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4.
srr_branch_sh tfibtbl_rtF_ok HS.
{
assert (ZLO : p + N8v <= kLowShadowBeg).
{ rewrite branch_geu_U in Hc. apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc. revert Hc.
rewrite !U_SOff, (HEn4 40%nat ltac:(cbv; zlia)), EaSHB, (HEn4 10%nat ltac:(cbv; zlia)), E10, Hp10. unfold w64.
rewrite !unsigned_lit_small by (clear - DR; numconst; zlia). rewrite !zcanon_id by (clear - DR; unfold M64; numconst; zlia).
pose proof Hp as (_ & _ & ZC). pose proof N8_ge as [N8a _]. clear - ZC N8a. intros Hc. unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. zlia. }
clear Hc. srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4.
pose proof derived_align as (_ & _ & N8al & _).
assert (N8V : zev (rho_of En4) (SAlu ALU_AND (SAlu ALU_ADD SZt (SLit 7)) (SLit (-8))) = N8v).
{ cbn [zev]. rewrite SIZEV. unfold zalu_raw. rewrite (zcanon_id 7) by (unfold M64; zlia). rewrite (zcanon_id (nn + 7)) by (clear - Hnn; unfold M64; zlia).
change (zcanon (-8)) with (2 ^ 64 - 8). rewrite land_m8_64 by (clear - Hnn; zlia). unfold AFgm.N8v.
pose proof (Z.div_mod (nn + 7) 8 ltac:(zlia)). pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(zlia)). rewrite zcanon_id; [clear - Hnn H H0; zlia | clear - Hnn H H0; unfold M64; zlia]. }
assert (R42 : rho_of En4 42%nat = N8v) by (unfold rho_of; rewrite (HEn4 42%nat ltac:(cbv; zlia)), EaN8; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
apply (st_ok_pin_regU _ _ _ 11%bv (SOff 42%nat 0)) in HS; [| intros X; discriminate
| pin_prep; fold T1term; fold SZt; etransitivity; [|symmetry; exact N8V]; cbn [zev]; rewrite R42, Z.add_0_r; apply zcanon_id; clear - DR; unfold M64; zlia].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 15%bv (SLit 0)) in HS; [| intros X; discriminate
| pin_prep; fold T1term; fold SZt;
change (zev (rho_of En4) (SLit 0) = zcanon (Z.land (zev (rho_of En4) (SAlu ALU_AND (SAlu ALU_ADD SZt (SLit 7)) (SLit (-8)))) (zev (rho_of En4) (SLit 7))));
rewrite N8V; cbn [zev]; rewrite (zcanon_id 7) by (unfold M64; zlia); rewrite land_7_mod by (clear - DR; zlia); rewrite N8al; reflexivity].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4.
srr_branch_sh tfibtbl_rtF_ok HS.
2:{ exfalso. rewrite branch_geu_U in Hc. apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. revert Hc.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of.
rewrite ?(HEn4 40%nat ltac:(cbv; zlia)), ?(HEn4 10%nat ltac:(cbv; zlia)), ?(HEn4 42%nat ltac:(cbv; zlia)), ?EaSHB, ?E10, ?Hp10, ?EaN8. unfold w64. rewrite !unsigned_lit_small by (clear - DR; numconst; zlia).
clear - ZLO DR. numconst. zcanon_simp. zlia. }
clear Hc. srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4.
pose proof derived_align as (_ & P8 & _).
assert (R10 : rho_of En4 10%nat = p) by (unfold rho_of; rewrite (HEn4 10%nat ltac:(cbv; zlia)), E10, Hp10; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R40 : rho_of En4 40%nat = SHADOW_OFF) by (unfold rho_of; rewrite (HEn4 40%nat ltac:(cbv; zlia)), EaSHB; unfold w64; apply unsigned_lit_small; numconst; zlia).
assert (R41 : rho_of En4 41%nat = SPv) by (unfold rho_of; rewrite (HEn4 41%nat ltac:(cbv; zlia)), EaSP; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R43 : rho_of En4 43%nat = CNT8v) by (unfold rho_of; rewrite (HEn4 43%nat ltac:(cbv; zlia)), EaCNT8; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (Ep : p = 8 * (p / 8)) by (clear - DR; zlia).
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 41%nat 0)) in HS; [| intros X; discriminate
| pin_prep; cbn [zev]; unfold zalu_raw; rewrite R10, R40, R41, !Z.add_0_r; change (Z.land (zcanon 3) 63) with 3;
rewrite (zcanon_id p) by (clear - DR; numconst; unfold M64; zlia); rewrite Z.shiftr_div_pow2 by zlia; change (2 ^ 3) with 8;
unfold AFgm.SPv; numconst; zcanon_simp; clear - DR; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 43%nat 0)) in HS; [| intros X; discriminate
| pin_prep; cbn [zev]; unfold zalu_raw; rewrite R10, R42, R43, !Z.add_0_r; change (Z.land (zcanon 3) 63) with 3;
rewrite (zcanon_id p) by (clear - DR; numconst; unfold M64; zlia); rewrite (zcanon_id (p + -8)) by (clear - DR; numconst; unfold M64; zlia);
rewrite (zcanon_id N8v) by (clear - DR; numconst; unfold M64; zlia); rewrite (zcanon_id (p + -8 + N8v)) by (clear - DR; numconst; unfold M64; zlia);
rewrite !Z.shiftr_div_pow2 by zlia; change (2 ^ 3) with 8; rewrite (zcanon_id 1) by (unfold M64; zlia);
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DR))))))))) as EN8;
numconst; zcanon_simp; clear - DR Ep EN8; nia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msM end.
match goal with M : EQ4a mem4 (ms_mem msM) |- _ => rename M into EQM end.
assert (SHPRES : forall a, SPv <= a < SPv + CNT8v -> apresent (w_H W) (ms_mem msM) a).
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha DR; numconst; zlia).
assert (NW : ~ WIN2 a) by (intros Hw; destruct (WIN_zone a (WIN2_WIN a Hw)) as (_ & Hnb & _); apply Hnb; clear - Ha DR; numconst; zlia).
apply (apresent_same (w_H W) mem4). { apply EQM. rewrite unsigned_lit_small by exact Ra. exact NW. }
apply Hpr4. apply (apresent_same (w_H W) mem0).
{ apply (proj1 MEQD0); rewrite unsigned_lit_small by exact Ra; [intros Hw; destruct (WIN_zone a Hw) as (_ & Hnb & _); apply Hnb; clear - Ha DR; numconst; zlia|].
unfold AFgm.IZONE. clear - Ha DR; numconst; zlia. }
apply Hsh_pres. exact Ha. }
rreg HS (11%bv : bv 5) RA1m.
eapply (memset_stretch 102 En4 _ _ _ SPv CNT8v 0x357ac);
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| rreg HS (10%bv : bv 5) R; rewrite R, (HEn4 41%nat ltac:(cbv; zlia)), EaSP; reflexivity
| rreg HS (12%bv : bv 5) R; rewrite R, (HEn4 43%nat ltac:(cbv; zlia)), EaCNT8; reflexivity
| rreg HS (1%bv : bv 5) R; rewrite R; reflexivity
| clear - DR; zlia | clear - DR; numconst; zlia | clear - DR; numconst; zlia | reflexivity | zlia
| exact SHPRES
| intros r Hr | intros r a Hr | intros r a Hr | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|Hr]]]]];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn4 37%nat ltac:(cbv; zlia)), EaIM; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; numconst; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr by (vm_compute; reflexivity) end;
pose proof (tail_facts En4 r HEn4 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7); clear - DR Y1 Y2 Y3 Y4 Y7; numconst; zlia ].
intros regs5 mem5 mat5 HS5 H10c Hfr5 Hpr5 Hfill. clear HS. rename HS5 into HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En5 := E) in HS; let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (HEn5 : forall k, (k < aHAVf)%nat -> ew En5 k = ew E0 k) by (intros k Hk; subst En5; unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; apply HEn4; exact Hk).
assert (EQ5 : EQS mem4 mem5).
{ split; [intros x Hx Hs; rewrite (Hfr5 x Hs); exact (EQM x Hx)|]. intros x Hs. rewrite (Hfill x Hs), RA1m. reflexivity. }
clear EQM.
apply (st_ok_forget_reg En5 _ _ 5%bv 108) in HS; [| intros X; discriminate | vm_compute; reflexivity].
apply (st_ok_forget_reg _ _ _ 7%bv 109) in HS; [| intros X; discriminate | vm_compute; reflexivity].
apply (st_ok_forget_reg _ _ _ 17%bv 110) in HS; [| intros X; discriminate | vm_compute; reflexivity].
apply (st_ok_forget_reg _ _ _ 28%bv 111) in HS; [| intros X; discriminate | vm_compute; reflexivity].
apply (st_ok_facts_leb tfibsegs _ _ _ AFfw.F_R) in HS; [| vm_compute; reflexivity].
cbn [ms_regs restrict] in HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En6 := E) in HS; change ss with AFfw.SS_R in HS end.
assert (HEn6 : forall k, (k < aHAVf)%nat -> ew En6 k = ew E0 k) by (intros k Hk; subst En6; unfold aHAVf in Hk; rewrite !ew_havoc_old by zlia; apply HEn5; exact Hk).
clearbody En6. clear En5 HEn5.
srr_run_to_sh tfibtbl_rtF_ok HS 0x357d0. eqs_acc HEn6.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msE end.
match goal with M : EQS mem4 (ms_mem msE) |- _ => rename M into EQE end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En6 _ _ HS eq_refl) as HshE; cbn [ss_pc] in HshE.
apply SRr_ret. split; [reflexivity|].
eexists msE, _, En6. split; [reflexivity|]. split; [exact HshE|]. split; [exact HEn6|]. split; [exact HS|]. split; [exact EQE|].
assert (BV2 : bv_unsigned (ew En6 2) = sp0) by (rewrite (HEn6 2%nat ltac:(cbv; zlia)), E2; reflexivity).
intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2176)); [|destruct (Z_lt_le_dec a (sp0 - 2128)); [|destruct (Z_lt_le_dec a (sp0 - 64))]].
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; numconst; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l l0; numconst; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
- apply (apresent_same (w_H W) mem4); [|apply PRES4; exact Ha]. apply (proj1 EQE); rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; zlia).
+ intros Hw. unfold AFgm.WIN2, AFgm.WINT, AFgm.WINB in Hw. pose proof stack_ivs as (IT & _ & _ & _ & _ & IPP).
pose proof LYD as ((_ & _ & _ & _ & PSTK) & _). unfold zdisjoint in PSTK. cbn [fst snd] in PSTK.
clear - Hw Ha l0 l1 DR LB Hlo Hhi IT IPP PSTK. numconst. unfold sp0 in *. zlia.
+ clear - Ha l0 DR Hlo LB. numconst. zlia.
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 4 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l1; numconst; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
}
assert (ZHI : kHighMemBeg <= p - 16).
{ rewrite branch_geu_U in Hc. apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. revert Hc.
rewrite !U_SOff, (HEn4 40%nat ltac:(cbv; zlia)), EaSHB, (HEn4 10%nat ltac:(cbv; zlia)), E10, Hp10. unfold w64.
rewrite !unsigned_lit_small by (clear - DR; numconst; zlia). rewrite !zcanon_id by (clear - DR; unfold M64; numconst; zlia).
pose proof Hp as (_ & _ & ZC). pose proof N8_ge as [N8a _]. clear - ZC N8a. intros Hc. unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. zlia. }
clear Hc.
apply (st_ok_add_atom tfibsegs En4 _ _ 10%nat (mkAF (kHighMemBeg + 16) (CEIL_MAX - 16) 4)) in HS.
2:{ split; [|split; [|cbn [af_al2]; zlia]]; cbn [af_lo af_hi af_al2]; rewrite (HEn4 10%nat ltac:(cbv; zlia)), E10, Hp10; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia).
- pose proof Hp as (_ & ZB & _). pose proof derived_align as (P16 & _). clear - ZHI ZB DR P16. numconst. zlia.
- pose proof derived_align as (P16 & _). change (2 ^ 4) with 16. exact P16. }
lazymatch type of HS with st_ok _ _ ?ss _ => let ss2 := eval vm_compute in ss in change ss with ss2 in HS end.
srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4.
pose proof derived_align as (_ & _ & N8al & _).
assert (N8V : zev (rho_of En4) (SAlu ALU_AND (SAlu ALU_ADD SZt (SLit 7)) (SLit (-8))) = N8v).
{ cbn [zev]. rewrite SIZEV. unfold zalu_raw. rewrite (zcanon_id 7) by (unfold M64; zlia). rewrite (zcanon_id (nn + 7)) by (clear - Hnn; unfold M64; zlia).
change (zcanon (-8)) with (2 ^ 64 - 8). rewrite land_m8_64 by (clear - Hnn; zlia). unfold AFgm.N8v.
pose proof (Z.div_mod (nn + 7) 8 ltac:(zlia)). pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(zlia)). rewrite zcanon_id; [clear - Hnn H H0; zlia | clear - Hnn H H0; unfold M64; zlia]. }
assert (R42 : rho_of En4 42%nat = N8v) by (unfold rho_of; rewrite (HEn4 42%nat ltac:(cbv; zlia)), EaN8; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
apply (st_ok_pin_regU _ _ _ 11%bv (SOff 42%nat 0)) in HS; [| intros X; discriminate
| pin_prep; fold T1term; fold SZt; etransitivity; [|symmetry; exact N8V]; cbn [zev]; rewrite R42, Z.add_0_r; apply zcanon_id; clear - DR; unfold M64; zlia].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 15%bv (SLit 0)) in HS; [| intros X; discriminate
| pin_prep; fold T1term; fold SZt;
change (zev (rho_of En4) (SLit 0) = zcanon (Z.land (zev (rho_of En4) (SAlu ALU_AND (SAlu ALU_ADD SZt (SLit 7)) (SLit (-8)))) (zev (rho_of En4) (SLit 7))));
rewrite N8V; cbn [zev]; rewrite (zcanon_id 7) by (unfold M64; zlia); rewrite land_7_mod by (clear - DR; zlia); rewrite N8al; reflexivity].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4.
srr_branch_sh tfibtbl_rtF_ok HS.
{ exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc. revert Hc.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of.
rewrite ?(HEn4 10%nat ltac:(cbv; zlia)), ?(HEn4 42%nat ltac:(cbv; zlia)), ?E10, ?Hp10, ?EaN8. unfold w64. rewrite !unsigned_lit_small by (clear - DR; numconst; zlia).
pose proof Hp as (_ & ZB & _). clear - ZB DR. numconst. zcanon_simp. zlia. }
clear Hc. srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4.
pose proof derived_align as (_ & P8 & _).
assert (R10 : rho_of En4 10%nat = p) by (unfold rho_of; rewrite (HEn4 10%nat ltac:(cbv; zlia)), E10, Hp10; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R40 : rho_of En4 40%nat = SHADOW_OFF) by (unfold rho_of; rewrite (HEn4 40%nat ltac:(cbv; zlia)), EaSHB; unfold w64; apply unsigned_lit_small; numconst; zlia).
assert (R41 : rho_of En4 41%nat = SPv) by (unfold rho_of; rewrite (HEn4 41%nat ltac:(cbv; zlia)), EaSP; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R43 : rho_of En4 43%nat = CNT8v) by (unfold rho_of; rewrite (HEn4 43%nat ltac:(cbv; zlia)), EaCNT8; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (Ep : p = 8 * (p / 8)) by (clear - DR; zlia).
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 41%nat 0)) in HS; [| intros X; discriminate
| pin_prep; cbn [zev]; unfold zalu_raw; rewrite R10, R40, R41, !Z.add_0_r; change (Z.land (zcanon 3) 63) with 3;
rewrite (zcanon_id p) by (clear - DR; numconst; unfold M64; zlia); rewrite Z.shiftr_div_pow2 by zlia; change (2 ^ 3) with 8;
unfold AFgm.SPv; numconst; zcanon_simp; clear - DR; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 43%nat 0)) in HS; [| intros X; discriminate
| pin_prep; cbn [zev]; unfold zalu_raw; rewrite R10, R42, R43, !Z.add_0_r; change (Z.land (zcanon 3) 63) with 3;
rewrite (zcanon_id p) by (clear - DR; numconst; unfold M64; zlia); rewrite (zcanon_id (p + -8)) by (clear - DR; numconst; unfold M64; zlia);
rewrite (zcanon_id N8v) by (clear - DR; numconst; unfold M64; zlia); rewrite (zcanon_id (p + -8 + N8v)) by (clear - DR; numconst; unfold M64; zlia);
rewrite !Z.shiftr_div_pow2 by zlia; change (2 ^ 3) with 8; rewrite (zcanon_id 1) by (unfold M64; zlia);
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DR))))))))) as EN8;
numconst; zcanon_simp; clear - DR Ep EN8; nia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msM end.
match goal with M : EQ4a mem4 (ms_mem msM) |- _ => rename M into EQM end.
assert (SHPRES : forall a, SPv <= a < SPv + CNT8v -> apresent (w_H W) (ms_mem msM) a).
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha DR; numconst; zlia).
assert (NW : ~ WIN2 a) by (intros Hw; destruct (WIN_zone a (WIN2_WIN a Hw)) as (_ & Hnb & _); apply Hnb; clear - Ha DR; numconst; zlia).
apply (apresent_same (w_H W) mem4). { apply EQM. rewrite unsigned_lit_small by exact Ra. exact NW. }
apply Hpr4. apply (apresent_same (w_H W) mem0).
{ apply (proj1 MEQD0); rewrite unsigned_lit_small by exact Ra; [intros Hw; destruct (WIN_zone a Hw) as (_ & Hnb & _); apply Hnb; clear - Ha DR; numconst; zlia|].
unfold AFgm.IZONE. clear - Ha DR; numconst; zlia. }
apply Hsh_pres. exact Ha. }
rreg HS (11%bv : bv 5) RA1m.
eapply (memset_stretch 102 En4 _ _ _ SPv CNT8v 0x357ac);
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| rreg HS (10%bv : bv 5) R; rewrite R, (HEn4 41%nat ltac:(cbv; zlia)), EaSP; reflexivity
| rreg HS (12%bv : bv 5) R; rewrite R, (HEn4 43%nat ltac:(cbv; zlia)), EaCNT8; reflexivity
| rreg HS (1%bv : bv 5) R; rewrite R; reflexivity
| clear - DR; zlia | clear - DR; numconst; zlia | clear - DR; numconst; zlia | reflexivity | zlia
| exact SHPRES
| intros r Hr | intros r a Hr | intros r a Hr | ].
1-3: cbn [ss_mem] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|Hr]]]]];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn4 37%nat ltac:(cbv; zlia)), EaIM; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; numconst; zlia
| cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2; clear - DR Usp Hlo Hhi LB; numconst; zlia
| apply (in_map skel) in Hr;
lazymatch type of Hr with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr by (vm_compute; reflexivity) end;
pose proof (tail_facts En4 r HEn4 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7); clear - DR Y1 Y2 Y3 Y4 Y7; numconst; zlia ].
intros regs5 mem5 mat5 HS5 H10c Hfr5 Hpr5 Hfill. clear HS. rename HS5 into HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En5 := E) in HS; let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (HEn5 : forall k, (k < aHAVf)%nat -> ew En5 k = ew E0 k) by (intros k Hk; subst En5; unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; apply HEn4; exact Hk).
assert (EQ5 : EQS mem4 mem5).
{ split; [intros x Hx Hs; rewrite (Hfr5 x Hs); exact (EQM x Hx)|]. intros x Hs. rewrite (Hfill x Hs), RA1m. reflexivity. }
clear EQM.
apply (st_ok_forget_reg En5 _ _ 5%bv 108) in HS; [| intros X; discriminate | vm_compute; reflexivity].
apply (st_ok_forget_reg _ _ _ 7%bv 109) in HS; [| intros X; discriminate | vm_compute; reflexivity].
apply (st_ok_forget_reg _ _ _ 17%bv 110) in HS; [| intros X; discriminate | vm_compute; reflexivity].
apply (st_ok_forget_reg _ _ _ 28%bv 111) in HS; [| intros X; discriminate | vm_compute; reflexivity].
apply (st_ok_facts_leb tfibsegs _ _ _ AFfw.F_R) in HS; [| vm_compute; reflexivity].
cbn [ms_regs restrict] in HS.
lazymatch type of HS with st_ok _ ?E ?ss _ => set (En6 := E) in HS; change ss with AFfw.SS_R in HS end.
assert (HEn6 : forall k, (k < aHAVf)%nat -> ew En6 k = ew E0 k) by (intros k Hk; subst En6; unfold aHAVf in Hk; rewrite !ew_havoc_old by zlia; apply HEn5; exact Hk).
clearbody En6. clear En5 HEn5.
srr_run_to_sh tfibtbl_rtF_ok HS 0x357d0. eqs_acc HEn6.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msE end.
match goal with M : EQS mem4 (ms_mem msE) |- _ => rename M into EQE end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En6 _ _ HS eq_refl) as HshE; cbn [ss_pc] in HshE.
apply SRr_ret. split; [reflexivity|].
eexists msE, _, En6. split; [reflexivity|]. split; [exact HshE|]. split; [exact HEn6|]. split; [exact HS|]. split; [exact EQE|].
assert (BV2 : bv_unsigned (ew En6 2) = sp0) by (rewrite (HEn6 2%nat ltac:(cbv; zlia)), E2; reflexivity).
intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2176)); [|destruct (Z_lt_le_dec a (sp0 - 2128)); [|destruct (Z_lt_le_dec a (sp0 - 64))]].
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; numconst; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l l0; numconst; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
- apply (apresent_same (w_H W) mem4); [|apply PRES4; exact Ha]. apply (proj1 EQE); rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; zlia).
+ intros Hw. unfold AFgm.WIN2, AFgm.WINT, AFgm.WINB in Hw. pose proof stack_ivs as (IT & _ & _ & _ & _ & IPP).
pose proof LYD as ((_ & _ & _ & _ & PSTK) & _). unfold zdisjoint in PSTK. cbn [fst snd] in PSTK.
clear - Hw Ha l0 l1 DR LB Hlo Hhi IT IPP PSTK. numconst. unfold sp0 in *. zlia.
+ clear - Ha l0 DR Hlo LB. numconst. zlia.
- eapply (st_ok_window_apresent_off (w_H W) En6 _ _ 4 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l1; numconst; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
Qed.
End WK.
End b.
