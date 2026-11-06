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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF6m YF6b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAME, SHADOW_OFF, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_IAL_FLAG, TFX_TP, TFX_TSD in *.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variables (p nn hb1 : Z) (q : qcache) (lastb : batch) (j1 j2 j3 : Z).
Variable ii : bool.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53100 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii.
Local Notation tr := (YF6m.tr ly regs0 ch).
Local Notation LENv := (YF6m.LENv ly regs0 ch).
Local Notation IMv := (YF6m.IMv p).
Local Notation HWv := (YF6m.HWv hb1).
Local Notation SPv := (YF6m.SPv p).
Local Notation N8v := (YF6m.N8v nn).
Local Notation CNT8v := (YF6m.CNT8v nn).
Local Notation Bv := (YF6m.Bv ly lastb).
Local Notation BBv := (YF6m.BBv lastb).
Local Notation BCv := (YF6m.BCv lastb).
Local Notation SLOTv := (YF6m.SLOTv ly lastb).
Local Notation QSv := (YF6m.QSv q).
Local Notation QFv := (YF6m.QFv ly q).
Local Notation QBv := (YF6m.QBv q).
Local Notation XW := (YF6m.XW ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E0 := (YF6m.E0 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation Er := (YF6m.Er ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E2 := (YF6m.E2 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E1 := (YF6m.E1 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E8 := (YF6m.E8 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E10 := (YF6m.E10 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E4 := (YF6m.E4 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaT := (YF6m.EaT ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaC := (YF6m.EaC ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSB := (YF6m.EaSB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaTOP := (YF6m.EaTOP ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaLEN := (YF6m.EaLEN ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaIM := (YF6m.EaIM ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaHW := (YF6m.EaHW ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaN := (YF6m.EaN ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSHB := (YF6m.EaSHB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSP := (YF6m.EaSP ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaN8 := (YF6m.EaN8 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaCNT8 := (YF6m.EaCNT8 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaB := (YF6m.EaB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaBB := (YF6m.EaBB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaBC := (YF6m.EaBC ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSLOT := (YF6m.EaSLOT ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaQS := (YF6m.EaQS ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaQF := (YF6m.EaQF ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaQB := (YF6m.EaQB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaJ1 := (YF6m.EaJ1 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaJ2 := (YF6m.EaJ2 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaJ3 := (YF6m.EaJ3 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation AL := YF6m.AL.
Local Notation HB1MASK := (YF6m.HB1MASK hb1).
Local Notation PSTATIC := (YF6m.PSTATIC ly p nn).
Local Notation PBDISJ := (YF6m.PBDISJ ly p nn lastb).
Local Notation REG0 := YF6m.REG0.
Local Notation SS0 := YF6m.SS0.
Local Notation LYB := (YF6m.LYB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation LYD := (YF6m.LYD W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation iv_vs_stack := (YF6m.iv_vs_stack W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation N8_ge := (YF6m.N8_ge W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation stack_ivs := (YF6m.stack_ivs W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation derived_ranges := (YF6m.derived_ranges W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation derived_align := (YF6m.derived_align W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WINT := (YF6m.WINT ly).
Local Notation WINB := (YF6m.WINB ly p lastb).
Local Notation WIN := (YF6m.WIN ly regs0 p lastb).
Local Notation WSKEL := YF6m.WSKEL.
Local Notation win_sub := YF6m.win_sub.
Local Notation win_sub_sound := (YF6m.win_sub_sound W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WSKEL_WIN := (YF6m.WSKEL_WIN W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation windows_WIN := (YF6m.windows_WIN W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation frame_WIN := (YF6m.frame_WIN W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN_zone := (YF6m.WIN_zone W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN_off := (YF6m.WIN_off W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN_not_high := (YF6m.WIN_not_high W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation all_disjoint_of_forall := (YF6m.all_disjoint_of_forall W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation kept_of_frame := (YF6m.kept_of_frame W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation kept_of_frame_hi := (YF6m.kept_of_frame_hi W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation kept_of_vframe := (YF6m.kept_of_vframe W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation p_ivs := (YF6m.p_ivs W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation SKEL_TAIL := YF6m.SKEL_TAIL.
Local Notation DZONE := (YF6m.DZONE ly).
Local Notation IZONE := YF6m.IZONE.
Local Notation tail_facts := (YF6m.tail_facts W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation MEQ := (YF6m.MEQ ly regs0 mem0 p lastb).
Local Notation IAL_POST := (YF6m.IAL_POST W).
Local Notation MEQI := (YF6m.MEQI W ly regs0 mem0 p lastb).
Local Notation MEQI_frame := (YF6m.MEQI_frame W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN2 := (YF6m.WIN2 ly regs0 p lastb).
Local Notation WIN2_WIN := (YF6m.WIN2_WIN ly regs0 p lastb).
Local Notation WSKEL2 := YF6m.WSKEL2.
Local Notation WSKEL2_WIN2 := (YF6m.WSKEL2_WIN2 W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation windows_WIN2 := (YF6m.windows_WIN2 W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation OBJQ := (YF6m.OBJQ regs0).
Local Notation MEQJ := (YF6m.MEQJ W ly regs0 mem0 p lastb).
Local Notation MEQJ_frame := (YF6m.MEQJ_frame W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation memset_stretch := (YF6m.memset_stretch W ly regs0 mem0 md0 ch p nn hb1 q lastb j1 j2 j3 ii mat0 FH).
Local Notation notWIN_img := (YF6m.notWIN_img W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_shb := (YF6m.notWIN_shb W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_Thead := (YF6m.notWIN_Thead W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_C := (YF6m.notWIN_C W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_NB := (YF6m.notWIN_NB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_SB := (YF6m.notWIN_SB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Hp10 Htp Hra Hra4096 Hsp Hsp_al Hch Hp IMG Hp_al Hnn Hhb1 Hhb1m Hp_static Hp_pres Hsh_pres Hq Hlastb HB HB_al HBp HB_pres Hjunk HIAL IA1 U1 SEED].
Local Notation off_T := (YF6m.off_T W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_C := (YF6m.off_C W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_NB := (YF6m.off_NB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_SB := (YF6m.off_SB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_P := (YF6m.off_P W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_P8 := (YF6m.off_P8 W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation pres_off_of_frame := (YF6m.pres_off_of_frame W).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; unfold kThreadObjSize; tac | img_apply off_C; tac | img_apply off_P8; tac | img_apply off_P; tac
| img_apply off_NB; unfold kNodesBlockSize; tac | img_apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Ltac meq_acc HE :=
match goal with
| M : MEQI ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQI_frame E rs ma mb HE ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Ltac show_regs HS := lazymatch type of HS with st_ok _ _ ?ss _ => let r := img_ev (ss_pc ss, ss_regs ss) in idtac r end.
Ltac show_skel HS := lazymatch type of HS with st_ok _ _ ?ss _ => let r := img_ev (combine (seq 0 (length (ss_mem ss))) (skeleton (ss_mem ss))) in idtac r end.
Ltac show_reg HS i := lazymatch type of HS with st_ok _ _ ?ss _ => let r := img_ev (nth i (ss_mem ss) (YQ0b.mkRegion None 0 0 0 0 [])) in idtac r end.
Lemma shamt_p : forall (rho : nat -> Z), rho 10%nat = p ->
Z.land (zev rho (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10%nat 0) (SLit 3)) (SLit (-128))) mod 2 ^ 32) 31 = 0.
Proof.
open_FH. intros rho Hr. pose proof derived_ranges as DR. pose proof derived_align as (P16 & _). pose proof N8_ge as [N8a _].
cbn [zev zalu_raw]. rewrite Hr. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in DR.
rewrite (zcanon_id (p + 0)) by (img_try (unfold M64; img_lia)). img_change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by img_lia. img_change (2 ^ 3) with 8.
rewrite (zcanon_id ((p + 0) * 8)) by (img_try (unfold M64; img_lia)). img_change (zcanon (-128)) with (2 ^ 64 - 128).
replace ((p + 0) * 8 + (2 ^ 64 - 128)) with ((p * 8 - 128) + 1 * M64) by (img_try (unfold M64; img_lia)).
unfold zcanon. rewrite Z_mod_plus_full. rewrite (Z.mod_small _ M64) by (img_try (unfold M64; img_lia)).
img_change 31 with (Z.ones 5). rewrite Z.land_ones by img_lia.
rewrite (Z.mod_mod_divide _ (2 ^ 32) (2 ^ 5)) by (img_try (exists (2 ^ 27); img_refl)).
assert (Ep : p = 16 * (p / 16)) by (img_try (pose proof (Z.div_mod p 16 ltac:(img_lia)); unfold YF6m.AL in P16; img_lia)).
rewrite Ep. replace (16 * (p / 16) * 8 - 128) with ((4 * (p / 16) - 4) * 2 ^ 5) by img_lia. img_apply Z_mod_mult.
Qed.
Definition TRACEQ (m : word -> option byte) : Prop :=
forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) m) (sp0 - 2120 + 8 * Z.of_nat i) 8 (nth i tr 0).
Definition at_D1 (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists (ms : machine_state) mat (E3 : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
ms = mkst (ms_regs ms) (w64 (0x72fcc + D_2c4)) (ms_mem ms) (seg_rom tfxsegs) /\
(forall k, (k < aHAVf)%nat -> ew E3 k = ew E0 k) /\
st_ok tfxsegs E3 SS_B (restrict (w_H W) ms) /\
MEQI (ms_mem ms) /\ TRACEQ (ms_mem ms) /\ (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).
Ltac meq_accJ HE :=
match goal with
| M : MEQJ ?mr ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQJ_frame E rs mr ma mb HE ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Variable regsD : bvmap 5 word.
Hypothesis REGSD : regs_ok E0 REGS_DC regsD.
Hypothesis STKD : Forall (region_ok tfxsegs E0 m0) [R_OBJ; R_SCR; R_TOP].
Hypothesis HQ12 : 4096 <= bv_unsigned (getr regs0 12) <= 2 ^ 47.
Hypothesis Hii : ii = true.
Hypothesis PRES0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis TRQ0 : TRACEQ mem0.
Lemma SEED_DC : st_ok tfxsegs E0 SS_DC (restrict (w_H W) (mkst regsD (w64 (0x3244c + D_150)) mem0 (seg_rom tfxsegs))).
Proof.
open_FH. destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB. pose proof derived_ranges as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof SEED as HS0. rewrite restrict_mkst_fx in HS0. destruct HS0 as (_ & _ & _ & _ & _ & _ & _ & (_ & HR & HP) & (HFA & _ & _)).
cbn [ms_mem mkst ss_mem ss_facts] in HR, HP, HFA.
rewrite restrict_mkst_fx. unfold SS_DC, w64, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [img_refl|]). split; [img_try (img_exact REGSD)|]. split; [| img_try (split; [| split; img_exact I])].
-
split; [img_try ((img_case; vm_compute); img_refl)|].
assert (EL : REG0 = YQ0b.mkRegion (Some 2%nat) (- ASTACK) 0 (- ASTACK) 0 [] :: tl REG0) by (img_try ((img_case; vm_compute); img_refl)).
change (ss_mem SS0) with REG0 in HR, HP. rewrite EL in HR, HP.
assert (TD : forall r', In r' (tl REG0) -> let b := base_val E0 (YQ0b.r_base r') in
(b + YQ0b.r_hi r' <= sp0 - ASTACK \/ sp0 <= b + YQ0b.r_lo r') /\ (b + YQ0b.r_hi r' <= TFX_IAL_LO \/ TFX_IAL_HI <= b + YQ0b.r_lo r')).
{ intros r' Hr'. apply (in_map skel) in Hr'. img_change (map skel (tl REG0)) with (map skel (tl REG0)) in Hr'.
replace (map skel (tl REG0)) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)).
pose proof (tail_facts E0 r' ltac:(img_try (intros; img_refl)) Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7). cbv zeta. split; [img_try (img_exact Y1) | img_try (img_exact (proj1 Y5))]. }
assert (BIM : base_val E0 (Some 37%nat) = IMv).
{ cbn [base_val]. rewrite EaIM. unfold w64. img_apply unsigned_lit_small. clear - DR. numconst. img_lia. }
assert (B2 : base_val E0 (Some 2%nat) = sp0) by (img_try (cbn [base_val]; rewrite E2; img_refl)).
split.
+ inversion STKD as [|? ? K1 K']; (subst; cbv beta). inversion K' as [|? ? K2 K'']; (subst; cbv beta). inversion K'' as [|? ? K3 _]; (subst; cbv beta).
constructor; [img_try (img_exact K1)|]. constructor; [img_try (img_exact K2)|]. constructor; [|img_try (constructor; [img_exact K3 | img_exact (Forall_inv_tail HR)])].
unfold YQ0b.region_ok, R_IM. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite BIM.
split; [img_try (clear - DR; numconst; img_lia)|]. split; [img_try (clear - DR; numconst; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. intros i Hi. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len YQ0b.cbyte] in Hi |- *.
exists (Z_to_bv 8 0). split; [img_refl|]. destruct HIAL as (_ & _ & _ & IV5). img_apply IV5. clear - DR Hi. numconst. img_lia.
+ cbn [pairwise_disjoint] in HP. destruct HP as [_ HPt].
cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, R_OBJ, R_SCR, R_IM, R_TOP. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite !BIM, !B2.
assert (ST : forall lo hi, - ASTACK <= lo -> hi <= 0 -> all_disjoint E0 (YQ0b.mkRegion (Some 2%nat) lo hi 0 0 []) (tl REG0)).
{ intros lo hi Hl Hh. img_apply all_disjoint_of_forall. intros r' Hr'. destruct (TD r' Hr') as [Y1 _]. cbv zeta in Y1.
unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite B2. clear - Y1 Hl Hh. unfold ASTACK in *. img_lia. }
assert (ST' : forall lo hi wlo whi cs, - ASTACK <= lo -> hi <= 0 -> all_disjoint E0 (YQ0b.mkRegion (Some 2%nat) lo hi wlo whi cs) (tl REG0)).
{ intros lo hi wlo whi cs Hl Hh. specialize (ST lo hi Hl Hh). revert ST. generalize (tl REG0). clear. intros L. induction L as [|x L IH]; intros H; [img_try (img_exact I)|].
cbn [all_disjoint] in H |- *. destruct H as [Hd Ha]. split; [img_try (img_exact Hd) | img_try (img_exact (IH Ha))]. }
split; [img_try (split; [clear; unfold ASTACK; img_lia | split; [clear - DR Usp Hlo LB; numconst; img_lia | split; [clear; img_lia | img_apply ST'; [unfold ASTACK; img_lia | img_lia]]]])|].
split; [img_try (split; [clear - DR Usp Hlo LB; numconst; img_lia | split; [clear; unfold ASTACK; img_lia | img_apply ST'; [img_lia | unfold ASTACK; img_lia]]])|].
split; [img_try (split; [clear - DR Usp Hlo LB; numconst; img_lia|])|].
{ img_apply all_disjoint_of_forall. intros r' Hr'. destruct (TD r' Hr') as [_ Y5]. cbv zeta in Y5.
unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite BIM. clear - Y5 DR. numconst. img_lia. }
split; [img_try (img_apply ST'; [unfold ASTACK; img_lia | img_lia]) | img_try (img_exact HPt)].
-
unfold FFD. change (ss_facts SS0) with FF in HFA |- *.
destruct (f_atoms FF) as [|[k2 f2] [|[k10 f10] rest]] eqn:EA; cbv iota beta; [img_try (rewrite EA; img_exact HFA) | img_try (rewrite EA; img_exact HFA) |].
cbn [atoms_ok f_atoms] in HFA |- *. destruct HFA as (F2 & F10 & FR). split; [img_try (img_exact F2)|]. split; [img_try (img_exact F10)|]. split; [|img_try (img_exact FR)].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (Er 12 12%bv eq_refl). split; [img_try (img_exact HQ12)|]. split; [img_try (img_apply Z.mod_1_r) | img_lia].
Qed.
Lemma segB : SRr tfxsegs W (mkCfg (mkst regsD (w64 (0x3244c + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0)) at_D1.
Proof.
pose proof SEED_DC as HS.
open_FH. pose proof Hwx_tfa as Hwx. destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB. pose proof derived_ranges as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
set (mem2 := mem0) in *. pose proof TRQ0 as Ht2.
assert (PRES3 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a) by img_exact PRES0.
set (En2 := E0) in HS.
assert (HEn2 : forall k, (k < aHAVf)%nat -> ew En2 k = ew E0 k) by (img_try (intros k Hk; img_refl)).
assert (MEQ2 : MEQJ mem2 mem2).
{ split; [|img_try (intros x Hx; img_refl)]. split; [img_try (intros x Hx Hz; img_refl)|].
unfold YF6m.IAL_POST. (subst ii; cbv beta). destruct HIAL as (I1 & I2 & (I3 & I4) & I5). repeat split; assumption. }
srr_run_sh tfxtbl_rrF_ok HS. meq_accJ HEn2.
match goal with M : MEQJ _ _ |- _ => rename M into MQ end.
lazymatch type of HS with st_ok _ ?E _ _ => set (En3 := E) in HS end.
assert (HEn3 : forall k, (k < aHAVf)%nat -> ew En3 k = ew E0 k) by (img_try (intros k Hk; (subst En3; cbv beta); img_exact (HEn2 k Hk))).
assert (R10 : rho_of En3 10%nat = p) by (img_try (unfold rho_of; rewrite (HEn3 10%nat ltac:((img_case; cbv); img_lia)), E10, Hp10; unfold w64; img_apply unsigned_lit_small; clear - DR; numconst; img_lia)).
assert (R38 : rho_of En3 38%nat = HWv) by (img_try (unfold rho_of; rewrite (HEn3 38%nat ltac:((img_case; cbv); img_lia)), EaHW; unfold w64; img_apply unsigned_lit_small; clear - DR; img_lia)).
assert (PINW : forall (c : Z) (r : bv 5), U En3 (SLit c) = U En3 (SLit c) ->
zcanon c = bv_wrap 64 (bv_swrap 32 (Z.shiftl (zcanon c mod 2 ^ 32) 0)) ->
U En3 (SLit c) = U En3 (SAluw ALU_SLL (SLit c) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 3)) (SLit (-128))))).
{ intros c r _ Hc. img_apply U_eq_by_zev; [img_refl | img_refl |].
cbn [zev]. fold (zev (rho_of En3) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 3)) (SLit (-128)))).
unfold zalu_raw. rewrite (shamt_p (rho_of En3) R10). img_exact Hc. }
apply (st_ok_pin_regU _ _ _ 15%bv (SLit 255)) in HS; [| img_try (intros X; discriminate) | img_try (img_apply (PINW 255 15%bv eq_refl); (img_case; vm_compute); img_refl)].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 14%bv (SLit 2)) in HS; [| img_try (intros X; discriminate) | img_try (img_apply (PINW 2 14%bv eq_refl); (img_case; vm_compute); img_refl)].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 16%bv (SLit 3)) in HS; [| img_try (intros X; discriminate) | img_try (img_apply (PINW 3 16%bv eq_refl); (img_case; vm_compute); img_refl)].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
pose proof derived_align as (_ & _ & _ & _ & HW256 & HWb1 & _).
apply (st_ok_pin_regU _ _ _ 17%bv (SLit 2)) in HS. 2:{ intros X; discriminate. }
2:{ lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end.
img_apply U_eq_by_zev; [img_refl | img_refl |]. cbn [zev].
fold (zev (rho_of En3) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 3)) (SLit (-128)))). unfold zalu_raw. rewrite (shamt_p (rho_of En3) R10), R38.
img_change (bv_wrap 64 (bv_swrap 32 (Z.shiftl (zcanon 255 mod 2 ^ 32) 0))) with (Z.ones 8).
rewrite (zcanon_id (HWv + 0)) by (img_try (clear - DR; unfold M64; img_lia)). rewrite Z.add_0_r, Z.land_ones by img_lia. img_change (2 ^ 8) with 256. rewrite HW256. img_refl. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rrF_ok HS. meq_accJ HEn3.
assert (T1V : zev (rho_of En3) T1term = 3 + 256 * hb1) by (img_try (img_apply T1_val; [img_try (img_exact Hhb1) | img_try (rewrite R38; img_refl)])).
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 1)) in HS. 2:{ intros X; discriminate. }
2:{ lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end.
img_apply U_eq_by_zev; [img_refl | img_refl |]. fold T1term. cbn [zev]. rewrite T1V. unfold zalu_raw.
img_change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftr_div_pow2 by img_lia. img_change (2 ^ 8) with 256.
rewrite (Z.mul_comm 256), Z_div_plus_full by img_lia. img_change (3 / 256) with 0. rewrite Z.add_0_l.
img_change (2 ^ Z.of_N 8) with 256. rewrite (zcanon_id hb1) by (img_try (unfold M64; img_lia)). rewrite (Z.mod_small hb1 256) by img_lia.
rewrite (zcanon_id hb1) by (img_try (unfold M64; img_lia)). img_change (zcanon 3) with (Z.ones 2). rewrite Z.land_ones by img_lia. img_change (2 ^ 2) with 4.
replace (hb1 mod 4) with 1; [img_refl|]. rewrite <- HWb1. unfold YF6m.HWv. rewrite (Z.mul_comm 256), Z_div_plus_full by img_lia. img_refl. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rrF_ok HS. meq_accJ HEn3.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 3)) in HS. 2:{ intros X; discriminate. }
2:{ lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end.
img_apply U_eq_by_zev; [img_refl | img_refl |]. fold T1term. cbn [zev]. rewrite T1V.
img_change (2 ^ Z.of_N 8) with 256. rewrite (Z.mul_comm 256), Z_mod_plus_full. img_refl. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfxtbl_rrF_ok HS (0x72fcc + D_2c4). meq_accJ HEn3.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msD end.
match goal with M : MEQJ mem2 (ms_mem msD) |- _ => rename M into MEQD end.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En3 _ _ HS eq_refl) as HshapeD; cbn [ss_pc] in HshapeD.
img_apply SRr_ret. split; [img_refl|]. exists msD, mat1, En3.
split; [img_refl|]. split; [img_try (img_exact HshapeD)|]. split; [img_try (img_exact HEn3)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact (proj1 MEQD))|].
split. { intros i Hi. eapply val_mem_frame; [|img_try (img_exact (Ht2 i Hi))]. intros k Hk. img_apply (proj2 MEQD).
pose proof (unwind_of_chain_length (0x53640 + D_2c4) ((sp0, bv_unsigned (getr regs0 1), bv_unsigned (getr regs0 8)) :: ch)) as LEN.
assert (HL : (i < 30)%nat).
{ revert Hi LEN. unfold YF6m.tr, call_trace, frame0_ok, spZ, raZ, s0Z. fold sp0. destruct (sp0 + 16 <? ly_top ly); cbn [length]; intros; img_lia. }
rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB Hk HL; numconst; img_lia)). clear - Hk HL; img_lia. }
intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2208)); [|img_try (destruct (Z_lt_le_dec a (sp0 - 64)))].
- eapply (st_ok_window_apresent_off (w_H W) En3 _ _ 1 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn3 2%nat ltac:((img_case; cbv); img_lia)), E2; clear - Ha l Usp Hlo LB; numconst; img_lia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; img_lia)) ].
-
destruct (PRES3 a Ha) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite <- Hb. img_apply (proj2 MEQD). rewrite unsigned_lit_small by (img_try (clear - Ha Usp Hlo LB; numconst; img_lia)). unfold IFRAME in *. img_lia.
- eapply (st_ok_window_apresent_off (w_H W) En3 _ _ 3 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn3 2%nat ltac:((img_case; cbv); img_lia)), E2; clear - Ha l0 Usp Hlo LB; numconst; img_lia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; img_lia)) ].
Qed.
End WK.
End d.
