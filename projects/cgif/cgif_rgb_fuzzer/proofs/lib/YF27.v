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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF2d YF1q YF25.
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
Local Notation tr := (YF2d.tr ly regs0 ch).
Local Notation LENv := (YF2d.LENv ly regs0 ch).
Local Notation IMv := (YF2d.IMv p).
Local Notation HWv := (YF2d.HWv hb1).
Local Notation SPv := (YF2d.SPv p).
Local Notation N8v := (YF2d.N8v nn).
Local Notation CNT8v := (YF2d.CNT8v nn).
Local Notation Bv := (YF2d.Bv ly lastb).
Local Notation BBv := (YF2d.BBv lastb).
Local Notation BCv := (YF2d.BCv lastb).
Local Notation SLOTv := (YF2d.SLOTv ly lastb).
Local Notation QSv := (YF2d.QSv q).
Local Notation QFv := (YF2d.QFv ly q).
Local Notation QBv := (YF2d.QBv q).
Local Notation XW := (YF2d.XW ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E0 := (YF2d.E0 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation Er := (YF2d.Er ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E2 := (YF2d.E2 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E1 := (YF2d.E1 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E8 := (YF2d.E8 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E10 := (YF2d.E10 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation E4 := (YF2d.E4 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaT := (YF2d.EaT ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaC := (YF2d.EaC ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSB := (YF2d.EaSB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaTOP := (YF2d.EaTOP ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaLEN := (YF2d.EaLEN ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaIM := (YF2d.EaIM ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaHW := (YF2d.EaHW ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaN := (YF2d.EaN ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSHB := (YF2d.EaSHB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSP := (YF2d.EaSP ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaN8 := (YF2d.EaN8 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaCNT8 := (YF2d.EaCNT8 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaB := (YF2d.EaB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaBB := (YF2d.EaBB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaBC := (YF2d.EaBC ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaSLOT := (YF2d.EaSLOT ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaQS := (YF2d.EaQS ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaQF := (YF2d.EaQF ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaQB := (YF2d.EaQB ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaJ1 := (YF2d.EaJ1 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaJ2 := (YF2d.EaJ2 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation EaJ3 := (YF2d.EaJ3 ly regs0 ch p nn hb1 q lastb j1 j2 j3).
Local Notation AL := YF2d.AL.
Local Notation HB1MASK := (YF2d.HB1MASK hb1).
Local Notation PSTATIC := (YF2d.PSTATIC ly p nn).
Local Notation PBDISJ := (YF2d.PBDISJ ly p nn lastb).
Local Notation REG0 := YF2d.REG0.
Local Notation SS0 := YF2d.SS0.
Local Notation LYB := (YF2d.LYB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation LYD := (YF2d.LYD W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation iv_vs_stack := (YF2d.iv_vs_stack W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation N8_ge := (YF2d.N8_ge W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation stack_ivs := (YF2d.stack_ivs W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation derived_ranges := (YF2d.derived_ranges W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation derived_align := (YF2d.derived_align W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WINT := (YF2d.WINT ly).
Local Notation WINB := (YF2d.WINB ly p lastb).
Local Notation WIN := (YF2d.WIN ly regs0 p lastb).
Local Notation WSKEL := YF2d.WSKEL.
Local Notation win_sub := YF2d.win_sub.
Local Notation win_sub_sound := (YF2d.win_sub_sound W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WSKEL_WIN := (YF2d.WSKEL_WIN W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation windows_WIN := (YF2d.windows_WIN W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation frame_WIN := (YF2d.frame_WIN W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN_zone := (YF2d.WIN_zone W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN_off := (YF2d.WIN_off W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN_not_high := (YF2d.WIN_not_high W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation all_disjoint_of_forall := (YF2d.all_disjoint_of_forall W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation kept_of_frame := (YF2d.kept_of_frame W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation kept_of_frame_hi := (YF2d.kept_of_frame_hi W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation kept_of_vframe := (YF2d.kept_of_vframe W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation p_ivs := (YF2d.p_ivs W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation SKEL_TAIL := YF2d.SKEL_TAIL.
Local Notation DZONE := (YF2d.DZONE ly).
Local Notation IZONE := YF2d.IZONE.
Local Notation tail_facts := (YF2d.tail_facts W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation MEQ := (YF2d.MEQ ly regs0 mem0 p lastb).
Local Notation IAL_POST := (YF2d.IAL_POST W).
Local Notation MEQI := (YF2d.MEQI W ly regs0 mem0 p lastb).
Local Notation MEQI_frame := (YF2d.MEQI_frame W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation WIN2 := (YF2d.WIN2 ly regs0 p lastb).
Local Notation WIN2_WIN := (YF2d.WIN2_WIN ly regs0 p lastb).
Local Notation WSKEL2 := YF2d.WSKEL2.
Local Notation WSKEL2_WIN2 := (YF2d.WSKEL2_WIN2 W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation windows_WIN2 := (YF2d.windows_WIN2 W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation OBJQ := (YF2d.OBJQ regs0).
Local Notation MEQJ := (YF2d.MEQJ W ly regs0 mem0 p lastb).
Local Notation MEQJ_frame := (YF2d.MEQJ_frame W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation memset_stretch := (YF2d.memset_stretch W ly regs0 mem0 md0 ch p nn hb1 q lastb j1 j2 j3 ii mat0 FH).
Local Notation notWIN_img := (YF2d.notWIN_img W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_shb := (YF2d.notWIN_shb W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_Thead := (YF2d.notWIN_Thead W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_C := (YF2d.notWIN_C W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_NB := (YF2d.notWIN_NB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation notWIN_SB := (YF2d.notWIN_SB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Hp10 Htp Hra Hra4096 Hsp Hsp_al Hch Hp IMG Hp_al Hnn Hhb1 Hhb1m Hp_static Hp_pres Hsh_pres Hq Hlastb HB HB_al HBp HB_pres Hjunk HIAL IA1 U1 SEED].
Local Notation off_T := (YF2d.off_T W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_C := (YF2d.off_C W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_NB := (YF2d.off_NB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_SB := (YF2d.off_SB W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_P := (YF2d.off_P W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation off_P8 := (YF2d.off_P8 W ly regs0 mem0 ch p nn hb1 q lastb j1 j2 j3 ii FH).
Local Notation pres_off_of_frame := (YF2d.pres_off_of_frame W).
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; unfold kThreadObjSize; tac | img_apply off_C; tac | img_apply off_P8; tac | img_apply off_P; tac
| img_apply off_NB; unfold kNodesBlockSize; tac | img_apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Local Notation at_U1 := (YF25.at_U1 W ly regs0 mem0 md0 ch p nn hb1 q lastb j1 j2 j3).
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
assert (Ep : p = 16 * (p / 16)) by (img_try (pose proof (Z.div_mod p 16 ltac:(img_lia)); unfold YF2d.AL in P16; img_lia)).
rewrite Ep. replace (16 * (p / 16) * 8 - 128) with ((4 * (p / 16) - 4) * 2 ^ 5) by img_lia. img_apply Z_mod_mult.
Qed.
Definition TRACEQ (m : word -> option byte) : Prop :=
forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) m) (sp0 - 2112 + 8 * Z.of_nat i) 8 (nth i tr 0).
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
Lemma segB : forall W' c', at_U1 W' c' -> SRr tfxsegs W' c' at_D1.
Proof.
intros W' c' (-> & msU & regs2 & mem2 & mat2 & En1 & -> & HEn1 & HS & HP2 & Hfr2 & Hpr2 & Ht1 & Ht2 & Ht3 & MEQU & PRES2).
open_FH. pose proof Hwx_tfa as Hwx. destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB. pose proof derived_ranges as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
rreg HS (2%bv : bv 5) Q2. rewrite (HEn1 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2 in Q2.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem2 x = ms_mem msU x).
{ intros x Hx. img_apply Hfr2; clear - Hx; unfold ASTACK, UNW_STK in *; img_lia. }
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := img_ev (ss_mem ss) in
lazymatch m with ?rim :: ?rscr :: ?rfr :: ?rest =>
pose proof (st_ok_after_call tfxsegs 70 En1 ss ms0 regs2 (mrestrict (w_H W) mem2) (rim :: trim_lo rfr (-64) :: rest) (0x532a0 + D_2c4) HS eq_refl
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (img_apply submem_keep; [img_try (img_apply subregion_refl)|]; img_apply submem_drop; img_apply submem_keep; [img_try (img_apply subregion_trim_lo) | img_try (img_apply submem_refl)]))
ltac:(img_try ((img_case; vm_compute); img_refl)) HP2) as HS1;
let rsv := img_ev (rim :: trim_lo rfr (-64) :: rest) in
img_change (rim :: trim_lo rfr (-64) :: rest) with rsv in HS1;
let ss2 := img_ev (ss_after_call ss rsv 70 (0x532a0 + D_2c4)) in
change (ss_after_call ss rsv 70 (0x532a0 + D_2c4)) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfxsegs En1 (mrestrict (w_H W) (ms_mem msU)) (mrestrict (w_H W) mem2)) (r0 :: r1 :: tail));
[ img_try (constructor; [|constructor];
[ eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
rewrite (HEn1 37%nat ltac:((img_case; cbv); img_lia)), EaIM; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; img_lia); intros a Ha; cbn beta; clear - Ha DR Hlo LB Usp; numconst; img_lia
| eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi];
rewrite (HEn1 2%nat ltac:((img_case; cbv); img_lia)), E2; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; img_lia
| img_apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by ((img_case; vm_compute); img_refl);
pose proof (tail_facts En1 r HEn1 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); intros a Ha; cbn beta; clear - Ha Y1 Y2 Y3 Y4; numconst; img_lia ])
| img_try (specialize (HS1 KEPT); clear KEPT) ]
end.
assert (OBJ0 : val_mem tfxsegs (mrestrict (w_H W) mem2) (sp0 - 2128) 8 (sp0 - 2112)).
{ eapply val_mem_frame; [img_try (intros k Hk; img_apply Hfr2; rewrite unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; img_lia); clear - Hk; numconst; img_lia)|].
memv HS 2%nat 2%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 2%nat ltac:((img_case; cbv); img_lia)), E2; unfold sp0; img_lia)
| img_try (cbn [sv_denot]; rewrite (HEn1 2%nat ltac:((img_case; cbv); img_lia)), E2; f_equal; unfold sp0; img_lia) | img_try (clear - Usp Hlo LB; numconst; img_lia)]. }
assert (OBJ1 : val_mem tfxsegs (mrestrict (w_H W) mem2) (sp0 - 2120) 8 LENv).
{ replace (YF2d.LENv ly regs0 ch) with (LENv + 2 ^ 32 * 0) by img_lia.
pose proof (unwind_of_chain_length (0x53244 + D_2c4) ((sp0, bv_unsigned (getr regs0 1), bv_unsigned (getr regs0 8)) :: ch)) as LEN.
assert (HL : 1 <= LENv <= 30).
{ unfold YF2d.LENv, YF2d.tr, call_trace, frame0_ok, spZ, raZ, s0Z. fold sp0. destruct (sp0 + 16 <? ly_top ly); cbn [length]; img_lia. }
img_apply val_mem_4_4; [img_lia | img_lia | |].
- eapply val_mem_addr; [img_try (img_exact Ht1) | img_lia].
- assert (Z8 : val_mem tfxsegs (mrestrict (w_H W) (ms_mem msU)) (sp0 - 2120) 8 0).
{ memv HS 2%nat 1%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite (HEn1 2%nat ltac:((img_case; cbv); img_lia)), E2; unfold sp0; img_lia) | img_refl | img_lia]. }
assert (Z4 : val_mem tfxsegs (mrestrict (w_H W) (ms_mem msU)) (sp0 - 2120 + 4) 4 0).
{ intros k Hk. replace (sp0 - 2120 + 4 + Z.of_nat k) with (sp0 - 2120 + Z.of_nat (4 + k)) by img_lia.
rewrite (Z8 (4 + k)%nat ltac:(img_lia)). rewrite !le_byte_zero. img_refl. }
eapply val_mem_frame; [img_try (intros k Hk; img_apply Hfr2; rewrite unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; img_lia); clear - Hk; numconst; img_lia)| img_try (img_exact Z4)]. }
assert (PRES3 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a) by (img_try (intros a Ha; apply Hpr2, PRES2, Ha)).
set (En2 := havoc En1 70 (map (getr regs2) CLOB)) in HS1.
assert (HEn2 : forall k, (k < aHAVf)%nat -> ew En2 k = ew E0 k) by (img_try (intros k Hk; (subst En2; cbv beta); unfold aHAVf in Hk; rewrite ew_havoc_old by img_lia; img_apply HEn1; img_exact Hk)).
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn2 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2; unfold IFRAME;
split; [img_try (clear - Usp Hlo LB; numconst; img_lia)|]; split; [img_try (clear - Usp Hlo LB; numconst; img_lia)|];
split; [img_try (intros o Ho; img_apply apresent_writable_off; [off_by ltac:(clear - Usp Hlo LB Ho; numconst; img_lia) | img_apply PRES3; clear - Ho; numconst; img_lia]) | img_try (constructor)]
| img_apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn2 37%nat ltac:(img_try ((img_case; cbv); img_lia))), (HEn2 2%nat ltac:(img_try ((img_case; cbv); img_lia))), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (img_try (clear - DR; numconst; img_lia)); clear - DR Usp Hlo LB; numconst; img_lia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold IFRAME; img_lia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_facts En2 r' HEn2 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn2 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; img_lia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 2%nat) (- 2128) (- 64) 0 0
[YQ0b.mkChunk (- 2128) (CVal 8 (SOff 2 (- 2112))); YQ0b.mkChunk (- 2120) (CVal 8 (SOff 36%nat 0))])) in HS1;
[ | img_refl
| unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn2 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2;
split; [img_try (clear - Usp Hlo LB; numconst; img_lia)|]; split; [img_try (clear - Usp Hlo LB; numconst; img_lia)|]; split; [img_try (intros o Ho; img_lia) |];
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])];
[ img_try (eapply (chunk_ok_val tfxsegs En2 _ _ (-2128) 8 (SOff 2 (-2112)) (sp0 - 2112));
[cbn [sv_denot]; rewrite (HEn2 2%nat ltac:((img_case; cbv); img_lia)), E2; f_equal; unfold sp0; img_lia | clear - Usp Hlo LB; numconst; img_lia | cbn; img_lia
| eapply val_mem_addr; [img_exact OBJ0 | unfold sp0; img_lia]])
| img_try (eapply (chunk_ok_val tfxsegs En2 _ _ (-2120) 8 (SOff 36%nat 0) LENv);
[cbn [sv_denot]; rewrite (HEn2 36%nat ltac:((img_case; cbv); img_lia)), EaLEN; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia
| pose proof (unwind_of_chain_length (0x53244 + D_2c4) ((sp0, bv_unsigned (getr regs0 1), bv_unsigned (getr regs0 8)) :: ch));
unfold YF2d.LENv, YF2d.tr, call_trace, frame0_ok, spZ, raZ, s0Z; fold sp0; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
destruct (sp0 + 16 <? ly_top ly); cbn [length]; img_lia
| cbn; img_lia | eapply val_mem_addr; [img_exact OBJ1 | unfold sp0; img_lia]]) ]
| img_apply all_disjoint_of_forall; intros r' [<-|[<-|[<-|Hr']]];
[ unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; unfold IFRAME, ASTACK; img_lia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn2 37%nat ltac:(img_try ((img_case; cbv); img_lia))), (HEn2 2%nat ltac:(img_try ((img_case; cbv); img_lia))), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (img_try (clear - DR; numconst; img_lia)); clear - DR Usp Hlo LB; numconst; img_lia
| unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; img_lia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (img_try ((img_case; vm_compute); img_refl)) end;
pose proof (tail_facts En2 r' HEn2 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite (HEn2 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2;
clear - Y1 Y2; unfold ASTACK in *; img_lia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (MEQ2 : MEQJ mem2 mem2).
{ split; [|img_try (intros x Hx; img_refl)]. destruct MEQU as [M I]. assert (LOWEQ : forall a, a < sp0 - ASTACK -> 0 <= a -> mem2 (Z_to_bv 64 a) = ms_mem msU (Z_to_bv 64 a)).
{ intros a Ha Ha'. img_apply Hfr'. rewrite unsigned_lit_small by (img_try (clear - Ha Ha' Usp; unfold ASTACK in *; img_lia)). img_lia. }
split.
- intros x Hx Hz. rewrite <- (M x Hx Hz). img_apply Hfr'. intros HH. img_apply Hx. left. unfold ASTACK in *. img_lia.
- destruct I as (I1 & I2 & I3 & I4 & I5). unfold YF2d.IAL_POST.
repeat match goal with |- _ /\ _ => split end;
try (eapply val_mem_frame; [|img_try (eassumption)]; intros k Hk; img_apply LOWEQ; clear - Hk Hlo LB; numconst; img_lia).
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) (ms_mem msU) mem2 a) by (img_try (img_apply LOWEQ; clear - Ha Hlo LB; numconst; img_lia)). img_apply I5. img_exact Ha. }
clear MEQU.
srr_run_sh tfxtbl_rtF_ok HS. meq_accJ HEn2.
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
srr_run_sh tfxtbl_rtF_ok HS. meq_accJ HEn3.
assert (T1V : zev (rho_of En3) T1term = 3 + 256 * hb1) by (img_try (img_apply T1_val; [img_try (img_exact Hhb1) | img_try (rewrite R38; img_refl)])).
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 1)) in HS. 2:{ intros X; discriminate. }
2:{ lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end.
img_apply U_eq_by_zev; [img_refl | img_refl |]. fold T1term. cbn [zev]. rewrite T1V. unfold zalu_raw.
img_change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftr_div_pow2 by img_lia. img_change (2 ^ 8) with 256.
rewrite (Z.mul_comm 256), Z_div_plus_full by img_lia. img_change (3 / 256) with 0. rewrite Z.add_0_l.
img_change (2 ^ Z.of_N 8) with 256. rewrite (zcanon_id hb1) by (img_try (unfold M64; img_lia)). rewrite (Z.mod_small hb1 256) by img_lia.
rewrite (zcanon_id hb1) by (img_try (unfold M64; img_lia)). img_change (zcanon 3) with (Z.ones 2). rewrite Z.land_ones by img_lia. img_change (2 ^ 2) with 4.
replace (hb1 mod 4) with 1; [img_refl|]. rewrite <- HWb1. unfold YF2d.HWv. rewrite (Z.mul_comm 256), Z_div_plus_full by img_lia. img_refl. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtF_ok HS. meq_accJ HEn3.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 3)) in HS. 2:{ intros X; discriminate. }
2:{ lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end.
img_apply U_eq_by_zev; [img_refl | img_refl |]. fold T1term. cbn [zev]. rewrite T1V.
img_change (2 ^ Z.of_N 8) with 256. rewrite (Z.mul_comm 256), Z_mod_plus_full. img_refl. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfxtbl_rtF_ok HS (0x72fcc + D_2c4). meq_accJ HEn3.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msD end.
match goal with M : MEQJ mem2 (ms_mem msD) |- _ => rename M into MEQD end.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) En3 _ _ HS eq_refl) as HshapeD; cbn [ss_pc] in HshapeD.
img_apply SRr_ret. split; [img_refl|]. exists msD, mat1, En3.
split; [img_refl|]. split; [img_try (img_exact HshapeD)|]. split; [img_try (img_exact HEn3)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact (proj1 MEQD))|].
split. { intros i Hi. eapply val_mem_frame; [|img_try (img_exact (Ht2 i Hi))]. intros k Hk. img_apply (proj2 MEQD).
pose proof (unwind_of_chain_length (0x53244 + D_2c4) ((sp0, bv_unsigned (getr regs0 1), bv_unsigned (getr regs0 8)) :: ch)) as LEN.
assert (HL : (i < 30)%nat).
{ revert Hi LEN. unfold YF2d.tr, call_trace, frame0_ok, spZ, raZ, s0Z. fold sp0. destruct (sp0 + 16 <? ly_top ly); cbn [length]; intros; img_lia. }
rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB Hk HL; numconst; img_lia)). clear - Hk HL; img_lia. }
intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)); [|img_try (destruct (Z_lt_le_dec a (sp0 - 64)))].
- eapply (st_ok_window_apresent_off (w_H W) En3 _ _ 1 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn3 2%nat ltac:((img_case; cbv); img_lia)), E2; clear - Ha l Usp Hlo LB; numconst; img_lia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; img_lia)) ].
-
destruct (PRES3 a Ha) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite <- Hb. img_apply (proj2 MEQD). rewrite unsigned_lit_small by (img_try (clear - Ha Usp Hlo LB; numconst; img_lia)). unfold IFRAME in *. img_lia.
- eapply (st_ok_window_apresent_off (w_H W) En3 _ _ 3 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn3 2%nat ltac:((img_case; cbv); img_lia)), E2; clear - Ha l0 Usp Hlo LB; numconst; img_lia) | img_try (off_by ltac:(clear - Ha Usp Hlo LB; numconst; img_lia)) ].
Qed.
End WK.
End d.
