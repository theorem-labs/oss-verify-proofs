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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFeq AFgm AFfw AFgb.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAME, SHADOW_OFF, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Local Notation at_U1 := (AFgb.at_U1 W ly regs0 mem0 md0 ch p nn hb1 q j1 j2 j3).
Ltac meq_acc HE :=
match goal with
| M : MEQI ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQI_frame E rs ma mb HE ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Ltac show_regs HS := lazymatch type of HS with st_ok _ _ ?ss _ => let r := eval vm_compute in (ss_pc ss, ss_regs ss) in idtac r end.
Ltac show_skel HS := lazymatch type of HS with st_ok _ _ ?ss _ => let r := eval vm_compute in (combine (seq 0 (length (ss_mem ss))) (skeleton (ss_mem ss))) in idtac r end.
Ltac show_reg HS i := lazymatch type of HS with st_ok _ _ ?ss _ => let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in idtac r end.
Lemma shamt_p : forall (rho : nat -> Z), rho 10%nat = p ->
Z.land (zev rho (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10%nat 0) (SLit 3)) (SLit (-128))) mod 2 ^ 32) 31 = 0.
Proof.
open_FH. intros rho Hr. pose proof derived_ranges as DR. pose proof derived_align as (P16 & _). pose proof N8_ge as [N8a _].
cbn [zev zalu_raw]. rewrite Hr. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in DR.
rewrite (zcanon_id (p + 0)) by (unfold M64; zlia). change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((p + 0) * 8)) by (unfold M64; zlia). change (zcanon (-128)) with (2 ^ 64 - 128).
replace ((p + 0) * 8 + (2 ^ 64 - 128)) with ((p * 8 - 128) + 1 * M64) by (unfold M64; zlia).
unfold zcanon. rewrite Z_mod_plus_full. rewrite (Z.mod_small _ M64) by (unfold M64; zlia).
change 31 with (Z.ones 5). rewrite Z.land_ones by zlia.
rewrite (Z.mod_mod_divide _ (2 ^ 32) (2 ^ 5)) by (exists (2 ^ 27); reflexivity).
assert (Ep : p = 16 * (p / 16)) by (pose proof (Z.div_mod p 16 ltac:(zlia)); unfold AFgm.AL in P16; zlia).
rewrite Ep. replace (16 * (p / 16) * 8 - 128) with ((4 * (p / 16) - 4) * 2 ^ 5) by zlia. apply Z_mod_mult.
Qed.
Definition TRACEQ (m : word -> option byte) : Prop :=
forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) m) (sp0 - 2112 + 8 * Z.of_nat i) 8 (nth i tr 0).
Definition at_D1 (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists (ms : machine_state) mat (E3 : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
ms = mkst (ms_regs ms) (w64 0x724b0) (ms_mem ms) (seg_rom tfibsegs) /\
(forall k, (k < aHAVf)%nat -> ew E3 k = ew E0 k) /\
st_ok tfibsegs E3 SS_B (restrict (w_H W) ms) /\
MEQI (ms_mem ms) /\ TRACEQ (ms_mem ms) /\ (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).
Ltac meq_accJ HE :=
match goal with
| M : MEQJ ?mr ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQJ_frame E rs mr ma mb HE ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Lemma segB : forall W' c', at_U1 W' c' -> SRr tfibsegs W' c' at_D1.
Proof.
intros W' c' (-> & msU & regs2 & mem2 & mat2 & En1 & -> & HEn1 & HS & HP2 & Hfr2 & Hpr2 & Ht1 & Ht2 & Ht3 & MEQU & PRES2).
open_FH. pose proof Hwx_tfa as Hwx. destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB. pose proof derived_ranges as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
rreg HS (2%bv : bv 5) Q2. rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2 in Q2.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem2 x = ms_mem msU x).
{ intros x Hx. apply Hfr2; clear - Hx; unfold ASTACK, UNW_STK in *; zlia. }
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?rim :: ?rscr :: ?rfr :: ?rest =>
pose proof (st_ok_after_call tfibsegs 70 En1 ss ms0 regs2 (mrestrict (w_H W) mem2) (rim :: trim_lo rfr (-64) :: rest) 0x52ac8 HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl|]; apply submem_drop; apply submem_keep; [apply subregion_trim_lo | apply submem_refl])
ltac:(vm_compute; reflexivity) HP2) as HS1;
let rsv := eval vm_compute in (rim :: trim_lo rfr (-64) :: rest) in
change (rim :: trim_lo rfr (-64) :: rest) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 70 0x52ac8) in
change (ss_after_call ss rsv 70 0x52ac8) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs En1 (mrestrict (w_H W) (ms_mem msU)) (mrestrict (w_H W) mem2)) (r0 :: r1 :: tail));
[ constructor; [|constructor];
[ eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn1 37%nat ltac:(cbv; zlia)), EaIM; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); intros a Ha; cbn beta; clear - Ha DR Hlo LB Usp; numconst; zlia
| eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; zlia
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts En1 r HEn1 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); intros a Ha; cbn beta; clear - Ha Y1 Y2 Y3 Y4; numconst; zlia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (OBJ0 : val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 2128) 8 (sp0 - 2112)).
{ eapply val_mem_frame; [intros k Hk; apply Hfr2; rewrite unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; zlia); clear - Hk; numconst; zlia|].
memv HS 2%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; f_equal; unfold sp0; zlia | clear - Usp Hlo LB; numconst; zlia]. }
assert (OBJ1 : val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 2120) 8 LENv).
{ replace (AFgm.LENv ly regs0 ch) with (LENv + 2 ^ 32 * 0) by zlia.
pose proof (unwind_of_chain_length 0x52a6c ((sp0, bv_unsigned (getr regs0 1), bv_unsigned (getr regs0 8)) :: ch)) as LEN.
assert (HL : 1 <= LENv <= 30).
{ unfold AFgm.LENv, AFgm.tr, call_trace, frame0_ok, spZ, raZ, s0Z. fold sp0. destruct (sp0 + 16 <? ly_top ly); cbn [length]; zlia. }
apply val_mem_4_4; [zlia | zlia | |].
- eapply val_mem_addr; [exact Ht1 | zlia].
- assert (Z8 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msU)) (sp0 - 2120) 8 0).
{ memv HS 2%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia | reflexivity | zlia]. }
assert (Z4 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msU)) (sp0 - 2120 + 4) 4 0).
{ intros k Hk. replace (sp0 - 2120 + 4 + Z.of_nat k) with (sp0 - 2120 + Z.of_nat (4 + k)) by zlia.
rewrite (Z8 (4 + k)%nat ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
eapply val_mem_frame; [intros k Hk; apply Hfr2; rewrite unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; zlia); clear - Hk; numconst; zlia| exact Z4]. }
assert (PRES3 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a) by (intros a Ha; apply Hpr2, PRES2, Ha).
set (En2 := havoc En1 70 (map (getr regs2) CLOB)) in HS1.
assert (HEn2 : forall k, (k < aHAVf)%nat -> ew En2 k = ew E0 k) by (intros k Hk; subst En2; unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; apply HEn1; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; unfold IFRAME;
split; [clear - Usp Hlo LB; numconst; zlia|]; split; [clear - Usp Hlo LB; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Usp Hlo LB Ho; numconst; zlia) | apply PRES3; clear - Ho; numconst; zlia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 37%nat ltac:(cbv; zlia)), (HEn2 2%nat ltac:(cbv; zlia)), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR Usp Hlo LB; numconst; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En2 r' HEn2 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- 2128) (- 64) 0 0
[YP09.mkChunk (- 2128) (CVal 8 (SOff 2 (- 2112))); YP09.mkChunk (- 2120) (CVal 8 (SOff 36%nat 0))])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2;
split; [clear - Usp Hlo LB; numconst; zlia|]; split; [clear - Usp Hlo LB; numconst; zlia|]; split; [intros o Ho; zlia |];
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
[ eapply (chunk_ok_val tfibsegs En2 _ _ (-2128) 8 (SOff 2 (-2112)) (sp0 - 2112));
[cbn [sv_denot]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; f_equal; unfold sp0; zlia | clear - Usp Hlo LB; numconst; zlia | cbn; zlia
| eapply val_mem_addr; [exact OBJ0 | unfold sp0; zlia]]
| eapply (chunk_ok_val tfibsegs En2 _ _ (-2120) 8 (SOff 36%nat 0) LENv);
[cbn [sv_denot]; rewrite (HEn2 36%nat ltac:(cbv; zlia)), EaLEN; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia
| pose proof (unwind_of_chain_length 0x52a6c ((sp0, bv_unsigned (getr regs0 1), bv_unsigned (getr regs0 8)) :: ch));
unfold AFgm.LENv, AFgm.tr, call_trace, frame0_ok, spZ, raZ, s0Z; fold sp0; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
destruct (sp0 + 16 <? ly_top ly); cbn [length]; zlia
| cbn; zlia | eapply val_mem_addr; [exact OBJ1 | unfold sp0; zlia]] ]
| apply all_disjoint_of_forall; intros r' [<-|[<-|[<-|Hr']]];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME, ASTACK; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 37%nat ltac:(cbv; zlia)), (HEn2 2%nat ltac:(cbv; zlia)), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR Usp Hlo LB; numconst; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En2 r' HEn2 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (MEQ2 : MEQJ mem2 mem2).
{ split; [|intros x Hx; reflexivity]. destruct MEQU as [M I]. assert (LOWEQ : forall a, a < sp0 - ASTACK -> 0 <= a -> mem2 (Z_to_bv 64 a) = ms_mem msU (Z_to_bv 64 a)).
{ intros a Ha Ha'. apply Hfr'. rewrite unsigned_lit_small by (clear - Ha Ha' Usp; unfold ASTACK in *; zlia). zlia. }
split.
- intros x Hx Hz. rewrite <- (M x Hx Hz). apply Hfr'. intros HH. apply Hx. left. unfold ASTACK in *. zlia.
- destruct I as (I1 & I2 & I3 & I4 & I5). unfold AFgm.IAL_POST.
repeat match goal with |- _ /\ _ => split end;
try (eapply val_mem_frame; [|eassumption]; intros k Hk; apply LOWEQ; clear - Hk Hlo LB; numconst; zlia).
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) (ms_mem msU) mem2 a) by (apply LOWEQ; clear - Ha Hlo LB; numconst; zlia). apply I5. exact Ha. }
clear MEQU.
srr_run_sh tfibtbl_rtF_ok HS. meq_accJ HEn2.
match goal with M : MEQJ _ _ |- _ => rename M into MQ end.
lazymatch type of HS with st_ok _ ?E _ _ => set (En3 := E) in HS end.
assert (HEn3 : forall k, (k < aHAVf)%nat -> ew En3 k = ew E0 k) by (intros k Hk; subst En3; exact (HEn2 k Hk)).
assert (R10 : rho_of En3 10%nat = p) by (unfold rho_of; rewrite (HEn3 10%nat ltac:(cbv; zlia)), E10, Hp10; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R38 : rho_of En3 38%nat = HWv) by (unfold rho_of; rewrite (HEn3 38%nat ltac:(cbv; zlia)), EaHW; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (PINW : forall (c : Z) (r : bv 5), U En3 (SLit c) = U En3 (SLit c) ->
zcanon c = bv_wrap 64 (bv_swrap 32 (Z.shiftl (zcanon c mod 2 ^ 32) 0)) ->
U En3 (SLit c) = U En3 (SAluw ALU_SLL (SLit c) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 3)) (SLit (-128))))).
{ intros c r _ Hc. apply U_eq_by_zev; [reflexivity | reflexivity |].
cbn [zev]. fold (zev (rho_of En3) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 3)) (SLit (-128)))).
unfold zalu_raw. rewrite (shamt_p (rho_of En3) R10). exact Hc. }
apply (st_ok_pin_regU _ _ _ 15%bv (SLit 255)) in HS; [| intros X; discriminate | apply (PINW 255 15%bv eq_refl); vm_compute; reflexivity].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 14%bv (SLit 2)) in HS; [| intros X; discriminate | apply (PINW 2 14%bv eq_refl); vm_compute; reflexivity].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 16%bv (SLit 3)) in HS; [| intros X; discriminate | apply (PINW 3 16%bv eq_refl); vm_compute; reflexivity].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
pose proof derived_align as (_ & _ & _ & _ & HW256 & HWb1 & _).
apply (st_ok_pin_regU _ _ _ 17%bv (SLit 2)) in HS. 2:{ intros X; discriminate. }
2:{ lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end.
apply U_eq_by_zev; [reflexivity | reflexivity |]. cbn [zev].
fold (zev (rho_of En3) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 3)) (SLit (-128)))). unfold zalu_raw. rewrite (shamt_p (rho_of En3) R10), R38.
change (bv_wrap 64 (bv_swrap 32 (Z.shiftl (zcanon 255 mod 2 ^ 32) 0))) with (Z.ones 8).
rewrite (zcanon_id (HWv + 0)) by (clear - DR; unfold M64; zlia). rewrite Z.add_0_r, Z.land_ones by zlia. change (2 ^ 8) with 256. rewrite HW256. reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtF_ok HS. meq_accJ HEn3.
assert (T1V : zev (rho_of En3) T1term = 3 + 256 * hb1) by (apply T1_val; [exact Hhb1 | rewrite R38; reflexivity]).
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 1)) in HS. 2:{ intros X; discriminate. }
2:{ lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end.
apply U_eq_by_zev; [reflexivity | reflexivity |]. fold T1term. cbn [zev]. rewrite T1V. unfold zalu_raw.
change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 8) with 256.
rewrite (Z.mul_comm 256), Z_div_plus_full by zlia. change (3 / 256) with 0. rewrite Z.add_0_l.
change (2 ^ Z.of_N 8) with 256. rewrite (zcanon_id hb1) by (unfold M64; zlia). rewrite (Z.mod_small hb1 256) by zlia.
rewrite (zcanon_id hb1) by (unfold M64; zlia). change (zcanon 3) with (Z.ones 2). rewrite Z.land_ones by zlia. change (2 ^ 2) with 4.
replace (hb1 mod 4) with 1; [reflexivity|]. rewrite <- HWb1. unfold AFgm.HWv. rewrite (Z.mul_comm 256), Z_div_plus_full by zlia. reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtF_ok HS. meq_accJ HEn3.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 3)) in HS. 2:{ intros X; discriminate. }
2:{ lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end.
apply U_eq_by_zev; [reflexivity | reflexivity |]. fold T1term. cbn [zev]. rewrite T1V.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mul_comm 256), Z_mod_plus_full. reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x724b0. meq_accJ HEn3.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msD end.
match goal with M : MEQJ mem2 (ms_mem msD) |- _ => rename M into MEQD end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En3 _ _ HS eq_refl) as HshapeD; cbn [ss_pc] in HshapeD.
apply SRr_ret. split; [reflexivity|]. exists msD, mat1, En3.
split; [reflexivity|]. split; [exact HshapeD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact (proj1 MEQD)|].
split. { intros i Hi. eapply val_mem_frame; [|exact (Ht2 i Hi)]. intros k Hk. apply (proj2 MEQD).
pose proof (unwind_of_chain_length 0x52a6c ((sp0, bv_unsigned (getr regs0 1), bv_unsigned (getr regs0 8)) :: ch)) as LEN.
assert (HL : (i < 30)%nat).
{ revert Hi LEN. unfold AFgm.tr, call_trace, frame0_ok, spZ, raZ, s0Z. fold sp0. destruct (sp0 + 16 <? ly_top ly); cbn [length]; intros; zlia. }
rewrite unsigned_lit_small by (clear - Usp Hlo LB Hk HL; numconst; zlia). clear - Hk HL; zlia. }
intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)); [|destruct (Z_lt_le_dec a (sp0 - 64))].
- eapply (st_ok_window_apresent_off (w_H W) En3 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn3 2%nat ltac:(cbv; zlia)), E2; clear - Ha l Usp Hlo LB; numconst; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
-
destruct (PRES3 a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply (proj2 MEQD). rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; zlia). unfold IFRAME in *. zlia.
- eapply (st_ok_window_apresent_off (w_H W) En3 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn3 2%nat ltac:(cbv; zlia)), E2; clear - Ha l0 Usp Hlo LB; numconst; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
Qed.
End WK.
End d.
