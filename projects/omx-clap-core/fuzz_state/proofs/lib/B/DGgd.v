(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGgd.v (a working branch ced28ed2383, file sha256 80df1e8ef27e) onto omx-clap-core/fuzz_state's asan-ubsan image (fuzz_state.asan-ubsan, pinned sha256 5ac5ce0954f8; addresses read from its unstripped build b1566a1ca816); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YE3d YFeq DGgm DGbase DGfw.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, DFSTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, SHADOW_OFF, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (tr : list Z).
Variables (p nn hb1 : Z) (q : qcache) (j1 j2 j3 : Z).
Variable regsU : bvmap 5 word.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regsU (w64 A_Deallocate) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU.
Local Notation LENv := (DGgm.LENv ly regs0 tr).
Local Notation IMv := (DGgm.IMv p).
Local Notation HWv := (DGgm.HWv hb1).
Local Notation SPv := (DGgm.SPv p).
Local Notation N8v := (DGgm.N8v nn).
Local Notation CNT8v := (DGgm.CNT8v nn).
Local Notation QBFv := (DGgm.QBFv nn q).
Local Notation XW := (DGgm.XW ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E0 := (DGgm.E0 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation Er := (DGgm.Er ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E2 := (DGgm.E2 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E1 := (DGgm.E1 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E8 := (DGgm.E8 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E10 := (DGgm.E10 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E4 := (DGgm.E4 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaT := (DGgm.EaT ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaC := (DGgm.EaC ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaSB := (DGgm.EaSB ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaTOP := (DGgm.EaTOP ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaLEN := (DGgm.EaLEN ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaIM := (DGgm.EaIM ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaHW := (DGgm.EaHW ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaN := (DGgm.EaN ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaSHB := (DGgm.EaSHB ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaSP := (DGgm.EaSP ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaN8 := (DGgm.EaN8 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaCNT8 := (DGgm.EaCNT8 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaQBF := (DGgm.EaQBF ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaJ1 := (DGgm.EaJ1 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaJ2 := (DGgm.EaJ2 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaJ3 := (DGgm.EaJ3 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation AL := DGgm.AL.
Local Notation HB1MASK := (DGgm.HB1MASK hb1).
Local Notation PSTATIC := (DGgm.PSTATIC ly p nn).
Local Notation REG0 := DGgm.REG0.
Local Notation FFM := DGgm.FFM.
Local Notation SS0 := DGgm.SS0.
Local Notation LYB := (DGgm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation LYD := (DGgm.LYD W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation iv_vs_stack := (DGgm.iv_vs_stack W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation N8_ge := (DGgm.N8_ge W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation stack_ivs := (DGgm.stack_ivs W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation derived_ranges := (DGgm.derived_ranges W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation derived_align := (DGgm.derived_align W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WINT := (DGgm.WINT ly).
Local Notation WINB := (DGgm.WINB p).
Local Notation WIN := (DGgm.WIN ly regs0 p).
Local Notation WSKEL := DGgm.WSKEL.
Local Notation win_sub := DGgm.win_sub.
Local Notation win_sub_sound := (DGgm.win_sub_sound W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WSKEL_WIN := (DGgm.WSKEL_WIN W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation windows_WIN := (DGgm.windows_WIN W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation frame_WIN := (DGgm.frame_WIN W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WIN_zone := (DGgm.WIN_zone W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WIN_off := (DGgm.WIN_off W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WIN_not_high := (DGgm.WIN_not_high W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation all_disjoint_of_forall := (DGgm.all_disjoint_of_forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation kept_of_frame := (DGgm.kept_of_frame W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation kept_of_frame_hi := (DGgm.kept_of_frame_hi W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation kept_of_vframe := (DGgm.kept_of_vframe W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation p_ivs := (DGgm.p_ivs W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation SKEL_TAIL := DGgm.SKEL_TAIL.
Local Notation DZONE := (DGgm.DZONE ly).
Local Notation IZONE := DGgm.IZONE.
Local Notation tail_facts := (DGgm.tail_facts W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation MEQ := (DGgm.MEQ ly regs0 mem0 p).
Local Notation IAL_POST := (DGgm.IAL_POST W).
Local Notation MEQI := (DGgm.MEQI W ly regs0 mem0 p).
Local Notation MEQI_frame := (DGgm.MEQI_frame W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WIN2 := (DGgm.WIN2 ly regs0 p).
Local Notation WIN2_WIN := (DGgm.WIN2_WIN ly regs0 p).
Local Notation WSKEL2 := DGgm.WSKEL2.
Local Notation WSKEL2_WIN2 := (DGgm.WSKEL2_WIN2 W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation windows_WIN2 := (DGgm.windows_WIN2 W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation OBJQ := (DGgm.OBJQ regs0).
Local Notation MEQJ := (DGgm.MEQJ W ly regs0 mem0 p).
Local Notation MEQJ_frame := (DGgm.MEQJ_frame W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation memset_stretch := (DGgm.memset_stretch W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_img := (DGgm.notWIN_img W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_shb := (DGgm.notWIN_shb W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_Thead := (DGgm.notWIN_Thead W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_C := (DGgm.notWIN_C W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_NB := (DGgm.notWIN_NB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_SB := (DGgm.notWIN_SB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Hp10 Htp Hra Hra4096 Hsp Hsp_al Htrlen Hso Hbp Hinst Hp IMG Hp_al Hnn Hhb1 Hhb1m Hp_static Hp_pres Hsh_pres Hqb Hjunk HIAL SEED PBUF0].
Local Notation off_T := (DGgm.off_T W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation off_C := (DGgm.off_C W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation off_NB := (DGgm.off_NB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation off_SB := (DGgm.off_SB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation off_P := (DGgm.off_P W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation off_P8 := (DGgm.off_P8 W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation pres_off_of_frame := (DGgm.pres_off_of_frame W).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize; tac | apply off_C; tac | apply off_P8; tac | apply off_P; tac
| apply off_NB; unfold kNodesBlockSize; tac | apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
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
assert (Ep : p = 16 * (p / 16)) by (pose proof (Z.div_mod p 16 ltac:(zlia)); unfold DGgm.AL in P16; zlia).
rewrite Ep. replace (16 * (p / 16) * 8 - 128) with ((4 * (p / 16) - 4) * 2 ^ 5) by zlia. apply Z_mod_mult.
Qed.
Definition TRACEQ (m : word -> option byte) : Prop :=
forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) m) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
Definition at_D1 (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists (ms : machine_state) mat (E3 : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
ms = mkst (ms_regs ms) (w64 0x72fac) (ms_mem ms) (seg_rom tfibsegs) /\
(forall k, (k < aHAVf)%nat -> ew E3 k = ew E0 k) /\
st_ok tfibsegs E3 SS_B (restrict (w_H W) ms) /\
MEQI (ms_mem ms) /\ TRACEQ (ms_mem ms) /\ (forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).
Ltac meq_accJ HE :=
match goal with
| M : MEQJ ?mr ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQJ_frame E rs mr ma mb HE ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
(* From Deallocate's entry (the seed) to StackDepotPut's entry: YFgc.segB's script after the free interceptor's
   prefix (the unwinder's return and the stack object's regions are gone: the object is the seed's aSO region). *)
Lemma segB : SRr tfibsegs W cfg0 at_D1.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB. pose proof derived_ranges as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
set (En2 := E0) in HS.
assert (HEn2 : forall k, (k < aHAVf)%nat -> ew En2 k = ew E0 k) by (intros k _; reflexivity).
assert (MEQ2 : MEQJ mem0 mem0) by (split; [split; [intros x _ _; reflexivity | exact HIAL] | intros x _; reflexivity]).
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
replace (hb1 mod 4) with 1; [reflexivity|]. rewrite <- HWb1. unfold DGgm.HWv. rewrite (Z.mul_comm 256), Z_div_plus_full by zlia. reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtF_ok HS. meq_accJ HEn3.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 3)) in HS. 2:{ intros X; discriminate. }
2:{ lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end.
apply U_eq_by_zev; [reflexivity | reflexivity |]. fold T1term. cbn [zev]. rewrite T1V.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mul_comm 256), Z_mod_plus_full. reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS 0x72fac. meq_accJ HEn3.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msD end.
match goal with M : MEQJ mem0 (ms_mem msD) |- _ => rename M into MEQD end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En3 _ _ HS eq_refl) as HshapeD; cbn [ss_pc] in HshapeD.
apply SRr_ret. split; [reflexivity|]. exists msD, mat1, En3.
split; [reflexivity|]. split; [exact HshapeD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact (proj1 MEQD)|].
split. { intros i Hi. eapply val_mem_frame; [|exact (PBUF0 i Hi)]. intros k Hk. apply (proj2 MEQD). right.
destruct Hbp as (B1 & B2 & B3). assert (HL : (i < 30)%nat) by lia.
rewrite unsigned_lit_small by (clear - B1 B2 Hk HL Usp Hlo LB; unfold BPv in *; numconst; lia). clear - Hk HL; lia. }
intros a Ha. eapply (st_ok_window_apresent_off (w_H W) En3 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn3 2%nat ltac:(cbv; lia)), E2; clear - Ha Usp Hlo LB; numconst; lia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; lia) ].
Qed.
End WK.
End d.
