(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMrecS2.v (commit 67deba317dfb, blob 57dc16216381) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFf2 AFh9 AFha AFhc AFhb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFhf AFhd AFhl.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMrecS.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, AFh9.YFRAME, AFha.YFRAME, AFhc.YFRAME, AFhb.YFRAME, DMwalkIFA.DRSTACK_X in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : DMwalkIFA.dr_pre_r B ARXr AOX DRq (as_inst B) ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (AFhd.sp0 regs0).
Local Notation sp1 := (AFhd.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation zlen := (@AFhd.zlen _).
Local Ltac open_PRE := pose proof PRE as (HAR & Hinst & HDQ & LY & IMG & HSTK & HBL & LENP & INIT & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & CELLS).

Lemma entry_facts_r :
ly_stk_lo ly + DRSTACK <= sp0 /\ sp0 + 32 <= ly_stk_hi ly /\ sp0 mod 16 = 0 /\
getr regs0 3 = w64 (as_gp B) /\ getr regs0 4 = w64 TFIB_TP /\ YK0s.ret_ok (getr regs0 1) /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof.
open_PRE. pose proof (DMrecS.ly_facts ly LY IMG) as (_ & _ & _ & _ & T5 & T6 & _).
rewrite (ts_tp _ TB) in Htp. unfold AFhd.sp0, spZ in *. unfold DMwalkIFA.DRSTACK_X, DRSTACK in *. splits; first [assumption | lia].
Qed.
Lemma sp_facts_r : kHighMemBeg + DRSTACK <= sp0 /\ sp0 + 32 <= kHighMemEnd /\ 0 <= sp0 < 2 ^ 64 /\ 0 <= sp1 < 2 ^ 64 /\ sp1 = sp0 - 112 /\ sp0 mod 16 = 0 /\ sp1 mod 16 = 0.
Proof.
pose proof entry_facts_r as (E1 & E2 & E3 & _ & _ & _ & E7 & E8).
assert (U0 : 0 <= sp0 < 2 ^ 64) by (unfold AFhd.sp0; apply u64_range).
unfold AFhd.sp1, AFh9.YFRAME. numconst. splits; try lia.
all: replace (sp0 - 112) with (sp0 + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact E3.
Qed.
Lemma sp1_val_r : forall regs, AFhd.loop_regs regs0 regs -> bv_unsigned (getr regs 2) = sp1.
Proof. intros regs (R2 & _). rewrite R2. unfold w64. apply unsigned_lit_small. pose proof sp_facts_r as (_ & _ & _ & U1 & _). exact U1. Qed.

Lemma stack_not_owned_r : forall X a, (forall a', AOX ly X a' -> AOX ly X0 a') -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly X a.
Proof. intros X a SH Ha O. open_PRE. exact (HSTK a Ha (SH a O)). Qed.

Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Lemma seed_E_r : AFh9.free_hyps W0 ly regs0 mem0 (zlen P0).
Proof.
open_PRE. unfold spZ in *.
pose proof entry_facts_r as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts_r as (S1 & S2 & U0 & U1 & S5 & S6 & S7').
pose proof (DMrecS.ly_facts ly LY IMG) as (_ & _ & _ & _ & _ & _ & _ & _ & FT1 & FT2 & FT3).
assert (Hz : 0 <= zlen P0 < 2 ^ 40) by (clear - LENP; unfold AFhd.zlen, DMwalkIFA.zl in *; lia).
assert (VSZ : val_mem tfibsegs (mrestrict (w_H W0) mem0) sp0 8 (zlen P0)).
{ unfold YFeuC.plist_cells, qc_cells in CELLS. apply Forall_cons_iff in CELLS as [C0 _]. cbn [qc_list length] in C0.
pose proof (cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C0) as V. cbn [aeval] in V. exact V. }
assert (Ha1' : getr regs0 11 = getr regs0 2) by (rewrite Ha1; unfold w64; apply Z_to_bv_bv_unsigned).
constructor.
- exact LY.
- exact IMG.
- exact Etp.
- split; [exact E1 | exact E2].
- exact E3.
- intros a Ha. apply HPRES. clear - Ha. unfold AFhd.sp0 in *. numconst. lia.
- split; [exact Ha1' | exact Ha2].
- exact Era.
- exact Hz.
-
rewrite restrict_mkst_fx. unfold AFh9.SS0, AFh9.SR0, sr_set. cbn [bv_eqb]. unfold AFh9.E0, w64, A_DoRecycle. apply (entry_st_ok_full tfibsegs).
+ set (E0 := Ereg regs0 (AFh9.XW ly (zlen P0))).
repeat (apply regs_ok_pin; [| intros XX; discriminate |]); [apply regs_ok_Ereg | ..]; cbn [sv_denot].
* rewrite Etp. reflexivity.
* rewrite (AFh9.E2 ly regs0 (zlen P0) : ew E0 2 = getr regs0 2), Ha1'. rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs0 2)) at 2. rewrite Zbv_add_unsigned, Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
* change (ew E0 32) with (Z_to_bv 64 T). rewrite Ha2. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ vm_compute. reflexivity.
+ cbn [ms_mem mkst]. set (E0 := Ereg regs0 (AFh9.XW ly (zlen P0))).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite (AFh9.E2 ly regs0 (zlen P0) : ew E0 2 = getr regs0 2); reflexivity).
unfold AFh9.REG0, AFh9.R_STK, AFh9.YFRAME. apply Forall_cons; [|apply Forall_nil].
reg_intro. rewrite BV2. split; [clear - S1; numconst; lia|]. split; [clear - S2; numconst; lia|]. split.
{ intros o Ho. apply apresent_writable; [clear - Ho S1 S2; numconst; lia|]. apply HPRES. clear - Ho. unfold AFhd.sp0. numconst. lia. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom8 E0 _ _ _ 46%nat (zlen P0)); [reflexivity | clear - Hz; lia | eapply val_mem_addr; [exact VSZ | lia]].
+ apply pairwise_disjoint_of_extents. cbn. tauto.
+ split; [|split; exact I]. cbn [AFh9.FFE f_atoms atoms_ok].
set (E0 := Ereg regs0 (AFh9.XW ly (zlen P0))).
assert (E2' : ew E0 2 = w64 sp0) by (rewrite (AFh9.E2 ly regs0 (zlen P0) : ew E0 2 = getr regs0 2); unfold w64, AFhd.sp0; symmetry; apply Z_to_bv_bv_unsigned).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, kThreadObjSize in *.
split. { apply (afact_intro E0 2%nat sp0); [exact E2'| exact U0 | ceil; clear - CR0 S1 S2; lia | change (2 ^ 4) with 16; exact E3 | clear; lia]. }
split. { apply (afact_intro E0 32%nat T); [reflexivity | ceil; clear - CR0 FT1 FT2; lia | ceil; clear - CR0 FT1 FT2; lia | change (2 ^ 12) with 4096; exact FT3 | clear; lia]. }
split; [|exact I]. { apply (afact_intro E0 46%nat (zlen P0)); [reflexivity | ceil; clear - CR0 Hz; lia | ceil; clear - CR0 Hz; lia | change (2 ^ 0) with 1; apply Z.mod_1_r | clear; lia]. }
Qed.
End e.
End c.
