(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGh1.v (commit 30a1993588f, c5 + memnorm; file sha256 c2f41408f626) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/DGh1.v (commit d2dafa219c1, file sha256 ddbc1e9ca3c8) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 2 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFeq DGbase DGgn DGfx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, DFSTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, SHADOW_OFF, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (tr : list Z).
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
Hypothesis FH : free_hyps W ly regs0 mem0 tr regsU.
Local Notation LENv := (DGgn.LENv ly regs0 tr).
Local Notation XW := (DGgn.XW ly regs0 tr).
Local Notation E0 := (DGgn.E0 ly regs0 tr).
Local Notation Er := (DGgn.Er ly regs0 tr).
Local Notation E2 := (DGgn.E2 ly regs0 tr).
Local Notation E1 := (DGgn.E1 ly regs0 tr).
Local Notation E8 := (DGgn.E8 ly regs0 tr).
Local Notation E10 := (DGgn.E10 ly regs0 tr).
Local Notation E4 := (DGgn.E4 ly regs0 tr).
Local Notation EaT := (DGgn.EaT ly regs0 tr).
Local Notation EaC := (DGgn.EaC ly regs0 tr).
Local Notation EaSB := (DGgn.EaSB ly regs0 tr).
Local Notation EaTOP := (DGgn.EaTOP ly regs0 tr).
Local Notation EaLEN := (DGgn.EaLEN ly regs0 tr).
Local Notation EaIM := (DGgn.EaIM ly regs0 tr).
Local Notation EaSHB := (DGgn.EaSHB ly regs0 tr).
Local Notation AL := DGgn.AL.
Local Notation REG0 := DGgn.REG0.
Local Notation FFN := DGgn.FFN.
Local Notation SS0 := DGgn.SS0.
Local Notation LYB := (DGgn.LYB W ly regs0 mem0 tr regsU FH).
Local Notation LYD := (DGgn.LYD W ly regs0 mem0 tr regsU FH).
Local Notation iv_vs_stack := (DGgn.iv_vs_stack W ly regs0 mem0 tr regsU FH).
Local Notation stack_ivs := (DGgn.stack_ivs W ly regs0 mem0 tr regsU FH).
Local Notation WIN := (DGgn.WIN ly regs0).
Local Notation WSKEL := DGgn.WSKEL.
Local Notation win_sub := DGgn.win_sub.
Local Notation win_sub_sound := (DGgn.win_sub_sound W ly regs0 mem0 tr regsU FH).
Local Notation WSKEL_WIN := (DGgn.WSKEL_WIN W ly regs0 mem0 tr regsU FH).
Local Notation windows_WIN := (DGgn.windows_WIN W ly regs0 mem0 tr regsU FH).
Local Notation frame_WIN := (DGgn.frame_WIN W ly regs0 mem0 tr regsU FH).
Local Notation WIN_zone := (DGgn.WIN_zone W ly regs0 mem0 tr regsU FH).
Local Notation WIN_off := (DGgn.WIN_off W ly regs0 mem0 tr regsU FH).
Local Notation WIN_not_high := (DGgn.WIN_not_high W ly regs0 mem0 tr regsU FH).
Local Notation all_disjoint_of_forall := (DGgn.all_disjoint_of_forall W ly regs0 mem0 tr regsU FH).
Local Notation kept_of_frame := (DGgn.kept_of_frame W ly regs0 mem0 tr regsU FH).
Local Notation kept_of_frame_hi := (DGgn.kept_of_frame_hi W ly regs0 mem0 tr regsU FH).
Local Notation kept_of_vframe := (DGgn.kept_of_vframe W ly regs0 mem0 tr regsU FH).
Local Notation SKEL_TAIL := DGgn.SKEL_TAIL.
Local Notation IZONE := DGgn.IZONE.
Local Notation tail_facts := (DGgn.tail_facts W ly regs0 mem0 tr regsU FH).
Local Notation MEQ := (DGgn.MEQ ly regs0 mem0).
Local Notation IAL_POST := (DGgn.IAL_POST W).
Local Notation MEQI := (DGgn.MEQI W ly regs0 mem0).
Local Notation MEQI_frame := (DGgn.MEQI_frame W ly regs0 mem0 tr regsU FH).
Local Notation notWIN_img := (DGgn.notWIN_img W ly regs0 mem0 tr regsU FH).
Local Notation notWIN_shb := (DGgn.notWIN_shb W ly regs0 mem0 tr regsU FH).
Local Notation notWIN_Thead := (DGgn.notWIN_Thead W ly regs0 mem0 tr regsU FH).
Local Notation notWIN_C := (DGgn.notWIN_C W ly regs0 mem0 tr regsU FH).
Local Notation notWIN_NB := (DGgn.notWIN_NB W ly regs0 mem0 tr regsU FH).
Local Notation notWIN_SB := (DGgn.notWIN_SB W ly regs0 mem0 tr regsU FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Hp10 Htp Hra Hra4096 Hsp Hsp_al Htrlen Hso Hbp Hinst HIAL SEED PBUF0].
Local Notation off_T := (DGgn.off_T W ly regs0 mem0 tr regsU FH).
Local Notation off_C := (DGgn.off_C W ly regs0 mem0 tr regsU FH).
Local Notation off_NB := (DGgn.off_NB W ly regs0 mem0 tr regsU FH).
Local Notation off_SB := (DGgn.off_SB W ly regs0 mem0 tr regsU FH).
Local Notation pres_off_of_frame := (DGgn.pres_off_of_frame W).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize; tac | apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac | apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Definition at_RETN (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
regs_preserved regs0 regs' /\
MEQI mem' /\
val_mem tfibsegs (mrestrict (w_H W) mem') (T + t_unwinding) 1 0 /\
(forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W) mem' a).
Ltac meq_acc HE :=
match goal with
| M : MEQI ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQI_frame E rs ma mb HE ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.
Ltac cs_case HS HEn Htp kb :=
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ => replace (Z_to_bv 5 k) with kb by (apply bv_eq; reflexivity) end;
let RR := fresh "RR" in rreg HS kb RR; rewrite RR; first [ rewrite HEn by (cbv; zlia); apply Er; reflexivity | rewrite Htp; reflexivity ].
(* The NULL arm of the frame-generic Deallocate walk (from YFh1.segN, without the free interceptor's prefix: the
   internal-allocator check and the unwinder are the caller's, so the walk starts at the generic seed DGgn.SS0 at
   Deallocate's first instruction and stops at the early [ret] at 0x319a0, the state DGfx.SS_RN). *)
Lemma segN : SRr tfibsegs W cfg0 at_RETN.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS.
destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
set (En0 := E0) in HS.
assert (HEn0 : forall k, (k < aHAVf)%nat -> ew En0 k = ew E0 k) by (intros k _; reflexivity).
assert (MEQ0 : MEQI mem0) by (split; [intros x _ _; reflexivity | exact HIAL]).
srr_run_to_sh tfibtbl_rtF_ok HS 0x319a0. meq_acc HEn0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
match goal with M : MEQI (ms_mem msR) |- _ => rename M into MEQR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W En0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
rreg HS (1%bv : bv 5) Q1. rewrite (HEn0 1%nat ltac:(cbv; zlia)), E1 in Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { intros r Hr. unfold callee_saved in Hr.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
clear Hr. repeat match type of R with _ \/ _ => destruct R as [R|R] end; subst r;
[ cs_case HS HEn0 Htp (2%bv : bv 5) | cs_case HS HEn0 Htp (3%bv : bv 5) | cs_case HS HEn0 Htp (4%bv : bv 5) | cs_case HS HEn0 Htp (8%bv : bv 5) | cs_case HS HEn0 Htp (9%bv : bv 5)
| cs_case HS HEn0 Htp (18%bv : bv 5) | cs_case HS HEn0 Htp (19%bv : bv 5) | cs_case HS HEn0 Htp (20%bv : bv 5) | cs_case HS HEn0 Htp (21%bv : bv 5) | cs_case HS HEn0 Htp (22%bv : bv 5)
| cs_case HS HEn0 Htp (23%bv : bv 5) | cs_case HS HEn0 Htp (24%bv : bv 5) | cs_case HS HEn0 Htp (25%bv : bv 5) | cs_case HS HEn0 Htp (26%bv : bv 5) | cs_case HS HEn0 Htp (27%bv : bv 5) ]. }
split; [exact MEQR|].
split. { memv HS 33%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn0 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); unfold t_unwinding; zlia | reflexivity | zlia]. }
intros a Ha. eapply (st_ok_window_apresent_off (w_H W) En0 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn0 2%nat ltac:(cbv; zlia)), E2; clear - Ha Usp Hlo LB; numconst; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
Qed.
End WK.
End c.
