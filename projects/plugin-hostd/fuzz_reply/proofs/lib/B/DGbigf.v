(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGbigf.v (commit 8b4ae5e9984e, the Deallocate big arm, closed at cgif; file sha256 54286126524a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 8 image addresses moved by code-verified function pairs (8 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 14 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: then from plugin-hostd/fuzz_reply lib/A (commit 29bcc0b4b8f) to image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a, unstripped twin 3389287e1d61) by alreloc 56664a20986eb62e, same unit A -> B. *)
(* Theorem Labs, 2026-10 (the Deallocate big-block arm): DGgf.v copied over the big seed (DGbigm for DGgm, DGbigw for
   DGfw, DGbigd for DGgd): segC_big, the walk of a block above the quarantine's max_size from StackDepotPut's return
   (0x35e1c) to QuarantineCallback::Recycle's entry (0x33e88, ra = 0x35ffc). The text is DGgf.segCm1's up to the pin
   of x15 to atom 39 at Quarantine::Put's entry and the run after it; Put's size test (0x35f7c) is then decided as
   NOT taken by the seed's range of atom 39 (kQuarantineMax < nn), and the run stops at FromPrimary's lower test
   (0x35f88, DGbigw.SS_P). Each of FromPrimary's three outcomes (below the primary space, above it, inside it: 0x35f88,
   0x35f98) runs to 0x33e88 (DGbigw.SS_Q1 / SS_Q2 / SS_Q3); x13, the only register where they differ, is forgotten
   into atom 102 and the facts are weakened to DGbigw.F_Q, which gives DGbigw.SS_Q (rcy_close). at_RCY replaces
   DGgf.at_ENQ; the enqueue side (EQ4, EQS and their frame lemmas) is not copied. Nothing here is a function's proof
   (rule 24). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFeq DGbase DGbigm DGbigw DGbigd.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, DFSTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, SHADOW_OFF, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Local Notation LENv := (DGbigm.LENv ly regs0 tr).
Local Notation IMv := (DGbigm.IMv p).
Local Notation HWv := (DGbigm.HWv hb1).
Local Notation SPv := (DGbigm.SPv p).
Local Notation N8v := (DGbigm.N8v nn).
Local Notation CNT8v := (DGbigm.CNT8v nn).
Local Notation QBv := (DGbigm.QBv q).
Local Notation XW := (DGbigm.XW ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E0 := (DGbigm.E0 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation Er := (DGbigm.Er ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E2 := (DGbigm.E2 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E1 := (DGbigm.E1 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E8 := (DGbigm.E8 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E10 := (DGbigm.E10 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E13 := (DGbigm.E13 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation E4 := (DGbigm.E4 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaT := (DGbigm.EaT ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaC := (DGbigm.EaC ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaSB := (DGbigm.EaSB ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaTOP := (DGbigm.EaTOP ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaLEN := (DGbigm.EaLEN ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaIM := (DGbigm.EaIM ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaHW := (DGbigm.EaHW ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaN := (DGbigm.EaN ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaSHB := (DGbigm.EaSHB ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaSP := (DGbigm.EaSP ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaN8 := (DGbigm.EaN8 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaCNT8 := (DGbigm.EaCNT8 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaQB := (DGbigm.EaQB ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaJ1 := (DGbigm.EaJ1 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaJ2 := (DGbigm.EaJ2 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation EaJ3 := (DGbigm.EaJ3 ly regs0 tr p nn hb1 q j1 j2 j3).
Local Notation AL := DGbigm.AL.
Local Notation HB1MASK := (DGbigm.HB1MASK hb1).
Local Notation PSTATIC := (DGbigm.PSTATIC ly p nn).
Local Notation REG0 := DGbigm.REG0.
Local Notation FFM := DGbigm.FFM.
Local Notation SS0 := DGbigm.SS0.
Local Notation LYB := (DGbigm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation LYD := (DGbigm.LYD W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation iv_vs_stack := (DGbigm.iv_vs_stack W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation N8_ge := (DGbigm.N8_ge W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation stack_ivs := (DGbigm.stack_ivs W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation derived_ranges := (DGbigm.derived_ranges W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation derived_align := (DGbigm.derived_align W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WINT := (DGbigm.WINT ly).
Local Notation WINB := (DGbigm.WINB p).
Local Notation WIN := (DGbigm.WIN ly regs0 p).
Local Notation WSKEL := DGbigm.WSKEL.
Local Notation win_sub := DGbigm.win_sub.
Local Notation win_sub_sound := (DGbigm.win_sub_sound W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WSKEL_WIN := (DGbigm.WSKEL_WIN W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation windows_WIN := (DGbigm.windows_WIN W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation frame_WIN := (DGbigm.frame_WIN W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WIN_zone := (DGbigm.WIN_zone W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WIN_off := (DGbigm.WIN_off W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WIN_not_high := (DGbigm.WIN_not_high W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation all_disjoint_of_forall := (DGbigm.all_disjoint_of_forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation kept_of_frame := (DGbigm.kept_of_frame W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation kept_of_frame_hi := (DGbigm.kept_of_frame_hi W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation kept_of_vframe := (DGbigm.kept_of_vframe W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation p_ivs := (DGbigm.p_ivs W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation SKEL_TAIL := DGbigm.SKEL_TAIL.
Local Notation DZONE := (DGbigm.DZONE ly).
Local Notation IZONE := DGbigm.IZONE.
Local Notation tail_facts := (DGbigm.tail_facts W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation MEQ := (DGbigm.MEQ ly regs0 mem0 p).
Local Notation IAL_POST := (DGbigm.IAL_POST W).
Local Notation MEQI := (DGbigm.MEQI W ly regs0 mem0 p).
Local Notation MEQI_frame := (DGbigm.MEQI_frame W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation WIN2 := (DGbigm.WIN2 ly regs0 p).
Local Notation WIN2_WIN := (DGbigm.WIN2_WIN ly regs0 p).
Local Notation WSKEL2 := DGbigm.WSKEL2.
Local Notation WSKEL2_WIN2 := (DGbigm.WSKEL2_WIN2 W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation windows_WIN2 := (DGbigm.windows_WIN2 W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation OBJQ := (DGbigm.OBJQ regs0).
Local Notation MEQJ := (DGbigm.MEQJ W ly regs0 mem0 p).
Local Notation MEQJ_frame := (DGbigm.MEQJ_frame W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation memset_stretch := (DGbigm.memset_stretch W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_img := (DGbigm.notWIN_img W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_shb := (DGbigm.notWIN_shb W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_Thead := (DGbigm.notWIN_Thead W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_C := (DGbigm.notWIN_C W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_NB := (DGbigm.notWIN_NB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation notWIN_SB := (DGbigm.notWIN_SB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY Hp10 Htp Hra Hra4096 Hsp Hsp_al Htrlen Hso Hbp Hinst Hp IMG Hp_al Hnn Hhb1 Hhb1m Hp_static Hp_pres Hqb Hjunk HIAL SEED PBUF0];
unfold kQuarantineMax in Hnn.
Local Notation off_T := (DGbigm.off_T W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation off_C := (DGbigm.off_C W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation off_NB := (DGbigm.off_NB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation off_SB := (DGbigm.off_SB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation off_P := (DGbigm.off_P W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation off_P8 := (DGbigm.off_P8 W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation pres_off_of_frame := (DGbigm.pres_off_of_frame W).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize; tac | apply off_C; tac | apply off_P8; tac | apply off_P; tac
| apply off_NB; unfold kNodesBlockSize; tac | apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Notation at_D1 := (DGbigd.at_D1 W ly regs0 mem0 md0 tr p nn hb1 q j1 j2 j3).
Ltac show_regs HS := lazymatch type of HS with st_ok _ _ ?ss _ => let r := eval vm_compute in (ss_pc ss, ss_regs ss) in idtac r end.
Ltac show_skel HS := lazymatch type of HS with st_ok _ _ ?ss _ => let r := eval vm_compute in (combine (seq 0 (length (ss_mem ss))) (skeleton (ss_mem ss))) in idtac r end.
Ltac show_reg HS i := lazymatch type of HS with st_ok _ _ ?ss _ => let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in idtac r end.
Definition EQ4a (m4 m : word -> option byte) : Prop := forall x : word, ~ WIN2 (bv_unsigned x) -> m x = m4 x.
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
Definition after_D1 (msD : machine_state) (E3 : env) (regs4 : bvmap 5 word) (mem4 : word -> option byte) : Prop :=
msD = mkst (ms_regs msD) (w64 0x74364) (ms_mem msD) (seg_rom tfibsegs) /\
(forall k, (k < aHAVf)%nat -> ew E3 k = ew E0 k) /\
st_ok tfibsegs E3 DGbigw.SS_B (restrict (w_H W) msD) /\
regs_preserved (ms_regs msD) regs4 /\
(forall x : word, ~ (sp0 - 48 - DEP_STK <= bv_unsigned x < sp0 - 48) -> ~ DZONE (bv_unsigned x) -> mem4 x = ms_mem msD x) /\
(forall a, apresent (w_H W) (ms_mem msD) a -> apresent (w_H W) mem4 a) /\
MEQI (ms_mem msD) /\
(forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem msD) a).
Lemma denot_by_zev : forall (E : env) t v, svpure t = true -> 0 <= v < 2 ^ 64 -> zev (rho_of E) t = v -> sv_denot E t = Z_to_bv 64 v.
Proof.
intros E t v Hp Hv Hz. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (sv_denot E t)) with (U E t).
rewrite (U_zev E t Hp), Hz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). symmetry. apply Z.mod_small. exact Hv.
Qed.
(* At QuarantineCallback::Recycle's entry (0x33e88, ra = 0x35ffc), the common state DGbigw.SS_Q of FromPrimary's
   three outcomes. *)
Definition at_RCY (mem4 : word -> option byte) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists (ms : machine_state) mat (E5 : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
ms = mkst (ms_regs ms) (w64 0x33e88) (ms_mem ms) (seg_rom tfibsegs) /\
(forall k, (k < aHAVf)%nat -> ew E5 k = ew E0 k) /\
st_ok tfibsegs E5 DGbigw.SS_Q (restrict (w_H W) ms) /\
EQ4a mem4 (ms_mem ms) /\ (forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |].
(* The close shared by the three outcomes at 0x33e88: x13 forgotten into atom 102, the facts weakened to DGbigw.F_Q,
   the state is DGbigw.SS_Q; the stack below sp0 is present by SS_Q's windows 0 ([-DFSTACK, -48)) and 2 ([-48, 0)). *)
Lemma rcy_close : forall (E : env) ss ms mat mem4,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
ss_atoms_lt 102 ss = true ->
facts_leb DGbigw.F_Q (ss_facts ss) = true ->
set_facts (mkSS (ss_pc ss) (sr_set (ss_regs ss) 13%bv (SOff 102%nat 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) DGbigw.F_Q = DGbigw.SS_Q ->
EQ4a mem4 (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0)) (at_RCY mem4).
Proof.
intros E ss ms mat mem4 HE HS Hlt Hle Heq EQE.
open_FH. destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply (st_ok_forget_reg _ _ _ 13%bv 102) in HS; [| intros X; discriminate | exact Hlt].
apply (st_ok_facts_leb tfibsegs _ _ _ DGbigw.F_Q) in HS; [| exact Hle].
rewrite Heq in HS. clear Heq Hle Hlt.
lazymatch type of HS with st_ok _ ?E' _ _ => set (E6 := E') in HS end.
assert (HE6 : forall k, (k < aHAVf)%nat -> ew E6 k = ew E0 k) by (intros k Hk; subst E6; unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; apply HE; exact Hk).
clearbody E6.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E6 _ _ HS eq_refl) as HshE.
change (ss_pc DGbigw.SS_Q) with 0x33e88 in HshE.
apply SRr_ret. split; [reflexivity|].
exists ms, mat, E6. split; [reflexivity|]. split; [exact HshE|]. split; [exact HE6|]. split; [exact HS|]. split; [exact EQE|].
assert (BV2 : bv_unsigned (ew E6 2) = sp0) by (rewrite (HE6 2%nat ltac:(cbv; zlia)), E2; reflexivity).
intros a Ha. destruct (Z_lt_le_dec a (sp0 - 48)).
- eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; numconst; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; numconst; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
Qed.
Ltac rcy_leaf HE :=
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
apply (rcy_close _ _ _ _ _ HE HS); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | assumption]
end.
Lemma segC_big : forall msD E3 regs4 mem4 mat4, after_D1 msD E3 regs4 mem4 ->
SRr tfibsegs W (mkCfg (mkst regs4 (w64 0x35e1c) mem4 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat4 md0)) (at_RCY mem4).
Proof.
intros msD E3 regs4 mem4 mat4 (HshD & HEn3 & HS & HP4 & Hfr4 & Hpr4 & MEQD0 & PRESD).
open_FH. pose proof Hwx_tfa as Hwx. destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB. pose proof derived_ranges as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
set (XD := fun a : Z => (sp0 - 48 - DEP_STK <= a < sp0 - 48) \/ DZONE a).
assert (Hfr' : forall x : word, ~ XD (bv_unsigned x) -> mem4 x = ms_mem msD x).
{ intros x Hx. subst XD. apply Hfr4; cbn beta in Hx; tauto. }
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?robj :: ?rscr :: ?rest =>
pose proof (st_ok_after_call tfibsegs 86 E3 ss ms0 regs4 (mrestrict (w_H W) mem4) (robj :: trim_lo rscr (-48) :: rest) 0x35e1c HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_trim_lo | apply submem_refl])
ltac:(vm_compute; reflexivity) HP4) as HS1;
let rsv := eval vm_compute in (robj :: trim_lo rscr (-48) :: rest) in
change (robj :: trim_lo rscr (-48) :: rest) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 86 0x35e1c) in
change (ss_after_call ss rsv 86 0x35e1c) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?r2 :: ?r3 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E3 (mrestrict (w_H W) (ms_mem msD)) (mrestrict (w_H W) mem4)) (r0 :: r1 :: r2 :: r3 :: tail));
[ pose proof LYD as (_ & _ & (_ & _ & NBSTK) & (_ & SBSTK) & _); unfold zdisjoint in NBSTK, SBSTK; cbn [fst snd] in NBSTK, SBSTK;
constructor; [|constructor; [|constructor; [|constructor]]];
[ eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn3 13%nat ltac:(cbv; zlia)), E13; subst XD; unfold DGbigm.DZONE; intros a Ha; cbn beta; unfold sp0, SOv in *;
clear - Ha Usp Hlo Hhi LB NBSTK SBSTK Hso; numconst; zlia
| eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn3 2%nat ltac:(cbv; zlia)), E2; subst XD; unfold DGbigm.DZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo Hhi LB NBSTK SBSTK; numconst; zlia
| (* slot (empty extent) *) eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
intros a Ha; cbn beta in Ha; clear - Ha; zlia
| (* slot (empty extent) *) eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
intros a Ha; cbn beta in Ha; clear - Ha; zlia
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts E3 r HEn3 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
eapply (kept_of_frame E3 _ _ XD _ Hfr' Hpr4); intros a Ha; subst XD; unfold DGbigm.DZONE; cbn beta; clear - Ha Y1 Y2 Y3 Y4 Y6; numconst; zlia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES4 : forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W) mem4 a) by (intros a Ha; apply Hpr4, PRESD, Ha).
set (En4 := havoc E3 86 (map (getr regs4) CLOB)) in HS1.
assert (HEn4 : forall k, (k < aHAVf)%nat -> ew En4 k = ew E0 k) by (intros k Hk; subst En4; unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; apply HEn3; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- DFSTACK) (- 48) (- DFSTACK) (- 48) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2;
split; [clear - Usp Hlo LB; numconst; zlia|]; split; [clear - Usp Hlo LB; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Usp Hlo LB Ho; numconst; zlia) | apply PRES4; clear - Ho; numconst; zlia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|[<-|[<-|[<-|Hr']]]];
[ (* object (base aSO, above sp0) *) unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite (HEn4 13%nat ltac:(cbv; zlia)), (HEn4 2%nat ltac:(cbv; zlia)), E13, E2; unfold sp0, SOv in *; clear - Hso Usp; unfold DFSTACK; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold DFSTACK; zlia
| (* slot (was the image region) *) unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold DFSTACK; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold DFSTACK; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En4 r' HEn4 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn4 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold DFSTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (EQ0 : EQ4a mem4 mem4) by (intros x _; reflexivity).
srr_run_to_sh tfibtbl_rtF_ok HS 0x35f3c. eq4a_acc HEn4.
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
(* Put's size test (0x35f7c) is not taken (atom 39 is above kQuarantineMax); the run stops at FromPrimary's lower
   test (0x35f88, DGbigw.SS_P). *)
srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4.
srr_branch_sh tfibtbl_rtF_ok HS.
- (* the chunk below the primary space: DGbigw.SS_Q1 *)
clear Hc. srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4. rcy_leaf HEn4.
- (* at FromPrimary's upper test (0x35f98, DGbigw.SS_P2) *)
clear Hc. srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4.
srr_branch_sh tfibtbl_rtF_ok HS.
+ (* the chunk above the primary space: DGbigw.SS_Q2 *)
clear Hc. srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4. rcy_leaf HEn4.
+ (* the chunk inside the primary space, FillChunk vacuous: DGbigw.SS_Q3 *)
clear Hc. srr_run_sh tfibtbl_rtF_ok HS. eq4a_acc HEn4. rcy_leaf HEn4.
Qed.
End WK.
End b.
