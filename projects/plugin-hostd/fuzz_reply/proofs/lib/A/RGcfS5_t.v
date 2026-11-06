(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from fuzz_preset (commit d0fcb396eeeb); module paths changed and every image numeral moved by symbol + offset to fuzz_reply's asan image A (unstripped fuzz_reply.asan sha256 d751b179ea49, pin 42c58610e125). *)
(* Modified by Theorem Labs, 2026-10-29: copied from the preset unit's lib/A/FSRealloc_S1_t.v (commit 337e6a94485, sha256 0388a364a67d; internal record) for realloc(NULL, n) (segment S5, RGtop's seg_npre), which was relocated from the fuzz_state unit's lib/A/FSRealloc_S1_t.v (commit ddc081c1a03, sha256 93e81e179b96; internal record), a port of the cgif_rgb unit's lib/YF6t.v. *)
(* fuzz_reply.asan image A, realloc(NULL, n) (segment S5, RGtop's seg_npre). segA: the machine walk from A/RGcfS5_u.v's
   seed (a0 = 0) at __wrap_realloc 0x53df0 (`j 0x541ec` -> __interceptor_realloc 0x541ec, frame 0x7f0 + 0x70) to
   Allocator::Allocate's entry 0x31bd8 (at_PA states PAST_topN of A/RGcfS5_pa.v).
   Path: 0x5422c `jal 0xb4d8` -> internal_allocator 0x5f704 (cut by tfib_ialloc_spec; returns to 0x54230); with a0 a
   literal, the PointerIsMine probe 0x54230-0x5424c needs no pins, and the run reads the map word at the literal 0xa72c8
   (A/RGcfS5_r.v R_IMN); the LONG trace branch (GetMallocContextSize 0x5bb78 `auipc a0, 0x4b; lw a0, 0x244(a0)` reads
   malloc_context_size at 0xa6dbc, the REG0 seed cell = A/AF0m.v:98 `z4 (ANum 0xa6dbc) 0x1e`, `bltu a1, a0` 0x542f0
   taken) to `jal 0x2096c` 0x54324 (GetCurrentPc 0x74c90; pc0 = 0x54328) and `jal 0x7808` 0x54380 (UnwindImpl 0x5bb88,
   cut by tfib_unwind_spec; returns to 0x54384); `jal -0x21e34` 0x54394 -> asan_realloc 0x32560 (`beqz a0` 0x32570
   taken -> 0x325b8 .. `jal Allocate` 0x325d4) -> 0x31bd8. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AFeq FSRealloc_S1_tbl FSRealloc_S1_pa RGcfS5_pa RGcfS5_u FSRealloc_S1_r RGcfS5_r.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold IFRAMER, zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAMER, SHADOW_OFF, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variable rn : Z.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variable ii : bool.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x53df0) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 ch ii rn.
Local Notation tr := (RGcfS5_u.tr ly regs0 ch).
Local Notation LENv := (RGcfS5_u.LENv ly regs0 ch).
Local Notation XW := (RGcfS5_u.XW ly regs0 ch).
Local Notation E0 := (RGcfS5_u.E0 ly regs0 ch).
Local Notation Er := (RGcfS5_u.Er ly regs0 ch).
Local Notation E2 := (RGcfS5_u.E2 ly regs0 ch).
Local Notation E1 := (RGcfS5_u.E1 ly regs0 ch).
Local Notation E8 := (RGcfS5_u.E8 ly regs0 ch).
Local Notation E10 := (RGcfS5_u.E10 ly regs0 ch).
Local Notation E4 := (RGcfS5_u.E4 ly regs0 ch).
Local Notation EaT := (RGcfS5_u.EaT ly regs0 ch).
Local Notation EaC := (RGcfS5_u.EaC ly regs0 ch).
Local Notation EaSB := (RGcfS5_u.EaSB ly regs0 ch).
Local Notation EaTOP := (RGcfS5_u.EaTOP ly regs0 ch).
Local Notation EaLEN := (RGcfS5_u.EaLEN ly regs0 ch).
Local Notation E11 := (RGcfS5_u.E11 ly regs0 ch).
Local Notation EaSHB := (RGcfS5_u.EaSHB ly regs0 ch).
Local Notation AL := RGcfS5_u.AL.
Local Notation REG0 := RGcfS5_u.REG0.
Local Notation FFN := RGcfS5_u.FFN.
Local Notation SS0 := RGcfS5_u.SS0.
Local Notation LYB := (RGcfS5_u.LYB W ly regs0 mem0 ch ii rn FH).
Local Notation LYD := (RGcfS5_u.LYD W ly regs0 mem0 ch ii rn FH).
Local Notation iv_vs_stack := (RGcfS5_u.iv_vs_stack W ly regs0 mem0 ch ii rn FH).
Local Notation stack_ivs := (RGcfS5_u.stack_ivs W ly regs0 mem0 ch ii rn FH).
Local Notation WIN := (RGcfS5_u.WIN ly regs0).
Local Notation WSKEL := RGcfS5_u.WSKEL.
Local Notation win_sub := RGcfS5_u.win_sub.
Local Notation win_sub_sound := (RGcfS5_u.win_sub_sound W ly regs0 mem0 ch ii rn FH).
Local Notation WSKEL_WIN := (RGcfS5_u.WSKEL_WIN W ly regs0 mem0 ch ii rn FH).
Local Notation windows_WIN := (RGcfS5_u.windows_WIN W ly regs0 mem0 ch ii rn FH).
Local Notation frame_WIN := (RGcfS5_u.frame_WIN W ly regs0 mem0 ch ii rn FH).
Local Notation WIN_zone := (RGcfS5_u.WIN_zone W ly regs0 mem0 ch ii rn FH).
Local Notation WIN_off := (RGcfS5_u.WIN_off W ly regs0 mem0 ch ii rn FH).
Local Notation WIN_not_high := (RGcfS5_u.WIN_not_high W ly regs0 mem0 ch ii rn FH).
Local Notation all_disjoint_of_forall := (RGcfS5_u.all_disjoint_of_forall W ly regs0 mem0 ch ii rn FH).
Local Notation kept_of_frame := (RGcfS5_u.kept_of_frame W ly regs0 mem0 ch ii rn FH).
Local Notation kept_of_frame_hi := (RGcfS5_u.kept_of_frame_hi W ly regs0 mem0 ch ii rn FH).
Local Notation kept_of_vframe := (RGcfS5_u.kept_of_vframe W ly regs0 mem0 ch ii rn FH).
Local Notation SKEL_TAIL := RGcfS5_u.SKEL_TAIL.
Local Notation IZONE := RGcfS5_u.IZONE.
Local Notation tail_facts := (RGcfS5_u.tail_facts W ly regs0 mem0 ch ii rn FH).
Local Notation MEQ := (RGcfS5_u.MEQ ly regs0 mem0).
Local Notation IAL_POST := (RGcfS5_u.IAL_POST W).
Local Notation MEQI := (RGcfS5_u.MEQI W ly regs0 mem0).
Local Notation MEQI_frame := (RGcfS5_u.MEQI_frame W ly regs0 mem0 ch ii rn FH).
Local Notation notWIN_img := (RGcfS5_u.notWIN_img W ly regs0 mem0 ch ii rn FH).
Local Notation notWIN_shb := (RGcfS5_u.notWIN_shb W ly regs0 mem0 ch ii rn FH).
Local Notation notWIN_Thead := (RGcfS5_u.notWIN_Thead W ly regs0 mem0 ch ii rn FH).
Local Notation notWIN_C := (RGcfS5_u.notWIN_C W ly regs0 mem0 ch ii rn FH).
Local Notation notWIN_NB := (RGcfS5_u.notWIN_NB W ly regs0 mem0 ch ii rn FH).
Local Notation notWIN_SB := (RGcfS5_u.notWIN_SB W ly regs0 mem0 ch ii rn FH).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Hp10 Hn11 Hn Htp Hra Hra4096 Hsp Hsp_al Hch HIAL IA1 U1 SEED].
Local Notation off_T := (RGcfS5_u.off_T W ly regs0 mem0 ch ii rn FH).
Local Notation off_C := (RGcfS5_u.off_C W ly regs0 mem0 ch ii rn FH).
Local Notation off_NB := (RGcfS5_u.off_NB W ly regs0 mem0 ch ii rn FH).
Local Notation off_SB := (RGcfS5_u.off_SB W ly regs0 mem0 ch ii rn FH).
Local Notation pres_off_of_frame := (RGcfS5_u.pres_off_of_frame W).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize; tac | apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac | apply off_SB; unfold kStoreBlockSize; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Definition at_PA (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x31bd8) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
PAST_topN regs0 LENv (w_H W) regs' mem' /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 2120 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
MEQI mem' /\
val_mem tfibsegs (mrestrict (w_H W) mem') (T + t_unwinding) 1 0 /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem' a).
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
Lemma segA : SRr tfibsegs W cfg0 at_PA.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS.
destruct Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
srr_run_to_sh tfibtbl_rr_ok HS 0x5f704.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape. rewrite Hshape.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2.
eapply SRr_bind.
{ destruct HIAL as (IA & IB & IC & ID).
assert (FR : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ms_mem ms (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha. apply HF. intros Hw.
lazymatch type of Hw with in_wrange _ ?rs _ =>
pose proof (WIN_zone _ (windows_WIN E0 rs _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw)) as (X & _) end.
rewrite unsigned_lit_small in X by (unfold TFIB_IMG_LO, TFIB_IMG_END in Ha; zlia). exact (X Ha). }
apply (IA1 W (ms_regs ms) (ms_mem ms) _ ii).
- rreg HS (1%bv : bv 5) R1; rewrite R1. apply YK0s.ret_ok_even. reflexivity.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; zlia).
replace (bv_unsigned (getr regs0 2) + -2144) with (bv_unsigned (getr regs0 2) + (-134) * 16) by zlia. rewrite Z_mod_plus_full. exact Hsp_al.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; zlia). numconst; zlia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; zlia). numconst; zlia.
- intros a Ha. rewrite R2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (numconst; zlia).
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; numconst; zlia
| off_by ltac:(numconst; zlia) ].
- eapply val_mem_frame; [|exact IA]. intros k Hk. apply FR; numconst; zlia.
- eapply val_mem_frame; [|exact IB]. intros k Hk. apply FR; numconst; zlia.
- memv HS 21%nat 0%nat; [reflexivity | reflexivity | zlia].
- memv HS 22%nat 0%nat; [reflexivity | reflexivity | zlia].
- destruct ii; destruct IC as [IC1 IC2]; split; (eapply val_mem_frame; [|eassumption]); intros k Hk; apply FR; numconst; zlia.
- intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) mem0 (ms_mem ms) a) by (apply FR; numconst; zlia). apply ID. exact Ha. }
intros W' c' Hle (-> & regs1 & mem1 & mat1 & -> & HP & H10r & Hfr & Hpr & IV1 & IV2 & IV3 & IV4 & IV5). srr_norm_model.
rreg HS (1%bv : bv 5) R1.
set (X1 := fun a : Z => (sp0 - 2192 <= a < sp0 - 2144) \/ IZONE a).
assert (Hfr' : forall x : word, ~ X1 (bv_unsigned x) -> mem1 x = ms_mem ms x).
{ intros x Hx. subst X1. unfold IZONE in Hx. rewrite R2 in Hfr. unfold w64 in Hfr. rewrite unsigned_lit_small in Hfr by (numconst; zlia).
apply Hfr; unfold IAL_STK in *; tauto || (intros HH; apply Hx; tauto) || zlia. }
jafter_call2 HS 54%nat regs1 (mrestrict (w_H W) mem1) HP (-2144) (seq 0 36) HS1.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E0 (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1)) (r0 :: tail));
[ constructor;
[ eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:(subst X1; unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; zlia) Hpr)); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite E2; subst X1; unfold IZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; zlia
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts E0 r (fun k _ => eq_refl) Hr) as (Y1 & Y2 & Y3 & Y4 & Y5);
eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:(subst X1; unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; zlia) Hpr)); intros a Ha; subst X1; unfold IZONE; cbn beta; clear - Ha Y1 Y2 Y3 Y4 Y5; numconst; zlia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a).
{ intros a Ha. apply Hpr; [clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia|]. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; numconst; zlia | off_by ltac:(numconst; zlia) ]. }
set (En1 := havoc E0 54 (map (getr regs1) CLOB)) in HS1.
assert (HEn1 : forall k, (k < aHAVf)%nat -> ew En1 k = ew E0 k) by (intros k Hk; subst En1; apply ew_havoc_old; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAMER) (- ASTACK) (- IFRAMER) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold IFRAMER;
split; [numconst; zlia|]; split; [numconst; zlia|]; split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(numconst; zlia) | apply PRES1; numconst; zlia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|Hr'];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAMER; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold IFRAMER, ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_add_region _ _ _ R_IMN) in HS1;
[ | reflexivity
| unfold R_IMN, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
split; [zlia|]; split; [zlia|]; split; [intros o Ho; zlia|];
apply Forall_cons; [|apply Forall_nil]; intros i Hi; cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len YP09.cbyte] in Hi |- *;
exists (Z_to_bv 8 0); split; [reflexivity|]; apply IV5; clear - Hi; numconst; zlia
| unfold R_IMN; apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2;
clear - Usp Hlo LB; numconst; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2;
clear - Usp Hlo LB; numconst; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; clear - Y5; numconst; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_pin_reg _ _ _ 10%bv (SLit TFIB_IAL_LO)) in HS1; [| intros X; discriminate | cbn [sv_denot ms_regs]; symmetry; exact H10r].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. rewrite R1. clear HS. rename HS1 into HS.
assert (MEQ1 : MEQI mem1).
{ split.
- intros x Hx Hz. rewrite Hfr' by (subst X1; cbn beta; intros [HH|HH]; [apply Hx; left; unfold ASTACK; zlia | exact (Hz HH)]).
apply HF. intros Hw. apply Hx. exact (windows_WIN E0 (ss_mem SS0) _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw).
- exact (conj IV1 (conj IV2 (conj IV3 (conj IV4 IV5)))). }
clear HF HFr Hfr Hfr'.
srr_run_to_sh tfibtbl_rr_ok HS 0x5bb88. meq_acc HEn1.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msU end.
match goal with M : MEQI (ms_mem msU) |- _ => rename M into MEQU end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En1 _ _ HS eq_refl) as Hshape2; cbn [ss_pc] in Hshape2. rewrite Hshape2.
rreg HS (2%bv : bv 5) Q2. rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2 in Q2.
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msU) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAMER)).
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; numconst; zlia | off_by ltac:(numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; numconst; zlia | off_by ltac:(numconst; zlia) ]. }
eapply SRr_bind.
{ apply (U1 W ly (ms_regs msU) (ms_mem msU) _ (sp0 - 2136) 0x54328 sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
1:{ rreg HS (10%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)), E2. unfold sp0. f_equal; zlia. }
1:{ rreg HS (11%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (12%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)), E2. unfold sp0. symmetry. apply Z_to_bv_bv_unsigned. }
1:{ rreg HS (13%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (14%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (15%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (4%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (1%bv : bv 5) R; rewrite R. apply YK0s.ret_ok_even. reflexivity. }
1:{ zlia. }
1:{ memv HS 3%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 7%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 8%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 28%nat 0%nat; [reflexivity | reflexivity | unfold TFIB_TSD; zlia]. }
1:{ memv HS 29%nat 0%nat; [reflexivity | cbn [sv_denot]; rewrite (HEn1 33%nat ltac:(cbv; zlia)), EaC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 30%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 33%nat ltac:(cbv; zlia)), EaC; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 31%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia | reflexivity | zlia]. }
1:{ memv HS 31%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn1 35%nat ltac:(cbv; zlia)), EaTOP; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 31%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn1 35%nat ltac:(cbv; zlia)), EaTOP; unfold w64, ly_bot, kStackSpan; rewrite Zbv_add_unsigned; f_equal; zlia
| unfold ly_bot, kStackSpan; clear - LB; numconst; zlia]. }
1:{ memv HS 32%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); unfold t_unwinding; zlia | reflexivity | zlia]. }
1:{ eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 32 _ _ HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); numconst; zlia | off_by ltac:(clear - LB; numconst; zlia) ]. }
1:{ memv HS 23%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 24%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia).
replace (bv_unsigned (getr regs0 2) + -2144) with (bv_unsigned (getr regs0 2) + (-134) * 16) by zlia. rewrite Z_mod_plus_full. exact Hsp_al. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia). clear - Hlo LB; numconst; zlia. }
1:{ intros a Ha. rewrite Q2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - Usp Hlo LB; numconst; zlia). apply PRES2. clear - Ha; numconst; zlia. }
1:{ unfold sp0. replace (bv_unsigned (getr regs0 2) - 2136) with (bv_unsigned (getr regs0 2) + (- 267) * 8) by zlia.
rewrite Z_mod_plus_full. apply (mod0_factor _ 8 2); [zlia | exact Hsp_al]. }
1:{ clear - Hlo LB; numconst; zlia. }
1:{ right. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia). zlia. }
1:{ intros a Ha. apply PRES2. clear - Ha; numconst; zlia. }
1:{ clear; numconst; zlia. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; zlia). zlia. }
1:{ exact Hbot. }
1:{ exact Hhi. }
1:{ apply (mod0_factor _ 8 2); [zlia | exact Hsp_al]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 2%nat 10%nat;
[cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia | cbn [sv_denot]; rewrite (HEn1 1%nat ltac:(cbv; zlia)), E1, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 2%nat 9%nat;
[cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia | cbn [sv_denot]; rewrite (HEn1 8%nat ltac:(cbv; zlia)), E8, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ exact Hra4096. }
fold sp0 in Hch. destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|exact Hch].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:Hb; [exact Hch|].
destruct Hch as [H16 Hfp]. split; [exact H16|].
apply Z.ltb_lt in Hf0.
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
eapply fpchain_ext2; [exact Hfp | zlia |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|exact Hva]. intros i Hi. apply aview_same.
apply (proj1 MEQU (Z_to_bv 64 (a + i))); rewrite unsigned_lit_small by (clear - Ha1 Ha2 H16 Hi Usp LB; numconst; zlia).
- apply WIN_not_high. zlia.
- intros Hz. clear - Hz H16 Ha1 Hi LB Hlo. unfold RGcfS5_u.IZONE in Hz. numconst. zlia. }
clear Hle. intros W' c' Hle (-> & regs2 & mem2 & mat2 & -> & HP2 & Hfr2 & Hpr2 & Ht1 & Ht2 & Ht3). srr_norm_model.
rreg HS (1%bv : bv 5) Q1. rewrite Q1. clear Q1.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem2 x = ms_mem msU x).
{ intros x Hx. rewrite Q2 in Hfr2. unfold w64, BST_SIZE in Hfr2. rewrite unsigned_lit_small in Hfr2 by (clear - Usp Hlo LB; numconst; zlia).
apply Hfr2; clear - Hx; unfold ASTACK, UNW_STK in *; zlia. }
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?rim :: ?rscr :: ?rfr :: ?rest =>
pose proof (st_ok_after_call tfibsegs 70 En1 ss ms0 regs2 (mrestrict (w_H W) mem2) (rim :: trim_lo rfr (-64) :: rest) 0x54384 HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl|]; apply submem_drop; apply submem_keep; [apply subregion_trim_lo | apply submem_refl])
ltac:(vm_compute; reflexivity) HP2) as HS1;
let rsv := eval vm_compute in (rim :: trim_lo rfr (-64) :: rest) in
change (rim :: trim_lo rfr (-64) :: rest) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 70 0x54384) in
change (ss_after_call ss rsv 70 0x54384) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs En1 (mrestrict (w_H W) (ms_mem msU)) (mrestrict (w_H W) mem2)) (r0 :: r1 :: tail));
[ constructor; [|constructor];
[ eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
intros a Ha; cbn beta; clear - Ha Hlo LB Usp; numconst; zlia
| eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; zlia
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts En1 r HEn1 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5);
eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); intros a Ha; cbn beta; clear - Ha Y1 Y2 Y3 Y4; numconst; zlia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (HL : 1 <= LENv <= 30).
{ pose proof (unwind_of_chain_length 0x54328 ((sp0, bv_unsigned (getr regs0 1), bv_unsigned (getr regs0 8)) :: ch)) as LEN.
unfold RGcfS5_u.LENv, RGcfS5_u.tr, call_trace, frame0_ok, spZ, raZ, s0Z. fold sp0. destruct (sp0 + 16 <? ly_top ly); cbn [length]; zlia. }
pose proof Hfr2 as Hfr2n. rewrite Q2 in Hfr2n. unfold w64, BST_SIZE in Hfr2n. rewrite unsigned_lit_small in Hfr2n by (clear - Usp Hlo LB; numconst; zlia).
assert (OBJ0 : val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 2136) 8 (sp0 - 2120)).
{ eapply val_mem_frame; [intros k Hk; apply Hfr2n; rewrite unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; zlia); clear - Hk; numconst; unfold sp0; zlia|].
memv HS 2%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; f_equal; unfold sp0; zlia | clear - Usp Hlo LB; numconst; zlia]. }
assert (OBJ1 : val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 2128) 8 LENv).
{ replace (RGcfS5_u.LENv ly regs0 ch) with (LENv + 2 ^ 32 * 0) by zlia.
apply val_mem_4_4; [zlia | zlia | |].
- eapply val_mem_addr; [exact Ht1 | zlia].
- assert (Z8 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msU)) (sp0 - 2128) 8 0).
{ memv HS 2%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia | reflexivity | zlia]. }
assert (Z4 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msU)) (sp0 - 2128 + 4) 4 0).
{ intros k Hk. replace (sp0 - 2128 + 4 + Z.of_nat k) with (sp0 - 2128 + Z.of_nat (4 + k)) by zlia.
rewrite (Z8 (4 + k)%nat ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
eapply val_mem_frame; [intros k Hk; apply Hfr2n; rewrite unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; zlia); clear - Hk; numconst; unfold sp0; zlia| exact Z4]. }
assert (PRES3 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a) by (intros a Ha; apply Hpr2, PRES2, Ha).
set (En2 := havoc En1 70 (map (getr regs2) CLOB)) in HS1.
assert (HEn2 : forall k, (k < aHAVf)%nat -> ew En2 k = ew E0 k) by (intros k Hk; subst En2; unfold aHAVf in Hk; rewrite ew_havoc_old by zlia; apply HEn1; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAMER) (- ASTACK) (- IFRAMER) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; unfold IFRAMER;
split; [clear - Usp Hlo LB; numconst; zlia|]; split; [clear - Usp Hlo LB; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Usp Hlo LB Ho; numconst; zlia) | apply PRES3; clear - Ho; numconst; zlia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2;
clear - Usp Hlo LB; numconst; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAMER; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En2 r' HEn2 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold IFRAMER, ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_add_region _ _ _ R_OBJR) in HS1;
[ | reflexivity
| unfold R_OBJR, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2;
split; [clear - Usp Hlo LB; numconst; zlia|]; split; [clear - Usp Hlo LB; numconst; zlia|]; split; [intros o Ho; zlia |];
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
[ eapply (chunk_ok_val tfibsegs En2 _ _ (-2136) 8 (SOff 2 (-2120)) (sp0 - 2120));
[cbn [sv_denot]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; f_equal; unfold sp0; zlia | clear - Usp Hlo LB; numconst; zlia | cbn; zlia
| eapply val_mem_addr; [exact OBJ0 | unfold sp0; zlia]]
| eapply (chunk_ok_val tfibsegs En2 _ _ (-2128) 8 (SOff 36%nat 0) LENv);
[cbn [sv_denot]; rewrite (HEn2 36%nat ltac:(cbv; zlia)), EaLEN; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HL; zlia
| cbn; zlia | eapply val_mem_addr; [exact OBJ1 | unfold sp0; zlia]] ]
| unfold R_OBJR; apply all_disjoint_of_forall; intros r' [<-|[<-|[<-|Hr']]];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAMER, ASTACK; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2;
clear - Usp Hlo LB; numconst; zlia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En2 r' HEn2 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold ASTACK in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (MEQ2 : MEQI mem2).
{ destruct MEQU as [M I]. assert (LOWEQ : forall a, a < sp0 - ASTACK -> 0 <= a -> mem2 (Z_to_bv 64 a) = ms_mem msU (Z_to_bv 64 a)).
{ intros a Ha Ha'. apply Hfr'. rewrite unsigned_lit_small by (clear - Ha Ha' Usp; unfold ASTACK in *; zlia). zlia. }
split.
- intros x Hx Hz. rewrite <- (M x Hx Hz). apply Hfr'. intros HH. apply Hx. left. unfold ASTACK in *. zlia.
- destruct I as (I1 & I2 & I3 & I4 & I5). unfold RGcfS5_u.IAL_POST.
repeat match goal with |- _ /\ _ => split end;
try (eapply val_mem_frame; [|eassumption]; intros k Hk; apply LOWEQ; clear - Hk Hlo LB; numconst; zlia).
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) (ms_mem msU) mem2 a) by (apply LOWEQ; clear - Ha Hlo LB; numconst; zlia). apply I5. exact Ha. }
clear MEQU.
srr_run_to_sh tfibtbl_rr_ok HS 0x31bd8. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
lazymatch type of HF with frame_of _ ?rs _ _ =>
pose proof (MEQI_frame En2 rs _ _ HEn2 ltac:(vm_compute; reflexivity) HF MEQ2) as MEQR end.
assert (FRR : forall y : word, ~ (sp0 - ASTACK <= bv_unsigned y < sp0 - IFRAMER) -> ~ (sp0 - 64 <= bv_unsigned y < sp0) ->
~ (T + t_unwinding <= bv_unsigned y < T + t_unwinding + 1) -> ms_mem msR y = mem2 y).
{ intros y Y1 Y2 Y3. apply HF. intros Hw. destruct (in_wrange_windows En2 _ _ Hw) as (b & lo & hi & Hin & Hr).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hr;
rewrite ?(HEn2 2%nat ltac:(cbv; zlia)), ?E2, ?(HEn2 32%nat ltac:(cbv; zlia)), ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by (clear - LB; numconst; zlia);
clear - Y1 Y2 Y3 Hr; unfold IFRAMER, ASTACK, t_unwinding in *; unfold sp0, T in *; zlia |]).
destruct Hin. }
clear HF.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En2 _ _ HS eq_refl) as HshapeR; cbn [ss_pc] in HshapeR. rewrite HshapeR.
apply SRr_ret. split; [reflexivity|]. eexists (ms_regs msR), (ms_mem msR), _. split; [reflexivity|].
assert (EDn : ed En2 = ed E0) by (subst En2 En1; rewrite !ed_havoc; reflexivity).
pose proof (pachkN_ok aHAVf XW regs0 E0 En2 (w_H W) _ msR ltac:(cbv; zlia) HS eq_refl HEn2 EDn ltac:(vm_compute; reflexivity)) as (HLn & HRg & HFm).
split. { split; [|split; [exact HRg | exact HFm]]. rewrite EaLEN in HLn. unfold w64 in HLn. rewrite unsigned_lit_small in HLn by (clear - HL; zlia). exact HLn. }
split. { intros i Hi. eapply val_mem_frame; [|eapply val_mem_addr; [exact (Ht2 i Hi) | clear; zlia]]. intros k Hk. apply FRR;
rewrite unsigned_lit_small by (clear - Hi Hk HL Usp Hlo LB; unfold RGcfS5_u.LENv in HL; numconst; zlia);
[ clear - Hi Hk HL; unfold RGcfS5_u.LENv in HL; numconst; zlia | clear - Hi Hk HL; unfold RGcfS5_u.LENv in HL; zlia
| pose proof stack_ivs as (IT & _); clear - Hi Hk HL IT Hlo; unfold RGcfS5_u.LENv in HL; numconst; unfold sp0, T in *; zlia ]. }
split; [exact MEQR|].
split. { memv HS 33%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); unfold t_unwinding; zlia | reflexivity | zlia]. }
intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAMER)); [|destruct (Z_lt_le_dec a (sp0 - 64))].
- eapply (st_ok_window_apresent_off (w_H W) En2 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; clear - Ha l; numconst; unfold sp0; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ].
- apply (apresent_same (w_H W) mem2); [|apply PRES3; exact Ha].
apply FRR; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia);
[clear - Ha l; numconst; zlia | clear - Ha l0; zlia | pose proof stack_ivs as (IT & _); clear - Ha IT; numconst; unfold sp0, T in *; zlia].
- eapply (st_ok_window_apresent_off (w_H W) En2 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn2 2%nat ltac:(cbv; zlia)), E2; clear - Ha l0; numconst; unfold sp0; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ].
Qed.
End WK.
End c.
