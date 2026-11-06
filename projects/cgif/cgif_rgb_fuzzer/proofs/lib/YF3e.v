(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF36.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFX_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFX_TP, TFX_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax, YFRAME in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x33b38 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9.
Local Notation XW := (YF36.XW sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation E0 := (YF36.E0 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation Er := (YF36.Er regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation E2 := (YF36.E2 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation E1 := (YF36.E1 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqSZ := (YF36.EqSZ regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqRA := (YF36.EqRA regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS0 := (YF36.EqS0 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS1 := (YF36.EqS1 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS2 := (YF36.EqS2 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS3 := (YF36.EqS3 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS4 := (YF36.EqS4 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS5 := (YF36.EqS5 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS6 := (YF36.EqS6 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS7 := (YF36.EqS7 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS8 := (YF36.EqS8 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation EqS9 := (YF36.EqS9 regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation R_STK := YF36.R_STK.
Local Notation REG0 := YF36.REG0.
Local Notation FFQ := YF36.FFQ.
Local Notation SR0 := YF36.SR0.
Local Notation SS0 := YF36.SS0.
Local Notation LYB := (YF36.LYB W ly regs0 mem0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 FH).
Local Notation derived_ranges := (YF36.derived_ranges W ly regs0 mem0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 FH).
Local Notation WIN := YF36.WIN.
Local Notation win_sub := YF36.win_sub.
Local Notation win_sub_sound := (YF36.win_sub_sound ly regs0).
Local Notation WSK0 := YF36.WSK0.
Local Notation sk_ok := YF36.sk_ok.
Local Notation WSK0_ok := (YF36.WSK0_ok regs0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation windows_WIN := (YF36.windows_WIN ly regs0).
Local Notation MEQ := (YF36.MEQ mem0).
Local Notation MEQ_frame := (YF36.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (YF36.MEQ_0 mem0).
Local Notation MEQ_all := (YF36.MEQ_all mem0).
Local Notation SREGS := YF36.SREGS.
Local Notation at_O := (YF36.at_O W regs0 mem0 md0 sz).
Local Notation SREGS_X := YF36.SREGS_X.
Local Notation at_RETQ := (YF36.at_RETQ W regs0 mem0 md0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Local Notation postQ := (YF36.postQ W regs0 mem0 md0 sz vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hsp Hsp_al Hpres Hregs Hra Hsz Hvals SEED].
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(img_try ((img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by img_refl; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by img_lia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := img_ev (2 ^ k) in img_change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac uncond HS := unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := img_ev (ss_pc ss) in idtac "PC" pc;
let r := img_ev (sym_step_sh tfxsegs tfxtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Ltac reg_atomv HS r EQ := let Q := fresh "Q" in rreg HS r Q; rewrite Q; cbn [sv_denot]; rewrite EQ; unfold w64; rewrite ?Zbv_add_unsigned; first [ img_refl | f_equal; img_lia ].
Lemma segYQ : SRr tfxsegs W cfg0 postQ.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi].
pose proof derived_ranges as (dK1 & dK2 & dSZ).
evalS HS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R46 : rho_of E0 46%nat = sz) by (img_try (unfold rho_of; rewrite EqSZ; unfold w64; img_apply unsigned_lit_small; clear - dSZ; img_lia)).
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfxtbl_rtG_ok HS.
-
assert (HNZ : sz <> 0).
{ lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R46 dSZ; zbranch Hbr; apply Bool.negb_true_iff in Hbr; apply Z.eqb_neq in Hbr; img_lia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
srr_run_to_sh tfxtbl_rtG_ok HS (0x33ab4 + D_150). meq_acc SK0.
unfold YF36.postQ. replace (sz =? 0) with false by (img_try (symmetry; img_apply Z.eqb_neq; img_exact HNZ)).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
assert (MM : ms_mem msx = mem0) by (img_try (img_apply functional_extensionality; intros x; img_exact (MEQ_all _ MQ x)));
img_apply SRr_ret; split; [img_refl|]; split; [img_try (img_exact HNZ)|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), mt end;
split; [img_try (rewrite HshR at 1; rewrite MM; img_refl)|] end.
split. { reg_entry HS (2%bv : bv 5) 2%nat. }
split. { intros r Hr; cbn [YF36.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
- reg_entry HS (3%bv : bv 5) 3%nat.
- let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; img_refl.
- let Q := fresh "Q" in rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; destruct Hregs as (R8 & _); rewrite R8; unfold w64; f_equal; unfold sp0; numconst; img_lia.
- let Q := fresh "Q" in rreg HS (9%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); rewrite R9; img_refl.
- let Q := fresh "Q" in rreg HS (18%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & R18 & _); rewrite R18; img_refl.
- let Q := fresh "Q" in rreg HS (19%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & R19 & _); rewrite R19; img_refl.
- let Q := fresh "Q" in rreg HS (21%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & R21); rewrite R21; img_refl.
- reg_entry HS (26%bv : bv 5) 26%nat.
- reg_entry HS (27%bv : bv 5) 27%nat. }
reg_atomv HS (10%bv : bv 5) constr:(EqSZ).
-
assert (HZ : sz = 0).
{ lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R46 dSZ; zbranch Hbr; apply Bool.negb_false_iff in Hbr; apply Z.eqb_eq in Hbr; img_lia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SK0.
unfold YF36.postQ. replace (sz =? 0) with true by (img_try (symmetry; img_apply Z.eqb_eq; img_exact HZ)).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfxsegs tfxtbl_rtG tfxtbl_rtG_ok Hwx W E0); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. split; [img_refl|]. split; [img_try (img_exact HZ)|]. exists (ms_regs msR), mat'.
rreg HS (1%bv : bv 5) Q1.
assert (MM : ms_mem msR = mem0).
{ img_apply functional_extensionality. intros x. img_exact (MEQ_all _ MQ x). }
assert (RA : getr (ms_regs msR) 1 = w64 vra) by (img_try (rewrite Q1; first [img_exact EqRA | cbn [sv_denot]; rewrite EqRA; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; img_refl])).
split. { rewrite RA, MM. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split. { let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; numconst; img_lia. }
split. { img_exact RA. }
split. { reg_atomv HS (8%bv : bv 5) constr:(EqS0). }
split. { reg_atomv HS (9%bv : bv 5) constr:(EqS1). }
split. { reg_atomv HS (18%bv : bv 5) constr:(EqS2). }
split. { reg_atomv HS (19%bv : bv 5) constr:(EqS3). }
split. { reg_atomv HS (20%bv : bv 5) constr:(EqS4). }
split. { reg_atomv HS (21%bv : bv 5) constr:(EqS5). }
split. { reg_atomv HS (22%bv : bv 5) constr:(EqS6). }
split. { reg_atomv HS (23%bv : bv 5) constr:(EqS7). }
split. { reg_atomv HS (24%bv : bv 5) constr:(EqS8). }
split. { reg_atomv HS (25%bv : bv 5) constr:(EqS9). }
intros r Hr. cbn [YF36.SREGS_X In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
first [ reg_entry HS (3%bv : bv 5) 3%nat | let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q, Htp; img_refl
| reg_entry HS (26%bv : bv 5) 26%nat | reg_entry HS (27%bv : bv 5) 27%nat ].
Qed.
End WK.
End a.
