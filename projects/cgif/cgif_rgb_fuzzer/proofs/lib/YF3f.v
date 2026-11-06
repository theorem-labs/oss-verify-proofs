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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF37.
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
Variables (b bc hi i : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x33b00 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 b bc hi i.
Local Notation S7v := (YF37.S7v b i).
Local Notation XW := (YF37.XW ly b bc hi i).
Local Notation E0 := (YF37.E0 ly regs0 b bc hi i).
Local Notation Er := (YF37.Er ly regs0 b bc hi i).
Local Notation E2 := (YF37.E2 ly regs0 b bc hi i).
Local Notation E1 := (YF37.E1 ly regs0 b bc hi i).
Local Notation EqT := (YF37.EqT ly regs0 b bc hi i).
Local Notation EqSB := (YF37.EqSB ly regs0 b bc hi i).
Local Notation EqB := (YF37.EqB ly regs0 b bc hi i).
Local Notation EqBC := (YF37.EqBC ly regs0 b bc hi i).
Local Notation EqHI := (YF37.EqHI ly regs0 b bc hi i).
Local Notation EqS7 := (YF37.EqS7 ly regs0 b bc hi i).
Local Notation EqI := (YF37.EqI ly regs0 b bc hi i).
Local Notation R_STK := YF37.R_STK.
Local Notation REG0 := YF37.REG0.
Local Notation R_SLOT := YF37.R_SLOT.
Local Notation FFY := YF37.FFY.
Local Notation SR0 := YF37.SR0.
Local Notation SS0 := YF37.SS0.
Local Notation LYB := (YF37.LYB W ly regs0 mem0 b bc hi i FH).
Local Notation derived_ranges := (YF37.derived_ranges W ly regs0 mem0 b bc hi i FH).
Local Notation WIN := YF37.WIN.
Local Notation win_sub := YF37.win_sub.
Local Notation win_sub_sound := (YF37.win_sub_sound ly regs0).
Local Notation WSK0 := YF37.WSK0.
Local Notation sk_ok := YF37.sk_ok.
Local Notation WSK0_ok := (YF37.WSK0_ok ly regs0 b bc hi i).
Local Notation windows_WIN := (YF37.windows_WIN ly regs0).
Local Notation MEQ := (YF37.MEQ mem0).
Local Notation MEQ_frame := (YF37.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (YF37.MEQ_0 mem0).
Local Notation SREGS := YF37.SREGS.
Local Notation at_RCi := (YF37.at_RCi W regs0 mem0 md0 b bc hi i).
Local Notation at_CD24 := (YF37.at_CD24 W ly regs0 mem0 md0 b bc i).
Local Notation postR := (YF37.postR W ly regs0 mem0 md0 b bc hi i).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hsp Hsp_al Hpres Hregs Hcb Hsb Hb Hi Hslot Hhi0 SEED].
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
img_apply U_eq_by_zev; [img_refl | img_refl |].
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
Ltac unpin HS := cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := img_ev (ss_pc ss) in idtac "PC" pc;
let r := img_ev (sym_step_sh tfxsegs tfxtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Definition A2T : sv := SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff 34%nat 0) (SLit 2475880078570760549664030720)) (SAlu ALU_SLL (SOff 40%nat 0) (SLit 27))) (SLit 59).
Lemma A2_val : forall (rho : nat -> Z) sb p cc rel, rho 34%nat = sb -> rho 40%nat = p -> p - sb = cc * 2 ^ 32 + rel -> 0 <= rel < 2 ^ 32 -> 0 <= cc < 32 ->
0 <= sb -> sb <= p < 2 ^ 64 -> zev rho A2T = cc.
Proof.
intros rho sb p cc rel H34 H40 Hd Hrel Hcc Hsb Hp. unfold A2T. cbn [zev zalu_raw zmd_raw]. rewrite H34, H40, !Z.add_0_r.
img_change (Z.land (zcanon 27) 63) with 27. img_change (Z.land (zcanon 59) 63) with 59.
rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by img_lia.
img_change (zcanon 2475880078570760549664030720) with (2 ^ 64 - 2 ^ 27).
unfold zcanon, M64. img_change (2 ^ 64) with 18446744073709551616. img_change (2 ^ 27) with 134217728. img_change (2 ^ 59) with 576460752303423488.
img_change (2 ^ 32) with 4294967296 in *. img_lia.
Qed.
Lemma segYR : SRr tfxsegs W cfg0 postR.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof DR as (dS1 & dS2 & dSal & dB1 & dB2 & dBal & dI & dBC & dHI & dS7 & dT1 & dT2 & dK1 & dK2).
evalS HS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (R34 : rho_of E0 34%nat = SB) by (img_try (unfold rho_of; rewrite EqSB; unfold w64; img_apply unsigned_lit_small; clear - dS1 dS2; numconst; img_lia)).
assert (R40 : rho_of E0 40%nat = b) by (img_try (unfold rho_of; rewrite EqB; unfold w64; img_apply unsigned_lit_small; clear - dS1 dS2 dB1 dB2; numconst; img_lia)).
assert (R43 : rho_of E0 43%nat = bc) by (img_try (unfold rho_of; rewrite EqBC; unfold w64; img_apply unsigned_lit_small; clear - dI dBC; numconst; img_lia)).
assert (R45 : rho_of E0 45%nat = S7v) by (img_try (unfold rho_of; rewrite EqS7; unfold w64; img_apply unsigned_lit_small; clear - dS1 dS2 dB1 dB2 dS7 dI dBC; numconst; img_lia)).
assert (R52 : rho_of E0 52%nat = i) by (img_try (unfold rho_of; rewrite EqI; unfold w64; img_apply unsigned_lit_small; clear - dI dBC; numconst; img_lia)).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite E2; img_refl)).
assert (BV45 : bv_unsigned (ew E0 45) = S7v) by img_exact R45.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfxtbl_rtG_ok HS.
-
assert (HLT : i < bc).
{ lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R52 R43 dI dBC; zbranch Hbr; apply Bool.negb_true_iff in Hbr; apply Z.eqb_neq in Hbr; img_lia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear Hbr end. uncond HS.
destruct (Hslot HLT) as (Vhi & Phi & H1 & H2 & H3).
apply (st_ok_add_region _ _ _ R_SLOT) in HS;
[ | img_refl
| unfold YF37.R_SLOT, YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict]; rewrite BV45;
split; [img_try (clear - dS1 dS2 dB1 dB2 dS7 dI dBC; numconst; img_lia)|]; split; [img_try (clear - dS1 dS2 dB1 dB2 dS7 dI dBC; numconst; img_lia)|];
split; [img_try (intros o Ho; img_lia)|];
img_apply Forall_cons; [|img_try (img_apply Forall_nil)];
eapply chunk_ok_val; [img_try (cbn [sv_denot]; rewrite EqHI; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; img_refl) | img_try (clear - dHI; cbn; numconst; img_lia) | img_try (cbn; img_lia) |];
lazymatch goal with M : MEQ ?mm |- val_mem _ (mrestrict _ ?mm) _ _ _ => eapply val_mem_frame; [img_try (intros kk Hkk; img_apply M; intros []) | img_try (eapply val_mem_addr; [img_exact Vhi | unfold YF37.S7v; img_lia])] end
| unfold YF37.R_SLOT; cbn [YQ0b.all_disjoint ss_mem]; unfold YQ0b.extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?BV2, ?BV45;
unfold YF37.S7v in *; pose proof LB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & _); clear - L1 L2 L3 L4 L5 L6 L7 dS1 dS2 dB1 dB2 dI dBC dK1 dK2 Hlo Hhi; try unfold SB in *; try unfold sp0 in *; numconst; repeat split; img_lia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
srr_run_to_sh tfxtbl_rtG_ok HS (0x33b74 + D_150). meq_acc SK0.
unfold YF37.postR. replace (i <? bc) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_exact HLT)).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
img_apply SRr_ret; split; [img_refl|]; split; [img_try (img_exact HLT)|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [img_try (rewrite HshR at 1; img_refl)|] end.
split. { reg_atom HS (2%bv : bv 5) 2%nat. }
split. { rreg HS (1%bv : bv 5) Q; rewrite Q; img_refl. }
split. { intros r Hr; cbn [YF37.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; [| | | | | | | | | | img_try (reg_atom HS (26%bv : bv 5) 26%nat) | img_try (reg_atom HS (27%bv : bv 5) 27%nat)].
- reg_atom HS (3%bv : bv 5) 3%nat.
- rreg HS (4%bv : bv 5) Q; rewrite Q; symmetry; img_exact Htp.
- rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; destruct Hregs as (R8 & _); rewrite R8; unfold w64; f_equal; unfold sp0; img_lia.
- rreg HS (9%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); rewrite R9; img_refl.
- rreg HS (18%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & R18 & _); rewrite R18; img_refl.
- rreg HS (19%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & R19 & _); rewrite R19; img_refl.
- rreg HS (20%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & R20 & _); rewrite R20; first [rewrite EqB; img_refl | cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia].
- rreg HS (21%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & R21 & _); rewrite R21; img_refl.
- rreg HS (22%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & _ & R22 & _); rewrite R22; first [rewrite EqBC; img_refl | cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia].
- rreg HS (24%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & _ & _ & _ & R24 & _); rewrite R24; cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia. }
split. { rreg HS (10%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; img_lia. }
split. { rreg HS (11%bv : bv 5) Q; rewrite Q; first [rewrite EqHI; img_refl | cbn [sv_denot]; rewrite EqHI; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia]. }
split. { rreg HS (23%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqS7; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia. }
split. { rreg HS (25%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqI; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia. }
img_exact MQ.
-
assert (HEQ : i = bc).
{ lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R52 R43 dI dBC; zbranch Hbr; apply Bool.negb_false_iff in Hbr; apply Z.eqb_eq in Hbr; img_lia end. }
lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear Hbr end. uncond HS.
srr_run_sh tfxtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfxtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R40 R34 dS1 dS2 dB1 dB2; zbranch Hbr; apply Z.ltb_lt in Hbr; img_lia end. }
uncond HS. srr_run_sh tfxtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfxtbl_rtG_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R40 R34 dS1 dS2 dB1 dB2; zbranch Hbr; apply Bool.negb_true_iff in Hbr; apply Z.ltb_ge in Hbr; img_lia end. }
uncond HS. srr_run_to_sh tfxtbl_rtG_ok HS (0x33b2c + D_150). meq_acc SK0.
apply (st_ok_pin_regU _ _ _ 12%bv (SLit kBatchClass)) in HS;
[ | img_try (intros X; discriminate)
| img_try (pin_prep; change (zev (rho_of E0) (SLit kBatchClass) = zev (rho_of E0) A2T);
rewrite (A2_val (rho_of E0) SB b 24 (b - SB - 24 * 2 ^ 32) R34 R40); [img_refl | img_lia | clear - dB1 dB2; numconst; img_lia | img_lia | clear - dS1; numconst; img_lia | clear - dS1 dS2 dB1 dB2; numconst; img_lia ]) ].
unpin HS. srr_run_to_sh tfxtbl_rtG_ok HS (0x33f78 + D_150). meq_acc SK0.
unfold YF37.postR. replace (i <? bc) with false by (img_try (symmetry; img_apply Z.ltb_ge; img_lia)).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
img_apply SRr_ret; split; [img_refl|]; split; [img_try (img_exact HEQ)|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [img_try (rewrite HshR at 1; img_refl)|] end.
split. { reg_atom HS (2%bv : bv 5) 2%nat. }
split. { rreg HS (1%bv : bv 5) Q; rewrite Q; img_refl. }
split. { intros r Hr; cbn [YF37.SREGS In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; [| | | | | | | | | | img_try (reg_atom HS (26%bv : bv 5) 26%nat) | img_try (reg_atom HS (27%bv : bv 5) 27%nat)].
- reg_atom HS (3%bv : bv 5) 3%nat.
- rreg HS (4%bv : bv 5) Q; rewrite Q; symmetry; img_exact Htp.
- rreg HS (8%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; destruct Hregs as (R8 & _); rewrite R8; unfold w64; f_equal; unfold sp0; img_lia.
- rreg HS (9%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); rewrite R9; img_refl.
- rreg HS (18%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & R18 & _); rewrite R18; img_refl.
- rreg HS (19%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & R19 & _); rewrite R19; img_refl.
- rreg HS (20%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & R20 & _); rewrite R20; first [rewrite EqB; img_refl | cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia].
- rreg HS (21%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & R21 & _); rewrite R21; img_refl.
- rreg HS (22%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & _ & R22 & _); rewrite R22; first [rewrite EqBC; img_refl | cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia].
- rreg HS (24%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & _ & _ & _ & _ & _ & _ & _ & R24 & _); rewrite R24; cbn [sv_denot]; rewrite EqBC; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia. }
split. { rreg HS (10%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqT; unfold w64; rewrite Zbv_add_unsigned; img_refl. }
split. { rreg HS (11%bv : bv 5) Q; rewrite Q; destruct Hregs as (_ & R9 & _); img_refl. }
split. { rreg HS (12%bv : bv 5) Q; rewrite Q; img_refl. }
split. { rreg HS (13%bv : bv 5) Q; rewrite Q; first [rewrite EqB; img_refl | cbn [sv_denot]; rewrite EqB; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia]. }
img_exact MQ.
Qed.
End WK.
End a.
