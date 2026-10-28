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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFgx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33888) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4.
Local Notation XW := (AFgx.XW ly m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation E0 := (AFgx.E0 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation Er := (AFgx.Er ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation E2 := (AFgx.E2 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation E1 := (AFgx.E1 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqT := (AFgx.EqT ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqC := (AFgx.EqC ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqSB := (AFgx.EqSB ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqM := (AFgx.EqM ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqMAP := (AFgx.EqMAP ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqLEN := (AFgx.EqLEN ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqHW := (AFgx.EqHW ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqNN := (AFgx.EqNN ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqJ1 := (AFgx.EqJ1 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqJ2 := (AFgx.EqJ2 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqCBP := (AFgx.EqCBP ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqRA := (AFgx.EqRA ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS0 := (AFgx.EqS0 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS1 := (AFgx.EqS1 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS2 := (AFgx.EqS2 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS3 := (AFgx.EqS3 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS4 := (AFgx.EqS4 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation R_STK := AFgx.R_STK.
Local Notation R_MAPH := AFgx.R_MAPH.
Local Notation R_HDR := AFgx.R_HDR.
Local Notation R_MUT1 := AFgx.R_MUT1.
Local Notation R_CTX := AFgx.R_CTX.
Local Notation R_JST := AFgx.R_JST.
Local Notation REG0 := AFgx.REG0.
Local Notation FFX := AFgx.FFX.
Local Notation SR0 := AFgx.SR0.
Local Notation SS0 := AFgx.SS0.
Local Notation LYB := (AFgx.LYB W ly regs0 mem0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 FH).
Local Notation WIN := (AFgx.WIN ly regs0).
Local Notation win_sub := AFgx.win_sub.
Local Notation win_sub_sound := (AFgx.win_sub_sound ly regs0).
Local Notation WSK0 := AFgx.WSK0.
Local Notation sk_ok := (AFgx.sk_ok ly regs0).
Local Notation WSK0_ok := (AFgx.WSK0_ok W ly regs0 mem0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 FH).
Local Notation windows_WIN := (AFgx.windows_WIN ly regs0).
Local Notation MEQ := (AFgx.MEQ ly regs0 mem0).
Local Notation MEQ_frame := (AFgx.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (AFgx.MEQ_0 ly regs0 mem0).
Local Notation SREGS := AFgx.SREGS.
Local Notation at_LMD := (AFgx.at_LMD W ly regs0 mem0 md0 map nn j1 j2 vra vs0 vs1 vs2 vs3 vs4).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hregs Hsp Hsp_al Hpres Hframes Hsaved Hmap Hmaph Hhw Hhdr Hmut Hsb Htsd Hjst SEED].
Ltac off_by tac :=
first [ apply off_img_high; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac zdec Hbr := zbranch Hbr; unfold zcanon, M64 in Hbr;
rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hbr;
first [apply Z.ltb_lt in Hbr | apply Z.ltb_ge in Hbr | apply Z.eqb_eq in Hbr | apply Z.eqb_neq in Hbr | apply Z.leb_le in Hbr | apply Z.leb_gt in Hbr];
try unfold SB in *; try unfold sp0 in *; zlia.
Ltac uncond HS := unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac chunk_index cs off k :=
lazymatch cs with
| (YP09.mkChunk ?o _) :: ?t => let e := eval vm_compute in (o =? off) in
lazymatch e with true => k | false => chunk_index t off (S k) end
end.
Ltac memvo HS i off :=
lazymatch type of HS with st_ok _ _ ?ss _ =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
let cs := eval cbv in (YP09.r_chunks rg) in
let j := chunk_index cs off 0%nat in memv HS i j end end.
Ltac wordeq_prep := apply bv_eq; unfold w64; rewrite ?Z_to_bv_unsigned; repeat (rewrite alu64_unsigned; cbn [zalu_raw]);
repeat match goal with R : rho_of _ ?k = _ |- context [bv_unsigned (ew _ ?k)] => unfold rho_of in R; rewrite R end;
rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
repeat match goal with |- context [?a mod ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (a mod b) in change (a mod b) with c end;
repeat match goal with |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end.
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Lemma segGX : SRr tfibsegs W cfg0 at_LMD.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof LYB as LB.
destruct Hsp as [S1 S2]. destruct Hregs as (R10 & R11 & R13 & R8 & R9 & R18 & R19 & R20).
destruct Hmap as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & FAR). destruct Hhw as [W1 W2]. destruct Hsaved as (V0 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9).
destruct Hjst as (J1 & J2 & J3 & J4 & J5).
pose proof LB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
evalS HS.
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_ok E0 HE0) as SK0.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (R32 : rho_of E0 32%nat = T) by (unfold rho_of; rewrite EqT; unfold w64; apply unsigned_lit_small; clear - L1 L2; numconst; zlia).
assert (R34 : rho_of E0 34%nat = SB) by (unfold rho_of; rewrite EqSB; unfold w64; apply unsigned_lit_small; clear - L3 L4 L5 L6; numconst; zlia).
assert (R35 : rho_of E0 35%nat = m) by (unfold rho_of; rewrite EqM; unfold w64; apply unsigned_lit_small; clear - P1 P2 P6 P7 W2; numconst; zlia).
assert (R36 : rho_of E0 36%nat = map) by (unfold rho_of; rewrite EqMAP; unfold w64; apply unsigned_lit_small; clear - P1 P2 P4; numconst; zlia).
assert (R37 : rho_of E0 37%nat = len) by (unfold rho_of; rewrite EqLEN; unfold w64; apply unsigned_lit_small; clear - P4; numconst; zlia).
assert (R38 : rho_of E0 38%nat = hw) by (unfold rho_of; rewrite EqHW; unfold w64; apply unsigned_lit_small; clear - W1; numconst; zlia).
assert (R39 : rho_of E0 39%nat = nn) by (unfold rho_of; rewrite EqNN; unfold w64; apply unsigned_lit_small; clear - W2; numconst; zlia).
assert (R40 : rho_of E0 40%nat = j1) by (unfold rho_of; rewrite EqJ1; unfold w64; apply unsigned_lit_small; exact J3).
assert (R41 : rho_of E0 41%nat = j2) by (unfold rho_of; rewrite EqJ2; unfold w64; apply unsigned_lit_small; exact J4).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
Ltac nt HS := lazymatch goal with Hbr : branch_taken _ _ _ = _ |- _ => clear Hbr end; uncond HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R36 R37 P1 P2 P4; zdec Hbr end. } nt HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R35 R36 P1 P2 P6 P7 W2; zdec Hbr end. } nt HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R35 R36 R37 P1 P2 P4 P6 P7 W2; zdec Hbr end. } nt HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
pose proof FAR as FAR2.
eassert (JOIN1 : forall ms1 mat1, MEQ (ms_mem ms1) -> st_ok tfibsegs E0 _ (restrict (w_H W) ms1) ->
SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md0) mat1 md0)) at_LMD).
2: { destruct FAR as [FL|FR].
- srr_branch_sh tfibtbl_rtG_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FL; zdec Hbr end. } nt HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x336d8. meq_acc SK0. apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS. eapply JOIN1; [exact MQ | exact HS].
- srr_branch_sh tfibtbl_rtG_ok HS. 2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FR; zdec Hbr end. } nt HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS. 2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FR; zdec Hbr end. } nt HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x336d8. meq_acc SK0. apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS. eapply JOIN1; [exact MQ | exact HS]. }
clear MQ HS. intros msj matj MQ HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
eassert (JOIN2 : forall ms2 mat2, MEQ (ms_mem ms2) -> st_ok tfibsegs E0 _ (restrict (w_H W) ms2) ->
SRr tfibsegs W (mkCfg ms2 (with_vm_backing (m_vm_lazy md0) mat2 md0)) at_LMD).
2: { destruct FAR2 as [FL|FR].
- srr_branch_sh tfibtbl_rtG_ok HS. 2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FL; zdec Hbr end. } nt HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33798. meq_acc SK0. apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS. eapply JOIN2; [exact MQ | exact HS].
- srr_branch_sh tfibtbl_rtG_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FR; zdec Hbr end. } nt HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SK0.
srr_branch_sh tfibtbl_rtG_ok HS. 2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FR; zdec Hbr end. } nt HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33798. meq_acc SK0. apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS. eapply JOIN2; [exact MQ | exact HS]. }
clear MQ HS. intros msk matk MQ HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33b38. meq_acc SK0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [rewrite HshR at 1; reflexivity|] end.
split. { idtac "SREGS". intros r Hr; cbn [AFgx.SREGS In] in Hr.
repeat (destruct Hr as [<-|Hr]; [| ]); try contradiction;
lazymatch goal with |- getr _ ?r = getr regs0 ?r => first [let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in reg_atom HS r k | rreg HS r Q; rewrite Q; symmetry; exact Htp] end. }
split. { idtac "F2". rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold AFgx.GFRAME, w64; f_equal; unfold sp0; zlia. }
split. { idtac "F1". rreg HS (1%bv : bv 5) Q; rewrite Q; first [exact EqRA | cbn [sv_denot]; rewrite EqRA; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity]. }
split. { idtac "F8". rreg HS (8%bv : bv 5) Q; rewrite Q; first [exact EqS0 | cbn [sv_denot]; rewrite EqS0; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity]. }
split. { idtac "F9". rreg HS (9%bv : bv 5) Q; rewrite Q; first [exact EqS1 | cbn [sv_denot]; rewrite EqS1; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity]. }
split. { idtac "F18". rreg HS (18%bv : bv 5) Q; rewrite Q; first [exact EqS2 | cbn [sv_denot]; rewrite EqS2; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity]. }
split. { idtac "F19". rreg HS (19%bv : bv 5) Q; rewrite Q; first [exact EqS3 | cbn [sv_denot]; rewrite EqS3; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity]. }
split. { idtac "F20". rreg HS (20%bv : bv 5) Q; rewrite Q; first [exact EqS4 | cbn [sv_denot]; rewrite EqS4; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity]. }
split. { idtac "F10". rreg HS (10%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { idtac "F11". rreg HS (11%bv : bv 5) Q; rewrite Q; reflexivity. }
split. { idtac "F12". rreg HS (12%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite EqMAP; unfold w64; rewrite ?Zbv_add_unsigned; reflexivity. }
split. { exact MQ. }
split. { idtac "PRES". intros a Ha.
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; unfold sp0; clear - Ha; zlia | off_by ltac:(clear - Ha S1 S2 L7 L8; unfold AFgx.GFRAME in *; numconst; unfold KSTACK in *; zlia) ]. }
split. { idtac "MUT". memvo HS 3%nat (A_ALLOCATOR + 680); [reflexivity | reflexivity | cbn; zlia]. }
split. { idtac "J1". memvo HS 5%nat (t_stats + 40); [cbn [base_val YP09.r_base]; unfold rho_of in R32; rewrite R32; unfold t_stats; zlia | cbn [sv_denot]; clear - J3 R40; wordeq_prep; zlia | clear; change (2 ^ 64) with 18446744073709551616; pose proof (Z.mod_pos_bound (j1 + 1) 18446744073709551616 ltac:(zlia)); zlia]. }
idtac "J2". memvo HS 5%nat (t_stats + 48); [cbn [base_val YP09.r_base]; unfold rho_of in R32; rewrite R32; unfold t_stats; zlia | cbn [sv_denot]; clear - J4 W1 W2 R38 R39 R41; wordeq_prep; rewrite !Z.add_0_r; rewrite (Z.mod_small hw 18446744073709551616) by zlia; rewrite (Z.div_small hw 65536) by zlia; replace ((0 mod 18446744073709551616 * 4294967296) mod 18446744073709551616) with 0 by reflexivity; rewrite Z.lor_0_l; zlia | clear; change (2 ^ 64) with 18446744073709551616; pose proof (Z.mod_pos_bound (j2 + nn) 18446744073709551616 ltac:(zlia)); zlia].
Qed.
End WK.
End d.
