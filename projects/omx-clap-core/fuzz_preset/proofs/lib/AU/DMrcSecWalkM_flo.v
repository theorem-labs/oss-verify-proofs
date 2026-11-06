(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecWalkM_flo.v (a working branch 5ad50e61fc6a, file sha256 95775155cbb4) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; its 21 image addresses moved by code-verified function pairs (17 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 4 code pcs the tool read as sizes, by the internal file funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4, row srrm-walk; integrator a Theorem Labs lane): DMrcSecWalk.segGD_f_lo (the
   arm own = false, small = true, map below kLowMemEnd of the secondary recycle walk from 0x34ec8) re-run on the
   materialized-page (M) engine of YA0pM.v, so that the post DMrcSecMat.at_MUN_M also bounds the materialized pages
   (form F2: DMrcSecMat.mat_rec / mat_mid, and at the return mat_rec / mat_gone).
   rule 24: no function proved (srrm-walk bookkeeping over the already proved walk of
   __asan::QuarantineCallback::Recycle (0x348fc)).
   The prelude (imports, Section variables, hypotheses, Lets, notations, tactics) is DMrcSecWalk.v's, verbatim; this
   file adds one Section hypothesis QLY (the walk's pointer array q is the layout's ly_Q; the consumer instantiates
   q := ly_Q ly).  Each M run's read window (YP09R.in_rrange of the run's first symbolic memory) is checked by
   computation against the window lists SKF1 / SKF2, whose addresses lie in DMrcSecMat.RDW, outside the madvised
   interior [PBv, PEv), and (SKF2, after the munmap, without the map header) outside the map. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n YK0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFl3 YFeq YFew YFeu YFfm YFk7.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMrcSecGv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09R.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YA0pM.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMrcSecMat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFfn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 : Z).
Variables (own small : bool).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x34ec8) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small.
Hypothesis GATE : forall PB k, 0 < k -> SHAv map <= PB -> PB + k <= SHEv map len ->
madvise_dontneed_ok (m_vmmaps md0) (Z_to_bv 64 PB) (Z_to_bv 64 k) = true.
Local Notation XW := (DMrcSecGv.XW ly map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation E0 := (DMrcSecGv.E0 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation Er := (DMrcSecGv.Er ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation E2 := (DMrcSecGv.E2 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation E1 := (DMrcSecGv.E1 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqT := (DMrcSecGv.EqT ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqC := (DMrcSecGv.EqC ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqMAP := (DMrcSecGv.EqMAP ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqLEN := (DMrcSecGv.EqLEN ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqIDX := (DMrcSecGv.EqIDX ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqN := (DMrcSecGv.EqN ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqQ := (DMrcSecGv.EqQ ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqQI := (DMrcSecGv.EqQI ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqQL := (DMrcSecGv.EqQL ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqLAST := (DMrcSecGv.EqLAST ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ1 := (DMrcSecGv.EqJ1 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ2 := (DMrcSecGv.EqJ2 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ3 := (DMrcSecGv.EqJ3 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ4 := (DMrcSecGv.EqJ4 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ5 := (DMrcSecGv.EqJ5 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ6 := (DMrcSecGv.EqJ6 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqSHB := (DMrcSecGv.EqSHB ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqSHA := (DMrcSecGv.EqSHA ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqCNT := (DMrcSecGv.EqCNT ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqRA := (DMrcSecGv.EqRA ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqS0 := (DMrcSecGv.EqS0 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqS1 := (DMrcSecGv.EqS1 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqS2 := (DMrcSecGv.EqS2 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqSHE := (DMrcSecGv.EqSHE ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation R_MAPH := (DMrcSecGv.R_MAPH own).
Local Notation R_STK := DMrcSecGv.R_STK.
Local Notation R_MW0 := DMrcSecGv.R_MW0.
Local Notation R_MW1 := DMrcSecGv.R_MW1.
Local Notation R_NS := DMrcSecGv.R_NS.
Local Notation R_J12 := DMrcSecGv.R_J12.
Local Notation R_J34 := DMrcSecGv.R_J34.
Local Notation R_QI := DMrcSecGv.R_QI.
Local Notation R_CTX := DMrcSecGv.R_CTX.
Local Notation R_JST := DMrcSecGv.R_JST.
Local Notation R_LASTH := DMrcSecGv.R_LASTH.
Local Notation R_QL := DMrcSecGv.R_QL.
Local Notation COMMON := DMrcSecGv.COMMON.
Local Notation REG0 := (DMrcSecGv.REG0 own).
Local Notation FFD := (DMrcSecGv.FFD small).
Local Notation SR0 := DMrcSecGv.SR0.
Local Notation SS0 := (DMrcSecGv.SS0 own small).
Local Notation LYB := (DMrcSecGv.LYB W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small FH).
Local Notation derived_ranges := (DMrcSecGv.derived_ranges W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small FH).
Local Notation WIN := (DMrcSecGv.WIN ly regs0 qi lst).
Local Notation WINS := (DMrcSecGv.WINS map len).
Local Notation WINM := (DMrcSecGv.WINM map len).
Local Notation WIN2 := (DMrcSecGv.WIN2 ly regs0 map len qi lst).
Local Notation WIN3 := (DMrcSecGv.WIN3 ly regs0 map len qi lst).
Local Notation win_sub := DMrcSecGv.win_sub.
Local Notation win_sub_sound := (DMrcSecGv.win_sub_sound ly regs0).
Local Notation WSK0 := (DMrcSecGv.WSK0 own).
Local Notation within := DMrcSecGv.within.
Local Notation within_mono := DMrcSecGv.within_mono.
Local Notation windows_within := (DMrcSecGv.windows_within ly regs0).
Local Notation frame_within := (DMrcSecGv.frame_within ly regs0).
Local Notation MEQP := (DMrcSecGv.MEQP mem0).
Local Notation MEQP_frame := (DMrcSecGv.MEQP_frame ly regs0 mem0).
Local Notation MEQP_weaken := (DMrcSecGv.MEQP_weaken mem0).
Local Notation MEQP_0 := (DMrcSecGv.MEQP_0 mem0).
Local Notation WIN_WIN2 := (DMrcSecGv.WIN_WIN2 ly regs0 map len qi lst).
Local Notation WIN2_WIN3 := (DMrcSecGv.WIN2_WIN3 ly regs0 map len qi lst).
Local Notation WINS_WIN2 := (DMrcSecGv.WINS_WIN2 ly regs0 map len qi lst).
Local Notation WSK0_within := (DMrcSecGv.WSK0_within W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small FH).
Local Notation WIN_not_WINS := (DMrcSecGv.WIN_not_WINS W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small FH).
Local Notation SHD := (DMrcSecGv.SHD map len).
Local Notation SHD_frame := (DMrcSecGv.SHD_frame W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small FH).
Local Notation SREGS := DMrcSecGv.SREGS.
Local Notation at_RET := (DMrcSecGv.at_RET W ly regs0 mem0 map len idx n qi lst vra vs0 vs1 vs2 own).
Local Notation at_MUN := (DMrcSecGv.at_MUN W ly regs0 mem0 md0 map len idx n qi lst vra vs0 vs1 vs2 own).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hra Hregs Hsp Hsp_al Hpres Hsaved Hmap Hdisj Hmaph Harr Hq Hqi Hql Hlst Hown Hlsth Hns Hjunk Hmut Htsd Hjst Hsh_pres SEED].
Ltac off_by tac :=
first [ apply off_img_high; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Ltac meq_acc KW :=
match goal with
| M : MEQP ?D ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQP_frame D E _ rs ma mb KW ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac acc2 KW K :=
lazymatch goal with
| Mq : MEQP ?D ?ma, Sh : SHD ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let Mq2 := fresh "MQ" in let Sh2 := fresh "SHz" in
pose proof (MEQP_frame D E _ rs ma mb KW ltac:(vm_compute; reflexivity) HFx Mq) as Mq2;
pose proof (SHD_frame E _ rs ma mb K ltac:(vm_compute; reflexivity) HFx Sh) as Sh2;
clear Mq Sh HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename Mq2 into MQ; rename Sh2 into SH
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
try unfold sp0 in *; zlia.
Ltac uncond HS := unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac nt HS := lazymatch goal with Hbr : branch_taken _ _ _ = _ |- _ => clear Hbr end; uncond HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtM ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
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
Ltac jword HS i off := eexists; memvo HS i off; [reflexivity | symmetry; apply Z_to_bv_bv_unsigned | apply u64_range].
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |].
Ltac qw_split1 HS iW :=
let VW := fresh "VW" in
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) =>
assert (VW : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msx)) (A_ALLOCATOR + 680) 4 1) by (memv HS iW 0%nat; [reflexivity | reflexivity | zlia]);
apply (proj1 (val_mem4_bytes _ _ _)) in VW; destruct VW as (VW0 & VW1 & VW2 & VW3);
change (YO0f.le_byte 1 4 0) with 1 in VW0; change (YO0f.le_byte 1 4 1) with 0 in VW1;
change (YO0f.le_byte 1 4 2) with 0 in VW2; change (YO0f.le_byte 1 4 3) with 0 in VW3;
eapply (st_ok_set_region E _ _ iW _ R_MW1) in HS;
[ | reflexivity | repeat split; reflexivity | reflexivity
| apply Forall_cons; [ eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | apply (proj2 (val_mem1_byte _ _ _)); rewrite Z.add_0_l; exact VW0 ]
| apply Forall_cons; [ apply chunk_ok_zero_mb; exact (bytes3_of _ _ _ VW1 VW2 VW3) | apply Forall_nil ] ] ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts smem_upd] in HS; clear VW0 VW1 VW2 VW3
end.
Ltac qw_join0 HS iW :=
let VW := fresh "VW" in let VZ := fresh "VZ" in
lazymatch type of HS with st_ok _ ?E ?ss (restrict _ ?msx) =>
assert (VW : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msx)) (A_ALLOCATOR + 680) 1 0) by (memv HS iW 0%nat; [reflexivity | reflexivity | zlia]);
apply (proj1 (val_mem1_byte _ _ _)) in VW; change (YO0f.le_byte 0 1 0) with 0 in VW;
assert (VZ : forall a, A_ALLOCATOR + 681 <= a < A_ALLOCATOR + 681 + 3 -> mbyte tfibsegs (mrestrict (w_H W) (ms_mem msx)) a = Some (Z_to_bv 8 0))
by (intros a Ha; eapply (st_ok_chunk_zero (w_H W) E ss msx iW _ 1 _ _ a HS); [reflexivity | reflexivity | cbn [base_val YP09.r_base]; unfold A_ALLOCATOR in Ha |- *; clear - Ha; zlia]);
eapply (st_ok_set_region E _ _ iW _ R_MW0) in HS;
[ | reflexivity | repeat split; reflexivity | reflexivity
| apply Forall_cons; [ apply chunk_ok_zero_mb; refine (bytes4_of _ _ _ VW (VZ _ _) (VZ _ _) (VZ _ _)); unfold A_ALLOCATOR; zlia | apply Forall_nil ] ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts smem_upd] in HS; clear VW VZ
end.
Ltac rrege HS r Hr :=
lazymatch type of HS with
| st_ok_ecall ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let v := eval cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in (sv_denot E e) in
let v := simp_off0 v in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (Hr : getr rg r = v)
by (refine (eq_trans (st_ok_ecall_restrict_reg H E ss ms r HS) _);
change (sv_denot E e = v);
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity)
end.
(* ---------------------------------------------------------------------------------------------------------------- *)
(* The M re-run (row srrm-walk). *)
Hypothesis QLY : q = ly_Q ly.
Local Notation at_MUN_M := (DMrcSecMat.at_MUN_M W ly regs0 mem0 md0 map len idx n qi lst vra vs0 vs1 vs2 own mat0).

(* The address classes: before the madvise a page may come from a read zone or the shadow window; a run's window
   address lies in a read zone outside the madvised interior (GZ1), and after the munmap also outside the map (GZ2). *)
Definition ZW1 (a : Z) : Prop := DMrcSecMat.RDW ly map len lst a \/ DMrcSecMat.WINSv map len a.
Definition GZ1 (a : Z) : Prop :=
DMrcSecMat.RDW ly map len lst a /\ page_outside_range (DMrcSecMat.PBv map) (DMrcSecMat.PEv map len) (page_base_of a) = true.
Definition GZ2 (a : Z) : Prop := GZ1 a /\ page_outside_range map (map + len) (page_base_of a) = true.

(* The window lists (base atom, lo, hi): stack, image, cache context, thread object, the two pointer-array slots, the
   last map's first page; SKF1 adds the dead map's header. *)
Definition SKF2 : list (option nat * Z * Z) :=
[ (Some 2%nat, - GDEPTH, 0); (None, TFIB_IMG_LO, TFIB_IMG_END); (Some 33%nat, 0, 256); (Some 32%nat, 0, kThreadObjSize);
(Some 39%nat, 0, 8); (Some 40%nat, 0, 8); (Some 41%nat, 0, 4096) ].
Definition SKF1 : list (option nat * Z * Z) := SKF2 ++ [ (Some 34%nat, 0, 32) ].
Definition skbF (SK : list (option nat * Z * Z)) (rs : smem) : bool :=
forallb (fun r => existsb (DMrcSecGv.win_sub (YP09.r_base r, YP09.r_lo r, YP09.r_hi r)) SK || (YP09.r_hi r <=? YP09.r_lo r)) rs.

Lemma mf_win_sub_sound : forall E a t w, DMrcSecGv.win_sub t w = true ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t ->
base_val E (fst (fst w)) + snd (fst w) <= a < base_val E (fst (fst w)) + snd w.
Proof.
intros E a [[bt lt] ht] [[bu lu] hu] Hs Hr. unfold DMrcSecGv.win_sub in Hs. cbn [fst snd] in *.
apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct bt as [x|], bu as [y|]; cbn in H1; try discriminate.
- apply Nat.eqb_eq in H1. subst. lia.
- lia.
Qed.

Lemma mf_rrange_within : forall (D : Z -> Prop) (E : env) SK rs a,
within D E SK -> skbF SK rs = true -> YP09R.in_rrange E rs a -> D a.
Proof.
intros D E SK rs a HK Hb (r & Hin & Hr). unfold skbF in Hb.
pose proof (proj1 (forallb_forall _ _) Hb r Hin) as Ht. cbv beta in Ht.
apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub).
  exact (HK t a Hint (mf_win_sub_sound E a (YP09.r_base r, YP09.r_lo r, YP09.r_hi r) t Hsub Hr)).
- apply Z.leb_le in Ht. lia.
Qed.

Lemma mf_pbo_u : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (page_base_of a) = a / page_size * page_size.
Proof.
intros a Ha64. unfold page_base_of. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64).
unfold page_size in *. pose proof (Z.div_mod a 4096 ltac:(lia)). pose proof (Z.mod_pos_bound a 4096 ltac:(lia)). lia.
Qed.

Lemma mf_por_of : forall lo hi a, 0 <= a < 2 ^ 64 -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> (a < lo \/ hi <= a) ->
page_outside_range lo hi (page_base_of a) = true.
Proof.
intros lo hi a Ha Hlo Hhi Hout. unfold page_outside_range. rewrite (mf_pbo_u a Ha). unfold page_size.
pose proof (Z.div_mod a 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound a 4096 ltac:(lia)) as M.
pose proof (Z.div_mod lo 4096 ltac:(lia)) as Dl. pose proof (Z.div_mod hi 4096 ltac:(lia)) as Dh. rewrite Hlo in Dl. rewrite Hhi in Dh.
set (qa := a / 4096) in *. set (qlo := lo / 4096) in *. set (qhi := hi / 4096) in *.
repeat match goal with
| |- context [?x <=? ?y] => destruct (Z.leb_spec x y)
| |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
end; cbn; first [reflexivity | exfalso; lia].
Qed.

Lemma mf_por_empty : forall lo hi p, hi <= lo -> page_outside_range lo hi p = true.
Proof.
intros lo hi p H. unfold page_outside_range.
repeat match goal with
| |- context [?x <=? ?y] => destruct (Z.leb_spec x y)
| |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
end; cbn; first [reflexivity | exfalso; unfold page_size in *; lia].
Qed.

Lemma mf_PBv_al : DMrcSecMat.PBv map mod 4096 = 0.
Proof.
unfold DMrcSecMat.PBv. pose proof (Z.div_mod (SHAv map + 4095) 4096 ltac:(lia)) as Y.
replace (SHAv map + 4095 - (SHAv map + 4095) mod 4096) with ((SHAv map + 4095) / 4096 * 4096) by lia. apply Z_mod_mult.
Qed.
Lemma mf_PEv_al : DMrcSecMat.PEv map len mod 4096 = 0.
Proof.
unfold DMrcSecMat.PEv. pose proof (Z.div_mod (SHEv map len) 4096 ltac:(lia)) as Y.
replace (SHEv map len - SHEv map len mod 4096) with (SHEv map len / 4096 * 4096) by lia. apply Z_mod_mult.
Qed.
Lemma mf_PBv_ge : SHAv map <= DMrcSecMat.PBv map.
Proof. unfold DMrcSecMat.PBv. pose proof (Z.mod_pos_bound (SHAv map + 4095) 4096 ltac:(lia)). lia. Qed.
Lemma mf_PEv_le : DMrcSecMat.PEv map len <= SHEv map len.
Proof. unfold DMrcSecMat.PEv. pose proof (Z.mod_pos_bound (SHEv map len) 4096 ltac:(lia)). lia. Qed.

(* An address below the low shadow or in high memory has its page outside the madvised interior. *)
Lemma mf_por_PB : forall a, 0 <= a < 2 ^ 64 -> (a < 0x7fff8000 \/ 0x10007fff8000 <= a) ->
page_outside_range (DMrcSecMat.PBv map) (DMrcSecMat.PEv map len) (page_base_of a) = true.
Proof.
intros a Ha Hz. pose proof derived_ranges as DR.
destruct DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & dSH1 & dSH2 & _).
apply mf_por_of; [exact Ha | exact mf_PBv_al | exact mf_PEv_al |].
pose proof mf_PBv_ge as G1. pose proof mf_PEv_le as G2. unfold SHEv in G2. clear - Hz dSH1 dSH2 G1 G2. lia.
Qed.
Lemma mf_por_map : forall a, 0 <= a < 2 ^ 64 -> (a < map \/ map + len <= a) ->
page_outside_range map (map + len) (page_base_of a) = true.
Proof.
intros a Ha Hm. open_FH. destruct Hmap as (P1 & P2 & P3 & P4 & P5 & P6).
apply mf_por_of; [exact Ha | exact P3 | rewrite Zplus_mod, P3, P5; reflexivity | exact Hm].
Qed.
Lemma gz1_intro : forall a, 0 <= a < 2 ^ 64 -> DMrcSecMat.RDW ly map len lst a -> (a < 0x7fff8000 \/ 0x10007fff8000 <= a) -> GZ1 a.
Proof. intros a Ha HR Hz. split; [exact HR | exact (mf_por_PB a Ha Hz)]. Qed.
Lemma gz2_intro : forall a, 0 <= a < 2 ^ 64 -> DMrcSecMat.RDW ly map len lst a -> (a < 0x7fff8000 \/ 0x10007fff8000 <= a) ->
(a < map \/ map + len <= a) -> GZ2 a.
Proof. intros a Ha HR Hz Hm. split; [exact (gz1_intro a Ha HR Hz) | exact (mf_por_map a Ha Hm)]. Qed.

(* The windows of SKF2 under any env that keeps the atoms below 56: read zones, outside the interior and the map. *)
Lemma KGF2 : own = false -> forall E : env, (forall k, (k < 56)%nat -> ew E k = ew E0 k) -> within GZ2 E SKF2.
Proof.
intros OWN E HE t a Hin Hr. open_FH. pose proof derived_ranges as DR. pose proof LYB as LB.
rewrite OWN in Hown. cbv iota in Hown.
destruct Hsp as [S1 S2]. destruct Hmap as (P1 & P2 & P3 & P4 & P5 & P6).
destruct Harr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). destruct Hlst as (X1 & X2 & X3). destruct Hdisj as [D1 D2].
pose proof DR as (_ & _ & _ & _ & dK1 & dK2 & _).
pose proof LB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & _).
clear SEED Hpres Hmaph Hqi Hql Hlsth Htsd Hsh_pres Hjst Hjunk Hns Hmut Hq Hsaved Hregs Hra Htp Hsp_al IMG LY DR LB.
try unfold sp0, T in *.
assert (BSP : bv_unsigned (ew E 2) = bv_unsigned (getr regs0 2)) by (rewrite (HE 2%nat ltac:(lia)), E2; reflexivity).
assert (BT : bv_unsigned (ew E 32) = ly_T ly)
by (rewrite (HE 32%nat ltac:(lia)), EqT; unfold w64; apply unsigned_lit_small; clear - L1; unfold zone3, zone3cases in *; numconst; lia).
assert (BC : bv_unsigned (ew E 33) = ly_C ly)
by (rewrite (HE 33%nat ltac:(lia)), EqC; unfold w64; apply unsigned_lit_small; clear - L4; unfold zone3, zone3cases in *; numconst; lia).
assert (BQI : bv_unsigned (ew E 39) = qi)
by (rewrite (HE 39%nat ltac:(lia)), EqQI; unfold w64; apply unsigned_lit_small; clear - A1 A2 A3 A5; unfold zone3, zone3cases in *; numconst; lia).
assert (BQL : bv_unsigned (ew E 40) = ql)
by (rewrite (HE 40%nat ltac:(lia)), EqQL; unfold w64; apply unsigned_lit_small; clear - A1 A2 A4 A5; unfold zone3, zone3cases in *; numconst; lia).
assert (BLST : bv_unsigned (ew E 41) = lst)
by (rewrite (HE 41%nat ltac:(lia)), EqLAST; unfold w64; apply unsigned_lit_small; clear - X1; unfold zone3, zone3cases in *; numconst; lia).
unfold SKF2 in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?BSP, ?BT, ?BC, ?BQI, ?BQL, ?BLST in Hr.
- (* stack *) apply gz2_intro.
  + clear - Hr dK1 dK2. unfold GDEPTH in *. numconst. lia.
  + unfold DMrcSecMat.RDW. left. clear - Hr S1 S2. unfold GDEPTH in *. numconst. lia.
  + right. clear - Hr dK1. unfold GDEPTH in *. numconst. lia.
  + right. clear - Hr S1 L7 P2. unfold GDEPTH in *. numconst. lia.
- (* image *) apply gz2_intro.
  + clear - Hr. numconst. lia.
  + unfold DMrcSecMat.RDW. right. left. clear - Hr. lia.
  + left. clear - Hr. numconst. lia.
  + clear - Hr P1. unfold zone3, zone3cases in *. numconst. lia.
- (* cache context *) apply gz2_intro.
  + clear - Hr L4. unfold zone3, zone3cases in *. numconst. lia.
  + unfold DMrcSecMat.RDW. right. right. right. left. clear - Hr. lia.
  + clear - Hr L4. unfold zone3, zone3cases in *. numconst. lia.
  + clear - Hr D2. lia.
- (* thread object *) apply gz2_intro.
  + clear - Hr L1. unfold zone3, zone3cases in *. numconst. lia.
  + unfold DMrcSecMat.RDW. right. right. left. clear - Hr. lia.
  + clear - Hr L1. unfold zone3, zone3cases in *. numconst. lia.
  + clear - Hr D1. lia.
- (* pointer-array slot qi *) apply gz2_intro.
  + clear - Hr A1 A2 A3 A5. unfold zone3, zone3cases in *. numconst. lia.
  + unfold DMrcSecMat.RDW. right. right. right. right. left. rewrite <- QLY. clear - Hr A1 A2 A3. numconst. lia.
  + clear - Hr A1 A2 A3 A5. unfold zone3, zone3cases in *. numconst. lia.
  + clear - Hr A1 A2 A3 A8. numconst. lia.
- (* pointer-array slot ql *) apply gz2_intro.
  + clear - Hr A1 A2 A4 A5. unfold zone3, zone3cases in *. numconst. lia.
  + unfold DMrcSecMat.RDW. right. right. right. right. left. rewrite <- QLY. clear - Hr A1 A2 A4. numconst. lia.
  + clear - Hr A1 A2 A4 A5. unfold zone3, zone3cases in *. numconst. lia.
  + clear - Hr A1 A2 A4 A8. numconst. lia.
- (* last map's first page *) apply gz2_intro.
  + clear - Hr X1. unfold zone3, zone3cases in *. numconst. lia.
  + unfold DMrcSecMat.RDW. right. right. right. right. right. right. clear - Hr. lia.
  + clear - Hr X1. unfold zone3, zone3cases in *. numconst. lia.
  + clear - Hr Hown. lia.
Qed.

Lemma KGF1 : own = false -> forall E : env, (forall k, (k < 56)%nat -> ew E k = ew E0 k) -> within GZ1 E SKF1.
Proof.
intros OWN E HE t a Hin Hr. unfold SKF1 in Hin. apply in_app_iff in Hin as [Hin|Hin].
- destruct (KGF2 OWN E HE t a Hin Hr) as [G _]. exact G.
- cbn [In] in Hin. destruct Hin as [<-|[]]. open_FH. destruct Hmap as (P1 & P2 & P3 & P4 & P5 & P6).
  assert (BMAP : bv_unsigned (ew E 34) = map)
  by (rewrite (HE 34%nat ltac:(lia)), EqMAP; unfold w64; apply unsigned_lit_small; clear - P1 P4; unfold zone3, zone3cases in *; numconst; lia).
  cbn [fst snd base_val] in Hr. rewrite BMAP in Hr. apply gz1_intro.
  + clear - Hr P1 P4. unfold zone3, zone3cases in *. numconst. lia.
  + unfold DMrcSecMat.RDW. right. right. right. right. right. left. clear - Hr P4. lia.
  + clear - Hr P1 P4. unfold zone3, zone3cases in *. numconst. lia.
Qed.

(* The page invariants and their steps. *)
Lemma inv1_step : forall E rs md md', within GZ1 E SKF1 -> skbF SKF1 rs = true ->
DMrcSecMat.mat_win ZW1 mat0 (m_vm_materialized md) -> mat_in_win E rs md md' -> DMrcSecMat.mat_win ZW1 mat0 (m_vm_materialized md').
Proof.
intros E rs md md' HK Hb INV HW p Hp. destruct (HW p Hp) as [H | (a & Ha & ->)].
- exact (INV p H).
- right. exists a. split; [| reflexivity]. left. destruct (mf_rrange_within GZ1 E SKF1 rs a HK Hb Ha) as [G _]. exact G.
Qed.

Lemma inv1_memset : forall X X', DMrcSecMat.mat_win ZW1 mat0 X ->
(forall p, In p X' -> In p X \/ exists a, SHAv map <= a < SHAv map + CNTv len /\ p = page_base_of a) ->
DMrcSecMat.mat_win ZW1 mat0 X'.
Proof.
intros X X' INV HM p Hp. destruct (HM p Hp) as [H | (a & Ha & ->)]; [exact (INV p H) |].
right. exists a. split; [right; unfold DMrcSecMat.WINSv, SHEv; exact Ha | reflexivity].
Qed.

Lemma inv12_madv : forall X lo hi, DMrcSecMat.mat_win ZW1 mat0 X -> lo = DMrcSecMat.PBv map -> hi = DMrcSecMat.PEv map len ->
DMrcSecMat.mat_rec ly map len lst mat0 (List.filter (page_outside_range lo hi) X) /\
DMrcSecMat.mat_mid map len (List.filter (page_outside_range lo hi) X).
Proof.
intros X lo hi INV -> ->. split; intros p Hp; apply filter_In in Hp as [Hp Ho].
- destruct (INV p Hp) as [H | (a & [Ha|Ha] & ->)].
  + left. exact H.
  + right. left. exists a. split; [exact Ha | reflexivity].
  + right. right. exists a. split; [exact Ha |]. split; [reflexivity | exact Ho].
- exact Ho.
Qed.

Lemma inv12_empty : forall X, DMrcSecMat.PEv map len <= DMrcSecMat.PBv map -> DMrcSecMat.mat_win ZW1 mat0 X ->
DMrcSecMat.mat_rec ly map len lst mat0 X /\ DMrcSecMat.mat_mid map len X.
Proof.
intros X HE INV. split; intros p Hp.
- destruct (INV p Hp) as [H | (a & [Ha|Ha] & ->)].
  + left. exact H.
  + right. left. exists a. split; [exact Ha | reflexivity].
  + right. right. exists a. split; [exact Ha |]. split; [reflexivity | apply mf_por_empty; exact HE].
- apply mf_por_empty. exact HE.
Qed.

Lemma inv2_step : forall E rs md md', within GZ1 E SKF1 -> skbF SKF1 rs = true ->
DMrcSecMat.mat_rec ly map len lst mat0 (m_vm_materialized md) /\ DMrcSecMat.mat_mid map len (m_vm_materialized md) ->
mat_in_win E rs md md' ->
DMrcSecMat.mat_rec ly map len lst mat0 (m_vm_materialized md') /\ DMrcSecMat.mat_mid map len (m_vm_materialized md').
Proof.
intros E rs md md' HK Hb [R M] HW. split; intros p Hp; destruct (HW p Hp) as [H | (a & Ha & ->)].
- exact (R p H).
- destruct (mf_rrange_within GZ1 E SKF1 rs a HK Hb Ha) as [G _]. right. left. exists a. split; [exact G | reflexivity].
- exact (M p H).
- destruct (mf_rrange_within GZ1 E SKF1 rs a HK Hb Ha) as [_ G]. exact G.
Qed.

Lemma inv23_mun : forall X, DMrcSecMat.mat_rec ly map len lst mat0 X /\ DMrcSecMat.mat_mid map len X ->
DMrcSecMat.mat_rec ly map len lst mat0 (List.filter (page_outside_range map (map + len)) X) /\
DMrcSecMat.mat_gone map len (List.filter (page_outside_range map (map + len)) X).
Proof.
intros X [R M]. split; intros p Hp; apply filter_In in Hp as [Hp Ho].
- exact (R p Hp).
- split; [exact (M p Hp) | exact Ho].
Qed.

Lemma inv3_step : forall E rs md md', within GZ2 E SKF2 -> skbF SKF2 rs = true ->
DMrcSecMat.mat_rec ly map len lst mat0 (m_vm_materialized md) /\ DMrcSecMat.mat_gone map len (m_vm_materialized md) ->
mat_in_win E rs md md' ->
DMrcSecMat.mat_rec ly map len lst mat0 (m_vm_materialized md') /\ DMrcSecMat.mat_gone map len (m_vm_materialized md').
Proof.
intros E rs md md' HK Hb [R M] HW. split; intros p Hp; destruct (HW p Hp) as [H | (a & Ha & ->)].
- exact (R p H).
- destruct (mf_rrange_within GZ2 E SKF2 rs a HK Hb Ha) as [[G _] _]. right. left. exists a. split; [exact G | reflexivity].
- exact (M p H).
- destruct (mf_rrange_within GZ2 E SKF2 rs a HK Hb Ha) as [[_ G1] G2]. split; [exact G1 | exact G2].
Qed.

(* After each M run: fold the run's window fact HMW into the page invariant INV (the window list checked by vm_compute). *)
Ltac m1 KG :=
lazymatch goal with HMW : mat_in_win ?E ?rs ?md ?md', INV : DMrcSecMat.mat_win ZW1 mat0 _ |- _ =>
let I2 := fresh "INV" in
pose proof (inv1_step E rs md md' KG ltac:(vm_compute; reflexivity) INV HMW) as I2;
rewrite ?m_vm_materialized_wvb in I2; clear INV HMW; rename I2 into INV end.
Ltac m2 KG :=
lazymatch goal with HMW : mat_in_win ?E ?rs ?md ?md', INV : DMrcSecMat.mat_rec ly map len lst mat0 _ /\ DMrcSecMat.mat_mid map len _ |- _ =>
let I2 := fresh "INV" in
pose proof (inv2_step E rs md md' KG ltac:(vm_compute; reflexivity) INV HMW) as I2;
rewrite ?m_vm_materialized_wvb in I2; clear INV HMW; rename I2 into INV end.
Ltac m3 KG :=
lazymatch goal with HMW : mat_in_win ?E ?rs ?md ?md', INV : DMrcSecMat.mat_rec ly map len lst mat0 _ /\ DMrcSecMat.mat_gone map len _ |- _ =>
let I2 := fresh "INV" in
pose proof (inv3_step E rs md md' KG ltac:(vm_compute; reflexivity) INV HMW) as I2;
rewrite ?m_vm_materialized_wvb in I2; clear INV HMW; rename I2 into INV end.
Lemma segGD_f_lo_M : DMrcSecMat.memset_nwM_t W -> own = false -> small = true -> map < kLowMemEnd ->
SRr tfibsegs W cfg0 (DMrcSecMat.at_MUN_M W ly regs0 mem0 md0 map len idx n qi lst vra vs0 vs1 vs2 own mat0).
Proof.
intros MSM OWN SM ZARM. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof LYB as LB. pose proof derived_ranges as DR.
rewrite OWN, SM in HS. rewrite SM in Hmap. rewrite OWN in Hown, Hql, Hlsth.
destruct Hsp as [S1 S2]. destruct Hregs as (R10 & R11 & R12 & R1 & R8 & R9 & R18).
destruct Hmap as (P1 & P2 & P3 & P4 & P5 & P6). destruct Harr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). destruct Hlst as (X1 & X2 & X3).
pose proof DR as (_ & _ & _ & _ & dK1 & dK2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & dSH1 & dSH2 & dSH3 & dL8 & dM8 & dCNT & dJ1 & dJ2 & dJ3 & dJ4 & dJ5 & dJ6 & dV1 & dV2 & dV3 & dV4).
pose proof LB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13).
evalS HS.
pose proof (MEQP_0 WIN) as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK0_within E0 HE0) as K0. rewrite OWN in K0.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (R32 : rho_of E0 32%nat = T) by (unfold rho_of; rewrite EqT; unfold w64; apply unsigned_lit_small; clear - L1 L2; numconst; zlia).
assert (R33 : rho_of E0 33%nat = ly_C ly) by (unfold rho_of; rewrite EqC; unfold w64; apply unsigned_lit_small; clear - L4 L5; numconst; zlia).
assert (R34 : rho_of E0 34%nat = map) by (unfold rho_of; rewrite EqMAP; unfold w64; apply unsigned_lit_small; clear - P1 P2 P4; numconst; zlia).
assert (R35 : rho_of E0 35%nat = len) by (unfold rho_of; rewrite EqLEN; unfold w64; apply unsigned_lit_small; clear - P4; numconst; zlia).
assert (R36 : rho_of E0 36%nat = idx) by (unfold rho_of; rewrite EqIDX; unfold w64; apply unsigned_lit_small; clear - A1 A2; zlia).
assert (R37 : rho_of E0 37%nat = n) by (unfold rho_of; rewrite EqN; unfold w64; apply unsigned_lit_small; clear - A1 A2; zlia).
assert (R38 : rho_of E0 38%nat = q) by (unfold rho_of; rewrite EqQ; unfold w64; apply unsigned_lit_small; clear - A5 A6; numconst; zlia).
assert (R39 : rho_of E0 39%nat = qi) by (unfold rho_of; rewrite EqQI; unfold w64; apply unsigned_lit_small; clear - A1 A2 A3 A5 A6; numconst; zlia).
assert (R40 : rho_of E0 40%nat = ql) by (unfold rho_of; rewrite EqQL; unfold w64; apply unsigned_lit_small; clear - A1 A2 A4 A5 A6; numconst; zlia).
assert (R41 : rho_of E0 41%nat = lst) by (unfold rho_of; rewrite EqLAST; unfold w64; apply unsigned_lit_small; clear - X1 X2; numconst; zlia).
assert (R42 : rho_of E0 42%nat = j1) by (unfold rho_of; rewrite EqJ1; unfold w64; apply unsigned_lit_small; exact dJ1).
assert (R43 : rho_of E0 43%nat = j2) by (unfold rho_of; rewrite EqJ2; unfold w64; apply unsigned_lit_small; exact dJ2).
assert (R44 : rho_of E0 44%nat = j3) by (unfold rho_of; rewrite EqJ3; unfold w64; apply unsigned_lit_small; exact dJ3).
assert (R45 : rho_of E0 45%nat = j4) by (unfold rho_of; rewrite EqJ4; unfold w64; apply unsigned_lit_small; exact dJ4).
assert (R46 : rho_of E0 46%nat = j5) by (unfold rho_of; rewrite EqJ5; unfold w64; apply unsigned_lit_small; exact dJ5).
assert (R47 : rho_of E0 47%nat = j6) by (unfold rho_of; rewrite EqJ6; unfold w64; apply unsigned_lit_small; exact dJ6).
assert (R48 : rho_of E0 48%nat = SHADOW_OFF) by (unfold rho_of; rewrite EqSHB; reflexivity).
assert (R49 : rho_of E0 49%nat = SHAv map) by (unfold rho_of; rewrite EqSHA; unfold w64; apply unsigned_lit_small; clear - dSH1 dSH3; zlia).
assert (R50 : rho_of E0 50%nat = CNTv len) by (unfold rho_of; rewrite EqCNT; unfold w64; apply unsigned_lit_small; clear - dCNT; zlia).
assert (R55 : rho_of E0 55%nat = SHEv map len) by (unfold rho_of; rewrite EqSHE; unfold w64; apply unsigned_lit_small; unfold SHEv; clear - dSH1 dSH2 dCNT; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (INV : DMrcSecMat.mat_win ZW1 mat0 mat0) by (intros p Hp; left; exact Hp).
pose proof (KGF1 OWN E0 (fun k _ => eq_refl)) as KG0.
srr_run_shM tfibtbl_rtM_ok HS. meq_acc K0. m1 KG0.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 39%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R36, ?R38, ?R39, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id idx) by (clear - A1 A2; unfold M64; zlia); rewrite !Z.shiftl_mul_pow2 by zlia; change (2 ^ 3) with 8;
clear - A1 A2 A3 A5 A6; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_shM tfibtbl_rtM_ok HS. meq_acc K0. m1 KG0.
srr_branch_sh tfibtbl_rtM_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R36 R37 A1 A2; zdec Hbr end. } nt HS.
srr_run_shM tfibtbl_rtM_ok HS. meq_acc K0. m1 KG0.
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 40%nat 8)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R37, ?R38, ?R40, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id n) by (clear - A1 A2; unfold M64; zlia); rewrite !Z.shiftl_mul_pow2 by zlia; change (2 ^ 3) with 8;
clear - A1 A2 A4 A5 A6; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_shM tfibtbl_rtM_ok HS 0x34fa0. meq_acc K0. m1 KG0.
qw_split1 HS 2%nat.
srr_run_to_shM tfibtbl_rtM_ok HS 0x34fa4. meq_acc K0. m1 KG0.
qw_join0 HS 2%nat.
assert (ZLO : map + len <= kLowShadowBeg) by (clear - ZARM P1; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *; lia).
apply (st_ok_add_atom tfibsegs E0 _ _ 34%nat (mkAF 4096 (kLowShadowBeg - 8192) 12)) in HS.
2:{ pose proof R34 as RR. unfold rho_of in RR. split; [|split]; cbn [af_lo af_hi af_al2];
[ rewrite RR; clear - P1 ZLO P4; unfold zone3, kLowShadowBeg in *; lia | rewrite RR; change (2 ^ 12) with 4096; exact P3 | lia ]. }
evalS HS.
srr_run_to_shM tfibtbl_rtM_ok HS 0x54c4c. meq_acc K0. m1 KG0.
srr_branch_sh tfibtbl_rtM_ok HS. 2:{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R34 R35 R48 ZLO P1 P4; unfold kLowShadowBeg in ZLO; zdec Hbr end. } nt HS.
srr_run_to_shM tfibtbl_rtM_ok HS 0x54cb4. meq_acc K0. m1 KG0.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 49%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R34, ?R48, ?R49, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id map) by (clear - P1 P2 P4; unfold M64; numconst; zlia); rewrite !Z.shiftr_div_pow2 by zlia; change (2 ^ 3) with 8;
unfold SHAv in *; clear - P1 P2 P4 dSH1 dSH3; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff 50%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R34, ?R35, ?R50, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite !Z.shiftr_div_pow2 by zlia; change (2 ^ 3) with 8;
unfold CNTv in *; clear - P1 P2 P4 dL8 dM8 dCNT; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_shM tfibtbl_rtM_ok HS. meq_acc K0. m1 KG0. dbg HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msM end.
assert (SHPRES : forall a, SHAv map <= a < SHAv map + CNTv len -> apresent (w_H W) (ms_mem msM) a).
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha dSH1 dSH2; zlia).
apply (apresent_same (w_H W) mem0).
- apply MQ. rewrite unsigned_lit_small by exact Ra. intros Hx. exact (WIN_not_WINS a Hx Ha).
- apply Hsh_pres. exact Ha. }
rreg HS (11%bv : bv 5) RA1m.
eapply (MSM 56%nat E0 _ _ _ (SHAv map) (CNTv len) 0x34fbc);
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite EqSHA; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity
| rreg HS (12%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite EqCNT; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; reflexivity
| rreg HS (1%bv : bv 5) R; rewrite R; reflexivity
| clear - dCNT; zlia | clear - dSH1; numconst; zlia | clear - dSH1 dSH2; numconst; zlia | reflexivity | zlia
| exact SHPRES
| intros r Hr | intros r a Hr | ].
1-2: cbn [ss_mem In] in Hr; unfold rho_of in R32, R33, R34, R39, R40, R41; repeat (destruct Hr as [<-|Hr];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?BV2, ?R32, ?R33, ?R34, ?R39, ?R40, ?R41;
unfold T, sp0 in *; clear - dK1 dK2 L1 L2 L4 L5 P1 P2 P4 A1 A2 A3 A4 A5 A6 X1 X2 dSH1 dSH2 dSH3; unfold GDEPTH; numconst; first [zlia | match goal with |- ?g => idtac "REGFAIL" g end] |]); destruct Hr.
intros regs5 mem5 mat5 HS5 H10c Hfr5 Hpr5 Hfill HMS. clear HS. rename HS5 into HS. evalS HS.
rewrite ?m_vm_materialized_wvb in HMS. pose proof (inv1_memset _ _ INV HMS) as INV5. clear INV HMS. rename INV5 into INV.
lazymatch type of HS with st_ok _ ?E _ _ => set (E5 := E) in HS end.
assert (HE5 : forall k, (k < 56)%nat -> ew E5 k = ew E0 k) by (intros k Hk; subst E5; rewrite ew_havoc_old by zlia; reflexivity).
assert (HE5' : forall k, (k < aHAVf)%nat -> ew E5 k = ew E0 k) by (intros k Hk; apply HE5; unfold aHAVf in Hk; zlia).
pose proof (WSK0_within E5 HE5') as K5. rewrite OWN in K5.
pose proof (KGF1 OWN E5 HE5) as KG5.
assert (MQ5 : MEQP WIN2 mem5).
{ intros x Hx. rewrite (Hfr5 x) by (intros Hs; apply Hx; apply WINS_WIN2; exact Hs). apply MQ. intros Hw; apply Hx; exact (WIN_WIN2 _ Hw). }
assert (SH5 : SHD mem5).
{ intros x Hx. rewrite (Hfill x Hx), RA1m. reflexivity. }
pose proof (within_mono _ _ E5 _ WIN_WIN2 K5) as KW5.
clear MQ Hfr5 Hfill SHPRES. rename MQ5 into MQ. rename SH5 into SH.
assert (HR5 : forall k, (k < 56)%nat -> rho_of E5 k = rho_of E0 k) by (intros k Hk; unfold rho_of; rewrite (HE5 k Hk); reflexivity).
assert (Q32 : rho_of E5 32%nat = T) by (rewrite (HR5 32%nat ltac:(zlia)); exact R32).
assert (Q33 : rho_of E5 33%nat = ly_C ly) by (rewrite (HR5 33%nat ltac:(zlia)); exact R33).
assert (Q34 : rho_of E5 34%nat = map) by (rewrite (HR5 34%nat ltac:(zlia)); exact R34).
assert (Q35 : rho_of E5 35%nat = len) by (rewrite (HR5 35%nat ltac:(zlia)); exact R35).
assert (Q48 : rho_of E5 48%nat = SHADOW_OFF) by (rewrite (HR5 48%nat ltac:(zlia)); exact R48).
assert (Q49 : rho_of E5 49%nat = SHAv map) by (rewrite (HR5 49%nat ltac:(zlia)); exact R49).
assert (Q50 : rho_of E5 50%nat = CNTv len) by (rewrite (HR5 50%nat ltac:(zlia)); exact R50).
assert (Q55 : rho_of E5 55%nat = SHEv map len) by (rewrite (HR5 55%nat ltac:(zlia)); exact R55).
srr_run_to_shM tfibtbl_rtM_ok HS 0x5354c. acc2 KW5 K5. m1 KG5.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 49%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?Q34, ?Q48, ?Q49, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id map) by (clear - P1 P2 P4; unfold M64; numconst; zlia); rewrite !Z.shiftr_div_pow2 by zlia; change (2 ^ 3) with 8;
unfold SHAv in *; clear - P1 P2 P4 dSH1 dSH3; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_shM tfibtbl_rtM_ok HS 0x53594. acc2 KW5 K5. m1 KG5.
srr_branch_sh tfibtbl_rtM_ok HS. 2:{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr Q34 Q35 Q48 ZLO P1 P4; unfold kLowShadowBeg in ZLO; zdec Hbr end. } nt HS.
srr_run_to_shM tfibtbl_rtM_ok HS 0x53558. acc2 KW5 K5. m1 KG5.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 55%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?Q34, ?Q35, ?Q48, ?Q55, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite !Z.shiftr_div_pow2 by zlia; change (2 ^ 3) with 8;
unfold SHEv, SHAv, CNTv in *; clear - P1 P2 P4 dSH1 dSH2 dSH3 dL8 dM8 dCNT; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_shM tfibtbl_rtM_ok HS. acc2 KW5 K5. m1 KG5.
eassert (JOIN : forall (E' : env) regs6 mem6 mat6, (forall k, (k < 56)%nat -> ew E' k = ew E0 k) -> MEQP WIN2 mem6 ->
SHD mem6 -> DMrcSecMat.mat_rec ly map len lst mat0 mat6 /\ DMrcSecMat.mat_mid map len mat6 ->
st_ok tfibsegs E' _ (restrict (w_H W) (mkst regs6 (Z_to_bv 64 0x34fc8) mem6 (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs6 (Z_to_bv 64 0x34fc8) mem6 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat6 md0)) at_MUN_M).
2: { assert (USHA : 0 <= SHAv map + 4095 < 2 ^ 64) by (clear - dSH1 dSH3; zlia). assert (USHE : 0 <= SHEv map len < 2 ^ 64) by (unfold SHEv; clear - dSH1 dSH2 dCNT; zlia).
destruct (Z_lt_le_dec (SHAv map + 4095 - (SHAv map + 4095) mod 4096) (SHEv map len - SHEv map len mod 4096)) as [LTc|GEc].
- srr_branch_sh tfibtbl_rtM_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr Q49 Q55 USHA USHE LTc; zbranch Hbr;
rewrite ?(zcanon_id (SHEv map len)) in Hbr by (unfold M64; zlia); rewrite !land_m4096 in Hbr by zlia; unfold zcanon, M64 in Hbr;
apply Bool.negb_true_iff in Hbr; apply Z.ltb_ge in Hbr; zlia end. }
nt HS.
srr_run_shM tfibtbl_rtM_ok HS. acc2 KW5 K5. m1 KG5.
set (PB := SHAv map + 4095 - (SHAv map + 4095) mod 4096) in *. set (PE := SHEv map len - SHEv map len mod 4096) in *.
lazymatch goal with |- SRr _ _ (mkCfg ?msx (with_vm_backing _ ?mt _)) _ =>
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
pose proof (st_ok_ecall_full_shape (w_H W) E5 ssM msx HS eq_refl) as SHP; cbn [ss_pc] in SHP; rename msx into msE end end.
rrege HS (17%bv : bv 5) Q17. rrege HS (12%bv : bv 5) Q12.
assert (RPB : SHAv map <= PB <= SHAv map + 4095 /\ PB mod 4096 = 0).
{ subst PB. clear. pose proof (Z.mod_pos_bound (SHAv map + 4095) 4096 ltac:(lia)) as X. split; [lia|].
pose proof (Z.div_mod (SHAv map + 4095) 4096 ltac:(lia)) as Y. replace (SHAv map + 4095 - (SHAv map + 4095) mod 4096) with ((SHAv map + 4095) / 4096 * 4096) by lia. apply Z_mod_mult. }
assert (RPE : 0 <= PE <= SHEv map len /\ PE mod 4096 = 0).
{ subst PE. clear - USHE. pose proof (Z.mod_pos_bound (SHEv map len) 4096 ltac:(lia)) as X. split; [lia|].
pose proof (Z.div_mod (SHEv map len) 4096 ltac:(lia)) as Y. replace (SHEv map len - SHEv map len mod 4096) with (SHEv map len / 4096 * 4096) by lia. apply Z_mod_mult. }
assert (V10 : getr (ms_regs msE) 10 = Z_to_bv 64 PB).
{ lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
refine (eq_trans (st_ok_ecall_restrict_reg (w_H W) E5 ssM msE 10%bv HS) _);
let e := eval vm_compute in (sr_get (ss_regs ssM) 10%bv) in change (sr_get (ss_regs ssM) 10%bv) with e end.
rewrite denot_lit_U. f_equal. rewrite U_zev by reflexivity. cbn [zev zalu_raw zmd_raw]. unfold zalu_raw. rewrite Q49.
rewrite (zcanon_id (SHAv map + 4095)) by (unfold M64; clear - USHA; lia). change (zcanon 18446744073709547520) with 18446744073709547520.
rewrite land_m4096 by (clear - USHA; lia). fold PB. apply zcanon_id. unfold M64. clear - RPB USHA. lia. }
assert (V11 : getr (ms_regs msE) 11 = Z_to_bv 64 (PE - PB)).
{ lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
refine (eq_trans (st_ok_ecall_restrict_reg (w_H W) E5 ssM msE 11%bv HS) _);
let e := eval vm_compute in (sr_get (ss_regs ssM) 11%bv) in change (sr_get (ss_regs ssM) 11%bv) with e end.
rewrite denot_lit_U. f_equal. rewrite U_zev by reflexivity. cbn [zev zalu_raw zmd_raw]. unfold zalu_raw. rewrite Q49, Q55, Z.add_0_r.
rewrite (zcanon_id (SHAv map + 4095)), (zcanon_id (SHEv map len)) by (unfold M64; clear - USHA USHE; lia). change (zcanon 18446744073709547520) with 18446744073709547520.
rewrite !land_m4096 by (clear - USHA USHE; lia). fold PB. fold PE. rewrite (zcanon_id PB), (zcanon_id PE) by (unfold M64; clear - RPB RPE USHA USHE; lia). apply zcanon_id. unfold M64. clear - RPB RPE USHA USHE LTc. lia. }
assert (NAL : (PE - PB) mod 4096 = 0) by (rewrite Zminus_mod, (proj2 RPE), (proj2 RPB); reflexivity).
assert (ZF : YK0v.zfill (Z_to_bv 64 PB) (Z_to_bv 64 (PE - PB)) (ms_mem msE) = ms_mem msE).
{ apply FunctionalExtensionality.functional_extensionality. intros x. unfold YK0v.zfill, YK02.zmem.
rewrite !unsigned_lit_small by (clear - RPB RPE USHA USHE LTc; lia).
destruct (Z.leb_spec PB (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (PB + (PE - PB))); cbn [andb]; try reflexivity.
symmetry. apply SH. unfold DMrcSecGv.WINS. unfold SHEv in RPE. clear - RPB RPE H H1. lia. }
rewrite SHP.
apply (SRr_madvise_pg tfibsegs W (ms_regs msE) (Z_to_bv 64 414700) (ms_mem msE) (seg_rom tfibsegs) _ PB (PE - PB) _ Q17 V10 V11 Q12);
[clear - RPB USHA; lia | exact (proj2 RPB) | clear - LTc; lia | exact NAL | clear - RPB RPE USHA USHE; lia | apply GATE; clear - RPB RPE LTc; lia |].
rewrite ZF, YA06.madvise_next_wvb.
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing _ (List.filter (page_outside_range ?lo ?hi) ?m) _)) _ =>
assert (INVm : DMrcSecMat.mat_rec ly map len lst mat0 (List.filter (page_outside_range lo hi) m) /\ DMrcSecMat.mat_mid map len (List.filter (page_outside_range lo hi) m))
by (apply inv12_madv; [exact INV | rewrite unsigned_lit_small by (clear - RPB USHA; lia); reflexivity
| rewrite !unsigned_lit_small by (clear - RPB RPE USHA USHE LTc; lia); replace (PB + (PE - PB)) with PE by ring; reflexivity]) end.
clear INV. rename INVm into INV.
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
assert (KEPT : Forall (region_kept tfibsegs E5 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W) (ms_mem msE))) (ss_mem ssM))
by (apply Forall_forall; intros r _; apply region_kept_ext; intros z _; reflexivity) end.
pose proof (st_node_cont (w_H W) E5 _ msE (SLit 0) 0 414704 (ms_mem msE) HS eq_refl eq_refl ltac:(vm_compute; reflexivity) KEPT) as HS2.
clear HS KEPT Q17 Q12 V10 V11 ZF SHP. rename HS2 into HS. evalS HS.
change (v_addi (Z_to_bv 64 414700) 4) with (Z_to_bv 64 414704).
srr_run_to_shM tfibtbl_rtM_ok HS 0x34fc8. acc2 KW5 K5. m2 KG5.
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E5 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR; rewrite HshR;
apply (st_ok_forget 62%nat E5 _ (w_H W) msx [10; 11; 12; 13; 17]%bv) in HS; [| reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | reflexivity];
evalS HS; cbn [ss_pc] in HS;
refine (JOIN _ _ _ _ _ MQ SH INV HS) end.
intros k Hk. rewrite ew_havoc_old by zlia. apply HE5. exact Hk.
- srr_branch_sh tfibtbl_rtM_ok HS.
2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr Q49 Q55 USHA USHE GEc; zbranch Hbr;
rewrite ?(zcanon_id (SHEv map len)) in Hbr by (unfold M64; zlia); rewrite !land_m4096 in Hbr by zlia; unfold zcanon, M64 in Hbr;
apply Bool.negb_false_iff in Hbr; apply Z.ltb_lt in Hbr; zlia end. }
nt HS. pose proof (inv12_empty _ GEc INV) as INV2. clear INV. rename INV2 into INV.
srr_run_to_shM tfibtbl_rtM_ok HS 0x34fc8. acc2 KW5 K5. m2 KG5.
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E5 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR; rewrite HshR;
apply (st_ok_forget 62%nat E5 _ (w_H W) msx [10; 11; 12; 13; 17]%bv) in HS; [| reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | reflexivity];
evalS HS; cbn [ss_pc] in HS;
refine (JOIN _ _ _ _ _ MQ SH INV HS) end.
intros k Hk. rewrite ew_havoc_old by zlia. apply HE5. exact Hk. }
clear MQ SH HS KW5 K5 HE5 HE5' HR5 Q32 Q33 Q34 Q35 Q48 Q49 Q50 Q55 INV KG5. subst E5.
intros E6 regs6 mem6 mat6 HE6 MQ SH INV HS.
pose proof (KGF1 OWN E6 HE6) as KG6. pose proof (KGF2 OWN E6 HE6) as KG6b.
assert (HE6' : forall k, (k < aHAVf)%nat -> ew E6 k = ew E0 k) by (intros k Hk; apply HE6; unfold aHAVf in Hk; zlia).
pose proof (WSK0_within E6 HE6') as K6. rewrite OWN in K6. pose proof (within_mono _ _ E6 _ WIN_WIN2 K6) as KW6.
assert (HR6 : forall k, (k < 56)%nat -> rho_of E6 k = rho_of E0 k) by (intros k Hk; unfold rho_of; rewrite (HE6 k Hk); reflexivity).
assert (Q32 : rho_of E6 32%nat = T) by (rewrite (HR6 32%nat ltac:(zlia)); exact R32).
assert (Q33 : rho_of E6 33%nat = ly_C ly) by (rewrite (HR6 33%nat ltac:(zlia)); exact R33).
assert (Q34 : rho_of E6 34%nat = map) by (rewrite (HR6 34%nat ltac:(zlia)); exact R34).
assert (Q35 : rho_of E6 35%nat = len) by (rewrite (HR6 35%nat ltac:(zlia)); exact R35).
assert (Q46 : rho_of E6 46%nat = j5) by (rewrite (HR6 46%nat ltac:(zlia)); exact R46).
assert (Q47 : rho_of E6 47%nat = j6) by (rewrite (HR6 47%nat ltac:(zlia)); exact R47).
srr_run_to_shM tfibtbl_rtM_ok HS 0x653b0. acc2 KW6 K6. m2 KG6.
lazymatch type of HS with st_ok _ _ ?ss _ => let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?r0 :: ?rest => apply (st_ok_drop_regions _ _ _ [r0] rest) in HS; [| vm_compute; reflexivity | vm_compute; reflexivity] end end.
cbn [ss_pc ss_regs ss_resv ss_facts] in HS.
srr_run_shM tfibtbl_rtM_ok HS. acc2 KW6 K6. m2 KG6.
lazymatch goal with |- SRr _ _ (mkCfg ?msx (with_vm_backing _ ?mt _)) _ =>
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
pose proof (st_ok_ecall_full_shape (w_H W) E6 ssM msx HS eq_refl) as SHP;
apply SRr_ret; split; [reflexivity|]; exists (ms_regs msx), (ms_mem msx), mt; rename msx into msE end end.
split. { rewrite SHP at 1. reflexivity. }
split. { idtac "A7". rrege HS (17%bv : bv 5) Q17. rewrite Q17. reflexivity. }
assert (BV6 : forall (k : nat) v, (k < 56)%nat -> ew E0 k = w64 v -> ew E6 k = w64 v) by (intros k v Hk Hv; rewrite (HE6 k Hk); exact Hv).
split. { idtac "A0". rrege HS (10%bv : bv 5) Q10. rewrite Q10. cbn [sv_denot]. rewrite (BV6 34%nat map ltac:(zlia) EqMAP). unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity. }
split. { idtac "A1". rrege HS (11%bv : bv 5) Q11. rewrite Q11. cbn [sv_denot]. rewrite (BV6 35%nat len ltac:(zlia) EqLEN). unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity. }
split. { exact (proj1 INV). }
split. { exact (proj2 INV). }
cbv zeta.
assert (PV2 : bv_unsigned (ew E6 2) = sp0) by (rewrite (HE6 2%nat ltac:(zlia)), E2; reflexivity).
assert (PV32 : bv_unsigned (ew E6 32) = T) by (rewrite (HE6 32%nat ltac:(zlia)); exact R32).
assert (PV33 : bv_unsigned (ew E6 33) = ly_C ly) by (rewrite (HE6 33%nat ltac:(zlia)); exact R33).
assert (PV39 : bv_unsigned (ew E6 39) = qi) by (rewrite (HE6 39%nat ltac:(zlia)); exact R39).
assert (PV40 : bv_unsigned (ew E6 40) = ql) by (rewrite (HE6 40%nat ltac:(zlia)); exact R40).
assert (PV41 : bv_unsigned (ew E6 41) = lst) by (rewrite (HE6 41%nat ltac:(zlia)); exact R41).
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
assert (KEPT : Forall (region_kept tfibsegs E6 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W) (unfill (w64 map) (w64 len) (ms_mem msE)))) (ss_mem ssM)) end.
{ assert (UM : bv_unsigned (w64 map) = map) by (unfold w64; apply unsigned_lit_small; clear - P1 P2 P4; numconst; zlia).
assert (UL : bv_unsigned (w64 len) = len) by (unfold w64; apply unsigned_lit_small; clear - P4; numconst; zlia).
apply Forall_forall. intros r Hr. apply region_kept_ext. intros z Hz. revert Hz.
cbn [ss_mem In] in Hr; repeat (destruct Hr as [<-|Hr];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?PV2, ?PV32, ?PV33, ?PV39, ?PV40, ?PV41;
unfold T, sp0 in *; clear - dK1 dK2 L1 L2 L4 L5 L7 S1 P1 P2 P4 A1 A2 A3 A4 A5 A6 A8 X1 X2 Hown Hdisj UM UL; unfold GDEPTH; numconst; intros Hz;
apply mrestrict_unfill_out; rewrite ?UM, ?UL; first [zlia | match goal with |- ?g => idtac "KEPTFAIL" g; match type of Hz with ?t => idtac "HZ" t end end] |]); destruct Hr. }
pose proof (st_node_cont (w_H W) E6 _ msE (SLit 0) 0 0x653b8 (unfill (w64 map) (w64 len) (ms_mem msE)) HS eq_refl eq_refl ltac:(vm_compute; reflexivity) KEPT) as HS2.
clear HS KEPT. rename HS2 into HS. evalS HS. change (Z_to_bv 64 0) with (w64 0) in HS. change (Z_to_bv 64 0x653b8) with (w64 0x653b8) in HS.
assert (UM0 : bv_unsigned (w64 map) = map) by (unfold w64; apply unsigned_lit_small; clear - P1 P2 P4; numconst; zlia).
assert (UL0 : bv_unsigned (w64 len) = len) by (unfold w64; apply unsigned_lit_small; clear - P4; numconst; zlia).
lazymatch goal with |- SRr _ _ (mkCfg _ ?MM) _ =>
assert (INVm : DMrcSecMat.mat_rec ly map len lst mat0 (m_vm_materialized MM) /\ DMrcSecMat.mat_gone map len (m_vm_materialized MM))
by (rewrite YFfn.munmap_materialized, m_vm_materialized_wvb, UM0, UL0; exact (inv23_mun _ INV)) end.
clear INV. rename INVm into INV.
assert (MQ7 : MEQP WIN3 (unfill (w64 map) (w64 len) (ms_mem msE))).
{ intros x Hx. unfold WIN3 in Hx. rewrite unfill_out by (unfold w64; rewrite !unsigned_lit_small by (clear - P1 P2 P4; numconst; zlia); unfold WINM in Hx; clear - Hx; zlia).
apply MQ. unfold WIN2. clear - Hx. tauto. }
assert (SH7 : SHD (unfill (w64 map) (w64 len) (ms_mem msE))).
{ intros x Hx. rewrite unfill_out by (unfold w64; rewrite !unsigned_lit_small by (clear - P1 P2 P4; numconst; zlia); unfold WINS in Hx; clear - Hx P1 dSH1 dSH2; numconst; zlia).
exact (SH x Hx). }
clear MQ SH. rename MQ7 into MQ. rename SH7 into SH.
pose proof (within_mono _ _ E6 _ (fun a Ha => WIN2_WIN3 a (WIN_WIN2 a Ha)) K6) as KW7.
srr_run_shM tfibtbl_rtM_ok HS. acc2 KW7 K6. m3 KG6b.
eapply (SRr_ret_atM tfibsegs tfibtbl_rtM tfibtbl_rtM_ok Hwx W E6); [exact HS | reflexivity | vm_compute; reflexivity |].
split. 2: { cbn [cfg_model]. exact INV. }
split; [reflexivity|].
lazymatch type of INV with _ /\ DMrcSecMat.mat_gone _ _ ?mR =>
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists (ms_regs msx), (ms_mem msx), mR; rename msx into msR end end.
assert (Er6 : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E6 k = getr regs0 r).
{ intros k r Hk. rewrite (HE6 k) by (pose proof (u5_range r); zlia). exact (Er k r Hk). }
split. { idtac "PCv". rreg HS (1%bv : bv 5) Q1. rewrite Q1. cbn [sv_denot]. rewrite (BV6 51%nat vra ltac:(zlia) EqRA). unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
unfold YK0s.ret_ok, w64 in Hra. rewrite Hra. reflexivity. }
split. { idtac "SREGS". intros r Hr; cbn [DMrcSecGv.SREGS In] in Hr.
repeat (destruct Hr as [<-|Hr]; [| ]); try contradiction;
lazymatch goal with |- getr _ ?r = getr regs0 ?r =>
let RR := fresh "RR" in rreg HS r RR; rewrite RR; let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
first [ exact (Er6 k r eq_refl) | cbn [sv_denot]; rewrite (Er6 k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned | rewrite Htp; reflexivity ] end. }
split. { idtac "F2". rreg HS (2%bv : bv 5) Q2; rewrite Q2; first [ exact (Er6 2%nat 2%bv eq_refl) | cbn [sv_denot]; rewrite (Er6 2%nat 2%bv eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ]. }
split. { idtac "F8". rreg HS (8%bv : bv 5) Q8; rewrite Q8; cbn [sv_denot]; rewrite (BV6 52%nat vs0 ltac:(zlia) EqS0); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity. }
split. { idtac "F9". rreg HS (9%bv : bv 5) Q9; rewrite Q9; cbn [sv_denot]; rewrite (BV6 53%nat vs1 ltac:(zlia) EqS1); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity. }
split. { idtac "F18". rreg HS (18%bv : bv 5) Q18; rewrite Q18; cbn [sv_denot]; rewrite (BV6 54%nat vs2 ltac:(zlia) EqS2); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity. }
split. { exact MQ. }
split. { exact SH. }
split. { idtac "PRES". intros a Ha.
eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite PV2; clear - Ha; unfold GDEPTH in *; zlia | off_by ltac:(clear - Ha S1 L7 Usp; unfold GDEPTH in *; numconst; unfold KSTACK in *; zlia) ]. }
split. { idtac "PRES2". intros a [Ha|Ha].
- eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 5 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite PV39; clear - Ha; zlia | off_by ltac:(clear - Ha A1 A2 A3 A5 A6; numconst; zlia) ].
- eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 7 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite PV32; unfold T in *; clear - Ha; numconst; zlia | off_by ltac:(unfold T in *; clear - Ha L1 L2; numconst; zlia) ]. }
cbv zeta.
split. { idtac "MUT". apply (proj2 (val_mem4_bytes _ _ _)). change (YO0f.le_byte 0 4 0) with 0. change (YO0f.le_byte 0 4 1) with 0. change (YO0f.le_byte 0 4 2) with 0. change (YO0f.le_byte 0 4 3) with 0.
lazymatch type of HS with st_ok _ ?E ?ss (restrict _ _) =>
assert (VZ : forall a, A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 680 + 4 -> mbyte tfibsegs (mrestrict (w_H W) (ms_mem msR)) a = Some (Z_to_bv 8 0))
by (intros a Ha; eapply (st_ok_chunk_zero (w_H W) E ss msR 1 _ 0 _ _ a HS); [reflexivity | reflexivity | cbn [base_val YP09.r_base]; unfold A_ALLOCATOR in Ha |- *; clear - Ha; zlia]) end.
repeat split; apply VZ; unfold A_ALLOCATOR; zlia. }
split. { idtac "NS". memvo HS 2%nat (A_ALLOCATOR + 120); [reflexivity | cbn [sv_denot]; rewrite (BV6 37%nat n ltac:(zlia) EqN); unfold w64; rewrite ?Zbv_add_unsigned; f_equal; rewrite unsigned_lit_small by (clear - A1 A2; zlia); zlia | clear - A1 A2; zlia]. }
split. { idtac "SRT". memvo HS 2%nat (A_ALLOCATOR + 128); [reflexivity | reflexivity | zlia]. }
split. { idtac "JW1". jword HS 3%nat (A_ALLOCATOR + 144). }
split. { jword HS 3%nat (A_ALLOCATOR + 152). }
split. { jword HS 4%nat (A_ALLOCATOR + 704). }
split. { jword HS 4%nat (A_ALLOCATOR + 712). }
split. { idtac "QI". memvo HS 5%nat 0; [cbn [base_val YP09.r_base]; rewrite PV39; zlia | cbn [sv_denot]; rewrite (BV6 41%nat lst ltac:(zlia) EqLAST); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity | clear - X1 X2; numconst; zlia]. }
idtac "OWNF". intros _. split.
{ memvo HS 30%nat 24; [cbn [base_val YP09.r_base]; rewrite PV41; zlia | cbn [sv_denot]; rewrite (BV6 36%nat idx ltac:(zlia) EqIDX); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity | clear - A1 A2; zlia]. }
intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 30 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite PV41; clear - Ha; zlia | off_by ltac:(clear - Ha X1 X2; numconst; zlia) ].
Qed.
End WK.
End d.
