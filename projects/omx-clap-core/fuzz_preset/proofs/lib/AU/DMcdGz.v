(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMcdGz.v (commit ce1a656b52b7, file sha256 9c1f3b14c39a) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 4 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 5 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30, a prior worker (lane B1 slice H3): W1 of CacheDealloc's (0x34d00) GROWTH arm, from the entry to
   EnsureFreeArraySpace's entry 0x35560 (ra = 0x3539c), ending in DMcdGI.at_EFA.  The helpers (lines up to val_mem_move)
   and the walk's prefix are the released YFgz.v (lib/YFgz.v:1-310, segK2) with YFgk renamed to its growth copy DMcdGk;
   the only change is the arm at 0x33fc0's room branch (growth taken, no-growth refuted) and the stop at 0x35560.
   rule 24: proves function SizeClassAllocator64LocalCache::Deallocate (W1 of its growth arm); reuse: YFgz.segK2 (released)
   walks the same prefix; `proof-index ReturnToAllocator EnsureFreeArraySpace 0x3539c 0x347c4` 2026-10-30T01:1xZ exit 4. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMcdGz.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, CacheDealloc walk (H3 DMcd* + FG*N, a prior worker DMcdGWb / DMcdGW); file sha256 0df8287a4bf5) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 4 image addresses moved by code-verified function pairs (4 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 6 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMcdGz.v at commit 9ee489aa7d7, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (10 numerals; per-numeral report). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFep YFeo YFgo YFh2 YFfo. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMcdGk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMcdK DMcdGI.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, KSTACK, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, o_quar, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize in *.
Definition kT : nat := 32.
Definition kSB : nat := 33.
Definition kP : nat := 34.
Definition kC : nat := 35.
Definition kPC : nat := 36.
Definition kCNT : nat := 37.
Definition kMAX : nat := 38.
Definition kSZ : nat := 39.
Definition kSLOT : nat := 40.
Definition kRG : nat := 41.
Definition kOLD : nat := 42.
Definition kMF : nat := 43.
Definition kDST : nat := 44.
Definition kSRC : nat := 45.
Definition kJ80 : nat := 46.
Definition kJ88 : nat := 47.
Definition kJST : nat := 48.
Definition kRI : nat := 49.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (c off cnt old mf j80 j88 jst : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x34d00) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 c off cnt old mf j80 j88 jst.
Local Notation Pv := (DMcdGk.Pv ly off).
Local Notation PCv := (DMcdGk.PCv ly c).
Local Notation MAXv := (DMcdGk.MAXv c).
Local Notation SZv := (DMcdGk.SZv c).
Local Notation Nv := (DMcdGk.Nv c).
Local Notation CNTPv := (DMcdGk.CNTPv c cnt).
Local Notation SLOTv := (DMcdGk.SLOTv ly c cnt).
Local Notation RIv := (DMcdGk.RIv ly).
Local Notation RGv := (DMcdGk.RGv ly c).
Local Notation RBv := (DMcdGk.RBv ly c).
Local Notation FAv := (DMcdGk.FAv ly c).
Local Notation DSTv := (DMcdGk.DSTv ly c old).
Local Notation SRCv := (DMcdGk.SRCv ly c cnt).
Local Notation RELv := (DMcdGk.RELv c off).
Local Notation XW := (DMcdGk.XW ly c off cnt old mf j80 j88 jst).
Local Notation E0 := (DMcdGk.E0 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation Er := (DMcdGk.Er ly regs0 c off cnt old mf j80 j88 jst).
Local Notation E2 := (DMcdGk.E2 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation E1 := (DMcdGk.E1 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqT := (DMcdGk.EqT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSB := (DMcdGk.EqSB ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqP := (DMcdGk.EqP ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqC := (DMcdGk.EqC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqPC := (DMcdGk.EqPC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqCNT := (DMcdGk.EqCNT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqMAX := (DMcdGk.EqMAX ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSZ := (DMcdGk.EqSZ ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSLOT := (DMcdGk.EqSLOT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqRG := (DMcdGk.EqRG ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqOLD := (DMcdGk.EqOLD ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqMF := (DMcdGk.EqMF ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqDST := (DMcdGk.EqDST ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSRC := (DMcdGk.EqSRC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJ80 := (DMcdGk.EqJ80 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJ88 := (DMcdGk.EqJ88 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJST := (DMcdGk.EqJST ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqRI := (DMcdGk.EqRI ly regs0 c off cnt old mf j80 j88 jst).
Local Notation R_PC := DMcdGk.R_PC.
Local Notation R_JST := DMcdGk.R_JST.
Local Notation R_STK_HI := DMcdGk.R_STK_HI.
Local Notation R_STK_LO := DMcdGk.R_STK_LO.
Local Notation REG0 := DMcdGk.REG0.
Local Notation R_SLOT := DMcdGk.R_SLOT.
Local Notation R_RGA := DMcdGk.R_RGA.
Local Notation R_RGB := DMcdGk.R_RGB.
Local Notation R_RGC := DMcdGk.R_RGC.
Local Notation WRG := (DMcdGk.WRG ly c).
Local Notation FFK := DMcdGk.FFK.
Local Notation SR0 := DMcdGk.SR0.
Local Notation SS0 := DMcdGk.SS0.
Local Notation LYB := (DMcdGk.LYB W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation class_facts := (DMcdGk.class_facts W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation derived_ranges := (DMcdGk.derived_ranges W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WINF := (DMcdGk.WINF ly c cnt).
Local Notation WINR := (DMcdGk.WINR ly c cnt old).
Local Notation WIN := (DMcdGk.WIN ly regs0 c cnt old).
Local Notation win_sub := DMcdGk.win_sub.
Local Notation win_sub_sound := (DMcdGk.win_sub_sound ly regs0).
Local Notation WSK0 := DMcdGk.WSK0.
Local Notation WSKR := DMcdGk.WSKR.
Local Notation sk_ok := (DMcdGk.sk_ok ly regs0 c cnt old).
Local Notation WSK0_ok := (DMcdGk.WSK0_ok W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WSKR_ok := (DMcdGk.WSKR_ok W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation windows_WIN := (DMcdGk.windows_WIN ly regs0 c cnt old).
Local Notation WIN_zone := (DMcdGk.WIN_zone W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WIN_off := (DMcdGk.WIN_off W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation MEQ := (DMcdGk.MEQ ly regs0 mem0 c cnt old).
Local Notation MEQ_frame := (DMcdGk.MEQ_frame ly regs0 mem0 c cnt old).
Local Notation MEQ_0 := (DMcdGk.MEQ_0 ly regs0 mem0 c cnt old).
Local Notation WINX := (DMcdGk.WINX ly regs0 c cnt).
Local Notation WINX_WIN := (DMcdGk.WINX_WIN ly regs0 c cnt old).
Local Notation sk_okX := (DMcdGk.sk_okX ly regs0 c cnt).
Local Notation WSKX := DMcdGk.WSKX.
Local Notation WSKX_okX := (DMcdGk.WSKX_okX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation windows_WINX := (DMcdGk.windows_WINX ly regs0 c cnt).
Local Notation MEQX := (DMcdGk.MEQX ly regs0 mem0 c cnt).
Local Notation MEQX_frame := (DMcdGk.MEQX_frame ly regs0 mem0 c cnt).
Local Notation MEQX_0 := (DMcdGk.MEQX_0 ly regs0 mem0 c cnt).
Local Notation MEQX_MEQ := (DMcdGk.MEQX_MEQ ly regs0 mem0 c cnt old).
Local Notation DST_notWINX := (DMcdGk.DST_notWINX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation SRC_notWINX := (DMcdGk.SRC_notWINX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WINY := (DMcdGk.WINY ly regs0 c cnt).
Local Notation WINY_WIN := (DMcdGk.WINY_WIN ly regs0 c cnt old).
Local Notation WINX_WINY := (DMcdGk.WINX_WINY ly regs0 c cnt).
Local Notation DST_notWINY := (DMcdGk.DST_notWINY W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation sk_okY := (DMcdGk.sk_okY ly regs0 c cnt).
Local Notation WSKR_okY := (DMcdGk.WSKR_okY W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation windows_WINY := (DMcdGk.windows_WINY ly regs0 c cnt).
Local Notation MEQY := (DMcdGk.MEQY ly regs0 c cnt).
Local Notation MEQY_frame := (DMcdGk.MEQY_frame ly regs0 c cnt).
Local Notation MEQY_0 := (DMcdGk.MEQY_0 ly regs0 c cnt).
Local Notation all_disjoint_of_forall := DMcdGk.all_disjoint_of_forall.
Local Notation SREGS := DMcdGk.SREGS.
Local Notation at_RETK := (DMcdGk.at_RETK W ly regs0 mem0 md0 c off cnt old mf).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hra Hra4096 Hsp Hsp_al Hpres Hc Hcnt Hoff Hslot Hjunk Hfull SEED].
Local Notation off_T := (DMcdGk.off_T W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |].
Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
| M : MEQX ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQX_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
| M : MEQY ?m3 ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQY_frame E _ rs m3 ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac reg_zevK HS r tac :=
let Q := fresh "Q" in
pose proof (st_ok_reg_denot (w_H W) _ _ _ r HS) as Q; cbn [ms_regs restrict] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?sr ?rr) => let t := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with t in Q end;
rewrite Q; clear Q;
apply denot_by_zev; [ reflexivity | tac
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; tac ].
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ apply Er; reflexivity | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
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
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtK ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Lemma val_mem_move : forall (Hh : word -> bool) (m m' : word -> option byte) a a' (n : nat) v,
(forall k, (k < n)%nat -> m' (Z_to_bv 64 (a' + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
(forall k, (k < n)%nat -> Hh (Z_to_bv 64 (a' + Z.of_nat k)) = false) ->
(forall k, (k < n)%nat -> Hh (Z_to_bv 64 (a + Z.of_nat k)) = false) ->
(forall k, (k < n)%nat -> off_img (a + Z.of_nat k)) -> a + Z.of_nat n <= 2 ^ 64 ->
val_mem tfibsegs (mrestrict Hh m) a n v -> val_mem tfibsegs (mrestrict Hh m') a' n v.
Proof.
clear. intros Hh m m' a a' n v He Hd Hs Ha Han Hv k Hk. pose proof (Hv k Hk) as E.
unfold mbyte, mrestrict in E |- *. rewrite (Hd k Hk), (He k Hk). rewrite (Hs k Hk) in E.
destruct (m (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [exact E|].
rewrite (seg_rom_none_off (a + Z.of_nat k) (Ha k Hk)) in E. discriminate.
Qed.
Theorem seg_w1 : cnt = MAXv ->
  SRr tfibsegs W cfg0 (fun W' c' => W' = W /\ DMcdGI.at_EFA W ly regs0 mem0 md0 c off cnt old mf j80 j88 jst c' /\
    DMcdGI.efa_mach W ly regs0 md0 c old mf j80 j88 jst c').
Proof.
intros HFULL. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof DR as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dP1 & dP2 & dPal & dC1 & dC2 & dCal & [dN1 dN2] & [dQ1 dQ2] & dL1 & dL2 & dI1 & dI2 & dG0 & dG1 & dG2 & dI3 & dB0 & dB1 & dB2 & dF0 & [dJ1 dJ2] & [dJ3 dJ4] & [dJ5 dJ6]).
pose proof class_facts as KF. pose proof KF as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
destruct Hoff as (O1 & O2 & O3).
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQX_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSKX_okX E0 HE0 HFULL) as SK0.
assert (HCP : CNTPv = cnt - Nv) by (unfold DMcdGk.CNTPv; destruct (Z.eqb_spec cnt MAXv); [reflexivity | zlia]).
destruct (Hfull HFULL) as (F1 & F2 & F3 & F4 & Frg & Vmx & Vold & Vmf & V80 & V88 & Psrc & Pold).
assert (R32 : rho_of E0 32%nat = T) by (unfold rho_of; rewrite EqT; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (R33 : rho_of E0 33%nat = SB) by (unfold rho_of; rewrite EqSB; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (R34 : rho_of E0 34%nat = Pv) by (unfold rho_of; rewrite EqP; unfold w64; apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia).
assert (R35 : rho_of E0 35%nat = c) by (unfold rho_of; rewrite EqC; unfold w64; apply unsigned_lit_small; clear - Hc; zlia).
assert (R36 : rho_of E0 36%nat = PCv) by (unfold rho_of; rewrite EqPC; unfold w64; apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia).
assert (R37 : rho_of E0 37%nat = cnt) by (unfold rho_of; rewrite EqCNT; unfold w64; apply unsigned_lit_small; clear - Hcnt K3; zlia).
assert (R38 : rho_of E0 38%nat = MAXv) by (unfold rho_of; rewrite EqMAX; unfold w64; apply unsigned_lit_small; clear - K3; zlia).
assert (R39 : rho_of E0 39%nat = SZv) by (unfold rho_of; rewrite EqSZ; unfold w64; apply unsigned_lit_small; clear - K1; numconst; zlia).
assert (R40 : rho_of E0 40%nat = SLOTv) by (unfold rho_of; rewrite EqSLOT; unfold w64; apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia).
assert (R48 : rho_of E0 48%nat = jst) by (unfold rho_of; rewrite EqJST; unfold w64; apply unsigned_lit_small; clear - Hjunk; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
assert (BV32 : bv_unsigned (ew E0 32) = T) by exact R32.
assert (BV36 : bv_unsigned (ew E0 36) = PCv) by exact R36.
assert (BV40 : bv_unsigned (ew E0 40) = SLOTv) by exact R40.
assert (R41 : rho_of E0 41%nat = RGv) by (unfold rho_of; rewrite EqRG; unfold w64; apply unsigned_lit_small; clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia).
assert (R42 : rho_of E0 42%nat = old) by (unfold rho_of; rewrite EqOLD; unfold w64; apply unsigned_lit_small; clear - F1 F2 F3 K5; numconst; zlia).
assert (R43 : rho_of E0 43%nat = mf) by (unfold rho_of; rewrite EqMF; unfold w64; apply unsigned_lit_small; clear - F1 F2 F3 K5; numconst; zlia).
assert (R46 : rho_of E0 46%nat = j80) by (unfold rho_of; rewrite EqJ80; unfold w64; apply unsigned_lit_small; clear - Hjunk; zlia).
assert (R47 : rho_of E0 47%nat = j88) by (unfold rho_of; rewrite EqJ88; unfold w64; apply unsigned_lit_small; clear - Hjunk; zlia).
assert (R49 : rho_of E0 49%nat = RIv) by (unfold rho_of; rewrite EqRI; unfold w64; apply unsigned_lit_small; clear - dI1 dI3; numconst; zlia).
assert (BV41 : bv_unsigned (ew E0 41) = RGv) by exact R41.
apply (st_ok_add_region _ _ _ R_RGC) in HS;
[ | reflexivity
| unfold DMcdGk.R_RGC; unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV41;
split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | apply Frg; zlia]|];
apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqJ80; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - Hjunk; cbn; zlia | cbn; zlia | rewrite ?Z.add_0_r; exact V80]|];
apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqJ88; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - Hjunk; cbn; zlia | cbn; zlia | rewrite ?Z.add_0_r; exact V88]|];
apply Forall_nil
| unfold DMcdGk.R_RGC; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3 Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_RGB) in HS;
[ | reflexivity
| unfold DMcdGk.R_RGB; unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV41;
split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | apply Frg; zlia]|];
apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqOLD; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - F1 F2 F3 K5; cbn; numconst; zlia | cbn; zlia | rewrite ?Z.add_0_r; exact Vold]|];
apply Forall_cons; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite EqMF; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - F1 F2 F3 K5; cbn; numconst; zlia | cbn; zlia | rewrite ?Z.add_0_r; exact Vmf]|];
apply Forall_nil
| unfold DMcdGk.R_RGB, DMcdGk.R_RGC; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3 Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_RGA) in HS;
[ | reflexivity
| unfold DMcdGk.R_RGA; unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict]; rewrite BV41;
split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | apply Frg; zlia]|];
apply Forall_cons; [eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia | rewrite Z.add_0_r; exact Vmx]|];
apply Forall_nil
| unfold DMcdGk.R_RGA, DMcdGk.R_RGB, DMcdGk.R_RGC; cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?BV32, ?BV36, ?BV41, ?BV2;
try unfold T in *; try unfold SB in *; try unfold sp0 in *; clear - LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3 Hlo Hhi; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
pose proof SK0 as SKR.
srr_run_to_sh tfibtbl_rtK_ok HS 0x34d34. meq_acc SKR.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff 36%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?R36, ?R32, ?R35, ?Z.add_0_r; land_lits;
rewrite (zcanon_id c) by (clear - Hc; unfold M64; zlia);
unfold DMcdGk.PCv; clear - Hc dT1 dT2; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtK_ok HS. meq_acc SKR.
srr_branch_sh tfibtbl_rtK_ok HS.
2:{ exfalso. clear - Hc0 R37 R38 HFULL K3 Hcnt. zbranch Hc0. apply Z.eqb_neq in Hc0. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtK_ok HS. meq_acc SKR.
srr_branch_sh tfibtbl_rtK_ok HS.
{ exfalso. clear - Hc1 R37 R38 HFULL K3 K4 K5 K6 Hcnt. zbranch Hc1. apply Z.ltb_lt in Hc1. unfold DMcdGk.Nv, DMcdGk.MAXv in *. zlia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtK_ok HS 0x352c8. meq_acc SKR. dbg HS.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff 41%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?R41, ?R49, ?R35, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?(zcanon_id c) by (clear - Hc; unfold M64; zlia); rewrite ?Z.shiftl_mul_pow2 by zlia;
unfold DMcdGk.RGv; clear - Hc dI1 dI3; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.

(* W1's stop: EnsureFreeArraySpace's entry, before its room branch (segK2 walks on into it; the growth arm stops here). *)
srr_run_to_sh tfibtbl_rtK_ok HS 0x35560. meq_acc SKR. dbg HS.
lazymatch type of HS with st_ok _ _ ?ss (restrict _ ?msx) => rename msx into msE end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
Ltac zevR tac :=
apply denot_by_zev; [ reflexivity | tac
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let cc := eval vm_compute in (2 ^ k) in change (2 ^ k) with cc end; tac ].
assert (R2 : rho_of E0 2%nat = sp0) by (unfold rho_of; exact BV2).
assert (MACH : DMcdGI.efa_mach W ly regs0 md0 c old mf j80 j88 jst
  (mkCfg msE (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md0) mat0 md0)) mat (with_vm_backing (m_vm_lazy md0) mat0 md0)))).
{ rewrite wvb_collapse. exists (ms_regs msE), (ms_mem msE), mat. split; [rewrite Hshape; reflexivity|].
  split. { let Q := fresh "Q" in rreg HS (1%bv : bv 5) Q; rewrite Q. reflexivity. }
  split. { reg_zevK HS (2%bv : bv 5) ltac:(clear - Usp dK1 Hlo LB; numconst; zcanon_simp; unfold zcanon, M64; zlia). }
  split. { let Q := fresh "Q" in rreg HS (4%bv : bv 5) Q; rewrite Q. reflexivity. }
  split. { let Q := fresh "Q" in rreg HS (10%bv : bv 5) Q; rewrite Q. reflexivity. }
  split. { reg_zevK HS (11%bv : bv 5) ltac:(clear - dG0 dG1 dG2 dI1 dI3; numconst; zcanon_simp; unfold zcanon, M64; zlia). }
  split. { reg_zevK HS (12%bv : bv 5) ltac:(unfold DMcdGk.RBv in *; rewrite ?K8 in *; try unfold SB in *; clear - dB0 dB1 dB2 dS1 dS2 K7 K9 Hc; numconst; zcanon_simp; unfold zcanon, M64; zlia). }
  split. { reg_zevK HS (13%bv : bv 5) ltac:(unfold DMcdGk.Nv, DMcdGk.MAXv in *; clear - F1 F2 F3 F4 K3 K4 K5 K6; numconst; zcanon_simp; unfold zcanon, M64; zlia). }
  split.
  { intros a Ha. destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
    - destruct (Z_lt_le_dec a (sp0 - 240)).
      + eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 4 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
      + eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; clear - Ha l; zlia | off_by ltac:(clear - Ha Usp Hlo LB; numconst; zlia) ].
    - eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV41; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
    - eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV41; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
    - eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV41; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
    - eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 5 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV36; clear - Ha; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ].
    - eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 6 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV32; clear - Ha; numconst; zlia | off_by ltac:(clear - Ha DR; numconst; zlia) ]. }
  cbv zeta.
  split. { memvo HS 0%nat 0; [ rewrite BV41; zlia | reflexivity | zlia ]. }
  split. { memvo HS 1%nat 16; [ rewrite BV41; zlia | cbn [sv_denot]; rewrite EqOLD; first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]] | clear - F1 F2 F3 K5; numconst; zlia ]. }
  split. { memvo HS 1%nat 24; [ rewrite BV41; zlia | cbn [sv_denot]; rewrite EqMF; first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]] | clear - F1 F2 F3 K5; numconst; zlia ]. }
  split. { memvo HS 2%nat 80; [ rewrite BV41; zlia | cbn [sv_denot]; rewrite EqJ80; first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]] | clear - Hjunk; zlia ]. }
  split. { memvo HS 2%nat 88; [ rewrite BV41; zlia | cbn [sv_denot]; rewrite EqJ88; first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]] | clear - Hjunk; zlia ]. }
  split. { memvo HS 5%nat 0; [ rewrite BV36; zlia
         | zevR ltac:(unfold DMcdGk.Nv, DMcdGk.MAXv in *; rewrite ?HCP; clear - Hcnt HFULL K3 K4 K5 K6; numconst; zcanon_simp;
             repeat (rewrite zcanon_negadd; [ | zlia | unfold M64; zlia ]); zcanon_simp; unfold zcanon, M64; try zlia)
         | unfold DMcdGk.Nv, DMcdGk.MAXv in *; clear - K3 K5 K6; zlia ]. }
  split. { change (class_size c) with SZv. memvo HS 5%nat 8; [ rewrite BV36; zlia | cbn [sv_denot]; rewrite EqSZ; first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; clear - K1; numconst; zlia]] | clear - K1; numconst; zlia ]. }
  { memvo HS 6%nat 2784; [ rewrite BV32; zlia | cbn [sv_denot]; rewrite EqJST; first [reflexivity | unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia]] | clear - Hjunk; zlia ]. } }
lazymatch type of HS with st_ok _ _ ?ss _ =>
  assert (EK : ss = DMcdK.K9) by (vm_compute; reflexivity); rewrite EK in HS end.
apply SRr_ret. split; [reflexivity|]. split; [|exact MACH].
unfold DMcdGI.at_EFA. exists msE, mat, E0.
split; [apply (f_equal (mkCfg msE)); first [reflexivity | apply (wvb_collapse _ _ mat0) | symmetry; apply (wvb_collapse _ _ mat0)]|]. split; [intros; reflexivity|]. split; [exact HS | exact MQ].
Qed.
End WK.
End d.
