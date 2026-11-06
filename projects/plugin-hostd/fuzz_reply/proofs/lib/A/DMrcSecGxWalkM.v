(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecGxWalkM.v (commit 237eb205ab7b, H4 srrm M walk (image-specific files); file sha256 a43f89e5bc76) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 6 image addresses moved by code-verified function pairs (7 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4, row srrm-walk): segGX (DMrcSecGxWalk.v) re-run on the materialized-page
   (M) runners of YA0pM, so the post also bounds the materialized pages: every page materialized at 0x343fc was
   materialized at the entry (mat0) or is the page of an address in ZGX, the union of the zones the walk's runs read.
   ZGX holds only zones of DMrcSecMat.RDW's kinds, in RDW's text: the stack, the image window, the thread object, the
   cache context and the dead map [map, map + len) (this Section's map / len); the walk reads no pointer array and no
   last map, so ZGX names neither.  The prelude and the helpers of Section WK are DMrcSecGxWalk.v's, verbatim.
   rule 24: no function proved (srrm-walk bookkeeping). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu DMrcSecGx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP09R YA0pM.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMrcSecMat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x3414c) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4.
Local Notation XW := (DMrcSecGx.XW ly m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation E0 := (DMrcSecGx.E0 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation Er := (DMrcSecGx.Er ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation E2 := (DMrcSecGx.E2 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation E1 := (DMrcSecGx.E1 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqT := (DMrcSecGx.EqT ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqC := (DMrcSecGx.EqC ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqSB := (DMrcSecGx.EqSB ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqM := (DMrcSecGx.EqM ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqMAP := (DMrcSecGx.EqMAP ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqLEN := (DMrcSecGx.EqLEN ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqHW := (DMrcSecGx.EqHW ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqNN := (DMrcSecGx.EqNN ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqJ1 := (DMrcSecGx.EqJ1 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqJ2 := (DMrcSecGx.EqJ2 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqCBP := (DMrcSecGx.EqCBP ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqRA := (DMrcSecGx.EqRA ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS0 := (DMrcSecGx.EqS0 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS1 := (DMrcSecGx.EqS1 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS2 := (DMrcSecGx.EqS2 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS3 := (DMrcSecGx.EqS3 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation EqS4 := (DMrcSecGx.EqS4 ly regs0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4).
Local Notation R_STK := DMrcSecGx.R_STK.
Local Notation R_MAPH := DMrcSecGx.R_MAPH.
Local Notation R_HDR := DMrcSecGx.R_HDR.
Local Notation R_MUT1 := DMrcSecGx.R_MUT1.
Local Notation R_CTX := DMrcSecGx.R_CTX.
Local Notation R_JST := DMrcSecGx.R_JST.
Local Notation REG0 := DMrcSecGx.REG0.
Local Notation FFX := DMrcSecGx.FFX.
Local Notation SR0 := DMrcSecGx.SR0.
Local Notation SS0 := DMrcSecGx.SS0.
Local Notation LYB := (DMrcSecGx.LYB W ly regs0 mem0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 FH).
Local Notation WIN := (DMrcSecGx.WIN ly regs0).
Local Notation win_sub := DMrcSecGx.win_sub.
Local Notation win_sub_sound := (DMrcSecGx.win_sub_sound ly regs0).
Local Notation WSK0 := DMrcSecGx.WSK0.
Local Notation sk_ok := (DMrcSecGx.sk_ok ly regs0).
Local Notation WSK0_ok := (DMrcSecGx.WSK0_ok W ly regs0 mem0 m map len hw nn j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 FH).
Local Notation windows_WIN := (DMrcSecGx.windows_WIN ly regs0).
Local Notation MEQ := (DMrcSecGx.MEQ ly regs0 mem0).
Local Notation MEQ_frame := (DMrcSecGx.MEQ_frame ly regs0 mem0).
Local Notation MEQ_0 := (DMrcSecGx.MEQ_0 ly regs0 mem0).
Local Notation SREGS := DMrcSecGx.SREGS.
Local Notation at_LMD := (DMrcSecGx.at_LMD W ly regs0 mem0 md0 map nn j1 j2 vra vs0 vs1 vs2 vs3 vs4).
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
(* The zones the walk's runs read (the region extents of its symbolic memory REG0: the frame [sp0, sp0 + 80), the map
   header [map, map + 16), the chunk header [m, m + 8), the cache context [C, C + 160), the thread stats
   [T + t_stats + 40, T + t_stats + 56) and the image cells), each widened to its zone in DMrcSecMat.RDW's text. *)
Definition ZGX (a : Z) : Prop :=
(ly_stk_lo ly <= a < ly_stk_hi ly) \/ (TFIB_IMG_LO <= a < TFIB_IMG_END) \/
(ly_T ly <= a < ly_T ly + kThreadObjSize) \/ (ly_C ly <= a < ly_C ly + 256) \/ (map <= a < map + len).
(* The static extents (base atom, lo, hi) the read windows are checked against, by computation, at each run. *)
Definition ZSK : list (option nat * Z * Z) :=
[ (Some 2%nat, 0, 80); (None, TFIB_IMG_LO, TFIB_IMG_END); (Some 32%nat, 0, kThreadObjSize); (Some 33%nat, 0, 256);
  (Some 36%nat, 0, 8192); (Some 35%nat, 0, 16) ].
Definition rr_chk (rs : smem) : bool :=
forallb (fun r => existsb (win_sub (YP09.r_base r, YP09.r_lo r, YP09.r_hi r)) ZSK || (YP09.r_hi r <=? YP09.r_lo r)) rs.
Lemma ZSK_ok : forall t a, In t ZSK -> base_val E0 (fst (fst t)) + snd (fst t) <= a < base_val E0 (fst (fst t)) + snd t -> ZGX a.
Proof.
open_FH. destruct Hsp as [S1 S2]. destruct Hmap as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & FAR). destruct Hhw as [W1 W2].
pose proof LYB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
assert (R32 : rho_of E0 32%nat = T) by (unfold rho_of; rewrite EqT; unfold w64; apply unsigned_lit_small; clear - L1 L2; numconst; zlia).
assert (R33 : rho_of E0 33%nat = ly_C ly) by (unfold rho_of; rewrite EqC; unfold w64; apply unsigned_lit_small; clear - L10 L11; numconst; zlia).
assert (R35 : rho_of E0 35%nat = m) by (unfold rho_of; rewrite EqM; unfold w64; apply unsigned_lit_small; clear - P1 P2 P6 P7 W2; numconst; zlia).
assert (R36 : rho_of E0 36%nat = map) by (unfold rho_of; rewrite EqMAP; unfold w64; apply unsigned_lit_small; clear - P1 P2 P4; numconst; zlia).
unfold rho_of in R32, R33, R35, R36.
intros t a Hin Hr. unfold ZGX. cbn [ZSK In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd base_val] in Hr.
- left. rewrite E2 in Hr. clear - S1 S2 Hr. unfold DMrcSecGx.GFRAME, KSTACK in *. lia.
- right; left. lia.
- right; right; left. rewrite R32 in Hr. unfold T in Hr. lia.
- right; right; right; left. rewrite R33 in Hr. lia.
- right; right; right; right. rewrite R36 in Hr. clear - Hr P4. lia.
- right; right; right; right. rewrite R35 in Hr. clear - Hr P3 P5 P6 P7 P8 W2. lia.
Qed.
Lemma rr_ZGX : forall rs a, rr_chk rs = true -> in_rrange E0 rs a -> ZGX a.
Proof.
intros rs a Hc (r & Hin & Hr). unfold rr_chk in Hc.
pose proof (proj1 (forallb_forall _ _) Hc r Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (w & Hw & Hsub).
  apply (ZSK_ok w a Hw). apply (win_sub_sound E0 a (YP09.r_base r, YP09.r_lo r, YP09.r_hi r) w Hsub). cbn [fst snd]. exact Hr.
- apply Z.leb_le in Ht. lia.
Qed.
(* One M run: its materialized pages stay inside mat0 or the pages of ZGX. *)
Lemma mw_step : forall rs md md', mat_in_win E0 rs md md' -> rr_chk rs = true ->
DMrcSecMat.mat_win ZGX mat0 (m_vm_materialized md) -> DMrcSecMat.mat_win ZGX mat0 (m_vm_materialized md').
Proof.
intros rs md md' HW Hc MW p Hp. destruct (HW p Hp) as [H | (a & Ha & ->)].
- exact (MW p H).
- right. exists a. split; [exact (rr_ZGX rs a Hc Ha) | reflexivity].
Qed.
Ltac mw := lazymatch goal with HMW : mat_in_win _ _ _ _, MW : DMrcSecMat.mat_win _ _ _ |- _ =>
let MW2 := fresh "MWn" in pose proof (mw_step _ _ _ HMW) as MW2; specialize (MW2 ltac:(vm_compute; reflexivity) MW);
rewrite ?m_vm_materialized_wvb in MW2; clear MW HMW; rename MW2 into MW end; srr_norm_model.
Local Notation QGX := (fun (W' : world tfibsegs) (c' : config) => at_LMD W' c' /\ DMrcSecMat.mat_win ZGX mat0 (m_vm_materialized (cfg_model c'))).
Lemma segGX_M : SRr tfibsegs W cfg0 (fun W' c' => at_LMD W' c' /\ DMrcSecMat.mat_win ZGX mat0 (m_vm_materialized (cfg_model c'))).
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof LYB as LB.
destruct Hsp as [S1 S2]. destruct Hregs as (R10 & R11 & R13 & R8 & R9 & R18 & R19 & R20).
destruct Hmap as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & FAR). destruct Hhw as [W1 W2]. destruct Hsaved as (V0 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9).
destruct Hjst as (J1 & J2 & J3 & J4 & J5).
pose proof LB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
evalS HS.
pose proof MEQ_0 as MQ.
assert (MW : DMrcSecMat.mat_win ZGX mat0 mat0) by (intros p Hp; left; exact Hp).
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
srr_run_shM tfibtbl_rtG_ok HS. meq_acc SK0. mw.
srr_branch_sh tfibtbl_rtG_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R36 R37 P1 P2 P4; zdec Hbr end. } nt HS.
srr_run_shM tfibtbl_rtG_ok HS. meq_acc SK0. mw.
srr_branch_sh tfibtbl_rtG_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R35 R36 P1 P2 P6 P7 W2; zdec Hbr end. } nt HS.
srr_run_shM tfibtbl_rtG_ok HS. meq_acc SK0. mw.
srr_branch_sh tfibtbl_rtG_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R35 R36 R37 P1 P2 P4 P6 P7 W2; zdec Hbr end. } nt HS.
srr_run_shM tfibtbl_rtG_ok HS. meq_acc SK0. mw.
pose proof FAR as FAR2.
eassert (JOIN1 : forall ms1 mat1, MEQ (ms_mem ms1) -> DMrcSecMat.mat_win ZGX mat0 mat1 -> st_ok tfibsegs E0 _ (restrict (w_H W) ms1) ->
SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md0) mat1 md0)) QGX).
2: { destruct FAR as [FL|FR].
- srr_branch_sh tfibtbl_rtG_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FL; zdec Hbr end. } nt HS.
srr_run_to_shM tfibtbl_rtG_ok HS 0x33f9c. meq_acc SK0. mw. apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS. eapply JOIN1; [exact MQ | exact MW | exact HS].
- srr_branch_sh tfibtbl_rtG_ok HS. 2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FR; zdec Hbr end. } nt HS.
srr_run_shM tfibtbl_rtG_ok HS. meq_acc SK0. mw.
srr_branch_sh tfibtbl_rtG_ok HS. 2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FR; zdec Hbr end. } nt HS.
srr_run_to_shM tfibtbl_rtG_ok HS 0x33f9c. meq_acc SK0. mw. apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS. eapply JOIN1; [exact MQ | exact MW | exact HS]. }
clear MQ MW HS. intros msj matj MQ MW HS.
srr_run_shM tfibtbl_rtG_ok HS. meq_acc SK0. mw.
eassert (JOIN2 : forall ms2 mat2, MEQ (ms_mem ms2) -> DMrcSecMat.mat_win ZGX mat0 mat2 -> st_ok tfibsegs E0 _ (restrict (w_H W) ms2) ->
SRr tfibsegs W (mkCfg ms2 (with_vm_backing (m_vm_lazy md0) mat2 md0)) QGX).
2: { destruct FAR2 as [FL|FR].
- srr_branch_sh tfibtbl_rtG_ok HS. 2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FL; zdec Hbr end. } nt HS.
srr_run_to_shM tfibtbl_rtG_ok HS 0x3405c. meq_acc SK0. mw. apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS. eapply JOIN2; [exact MQ | exact MW | exact HS].
- srr_branch_sh tfibtbl_rtG_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FR; zdec Hbr end. } nt HS.
srr_run_shM tfibtbl_rtG_ok HS. meq_acc SK0. mw.
srr_branch_sh tfibtbl_rtG_ok HS. 2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R34 R36 P1 P2 P4 L3 L4 L5 L6 FR; zdec Hbr end. } nt HS.
srr_run_to_shM tfibtbl_rtG_ok HS 0x3405c. meq_acc SK0. mw. apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS. evalS HS. eapply JOIN2; [exact MQ | exact MW | exact HS]. }
clear MQ MW HS. intros msk matk MQ MW HS.
srr_run_to_shM tfibtbl_rtG_ok HS 0x343fc. meq_acc SK0. mw.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [| exact MW]; split; [reflexivity|];
lazymatch goal with |- context [with_vm_backing _ ?mt _] => exists (ms_regs msx), (ms_mem msx), mt end;
split; [rewrite HshR at 1; reflexivity|] end.
split. { idtac "SREGS". intros r Hr; cbn [DMrcSecGx.SREGS In] in Hr.
repeat (destruct Hr as [<-|Hr]; [| ]); try contradiction;
lazymatch goal with |- getr _ ?r = getr regs0 ?r => first [let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in reg_atom HS r k | rreg HS r Q; rewrite Q; symmetry; exact Htp] end. }
split. { idtac "F2". rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold DMrcSecGx.GFRAME, w64; f_equal; unfold sp0; zlia. }
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
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; unfold sp0; clear - Ha; zlia | off_by ltac:(clear - Ha S1 S2 L7 L8; unfold DMrcSecGx.GFRAME in *; numconst; unfold KSTACK in *; zlia) ]. }
split. { idtac "MUT". memvo HS 3%nat (A_ALLOCATOR + 680); [reflexivity | reflexivity | cbn; zlia]. }
split. { idtac "J1". memvo HS 5%nat (t_stats + 40); [cbn [base_val YP09.r_base]; unfold rho_of in R32; rewrite R32; unfold t_stats; zlia | cbn [sv_denot]; clear - J3 R40; wordeq_prep; zlia | clear; change (2 ^ 64) with 18446744073709551616; pose proof (Z.mod_pos_bound (j1 + 1) 18446744073709551616 ltac:(zlia)); zlia]. }
idtac "J2". memvo HS 5%nat (t_stats + 48); [cbn [base_val YP09.r_base]; unfold rho_of in R32; rewrite R32; unfold t_stats; zlia | cbn [sv_denot]; clear - J4 W1 W2 R38 R39 R41; wordeq_prep; rewrite !Z.add_0_r; rewrite (Z.mod_small hw 18446744073709551616) by zlia; rewrite (Z.div_small hw 65536) by zlia; replace ((0 mod 18446744073709551616 * 4294967296) mod 18446744073709551616) with 0 by reflexivity; rewrite Z.lor_0_l; zlia | clear; change (2 ^ 64) with 18446744073709551616; pose proof (Z.mod_pos_bound (j2 + nn) 18446744073709551616 ltac:(zlia)); zlia].
Qed.
End WK.
End d.
