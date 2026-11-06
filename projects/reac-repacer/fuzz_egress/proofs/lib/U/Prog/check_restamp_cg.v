(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_egress: the cut-free (SRcf) walk of check_restamp on the UBSan image, 0x12e58, against
   lib/U/Prog/check_restamp_ccf.v: check_restamp_holds_cf, as reac-repacer/fuzz_uci's lib/U/Prog/check_value_cg.v
   (at bc49657c087a) is to its check_value.v. Section CRS is lib/U/Prog/check_restamp.v's with SR replaced by SRcf
   (SRcf_bind / SRcf_ret, EgressGlue_cg's eg_runA_cf / eg_runN_cf), malloc at the agree room (malloc_contract_ag;
   room_ag_gen from the room premise cr_room_cf), free by the kit's free_contract_cf; memcpy, rp_restamp and bcmp are
   Section hypotheses, as there. The instruction segments (cs_short, cs_seg1, cs_seg2) and the glue lemmas over the
   allocator invariant (cs_inv, cs_pre, cs_inv_call, cs_inv_A, cs_frame_call, ...), none of which mentions SR, are that
   file's, used as they are (module CRW). The aborts and traps that file shows unreachable stay so: the n < 18 return
   and, for 18 <= n, the NULL test of fuzz_dup's malloc, the UBSan overflow checks on c + 14, c + 15, c + 16, f + 16,
   the two restamped-byte tests and the two bcmp tests (cs_seg2). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import
  PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import memcpy_c bcmp_c rp_restamp_c check_restamp_c.
Import ListNotations.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import check_restamp_c.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import EgressGlue.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import LLVMFuzzerTestOneInput_cfb
  check_restamp_ccf EgressGlue_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require check_restamp.
Local Open Scope Z_scope.

Module CRW := OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog.check_restamp.

Section CRS.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = 0x14240.
Hypothesis FREEPC : ms_free B = 0x14100.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis MALLOC : malloc_contract_ag B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis MCPY : memcpy_contract.
Hypothesis RST : rp_restamp_contract.
Hypothesis BCMP : bcmp_contract.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (f n ctr : Z) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CHECK_RESTAMP_STACK L A regs mem md.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 f.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis R12 : getr regs 12 = Z_to_bv 64 ctr.
Hypothesis NB : 0 <= n <= 1600.
Hypothesis IB : in_block L A f n.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : cr_room_cf b n.

(* check_restamp.v's invariant, frame, final predicate and glue lemmas at this Section's entry state *)
Let cs_inv := CRW.cs_inv B API L A regs mem md.
Let cs_keep := CRW.cs_keep regs.
Let cs_frame := CRW.cs_frame regs.
Let cs_final := CRW.cs_final B API L A regs mem md b.
Let cs_pre := CRW.cs_pre B API L A regs mem md PRE.
Let cs_inv_call := CRW.cs_inv_call B API AX CT L A regs mem md PRE.
Let cs_inv_A := CRW.cs_inv_A B API SEGS L A regs mem md n PRE NB.
Let cs_free_keep := CRW.cs_free_keep B API L A regs mem md.
Let cs_frame_call := CRW.cs_frame_call B API SEGS ERR L A regs mem md PRE.
Let cs_inv_kept := CRW.cs_inv_kept B API L A regs mem md.
Let cs_keep_pres := CRW.cs_keep_pres regs.
Let cs_heap_E := CRW.cs_heap_E B API AX.
Let cs_blk := CRW.cs_blk B API AX.

(* The tail call: free(c) at the entry sp, returning to the caller's ra. *)
Lemma cs_ph3_cf : forall (fx7 : FPState) L1 A1 regs7 m7 md1 c d1 d2,
  frm_zero (@fp_csr fx7) ->
  cs_inv L1 A1 m7 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = d1 ++ (c, n) :: d2 -> blocks L A = d1 ++ d2 -> 0 < n ->
  res_ok_slots A1 (sb_malloc b n) ->
  getr regs7 1 = getr regs 1 -> spZ regs7 = spZ regs -> getr regs7 10 = Z_to_bv 64 c ->
  regs_preserved regs regs7 ->
  SRcf B (mkCfg (@mkst fx7 regs7 (Z_to_bv 64 CRW.CS_FREE) m7 (seg_rom (ms_segs B))) md1) cs_final.
Proof.
  intros fx7 L1 A1 regs7 m7 md1 c d1 d2 Hfrm I Hinit Hb1 Hb0 Hn Hres G1 S7 G10 P7.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_RESTAMP_STACK = 8240) by reflexivity.
  pose proof I as ((M1 & W1 & B1 & _) & I2 & I3 & I4 & I5).
  destruct (eg_bu L1 A1 c _ ltac:(rewrite Hb1; apply eg_in_mid)) as (p & Hp & Ep).
  assert (Hpre7 : call_pre B (aa_MR API) L1 A1 regs7 m7 md1).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 regs7 m7 md1)).
    apply (cs_pre L1 A1 m7 md1 regs7 0 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia | rewrite S7; exact H16
      | exact (P7 4 ltac:(unfold callee_saved; lia)) | rewrite G1; exact Hra | exact Hinit]. }
  replace (Z_to_bv 64 CRW.CS_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply (SRcf_bind B).
  { apply (FREE fx7 L1 A1 regs7 m7 md1 p n (sb_malloc b n) Hpre7 I4 Hp).
    - rewrite G10, Ep. reflexivity.
    - exact Hres. }
  intros c' (L6 & A6 & regs12 & m12 & md6 & -> & Hpost & (e1 & e2 & Hd1 & Hd2) & Hkept & Hro6 & Hgk6 & Hub6 &
    Hinit6 & Hlen6 & Hres6).
  apply call_post_k_alloc in Hpost.
  rewrite Ep in Hd1.
  assert (PW1 : pairwise ranges_disjoint (d1 ++ (c, n) :: d2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1)).
  assert (ND1 : ~ In (c, n) (d1 ++ d2)) by (apply (eg_notin d1 d2 _ PW1); cbn; lia).
  assert (Hb6 : blocks L6 A6 = blocks L A).
  { rewrite Hd2, Hb0. symmetry. apply (eg_rm (c, n) d1 d2 e1 e2 ND1). rewrite <- Hb1. exact Hd1. }
  assert (HD1 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L1 p, n) y).
  { intros y Hy. rewrite Ep. apply (eg_pw_mid d1 d2 _ y PW1). rewrite <- Hb0. exact Hy. }
  assert (HU6 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A6)).
  { intros q k Hq. apply Hub6; [exact (I3 q k Hq) | exact (cs_free_keep L1 A1 m7 md1 p _ I Hp ltac:(lia) HD1 q k Hq)]. }
  assert (I6 : cs_inv L6 A6 m12 md6).
  { apply (cs_inv_call L1 A1 m7 md1 regs7 ALLOC_STACK _ L6 A6 regs12 m12 md6 I Hpost);
      [rewrite S7, HK0; unfold ALLOC_STACK; lia | lia | exact (cs_heap_E L1 A1 m7 md1 p _ M1 Hp) | exact Hlen6
      | exact HU6 | exact Hro6 | exact Hgk6]. }
  apply (SRcf_ret B). exists fx7, L6, A6, regs12, m12, md6.
  split; [rewrite G1; reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I6 as (I6a & _). apply (kb_post B API); [exact I6a|].
    exact (kb_preserved_trans _ _ _ P7 (proj2 (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost))). }
  split; [exact Hb6|].
  split; [exact (cs_inv_kept _ _ _ _ I6)|].
  destruct I6 as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres6; exact Hres6 | intros _; exact (Hinit6 Hinit)].
Qed.

(* After malloc: the body on the normalized memory (CRW.cs_seg2) as one eg_runN_cf segment, then the tail call. *)
Lemma cs_ph2_cf : forall L1 A1 regs2 m2 md1 c d1 d2,
  cs_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = d1 ++ (c, n) :: d2 -> blocks L A = d1 ++ d2 -> 18 <= n ->
  res_ok_slots A1 (sb_malloc b n) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs2 8 = Z_to_bv 64 n -> getr regs2 10 = Z_to_bv 64 c ->
  getr regs2 18 = Z_to_bv 64 f -> getr regs2 19 = Z_to_bv 64 ctr -> cs_keep regs2 -> cs_frame m2 ->
  SRcf B (mkCfg (mkst regs2 (Z_to_bv 64 0x12ea8) m2 (seg_rom (ms_segs B))) md1) cs_final.
Proof.
  intros L1 A1 regs2 m2 md1 c d1 d2 I Hinit Hb1 Hb0 Hn18 Hres G2 G8 G10 G18 G19 GK (junk & FR).
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_RESTAMP_STACK = 8240) by reflexivity.
  pose proof I as ((M1 & W1 & B1 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  pose proof (eg_img_low B SEGS) as HIL.
  assert (S2 : spZ regs2 = spZ regs - 48) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  assert (Hro' : ro_agree rsegs m2) by (rewrite <- SEGS; exact I4).
  assert (InC : In (c, n) (blocks L1 A1)) by (rewrite Hb1; apply eg_in_mid).
  destruct (cs_blk L1 A1 m2 md1 c n M1 InC) as (HC1 & HC2 & _ & HCi).
  pose proof IB as (q & k & Hq & Hq1 & Hq2).
  destruct (cs_blk L A mem md q k HM Hq) as (HQ1 & HQ2 & _).
  assert (Hq' : In (q, k) (d1 ++ d2)) by (rewrite <- Hb0; exact Hq).
  assert (HqL1 : In (q, k) (blocks L1 A1)) by (rewrite Hb1; apply eg_in_ins; exact Hq').
  destruct (cs_blk L1 A1 m2 md1 q k M1 HqL1) as (_ & _ & _ & HQi).
  assert (PW1 : pairwise ranges_disjoint (d1 ++ (c, n) :: d2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1)).
  pose proof (CRW.cs_pw _ _ _ _ _ _ PW1 Hq') as DCQ.
  assert (PN : forall a, present m2 a -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
                 exists bb, normalize rsegs m2 (Z_to_bv 64 a) = Some bb).
  { intros a [bb Hbb] Hni Ha. exists bb. unfold normalize. cbv beta.
    pose proof (eg_ro_false B a Ha (eg_fs_none B SEGS a Hni)) as E. rewrite SEGS in E. unfold Mem.wa in E.
    rewrite E. exact Hbb. }
  assert (CJx : exists cj, Step.rw_cells rsegs (normalize rsegs m2) c [Cells.CB (Z.to_nat n) cj]).
  { apply CRW.cs_cells_of; [lia | lia |].
    intros i Hi. destruct (HCi i ltac:(lia)) as (X1 & X2 & _). apply PN; [exact X1 | exact X2 | lia]. }
  destruct CJx as (cj & CJ).
  assert (FJx : exists src, Step.rw_cells rsegs (normalize rsegs m2) f [Cells.CB (Z.to_nat n) src]).
  { apply CRW.cs_cells_of; [lia | lia |].
    intros i Hi. destruct (HQi (f - q + i) ltac:(lia)) as (X1 & X2 & _).
    replace (q + (f - q + i)) with (f + i) in X1, X2 by ring. apply PN; [exact X1 | exact X2 | lia]. }
  destruct FJx as (src & FJ).
  destruct FJ as [[FW FB] _]. cbn [Cells.cells_bytes Cells.cbytes] in FB. rewrite app_nil_r in FB.
  cbn in FW. destruct FW as [FL _].
  assert (FRn : Step.rw_cells rsegs (normalize rsegs m2) (spZ regs - 48) [Cells.CB 8 junk; Cells.C8 (getr regs 19);
    Cells.C8 (getr regs 18); Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)]).
  { apply (CRW.cs_cells_norm m2 _ _ Hro' FR). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
    pose proof (eg_ro_false B (spZ regs - 48 + i) ltac:(lia) (eg_fs_high B HIL (spZ regs - 48 + i) ltac:(lia))) as E.
    rewrite SEGS in E. exact E. }
  eapply (eg_runN_cf B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G8, G10, G18, G19.
    eapply (CRW.cs_seg2 MCPY RST BCMP); rewrite ?MState.unsigned_lit by lia;
      try change (bv_unsigned (getr regs2 2)) with (spZ regs2); rewrite ?S2;
      first [ lia | exact (mem_inv_normalize rsegs m2) | exact FRn | exact CJ | exact FB | exact FL ]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
    MU & WM) Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR). cbn [ms_mem MState.MS] in HR.
  rewrite !MState.unsigned_lit in MU by lia.
  set (W := [(c, c + n)]) in MU.
  pose proof (mem_rel_normalize rsegs m2 Hro') as HR6.
  pose proof (munch_rel rsegs _ m2 _ (ms_mem ms) m' HR6 HR Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m2 _ (ms_mem ms) m' HR6 HR Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m2 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (HinW : forall x, ~ Frame.outside W x -> c <= x < c + n)
    by (intros x Hx; unfold W in Hx; cbn [Frame.outside] in Hx; lia).
  assert (PRES : forall x, m2 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (eg_pres B m2 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (HinW _ Hout) as Hs.
    apply (eg_fs_none B SEGS). destruct (HCi (bv_unsigned x - c) ltac:(lia)) as (_ & Hni & _).
    replace (c + (bv_unsigned x - c)) with (bv_unsigned x) in Hni by ring. exact Hni. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CHECK_RESTAMP_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L1 A1 x /\
      forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. pose proof (HinW _ Hout) as Hs. right.
    destruct (HCi (x - c) ltac:(lia)) as (_ & Hn1 & Hn2).
    replace (c + (x - c)) with x in Hn1, Hn2 by ring.
    split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
    intros p k0 i Hp Hi E. assert (Y : In (ptr_addr L p, k0) (d1 ++ d2)) by (rewrite <- Hb0; exact (eg_ub L A p k0 Hp)).
    pose proof (CRW.cs_pw _ _ _ _ _ _ PW1 Y). lia. }
  pose proof (cs_inv_A L1 A1 m2 md1 (ms_mem ms) W I MU7 WM7 PRES HWW RO7) as I7.
  assert (G7a : getr regs7 1 = getr regs 1) by (rewrite Hg7; reflexivity).
  assert (G7b : getr regs7 2 = Z_to_bv 64 (bv_unsigned (getr regs2 2) + 48)) by (rewrite Hg7; reflexivity).
  change (bv_unsigned (getr regs2 2)) with (spZ regs2) in G7b. rewrite S2 in G7b.
  replace (spZ regs - 48 + 48) with (spZ regs) in G7b by lia.
  assert (S7 : spZ regs7 = spZ regs) by (unfold spZ at 1; rewrite G7b; apply MState.unsigned_lit; lia).
  assert (G7c : getr regs7 10 = Z_to_bv 64 c) by (rewrite Hg7; reflexivity).
  assert (P7 : regs_preserved regs regs7).
  { destruct GK as (K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    assert (Hs : getr regs7 2 = getr regs 2) by (rewrite G7b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg7; first [reflexivity | exact K3 | exact K4 | exact K20 | exact K21 | exact K22
        | exact K23 | exact K24 | exact K25 | exact K26 | exact K27]]. }
  apply (cs_ph3_cf (mkFP fp_regs fp_csr) L1 A1 regs7 (ms_mem ms) md1 c d1 d2 FRM I7 Hinit Hb1 Hb0 ltac:(lia) Hres
    G7a S7 G7c P7).
Qed.

(* Entry: the n < 18 return, or the frame and malloc(n) at the agree room, then cs_ph2_cf. *)
Lemma cs_entry_cf :
  SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_RESTAMP) mem (seg_rom (ms_segs B))) md) cs_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_RESTAMP_STACK = 8240) by reflexivity.
  pose proof (eg_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  assert (I0 : cs_inv L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p k Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : Frame.stk rsegs mem (spZ regs - CHECK_RESTAMP_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CHECK_RESTAMP_STACK L A regs mem md PRE ltac:(lia))).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 48, spZ regs)] x -> spZ regs - 48 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (FRAME : forall m1, Frame.munch [(spZ regs - 48, spZ regs)] mem m1 -> Frame.wmono rsegs mem m1 ->
    cs_inv L A m1 md /\ ro_agree (ms_segs B) m1 /\ Frame.wmono (ms_segs B) mem m1).
  { intros m1 MU WM.
    assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
    assert (Hro1 : ro_agree (ms_segs B) m1).
    { apply (eg_ro_munch B _ mem m1 RO MU). intros a Ha Ho. apply (eg_fs_high B HIL). pose proof (Hout a Ho). lia. }
    split; [|split; [exact Hro1 | exact WM']].
    apply (cs_inv_A L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 48, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (eg_pres B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (eg_fs_high B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  destruct (Z_lt_ge_dec n 18) as [Hs|Hs].
  - (* n < 18: it returns at once *)
    eapply (eg_runA_cf B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
    { unfold rmk. rewrite R10, R11, R12.
      eapply CRW.cs_short; [exact ST | unfold spZ; lia | rewrite MState.unsigned_lit by lia; lia]. }
    { intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & _).
      repeat split; reflexivity. }
    intros ms regs1 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
      MU & WM) Hg1.
    cbn [MState.MS ms_pc_val ms_mem].
    rewrite (kb_ret_pc _ Hra).
    change (bv_unsigned (getr regs 2)) with (spZ regs) in MU.
    destruct (FRAME m1 MU WM) as (I1 & _ & _).
    apply (SRcf_ret B). exists fx, L, A, regs1, m1, md.
    split; [reflexivity|]. split; [exact FRM|].
    split.
    { destruct I1 as (I1a & _). apply (kb_post B API); [exact I1a|].
      intros r Hr. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        rewrite Hg1; reflexivity. }
    split; [reflexivity|].
    split; [exact (cs_inv_kept _ _ _ _ I1)|].
    destruct I1 as (_ & _ & _ & Hro' & Hg').
    split; [exact Hg'|]. split; [exact Hro'|]. split; [exact RES | intros H; exact H].
  - (* 18 <= n: the copy, the checks, free *)
    eapply (eg_runA_cf B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
    { unfold rmk. rewrite R10, R11, R12.
      eapply CRW.cs_seg1; [exact ST | unfold spZ; lia | rewrite MState.unsigned_lit by lia; lia]. }
    { intros ms (t0' & t1' & t2' & a1' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> & _).
      repeat split; reflexivity. }
    intros ms regs1 (t0' & t1' & t2' & a1' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> &
      MU & WM & FR1) Hg1.
    cbn [MState.MS ms_pc_val ms_mem].
    change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
    assert (G1a : getr regs1 1 = Z_to_bv 64 0x12ea8) by (rewrite Hg1; reflexivity).
    assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg1; reflexivity).
    assert (G1c : getr regs1 10 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
    assert (G1d : getr regs1 8 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
    assert (G1e : getr regs1 18 = Z_to_bv 64 f) by (rewrite Hg1; reflexivity).
    assert (G1f : getr regs1 19 = Z_to_bv 64 ctr) by (rewrite Hg1; reflexivity).
    assert (K1 : cs_keep regs1).
    { unfold cs_keep, CRW.cs_keep. repeat match goal with |- _ /\ _ => split end; rewrite Hg1; reflexivity. }
    assert (S1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
    destruct (FRAME m1 MU WM) as (I1 & Hro1 & WM').
    assert (FR1' : cs_frame m1) by (exists junk; exact FR1).
    assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
    { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
      apply (kb_pre_A B API CHECK_RESTAMP_STACK 48 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 48, spZ regs)]
        PRE); [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
        | rewrite S1; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
        | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
        | exact MU | exact WM' | |].
      - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
      - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
    (* the agree room of fuzz_dup's malloc(n) *)
    assert (Hroom : room_ag b n).
    { destruct ROOM as ((R1 & R1') & R2 & R3). apply room_ag_gen; lia. }
    replace (Z_to_bv 64 CRW.CS_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
    eapply (SRcf_bind B).
    { exact (MALLOC L A regs1 m1 md n b Hpre1 Hro1 G1c RES Hroom). }
    intros c' (L1 & A1 & regs2 & m2 & md1 & res & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
      Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
    pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
    assert (I1' : cs_inv L1 A1 m2 md1).
    { apply (cs_inv_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 Hpost);
        [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
        | exact Hgk2]. }
    assert (FR2 : cs_frame m2).
    { apply (cs_frame_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1' Hpost); [lia | intros a []]. }
    rewrite G1a.
    apply (cs_ph2_cf L1 A1 regs2 m2 md1 res d1 d2 I1' Hinit1 Hb1 Hb0 ltac:(lia) Hres1).
    + transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
    + transitivity (getr regs1 8); [apply (Hp2 8); unfold callee_saved; lia | exact G1d].
    + exact G2.
    + transitivity (getr regs1 18); [apply (Hp2 18); unfold callee_saved; lia | exact G1e].
    + transitivity (getr regs1 19); [apply (Hp2 19); unfold callee_saved; lia | exact G1f].
    + exact (cs_keep_pres regs1 regs2 K1 Hp2).
    + exact FR2.
Qed.

End Body.

Theorem check_restamp_holds_cf : check_restamp_contract_cf B API.
Proof.
  intros L A regs mem md f n ctr b _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  eapply cs_entry_cf; eassumption.
Qed.
End CRS.
