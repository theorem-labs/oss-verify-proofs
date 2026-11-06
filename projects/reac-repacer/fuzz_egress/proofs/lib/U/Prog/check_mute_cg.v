(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_egress: the cut-free (SRcf) walk of check_mute on the UBSan image, 0x12f50, against
   lib/U/Prog/check_mute_ccf.v: check_mute_holds_cf, as reac-repacer/fuzz_uci's lib/U/Prog/check_value_cg.v
   (at bc49657c087a) is to its check_value.v. Section CM is lib/U/Prog/check_mute.v's with SR replaced by SRcf
   (SRcf_bind / SRcf_ret, EgressGlue_cg's eg_runA_cf / eg_runN_cf), malloc(n ? n : 1) at the agree room
   (malloc_contract_ag; room_ag_gen from the room premise cm_room_cf), free by the kit's free_contract_cf; memcpy,
   rp_mute and bcmp are Section hypotheses, as there. The instruction segments (CMSeg.cm_seg1, cm_seg2, cm_seg3) and
   the glue lemmas over the allocator invariant (ck_inv, ck_pre, ck_inv_call, ck_inv_A, ck_frame_call, ...), none of
   which mentions SR, are that file's, used as they are (module CMW); its ck_inv_A takes that file's room premise,
   which cm_room_cf implies (cm_room_sr). The aborts and traps that file shows unreachable stay so: the NULL test of
   fuzz_dup's malloc, the memcmp test of the kept bytes, the zero test of the muted ones and the UBSan overflow checks
   on the loop's c + i (CMSeg.cm_seg2). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require
  PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require EgressFrame.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require memcpy_c rp_mute_c bcmp_c.
Import ListNotations.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import check_mute_c memcpy_c rp_mute_c bcmp_c.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import EgressGlue.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import LLVMFuzzerTestOneInput_cfb
  check_mute_ccf EgressGlue_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require check_mute.
Local Open Scope Z_scope.

Module CMW := OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog.check_mute.

Section CM.
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
Hypothesis MC : memcpy_contract.
Hypothesis RPM : rp_mute_contract.
Hypothesis BC : bcmp_contract.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (f n : Z) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CHECK_MUTE_STACK L A regs mem md.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 f.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis HN : 0 <= n <= 1600.
Hypothesis IB : in_block L A f n.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : cm_room_cf b n.

(* check_mute.v's room premise, which its ck_inv_A takes: the agree room implies it (CAP_AG <= CAPMAX) *)
Lemma cm_room_sr : sb_live b + 1 <= sb_cap b <= CAPMAX /\ 0 <= sb_bytes b /\ sb_bytes b + Z.max n 1 <= 2 ^ 40.
Proof. destruct ROOM as (((R1 & R2) & R3) & R4 & R5). unfold CAP_AG, CAPMAX in *. lia. Qed.

(* check_mute.v's invariant, frame, final predicate and glue lemmas at this Section's entry state *)
Let ck_inv := CMW.ck_inv B API L A regs mem md.
Let ck_kept := CMW.ck_kept regs.
Let ck_frame := CMW.ck_frame regs.
Let ck_final := CMW.ck_final B API L A regs mem md b.
Let ck_pre := CMW.ck_pre B API L A regs mem md n PRE.
Let ck_inv_call := CMW.ck_inv_call B API AX CT L A regs mem md n PRE.
Let ck_inv_A := CMW.ck_inv_A B API SEGS L A regs mem md n b PRE HN cm_room_sr.
Let ck_free_keep := CMW.ck_free_keep B API L A regs mem md n.
Let ck_frame_call := CMW.ck_frame_call B API SEGS ERR L A regs mem md n PRE.
Let ck_inv_kept := CMW.ck_inv_kept B API L A regs mem md.
Let ck_kept_pres := CMW.ck_kept_pres regs n.
Let ck_heap_E := CMW.ck_heap_E B API AX n.
Let ck_blk := CMW.ck_blk B API AX.

(* 0x1301c: restore the frame, then free(c) as a tail call. *)
Lemma ck_ph4_cf : forall (fx7 : FPState) L1 A1 regs7 m7 md1 P c1 c2,
  frm_zero (@fp_csr fx7) ->
  ck_inv L1 A1 m7 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = c1 ++ (P, Z.max n 1) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A1 (sb_malloc b (Z.max n 1)) ->
  getr regs7 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs7 8 = Z_to_bv 64 P -> ck_kept regs7 ->
  ck_frame m7 ->
  SRcf B (mkCfg (@mkst fx7 regs7 (Z_to_bv 64 0x1301c) m7 (seg_rom (ms_segs B))) md1) ck_final.
Proof.
  intros fx7 L1 A1 regs7 m7 md1 P c1 c2 Hfrm I Hinit Hb1 Hb0 Hres G2 G8 GK (junk & FR).
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_MUTE_STACK = 8240) by reflexivity.
  assert (Hk : 0 < Z.max n 1) by lia.
  pose proof I as ((M5 & W5 & B5 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m7 md1 M5) as [Hh Hlz].
  assert (USP : bv_unsigned (getr regs7 2) = spZ regs - 48) by (rewrite G2; apply MState.unsigned_lit; lia).
  eapply (eg_runA_cf (fx := fx7) B SEGS regs7 _ m7 md1); [exact Hh | exact Hlz | | |].
  { unfold rmk. eapply CMW.CMSeg.cm_seg3. rewrite USP. exact FR. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs11 -> Hg11. cbn [MState.MS ms_pc_val ms_mem].
  assert (G11a : getr regs11 1 = getr regs 1) by (rewrite Hg11; reflexivity).
  assert (G11b : getr regs11 2 = Z_to_bv 64 (bv_unsigned (getr regs7 2) + 48)) by (rewrite Hg11; reflexivity).
  rewrite USP in G11b. replace (spZ regs - 48 + 48) with (spZ regs) in G11b by lia.
  assert (G11c : getr regs11 4 = getr regs 4) by (rewrite Hg11; exact (proj1 (proj2 GK))).
  assert (G11d : getr regs11 10 = Z_to_bv 64 P) by (rewrite Hg11; exact G8).
  assert (S11 : spZ regs11 = spZ regs) by (unfold spZ at 1; rewrite G11b; apply MState.unsigned_lit; lia).
  assert (P11 : regs_preserved regs regs11).
  { destruct GK as (K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    assert (Hs : getr regs11 2 = getr regs 2) by (rewrite G11b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg11; first [reflexivity | exact K3 | exact K4 | exact K20 | exact K21 | exact K22
        | exact K23 | exact K24 | exact K25 | exact K26 | exact K27]]. }
  destruct (eg_bu L1 A1 P _ ltac:(rewrite Hb1; apply eg_in_mid)) as (p & Hp & Ep).
  assert (Hpre11 : call_pre B (aa_MR API) L1 A1 regs11 m7 md1).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 regs11 m7 md1)).
    apply (ck_pre L1 A1 m7 md1 regs11 0 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia | rewrite S11; exact H16 | exact G11c | rewrite G11a; exact Hra
      | exact Hinit]. }
  replace (Z_to_bv 64 CMW.CMSeg.CM_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply (SRcf_bind B).
  { apply (FREE fx7 L1 A1 regs11 m7 md1 p (Z.max n 1) (sb_malloc b (Z.max n 1)) Hpre11 I4 Hp).
    - rewrite G11d, Ep. reflexivity.
    - exact Hres. }
  intros c' (L6 & A6 & regs12 & m12 & md6 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro6 & Hgk6 & Hub6 &
    Hinit6 & Hlen6 & Hres6).
  apply call_post_k_alloc in Hpost.
  rewrite Ep in Hd1.
  assert (PW5 : pairwise ranges_disjoint (c1 ++ (P, Z.max n 1) :: c2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M5)).
  assert (ND5 : ~ In (P, Z.max n 1) (c1 ++ c2)) by (apply (eg_notin c1 c2 _ PW5); cbn; lia).
  assert (Hb6 : blocks L6 A6 = blocks L A).
  { rewrite Hd2, Hb0. symmetry. apply (eg_rm (P, Z.max n 1) c1 c2 d1 d2 ND5). rewrite <- Hb1. exact Hd1. }
  assert (HD5 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L1 p, Z.max n 1) y).
  { intros y Hy. rewrite Ep. apply (eg_pw_mid c1 c2 _ y PW5). rewrite <- Hb0. exact Hy. }
  assert (HU6 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A6)).
  { intros q k Hq. apply Hub6; [exact (I3 q k Hq) | exact (ck_free_keep L1 A1 m7 md1 p _ I Hp ltac:(lia) HD5 q k Hq)]. }
  assert (I6 : ck_inv L6 A6 m12 md6).
  { apply (ck_inv_call L1 A1 m7 md1 regs11 ALLOC_STACK _ L6 A6 regs12 m12 md6 I Hpost);
      [rewrite S11, HK0; unfold ALLOC_STACK; lia | lia | exact (ck_heap_E L1 A1 m7 md1 p _ M5 Hp) | exact Hlen6
      | exact HU6 | exact Hro6 | exact Hgk6]. }
  apply (SRcf_ret B). exists fx7, L6, A6, regs12, m12, md6.
  split; [rewrite G11a; reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I6 as (I6a & _). apply (kb_post B API); [exact I6a|].
    exact (kb_preserved_trans _ _ _ P11 (proj2 (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost))). }
  split; [exact Hb6|].
  split; [exact (ck_inv_kept _ _ _ _ I6)|].
  destruct I6 as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres6; exact Hres6 | exact (Hinit6 Hinit)].
Qed.

(* 0x12f7c, malloc returned c: the segment up to 0x1301c, in normalized memory, as one eg_runN_cf segment. *)
Lemma ck_ph3_cf : forall L1 A1 regs2 m2 md1 P c1 c2,
  ck_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = c1 ++ (P, Z.max n 1) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A1 (sb_malloc b (Z.max n 1)) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs2 9 = Z_to_bv 64 n -> getr regs2 10 = Z_to_bv 64 P ->
  getr regs2 18 = Z_to_bv 64 f -> ck_kept regs2 -> ck_frame m2 ->
  SRcf B (mkCfg (mkst regs2 (Z_to_bv 64 0x12f7c) m2 (seg_rom (ms_segs B))) md1) ck_final.
Proof.
  intros L1 A1 regs2 m2 md1 P c1 c2 I Hinit Hb1 Hb0 Hres G2 G9 G10 G18 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_MUTE_STACK = 8240) by reflexivity.
  pose proof I as ((M1 & W1 & B1 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  assert (Hro' : ro_agree rsegs m2) by (rewrite <- SEGS; exact I4).
  assert (PW1 : pairwise ranges_disjoint (c1 ++ (P, Z.max n 1) :: c2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1)).
  assert (InP : In (P, Z.max n 1) (blocks L1 A1)) by (rewrite Hb1; apply eg_in_mid).
  destruct (ck_blk L1 A1 m2 md1 P _ M1 InP) as (HP1 & HP2 & HP3 & HPi).
  pose proof IB as (q & k & Hq & Hq1 & Hq2).
  assert (Hq' : In (q, k) (c1 ++ c2)) by (rewrite <- Hb0; exact Hq).
  assert (HqL : In (q, k) (blocks L1 A1)) by (rewrite Hb1; apply eg_in_ins; exact Hq').
  destruct (ck_blk L1 A1 m2 md1 q k M1 HqL) as (HQ1 & HQ2 & _ & HQi).
  pose proof (eg_pw_mid c1 c2 _ _ PW1 Hq') as DPQ. unfold ranges_disjoint in DPQ. cbn [fst snd] in DPQ.
  assert (STf : Frame.stk rsegs (normalize rsegs m2) f (f + n)).
  { rewrite <- SEGS. apply (eg_blk_stk B SEGS m2 f n I4); [lia | lia |].
    intros i Hi. destruct (HQi (f - q + i) ltac:(lia)) as (X1 & X2 & _).
    replace (q + (f - q + i)) with (f + i) in X1, X2 by ring. split; assumption. }
  assert (STc : Frame.stk rsegs (normalize rsegs m2) P (P + n)).
  { rewrite <- SEGS. apply (eg_blk_stk B SEGS m2 P n I4); [lia | lia |].
    intros i Hi. destruct (HPi i ltac:(lia)) as (X1 & X2 & _). split; assumption. }
  destruct (Frame.stk_bytes rsegs _ f (f + n) STf ltac:(lia)) as (bs & HLb & HBf).
  replace (f + n - f) with n in HLb by ring.
  destruct (Frame.stk_carve rsegs _ P (P + n) (Z.to_nat n) STc ltac:(lia)) as (_ & junk & HJ).
  rewrite Z2Nat.id in HJ by lia. replace (P + n - n) with P in HJ by ring.
  eapply (eg_runN_cf B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | exact Hro' | | |].
  { pose proof YM05.alloc_ceiling_lt as Hc47. pose proof (Z.le_max_l n 1) as Hmx.
    unfold rmk. eapply (CMW.CMSeg.cm_seg2 MC RPM BC) with (f := f) (n := n) (c := P) (bs := bs);
      first [ eassumption | exact (mem_inv_normalize rsegs m2) | lia | destruct DPQ; [left | right]; lia ]. }
  { intros ms (ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & t3' & t4' &
      t5' & t6' & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & t3' &
    t4' & t5' & t6' & m' & -> & MU & WM) Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR). cbn [ms_mem MState.MS] in HR.
  set (W := [(P, P + n)]) in MU.
  pose proof (mem_rel_normalize rsegs m2 Hro') as HR6.
  pose proof (munch_rel rsegs _ m2 _ (ms_mem ms) m' HR6 HR Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m2 _ (ms_mem ms) m' HR6 HR Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m2 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (PRES : forall x, m2 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (eg_pres B m2 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    unfold W in Hout. cbn [Frame.outside] in Hout.
    apply (eg_fs_none B SEGS). destruct (HPi (bv_unsigned x - P) ltac:(lia)) as (_ & Hn & _).
    replace (P + (bv_unsigned x - P)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CHECK_MUTE_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L1 A1 x /\
      forall p n0 i, In (p, n0) (user_blocks A) -> 0 <= i < n0 -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. unfold W in Hout. cbn [Frame.outside] in Hout. right.
    destruct (HPi (x - P) ltac:(lia)) as (_ & Hn1 & Hn2). replace (P + (x - P)) with x in Hn1, Hn2 by ring.
    split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
    intros p n0 i Hp Hi E.
    assert (Y1 : In (ptr_addr L p, n0) (c1 ++ c2)) by (rewrite <- Hb0; exact (eg_ub L A p n0 Hp)).
    pose proof (eg_pw_mid c1 c2 _ _ PW1 Y1) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia. }
  pose proof (ck_inv_A L1 A1 m2 md1 (ms_mem ms) W I MU7 WM7 PRES HWW RO7) as I7.
  assert (FR7 : ck_frame (ms_mem ms)).
  { destruct FR as (junk' & FRc). exists junk'. rewrite <- SEGS in FRc |- *.
    apply (eg_cells_keep B m2 (ms_mem ms) _ _ FRc). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
    apply MU7. rewrite MState.unsigned_lit by lia. unfold W. cbn [Frame.outside]. repeat split; lia. }
  destruct GK as (K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  apply (ck_ph4_cf (mkFP fp_regs fp_csr) L1 A1 regs7 (ms_mem ms) md1 P c1 c2 FRM I7 Hinit Hb1 Hb0 Hres);
    [rewrite Hg7; exact G2 | rewrite Hg7; reflexivity | | exact FR7].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))); rewrite Hg7;
    first [exact K3 | exact K4 | exact K20 | exact K21 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26
      | exact K27].
Qed.

(* Entry: the frame, then malloc(n ? n : 1) at the agree room. *)
Lemma ck_entry_cf :
  SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_MUTE) mem (seg_rom (ms_segs B))) md) ck_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_MUTE_STACK = 8240) by reflexivity.
  pose proof (eg_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  pose proof IB as (q & k & Hq & Hq1 & Hq2).
  destruct (ck_blk L A mem md q k HM Hq) as (HQ1 & HQ2 & _).
  assert (I0 : ck_inv L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p n0 Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : Frame.stk rsegs mem (spZ regs - CHECK_MUTE_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CHECK_MUTE_STACK L A regs mem md PRE ltac:(lia))).
  eapply (eg_runA_cf B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
  { unfold rmk, CHECK_MUTE. rewrite R10, R11.
    eapply CMW.CMSeg.cm_seg1; [exact ST | unfold spZ; lia | lia | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> & _).
    repeat split; reflexivity. }
  intros ms regs1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> &
    MU & WM & FR1) Hg1.
  cbn [MState.MS ms_pc_val ms_mem].
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x12f7c) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg1; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 (Z.max n 1)) by (rewrite Hg1; reflexivity).
  assert (G1d : getr regs1 9 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
  assert (G1e : getr regs1 18 = Z_to_bv 64 f) by (rewrite Hg1; reflexivity).
  assert (K1 : ck_kept regs1)
    by (refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))); rewrite Hg1;
        reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 48, spZ regs)] x -> spZ regs - 48 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
  assert (Hro1 : ro_agree (ms_segs B) m1).
  { apply (eg_ro_munch B _ mem m1 RO MU). intros a Ha Ho. apply (eg_fs_high B HIL). pose proof (Hout a Ho). lia. }
  assert (I1 : ck_inv L A m1 md).
  { apply (ck_inv_A L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 48, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (eg_pres B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (eg_fs_high B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  assert (FR1' : ck_frame m1) by (exists junk; exact FR1).
  assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
    apply (kb_pre_A B API CHECK_MUTE_STACK 48 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 48, spZ regs)] PRE);
      [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
      | rewrite S1; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact MU | exact WM' | |].
    - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
  (* the agree room of fuzz_dup's malloc(n ? n : 1) *)
  assert (Hroom : room_ag b (Z.max n 1)).
  { destruct ROOM as ((R1 & R1') & R2 & R3). apply room_ag_gen; lia. }
  replace (Z_to_bv 64 CMW.CMSeg.CM_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply (SRcf_bind B).
  { exact (MALLOC L A regs1 m1 md (Z.max n 1) b Hpre1 Hro1 G1c RES Hroom). }
  intros c' (L1 & A1 & regs2 & m2 & md1 & res & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
    Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
  assert (I1' : ck_inv L1 A1 m2 md1).
  { apply (ck_inv_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 Hpost);
      [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
      | exact Hgk2]. }
  assert (FR2 : ck_frame m2).
  { apply (ck_frame_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1' Hpost); [lia | intros a []]. }
  rewrite G1a.
  apply (ck_ph3_cf L1 A1 regs2 m2 md1 res d1 d2 I1' Hinit1 Hb1 Hb0 Hres1).
  - transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
  - transitivity (getr regs1 9); [apply (Hp2 9); unfold callee_saved; lia | exact G1d].
  - exact G2.
  - transitivity (getr regs1 18); [apply (Hp2 18); unfold callee_saved; lia | exact G1e].
  - exact (ck_kept_pres regs1 regs2 K1 Hp2).
  - exact FR2.
Qed.

End Body.

Theorem check_mute_holds_cf : check_mute_contract_cf B API.
Proof.
  intros L A regs mem md f n b _ H1 H2 H3 H4 H5 H6 H7 H8 H9.
  eapply ck_entry_cf; eassumption.
Qed.
End CM.
