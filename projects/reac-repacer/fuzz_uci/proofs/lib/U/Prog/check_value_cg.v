(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the cut-free (SRcf) walk of check_value on the UBSan
   image, 0x12e48, against lib/U/Prog/check_value_ccf.v: check_value_holds_cf, as libreac/fuzz_decode's released
   lib/U/Prog/check_round_trip_cg.v is to its check_round_trip.v. Section CV is lib/U/Prog/check_value.v's with SR
   replaced by SRcf (SRcf_bind / SRcf_ret, CheckGlue_cg's crt_runA_cf / crt_runN_cf), fuzz_dup's malloc at the agree
   room (malloc_contract_ag; room_ag_gen for FuzzDup.v's fuzz_dup_room), free by the kit's free_contract_cf, and the
   room premise cv_room_cf; the instruction segments (cv_seg1 / cv_seg2 / cv_seg3, with expected_value's walk) are
   that file's, used as they are (module CVW). The aborts and traps that file's header shows unreachable stay so. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac
  Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import CheckGlue FuzzDup memcpy_c rp_uci_int_c
  check_no_overread_c check_value_c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import LLVMFuzzerTestOneInput_cfb check_value_ccf
  CheckGlue_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require check_value.
Import ListNotations.
Local Open Scope Z_scope.

Module CVW := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog.check_value.

(* From here on the names are the contract's: the allocator's ceiling (lib/U/Reusable/YM05.v) and YK11's getr /
   mkst, which the Lib imports above shadow *)
Local Abbreviation alloc_ceiling := YM05.alloc_ceiling (only parsing).
Local Abbreviation getr := YK11.getr (only parsing).
Local Abbreviation mkst := YK11.mkst (only parsing).

Section CV.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = 0x13f74.
Hypothesis FREEPC : ms_free B = 0x13e34.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis MALLOC : malloc_contract_ag B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis MC : memcpy_contract.
Hypothesis RUI : rp_uci_int_contract.

Lemma cv_blk_bytes : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  blk_data B m a bs -> bytes_at rsegs m a bs.
Proof.
  intros m a bs H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, SEGS. reflexivity.
Qed.

(* a heap block, seen in the normalized memory of a crt_runN_cf segment, is stack-like: writable and readable *)
Lemma cv_blk_stk : forall m a k, ro_agree (ms_segs B) m -> 0 <= a -> a + k <= 2 ^ 64 ->
  (forall i, 0 <= i < k -> present m (a + i) /\ ~ in_img B (a + i)) ->
  stk rsegs (normalize rsegs m) a (a + k).
Proof.
  intros m a k Hro H0 H1 H. rewrite <- SEGS.
  pose proof (mem_rel_normalize (ms_segs B) m Hro) as HR.
  split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H (x - a) ltac:(lia)) as [[bt Hb] Hni]. replace (a + (x - a)) with x in Hb, Hni by ring.
  assert (Hra : Mem.ro_addr (ms_segs B) (Mem.wa x) = false)
    by (apply crt_ro_false; [lia | exact (crt_fs_none B SEGS x Hni)]).
  split.
  - rewrite (wview_rel_rw (ms_segs B) m _ _ HR Hra). unfold wview, Mem.wa. rewrite Hb. discriminate.
  - exists bt. rewrite <- (mrd_rel (ms_segs B) m _ _ HR). unfold Mem.mrd, Mem.wa. rewrite Hb. reflexivity.
Qed.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (r n cur : Z) (bs : list byte) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CV_STACK L A regs mem md.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 r.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis R12 : getr regs 12 = Z_to_bv 64 cur.
Hypothesis HC : INT_MIN <= cur <= INT_MAX.
Hypothesis HN : 0 <= n <= REPLY_MAX.
Hypothesis HL : Z.of_nat (length bs) = n.
Hypothesis BD : blk_data B mem r bs.
Hypothesis IB : 0 < n -> in_block L A r n.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : cv_room_cf b n.

Let cv_inv := cg_inv B API CV_STACK L A regs mem md.

Definition cv_keep (r' : bvmap 5 word) : Prop :=
  getr r' 3 = getr regs 3 /\ getr r' 4 = getr regs 4 /\ getr r' 21 = getr regs 21 /\ getr r' 22 = getr regs 22 /\
  getr r' 23 = getr regs 23 /\ getr r' 24 = getr regs 24 /\ getr r' 25 = getr regs 25 /\
  getr r' 26 = getr regs 26 /\ getr r' 27 = getr regs 27.

Definition cv_frame (m' : word -> option byte) : Prop :=
  rw_cells rsegs m' (spZ regs - 48) [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
    C8 (getr regs 8); C8 (getr regs 1)].

Definition cv_final (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_k B (aa_MR API) CV_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur) /\
    blocks L' A' = blocks L A /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    guard_kept B mem mem' /\
    ro_agree (ms_segs B) mem' /\
    res_ok_slots A' b /\
    st_init_done A' = true.

Lemma cv_keep_pres : forall r1 r2, cv_keep r1 -> regs_preserved r1 r2 -> cv_keep r2.
Proof.
  intros r1 r2 (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27) Hp.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - transitivity (getr r1 3); [apply (Hp 3); unfold callee_saved; lia | exact K3].
  - transitivity (getr r1 4); [apply (Hp 4); unfold callee_saved; lia | exact K4].
  - transitivity (getr r1 21); [apply (Hp 21); unfold callee_saved; lia | exact K21].
  - transitivity (getr r1 22); [apply (Hp 22); unfold callee_saved; lia | exact K22].
  - transitivity (getr r1 23); [apply (Hp 23); unfold callee_saved; lia | exact K23].
  - transitivity (getr r1 24); [apply (Hp 24); unfold callee_saved; lia | exact K24].
  - transitivity (getr r1 25); [apply (Hp 25); unfold callee_saved; lia | exact K25].
  - transitivity (getr r1 26); [apply (Hp 26); unfold callee_saved; lia | exact K26].
  - transitivity (getr r1 27); [apply (Hp 27); unfold callee_saved; lia | exact K27].
Qed.

Lemma cv_frame_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cv_inv Lk Ak mk mdk -> cv_frame mk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regsk <= spZ regs - 48 -> (forall a, E2 a -> a < alloc_ceiling) ->
  cv_frame m2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 I FR Hpost Hsp HE.
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  unfold cv_frame in *. rewrite <- SEGS in FR |- *.
  assert (HK0 : CV_STACK = 8240) by reflexivity.
  apply (cg_cells_call B API CV_STACK L A regs mem md PRE Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 _ _ I FR Hpost);
    [lia | cbn [Cells.cells_size Cells.csize Nat.add]; lia | exact Hsp | exact HE | exact ERR].
Qed.

(* free(c) at 0x1302c, entered at free with ra = 0x13030, then the epilogue 0x13030 - 0x13050 *)
Lemma cv_ph3_cf : forall (fx7 : FPState) L3 A3 regs7 m7 md3 P c1 c2,
  frm_zero (@fp_csr fx7) ->
  cv_inv L3 A3 m7 md3 -> st_init_done A3 = true ->
  blocks L3 A3 = c1 ++ (P, fuzz_dup_size n) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A3 (sb_malloc b (fuzz_dup_size n)) ->
  getr regs7 1 = Z_to_bv 64 0x13030 -> getr regs7 2 = Z_to_bv 64 (spZ regs - 48) ->
  getr regs7 10 = Z_to_bv 64 P -> getr regs7 18 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur) ->
  cv_keep regs7 -> cv_frame m7 ->
  SRcf B (mkCfg (@mkst fx7 regs7 (Z_to_bv 64 CVW.CV_FREE) m7 (seg_rom (ms_segs B))) md3) cv_final.
Proof.
  intros fx7 L3 A3 regs7 m7 md3 P c1 c2 Hfrm I Hinit Hb3 Hb0 Hres G1 G2 G10 G18 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CV_STACK = 8240) by reflexivity.
  pose proof HN as HN'. unfold REPLY_MAX in HN'.
  pose proof (fuzz_dup_size_range n ltac:(lia)) as [Z1 Z2].
  pose proof I as ((M3 & W3 & B3 & _) & I2 & I3 & I4 & I5).
  assert (S7 : spZ regs7 = spZ regs - 48) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  assert (PW3 : pairwise ranges_disjoint (c1 ++ (P, fuzz_dup_size n) :: c2))
    by (rewrite <- Hb3; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M3)).
  destruct (crt_bu L3 A3 P _ ltac:(rewrite Hb3; apply crt_in_mid)) as (p & Hp & Ep).
  assert (Hpre7 : call_pre B (aa_MR API) L3 A3 regs7 m7 md3).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L3 A3 regs7 m7 md3)).
    apply (cg_pre B API CV_STACK L A regs mem md PRE L3 A3 m7 md3 regs7 48 ALLOC_STACK I);
      [lia | lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S7; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj1 (proj2 GK)) | rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  replace (Z_to_bv 64 CVW.CV_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply (SRcf_bind B).
  { apply (FREE fx7 L3 A3 regs7 m7 md3 p (fuzz_dup_size n) (sb_malloc b (fuzz_dup_size n)) Hpre7 I4 Hp).
    - rewrite G10, Ep. reflexivity.
    - exact Hres. }
  intros c' (L4 & A4 & regs8 & m8 & md4 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro4 & Hgk4 & Hub4 &
    Hinit4 & Hlen4 & Hres4).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp8 & _).
  rewrite Ep in Hd1.
  assert (ND3 : ~ In (P, fuzz_dup_size n) (c1 ++ c2)) by (apply (crt_notin c1 c2 _ PW3); cbn; lia).
  assert (Hb4 : blocks L4 A4 = blocks L A).
  { rewrite Hd2, Hb0. symmetry. apply (crt_rm (P, fuzz_dup_size n) c1 c2 d1 d2 ND3). rewrite <- Hb3. exact Hd1. }
  assert (HD3 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L3 p, fuzz_dup_size n) y).
  { intros y Hy. rewrite Ep. apply (crt_pw_mid c1 c2 _ y PW3). rewrite <- Hb0. exact Hy. }
  assert (HU4 : forall q' k, In (q', k) (user_blocks A) -> In (q', k) (user_blocks A4)).
  { intros q' k Hq'. apply Hub4;
      [exact (I3 q' k Hq') | exact (cg_free_keep B API CV_STACK L A regs mem md L3 A3 m7 md3 p _ I Hp
        ltac:(lia) HD3 q' k Hq')]. }
  assert (I4' : cv_inv L4 A4 m8 md4).
  { apply (cg_inv_call B API CV_STACK L A regs mem md PRE AX CT L3 A3 m7 md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8
      md4 I Hpost);
      [rewrite S7, HK0; unfold ALLOC_STACK; lia | lia | exact (crt_heap_E B API L3 A3 m7 md3 p _ AX M3 Hp)
      | exact Hlen4 | exact HU4 | exact Hro4 | exact Hgk4]. }
  assert (FR4 : cv_frame m8).
  { apply (cv_frame_call L3 A3 m7 md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8 md4 I FR Hpost); [lia |].
    intros a Ha. exact (proj1 (crt_heap_E B API L3 A3 m7 md3 p _ AX M3 Hp a Ha)). }
  assert (G8a : getr regs8 2 = Z_to_bv 64 (spZ regs - 48))
    by (transitivity (getr regs7 2); [apply (Hp8 2); unfold callee_saved; lia | exact G2]).
  assert (G8b : getr regs8 18 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur))
    by (transitivity (getr regs7 18); [apply (Hp8 18); unfold callee_saved; lia | exact G18]).
  pose proof (cv_keep_pres regs7 regs8 GK Hp8) as GK8.
  (* the epilogue *)
  pose proof I4' as ((M4 & _) & _ & _ & _ & _).
  destruct (kb_md B API L4 A4 m8 md4 M4) as [Hh Hlz].
  assert (USP : bv_unsigned (getr regs8 2) = spZ regs - 48) by (rewrite G8a; apply MState.unsigned_lit; lia).
  rewrite G1.
  eapply (crt_runA_cf (fx := fx7) B SEGS regs8 _ m8 md4); [exact Hh | exact Hlz | | |].
  { unfold rmk. eapply CVW.cv_seg3. rewrite USP. exact FR4. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs9 -> Hg9. cbn [MState.MS ms_pc_val ms_mem].
  rewrite (kb_ret_pc _ Hra).
  assert (G9a : getr regs9 1 = getr regs 1) by (rewrite Hg9; reflexivity).
  assert (G9b : getr regs9 2 = Z_to_bv 64 (bv_unsigned (getr regs8 2) + 48)) by (rewrite Hg9; reflexivity).
  rewrite USP in G9b. replace (spZ regs - 48 + 48) with (spZ regs) in G9b by lia.
  assert (G9c : getr regs9 10 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur)) by (rewrite Hg9; exact G8b).
  assert (P9 : regs_preserved regs regs9).
  { destruct GK8 as (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    assert (Hs : getr regs9 2 = getr regs 2) by (rewrite G9b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r' Hr. unfold callee_saved in Hr.
    assert (C : r' = 2 \/ r' = 3 \/ r' = 4 \/ r' = 8 \/ r' = 9 \/ r' = 18 \/ r' = 19 \/ r' = 20 \/ r' = 21 \/
                r' = 22 \/ r' = 23 \/ r' = 24 \/ r' = 25 \/ r' = 26 \/ r' = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg9; first [reflexivity | exact K3 | exact K4 | exact K21 | exact K22 | exact K23
        | exact K24 | exact K25 | exact K26 | exact K27]]. }
  apply (SRcf_ret B). exists fx7, L4, A4, regs9, m8, md4.
  split; [reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I4' as (I4a & _). apply (kb_post B API); [exact I4a | exact P9]. }
  split; [exact G9c|].
  split; [exact Hb4|].
  split; [exact (cg_inv_kept B API CV_STACK L A regs mem md _ _ _ _ I4')|].
  destruct I4' as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres4; exact Hres4 | exact (Hinit4 Hinit)].
Qed.

(* 0x12e7c - 0x1302c as one crt_runN_cf segment over the normalized memory (cv_seg2) *)
Lemma cv_ph2_cf : forall L1 A1 regs2 m2 md1 P c1 c2,
  cv_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = c1 ++ (P, fuzz_dup_size n) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A1 (sb_malloc b (fuzz_dup_size n)) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs2 8 = Z_to_bv 64 cur -> getr regs2 10 = Z_to_bv 64 P ->
  getr regs2 19 = Z_to_bv 64 n -> getr regs2 20 = Z_to_bv 64 r ->
  cv_keep regs2 -> cv_frame m2 ->
  SRcf B (mkCfg (mkst regs2 (Z_to_bv 64 0x12e7c) m2 (seg_rom (ms_segs B))) md1) cv_final.
Proof.
  intros L1 A1 regs2 m2 md1 P c1 c2 I Hinit Hb1 Hb0 Hres G2 G8 G10 G19 G20 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CV_STACK = 8240) by reflexivity.
  pose proof HN as HN'. unfold REPLY_MAX in HN'.
  pose proof (fuzz_dup_size_range n ltac:(lia)) as [Z1 Z2].
  pose proof I as ((M1 & W1 & B1 & _ & _ & _ & _ & _ & S1) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  pose proof (crt_img_low B SEGS) as HIL.
  assert (USP : bv_unsigned (getr regs2 2) = spZ regs - 48) by (rewrite G2; apply MState.unsigned_lit; lia).
  assert (Hro' : ro_agree rsegs m2) by (rewrite <- SEGS; exact I4).
  assert (PW1 : pairwise ranges_disjoint (c1 ++ (P, fuzz_dup_size n) :: c2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1)).
  assert (InP : In (P, fuzz_dup_size n) (blocks L1 A1)) by (rewrite Hb1; apply crt_in_mid).
  destruct (crt_blk B API AX L1 A1 m2 md1 P _ M1 InP) as (HP1 & HP2 & _ & HPi).
  (* the reply r: inside an old block, so apart from the new one and kept since entry *)
  assert (HR : 0 < n -> 4096 <= r /\ r + n <= spZ regs - 48 - 32 /\ (r + n <= P \/ P + n <= r) /\
                bytes_at rsegs (normalize rsegs m2) r bs).
  { intros Hn. destruct (IB Hn) as (qa & ka & Hqa & Ha1 & Ha2).
    destruct (crt_blk B API AX L A mem md qa ka HM Hqa) as (HA1 & HA2 & _).
    assert (Ac : In (qa, ka) (c1 ++ c2)) by (rewrite <- Hb0; exact Hqa).
    pose proof (crt_pw _ _ _ _ _ _ PW1 Ac) as DPA.
    assert (Hnz : fuzz_dup_size n = n) by (unfold fuzz_dup_size; destruct (Z.eqb_spec n 0); lia).
    split; [lia|]. split; [lia|]. split; [lia|].
    apply (bytes_at_normalize rsegs); [exact Hro'|].
    apply cv_blk_bytes; [lia | lia |].
    pose proof (cg_inv_kept B API CV_STACK L A regs mem md _ _ _ _ I) as KP.
    intros i Hi. rewrite <- (BD i Hi).
    pose proof (KP qa ka (r - qa + i) Hqa (fun H => H) ltac:(lia)) as E.
    replace (qa + (r - qa + i)) with (r + i) in E by ring. exact E. }
  assert (Hold : forall y, In y (blocks L A) -> In y (c1 ++ c2)) by (intros y Hy; rewrite <- Hb0; exact Hy).
  assert (ST : stk rsegs (normalize rsegs m2) (spZ regs - 48 - 32) (spZ regs - 48)).
  { rewrite <- SEGS. apply (crt_stk_norm B HIL); [| exact I4 | lia].
    apply (crt_stk B HIL); [lia | lia |]. intros a Ha. apply S1. left. lia. }
  assert (SPn : stk rsegs (normalize rsegs m2) P (P + fuzz_dup_size n)).
  { apply cv_blk_stk; [exact I4 | lia | lia |].
    intros i Hi. destruct (HPi i Hi) as (X1 & X2 & _). split; assumption. }
  eapply (crt_runN_cf B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G8, G10, G19, G20.
    apply (CVW.cv_seg2 MC RUI) with (r := r) (n := n) (cur := cur) (P := P) (bs := bs);
      rewrite ?USP; first [exact HL | exact HC | exact HR | exact (mem_inv_normalize rsegs m2) | exact SPn
        | exact ST | lia]. }
  { intros ms (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & x3 & x4 & x5 & x6 & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & x3 & x4 & x5 & x6 & m' & -> &
    MU & WM & MI') Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR'). cbn [ms_mem MState.MS] in HR'.
  rewrite USP in MU. unfold CVW.cv_W in MU.
  set (W := [(spZ regs - 48 - 32, spZ regs - 48); (P, P + fuzz_dup_size n)]) in MU.
  pose proof (mem_rel_normalize rsegs m2 Hro') as HR6.
  pose proof (munch_rel rsegs _ m2 _ (ms_mem ms) m' HR6 HR' Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m2 _ (ms_mem ms) m' HR6 HR' Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m2 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (PRES : forall x, m2 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (crt_pres B m2 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    destruct (CVW.cv_not_out2 _ _ _ _ _ Hout) as [Hs|Hs].
    - apply (crt_fs_high B HIL). lia.
    - apply (crt_fs_none B SEGS). destruct (HPi (bv_unsigned x - P) ltac:(lia)) as (_ & Hn & _).
      replace (P + (bv_unsigned x - P)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CV_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L1 A1 x /\
      forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. destruct (CVW.cv_not_out2 _ _ _ _ _ Hout) as [Hs|Hs].
    - left. lia.
    - right. destruct (HPi (x - P) ltac:(lia)) as (_ & Hn1 & Hn2).
      replace (P + (x - P)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p k i Hp Hi E. pose proof (Hold _ (crt_ub L A p k Hp)) as Y1.
      pose proof (crt_pw _ _ _ _ _ _ PW1 Y1). lia. }
  pose proof (cg_inv_A B API CV_STACK L A regs mem md PRE SEGS L1 A1 m2 md1 (ms_mem ms) W I MU7 WM7 PRES HWW RO7)
    as I7.
  assert (FR7 : cv_frame (ms_mem ms)).
  { unfold cv_frame in *. rewrite <- SEGS in FR |- *.
    apply (crt_cells_keep B m2 (ms_mem ms) _ _ FR). intros i Hi.
    change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
    apply MU7. rewrite MState.unsigned_lit by lia. unfold W. cbn [Frame.outside]. repeat split; lia. }
  destruct GK as (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  cbn [MState.MS ms_pc_val ms_fregs ms_fcsr].
  apply (cv_ph3_cf (mkFP fp_regs fp_csr) L1 A1 regs7 (ms_mem ms) md1 P c1 c2 FRM I7 Hinit Hb1 Hb0 Hres);
    [rewrite Hg7; reflexivity | rewrite Hg7; exact G2 | rewrite Hg7; reflexivity | rewrite Hg7; reflexivity
    | | exact FR7].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); rewrite Hg7;
    first [exact K3 | exact K4 | exact K21 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26 | exact K27].
Qed.

(* 0x12e48 - 0x12e78 and malloc(n ? n : 1), fuzz_dup's allocation *)
Lemma cv_entry_cf :
  SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_VALUE) mem (seg_rom (ms_segs B))) md) cv_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CV_STACK = 8240) by reflexivity.
  pose proof HN as HN'. unfold REPLY_MAX in HN'.
  pose proof (crt_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  assert (I0 : cv_inv L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p k Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : stk rsegs mem (spZ regs - CV_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CV_STACK L A regs mem md PRE ltac:(lia))).
  eapply (crt_runA_cf B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
  { unfold rmk. rewrite R10, R11, R12. eapply CVW.cv_seg1; [exact ST | unfold spZ in *; lia | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & _).
    repeat split; reflexivity. }
  intros ms regs1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
    MU & WM & FR1) Hg1.
  cbn [MState.MS ms_pc_val ms_mem].
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x12e7c) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg1; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 (fuzz_dup_size n)) by (rewrite Hg1; reflexivity).
  assert (G1d : getr regs1 8 = Z_to_bv 64 cur) by (rewrite Hg1; reflexivity).
  assert (G1f : getr regs1 19 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
  assert (G1g : getr regs1 20 = Z_to_bv 64 r) by (rewrite Hg1; reflexivity).
  assert (K1 : cv_keep regs1)
    by (refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); rewrite Hg1; reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 48, spZ regs)] x -> spZ regs - 48 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
  assert (Hro1 : ro_agree (ms_segs B) m1).
  { apply (crt_ro_munch B _ mem m1 RO MU). intros a Ha Ho. apply (crt_fs_high B HIL). pose proof (Hout a Ho). lia. }
  assert (I1 : cv_inv L A m1 md).
  { apply (cg_inv_A B API CV_STACK L A regs mem md PRE SEGS L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 48, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (crt_pres B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (crt_fs_high B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
    apply (kb_pre_A B API CV_STACK 48 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 48, spZ regs)] PRE);
      [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
      | rewrite S1; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact MU | exact WM' | |].
    - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (Hroom : room_ag b (fuzz_dup_size n)).
  { destruct ROOM as ((R1 & R1') & R2 & R3). pose proof HN as HN0. unfold REPLY_MAX in HN0.
    pose proof (fuzz_dup_size_range n ltac:(lia)) as [Z1 Z2]. apply room_ag_gen; lia. }
  replace (Z_to_bv 64 CVW.CV_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply (SRcf_bind B).
  { exact (MALLOC L A regs1 m1 md (fuzz_dup_size n) b Hpre1 Hro1 G1c RES Hroom). }
  intros c' (L1 & A1 & regs2 & m2 & md1 & res & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
    Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
  assert (I1' : cv_inv L1 A1 m2 md1).
  { apply (cg_inv_call B API CV_STACK L A regs mem md PRE AX CT L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1
      Hpost);
      [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
      | exact Hgk2]. }
  assert (FR2 : cv_frame m2).
  { apply (cv_frame_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1 Hpost); [lia | intros a []]. }
  rewrite G1a.
  apply (cv_ph2_cf L1 A1 regs2 m2 md1 res d1 d2 I1' Hinit1 Hb1 Hb0 Hres1).
  - transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
  - transitivity (getr regs1 8); [apply (Hp2 8); unfold callee_saved; lia | exact G1d].
  - exact G2.
  - transitivity (getr regs1 19); [apply (Hp2 19); unfold callee_saved; lia | exact G1f].
  - transitivity (getr regs1 20); [apply (Hp2 20); unfold callee_saved; lia | exact G1g].
  - exact (cv_keep_pres regs1 regs2 K1 Hp2).
  - exact FR2.
Qed.

End Body.

Theorem check_value_holds_cf : check_value_contract_cf B API.
Proof.
  intros L A regs mem md r n cur bs b _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
  eapply cv_entry_cf; eassumption.
Qed.
End CV.
