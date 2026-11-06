(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the cut-free (SRcf) walk of check_no_overread on the UBSan
   image, 0x12d54, against lib/U/Prog/check_no_overread_ccf.v: check_no_overread_holds_cf, as libreac/fuzz_decode's
   released lib/U/Prog/check_round_trip_cg.v is to its check_round_trip.v. Section CNO is lib/U/Prog/check_no_overread.v's
   with SR replaced by SRcf (SRcf_bind / SRcf_ret, CheckGlue_cg's crt_runA_cf / crt_runN_cf), malloc at the agree room
   (malloc_contract_ag with room_ag_gen for room_slots_small), free by the kit's free_contract_cf, and the room premise
   cno_room_cf; the instruction segments (cno_seg1 / cno_seg2 / cno_seg3 / cno_seg5) and list lemmas are that file's,
   used as they are (module CN). The same 59 of 61 instructions are walked, for the same reasons (that file's header):
   the abort call 0x12e40 and the trap 0x12e44 never run. *)
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
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import CheckGlue memcpy_c rp_uci_int_c
  check_no_overread_c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import LLVMFuzzerTestOneInput_cfb check_no_overread_ccf
  CheckGlue_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require check_no_overread.
Import ListNotations.
Local Open Scope Z_scope.

Module CN := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog.check_no_overread.

(* From here on the names are the contract's: the allocator's ceiling (lib/U/Reusable/YM05.v), not the kit's
   Lib/Ceiling.v class, and YK11's getr / mkst, not Lib/PropExec.v's, which the Lib imports above shadow them with *)
Local Abbreviation alloc_ceiling := YM05.alloc_ceiling (only parsing).
Local Abbreviation getr := YK11.getr (only parsing).
Local Abbreviation mkst := YK11.mkst (only parsing).

Section CNO.
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

Lemma cno_blk_bytes : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  blk_data B m a bs -> bytes_at rsegs m a bs.
Proof.
  intros m a bs H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, SEGS. reflexivity.
Qed.

(* a heap block, seen in the normalized memory of a crt_runN_cf segment, is stack-like: writable and readable *)
Lemma cno_blk_stk : forall m a k, ro_agree (ms_segs B) m -> 0 <= a -> a + k <= 2 ^ 64 ->
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
Hypothesis PRE : call_pre_k B (aa_MR API) CNO_STACK L A regs mem md.
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
Hypothesis ROOM : cno_room_cf b n.

Let cno_inv := cg_inv B API CNO_STACK L A regs mem md.

Definition cno_keep (r' : bvmap 5 word) : Prop :=
  getr r' 3 = getr regs 3 /\ getr r' 4 = getr regs 4 /\ getr r' 21 = getr regs 21 /\ getr r' 22 = getr regs 22 /\
  getr r' 23 = getr regs 23 /\ getr r' 24 = getr regs 24 /\ getr r' 25 = getr regs 25 /\
  getr r' 26 = getr regs 26 /\ getr r' 27 = getr regs 27.

Definition cno_frame (m' : word -> option byte) : Prop :=
  rw_cells rsegs m' (spZ regs - 48) [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
    C8 (getr regs 8); C8 (getr regs 1)].

Definition cno_final (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_k B (aa_MR API) CNO_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    blocks L' A' = blocks L A /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    guard_kept B mem mem' /\
    ro_agree (ms_segs B) mem' /\
    res_ok_slots A' b /\
    st_init_done A' = true.

Lemma cno_keep_pres : forall r1 r2, cno_keep r1 -> regs_preserved r1 r2 -> cno_keep r2.
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

Lemma cno_frame_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cno_inv Lk Ak mk mdk -> cno_frame mk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regsk <= spZ regs - 48 -> (forall a, E2 a -> a < alloc_ceiling) ->
  cno_frame m2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 I FR Hpost Hsp HE.
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  unfold cno_frame in *. rewrite <- SEGS in FR |- *.
  assert (HK0 : CNO_STACK = 8240) by reflexivity.
  apply (cg_cells_call B API CNO_STACK L A regs mem md PRE Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 _ _ I FR Hpost);
    [lia | cbn [Cells.cells_size Cells.csize Nat.add]; lia | exact Hsp | exact HE | exact ERR].
Qed.

(* 0x12e1c-0x12e3c (cno_seg5) and the tail call free(b) *)
Lemma cno_ph5_cf : forall (fx7 : FPState) L5 A5 regs10 m10 md5 Q f1 f2,
  frm_zero (@fp_csr fx7) ->
  cno_inv L5 A5 m10 md5 -> st_init_done A5 = true ->
  blocks L5 A5 = f1 ++ (Q, n + 1) :: f2 -> blocks L A = f1 ++ f2 ->
  res_ok_slots A5 (sb_malloc b (n + 1)) ->
  getr regs10 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs10 18 = Z_to_bv 64 Q -> cno_keep regs10 ->
  cno_frame m10 ->
  SRcf B (mkCfg (@mkst fx7 regs10 (Z_to_bv 64 0x12e1c) m10 (seg_rom (ms_segs B))) md5) cno_final.
Proof.
  intros fx7 L5 A5 regs10 m10 md5 Q f1 f2 Hfrm I Hinit Hb5 Hb0 Hres G2 G18 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CNO_STACK = 8240) by reflexivity.
  pose proof I as ((M5 & W5 & B5 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L5 A5 m10 md5 M5) as [Hh Hlz].
  assert (USP : bv_unsigned (getr regs10 2) = spZ regs - 48) by (rewrite G2; apply MState.unsigned_lit; lia).
  eapply (crt_runA_cf (fx := fx7) B SEGS regs10 _ m10 md5); [exact Hh | exact Hlz | | |].
  { unfold rmk. eapply CN.cno_seg5. rewrite USP. exact FR. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs11 -> Hg11. cbn [MState.MS ms_pc_val ms_mem].
  assert (G11a : getr regs11 1 = getr regs 1) by (rewrite Hg11; reflexivity).
  assert (G11b : getr regs11 2 = Z_to_bv 64 (bv_unsigned (getr regs10 2) + 48)) by (rewrite Hg11; reflexivity).
  rewrite USP in G11b. replace (spZ regs - 48 + 48) with (spZ regs) in G11b by lia.
  assert (G11c : getr regs11 4 = getr regs 4) by (rewrite Hg11; exact (proj1 (proj2 GK))).
  assert (G11d : getr regs11 10 = Z_to_bv 64 Q) by (rewrite Hg11; exact G18).
  assert (S11 : spZ regs11 = spZ regs) by (unfold spZ at 1; rewrite G11b; apply MState.unsigned_lit; lia).
  assert (P11 : regs_preserved regs regs11).
  { destruct GK as (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    assert (Hs : getr regs11 2 = getr regs 2) by (rewrite G11b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r' Hr. unfold callee_saved in Hr.
    assert (C : r' = 2 \/ r' = 3 \/ r' = 4 \/ r' = 8 \/ r' = 9 \/ r' = 18 \/ r' = 19 \/ r' = 20 \/ r' = 21 \/
                r' = 22 \/ r' = 23 \/ r' = 24 \/ r' = 25 \/ r' = 26 \/ r' = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg11; first [reflexivity | exact K3 | exact K4 | exact K21 | exact K22 | exact K23
        | exact K24 | exact K25 | exact K26 | exact K27]]. }
  destruct (crt_bu L5 A5 Q _ ltac:(rewrite Hb5; apply crt_in_mid)) as (q & Hq & Eq).
  assert (Hpre11 : call_pre B (aa_MR API) L5 A5 regs11 m10 md5).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L5 A5 regs11 m10 md5)).
    apply (cg_pre B API CNO_STACK L A regs mem md PRE L5 A5 m10 md5 regs11 0 ALLOC_STACK I);
      [lia | lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | rewrite S11; exact H16
      | exact G11c | rewrite G11a; exact Hra | exact Hinit]. }
  replace (Z_to_bv 64 CN.CNO_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply (SRcf_bind B).
  { apply (FREE fx7 L5 A5 regs11 m10 md5 q (n + 1) (sb_malloc b (n + 1)) Hpre11 I4 Hq).
    - rewrite G11d, Eq. reflexivity.
    - exact Hres. }
  intros c' (L6 & A6 & regs12 & m12 & md6 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro6 & Hgk6 & Hub6 &
    Hinit6 & Hlen6 & Hres6).
  apply call_post_k_alloc in Hpost.
  rewrite Eq in Hd1.
  assert (PW5 : pairwise ranges_disjoint (f1 ++ (Q, n + 1) :: f2))
    by (rewrite <- Hb5; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M5)).
  assert (ND5 : ~ In (Q, n + 1) (f1 ++ f2)) by (apply (crt_notin f1 f2 _ PW5); cbn; lia).
  assert (Hb6 : blocks L6 A6 = blocks L A).
  { rewrite Hd2, Hb0. symmetry. apply (crt_rm (Q, n + 1) f1 f2 d1 d2 ND5). rewrite <- Hb5. exact Hd1. }
  assert (HD5 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L5 q, n + 1) y).
  { intros y Hy. rewrite Eq. apply (crt_pw_mid f1 f2 _ y PW5). rewrite <- Hb0. exact Hy. }
  assert (HU6 : forall q' k, In (q', k) (user_blocks A) -> In (q', k) (user_blocks A6)).
  { intros q' k Hq'. apply Hub6;
      [exact (I3 q' k Hq') | exact (cg_free_keep B API CNO_STACK L A regs mem md L5 A5 m10 md5 q _ I Hq
        ltac:(lia) HD5 q' k Hq')]. }
  assert (I6 : cno_inv L6 A6 m12 md6).
  { apply (cg_inv_call B API CNO_STACK L A regs mem md PRE AX CT L5 A5 m10 md5 regs11 ALLOC_STACK _ L6 A6 regs12 m12
      md6 I Hpost);
      [rewrite S11, HK0; unfold ALLOC_STACK; lia | lia | exact (crt_heap_E B API L5 A5 m10 md5 q _ AX M5 Hq)
      | exact Hlen6 | exact HU6 | exact Hro6 | exact Hgk6]. }
  apply (SRcf_ret B). exists fx7, L6, A6, regs12, m12, md6.
  split; [rewrite G11a; reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I6 as (I6a & _). apply (kb_post B API); [exact I6a|].
    exact (kb_preserved_trans _ _ _ P11 (proj2 (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost))). }
  split; [exact Hb6|].
  split; [exact (cg_inv_kept B API CNO_STACK L A regs mem md _ _ _ _ I6)|].
  destruct I6 as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres6; exact Hres6 | exact (Hinit6 Hinit)].
Qed.

(* free(a) at 0x12e18, entered at free with ra = 0x12e1c *)
Lemma cno_ph4_cf : forall (fx7 : FPState) L3 A3 regs7 m7 md3 P Q c1 c2 e1 e2,
  frm_zero (@fp_csr fx7) ->
  cno_inv L3 A3 m7 md3 -> st_init_done A3 = true ->
  blocks L3 A3 = e1 ++ (Q, n + 1) :: e2 -> e1 ++ e2 = c1 ++ (P, n + 1) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A3 (sb_malloc (sb_malloc b (n + 1)) (n + 1)) ->
  getr regs7 1 = Z_to_bv 64 0x12e1c -> getr regs7 2 = Z_to_bv 64 (spZ regs - 48) ->
  getr regs7 10 = Z_to_bv 64 P -> getr regs7 18 = Z_to_bv 64 Q ->
  cno_keep regs7 -> cno_frame m7 ->
  SRcf B (mkCfg (@mkst fx7 regs7 (Z_to_bv 64 CN.CNO_FREE) m7 (seg_rom (ms_segs B))) md3) cno_final.
Proof.
  intros fx7 L3 A3 regs7 m7 md3 P Q c1 c2 e1 e2 Hfrm I Hinit Hb3 He Hb0 Hres G1 G2 G10 G18 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CNO_STACK = 8240) by reflexivity.
  pose proof I as ((M3 & W3 & B3 & _) & I2 & I3 & I4 & I5).
  assert (S7 : spZ regs7 = spZ regs - 48) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  assert (PW3 : pairwise ranges_disjoint (e1 ++ (Q, n + 1) :: e2))
    by (rewrite <- Hb3; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M3)).
  assert (PWe : pairwise ranges_disjoint (c1 ++ (P, n + 1) :: c2)) by (rewrite <- He; exact (crt_pw_del e1 e2 _ PW3)).
  assert (InP : In (P, n + 1) (blocks L3 A3)) by (rewrite Hb3; apply crt_in_ins; rewrite He; apply crt_in_mid).
  destruct (crt_bu L3 A3 P _ InP) as (p & Hp & Ep).
  assert (Hpre7 : call_pre B (aa_MR API) L3 A3 regs7 m7 md3).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L3 A3 regs7 m7 md3)).
    apply (cg_pre B API CNO_STACK L A regs mem md PRE L3 A3 m7 md3 regs7 48 ALLOC_STACK I);
      [lia | lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S7; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj1 (proj2 GK)) | rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  replace (Z_to_bv 64 CN.CNO_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply (SRcf_bind B).
  { apply (FREE fx7 L3 A3 regs7 m7 md3 p (n + 1) (sb_malloc (sb_malloc b (n + 1)) (n + 1)) Hpre7 I4 Hp).
    - rewrite G10, Ep. reflexivity.
    - exact Hres. }
  intros c' (L4 & A4 & regs8 & m8 & md4 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro4 & Hgk4 & Hub4 &
    Hinit4 & Hlen4 & Hres4).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp8 & _).
  rewrite Ep in Hd1.
  destruct (CN.cno_rm2 (P, n + 1) (Q, n + 1) c1 c2 e1 e2 d1 d2 PW3 ltac:(cbn; lia) He
    ltac:(rewrite <- Hb3; exact Hd1)) as (f1 & f2 & Ef & Ef0).
  assert (Hb4 : blocks L4 A4 = f1 ++ (Q, n + 1) :: f2) by (rewrite Hd2; exact Ef).
  assert (HD3 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L3 p, n + 1) y).
  { intros y Hy. rewrite Ep. apply (crt_pw_mid c1 c2 _ y PWe). rewrite <- Hb0. exact Hy. }
  assert (HU4 : forall q' k, In (q', k) (user_blocks A) -> In (q', k) (user_blocks A4)).
  { intros q' k Hq'. apply Hub4;
      [exact (I3 q' k Hq') | exact (cg_free_keep B API CNO_STACK L A regs mem md L3 A3 m7 md3 p _ I Hp
        ltac:(lia) HD3 q' k Hq')]. }
  assert (I4' : cno_inv L4 A4 m8 md4).
  { apply (cg_inv_call B API CNO_STACK L A regs mem md PRE AX CT L3 A3 m7 md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8
      md4 I Hpost);
      [rewrite S7, HK0; unfold ALLOC_STACK; lia | lia | exact (crt_heap_E B API L3 A3 m7 md3 p _ AX M3 Hp)
      | exact Hlen4 | exact HU4 | exact Hro4 | exact Hgk4]. }
  assert (FR4 : cno_frame m8).
  { apply (cno_frame_call L3 A3 m7 md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8 md4 I FR Hpost); [lia |].
    intros a Ha. exact (proj1 (crt_heap_E B API L3 A3 m7 md3 p _ AX M3 Hp a Ha)). }
  rewrite G1.
  apply (cno_ph5_cf fx7 L4 A4 regs8 m8 md4 Q f1 f2 Hfrm I4' (Hinit4 Hinit) Hb4).
  - rewrite Ef0. exact Hb0.
  - rewrite sb_free_malloc in Hres4. exact Hres4.
  - transitivity (getr regs7 2); [apply (Hp8 2); unfold callee_saved; lia | exact G2].
  - transitivity (getr regs7 18); [apply (Hp8 18); unfold callee_saved; lia | exact G18].
  - exact (cno_keep_pres regs7 regs8 GK Hp8).
  - exact FR4.
Qed.

(* 0x12d94-0x12e18 as one crt_runN_cf segment over the normalized memory (cno_seg3) *)
Lemma cno_ph3_cf : forall L2 A2 regs4 m4 md2 P Q c1 c2 e1 e2,
  cno_inv L2 A2 m4 md2 -> st_init_done A2 = true ->
  blocks L2 A2 = e1 ++ (Q, n + 1) :: e2 -> e1 ++ e2 = c1 ++ (P, n + 1) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A2 (sb_malloc (sb_malloc b (n + 1)) (n + 1)) ->
  getr regs4 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs4 8 = Z_to_bv 64 cur -> getr regs4 9 = Z_to_bv 64 P ->
  getr regs4 10 = Z_to_bv 64 Q -> getr regs4 19 = Z_to_bv 64 n -> getr regs4 20 = Z_to_bv 64 r ->
  cno_keep regs4 -> cno_frame m4 ->
  SRcf B (mkCfg (mkst regs4 (Z_to_bv 64 0x12d94) m4 (seg_rom (ms_segs B))) md2) cno_final.
Proof.
  intros L2 A2 regs4 m4 md2 P Q c1 c2 e1 e2 I Hinit Hb2 He Hb0 Hres G2 G8 G9 G10 G19 G20 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CNO_STACK = 8240) by reflexivity.
  pose proof HN as HN'. unfold REPLY_MAX in HN'.
  pose proof I as ((M2 & W2 & B2 & _ & _ & _ & _ & _ & S2) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L2 A2 m4 md2 M2) as [Hh Hlz].
  pose proof (crt_img_low B SEGS) as HIL.
  assert (USP : bv_unsigned (getr regs4 2) = spZ regs - 48) by (rewrite G2; apply MState.unsigned_lit; lia).
  assert (Hro' : ro_agree rsegs m4) by (rewrite <- SEGS; exact I4).
  assert (PW2 : pairwise ranges_disjoint (e1 ++ (Q, n + 1) :: e2))
    by (rewrite <- Hb2; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M2)).
  assert (PWe : pairwise ranges_disjoint (c1 ++ (P, n + 1) :: c2)) by (rewrite <- He; exact (crt_pw_del e1 e2 _ PW2)).
  assert (InQ : In (Q, n + 1) (blocks L2 A2)) by (rewrite Hb2; apply crt_in_mid).
  assert (InPe : In (P, n + 1) (e1 ++ e2)) by (rewrite He; apply crt_in_mid).
  assert (InP : In (P, n + 1) (blocks L2 A2)) by (rewrite Hb2; apply crt_in_ins; exact InPe).
  assert (Hold : forall y, In y (blocks L A) -> In y (c1 ++ c2) /\ In y (e1 ++ e2)).
  { intros y Hy. rewrite Hb0 in Hy. split; [exact Hy|]. rewrite He. apply crt_in_ins. exact Hy. }
  destruct (crt_blk B API AX L2 A2 m4 md2 Q _ M2 InQ) as (HQ1 & HQ2 & _ & HQi).
  destruct (crt_blk B API AX L2 A2 m4 md2 P _ M2 InP) as (HP1 & HP2 & _ & HPi).
  pose proof (crt_pw _ _ _ _ _ _ PW2 InPe) as DQP.
  (* the reply: inside an old block, so apart from both new ones and kept since entry *)
  assert (HR : 0 < n -> 0 <= r /\ (r + n <= P \/ P + n + 1 <= r) /\ (r + n <= Q \/ Q + n + 1 <= r) /\
                bytes_at rsegs (normalize rsegs m4) r bs).
  { intros Hn. destruct (IB Hn) as (qa & ka & Hqa & Ha1 & Ha2).
    destruct (crt_blk B API AX L A mem md qa ka HM Hqa) as (HA1 & HA2 & _).
    destruct (Hold _ Hqa) as (Ac & Ae).
    pose proof (crt_pw _ _ _ _ _ _ PWe Ac) as DPA.
    pose proof (crt_pw _ _ _ _ _ _ PW2 Ae) as DQA.
    split; [lia|]. split; [lia|]. split; [lia|].
    apply (bytes_at_normalize rsegs); [exact Hro'|].
    apply cno_blk_bytes; [lia | lia |].
    pose proof (cg_inv_kept B API CNO_STACK L A regs mem md _ _ _ _ I) as KP.
    intros i Hi. rewrite <- (BD i Hi).
    pose proof (KP qa ka (r - qa + i) Hqa (fun H => H) ltac:(lia)) as E.
    replace (qa + (r - qa + i)) with (r + i) in E by ring. exact E. }
  assert (ST : stk rsegs (normalize rsegs m4) (spZ regs - 48 - 32) (spZ regs - 48)).
  { rewrite <- SEGS. apply (crt_stk_norm B HIL); [| exact I4 | lia].
    apply (crt_stk B HIL); [lia | lia |]. intros a Ha. apply S2. left. lia. }
  assert (SPn : stk rsegs (normalize rsegs m4) P (P + n + 1)).
  { replace (P + n + 1) with (P + (n + 1)) by ring. apply cno_blk_stk; [exact I4 | lia | lia |].
    intros i Hi. destruct (HPi i Hi) as (X1 & X2 & _). split; assumption. }
  assert (SQn : stk rsegs (normalize rsegs m4) Q (Q + n + 1)).
  { replace (Q + n + 1) with (Q + (n + 1)) by ring. apply cno_blk_stk; [exact I4 | lia | lia |].
    intros i Hi. destruct (HQi i Hi) as (X1 & X2 & _). split; assumption. }
  eapply (crt_runN_cf B SEGS regs4 _ m4 md2); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G8, G9, G10, G19, G20.
    apply (CN.cno_seg3 MC RUI) with (r := r) (n := n) (cur := cur) (P := P) (Q := Q) (bs := bs);
      rewrite ?USP; first [exact HL | exact HC | exact HR | exact (mem_inv_normalize rsegs m4) | exact SPn | exact SQn
        | exact ST | lia]. }
  { intros ms (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z4 & x3 & x4 & x5 & x6 & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z4 & x3 & x4 & x5 & x6 & m' & -> & MU & WM &
    MI') Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR'). cbn [ms_mem MState.MS] in HR'.
  rewrite USP in MU. unfold CN.cno_W in MU.
  set (W := [(spZ regs - 48 - 32, spZ regs - 48); (P, P + n + 1); (Q, Q + n + 1)]) in MU.
  pose proof (mem_rel_normalize rsegs m4 Hro') as HR6.
  pose proof (munch_rel rsegs _ m4 _ (ms_mem ms) m' HR6 HR' Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m4 _ (ms_mem ms) m' HR6 HR' Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m4 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (PRES : forall x, m4 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (crt_pres B m4 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    destruct (CN.cno_not_out3 _ _ _ _ _ _ _ Hout) as [Hs|[Hs|Hs]].
    - apply (crt_fs_high B HIL). lia.
    - apply (crt_fs_none B SEGS). destruct (HPi (bv_unsigned x - P) ltac:(lia)) as (_ & Hn & _).
      replace (P + (bv_unsigned x - P)) with (bv_unsigned x) in Hn by ring. exact Hn.
    - apply (crt_fs_none B SEGS). destruct (HQi (bv_unsigned x - Q) ltac:(lia)) as (_ & Hn & _).
      replace (Q + (bv_unsigned x - Q)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CNO_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L2 A2 x /\
      forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. destruct (CN.cno_not_out3 _ _ _ _ _ _ _ Hout) as [Hs|[Hs|Hs]].
    - left. lia.
    - right. destruct (HPi (x - P) ltac:(lia)) as (_ & Hn1 & Hn2).
      replace (P + (x - P)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p k i Hp Hi E. destruct (Hold _ (crt_ub L A p k Hp)) as (Y1 & _).
      pose proof (crt_pw _ _ _ _ _ _ PWe Y1). lia.
    - right. destruct (HQi (x - Q) ltac:(lia)) as (_ & Hn1 & Hn2).
      replace (Q + (x - Q)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p k i Hp Hi E. destruct (Hold _ (crt_ub L A p k Hp)) as (_ & Y2).
      pose proof (crt_pw _ _ _ _ _ _ PW2 Y2). lia. }
  pose proof (cg_inv_A B API CNO_STACK L A regs mem md PRE SEGS L2 A2 m4 md2 (ms_mem ms) W I MU7 WM7 PRES HWW RO7)
    as I7.
  assert (FR7 : cno_frame (ms_mem ms)).
  { unfold cno_frame in *. rewrite <- SEGS in FR |- *.
    apply (crt_cells_keep B m4 (ms_mem ms) _ _ FR). intros i Hi.
    change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
    apply MU7. rewrite MState.unsigned_lit by lia. unfold W. cbn [Frame.outside]. repeat split; lia. }
  destruct GK as (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  cbn [MState.MS ms_pc_val ms_fregs ms_fcsr].
  apply (cno_ph4_cf (mkFP fp_regs fp_csr) L2 A2 regs7 (ms_mem ms) md2 P Q c1 c2 e1 e2 FRM I7 Hinit Hb2 He Hb0 Hres);
    [rewrite Hg7; reflexivity | rewrite Hg7; exact G2 | rewrite Hg7; reflexivity | rewrite Hg7; reflexivity
    | | exact FR7].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); rewrite Hg7;
    first [exact K3 | exact K4 | exact K21 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26 | exact K27].
Qed.

(* 0x12d88-0x12d90 (cno_seg2) and the second malloc(n + 1) *)
Lemma cno_ph2m_cf : forall L1 A1 regs2 m2 md1 P c1 c2,
  cno_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = c1 ++ (P, n + 1) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A1 (sb_malloc b (n + 1)) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs2 8 = Z_to_bv 64 cur -> getr regs2 10 = Z_to_bv 64 P ->
  getr regs2 18 = Z_to_bv 64 (n + 1) -> getr regs2 19 = Z_to_bv 64 n -> getr regs2 20 = Z_to_bv 64 r ->
  cno_keep regs2 -> cno_frame m2 ->
  SRcf B (mkCfg (mkst regs2 (Z_to_bv 64 0x12d88) m2 (seg_rom (ms_segs B))) md1) cno_final.
Proof.
  intros L1 A1 regs2 m2 md1 P c1 c2 I Hinit Hb1 Hb0 Hres G2 G8 G10 G18 G19 G20 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CNO_STACK = 8240) by reflexivity.
  pose proof HN as HN'. unfold REPLY_MAX in HN'.
  pose proof I as ((M1 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  eapply (crt_runA_cf B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | | |].
  { unfold rmk. apply CN.cno_seg2. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs3 -> Hg3. cbn [MState.MS ms_pc_val ms_mem].
  assert (G3a : getr regs3 1 = Z_to_bv 64 0x12d94) by (rewrite Hg3; reflexivity).
  assert (G3b : getr regs3 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg3; exact G2).
  assert (G3c : getr regs3 10 = Z_to_bv 64 (n + 1)) by (rewrite Hg3; exact G18).
  assert (G3d : getr regs3 8 = Z_to_bv 64 cur) by (rewrite Hg3; exact G8).
  assert (G3e : getr regs3 9 = Z_to_bv 64 P) by (rewrite Hg3; exact G10).
  assert (G3f : getr regs3 19 = Z_to_bv 64 n) by (rewrite Hg3; exact G19).
  assert (G3g : getr regs3 20 = Z_to_bv 64 r) by (rewrite Hg3; exact G20).
  assert (K3 : cno_keep regs3).
  { destruct GK as (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); rewrite Hg3;
      first [exact K3 | exact K4 | exact K21 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26
        | exact K27]. }
  assert (S3 : spZ regs3 = spZ regs - 48) by (unfold spZ at 1; rewrite G3b; apply MState.unsigned_lit; lia).
  assert (Hpre3 : call_pre B (aa_MR API) L1 A1 regs3 m2 md1).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 regs3 m2 md1)).
    apply (cg_pre B API CNO_STACK L A regs mem md PRE L1 A1 m2 md1 regs3 48 ALLOC_STACK I);
      [lia | lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S3; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj1 (proj2 K3)) | rewrite G3a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  assert (Hroom : room_ag (sb_malloc b (n + 1)) (n + 1)).
  { destruct ROOM as ((R1 & R1') & R2 & R3). apply room_ag_gen; cbn [sb_malloc sb_live sb_cap sb_bytes]; lia. }
  replace (Z_to_bv 64 CN.CNO_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply (SRcf_bind B).
  { exact (MALLOC L1 A1 regs3 m2 md1 (n + 1) (sb_malloc b (n + 1)) Hpre3 I4 G3c Hres Hroom). }
  intros c' (L2 & A2 & regs4 & m4 & md2 & res & -> & Hpost & G4 & _ & _ & _ & (d1 & d2 & Hb2 & Hb1') & _ & Hro2 &
    Hgk2 & HU2 & Hinit2 & Hlen2 & Hres2).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp4 & _).
  assert (I2' : cno_inv L2 A2 m4 md2).
  { apply (cg_inv_call B API CNO_STACK L A regs mem md PRE AX CT L1 A1 m2 md1 regs3 ALLOC_STACK _ L2 A2 regs4 m4
      md2 I Hpost);
      [rewrite S3, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen2
      | intros q k Hq; exact (HU2 q k (I3 q k Hq)) | exact Hro2 | exact Hgk2]. }
  assert (FR2 : cno_frame m4).
  { apply (cno_frame_call L1 A1 m2 md1 regs3 ALLOC_STACK _ L2 A2 regs4 m4 md2 I FR Hpost); [lia | intros a []]. }
  rewrite G3a.
  apply (cno_ph3_cf L2 A2 regs4 m4 md2 P res c1 c2 d1 d2 I2' Hinit2 Hb2).
  - rewrite <- Hb1'. exact Hb1.
  - exact Hb0.
  - exact Hres2.
  - transitivity (getr regs3 2); [apply (Hp4 2); unfold callee_saved; lia | exact G3b].
  - transitivity (getr regs3 8); [apply (Hp4 8); unfold callee_saved; lia | exact G3d].
  - transitivity (getr regs3 9); [apply (Hp4 9); unfold callee_saved; lia | exact G3e].
  - exact G4.
  - transitivity (getr regs3 19); [apply (Hp4 19); unfold callee_saved; lia | exact G3f].
  - transitivity (getr regs3 20); [apply (Hp4 20); unfold callee_saved; lia | exact G3g].
  - exact (cno_keep_pres regs3 regs4 K3 Hp4).
  - exact FR2.
Qed.

(* 0x12d54-0x12d84 (cno_seg1) and the first malloc(n + 1) *)
Lemma cno_entry_cf :
  SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (seg_rom (ms_segs B))) md) cno_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CNO_STACK = 8240) by reflexivity.
  pose proof HN as HN'. unfold REPLY_MAX in HN'.
  pose proof (crt_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  assert (I0 : cno_inv L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p k Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : stk rsegs mem (spZ regs - CNO_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CNO_STACK L A regs mem md PRE ltac:(lia))).
  eapply (crt_runA_cf B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
  { unfold rmk. rewrite R10, R11, R12. eapply CN.cno_seg1; [exact ST | unfold spZ in *; lia | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & _).
    repeat split; reflexivity. }
  intros ms regs1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
    MU & WM & FR1) Hg1.
  cbn [MState.MS ms_pc_val ms_mem].
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x12d88) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg1; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 (n + 1)) by (rewrite Hg1; reflexivity).
  assert (G1d : getr regs1 8 = Z_to_bv 64 cur) by (rewrite Hg1; reflexivity).
  assert (G1e : getr regs1 18 = Z_to_bv 64 (n + 1)) by (rewrite Hg1; reflexivity).
  assert (G1f : getr regs1 19 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
  assert (G1g : getr regs1 20 = Z_to_bv 64 r) by (rewrite Hg1; reflexivity).
  assert (K1 : cno_keep regs1)
    by (refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); rewrite Hg1; reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 48, spZ regs)] x -> spZ regs - 48 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
  assert (Hro1 : ro_agree (ms_segs B) m1).
  { apply (crt_ro_munch B _ mem m1 RO MU). intros a Ha Ho. apply (crt_fs_high B HIL). pose proof (Hout a Ho). lia. }
  assert (I1 : cno_inv L A m1 md).
  { apply (cg_inv_A B API CNO_STACK L A regs mem md PRE SEGS L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 48, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (crt_pres B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (crt_fs_high B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
    apply (kb_pre_A B API CNO_STACK 48 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 48, spZ regs)] PRE);
      [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
      | rewrite S1; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact MU | exact WM' | |].
    - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (Hroom : room_ag b (n + 1)) by (destruct ROOM as ((R1 & R1') & R2 & R3); apply room_ag_gen; lia).
  replace (Z_to_bv 64 CN.CNO_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply (SRcf_bind B).
  { exact (MALLOC L A regs1 m1 md (n + 1) b Hpre1 Hro1 G1c RES Hroom). }
  intros c' (L1 & A1 & regs2 & m2 & md1 & res & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
    Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
  assert (I1' : cno_inv L1 A1 m2 md1).
  { apply (cg_inv_call B API CNO_STACK L A regs mem md PRE AX CT L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1
      Hpost);
      [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
      | exact Hgk2]. }
  assert (FR2 : cno_frame m2).
  { apply (cno_frame_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1 Hpost); [lia | intros a []]. }
  rewrite G1a.
  apply (cno_ph2m_cf L1 A1 regs2 m2 md1 res d1 d2 I1' Hinit1 Hb1 Hb0 Hres1).
  - transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
  - transitivity (getr regs1 8); [apply (Hp2 8); unfold callee_saved; lia | exact G1d].
  - exact G2.
  - transitivity (getr regs1 18); [apply (Hp2 18); unfold callee_saved; lia | exact G1e].
  - transitivity (getr regs1 19); [apply (Hp2 19); unfold callee_saved; lia | exact G1f].
  - transitivity (getr regs1 20); [apply (Hp2 20); unfold callee_saved; lia | exact G1g].
  - exact (cno_keep_pres regs1 regs2 K1 Hp2).
  - exact FR2.
Qed.

End Body.

Theorem check_no_overread_holds_cf : check_no_overread_contract_cf B API.
Proof.
  intros L A regs mem md r n cur bs b _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
  eapply cno_entry_cf; eassumption.
Qed.
End CNO.
