(* Case 4 of the op loop of LLVMFuzzerTestOneInput in the plain image, tagged arm, segment 2: 0x1400c -> 0x1408c
   (fuzz_transport.c:1094-1101: `if (h_coalescable(c.key))` the scan of g_q for a queued command with the same key).
   From op4_t1 to op4_t2: s2 = at_ as a 32-bit value; memory unchanged. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4k.
Import ListNotations.
Open Scope Z_scope.

(* lwu of a value below 2^32 (Lib/Exec.v zx32_small, which this file does not see) *)
Lemma o4t2_zx32 : forall z, 0 <= z < 2 ^ 32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zx32. rewrite unsigned_lit by lia. f_equal. apply Z.mod_small. lia.
Qed.

(* the struct's last four bytes are its key (cmd_struct, TOps.v:191-192) *)
Lemma o4t2_skip : forall cb len display key, length cb = 24%nat ->
  skipn 28 (cmd_struct cb len display key) = put 4 key.
Proof.
  intros cb len display key L. unfold cmd_struct.
  rewrite skipn_app, L. rewrite skipn_all2 by lia. cbn [Nat.sub skipn app]. reflexivity.
Qed.

(* the frame of case 4 with the struct's key (sp + 0x6c) as its own C4 cell, for 0x1400c `lwu a0, 0x6c(sp)` *)
Lemma o4t2_view : forall m Sp x10 bf j30 cb len display key j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  rw_cells rsegs m Sp
    (op4_fr x10 bf j30 (cmd_struct cb len display key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  0 <= key < 2 ^ 32 ->
  rw_cells rsegs m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); x10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30;
     CB 28 (firstn 28 (cmd_struct cb len display key)); C4 (Z_to_bv 64 key); CB 8 j70;
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Proof.
  intros m Sp x10 bf j30 cb len display key j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H Hk.
  pose proof (proj1 (proj1 H)) as W. unfold op4_fr in W. cbn [cells_wf cell_wf] in W.
  destruct W as (_ & _ & _ & _ & _ & _ & _ & Lcs & _).
  assert (Lcb : length cb = 24%nat).
  { unfold cmd_struct in Lcs. rewrite !length_app, length_put in Lcs. cbn [length] in Lcs. lia. }
  unfold op4_fr in H.
  refine (op4_rw_mid m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); x10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30]
    [CB 32 (cmd_struct cb len display key)]
    [CB 28 (firstn 28 (cmd_struct cb len display key)); C4 (Z_to_bv 64 key)]
    [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    H _ _).
  - cbn [cells_wf cell_wf]. rewrite length_firstn, Lcs. split; [reflexivity | split; exact I].
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r.
    assert (E4 : le4 (Z_to_bv 64 key) = put 4 key).
    { unfold le4, put. rewrite unsigned_lit by lia. reflexivity. }
    rewrite E4, <- (o4t2_skip cb len display key Lcb). apply firstn_skipn.
Qed.

(* ---- the inlined coalescable test (0x14010-0x14030 against TCb.v h_coalescable_m). Copied from the ubsan twin
   (lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_m.v t4_mask16 / t4_land_mod /
   t4_f7 / t4_coal0); t4_f7's bound on Z.land k 15 is restated by Z.land_ones (Bytes.v's land_lt_pow2 is not in
   scope here). ---- *)
Lemma o4t2_mask16 : forall x m, 0 <= x -> 0 <= m ->
  Z.land x (Z.shiftl m 16) = Z.shiftl (Z.land (Z.shiftr x 16) m) 16.
Proof.
  intros x m Hx Hm. rewrite Z.shiftl_land.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 16) as [H|H].
  - rewrite (Z.shiftl_spec_low m 16 i) by lia. rewrite !andb_false_r. reflexivity.
  - rewrite (Z.shiftl_spec (Z.shiftr x 16) 16 i) by lia. rewrite Z.shiftr_spec by lia.
    replace (i - 16 + 16) with i by lia. reflexivity.
Qed.

Lemma o4t2_land_mod : forall y m, 0 <= y -> 0 <= m < 256 -> Z.land (y mod 256) m = Z.land y m.
Proof.
  intros y m Hy Hm.
  replace (y mod 256) with (Z.land y 255)
    by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; reflexivity).
  rewrite <- Z.land_assoc. f_equal.
  rewrite Z.land_comm. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

Lemma o4t2_f7 : forall k, 0 <= k < 256 -> (Z.land k 247 = 0 <-> (k = 0 \/ k = 8)).
Proof.
  intros k Hk. split.
  - intros H.
    assert (E7 : Z.land k 7 = 0).
    { change 7 with (Z.land 247 7) at 1. rewrite Z.land_assoc, H. reflexivity. }
    assert (E240 : Z.land k 240 = 0).
    { change 240 with (Z.land 247 240) at 1. rewrite Z.land_assoc, H. reflexivity. }
    assert (EK : k = Z.land k 15).
    { replace k with (Z.land k 255) at 1
        by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
      change 255 with (Z.lor 240 15). rewrite Z.land_lor_distr_r, E240, Z.lor_0_l. reflexivity. }
    assert (R : 0 <= Z.land k 15 < 16).
    { change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound k (2 ^ 4) ltac:(lia)) as R4. change (2 ^ 4) with 16 in R4. exact R4. }
    assert (M8 : k mod 8 = 0).
    { rewrite <- E7. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. }
    rewrite <- EK in R. lia.
  - intros [E|E]; rewrite E; reflexivity.
Qed.

(* h_coalescable(key) = 0 exactly when 0x14020 (key & 0xf70000 = 0) or 0x14030 (key & 0xff0000 = 0x90000) branches *)
Lemma o4t2_coal0 : forall key, 0 <= key < 2 ^ 32 ->
  (h_coalescable_m key = 0 <-> (Z.land key 16187392 = 0 \/ Z.land key 16711680 = 589824)).
Proof.
  intros key Hk.
  assert (HS : 0 <= Z.shiftr key 16) by (apply Z.shiftr_nonneg; lia).
  set (k := Z.shiftr key 16 mod 256).
  assert (HKR : 0 <= k < 256) by (unfold k; apply Z.mod_pos_bound; lia).
  assert (E1 : Z.land key 16187392 = Z.shiftl (Z.land k 247) 16).
  { change 16187392 with (Z.shiftl 247 16). rewrite (o4t2_mask16 key 247) by lia.
    unfold k. rewrite (o4t2_land_mod (Z.shiftr key 16) 247) by lia. reflexivity. }
  assert (E2 : Z.land key 16711680 = Z.shiftl k 16).
  { change 16711680 with (Z.shiftl 255 16). rewrite (o4t2_mask16 key 255) by lia.
    unfold k. f_equal. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. }
  rewrite E1, E2. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536.
  unfold h_coalescable_m, b2z, SPEC_KEY_INPUT, SPEC_KEY_KEEPALIVE.
  change (Z.shiftr key 16 mod 2 ^ 8) with k.
  split.
  - intros H.
    destruct (Z.eqb_spec k 0) as [E|E]; cbn [negb andb] in H.
    { left. rewrite E. reflexivity. }
    destruct (Z.eqb_spec k 8) as [E8|E8]; cbn [negb andb] in H.
    { left. rewrite E8. reflexivity. }
    destruct (Z.eqb_spec k 9) as [E9|E9]; cbn [negb andb] in H; [|discriminate H].
    right. lia.
  - intros [H|H].
    + assert (HL : Z.land k 247 = 0) by lia.
      apply (proj1 (o4t2_f7 k HKR)) in HL. destruct HL as [E|E]; rewrite E; reflexivity.
    + assert (E9 : k = 9) by lia. rewrite E9. reflexivity.
Qed.

(* the exit to 0x1408c: op4_t2 from the registers of op4_t1, s2 = at_ mod 2^32 *)
Ltac o4t2_fin HK HTOK HTM :=
  apply HK; unfold op4_t2; do 17 eexists; split; [reflexivity|]; split; [exact HTOK | exact HTM].

Lemma op4_tag2 : forall data D, op4_tag2_stmt data D.
Proof.
  intros data D Sp lo ops c3 B1 before display key at_ m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q
    FIND HT1 HAT HK.
  destruct HT1 as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & HTOK & HTM).
  pose proof HTOK as HTOK0. destruct HTOK0 as ((HOPS & HCUR & HBEF & HDISP & HKEY) & HNC).
  pose proof HTM as HTM0. destruct HTM0 as (j30 & j70 & HM).
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *. rewrite unsigned_lit in HOWIN by lia.
  unfold o4_cs in HRW.
  pose proof (o4t2_view _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRW HKEY) as HRWk.
  clear HRW.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_nq. wk_eq_fact OFF_g_q.
  (* 0x1400c lwu a0, 0x6c(sp): the key *)
  zstep. rewrite o4t2_zx32 by lia.
  (* 0x14010-0x1401c: a1 = key & 0xf70000, a2 = -1, s2 = 0xffffffff; 0x14020 beqz a1 *)
  do 5 zstep.
  if_cases K1; zify_cond K1.
  { (* key & 0xf70000 = 0: h_coalescable(key) = 0, at_ = -1, s2 = 0xffffffff *)
    assert (HC0 : h_coalescable_m key = 0) by (apply (proj2 (o4t2_coal0 key HKEY)); left; exact K1).
    unfold o4_atopt in HAT. rewrite HC0 in HAT. cbn [negb Z.eqb] in HAT. injection HAT as EA. subst at_.
    o4t2_fin HK HTOK HTM. }
  (* 0x14024-0x1402c: a1 = key & 0xff0000, a2 = 0x90000; 0x14030 beq a1, a2 *)
  do 4 zstep.
  if_cases K2; zify_cond K2.
  { (* key & 0xff0000 = 0x90000 (kind SPEC_KEY_KEEPALIVE): h_coalescable(key) = 0, at_ = -1 *)
    assert (HC0 : h_coalescable_m key = 0) by (apply (proj2 (o4t2_coal0 key HKEY)); right; exact K2).
    unfold o4_atopt in HAT. rewrite HC0 in HAT. cbn [negb Z.eqb] in HAT. injection HAT as EA. subst at_.
    o4t2_fin HK HTOK HTM. }
  assert (HC1 : h_coalescable_m key <> 0).
  { intros E. apply (proj1 (o4t2_coal0 key HKEY)) in E. destruct E as [E|E]; [exact (K1 E) | exact (K2 E)]. }
  unfold o4_atopt in HAT. rewrite (proj2 (Z.eqb_neq _ 0) HC1) in HAT. cbn [negb] in HAT.
  (* 0x14034 lwu a1, 0xc(s9): g_nq (s9 = &g_fail_next, 0xfdc8 + 0xc = OFF_g_nq) of the world o4_B2 B1; 0x14038 beqz a1 *)
  do 2 zstep.
  assert (GR : 0 <= g_nq (o4_B2 B1) < 2 ^ 32).
  { unfold g_nq. pose proof (u_at_range (o4_B2 B1) OFF_g_nq 4) as R.
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R. exact R. }
  assert (EG : u_at (o4_B2 B1) 64980 4 = g_nq (o4_B2 B1)) by reflexivity.
  if_cases K3; zify_cond K3; rewrite ?EG in K3.
  { (* g_nq = 0: the scan finds nothing, at_ = -1 *)
    cbn [submit_find_at] in HAT.
    replace (0 <? g_nq (o4_B2 B1)) with false in HAT by (symmetry; apply Z.ltb_ge; lia).
    injection HAT as EA. subst at_.
    o4t2_fin HK HTOK HTM. }
  (* 0x1403c-0x14050: a2 = 0, a3 = 1, a4 = &g_q (auipc 0x14044 + addi 0x14048: 0x41558 = W_BASE_PLAIN + OFF_g_q),
     a5 = 0xffffffff; then the scan's head 0x14054, i = 0 *)
  do 6 zstep.
  eapply (FIND (o4_B2 B1) key (S (Z.to_nat CMDS_MAX)) 0 at_).
  - exact HWM.
  - exact HKEY.
  - lia.
  - exact HAT.
  - intros a2' a3' a4' a5' a6'. o4t2_fin HK HTOK HTM.
Qed.
