From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YO0x YO0u YK14 YI04 YI06.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import fuzz_free_c memset_c pj_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition seg_lo_hi (lo hi : Z) : bool :=
  forallb (fun s => (lo <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? hi)) rsegs.

Lemma pf_seg_bound : seg_lo_hi 0x10000 0x55000 = true.
Proof. vm_compute. reflexivity. Qed.

Definition res_lo_hi (lo hi : Z) : bool :=
  forallb (fun s => (lo <=? bv_unsigned (fst s)) && (bv_unsigned (fst s) + bv_unsigned (snd s) <=? hi))
    (segments_reserved rsegs).

Lemma pf_res_bound : res_lo_hi 0x10000 0x55000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pf_guard_rom : forall k, 0 <= k < 8 -> seg_rom rsegs (Z_to_bv 64 (strtod_c.STRTOD_GUARD + k)) <> None.
Proof.
  intros k Hk. assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) as E by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; discriminate.
Qed.

Definition rkeep (R R0 : bvmap 5 word) : Prop :=
  forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr R (Z_to_bv 5 r) = getr R0 (Z_to_bv 5 r).

Local Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Lemma rkeep_trans : forall R1 R2 R3, rkeep R1 R2 -> rkeep R2 R3 -> rkeep R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. rewrite (H1 r Hr). exact (H2 r Hr). Qed.

Lemma beq0_lit : forall z, 0 <= z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = (z =? 0).
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma bltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Ltac rk_tac :=
  unfold rkeep; let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in intros r Hr;
  assert (Hr' : r = 3 \/ r = 4 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.

Ltac rg_tac := first [ reflexivity |
  unfold getr;
  lazymatch goal with |- (if bv_eqb ?r ?z then _ else _) = _ =>
    let b := eval vm_compute in (bv_eqb r z) in change (bv_eqb r z) with b end;
  cbv iota; simp_regs; f_equal; rewrite ?unsigned_lit by lia; lia ].

Lemma ka_null : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  evt rsegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
      s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 PJ_FREE) fc None m (seg_rom rsegs)).
Proof.
  intros. unfold PJ_FREE. step. if_true. step. apply evt_done. reflexivity.
Qed.

Lemma ka_entry : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m v n kids junk,
  0 < v -> v + 56 <= bv_unsigned sp + -48 \/ bv_unsigned sp <= v -> v + 56 <= 2 ^ 64 -> 48 <= bv_unsigned sp ->
  0 <= n < 2 ^ 64 -> 0 <= kids < 2 ^ 64 ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 kids)) ->
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 48 junk] ->
  evt rsegs (fun ms => exists R pc' m', ms = MS R F pc' fc None m' (seg_rom rsegs) /\
      getr R (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned sp + -48) /\
      getr R (Z_to_bv 5 8) = Z_to_bv 64 v /\
      getr R (Z_to_bv 5 10) = Z_to_bv 64 kids /\
      rkeep R (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
        t3 t4 t5 t6) /\
      Frame.munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m' /\ Frame.wmono rsegs m m' /\
      (exists j, rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
      (n = 0 /\ pc' = Z_to_bv 64 FUZZ_FREE /\ getr R (Z_to_bv 5 1) = Z_to_bv 64 0x14614 \/
       n <> 0 /\ pc' = Z_to_bv 64 PJ_FREE /\ getr R (Z_to_bv 5 1) = Z_to_bv 64 0x145e4 /\
       getr R (Z_to_bv 5 9) = Z_to_bv 64 0 /\ getr R (Z_to_bv 5 18) = Z_to_bv 64 0 /\
       getr R (Z_to_bv 5 19) = Z_to_bv 64 0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 PJ_FREE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v n kids junk
    Hv Hvd Hv2 Hsp Hn Hk BN BK FR.
  unfold PJ_FREE.
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (HV0 : bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  step.
  rewrite HV0; cbv iota.
  do 6 step.
  step.
  let mm := cur_mem in
  assert (RN : ov_read_bytes rsegs mm (wa (v + 40)) 8 = Some (le8 (Z_to_bv 64 n)))
    by (rewrite <- (Z.add_0_r (v + 40)) at 1; rewrite (bytes_at_read rsegs mm (v + 40) _ 0 8 BN) by (rewrite ?length_le8; cbn; lia); reflexivity);
  assert (RK : ov_read_bytes rsegs mm (wa (v + 24)) 8 = Some (le8 (Z_to_bv 64 kids)))
    by (rewrite <- (Z.add_0_r (v + 24)) at 1; rewrite (bytes_at_read rsegs mm (v + 24) _ 0 8 BK) by (rewrite ?length_le8; cbn; lia); reflexivity).
  step. step.
  if_cases HN.
  - rewrite beq0_lit in HN by lia. apply Z.eqb_eq in HN.
    step.
    step.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. split; [rk_tac|].
    split; [exact MU|]. split; [exact WM|]. split; [eexists; exact FR|].
    left. split; [exact HN|]. split; [reflexivity|]. rg_tac.
  - rewrite beq0_lit in HN by lia. apply Z.eqb_neq in HN.
    do 6 step.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. split; [rk_tac|].
    split; [exact MU|]. split; [exact WM|]. split; [eexists; exact FR|].
    right. split; [exact HN|]. split; [reflexivity|].
    split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. rg_tac.
Qed.

Definition loop_post (F : bvmap 5 word) (fc : bv 32) (R0 : bvmap 5 word) (m : word -> option byte)
    (sp : word) (v kids n i : Z) : machine_state -> Prop :=
  fun ms => exists R pc', ms = MS R F pc' fc None m (seg_rom rsegs) /\
    getr R (Z_to_bv 5 2) = sp /\ getr R (Z_to_bv 5 8) = Z_to_bv 64 v /\ rkeep R R0 /\
    (i + 1 < n /\ pc' = Z_to_bv 64 PJ_FREE /\ getr R (Z_to_bv 5 1) = Z_to_bv 64 0x145e4 /\
       getr R (Z_to_bv 5 10) = Z_to_bv 64 (kids + 56 * (i + 1)) /\
       getr R (Z_to_bv 5 9) = Z_to_bv 64 (56 * (i + 1)) /\ getr R (Z_to_bv 5 18) = Z_to_bv 64 (8 * (i + 1)) /\
       getr R (Z_to_bv 5 19) = Z_to_bv 64 (i + 1) \/
     n <= i + 1 /\ pc' = Z_to_bv 64 FUZZ_FREE /\ getr R (Z_to_bv 5 1) = Z_to_bv 64 0x14614 /\
       getr R (Z_to_bv 5 10) = Z_to_bv 64 kids).

Lemma ka_tail : forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m v n kids i,
  0 <= i -> i + 1 <= n -> 56 * n < 2 ^ 62 -> 0 <= kids -> kids + 56 * n < 2 ^ 64 -> 0 <= v -> v + 56 <= 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (v + 40)) 8 = Some (le8 (Z_to_bv 64 n)) ->
  ov_read_bytes rsegs m (wa (v + 24)) 8 = Some (le8 (Z_to_bv 64 kids)) ->
  evt rsegs (loop_post F fc (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 (56 * i)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (8 * i)) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m sp v kids n i)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 (56 * i)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (8 * i)) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x145f8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v n kids i
    Hi Hin Hn Hk Hkn Hv Hv2 RN RK.
  do 4 step.
  step.
  if_cases HC; rewrite bltu_lit in HC by lia.
  - apply Z.ltb_lt in HC.
    do 3 step.
    apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [rg_tac|]. split; [rg_tac|]. split; [rk_tac|].
    left. split; [exact HC|]. split; [reflexivity|].
    split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. rg_tac.
  - apply Z.ltb_ge in HC.
    do 2 step.
    apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [rg_tac|]. split; [rg_tac|]. split; [rk_tac|].
    right. split; [lia|]. split; [reflexivity|]. split; rg_tac.
Qed.

Lemma ka_child_ret : forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m v n kids keys x i,
  0 <= i -> i + 1 <= n -> 56 * n < 2 ^ 62 -> 0 <= kids -> kids + 56 * n < 2 ^ 64 -> 0 <= v -> v + 56 <= 2 ^ 64 ->
  0 <= keys -> keys + 8 * n < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (v + 40)) 8 = Some (le8 (Z_to_bv 64 n)) ->
  ov_read_bytes rsegs m (wa (v + 24)) 8 = Some (le8 (Z_to_bv 64 kids)) ->
  ov_read_bytes rsegs m (wa (v + 32)) 8 = Some (le8 (Z_to_bv 64 keys)) ->
  (keys <> 0 -> ov_read_bytes rsegs m (wa (keys + 8 * i)) 8 = Some (le8 (Z_to_bv 64 x))) ->
  evt rsegs (fun ms =>
      (keys <> 0 /\ exists R, ms = MS R F (Z_to_bv 64 FUZZ_FREE) fc None m (seg_rom rsegs) /\
         getr R (Z_to_bv 5 1) = Z_to_bv 64 0x145f8 /\ getr R (Z_to_bv 5 2) = sp /\
         getr R (Z_to_bv 5 8) = Z_to_bv 64 v /\ getr R (Z_to_bv 5 9) = Z_to_bv 64 (56 * i) /\
         getr R (Z_to_bv 5 10) = Z_to_bv 64 x /\
         getr R (Z_to_bv 5 18) = Z_to_bv 64 (8 * i) /\ getr R (Z_to_bv 5 19) = Z_to_bv 64 i /\
         rkeep R (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 (56 * i)) a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 (8 * i)) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) \/
      (keys = 0 /\ loop_post F fc (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 (56 * i)) a0 a1 a2 a3 a4 a5 a6
         a7 (Z_to_bv 64 (8 * i)) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m sp v kids n i ms))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 (56 * i)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (8 * i)) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x145e4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v n kids keys x i
    Hi Hin Hn Hk Hkn Hv Hv2 Hy Hyn RN RK RY RX.
  step. step.
  if_cases HY; rewrite beq0_lit in HY by lia.
  - apply Z.eqb_eq in HY. subst keys.
    eapply evt_mono; [apply (ka_tail ra sp gp tp t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 F fc m v n kids i Hi Hin Hn Hk Hkn Hv Hv2 RN RK)|].
    intros ms (R & pc' & E & H2 & H8 & HK & HB). right. split; [reflexivity|].
    exists R, pc'. split; [exact E|]. split; [exact H2|]. split; [exact H8|]. split; [|exact HB].
    eapply rkeep_trans; [exact HK|]. rk_tac.
  - apply Z.eqb_neq in HY. specialize (RX HY).
    do 3 step.
    apply evt_done. left. split; [exact HY|]. eexists. split; [reflexivity|].
    split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|].
    split; [rg_tac|]. split; [rg_tac|]. rk_tac.
Qed.

Lemma ka_kids_ret : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m v keys,
  0 <= v -> v + 56 <= 2 ^ 64 -> 0 <= keys < 2 ^ 64 -> s0 = Z_to_bv 64 v ->
  ov_read_bytes rsegs m (wa (v + 32)) 8 = Some (le8 (Z_to_bv 64 keys)) ->
  evt rsegs (fun ms => exists R, ms = MS R F (Z_to_bv 64 FUZZ_FREE) fc None m (seg_rom rsegs) /\
      getr R (Z_to_bv 5 1) = Z_to_bv 64 0x1461c /\ getr R (Z_to_bv 5 2) = sp /\
      getr R (Z_to_bv 5 8) = Z_to_bv 64 v /\ getr R (Z_to_bv 5 10) = Z_to_bv 64 keys /\
      rkeep R (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x14614) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v keys
    Hv Hv2 Hy E0 RY. subst s0.
  step. step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. rk_tac.
Qed.

Lemma ka_keys_ret : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m v str,
  0 <= v -> v + 56 <= 2 ^ 64 -> 0 <= str < 2 ^ 64 -> s0 = Z_to_bv 64 v ->
  ov_read_bytes rsegs m (wa (v + 16)) 8 = Some (le8 (Z_to_bv 64 str)) ->
  evt rsegs (fun ms => exists R, ms = MS R F (Z_to_bv 64 FUZZ_FREE) fc None m (seg_rom rsegs) /\
      getr R (Z_to_bv 5 1) = Z_to_bv 64 0x14624 /\ getr R (Z_to_bv 5 2) = sp /\
      getr R (Z_to_bv 5 8) = Z_to_bv 64 v /\ getr R (Z_to_bv 5 10) = Z_to_bv 64 str /\
      rkeep R (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x1461c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v str
    Hv Hv2 Hs E0 RS. subst s0.
  step. step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. rk_tac.
Qed.

Lemma ka_str_ret : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m v j xra xs0 xs1 xs2 xs3,
  0 <= v -> v + 56 <= 2 ^ 64 -> s0 = Z_to_bv 64 v -> bv_unsigned sp + 48 < 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp) [CB 8 j; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  evt rsegs (fun ms => exists R, ms = MS R F (Z_to_bv 64 MEMSET) fc None m (seg_rom rsegs) /\
      getr R (Z_to_bv 5 1) = xra /\ getr R (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned sp + 48) /\
      getr R (Z_to_bv 5 8) = xs0 /\ getr R (Z_to_bv 5 9) = xs1 /\
      getr R (Z_to_bv 5 18) = xs2 /\ getr R (Z_to_bv 5 19) = xs3 /\
      getr R (Z_to_bv 5 10) = Z_to_bv 64 v /\ getr R (Z_to_bv 5 11) = Z_to_bv 64 0 /\
      getr R (Z_to_bv 5 12) = Z_to_bv 64 56 /\
      rkeep R (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x14624) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v j
    xra xs0 xs1 xs2 xs3 Hv Hv2 E0 Hsp FR. subst s0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  do 10 step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|].
  split; [rg_tac|]. split; [rg_tac|]. split; [rg_tac|]. rk_tac.
Qed.

Lemma pf_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ka_memset : memset_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m v,
  MemNorm.ro_agree rsegs m -> 0 <= v -> v + 56 <= 2 ^ 64 ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (Z_to_bv 64 (v + i)) = false) ->
  stk rsegs m v (v + 56) ->
  evt rsegs (fun ms => exists R m', ms = MS R F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      rkeep R (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 0) (Z_to_bv 64 56) a3 a4 a5 a6 a7
        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) /\
      getr R (Z_to_bv 5 2) = sp /\ getr R (Z_to_bv 5 8) = s0 /\ getr R (Z_to_bv 5 9) = s1 /\
      getr R (Z_to_bv 5 18) = s2 /\ getr R (Z_to_bv 5 19) = s3 /\
      Frame.munch [(v, v + 56)] m m' /\ Frame.wmono rsegs m m' /\
      bytes_at rsegs m' v (repeat (Z_to_bv 8 0) 56) /\ wr_at rsegs m' v 56 /\ MemNorm.ro_same rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 0) (Z_to_bv 64 56) a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros HMS ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v
    HRO Hv Hv2 HNR ST.
  destruct (stk_carve rsegs m v (v + 56) 56 ST ltac:(lia)) as [_ [junk FR]].
  replace (v + 56 - Z.of_nat 56) with v in FR by lia.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as HR.
  assert (FRn : rw_cells rsegs (MemNorm.normalize rsegs m) (bv_unsigned (Z_to_bv 64 v))
                  [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) junk]).
  { rewrite !unsigned_lit by lia. destruct FR as [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
    - exact (MemNorm.bytes_at_normalize rsegs m v _ HRO Hb).
    - apply (MemNorm.wr_at_norm rsegs m _ v _ HR Hw). intros i Hi. cbn [cells_size csize] in Hi.
      unfold wa. apply HNR. lia. }
  eapply evt_mono.
  { apply (MemNorm.evt_normalize rsegs); [exact pf_wx | exact HRO |].
    exact (HMS ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 0) (Z_to_bv 64 56) a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (MemNorm.normalize rsegs m) junk FRn
      (MemNorm.mem_inv_normalize rsegs m)). }
  intros ms (s0' & Hpost & Hrel & Hro).
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    -> & MU & WM & MI & RW).
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  destruct ms as [rg fr pcv sv rs fcs mm ro]. cbn in E1, E2, E3, E4, E5, E6, E7, E8, Hro |- *.
  subst rg fr pcv sv rs fcs ro.
  rewrite !unsigned_lit in MU, RW by lia.
  eexists _, mm.
  split; [reflexivity|]. split; [rk_tac|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (MemNorm.munch_rel rsegs _ m _ mm m0' HR E8 Hro MU)|].
  split; [exact (MemNorm.wmono_rel rsegs m _ mm m0' HR E8 Hro WM)|].
  destruct RW as [[_ Hb] Hw]. cbn [cells_bytes cbytes app cells_size csize] in Hb, Hw. rewrite app_nil_r in Hb.
  change (Z.to_nat 56) with 56%nat in Hb, Hw.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in Hb.
  split; [exact (proj2 (MemNorm.bytes_at_rel rsegs mm m0' v _ E8) Hb)|].
  split; [exact (MemNorm.wr_at_rel rsegs mm m0' v _ E8 Hw)|].
  exact Hro.
Qed.

Lemma pf_nodup_fst0 : forall (l : list (Z * Z)) a k k', List.NoDup (map fst l) -> In (a, k) l -> In (a, k') l -> k = k'.
Proof.
  induction l as [|[x y] l IH]; intros a k k' HN H1 H2; [destruct H1|].
  cbn in HN. inversion HN as [|? ? Hx HN']; subst.
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - injection E1 as E1a E1k. injection E2 as E2a E2k. congruence.
  - injection E1 as E1a E1k. subst x y. exfalso. apply Hx. apply in_map_iff. exists (a, k'). auto.
  - injection E2 as E2a E2k. subst x y. exfalso. apply Hx. apply in_map_iff. exists (a, k). auto.
  - exact (IH a k k' HN' H1 H2).
Qed.

Lemma pf_nodup_fst : forall (l : list (Z * Z)) a k k', NoDup (map fst l) -> In (a, k) l -> In (a, k') l -> k = k'.
Proof. intros l a k k' HN. apply pf_nodup_fst0. apply NoDup_ListNoDup. exact HN. Qed.

Lemma pf_perm_sub0 : forall (D L : list (Z * Z)), List.NoDup D -> (forall x, In x D -> In x L) ->
  exists R, Permutation L (D ++ R).
Proof.
  induction D as [|x D IH]; intros L HN HI.
  - exists L. reflexivity.
  - inversion HN as [|? ? Hx HN']; subst.
    destruct (in_split x L (HI x (or_introl eq_refl))) as (l1 & l2 & ->).
    destruct (IH (l1 ++ l2) HN') as (R & HR).
    + intros y Hy. assert (Hy' : In y (l1 ++ x :: l2)) by (apply HI; right; exact Hy).
      apply in_app_or in Hy'. apply in_or_app.
      destruct Hy' as [Hy'|[E|Hy']]; [left; exact Hy' | subst; contradiction | right; exact Hy'].
    + exists R. cbn. transitivity (x :: l1 ++ l2); [symmetry; apply Permutation_middle | constructor; exact HR].
Qed.

Lemma pf_perm_sub : forall (D L : list (Z * Z)), NoDup D -> (forall x, In x D -> In x L) ->
  exists R, Permutation L (D ++ R).
Proof. intros D L HN. apply pf_perm_sub0. apply NoDup_ListNoDup. exact HN. Qed.

Lemma pf_perm4 : forall (a b c d : list (Z * Z)), Permutation (a ++ b ++ c ++ d) (d ++ b ++ c ++ a).
Proof.
  intros a b c d. rewrite (app_assoc b c d), (app_assoc b c a), app_assoc.
  eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app_head. apply Permutation_app_comm.
Qed.

Section Struct.
Variable segs : list Segment.

Lemma pf_items_blocks : forall m lblk (P : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a1 D1, P a1 D1 -> forall b, In b D1 -> lblk (fst b) (snd b)) ->
  pf_items segs m lblk P ks a ka n D -> forall b, In b D -> lblk (fst b) (snd b).
Proof.
  intros m lblk P ks n. induction n as [|n IH]; intros a ka D HP H b Hb; cbn [pf_items] in H.
  - subst D. destruct Hb.
  - destruct H as (Dk & D1 & D2 & -> & Hk & H1 & H2).
    apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    + unfold pj_key in Hk. destruct ks.
      * destruct Hk as (x & _ & [(_ & ->)|(k & Hl & ->)]); [destruct Hb|]. destruct Hb as [<-|[]]. exact Hl.
      * subst Dk. destruct Hb.
    + apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (HP _ _ H1 b Hb) | exact (IH _ _ _ HP H2 b Hb)].
Qed.

Lemma pf_fd_blocks : forall m lblk d p D, pj_fd segs m lblk d p D -> forall b, In b D -> lblk (fst b) (snd b).
Proof.
  intros m lblk d. induction d as [|d IH]; intros p D H b Hb; cbn [pj_fd] in H;
    destruct H as (_ & _ & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & _ & HS & HK & HY & HP & HI);
    apply (Permutation_in b HP) in Hb;
    apply in_app_or in Hb; destruct Hb as [Hb|Hb];
    [ destruct HS as [(_ & ->)|(k & Hl & ->)]; [destruct Hb | destruct Hb as [<-|[]]; exact Hl] | |
      destruct HS as [(_ & ->)|(k & Hl & ->)]; [destruct Hb | destruct Hb as [<-|[]]; exact Hl] | ];
    apply in_app_or in Hb; destruct Hb as [Hb|Hb];
    try (destruct HK as [(_ & _ & ->)|(k & Hl & _ & ->)]; [destruct Hb | destruct Hb as [<-|[]]; exact Hl]);
    apply in_app_or in Hb; destruct Hb as [Hb|Hb];
    try (destruct HY as [(_ & _ & ->)|(_ & k & Hl & _ & ->)]; [destruct Hb | destruct Hb as [<-|[]]; exact Hl]).
  - destruct HI as (_ & ->). destruct Hb.
  - exact (pf_items_blocks m lblk _ ks _ _ _ _ IH HI b Hb).
Qed.

Lemma pf_bytes_agree : forall m m' a bs, Mem.bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H3) HA. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (H3 i Hi). exact (HA (Z.of_nat i) ltac:(lia)).
Qed.

Lemma pf_stk_agree : forall m m' lo hi, Frame.stk segs m lo hi ->
  (forall x, lo <= x < hi -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x <-> writable_at segs m' x)) ->
  Frame.stk segs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H3) HA. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H3 a Ha) as [Hw (b & Hb)]. destruct (HA a Ha) as [Hm Hwr]. split.
  - apply Hwr. exact Hw.
  - exists b. rewrite <- Hb. exact Hm.
Qed.

Lemma pf_u64_agree : forall m m' a x, pj_u64 segs m a x ->
  (forall y, a <= y < a + 8 -> mbyte segs m' y = mbyte segs m y) -> pj_u64 segs m' a x.
Proof.
  intros m m' a x (Hx & HB) HA. split; [exact Hx|]. apply (pf_bytes_agree m); [exact HB|].
  rewrite Mem.length_le8. intros i Hi. apply HA. lia.
Qed.

Lemma pf_hdr_agree : forall m m' p ty num str kids keys n cap, pj_hdr segs m p ty num str kids keys n cap ->
  (forall x, p <= x < p + 56 -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x <-> writable_at segs m' x)) ->
  pj_hdr segs m' p ty num str kids keys n cap.
Proof.
  intros m m' p ty num str kids keys n cap ((Hal & Hst) & (Ht & Bt) & H1 & H2 & H3 & H4 & H5 & H6) HA.
  assert (HM : forall y, p <= y < p + 56 -> mbyte segs m' y = mbyte segs m y) by (intros y Hy; exact (proj1 (HA y Hy))).
  split; [split; [exact Hal | exact (pf_stk_agree m m' p (p + 56) Hst HA)]|].
  split; [split; [exact Ht|]; apply (pf_bytes_agree m); [exact Bt|]; rewrite Mem.length_le4; intros i Hi; apply HM; lia|].
  split; [apply (pf_u64_agree m); [exact H1 | intros y Hy; apply HM; lia]|].
  split; [apply (pf_u64_agree m); [exact H2 | intros y Hy; apply HM; lia]|].
  split; [apply (pf_u64_agree m); [exact H3 | intros y Hy; apply HM; lia]|].
  split; [apply (pf_u64_agree m); [exact H4 | intros y Hy; apply HM; lia]|].
  split; [apply (pf_u64_agree m); [exact H5 | intros y Hy; apply HM; lia]|].
  apply (pf_u64_agree m); [exact H6 | intros y Hy; apply HM; lia].
Qed.

Lemma pf_items_frame : forall m lblk m' lblk' (P P' : Z -> list (Z * Z) -> Prop) ks n a ka D,
  pf_items segs m lblk P ks a ka n D ->
  (forall j D1, (j < n)%nat -> incl D1 D -> P (a + 56 * Z.of_nat j) D1 -> P' (a + 56 * Z.of_nat j) D1) ->
  (ks = true -> forall j x, (j < n)%nat -> pj_u64 segs m (ka + 8 * Z.of_nat j) x ->
     pj_u64 segs m' (ka + 8 * Z.of_nat j) x) ->
  (forall a1 k1, In (a1, k1) D -> lblk' a1 k1) ->
  pf_items segs m' lblk' P' ks a ka n D.
Proof.
  intros m lblk m' lblk' P P' ks n. induction n as [|n IH]; intros a ka D H HP HK HL; cbn [pf_items] in H |- *.
  - exact H.
  - destruct H as (Dk & D1 & D2 & -> & Hk & H1 & H2).
    exists Dk, D1, D2. split; [reflexivity|]. split.
    + unfold pj_key in Hk |- *. destruct ks; [|exact Hk].
      destruct Hk as (x & Hx & Hc). exists x. split.
      * pose proof (HK eq_refl 0%nat x ltac:(lia)) as HK0. rewrite Z.add_0_r in HK0. apply HK0. exact Hx.
      * destruct Hc as [Hc|(k & Hl & EDk)]; [left; exact Hc|right]. exists k. split; [|exact EDk].
        apply HL. subst Dk. apply in_or_app. left. left. reflexivity.
    + split.
      * pose proof (HP 0%nat D1 ltac:(lia)) as HP0. rewrite Z.add_0_r in HP0. apply HP0; [|exact H1].
        intros b Hb. apply in_or_app. right. apply in_or_app. left. exact Hb.
      * apply IH; [exact H2 | | | ].
        -- intros j D3 Hj Hs HP3. replace (a + 56 + 56 * Z.of_nat j) with (a + 56 * Z.of_nat (S j)) in * by lia.
           apply HP; [lia | | exact HP3]. intros b Hb. apply in_or_app. right. apply in_or_app. right. apply Hs. exact Hb.
        -- intros Hks j x Hj Hx. replace (ka + 8 + 8 * Z.of_nat j) with (ka + 8 * Z.of_nat (S j)) in * by lia.
           apply (HK Hks (S j)); [lia | exact Hx].
        -- intros a1 k1 Hin. apply HL. apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.

Lemma pf_fd_frame : forall d m lblk m' lblk' p D, pj_fd segs m lblk d p D ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  (forall x, pj_foot p D x -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x <-> writable_at segs m' x)) ->
  pj_fd segs m' lblk' d p D.
Proof.
  induction d as [|d IH]; intros m lblk m' lblk' p D H HL HA; cbn [pj_fd] in H |- *;
    destruct H as (HND & HAP & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & HH & HS & HK & HY & HP & HI);
    (split; [exact HND|]); (split; [exact HAP|]);
    exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di;
    (assert (HD : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D)
       by (intros b Hb; exact (Permutation_in b (Permutation_sym HP) Hb)));
    (split; [apply (pf_hdr_agree m); [exact HH | intros x Hx; apply HA; left; exact Hx]|]);
    (split; [destruct HS as [HS|(k & _ & ->)]; [left; exact HS | right; exists k; split; [apply HL, HD; left; reflexivity | reflexivity]]|]);
    (split; [destruct HK as [HK|(k & _ & Hk & ->)]; [left; exact HK | right; exists k; split; [apply HL, HD; apply in_or_app; right; left; reflexivity | split; [exact Hk | reflexivity]]]|]);
    (split; [destruct HY as [HY|(Hks & k & _ & Hk & ->)]; [left; exact HY | right; split; [exact Hks|]; exists k; split; [apply HL, HD; apply in_or_app; right; apply in_or_app; right; left; reflexivity | split; [exact Hk | reflexivity]]]|]);
    (split; [exact HP|]).
  - exact HI.
  - apply (pf_items_frame m lblk m' lblk' (pj_fd segs m lblk d) _ ks _ kids keys Di HI).
    + intros j D1 Hj Hs HP1. apply (IH m lblk m' lblk' _ D1 HP1).
      * intros a k Hin. apply HL. apply HD. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
        apply Hs. exact Hin.
      * intros x Hx. apply HA. right. destruct Hx as [Hx|(b & Hb & Hx)].
        -- destruct HK as [(_ & En & _)|(k & _ & Hk & EDk)]; [lia|].
           exists (kids, k). split; [apply HD; apply in_or_app; right; rewrite EDk; left; reflexivity|].
           unfold pj_holds; cbn. lia.
        -- exists b. split; [|exact Hx]. apply HD. apply in_or_app. right. apply in_or_app. right. apply in_or_app.
           right. apply Hs. exact Hb.
    + intros Hks j x Hj Hx. apply (pf_u64_agree m); [exact Hx|]. intros y Hy. apply HA. right.
      destruct HY as [(_ & Hf & _)|(_ & k & _ & Hk & EDy)]; [congruence|].
      exists (keys, k). split; [apply HD; apply in_or_app; right; apply in_or_app; right; rewrite EDy; left; reflexivity|].
      unfold pj_holds; cbn. lia.
    + intros a1 k1 Hin. apply HL. apply HD. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      exact Hin.
Qed.

Lemma pf_items_mono : forall m lblk (P P' : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a1 D1, P a1 D1 -> P' a1 D1) -> pf_items segs m lblk P ks a ka n D -> pf_items segs m lblk P' ks a ka n D.
Proof.
  intros m lblk P P' ks n. induction n as [|n IH]; intros a ka D HPP H; cbn [pf_items] in *; [exact H|].
  destruct H as (Dk & D1 & D2 & E & HK & H1 & H2). exists Dk, D1, D2.
  split; [exact E|]. split; [exact HK|]. split; [exact (HPP _ _ H1) | exact (IH _ _ _ HPP H2)].
Qed.

End Struct.

Section Helpers.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Lemma pf_prid : forall A p n, WF A -> In (p, n) (user_blocks A) -> (prid p < length (st_regions A))%nat.
Proof.
  intros A p n HW Hin.
  destruct (YO0x.user_blocks_frame A p n HW Hin) as (g & am & idx & fr & Hu & _ & _ & _ & _ & ->).
  pose proof (YO0u.used_group_prid_lt [] None U0 A g am HW Hu) as H.
  unfold frame_ptr, slot_start. destruct (am_mem am) as [r o]. cbn in H |- *. exact H.
Qed.

Lemma pf_ptr_stable : forall A L L' p, layout_le A L L' -> (prid p < length (st_regions A))%nat ->
  ptr_addr L' p = ptr_addr L p.
Proof.
  intros A L L' [r o] (_ & _ & _ & HR) Hp. unfold ptr_addr, loc_addr. cbn in Hp. rewrite (HR r Hp). reflexivity.
Qed.

Lemma pf_layout_trans : forall A A1 L L1 L2, layout_le A L L1 -> layout_le A1 L1 L2 ->
  (length (st_regions A) <= length (st_regions A1))%nat -> layout_le A L L2.
Proof.
  intros A A1 L L1 L2 (H1 & H2 & H3 & H4) (G1 & G2 & G3 & G4) Hl.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (G4 r ltac:(lia)). apply H4. exact Hr.
Qed.

Lemma pf_blocks_disj : forall L A mem md a1 n1 a2 n2, MR L A mem md ->
  In (a1, n1) (blocks L A) -> In (a2, n2) (blocks L A) -> (a1, n1) <> (a2, n2) -> 0 < n1 -> 0 < n2 ->
  a1 + n1 <= a2 \/ a2 + n2 <= a1.
Proof.
  intros L A mem md a1 n1 a2 n2 HM H1 H2 Hne Hn1 Hn2.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) L A mem md HM) as HP.
  destruct (YI06.pairwise_in2 _ _ _ _ HP H1 H2 Hne) as [Hd|Hd]; unfold ranges_disjoint in Hd; cbn in Hd; lia.
Qed.

Lemma pf_lraw : forall L A mem Lam peak cnt fail a k, ledger B L A mem Lam peak cnt fail -> In (a, k) Lam ->
  0 <= k /\ In (a - 16, k + 16) (blocks L A).
Proof.
  intros L A mem Lam peak cnt fail a k (_ & _ & _ & _ & _ & HF) Hin.
  rewrite Forall_forall in HF. destruct (HF _ Hin) as (H0 & H1 & _). split; assumption.
Qed.

Lemma pf_lfst : forall L A mem Lam peak cnt fail a k k', ledger B L A mem Lam peak cnt fail ->
  In (a, k) Lam -> In (a, k') Lam -> k = k'.
Proof.
  intros L A mem Lam peak cnt fail a k k' (_ & _ & _ & _ & HN & _) H1 H2. exact (pf_nodup_fst Lam a k k' HN H1 H2).
Qed.

Lemma pf_mbyte_munch : forall W m m' a, Frame.munch W m m' -> 0 <= a < 2 ^ 64 -> Frame.outside W a ->
  mbyte segs m' a = mbyte segs m a /\ (writable_at segs m a <-> writable_at segs m' a).
Proof.
  intros W m m' a H Ha Ho. assert (E : m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { apply H. rewrite unsigned_lit by exact Ha. exact Ho. }
  unfold mbyte, writable_at, wview. rewrite E. split; [reflexivity | tauto].
Qed.

Lemma pf_find_seg : forall (l : list Segment) x n seg, find_segment l x n = Some seg ->
  In seg l /\ Z.of_N (seg_base seg) <= x /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction l as [|s l IH]; intros x n seg H; cbn in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2.
    split; [left; reflexivity | lia].
  - destruct (IH x n seg H) as (H1 & H2). split; [right; exact H1 | exact H2].
Qed.

Lemma pf_rsegs_nil : rsegs <> [].
Proof. intro E. discriminate E. Qed.

Lemma pf_img_bound : ms_segs B = rsegs -> forall x, in_img B x -> 0x10000 <= x < 0x55000.
Proof.
  intros HS x (_ & r & Hr & Hx). rewrite HS in Hr. pose proof pf_res_bound as H. unfold res_lo_hi in H.
  rewrite forallb_forall in H. specialize (H r Hr). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Definition res_has (lo hi : Z) : bool :=
  existsb (fun r => (bv_unsigned (fst r) <=? lo) && (hi <=? bv_unsigned (fst r) + bv_unsigned (snd r)))
    (segments_reserved rsegs).

Lemma pf_res_has_img : ms_segs B = rsegs -> forall lo hi, res_has lo hi = true -> forall x, lo <= x < hi -> in_img B x.
Proof.
  intros HS lo hi H x Hx. unfold in_img. rewrite HS. split; [exact pf_rsegs_nil|].
  apply existsb_exists in H as (r & Hin & Hr). exists r. split; [exact Hin|].
  apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma pf_statics_res : res_has G_LIVE (G_LIVE + 8) && res_has G_PEAK (G_PEAK + 8) && res_has G_COUNT (G_COUNT + 8) &&
  res_has G_FAIL (G_FAIL + 8) && res_has strtod_c.STRTOD_ERRNO (strtod_c.STRTOD_ERRNO + 4) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pf_statics_img : ms_segs B = rsegs -> forall x, alloc_statics x -> in_img B x.
Proof.
  intros HS x Hx. pose proof pf_statics_res as H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  unfold alloc_statics in Hx. destruct Hx as [Hx|[Hx|[Hx|Hx]]];
    [exact (pf_res_has_img HS _ _ H1 x Hx) | exact (pf_res_has_img HS _ _ H2 x Hx) |
     exact (pf_res_has_img HS _ _ H3 x Hx) | exact (pf_res_has_img HS _ _ H4 x Hx)].
Qed.

Lemma pf_errno_img : ms_segs B = rsegs -> forall x, strtod_c.STRTOD_ERRNO <= x < strtod_c.STRTOD_ERRNO + 4 -> in_img B x.
Proof.
  intros HS x Hx. pose proof pf_statics_res as H. apply andb_prop in H as [_ H]. exact (pf_res_has_img HS _ _ H x Hx).
Qed.

Definition res_cover : bool :=
  forallb (fun s => let r := segment_reservation s in
    (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r))) rsegs.

Lemma pf_res_cover : res_cover = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pf_find_img : ms_segs B = rsegs -> forall x seg, find_segment rsegs x 1 = Some seg -> in_img B x.
Proof.
  intros HS x seg H. destruct (pf_find_seg rsegs x 1 seg H) as (Hin & H1 & H2).
  unfold in_img. rewrite HS. split; [exact pf_rsegs_nil|]. exists (segment_reservation seg).
  split; [apply in_map; exact Hin|].
  pose proof pf_res_cover as C. unfold res_cover in C. rewrite forallb_forall in C. specialize (C seg Hin).
  cbv zeta in C. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1, C2. lia.
Qed.

Lemma pf_not_img_ro : ms_segs B = rsegs -> forall x, 0 <= x < 2 ^ 64 -> ~ in_img B x ->
  ro_addr rsegs (Z_to_bv 64 x) = false.
Proof.
  intros HS x Hx Hn. unfold ro_addr. rewrite unsigned_lit by exact Hx.
  destruct (find_segment rsegs x 1) as [seg|] eqn:F; [|reflexivity].
  exfalso. exact (Hn (pf_find_img HS x seg F)).
Qed.

Lemma pf_static_low : forall L A mem md a, MR L A mem md -> static_owned B a -> a < alloc_ceiling.
Proof.
  intros L A mem md a HM Hs. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md a HM (or_intror Hs)). lia.
Qed.

Lemma pf_out1 : forall lo hi x, x < lo \/ hi <= x -> Frame.outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn. split; [lia | exact I]. Qed.

Lemma pf_blk_range : forall L A mem md a k, MR L A mem md -> In (a, k) (blocks L A) ->
  4096 <= a /\ a + k <= alloc_ceiling.
Proof.
  intros L A mem md a k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq).
  cbn [fst snd] in Eq. injection Eq as <- <-. exact (mr_blocks_range _ _ (aa_laws API) L A mem md q k' HM Hq).
Qed.

Lemma pf_blk_present : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  present mem (a + i) /\ ~ owned B L A (a + i).
Proof.
  intros L A mem md a k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq).
  cbn [fst snd] in Eq. injection Eq as <- <-.
  destruct (mr_blocks _ _ (aa_laws API) L A mem md q k' i HM Hq Hi) as (H1 & _ & _ & H4). split; assumption.
Qed.

Lemma pf_blk_user : forall L A a k, In (a, k) (blocks L A) -> exists q, In (q, k) (user_blocks A) /\ ptr_addr L q = a.
Proof.
  intros L A a k Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq).
  cbn [fst snd] in Eq. injection Eq as <- <-. exists q. split; [exact Hq | reflexivity].
Qed.

Lemma pf_present_wr : forall mem a, present mem a -> writable_at segs mem a.
Proof. intros mem a (b & Hb). unfold writable_at, wview. rewrite Hb. discriminate. Qed.

Lemma pf_MR_munch : forall L A mem mem' md W, MR L A mem md -> Frame.munch W mem mem' ->
  (forall x, 0 <= x < alloc_ceiling -> Frame.outside W x) -> MR L A mem' md.
Proof.
  intros L A mem mem' md W HM Hm HW. pose proof alloc_ceiling_lt as Hc.
  assert (Heq : forall x, 0 <= x < alloc_ceiling -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hx. apply Hm. rewrite unsigned_lit by lia. apply HW. exact Hx. }
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
  apply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
  - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
    unfold mbyte. rewrite (Heq a) by lia. reflexivity.
  - intros a Ho (b & Hb). pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
    exists b. rewrite (Heq a) by lia. exact Hb.
  - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as ((b & Hb) & H1 & H2 & _).
    exists b. rewrite (Heq (ptr_addr L p + i)) by lia. exact Hb.
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hmat.
Qed.

Lemma sptr_eq_dec : forall p q : sptr, {p = q} + {p <> q}.
Proof. decide equality; [apply Z.eq_dec | apply Nat.eq_dec]. Qed.

Lemma ub_eq_dec : forall x y : sptr * Z, {x = y} + {x <> y}.
Proof. decide equality; [apply Z.eq_dec | apply sptr_eq_dec]. Qed.

Lemma zz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.

Lemma pf_rpost_refl : forall K L A regs mem md (E : Z -> Prop) (gone : Z -> Z -> Prop) regs',
  call_pre_k B MR K L A regs mem md -> (forall r, getr regs' r = getr regs r) ->
  rpost B API K L A regs mem md E gone L A regs' mem md.
Proof.
  intros K L A regs mem md E gone regs' (HM & HW & HB & _ & _ & _ & _ & HSW & _ & HEW & _) Hg.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [tauto|]. split; [intros _ i _; reflexivity|]. split; [lia|]. split; [intros p n Hin _; exact Hin|].
  split; [intros p n _ _; reflexivity|]. split; [intros r _; apply Hg|].
  split; [exists (m_vmmaps md); apply YI06.with_vmmaps_self|].
  split; [intros; split; [reflexivity | tauto]|]. split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|].
  intros a [Ha|Ha]; [apply HSW; exact Ha | apply HEW; exact Ha].
Qed.

End Helpers.

Definition rmk (regs : bvmap 5 word) : bvmap 5 word :=
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
    (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
    (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
    (getr regs 29) (getr regs 30) (getr regs 31).

Lemma pf_getr_eqv : forall R R', Regs6ss.xregs_eqv R R' -> forall r, getr R' r = getr R r.
Proof.
  intros R R' H r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. rewrite <- bv_eqb0_is_x0. exact E.
Qed.

Lemma pf_ret_ok : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 z).
Proof.
  intros z Hz Hm. unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ. rewrite unsigned_lit by lia. rewrite Z.add_0_r.
  rewrite (YK0s.land_m2_even z Hm). reflexivity.
Qed.

Lemma pf_pres_keep : forall R R', regs_preserved R R' -> rkeep R' R.
Proof. intros R R' H r Hr. apply H. unfold callee_saved. lia. Qed.

Lemma pf_cells_agree : forall segs m m' A cs, rw_cells segs m A cs ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) ->
     mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x <-> writable_at segs m' x)) ->
  rw_cells segs m' A cs.
Proof.
  intros segs m m' A cs [[Hwf Hb] (W1 & W2 & W3)] HA. split; [split; [exact Hwf|]|].
  - apply (pf_bytes_agree segs m); [exact Hb|]. rewrite cells_bytes_length by exact Hwf.
    intros i Hi. exact (proj1 (HA (A + i) ltac:(lia))).
  - split; [exact W1|]. split; [exact W2|]. intros i Hi. apply (proj2 (HA (A + i) ltac:(lia))). exact (W3 i Hi).
Qed.

Lemma pf_g1 : forall R, getr R 1 = getr R (Z_to_bv 5 1). Proof. reflexivity. Qed.
Lemma pf_g2 : forall R, getr R 2 = getr R (Z_to_bv 5 2). Proof. reflexivity. Qed.
Lemma pf_g4 : forall R, getr R 4 = getr R (Z_to_bv 5 4). Proof. reflexivity. Qed.
Lemma pf_g8 : forall R, getr R 8 = getr R (Z_to_bv 5 8). Proof. reflexivity. Qed.
Lemma pf_g9 : forall R, getr R 9 = getr R (Z_to_bv 5 9). Proof. reflexivity. Qed.
Lemma pf_g10 : forall R, getr R 10 = getr R (Z_to_bv 5 10). Proof. reflexivity. Qed.
Lemma pf_g11 : forall R, getr R 11 = getr R (Z_to_bv 5 11). Proof. reflexivity. Qed.
Lemma pf_g12 : forall R, getr R 12 = getr R (Z_to_bv 5 12). Proof. reflexivity. Qed.
Lemma pf_g18 : forall R, getr R 18 = getr R (Z_to_bv 5 18). Proof. reflexivity. Qed.
Lemma pf_g19 : forall R, getr R 19 = getr R (Z_to_bv 5 19). Proof. reflexivity. Qed.

Lemma pf_rmk_getr : forall regs r, getr (rmk regs) r = getr regs r.
Proof. intros regs r. apply pf_getr_eqv. exact (Regs6ss.mkR_of_eqv regs). Qed.

Lemma pf_mod2_land : forall x, (x mod 2 ^ 64) mod 2 = x mod 2.
Proof.
  intros x. change ((x mod 2 ^ 64) mod 2) with ((x mod 2 ^ 64) mod 2 ^ 1). change (x mod 2) with (x mod 2 ^ 1).
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

Lemma pf_land_m2 : forall x, Z.land x (-2) mod 2 = 0.
Proof.
  intros x. change (Z.land x (-2) mod 2) with (Z.land x (-2) mod 2 ^ 1).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. apply Z.land_0_r.
Qed.

Lemma pf_ret_pc : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k Hk. unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ in Hk.
  pose proof (bv_unsigned_in_range 64 k) as Hr.
  assert (Hz : bv_unsigned k = Z.land (bv_unsigned k) (-2) mod 2 ^ 64).
  { rewrite <- Hk at 1. rewrite Z_to_bv_unsigned, Z.add_0_r. reflexivity. }
  assert (Hm : bv_unsigned k mod 2 = 0) by (rewrite Hz, pf_mod2_land; apply pf_land_m2).
  rewrite <- (MState.Z_to_bv_bv_unsigned k). apply MState.ret_pc_even; [exact Hr | exact Hm].
Qed.

Section Glue.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Local Notation segs := (ms_segs B).

Lemma pf_run : forall regs pc mem md (Kp : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt segs (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom segs) /\ Kp R pc' mem')
    (MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom segs)) ->
  (forall R pc' mem' regs', Kp R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     SR segs (mkCfg (mkst regs' pc' mem' (seg_rom segs)) md) P) ->
  SR segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) P.
Proof.
  intros regs pc mem md Kp P Hh Hl HE HK.
  eapply (evt_SR_canon segs (mkst regs pc mem (seg_rom segs)) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & pc' & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' HKR). apply pf_getr_eqv. exact HR.
Qed.

End Glue.

Definition pjf_at {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) (F : ResForm)
    (d : nat) : Prop :=
  forall L A regs mem md Lam peak cnt fail b v D,
    reader_env B API (PJ_FREE_K d) L A regs mem md ->
    ledger B L A mem Lam peak cnt fail ->
    rf_ok F A b ->
    getr regs 10 = Z_to_bv 64 v ->
    (v = 0 /\ D = [] \/
     v <> 0 /\ pj_fd (ms_segs B) mem (lin Lam) d v D /\ rplace B L A Lam regs mem v /\
     Frame.disjoint_from [(v, v + 56)] (spZ regs - PJ_FREE_K d) (PJ_FREE_K d)) ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 PJ_FREE) mem (seg_rom (ms_segs B))) md)
      (fun c' => exists L' A' regs' mem' md' Lam',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
         rpost B API (PJ_FREE_K d) L A regs mem md (pj_free_writes v D) (freed D) L' A' regs' mem' md' /\
         rd_cells B mem' /\
         Permutation Lam (D ++ Lam') /\
         ledger B L' A' mem' Lam' peak cnt fail /\
         (exists D', Permutation D D' /\ rf_ok F A' (rf_frees F b D')) /\
         (v = 0 -> L' = L /\ A' = A /\ Lam' = Lam) /\
         (v <> 0 -> pj_zero (ms_segs B) mem' v)).

Section Node.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Local Notation segs := (ms_segs B).
Local Notation MR := (aa_MR API).

Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (Lam0 : list (Z * Z)) (peak cnt fail : Z) (b0 : rf_R F) (v : Z) (d : nat) (D : list (Z * Z)).
Hypothesis HENV : reader_env B API (PJ_FREE_K d) L0 A0 regs0 mem0 md0.
Hypothesis HLED : ledger B L0 A0 mem0 Lam0 peak cnt fail.
Hypothesis HRES : rf_ok F A0 b0.
Hypothesis HA0 : getr regs0 10 = Z_to_bv 64 v.
Hypothesis HV : v <> 0.
Hypothesis HPL : rplace B L0 A0 Lam0 regs0 mem0 v.
Variables (ty num str kids keys n cap : Z) (ks : bool) (Ds Dk Dy Di Rest0 : list (Z * Z)).
Hypothesis HND : NoDup D.
Hypothesis HAP : pj_apart D v.
Hypothesis HHD : pj_hdr segs mem0 v ty num str kids keys n cap.
Hypothesis HS : str = 0 /\ Ds = [] \/ exists k, lin Lam0 str k /\ Ds = [(str, k)].
Hypothesis HK : kids = 0 /\ n = 0 /\ Dk = [] \/ exists k, lin Lam0 kids k /\ 56 * n <= k /\ Dk = [(kids, k)].
Hypothesis HY : keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k, lin Lam0 keys k /\ 8 * n <= k /\ Dy = [(keys, k)].
Hypothesis HP : Permutation D (Ds ++ Dk ++ Dy ++ Di).
Hypothesis HREST : Permutation Lam0 (D ++ Rest0).
Hypothesis FF : fuzz_free_contract B API F.
Hypothesis MSC : memset_contract.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis IH : forall d', d = S d' -> pjf_at B API F d'.

Local Notation K := (PJ_FREE_K d).
Local Notation sp0 := (spZ regs0).
Local Notation E := (pj_free_writes v D).

Lemma n_seg : ms_segs B = rsegs.
Proof. destruct HENV as (H & _). exact H. Qed.

Lemma n_pre : call_pre_k B MR K L0 A0 regs0 mem0 md0.
Proof. destruct HENV as (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma n_K : 48 + ALLOC_STACK <= K.
Proof. unfold PJ_FREE_K, PJ_FREE_F, FREE_K. lia. Qed.

Lemma n_sp : sp0 mod 16 = 0 /\ alloc_ceiling + K <= sp0 /\ sp0 <= 2 ^ 47.
Proof.
  destruct HENV as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & H1 & H2 & _) & H3 & _). split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma n_MR0 : MR L0 A0 mem0 md0 /\ WF A0 /\ bounded A0.
Proof. destruct n_pre as (H1 & H2 & H3 & _). split; [exact H1|]. split; [exact H2 | exact H3]. Qed.

Lemma n_ceil : 140735332483072 <= alloc_ceiling < 2 ^ 47.
Proof. pose proof alloc_ceiling_value. pose proof alloc_ceiling_lt. lia. Qed.

Lemma n_v : 0 < v /\ v + 56 <= 2 ^ 64 /\ v mod 8 = 0.
Proof. destruct HHD as ((Hal & (H0 & H1 & _)) & _). split; [lia|]. split; [exact H1 | exact Hal]. Qed.

Lemma n_Dsub : forall x, In x D -> In x Lam0.
Proof. intros x H. apply (Permutation_in x (Permutation_sym HREST)). apply in_or_app. left. exact H. Qed.

Lemma n_vplace0 : sp0 <= v \/
  exists ra rk, In (ra, rk) (blocks L0 A0) /\ ~ In (ra + 16, rk - 16) D /\ ra <= v /\ v + 56 <= ra + rk.
Proof.
  destruct HPL as (Hpl & _ & _). destruct Hpl as [(H1 & _)|[(a & k & Hb & Hn & H1 & H2)|(a & k & Hl & H1 & H2)]].
  - left. exact H1.
  - right. exists a, k. split; [exact Hb|]. split; [intro Hi; apply Hn; apply n_Dsub; exact Hi|]. split; assumption.
  - right. destruct (pf_lraw B (L0) A0 mem0 Lam0 peak cnt fail a k HLED Hl) as (Hk & Hb).
    exists (a - 16), (k + 16). split; [exact Hb|].
    replace (a - 16 + 16) with a by lia. replace (k + 16 - 16) with k by lia.
    split; [|lia]. intro Hi. apply (HAP (a, k) v Hi); [unfold pj_holds; cbn; lia | lia].
Qed.

Lemma n_vbelow : v + 56 <= sp0 - K \/ sp0 <= v.
Proof.
  destruct n_vplace0 as [H|(ra & rk & Hb & _ & H1 & H2)]; [right; exact H|left].
  destruct n_MR0 as (HM & _). pose proof (pf_blk_range B API L0 A0 mem0 md0 ra rk HM Hb). pose proof n_sp. lia.
Qed.

Definition rrel (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model) : Prop :=
  MR Lc Ac memc mdc /\ WF Ac /\ bounded Ac /\ layout_le A0 L0 Lc /\
  (st_init_done A0 = true -> st_init_done Ac = true) /\
  (length (st_regions A0) <= length (st_regions Ac))%nat /\
  (forall p m, In (p, m) (user_blocks A0) -> ~ freed D (ptr_addr L0 p) m -> In (p, m) (user_blocks Ac)) /\
  (exists vm', mdc = with_vmmaps vm' md0) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B K regs0 a -> ~ E a ->
     mbyte segs memc a = mbyte segs mem0 a /\ (writable_at segs mem0 a <-> writable_at segs memc a)) /\
  (forall a, in_img B a -> (forall L1 A1 m1 md1, MR L1 A1 m1 md1 -> ~ owned B L1 A1 a) ->
     ~ scratch_k B K regs0 a -> ~ E a ->
     mbyte segs memc a = mbyte segs mem0 a /\ (writable_at segs mem0 a <-> writable_at segs memc a)) /\
  (forall p m i, In (p, m) (user_blocks A0) -> In (p, m) (user_blocks Ac) -> 0 <= i < m ->
     ~ E (ptr_addr L0 p + i) -> mbyte segs memc (ptr_addr L0 p + i) = mbyte segs mem0 (ptr_addr L0 p + i)) /\
  (forall a, scratch_k B K regs0 a -> writable_at segs memc a) /\
  (st_init_done Ac = false -> forall i, 0 <= i < 8 ->
     mbyte segs memc (ms_libc B + 8 + i) = mbyte segs mem0 (ms_libc B + 8 + i)).

Lemma rrel_init : rrel L0 A0 mem0 md0.
Proof.
  destruct n_pre as (HM & HW & HB & _ & _ & _ & _ & HSW & _ & HEW & _).
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [tauto|]. split; [lia|]. split; [intros p m H _; exact H|].
  split; [exists (m_vmmaps md0); apply YI06.with_vmmaps_self|].
  split; [intros; split; [reflexivity | tauto]|]. split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|]. split; [|intros; reflexivity].
  intros a [Ha|Ha]; [apply HSW; exact Ha | apply HEW; exact Ha].
Qed.

Lemma rrel_ptr : forall Lc Ac memc mdc p m, rrel Lc Ac memc mdc -> In (p, m) (user_blocks A0) ->
  ptr_addr Lc p = ptr_addr L0 p.
Proof.
  intros Lc Ac memc mdc p m (_ & _ & _ & HL & _) Hin. destruct n_MR0 as (_ & HW & _).
  exact (pf_ptr_stable A0 L0 Lc p HL (pf_prid A0 p m HW Hin)).
Qed.

Lemma rrel_ub_gone : forall Lc Ac memc mdc p m i, rrel Lc Ac memc mdc -> In (p, m) (user_blocks A0) ->
  ~ In (p, m) (user_blocks Ac) -> 0 <= i < m -> E (ptr_addr L0 p + i).
Proof.
  intros Lc Ac memc mdc p m i (_ & _ & _ & _ & _ & _ & Hk & _) Hin Hn Hi.
  destruct (in_dec zz_eq_dec (ptr_addr L0 p + 16, m - 16) D) as [Hf|Hf].
  - split; [exact HV|]. right. left. exists (ptr_addr L0 p + 16), (m - 16). split; [exact Hf | lia].
  - exfalso. apply Hn. apply Hk; [exact Hin | exact Hf].
Qed.

Lemma rrel_store : forall Lc Ac memc mdc memc', rrel Lc Ac memc mdc ->
  Frame.munch [(sp0 - 48, sp0)] memc memc' -> Frame.wmono segs memc memc' -> rrel Lc Ac memc' mdc.
Proof.
  intros Lc Ac memc mdc memc' HR Hmu Hwm. pose proof HR as (HM & HW & HB & HL & HI & HLn & Hk & Hmd & HH & HG & HU & HSW & HAV).
  pose proof n_sp as (_ & Hsp & Hsp2). pose proof n_K as HKK. pose proof n_ceil as Hc. unfold ALLOC_STACK in HKK.
  assert (Hout : forall x, 0 <= x < alloc_ceiling -> Frame.outside [(sp0 - 48, sp0)] x)
    by (intros x Hx; apply pf_out1; lia).
  split; [exact (pf_MR_munch B API Lc Ac memc memc' mdc _ HM Hmu Hout)|].
  split; [exact HW|]. split; [exact HB|]. split; [exact HL|]. split; [exact HI|]. split; [exact HLn|].
  split; [exact Hk|]. split; [exact Hmd|].
  split.
  { intros a Ha Hs He. destruct (HH a Ha Hs He) as [E1 E2].
    assert (Ho : Frame.outside [(sp0 - 48, sp0)] a).
    { apply pf_out1. destruct (Z_lt_le_dec a (sp0 - 48)) as [Hw|Hw]; [left; exact Hw|].
      destruct (Z_lt_le_dec a sp0) as [Hw'|Hw']; [exfalso; apply Hs; left; lia | right; exact Hw']. }
    destruct (pf_mbyte_munch B _ memc memc' a Hmu ltac:(lia) Ho) as [F1 F2]. split; [congruence | tauto]. }
  split.
  { intros a Ha Hno Hs He. destruct (HG a Ha Hno Hs He) as [E1 E2].
    pose proof (pf_img_bound B n_seg a Ha) as Hab.
    destruct (pf_mbyte_munch B _ memc memc' a Hmu ltac:(lia) (Hout a ltac:(lia))) as [F1 F2]. split; [congruence | tauto]. }
  split.
  { intros p m i Hin Hin' Hi He. rewrite <- (HU p m i Hin Hin' Hi He).
    rewrite <- (rrel_ptr Lc Ac memc mdc p m HR Hin).
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p m i HM Hin' Hi) as (_ & H1 & H2 & _).
    exact (proj1 (pf_mbyte_munch B _ memc memc' (ptr_addr Lc p + i) Hmu ltac:(lia) (Hout (ptr_addr Lc p + i) ltac:(lia)))). }
  split.
  { intros a Ha. unfold writable_at. apply Hwm. exact (HSW a Ha). }
  intros Hf i Hi. rewrite <- (HAV Hf i Hi).
  assert (Hs : static_owned B (ms_libc B + 8 + i)) by (unfold static_owned; right; right; left; lia).
  pose proof (pf_static_low B API Lc Ac memc mdc _ HM Hs).
  pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM (or_intror Hs)).
  exact (proj1 (pf_mbyte_munch B _ memc memc' (ms_libc B + 8 + i) Hmu ltac:(lia) (Hout (ms_libc B + 8 + i) ltac:(lia)))).
Qed.

Lemma n_blk_set_low : forall x, blk_set D x -> x < alloc_ceiling.
Proof.
  intros x (a & k & Hin & Hx). destruct n_MR0 as (HM & _).
  destruct (pf_lraw B L0 A0 mem0 Lam0 peak cnt fail a k HLED (n_Dsub _ Hin)) as (Hk & Hraw).
  pose proof (pf_blk_range B API L0 A0 mem0 md0 _ _ HM Hraw). lia.
Qed.

Lemma n_E_win : forall a, sp0 - K <= a < sp0 -> ~ E a.
Proof.
  intros a Ha (_ & [Hw|[Hw|Hw]]).
  - pose proof n_vbelow. lia.
  - pose proof (n_blk_set_low a Hw). pose proof n_sp. lia.
  - pose proof (pf_img_bound B n_seg a (pf_statics_img B n_seg a Hw)). pose proof n_sp. pose proof n_ceil. lia.
Qed.

Lemma rrel_ff : forall Lc Ac memc mdc Lamc regs_c p k L' A' regs' mem' md',
  rrel Lc Ac memc mdc -> ledger B Lc Ac memc Lamc peak cnt fail -> In (p, k) D -> In (p, k) Lamc ->
  spZ regs_c = sp0 - 48 ->
  call_post_k B MR ALLOC_STACK Lc Ac regs_c memc mdc (free_writes p k) L' A' regs' mem' md' ->
  (st_init_done Ac = true -> st_init_done A' = true) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  ublocks_kept Lc Ac A' (p - 16, k + 16) ->
  rrel L' A' mem' md'.
Proof.
  intros Lc Ac memc mdc Lamc regs_c p k L' A' regs' mem' md' HR HLc HpD HpL Hsp Hpost Hin Hlen Hkept.
  pose proof HR as (HM & HW & HB & HL & HI & HLn & Hk & Hmd & HH & HG & HU & HSW & HAV).
  pose proof Hpost as (HM' & HW' & HB' & HL' & HPA & _ & Hmd' & HF & HUB & HSW').
  pose proof n_sp as (_ & Hsp0 & Hsp2). pose proof n_K as HKK. pose proof n_ceil as Hc. unfold ALLOC_STACK in HKK.
  destruct (pf_lraw B Lc Ac memc Lamc peak cnt fail p k HLc HpL) as (Hk0 & Hraw).
  destruct (pf_blk_range B API Lc Ac memc mdc _ _ HM Hraw) as (Hr1 & Hr2).
  assert (HGL : G_LIVE + 8 <= alloc_ceiling) by (unfold G_LIVE; lia).
  assert (HnFW : forall a, alloc_ceiling <= a -> ~ free_writes p k a) by (intros a Ha [Hw|(_ & Hw)]; lia).
  assert (HSC : forall a, ~ scratch_k B K regs0 a -> ~ scratch_k B ALLOC_STACK regs_c a).
  { intros a Hs [Hw|Hw]; apply Hs; [left | right; exact Hw]. unfold ALLOC_STACK in Hw. lia. }
  assert (HFE : forall a, free_writes p k a -> E a).
  { intros a [Hw|(_ & Hw)]; split; try exact HV; right; [right; left; exact Hw | left; exists p, k; split; [exact HpD | lia]]. }
  split; [exact HM'|]. split; [exact HW'|]. split; [exact HB'|].
  split; [exact (pf_layout_trans A0 Ac L0 Lc L' HL HL' HLn)|].
  split; [intros H0; apply Hin; apply HI; exact H0|]. split; [lia|].
  split.
  { intros q m Hq Hf. apply Hkept; [apply Hk; assumption|].
    rewrite (rrel_ptr Lc Ac memc mdc q m HR Hq). intro Eq. injection Eq as E1 E2. apply Hf. unfold freed.
    replace (ptr_addr L0 q + 16) with p by lia. replace (m - 16) with k by lia. exact HpD. }
  split.
  { destruct Hmd as (vm & ->). destruct Hmd' as (vm' & ->). exists vm'. apply YI06.with_vmmaps_twice. }
  split.
  { intros a Ha Hs He. destruct (HH a Ha Hs He) as [E1 E2].
    assert (Ho : ~ owned B Lc Ac a) by (intro Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho); lia).
    assert (Ho' : ~ owned B L' A' a) by (intro Ho'; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho'); lia).
    destruct (HF a (or_introl Ha) Ho Ho' (HSC a Hs) (HnFW a (proj1 Ha))) as [F1 F2].
    split; [rewrite F1; exact E1 | tauto]. }
  split.
  { intros a Ha Hno Hs He. destruct (HG a Ha Hno Hs He) as [E1 E2].
    pose proof (pf_img_bound B n_seg a Ha) as Hab.
    assert (Hs' : ~ scratch_k B ALLOC_STACK regs_c a).
    { intros [Hw|Hw]; [unfold ALLOC_STACK in Hw; lia | apply Hs; right; exact Hw]. }
    destruct (HF a (or_intror Ha) (Hno _ _ _ _ HM) (Hno _ _ _ _ HM') Hs' (fun Hw => He (HFE a Hw))) as [F1 F2].
    split; [rewrite F1; exact E1 | tauto]. }
  split.
  { intros q m i Hq Hq' Hi He.
    destruct (in_dec ub_eq_dec (q, m) (user_blocks Ac)) as [Hc'|Hc'].
    - rewrite <- (HU q m i Hq Hc' Hi He). rewrite <- (rrel_ptr Lc Ac memc mdc q m HR Hq).
      exact (HUB q m i Hc' Hq' Hi).
    - exfalso. exact (He (rrel_ub_gone Lc Ac memc mdc q m i HR Hq Hc' Hi)). }
  split.
  { intros a Ha.
    assert (Hd : scratch_k B ALLOC_STACK regs_c a \/ ~ scratch_k B ALLOC_STACK regs_c a) by (unfold scratch_k; lia).
    destruct Hd as [Hd|Hs']; [apply HSW'; exact Hd|].
    destruct Ha as [Ha|Ha]; [|exfalso; apply Hs'; right; exact Ha].
    assert (Ho : ~ owned B Lc Ac a) by (intro Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho); lia).
    assert (Ho' : ~ owned B L' A' a) by (intro Ho'; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho'); lia).
    assert (Hac : alloc_ceiling <= a < 2 ^ 64) by lia.
    destruct (HF a (or_introl Hac) Ho Ho' Hs' (HnFW a (proj1 Hac))) as [_ F2].
    apply F2. apply HSW. left. exact Ha. }
  intros Hf. exfalso. destruct (pf_blk_user _ _ _ _ Hraw) as (q & Hq & _).
  assert (Hi : st_init_done Ac = true) by exact (YI04.init_done_of_block Ac (q, k + 16) HW Hq).
  rewrite (Hin Hi) in Hf. discriminate.
Qed.

Lemma rrel_child : forall Lc Ac memc mdc regs_c d' c D1 L' A' regs' mem' md',
  rrel Lc Ac memc mdc -> d = S d' -> spZ regs_c = sp0 - 48 -> incl D1 D -> c <> 0 ->
  (forall x, c <= x < c + 56 -> blk_set D x) ->
  rpost B API (PJ_FREE_K d') Lc Ac regs_c memc mdc (pj_free_writes c D1) (freed D1) L' A' regs' mem' md' ->
  rrel L' A' mem' md'.
Proof.
  intros Lc Ac memc mdc regs_c d' c D1 L' A' regs' mem' md' HR Hd Hsp HDs Hc0 Hcb Hpost.
  pose proof HR as (HM & HW & HB & HL & HI & HLn & Hk & Hmd & HH & HG & HU & HSW & HAV).
  pose proof Hpost as (HM' & HW' & HB' & HL' & HI' & HAV' & HLn' & Hk' & HPA & _ & Hmd' & HF & HFG & HUB & HSW').
  pose proof n_sp as (_ & Hsp0 & Hsp2). pose proof n_ceil as Hc.
  assert (HKd : PJ_FREE_K d = PJ_FREE_K d' + 48) by (rewrite Hd; unfold PJ_FREE_K, PJ_FREE_F; lia).
  assert (HSC : forall a, ~ scratch_k B K regs0 a -> ~ scratch_k B (PJ_FREE_K d') regs_c a).
  { intros a Hs [Hw|Hw]; apply Hs; [left | right; exact Hw]. lia. }
  assert (HFE : forall a, pj_free_writes c D1 a -> E a).
  { intros a (_ & [Hw|[(a1 & k1 & Hin1 & Hw)|Hw]]); split; try exact HV; right.
    - left. exact (Hcb a Hw).
    - left. exists a1, k1. split; [apply HDs; exact Hin1 | exact Hw].
    - right. exact Hw. }
  split; [exact HM'|]. split; [exact HW'|]. split; [exact HB'|].
  split; [exact (pf_layout_trans A0 Ac L0 Lc L' HL HL' HLn)|].
  split; [intros H0; apply HI'; apply HI; exact H0|]. split; [lia|].
  split.
  { intros q m Hq Hf. apply Hk'; [apply Hk; assumption|].
    rewrite (rrel_ptr Lc Ac memc mdc q m HR Hq). intro Hf1. apply Hf. apply HDs. exact Hf1. }
  split.
  { destruct Hmd as (vm & ->). destruct Hmd' as (vm' & ->). exists vm'. apply YI06.with_vmmaps_twice. }
  split.
  { intros a Ha Hs He. destruct (HH a Ha Hs He) as [E1 E2].
    destruct (HF a Ha (HSC a Hs) (fun Hw => He (HFE a Hw))) as [F1 F2].
    split; [rewrite F1; exact E1 | tauto]. }
  split.
  { intros a Ha Hno Hs He. destruct (HG a Ha Hno Hs He) as [E1 E2].
    destruct (HFG a Ha Hno (HSC a Hs) (fun Hw => He (HFE a Hw))) as [F1 F2].
    split; [rewrite F1; exact E1 | tauto]. }
  split.
  { intros q m i Hq Hq' Hi He.
    destruct (in_dec ub_eq_dec (q, m) (user_blocks Ac)) as [Hc'|Hc'].
    - rewrite <- (HU q m i Hq Hc' Hi He). rewrite <- (rrel_ptr Lc Ac memc mdc q m HR Hq).
      apply (HUB q m i Hc' Hq' Hi). rewrite (rrel_ptr Lc Ac memc mdc q m HR Hq).
      intro Hw. exact (He (HFE _ Hw)).
    - exfalso. exact (He (rrel_ub_gone Lc Ac memc mdc q m i HR Hq Hc' Hi)). }
  split.
  { intros a Ha.
    assert (Hdc : scratch_k B (PJ_FREE_K d') regs_c a \/ ~ scratch_k B (PJ_FREE_K d') regs_c a) by (unfold scratch_k; lia).
    destruct Hdc as [Hdc|Hs']; [apply HSW'; exact Hdc|].
    destruct Ha as [Ha|Ha]; [|exfalso; apply Hs'; right; exact Ha].
    assert (HnE : ~ pj_free_writes c D1 a) by (intro Hw; exact (n_E_win a Ha (HFE a Hw))).
    assert (Hac : alloc_ceiling <= a < 2 ^ 64) by lia.
    destruct (HF a Hac Hs' HnE) as [_ F2]. apply F2. apply HSW. left. exact Ha. }
  intros Hf i Hi. rewrite (HAV' Hf i Hi). apply HAV; [|exact Hi].
  destruct (st_init_done Ac) eqn:EI; [rewrite (HI' eq_refl) in Hf; discriminate | reflexivity].
Qed.

Lemma n_word_agree : forall m m' a w, word_mem segs m a w ->
  (forall k, 0 <= k < 8 -> mbyte segs m' (a + k) = mbyte segs m (a + k)) -> word_mem segs m' a w.
Proof. intros m m' a w H HA k Hk. rewrite HA by lia. exact (H k Hk). Qed.

Lemma n_auxv_agree : forall sec lo m m', auxv_pre B sec lo m ->
  (forall x, (ms_libc B + 8 <= x < ms_libc B + 16) \/ (lo <= x < 2 ^ 63) -> mbyte segs m' x = mbyte segs m x) ->
  auxv_pre B sec lo m'.
Proof.
  intros sec lo m m' (av & ar & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) HA.
  exists av, ar.
  split; [apply (n_word_agree m); [exact H1 | intros k Hk; apply HA; lia]|].
  split; [intros k Hk; apply (n_word_agree m); [exact (H2 k Hk) | intros j Hj; apply HA; lia]|].
  split; [apply (n_word_agree m); [exact H3 | intros j Hj; apply HA; lia]|].
  split; [apply (n_word_agree m); [exact H4 | intros j Hj; apply HA; lia]|].
  repeat split; assumption.
Qed.

Lemma n_notE_high : forall x, alloc_ceiling <= x -> ~ (v <= x < v + 56) -> ~ E x.
Proof.
  intros x Hx Hv (_ & [Hw|[Hw|Hw]]).
  - exact (Hv Hw).
  - pose proof (n_blk_set_low x Hw). lia.
  - pose proof (pf_img_bound B n_seg x (pf_statics_img B n_seg x Hw)). pose proof n_ceil. lia.
Qed.

Lemma n_errno_low : forall x, errno_addr B <= x < errno_addr B + 4 -> x < 0x55000.
Proof.
  intros x Hx. destruct HENV as (_ & _ & Her & _). rewrite Her in Hx.
  exact (proj2 (pf_img_bound B n_seg x (pf_errno_img B n_seg x Hx))).
Qed.

Lemma n_notscr_high : forall x, sp0 <= x -> ~ scratch_k B K regs0 x.
Proof.
  intros x Hx Hw. unfold scratch_k in Hw. destruct Hw as [Hw|Hw].
  - unfold spZ in *. lia.
  - pose proof (n_errno_low x Hw). pose proof n_sp as (_ & Hs & _). pose proof n_ceil. pose proof n_K as HK0.
    unfold ALLOC_STACK in HK0. lia.
Qed.

Definition Pd (a : Z) (D1 : list (Z * Z)) : Prop := exists d', d = S d' /\ pj_fd segs mem0 (lin Lam0) d' a D1.

Definition FP (ik iy : nat) (Dr : list (Z * Z)) (x : Z) : Prop :=
  (v <= x < v + 56) \/ (ks = true /\ keys + 8 * Z.of_nat iy <= x < keys + 8 * n) \/
  (kids + 56 * Z.of_nat ik <= x < kids + 56 * n) \/ (exists b, In b Dr /\ pj_holds b x).

Definition vplace (Lc : layout) (Ac : astate) : Prop :=
  sp0 <= v \/ exists ra rk, In (ra, rk) (blocks Lc Ac) /\ ~ In (ra + 16, rk - 16) D /\ ra <= v /\ v + 56 <= ra + rk.

Definition frm (memc : word -> option byte) : Prop :=
  exists j, rw_cells rsegs memc (sp0 - 48)
    [CB 8 j; C8 (getr regs0 19); C8 (getr regs0 18); C8 (getr regs0 9); C8 (getr regs0 8); C8 (getr regs0 1)].

Definition cur (ik iy : nat) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
    (Lamc Dfr Dr R : list (Z * Z)) : Prop :=
  rrel Lc Ac memc mdc /\ ledger B Lc Ac memc Lamc peak cnt fail /\
  (exists Df, Permutation Dfr Df /\ rf_ok F Ac (rf_frees F b0 Df)) /\
  MemNorm.ro_agree segs memc /\ Permutation D (Dfr ++ Dr ++ R) /\ Permutation Lamc (Dr ++ R ++ Rest0) /\
  pf_items segs mem0 (lin Lam0) Pd ks (kids + 56 * Z.of_nat ik) (keys + 8 * Z.of_nat ik) (Z.to_nat n - ik) Dr /\
  (forall x, FP ik iy Dr x -> mbyte segs memc x = mbyte segs mem0 x /\ (writable_at segs mem0 x <-> writable_at segs memc x)) /\
  frm memc /\ vplace Lc Ac.

Lemma n_auxv_call : forall ik iy Lc Ac memc mdc Lamc Dfr Dr R, cur ik iy Lc Ac memc mdc Lamc Dfr Dr R ->
  st_init_done Ac = false -> auxv_pre B (ly_sec Lc) (sp0 - 48) memc.
Proof.
  intros ik iy Lc Ac memc mdc Lamc Dfr Dr R (HR & _ & _ & _ & _ & _ & _ & HA & _) Hf.
  pose proof HR as (HM & _ & _ & HL & HI & _ & _ & _ & HH & _ & _ & _ & HAV).
  assert (Hf0 : st_init_done A0 = false) by (destruct (st_init_done A0) eqn:E0; [rewrite (HI eq_refl) in Hf; discriminate | reflexivity]).
  destruct n_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Haux). specialize (Haux Hf0).
  destruct HL as (_ & Hsec & _). rewrite Hsec.
  apply (auxv_pre_mono B (ly_sec L0) sp0 (sp0 - 48) memc); [lia|].
  apply (n_auxv_agree (ly_sec L0) sp0 mem0 memc Haux).
  pose proof n_sp as (_ & Hsp & Hsp2). pose proof n_ceil as Hc. pose proof n_v as (Hv1 & Hv2 & _).
  intros x [Hx|Hx].
  - pose proof (HAV Hf (x - (ms_libc B + 8)) ltac:(lia)) as Hq. replace (ms_libc B + 8 + (x - (ms_libc B + 8))) with x in Hq by lia.
    exact Hq.
  - assert (Hv : v <= x < v + 56 \/ ~ (v <= x < v + 56)) by lia. destruct Hv as [Hv|Hv].
    + exact (proj1 (HA x (or_introl Hv))).
    + pose proof n_K as HK0. unfold ALLOC_STACK in HK0.
      assert (Hxa : alloc_ceiling <= x < 2 ^ 64) by lia.
      exact (proj1 (HH x Hxa (n_notscr_high x (proj1 Hx)) (n_notE_high x (proj1 Hxa) Hv))).
Qed.

Lemma pf_perm_mv : forall (X Y C : list (Z * Z)) x, Permutation (X ++ Y ++ x :: C) ((X ++ [x]) ++ Y ++ C).
Proof.
  intros X Y C x. rewrite <- app_assoc. apply Permutation_app_head. cbn. symmetry. apply Permutation_middle.
Qed.

Lemma pf_nodup_notin : forall (X Y C : list (Z * Z)) x y, List.NoDup (X ++ Y ++ x :: C) -> In y (Y ++ C) -> y <> x.
Proof.
  intros X Y C x y HN Hy ->. rewrite app_assoc in HN. apply NoDup_remove_2 in HN. apply HN.
  rewrite <- app_assoc. apply in_or_app. right. exact Hy.
Qed.

Lemma pf_blk_survive : forall (l b1 b2 : list (Z * Z)) R Fz, In R (b1 ++ Fz :: b2) -> R <> Fz -> In R (b1 ++ b2).
Proof.
  intros l b1 b2 R Fz H Hne. apply in_app_or in H. apply in_or_app.
  destruct H as [H|[H|H]]; [left; exact H | congruence | right; exact H].
Qed.

Lemma n_D_nodup : forall X, Permutation D X -> List.NoDup X.
Proof. intros X HX. apply (Permutation_NoDup HX). apply NoDup_ListNoDup. exact HND. Qed.

Lemma T_ff : forall ik iy iy' Lc Ac memc mdc Lamc Dfr Dr R1 R2 regs_c p k ret,
  cur ik iy Lc Ac memc mdc Lamc Dfr Dr (R1 ++ R2) ->
  (p = 0 /\ k = 0 /\ R1 = [] \/ p <> 0 /\ R1 = [(p, k)]) ->
  (forall x, FP ik iy' Dr x -> FP ik iy Dr x) ->
  (forall x, FP ik iy' Dr x -> v <= x < v + 56 \/ exists a b, In (a, b) (Dr ++ R2) /\ a <= x < a + b) ->
  getr regs_c 10 = Z_to_bv 64 p -> getr regs_c 1 = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
  getr regs_c 2 = Z_to_bv 64 (sp0 - 48) -> getr regs_c 4 = getr regs0 4 ->
  SR segs (mkCfg (mkst regs_c (Z_to_bv 64 FUZZ_FREE) memc (seg_rom segs)) mdc)
    (fun c' => exists L' A' regs' mem' md' Lam',
       c' = mkCfg (mkst regs' (Z_to_bv 64 ret) mem' (seg_rom segs)) md' /\ regs_preserved regs_c regs' /\
       cur ik iy' L' A' mem' md' Lam' (Dfr ++ R1) Dr R2).
Proof.
  intros ik iy iy' Lc Ac memc mdc Lamc Dfr Dr R1 R2 regs_c p k ret Hc Hp1 HFP HFPin H10 H1 Hret Hret2 H2 H4.
  pose proof Hc as (HR & HLc & HRc0 & HRO & HPD & HPm & HIt & HA & HFr & HVp).
  destruct HRc0 as (Df & HDf & HRc).
  pose proof HR as (HM & HW & HB & HL & HI & HLn & Hk & Hmd & HH & HG & HU & HSW & HAV).
  pose proof n_sp as (Hal & Hsp0 & Hsp2). pose proof n_ceil as Hc0. pose proof n_K as HK0. unfold ALLOC_STACK in HK0.
  assert (Hsp : spZ regs_c = sp0 - 48) by (unfold spZ at 1; rewrite H2; apply unsigned_lit; lia).
  assert (Hpre : call_pre_k B MR ALLOC_STACK Lc Ac regs_c memc mdc).
  { destruct n_pre as (_ & _ & _ & _ & _ & _ & _ & _ & Htp & _).
    split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [rewrite H1; apply pf_ret_ok; assumption|].
    rewrite Hsp. unfold ALLOC_STACK. split; [lia|]. split; [lia|]. split; [lia|].
    split; [intros a Ha; apply HSW; left; lia|]. split; [rewrite H4; exact Htp|].
    split; [intros a Ha; apply HSW; right; exact Ha|].
    intros Hf. exact (n_auxv_call ik iy Lc Ac memc mdc Lamc Dfr Dr _ Hc Hf). }
  assert (HinL : p = 0 /\ k = 0 \/ In (p, k) Lamc).
  { destruct Hp1 as [(-> & -> & _)|(_ & ->)]; [left; split; reflexivity|right].
    apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
  eapply SR_mono; [exact (FF Lc Ac regs_c memc mdc p k (rf_frees F b0 Df) Lamc peak cnt fail Hpre H10 HLc HRO HinL HRc)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & HRO' & _ & HIn' & _ & Hpost & HLen' & Hkeeps & Hkept & Harm).
  rewrite H1.
  destruct Harm as [(Hp0 & -> & -> & -> & -> & -> & _ & _ & _)|(Hp0 & (b1 & b2 & Eb & Eb') & (l1 & l2 & El & HL') & HR')].
  - destruct Hp1 as [(_ & _ & ->)|(Hp1 & _)]; [|contradiction].
    exists Lc, Ac, regs_c, memc, mdc, Lamc. split; [reflexivity|]. split; [intros r _; reflexivity|].
    rewrite app_nil_r. cbn [app] in HPD, HPm, HFPin.
    split; [exact HR|]. split; [exact HLc|]. split; [exists Df; split; [exact HDf | exact HRc]|].
    split; [exact HRO|]. split; [exact HPD|].
    split; [exact HPm|]. split; [exact HIt|]. split; [intros x Hx; exact (HA x (HFP x Hx))|].
    split; [exact HFr | exact HVp].
  - destruct Hp1 as [(Hp1 & _)|(_ & ->)]; [contradiction|].
    pose proof Hpost as (HM' & HW' & HB' & HLay' & HPA' & HRP' & Hmd' & HF' & HUB' & HSW').
    assert (HpD : In (p, k) D).
    { apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
    assert (HpL : In (p, k) Lamc) by (destruct HinL as [(E1 & _)|H0]; [contradiction | exact H0]).
    destruct (pf_lraw B Lc Ac memc Lamc peak cnt fail p k HLc HpL) as (Hk0 & Hraw).
    destruct (pf_blk_range B API Lc Ac memc mdc _ _ HM Hraw) as (Hr1 & Hr2).
    assert (HGL : G_LIVE + 8 <= alloc_ceiling) by (unfold G_LIVE; lia).
    assert (HKS : forall x, sp0 - 48 <= x -> ~ scratch_k B ALLOC_STACK regs_c x).
    { intros x Hx Hw. unfold scratch_k in Hw. rewrite Hsp in Hw. destruct Hw as [Hw|Hw]; [lia|].
      pose proof (n_errno_low x Hw). lia. }
    assert (Hhigh : forall x, sp0 - 48 <= x < 2 ^ 64 ->
      mbyte segs mem' x = mbyte segs memc x /\ (writable_at segs memc x <-> writable_at segs mem' x)).
    { intros x Hx.
      assert (Ho : ~ owned B Lc Ac x) by (intro Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho); lia).
      assert (Ho' : ~ owned B L' A' x) by (intro Ho'; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho'); lia).
      assert (Hxa : alloc_ceiling <= x < 2 ^ 64) by lia.
      apply (HF' x (or_introl Hxa) Ho Ho' (HKS x (proj1 Hx))). intros [Hw|(_ & Hw)]; lia. }
    assert (Hsurv : forall R, In R (blocks Lc Ac) -> R <> (p - 16, k + 16) -> In R (blocks L' A')).
    { intros R HRin Hne. rewrite Eb'. rewrite Eb in HRin. exact (pf_blk_survive [] b1 b2 R _ HRin Hne). }
    assert (Hkeep : forall ra rk x, In (ra, rk) (blocks Lc Ac) -> (ra, rk) <> (p - 16, k + 16) -> 0 < rk ->
      ra <= x < ra + rk -> mbyte segs mem' x = mbyte segs memc x /\ (writable_at segs memc x <-> writable_at segs mem' x)).
    { intros ra rk x HRin Hne Hrk Hx.
      assert (Hra : ra <> p - 16).
      { intro Ea. destruct (pf_blocks_disj B API Lc Ac memc mdc ra rk (p - 16) (k + 16) HM HRin Hraw Hne Hrk ltac:(lia)); lia. }
      split.
      - pose proof (Hkeeps ra rk (x - ra) HRin Hra ltac:(lia)) as Hq. replace (ra + (x - ra)) with x in Hq by lia. exact Hq.
      - pose proof (Hsurv _ HRin Hne) as HRin'.
        destruct (pf_blk_present B API Lc Ac memc mdc ra rk (x - ra) HM HRin ltac:(lia)) as (Pr & _).
        destruct (pf_blk_present B API L' A' mem' md' ra rk (x - ra) HM' HRin' ltac:(lia)) as (Pr' & _).
        replace (ra + (x - ra)) with x in Pr, Pr' by lia.
        split; intros _; apply pf_present_wr; assumption. }
    assert (HnD := n_D_nodup _ HPD).
    exists L', A', regs', mem', md', (l1 ++ l2). split; [reflexivity|]. split; [exact HRP'|].
    split; [exact (rrel_ff Lc Ac memc mdc Lamc regs_c p k L' A' regs' mem' md' HR HLc HpD HpL Hsp Hpost HIn' HLen' Hkept)|].
    split; [exact HL'|].
    split; [exists (Df ++ [(p, k)]); split; [apply Permutation_app_tail; exact HDf | rewrite rf_frees_app; exact HR']|].
    split; [exact HRO'|].
    split; [exact (Permutation_trans HPD (pf_perm_mv Dfr Dr R2 (p, k)))|].
    split.
    { rewrite El in HPm. cbn [app] in HPm.
      exact (Permutation_app_inv l1 l2 Dr (R2 ++ Rest0) (p, k) HPm). }
    split; [exact HIt|].
    split.
    { intros x Hx. destruct (HA x (HFP x Hx)) as [E1 E2].
      assert (HP2 : mbyte segs mem' x = mbyte segs memc x /\ (writable_at segs memc x <-> writable_at segs mem' x)).
      { destruct (HFPin x Hx) as [Hv|(a & b & Hab & Hx')].
        - destruct HVp as [Hst|(ra & rk & Hb & Hn & Hr3 & Hr4)].
          + pose proof n_v. apply Hhigh. lia.
          + apply (Hkeep ra rk x Hb); [|lia|lia]. intro Eq. injection Eq as Ea Ek. apply Hn.
            replace (ra + 16) with p by lia. replace (rk - 16) with k by lia. exact HpD.
        - assert (HabL : In (a, b) Lamc).
          { apply (Permutation_in _ (Permutation_sym HPm)). apply in_app_or in Hab. apply in_or_app.
            destruct Hab as [Hab|Hab]; [left; exact Hab | right; apply in_or_app; left; apply in_or_app; right; exact Hab]. }
          assert (Hne : (a, b) <> (p, k)) by exact (pf_nodup_notin Dfr Dr R2 (p, k) (a, b) HnD Hab).
          destruct (pf_lraw B Lc Ac memc Lamc peak cnt fail a b HLc HabL) as (Hb0 & Hraw2).
          apply (Hkeep (a - 16) (b + 16) x Hraw2); [|lia|lia]. intro Eq. injection Eq as Ea Eb2.
          apply Hne. f_equal; [lia|]. assert (a = p) by lia. subst a. exact (pf_lfst B Lc Ac memc Lamc peak cnt fail p b k HLc HabL HpL). }
      destruct HP2 as [F1 F2]. split; [rewrite F1; exact E1 | tauto]. }
    split.
    { destruct HFr as (j & Hj). exists j. apply (pf_cells_agree rsegs memc mem' _ _ Hj). intros x Hx.
      cbn [cells_size csize Nat.add] in Hx. rewrite <- n_seg. apply Hhigh. lia. }
    destruct HVp as [Hst|(ra & rk & Hb & Hn & Hr3 & Hr4)]; [left; exact Hst|right].
    exists ra, rk. split; [|split; [exact Hn | split; assumption]].
    apply Hsurv; [exact Hb|]. intro Eq. injection Eq as Ea Ek. apply Hn.
    replace (ra + 16) with p by lia. replace (rk - 16) with k by lia. exact HpD.
Qed.

Local Notation R0 := (Dk ++ Dy ++ Ds).

Lemma pf_nodup_disj : forall (X Y W : list (Z * Z)) a, List.NoDup (X ++ Y ++ W) -> In a Y -> In a W -> False.
Proof.
  intros X Y W a H. apply NoDup_app_remove_l in H. revert H.
  induction Y as [|y Y IHy]; intros H Hy Hz; [destruct Hy|].
  cbn in H. inversion H as [|? ? Hn H']; subst. destruct Hy as [<-|Hy].
  - apply Hn. apply in_or_app. right. exact Hz.
  - exact (IHy H' Hy Hz).
Qed.

Lemma pf_perm_child : forall (Fl X Y W R : list (Z * Z)), Permutation (Fl ++ (X ++ Y ++ W) ++ R) ((Fl ++ Y) ++ W ++ X ++ R).
Proof.
  intros Fl X Y W R. rewrite <- !app_assoc. apply Permutation_app_head.
  rewrite !(app_assoc Y W). apply Permutation_app_swap_app.
Qed.

Lemma pf_perm_lam : forall (L Lm X Y W R T : list (Z * Z)), Permutation L ((X ++ Y ++ W) ++ R ++ T) ->
  Permutation L (Y ++ Lm) -> Permutation Lm (W ++ (X ++ R) ++ T).
Proof.
  intros L Lm X Y W R T H1 H2. pose proof (Permutation_trans (Permutation_sym H2) H1) as H3.
  apply (Permutation_app_inv_l Y). eapply Permutation_trans; [exact H3|].
  rewrite <- !app_assoc. rewrite !(app_assoc Y W). apply Permutation_app_swap_app.
Qed.

Lemma rp_keep_high : forall K' Lc Ac regs_c memc mdc (Ec : Z -> Prop) gone L' A' regs' mem' md' x,
  rpost B API K' Lc Ac regs_c memc mdc Ec gone L' A' regs' mem' md' ->
  alloc_ceiling <= x < 2 ^ 64 -> ~ scratch_k B K' regs_c x -> ~ Ec x ->
  mbyte segs mem' x = mbyte segs memc x /\ (writable_at segs memc x <-> writable_at segs mem' x).
Proof.
  intros K' Lc Ac regs_c memc mdc Ec gone L' A' regs' mem' md' x Hrp Hx Hs He.
  pose proof Hrp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _). exact (HF x Hx Hs He).
Qed.

Lemma rp_keep_blk : forall K' Lc Ac regs_c memc mdc (Ec : Z -> Prop) D1 L' A' regs' mem' md' ra rk x,
  rpost B API K' Lc Ac regs_c memc mdc Ec (freed D1) L' A' regs' mem' md' ->
  MR Lc Ac memc mdc -> In (ra, rk) (blocks Lc Ac) -> ~ In (ra + 16, rk - 16) D1 -> ra <= x < ra + rk -> ~ Ec x ->
  mbyte segs mem' x = mbyte segs memc x /\ (writable_at segs memc x <-> writable_at segs mem' x).
Proof.
  intros K' Lc Ac regs_c memc mdc Ec D1 L' A' regs' mem' md' ra rk x Hrp HM Hin Hn Hx He.
  pose proof Hrp as (HM' & _ & _ & _ & _ & _ & _ & Hk' & HPA & _ & _ & _ & _ & HUB & _).
  destruct (pf_blk_user _ _ _ _ Hin) as (q & Hq & Eq).
  assert (Hq' : In (q, rk) (user_blocks A')) by (apply Hk'; [exact Hq | unfold freed; rewrite Eq; exact Hn]).
  assert (Hxe : ptr_addr Lc q + (x - ra) = x) by lia.
  split.
  - rewrite <- Hxe. apply (HUB q rk (x - ra) Hq Hq'); [lia | rewrite Hxe; exact He].
  - destruct (pf_blk_present B API Lc Ac memc mdc ra rk (x - ra) HM Hin ltac:(lia)) as (P1 & _).
    assert (Hin' : In (ra, rk) (blocks L' A')).
    { unfold blocks. apply in_map_iff. exists (q, rk). cbn [fst snd]. rewrite (HPA q rk Hq Hq'), Eq.
      split; [reflexivity | exact Hq']. }
    destruct (pf_blk_present B API L' A' mem' md' ra rk (x - ra) HM' Hin' ltac:(lia)) as (P2 & _).
    replace (ra + (x - ra)) with x in P1, P2 by lia.
    split; intros _; apply pf_present_wr; assumption.
Qed.

Lemma n_lam_disj : forall Lc Ac memc mdc Lamc a k a' k' x, MR Lc Ac memc mdc ->
  ledger B Lc Ac memc Lamc peak cnt fail -> In (a, k) Lamc -> In (a', k') Lamc -> (a, k) <> (a', k') ->
  a - 16 <= x < a + k -> a' - 16 <= x < a' + k' -> False.
Proof.
  intros Lc Ac memc mdc Lamc a k a' k' x HM HL H1 H2 Hne Hx Hx'.
  destruct (pf_lraw B Lc Ac memc Lamc peak cnt fail a k HL H1) as (Hk & Hr).
  destruct (pf_lraw B Lc Ac memc Lamc peak cnt fail a' k' HL H2) as (Hk' & Hr').
  assert (Hne' : (a - 16, k + 16) <> (a' - 16, k' + 16)).
  { intro Eq. injection Eq as E1 E2. apply Hne. assert (a = a') by lia. subst a'.
    f_equal. exact (pf_lfst B Lc Ac memc Lamc peak cnt fail a k k' HL H1 H2). }
  destruct (pf_blocks_disj B API Lc Ac memc mdc _ _ _ _ HM Hr Hr' Hne' ltac:(lia) ltac:(lia)); lia.
Qed.

Lemma n_ckeep : forall Lc Ac memc mdc Lamc regs_c d' c D1 L' A' regs' mem' md' a k x,
  MR Lc Ac memc mdc -> ledger B Lc Ac memc Lamc peak cnt fail -> (forall bb, In bb D1 -> In bb Lamc) ->
  In (a, k) Lamc -> ~ In (a, k) D1 -> a <= x < a + k -> ~ (c <= x < c + 56) ->
  rpost B API (PJ_FREE_K d') Lc Ac regs_c memc mdc (pj_free_writes c D1) (freed D1) L' A' regs' mem' md' ->
  mbyte segs mem' x = mbyte segs memc x /\ (writable_at segs memc x <-> writable_at segs mem' x).
Proof.
  intros Lc Ac memc mdc Lamc regs_c d' c D1 L' A' regs' mem' md' a k x HM HL HD1 Hin Hn Hx Hc Hrp.
  destruct (pf_lraw B Lc Ac memc Lamc peak cnt fail a k HL Hin) as (Hk & Hraw).
  apply (rp_keep_blk (PJ_FREE_K d') Lc Ac regs_c memc mdc _ D1 L' A' regs' mem' md' (a - 16) (k + 16) x Hrp HM Hraw).
  - replace (a - 16 + 16) with a by lia. replace (k + 16 - 16) with k by lia. exact Hn.
  - lia.
  - intros (_ & [Hw|[(a1 & k1 & Hin1 & Hw)|Hw]]).
    + exact (Hc Hw).
    + apply (n_lam_disj Lc Ac memc mdc Lamc a k a1 k1 x HM HL Hin (HD1 _ Hin1)); [|lia|lia].
      intro E1. apply Hn. rewrite E1. exact Hin1.
    + apply (ledger_block_not_img B Lc Ac memc Lamc peak cnt fail a k (x - a) HL Hin ltac:(lia)).
      replace (a + (x - a)) with x by lia. exact (pf_statics_img B n_seg x Hw).
Qed.

Lemma n_v_heads : forall a k x, In (a, k) Lam0 -> a - 16 <= x < a -> ~ (v <= x < v + 56).
Proof.
  intros a k x Hin Hx Hv. destruct n_MR0 as (HM & _).
  destruct (pf_lraw B L0 A0 mem0 Lam0 peak cnt fail a k HLED Hin) as (Hk & Hraw).
  destruct (pf_blk_range B API L0 A0 mem0 md0 _ _ HM Hraw) as (Hr1 & Hr2).
  pose proof n_sp as (_ & Hs & _). pose proof n_K as HK0. unfold ALLOC_STACK in HK0.
  destruct HPL as (Hpl & _ & _). destruct Hpl as [(H1 & _)|[(ra & rk & Hb & Hn & H1 & H2)|(a' & k' & Hl & H1 & H2)]].
  - lia.
  - assert (Hne : (ra, rk) <> (a - 16, k + 16)).
    { intro Eq. injection Eq as E1 E2. apply Hn. unfold lin. replace (ra + 16) with a by lia.
      replace (rk - 16) with k by lia. exact Hin. }
    destruct (pf_blocks_disj B API L0 A0 mem0 md0 _ _ _ _ HM Hb Hraw Hne ltac:(lia) ltac:(lia)); lia.
  - destruct (Z.eq_dec a' a) as [->|Ha]; [lia|].
    apply (n_lam_disj L0 A0 mem0 md0 Lam0 a k a' k' x HM HLED Hin Hl); [intro Eq; injection Eq as E1; lia | lia | lia].
Qed.

Lemma n_v_notEc : forall c D1 x, (forall bb, In bb D1 -> In bb D) ->
  (exists a k, In (a, k) D /\ a <= c /\ c + 56 <= a + k) -> v <= x < v + 56 -> ~ pj_free_writes c D1 x.
Proof.
  intros c D1 x HD1 (a & k & Hin & H1 & H2) Hx (_ & [Hw|[(a1 & k1 & Hin1 & Hw)|Hw]]).
  - apply (HAP (a, k) x Hin); [unfold pj_holds; cbn; lia | exact Hx].
  - destruct (Z_lt_le_dec x a1) as [Hl|Hl].
    + exact (n_v_heads a1 k1 x (n_Dsub _ (HD1 _ Hin1)) ltac:(lia) Hx).
    + apply (HAP (a1, k1) x (HD1 _ Hin1)); [unfold pj_holds; cbn; lia | exact Hx].
  - destruct HPL as (_ & _ & Hb). destruct (Hb (x - v) ltac:(lia)) as (_ & Hs & _).
    apply Hs. replace (v + (x - v)) with x by lia. exact Hw.
Qed.

Lemma n_kids_blk : 0 < n -> exists kk, In (kids, kk) Lam0 /\ 56 * n <= kk /\ Dk = [(kids, kk)].
Proof. intros Hn. destruct HK as [(_ & E & _)|(kk & H1 & H2 & H3)]; [lia|]. exists kk. auto. Qed.

Lemma T_child : forall i Lc Ac memc mdc Lamc Dfr Dk1 D1 D2 regs_c d',
  cur i i Lc Ac memc mdc Lamc Dfr (Dk1 ++ D1 ++ D2) R0 ->
  (i < Z.to_nat n)%nat -> d = S d' -> pj_fd segs mem0 (lin Lam0) d' (kids + 56 * Z.of_nat i) D1 ->
  pf_items segs mem0 (lin Lam0) Pd ks (kids + 56 * Z.of_nat (S i)) (keys + 8 * Z.of_nat (S i)) (Z.to_nat n - S i) D2 ->
  getr regs_c 10 = Z_to_bv 64 (kids + 56 * Z.of_nat i) -> getr regs_c 1 = Z_to_bv 64 0x145e4 ->
  getr regs_c 2 = Z_to_bv 64 (sp0 - 48) -> getr regs_c 4 = getr regs0 4 ->
  SR segs (mkCfg (mkst regs_c (Z_to_bv 64 PJ_FREE) memc (seg_rom segs)) mdc)
    (fun c' => exists L' A' regs' mem' md' Lam',
       c' = mkCfg (mkst regs' (Z_to_bv 64 0x145e4) mem' (seg_rom segs)) md' /\ regs_preserved regs_c regs' /\
       cur (S i) i L' A' mem' md' Lam' (Dfr ++ D1) D2 (Dk1 ++ R0)).
Proof.
  intros i Lc Ac memc mdc Lamc Dfr Dk1 D1 D2 regs_c d' Hc Hi Hd HD1 HI2 H10 H1 H2 H4.
  pose proof Hc as (HR & HLc & HRc0 & HRO & HPD & HPm & _ & HA & HFr & HVp).
  destruct HRc0 as (Df & HDf & HRc).
  pose proof HR as (HM & HW & HB & HL & HI & HLn & Hk & Hmd & HH & HG & HU & HSW & HAV).
  pose proof n_sp as (Hal & Hsp0 & Hsp2). pose proof n_ceil as Hc0. pose proof n_K as HK0. unfold ALLOC_STACK in HK0.
  assert (HKd : PJ_FREE_K d = PJ_FREE_K d' + 48) by (rewrite Hd; unfold PJ_FREE_K, PJ_FREE_F; lia).
  assert (Hsp : spZ regs_c = sp0 - 48) by (unfold spZ at 1; rewrite H2; apply unsigned_lit; lia).
  assert (Hn0 : 0 < n /\ Z.of_nat i < n) by lia.
  destruct (n_kids_blk (proj1 Hn0)) as (kk & Hkk & Hkn & EDk).
  assert (HkR : In (kids, kk) R0) by (apply in_or_app; left; rewrite EDk; left; reflexivity).
  assert (HkL : In (kids, kk) Lamc).
  { apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. right. apply in_or_app. left. exact HkR. }
  assert (HkD : In (kids, kk) D).
  { apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. apply in_or_app. right. exact HkR. }
  destruct (pf_lraw B Lc Ac memc Lamc peak cnt fail kids kk HLc HkL) as (Hkk0 & Hkraw).
  destruct (pf_blk_range B API Lc Ac memc mdc _ _ HM Hkraw) as (Hkr1 & Hkr2).
  assert (HDrL : forall bb, In bb (Dk1 ++ D1 ++ D2) -> In bb Lamc).
  { intros bb Hb. apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. left. exact Hb. }
  assert (HD1r : forall bb, In bb D1 -> In bb (Dk1 ++ D1 ++ D2)).
  { intros bb Hb. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (HD1D : forall bb, In bb D1 -> In bb D).
  { intros bb Hb. apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. apply in_or_app. left.
    apply HD1r. exact Hb. }
  assert (HDn := n_D_nodup _ HPD).
  assert (HDrn : List.NoDup (Dk1 ++ D1 ++ D2)).
  { apply NoDup_app_remove_l in HDn. apply NoDup_app_remove_r in HDn. exact HDn. }
  set (c := kids + 56 * Z.of_nat i) in *.
  assert (Hc1 : kids <= c /\ c + 56 <= kids + kk) by (unfold c; lia).
  assert (Henv : reader_env B API (PJ_FREE_K d') Lc Ac regs_c memc mdc).
  { destruct HENV as (E1 & E2 & E3 & E4 & E5 & Hpre0 & E7 & E8 & E9 & _).
    destruct Hpre0 as (_ & _ & _ & _ & _ & _ & _ & _ & Htp & _).
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    split.
    { split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [rewrite H1; apply pf_ret_ok; lia|].
      rewrite Hsp. split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros a Ha; apply HSW; left; lia|]. split; [rewrite H4; exact Htp|].
      split; [intros a Ha; apply HSW; right; exact Ha|].
      intros Hf. exact (n_auxv_call i i Lc Ac memc mdc Lamc Dfr _ _ Hc Hf). }
    rewrite Hsp. split; [lia|]. split; [lia|]. split; [exact E9|].
    split; [exact HRO|].
    destruct (ax_statics AX Lc Ac memc mdc HM) as (Hg1 & (g & _ & Hg2) & _).
    split; [exact Hg1 | exists g; exact Hg2]. }
  assert (Hfd : pj_fd segs memc (lin Lamc) d' c D1).
  { apply (pf_fd_frame segs d' mem0 (lin Lam0) memc (lin Lamc) c D1 HD1).
    - intros a k Hin. apply HDrL. apply HD1r. exact Hin.
    - intros x Hx. apply HA. destruct Hx as [Hx|(bb & Hbb & Hx)].
      + right. right. left. unfold c in Hx. lia.
      + right. right. right. exists bb. split; [apply HD1r; exact Hbb | exact Hx]. }
  assert (Hpl : rplace B Lc Ac Lamc regs_c memc c).
  { split; [|split].
    - right. right. exists kids, kk. split; [exact HkL | lia].
    - rewrite Hsp. intros Hx. exfalso. lia.
    - intros j Hj.
      assert (Hni : ~ in_img B (c + j)).
      { replace (c + j) with (kids + (c + j - kids)) by lia.
        apply (ledger_block_not_img B Lc Ac memc Lamc peak cnt fail kids kk); [exact HLc | exact HkL | lia]. }
      split; [|split; [|split; [|exact Hni]]].
      + assert (Hj2 : 0 <= c + j - (kids - 16) < kk + 16) by lia.
        replace (c + j) with (kids - 16 + (c + j - (kids - 16))) by lia.
        exact (proj2 (pf_blk_present B API Lc Ac memc mdc _ _ _ HM Hkraw Hj2)).
      + intro Hs. exact (Hni (pf_statics_img B n_seg _ Hs)).
      + intro Hs. destruct HENV as (_ & _ & Her & _). rewrite Her in Hs. exact (Hni (pf_errno_img B n_seg _ Hs)). }
  assert (Hdj : Frame.disjoint_from [(c, c + 56)] (spZ regs_c - PJ_FREE_K d') (PJ_FREE_K d')).
  { cbn. split; [right; rewrite Hsp; lia | exact I]. }
  assert (Hc0' : c <> 0) by lia.
  eapply SR_bind.
  { exact (IH d' Hd Lc Ac regs_c memc mdc Lamc peak cnt fail (rf_frees F b0 Df) c D1 Henv HLc HRc H10
      (or_intror (conj Hc0' (conj Hfd (conj Hpl Hdj))))). }
  intros c' (L' & A' & regs' & mem' & md' & Lam' & -> & Hrp & Hrd & HPl & HL' & (D1' & HD1' & HR') & _ & Hz).
  apply SR_ret.
  exists L', A', regs', mem', md', Lam'. rewrite H1. split; [reflexivity|].
  pose proof Hrp as (HM' & _ & _ & _ & _ & _ & _ & Hk' & HPA & HRP & _).
  split; [exact HRP|].
  assert (Hrr : rrel L' A' mem' md').
  { apply (rrel_child Lc Ac memc mdc regs_c d' c D1 L' A' regs' mem' md' HR Hd Hsp); [exact HD1D | exact Hc0' | | exact Hrp].
    intros x Hx. exists kids, kk. split; [exact HkD | lia]. }
  assert (HnR : forall bb, In bb (Dk1 ++ D1 ++ D2) -> In bb R0 -> False).
  { intros bb H5 H6. exact (pf_nodup_disj Dfr _ R0 bb HDn H5 H6). }
  assert (HFPs : forall x, FP (S i) i D2 x -> FP i i (Dk1 ++ D1 ++ D2) x).
  { intros x [Hx|[Hx|[Hx|(bb & Hbb & Hx)]]]; [left; exact Hx | right; left; exact Hx | right; right; left; lia |].
    right. right. right. exists bb. split; [apply in_or_app; right; apply in_or_app; right; exact Hbb | exact Hx]. }
  assert (Hnscr : forall x, sp0 - 48 <= x -> ~ scratch_k B (PJ_FREE_K d') regs_c x).
  { intros x Hx Hw. unfold scratch_k in Hw. rewrite Hsp in Hw. destruct Hw as [Hw|Hw]; [lia|].
    pose proof (n_errno_low x Hw). lia. }
  assert (Hagr : forall x, FP (S i) i D2 x ->
    mbyte segs mem' x = mbyte segs memc x /\ (writable_at segs memc x <-> writable_at segs mem' x)).
  { intros x Hx. destruct Hx as [Hx|[(Hks & Hx)|[Hx|(bb & Hbb & Hx)]]].
    - assert (HnE : ~ pj_free_writes c D1 x).
      { apply (n_v_notEc c D1 x HD1D); [exists kids, kk; split; [exact HkD | lia] | exact Hx]. }
      destruct HVp as [Hst|(ra & rk & Hb & Hnr & Hr3 & Hr4)].
      + pose proof n_v as (Hv1 & Hv2 & _). assert (Hxa : alloc_ceiling <= x < 2 ^ 64) by lia.
        exact (rp_keep_high _ _ _ _ _ _ _ _ _ _ _ _ _ x Hrp Hxa (Hnscr x ltac:(lia)) HnE).
      + apply (rp_keep_blk _ _ _ _ _ _ _ D1 _ _ _ _ _ ra rk x Hrp HM Hb); [intro Hin; apply Hnr; apply HD1D; exact Hin | lia | exact HnE].
    - destruct HY as [(_ & Hf & _)|(_ & ky & Hky & Hkyn & EDy)]; [congruence|].
      assert (HyR : In (keys, ky) R0) by (apply in_or_app; right; apply in_or_app; left; rewrite EDy; left; reflexivity).
      assert (HyL : In (keys, ky) Lamc).
      { apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. right. apply in_or_app. left. exact HyR. }
      apply (n_ckeep Lc Ac memc mdc Lamc regs_c d' c D1 L' A' regs' mem' md' keys ky x HM HLc);
        [intros bb Hbb; apply HDrL; apply HD1r; exact Hbb | exact HyL | intro Hin; exact (HnR _ (HD1r _ Hin) HyR) | lia | | exact Hrp].
      intro Hcx. apply (n_lam_disj Lc Ac memc mdc Lamc keys ky kids kk x HM HLc HyL HkL); [|lia|lia].
      intro Eq. pose proof HDn as HDn2. rewrite app_assoc in HDn2.
      apply (pf_nodup_disj (Dfr ++ (Dk1 ++ D1 ++ D2)) Dk (Dy ++ Ds) (kids, kk) HDn2); [rewrite EDk; left; reflexivity|].
      rewrite <- Eq. apply in_or_app. left. rewrite EDy. left. reflexivity.
    - apply (n_ckeep Lc Ac memc mdc Lamc regs_c d' c D1 L' A' regs' mem' md' kids kk x HM HLc);
        [intros bb Hbb; apply HDrL; apply HD1r; exact Hbb | exact HkL | intro Hin; exact (HnR _ (HD1r _ Hin) HkR) | lia | unfold c; lia | exact Hrp].
    - destruct bb as [a k]. unfold pj_holds in Hx. cbn [fst snd] in Hx.
      assert (HaDr : In (a, k) (Dk1 ++ D1 ++ D2)) by (apply in_or_app; right; apply in_or_app; right; exact Hbb).
      apply (n_ckeep Lc Ac memc mdc Lamc regs_c d' c D1 L' A' regs' mem' md' a k x HM HLc);
        [intros bb Hb2; apply HDrL; apply HD1r; exact Hb2 | exact (HDrL _ HaDr) | | lia | | exact Hrp].
      + intro Hin. exact (pf_nodup_disj Dk1 D1 D2 (a, k) HDrn Hin Hbb).
      + intro Hcx. apply (n_lam_disj Lc Ac memc mdc Lamc a k kids kk x HM HLc (HDrL _ HaDr) HkL); [|lia|lia].
        intro Eq. apply (HnR (a, k) HaDr). rewrite Eq. exact HkR. }
  assert (Hfrm : frm mem').
  { destruct HFr as (j & Hj). exists j. apply (pf_cells_agree rsegs memc mem' _ _ Hj). intros x Hx.
    cbn [cells_size csize Nat.add] in Hx. rewrite <- n_seg.
    assert (Hxa : alloc_ceiling <= x < 2 ^ 64) by lia.
    apply (rp_keep_high _ _ _ _ _ _ _ _ _ _ _ _ _ x Hrp Hxa (Hnscr x ltac:(lia))).
    intros (_ & [Hw|[(a1 & k1 & Hin1 & Hw)|Hw]]); [lia | | ].
    - pose proof (n_blk_set_low x (ex_intro _ a1 (ex_intro _ k1 (conj (HD1D _ Hin1) Hw)))). lia.
    - pose proof (pf_img_bound B n_seg x (pf_statics_img B n_seg x Hw)). lia. }
  assert (Hvp : vplace L' A').
  { destruct HVp as [Hst|(ra & rk & Hb & Hnr & Hr3 & Hr4)]; [left; exact Hst|right].
    exists ra, rk. split; [|split; [exact Hnr | split; assumption]].
    destruct (pf_blk_user _ _ _ _ Hb) as (q & Hq & Eq).
    assert (Hq' : In (q, rk) (user_blocks A')).
    { apply Hk'; [exact Hq|]. unfold freed. rewrite Eq. intro Hin. apply Hnr. apply HD1D. exact Hin. }
    unfold blocks. apply in_map_iff. exists (q, rk). cbn [fst snd]. rewrite (HPA q rk Hq Hq'), Eq.
    split; [reflexivity | exact Hq']. }
  split; [exact Hrr|]. split; [exact HL'|].
  split; [exists (Df ++ D1'); split; [exact (Permutation_app HDf HD1') | rewrite rf_frees_app; exact HR']|].
  split; [exact (proj1 Hrd)|].
  split; [exact (Permutation_trans HPD (pf_perm_child Dfr Dk1 D1 D2 R0))|].
  split; [exact (pf_perm_lam Lamc Lam' Dk1 D1 D2 R0 Rest0 HPm HPl)|].
  split; [exact HI2|].
  split; [|split; [exact Hfrm | exact Hvp]].
  intros x Hx. destruct (HA x (HFPs x Hx)) as [E1 E2]. destruct (Hagr x Hx) as [F1 F2].
  split; [rewrite F1; exact E1 | tauto].
Qed.

Lemma n_present_of_mrd : forall m x b, ~ in_img B x -> 0 <= x < 2 ^ 64 -> mrd rsegs m (wa x) = Some b -> present m x.
Proof.
  intros m x b Hn Hx H. unfold mrd in H. destruct (m (wa x)) as [b'|] eqn:E; [exists b'; exact E|].
  exfalso. apply Hn. cbv beta iota delta [lib.Lib.PropExec.seg_rom memory_read] in H.
  match type of H with context [find_segment rsegs ?a ?nn] =>
    assert (Ea : a = x) by (first [apply wa_unsigned | apply unsigned_lit]; lia);
    assert (En : nn = 1) by reflexivity;
    revert H; rewrite Ea, En end.
  destruct (find_segment rsegs x 1) as [sg|] eqn:Fs; intros H; [|discriminate].
  exact (pf_find_img B n_seg x sg Fs).
Qed.

Lemma n_v_inE : forall x, v <= x < v + 56 -> E x.
Proof. intros x Hx. split; [exact HV | left; exact Hx]. Qed.

Lemma n_nown_v : forall Lc Ac memc mdc x, MR Lc Ac memc mdc -> vplace Lc Ac -> v <= x < v + 56 -> ~ owned B Lc Ac x.
Proof.
  intros Lc Ac memc mdc x HM [Hst|(ra & rk & Hb & _ & H1 & H2)] Hx Ho.
  - pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). pose proof n_sp as (_ & Hs & _).
    pose proof n_K as HK0. unfold ALLOC_STACK in HK0. lia.
  - pose proof (pf_blk_present B API Lc Ac memc mdc ra rk (x - ra) HM Hb ltac:(lia)) as (_ & Hn).
    replace (ra + (x - ra)) with x in Hn by lia. exact (Hn Ho).
Qed.

Lemma rrel_final : forall Lc Ac memc mdc mem' regs',
  rrel Lc Ac memc mdc -> vplace Lc Ac -> Frame.munch [(v, v + 56)] memc mem' -> Frame.wmono segs memc mem' ->
  (forall i, 0 <= i < 56 -> present mem' (v + i)) -> regs_preserved regs0 regs' ->
  rpost B API K L0 A0 regs0 mem0 md0 E (freed D) Lc Ac regs' mem' mdc.
Proof.
  intros Lc Ac memc mdc mem' regs' HR HVp Hmu Hwm Hpr Hrp.
  pose proof HR as (HM & HW & HB & HL & HI & HLn & Hk & Hmd & HH & HG & HU & HSW & HAV).
  pose proof n_v as (Hv1 & Hv2 & _). pose proof n_ceil as Hc0.
  assert (Hout : forall x, ~ (v <= x < v + 56) -> 0 <= x < 2 ^ 64 ->
    mbyte segs mem' x = mbyte segs memc x /\ (writable_at segs memc x <-> writable_at segs mem' x)).
  { intros x Hx Hr. assert (Ho : Frame.outside [(v, v + 56)] x) by (apply pf_out1; lia).
    exact (pf_mbyte_munch B _ memc mem' x Hmu Hr Ho). }
  assert (Hpm : forall x, ~ (v <= x < v + 56) -> 0 <= x < 2 ^ 64 -> present memc x -> present mem' x).
  { intros x Hx Hr (bb & Hb). exists bb. rewrite (Hmu (Z_to_bv 64 x)); [exact Hb|].
    rewrite unsigned_lit by exact Hr. apply pf_out1. lia. }
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
  assert (HM' : MR Lc Ac mem' mdc).
  { apply (mr_frame _ _ (aa_laws API) Lc Ac memc mem' mdc mdc HM).
    - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
      assert (Hna : ~ (v <= a < v + 56)) by (intro Hx; exact (n_nown_v Lc Ac memc mdc a HM HVp Hx Ho)).
      assert (Har : 0 <= a < 2 ^ 64) by lia. exact (proj1 (Hout a Hna Har)).
    - intros a Ho Hp. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
      assert (Hna : ~ (v <= a < v + 56)) by (intro Hx; exact (n_nown_v Lc Ac memc mdc a HM HVp Hx Ho)).
      assert (Har : 0 <= a < 2 ^ 64) by lia. exact (Hpm a Hna Har Hp).
    - intros p m i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p m i HM Hin Hi) as (Hp & H1 & H2 & _).
      assert (Har : 0 <= ptr_addr Lc p + i < 2 ^ 64) by lia.
      destruct (Z_lt_le_dec (ptr_addr Lc p + i) v) as [Hlt|Hge];
        [|destruct (Z_lt_le_dec (ptr_addr Lc p + i) (v + 56)) as [Hlt2|Hge2]].
      + assert (Hna : ~ (v <= ptr_addr Lc p + i < v + 56)) by lia. exact (Hpm _ Hna Har Hp).
      + pose proof (Hpr (ptr_addr Lc p + i - v) ltac:(lia)) as P.
        replace (v + (ptr_addr Lc p + i - v)) with (ptr_addr Lc p + i) in P by lia. exact P.
      + assert (Hna : ~ (v <= ptr_addr Lc p + i < v + 56)) by lia. exact (Hpm _ Hna Har Hp).
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HM'|]. split; [exact HW|]. split; [exact HB|]. split; [exact HL|]. split; [exact HI|].
  split.
  { intros Hf i Hi. assert (Hs : static_owned B (ms_libc B + 8 + i)) by (unfold static_owned; right; right; left; lia).
    pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM (or_intror Hs)).
    assert (Hna : ~ (v <= ms_libc B + 8 + i < v + 56)).
    { intro Hx. exact (n_nown_v Lc Ac memc mdc _ HM HVp Hx (or_intror Hs)). }
    assert (Har : 0 <= ms_libc B + 8 + i < 2 ^ 64) by lia.
    rewrite <- (HAV Hf i Hi). exact (proj1 (Hout _ Hna Har)). }
  split; [exact HLn|]. split; [exact Hk|].
  split; [intros p m H1 _; exact (rrel_ptr Lc Ac memc mdc p m HR H1)|].
  split; [exact Hrp|]. split; [exact Hmd|].
  split.
  { intros a Ha Hs He. destruct (HH a Ha Hs He) as [E1 E2].
    assert (Har : 0 <= a < 2 ^ 64) by lia.
    destruct (Hout a (fun Hx => He (n_v_inE a Hx)) Har) as [F1 F2]. split; [rewrite F1; exact E1 | tauto]. }
  split.
  { intros a Ha Hno Hs He. destruct (HG a Ha Hno Hs He) as [E1 E2].
    pose proof (pf_img_bound B n_seg a Ha). assert (Har : 0 <= a < 2 ^ 64) by lia.
    destruct (Hout a (fun Hx => He (n_v_inE a Hx)) Har) as [F1 F2]. split; [rewrite F1; exact E1 | tauto]. }
  split.
  { intros p m i H1 H2 Hi He. rewrite <- (HU p m i H1 H2 Hi He).
    pose proof (rrel_ptr Lc Ac memc mdc p m HR H1) as Ep.
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p m i HM H2 Hi) as (_ & H3 & H4 & _).
    assert (Har : 0 <= ptr_addr L0 p + i < 2 ^ 64) by lia.
    exact (proj1 (Hout (ptr_addr L0 p + i) (fun Hx => He (n_v_inE _ Hx)) Har)). }
  intros a Ha. unfold writable_at. apply Hwm. exact (HSW a Ha).
Qed.

Lemma n_ledger_frame : forall Lc Ac memc mdc mem' Lamc, MR Lc Ac memc mdc -> ledger B Lc Ac memc Lamc peak cnt fail ->
  (forall bb, In bb Lamc -> In bb Lam0) ->
  (forall x, ~ (v <= x < v + 56) -> 0 <= x < 2 ^ 64 -> mbyte segs mem' x = mbyte segs memc x) ->
  ledger B Lc Ac mem' Lamc peak cnt fail.
Proof.
  intros Lc Ac memc mdc mem' Lamc HM HL HLL HA.
  destruct HL as ((W1 & W2 & W3 & W4) & H2 & H3 & H4 & H5 & HF).
  assert (Hst : forall x, alloc_statics x -> mbyte segs mem' x = mbyte segs memc x).
  { intros x Hx. pose proof (pf_img_bound B n_seg x (pf_statics_img B n_seg x Hx)). apply HA; [|lia].
    intro Hv. destruct HPL as (_ & _ & Hb). destruct (Hb (x - v) ltac:(lia)) as (_ & Hs & _).
    apply Hs. replace (v + (x - v)) with x by lia. exact Hx. }
  split.
  { unfold alloc_words. split; [|split; [|split]]; apply (n_word_agree memc); try assumption;
      intros k Hk; apply Hst; unfold alloc_statics; lia. }
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  rewrite Forall_forall in HF |- *. intros [a k] Hin. destruct (HF _ Hin) as (K1 & K2 & K3 & K4). cbn [fst snd] in *.
  pose proof (pf_blk_range B API Lc Ac memc mdc _ _ HM K2) as (R1 & R2). pose proof n_ceil.
  split; [exact K1|]. split; [exact K2|]. split; [|exact K4].
  apply (n_word_agree memc); [exact K3|]. intros j Hj. apply HA; [|lia].
  apply (n_v_heads a k (a - 16 + j) (HLL _ Hin)). lia.
Qed.

Definition Qf (c' : config) : Prop :=
  exists L' A' regs' mem' md' Lam',
    c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom segs)) md' /\
    rpost B API K L0 A0 regs0 mem0 md0 E (freed D) L' A' regs' mem' md' /\
    rd_cells B mem' /\ Permutation Lam0 (D ++ Lam') /\ ledger B L' A' mem' Lam' peak cnt fail /\
    (exists D', Permutation D D' /\ rf_ok F A' (rf_frees F b0 D')) /\ (v = 0 -> L' = L0 /\ A' = A0 /\ Lam' = Lam0) /\
    (v <> 0 -> pj_zero segs mem' v).

Lemma T_fin_post : forall ik iy Lc Ac memc mdc Lamc Dfr mem' regs',
  cur ik iy Lc Ac memc mdc Lamc Dfr [] [] ->
  Frame.munch [(v, v + 56)] memc mem' -> Frame.wmono rsegs memc mem' ->
  bytes_at rsegs mem' v (repeat (Z_to_bv 8 0) 56) -> wr_at rsegs mem' v 56 -> MemNorm.ro_same rsegs memc mem' ->
  regs_preserved regs0 regs' ->
  Qf (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom segs)) mdc).
Proof.
  intros ik iy Lc Ac memc mdc Lamc Dfr mem' regs' Hc Hmu Hwm Hz Hwr Hro Hrp.
  pose proof Hc as (HR & HLc & HRc & HRO & HPD & HPm & _ & HA & _ & HVp).
  pose proof HR as (HM & _).
  pose proof n_v as (Hv1 & Hv2 & Hv8).
  assert (Hpr : forall i, 0 <= i < 56 -> present mem' (v + i)).
  { intros i Hi. destruct HPL as (_ & _ & Hb). destruct (Hb i Hi) as (_ & _ & _ & Hni).
    pose proof Hz as (_ & _ & Hz').
    assert (Hii : (Z.to_nat i < length (repeat (Z_to_bv 8 0) 56))%nat) by (rewrite repeat_length; lia).
    pose proof (Hz' (Z.to_nat i) Hii) as Hzi.
    rewrite (pj_nth_repeat _ _ 56 (Z.to_nat i)) in Hzi by lia.
    replace (v + Z.of_nat (Z.to_nat i)) with (v + i) in Hzi by lia.
    assert (Hr : 0 <= v + i < 2 ^ 64) by lia.
    exact (n_present_of_mrd mem' (v + i) _ Hni Hr Hzi). }
  assert (Hwm' : Frame.wmono segs memc mem') by (rewrite n_seg; exact Hwm).
  assert (HRP : rpost B API K L0 A0 regs0 mem0 md0 E (freed D) Lc Ac regs' mem' mdc)
    by exact (rrel_final Lc Ac memc mdc mem' regs' HR HVp Hmu Hwm' Hpr Hrp).
  pose proof HRP as (HM' & _).
  assert (Hout : forall x, ~ (v <= x < v + 56) -> 0 <= x < 2 ^ 64 -> mbyte segs mem' x = mbyte segs memc x).
  { intros x Hx Hr. assert (Ho : Frame.outside [(v, v + 56)] x) by (apply pf_out1; lia).
    exact (proj1 (pf_mbyte_munch B _ memc mem' x Hmu Hr Ho)). }
  assert (Hro' : MemNorm.ro_same segs memc mem') by (rewrite n_seg; exact Hro).
  exists Lc, Ac, regs', mem', mdc, Lamc. split; [reflexivity|]. split; [exact HRP|].
  split.
  { split; [exact (MemNorm.ro_agree_same segs memc mem' HRO Hro')|].
    destruct (ax_statics AX Lc Ac mem' mdc HM') as (Hg1 & (g & _ & Hg2) & _). split; [exact Hg1 | exists g; exact Hg2]. }
  assert (HL' : Permutation Lamc Rest0) by exact HPm.
  split; [exact (Permutation_trans HREST (Permutation_app_head D (Permutation_sym HL')))|].
  split.
  { apply (n_ledger_frame Lc Ac memc mdc mem' Lamc HM HLc); [|exact Hout].
    intros bb Hb. apply (Permutation_in _ (Permutation_sym HREST)). apply in_or_app. right.
    exact (Permutation_in _ HL' Hb). }
  split.
  { assert (HD' : Permutation D Dfr) by (rewrite <- (app_nil_r Dfr); exact HPD).
    destruct HRc as (Df & HDf & HRc'). exists Df. split; [exact (Permutation_trans HD' HDf) | exact HRc']. }
  split; [intros H0; exfalso; exact (HV H0)|].
  intros _. split; [split; [exact Hv8|]|].
  - split; [lia|]. split; [lia|]. intros a Ha.
    pose proof Hwr as (_ & _ & Hw). pose proof Hz as (_ & _ & Hz').
    pose proof (Hw (a - v) ltac:(lia)) as Hw1. replace (v + (a - v)) with a in Hw1 by lia.
    assert (Hii : (Z.to_nat (a - v) < length (repeat (Z_to_bv 8 0) 56))%nat) by (rewrite repeat_length; lia).
    pose proof (Hz' (Z.to_nat (a - v)) Hii) as Hz1.
    rewrite (pj_nth_repeat _ _ 56 (Z.to_nat (a - v))) in Hz1 by lia.
    replace (v + Z.of_nat (Z.to_nat (a - v))) with a in Hz1 by lia.
    rewrite n_seg. split; [exact Hw1 | exists (Z_to_bv 8 0); exact Hz1].
  - rewrite n_seg. exact Hz.
Qed.

Lemma n_ro_v : forall i, 0 <= i < 56 -> ro_addr rsegs (Z_to_bv 64 (v + i)) = false.
Proof.
  intros i Hi. destruct HPL as (_ & _ & Hb). destruct (Hb i Hi) as (_ & _ & _ & Hni).
  pose proof n_v. apply (pf_not_img_ro B n_seg); [lia | exact Hni].
Qed.

Lemma T_fin : forall ik iy Lc Ac memc mdc Lamc Dfr regs_c,
  cur ik iy Lc Ac memc mdc Lamc Dfr [] [] ->
  getr regs_c 2 = Z_to_bv 64 (sp0 - 48) -> getr regs_c 8 = Z_to_bv 64 v -> rkeep regs_c regs0 ->
  SR segs (mkCfg (mkst regs_c (Z_to_bv 64 0x14624) memc (seg_rom segs)) mdc) Qf.
Proof.
  intros ik iy Lc Ac memc mdc Lamc Dfr regs_c Hc H2 H8 HKc.
  pose proof Hc as (HR & HLc & HRc & HRO & HPD & HPm & _ & HA & HFr & HVp).
  pose proof HR as (HM & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof n_sp as (Hal & Hsp0 & Hsp2). pose proof n_ceil as Hc0. pose proof n_K as HK0. unfold ALLOC_STACK in HK0.
  pose proof n_v as (Hv1 & Hv2 & Hv8).
  destruct HFr as (j & Hj).
  assert (Hra : YK0s.ret_ok (getr regs0 1)) by (destruct n_pre as (_ & _ & _ & H & _); exact H).
  apply (pf_run B regs_c (Z_to_bv 64 0x14624) memc mdc
    (fun R pc' mem' => pc' = Z_to_bv 64 MEMSET /\ mem' = memc /\
       getr R (Z_to_bv 5 1) = getr regs0 1 /\ getr R (Z_to_bv 5 2) = getr regs0 2 /\
       getr R (Z_to_bv 5 8) = getr regs0 8 /\ getr R (Z_to_bv 5 9) = getr regs0 9 /\
       getr R (Z_to_bv 5 18) = getr regs0 18 /\ getr R (Z_to_bv 5 19) = getr regs0 19 /\
       getr R (Z_to_bv 5 10) = Z_to_bv 64 v /\ getr R (Z_to_bv 5 11) = Z_to_bv 64 0 /\
       getr R (Z_to_bv 5 12) = Z_to_bv 64 56 /\ rkeep R regs0) Qf Hh Hl).
  { rewrite n_seg. unfold rmk.
    eapply evt_mono.
    { eapply (ka_str_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v).
      - lia.
      - lia.
      - exact H8.
      - rewrite H2, unsigned_lit by lia. lia.
      - rewrite H2, unsigned_lit by lia. exact Hj. }
    intros ms (R & -> & E1 & E2 & E8 & E9 & E18 & E19 & E10 & E11 & E12 & HK1).
    exists R, (Z_to_bv 64 MEMSET), memc. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact E1|].
    split.
    { rewrite E2, H2, unsigned_lit by lia. replace (spZ regs0 - 48 + 48) with (spZ regs0) by lia.
      unfold spZ. apply MState.Z_to_bv_bv_unsigned. }
    split; [exact E8|]. split; [exact E9|]. split; [exact E18|]. split; [exact E19|].
    split; [exact E10|]. split; [exact E11|]. split; [exact E12|].
    eapply rkeep_trans; [exact HK1|]. eapply rkeep_trans; [|exact HKc]. rk_tac. }
  intros R1 pc1 mem1 regs1 (-> & -> & E1 & E2 & E8 & E9 & E18 & E19 & E10 & E11 & E12 & HK1) Hg1.
  apply (pf_run B regs1 (Z_to_bv 64 MEMSET) memc mdc
    (fun R pc' mem' => pc' = getr regs0 1 /\ rkeep R regs0 /\
       getr R (Z_to_bv 5 2) = getr regs0 2 /\ getr R (Z_to_bv 5 8) = getr regs0 8 /\
       getr R (Z_to_bv 5 9) = getr regs0 9 /\ getr R (Z_to_bv 5 18) = getr regs0 18 /\
       getr R (Z_to_bv 5 19) = getr regs0 19 /\
       Frame.munch [(v, v + 56)] memc mem' /\ Frame.wmono rsegs memc mem' /\
       bytes_at rsegs mem' v (repeat (Z_to_bv 8 0) 56) /\ wr_at rsegs mem' v 56 /\ MemNorm.ro_same rsegs memc mem')
    Qf Hh Hl).
  { rewrite n_seg. unfold rmk.
    rewrite (pf_g10 regs1), (pf_g11 regs1), (pf_g12 regs1), (Hg1 (Z_to_bv 5 10)), (Hg1 (Z_to_bv 5 11)),
      (Hg1 (Z_to_bv 5 12)), E10, E11, E12.
    assert (Hst : stk rsegs memc v (v + 56)).
    { destruct HHD as ((_ & Hst0) & _). rewrite <- n_seg.
      apply (pf_stk_agree segs mem0 memc v (v + 56) Hst0). intros x Hx. apply HA. left. exact Hx. }
    assert (HRO' : MemNorm.ro_agree rsegs memc) by (rewrite <- n_seg; exact HRO).
    eapply evt_mono.
    { exact (ka_memset MSC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ memc v HRO' ltac:(lia) ltac:(lia) n_ro_v Hst). }
    intros ms (R & m' & -> & HK2 & G2 & G8 & G9 & G18 & G19 & Hmu & Hwm & Hz & Hwr & Hro).
    exists R, (getr regs0 1), m'. split.
    { f_equal. rewrite (pf_g1 regs1), (Hg1 (Z_to_bv 5 1)), E1. exact (pf_ret_pc _ Hra). }
    split; [reflexivity|].
    split.
    { eapply rkeep_trans; [exact HK2|]. eapply rkeep_trans; [|exact HK1].
      eapply rkeep_trans; [|intros r _; apply Hg1]. rk_tac. }
    split; [rewrite G2, (pf_g2 regs1), (Hg1 (Z_to_bv 5 2)); exact E2|].
    split; [rewrite G8, (pf_g8 regs1), (Hg1 (Z_to_bv 5 8)); exact E8|].
    split; [rewrite G9, (pf_g9 regs1), (Hg1 (Z_to_bv 5 9)); exact E9|].
    split; [rewrite G18, (pf_g18 regs1), (Hg1 (Z_to_bv 5 18)); exact E18|].
    split; [rewrite G19, (pf_g19 regs1), (Hg1 (Z_to_bv 5 19)); exact E19|].
    split; [exact Hmu|]. split; [exact Hwm|]. split; [exact Hz|]. split; [exact Hwr | exact Hro]. }
  intros R2 pc2 mem2 regs2 (-> & HK2 & G2 & G8 & G9 & G18 & G19 & Hmu & Hwm & Hz & Hwr & Hro) Hg2.
  apply SR_ret. apply (T_fin_post ik iy Lc Ac memc mdc Lamc Dfr mem2 regs2 Hc Hmu Hwm Hz Hwr Hro).
  intros r Hr. rewrite (Hg2 (Z_to_bv 5 r)). unfold callee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]].
  - rewrite G2. reflexivity.
  - apply HK2. lia.
  - apply HK2. lia.
  - rewrite G8. reflexivity.
  - rewrite G9. reflexivity.
  - assert (Hr' : r = 18 \/ r = 19 \/ 20 <= r <= 27) by lia.
    destruct Hr' as [->|[->|Hr']]; [rewrite G18; reflexivity | rewrite G19; reflexivity | apply HK2; lia].
Qed.

Local Notation NN := (Z.to_nat n).

Lemma n_hs : pj_u64 segs mem0 (v + 16) str.
Proof. destruct HHD as (_ & _ & _ & H & _). exact H. Qed.

Lemma n_hk : pj_u64 segs mem0 (v + 24) kids.
Proof. destruct HHD as (_ & _ & _ & _ & H & _). exact H. Qed.

Lemma n_hy : pj_u64 segs mem0 (v + 32) keys.
Proof. destruct HHD as (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma n_hn : pj_u64 segs mem0 (v + 40) n.
Proof. destruct HHD as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma n_hdr_vals : 0 <= str < 2 ^ 64 /\ 0 <= kids < 2 ^ 64 /\ 0 <= keys < 2 ^ 64 /\ 0 <= n < 2 ^ 64.
Proof. exact (conj (proj1 n_hs) (conj (proj1 n_hk) (conj (proj1 n_hy) (proj1 n_hn)))). Qed.

Lemma n_rd8 : forall m a x, pj_u64 segs mem0 a x -> (forall y, a <= y < a + 8 -> mbyte segs m y = mbyte segs mem0 y) ->
  ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 x)).
Proof.
  intros m a x Hu HA. destruct (pf_u64_agree segs mem0 m a x Hu HA) as (_ & HB). rewrite n_seg in HB.
  rewrite <- (Z.add_0_r a) at 1. rewrite (bytes_at_read rsegs m a _ 0 8 HB) by (rewrite ?length_le8; cbn; lia).
  reflexivity.
Qed.

Lemma n_lam_rng : forall a k, In (a, k) Lam0 -> 4112 <= a /\ 0 <= k /\ a + k <= alloc_ceiling.
Proof.
  intros a k H. destruct n_MR0 as (HM & _).
  destruct (pf_lraw B L0 A0 mem0 Lam0 peak cnt fail a k HLED H) as (Hk & Hraw).
  pose proof (pf_blk_range B API L0 A0 mem0 md0 _ _ HM Hraw). lia.
Qed.

Lemma n_R0_sub : forall bb, In bb R0 -> In bb Lam0.
Proof.
  intros bb H. apply n_Dsub. apply (Permutation_in _ (Permutation_sym HP)).
  apply in_app_or in H as [H|H]; [|apply in_app_or in H as [H|H]].
  - apply in_or_app. right. apply in_or_app. left. exact H.
  - apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact H.
  - apply in_or_app. left. exact H.
Qed.

Lemma n_Di_sub : forall bb, In bb Di -> In bb Lam0.
Proof.
  intros bb H. apply n_Dsub. apply (Permutation_in _ (Permutation_sym HP)).
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

Lemma n_FP_cover : forall ik iy Dr y, FP ik iy Dr y ->
  v <= y < v + 56 \/ exists a b, In (a, b) (Dr ++ R0) /\ a <= y < a + b.
Proof.
  intros ik iy Dr y [H|[(Hk & H)|[H|(bb & Hin & H)]]].
  - left. exact H.
  - right. destruct HY as [(_ & Hf & _)|(_ & ky & _ & Hkyn & EDy)]; [rewrite Hk in Hf; discriminate|].
    exists keys, ky. split; [|lia].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite EDy. left. reflexivity.
  - right. assert (Hn : 0 < n) by lia. destruct (n_kids_blk Hn) as (kk & _ & Hkn & EDk).
    exists kids, kk. split; [|lia].
    apply in_or_app. right. apply in_or_app. left. rewrite EDk. left. reflexivity.
  - right. destruct bb as [a b]. exists a, b. split; [apply in_or_app; left; exact Hin | exact H].
Qed.

Lemma n_FP_rng : forall ik iy Dr x, (forall bb, In bb Dr -> In bb Lam0) -> FP ik iy Dr x ->
  v <= x < v + 56 \/ 0 <= x < alloc_ceiling.
Proof.
  intros ik iy Dr x HD Hx. destruct (n_FP_cover ik iy Dr x Hx) as [H|(a & b & Hin & H)]; [left; exact H|right].
  assert (Hl : In (a, b) Lam0).
  { apply in_app_or in Hin as [Hin|Hin]; [exact (HD _ Hin) | exact (n_R0_sub _ Hin)]. }
  pose proof (n_lam_rng a b Hl). lia.
Qed.

Lemma n_FP_iy : forall ik iy iy' Dr x, (iy <= iy')%nat -> FP ik iy' Dr x -> FP ik iy Dr x.
Proof.
  intros ik iy iy' Dr x Hle [H|[(Hk & H)|[H|H]]].
  - left. exact H.
  - right. left. split; [exact Hk | lia].
  - right. right. left. exact H.
  - right. right. right. exact H.
Qed.

Lemma n_FP_end : forall y, FP NN NN [] y -> v <= y < v + 56.
Proof.
  intros y Hy. pose proof n_hdr_vals as (_ & _ & _ & Hn0).
  destruct Hy as [H|[(_ & H)|[H|(bb & Hb & _)]]].
  - exact H.
  - rewrite Z2Nat.id in H by lia. lia.
  - rewrite Z2Nat.id in H by lia. lia.
  - destruct Hb.
Qed.

Lemma n_kshape : exists k, kids = 0 /\ k = 0 /\ Dk = [] \/ kids <> 0 /\ Dk = [(kids, k)].
Proof.
  destruct HK as [(E1 & _ & E2)|(k & Hk & _ & E)].
  - exists 0. left. split; [exact E1 | split; [reflexivity | exact E2]].
  - exists k. right. split; [pose proof (n_lam_rng kids k Hk); lia | exact E].
Qed.

Lemma n_yshape : exists k, keys = 0 /\ k = 0 /\ Dy = [] \/ keys <> 0 /\ Dy = [(keys, k)].
Proof.
  destruct HY as [(E1 & _ & E2)|(_ & k & Hk & _ & E)].
  - exists 0. left. split; [exact E1 | split; [reflexivity | exact E2]].
  - exists k. right. split; [pose proof (n_lam_rng keys k Hk); lia | exact E].
Qed.

Lemma n_sshape : exists k, str = 0 /\ k = 0 /\ Ds = [] \/ str <> 0 /\ Ds = [(str, k)].
Proof.
  destruct HS as [(E1 & E2)|(k & Hk & E)].
  - exists 0. left. split; [exact E1 | split; [reflexivity | exact E2]].
  - exists k. right. split; [pose proof (n_lam_rng str k Hk); lia | exact E].
Qed.

Lemma n_lbound : 0 < n -> 56 * n <= alloc_ceiling /\ 0 <= kids /\ kids + 56 * n <= alloc_ceiling /\
  0 <= keys /\ keys + 8 * n <= alloc_ceiling.
Proof.
  intros Hn. destruct (n_kids_blk Hn) as (kk & Hkk & Hkn & _). pose proof (n_lam_rng kids kk Hkk) as Hr.
  destruct HY as [(Ey & _ & _)|(_ & ky & Hky & Hkyn & _)].
  - rewrite Ey. lia.
  - pose proof (n_lam_rng keys ky Hky). lia.
Qed.

Lemma cur_fp : forall ik iy iy' Lc Ac memc mdc Lamc Dfr Dr R, cur ik iy Lc Ac memc mdc Lamc Dfr Dr R ->
  (forall x, FP ik iy' Dr x -> FP ik iy Dr x) -> cur ik iy' Lc Ac memc mdc Lamc Dfr Dr R.
Proof.
  intros ik iy iy' Lc Ac memc mdc Lamc Dfr Dr R (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) HF.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [intros x Hx; exact (H8 x (HF x Hx))|]. split; [exact H9 | exact H10].
Qed.

Lemma n_vrd : forall ik iy Lc Ac memc mdc Lamc Dfr Dr R a x, cur ik iy Lc Ac memc mdc Lamc Dfr Dr R ->
  pj_u64 segs mem0 a x -> v <= a -> a + 8 <= v + 56 ->
  ov_read_bytes rsegs memc (wa a) 8 = Some (le8 (Z_to_bv 64 x)).
Proof.
  intros ik iy Lc Ac memc mdc Lamc Dfr Dr R a x Hc Hu H1 H2. apply (n_rd8 memc a x Hu).
  intros y Hy. destruct Hc as (_ & _ & _ & _ & _ & _ & _ & HA & _).
  assert (Hf : FP ik iy Dr y) by (left; lia). exact (proj1 (HA y Hf)).
Qed.

Lemma n_ro_munch : forall memc memc', Frame.munch [(sp0 - 48, sp0)] memc memc' -> MemNorm.ro_same segs memc memc'.
Proof.
  intros memc memc' Hmu a Ha. apply Hmu. rewrite n_seg in Ha. unfold ro_addr in Ha.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [sg|] eqn:Fs; [|discriminate].
  pose proof (pf_img_bound B n_seg _ (pf_find_img B n_seg _ sg Fs)) as Hb.
  pose proof n_sp as (_ & Hsp & _). pose proof n_ceil. pose proof n_K as HK0. unfold ALLOC_STACK in HK0.
  apply pf_out1. lia.
Qed.

Lemma n_ledger_low : forall Lc Ac memc mdc mem' Lamc, MR Lc Ac memc mdc -> ledger B Lc Ac memc Lamc peak cnt fail ->
  (forall x, 0 <= x < alloc_ceiling -> mbyte segs mem' x = mbyte segs memc x) ->
  ledger B Lc Ac mem' Lamc peak cnt fail.
Proof.
  intros Lc Ac memc mdc mem' Lamc HM HL HA. pose proof n_ceil as Hc0.
  destruct HL as ((W1 & W2 & W3 & W4) & H2 & H3 & H4 & H5 & HF).
  assert (Hst : forall x, alloc_statics x -> mbyte segs mem' x = mbyte segs memc x).
  { intros x Hx. pose proof (pf_img_bound B n_seg x (pf_statics_img B n_seg x Hx)). apply HA. lia. }
  split.
  { unfold alloc_words. split; [|split; [|split]]; apply (n_word_agree memc); try assumption;
      intros k Hk; apply Hst; unfold alloc_statics; lia. }
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  rewrite Forall_forall in HF |- *. intros [a k] Hin. destruct (HF _ Hin) as (K1 & K2 & K3 & K4). cbn [fst snd] in *.
  pose proof (pf_blk_range B API Lc Ac memc mdc _ _ HM K2) as (R1 & R2).
  split; [exact K1|]. split; [exact K2|]. split; [|exact K4].
  apply (n_word_agree memc); [exact K3|]. intros j Hj. apply HA. lia.
Qed.

Lemma n_stk0 : Frame.stk rsegs mem0 (sp0 - 48) sp0.
Proof.
  destruct n_pre as (_ & _ & _ & _ & _ & _ & _ & HW & _).
  pose proof n_sp as (_ & Hsp & Hsp2). pose proof n_ceil. pose proof n_K as HK0. unfold ALLOC_STACK in HK0.
  split; [lia|]. split; [lia|]. intros a Ha.
  assert (Hw : writable_at segs mem0 a) by (apply HW; lia).
  rewrite n_seg in Hw. split; [exact Hw|].
  revert Hw. unfold mrd, wa, writable_at, wview.
  destruct (mem0 (Z_to_bv 64 a)) as [b|]; intros Hw; [exists b; reflexivity|].
  rewrite unsigned_lit in Hw by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:Fs; [|contradiction].
  exfalso. pose proof (pf_img_bound B n_seg a (pf_find_img B n_seg a seg Fs)). lia.
Qed.

Definition rsite (R : bvmap 5 word) : Prop :=
  getr R (Z_to_bv 5 2) = Z_to_bv 64 (sp0 - 48) /\ getr R (Z_to_bv 5 8) = Z_to_bv 64 v /\ rkeep R regs0.

Definition lhd (i : Z) (R : bvmap 5 word) : Prop :=
  getr R (Z_to_bv 5 1) = Z_to_bv 64 0x145e4 /\ getr R (Z_to_bv 5 10) = Z_to_bv 64 (kids + 56 * i) /\
  getr R (Z_to_bv 5 9) = Z_to_bv 64 (56 * i) /\ getr R (Z_to_bv 5 18) = Z_to_bv 64 (8 * i) /\
  getr R (Z_to_bv 5 19) = Z_to_bv 64 i.

Definition s14 (i : Z) (R : bvmap 5 word) : Prop :=
  rsite R /\ getr R (Z_to_bv 5 9) = Z_to_bv 64 (56 * i) /\ getr R (Z_to_bv 5 18) = Z_to_bv 64 (8 * i) /\
  getr R (Z_to_bv 5 19) = Z_to_bv 64 i.

Definition lp (i : Z) (R : bvmap 5 word) (pc : word) : Prop :=
  rsite R /\ (i + 1 < n /\ pc = Z_to_bv 64 PJ_FREE /\ lhd (i + 1) R \/
    n <= i + 1 /\ pc = Z_to_bv 64 FUZZ_FREE /\ getr R (Z_to_bv 5 1) = Z_to_bv 64 0x14614 /\
    getr R (Z_to_bv 5 10) = Z_to_bv 64 kids).

Definition LH (i : nat) : Prop := forall Lc Ac memc mdc Lamc Dfr Dr regs_c,
  (i < NN)%nat -> cur i i Lc Ac memc mdc Lamc Dfr Dr R0 -> rsite regs_c -> lhd (Z.of_nat i) regs_c ->
  SR segs (mkCfg (mkst regs_c (Z_to_bv 64 PJ_FREE) memc (seg_rom segs)) mdc) Qf.

Lemma rsite_eq : forall R R', rsite R -> (forall r, getr R' r = getr R r) -> rsite R'.
Proof.
  intros R R' (H2 & H8 & Hkp) Hg. split; [rewrite Hg; exact H2|]. split; [rewrite Hg; exact H8|].
  intros r Hr. rewrite Hg. exact (Hkp r Hr).
Qed.

Lemma rsite_pres : forall R R', rsite R -> regs_preserved R R' -> rsite R'.
Proof.
  intros R R' (H2 & H8 & Hkp) Hpr. split; [rewrite (Hpr 2 ltac:(unfold callee_saved; lia)); exact H2|].
  split; [rewrite (Hpr 8 ltac:(unfold callee_saved; lia)); exact H8|].
  exact (rkeep_trans R' R regs0 (pf_pres_keep R R' Hpr) Hkp).
Qed.

Lemma rsite_ka : forall R regs X, rsite regs -> getr R (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) ->
  getr R (Z_to_bv 5 8) = Z_to_bv 64 v -> rkeep R X -> rkeep X regs -> rsite R.
Proof.
  intros R regs X (H2 & H8 & Hkp) E2 E8 K1 K2. split; [rewrite E2; exact H2|]. split; [exact E8|].
  exact (rkeep_trans R X regs0 K1 (rkeep_trans X regs regs0 K2 Hkp)).
Qed.

Lemma lhd_eq : forall i R R', lhd i R -> (forall r, getr R' r = getr R r) -> lhd i R'.
Proof. intros i R R' H Hg. unfold lhd in *. rewrite !Hg. exact H. Qed.

Lemma s14_eq : forall i R R', s14 i R -> (forall r, getr R' r = getr R r) -> s14 i R'.
Proof. intros i R R' (Hs & H) Hg. split; [exact (rsite_eq R R' Hs Hg)|]. rewrite !Hg. exact H. Qed.

Lemma s14_pres : forall i R R', s14 i R -> regs_preserved R R' -> s14 i R'.
Proof.
  intros i R R' (Hs & H9 & H18 & H19) Hpr. split; [exact (rsite_pres R R' Hs Hpr)|].
  rewrite (Hpr 9 ltac:(unfold callee_saved; lia)), (Hpr 18 ltac:(unfold callee_saved; lia)),
    (Hpr 19 ltac:(unfold callee_saved; lia)).
  split; [exact H9|]. split; [exact H18 | exact H19].
Qed.

Lemma lp_eq : forall i R R' pc, lp i R pc -> (forall r, getr R' r = getr R r) -> lp i R' pc.
Proof.
  intros i R R' pc (Hs & H) Hg. split; [exact (rsite_eq R R' Hs Hg)|]. unfold lhd in *. rewrite !Hg. exact H.
Qed.

Lemma T_ffx : forall Lc Ac memc mdc Lamc Dfr R1 R2 regs_c p k ret,
  cur NN NN Lc Ac memc mdc Lamc Dfr [] (R1 ++ R2) ->
  (p = 0 /\ k = 0 /\ R1 = [] \/ p <> 0 /\ R1 = [(p, k)]) -> rsite regs_c ->
  getr regs_c (Z_to_bv 5 10) = Z_to_bv 64 p -> getr regs_c (Z_to_bv 5 1) = Z_to_bv 64 ret ->
  0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
  SR segs (mkCfg (mkst regs_c (Z_to_bv 64 FUZZ_FREE) memc (seg_rom segs)) mdc)
    (fun c' => exists L' A' regs' mem' md' Lam',
       c' = mkCfg (mkst regs' (Z_to_bv 64 ret) mem' (seg_rom segs)) md' /\ rsite regs' /\
       cur NN NN L' A' mem' md' Lam' (Dfr ++ R1) [] R2).
Proof.
  intros Lc Ac memc mdc Lamc Dfr R1 R2 regs_c p k ret Hc Hsh Hs H10 H1 Hr1 Hr2.
  pose proof Hs as (H2 & H8 & Hkp).
  eapply SR_mono.
  { apply (T_ff NN NN NN Lc Ac memc mdc Lamc Dfr [] R1 R2 regs_c p k ret Hc Hsh).
    - intros y Hy. exact Hy.
    - intros y Hy. left. exact (n_FP_end y Hy).
    - exact H10.
    - exact H1.
    - exact Hr1.
    - exact Hr2.
    - exact H2.
    - exact (Hkp 4 ltac:(lia)). }
  intros c' (L' & A' & regs' & mem' & md' & Lam' & -> & HP' & Hc').
  exists L', A', regs', mem', md', Lam'. split; [reflexivity|].
  split; [exact (rsite_pres regs_c regs' Hs HP') | exact Hc'].
Qed.

Lemma T_exit : forall Lc Ac memc mdc Lamc Dfr Dr regs_c,
  cur NN NN Lc Ac memc mdc Lamc Dfr Dr R0 -> rsite regs_c ->
  getr regs_c (Z_to_bv 5 1) = Z_to_bv 64 0x14614 -> getr regs_c (Z_to_bv 5 10) = Z_to_bv 64 kids ->
  SR segs (mkCfg (mkst regs_c (Z_to_bv 64 FUZZ_FREE) memc (seg_rom segs)) mdc) Qf.
Proof.
  intros Lc Ac memc mdc Lamc Dfr Dr regs_c Hc Hs H1 H10.
  assert (HDr : Dr = []).
  { destruct Hc as (_ & _ & _ & _ & _ & _ & HIt & _). rewrite Nat.sub_diag in HIt. exact HIt. }
  subst Dr.
  pose proof n_v as (Hv1 & Hv2 & Hv8). pose proof n_hdr_vals as (Hs0 & Hk0 & Hy0 & Hn0).
  destruct n_kshape as (kk & Hkk). destruct n_yshape as (ky & Hky). destruct n_sshape as (kz & Hkz).
  eapply SR_bind.
  { apply (T_ffx Lc Ac memc mdc Lamc Dfr Dk (Dy ++ Ds) regs_c kids kk 0x14614 Hc Hkk Hs H10 H1);
      [lia | reflexivity]. }
  intros c1 (L1 & A1 & regs1 & mem1 & md1 & Lam1 & -> & Hs1 & Hc1).
  pose proof Hc1 as ((HM1 & _) & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM1) as (Hh1 & Hl1 & _).
  pose proof Hs1 as (G2 & G8 & GK).
  apply (pf_run B regs1 (Z_to_bv 64 0x14614) mem1 md1
    (fun R pc' mem' => pc' = Z_to_bv 64 FUZZ_FREE /\ mem' = mem1 /\ rsite R /\
       getr R (Z_to_bv 5 1) = Z_to_bv 64 0x1461c /\ getr R (Z_to_bv 5 10) = Z_to_bv 64 keys) Qf Hh1 Hl1).
  { rewrite n_seg. unfold rmk. eapply evt_mono.
    { eapply ka_kids_ret with (v := v) (keys := keys);
        [lia | lia | lia | exact G8 | eapply n_vrd; [exact Hc1 | exact n_hy | lia | lia]]. }
    intros ms (R & -> & E1 & E2 & E8 & E10 & HK1). exists R, (Z_to_bv 64 FUZZ_FREE), mem1.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply (rsite_ka R regs1 _ Hs1 E2 E8 HK1); rk_tac|]. split; [exact E1 | exact E10]. }
  intros R pc' mem' regs2 (-> & -> & Hs2 & E1 & E10) Hg2.
  eapply SR_bind.
  { apply (T_ffx L1 A1 mem1 md1 Lam1 (Dfr ++ Dk) Dy Ds regs2 keys ky 0x1461c Hc1 Hky (rsite_eq _ _ Hs2 Hg2));
      [rewrite Hg2; exact E10 | rewrite Hg2; exact E1 | lia | reflexivity]. }
  intros c2 (L2 & A2 & regs3 & mem2 & md2 & Lam2 & -> & Hs3 & Hc2).
  pose proof Hc2 as ((HM2 & _) & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  pose proof Hs3 as (G2' & G8' & GK').
  apply (pf_run B regs3 (Z_to_bv 64 0x1461c) mem2 md2
    (fun R pc' mem' => pc' = Z_to_bv 64 FUZZ_FREE /\ mem' = mem2 /\ rsite R /\
       getr R (Z_to_bv 5 1) = Z_to_bv 64 0x14624 /\ getr R (Z_to_bv 5 10) = Z_to_bv 64 str) Qf Hh2 Hl2).
  { rewrite n_seg. unfold rmk. eapply evt_mono.
    { eapply ka_keys_ret with (v := v) (str := str);
        [lia | lia | lia | exact G8' | eapply n_vrd; [exact Hc2 | exact n_hs | lia | lia]]. }
    intros ms (Rk & -> & F1 & F2 & F8 & F10 & HK2). exists Rk, (Z_to_bv 64 FUZZ_FREE), mem2.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply (rsite_ka Rk regs3 _ Hs3 F2 F8 HK2); rk_tac|]. split; [exact F1 | exact F10]. }
  intros R' pc' mem' regs4 (-> & -> & Hs4 & E1' & E10') Hg4.
  eapply SR_bind.
  { apply (T_ffx L2 A2 mem2 md2 Lam2 ((Dfr ++ Dk) ++ Dy) Ds [] regs4 str kz 0x14624);
      [rewrite app_nil_r; exact Hc2 | exact Hkz | exact (rsite_eq _ _ Hs4 Hg4) | rewrite Hg4; exact E10' |
       rewrite Hg4; exact E1' | lia | reflexivity]. }
  intros c3 (L3 & A3 & regs5 & mem3 & md3 & Lam3 & -> & (J2 & J8 & JK) & Hc3).
  exact (T_fin NN NN L3 A3 mem3 md3 Lam3 (((Dfr ++ Dk) ++ Dy) ++ Ds) regs5 Hc3 J2 J8 JK).
Qed.

Lemma T_lp : forall i Lc Ac memc mdc Lamc Dfr D2 regs pc,
  (i < NN)%nat -> cur (S i) (S i) Lc Ac memc mdc Lamc Dfr D2 R0 -> lp (Z.of_nat i) regs pc -> LH (S i) ->
  SR segs (mkCfg (mkst regs pc memc (seg_rom segs)) mdc) Qf.
Proof.
  intros i Lc Ac memc mdc Lamc Dfr D2 regs pc Hi Hc (Hs & [(Hlt & -> & Hh)|(Hge & -> & H1 & H10)]) IH1.
  - apply (IH1 Lc Ac memc mdc Lamc Dfr D2 regs); [lia | exact Hc | exact Hs |].
    replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by lia. exact Hh.
  - assert (Ei : S i = NN) by lia. rewrite Ei in Hc.
    exact (T_exit Lc Ac memc mdc Lamc Dfr D2 regs Hc Hs H1 H10).
Qed.

Lemma T_tl : forall i Lc Ac memc mdc Lamc Dfr D2 regs,
  (i < NN)%nat -> cur (S i) (S i) Lc Ac memc mdc Lamc Dfr D2 R0 -> s14 (Z.of_nat i) regs -> LH (S i) ->
  SR segs (mkCfg (mkst regs (Z_to_bv 64 0x145f8) memc (seg_rom segs)) mdc) Qf.
Proof.
  intros i Lc Ac memc mdc Lamc Dfr D2 regs Hi Hc H14 IH1.
  pose proof H14 as (Hs & H9 & H18 & H19). pose proof Hs as (H2 & H8 & Hkp).
  pose proof Hc as ((HM & _) & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof n_v as (Hv1 & Hv2 & Hv8). pose proof n_hdr_vals as (Hs0 & Hk0 & Hy0 & Hn0). pose proof n_ceil as Hc0.
  assert (Hn : 0 < n) by lia.
  pose proof (n_lbound Hn) as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5).
  apply (pf_run B regs (Z_to_bv 64 0x145f8) memc mdc (fun R pc' mem' => mem' = memc /\ lp (Z.of_nat i) R pc')
    Qf Hh Hl).
  { rewrite n_seg. unfold rmk.
    rewrite (pf_g8 regs), (pf_g9 regs), (pf_g18 regs), (pf_g19 regs), H8, H9, H18, H19.
    eapply evt_mono.
    { eapply ka_tail with (v := v) (n := n) (kids := kids) (i := Z.of_nat i);
        [lia | lia | lia | lia | lia | lia | lia | |].
      - eapply n_vrd; [exact Hc | exact n_hn | lia | lia].
      - eapply n_vrd; [exact Hc | exact n_hk | lia | lia]. }
    intros ms (R & pc' & -> & E2 & E8 & HK1 & HB). exists R, pc', memc. split; [reflexivity|].
    split; [reflexivity|].
    split; [apply (rsite_ka R regs _ Hs E2 E8 HK1); rk_tac|].
    destruct HB as [(Hlt & -> & E1 & E10 & E9 & E18 & E19)|(Hge & -> & E1 & E10)].
    - left. split; [exact Hlt|]. split; [reflexivity|]. split; [exact E1|]. split; [exact E10|].
      split; [exact E9|]. split; [exact E18 | exact E19].
    - right. split; [exact Hge|]. split; [reflexivity|]. split; [exact E1 | exact E10]. }
  intros R pc' mem' regs' (-> & Hlp) Hg.
  exact (T_lp i Lc Ac memc mdc Lamc Dfr D2 regs' pc' Hi Hc (lp_eq _ _ _ _ Hlp Hg) IH1).
Qed.

Lemma T_loop : forall j i, (NN - i = j)%nat -> LH i.
Proof.
  induction j as [|j IHj]; intros i Hj Lc Ac memc mdc Lamc Dfr Dr regs_c Hi Hc Hs Hh; [lia|].
  assert (IH1 : LH (S i)) by (apply IHj; lia).
  pose proof Hc as (_ & _ & _ & _ & _ & _ & HIt & _).
  replace (NN - i)%nat with (S (NN - S i)) in HIt by lia.
  cbn [pf_items] in HIt. destruct HIt as (Dk1 & D1 & D2 & EDr & HKy & (d' & Hd & HD1) & HI2).
  subst Dr.
  assert (HI2' : pf_items segs mem0 (lin Lam0) Pd ks (kids + 56 * Z.of_nat (S i)) (keys + 8 * Z.of_nat (S i))
    (NN - S i) D2).
  { replace (kids + 56 * Z.of_nat (S i)) with (kids + 56 * Z.of_nat i + 56) by lia.
    replace (keys + 8 * Z.of_nat (S i)) with (keys + 8 * Z.of_nat i + 8) by lia. exact HI2. }
  pose proof Hs as (H2 & H8 & Hkp). pose proof Hh as (H1 & H10 & H9 & H18 & H19).
  pose proof n_v as (Hv1 & Hv2 & Hv8). pose proof n_hdr_vals as (Hs0 & Hk0 & Hy0 & Hn0). pose proof n_ceil as Hc0.
  assert (Hn : 0 < n) by lia.
  pose proof (n_lbound Hn) as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5).
  eapply SR_bind.
  { exact (T_child i Lc Ac memc mdc Lamc Dfr Dk1 D1 D2 regs_c d' Hc Hi Hd HD1 HI2' H10 H1 H2 (Hkp 4 ltac:(lia))). }
  intros c1 (L1 & A1 & regs1 & mem1 & md1 & Lam1 & -> & HP1 & Hc1).
  pose proof (rsite_pres regs_c regs1 Hs HP1) as Hs1. pose proof Hs1 as (G2 & G8 & GK).
  assert (G9 : getr regs1 (Z_to_bv 5 9) = Z_to_bv 64 (56 * Z.of_nat i))
    by (rewrite (HP1 9 ltac:(unfold callee_saved; lia)); exact H9).
  assert (G18 : getr regs1 (Z_to_bv 5 18) = Z_to_bv 64 (8 * Z.of_nat i))
    by (rewrite (HP1 18 ltac:(unfold callee_saved; lia)); exact H18).
  assert (G19 : getr regs1 (Z_to_bv 5 19) = Z_to_bv 64 (Z.of_nat i))
    by (rewrite (HP1 19 ltac:(unfold callee_saved; lia)); exact H19).
  pose proof Hc1 as ((HM1 & _) & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM1) as (Hh1 & Hl1 & _).
  assert (HX : exists x kx,
    (keys <> 0 -> ov_read_bytes rsegs mem1 (wa (keys + 8 * Z.of_nat i)) 8 = Some (le8 (Z_to_bv 64 x))) /\
    (keys = 0 /\ Dk1 = [] \/ keys <> 0 /\ (x = 0 /\ kx = 0 /\ Dk1 = [] \/ x <> 0 /\ Dk1 = [(x, kx)]))).
  { destruct HY as [(Ey & Eks & _)|(Eks & ky & Hky & Hkyn & _)].
    - exists 0, 0. split; [intros Hne; contradiction|]. left. split; [exact Ey|].
      unfold pj_key in HKy. rewrite Eks in HKy. exact HKy.
    - pose proof (n_lam_rng keys ky Hky) as Hkr.
      unfold pj_key in HKy. rewrite Eks in HKy. destruct HKy as (x & Hx & Hsh).
      assert (Hrd : ov_read_bytes rsegs mem1 (wa (keys + 8 * Z.of_nat i)) 8 = Some (le8 (Z_to_bv 64 x))).
      { apply (n_rd8 mem1 _ x Hx). intros y Hy. destruct Hc1 as (_ & _ & _ & _ & _ & _ & _ & HA1 & _).
        assert (Hf : FP (S i) i D2 y) by (right; left; split; [exact Eks | lia]).
        exact (proj1 (HA1 y Hf)). }
      exists x. destruct Hsh as [(Ex & EDk)|(kx & Hkx & EDk)].
      + exists 0. split; [intros _; exact Hrd|]. right. split; [lia|].
        left. split; [exact Ex | split; [reflexivity | exact EDk]].
      + exists kx. split; [intros _; exact Hrd|]. right. split; [lia|]. right.
        split; [pose proof (n_lam_rng x kx Hkx); lia | exact EDk]. }
  destruct HX as (x & kx & Hrx & Hsh).
  apply (pf_run B regs1 (Z_to_bv 64 0x145e4) mem1 md1
    (fun R pc' mem' => mem' = mem1 /\
      (keys <> 0 /\ pc' = Z_to_bv 64 FUZZ_FREE /\ s14 (Z.of_nat i) R /\
         getr R (Z_to_bv 5 1) = Z_to_bv 64 0x145f8 /\ getr R (Z_to_bv 5 10) = Z_to_bv 64 x \/
       keys = 0 /\ lp (Z.of_nat i) R pc')) Qf Hh1 Hl1).
  { rewrite n_seg. unfold rmk.
    rewrite (pf_g8 regs1), (pf_g9 regs1), (pf_g18 regs1), (pf_g19 regs1), G8, G9, G18, G19.
    eapply evt_mono.
    { eapply ka_child_ret with (v := v) (n := n) (kids := kids) (keys := keys) (x := x) (i := Z.of_nat i);
        [lia | lia | lia | lia | lia | lia | lia | lia | lia | | | | exact Hrx].
      - eapply n_vrd; [exact Hc1 | exact n_hn | lia | lia].
      - eapply n_vrd; [exact Hc1 | exact n_hk | lia | lia].
      - eapply n_vrd; [exact Hc1 | exact n_hy | lia | lia]. }
    intros ms [(Hy & R & -> & E1 & E2 & E8 & E9 & E10 & E18 & E19 & HK1)|(Hy & R & pc' & -> & E2 & E8 & HK1 & HB)].
    - exists R, (Z_to_bv 64 FUZZ_FREE), mem1. split; [reflexivity|]. split; [reflexivity|]. left.
      split; [exact Hy|]. split; [reflexivity|].
      split; [split; [apply (rsite_ka R regs1 _ Hs1 E2 E8 HK1); rk_tac | split; [exact E9 | split; [exact E18 | exact E19]]]|].
      split; [exact E1 | exact E10].
    - exists R, pc', mem1. split; [reflexivity|]. split; [reflexivity|]. right. split; [exact Hy|].
      split; [apply (rsite_ka R regs1 _ Hs1 E2 E8 HK1); rk_tac|].
      destruct HB as [(Hlt & -> & E1 & E10 & E9 & E18 & E19)|(Hge & -> & E1 & E10)].
      + left. split; [exact Hlt|]. split; [reflexivity|]. split; [exact E1|]. split; [exact E10|].
        split; [exact E9|]. split; [exact E18 | exact E19].
      + right. split; [exact Hge|]. split; [reflexivity|]. split; [exact E1 | exact E10]. }
  intros R pc' mem' regs2 (-> & [(Hy & -> & H14 & E1 & E10)|(Hy & Hlp)]) Hg.
  - destruct Hsh as [(Hz0 & _)|(_ & Hsh)]; [contradiction|].
    pose proof (s14_eq _ _ _ H14 Hg) as H14'. pose proof H14' as ((J2 & J8 & JK) & _).
    eapply SR_bind.
    { apply (T_ff (S i) i (S i) L1 A1 mem1 md1 Lam1 (Dfr ++ D1) D2 Dk1 R0 regs2 x kx 0x145f8 Hc1 Hsh).
      - intros y Hy'. exact (n_FP_iy (S i) i (S i) D2 y (Nat.le_succ_diag_r i) Hy').
      - intros y Hy'. exact (n_FP_cover (S i) (S i) D2 y Hy').
      - rewrite Hg. exact E10.
      - rewrite Hg. exact E1.
      - lia.
      - reflexivity.
      - exact J2.
      - exact (JK 4 ltac:(lia)). }
    intros c2 (L2 & A2 & regs3 & mem2 & md2 & Lam2 & -> & HP3 & Hc2).
    exact (T_tl i L2 A2 mem2 md2 Lam2 ((Dfr ++ D1) ++ Dk1) D2 regs3 Hi Hc2 (s14_pres _ _ _ H14' HP3) IH1).
  - destruct Hsh as [(_ & ->)|(Hy' & _)]; [|contradiction].
    apply (T_lp i L1 A1 mem1 md1 Lam1 (Dfr ++ D1) D2 regs2 pc' Hi); [|exact (lp_eq _ _ _ _ Hlp Hg) | exact IH1].
    exact (cur_fp (S i) i (S i) L1 A1 mem1 md1 Lam1 (Dfr ++ D1) D2 R0 Hc1
      (fun y Hy' => n_FP_iy (S i) i (S i) D2 y (Nat.le_succ_diag_r i) Hy')).
Qed.

Lemma T_entry : pf_items segs mem0 (lin Lam0) Pd ks kids keys NN Di ->
  SR segs (mkCfg (mkst regs0 (Z_to_bv 64 PJ_FREE) mem0 (seg_rom segs)) md0) Qf.
Proof using All.
  intros HIT.
  destruct n_MR0 as (HM & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof n_sp as (Hal & Hsp0 & Hsp2). pose proof n_ceil as Hc0. pose proof n_K as HK0. unfold ALLOC_STACK in HK0.
  pose proof n_v as (Hv1 & Hv2 & Hv8). pose proof n_hdr_vals as (Hs0 & Hk0 & Hy0 & Hn0). pose proof n_vbelow as Hvb.
  assert (HRO0 : MemNorm.ro_agree segs mem0)
    by (destruct HENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (H & _)); exact H).
  assert (H48 : Z.of_nat 48 = 48) by reflexivity.
  assert (Hle : sp0 - 48 <= sp0 - Z.of_nat 48) by (rewrite H48; lia).
  destruct (Frame.stk_carve rsegs mem0 (sp0 - 48) sp0 48 n_stk0 Hle) as (_ & junk & Hjunk).
  rewrite H48 in Hjunk.
  apply (pf_run B regs0 (Z_to_bv 64 PJ_FREE) mem0 md0
    (fun R pc' mem' => rsite R /\ Frame.munch [(sp0 - 48, sp0)] mem0 mem' /\ Frame.wmono rsegs mem0 mem' /\
       frm mem' /\
       (n = 0 /\ pc' = Z_to_bv 64 FUZZ_FREE /\ getr R (Z_to_bv 5 1) = Z_to_bv 64 0x14614 /\
          getr R (Z_to_bv 5 10) = Z_to_bv 64 kids \/
        n <> 0 /\ pc' = Z_to_bv 64 PJ_FREE /\ lhd (Z.of_nat 0) R)) Qf Hh Hl).
  { rewrite n_seg. unfold rmk. rewrite HA0.
    eapply evt_mono.
    { eapply ka_entry with (v := v) (n := n) (kids := kids) (junk := junk).
      - lia.
      - unfold spZ in Hvb. lia.
      - lia.
      - unfold spZ in Hsp0. lia.
      - lia.
      - lia.
      - destruct n_hn as (_ & Hb). rewrite n_seg in Hb. exact Hb.
      - destruct n_hk as (_ & Hb). rewrite n_seg in Hb. exact Hb.
      - unfold spZ in Hjunk.
        replace (bv_unsigned (getr regs0 2) + -48) with (bv_unsigned (getr regs0 2) - 48) by lia. exact Hjunk. }
    intros ms (R & pc' & m' & -> & E2 & E8 & E10 & HK1 & Hmu & Hwm & (j & Hj) & Hbr).
    exists R, pc', m'. split; [reflexivity|].
    split.
    { split; [rewrite E2; f_equal; unfold spZ; lia|]. split; [exact E8|]. eapply rkeep_trans; [exact HK1|]. rk_tac. }
    split; [unfold spZ; replace (bv_unsigned (getr regs0 2) - 48) with (bv_unsigned (getr regs0 2) + -48) by lia;
      exact Hmu|].
    split; [exact Hwm|].
    split; [exists j; unfold spZ; replace (bv_unsigned (getr regs0 2) - 48) with (bv_unsigned (getr regs0 2) + -48) by lia;
      exact Hj|].
    destruct Hbr as [(Hn & -> & E1)|(Hn & -> & E1 & E9 & E18 & E19)].
    - left. split; [exact Hn|]. split; [reflexivity|]. split; [exact E1 | exact E10].
    - right. split; [exact Hn|]. split; [reflexivity|].
      split; [exact E1|]. split; [rewrite E10; f_equal; lia|]. split; [rewrite E9; reflexivity|].
      split; [rewrite E18; reflexivity | rewrite E19; reflexivity]. }
  intros R pc' m' regs1 (Hs & Hmu & Hwm & Hfr & Hbr) Hg.
  assert (Hwm' : Frame.wmono segs mem0 m') by (rewrite n_seg; exact Hwm).
  assert (Hlow : forall x, 0 <= x < alloc_ceiling -> mbyte segs m' x = mbyte segs mem0 x).
  { intros x Hx. assert (Ho : Frame.outside [(sp0 - 48, sp0)] x) by (apply pf_out1; lia).
    exact (proj1 (pf_mbyte_munch B _ mem0 m' x Hmu ltac:(lia) Ho)). }
  assert (Hc : cur 0 0 L0 A0 m' md0 Lam0 [] Di R0).
  { split; [exact (rrel_store L0 A0 mem0 md0 m' rrel_init Hmu Hwm')|].
    split; [exact (n_ledger_low L0 A0 mem0 md0 m' Lam0 HM HLED Hlow)|].
    split; [exists []; split; [apply perm_nil | exact HRES]|].
    split; [exact (MemNorm.ro_agree_same segs mem0 m' HRO0 (n_ro_munch mem0 m' Hmu))|].
    split; [exact (Permutation_trans HP (pf_perm4 Ds Dk Dy Di))|].
    split.
    { rewrite app_assoc. eapply Permutation_trans; [exact HREST|]. apply Permutation_app_tail.
      exact (Permutation_trans HP (pf_perm4 Ds Dk Dy Di)). }
    split.
    { replace (kids + 56 * Z.of_nat 0) with kids by lia. replace (keys + 8 * Z.of_nat 0) with keys by lia.
      rewrite Nat.sub_0_r. exact HIT. }
    split.
    { intros x Hx. assert (Ho : Frame.outside [(sp0 - 48, sp0)] x).
      { apply pf_out1. destruct (n_FP_rng 0 0 Di x n_Di_sub Hx) as [Hr|Hr]; lia. }
      assert (Hr : 0 <= x < 2 ^ 64) by (destruct (n_FP_rng 0 0 Di x n_Di_sub Hx) as [Hr|Hr]; lia).
      exact (pf_mbyte_munch B _ mem0 m' x Hmu Hr Ho). }
    split; [exact Hfr | exact n_vplace0]. }
  destruct Hbr as [(Hn & -> & E1 & E10)|(Hn & -> & Hh0)].
  - assert (Ei : NN = 0%nat) by (rewrite Hn; reflexivity).
    apply (T_exit L0 A0 m' md0 Lam0 [] Di regs1).
    + rewrite Ei. exact Hc.
    + exact (rsite_eq _ _ Hs Hg).
    + rewrite Hg. exact E1.
    + rewrite Hg. exact E10.
  - apply (T_loop NN 0 (Nat.sub_0_r NN) L0 A0 m' md0 Lam0 [] Di regs1).
    + lia.
    + exact Hc.
    + exact (rsite_eq _ _ Hs Hg).
    + exact (lhd_eq _ _ _ Hh0 Hg).
Qed.

End Node.

Section Main.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis FF : fuzz_free_contract B API F.
Hypothesis MSC : memset_contract.
Hypothesis AX : AllocExtra B (aa_MR API).

Lemma pjf_step : forall d, (forall d', d = S d' -> pjf_at B API F d') -> pjf_at B API F d.
Proof.
  intros d IH L A regs mem md Lam peak cnt fail b v D HENV HLED HRES HA0 Hc.
  destruct Hc as [(-> & ->)|(Hv & Hfd & HPL & _)].
  - assert (Hrd : rd_cells B mem) by (destruct HENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H); exact H).
    pose proof HENV as (HSG & _ & _ & _ & _ & Hpre & _).
    pose proof Hpre as (HM & _ & _ & Hra & _).
    destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
    apply (pf_run B regs (Z_to_bv 64 PJ_FREE) mem md
      (fun R pc' mem' => pc' = getr regs 1 /\ mem' = mem /\ (forall r, getr R r = getr regs r)) _ Hh Hl).
    + rewrite HSG. unfold rmk. rewrite HA0.
      eapply evt_mono; [apply ka_null|].
      intros ms ->. do 3 eexists. split; [reflexivity|]. split; [exact (pf_ret_pc _ Hra)|]. split; [reflexivity|].
      intros r. rewrite <- HA0. exact (pf_rmk_getr regs r).
    + intros R pc' mem' regs' (-> & -> & HR) Hg. apply SR_ret.
      exists L, A, regs', mem, md, Lam. split; [reflexivity|].
      split; [apply (pf_rpost_refl B API _ L A regs mem md _ _ regs' Hpre); intros r; rewrite Hg; apply HR|].
      split; [exact Hrd|]. split; [apply Permutation_refl|]. split; [exact HLED|].
      split; [exists []; split; [apply perm_nil | exact HRES]|].
      split; [intros _; split; [reflexivity | split; reflexivity]|]. intros H0. exfalso. exact (H0 eq_refl).
  - assert (Hsub : forall x, In x D -> In x Lam).
    { intros [a k] Hx. exact (pf_fd_blocks (ms_segs B) mem (lin Lam) d v D Hfd (a, k) Hx). }
    destruct d as [|d0]; pose proof Hfd as Hfd0; cbn [pj_fd] in Hfd0;
      destruct Hfd0 as (HND & HAP & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & HHD & HS & HK &
        HY & HP & HPi);
      destruct (pf_perm_sub D Lam HND Hsub) as (Rest0 & HREST);
      (eapply SR_mono; [eapply (T_entry B API F L A regs mem md Lam peak cnt fail b v _ D HENV HLED HRES HA0 Hv HPL
         ty num str kids keys n cap ks Ds Dk Dy Di Rest0 HND HAP HHD HS HK HY HP HREST FF MSC AX IH) |
       intros c' Hq; exact Hq]).
    + destruct HPi as (-> & ->). reflexivity.
    + eapply pf_items_mono; [|exact HPi]. intros a D1 H1. unfold Pd. exists d0. split; [reflexivity | exact H1].
Qed.

Lemma pjf_all : forall d, pjf_at B API F d.
Proof.
  induction d as [|d IHd]; apply pjf_step; intros d' Hd; [discriminate | injection Hd as <-; exact IHd].
Qed.

Theorem pj_free_holds : pj_free_contract B API F.
Proof.
  unfold pj_free_contract. intros L A regs mem md Lam peak cnt fail b v d D.
  exact (pjf_all d L A regs mem md Lam peak cnt fail b v D).
Qed.

End Main.
