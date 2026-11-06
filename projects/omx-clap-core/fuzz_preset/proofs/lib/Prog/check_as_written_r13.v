From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_as_written_s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require LedgerCells fuzz_alloc_ran_out_c.
Import ListNotations.
Open Scope Z_scope.

Theorem caw_run1 : caw_run1_prop.
Proof.
  unfold caw_run1_prop, CAW_ENTRY, CAW_AFTER_MALLOC, CAW_MALLOC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m data size lo E0 E1 Hd Hs Hds ST LO.
  subst a0 a1.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 80%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  do 13 step.
  apply evt_done.
  do 4 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. exact FR.
Qed.

Lemma caw_r13_rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. pose proof (bytes_at_read rsegs m a _ 0 8 H ltac:(lia) ltac:(rewrite length_le8; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. reflexivity.
Qed.

Lemma caw_r13_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. pose proof (bytes_at_read rsegs m a _ 0 4 H ltac:(lia) ltac:(rewrite length_le4; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. reflexivity.
Qed.

Lemma caw_r13_rds : forall m S v0 v1 v2 v3,
  bytes_at rsegs m (S + 48) (le8 v0 ++ le8 v1 ++ le8 v2 ++ le8 v3) ->
  ov_read_bytes rsegs m (wa (S + 48)) 8 = Some (le8 v0) /\ ov_read_bytes rsegs m (wa (S + 56)) 8 = Some (le8 v1) /\
  ov_read_bytes rsegs m (wa (S + 64)) 8 = Some (le8 v2) /\ ov_read_bytes rsegs m (wa (S + 72)) 8 = Some (le8 v3).
Proof.
  intros m S v0 v1 v2 v3 H.
  apply bytes_at_app in H as [H0 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [H1 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [H2 H3]. rewrite length_le8 in H3.
  change (Z.of_nat 8) with 8 in H1, H2, H3.
  replace (S + 48 + 8) with (S + 56) in H1 by lia.
  replace (S + 48 + 8 + 8) with (S + 64) in H2 by lia.
  replace (S + 48 + 8 + 8 + 8) with (S + 72) in H3 by lia.
  split; [apply caw_r13_rd8; exact H0|]. split; [apply caw_r13_rd8; exact H1|].
  split; [apply caw_r13_rd8; exact H2|]. apply caw_r13_rd8; exact H3.
Qed.

Lemma caw_r13_rd1 : forall m a v, bytes_at rsegs m a (le1 v) -> ov_read_bytes rsegs m (wa a) 1 = Some (le1 v).
Proof.
  intros m a v H. pose proof (bytes_at_read rsegs m a _ 0 1 H ltac:(lia) ltac:(rewrite length_le1; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. reflexivity.
Qed.

Lemma caw_zx8 : forall z, 0 <= z < 2 ^ 8 -> zx8 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx8. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma caw_r13_seqz : forall rcv, 0 <= rcv < 2 ^ 64 ->
  v_sltiu (Z_to_bv 64 rcv) 1 = Z_to_bv 64 (if rcv =? 0 then 1 else 0).
Proof.
  intros rcv Hr. rewrite v_sltiu_b2z, (unsigned_lit rcv) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec rcv 0) as [->|Hn]; [reflexivity|].
  replace (rcv <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* out_of_memory() and the two checks, from 0x13b6c (s2 = want, s0 = rc) to the return *)
Lemma caw_oom : fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S1 rcv w go gr : Z) (rav s0v s1v s2v : word),
    sp = Z_to_bv 64 S1 -> 0 <= S1 -> S1 + 80 < 2 ^ 64 -> s0 = Z_to_bv 64 rcv -> 0 <= rcv < 2 ^ 64 ->
    s2 = Z_to_bv 64 w -> w = -1 \/ w = 0 \/ w = 1 -> (rcv = 0 <-> 0 <= w) -> (rcv = 0 -> w = 0) ->
    caw_flags m go gr ->
    bytes_at rsegs m (S1 + 48) (le8 s2v ++ le8 s1v ++ le8 s0v ++ le8 rav) ->
    evt rsegs (caw_ret rav (Z_to_bv 64 (caw_rv go gr)) (Z_to_bv 64 (S1 + 80)) gp tp s0v s1v s2v s3 s4 s5 s6 s7 s8 s9
                 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b6c) fc None m (seg_rom rsegs)).
Proof.
  intros RANC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S1 rcv w go gr rav s0v s1v s2v Esp HS0 HS1 Es0 Hr Es2 Hw Hrw Hw0 (Hgo & Hgr & BO & BR) BY.
  subst sp s0 s2.
  destruct (caw_r13_rds m S1 s2v s1v s0v rav BY) as (R48 & R56 & R64 & R72).
  pose proof (caw_r13_rd1 m _ _ BO) as RO. unfold LedgerCells.GL_OWN_RAN_OUT in RO.
  unfold caw_ret, caw_rv.
  do 3 step.
  step. rewrite (caw_zx8 go Hgo). if_cases HB; zify_cond HB.
  - replace ((go =? 0) && (gr =? 0)) with false by (symmetry; apply andb_false_intro1; apply Z.eqb_neq; lia).
    do 7 step.
    apply evt_done. do 14 eexists. reflexivity.
  - assert (E0 : go = 0) by lia. subst go. try clear HB.
    step.
    eapply evt_cut; [eapply RANC with (ran_out := Z_to_bv 64 gr); [rewrite unsigned_lit by lia; lia | exact BR] |].
    intros ms' ->.
    match goal with |- context [ret_pc (Z_to_bv 64 ?k)] =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (apply bv_eq; vm_compute; reflexivity) end.
    step. if_cases HB; zify_cond HB.
    + replace ((0 =? 0) && (gr =? 0)) with false by (symmetry; apply andb_false_intro2; apply Z.eqb_neq; lia).
      do 7 step.
      apply evt_done. do 14 eexists. reflexivity.
    + assert (E1 : gr = 0) by lia. subst gr. try clear HB.
      step. rewrite (caw_r13_seqz rcv Hr).
      destruct Hw as [-> | [-> | ->]].
      * assert (Hn : rcv <> 0) by (intros E; apply Hrw in E; lia).
        rewrite (proj2 (Z.eqb_neq rcv 0) Hn).
        step. step. if_cases HB; [exfalso; vm_compute in HB; discriminate HB | clear HB].
        step. step. if_cases HB; [clear HB | zify_cond HB; lia].
        do 7 step.
        apply evt_done. do 14 eexists. reflexivity.
      * assert (E : rcv = 0) by (apply Hrw; lia). subst rcv.
        step. step. if_cases HB; [exfalso; vm_compute in HB; discriminate HB | clear HB].
        step. step. if_cases HB; [exfalso; vm_compute in HB; discriminate HB | clear HB].
        step. if_cases HB; [exfalso; vm_compute in HB; discriminate HB | clear HB].
        do 7 step.
        apply evt_done. do 14 eexists. reflexivity.
      * exfalso. assert (E : rcv = 0) by (apply Hrw; lia). specialize (Hw0 E). lia.
Qed.

Theorem caw_run3a : caw_run3a_prop.
Proof.
  unfold caw_run3a_prop, CAW_RET_REFUSE.
  intros RANC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S1 rcv go gr rav s0v s1v s2v Esp HS0 HS1 Es0 Hr Hnz FL BY.
  subst sp s0.
  do 2 step.
  eapply (caw_oom RANC) with (w := -1) (rcv := rcv) (S1 := S1);
    [reflexivity | exact HS0 | exact HS1 | reflexivity | exact Hr | | | | | exact FL | exact BY].
  - apply bv_eq. vm_compute. reflexivity.
  - left. reflexivity.
  - split; intros H; [exfalso; exact (Hnz H) | lia].
  - intros H. exfalso. exact (Hnz H).
Qed.

Theorem caw_run3b : caw_run3b_prop.
Proof.
  unfold caw_run3b_prop, CAW_RET_ACCEPT.
  intros RANC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S1 rcv dl go gr pe rav s0v s1v s2v Esp HS0 HS1 Es0 Hr Es1 Hpe Hdl Hd0 FL BD BY.
  subst sp s0 s1.
  pose proof (caw_r13_rd4 m (S1 + 40) (Z_to_bv 64 dl) BD) as R40.
  destruct pe.
  - assert (E : rcv = 0) by (apply Hpe; reflexivity). subst rcv.
    rewrite (Hd0 eq_refl) in R40.
    do 3 step.
    eapply (caw_oom RANC) with (w := 0) (rcv := 0) (S1 := S1);
      [reflexivity | exact HS0 | exact HS1 | reflexivity | lia | | | | | exact FL | exact BY].
    + apply bv_eq. vm_compute. reflexivity.
    + right. left. reflexivity.
    + split; intros _; lia.
    + intros _. reflexivity.
  - assert (E : rcv <> 0) by (intros E; apply Hpe in E; discriminate E).
    destruct Hdl as [-> | ->].
    + do 3 step.
      eapply (caw_oom RANC) with (w := -1) (rcv := rcv) (S1 := S1);
        [reflexivity | exact HS0 | exact HS1 | reflexivity | exact Hr | | | | | exact FL | exact BY].
      * apply bv_eq. vm_compute. reflexivity.
      * left. reflexivity.
      * split; intros H; [exfalso; exact (E H) | lia].
      * intros H. exfalso. exact (E H).
    + do 3 step.
      eapply (caw_oom RANC) with (w := -1) (rcv := rcv) (S1 := S1);
        [reflexivity | exact HS0 | exact HS1 | reflexivity | exact Hr | | | | | exact FL | exact BY].
      * apply bv_eq. vm_compute. reflexivity.
      * left. reflexivity.
      * split; intros H; [exfalso; exact (E H) | lia].
      * intros H. exfalso. exact (E H).
Qed.
