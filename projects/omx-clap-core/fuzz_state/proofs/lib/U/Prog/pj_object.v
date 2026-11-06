From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import memset_c pj_object_c.
Import ListNotations.
Open Scope Z_scope.

Lemma pj_object_find_in : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c end.
  - injection H as <-. left. reflexivity.
  - right. eapply IH. exact H.
Qed.

Lemma pj_object_wr_rd : forall seg, In seg rsegs -> seg_writable seg = true -> seg_readable seg = true.
Proof.
  intros seg Hin Hw.
  assert (C : forallb (fun s => implb (seg_writable s) (seg_readable s)) rsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). rewrite Hw in C. exact C.
Qed.

Lemma pj_object_rd : forall m x, wview rsegs m x <> None -> exists b, mrd rsegs m x = Some b.
Proof.
  intros m x H. unfold mrd. destruct (m x) as [b|] eqn:E; [exists b; reflexivity|].
  unfold wview in H. rewrite E in H.
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|] eqn:FS; [|exfalso; apply H; reflexivity].
  destruct (seg_writable seg) eqn:W; [|exfalso; apply H; reflexivity].
  rewrite (pj_object_wr_rd seg (pj_object_find_in _ _ _ _ FS) W).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at _ _) as [b|]; [exists b; reflexivity | exfalso; apply H; reflexivity].
Qed.

Lemma pj_object_rw : forall m a n, wr_at rsegs m a (Z.of_nat n) -> exists junk, rw_cells rsegs m a [CB n junk].
Proof.
  intros m a n (H1 & H2 & H).
  assert (S : stk rsegs m a (a + Z.of_nat n)).
  { split; [lia|]. split; [lia|]. intros x Hx.
    assert (W : wview rsegs m (wa x) <> None) by (replace x with (a + (x - a)) by lia; apply H; lia).
    split; [exact W | apply pj_object_rd, W]. }
  destruct (stk_carve rsegs m a (a + Z.of_nat n) n S ltac:(lia)) as [_ (junk & J)].
  exists junk. replace (a + Z.of_nat n - Z.of_nat n) with a in J by lia. exact J.
Qed.

Lemma pj_object_stk : forall m m' lo hi a n, stk rsegs m lo hi -> munch [(a, a + n)] m m' -> wmono rsegs m m' ->
  stk rsegs m' a (a + n) -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi a n (H1 & H2 & H) MU WM (_ & _ & K). split; [lia|]. split; [lia|].
  intros x Hx. destruct (H x Hx) as [W (b & B)]. split; [apply WM, W|].
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + n)).
  - apply (K x). lia.
  - exists b. unfold mrd in *. rewrite MU; [exact B|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia|exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact B|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia|exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact B|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia|exact I].
Qed.

Theorem pj_object_holds : memset_contract -> pj_object_contract.
Proof.
  intros MEMSET_H. unfold pj_object_contract, PJ_OBJECT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v lo
    E0 NZ AL HW SPA ST LO DJ MI.
  subst a0.
  pose proof HW as (HV0 & HV1 & _).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(v, v + 56); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  do 7 zstep.
  destruct (pj_object_rw m1 v 56%nat HW) as [junk2 RV].
  eapply evt_cut.
  { eapply MEMSET_H with (junk := junk2).
    - rewrite (unsigned_lit v) by lia. exact RV.
    - exact MI. }
  intros ms' POST. unfold memset_post in POST.
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
    E & MUc & WMc & MIc & RVc).
  subst ms'.
  rewrite (unsigned_lit v) in MUc, RVc by lia.
  change (bv_unsigned (Z_to_bv 64 56)) with 56 in MUc.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) with 56%nat in RVc.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RVc.
  replace (ret_pc (Z_to_bv 64 85236)) with (Z_to_bv 64 85236) by (apply bv_eq; vm_compute; reflexivity).
  assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -16)).
  { apply (pj_object_stk m1 m2 lo (bv_unsigned sp + -16) v 56 ST MUc WMc).
    exact (stk_of_rw_cells rsegs m2 v _ RVc). }
  assert (MU2 : munch [(v, v + 56); (bv_unsigned sp + -16, bv_unsigned sp)] m m2).
  { apply (munch_trans _ m m1 m2 MU). eapply munch_weaken; [|exact MUc].
    unfold sub_fp. cbn [outside]. intros x Hx. tauto. }
  pose proof (wmono_trans rsegs m m1 m2 WM WMc) as WM2.
  apply (rw_cells_transport rsegs [(v, v + 56)] m1 m2) in FR;
    [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia].
  clear ST MU WM MI HW RV MUc WMc.
  rename ST2 into ST, MU2 into MU, WM2 into WM, MIc into MI, RVc into RV.
  zstep.
  assert (C1 : bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite (unsigned_lit v) by lia.
    apply Z.eqb_neq. exact NZ. }
  rewrite C1. cbv iota.
  zstep. zstep.
  assert (C2 : negb (bv_eqb (Z_to_bv 64 (Z.land v 7)) (Z_to_bv 64 0)) = false).
  { assert (LV : Z.land v 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact AL).
    rewrite LV. reflexivity. }
  rewrite C2. cbv iota.
  do 5 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
  destruct RV as [[_ RB] _]. eapply bytes_at_ext; [exact RB|].
  first [reflexivity | vm_compute; reflexivity].
Qed.
