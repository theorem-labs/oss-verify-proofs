(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread.v, with its addresses and numbers changed; 1094 of its 1293 lines of code are new or changed and 653 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require
  PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Img0 EgressFrame EgressBraid.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require
  memcpy_c want_width_c rp_slot_width_c rp_slot_write_c bcmp_c want_width check_gate check_mute.
Import ListNotations.

(* The machine-level segments of check_inject (plain 0x13028), between its allocator calls. *)
Module CISeg.
Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Img0 EgressFrame EgressBraid StrFun
  memcpy_c want_width_c rp_slot_width_c rp_slot_write_c bcmp_c.
Open Scope Z_scope.

Definition CI_MALLOC : Z := 0x14010.
Definition CI_FREE : Z := 0x13ed0.

Ltac ci_usub := check_mute.CMSeg.cm_usub.
Ltac ci_usub_in H := check_mute.CMSeg.cm_usub_in H.
Ltac ci_w := check_mute.CMSeg.cm_w.
Ltac ci_ret := repeat match goal with |- context [ret_pc (Z_to_bv 64 ?z)] =>
  replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.

(* transport_after_call (Lib/Tac.v) with a solver for footprints of more than one interval. *)
Ltac ci_slv := cbn [disjoint_from outside] in *; simpl_sizes; repeat split; lia.
Ltac ci_xport segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : rw_cells segs m ?A2 _ |- _ => footprint_starts_at W A2; clear H
  | H : bytes_at segs m ?A2 _ |- _ => footprint_starts_at W A2; clear H
  end;
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | ci_slv ] | clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | ci_slv ] | clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | ci_slv ] | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; intros; ci_slv | exact MU ] ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* Entry to the call of malloc(n ? n : 1) for c. *)
Definition ci_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f n slot v : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 junk,
    ms' = MS (mkR (Z_to_bv 64 0x13068) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n)
               (Z_to_bv 64 (Z.max n 1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 v) (Z_to_bv 64 slot) (Z_to_bv 64 (Z.max n 1))
               (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CI_MALLOC) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
    rw_cells rsegs m1 (bv_unsigned sp - 64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ci_seg1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n slot v lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp ->
    0 <= n <= 1600 -> 0 <= f < 2 ^ 64 ->
    evt rsegs (ci_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f n slot v m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 slot) (Z_to_bv 64 v) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13028) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f n slot v lo
    ST LO HN HF.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  do 16 step.
  apply evt_done. unfold ci_s1_post.
  do 16 eexists. split.
  2: { split; [eassumption|]. split; [eassumption|]. replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia.
       eassumption. }
  f_equal. check_mute.CMSeg.cm_regs.
  all: first [ exact (check_mute.CMSeg.cm_seqz n ltac:(lia)) | ci_w ].
Qed.

(* From the return of malloc (c in a0, 0x13068) to the call of malloc for e: fuzz_dup's memcpy. *)
Section S2.
Variable MC : memcpy_contract.
Variables (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (f n c slot v : Z) (bs : list byte).
Hypothesis HN : 0 <= n <= 1600.
Hypothesis HC : 4096 <= c /\ c + n < 2 ^ 47.
Hypothesis HF : 0 <= f /\ f + n < 2 ^ 47.
Hypothesis HD : c + n <= f \/ f + n <= c.
Hypothesis HL : length bs = Z.to_nat n.

Definition ci_s2_post : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 (if n =? 0 then 0x130ac else 0x1308c)) sp gp tp t0 t1 t2 (Z_to_bv 64 c)
               (Z_to_bv 64 n) (Z_to_bv 64 (Z.max n 1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 v) (Z_to_bv 64 slot)
               (Z_to_bv 64 (Z.max n 1)) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CI_MALLOC) fc None m' (seg_rom rsegs) /\
    munch [(c, c + n)] m0 m' /\ wmono rsegs m0 m' /\ bytes_at rsegs m' c bs /\ bytes_at rsegs m' f bs.

Lemma ci_seg2 : forall (ra t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk : list byte),
  bytes_at rsegs m0 f bs -> rw_cells rsegs m0 c [CB (Z.to_nat n) junk] -> mem_inv rsegs m0 ->
  evt rsegs ci_s2_post
    (MS (mkR ra sp gp tp t0 t1 t2 x8 (Z_to_bv 64 n) (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 v)
             (Z_to_bv 64 slot) (Z_to_bv 64 (Z.max n 1)) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13068) fc None m0 (seg_rom rsegs)).
Proof using All.
  intros ra t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 junk HBf HJ MI.
  pose proof (munch_refl [(c, c + n)] m0) as MU0.
  pose proof (wmono_refl rsegs m0) as WM0.
  step. if_cases H0; zify_cond H0; rewrite ?unsigned_lit in H0 by lia; [lia |].
  step. step.
  if_cases HZ; zify_cond HZ; rewrite ?unsigned_lit in HZ by lia.
  - (* n = 0: fuzz_dup copies nothing *)
    do 2 step.
    apply evt_done. unfold ci_s2_post. do 15 eexists. split.
    + rewrite (proj2 (Z.eqb_eq n 0)) by lia. reflexivity.
    + split; [exact MU0|]. split; [exact WM0|].
      assert (Hb : bs = []) by (apply length_zero_iff_nil; rewrite HL; lia). rewrite Hb in HBf |- *.
      split; [apply bytes_at_nil; lia | exact HBf].
  - do 4 step.
    eapply evt_cut; [eapply MC with (src := bs) (junk := junk) (m := m0) |].
    { rewrite unsigned_lit by lia. exact HBf. }
    { rewrite unsigned_lit by lia. exact HL. }
    { rewrite !unsigned_lit by lia. exact HJ. }
    { rewrite !unsigned_lit by lia. lia. }
    { exact MI. }
    intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
      MU1 & WM1 & MI1 & RW1 & HF1).
    ci_usub_in MU1. ci_usub_in RW1. ci_usub_in HF1.
    ci_ret.
    do 2 step.
    apply evt_done. unfold ci_s2_post. do 15 eexists. split.
    + rewrite (proj2 (Z.eqb_neq n 0)) by lia. reflexivity.
    + split; [exact MU1|]. split; [exact WM1|].
      split; [exact (check_mute.CMSeg.cm_bytes_of_cells _ _ _ _ RW1) | exact HF1].
Qed.

End S2.

Lemma ci_merge7 : forall segs m A c0 c1 c2 c3 c4 c5 c6 rest,
  rw_cells segs m A (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: rest) ->
  rw_cells segs m A (CB (cells_size [c0; c1; c2; c3; c4; c5; c6]) (cells_bytes [c0; c1; c2; c3; c4; c5; c6]) :: rest).
Proof. intros segs m A c0 c1 c2 c3 c4 c5 c6 rest H. exact (rw_cells_merge segs m A [] [c0; c1; c2; c3; c4; c5; c6] rest H). Qed.

(* The w_put loop (0x13100 .. 0x13180), sample t, for a frame of width w holding the slot. *)
Section Loop.
Variables (sp gp tp t1 t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (r8 r9 r18 r19 r20 r21 rra : word) (m0 : word -> option byte)
  (c n e f v slot w bo lo : Z) (bs vbs : list byte).
Hypothesis HW : 2 <= w <= 40.
Hypothesis HWe : w mod 2 = 0.
Hypothesis HN : 52 + 36 * w <= n.
Hypothesis HSL : 0 <= slot < w.
Hypothesis HAT : (slot mod 2 = 0 /\ bo = 0) \/ (slot mod 2 = 1 /\ bo = 3).
Hypothesis HCE : 0 < c /\ 0 < e /\ (c + n <= e \/ e + n <= c) /\ c + n <= bv_unsigned sp - 64 /\
  e + n <= bv_unsigned sp - 64.
Hypothesis HVS : bv_unsigned sp + 64 <= v /\ v + 48 <= 2 ^ 64.
Hypothesis HLO : 0 <= lo /\ lo + 64 <= bv_unsigned sp.
Hypothesis HVL : length vbs = 48%nat.
Hypothesis HLB : length bs = Z.to_nat n.

Notation ci_W := [(bv_unsigned sp - 64, bv_unsigned sp + 8); (c, c + n); (e, e + n)].
Notation ci_FR := [C8 r21; C8 r20; C8 r19; C8 r18; C8 r9; C8 r8; C8 rra].

Definition ci_G (t : Z) : Z := 50 + 3 * (t * w + (slot - slot mod 2)).

Definition ci_mem (mm : word -> option byte) (L junk : list byte) : Prop :=
  bytes_at rsegs mm e L /\ length L = Z.to_nat n /\ wr_at rsegs mm e n /\ bytes_at rsegs mm c bs /\
  wr_at rsegs mm c n /\ bytes_at rsegs mm v vbs /\ rw_cells rsegs mm (bv_unsigned sp) (CB 8 junk :: ci_FR) /\
  stk rsegs mm lo (bv_unsigned sp) /\ mem_inv rsegs mm /\ munch ci_W m0 mm /\ wmono rsegs m0 mm.

Lemma ci_G_bound : forall t, 0 <= t <= 11 -> 50 <= ci_G t /\ ci_G t + 6 <= 50 + 36 * w.
Proof.
  intros t Ht. unfold ci_G. pose proof (Z.mod_pos_bound slot 2 ltac:(lia)).
  assert (slot - slot mod 2 <= w - 2) by (Z.div_mod_to_equations; lia). nia.
Qed.

Ltac ci_ld_e j jz :=
  match goal with HE : bytes_at rsegs ?mm ?e0 (?A ++ ?X ++ ?C), HA : Z.of_nat (length ?A) = ?G |- _ =>
    let R := fresh "RE" in
    pose proof (group_read rsegs mm e0 A X C j (G + jz) HE ltac:(cbn; lia) ltac:(rewrite HA; lia)) as R;
    cbn [nth] in R; step; clear R
  end.

Ltac ci_st_e j jz :=
  match goal with HE : bytes_at rsegs ?mm ?e0 (?A ++ ?X ++ ?C), HA : Z.of_nat (length ?A) = ?G,
                  HWE : wr_at rsegs ?mm ?e0 ?n0 |- _ =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs mm (wa (e0 + (G + jz))) 1 = true)
      by (apply (wr_at_store_ok rsegs mm e0 n0 (G + jz) 1 HWE); cbn; lia);
    step; rewrite ?Mem.le1_zxb;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm ?a [?b]) _) =>
      change a with (wa (e0 + (G + jz)));
      apply (group_write rsegs mm e0 A X C j (G + jz) b) in HE; [| cbn; lia | rewrite HA; lia];
      let X' := eval cbv [upd_bytes firstn skipn app length Nat.add] in (upd_bytes X j [b]) in
      change (upd_bytes X j [b]) with X' in HE
    end;
    store_done
  end.

Ltac ci_ld_v t :=
  match goal with HV : bytes_at rsegs ?mm v vbs |- _ =>
    let R := fresh "RV" in
    pose proof (word4_read rsegs mm v vbs t (4 * t) HV ltac:(lia) ltac:(rewrite HVL; cbn; lia) eq_refl) as R;
    step; clear R
  end.

(* A byte store into the frame's cells: the stored byte is a loaded one (zxb) or one of v[s]'s (lem). *)
Ltac ci_st_s := step; rewrite ?Mem.le1_zxb; mem_after_store.
Ltac ci_st_be lem := step; rewrite lem; mem_after_store.

Lemma ci_iter : forall (t : Z) (ra1 x5 x16 x17 : word) (junk : list byte) (mm : word -> option byte)
    (Q : machine_state -> Prop),
  0 <= t <= 11 ->
  ci_mem mm (slot_write_upto w slot vbs bs (Z.to_nat t)) junk ->
  (forall (x5' x13' x15' x16' x17' : word) (junk' : list byte) (mm' : word -> option byte),
     x13' = Z_to_bv 64 (e + ci_G (t + 1) + 5) -> x15' = Z_to_bv 64 (v + 4 * (t + 1)) ->
     ci_mem mm' (slot_write_upto w slot vbs bs (Z.to_nat (t + 1))) junk' ->
     evt rsegs Q (MS (mkR ra1 sp gp tp x5' t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 n) (Z_to_bv 64 w) (Z_to_bv 64 (3 * w))
       (Z_to_bv 64 (bv_unsigned sp + (2 + bo))) x13' (Z_to_bv 64 (v + 48)) x15' x16' x17' (Z_to_bv 64 v)
       (Z_to_bv 64 slot) (Z_to_bv 64 e) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x13180) fc None mm' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra1 sp gp tp x5 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 n) (Z_to_bv 64 w) (Z_to_bv 64 (3 * w))
       (Z_to_bv 64 (bv_unsigned sp + (2 + bo))) (Z_to_bv 64 (e + ci_G t + 5)) (Z_to_bv 64 (v + 48))
       (Z_to_bv 64 (v + 4 * t)) x16 x17 (Z_to_bv 64 v)
       (Z_to_bv 64 slot) (Z_to_bv 64 e) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x13100) fc None mm (seg_rom rsegs)).
Proof using All.
  intros t ra1 x5 x16 x17 junk mm Q Ht (HE & HL & HWE & HBC & HWC & HV & FR & ST & HI & MU & WM) K.
  pose proof (ci_G_bound t Ht) as HG.
  destruct (group_split (slot_write_upto w slot vbs bs (Z.to_nat t)) (Z.to_nat (ci_G t)) ltac:(lia))
    as (A & C & g0 & g1 & g2 & g3 & g4 & g5 & EL & HLA).
  rewrite EL in HE, HL. rewrite !length_app in HL. cbn [length] in HL.
  assert (HA : Z.of_nat (length A) = ci_G t) by lia.
  assert (HC : Z.of_nat (length C) = n - ci_G t - 6) by lia.
  clear HLA HL.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  destruct HAT as [[Hp ->]|[Hp ->]];
  ( ci_ld_e 1%nat 1;        (* lbu a6, -4(a3) *)
    ci_st_s;                (* sb a6, 2(sp) *)
    ci_ld_e 0%nat 0;        (* lbu a6, -5(a3) *)
    ci_ld_e 5%nat 5;        (* lbu a7, 0(a3) *)
    ci_st_s;                (* sb a6, 3(sp) *)
    ci_ld_e 3%nat 3;        (* lbu a6, -2(a3) *)
    ci_st_s;                (* sb a6, 4(sp) *)
    ci_ld_e 2%nat 2;        (* lbu a6, -3(a3) *)
    ci_ld_v t;              (* lw t0, 0(a5) *)
    ci_st_s;                (* sb a6, 5(sp) *)
    ci_st_s;                (* sb a7, 6(sp) *)
    ci_ld_e 4%nat 4;        (* lbu a6, -1(a3) *)
    step;                   (* srli a7, t0, 16 *)
    ci_st_s;                (* sb a6, 7(sp) *)
    step;                   (* srli a6, t0, 8 *)
    ci_st_be w32_b2;        (* sb a7, 0(a2) *)
    ci_st_be w32_b1;        (* sb a6, 1(a2) *)
    step;                   (* lbu a6, 3(sp) *)
    ci_st_be w32_le1;       (* sb t0, 2(a2) *)
    ci_st_e 0%nat 0;        (* sb a6, -5(a3) *)
    step;                   (* lbu a6, 2(sp) *)
    ci_st_e 1%nat 1;        (* sb a6, -4(a3) *)
    step;                   (* lbu a6, 5(sp) *)
    ci_st_e 2%nat 2;        (* sb a6, -3(a3) *)
    step;                   (* lbu a6, 4(sp) *)
    ci_st_e 3%nat 3;        (* sb a6, -2(a3) *)
    step;                   (* lbu a6, 7(sp) *)
    ci_st_e 4%nat 4;        (* sb a6, -1(a3) *)
    step;                   (* lbu a6, 6(sp) *)
    step;                   (* addi a5, a5, 4 *)
    ci_st_e 5%nat 5;        (* sb a6, 0(a3) *)
    step;                   (* add a3, a3, a1 *)
    match goal with FR : rw_cells _ _ _ _ |- _ => apply ci_merge7 in FR; cbn [cells_size csize Nat.add] in FR end;
    eapply K; [ f_equal; unfold ci_G; lia | f_equal; lia | ];
    replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia;
    rewrite (slot_write_upto_S_group w slot vbs bs (Z.to_nat t) A C g0 g1 g2 g3 g4 g5 EL)
      by (rewrite Z2Nat.id by lia; rewrite HA; reflexivity);
    unfold wput_group; rewrite Hp; cbn [Z.eqb]; rewrite !Z2Nat.id by lia;
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))));
    first [ eassumption | rewrite !length_app; cbn [length]; lia ] ).
Qed.

Lemma ci_loop : forall (i : nat) (t : Z) (ra1 x5 x11 x12 x13 x14 x15 x16 x17 : word) (junk : list byte)
    (mm : word -> option byte) (Q : machine_state -> Prop),
  t = 11 - Z.of_nat i -> 0 <= t ->
  x11 = Z_to_bv 64 (3 * w) -> x12 = Z_to_bv 64 (bv_unsigned sp + (2 + bo)) -> x13 = Z_to_bv 64 (e + ci_G t + 5) ->
  x14 = Z_to_bv 64 (v + 48) -> x15 = Z_to_bv 64 (v + 4 * t) ->
  ci_mem mm (slot_write_upto w slot vbs bs (Z.to_nat t)) junk ->
  (forall (x5' x13' x15' x16' x17' : word) (junk' : list byte) (mm' : word -> option byte),
     ci_mem mm' (slot_write_upto w slot vbs bs 12) junk' ->
     evt rsegs Q (MS (mkR ra1 sp gp tp x5' t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 n) (Z_to_bv 64 w) x11 x12 x13' x14 x15'
       x16' x17' (Z_to_bv 64 v) (Z_to_bv 64 slot) (Z_to_bv 64 e) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x13184) fc None mm' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra1 sp gp tp x5 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 n) (Z_to_bv 64 w) x11 x12 x13 x14 x15 x16 x17
       (Z_to_bv 64 v) (Z_to_bv 64 slot) (Z_to_bv 64 e) (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x13100) fc None mm (seg_rom rsegs)).
Proof using All.
  induction i as [|i IH]; intros t ra1 x5 x11 x12 x13 x14 x15 x16 x17 junk mm Q Et Ht -> -> -> -> -> HM K.
  - cbn [Z.of_nat] in Et.
    apply (ci_iter t ra1 x5 x16 x17 junk mm Q ltac:(lia) HM).
    intros x5' x13' x15' x16' x17' junk' mm' -> -> HM'.
    replace (v + 4 * (t + 1)) with (v + 48) by lia.
    step. rewrite bv_eqb_refl. cbn [negb].
    replace (Z.to_nat (t + 1)) with 12%nat in HM' by lia.
    exact (K _ _ _ _ _ _ _ HM').
  - apply (ci_iter t ra1 x5 x16 x17 junk mm Q ltac:(lia) HM).
    intros x5' x13' x15' x16' x17' junk' mm' -> -> HM'.
    step.
    let HC := fresh "HC" in
    if_cases HC; zify_cond HC; [| exfalso; Z.div_mod_to_equations; lia].
    eapply (IH (t + 1)); [lia | lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HM'
      | exact K].
Qed.

End Loop.

(* From the return of malloc (e in a0) to the call of free(c) (0x131b8): fuzz_dup's memcpy, want_width, the w_put
   loop, rp_slot_write, bcmp; no abort is reachable. *)
Section S3.
Variable MC : memcpy_contract.
Variable WW : want_width_contract.
Variable RSW : rp_slot_write_contract.
Variable BC : bcmp_contract.
Variables (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (r8 r9 r18 r19 r20 r21 rra : word) (c e f n slot v lo : Z) (bs vbs : list byte).
Hypothesis HN : 0 <= n <= 1600.
Hypothesis HSL : -2 <= slot <= 253.
Hypothesis HCE : 4096 <= c /\ 4096 <= e /\ (c + n <= e \/ e + n <= c) /\ c + n <= bv_unsigned sp - 64 /\
  e + n <= bv_unsigned sp - 64.
Hypothesis HF : 0 <= f /\ (f + n <= e \/ e + n <= f) /\ f + n <= bv_unsigned sp - 64.
Hypothesis HVS : bv_unsigned sp + 64 <= v /\ v + 48 <= 2 ^ 64 /\ v mod 4 = 0.
Hypothesis HLO : 0 <= lo /\ lo + 64 <= bv_unsigned sp /\ e + n <= lo.
Hypothesis HL : length bs = Z.to_nat n.
Hypothesis HVL : length vbs = 48%nat.

Notation ci_W := [(bv_unsigned sp - 64, bv_unsigned sp + 8); (c, c + n); (e, e + n)].
Notation ci_FR := [C8 r21; C8 r20; C8 r19; C8 r18; C8 r9; C8 r8; C8 rra].
Notation ci_w := (want_width_model n bs slot).

Definition ci_s3_post : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x9 x18 x19 x21 t3 t4 t5 t6 m' junk',
    ms' = MS (mkR (Z_to_bv 64 0x131bc) sp gp tp t0 t1 t2 (Z_to_bv 64 c) x9 (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7 x18 x19
               (Z_to_bv 64 e) x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CI_FREE) fc None m' (seg_rom rsegs) /\
    munch ci_W m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' (bv_unsigned sp) (CB 8 junk' :: ci_FR).

(* 0x13184: got = rp_slot_write(c, n, slot, v), checked against nch > 0; bcmp(c, e, n); the call of free(c). *)
Lemma ci_fin : forall (ra x5 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (L junk : list byte)
    (m : word -> option byte),
  x20 = Z_to_bv 64 e ->
  L = (if 0 <? ci_w then slot_write_upto ci_w slot vbs bs 12 else bs) -> length L = Z.to_nat n ->
  bytes_at rsegs m e L -> bytes_at rsegs m c bs -> wr_at rsegs m c n -> bytes_at rsegs m v vbs ->
  rw_cells rsegs m (bv_unsigned sp) (CB 8 junk :: ci_FR) -> stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  munch ci_W m0 m -> wmono rsegs m0 m ->
  evt rsegs ci_s3_post
    (MS (mkR ra sp gp tp x5 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 n) (Z_to_bv 64 ci_w) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 v) (Z_to_bv 64 slot) x20 (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13184) fc None m (seg_rom rsegs)).
Proof using All.
  intros ra x5 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 L junk m -> EL HLL HBe HBc HWc HBv FR ST HI MU WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (want_width_cases n bs slot) as WC.
  assert (CGM : rp_slot_width_model n bs slot = ci_w) by (apply check_gate.cg_models; lia).
  assert (Hw : -1 <= ci_w <= 40) by lia.
  step. rewrite want_width.ww_slt by lia.
  do 5 step.
  eapply evt_cut; [eapply (RSW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs vbs lo) |].
  all: ci_usub.
  { exact HI. }
  { exact ST. }
  { unfold RP_SLOT_WRITE_STACK. lia. }
  { lia. }
  { exact HBc. }
  { exact HL. }
  { exact HWc. }
  { exact HBv. }
  { exact HVL. }
  1-5: unfold RP_SLOT_WRITE_STACK; lia.
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 &
    MI1 & ST1 & HB1).
  ci_ret. ci_usub_in MU1. ci_usub_in HB1.
  rewrite check_gate.cg_signed in HB1 |- * by lia.
  clear ST HI. rename ST1 into ST. rename MI1 into HI.
  unfold RP_SLOT_WRITE_STACK in MU1.
  ci_xport rsegs m m1 MU1 WM1.
  assert (EQ : (if rp_slot_width_model n bs slot <? 0 then 0 else 1) = Z.b2z (0 <? ci_w)).
  { rewrite CGM. destruct WC as [E|(E1 & _)]; [rewrite E; reflexivity|].
    rewrite (proj2 (Z.ltb_ge ci_w 0)) by lia. rewrite (proj2 (Z.ltb_lt 0 ci_w)) by lia. reflexivity. }
  rewrite EQ.
  step. rewrite bv_eqb_refl. cbn [negb].
  do 4 step.
  eapply evt_cut; [eapply BC with (ls := rp_slot_write_bytes n bs slot vbs) (rs := L) (v := 0) (m := m1) |].
  { ci_usub. exact HB1. }
  { ci_usub. eassumption. }
  { ci_usub. assert (EL' : rp_slot_write_bytes n bs slot vbs = L).
    { rewrite EL. unfold rp_slot_write_bytes. rewrite CGM. destruct WC as [E|(E1 & _)].
      - rewrite E. reflexivity.
      - rewrite (proj2 (Z.ltb_ge ci_w 0)) by lia. rewrite (proj2 (Z.ltb_lt 0 ci_w)) by lia. reflexivity. }
    rewrite EL'. apply check_mute.CMSeg.cm_memcmp_prefix; [lia | lia | reflexivity]. }
  { exact HI. }
  intros ms3 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & MI3 &
    HB3 & HF3).
  ci_ret.
  ci_xport rsegs m1 m3 MU3 WM3.
  step. if_false.
  do 2 step.
  apply evt_done. unfold ci_s3_post. do 20 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma ci_tail : forall (ra x5 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (junk : list byte)
    (m : word -> option byte),
  x20 = Z_to_bv 64 e ->
  bytes_at rsegs m f bs -> bytes_at rsegs m c bs -> wr_at rsegs m c n -> bytes_at rsegs m e bs -> wr_at rsegs m e n ->
  bytes_at rsegs m v vbs -> rw_cells rsegs m (bv_unsigned sp) (CB 8 junk :: ci_FR) -> stk rsegs m lo (bv_unsigned sp) ->
  mem_inv rsegs m -> munch ci_W m0 m -> wmono rsegs m0 m ->
  evt rsegs ci_s3_post
    (MS (mkR ra sp gp tp x5 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 v)
             (Z_to_bv 64 slot) x20 (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x130b4) fc None m (seg_rom rsegs)).
Proof using All.
  intros ra x5 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 junk m -> HBf HBc HWc HBe HWe HBv FR ST HI MU WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  do 4 step.
  eapply evt_cut; [eapply (WW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs slot) |].
  { ci_usub. exact HBf. }
  { ci_usub. exact HL. }
  { reflexivity. }
  { lia. }
  intros ms' (b1 & b2 & b3 & b4 & b5 & b6 & ->).
  ci_ret. ci_usub.
  pose proof (want_width_cases n bs slot) as WC.
  step.
  let HB := fresh "HB" in if_cases HB; zify_cond HB.
  - (* nch <= 0, so nch = -1: no w_put *)
    destruct WC as [Ew | (Hw1 & _)].
    2: { exfalso. apply andb_false_iff in HB. rewrite !Z.mod_small in HB by lia.
         destruct HB as [HB|HB]; apply Z.ltb_ge in HB; lia. }
    eapply (ci_fin _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 e) _ _ _ _ bs junk m eq_refl);
      first [ rewrite Ew; reflexivity | eassumption ].
  - (* the w_put loop, for the slot's 12 samples *)
    destruct WC as [Ew | (Hw1 & Hwe & Hwn & Hws)].
    { exfalso. rewrite Ew in HB1. change ((-1) mod 18446744073709551616) with 18446744073709551615 in HB1. lia. }
    do 14 step.
    assert (Hpar : (slot mod 2 = 0 /\ (if slot mod 2 =? 0 then 0 else 3) = 0) \/
                   (slot mod 2 = 1 /\ (if slot mod 2 =? 0 then 0 else 3) = 3)).
    { pose proof (Z.mod_pos_bound slot 2 ltac:(lia)). destruct (Z.eqb_spec (slot mod 2) 0); [left | right]; lia. }
    eapply (ci_loop sp gp tp t1 t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc r8 r9 r18 r19 r20 r21 rra m0 c n e f v slot
      ci_w (if slot mod 2 =? 0 then 0 else 3) lo bs vbs) with (i := 11%nat) (t := 0);
      [ lia | exact Hwe | lia | lia | exact Hpar | lia | lia | lia | exact HVL | exact HL
      | reflexivity | lia | ci_w | | | reflexivity | ci_w | | ].
    + ci_usub. rewrite par_mask by lia. f_equal. lia.
    + ci_usub. rewrite land_m2 by lia. pose proof (Z.mod_pos_bound slot 2 ltac:(lia)).
      rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. unfold ci_G. f_equal. lia.
    + exact (conj HBe (conj HL (conj HWe (conj HBc (conj HWc (conj HBv (conj FR (conj ST (conj HI (conj MU WM)))))))))).
    + intros x5' x13' x15' x16' x17' junk' mm' (HE' & HL' & HWE' & HBC' & HWC' & HV' & FR' & ST' & HI' & MU' & WM').
      eapply (ci_fin _ _ t1 t2 _ _ _ _ _ _ _ (Z_to_bv 64 e) t3 t4 t5 t6 (slot_write_upto ci_w slot vbs bs 12) junk' mm'
        eq_refl); first [ rewrite (proj2 (Z.ltb_lt 0 ci_w)) by lia; reflexivity | eassumption ].
Qed.

Lemma ci_seg3 : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (junk junke : list byte),
  bytes_at rsegs m0 f bs -> bytes_at rsegs m0 c bs -> wr_at rsegs m0 c n -> rw_cells rsegs m0 e [CB (Z.to_nat n) junke] ->
  bytes_at rsegs m0 v vbs -> rw_cells rsegs m0 (bv_unsigned sp) (CB 8 junk :: ci_FR) -> stk rsegs m0 lo (bv_unsigned sp) ->
  mem_inv rsegs m0 ->
  evt rsegs ci_s3_post
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 n) (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 v)
             (Z_to_bv 64 slot) x20 (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (if n =? 0 then 0x130ac else 0x1308c)) fc None m0 (seg_rom rsegs)).
Proof using All.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 junk junke HBf HBc HWc HJ HBv FR ST HI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (munch_refl ci_W m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  destruct (Z.eqb_spec n 0) as [Hn0|Hn0].
  - (* n = 0: fuzz_dup copies nothing *)
    step. step. let H := fresh "H" in if_cases H; zify_cond H; rewrite ?unsigned_lit in H by lia; [lia|].
    assert (Hb : bs = []) by (apply length_zero_iff_nil; rewrite HL; lia).
    eapply ci_tail; [reflexivity | exact HBf | exact HBc | exact HWc | | | exact HBv | exact FR | exact ST | exact HI
      | exact MU | exact WM].
    + rewrite Hb. apply bytes_at_nil. lia.
    + pose proof (check_mute.CMSeg.cm_wr_of_cells _ _ _ _ HJ) as W. rewrite Z2Nat.id in W by lia. exact W.
  - step. let H := fresh "H" in if_cases H; zify_cond H; rewrite ?unsigned_lit in H by lia; [lia|].
    do 4 step.
    eapply evt_cut; [eapply MC with (src := bs) (junk := junke) (m := m0) |].
    { ci_usub. exact HBf. }
    { ci_usub. exact HL. }
    { ci_usub. exact HJ. }
    { ci_usub. lia. }
    { exact HI. }
    intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
      MU1 & WM1 & MI1 & RW1 & HF1).
    ci_usub_in MU1. ci_usub_in RW1. ci_usub_in HF1.
    ci_ret.
    clear HI. rename MI1 into HI.
    pose proof (check_mute.CMSeg.cm_bytes_of_cells _ _ _ _ RW1) as HBe.
    pose proof (check_mute.CMSeg.cm_wr_of_cells _ _ _ _ RW1) as HWe. rewrite Z2Nat.id in HWe by lia.
    clear RW1 HJ.
    ci_xport rsegs m0 m1 MU1 WM1.
    step.
    eapply ci_tail; first [ reflexivity | eassumption ].
Qed.

End S3.

(* 0x131bc, free(c) returned: e in a0, restore the frame, then free(e) as a tail call. *)
Lemma ci_seg4 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (v0 v1 v2 v3 v4 v5 vra : word),
    rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 v0 v1 s4 a1 a2 a3 a4
                                       a5 a6 a7 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CI_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x131bc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk
    v0 v1 v2 v3 v4 v5 vra FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 10 step.
  check_mute.CMSeg.cm_fin.
Qed.

End CISeg.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import check_mute_c check_inject_c memcpy_c
  want_width_c rp_slot_write_c bcmp_c.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import check_mute.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import EgressGlue.
Local Open Scope Z_scope.

(* Allocator-call glue check_inject needs beyond check_mute's (eg_*, ck_blk, ck_heap_E, reused from check_mute.v;
   ck_heap_E takes an unused Z argument, a section variable of check_mute.v's Body, passed as 0 here): the stack
   below the frame for rp_slot_write (decode's crt_stk / crt_stk_norm), a frame's cells and a block's bytes moved
   between raw and normalized memory, and the block list after freeing the older of two new blocks. *)
Lemma cig_pw_del : forall (l1 l2 : list (Z * Z)) x, pairwise ranges_disjoint (l1 ++ x :: l2) ->
  pairwise ranges_disjoint (l1 ++ l2).
Proof.
  induction l1 as [|z l1 IH]; intros l2 x H; cbn in H |- *.
  - destruct H as [_ H]. exact H.
  - destruct H as [Hz H]. split; [|exact (IH l2 x H)].
    intros y Hy. apply Hz. apply eg_in_ins. exact Hy.
Qed.

(* Freeing p from l2 = e1 ++ q :: e2, where e1 ++ e2 = d1 ++ p :: d2 (p allocated before q). *)
Lemma cig_rm2 : forall (l2 e1 e2 d1 d2 b1 b2 : list (Z * Z)) (p q : Z * Z),
  pairwise ranges_disjoint l2 -> 0 < snd p ->
  l2 = e1 ++ q :: e2 -> e1 ++ e2 = d1 ++ p :: d2 -> l2 = b1 ++ p :: b2 ->
  exists c1 c2, b1 ++ b2 = c1 ++ q :: c2 /\ c1 ++ c2 = d1 ++ d2.
Proof.
  intros l2 e1 e2 d1 d2 b1 b2 p q PW Hp E1 E2 E3.
  assert (Hin : In p (e1 ++ e2)) by (rewrite E2; apply eg_in_mid).
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (in_split p e1 Hin) as (x1 & x2 & ->).
    assert (EL : l2 = x1 ++ p :: (x2 ++ q :: e2)) by (rewrite E1, <- app_assoc; reflexivity).
    assert (NI : ~ In p (x1 ++ x2 ++ q :: e2)).
    { apply (eg_notin x1 (x2 ++ q :: e2) p); [rewrite <- EL; exact PW | exact Hp]. }
    exists (x1 ++ x2), e2. split.
    + rewrite <- app_assoc. symmetry. apply (eg_rm p x1 (x2 ++ q :: e2) b1 b2 NI). rewrite <- EL, <- E3. reflexivity.
    + rewrite <- app_assoc. apply (eg_rm p x1 (x2 ++ e2) d1 d2).
      * intros H. apply NI. apply in_app_or in H. apply in_or_app. destruct H as [H|H]; [left; exact H|].
        right. apply in_app_or in H. apply in_or_app. destruct H as [H|H]; [left; exact H | right; right; exact H].
      * rewrite <- E2, <- app_assoc. reflexivity.
  - destruct (in_split p e2 Hin) as (y1 & y2 & ->).
    assert (EL : l2 = (e1 ++ q :: y1) ++ p :: y2) by (rewrite E1, <- app_assoc; reflexivity).
    assert (NI : ~ In p ((e1 ++ q :: y1) ++ y2)).
    { apply (eg_notin (e1 ++ q :: y1) y2 p); [rewrite <- EL; exact PW | exact Hp]. }
    exists e1, (y1 ++ y2). split.
    + rewrite app_comm_cons, app_assoc. symmetry. apply (eg_rm p (e1 ++ q :: y1) y2 b1 b2 NI).
      rewrite <- EL, <- E3. reflexivity.
    + rewrite app_assoc. apply (eg_rm p (e1 ++ y1) y2 d1 d2).
      * intros H. apply NI. apply in_app_or in H. apply in_or_app. destruct H as [H|H]; [|right; exact H].
        left. apply in_app_or in H. apply in_or_app. destruct H as [H|H]; [left; exact H | right; right; exact H].
      * rewrite <- E2, <- app_assoc. reflexivity.
Qed.

Section G2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.

Lemma cig_stk : img_low B -> forall m lo hi, alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at (ms_segs B) m a) -> Frame.stk (ms_segs B) m lo hi.
Proof.
  intros [_ HI] m lo hi Hlo Hhi HW. pose proof alloc_ceiling_value as Hc.
  split; [lia|]. split; [lia|]. intros a Ha.
  assert (Hw : writable_at (ms_segs B) m a) by (apply HW; lia).
  split; [exact Hw|].
  revert Hw. unfold Mem.mrd, Mem.wa, writable_at, wview.
  destruct (m (Z_to_bv 64 a)) as [b|]; intros Hw; [exists b; reflexivity|].
  rewrite MState.unsigned_lit in Hw by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:F; [|contradiction].
  exfalso. destruct (HI a seg F). lia.
Qed.

Lemma cig_stk_norm : img_low B -> forall m lo hi, Frame.stk (ms_segs B) m lo hi -> ro_agree (ms_segs B) m ->
  alloc_ceiling <= lo -> Frame.stk (ms_segs B) (normalize (ms_segs B) m) lo hi.
Proof.
  intros HI m lo hi (H1 & H2 & H) Hro Hlo. pose proof (mem_rel_normalize (ms_segs B) m Hro) as HR.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as [Hw [b Hb]].
  assert (Hra : Mem.ro_addr (ms_segs B) (Mem.wa a) = false)
    by (apply eg_ro_false; [lia | apply (eg_fs_high B HI); lia]).
  split.
  - rewrite (wview_rel_rw (ms_segs B) m _ _ HR Hra). exact Hw.
  - exists b. rewrite <- (mrd_rel (ms_segs B) m _ _ HR). exact Hb.
Qed.

Lemma cig_cells_norm : img_low B -> forall m A cs, Step.rw_cells (ms_segs B) m A cs -> ro_agree (ms_segs B) m ->
  alloc_ceiling <= A -> Step.rw_cells (ms_segs B) (normalize (ms_segs B) m) A cs.
Proof.
  intros HI m A cs [[Hwf Hb] Hw] Hro HA. pose proof (mem_rel_normalize (ms_segs B) m Hro) as HR.
  split; [split; [exact Hwf | exact (proj1 (bytes_at_rel (ms_segs B) m _ A _ HR) Hb)]|].
  pose proof Hw as (Ha & Hn & _).
  apply (wr_at_norm (ms_segs B) m _ A _ HR Hw). intros i Hi.
  apply eg_ro_false; [lia | apply (eg_fs_high B HI); lia].
Qed.

Lemma cig_cells_rel : forall m m0 A cs, mem_rel (ms_segs B) m m0 -> Step.rw_cells (ms_segs B) m0 A cs ->
  Step.rw_cells (ms_segs B) m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (proj2 (bytes_at_rel (ms_segs B) m m0 A _ HR) Hb)]|].
  exact (wr_at_rel (ms_segs B) m m0 A _ HR Hw).
Qed.

Lemma cig_wr_of_stk : forall m a k, Frame.stk (ms_segs B) m a (a + k) -> 0 <= k -> Mem.wr_at (ms_segs B) m a k.
Proof.
  intros m a k (H1 & H2 & H) Hk. split; [lia|]. split; [lia|]. intros i Hi. apply (H (a + i)). lia.
Qed.

(* Bytes above alloc_ceiling (the caller's stack), present in raw memory, read in normalized memory (as check_mute's
   eg_blk_stk for a heap block). *)
Lemma cig_stk_hi : img_low B -> forall m a k, alloc_ceiling <= a -> a + k <= 2 ^ 64 ->
  (forall i, 0 <= i < k -> present m (a + i)) -> Frame.stk (ms_segs B) (normalize (ms_segs B) m) a (a + k).
Proof.
  intros HI m a k Ha Hk H. pose proof alloc_ceiling_value as Hc.
  split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H (x - a) ltac:(lia)) as [b Hb]. replace (a + (x - a)) with x in Hb by ring.
  assert (Hr : Mem.ro_addr (ms_segs B) (Mem.wa x) = false)
    by (apply eg_ro_false; [lia | apply (eg_fs_high B HI); lia]).
  assert (E : normalize (ms_segs B) m (Mem.wa x) = Some b) by (unfold normalize; rewrite Hr; exact Hb).
  split.
  - unfold wview. rewrite E. discriminate.
  - exists b. unfold Mem.mrd. rewrite E. reflexivity.
Qed.

(* A block's bytes, kept by a callee that keeps the bytes of every block (blocks_kept). *)
Lemma cig_bytes_kept : forall L A m m' q k a bs,
  blocks_kept B L A m m' (fun _ => False) -> In (q, k) (blocks L A) -> q <= a -> a + Z.of_nat (length bs) <= q + k ->
  Mem.bytes_at (ms_segs B) m a bs -> Mem.bytes_at (ms_segs B) m' a bs.
Proof.
  intros L A m m' q k a bs HK Hin H1 H2 (Ha & Hl & H). split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite <- (H i Hi).
  pose proof (HK q k (a - q + Z.of_nat i) Hin (fun x => x) ltac:(lia)) as E.
  replace (q + (a - q + Z.of_nat i)) with (a + Z.of_nat i) in E by ring. exact E.
Qed.

End G2.

Section CI.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = 0x14010.
Hypothesis FREEPC : ms_free B = 0x13ed0.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis MC : memcpy_contract.
Hypothesis WW : want_width_contract.
Hypothesis RSW : rp_slot_write_contract.
Hypothesis BC : bcmp_contract.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (f n slot v : Z) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CHECK_INJECT_STACK L A regs mem md.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 f.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis R12 : getr regs 12 = Z_to_bv 64 slot.
Hypothesis R13 : getr regs 13 = Z_to_bv 64 v.
Hypothesis HN : 0 <= n <= 1600.
Hypothesis HSL : -2 <= slot <= 253.
Hypothesis IB : in_block L A f n.
Hypothesis HV1 : spZ regs <= v.
Hypothesis HV2 : v + 48 <= 2 ^ 64.
Hypothesis HV3 : v mod 4 = 0.
Hypothesis HVP : forall i, 0 <= i < 48 -> present mem (v + i).
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : sb_live b + 2 <= sb_cap b <= CAPMAX /\ 0 <= sb_bytes b /\ sb_bytes b + 2 * Z.max n 1 <= 2 ^ 40.

Definition ci_inv (L' : layout) (A' : astate) (m' : word -> option byte) (md' : Model) : Prop :=
  kb_mid B API CHECK_INJECT_STACK (spZ regs) L A mem md (fun _ => False) L' A' m' md' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A')) /\
  ro_agree (ms_segs B) m' /\ guard_kept B mem m'.

Definition ci_kept (r : bvmap 5 word) : Prop :=
  getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\
  getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

Definition ci_frame (m' : word -> option byte) : Prop :=
  exists junk, Step.rw_cells rsegs m' (spZ regs - 64) [Cells.CB 8 junk; Cells.C8 (getr regs 21);
    Cells.C8 (getr regs 20); Cells.C8 (getr regs 19); Cells.C8 (getr regs 18); Cells.C8 (getr regs 9);
    Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)].

Definition ci_final (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_k B (aa_MR API) CHECK_INJECT_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    blocks L' A' = blocks L A /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    guard_kept B mem mem' /\
    ro_agree (ms_segs B) mem' /\
    res_ok_slots A' b /\
    st_init_done A' = true.

Lemma ci_pre : forall Lk Ak mk mdk regsk f0 K1,
  ci_inv Lk Ak mk mdk -> spZ regsk = spZ regs - f0 -> 0 <= f0 -> 0 <= K1 -> f0 + K1 <= CHECK_INJECT_STACK ->
  spZ regsk mod 16 = 0 -> getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) -> st_init_done Ak = true ->
  call_pre_k B (aa_MR API) K1 Lk Ak regsk mk mdk.
Proof.
  intros Lk Ak mk mdk regsk f0 K1 ((M1 & W1 & B1 & _ & _ & _ & _ & _ & S1) & _) Hsp Hf HK1 HfK H16 H4 Hra Hinit.
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _ & Htp & _).
  refine (conj M1 (conj W1 (conj B1 (conj Hra (conj H16 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - lia.
  - lia.
  - intros a Ha. apply S1. left. lia.
  - rewrite H4. exact Htp.
  - intros a Ha. apply S1. right. exact Ha.
  - intros E. rewrite Hinit in E. discriminate.
Qed.

Lemma ci_inv_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  ci_inv Lk Ak mk mdk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regs - CHECK_INJECT_STACK <= spZ regsk - K2 -> spZ regsk <= spZ regs ->
  (forall a, E2 a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (length (st_regions Ak) <= length (st_regions A2))%nat ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A2)) ->
  ro_agree (ms_segs B) m2 -> guard_kept B mk m2 ->
  ci_inv L2 A2 m2 md2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 (I1 & I2 & I3 & I4 & I5) Hpost H1 H2 HE HL HU Hro Hg.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost) as [Hmid _].
  split.
  { apply (eg_drop B API _ _ _ _ _ _ (fun a => False \/ E2 a)).
    - eapply (eg_seq B API AX CT); [exact HM | exact I1 | exact Hmid | lia | lia | lia | lia | | exact I2 | exact I3].
      intros a Ha _ He. destruct (HE a He) as [Ha' _]. lia.
    - intros a [[]|He]. exact (HE a He). }
  split; [lia|]. split; [exact HU|]. split; [exact Hro|].
  intros i Hi. rewrite (Hg i Hi). exact (I5 i Hi).
Qed.

Lemma ci_inv_A : forall Lk Ak mk mdk mk' W,
  ci_inv Lk Ak mk mdk ->
  Frame.munch W mk mk' -> Frame.wmono (ms_segs B) mk mk' -> (forall x, mk x <> None -> mk' x <> None) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CHECK_INJECT_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B Lk Ak x /\
      forall p n, forall i, In (p, n) (user_blocks A) -> 0 <= i < n -> ptr_addr L p + i <> x)) ->
  ro_agree (ms_segs B) mk' ->
  ci_inv Lk Ak mk' mdk.
Proof.
  intros Lk Ak mk mdk mk' W (I1 & I2 & I3 & I4 & I5) Hm Hw Hp HW Hro.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (eg_img_low B SEGS) as HIL.
  pose proof I1 as (M1 & _).
  split.
  { apply (eg_drop B API _ _ _ _ _ _
      (fun x => False \/ (0 <= x < 2 ^ 64 /\ ~ Frame.outside W x /\ ~ (spZ regs - CHECK_INJECT_STACK <= x < spZ regs)))).
    - apply (kb_mid_tail B API HIL _ _ _ _ _ _ _ Lk Ak mk mdk mk' W); [exact I1 | exact Hm | exact Hw | exact Hp | | |].
      + intros x Hx Hs He. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso. apply He. tauto.
      + intros x Hx Ho. destruct (kb_outside_dec W x) as [Hout|Hout]; [exact Hout|]. exfalso.
        destruct (HW x ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
      + intros p n0 i Hin Hin' Hi. destruct (kb_outside_dec W (ptr_addr L p + i)) as [Hout|Hout]; [exact Hout|].
        exfalso. destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n0 HM Hin) as [Hr1 Hr2].
        destruct (HW (ptr_addr L p + i) ltac:(lia) Hout) as [Hs | (_ & _ & _ & H4)];
          [lia | exact (H4 p n0 i Hin Hi eq_refl)].
    - intros x [[]|(Hx & Ho & Hs)].
      destruct (HW x Hx Ho) as [H|(H1 & H2 & _)]; [contradiction | split; assumption]. }
  split; [exact I2|]. split; [exact I3|]. split; [exact Hro|].
  intros i Hi. rewrite <- (I5 i Hi).
  assert (Ho : owned B Lk Ak (ms_got_guard B + i))
    by (right; unfold static_owned; right; right; right; right; left; lia).
  pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho) as Hr.
  apply (mbyte_munch (ms_segs B) W mk mk'); [exact Hm | lia |].
  destruct (kb_outside_dec W (ms_got_guard B + i)) as [Hout|Hout]; [exact Hout|]. exfalso.
  destruct (HW (ms_got_guard B + i) ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
Qed.

Lemma ci_free_keep : forall Lk Ak mk mdk p n0,
  ci_inv Lk Ak mk mdk -> In (p, n0) (user_blocks Ak) -> 0 < n0 ->
  (forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr Lk p, n0) y) ->
  forall q k, In (q, k) (user_blocks A) -> q <> p.
Proof.
  intros Lk Ak mk mdk p n0 ((M1 & W1 & _ & _ & P1 & _) & _ & I3 & _) Hp Hn HD q k Hq Eq. subst q.
  pose proof (I3 p k Hq) as Hpk.
  pose proof (user_block_ptrs_NoDup Ak W1) as ND.
  pose proof (eg_fst_unique _ p k n0 ND Hpk Hp) as Ek. subst k.
  pose proof (HD _ (eg_ub L A p n0 Hq)) as D.
  rewrite (P1 p n0 Hq Hpk) in D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma ci_frame_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  ci_inv Lk Ak mk mdk -> ci_frame mk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regsk <= spZ regs - 64 -> (forall a, E2 a -> a < alloc_ceiling) ->
  ci_frame m2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 ((M1 & _) & _) (junk & FR) Hpost Hsp HE.
  pose proof Hpost as (M2 & _ & _ & _ & _ & _ & _ & Hfr & _).
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  exists junk. rewrite <- SEGS in FR |- *.
  apply (eg_cells_mb B mk m2 _ _ FR). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 64 in Hi.
  assert (HK0 : CHECK_INJECT_STACK = 8256) by reflexivity.
  assert (Hr : alloc_ceiling <= spZ regs - 64 + i < 2 ^ 64) by lia.
  destruct (Hfr (spZ regs - 64 + i)) as [E W].
  - left. exact Hr.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho). lia.
  - unfold scratch_k. lia.
  - intros He. pose proof (HE _ He). lia.
  - split; [exact E | intros Hw; apply W; exact Hw].
Qed.

Lemma ci_inv_kept : forall Lk Ak mk mdk, ci_inv Lk Ak mk mdk -> blocks_kept B L A mem mk (fun _ => False).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & _ & _ & _ & K1 & _) & _ & I3 & _) a k i Hin _ Hi.
  destruct (eg_bu L A a k Hin) as (p & Hp & <-). exact (K1 p k i Hp (I3 p k Hp) Hi).
Qed.

Lemma ci_kept_pres : forall r r', ci_kept r -> regs_preserved r r' -> ci_kept r'.
Proof.
  intros r r' (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27) Hp.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - transitivity (getr r 3); [apply (Hp 3); unfold callee_saved; lia | exact K3].
  - transitivity (getr r 4); [apply (Hp 4); unfold callee_saved; lia | exact K4].
  - transitivity (getr r 22); [apply (Hp 22); unfold callee_saved; lia | exact K22].
  - transitivity (getr r 23); [apply (Hp 23); unfold callee_saved; lia | exact K23].
  - transitivity (getr r 24); [apply (Hp 24); unfold callee_saved; lia | exact K24].
  - transitivity (getr r 25); [apply (Hp 25); unfold callee_saved; lia | exact K25].
  - transitivity (getr r 26); [apply (Hp 26); unfold callee_saved; lia | exact K26].
  - transitivity (getr r 27); [apply (Hp 27); unfold callee_saved; lia | exact K27].
Qed.

(* v's bytes, in the caller's frame above check_inject's stack, stay present: no callee writes them. *)
Lemma ci_vpres : forall Lk Ak mk mdk, ci_inv Lk Ak mk mdk -> forall i, 0 <= i < 48 -> present mk (v + i).
Proof.
  intros Lk Ak mk mdk ((M1 & _ & _ & _ & _ & _ & F1 & _) & _) i Hi.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (eg_img_low B SEGS) as HIL.
  assert (HK0 : CHECK_INJECT_STACK = 8256) by reflexivity.
  destruct (F1 (v + i)) as [E _].
  - left. lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho). lia.
  - lia.
  - intros [].
  - destruct (HVP i Hi) as [b0 Hb0].
    assert (Hfs : find_segment (ms_segs B) (v + i) 1 = None) by (apply (eg_fs_high B HIL); lia).
    unfold mbyte in E. rewrite Hb0 in E. revert E. destruct (mk (Z_to_bv 64 (v + i))) as [b1|] eqn:Hm.
    + intros _. exists b1. exact Hm.
    + intros E. rewrite (seg_rom_unmapped (ms_segs B)) in E by (rewrite MState.unsigned_lit by lia; exact Hfs).
      discriminate E.
Qed.

(* 0x131bc, free(c) returned: restore the frame, then free(e) as a tail call. *)
Lemma ci_ph5 : forall (fx7 : FPState) L1 A1 regs7 m7 md1 Q c1 c2,
  frm_zero (@fp_csr fx7) ->
  ci_inv L1 A1 m7 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = c1 ++ (Q, Z.max n 1) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A1 (sb_malloc b (Z.max n 1)) ->
  getr regs7 2 = Z_to_bv 64 (spZ regs - 64) -> getr regs7 20 = Z_to_bv 64 Q -> ci_kept regs7 ->
  ci_frame m7 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs7 (Z_to_bv 64 0x131bc) m7 (seg_rom (ms_segs B))) md1) ci_final.
Proof.
  intros fx7 L1 A1 regs7 m7 md1 Q c1 c2 Hfrm I Hinit Hb1 Hb0 Hres G2 G20 GK (junk & FR).
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_INJECT_STACK = 8256) by reflexivity.
  assert (Hk : 0 < Z.max n 1) by lia.
  pose proof I as ((M5 & W5 & B5 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m7 md1 M5) as [Hh Hlz].
  assert (USP : bv_unsigned (getr regs7 2) = spZ regs - 64) by (rewrite G2; apply MState.unsigned_lit; lia).
  eapply (eg_runA (fx := fx7) B SEGS regs7 _ m7 md1); [exact Hh | exact Hlz | | |].
  { unfold rmk. eapply CISeg.ci_seg4. rewrite USP. exact FR. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs11 -> Hg11. cbn [MState.MS ms_pc_val ms_mem].
  assert (G11a : getr regs11 1 = getr regs 1) by (rewrite Hg11; reflexivity).
  assert (G11b : getr regs11 2 = Z_to_bv 64 (bv_unsigned (getr regs7 2) + 64)) by (rewrite Hg11; reflexivity).
  rewrite USP in G11b. replace (spZ regs - 64 + 64) with (spZ regs) in G11b by lia.
  assert (G11c : getr regs11 4 = getr regs 4) by (rewrite Hg11; exact (proj1 (proj2 GK))).
  assert (G11d : getr regs11 10 = Z_to_bv 64 Q) by (rewrite Hg11; exact G20).
  assert (S11 : spZ regs11 = spZ regs) by (unfold spZ at 1; rewrite G11b; apply MState.unsigned_lit; lia).
  assert (P11 : regs_preserved regs regs11).
  { destruct GK as (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27).
    assert (Hs : getr regs11 2 = getr regs 2) by (rewrite G11b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg11; first [reflexivity | exact K3 | exact K4 | exact K22 | exact K23 | exact K24
        | exact K25 | exact K26 | exact K27]]. }
  destruct (eg_bu L1 A1 Q _ ltac:(rewrite Hb1; apply eg_in_mid)) as (q & Hq & Eq).
  assert (Hpre11 : call_pre B (aa_MR API) L1 A1 regs11 m7 md1).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 regs11 m7 md1)).
    apply (ci_pre L1 A1 m7 md1 regs11 0 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia | rewrite S11; exact H16 | exact G11c | rewrite G11a; exact Hra
      | exact Hinit]. }
  replace (Z_to_bv 64 CISeg.CI_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply SR_bind.
  { apply (FREE fx7 L1 A1 regs11 m7 md1 q (Z.max n 1) (sb_malloc b (Z.max n 1)) Hpre11 I4 Hq).
    - rewrite G11d, Eq. reflexivity.
    - exact Hres. }
  intros c' (L6 & A6 & regs12 & m12 & md6 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro6 & Hgk6 & Hub6 &
    Hinit6 & Hlen6 & Hres6).
  apply call_post_k_alloc in Hpost.
  rewrite Eq in Hd1.
  assert (PW5 : pairwise ranges_disjoint (c1 ++ (Q, Z.max n 1) :: c2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M5)).
  assert (ND5 : ~ In (Q, Z.max n 1) (c1 ++ c2)) by (apply (eg_notin c1 c2 _ PW5); cbn; lia).
  assert (Hb6 : blocks L6 A6 = blocks L A).
  { rewrite Hd2, Hb0. symmetry. apply (eg_rm (Q, Z.max n 1) c1 c2 d1 d2 ND5). rewrite <- Hb1. exact Hd1. }
  assert (HD5 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L1 q, Z.max n 1) y).
  { intros y Hy. rewrite Eq. apply (eg_pw_mid c1 c2 _ y PW5). rewrite <- Hb0. exact Hy. }
  assert (HU6 : forall q' k, In (q', k) (user_blocks A) -> In (q', k) (user_blocks A6)).
  { intros q' k Hq'. apply Hub6; [exact (I3 q' k Hq') | exact (ci_free_keep L1 A1 m7 md1 q _ I Hq ltac:(lia) HD5 q' k Hq')]. }
  assert (I6 : ci_inv L6 A6 m12 md6).
  { apply (ci_inv_call L1 A1 m7 md1 regs11 ALLOC_STACK _ L6 A6 regs12 m12 md6 I Hpost);
      [rewrite S11, HK0; unfold ALLOC_STACK; lia | lia | exact (ck_heap_E B API AX 0 L1 A1 m7 md1 q _ M5 Hq) | exact Hlen6
      | exact HU6 | exact Hro6 | exact Hgk6]. }
  apply SR_ret. exists fx7, L6, A6, regs12, m12, md6.
  split; [rewrite G11a; reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I6 as (I6a & _). apply (kb_post B API); [exact I6a|].
    exact (kb_preserved_trans _ _ _ P11 (proj2 (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost))). }
  split; [exact Hb6|].
  split; [exact (ci_inv_kept _ _ _ _ I6)|].
  destruct I6 as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres6; exact Hres6 | exact (Hinit6 Hinit)].
Qed.

(* At free, called from 0x131b8 for c, the older of the two blocks. *)
Lemma ci_ph4 : forall (fx7 : FPState) L2 A2 regs8 m8 md2 P Q c1 c2 e1 e2,
  frm_zero (@fp_csr fx7) ->
  ci_inv L2 A2 m8 md2 -> st_init_done A2 = true ->
  blocks L2 A2 = e1 ++ (Q, Z.max n 1) :: e2 -> e1 ++ e2 = c1 ++ (P, Z.max n 1) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A2 (sb_malloc (sb_malloc b (Z.max n 1)) (Z.max n 1)) ->
  getr regs8 1 = Z_to_bv 64 0x131bc -> getr regs8 2 = Z_to_bv 64 (spZ regs - 64) -> getr regs8 10 = Z_to_bv 64 P ->
  getr regs8 20 = Z_to_bv 64 Q -> ci_kept regs8 -> ci_frame m8 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs8 (Z_to_bv 64 CISeg.CI_FREE) m8 (seg_rom (ms_segs B))) md2) ci_final.
Proof.
  intros fx7 L2 A2 regs8 m8 md2 P Q c1 c2 e1 e2 Hfrm I Hinit Hb2 He Hb0 Hres G1 G2 G10 G20 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_INJECT_STACK = 8256) by reflexivity.
  assert (Hk : 0 < Z.max n 1) by lia.
  pose proof I as ((M2 & W2 & B2 & _) & I2 & I3 & I4 & I5).
  assert (S8 : spZ regs8 = spZ regs - 64) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  assert (InP : In (P, Z.max n 1) (blocks L2 A2)) by (rewrite Hb2; apply eg_in_ins; rewrite He; apply eg_in_mid).
  destruct (eg_bu L2 A2 P _ InP) as (p & Hp & Ep).
  assert (Hpre8 : call_pre B (aa_MR API) L2 A2 regs8 m8 md2).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L2 A2 regs8 m8 md2)).
    apply (ci_pre L2 A2 m8 md2 regs8 64 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S8; replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj1 (proj2 GK)) | rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  replace (Z_to_bv 64 CISeg.CI_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply SR_bind.
  { apply (FREE fx7 L2 A2 regs8 m8 md2 p (Z.max n 1) (sb_malloc (sb_malloc b (Z.max n 1)) (Z.max n 1)) Hpre8 I4 Hp).
    - rewrite G10, Ep. reflexivity.
    - exact Hres. }
  intros c' (L5 & A5 & regs10 & m10 & md5 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro5 & Hgk5 & Hub5 &
    Hinit5 & Hlen5 & Hres5).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp10 & _).
  rewrite Ep in Hd1.
  assert (PW2 : pairwise ranges_disjoint (blocks L2 A2)) by exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M2).
  destruct (cig_rm2 (blocks L2 A2) e1 e2 c1 c2 d1 d2 (P, Z.max n 1) (Q, Z.max n 1) PW2 ltac:(cbn; lia) Hb2 He Hd1)
    as (c1' & c2' & Hc1 & Hc2).
  assert (Hb5 : blocks L5 A5 = c1' ++ (Q, Z.max n 1) :: c2') by (rewrite Hd2; exact Hc1).
  assert (PWe : pairwise ranges_disjoint (c1 ++ (P, Z.max n 1) :: c2)).
  { rewrite <- He. apply (cig_pw_del e1 e2 (Q, Z.max n 1)). rewrite <- Hb2. exact PW2. }
  assert (HD2 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L2 p, Z.max n 1) y).
  { intros y Hy. rewrite Ep. apply (eg_pw_mid c1 c2 _ y PWe). rewrite <- Hb0. exact Hy. }
  assert (HU5 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A5)).
  { intros q k Hq. apply Hub5; [exact (I3 q k Hq) | exact (ci_free_keep L2 A2 m8 md2 p _ I Hp ltac:(lia) HD2 q k Hq)]. }
  assert (I5' : ci_inv L5 A5 m10 md5).
  { apply (ci_inv_call L2 A2 m8 md2 regs8 ALLOC_STACK _ L5 A5 regs10 m10 md5 I Hpost);
      [rewrite S8, HK0; unfold ALLOC_STACK; lia | lia | exact (ck_heap_E B API AX 0 L2 A2 m8 md2 p _ M2 Hp) | exact Hlen5
      | exact HU5 | exact Hro5 | exact Hgk5]. }
  assert (FR5 : ci_frame m10).
  { apply (ci_frame_call L2 A2 m8 md2 regs8 ALLOC_STACK _ L5 A5 regs10 m10 md5 I FR Hpost); [lia |].
    intros a Ha. exact (proj1 (ck_heap_E B API AX 0 L2 A2 m8 md2 p _ M2 Hp a Ha)). }
  rewrite G1.
  apply (ci_ph5 fx7 L5 A5 regs10 m10 md5 Q c1' c2' Hfrm I5' (Hinit5 Hinit) Hb5).
  - rewrite Hc2. exact Hb0.
  - rewrite sb_free_malloc in Hres5. exact Hres5.
  - transitivity (getr regs8 2); [apply (Hp10 2); unfold callee_saved; lia | exact G2].
  - transitivity (getr regs8 20); [apply (Hp10 20); unfold callee_saved; lia | exact G20].
  - exact (ci_kept_pres regs8 regs10 GK Hp10).
  - exact FR5.
Qed.

(* At 0x1308c / 0x130ac, malloc returned e: the segment to the call of free(c), in normalized memory. *)
Lemma ci_ph3 : forall L2 A2 regs3 m3 md2 P Q c1 c2 e1 e2 bs,
  ci_inv L2 A2 m3 md2 -> st_init_done A2 = true ->
  blocks L2 A2 = e1 ++ (Q, Z.max n 1) :: e2 -> e1 ++ e2 = c1 ++ (P, Z.max n 1) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A2 (sb_malloc (sb_malloc b (Z.max n 1)) (Z.max n 1)) ->
  getr regs3 2 = Z_to_bv 64 (spZ regs - 64) -> getr regs3 8 = Z_to_bv 64 P -> getr regs3 9 = Z_to_bv 64 n ->
  getr regs3 10 = Z_to_bv 64 Q -> getr regs3 18 = Z_to_bv 64 v -> getr regs3 19 = Z_to_bv 64 slot ->
  getr regs3 21 = Z_to_bv 64 f -> ci_kept regs3 -> ci_frame m3 ->
  length bs = Z.to_nat n -> Mem.bytes_at rsegs m3 P bs -> Mem.bytes_at rsegs m3 f bs ->
  SR (ms_segs B) (mkCfg (mkst regs3 (Z_to_bv 64 (if n =? 0 then 0x130ac else 0x1308c)) m3 (seg_rom (ms_segs B)))
    md2) ci_final.
Proof.
  intros L2 A2 regs3 m3 md2 P Q c1 c2 e1 e2 bs I Hinit Hb2 He Hb0 Hres G2 G8 G9 G10 G18 G19 G21 GK FR HLb HBc HBf.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_INJECT_STACK = 8256) by reflexivity.
  pose proof I as ((M2 & W2 & B2 & _ & _ & _ & _ & _ & S2) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L2 A2 m3 md2 M2) as [Hh Hlz].
  pose proof (eg_img_low B SEGS) as HIL.
  assert (Hro' : ro_agree rsegs m3) by (rewrite <- SEGS; exact I4).
  assert (USP : bv_unsigned (getr regs3 2) = spZ regs - 64) by (rewrite G2; apply MState.unsigned_lit; lia).
  assert (PW2 : pairwise ranges_disjoint (e1 ++ (Q, Z.max n 1) :: e2))
    by (rewrite <- Hb2; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M2)).
  assert (PWe : pairwise ranges_disjoint (c1 ++ (P, Z.max n 1) :: c2)) by (rewrite <- He; exact (cig_pw_del e1 e2 _ PW2)).
  assert (InQ : In (Q, Z.max n 1) (blocks L2 A2)) by (rewrite Hb2; apply eg_in_mid).
  assert (InPe : In (P, Z.max n 1) (e1 ++ e2)) by (rewrite He; apply eg_in_mid).
  assert (InP : In (P, Z.max n 1) (blocks L2 A2)) by (rewrite Hb2; apply eg_in_ins; exact InPe).
  pose proof IB as (q & k & Hq & Hq1 & Hq2).
  assert (Hqc : In (q, k) (c1 ++ c2)) by (rewrite <- Hb0; exact Hq).
  assert (Hqe : In (q, k) (e1 ++ e2)) by (rewrite He; apply eg_in_ins; exact Hqc).
  assert (HqL : In (q, k) (blocks L2 A2)) by (rewrite Hb2; apply eg_in_ins; exact Hqe).
  destruct (ck_blk B API AX L2 A2 m3 md2 Q _ M2 InQ) as (HQ1 & HQ2 & HQ3 & HQi).
  destruct (ck_blk B API AX L2 A2 m3 md2 P _ M2 InP) as (HP1 & HP2 & HP3 & HPi).
  destruct (ck_blk B API AX L2 A2 m3 md2 q k M2 HqL) as (Hk1 & Hk2 & _ & Hki).
  pose proof (eg_pw_mid e1 e2 _ _ PW2 InPe) as DQP. unfold ranges_disjoint in DQP. cbn [fst snd] in DQP.
  pose proof (eg_pw_mid e1 e2 _ _ PW2 Hqe) as DQq. unfold ranges_disjoint in DQq. cbn [fst snd] in DQq.
  pose proof (eg_pw_mid c1 c2 _ _ PWe Hqc) as DPq. unfold ranges_disjoint in DPq. cbn [fst snd] in DPq.
  assert (STQ : Frame.stk rsegs (normalize rsegs m3) Q (Q + n)).
  { rewrite <- SEGS. apply (eg_blk_stk B SEGS m3 Q n I4); [lia | lia |].
    intros i Hi. destruct (HQi i ltac:(lia)) as (X1 & X2 & _). split; assumption. }
  assert (STP : Frame.stk rsegs (normalize rsegs m3) P (P + n)).
  { rewrite <- SEGS. apply (eg_blk_stk B SEGS m3 P n I4); [lia | lia |].
    intros i Hi. destruct (HPi i ltac:(lia)) as (X1 & X2 & _). split; assumption. }
  assert (STv : Frame.stk rsegs (normalize rsegs m3) v (v + 48)).
  { rewrite <- SEGS. apply (cig_stk_hi B HIL m3 v 48); [lia | lia | exact (ci_vpres L2 A2 m3 md2 I)]. }
  destruct (Frame.stk_bytes rsegs _ v (v + 48) STv ltac:(lia)) as (vbs & HLv & HBv).
  replace (v + 48 - v) with 48 in HLv by ring.
  destruct (Frame.stk_carve rsegs _ Q (Q + n) (Z.to_nat n) STQ ltac:(lia)) as (_ & junke & HJ).
  rewrite Z2Nat.id in HJ by lia. replace (Q + n - n) with Q in HJ by ring.
  assert (HWc : Mem.wr_at rsegs (normalize rsegs m3) P n)
    by (rewrite <- SEGS; apply cig_wr_of_stk; [rewrite SEGS; exact STP | lia]).
  assert (HBc' : Mem.bytes_at rsegs (normalize rsegs m3) P bs) by (apply bytes_at_normalize; [exact Hro' | exact HBc]).
  assert (HBf' : Mem.bytes_at rsegs (normalize rsegs m3) f bs) by (apply bytes_at_normalize; [exact Hro' | exact HBf]).
  destruct FR as (junk & FRc).
  assert (FRn : Step.rw_cells rsegs (normalize rsegs m3) (bv_unsigned (getr regs3 2)) [Cells.CB 8 junk;
    Cells.C8 (getr regs 21); Cells.C8 (getr regs 20); Cells.C8 (getr regs 19); Cells.C8 (getr regs 18);
    Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)]).
  { rewrite USP, <- SEGS. apply (cig_cells_norm B HIL); [rewrite SEGS; exact FRc | exact I4 | lia]. }
  assert (STs : Frame.stk rsegs (normalize rsegs m3) (spZ regs - 128) (bv_unsigned (getr regs3 2))).
  { rewrite USP, <- SEGS. apply (cig_stk_norm B HIL); [| exact I4 | lia].
    apply (cig_stk B HIL); [lia | lia |]. intros a Ha. apply S2. left. lia. }
  eapply (eg_runN B SEGS regs3 _ m3 md2); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G8, G9, G10, G18, G19, G21.
    eapply (CISeg.ci_seg3 MC WW RSW BC) with (bs := bs) (vbs := vbs) (lo := spZ regs - 128) (c := P) (e := Q) (f := f)
      (n := n) (slot := slot) (v := v);
      first [ exact (mem_inv_normalize rsegs m3) | eassumption | lia
            | rewrite USP; repeat split; lia ]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & x9' & x18' & x19' & x21' & t3' & t4' & t5' &
      t6' & m' & junk' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & x9' & x18' & x19' & x21' & t3' & t4' &
    t5' & t6' & m' & junk' & -> & MU & WM & FRm) Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR). cbn [ms_mem MState.MS] in HR.
  rewrite USP in MU, FRm.
  set (W := [(spZ regs - 64 - 64, spZ regs - 64 + 8); (P, P + n); (Q, Q + n)]) in MU.
  pose proof (mem_rel_normalize rsegs m3 Hro') as HR6.
  pose proof (munch_rel rsegs _ m3 _ (ms_mem ms) m' HR6 HR Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m3 _ (ms_mem ms) m' HR6 HR Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m3 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (PRES : forall x, m3 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (eg_pres B m3 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    unfold W in Hout. cbn [Frame.outside] in Hout.
    assert (C : (spZ regs - 128 <= bv_unsigned x < spZ regs - 56) \/ (P <= bv_unsigned x < P + n) \/
                (Q <= bv_unsigned x < Q + n)) by lia.
    destruct C as [C|[C|C]].
    - apply (eg_fs_high B HIL). lia.
    - apply (eg_fs_none B SEGS). destruct (HPi (bv_unsigned x - P) ltac:(lia)) as (_ & Hn & _).
      replace (P + (bv_unsigned x - P)) with (bv_unsigned x) in Hn by ring. exact Hn.
    - apply (eg_fs_none B SEGS). destruct (HQi (bv_unsigned x - Q) ltac:(lia)) as (_ & Hn & _).
      replace (Q + (bv_unsigned x - Q)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CHECK_INJECT_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L2 A2 x /\
      forall p n0 i, In (p, n0) (user_blocks A) -> 0 <= i < n0 -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. unfold W in Hout. cbn [Frame.outside] in Hout.
    assert (C : (spZ regs - 128 <= x < spZ regs - 56) \/ (P <= x < P + n) \/ (Q <= x < Q + n)) by lia.
    destruct C as [C|[C|C]].
    - left. lia.
    - right. destruct (HPi (x - P) ltac:(lia)) as (_ & Hn1 & Hn2). replace (P + (x - P)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p n0 i Hp Hi E.
      assert (Y1 : In (ptr_addr L p, n0) (c1 ++ c2)) by (rewrite <- Hb0; exact (eg_ub L A p n0 Hp)).
      pose proof (eg_pw_mid c1 c2 _ _ PWe Y1) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
    - right. destruct (HQi (x - Q) ltac:(lia)) as (_ & Hn1 & Hn2). replace (Q + (x - Q)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p n0 i Hp Hi E.
      assert (Y1 : In (ptr_addr L p, n0) (e1 ++ e2)) by (rewrite He; apply eg_in_ins; rewrite <- Hb0;
        exact (eg_ub L A p n0 Hp)).
      pose proof (eg_pw_mid e1 e2 _ _ PW2 Y1) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia. }
  pose proof (ci_inv_A L2 A2 m3 md2 (ms_mem ms) W I MU7 WM7 PRES HWW RO7) as I7.
  assert (FR7 : ci_frame (ms_mem ms)).
  { exists junk'. rewrite <- SEGS in FRm, HR |- *.
    exact (cig_cells_rel B (ms_mem ms) m' _ _ HR FRm). }
  destruct GK as (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27).
  apply (ci_ph4 (mkFP fp_regs fp_csr) L2 A2 regs7 (ms_mem ms) md2 P Q c1 c2 e1 e2 FRM I7 Hinit Hb2 He Hb0 Hres);
    [rewrite Hg7; reflexivity | rewrite Hg7; exact G2 | rewrite Hg7; reflexivity | rewrite Hg7; reflexivity | | exact FR7].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); rewrite Hg7;
    first [exact K3 | exact K4 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26 | exact K27].
Qed.

(* 0x13068, malloc returned c: fuzz_dup's memcpy, in normalized memory, then malloc for e. *)
Lemma ci_ph2 : forall L1 A1 regs2 m2 md1 P c1 c2,
  ci_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = c1 ++ (P, Z.max n 1) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A1 (sb_malloc b (Z.max n 1)) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 64) -> getr regs2 9 = Z_to_bv 64 n -> getr regs2 10 = Z_to_bv 64 P ->
  getr regs2 18 = Z_to_bv 64 v -> getr regs2 19 = Z_to_bv 64 slot -> getr regs2 20 = Z_to_bv 64 (Z.max n 1) ->
  getr regs2 21 = Z_to_bv 64 f -> ci_kept regs2 -> ci_frame m2 ->
  SR (ms_segs B) (mkCfg (mkst regs2 (Z_to_bv 64 0x13068) m2 (seg_rom (ms_segs B))) md1) ci_final.
Proof.
  intros L1 A1 regs2 m2 md1 P c1 c2 I Hinit Hb1 Hb0 Hres G2 G9 G10 G18 G19 G20 G21 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_INJECT_STACK = 8256) by reflexivity.
  pose proof I as ((M1 & W1 & B1 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  assert (Hro' : ro_agree rsegs m2) by (rewrite <- SEGS; exact I4).
  assert (PW1 : pairwise ranges_disjoint (c1 ++ (P, Z.max n 1) :: c2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1)).
  assert (InP : In (P, Z.max n 1) (blocks L1 A1)) by (rewrite Hb1; apply eg_in_mid).
  destruct (ck_blk B API AX L1 A1 m2 md1 P _ M1 InP) as (HP1 & HP2 & HP3 & HPi).
  pose proof IB as (q & k & Hq & Hq1 & Hq2).
  assert (Hq' : In (q, k) (c1 ++ c2)) by (rewrite <- Hb0; exact Hq).
  assert (HqL : In (q, k) (blocks L1 A1)) by (rewrite Hb1; apply eg_in_ins; exact Hq').
  destruct (ck_blk B API AX L1 A1 m2 md1 q k M1 HqL) as (HQ1 & HQ2 & _ & HQi).
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
  eapply (eg_runN B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | exact Hro' | | |].
  { pose proof YM05.alloc_ceiling_lt as Hc47.
    unfold rmk. rewrite G9, G10, G18, G19, G20, G21.
    eapply (CISeg.ci_seg2 MC) with (f := f) (n := n) (c := P) (bs := bs) (slot := slot) (v := v);
      first [ eassumption | exact (mem_inv_normalize rsegs m2) | lia | destruct DPQ; [left | right]; lia ]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
    MU & WM & HBc7 & HBf7) Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR). cbn [ms_mem MState.MS] in HR.
  set (W := [(P, P + n)]) in MU.
  pose proof (mem_rel_normalize rsegs m2 Hro') as HR6.
  pose proof (munch_rel rsegs _ m2 _ (ms_mem ms) m' HR6 HR Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m2 _ (ms_mem ms) m' HR6 HR Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m2 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (HBc8 : Mem.bytes_at rsegs (ms_mem ms) P bs) by exact (proj2 (bytes_at_rel rsegs _ _ P bs HR) HBc7).
  assert (HBf8 : Mem.bytes_at rsegs (ms_mem ms) f bs) by exact (proj2 (bytes_at_rel rsegs _ _ f bs HR) HBf7).
  assert (PRES : forall x, m2 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (eg_pres B m2 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    unfold W in Hout. cbn [Frame.outside] in Hout.
    apply (eg_fs_none B SEGS). destruct (HPi (bv_unsigned x - P) ltac:(lia)) as (_ & Hn & _).
    replace (P + (bv_unsigned x - P)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CHECK_INJECT_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L1 A1 x /\
      forall p n0 i, In (p, n0) (user_blocks A) -> 0 <= i < n0 -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. unfold W in Hout. cbn [Frame.outside] in Hout. right.
    destruct (HPi (x - P) ltac:(lia)) as (_ & Hn1 & Hn2). replace (P + (x - P)) with x in Hn1, Hn2 by ring.
    split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
    intros p n0 i Hp Hi E.
    assert (Y1 : In (ptr_addr L p, n0) (c1 ++ c2)) by (rewrite <- Hb0; exact (eg_ub L A p n0 Hp)).
    pose proof (eg_pw_mid c1 c2 _ _ PW1 Y1) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia. }
  pose proof (ci_inv_A L1 A1 m2 md1 (ms_mem ms) W I MU7 WM7 PRES HWW RO7) as I7.
  assert (FR7 : ci_frame (ms_mem ms)).
  { destruct FR as (junk' & FRc). exists junk'. rewrite <- SEGS in FRc |- *.
    apply (eg_cells_keep B m2 (ms_mem ms) _ _ FRc). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 64 in Hi.
    apply MU7. rewrite MState.unsigned_lit by lia. unfold W. cbn [Frame.outside]. repeat split; lia. }
  (* malloc(n ? n : 1) for e, from 0x13088 or 0x130a8 *)
  assert (G7a : getr regs7 1 = Z_to_bv 64 (if n =? 0 then 0x130ac else 0x1308c)) by (rewrite Hg7; reflexivity).
  assert (G7b : getr regs7 2 = Z_to_bv 64 (spZ regs - 64)) by (rewrite Hg7; exact G2).
  assert (G7c : getr regs7 10 = Z_to_bv 64 (Z.max n 1)) by (rewrite Hg7; reflexivity).
  assert (G7d : getr regs7 8 = Z_to_bv 64 P) by (rewrite Hg7; reflexivity).
  assert (G7e : getr regs7 9 = Z_to_bv 64 n) by (rewrite Hg7; reflexivity).
  assert (G7f : getr regs7 18 = Z_to_bv 64 v) by (rewrite Hg7; reflexivity).
  assert (G7g : getr regs7 19 = Z_to_bv 64 slot) by (rewrite Hg7; reflexivity).
  assert (G7h : getr regs7 21 = Z_to_bv 64 f) by (rewrite Hg7; reflexivity).
  assert (K7 : ci_kept regs7).
  { destruct GK as (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); rewrite Hg7;
      first [exact K3 | exact K4 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26 | exact K27]. }
  assert (S7 : spZ regs7 = spZ regs - 64) by (unfold spZ at 1; rewrite G7b; apply MState.unsigned_lit; lia).
  assert (Hpre7 : call_pre B (aa_MR API) L1 A1 regs7 (ms_mem ms) md1).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 regs7 (ms_mem ms) md1)).
    apply (ci_pre L1 A1 (ms_mem ms) md1 regs7 64 ALLOC_STACK I7); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S7; replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj1 (proj2 K7))
      | rewrite G7a; destruct (n =? 0); unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  assert (Hroom : room_slots (sb_malloc b (Z.max n 1)) (Z.max n 1)).
  { apply room_slots_small; cbn [sb_malloc sb_live sb_cap sb_bytes]; lia. }
  cbn [ms_pc_val ms_fregs ms_fcsr MState.MS].
  change (@mkst (mkFP (@fp_regs fx) (@fp_csr fx))) with (@mkst fx).
  replace (Z_to_bv 64 CISeg.CI_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply SR_bind.
  { exact (MALLOC L1 A1 regs7 (ms_mem ms) md1 (Z.max n 1) (sb_malloc b (Z.max n 1)) Hpre7 RO7 G7c Hres Hroom). }
  intros c' (L2 & A2 & regs8 & m8 & md2 & res & -> & Hpost & G8 & _ & _ & _ & (d1 & d2 & Hb2 & Hb1') & Hkept2 & Hro2 &
    Hgk2 & HU2 & Hinit2 & Hlen2 & Hres2).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp8 & _).
  assert (I2' : ci_inv L2 A2 m8 md2).
  { apply (ci_inv_call L1 A1 (ms_mem ms) md1 regs7 ALLOC_STACK _ L2 A2 regs8 m8 md2 I7 Hpost);
      [rewrite S7, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen2
      | intros q' k' Hq''; exact (HU2 q' k' (I3 q' k' Hq'')) | exact Hro2 | exact Hgk2]. }
  assert (FR2 : ci_frame m8).
  { apply (ci_frame_call L1 A1 (ms_mem ms) md1 regs7 ALLOC_STACK _ L2 A2 regs8 m8 md2 I7 FR7 Hpost); [lia | intros a []]. }
  assert (HBc9 : Mem.bytes_at rsegs m8 P bs).
  { rewrite <- SEGS. apply (cig_bytes_kept B L1 A1 (ms_mem ms) m8 P (Z.max n 1) P bs); [| exact InP | lia | lia |].
    - exact Hkept2.
    - rewrite SEGS. exact HBc8. }
  assert (HBf9 : Mem.bytes_at rsegs m8 f bs).
  { rewrite <- SEGS. apply (cig_bytes_kept B L1 A1 (ms_mem ms) m8 q k f bs); [| exact HqL | lia | lia |].
    - exact Hkept2.
    - rewrite SEGS. exact HBf8. }
  rewrite G7a.
  apply (ci_ph3 L2 A2 regs8 m8 md2 P res c1 c2 d1 d2 bs I2' Hinit2 Hb2).
  - rewrite <- Hb1'. exact Hb1.
  - exact Hb0.
  - exact Hres2.
  - transitivity (getr regs7 2); [apply (Hp8 2); unfold callee_saved; lia | exact G7b].
  - transitivity (getr regs7 8); [apply (Hp8 8); unfold callee_saved; lia | exact G7d].
  - transitivity (getr regs7 9); [apply (Hp8 9); unfold callee_saved; lia | exact G7e].
  - exact G8.
  - transitivity (getr regs7 18); [apply (Hp8 18); unfold callee_saved; lia | exact G7f].
  - transitivity (getr regs7 19); [apply (Hp8 19); unfold callee_saved; lia | exact G7g].
  - transitivity (getr regs7 21); [apply (Hp8 21); unfold callee_saved; lia | exact G7h].
  - exact (ci_kept_pres regs7 regs8 K7 Hp8).
  - exact FR2.
  - exact HLb.
  - exact HBc9.
  - exact HBf9.
Qed.

(* Entry: the frame, then malloc(n ? n : 1) for c. *)
Lemma ci_entry :
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 CHECK_INJECT) mem (seg_rom (ms_segs B))) md) ci_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_INJECT_STACK = 8256) by reflexivity.
  pose proof (eg_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  pose proof IB as (q & k & Hq & Hq1 & Hq2).
  destruct (ck_blk B API AX L A mem md q k HM Hq) as (HQ1 & HQ2 & _).
  assert (I0 : ci_inv L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p n0 Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : Frame.stk rsegs mem (spZ regs - CHECK_INJECT_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CHECK_INJECT_STACK L A regs mem md PRE ltac:(lia))).
  eapply (eg_runA B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
  { unfold rmk, CHECK_INJECT. rewrite R10, R11, R12, R13.
    eapply CISeg.ci_seg1; [exact ST | unfold spZ; lia | lia | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> & _).
    repeat split; reflexivity. }
  intros ms regs1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> &
    MU & WM & FR1) Hg1.
  cbn [MState.MS ms_pc_val ms_mem].
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x13068) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 64)) by (rewrite Hg1; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 (Z.max n 1)) by (rewrite Hg1; reflexivity).
  assert (G1d : getr regs1 9 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
  assert (G1e : getr regs1 18 = Z_to_bv 64 v) by (rewrite Hg1; reflexivity).
  assert (G1f : getr regs1 19 = Z_to_bv 64 slot) by (rewrite Hg1; reflexivity).
  assert (G1g : getr regs1 20 = Z_to_bv 64 (Z.max n 1)) by (rewrite Hg1; reflexivity).
  assert (G1h : getr regs1 21 = Z_to_bv 64 f) by (rewrite Hg1; reflexivity).
  assert (K1 : ci_kept regs1)
    by (refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); rewrite Hg1; reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 64) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 64, spZ regs)] x -> spZ regs - 64 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
  assert (Hro1 : ro_agree (ms_segs B) m1).
  { apply (eg_ro_munch B _ mem m1 RO MU). intros a Ha Ho. apply (eg_fs_high B HIL). pose proof (Hout a Ho). lia. }
  assert (I1 : ci_inv L A m1 md).
  { apply (ci_inv_A L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 64, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (eg_pres B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (eg_fs_high B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  assert (FR1' : ci_frame m1) by (exists junk; exact FR1).
  assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
    apply (kb_pre_A B API CHECK_INJECT_STACK 64 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 64, spZ regs)] PRE);
      [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
      | rewrite S1; replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact MU | exact WM' | |].
    - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (Hroom : room_slots b (Z.max n 1)) by (apply room_slots_small; lia).
  replace (Z_to_bv 64 CISeg.CI_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply SR_bind.
  { exact (MALLOC L A regs1 m1 md (Z.max n 1) b Hpre1 Hro1 G1c RES Hroom). }
  intros c' (L1 & A1 & regs2 & m2 & md1 & res & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
    Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
  assert (I1' : ci_inv L1 A1 m2 md1).
  { apply (ci_inv_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 Hpost);
      [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
      | exact Hgk2]. }
  assert (FR2 : ci_frame m2).
  { apply (ci_frame_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1' Hpost); [lia | intros a []]. }
  rewrite G1a.
  apply (ci_ph2 L1 A1 regs2 m2 md1 res d1 d2 I1' Hinit1 Hb1 Hb0 Hres1).
  - transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
  - transitivity (getr regs1 9); [apply (Hp2 9); unfold callee_saved; lia | exact G1d].
  - exact G2.
  - transitivity (getr regs1 18); [apply (Hp2 18); unfold callee_saved; lia | exact G1e].
  - transitivity (getr regs1 19); [apply (Hp2 19); unfold callee_saved; lia | exact G1f].
  - transitivity (getr regs1 20); [apply (Hp2 20); unfold callee_saved; lia | exact G1g].
  - transitivity (getr regs1 21); [apply (Hp2 21); unfold callee_saved; lia | exact G1h].
  - exact (ci_kept_pres regs1 regs2 K1 Hp2).
  - exact FR2.
Qed.

End Body.

Theorem check_inject_holds : check_inject_contract B API.
Proof.
  intros L A regs mem md f n slot v b _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
  eapply ci_entry; eassumption.
Qed.

End CI.
