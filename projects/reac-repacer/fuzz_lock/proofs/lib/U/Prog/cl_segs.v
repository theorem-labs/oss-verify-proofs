(* Walks of check_lookup (fuzz_lock.c:143-179) in fuzz_lock.ubsan, 0x12e34: the pieces between its allocator calls.
   The memcpy and rp_lock_lookup calls of the middle piece are taken through their contracts, and the inline
   expected() (0x12ebc-0x1317c) through check_lookup_exp_seg (lib/U/Prog/check_lookup_exp.v), taken here as
   its proof. The call wrappers, allocator addresses and tactics are those of
   lib/U/Prog/cno_segs.v. Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import memcpy_c rp_lock_lookup_c bcmp_c number_c
  number RpLib cno_segs.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require check_lookup_exp.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_dup(t, n) allocates n bytes, 1 for n = 0 (0x12e80 seqz a0,a1; add a0,a1,a0) *)
Definition cl_nb (n : Z) : Z := if n =? 0 then 1 else n.

Lemma cl_nb_val : forall n, 0 <= n < 2 ^ 64 ->
  Z_to_bv 64 (n + bv_unsigned (v_sltiu (Z_to_bv 64 n) 1)) = Z_to_bv 64 (cl_nb n).
Proof.
  intros n Hn. unfold cl_nb, v_sltiu. rewrite (unsigned_lit n) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec n 0) as [->|NZ]; [reflexivity|].
  destruct (Z.ltb_spec n 1); [lia|]. f_equal. change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
Qed.

(** * The prologue, 0x12e34-0x12e88: the frame of 208 bytes, then malloc(n ? n : 1) *)

Definition cl_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t n pa k rate : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 junk,
    ms' = MS (mkR (Z_to_bv 64 0x12e8c) (Z_to_bv 64 (bv_unsigned sp - 208)) gp tp t0 t1 t2 s0 (Z_to_bv 64 rate)
               (Z_to_bv 64 (cl_nb n)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 k) (Z_to_bv 64 pa) (Z_to_bv 64 n)
               (Z_to_bv 64 t) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CNO_MALLOC) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 208, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
    rw_cells rsegs m1 (bv_unsigned sp - 208) [CB 104 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4;
                                              C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma cl_seg1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t n pa k rate lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 208 <= bv_unsigned sp ->
    0 <= n < 2 ^ 26 -> 0 <= t < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> 0 <= rate < 2 ^ 64 ->
    evt rsegs (cl_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t n pa k rate m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 n) (Z_to_bv 64 pa) (Z_to_bv 64 k)
               (Z_to_bv 64 rate) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12e34) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t n pa k rate lo
    ST LO HN HT HP HK HR.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 208%nat ST.
  do 22 step.
  apply evt_done. unfold cl_s1_post.
  do 16 eexists. split.
  2: { split; [eassumption|]. split; [eassumption|]. replace (bv_unsigned sp - 208) with (bv_unsigned sp + -208) by lia.
       eassumption. }
  f_equal; cn_regs; first [ apply cl_nb_val; lia | cn_w ].
Qed.

(** * The epilogue, 0x13188-0x131c0 *)

Lemma cl_seg3 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 vra : word),
    rw_cells rsegs m (bv_unsigned sp + 104) [C8 v11; C8 v10; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2;
                                            C8 v1; C8 v0; C8 vra] ->
    evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 208)) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4
                                       a5 a6 a7 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3 t4 t5 t6)
                                 F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13188) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 vra FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 15 step.
  cn_fin.
Qed.

(** * The middle piece, 0x12e8c-0x13184: the NULL check, the copy, the lookup, expected() and the comparison *)

(* at the call of free(c) *)
Definition cl_s2_post (spz : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (n c : Z) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                    (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x13188) (Z_to_bv 64 spz) gp tp t0 t1 t2 (Z_to_bv 64 c) s1 (Z_to_bv 64 c)
               a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CNO_FREE) fc None m' (seg_rom rsegs) /\
    munch [(spz - 160, spz); (spz + 8, spz + 104); (c, c + cl_nb n)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m'.

Section S2.
Variables (spz : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (t n pa k rate c : Z) (T P SL : list byte).
Hypothesis BC : bcmp_contract.
Hypothesis RP : rp_lock_lookup_contract.
Hypothesis MC : memcpy_contract.
Hypothesis HT : Z.of_nat (length T) = n.
Hypothesis HN : 0 <= n < 2 ^ 26.
Hypothesis Ht : 0 < t.
Hypothesis Hc : 0 < c.
Hypothesis Hpa : spz + 208 <= pa.
Hypothesis HPL : length (P ++ Z_to_bv 8 0 :: SL) = 16%nat.
Hypothesis H8 : pa mod 8 = 0.
Hypothesis NP : ~ In (Z_to_bv 8 0) P.
Hypothesis HK : Z.of_nat (length P) = k.
Hypothesis Hrate : 0 <= rate < 2 ^ 64.
Hypothesis HSP : 160 <= spz.
Hypothesis HSP2 : spz + 208 + 16 <= 2 ^ 64.
Hypothesis HS8 : spz mod 8 = 0.
Hypothesis Dt : t + n <= spz - 160.
Hypothesis Dc : c + cl_nb n <= spz - 160.
Hypothesis Dct : t + n <= c \/ c + cl_nb n <= t.

Local Notation W := [(spz - 160, spz); (spz + 8, spz + 104); (c, c + cl_nb n)].
Local Notation Q := (cl_s2_post spz gp tp F fc n c m).

Lemma cl_nb_ge : n <= cl_nb n /\ 1 <= cl_nb n.
Proof. unfold cl_nb. destruct (Z.eqb_spec n 0); lia. Qed.

(* 0x1317c: bne s6,s8 (got <> want: abort); mv a0,s0; jal free *)
Lemma cl_t2 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 s9 s10 s11 t3 t4 t5 t6 : word) (vn : Z)
    (m4 : word -> option byte),
  munch W m m4 -> wmono rsegs m m4 -> mem_inv rsegs m4 ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 rate) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 pa) (Z_to_bv 64 vn) (Z_to_bv 64 t)
                       (Z_to_bv 64 (lock_lookup T P rate)) s7 (Z_to_bv 64 (lock_lookup T P rate)) s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1317c) fc None m4 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 s9 s10 s11 t3 t4 t5 t6 vn m4 MU WM MI.
  step. br false.
  step. step.
  apply evt_done. unfold cl_s2_post.
  do 26 eexists. split.
  - f_equal; cn_regs; cn_w.
  - split; [exact MU|]. split; [exact WM | exact MI].
Qed.

(* 0x12ea8: rp_lock_lookup(c, n, port, rate), then expected() *)
Lemma cl_m2 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (m2 : word -> option byte),
  bytes_at rsegs m2 c T -> bytes_at rsegs m2 t T -> bytes_at rsegs m2 pa (P ++ Z_to_bv 8 0 :: SL) ->
  stk rsegs m2 (spz - 160) (spz + 104) -> mem_inv rsegs m2 -> munch W m m2 -> wmono rsegs m m2 ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 rate) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 k) (Z_to_bv 64 pa) (Z_to_bv 64 n) (Z_to_bv 64 t) s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12ea8) fc None m2 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m2 CB TB PB ST MI MU WM.
  pose proof cl_nb_ge as NB.
  pose proof (cn_slack pa P SL H8 HPL) as SLK.
  assert (H16 : Z.of_nat (length (P ++ Z_to_bv 8 0 :: SL)) = 16) by (rewrite HPL; reflexivity).
  destruct (stk_split rsegs m2 (spz - 160) spz (spz + 104) ST ltac:(lia)) as [ST1 ST2].
  (* 0x12ea8 mv a0,s0; mv a1,s4; mv a2,s3; mv a3,s1; jal rp_lock_lookup *)
  do 5 step.
  assert (ST1' : stk rsegs m2 (bv_unsigned (Z_to_bv 64 spz) - 160) (bv_unsigned (Z_to_bv 64 spz)))
    by (rewrite unsigned_lit by lia; exact ST1).
  eapply (cn_rp_call RP); [exact HT | lia | lia | exact CB | lia | exact PB | exact NP | exact SLK | exact Hrate
    | exact ST1' | rewrite unsigned_lit by lia; exact HS8 | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; lia | exact MI | ].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 ST4.
  rewrite unsigned_lit in MU4, ST4 by lia.
  rewrite ret_pc_even by first [lia | reflexivity].
  pose proof (bytes_at_transport rsegs _ _ m4 t T TB MU4 ltac:(rewrite HT; djf)) as TB4.
  pose proof (bytes_at_transport rsegs _ _ m4 pa _ PB MU4 ltac:(rewrite H16; djf)) as PB4.
  pose proof (stk_transport_disjoint rsegs _ m2 m4 spz (spz + 104) ST2 MU4 WM4 ltac:(djf)) as ST5.
  pose proof (munch_trans W m _ m4 MU (munch_weaken [(spz - 160, spz)] W _ m4 ltac:(subfp) MU4)) as MU5.
  pose proof (wmono_trans rsegs m _ m4 WM WM4) as WM5.
  apply bytes_at_app in PB4. destruct PB4 as [PP4 _].
  (* the slots of expected() *)
  destruct (stk_carve rsegs m4 spz (spz + 104) 104 ST5 ltac:(lia)) as [_ [junk FR]].
  replace (spz + 104 - Z.of_nat 104) with spz in FR by lia.
  apply (rw_cells_split_CB rsegs _ _ [] 104 _ [] [8; 40; 8; 48]%nat) in FR; [|reflexivity].
  cbn [app mk_CB_cells] in FR.
  lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
    destruct (rw_split2 _ _ [c1] rest (spz + 8) FR ltac:(cbn; lia)) as [_ FR1] end.
  lazymatch type of FR1 with rw_cells _ _ _ (?c1 :: ?rest) =>
    destruct (rw_split2 _ _ [c1] rest (spz + 48) FR1 ltac:(cbn; lia)) as [C1 FR2] end.
  lazymatch type of FR2 with rw_cells _ _ _ (?c1 :: ?rest) =>
    destruct (rw_split2 _ _ [c1] rest (spz + 56) FR2 ltac:(cbn; lia)) as [C2 C3] end.
  replace (Z_to_bv 64 n) with (Z_to_bv 64 (Z.of_nat (length T))) by (rewrite HT; reflexivity).
  pose proof (bytes_at_bound rsegs m4 pa P PP4) as PPb.
  eapply (check_lookup_exp.check_lookup_exp_seg BC number_holds) with (P := P);
    [ lia | lia | lia | lia | lia | lia | lia | lia
    | rewrite length_app in HPL; cbn [length] in HPL; lia | lia | exact Hrate
    | exact TB4 | exact PP4 | exact C1 | exact C2 | exact C3 | exact MI4 | ].
  intros u0 u1 u2 rb b0 b1 b2 b3 b4 b5 b6 b7 v2 v7 v9 v10 v11 u3 u4 u5 u6 m5 J1' Jk' J2' MU6 WM6 MI6 _ _ _ _ _.
  apply (cl_t2 rb u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 v2 v7 v9 v10 v11 u3 u4 u5 u6 (Z.of_nat (length T)) m5).
  - exact (munch_trans W m m4 m5 MU5 (munch_weaken [(spz + 8, spz + 104)] W m4 m5 ltac:(subfp) MU6)).
  - exact (wmono_trans rsegs m m4 m5 WM5 WM6).
  - exact MI6.
Qed.

(* 0x12e8c: the NULL check of malloc's result (abort), then memcpy(c, t, n) when n != 0 *)
Lemma cl_seg2 : forall (ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  bytes_at rsegs m t T -> bytes_at rsegs m pa (P ++ Z_to_bv 8 0 :: SL) ->
  stk rsegs m c (c + cl_nb n) -> stk rsegs m (spz - 160) (spz + 104) -> mem_inv rsegs m ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 (Z_to_bv 64 rate) (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 k) (Z_to_bv 64 pa) (Z_to_bv 64 n) (Z_to_bv 64 t) s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12e8c) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 TB PB SC ST MI.
  pose proof cl_nb_ge as NB.
  assert (H16 : Z.of_nat (length (P ++ Z_to_bv 8 0 :: SL)) = 16) by (rewrite HPL; reflexivity).
  pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* 0x12e8c beqz a0 (abort); mv s0,a0; beqz s4 *)
  step. br false.
  step.
  step.
  rewrite ?Z.add_0_r.
  destruct (Z.eq_dec n 0) as [Z0|NZ].
  - br true.
    assert (T0 : T = []) by (destruct T; [reflexivity | cbn in HT; lia]).
    apply cl_m2; try assumption. rewrite T0. apply cn_bytes_nil; lia.
  - br false.
    assert (EN : cl_nb n = n) by (unfold cl_nb; rewrite (proj2 (Z.eqb_neq n 0) NZ); reflexivity).
    rewrite EN in SC.
    destruct (stk_carve rsegs m c (c + n) (Z.to_nat n) SC ltac:(lia)) as [_ [jc RC]].
    rewrite Z2Nat.id in RC by lia. replace (c + n - n) with c in RC by ring.
    (* 0x12e98 mv a0,s0; mv a1,s5; mv a2,s4; jal memcpy *)
    do 4 step.
    eapply (cn_mc_call MC); [exact HT | exact TB | exact RC | lia | lia | lia | exact MI | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 MU1 WM1 MI1 RC1 TB1.
    rewrite ret_pc_even by first [lia | reflexivity].
    pose proof (stk_transport_disjoint rsegs _ m m1 _ _ ST MU1 WM1 ltac:(djf)) as ST1.
    pose proof (bytes_at_transport rsegs _ m m1 pa _ PB MU1 ltac:(rewrite H16; djf)) as PB1.
    pose proof (munch_trans W m m m1 MU (munch_weaken [(c, c + n)] W m m1 ltac:(rewrite EN; subfp) MU1)) as MU2.
    pose proof (wmono_trans rsegs m m m1 WM WM1) as WM2.
    rewrite ?Z.add_0_r.
    apply cl_m2; try assumption.
    exact (cn_rw_bytes m1 c _ T RC1).
Qed.

End S2.
