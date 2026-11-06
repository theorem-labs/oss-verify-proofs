(* Walks of check_lookup (fuzz_lock.c:143-179) in fuzz_lock.plain, 0x12da0: the pieces between its allocator calls,
   in the form of libreac/fuzz_decode's lib/Prog/crt_segs.v. The memcpy and rp_lock_lookup calls inside the middle
   piece are taken through their contracts, the inlined [expected] (0x12e28 -> 0x130d0) through its walk
   check_lookup_exp_holds (check_lookup_exp.v).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import memcpy_c rp_lock_lookup_c bcmp_c
  check_lookup_exp.
Import ListNotations.
Open Scope Z_scope.

Definition CL_MALLOC : Z := 0x13fdc.
Definition CL_FREE : Z := 0x13e9c.

(* malloc(n ? n : 1), fuzz_dup of fuzz.h inlined *)
Definition cl_sz (n : Z) : Z := if n =? 0 then 1 else n.

Ltac cl_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.

Ltac cl_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cl_w := cl_usub; first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].
Ltac cl_fin := apply evt_done; f_equal; cl_regs; cl_w.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

(* the value of [seqz a0, a1; add a0, a1, a0] at 0x12dec *)
Lemma cl_sz_reg : forall n, 0 <= n < 2 ^ 63 ->
  Z_to_bv 64 (n + bv_unsigned (v_sltiu (Z_to_bv 64 n) 1)) = Z_to_bv 64 (cl_sz n).
Proof.
  intros n Hn. rewrite v_sltiu_b2z. rewrite (unsigned_lit n) by lia. change (bv_wrap 64 1) with 1. unfold cl_sz.
  destruct (Z.eqb_spec n 0) as [->|N]; [reflexivity|].
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  change (bv_unsigned (Z_to_bv 64 0)) with 0. f_equal. lia.
Qed.

Lemma cl_rw_tl : forall m A B c cs, rw_cells rsegs m A (c :: cs) -> B = A + Z.of_nat (csize c) -> rw_cells rsegs m B cs.
Proof.
  intros m A B c cs [[W Bt] V] ->. cbn [cells_wf cells_bytes cells_size] in *. destruct W as [W1 W2].
  pose proof (cbytes_length c W1) as Lc.
  apply bytes_at_app in Bt. destruct Bt as [_ B2]. rewrite Lc in B2.
  destruct V as (V1 & V2 & V3). split; [split|].
  - exact W2.
  - exact B2.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia.
    apply V3. lia.
Qed.

(** * The prologue, 0x12da0-0x12df4: the frame of 176 bytes, then malloc(n ? n : 1) *)
Definition cl_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t n pa k rate : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1,
    ms' = MS (mkR (Z_to_bv 64 0x12df8) (Z_to_bv 64 (bv_unsigned sp - 176)) gp tp t0 t1 t2 s0 (Z_to_bv 64 rate)
               (Z_to_bv 64 (cl_sz n)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 k) (Z_to_bv 64 pa) (Z_to_bv 64 n)
               (Z_to_bv 64 t) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CL_MALLOC) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
    rw_cells rsegs m1 (bv_unsigned sp - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5;
                                               C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma cl_seg1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t n pa k rate lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 176 <= bv_unsigned sp ->
    0 <= n < 2 ^ 26 -> 0 <= t < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> 0 <= rate < 2 ^ 64 ->
    evt rsegs (cl_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t n pa k rate m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 n) (Z_to_bv 64 pa) (Z_to_bv 64 k)
               (Z_to_bv 64 rate) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12da0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t n pa k rate lo
    ST LO HN HT HP HK HR.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 176%nat ST.
  do 22 step.
  rewrite cl_sz_reg by lia.
  apply evt_done. unfold cl_s1_post.
  do 15 eexists. split.
  2: { split; [eassumption|]. split; [eassumption|]. replace (bv_unsigned sp - 104) with (bv_unsigned sp + -176 + 72) by lia.
       eapply cl_rw_tl; [eassumption | reflexivity]. }
  f_equal; cl_regs; cl_w.
Qed.

(** * The epilogue, 0x130d4-0x13110: free(c) as a tail call *)
Lemma cl_seg4 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 vra : word),
    rw_cells rsegs m (bv_unsigned sp + 72) [C8 v11; C8 v10; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4;
                                            C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 176)) gp tp t0 t1 t2 v0 v1 s0 a1 a2 a3 a4
                                       a5 a6 a7 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CL_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x130d4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 vra FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 16 step.
  cl_fin.
Qed.

(** * The callees, with continuations *)

(* rp_lock_lookup's contract with the length register as a plain value *)
Lemma cl_rp_call : rp_lock_lookup_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tx k pa rate : Z) (T P SL : list byte)
         (K : machine_state -> Prop),
    Z.of_nat (length T) = k ->
    0 < tx -> tx + k < 2 ^ 64 -> bytes_at rsegs m tx T ->
    0 < pa -> bytes_at rsegs m pa (P ++ Z_to_bv 8 0 :: SL) -> ~ In (Z_to_bv 8 0) P ->
    (- (pa + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length SL) ->
    0 <= rate < 2 ^ 64 ->
    stk rsegs m (bv_unsigned sp - 176) (bv_unsigned sp) ->
    tx + k <= bv_unsigned sp - 176 -> bv_unsigned sp <= pa ->
    mem_inv rsegs m ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
       stk rsegs m' (bv_unsigned sp - 176) (bv_unsigned sp) ->
       evt rsegs K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lock_lookup T P rate)) a1' a2' a3' a4' a5' a6'
                           a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    evt rsegs K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 tx) (Z_to_bv 64 k) (Z_to_bv 64 pa) (Z_to_bv 64 rate)
                         a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x13118) fc None m (seg_rom rsegs)).
Proof.
  intros RP ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m tx k pa rate
    T P SL K <- Htx Htx2 TB Hpa PB NP SLK Hr ST D1 D2 MI KK.
  pose proof (bytes_at_bound rsegs m pa _ PB) as BP.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  eapply evt_cut.
  { eapply (RP ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m tx pa rate
      (bv_unsigned sp - 176) T P SL); unfold RP_FRAME; first [assumption | lia]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM &
    MI' & ST').
  unfold RP_FRAME in MU. exact (KK t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST').
Qed.

(* memcpy's contract with literal registers *)
Lemma cl_mc_call : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (dst src n : Z) (S junk : list byte)
         (K : machine_state -> Prop),
    Z.of_nat (length S) = n ->
    bytes_at rsegs m src S -> rw_cells rsegs m dst [CB (Z.to_nat n) junk] ->
    dst + n < 2 ^ 64 -> src + n < 2 ^ 64 ->
    src + n <= dst \/ dst + n <= src ->
    mem_inv rsegs m ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       munch [(dst, dst + n)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
       rw_cells rsegs m' dst [CB (Z.to_nat n) S] -> bytes_at rsegs m' src S ->
       evt rsegs K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 dst) a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    evt rsegs K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 src) (Z_to_bv 64 n)
                         a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1af18) fc None m (seg_rom rsegs)).
Proof.
  intros MC ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m dst src n
    S junk K HS SB RW Hd Hs D MI KK.
  pose proof (bytes_at_bound rsegs m src S SB) as BS.
  pose proof (rw_cells_bound rsegs m dst _ RW) as BD.
  assert (Hn : 0 <= n) by lia.
  eapply evt_cut.
  { eapply (MC ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 src) (Z_to_bv 64 n) a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S junk); rewrite ?unsigned_lit by lia.
    - exact SB.
    - rewrite <- HS, Nat2Z.id. reflexivity.
    - exact RW.
    - lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM &
    MI' & RW' & SB').
  rewrite ?unsigned_lit in MU by lia. rewrite ?unsigned_lit in RW' by lia. rewrite ?unsigned_lit in SB' by lia.
  exact (KK t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' RW' SB').
Qed.

Lemma cl_slack : forall pa (P SL : list byte), pa mod 8 = 0 -> length (P ++ Z_to_bv 8 0 :: SL) = 16%nat ->
  (- (pa + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length SL).
Proof.
  intros pa P SL H8 HL. rewrite length_app in HL. cbn [length] in HL.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cl_rw_bytes : forall m A n (bs : list byte), rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Ltac subfp := unfold sub_fp; intros ? Hx; cbn [outside] in Hx |- *;
  repeat match type of Hx with _ /\ _ => let H := fresh "Ho" in destruct Hx as [H Hx] end;
  repeat split; try exact I; lia.
Ltac djf := cbn [disjoint_from]; repeat split; try exact I; lia.

(** * 0x12df8-0x130d4: the NULL check, memcpy(c, t, n) when n != 0, got = rp_lock_lookup(c, n, port, rate), the
      inlined [expected] (want), and got = want *)

Definition cl_s3_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (spf t pa rate c v : Z) (T : list byte)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 rate) a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 pa) (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 t) (Z_to_bv 64 v) (Z_to_bv 64 v)
               s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x130d4) fc None m' (seg_rom rsegs) /\
    munch [(spf - 176, spf + 72); (c, c + Z.of_nat (length T))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Section S3.
Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (spf t pa rate c : Z) (T P SL : list byte).
Hypothesis RP : rp_lock_lookup_contract.
Hypothesis MC : memcpy_contract.
Hypothesis BC : bcmp_contract.
Hypothesis HN : Z.of_nat (length T) < 2 ^ 26.
Hypothesis Ht : 0 < t.
Hypothesis Hc : 0 < c.
Hypothesis Hpa : spf + 176 <= pa.
Hypothesis Hpa2 : pa + 16 <= 2 ^ 63.
Hypothesis HPL : length (P ++ Z_to_bv 8 0 :: SL) = 16%nat.
Hypothesis H8 : pa mod 8 = 0.
Hypothesis NP : ~ In (Z_to_bv 8 0) P.
Hypothesis Hrate : 0 <= rate < 2 ^ 64.
Hypothesis LO : 176 <= spf.
Hypothesis Dt : t + Z.of_nat (length T) <= spf - 176.
Hypothesis Dc : c + Z.of_nat (length T) <= spf - 176.
Hypothesis Dtc : t + Z.of_nat (length T) <= c \/ c + Z.of_nat (length T) <= t.

Local Notation N := (Z.of_nat (length T)).
Local Notation W := [(spf - 176, spf + 72); (c, c + N)].
Local Notation Q := (cl_s3_post gp tp F fc spf t pa rate c (lock_lookup T P rate) T m0).

(* 0x12e14: got = rp_lock_lookup(c, n, port, rate), then the inlined [expected] *)
Lemma cl_m3b : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (m : word -> option byte) (J : list byte),
  bytes_at rsegs m c T -> bytes_at rsegs m t T -> bytes_at rsegs m pa (P ++ Z_to_bv 8 0 :: SL) ->
  stk rsegs m (spf - 176) spf -> rw_cells rsegs m spf [CB 72 J] ->
  mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 rate) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (Z.of_nat (length P))) (Z_to_bv 64 pa) (Z_to_bv 64 N) (Z_to_bv 64 t)
                       s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12e14) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m J BC0 BT BP ST J72 MI MU WM.
  pose proof (cl_slack pa P SL H8 HPL) as SLK.
  assert (H16 : Z.of_nat (length (P ++ Z_to_bv 8 0 :: SL)) = 16) by (rewrite HPL; reflexivity).
  assert (HP15 : (length P <= 15)%nat) by (rewrite length_app in HPL; cbn [length] in HPL; lia).
  do 5 step.
  eapply (cl_rp_call RP) with (T := T) (P := P) (SL := SL);
    [ reflexivity | lia | lia | exact BC0 | lia | exact BP | exact NP | exact SLK | exact Hrate
    | rewrite unsigned_lit by lia; exact ST | uns; lia | uns; lia | exact MI | ].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 ST4.
  rewrite ret_pc_even by first [lia | reflexivity].
  rewrite unsigned_lit in MU4, ST4 by lia.
  pose proof (bytes_at_transport rsegs _ _ m4 t T BT MU4 ltac:(djf)) as BT4.
  pose proof (bytes_at_transport rsegs _ _ m4 pa _ BP MU4 ltac:(rewrite H16; djf)) as BP4.
  pose proof (rw_cells_transport rsegs _ _ m4 spf _ J72 MU4 WM4 ltac:(cbn [cells_size csize Nat.add]; djf)) as J4.
  pose proof (munch_trans W m0 m m4 MU (munch_weaken [(spf - 176, spf)] W m m4 ltac:(subfp) MU4)) as MU5.
  pose proof (wmono_trans rsegs m0 m m4 WM WM4) as WM5.
  eapply (check_lookup_exp_holds BC) with (sp := spf) (tx := t) (pa := pa) (rate := rate) (T := T) (P := P) (SL := SL) (J := J);
    [ exact HP15 | exact Hrate | lia | lia | exact BT4 | lia | exact BP4 | exact J4 | lia | lia | exact MI4 | ].
  intros ra' t0e t1e t2e a0e a1e a2e a3e a4e a5e a6e a7e s2e s8e s9e s10e s11e t3e t4e t5e t6e m5 J' MU6 WM6 MI6 J5.
  unfold EXP_OUT.
  step. br false.
  apply evt_done. unfold cl_s3_post.
  do 22 eexists. split; [reflexivity|].
  split; [exact (munch_trans W m0 m4 m5 MU5 (munch_weaken [(spf, spf + 72)] W m4 m5 ltac:(subfp) MU6))|].
  split; [exact (wmono_trans rsegs m0 m4 m5 WM5 WM6) | exact MI6].
Qed.

(* 0x12df8: the NULL check (malloc's c is not 0) and memcpy(c, t, n) when n != 0 *)
Lemma cl_m3 : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (J : list byte),
  bytes_at rsegs m0 t T -> bytes_at rsegs m0 pa (P ++ Z_to_bv 8 0 :: SL) ->
  stk rsegs m0 c (c + N) -> stk rsegs m0 (spf - 176) spf -> rw_cells rsegs m0 spf [CB 72 J] ->
  mem_inv rsegs m0 ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 t2 s0 (Z_to_bv 64 rate) (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (Z.of_nat (length P))) (Z_to_bv 64 pa) (Z_to_bv 64 N) (Z_to_bv 64 t)
                       s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12df8) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 J BT BP SC ST J72 MI.
  pose proof (munch_refl W m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  assert (H16 : Z.of_nat (length (P ++ Z_to_bv 8 0 :: SL)) = 16) by (rewrite HPL; reflexivity).
  step. br false. step. step.
  destruct (Z.eq_dec N 0) as [N0|N0].
  - br true.
    assert (T0 : T = []) by (apply length_zero_iff_nil; lia).
    apply cl_m3b with (J := J); try assumption.
    rewrite T0. apply bytes_at_nil. lia.
  - br false. do 4 step.
    destruct (stk_carve rsegs m0 c (c + N) (length T) SC ltac:(lia)) as [_ [junk CW]].
    replace (c + N - Z.of_nat (length T)) with c in CW by lia.
    eapply (cl_mc_call MC) with (S := T) (junk := junk);
      [ reflexivity | exact BT | rewrite Nat2Z.id; exact CW | lia | lia | lia | exact MI | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 CW2 BT2.
    rewrite ret_pc_even by first [lia | reflexivity].
    apply cl_m3b with (J := J).
    + exact (cl_rw_bytes _ _ _ _ CW2).
    + exact BT2.
    + exact (bytes_at_transport rsegs _ _ m2 pa _ BP MU2 ltac:(rewrite H16; djf)).
    + exact (stk_transport_disjoint rsegs _ _ m2 _ _ ST MU2 WM2 ltac:(djf)).
    + exact (rw_cells_transport rsegs _ _ m2 spf _ J72 MU2 WM2 ltac:(cbn [cells_size csize Nat.add]; djf)).
    + exact MI2.
    + exact (munch_weaken [(c, c + N)] W m0 m2 ltac:(subfp) MU2).
    + exact WM2.
Qed.

End S3.
