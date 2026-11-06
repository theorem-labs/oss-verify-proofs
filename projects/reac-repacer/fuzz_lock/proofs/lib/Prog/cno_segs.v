(* Walks of check_no_overread (fuzz_lock.c:120-141) in fuzz_lock.plain, 0x12cac: the pieces between its allocator
   calls. The memcpy and rp_lock_lookup calls inside the middle piece are taken through their contracts.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import memcpy_c rp_lock_lookup_c.
Import ListNotations.
Open Scope Z_scope.

Definition CNO_MALLOC : Z := 0x13fdc.
Definition CNO_FREE : Z := 0x13e9c.

Ltac cn_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.

Ltac cn_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.

Ltac cn_w := cn_usub; first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].

Ltac cn_fin := apply evt_done; f_equal; cn_regs; cn_w.

Ltac uns := rewrite ?unsigned_lit by lia.

Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

Ltac subfp := unfold sub_fp; intros ? Hx; cbn [outside] in Hx |- *;
  repeat match type of Hx with _ /\ _ => let H := fresh "Ho" in destruct Hx as [H Hx] end;
  repeat split; try exact I; lia.

Ltac djf := cbn [disjoint_from]; repeat split; try exact I; lia.

(* the prologue, 0x12cac-0x12ce4: the frame of 64 bytes, then malloc(n + 1) *)
Definition cn_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t n pa rate : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 junk,
    ms' = MS (mkR (Z_to_bv 64 0x12ce8) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 rate) s1
               (Z_to_bv 64 (n + 1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pa) (Z_to_bv 64 (n + 1)) (Z_to_bv 64 n)
               (Z_to_bv 64 t) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CNO_MALLOC) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
    rw_cells rsegs m1 (bv_unsigned sp - 64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma cn_seg1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t n pa rate lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp ->
    0 <= n < 2 ^ 26 -> 0 <= t < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= rate < 2 ^ 64 ->
    evt rsegs (cn_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t n pa rate m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 n) (Z_to_bv 64 pa) (Z_to_bv 64 rate)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12cac) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t n pa rate lo
    ST LO HN HT HP HR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  do 15 step.
  apply evt_done. unfold cn_s1_post.
  do 16 eexists. split.
  2: { split; [eassumption|]. split; [eassumption|]. replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia.
       eassumption. }
  f_equal; cn_regs; cn_w.
Qed.

(* 0x12ce8-0x12cf0: a = malloc's result in s1, then malloc(n + 1) again *)
Lemma cn_seg2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x12cf4) sp gp tp t0 t1 t2 s0 a0 s3 a1 a2 a3 a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CNO_MALLOC) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12ce8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step.
  cn_fin.
Qed.

(* the epilogue, 0x12d74-0x12d98: free(b) as a tail call *)
Lemma cn_seg4 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte)
         (v0 v1 v2 v3 v4 v5 vra : word),
    rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 v0 v1 s3 a1 a2 a3 a4
                                       a5 a6 a7 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 CNO_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12d74) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk
    v0 v1 v2 v3 v4 v5 vra FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 10 step.
  cn_fin.
Qed.

(* rp_lock_lookup's contract with the length register as a plain value *)
Lemma cn_rp_call : rp_lock_lookup_contract ->
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
Lemma cn_mc_call : memcpy_contract ->
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

Lemma cn_slack : forall pa (P SL : list byte), pa mod 8 = 0 -> length (P ++ Z_to_bv 8 0 :: SL) = 16%nat ->
  (- (pa + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length SL).
Proof.
  intros pa P SL H8 HL. rewrite length_app in HL. cbn [length] in HL.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cn_rw_bytes : forall m A n (bs : list byte), rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma cn_bytes_nil : forall m A, 0 <= A <= 2 ^ 64 -> bytes_at rsegs m A [].
Proof. intros m A HA. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

(* the post of the middle piece, at the first free *)
Definition cn_s3_post (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n pa rate ba bb v : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x12d74) sp gp tp t0 t1 t2 (Z_to_bv 64 rate) (Z_to_bv 64 ba) (Z_to_bv 64 ba)
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pa) (Z_to_bv 64 bb) (Z_to_bv 64 n) (Z_to_bv 64 v)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CNO_FREE) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 176, bv_unsigned sp); (ba, ba + n + 1); (bb, bb + n + 1)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m'.

Section S3.
Variables (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (t n pa rate ba bb : Z) (T P SL : list byte).
Hypothesis RP : rp_lock_lookup_contract.
Hypothesis MC : memcpy_contract.
Hypothesis HT : Z.of_nat (length T) = n.
Hypothesis HN : 0 <= n < 2 ^ 26.
Hypothesis Ht : 0 < t.
Hypothesis Hba : 0 < ba.
Hypothesis Hbb : 0 < bb.
Hypothesis Hpa : bv_unsigned sp <= pa.
Hypothesis HPL : length (P ++ Z_to_bv 8 0 :: SL) = 16%nat.
Hypothesis H8 : pa mod 8 = 0.
Hypothesis NP : ~ In (Z_to_bv 8 0) P.
Hypothesis Hrate : 0 <= rate < 2 ^ 64.
Hypothesis LO : 176 <= bv_unsigned sp.
Hypothesis Dt : t + n <= bv_unsigned sp - 176.
Hypothesis Da : ba + n + 1 <= bv_unsigned sp - 176.
Hypothesis Db : bb + n + 1 <= bv_unsigned sp - 176.
Hypothesis Dab : ba + n + 1 <= bb \/ bb + n + 1 <= ba.
Hypothesis Dta : t + n <= ba \/ ba + n + 1 <= t.
Hypothesis Dtb : t + n <= bb \/ bb + n + 1 <= t.

Local Notation W := [(bv_unsigned sp - 176, bv_unsigned sp); (ba, ba + n + 1); (bb, bb + n + 1)].
Local Notation Q := (cn_s3_post sp gp tp s6 s7 s8 s9 s10 s11 F fc n pa rate ba bb (lock_lookup T P rate) m).

Lemma cn_t3 : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m4 : word -> option byte),
  munch W m m4 -> wmono rsegs m m4 -> mem_inv rsegs m4 ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 rate) (Z_to_bv 64 ba) (Z_to_bv 64 (lock_lookup T P rate))
                       a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pa) (Z_to_bv 64 bb) (Z_to_bv 64 n)
                       (Z_to_bv 64 (lock_lookup T P rate)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12d68) fc None m4 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m4 MU WM MI.
  step. br false.
  do 2 step.
  apply evt_done. unfold cn_s3_post.
  do 15 eexists. split.
  - f_equal; cn_regs; cn_w.
  - split; [exact MU|]. split; [exact WM | exact MI].
Qed.

(* 0x12d24-0x12d64: a[n] = '0', b[n] = ' ', then the two lookups *)
Lemma cn_m3 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m2 : word -> option byte),
  bytes_at rsegs m2 ba T -> bytes_at rsegs m2 bb T ->
  stk rsegs m2 (ba + n) (ba + n + 1) -> stk rsegs m2 (bb + n) (bb + n + 1) ->
  bytes_at rsegs m2 pa (P ++ Z_to_bv 8 0 :: SL) ->
  stk rsegs m2 (bv_unsigned sp - 176) (bv_unsigned sp) ->
  mem_inv rsegs m2 -> munch W m m2 -> wmono rsegs m m2 ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 rate) (Z_to_bv 64 ba) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 pa) (Z_to_bv 64 bb) (Z_to_bv 64 n) (Z_to_bv 64 t) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12d24) fc None m2 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 BA BB SA SB PB ST MI MU WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (cn_slack pa P SL H8 HPL) as SLK.
  assert (H16 : Z.of_nat (length (P ++ Z_to_bv 8 0 :: SL)) = 16) by (rewrite HPL; reflexivity).
  destruct (stk_carve rsegs m2 (ba + n) (ba + n + 1) 1 SA ltac:(lia)) as [_ [ja CA]].
  destruct (stk_carve rsegs m2 (bb + n) (bb + n + 1) 1 SB ltac:(lia)) as [_ [jb CB']].
  clear SA SB.
  replace (ba + n + 1 - Z.of_nat 1) with (ba + n) in CA by lia.
  replace (bb + n + 1 - Z.of_nat 1) with (bb + n) in CB' by lia.
  assert (Han : exists x, x = ba + n) by eauto. destruct Han as [an Han]. rewrite <- Han in CA.
  assert (Hbn : exists x, x = bb + n) by eauto. destruct Hbn as [bn Hbn]. rewrite <- Hbn in CB'.
  step. rewrite <- ?Han. step. change (Z_to_bv 64 48) with (zxb (Z_to_bv 8 48)). step.
  step. rewrite <- ?Hbn. step. change (Z_to_bv 64 32) with (zxb (Z_to_bv 8 32)). step.
  do 5 step.
  eapply (cn_rp_call RP); [exact HT | lia | lia | exact BA | lia | exact PB | exact NP | exact SLK | exact Hrate
    | exact ST | lia | lia | exact MI | ].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 ST4.
  rewrite ret_pc_even by first [lia | reflexivity].
  pose proof (bytes_at_transport rsegs _ _ m4 bb T BB MU4 ltac:(rewrite HT; djf)) as BB4.
  pose proof (bytes_at_transport rsegs _ _ m4 pa _ PB MU4 ltac:(rewrite H16; djf)) as PB4.
  pose proof (munch_trans W m _ m4 MU (munch_weaken [(bv_unsigned sp - 176, bv_unsigned sp)] W _ m4 ltac:(subfp)
    MU4)) as MU5.
  pose proof (wmono_trans rsegs m _ m4 WM WM4) as WM5.
  do 6 step.
  eapply (cn_rp_call RP); [exact HT | lia | lia | exact BB4 | lia | exact PB4 | exact NP | exact SLK | exact Hrate
    | exact ST4 | lia | lia | exact MI4 | ].
  intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m5 MU6 WM6 MI6 ST6.
  rewrite ret_pc_even by first [lia | reflexivity].
  apply cn_t3.
  - exact (munch_trans W m m4 m5 MU5 (munch_weaken [(bv_unsigned sp - 176, bv_unsigned sp)] W m4 m5 ltac:(subfp) MU6)).
  - exact (wmono_trans rsegs m m4 m5 WM5 WM6).
  - exact MI6.
Qed.

(* 0x12cf4-0x12d20: the NULL checks, then memcpy(a, t, n) and memcpy(b, t, n) when n != 0 *)
Lemma cn_seg3 : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word),
  bytes_at rsegs m t T -> bytes_at rsegs m pa (P ++ Z_to_bv 8 0 :: SL) ->
  stk rsegs m ba (ba + n + 1) -> stk rsegs m bb (bb + n + 1) ->
  stk rsegs m (bv_unsigned sp - 176) (bv_unsigned sp) -> mem_inv rsegs m ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 rate) (Z_to_bv 64 ba) (Z_to_bv 64 bb) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 pa) s3 (Z_to_bv 64 n) (Z_to_bv 64 t) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12cf4) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 TB PB SA SB ST MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (H16 : Z.of_nat (length (P ++ Z_to_bv 8 0 :: SL)) = 16) by (rewrite HPL; reflexivity).
  pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
  step. br false.
  step.
  step. br false.
  step.
  destruct (Z.eq_dec n 0) as [Z0|NZ].
  - br true.
    assert (T0 : T = []) by (destruct T; [reflexivity | cbn in HT; lia]).
    destruct (stk_split rsegs m ba (ba + n) (ba + n + 1) SA ltac:(lia)) as [_ SA2].
    destruct (stk_split rsegs m bb (bb + n) (bb + n + 1) SB ltac:(lia)) as [_ SB2].
    apply cn_m3; try assumption; rewrite T0; apply cn_bytes_nil; lia.
  - br false.
    destruct (stk_split rsegs m ba (ba + n) (ba + n + 1) SA ltac:(lia)) as [SA1 SA2].
    destruct (stk_carve rsegs m ba (ba + n) (Z.to_nat n) SA1 ltac:(lia)) as [_ [ja RA]].
    rewrite Z2Nat.id in RA by lia. replace (ba + n - n) with ba in RA by ring.
    do 4 step.
    eapply (cn_mc_call MC); [exact HT | exact TB | exact RA | lia | lia | lia | exact MI | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 MU1 WM1 MI1 RA1 TB1.
    rewrite ret_pc_even by first [lia | reflexivity].
    pose proof (stk_transport_disjoint rsegs _ m m1 bb _ SB MU1 WM1 ltac:(djf)) as SB1.
    pose proof (stk_transport_disjoint rsegs _ m m1 _ _ SA2 MU1 WM1 ltac:(djf)) as SA3.
    pose proof (stk_transport_disjoint rsegs _ m m1 _ _ ST MU1 WM1 ltac:(djf)) as ST1.
    pose proof (bytes_at_transport rsegs _ m m1 pa _ PB MU1 ltac:(rewrite H16; djf)) as PB1.
    pose proof (munch_trans W m m m1 MU (munch_weaken [(ba, ba + n)] W m m1 ltac:(subfp) MU1)) as MU2.
    pose proof (wmono_trans rsegs m m m1 WM WM1) as WM2.
    destruct (stk_split rsegs m1 bb (bb + n) (bb + n + 1) SB1 ltac:(lia)) as [SB2 SB3].
    destruct (stk_carve rsegs m1 bb (bb + n) (Z.to_nat n) SB2 ltac:(lia)) as [_ [jb RB]].
    rewrite Z2Nat.id in RB by lia. replace (bb + n - n) with bb in RB by ring.
    do 4 step.
    eapply (cn_mc_call MC); [exact HT | exact TB1 | exact RB | lia | lia | lia | exact MI1 | ].
    intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 MU3 WM3 MI3 RB3 TB3.
    rewrite ret_pc_even by first [lia | reflexivity].
    pose proof (bytes_at_transport rsegs _ m1 m2 ba T (cn_rw_bytes m1 ba _ T RA1) MU3 ltac:(rewrite HT; djf)) as BA3.
    pose proof (stk_transport_disjoint rsegs _ m1 m2 _ _ SA3 MU3 WM3 ltac:(djf)) as SA4.
    pose proof (stk_transport_disjoint rsegs _ m1 m2 _ _ SB3 MU3 WM3 ltac:(djf)) as SB4.
    pose proof (stk_transport_disjoint rsegs _ m1 m2 _ _ ST1 MU3 WM3 ltac:(djf)) as ST3.
    pose proof (bytes_at_transport rsegs _ m1 m2 pa _ PB1 MU3 ltac:(rewrite H16; djf)) as PB3.
    apply cn_m3; try assumption.
    + exact (cn_rw_bytes m2 bb _ T RB3).
    + exact (munch_trans W m m1 m2 MU2 (munch_weaken [(bb, bb + n)] W m1 m2 ltac:(subfp) MU3)).
    + exact (wmono_trans rsegs m m1 m2 WM2 WM3).
Qed.

End S3.
