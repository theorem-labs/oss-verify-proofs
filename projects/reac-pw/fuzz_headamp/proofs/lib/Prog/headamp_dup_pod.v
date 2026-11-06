(** pod = fuzz_dup(pp->buf, len) in LLVMFuzzerTestOneInput (plain), past its malloc: the walk of [0x1404c, 0x1407c)
    against headamp_dup_pod_contract (Prog/LLVMFuzzerTestOneInput_c.v), from memcpy's contract (Prog/memcpy_c.v).

    0x1404c `beqz a0` falls through (pod <> 0, and pod is below 2^64 by its writable cells); 0x14050 `mv s1,a0`;
    0x14054 `andi s2,s6,0xff` keeps cap (0 <= cap <= 9); 0x14058 `beqz s4` falls through (len = head_len inp >= 8:
    Pod/Model.v pod_build_wf, Pod/Spa.v buf_header); 0x1405c-0x14064 a0 = pod, a1 = pp, a2 = len and `jal memcpy` at
    0x14068 (memcpy at 0x1d248, ra = 0x1406c): the source is the pp block's first len bytes, buf r (Pod/Layout.v
    pp_image: buf r ++ ...), the destination the pod block's len writable bytes, the two apart (len <= 5440 < 19744);
    then 0x1406c-0x14078 s0 = 3 cap, s4 = 3 cap + 3, a0 = s4. The evt stops at 0x1407c, before out's malloc. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import memcpy_c SlotInv LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Lemma dp_eqb_u : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma dp_land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(** The record's buffer length: 8 <= len <= 5440. *)
Lemma dp_len : forall inp, 8 <= head_len inp <= 5440.
Proof.
  intros inp. unfold head_len, head_rec.
  destruct (pod_build inp) as [r rest] eqn:E. cbn [fst].
  destruct (buf_header r (pod_build_wf inp r rest E)) as (_ & _ & _ & H). exact H.
Qed.

Lemma dp_rw_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Theorem headamp_dup_pod_holds : memcpy_c.memcpy_contract -> headamp_dup_pod_contract.
Proof.
  intros MCPY. unfold headamp_dup_pod_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    inp junk cap pp pod -> Hpod -> -> -> Hcap HPP HPC HSEP MI.
  pose proof (dp_len inp) as HL.
  pose proof (rw_cells_bound rsegs m pod _ HPC) as HPB. cbn [cells_size csize] in HPB.
  rewrite ?Nat.add_0_r, Z2Nat.id in HPB by lia.
  pose proof HPP as HPP0. unfold pp_bytes, pp_image in HPP0. apply bytes_at_app in HPP0 as [HBUF _].
  pose proof HBUF as (HQ0 & HQ1 & _). change (Z.of_nat (length (buf (head_rec inp)))) with (head_len inp) in HQ1.
  unfold HEAD_DUP_POD.
  (* 0x1404c beqz a0: pod <> 0 *)
  step. rewrite dp_eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x14050 mv s1,a0; 0x14054 andi s2,s6,0xff; 0x14058 beqz s4: len >= 8 *)
  step. step. rewrite unsigned_lit, dp_land255 by lia. step.
  rewrite dp_eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x1405c mv a0,s1; mv a1,s5; mv a2,s4; 0x14068 jal memcpy *)
  step. step. step. step.
  unfold POD_PROPS in HSEP.
  eapply evt_cut.
  { eapply MCPY with (src := buf (head_rec inp)) (junk := junk); rewrite ?unsigned_lit by lia.
    - exact HBUF.
    - unfold head_len. rewrite Nat2Z.id. reflexivity.
    - exact HPC.
    - lia.
    - exact MI. }
  intros ms' Hpost. unfold memcpy_post in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                     E & MU1 & WM1 & MI1 & CB1 & _).
  subst ms'. rewrite !unsigned_lit in MU1, CB1 by lia.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  (* 0x1406c slli s0,s2,1; add s0,s0,s2; addi s4,s0,3; mv a0,s4 *)
  step. step. step. step.
  rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
  replace (cap * 2 ^ 1 + cap) with (3 * cap) by lia.
  unfold OUT_LEN, HEAD_MALLOC3. replace (3 * (cap + 1)) with (3 * cap + 3) by lia.
  (* 0x1407c: the evt's end *)
  apply evt_done. do 15 eexists. exists m1.
  split; [reflexivity|].
  split; [exact (dp_rw_bytes _ _ _ _ CB1)|].
  split; [exact MU1|]. split; [exact WM1 | exact MI1].
Qed.
