(** headamp_dup_pod_contract (U/Prog/LLVMFuzzerTestOneInput_c.v), [0x140e4, 0x14114) of the UBSan image:
    pod = fuzz_dup(pp->buf, len) past its malloc (fuzz.h:75-78), then out's request (fuzz_headamp.c:326).
    0x140e4 `beqz a0` not taken (pod <> 0); 0x140e8 `mv s1,a0`; 0x140ec `lbu s2,8(sp)`, the low byte of the cell
    sp + 0x8 = cap (cap <= 9); 0x140f0 `beqz s3` not taken (len = |buf r| >= 8, Pod/Spa.v buf_header);
    `mv a0,s1; mv a1,s8; mv a2,s3` and memcpy(pod, pp, len) at 0x14100 (ra 0x14104) by U/Prog/memcpy_c.v's contract,
    the source being the first len bytes of pp_bytes r, which are buf r (Pod/Layout.v pp_image_tail); then
    `slli s0,s2,1; add s0,s0,s2` (3 cap), `addi s4,s0,3` (3 cap + 3), `mv a0,s4`, up to the `jal malloc` at
    0x14114. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c EvtFacts.
Import ListNotations.
Open Scope Z_scope.

(** 3 cap and 3 cap + 3 as `slli; add; addi` compute them. *)
Lemma triple_lit : forall c, 0 <= c <= 9 -> Z.shiftl (bv_unsigned (Z_to_bv 64 c)) 1 + c = 3 * c.
Proof. intros c Hc. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Theorem headamp_dup_pod_holds : memcpy_c.memcpy_contract -> headamp_dup_pod_contract.
Proof.
  intros MCPY. unfold headamp_dup_pod_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    inp junk cap pp pod -> Hp0 -> -> Hcap HCAP HPP HPC HSEP HMI.
  set (r := head_rec inp) in *.
  assert (HB : pod_build inp = (r, snd (pod_build inp))) by (unfold r, head_rec; apply surjective_pairing).
  pose proof (pod_build_wf inp r _ HB) as HWF.
  destruct (buf_header r HWF) as (_ & _ & _ & HL).
  assert (HLEN : head_len inp = Z.of_nat (length (buf r))) by reflexivity.
  rewrite HLEN in HPC, HSEP |- *.
  set (len := Z.of_nat (length (buf r))) in *.
  assert (HBUF : bytes_at rsegs m pp (buf r)).
  { unfold pp_bytes in HPP. rewrite pp_image_tail in HPP. apply bytes_at_app in HPP as [H _]. exact H. }
  destruct (bytes_at_bound rsegs m pp _ HBUF) as [HPP0 HPP1].
  destruct (rw_cells_bound rsegs m pod _ HPC) as [HP0 HP1]. cbn [cells_size csize] in HP1.
  rewrite Nat.add_0_r, Z2Nat.id in HP1 by lia.
  unfold HEAD_DUP_POD, HEAD_MALLOC3, POD_PROPS in *.
  (* 0x140e4 beqz a0; 0x140e8 mv s1,a0 *)
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  step.
  (* 0x140ec lbu s2,8(sp) *)
  pose proof (read_byte0 m (bv_unsigned sp + 8) _ HCAP) as HR. step. clear HR.
  rewrite zx8_small by lia.
  (* 0x140f0 beqz s3 *)
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x140f4 mv a0,s1; mv a1,s8; mv a2,s3; jal memcpy *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MCPY with (src := buf r) (junk := junk).
    - rewrite unsigned_lit by lia. exact HBUF.
    - rewrite unsigned_lit by lia. unfold len. lia.
    - rewrite !unsigned_lit by lia. exact HPC.
    - rewrite !unsigned_lit by lia. lia.
    - exact HMI. }
  intros ms' Hpost. unfold memcpy_c.memcpy_post in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                     E & MU1 & WM1 & MI1 & CB1 & _).
  subst ms'. rewrite !unsigned_lit in MU1, CB1 by lia. ret_even.
  (* 0x14104 slli s0,s2,1; add s0,s0,s2; addi s4,s0,3; mv a0,s4 *)
  step. step. step. step.
  rewrite (triple_lit cap) by lia.
  replace (3 * cap + 3) with (OUT_LEN cap) by (unfold OUT_LEN; lia).
  apply evt_done. do 15 eexists. exists m1. split; [reflexivity|].
  split; [exact (rw_cells_CB_bytes m1 pod _ _ CB1)|].
  split; [exact MU1|]. split; [exact WM1 | exact MI1].
Qed.
