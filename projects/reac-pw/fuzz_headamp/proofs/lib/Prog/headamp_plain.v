(** The plain parse and check_plain in LLVMFuzzerTestOneInput (plain): the walk of [0x14184, 0x141b4) against
    headamp_plain_contract (Prog/LLVMFuzzerTestOneInput_c.v), from the contracts of memset (Prog/memset_c.v),
    reac_headamp_prop_parse (Prog/reac_headamp_prop_parse_c.v) and check_plain (Prog/check_plain_c.v).

    0x14184-0x1418c a1 = 0xa5, a0 = out, a2 = 3 cap + 3 and `jal memset` at 0x14190 (MEMSET 0x1d64c, ra = 0x14194):
    out's writable cells, written whole; 0x14194-0x1419c a0 = s5 = (null ? 0 : pod), a1 = out, a2 = cap and
    `jal reac_headamp_prop_parse` at 0x141a0 (0x14874, ra = 0x141a4): its parse_args from the premises carried over
    memset's write of out (the pod bytes, their length and top size word (Pod/Spa.v buf_header), out writable and
    apart, res = NULL, errno a cell apart from the stack and the three blocks, the SSP cells), the stack region [lo, sp)
    with lo + 528 <= sp, frm0 fc; it answers o = head_ans nl cap inp, with out[0, 3n) = o's cells; 0x141a4-0x141ac
    a1 = s6 = rc, a2 = out, a3 = first and `jal check_plain` at 0x141b0 (0x14818, ra = 0x141b4): a0 = a1 since both
    are ans_rc o, and for rc > 0 out and first hold the same 3 rc bytes (first's from the premise, carried over memset
    and the parse: first's 3 max(rc, 0) bytes lie apart from out, errno and the stack); its frame [sp - 16, sp) lies
    in the stack region. The writes: out (memset, the parse), [sp - 528, sp) and errno (the parse), [sp - 16, sp)
    (check_plain); the frame's locals [sp, sp + 0x1b0) are kept, so stk holds over [lo, sp + 0x1b0) at the end. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import memset_c reac_headamp_prop_parse_result_c
  reac_headamp_prop_parse_c check_plain_c HeadSites SlotInv LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** The record's buffer: 8 <= len <= 5440 and its top size word len - 8. *)
Lemma hp_len : forall inp, 8 <= head_len inp <= 5440 /\
  u32_at (buf (head_rec inp)) 0 = Z.of_nat (length (buf (head_rec inp))) - 8.
Proof.
  intros inp. unfold head_len, head_rec.
  destruct (pod_build inp) as [r rest] eqn:E. cbn [fst].
  destruct (buf_header r (pod_build_wf inp r rest E)) as (_ & _ & H1 & H2). split; [exact H2 | exact H1].
Qed.

(** The parse's answer: its cells take 3 max(rc, 0) bytes, -1 <= rc <= cap. *)
Lemma hp_cells : forall cap o, 0 <= cap -> answer_ok cap o ->
  Z.of_nat (length (ha_cells_bytes (ans_cells o))) = 3 * Z.max (ans_rc o) 0 /\ -1 <= ans_rc o <= cap /\
  Z.of_nat (length (ans_cells o)) = Z.max (ans_rc o) 0.
Proof.
  intros cap o Hc H. rewrite length_ha_cells_bytes.
  apply answer_ok_parts in H as [[(E1 & E2 & _) | (E1 & E2 & _)] _].
  - rewrite E2. cbn [length]. lia.
  - lia.
Qed.

Theorem headamp_plain_holds : memset_c.memset_contract ->
  reac_headamp_prop_parse_c.reac_headamp_prop_parse_contract -> check_plain_c.check_plain_contract ->
  headamp_plain_contract.
Proof.
  intros MSET PARSE CKP. unfold headamp_plain_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    inp junk nl cap pod out first lo ev can -> -> -> -> -> -> Hnl Hcap Hpod0 Hpod16 HPOD Hout0 HOUT HOROM HFST
    HSOP HSFO HOLO HPLO HFLO ST HMID HSP16 HROM HERR HEd HG1 HG2 HG1d HG2d HFRM MI.
  destruct (hp_len inp) as [HL HU].
  pose proof (parse_answer (nl =? 1) (buf (head_rec inp)) cap ltac:(lia) ltac:(unfold head_len in HL; lia))
    as [HA _].
  change (parse_props (parse_arg (nl =? 1) (buf (head_rec inp))) cap) with (head_ans nl cap inp) in HA.
  destruct (hp_cells cap _ ltac:(lia) HA) as (HCB & HRC & HCN).
  pose proof (rw_cells_bound rsegs m out _ HOUT) as HOB. cbn [cells_size csize] in HOB.
  rewrite ?Nat.add_0_r, Z2Nat.id in HOB by (unfold OUT_LEN; lia).
  pose proof (rw_cells_bound rsegs m _ _ HERR) as HEB. cbn [cells_size csize] in HEB.
  pose proof ST as (HST0 & HST1 & _).
  pose proof HFST as (HF0 & HF1 & _). rewrite HCB in HF1.
  pose proof (bv_unsigned_in_range 64 sp) as HSPR. unfold bv_modulus in HSPR.
  unfold MID_STACK, PARSE_STACK, FRAME_LOCALS, OUT_LEN in *.
  unfold HEAD_PLAIN, HEAD_FREE.
  (* 0x14184 addi a1,zero,0xa5; mv a0,s3; mv a2,s4; 0x14190 jal memset *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := junk); rewrite ?unsigned_lit by lia.
    - exact HOUT.
    - exact MI. }
  (* 0x14194: back from memset; the premises carried over its write of out *)
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                     E & MU1 & WM1 & MI1 & CB1).
  subst ms'. rewrite !unsigned_lit in MU1, CB1 by lia.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  assert (HOW1 : wr_at rsegs m1 out (3 * (cap + 1))).
  { destruct CB1 as [_ HW]. cbn [cells_size csize] in HW. rewrite Nat.add_0_r, Z2Nat.id in HW by lia. exact HW. }
  clear CB1.
  assert (HPOD1 : bytes_at rsegs m1 pod (buf (head_rec inp))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HPOD MU1). change (Z.of_nat (length (buf (head_rec inp)))) with (head_len inp).
    cbn [disjoint_from]. lia. }
  assert (HERR1 : rw_cells rsegs m1 (PARSE_ERRNO tp) [C4 ev]).
  { apply (rw_cells_transport rsegs _ m m1 _ _ HERR MU1 WM1). cbn [disjoint_from cells_size csize] in HEd |- *. lia. }
  assert (HG11 : bytes_at rsegs m1 PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HG1 MU1). rewrite length_le8. cbn [disjoint_from] in HG1d |- *. lia. }
  assert (HG21 : bytes_at rsegs m1 PARSE_SSP_GUARD (le8 can)).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HG2 MU1). rewrite length_le8. cbn [disjoint_from] in HG2d |- *. lia. }
  destruct (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + 432) ST ltac:(lia)) as [STL STH].
  assert (STL1 : stk rsegs m1 lo (bv_unsigned sp)).
  { apply (stk_transport_disjoint rsegs _ m m1 _ _ STL MU1 WM1). cbn [disjoint_from]. lia. }
  (* 0x14194 mv a0,s5; mv a1,s3; mv a2,s2; 0x141a0 jal reac_headamp_prop_parse *)
  step. step. step. step.
  eapply evt_cut.
  { eapply PARSE with (null := nl =? 1) (lo := lo) (P := pod) (O := out) (cap := cap) (bs := buf (head_rec inp))
                      (ev := ev) (can := can).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold parse_args, parse_space. cbn [Z.eqb app].
      change (Z.of_nat (length (buf (head_rec inp)))) with (head_len inp) in HU |- *.
      cbn [disjoint_from] in HEd, HG1d, HG2d |- *.
      split; [exact HPOD1|]. split; [lia|]. split; [exact Hpod16|]. split; [lia|]. split; [exact HU|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HOW1|]. split; [lia|]. split; [lia|].
      split; [left; reflexivity|]. split; [exact HERR1|]. split; [lia|]. split; [left; reflexivity|].
      split; [exact HG11|]. split; [exact HG21|]. split; lia.
    - exact STL1.
    - unfold PARSE_STACK. lia.
    - intros a Ha. apply HROM. lia.
    - exact HFRM.
    - exact MI1. }
  (* 0x141a4: back from the parse *)
  intros ms' Hpost. unfold parse_post in Hpost.
  destruct Hpost as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                     F' & fc' & m2 & ev' & E & HFRM2 & MU2 & HC2 & _ & HERR2 & WM2 & MI2 & ST2).
  subst ms'.
  change (parse_props (parse_arg (nl =? 1) (buf (head_rec inp))) cap) with (head_ans nl cap inp) in MU2, HC2 |- *.
  unfold parse_writes, PARSE_STACK in MU2. cbn [Z.eqb app] in MU2.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  assert (HFST2 : bytes_at rsegs m2 first (ha_cells_bytes (ans_cells (head_ans nl cap inp)))).
  { apply (bytes_at_transport rsegs _ m1 m2 _ _
             (bytes_at_transport rsegs _ m m1 _ _ HFST MU1 ltac:(rewrite HCB; cbn [disjoint_from]; lia)) MU2).
    rewrite HCB. cbn [disjoint_from] in HEd |- *. lia. }
  (* 0x141a4 mv a1,s6; mv a2,s3; mv a3,s7; 0x141b0 jal check_plain *)
  step. step. step. step.
  eapply evt_cut.
  { eapply CKP with (lo := lo) (rc := ans_rc (head_ans nl cap inp))
                    (w := ha_cells_bytes (ans_cells (head_ans nl cap inp))).
    - reflexivity.
    - reflexivity.
    - lia.
    - intros Hpos. rewrite !unsigned_lit by lia.
      split; [lia|]. split; [exact HC2|]. split; [lia|]. split; [exact HFST2 | lia].
    - exact ST2.
    - unfold CHECK_PLAIN_FRAME. lia.
    - intros a Ha. apply HROM. lia.
    - exact MI2. }
  (* 0x141b4: back from check_plain *)
  intros ms' (a0''' & a1''' & a2''' & a3''' & a4''' & m3 & E & MU3 & WM3 & MI3 & ST3).
  subst ms'. unfold CHECK_PLAIN_FRAME in MU3.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  (* the post: every s register kept, errno a cell, the writes inside the munch list, stk over [lo, sp + 0x1b0) *)
  apply evt_done. do 18 eexists. exists m3, ev'.
  split; [reflexivity|].
  split; [exact HFRM2|].
  split.
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ HERR2 MU3 WM3). cbn [disjoint_from cells_size csize] in HEd |- *. lia. }
  split.
  { refine (munch_trans _ m m1 m3 (munch_weaken _ _ m m1 _ MU1)
              (munch_trans _ m1 m2 m3 (munch_weaken _ _ m1 m2 _ MU2) (munch_weaken _ _ m2 m3 _ MU3)));
      unfold sub_fp; cbn [outside]; intros x Hx; lia. }
  split; [exact (wmono_trans rsegs m m1 m3 WM1 (wmono_trans rsegs m1 m2 m3 WM2 WM3))|].
  split; [exact MI3|].
  apply (stk_merge rsegs m3 lo (bv_unsigned sp) (bv_unsigned sp + 432) ST3); [| lia].
  apply (stk_transport_disjoint rsegs _ m2 m3 _ _
           (stk_transport_disjoint rsegs _ m1 m2 _ _
              (stk_transport_disjoint rsegs _ m m1 _ _ STH MU1 WM1 ltac:(cbn [disjoint_from]; lia))
              MU2 WM2 ltac:(cbn [disjoint_from] in HEd |- *; lia))
           MU3 WM3).
  cbn [disjoint_from]. lia.
Qed.
