(** The walk of reac-pw/fuzz_role's LLVMFuzzerTestOneInput (UBSan) from malloc(pod)'s return (0x13f34) to the pc
    after check_code's return (0x141b4), against U/Prog/LLVMFuzzerTestOneInput_c.v's role_check_contract, with the
    callee contracts (U/Prog/*_c.v) as Section hypotheses. As the plain walk (Prog/RoleCheck/Walk.v), walked
    backwards: QC_done (0x141b4), code_ok (0x14194), answer_ok (0x14164), tail_ok (0x14148), absent_ok (0x140f0),
    malformed_ok (0x1413c), role_ok (0x14208), flag_ok (0x14134), float_ok (0x14108), value_ok (0x140a0); the
    pod_next_pair scan (outer_ok 0x13fdc; at 0x14004 an empty key slot, none_ok, or a key in it, some_ok with strcmp
    against "reac.cfg.role"; end_ok 0x14058), by induction on the entries left (scan_ok); setup_ok (0x13f94),
    after_parse (0x13f70), after_cpy (0x13f54) and head_ok (0x13f34). The UBSan checks on the way (the bounds of
    ent[*at] and ent[v], the pointer overflows of ent + 104 at and body + size - 1, the overflow of the increment of at) are each
    shown not taken: n_ent <= 32, e_size <= 45, and the pp block lies below the stack. The memory carries
    refuse_code's codes[] table (U/Prog/RoleCheck/Facts.v ctbl), which no write of the segment reaches. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import memcpy_c reac_role_prop_parse_c strcmp_c
  pod_nearest_c check_absent_c check_role_c check_malformed_c reac_role_cfg_changes_c reac_role_cfg_apply_state_c
  check_answer_c reac_role_refuse_code_c check_code_c SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Nearest Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleCheck Require Import Facts.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleCheck Require Import Facts.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).
(* Register equations at a loop head. *)
Ltac weq := first [ reflexivity
                  | (rewrite addiw1_small by lia; f_equal; lia)
                  | (f_equal; lia)
                  | (f_equal; rewrite ?unsigned_lit by lia; lia) ].

Section Check.
Variables (sp gp tp : word) (m : word -> option byte) (len pp pod lo fl : Z).

Local Abbreviation SP := (bv_unsigned sp).

Hypothesis HPOD : 0 < pod.
Hypothesis HLEN0 : 0 <= len.
Hypothesis HPODLO : pod + len <= lo.
Hypothesis HPP0 : 0 <= pp.
Hypothesis HPPLO : pp + 19744 <= lo.
Hypothesis HLO0 : 0 <= lo.
Hypothesis HLO : lo + 96 <= SP.
Hypothesis HSPT : SP + 440 <= 2^64.
Hypothesis HSPA : SP mod 16 = 0.
Hypothesis HROM : forall a, lo <= a < SP + 440 -> seg_rom rsegs (wa a) = None.
Hypothesis HPROM : forall a, pod <= a < pod + len -> seg_rom rsegs (wa a) = None.
Hypothesis HFL : 0 <= fl < 256.

Definition QC : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s9' s10' s11'
                     t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pod) a0' a1' a2' a3' a4' a5' a6' a7'
                  s2' s3' s4' s5' s6' s7' (Z_to_bv 64 pp) s9' s10' s11' t3' t4' t5' t6')
             F' (Z_to_bv 64 ROLE_FREE) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\
    munch [(SP - MID_STACK, SP + FRAME_LOCALS); (pod, pod + len)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (SP + FRAME_LOCALS).

(** The footprint and the memory the walk carries, with refuse_code's table read as the image. *)
Definition WC : list (Z * Z) := [(SP - 96, SP + 440); (pod, pod + len)].
Definition MemT (m1 : word -> option byte) : Prop :=
  munch WC m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (SP + 440) /\ ctbl m1.

Lemma table_out : forall a, CODES_LO <= a < CODES_HI -> outside WC a.
Proof.
  intros a Ha. unfold WC. cbn [outside]. pose proof (codes_apart lo (SP + 440) HROM a Ha) as H1.
  pose proof (codes_apart pod (pod + len) HPROM a Ha) as H2. split; [lia|]. split; [exact H2 | exact I].
Qed.

Lemma MemT_store : forall m1 a bs, MemT m1 -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP - 96 <= a -> a + Z.of_nat (length bs) <= SP + 440 -> MemT (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs (MU & WM & MI & ST & TB) HS H1 H2. pose proof ST as (ST0 & ST1 & _).
  split; [apply munch_write; [exact MU | lia | lia | unfold WC; cbn [inside]; left; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | exact HS]|].
  split; [apply stk_write; [exact ST | lia | lia]|].
  apply (ctbl_munch [(a, a + Z.of_nat (length bs))] m1); [exact TB | |].
  - apply munch_write; [apply munch_refl | lia | lia | cbn [inside]; left; lia].
  - intros x Hx. pose proof (table_out x Hx) as O. unfold WC in O. cbn [outside] in O |- *.
    destruct O as (O1 & _). split; [lia | exact I].
Qed.

(** A callee whose footprint lies below the stack top or in the frame's locals. *)
Lemma MemT_call : forall m1 m2 W, MemT m1 -> munch W m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo SP -> sub_fp W WC ->
  (forall x, SP <= x < SP + 440 -> outside W x \/ exists b, m2 (wa x) = Some b) -> MemT m2.
Proof.
  intros m1 m2 W (MU & WM & MI & ST & TB) MU2 WM2 MI2 ST2 SUB HX.
  split; [exact (munch_trans WC m m1 m2 MU (munch_weaken W WC m1 m2 SUB MU2))|].
  split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
  split; [exact MI2|].
  split.
  { destruct (stk_split rsegs m1 lo SP (SP + 440) ST ltac:(lia)) as [_ ST1].
    apply (stk_merge rsegs m2 lo SP); [exact ST2 | | lia].
    exact (stk_transport rsegs W m1 m2 SP (SP + 440) ST1 MU2 WM2 HX). }
  apply (ctbl_munch W m1 m2 TB MU2). intros a Ha. apply SUB. exact (table_out a Ha).
Qed.

Lemma MemT_below : forall m1 m2 k, MemT m1 -> munch [(SP - k, SP)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo SP -> 0 <= k <= 96 -> MemT m2.
Proof.
  intros m1 m2 k MT MU WM MI ST Hk. apply (MemT_call m1 m2 [(SP - k, SP)] MT MU WM MI ST).
  - unfold sub_fp, WC. cbn [outside]. intros x (O1 & _ & _). split; [lia | exact I].
  - intros x Hx. left. cbn [outside]. split; [lia | exact I].
Qed.

Lemma MemT_stk : forall m1, MemT m1 -> stk rsegs m1 lo SP.
Proof. intros m1 (_ & _ & _ & ST & _). exact (proj1 (stk_split rsegs m1 lo SP (SP + 440) ST ltac:(lia))). Qed.

Hypothesis CHG : reac_role_cfg_changes_contract.
Hypothesis APS : reac_role_cfg_apply_state_contract.
Hypothesis CKA : check_answer_contract.
Hypothesis RFC : reac_role_refuse_code_contract.
Hypothesis CKC : check_code_contract.

(** 0x141b4: the contract's postcondition. *)
Lemma QC_done : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 pp) s9
             s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ROLE_FREE) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF
    (MU & WM & MI & ST & _).
  apply evt_done. exists ra, t0, t1, t2, s0, a0, a1, a2, a3, a4, a5, a6, a7, s2, s3, s4, s5, s6, s7, s9, s10, s11,
    t3, t4, t5, t6, F, fc, m1.
  split; [reflexivity|]. split; [exact HF|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST].
Qed.

(** 0x14194 .. 0x141b4: check_code(refuse_code(0), refuse_code(1)). *)
Lemma code_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 pp) s9
             s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14194) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT.
  pose proof MT as (_ & _ & MI & _ & TB).
  assert (TB' : forall a, REFUSE_TBL <= a < REFUSE_TBL + REFUSE_TBL_SIZE -> mrd rsegs m1 (wa a) = seg_rom rsegs (wa a))
    by (intros a Ha; apply TB; unfold REFUSE_TBL, REFUSE_TBL_SIZE, CODES_LO, CODES_HI in *; lia).
  (* 0x14194 mv a0,zero; jal reac_role_refuse_code *)
  step. step.
  eapply evt_cut; [eapply RFC; exact TB'|]. intros ms' (a1x & a2x & a3x & ->). ret_even.
  match goal with |- context [refuse_code_res ?x] => replace (refuse_code_res x) with CODE_NONE by (vm_compute; reflexivity) end.
  (* 0x1419c mv s2,a0; addi a0,zero,1; jal reac_role_refuse_code *)
  step. step. step.
  eapply evt_cut; [eapply RFC; exact TB'|]. intros ms' (a1y & a2y & a3y & ->). ret_even.
  match goal with |- context [refuse_code_res ?x] => replace (refuse_code_res x) with CODE_MALFORMED by (vm_compute; reflexivity) end.
  (* 0x141a8 mv a1,a0; mv a0,s2; jal check_code *)
  step. step. step.
  eapply evt_cut.
  { eapply CKC with (lo := lo); [reflexivity | reflexivity | exact (MemT_stk m1 MT) | unfold CHECK_CODE_FRAME; lia
                                | intros a Ha; apply HROM; lia | exact MI]. }
  intros ms' (a0' & a1' & a2' & a3' & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'. ret_even.
  apply QC_done; [exact HF|].
  apply (MemT_below m1 m2 CHECK_CODE_FRAME MT MU2 WM2 MI2 ST2). unfold CHECK_CODE_FRAME. lia.
Qed.

(** 0x14164 .. 0x14190: check_answer(changes(cur, req), apply_state(cur, req), cur, req) with s3 = cur, s2 = req. *)
Lemma answer_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 pp) s9
             s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14164) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT.
  pose proof MT as (_ & _ & MI & _).
  (* 0x14164 mv a0,s3; mv a1,s2; jal reac_role_cfg_changes *)
  step. step. step.
  eapply evt_cut; [eapply CHG|]. intros ms' ->. ret_even.
  (* 0x14170 mv s4,a0; mv a0,s3; mv a1,s2; jal reac_role_cfg_apply_state *)
  step. step. step. step.
  eapply evt_cut; [eapply APS|]. intros ms' ->. ret_even.
  (* 0x14180 mv a1,a0; mv a0,s4; mv a2,s3; mv a3,s2; jal check_answer *)
  step. step. step. step. step.
  eapply evt_cut.
  { eapply CKA with (lo := lo); [reflexivity | reflexivity | exact (MemT_stk m1 MT) | unfold CHECK_ANSWER_FRAME; lia
                                | intros a Ha; apply HROM; lia | exact MI]. }
  intros ms' (a0' & a1' & a2' & a3' & a4' & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'. ret_even.
  apply code_ok; [exact HF|].
  apply (MemT_below m1 m2 CHECK_ANSWER_FRAME MT MU2 WM2 MI2 ST2). unfold CHECK_ANSWER_FRAME. lia.
Qed.

(** 0x14148 .. 0x14160: cur = fl bit 1 (s3 = fl), req = rc == 1 ? role : !cur. *)
Lemma tail_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 pp) s9
             s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14148) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT.
  pose proof MT as (_ & _ & _ & ST & _).
  (* 0x14148 slli a0,s3,62; addi a1,zero,1; srli s3,a0,63; beq s2,a1 *)
  step. step. step. step. if_cases E.
  - (* 0x14160 lw s2,0x158(sp) *)
    destruct (stk_read rsegs m1 lo (SP + 440) (SP + 344) 4 ST ltac:(lia) ltac:(lia)) as (bs & HR).
    step. clear HR. eapply answer_ok; [exact HF | exact MT].
  - (* 0x14158 xori s2,s3,1; j 0x14164 *)
    step. step. eapply answer_ok; [exact HF | exact MT].
Qed.

Hypothesis CKAB : check_absent_contract.
Hypothesis CKR : check_role_contract.
Hypothesis CKM : check_malformed_contract.

(** 0x140f0 .. 0x14104: check_absent(rc, role), then s8 = pp and s3 = fl again. *)
Lemma absent_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s2 = 0 ->
  bytes_at rsegs m1 (SP + 344) (le4 (Z_to_bv 64 0x5a)) -> bytes_at rsegs m1 (SP + 104) (le8 (Z_to_bv 64 pp)) ->
  bytes_at rsegs m1 (SP + 16) (le8 (Z_to_bv 64 fl)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x140f0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT H2 HC H68 H10.
  pose proof (read_le4_cell rsegs m1 (SP + 344) _ HC) as HR.
  (* 0x140f0 lw a1,0x158(sp); mv a0,s2; jal check_absent *)
  step. clear HR. rewrite sx32_small by lia. step. step.
  eapply evt_cut; [eapply CKAB; [exact H2 | reflexivity]|]. intros ms' ->. ret_even.
  (* 0x140fc ld s8,0x68(sp); ld s3,0x10(sp); j 0x14148 *)
  pose proof (read_le8 rsegs m1 (SP + 104) _ H68) as HR. step. clear HR.
  pose proof (read_le8 rsegs m1 (SP + 16) _ H10) as HR. step. clear HR.
  step. eapply tail_ok; [exact HF | exact MT].
Qed.

(** 0x1413c .. 0x14144: check_malformed(rc, role), returning to 0x14148. *)
Lemma malformed_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
                            (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s2 = 2^64 - 1 ->
  bytes_at rsegs m1 (SP + 344) (le4 (Z_to_bv 64 0x5a)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 pp) s9
             s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1413c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT H2 HC.
  pose proof (read_le4_cell rsegs m1 (SP + 344) _ HC) as HR.
  (* 0x1413c lw a1,0x158(sp); mv a0,s2; jal check_malformed *)
  step. clear HR. rewrite sx32_small by lia. step. step.
  eapply evt_cut; [eapply CKM; [exact H2 | reflexivity]|]. intros ms' ->. ret_even.
  eapply tail_ok; [exact HF | exact MT].
Qed.

(** 0x14208 .. 0x14218: check_role(rc, role, want) for want = v, 0 or 1. *)
Lemma role_ok : forall (ra t0 t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (v : Z),
  frm0 fc -> MemT m1 -> bv_unsigned s2 = 1 -> 0 <= v < 2 ->
  bytes_at rsegs m1 (SP + 344) (le4 (Z_to_bv 64 v)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
             (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14208) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m1 v HF MT H2 Hv HC.
  pose proof (read_le4_cell rsegs m1 (SP + 344) _ HC) as HR.
  (* 0x14208 lw a1,0x158(sp); sext.w a2,a2; mv a0,s2; jal check_role *)
  step. clear HR. rewrite sx32_small by lia. step. rewrite sextw_small by lia. step. step.
  eapply evt_cut; [eapply CKR; [exact H2 | reflexivity]|]. intros ms' ->. ret_even.
  (* 0x14218 j 0x14148 *)
  step. eapply tail_ok; [exact HF | exact MT].
Qed.

(** ** expect_role over the record in pp *)
Variable r : pod_rec.
Hypothesis HWF : pod_rec_wf r.
Local Abbreviation es := (ents r).
Local Abbreviation n := (length (ents r)).
Local Abbreviation E0 := (expect_model false r).

(** The memory of the scan: MemT, the record at pp, the cells sp + 0x10 = fl and sp + 0x68 = pp, the role cell,
    MemNorm.task_mem. *)
Definition MemS (m1 : word -> option byte) (c : Z) : Prop :=
  MemT m1 /\ bytes_at rsegs m1 pp (pp_bytes r) /\ bytes_at rsegs m1 (SP + 16) (le8 (Z_to_bv 64 fl)) /\
  bytes_at rsegs m1 (SP + 104) (le8 (Z_to_bv 64 pp)) /\ bytes_at rsegs m1 (SP + 344) (le4 (Z_to_bv 64 c)) /\
  MemNorm.task_mem rsegs m1.

Lemma len_pp : Z.of_nat (length (pp_bytes r)) = 19744.
Proof. exact (length_pp_bytes r HWF). Qed.

(** A store into the frame's locals off the three cells and the record. *)
Lemma MemS_store : forall m1 c a bs, MemS m1 c -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP - 96 <= a -> a + Z.of_nat (length bs) <= SP + 440 ->
  or_h (a + Z.of_nat (length bs) <= SP + 16) (SP + 24 <= a) ->
  or_h (a + Z.of_nat (length bs) <= SP + 104) (SP + 112 <= a) ->
  or_h (a + Z.of_nat (length bs) <= SP + 344) (SP + 348 <= a) ->
  MemS (write_to_mem m1 (wa a) bs) c.
Proof.
  intros m1 c a bs (MT & HP & H10 & H68 & HC & TM) HS H1 H2 D1 D2 D3. unfold or_h in *.
  pose proof len_pp as LP.
  split; [exact (MemT_store m1 a bs MT HS H1 H2)|].
  split; [apply bytes_at_write_other; [exact HP | lia | lia | lia]|].
  split; [apply bytes_at_write_other; [exact H10 | lia | lia | rewrite length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact H68 | lia | lia | rewrite length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact HC | lia | lia | rewrite length_le4; lia]|].
  exact (task_mem_write_u m1 (wa a) bs TM HS).
Qed.

Lemma role_key_at : forall m1, mem_inv rsegs m1 -> bytes_at rsegs m1 0x1032e (ROLE_KEY ++ [Z_to_bv 8 0]).
Proof.
  intros m1 MI.
  assert (RO : ro_cells rsegs m1 0x1032e [CB (length (ROLE_KEY ++ [Z_to_bv 8 0])) (ROLE_KEY ++ [Z_to_bv 8 0])]).
  { apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | vm_compute; congruence]. }
  destruct RO as [_ RB]. cbn [cells_bytes cbytes] in RB. rewrite app_nil_r in RB. exact RB.
Qed.

Lemma role_key_no_nul : ~ In (Z_to_bv 8 0) ROLE_KEY.
Proof.
  intros H. assert (F : forallb (fun b : byte => negb (bv_unsigned b =? 0)) ROLE_KEY = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. specialize (F _ H). vm_compute in F. discriminate F.
Qed.

Hypothesis STRC : strcmp_contract.
Hypothesis NEAR : pod_nearest_contract.

(** 0x14134 .. 0x14138: the flag test `flag < 2` (unsigned) on a2 = v, an int32. *)
Lemma flag_ok : forall (ra t0 t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (v : Z),
  frm0 fc -> MemT m1 -> -2^31 <= v < 2^31 ->
  bv_unsigned s2 = snd (flag_rc v) mod 2^64 ->
  bytes_at rsegs m1 (SP + 344) (le4 (Z_to_bv 64 (rcell (fst (flag_rc v))))) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
             (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14134) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m1 v HF MT Hv H2 HC.
  (* 0x14134 addi a0,zero,2; bltu a2,a0 *)
  step. step. rewrite ltu2_s by lia.
  destruct (Z.leb_spec 0 v) as [V1|V1]; destruct (Z.ltb_spec v 2) as [V2|V2]; cbn [andb].
  - destruct (flag_rc_in v ltac:(lia)) as (EF & EZ). rewrite EF in H2, HC. cbn [fst snd rcell] in H2, HC.
    rewrite EZ in HC. eapply role_ok; [exact HF | exact MT | rewrite H2; reflexivity | lia | exact HC].
  - rewrite (flag_rc_out v ltac:(lia)) in H2, HC. cbn [fst snd rcell] in H2, HC.
    eapply malformed_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC].
  - rewrite (flag_rc_out v ltac:(lia)) in H2, HC. cbn [fst snd rcell] in H2, HC.
    eapply malformed_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC].
  - rewrite (flag_rc_out v ltac:(lia)) in H2, HC. cbn [fst snd rcell] in H2, HC.
    eapply malformed_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC].
Qed.

(** 0x14108 .. 0x14130: pod_float, pod_nearest(f, &flag), then the flag test. *)
Lemma float_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (i : nat),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  (i < n)%nat -> E0 = expect_value (nth i es (Ent 0 0 [])) -> e_type (nth i es (Ent 0 0 [])) = POD_FLOAT ->
  s4 = Z_to_bv 64 (pp + 16404 + 104 * Z.of_nat i) -> s5 = Z_to_bv 64 (104 * Z.of_nat i) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 pp) s9
             s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14108) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m1 i HF MS1 H2 Hi HV Ht
    -> ->.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof (ent_wf_nth r i HWF Hi) as (Ht0 & Hb & Hsz).
  pose proof MS1 as (MT & HPPB & H10 & H68 & HC & TM). pose proof MT as (MU & WM & MI & ST & TB).
  pose proof (bytes_at_ent rsegs m1 pp r i HPPB HWF Hi) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat i) with (pp + 16404 + 104 * Z.of_nat i) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  rewrite HV, (ev_float _ Ht) in H2, HC.
  (* 0x14108 lw a0,4(s4); addi a1,zero,4; bltu a0,a1 *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size (nth i es (Ent 0 0 []))) 4) as [Es|Es]; cbv beta iota.
  { rewrite (proj2 (Z.leb_gt 4 _) Es) in H2, HC. cbn [fst snd rcell] in H2, HC.
    eapply malformed_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC]. }
  rewrite (proj2 (Z.leb_le 4 _) Es) in H2, HC.
  (* 0x14114 add s5,s8,s5; lui a0,4; add a0,s5,a0; flw fa0,0x1c(a0); addi a0,sp,0xb8; jal pod_nearest *)
  step. step. step.
  pose proof (ent_word_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR.
  rewrite extract_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn.
  step. step.
  eapply evt_cut.
  { eapply NEAR with (lo := lo) (b := rd32 (e_body (nth i es (Ent 0 0 [])))).
    - apply rd32_range.
    - apply freg_get_same. reflexivity.
    - rewrite unsigned_lit by lia. apply (stk_wr_at rsegs m1 lo (SP + 440)); [exact ST | lia | lia | lia].
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. unfold POD_NEAREST_STACK. right. lia.
    - exact (MemT_stk m1 MT).
    - unfold POD_NEAREST_STACK. lia.
    - intros a Ha. apply HROM. lia.
    - exact HF.
    - exact MI.
    - exact TM. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m2 &
              E & HFk & HF' & PNM & WM2 & MI2 & TM2 & ST2).
  subst ms'. ret_even. rewrite unsigned_lit in PNM by lia.
  revert H2 HC PNM. change NEAR_LO with INT32_MIN. change NEAR_HI with INT32_MAX.
  destruct (nearest (rd32 (e_body (nth i es (Ent 0 0 [])))) INT32_MIN INT32_MAX) as [w|] eqn:EN; intros H2 HC PNM;
    cbn [pod_near_mem pod_near_rc] in PNM |- *.
  - (* a nearest integer w: 0x1412c beqz a0 not taken; 0x14130 ld a2,0xb8(sp) *)
    destruct PNM as (MU2 & HW).
    assert (MT2 : MemT m2).
    { apply (MemT_call m1 m2 _ MT MU2 WM2 MI2 ST2).
      - unfold sub_fp, WC, POD_NEAREST_STACK. cbn [outside]. intros x (O1 & _ & _). repeat split; try exact I; lia.
      - intros x Hx. unfold POD_NEAREST_STACK.
        destruct (Z_lt_le_dec x (SP + 184)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; lia|].
        destruct (Z_lt_le_dec x (SP + 192)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; lia].
        apply (bytes_at_some rsegs m2 (SP + 184) _ x HW); rewrite length_le8; [intros a Ha; apply HROM | ]; lia. }
    assert (HC2 : bytes_at rsegs m2 (SP + 344) (le4 (Z_to_bv 64 (rcell (fst (flag_rc w)))))).
    { apply (bytes_at_transport rsegs _ m1 m2 _ _ HC MU2). cbn [disjoint_from]. rewrite length_le4.
      unfold POD_NEAREST_STACK. repeat split; lia. }
    step. if_false.
    pose proof (read_le8 rsegs m2 (SP + 184) _ HW) as HR. step. clear HR.
    pose proof (nearest_range _ _ EN) as Hw. unfold INT32_MIN, INT32_MAX in Hw.
    eapply flag_ok; [exact HF' | exact MT2 | lia | exact H2 | exact HC2].
  - (* none: 0x1412c beqz a0 to check_malformed *)
    cbn [fst snd rcell] in H2, HC.
    assert (MT2 : MemT m2) by (apply (MemT_below m1 m2 POD_NEAREST_STACK MT PNM WM2 MI2 ST2); unfold POD_NEAREST_STACK; lia).
    assert (HC2 : bytes_at rsegs m2 (SP + 344) (le4 (Z_to_bv 64 0x5a))).
    { apply (bytes_at_transport rsegs _ m1 m2 _ _ HC PNM). cbn [disjoint_from]. rewrite length_le4.
      unfold POD_NEAREST_STACK. repeat split; lia. }
    step. if_true.
    eapply malformed_ok; [exact HF' | exact MT2 | rewrite H2; reflexivity | exact HC2].
Qed.

(** 0x140a0 .. 0x140ec: the value ent[v] of the role key: the bounds and overflow checks, pod_int, else pod_float. *)
Lemma value_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (v : nat),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  (v < n)%nat -> E0 = expect_value (nth v es (Ent 0 0 [])) ->
  s11 = Z_to_bv 64 (Z.of_nat v) -> s5 = Z_to_bv 64 (104 * Z.of_nat v) -> s4 = Z_to_bv 64 (pp + 16404) ->
  bv_unsigned s7 = 2^64 - 1 - (pp + 16404) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x140a0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 v HF MS1 H2 Hv HV
    -> -> -> H7.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof (ent_wf_nth r v HWF Hv) as (Ht0 & Hb & Hsz).
  pose proof MS1 as (MT & HPPB & H10 & H68 & HC & TM). pose proof MT as (MU & WM & MI & ST & TB).
  (* 0x140a0 addi a0,zero,-1; addi a1,zero,33; sd a0,0xb8(sp) *)
  step. step.
  assert (HS : store_ok rsegs m1 (wa (SP + 184)) 8 = true)
    by exact (stk_store_ok rsegs m1 lo (SP + 440) (SP + 184) 8 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 184));
    assert (MS2 : MemS (write_to_mem m1 (wa (SP + 184)) BS) (rcell (fst E0)))
      by (apply MemS_store; unfold or_h; rewrite ?length_le8; [exact MS1 | exact HS | lia | lia | lia | lia | lia]);
    revert MS2; generalize (write_to_mem m1 (wa (SP + 184)) BS) as m2; intros m2 MS2
  end.
  clear HS MU WM MI ST TB MT HPPB H10 H68 HC TM.
  pose proof MS2 as (MT & HPPB & H10 & H68 & HC & TM).
  pose proof (bytes_at_ent rsegs m2 pp r v HPPB HWF Hv) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat v) with (pp + 16404 + 104 * Z.of_nat v) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  (* 0x140ac bgeu s11,a1: the bounds of ent[v] *)
  step. rewrite ltu_u by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [negb]. cbv beta iota.
  (* 0x140b0 ld s8,0x68(sp); ld s3,0x10(sp) *)
  pose proof (read_le8 rsegs m2 (SP + 104) _ H68) as HR. step. clear HR.
  pose proof (read_le8 rsegs m2 (SP + 16) _ H10) as HR. step. clear HR.
  (* 0x140b8 bltu s7,s5: ent + 104 v does not wrap *)
  step. unfold bv_ltu at 1. rewrite H7, (unsigned_lit (104 * Z.of_nat v)) by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x140bc add s4,s4,s5; lw a0,0(s4); addi a1,zero,6; beq a0,a1 *)
  step.
  pose proof (ent_type_read rsegs m2 _ _ HEB Ht0) as HR. step. clear HR.
  step. step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth v es (Ent 0 0 []))) 6) as [Et|Et]; cbv beta iota.
  { eapply float_ok; [exact HF | exact MS2 | exact H2 | exact Hv | exact HV | exact Et | weq | weq]. }
  (* 0x140cc addi a1,zero,4; bne a0,a1 *)
  step. step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth v es (Ent 0 0 []))) 4) as [Et4|Et4]; cbn [negb]; cbv beta iota.
  2:{ assert (EV : E0 = (None, -1)) by (rewrite HV; apply ev_other; unfold POD_FLOAT, POD_INT; lia).
      rewrite EV in H2, HC. cbn [fst snd rcell] in H2, HC.
      eapply malformed_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC]. }
  (* 0x140d4 lw a0,4(s4); bltu a0,a1 *)
  pose proof (ent_size_read rsegs m2 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size (nth v es (Ent 0 0 []))) 4) as [Es|Es]; cbv beta iota.
  { assert (EV : E0 = (None, -1)) by (rewrite HV, ev_int by exact Et4; rewrite (proj2 (Z.leb_gt 4 _) Es); reflexivity).
    rewrite EV in H2, HC. cbn [fst snd rcell] in H2, HC.
    eapply malformed_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC]. }
  (* 0x140dc add s5,s8,s5; lui a0,4; add a0,s5,a0; lw a2,0x1c(a0); j 0x14134 *)
  step. step. step.
  pose proof (ent_word_read rsegs m2 _ _ HEB ltac:(lia)) as HR. step. clear HR.
  rewrite sext_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn. step.
  assert (EV : E0 = flag_rc (s32 (rd32 (e_body (nth v es (Ent 0 0 []))))))
    by (rewrite HV, ev_int by exact Et4; rewrite (proj2 (Z.leb_le 4 _) Es); reflexivity).
  rewrite EV in H2, HC.
  pose proof (s32_range _ (rd32_range (e_body (nth v es (Ent 0 0 []))))) as Hw.
  eapply flag_ok; [exact HF | exact MT | lia | exact H2 | exact HC].
Qed.

(** ** pod_next_pair's scan (0x13fdc .. 0x140a0), by induction on the entries left *)
Definition outer_P (j : nat) : Prop :=
  forall (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  E0 = role_of_pairs expect_value (pairs_by key_of (skipn j es) None) -> (j <= n)%nat ->
  a5 = Z_to_bv 64 (Z.of_nat j) -> bv_unsigned s7 = 2^64 - 1 - (pp + 16404) -> bv_unsigned s10 = 2^64 - (pp + 16413) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 pod) a0 (Z_to_bv 64 0x1032e) a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 (pp + 16404)) s5 (Z_to_bv 64 8) s7 (Z_to_bv 64 446676598784) (Z_to_bv 64 (pp + 16412))
             s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13fdc) fc None m1 (seg_rom rsegs)).

(** At 0x14004 with the key slot empty (a0 = NULL) and the scan at entry j. *)
Definition inner_none_P (j : nat) : Prop :=
  forall (ra t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  E0 = role_of_pairs expect_value (pairs_by key_of (skipn j es) None) -> (j < n)%nat ->
  a5 = Z_to_bv 64 (Z.of_nat j) -> s11 = Z_to_bv 64 (Z.of_nat j) -> s5 = Z_to_bv 64 (104 * Z.of_nat j) ->
  bv_unsigned a3 = 2^64 - (pp + 16413 + 104 * Z.of_nat j) ->
  bv_unsigned s7 = 2^64 - 1 - (pp + 16404) -> bv_unsigned s10 = 2^64 - (pp + 16413) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 pod) (Z_to_bv 64 0) (Z_to_bv 64 0x1032e)
             (Z_to_bv 64 33) a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (pp + 16404)) s5 (Z_to_bv 64 8) s7
             (Z_to_bv 64 446676598784) (Z_to_bv 64 (pp + 16412)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14004) fc None m1
        (seg_rom rsegs)).

(** At 0x14004 with the key k at ka in the slot: entry j is its value. *)
Definition inner_some_P (j : nat) (k : list byte) (ka : Z) : Prop :=
  forall (ra t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  E0 = role_of_pairs expect_value (pairs_by key_of (skipn j es) (Some k)) -> (j < n)%nat ->
  0 < ka -> bytes_at rsegs m1 ka (k ++ [Z_to_bv 8 0]) -> ka + Z.of_nat (length (k ++ [Z_to_bv 8 0])) <= lo ->
  ~ In (Z_to_bv 8 0) k ->
  a5 = Z_to_bv 64 (Z.of_nat j) -> s11 = Z_to_bv 64 (Z.of_nat j) -> s5 = Z_to_bv 64 (104 * Z.of_nat j) ->
  bv_unsigned a3 = 2^64 - (pp + 16413 + 104 * Z.of_nat j) ->
  bv_unsigned s7 = 2^64 - 1 - (pp + 16404) -> bv_unsigned s10 = 2^64 - (pp + 16413) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 pod) (Z_to_bv 64 ka) (Z_to_bv 64 0x1032e)
             (Z_to_bv 64 33) a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (pp + 16404)) s5 (Z_to_bv 64 8) s7
             (Z_to_bv 64 446676598784) (Z_to_bv 64 (pp + 16412)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14004) fc None m1
        (seg_rom rsegs)).

(** The key slot after entry j: empty, or the key k at ka. *)
Definition slot_ok (m1 : word -> option byte) (ko : option (list byte)) (ka : Z) : Prop :=
  match ko with
  | Some k => 0 < ka /\ bytes_at rsegs m1 ka (k ++ [Z_to_bv 8 0]) /\
              ka + Z.of_nat (length (k ++ [Z_to_bv 8 0])) <= lo /\ ~ In (Z_to_bv 8 0) k
  | None => True
  end.

(** 0x13fdc .. 0x14000: `at < n_ent`, else no pair is left; the bound 33 of ent[*at], ent + 104 at, k = NULL. *)
Lemma outer_ok : forall j, ((j < n)%nat -> inner_none_P j) -> outer_P j.
Proof.
  intros j HI. unfold outer_P.
  intros ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s10 s11 t3 t4 t5 t6 F fc m1 HF MS1 H2 HE Hj -> H7 H10.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  (* 0x13fdc bge a5,s0 *)
  step. rewrite lts_s by lia.
  destruct (Z.ltb_spec (Z.of_nat j) (Z.of_nat n)) as [Hl|Hl]; cbn [negb]; cbv beta iota.
  2:{ assert (EA : E0 = (None, 0)) by (rewrite HE, skipn_all2 by lia; reflexivity).
      pose proof MS1 as (MT & _ & H10c & H68 & HC & _). rewrite EA in H2, HC. cbn [fst snd rcell] in H2, HC.
      eapply absent_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC | exact H68 | exact H10c]. }
  (* 0x13fe0 slli a3,a5,32; srli s11,a3,32; addi a0,zero,33; mv a2,s11; bltu a0,s11 *)
  step. step. rewrite zext32_small by lia. step. step. step. rewrite ltu_u by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x13ff4 addi a2,zero,33; mv a0,zero; mulhu s5,a3,s8; sub a3,s10,s5 *)
  step. step. step. rewrite mulhu_idx by lia. step.
  eapply (HI ltac:(lia)); [exact HF | exact MS1 | exact H2 | exact HE | lia | weq | weq | weq | | exact H7 | exact H10].
  rewrite (unsigned_lit (104 * Z.of_nat j)) by lia. apply (unsigned_sub_bound s10 (pp + 16413)); [exact H10 | lia | lia | lia].
Qed.

(** 0x14058 .. 0x1406c: the next entry, or no pair is left. *)
Lemma end_ok : forall j, (j < n)%nat ->
  ((S j < n)%nat -> inner_none_P (S j) /\ (forall k ka, inner_some_P (S j) k ka)) ->
  forall (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 s2 s3 s5 s7 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (ko : option (list byte)) (ka : Z),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  E0 = role_of_pairs expect_value (pairs_by key_of (skipn (S j) es) ko) -> slot_ok m1 ko ka ->
  a0 = Z_to_bv 64 (match ko with Some _ => ka | None => 0 end) ->
  a5 = Z_to_bv 64 (Z.of_nat j) -> s11 = Z_to_bv 64 (Z.of_nat j) -> s5 = Z_to_bv 64 (104 * Z.of_nat j) ->
  bv_unsigned a3 = 2^64 - (pp + 16413 + 104 * Z.of_nat j) ->
  bv_unsigned s7 = 2^64 - 1 - (pp + 16404) -> bv_unsigned s10 = 2^64 - (pp + 16413) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 pod) a0 (Z_to_bv 64 0x1032e)
             (Z_to_bv 64 33) a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (pp + 16404)) s5 (Z_to_bv 64 8) s7
             (Z_to_bv 64 446676598784) (Z_to_bv 64 (pp + 16412)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14058) fc None m1
        (seg_rom rsegs)).
Proof.
  intros j Hj HI ra t0 t1 t2 a0 a3 a4 a5 a6 a7 s2 s3 s5 s7 s10 s11 t3 t4 t5 t6 F fc m1 ko ka HF MS1 H2 HE HS -> -> -> ->
    H3 H7 H10.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  (* 0x14058 addi s11,s11,1; addi s5,s5,0x68; addiw a5,a5,1; addi a3,a3,-0x68; bltu s11,s0 *)
  step. step. step. step. step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (Z.of_nat j + 1) (Z.of_nat n)) as [Hl|Hl]; cbv beta iota.
  - assert (A3 : bv_unsigned (Z_to_bv 64 (bv_unsigned a3 + -104)) = 2^64 - (pp + 16413 + 104 * Z.of_nat (S j))).
    { rewrite H3. rewrite unsigned_lit by lia. lia. }
    destruct (HI ltac:(lia)) as [HN HSm]. destruct ko as [k|].
    + destruct HS as (Hka & HK & HKl & HNK).
      eapply (HSm k ka); [exact HF | exact MS1 | exact H2 | exact HE | lia | exact Hka | exact HK | exact HKl | exact HNK
                         | weq | weq | weq | exact A3 | exact H7 | exact H10].
    + eapply HN; [exact HF | exact MS1 | exact H2 | exact HE | lia | weq | weq | weq | exact A3 | exact H7 | exact H10].
  - (* 0x1406c j 0x140f0: no pair is left *)
    step.
    assert (EA : E0 = (None, 0)) by (rewrite HE, skipn_all2 by lia; destruct ko; reflexivity).
    pose proof MS1 as (MT & _ & H10c & H68 & HC & _). rewrite EA in H2, HC. cbn [fst snd rcell] in H2, HC.
    eapply absent_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC | exact H68 | exact H10c].
Qed.

(** 0x14004 .. 0x14050: pod_string(&pp->ent[j]) on an empty key slot, with the bounds of ent[*at] and the overflow
    checks of ent + 104 j and body + size - 1. *)
Lemma none_ok : forall j, ((S j < n)%nat -> inner_none_P (S j) /\ (forall k ka, inner_some_P (S j) k ka)) ->
  inner_none_P j.
Proof.
  intros j HI. unfold inner_none_P.
  intros ra t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s10 s11 t3 t4 t5 t6 F fc m1 HF MS1 H2 HE Hj -> -> -> H3 H7 H10.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  rewrite (skipn_nth_cons es j (Ent 0 0 []) Hj), rop_cons in HE.
  pose proof (ent_wf_nth r j HWF Hj) as (Ht0 & Hb & Hsz).
  pose proof MS1 as (MT & HPPB & H10c & H68 & HC & TM).
  pose proof (bytes_at_ent rsegs m1 pp r j HPPB HWF Hj) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat j) with (pp + 16404 + 104 * Z.of_nat j) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  (* 0x14004 bnez a0; beq a2,s11; bltu s7,s5 *)
  step. if_false.
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  step. unfold bv_ltu at 1. rewrite H7, (unsigned_lit (104 * Z.of_nat j)) by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x14010 add a0,s4,s5; lw a4,0(a0); bne a4,s6 *)
  step. pose proof (ent_type_read rsegs m1 _ _ HEB Ht0) as HR. step. clear HR.
  step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth j es (Ent 0 0 []))) 8) as [Et|Et]; cbn [negb]; cbv beta iota.
  2:{ (* not a String: 0x14054 mv a0,zero *)
      assert (EK : key_of (nth j es (Ent 0 0 [])) = None)
        by (rewrite key_of_cases; unfold POD_STRING; rewrite (proj2 (Z.eqb_neq _ _) Et); reflexivity).
      rewrite EK in HE. step.
      eapply (end_ok j Hj HI) with (ko := None) (ka := 0);
        [exact HF | exact MS1 | exact H2 | exact HE | exact I | reflexivity | reflexivity | reflexivity | reflexivity
        | exact H3 | exact H7 | exact H10]. }
  (* 0x1401c lw a0,4(a0); beqz a0 *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec (e_size (nth j es (Ent 0 0 []))) 0) as [Ez|Ez]; cbv beta iota.
  { assert (EK : key_of (nth j es (Ent 0 0 [])) = None)
      by (rewrite key_of_cases; rewrite Ez; cbn [Z.leb Z.compare]; rewrite andb_false_r; reflexivity).
    rewrite EK in HE.
    eapply (end_ok j Hj HI) with (ko := None) (ka := 0);
      [exact HF | exact MS1 | exact H2 | exact HE | exact I | rewrite Ez; reflexivity | reflexivity | reflexivity
      | reflexivity | exact H3 | exact H7 | exact H10]. }
  (* 0x14024 addi a0,a0,-1; slli a0,a0,32; srli a0,a0,32; bltu a3,a0 *)
  step. step. step. rewrite zext32_small by lia.
  step. unfold bv_ltu at 1. rewrite H3, (unsigned_lit (e_size (nth j es (Ent 0 0 [])) + -1)) by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x14034 add a0,s5,a0; add a0,s9,a0; lbu a0,0(a0) *)
  step. step.
  pose proof (ent_byte_read rsegs m1 _ _ (Z.to_nat (e_size (nth j es (Ent 0 0 [])) - 1)) HEB ltac:(lia)) as HR.
  step. clear HR.
  (* 0x14040 add a4,s9,s5; snez a0,a0; addi a0,a0,-1; and a0,a0,a4; j 0x14058 *)
  step. step. step. step. rewrite snez_mask by lia. step.
  destruct (Z.eqb_spec (bv_unsigned (nth (Z.to_nat (e_size (nth j es (Ent 0 0 [])) - 1))
                                         (e_body (nth j es (Ent 0 0 []))) NUL)) 0) as [Eb|Eb]; cbv beta iota.
  - (* a key *)
    assert (EK : key_of (nth j es (Ent 0 0 [])) = Some (cstr (e_body (nth j es (Ent 0 0 []))))).
    { rewrite key_of_cases. unfold POD_STRING, last_body_byte. rewrite (proj2 (Z.eqb_eq _ _) Et), Eb.
      rewrite (proj2 (Z.leb_le 1 _)) by lia. reflexivity. }
    rewrite EK in HE.
    assert (HNI : (nul_idx (e_body (nth j es (Ent 0 0 []))) < length (e_body (nth j es (Ent 0 0 []))))%nat).
    { pose proof (nul_idx_le_k (e_body (nth j es (Ent 0 0 []))) (Z.to_nat (e_size (nth j es (Ent 0 0 [])) - 1))
                    ltac:(lia) Eb). lia. }
    pose proof (ent_key_bytes rsegs m1 _ _ HEB HNI) as HKB.
    replace (pp + 16404 + 104 * Z.of_nat j + 8) with (pp + 16412 + 104 * Z.of_nat j) in HKB by lia.
    pose proof (nul_idx_le (e_body (nth j es (Ent 0 0 [])))) as HNL.
    assert (LK : Z.of_nat (length (cstr (e_body (nth j es (Ent 0 0 []))) ++ [Z_to_bv 8 0])) <= 46).
    { unfold cstr. rewrite length_app, length_firstn. cbn [length]. lia. }
    eapply (end_ok j Hj HI) with (ko := Some (cstr (e_body (nth j es (Ent 0 0 []))))) (ka := pp + 16412 + 104 * Z.of_nat j);
      [exact HF | exact MS1 | exact H2 | exact HE | | reflexivity | reflexivity | reflexivity | reflexivity
      | exact H3 | exact H7 | exact H10].
    cbn [slot_ok]. split; [lia|]. split; [exact HKB|]. split; [lia | apply cstr_no_nul].
  - (* not NUL-terminated *)
    assert (EK : key_of (nth j es (Ent 0 0 [])) = None).
    { rewrite key_of_cases. unfold last_body_byte. rewrite (proj2 (Z.eqb_neq _ _) Eb). rewrite andb_false_r. reflexivity. }
    rewrite EK in HE.
    eapply (end_ok j Hj HI) with (ko := None) (ka := 0);
      [exact HF | exact MS1 | exact H2 | exact HE | exact I | reflexivity | reflexivity | reflexivity | reflexivity
      | exact H3 | exact H7 | exact H10].
Qed.

(** 0x14004, 0x14070 .. 0x1409c: the key k in the slot: v = j; strcmp(k, "reac.cfg.role") with s10 spilled at sp + 0xb0. *)
Lemma some_ok : forall j, ((S j < n)%nat -> inner_none_P (S j)) -> forall k ka, inner_some_P j k ka.
Proof.
  intros j HI k ka. unfold inner_some_P.
  intros ra t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s10 s11 t3 t4 t5 t6 F fc m1 HF MS1 H2 HE Hj Hka HK HKl HNK -> -> -> H3 H7
    H10.
  pose proof (proj1 (ents_wf r HWF)) as Hn. pose proof (bytes_at_bound rsegs m1 ka _ HK) as (KB0 & KB1).
  pose proof MS1 as (MT & HPPB & H10c & H68 & HC & TM). pose proof MT as (_ & _ & MI & ST & _).
  (* 0x14004 bnez a0 taken *)
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbn [negb]. cbv beta iota.
  (* 0x14070 addiw s3,a5,1; blt s3,a5; bltz a5 *)
  step. rewrite addiw1_small by lia.
  step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x1407c sd s10,0xb0(sp) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 176)) 8 = true)
    by exact (stk_store_ok rsegs m1 lo (SP + 440) (SP + 176) 8 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 176));
    assert (MS2 : MemS (write_to_mem m1 (wa (SP + 176)) BS) (rcell (fst E0)))
      by (apply MemS_store; unfold or_h; rewrite ?length_le8; [exact MS1 | exact HS | lia | lia | lia | lia | lia]);
    assert (HK2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 176)) BS) ka (k ++ [Z_to_bv 8 0]))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact HK | lia | lia | lia]);
    assert (HSP : bytes_at rsegs (write_to_mem m1 (wa (SP + 176)) BS) (SP + 176) BS)
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    revert MS2 HK2 HSP; generalize (write_to_mem m1 (wa (SP + 176)) BS) as m2; intros m2 MS2 HK2 HSP
  end.
  clear HS HK MT HPPB H10c H68 HC TM MI ST.
  pose proof MS2 as (MT & HPPB & H10c & H68 & HC & TM). pose proof MT as (_ & _ & MI & ST & _).
  (* 0x14080 mv s10,s8; mv s8,a1; jal strcmp *)
  step. step. step.
  eapply evt_cut.
  { eapply STRC with (sx := k) (sy := ROLE_KEY).
    - rewrite unsigned_lit by lia. exact HK2.
    - exact HNK.
    - change (bv_unsigned (Z_to_bv 64 0x1032e)) with 0x1032e. exact (role_key_at m2 MI).
    - exact role_key_no_nul. }
  intros ms' (rr & x11 & x12 & x13 & E & Hr). subst ms'. ret_even.
  (* 0x1408c mv a1,s8; mv s8,s10; ld s10,0xb0(sp); mv a5,s3; bnez a0 *)
  step. step. pose proof (read_le8 rsegs m2 (SP + 176) _ HSP) as HR. step. clear HR. step.
  rewrite (skipn_nth_cons es j (Ent 0 0 []) Hj), rop_some in HE.
  revert HE. destruct (bytes_eqb k ROLE_KEY) eqn:EK; intros HE.
  - (* the role key: 0x140a0 *)
    apply bytes_eqb_eq in EK. rewrite (proj2 Hr EK).
    step. if_false.
    eapply value_ok with (v := j); [exact HF | exact MS2 | exact H2 | exact Hj | exact HE | weq | weq | weq | exact H7].
  - (* another key: back to the outer loop with at = j + 1 *)
    assert (Hrr : bv_eqb rr (Z_to_bv 64 0) = false).
    { destruct (bv_eqb rr (Z_to_bv 64 0)) eqn:X; [|reflexivity]. apply bv_eqb_true in X. apply Hr in X. subst k.
      rewrite (proj2 (bytes_eqb_eq ROLE_KEY ROLE_KEY) eq_refl) in EK. discriminate. }
    step. rewrite Hrr. cbn [negb]. cbv beta iota.
    eapply (outer_ok (S j) HI); [exact HF | exact MS2 | exact H2 | exact HE | lia | weq | exact H7 | exact H10].
Qed.

Lemma scan_ok : forall K j, (n - j <= K)%nat -> inner_none_P j /\ (forall k ka, inner_some_P j k ka).
Proof.
  induction K as [|K IH]; intros j HK.
  - split; [unfold inner_none_P; intros; lia | intros k ka; unfold inner_some_P; intros; lia].
  - assert (HN : (S j < n)%nat -> inner_none_P (S j) /\ (forall k ka, inner_some_P (S j) k ka))
      by (intros _; apply IH; lia).
    split; [apply none_ok; exact HN | intros k ka; apply some_ok; intros H; exact (proj1 (HN H))].
Qed.

(** ** The head: memcpy, the parse, the corrupt, NULL, is_props and params_struct tests, the scan's set-up *)
Hypothesis HLEN : len = Z.of_nat (length (buf r)).
Hypothesis HPODA : pod mod 16 = 0.
Hypothesis HSEP : or_h (pod + len <= pp) (pp + 19744 <= pod).
Hypothesis HPM : corrupt r = false -> parse_model (buf r) = E0.

(** The memory before the scan's set-up: MemS and the cell sp + 0x70 = &pp->n_ent. *)
Definition MemP (m1 : word -> option byte) (c : Z) : Prop :=
  MemS m1 c /\ bytes_at rsegs m1 (SP + 112) (le8 (Z_to_bv 64 (pp + 19732))).

Lemma len_buf : 8 <= len <= 5440.
Proof. destruct (buf_header r HWF) as (_ & _ & _ & H). lia. Qed.

(** 0x13f94 .. 0x13fd8: at = 0, n = n_ent, the constants and the overflow bounds of the scan. *)
Lemma setup_ok : forall (ra t0 t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  is_props r = true -> params_struct r = true ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 (Z_to_bv 64 (pp + 19732)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
             s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f94) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MS1 H2 EI EP.
  pose proof (proj1 (ents_wf r HWF)) as Hn. pose proof len_pp as LP.
  pose proof MS1 as (MT & HPPB & H10c & H68 & HC & TM).
  (* 0x13f94 mv a5,zero; lui a0,4; lw s0,0(a2) *)
  step. step.
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 19732)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (ents r)))))).
  { apply (read_field rsegs m1 pp r 19732 _ HPPB HWF); [exact (pp_n_ent r HWF) | lia | unfold PP_SIZE; lia | lia]. }
  step. clear HR. rewrite sx32_small by lia.
  (* 0x13fa0 lui a2,0xffffc; addi s8,zero,13; addi s6,zero,8; auipc a3; addiw s4,a0,0x14; addiw a0,a0,0x1c;
     addiw a2,a2,3; slli s8,s8,35 *)
  step. step. step. step. step. step. step. step.
  (* 0x13fc0 ld a4,0x68(sp) *)
  pose proof (read_le8 rsegs m1 (SP + 104) _ H68) as HR. step. clear HR.
  (* 0x13fc4 add s4,a4,s4; add s9,a4,a0; sub s10,a2,a4; not s7,s4; addi s10,s10,-32; addi a1,a3,0x382 *)
  step. step. step. step. step. step.
  eapply (outer_ok 0).
  - intros Hl. exact (proj1 (scan_ok (length (ents r)) 0 ltac:(lia))).
  - exact HF.
  - exact MS1.
  - exact H2.
  - exact (expect_struct r EI EP).
  - lia.
  - weq.
  - rewrite (unsigned_lit (pp + 16404)) by lia. rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia. lia.
  - rewrite (unsigned_lit pp) by lia. rewrite unsigned_lit by lia. lia.
Qed.

(** 0x13f70 .. 0x13f90: corrupt, the NULL flag, is_props, params_struct. *)
Lemma after_parse : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
                           (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemP m1 (rcell (fst (parse_res (Z.testbit fl 0) (buf r)))) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fl)) 1)) (Z_to_bv 64 pod)
             (Z_to_bv 64 (snd (parse_res (Z.testbit fl 0) (buf r)))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             (Z_to_bv 64 (pp + 16384)) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13f70) fc None m1
        (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF (MS1 & H70).
  pose proof len_pp as LP.
  pose proof MS1 as (MT & HPPB & H10c & H68 & HC & TM).
  (* 0x13f70 ld a2,0x70(sp); lw a1,4(a2); mv s2,a0; bnez a1 *)
  pose proof (read_le8 rsegs m1 (SP + 112) _ H70) as HR. step. clear HR.
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 19736)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (corrupt r))))).
  { apply (read_field rsegs m1 pp r 19736 _ HPPB HWF);
      [exact (pp_corrupt r HWF) | lia | unfold PP_SIZE; lia | destruct (corrupt r); cbn; lia]. }
  revert HR. destruct (corrupt r) eqn:EC; cbn [Z.b2z]; intros HR.
  { step. clear HR. rewrite sx32_small by lia. step. step. if_true. eapply tail_ok; [exact HF | exact MT]. }
  step. clear HR. rewrite sx32_small by lia. step. step. if_false.
  (* 0x13f80 bnez s0 *)
  step. rewrite (unsigned_lit fl) by lia. rewrite (land1_bit fl HFL).
  revert MS1 HC. destruct (Z.testbit fl 0) eqn:EB; intros MS1 HC; cbv beta iota.
  { (* the NULL argument: check_malformed *)
    if_true. cbn [parse_res fst snd rcell] in HC |- *.
    eapply malformed_ok; [exact HF | exact MT | reflexivity | exact HC]. }
  if_false. change (parse_res false (buf r)) with (parse_model (buf r)) in MS1, HC |- *.
  rewrite HPM in MS1, HC |- * by first [exact EC | reflexivity].
  (* 0x13f84 lw a0,8(s7); beqz a0 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 16392)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (is_props r))))).
  { apply (read_field rsegs m1 pp r 16392 _ HPPB HWF);
      [exact (pp_is_props r HWF) | lia | unfold PP_SIZE; lia | destruct (is_props r); cbn; lia]. }
  revert HR. destruct (is_props r) eqn:EI; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      rewrite (expect_not_props r EI) in HC |- *. cbn [fst snd rcell] in HC |- *.
      eapply malformed_ok; [exact HF | exact MT | reflexivity | exact HC]. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  (* 0x13f8c lw a0,0x10(s7); beqz a0 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 16400)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (params_struct r))))).
  { apply (read_field rsegs m1 pp r 16400 _ HPPB HWF);
      [exact (pp_params_struct r HWF) | lia | unfold PP_SIZE; lia | destruct (params_struct r); cbn; lia]. }
  revert HR. destruct (params_struct r) eqn:EP; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      rewrite (expect_no_struct r EI EP) in HC |- *. cbn [fst snd rcell] in HC |- *.
      eapply absent_ok; [exact HF | exact MT | reflexivity | exact HC | exact H68 | exact H10c]. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  eapply setup_ok; [exact HF | exact MS1 | apply unsigned_lit_wrap | exact EI | exact EP].
Qed.

Hypothesis MCPY : memcpy_contract.
Hypothesis PARSE : reac_role_prop_parse_contract.

(** The parse's memory: its frame, and the role cell when it answers a role. *)
Lemma MemP_parse : forall m2 m3 o, MemP m2 0x5a -> role_mem m2 m3 SP (SP + 344) o -> wmono rsegs m2 m3 ->
  mem_inv rsegs m3 -> stk rsegs m3 lo SP -> MemP m3 (rcell o).
Proof.
  intros m2 m3 o ((MT & HPPB & H10c & H68 & HC & TM) & H70) RM WM3 MI3 ST3. pose proof len_pp as LP.
  pose proof MT as (_ & _ & _ & ST & _).
  destruct o as [w|]; cbn [role_mem rcell] in RM |- *.
  - destruct RM as (MU3 & HW). unfold PARSE_FRAME in MU3.
    split; [split|].
    { apply (MemT_call m2 m3 _ MT MU3 WM3 MI3 ST3).
      - unfold sub_fp, WC. cbn [outside]. intros x (O1 & _ & _). repeat split; try exact I; lia.
      - intros x Hx. destruct (Z_lt_le_dec x (SP + 344)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; lia|].
        destruct (Z_lt_le_dec x (SP + 348)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; lia].
        apply (bytes_at_some rsegs m3 (SP + 344) _ x HW); rewrite length_le4; [intros a Ha; apply HROM | ]; lia. }
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HPPB MU3); cbn [disjoint_from]; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ H10c MU3); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ H68 MU3); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [exact HW|].
    { apply (task_mem_munch_u _ m2 m3 TM MU3). apply (stk_wview rsegs m2 lo (SP + 440)); [exact ST|].
      intros x Hx. cbn [outside] in Hx. lia. }
    apply (bytes_at_transport rsegs _ m2 m3 _ _ H70 MU3). cbn [disjoint_from]. rewrite length_le8. repeat split; lia.
  - unfold PARSE_FRAME in RM.
    split; [split|].
    { apply (MemT_below m2 m3 80 MT RM WM3 MI3 ST3). lia. }
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HPPB RM); cbn [disjoint_from]; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ H10c RM); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ H68 RM); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HC RM); cbn [disjoint_from]; rewrite length_le4; repeat split; lia|].
    { apply (task_mem_munch_u _ m2 m3 TM RM). apply (stk_wview rsegs m2 lo (SP + 440)); [exact ST|].
      intros x Hx. cbn [outside] in Hx. lia. }
    apply (bytes_at_transport rsegs _ m2 m3 _ _ H70 RM). cbn [disjoint_from]. rewrite length_le8. repeat split; lia.
Qed.

(** 0x13f54 .. 0x13f6c: role := 0x5a, rc = reac_role_prop_parse(fl & 1 ? NULL : pod, &role). *)
Lemma after_cpy : forall (ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bytes_at rsegs m1 pp (pp_bytes r) -> bytes_at rsegs m1 (SP + 16) (le8 (Z_to_bv 64 fl)) ->
  bytes_at rsegs m1 (SP + 104) (le8 (Z_to_bv 64 pp)) -> bytes_at rsegs m1 (SP + 112) (le8 (Z_to_bv 64 (pp + 19732))) ->
  MemNorm.task_mem rsegs m1 -> bytes_at rsegs m1 pod (buf r) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) (Z_to_bv 64 pod) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len)
             (Z_to_bv 64 fl) s4 s5 s6 (Z_to_bv 64 (pp + 16384)) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f54) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT HPPB H10c H68 H70 TM HPB.
  pose proof len_pp as LP. pose proof len_buf as LB. pose proof (buf_header r HWF) as (_ & _ & HU & _).
  pose proof MT as (MU & WM & MI & ST & TB).
  (* 0x13f54 addi a0,zero,0x5a; andi s0,s3,1; sw a0,0x158(sp) *)
  step. step.
  assert (HS : store_ok rsegs m1 (wa (SP + 344)) 4 = true)
    by exact (stk_store_ok rsegs m1 lo (SP + 440) (SP + 344) 4 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 344));
    assert (MP2 : MemP (write_to_mem m1 (wa (SP + 344)) BS) 0x5a);
    [ split; [split|];
      [ apply MemT_store; rewrite ?length_le4; [exact MT | exact HS | lia | lia]
      | split; [apply bytes_at_write_other; rewrite ?length_le4; [exact HPPB | lia | lia | lia]|];
        split; [apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H10c | lia | lia | lia]|];
        split; [apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H68 | lia | lia | lia]|];
        split; [apply bytes_at_write_same; rewrite ?length_le4; lia|];
        apply task_mem_write_u; rewrite ?length_le4; [exact TM | exact HS]
      | apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H70 | lia | lia | lia] ]
    | assert (HPB2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 344)) BS) pod (buf r))
        by (apply bytes_at_write_other; rewrite ?length_le4; [exact HPB | lia | lia | lia]);
      revert MP2 HPB2; generalize (write_to_mem m1 (wa (SP + 344)) BS) as m2; intros m2 MP2 HPB2 ]
  end.
  clear MU WM MI ST TB MT HPPB H10c H68 H70 TM HS.
  pose proof MP2 as ((MT & HPPB & H10c & H68 & HC & TM) & H70). pose proof MT as (MU & WM & MI & ST & TB).
  (* 0x13f60 addi a0,s0,-1; and a0,a0,s1; addi a1,sp,0x158; jal reac_role_prop_parse *)
  step. step. step. step.
  eapply evt_cut.
  { eapply PARSE with (null := Z.testbit fl 0) (lo := lo) (P := pod) (Q := SP + 344) (bs := buf r).
    - f_equal. apply parse_arg; lia.
    - reflexivity.
    - unfold role_args. split; [exact HPB2|]. split; [lia|]. split; [exact HPODA|]. split; [lia|].
      split; [rewrite HU; reflexivity|]. split; [lia|].
      split; [apply (stk_wr_at rsegs m2 lo (SP + 440)); [exact ST | lia | lia | lia]|]. split; lia.
    - exact (MemT_stk m2 MT).
    - unfold PARSE_FRAME. lia.
    - intros a Ha. apply HROM. lia.
    - exact HF.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m3 &
              E & HFk & HF' & RM & WM3 & MI3 & ST3).
  subst ms'. ret_even.
  eapply after_parse; [exact HF' | exact (MemP_parse m2 m3 _ MP2 RM WM3 MI3 ST3)].
Qed.

(** 0x13f34 .. 0x13f50: s3 = fl, pod <> 0; memcpy(pod, pp, len) (len >= 8). *)
Lemma head_ok : forall (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (junk : list byte),
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> stk rsegs m lo (SP + 440) -> ctbl m ->
  bytes_at rsegs m pp (pp_bytes r) -> bytes_at rsegs m (SP + 16) (le8 (Z_to_bv 64 fl)) ->
  bytes_at rsegs m (SP + 104) (le8 (Z_to_bv 64 pp)) -> bytes_at rsegs m (SP + 112) (le8 (Z_to_bv 64 (pp + 19732))) ->
  rw_cells rsegs m pod [CB (Z.to_nat len) junk] ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pod) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) s3 s4 s5 s6
             (Z_to_bv 64 (pp + 16384)) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f34) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 F fc junk HF HMI HTM HST HTB HPPB
    H10c H68 H70 HPC.
  pose proof len_pp as LP. pose proof len_buf as LB. pose proof HST as (HS0 & HS1 & _).
  (* 0x13f34 ld s3,0x10(sp); beqz a0; mv s1,a0; beqz s2 *)
  pose proof (read_le8 rsegs m (SP + 16) _ H10c) as HR. step. clear HR.
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  step. step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x13f44 mv a0,s1; mv a1,s8; mv a2,s2; jal memcpy *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MCPY with (src := buf r) (junk := junk).
    - rewrite unsigned_lit by lia. rewrite <- (pp_buf r). replace pp with (pp + Z.of_nat 0) at 1 by lia.
      apply (bytes_at_sub rsegs m pp (pp_bytes r) 0 (length (buf r)) HPPB). lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. exact HPC.
    - rewrite !unsigned_lit by lia. unfold or_h in HSEP. lia.
    - exact HMI. }
  intros ms' Hpost. unfold memcpy_post in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                     E & MU1 & WM1 & MI1 & CB1 & _).
  subst ms'. rewrite !unsigned_lit in MU1, CB1 by lia. ret_even.
  assert (MT1 : MemT m1).
  { split; [apply (munch_weaken [(pod, pod + len)] WC m m1); [|exact MU1]|].
    { unfold sub_fp, WC. cbn [outside]. intros x (_ & O2 & _). split; [exact O2 | exact I]. }
    split; [exact WM1|]. split; [exact MI1|].
    split; [apply (stk_transport_disjoint rsegs _ m m1 _ _ HST MU1 WM1); cbn [disjoint_from]; split; [lia | exact I]|].
    apply (ctbl_munch _ m m1 HTB MU1). intros a Ha. cbn [outside].
    split; [exact (codes_apart pod (pod + len) HPROM a Ha) | exact I]. }
  assert (DJ : forall A k, lo <= A -> A + k <= SP + 440 -> disjoint_from [(pod, pod + len)] A k)
    by (intros A k H1 H2; cbn [disjoint_from]; split; [lia | exact I]).
  eapply after_cpy.
  - exact HF.
  - exact MT1.
  - apply (bytes_at_transport rsegs _ m m1 _ _ HPPB MU1). cbn [disjoint_from]. unfold or_h in HSEP. split; [lia | exact I].
  - apply (bytes_at_transport rsegs _ m m1 _ _ H10c MU1). rewrite length_le8. apply DJ; lia.
  - apply (bytes_at_transport rsegs _ m m1 _ _ H68 MU1). rewrite length_le8. apply DJ; lia.
  - apply (bytes_at_transport rsegs _ m m1 _ _ H70 MU1). rewrite length_le8. apply DJ; lia.
  - apply (task_mem_munch_u _ m m1 HTM MU1). intros x Hx. cbn [outside] in Hx.
    destruct HPC as [_ (W0 & W1 & W)]. cbn [cells_size csize] in W.
    pose proof (W (bv_unsigned x - pod)) as Wx. replace (pod + (bv_unsigned x - pod)) with (bv_unsigned x) in Wx by lia.
    unfold wa in Wx. rewrite Z_to_bv_lit_self in Wx. apply Wx. lia.
  - exact (rw_cells_CB_bytes rsegs m1 pod _ _ CB1).
Qed.

End Check.
