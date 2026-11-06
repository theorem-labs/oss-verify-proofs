(** The walk of reac-pw/fuzz_role's LLVMFuzzerTestOneInput (plain) from malloc(pod)'s return (0x13f4c) to the pc
    after check_code's return (0x14158), against role_check_contract (Prog/LLVMFuzzerTestOneInput_c.v), with the
    callee contracts as Section hypotheses. Section Check fixes the contract's frame (sp, gp, tp, the entry memory
    m), the record r pod_build made with its buffer length len, fl, pp, pod and lo; QC is the contract's
    postcondition. Walked backwards: QC_done (0x14158), code_ok (0x14138: the two refusal codes and check_code),
    answer_ok (0x14108: changes, apply_state, check_answer), tail_ok (0x140f0: req), absent_ok (0x140a4),
    malformed_ok (0x140e4), role_ok (0x141a8); flag_ok (0x140dc: flag < 2), float_ok (0x140b8: pod_float and
    pod_nearest), value_ok (0x14058: ent[v] of the role key, pod_int or pod_float); the pod_next_pair scan by
    induction on the entries left (outer_ok 0x13fec, nokey_ok 0x1402c, key_ok 0x14030 with strcmp against
    "reac.cfg.role", inner_ok 0x14000); setup_ok (0x13fac), after_parse (0x13f88: corrupt, the NULL flag,
    is_props, params_struct), after_cpy (0x13f68: the role cell and reac_role_prop_parse) and head_ok (0x13f4c:
    memcpy). The answers agree because the scan computes expect_model false r (Pod/Role.v) step by step, and the
    parse's answer is parse_model of the uncorrupted buffer, which is the same (hypothesis HPM). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import memcpy_c reac_role_prop_parse_c strcmp_c pod_nearest_c
  check_absent_c check_role_c check_malformed_c
  reac_role_cfg_changes_c reac_role_cfg_apply_state_c check_answer_c reac_role_refuse_code_c check_code_c
  SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Nearest Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleCheck Require Import Facts.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).
(* Register equations at a loop head. *)
Ltac weq := first [ reflexivity
                  | (rewrite addiw1_small by lia; f_equal; lia)
                  | (f_equal; lia)
                  | (f_equal; rewrite ?unsigned_lit by lia; lia) ].

Section Check.
Variables (sp gp tp : word) (m : word -> option byte) (len pp pod lo : Z).

Local Abbreviation SP := (bv_unsigned sp).

Hypothesis HPOD : 0 < pod.
Hypothesis HLEN0 : 0 <= len.
Hypothesis HPODLO : pod + len <= lo.
Hypothesis HPP0 : 0 <= pp.
Hypothesis HPPLO : pp + 19744 <= lo.
Hypothesis HLO0 : 0 <= lo.
Hypothesis HLO : lo + 96 <= SP.
Hypothesis HSPT : SP + 392 <= 2^64.
Hypothesis HSPA : SP mod 16 = 0.
Hypothesis HROM : forall a, lo <= a < SP + 392 -> seg_rom rsegs (wa a) = None.

Definition QC : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10'
                     t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pod) a0' a1' a2' a3' a4' a5' a6' a7'
                  s2' s3' s4' s5' s6' s7' s8' s9' s10' (Z_to_bv 64 pp) t3' t4' t5' t6')
             F' (Z_to_bv 64 ROLE_FREE) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\
    munch [(SP - MID_STACK, SP + FRAME_LOCALS); (pod, pod + len)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (SP + FRAME_LOCALS).

(** The footprint and the memory the walk carries: changed only in the frame's locals, the callees' stack and the
    pod block; the stack region with the frame's locals present and writable. *)
Definition WC : list (Z * Z) := [(SP - 96, SP + 392); (pod, pod + len)].
Definition MemT (m1 : word -> option byte) : Prop :=
  munch WC m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (SP + 392).

Lemma MemT_store : forall m1 a bs, MemT m1 -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP - 96 <= a -> a + Z.of_nat (length bs) <= SP + 392 -> MemT (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs (MU & WM & MI & ST) HS H1 H2. pose proof ST as (ST0 & ST1 & _).
  split; [apply munch_write; [exact MU | lia | lia | unfold WC; cbn [inside]; left; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | exact HS]|].
  apply stk_write; [exact ST | lia | lia].
Qed.

(** A callee whose footprint lies below the stack top or in the frame's locals. *)
Lemma MemT_call : forall m1 m2 W, MemT m1 -> munch W m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo SP -> sub_fp W WC ->
  (forall x, SP <= x < SP + 392 -> outside W x \/ exists b, m2 (wa x) = Some b) -> MemT m2.
Proof.
  intros m1 m2 W (MU & WM & MI & ST) MU2 WM2 MI2 ST2 SUB HX.
  split; [exact (munch_trans WC m m1 m2 MU (munch_weaken W WC m1 m2 SUB MU2))|].
  split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
  split; [exact MI2|].
  destruct (stk_split rsegs m1 lo SP (SP + 392) ST ltac:(lia)) as [_ ST1].
  apply (stk_merge rsegs m2 lo SP); [exact ST2 | | lia].
  exact (stk_transport rsegs W m1 m2 SP (SP + 392) ST1 MU2 WM2 HX).
Qed.

Lemma MemT_below : forall m1 m2 k, MemT m1 -> munch [(SP - k, SP)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo SP -> 0 <= k <= 96 -> MemT m2.
Proof.
  intros m1 m2 k MT MU WM MI ST Hk. apply (MemT_call m1 m2 [(SP - k, SP)] MT MU WM MI ST).
  - unfold sub_fp, WC. cbn [outside]. intros x (O1 & _ & _). split; [lia | exact I].
  - intros x Hx. left. cbn [outside]. split; [lia | exact I].
Qed.

Lemma MemT_stk : forall m1, MemT m1 -> stk rsegs m1 lo SP.
Proof. intros m1 (_ & _ & _ & ST). exact (proj1 (stk_split rsegs m1 lo SP (SP + 392) ST ltac:(lia))). Qed.

Hypothesis CHG : reac_role_cfg_changes_contract.
Hypothesis APS : reac_role_cfg_apply_state_contract.
Hypothesis CKA : check_answer_contract.
Hypothesis RFC : reac_role_refuse_code_contract.
Hypothesis CKC : check_code_contract.

(** 0x14158: the contract's postcondition. *)
Lemma QC_done : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             (Z_to_bv 64 pp) t3 t4 t5 t6) F (Z_to_bv 64 ROLE_FREE) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m1 HF (MU & WM & MI & ST).
  apply evt_done. exists ra, t0, t1, t2, s0, a0, a1, a2, a3, a4, a5, a6, a7, s2, s3, s4, s5, s6, s7, s8, s9, s10,
    t3, t4, t5, t6, F, fc, m1.
  split; [reflexivity|]. split; [exact HF|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST].
Qed.

(** 0x14138 .. 0x14158: check_code(refuse_code(0), refuse_code(1)). *)
Lemma code_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             (Z_to_bv 64 pp) t3 t4 t5 t6) F (Z_to_bv 64 0x14138) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m1 HF MT.
  pose proof MT as (_ & _ & MI & _).
  (* 0x14138 mv a0,zero; jal reac_role_refuse_code *)
  step. step.
  eapply evt_cut; [eapply RFC; exact MI|]. intros ms' (a1x & ->). ret_even.
  match goal with |- context [refuse_code_res ?x] => replace (refuse_code_res x) with CODE_NONE by (vm_compute; reflexivity) end.
  (* 0x14140 mv s2,a0; addi a0,zero,1; jal reac_role_refuse_code *)
  step. step. step.
  eapply evt_cut; [eapply RFC; exact MI|]. intros ms' (a1y & ->). ret_even.
  match goal with |- context [refuse_code_res ?x] => replace (refuse_code_res x) with CODE_MALFORMED by (vm_compute; reflexivity) end.
  (* 0x1414c mv a1,a0; mv a0,s2; jal check_code *)
  step. step. step.
  eapply evt_cut.
  { eapply CKC with (lo := lo); [reflexivity | reflexivity | exact (MemT_stk m1 MT) | unfold CHECK_CODE_FRAME; lia
                                | intros a Ha; apply HROM; lia | exact MI]. }
  intros ms' (a0' & a1' & a2' & a3' & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'. ret_even.
  apply QC_done; [exact HF|].
  apply (MemT_below m1 m2 CHECK_CODE_FRAME MT MU2 WM2 MI2 ST2). unfold CHECK_CODE_FRAME. lia.
Qed.

(** 0x14108 .. 0x14134: check_answer(changes(cur, req), apply_state(cur, req), cur, req) with s3 = cur, s2 = req. *)
Lemma answer_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             (Z_to_bv 64 pp) t3 t4 t5 t6) F (Z_to_bv 64 0x14108) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m1 HF MT.
  pose proof MT as (_ & _ & MI & _).
  (* 0x14108 mv a0,s3; mv a1,s2; jal reac_role_cfg_changes *)
  step. step. step.
  eapply evt_cut; [eapply CHG|]. intros ms' ->. ret_even.
  (* 0x14114 mv s4,a0; mv a0,s3; mv a1,s2; jal reac_role_cfg_apply_state *)
  step. step. step. step.
  eapply evt_cut; [eapply APS|]. intros ms' ->. ret_even.
  (* 0x14124 mv a1,a0; mv a0,s4; mv a2,s3; mv a3,s2; jal check_answer *)
  step. step. step. step. step.
  eapply evt_cut.
  { eapply CKA with (lo := lo); [reflexivity | reflexivity | exact (MemT_stk m1 MT) | unfold CHECK_ANSWER_FRAME; lia
                                | intros a Ha; apply HROM; lia | exact MI]. }
  intros ms' (a0' & a1' & a2' & a3' & a4' & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'. ret_even.
  apply code_ok; [exact HF|].
  apply (MemT_below m1 m2 CHECK_ANSWER_FRAME MT MU2 WM2 MI2 ST2). unfold CHECK_ANSWER_FRAME. lia.
Qed.

(** 0x140f0 .. 0x14104: req = rc == 1 ? role : !cur (cur = fl bit 1 from s0 = fl << 62). *)
Lemma tail_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             (Z_to_bv 64 pp) t3 t4 t5 t6) F (Z_to_bv 64 0x140f0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m1 HF MT.
  pose proof MT as (_ & _ & _ & ST).
  (* 0x140f0 addi a0,zero,1; srli s3,s0,63; beq s2,a0 *)
  step. step. step. if_cases E.
  - (* 0x14104 lw s2,0x128(sp) *)
    destruct (stk_read rsegs m1 lo (SP + 392) (SP + 296) 4 ST ltac:(lia) ltac:(lia)) as (bs & HR).
    step. clear HR. eapply answer_ok; [exact HF | exact MT].
  - (* 0x140fc xori s2,s3,1; j 0x14108 *)
    step. step. eapply answer_ok; [exact HF | exact MT].
Qed.

Hypothesis CKAB : check_absent_contract.
Hypothesis CKR : check_role_contract.
Hypothesis CKM : check_malformed_contract.

(** 0x140a4 .. 0x140b4: check_absent(rc, role), then s11 = pp again. *)
Lemma absent_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s2 = 0 ->
  bytes_at rsegs m1 (SP + 296) (le4 (Z_to_bv 64 0x5a)) -> bytes_at rsegs m1 (SP + 80) (le8 (Z_to_bv 64 pp)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x140a4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT H2 HC H50.
  pose proof (read_le4_cell rsegs m1 (SP + 296) _ HC) as HR.
  (* 0x140a4 lw a1,0x128(sp); mv a0,s2; jal check_absent *)
  step. clear HR. rewrite sx32_small by lia. step. step.
  eapply evt_cut; [eapply CKAB; [exact H2 | reflexivity]|]. intros ms' ->. ret_even.
  pose proof (read_le8 rsegs m1 (SP + 80) _ H50) as HR.
  (* 0x140b0 ld s11,0x50(sp); j 0x140f0 *)
  step. clear HR. step. eapply tail_ok; [exact HF | exact MT].
Qed.

(** 0x140e4 .. 0x140ec: check_malformed(rc, role). *)
Lemma malformed_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                            (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s2 = 2^64 - 1 ->
  bytes_at rsegs m1 (SP + 296) (le4 (Z_to_bv 64 0x5a)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             (Z_to_bv 64 pp) t3 t4 t5 t6) F (Z_to_bv 64 0x140e4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m1 HF MT H2 HC.
  pose proof (read_le4_cell rsegs m1 (SP + 296) _ HC) as HR.
  (* 0x140e4 lw a1,0x128(sp); mv a0,s2; jal check_malformed *)
  step. clear HR. rewrite sx32_small by lia. step. step.
  eapply evt_cut; [eapply CKM; [exact H2 | reflexivity]|]. intros ms' ->. ret_even.
  eapply tail_ok; [exact HF | exact MT].
Qed.

(** 0x141a8 .. 0x141b8: check_role(rc, role, want) for want = v, 0 or 1. *)
Lemma role_ok : forall (ra t0 t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (v : Z),
  frm0 fc -> MemT m1 -> bv_unsigned s2 = 1 -> 0 <= v < 2 ->
  bytes_at rsegs m1 (SP + 296) (le4 (Z_to_bv 64 v)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 (Z_to_bv 64 pp) t3 t4 t5 t6) F (Z_to_bv 64 0x141a8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m1 v HF MT H2 Hv HC.
  pose proof (read_le4_cell rsegs m1 (SP + 296) _ HC) as HR.
  (* 0x141a8 lw a1,0x128(sp); sext.w a2,a2; mv a0,s2; jal check_role *)
  step. clear HR. rewrite sx32_small by lia. step. rewrite sextw_small by lia. step. step.
  eapply evt_cut; [eapply CKR; [exact H2 | reflexivity]|]. intros ms' ->. ret_even.
  (* 0x141b8 j 0x140f0 *)
  step. eapply tail_ok; [exact HF | exact MT].
Qed.

(** ** expect_role over the record in pp *)
Variable r : pod_rec.
Hypothesis HWF : pod_rec_wf r.
Local Abbreviation es := (ents r).
Local Abbreviation n := (length (ents r)).
Local Abbreviation E0 := (expect_model false r).

(** The memory of the scan: MemT, the record at pp, the cells sp + 0x50 = pp and sp + 0x80 = &pp->ent[0], the
    role cell, MemNorm.task_mem (pod_nearest's soft-float callees take it). *)
Definition MemS (m1 : word -> option byte) (c : Z) : Prop :=
  MemT m1 /\ bytes_at rsegs m1 pp (pp_bytes r) /\ bytes_at rsegs m1 (SP + 80) (le8 (Z_to_bv 64 pp)) /\
  bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 (pp + 16404))) /\ bytes_at rsegs m1 (SP + 296) (le4 (Z_to_bv 64 c)) /\
  MemNorm.task_mem rsegs m1.

Lemma len_pp : Z.of_nat (length (pp_bytes r)) = 19744.
Proof. exact (length_pp_bytes r HWF). Qed.

(** A store into the frame's locals off the three cells and the record. *)
Lemma MemS_store : forall m1 c a bs, MemS m1 c -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP - 96 <= a -> a + Z.of_nat (length bs) <= SP + 392 ->
  or_h (a + Z.of_nat (length bs) <= SP + 80) (SP + 88 <= a) ->
  or_h (a + Z.of_nat (length bs) <= SP + 128) (SP + 136 <= a) ->
  or_h (a + Z.of_nat (length bs) <= SP + 296) (SP + 300 <= a) ->
  MemS (write_to_mem m1 (wa a) bs) c.
Proof.
  intros m1 c a bs (MT & HP & H50 & H80 & HC & TM) HS H1 H2 D1 D2 D3. unfold or_h in *.
  pose proof len_pp as LP. pose proof (length_le8 (Z_to_bv 64 pp)) as L8. pose proof (length_le4 (Z_to_bv 64 c)) as L4.
  split; [exact (MemT_store m1 a bs MT HS H1 H2)|].
  split; [apply bytes_at_write_other; [exact HP | lia | lia | lia]|].
  split; [apply bytes_at_write_other; [exact H50 | lia | lia | rewrite length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact H80 | lia | lia | rewrite length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact HC | lia | lia | rewrite length_le4; lia]|].
  exact (task_mem_write rsegs m1 (wa a) bs TM HS).
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

(** 0x140dc .. 0x140e0: the flag test `flag < 2` (unsigned) on a2 = v, an int32. *)
Lemma flag_ok : forall (ra t0 t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (v : Z),
  frm0 fc -> MemT m1 -> -2^31 <= v < 2^31 ->
  bv_unsigned s2 = snd (flag_rc v) mod 2^64 ->
  bytes_at rsegs m1 (SP + 296) (le4 (Z_to_bv 64 (rcell (fst (flag_rc v))))) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 (Z_to_bv 64 pp) t3 t4 t5 t6) F (Z_to_bv 64 0x140dc) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m1 v HF MT Hv H2 HC.
  (* 0x140dc addi a0,zero,2; bltu a2,a0 *)
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

(** 0x140b8 .. 0x140d8: pod_float, pod_nearest(f, &flag), then the flag test. *)
Lemma float_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (i : nat),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  (i < n)%nat -> E0 = expect_value (nth i es (Ent 0 0 [])) -> e_type (nth i es (Ent 0 0 [])) = POD_FLOAT ->
  a0 = Z_to_bv 64 (pp + 16404 + 104 * Z.of_nat i) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x140b8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 i HF MS1 H2 Hi HV Ht ->.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof (ent_wf_nth r i HWF Hi) as (Ht0 & Hb & Hsz).
  pose proof MS1 as (MT & HPPB & H50 & H80 & HC & TM). pose proof MT as (MU & WM & MI & ST).
  pose proof (bytes_at_ent rsegs m1 pp r i HPPB HWF Hi) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat i) with (pp + 16404 + 104 * Z.of_nat i) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  rewrite HV, (ev_float _ Ht) in H2, HC.
  (* 0x140b8 lw a1,4(a0); addi a2,zero,4; ld s11,0x50(sp) *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. pose proof (read_le8 rsegs m1 (SP + 80) _ H50) as HR. step. clear HR.
  (* 0x140c4 bltu a1,a2 *)
  step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size (nth i es (Ent 0 0 []))) 4) as [Es|Es]; cbv beta iota.
  { rewrite (proj2 (Z.leb_gt 4 _) Es) in H2, HC. cbn [fst snd rcell] in H2, HC.
    eapply malformed_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC]. }
  rewrite (proj2 (Z.leb_le 4 _) Es) in H2, HC.
  (* 0x140c8 flw fa0,8(a0); addi a0,sp,0x88; jal pod_nearest *)
  pose proof (ent_word_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR.
  rewrite extract_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn.
  step. step.
  eapply evt_cut.
  { eapply NEAR with (lo := lo) (b := rd32 (e_body (nth i es (Ent 0 0 [])))).
    - apply rd32_range.
    - apply freg_get_same. reflexivity.
    - rewrite unsigned_lit by lia. apply (stk_wr_at rsegs m1 lo (SP + 392)); [exact ST | lia | lia | lia].
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
  - (* a nearest integer w: 0x140d4 beqz a0 not taken; 0x140d8 ld a2,0x88(sp) *)
    destruct PNM as (MU2 & HW).
    assert (MT2 : MemT m2).
    { apply (MemT_call m1 m2 _ MT MU2 WM2 MI2 ST2).
      - unfold sub_fp, WC, POD_NEAREST_STACK. cbn [outside]. intros x (O1 & _ & _). repeat split; try exact I; lia.
      - intros x Hx. unfold POD_NEAREST_STACK.
        destruct (Z_lt_le_dec x (SP + 136)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; lia|].
        destruct (Z_lt_le_dec x (SP + 144)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; lia].
        apply (bytes_at_some rsegs m2 (SP + 136) _ x HW); rewrite length_le8; [intros a Ha; apply HROM | ]; lia. }
    assert (HC2 : bytes_at rsegs m2 (SP + 296) (le4 (Z_to_bv 64 (rcell (fst (flag_rc w)))))).
    { apply (bytes_at_transport rsegs _ m1 m2 _ _ HC MU2). cbn [disjoint_from]. rewrite length_le4.
      unfold POD_NEAREST_STACK. repeat split; lia. }
    step. if_false.
    pose proof (read_le8 rsegs m2 (SP + 136) _ HW) as HR. step. clear HR.
    pose proof (nearest_range _ _ EN) as Hw. unfold INT32_MIN, INT32_MAX in Hw.
    eapply flag_ok; [exact HF' | exact MT2 | lia | exact H2 | exact HC2].
  - (* none: 0x140d4 beqz a0 to check_malformed *)
    cbn [fst snd rcell] in H2, HC.
    assert (MT2 : MemT m2) by (apply (MemT_below m1 m2 POD_NEAREST_STACK MT PNM WM2 MI2 ST2); unfold POD_NEAREST_STACK; lia).
    assert (HC2 : bytes_at rsegs m2 (SP + 296) (le4 (Z_to_bv 64 0x5a))).
    { apply (bytes_at_transport rsegs _ m1 m2 _ _ HC PNM). cbn [disjoint_from]. rewrite length_le4.
      unfold POD_NEAREST_STACK. repeat split; lia. }
    step. if_true.
    eapply malformed_ok; [exact HF' | exact MT2 | rewrite H2; reflexivity | exact HC2].
Qed.

(** 0x14058 .. 0x140a0: the value ent[at] of the role key (v = j + 1): pod_int, else pod_float. *)
Lemma value_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (j : nat),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  (S j < n)%nat -> E0 = expect_value (nth (S j) es (Ent 0 0 [])) -> s4 = Z_to_bv 64 (Z.of_nat j) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x14058) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 j HF MS1 H2 Hj HV ->.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof (ent_wf_nth r (S j) HWF Hj) as (Ht0 & Hb & Hsz).
  pose proof MS1 as (MT & HPPB & H50 & H80 & HC & TM). pose proof MT as (MU & WM & MI & ST).
  pose proof (bytes_at_ent rsegs m1 pp r (S j) HPPB HWF Hj) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat (S j)) with (pp + 16404 + 104 * Z.of_nat (S j)) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  (* 0x14058 addi s4,s4,1; addi a0,zero,13; slli a0,a0,35; slli s4,s4,32; mulhu a0,s4,a0 *)
  step. step. step. step. step. rewrite mulhu_idx by lia.
  (* 0x1406c ld a1,0x80(sp); add a0,a1,a0 *)
  pose proof (read_le8 rsegs m1 (SP + 128) _ H80) as HR. step. clear HR. step.
  (* 0x14074 lw a1,0(a0) *)
  pose proof (ent_type_read rsegs m1 _ _ HEB Ht0) as HR. step. clear HR.
  (* 0x14078 addi a2,zero,-1; addi a3,zero,6; sd a2,0x88(sp) *)
  step. step.
  assert (HS : store_ok rsegs m1 (wa (SP + 136)) 8 = true)
    by exact (stk_store_ok rsegs m1 lo (SP + 392) (SP + 136) 8 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 136));
    assert (MS2 : MemS (write_to_mem m1 (wa (SP + 136)) BS) (rcell (fst E0)))
      by (apply MemS_store; unfold or_h; rewrite ?length_le8; [exact MS1 | exact HS | lia | lia | lia | lia | lia]);
    revert MS2; generalize (write_to_mem m1 (wa (SP + 136)) BS) as m2; intros m2 MS2
  end.
  clear HS MU WM MI ST MT HPPB H50 H80 HC TM HEB.
  pose proof MS2 as (MT & HPPB & H50 & H80 & HC & TM).
  pose proof (bytes_at_ent rsegs m2 pp r (S j) HPPB HWF Hj) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat (S j)) with (pp + 16404 + 104 * Z.of_nat (S j)) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  (* 0x14084 beq a1,a3 *)
  step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth (S j) es (Ent 0 0 []))) 6) as [Et|Et]; cbv beta iota.
  { eapply float_ok; [exact HF | exact MS2 | exact H2 | exact Hj | exact HV | exact Et | weq]. }
  (* 0x14088 addi a2,zero,4; ld s11,0x50(sp); bne a1,a2 *)
  step. pose proof (read_le8 rsegs m2 (SP + 80) _ H50) as HR. step. clear HR.
  step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth (S j) es (Ent 0 0 []))) 4) as [Et4|Et4]; cbn [negb]; cbv beta iota.
  2:{ assert (EV : E0 = (None, -1)) by (rewrite HV; apply ev_other; unfold POD_FLOAT, POD_INT; lia).
      rewrite EV in H2, HC. cbn [fst snd rcell] in H2, HC.
      eapply malformed_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC]. }
  (* 0x14094 lw a1,4(a0); bltu a1,a2 *)
  pose proof (ent_size_read rsegs m2 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size (nth (S j) es (Ent 0 0 []))) 4) as [Es|Es]; cbv beta iota.
  { assert (EV : E0 = (None, -1)) by (rewrite HV, ev_int by exact Et4; rewrite (proj2 (Z.leb_gt 4 _) Es); reflexivity).
    rewrite EV in H2, HC. cbn [fst snd rcell] in H2, HC.
    eapply malformed_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC]. }
  (* 0x1409c lw a2,8(a0); j 0x140dc *)
  pose proof (ent_word_read rsegs m2 _ _ HEB ltac:(lia)) as HR. step. clear HR.
  rewrite sext_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn. step.
  assert (EV : E0 = flag_rc (s32 (rd32 (e_body (nth (S j) es (Ent 0 0 []))))))
    by (rewrite HV, ev_int by exact Et4; rewrite (proj2 (Z.leb_le 4 _) Es); reflexivity).
  rewrite EV in H2, HC.
  pose proof (s32_range _ (rd32_range (e_body (nth (S j) es (Ent 0 0 []))))) as Hv.
  eapply flag_ok; [exact HF | exact MT | lia | exact H2 | exact HC].
Qed.

(** ** pod_next_pair's scan (0x13fec .. 0x14054), by induction on the entries left *)
Definition outer_P (j : nat) : Prop :=
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  E0 = role_of_pairs expect_value (pairs_by key_of (skipn j es) None) -> (j <= n)%nat ->
  s6 = Z_to_bv 64 (Z.of_nat j) -> s5 = Z_to_bv 64 (Z.of_nat n) -> s11 = Z_to_bv 64 (1 - Z.of_nat n) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x1032e) s4 s5 s6
             (Z_to_bv 64 104) (Z_to_bv 64 8) (Z_to_bv 64 (-1)) (Z_to_bv 64 (pp + 16412)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fec) fc None m1 (seg_rom rsegs)).

Definition inner_P (j : nat) : Prop :=
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  E0 = role_of_pairs expect_value (pairs_by key_of (skipn j es) None) -> (j < n)%nat ->
  a1 = Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat j) -> s4 = Z_to_bv 64 (Z.of_nat j - 1) ->
  s6 = Z_to_bv 64 (Z.of_nat j + 1) -> s5 = Z_to_bv 64 (Z.of_nat n) -> s11 = Z_to_bv 64 (1 - Z.of_nat n) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x1032e) s4 s5 s6
             (Z_to_bv 64 104) (Z_to_bv 64 8) (Z_to_bv 64 (-1)) (Z_to_bv 64 (pp + 16412)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14000) fc None m1 (seg_rom rsegs)).

(** 0x13fec .. 0x13ffc: `at < n_ent`, else no pair is left (check_absent). *)
Lemma outer_ok : forall j, ((j < n)%nat -> inner_P j) -> outer_P j.
Proof.
  intros j HI. unfold outer_P.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s11 t3 t4 t5 t6 F fc m1 HF MS1 H2 HE Hj -> -> ->.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  (* 0x13fec bge s6,s5 *)
  step. rewrite lts_s by lia.
  destruct (Z.ltb_spec (Z.of_nat j) (Z.of_nat n)) as [Hl|Hl]; cbn [negb]; cbv beta iota.
  - (* 0x13ff0 addi s4,s6,-1; mul a1,s6,s7; addi s6,s6,1; add a1,s10,a1 *)
    step. step. step. step.
    eapply (HI ltac:(lia)); [exact HF | exact MS1 | exact H2 | exact HE | lia | weq | weq | weq | reflexivity | reflexivity].
  - assert (EA : E0 = (None, 0)) by (rewrite HE, skipn_all2 by lia; reflexivity).
    pose proof MS1 as (MT & _ & H50 & _ & HC & _). rewrite EA in H2, HC. cbn [fst snd rcell] in H2, HC.
    eapply absent_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC | exact H50].
Qed.

(** 0x1402c .. 0x14044: ent[j] is not a key: the next entry, or no pair is left. *)
Lemma nokey_ok : forall j, (j < n)%nat -> ((S j < n)%nat -> inner_P (S j)) ->
  forall (ra t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  E0 = role_of_pairs expect_value (pairs_by key_of (skipn (S j) es) None) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 (Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat j)) a2 a3 a4 a5 a6
             a7 s2 (Z_to_bv 64 0x1032e) (Z_to_bv 64 (Z.of_nat j - 1)) (Z_to_bv 64 (Z.of_nat n))
             (Z_to_bv 64 (Z.of_nat j + 1)) (Z_to_bv 64 104) (Z_to_bv 64 8) (Z_to_bv 64 (-1))
             (Z_to_bv 64 (pp + 16412)) (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x1402c) fc None m1 (seg_rom rsegs)).
Proof.
  intros j Hj HI ra t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 F fc m1 HF MS1 H2 HE.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  (* 0x1402c mv a0,zero; add a2,s11,s4; beq a2,s9 *)
  step. step. step. rewrite eqb_s by lia.
  destruct (Z.eqb_spec (1 - Z.of_nat n + (Z.of_nat j - 1)) (-1)) as [Ee|Ee]; cbv beta iota.
  - assert (EA : E0 = (None, 0)) by (rewrite HE, skipn_all2 by lia; reflexivity).
    pose proof MS1 as (MT & _ & H50 & _ & HC & _). rewrite EA in H2, HC. cbn [fst snd rcell] in H2, HC.
    eapply absent_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC | exact H50].
  - (* 0x14038 addi s4,s4,1; addiw s6,s6,1; addi a1,a1,0x68; beqz a0 *)
    step. step. step. step. if_true.
    eapply (HI ltac:(lia)); [exact HF | exact MS1 | exact H2 | exact HE | lia | weq | weq | weq | reflexivity | reflexivity].
Qed.

(** 0x14030 .. 0x14054: ent[j] is a key k: no value after it, or strcmp(k, "reac.cfg.role"). *)
Lemma key_ok : forall j k, (j < n)%nat -> ((S (S j) < n)%nat -> inner_P (S (S j))) ->
  forall (ra t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte),
  frm0 fc -> MemS m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  E0 = role_of_pairs expect_value (pairs_by key_of (skipn (S j) es) (Some k)) ->
  bytes_at rsegs m1 (pp + 16412 + 104 * Z.of_nat j) (k ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) k ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) (Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat j))
             (Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat j)) a2 a3 a4 a5 a6
             a7 s2 (Z_to_bv 64 0x1032e) (Z_to_bv 64 (Z.of_nat j - 1)) (Z_to_bv 64 (Z.of_nat n))
             (Z_to_bv 64 (Z.of_nat j + 1)) (Z_to_bv 64 104) (Z_to_bv 64 8) (Z_to_bv 64 (-1))
             (Z_to_bv 64 (pp + 16412)) (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14030) fc None m1 (seg_rom rsegs)).
Proof.
  intros j k Hj HI ra t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 F fc m1 HF MS1 H2 HE HK HNK.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof MS1 as (MT & HPPB & H50 & H80 & HC & TM). pose proof MT as (_ & _ & MI & _).
  (* 0x14030 add a2,s11,s4; beq a2,s9 *)
  step. step. rewrite eqb_s by lia.
  destruct (Z.eqb_spec (1 - Z.of_nat n + (Z.of_nat j - 1)) (-1)) as [Ee|Ee]; cbv beta iota.
  { assert (EA : E0 = (None, 0)) by (rewrite HE, skipn_all2 by lia; reflexivity).
    rewrite EA in H2, HC. cbn [fst snd rcell] in H2, HC.
    eapply absent_ok; [exact HF | exact MT | rewrite H2; reflexivity | exact HC | exact H50]. }
  (* 0x14038 addi s4,s4,1; addiw s6,s6,1; addi a1,a1,0x68; beqz a0 *)
  step. step. step. step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x14048 blt s4,s9 *)
  step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x1404c mv a1,s3; jal strcmp *)
  step. step.
  eapply evt_cut.
  { eapply STRC with (sx := k) (sy := ROLE_KEY).
    - rewrite unsigned_lit by lia. exact HK.
    - exact HNK.
    - change (bv_unsigned (Z_to_bv 64 0x1032e)) with 0x1032e. exact (role_key_at m1 MI).
    - exact role_key_no_nul. }
  intros ms' (rr & x11 & x12 & x13 & E & Hr). subst ms'. ret_even.
  rewrite (skipn_nth_cons es (S j) (Ent 0 0 [])) in HE by lia. rewrite rop_some in HE.
  revert HE. destruct (bytes_eqb k ROLE_KEY) eqn:EK; intros HE.
  - (* the role key: 0x14054 bnez a0 not taken *)
    apply bytes_eqb_eq in EK. rewrite (proj2 Hr EK).
    step. if_false.
    eapply value_ok with (j := j); [exact HF | exact MS1 | exact H2 | lia | exact HE | weq].
  - (* another key: back to the outer loop with at = j + 2 *)
    assert (Hrr : bv_eqb rr (Z_to_bv 64 0) = false).
    { destruct (bv_eqb rr (Z_to_bv 64 0)) eqn:X; [|reflexivity]. apply bv_eqb_true in X. apply Hr in X. subst k.
      rewrite (proj2 (bytes_eqb_eq ROLE_KEY ROLE_KEY) eq_refl) in EK. discriminate. }
    step. rewrite Hrr. cbn [negb]. cbv beta iota.
    eapply (outer_ok (S (S j)) HI); [exact HF | exact MS1 | exact H2 | exact HE | lia | weq | reflexivity | reflexivity].
Qed.

(** 0x14000 .. 0x14028: pod_string(&pp->ent[j]) on an empty key slot. *)
Lemma inner_ok : forall K j, (n - j <= K)%nat -> inner_P j.
Proof.
  induction K as [|K IH]; intros j HK; unfold inner_P;
    intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s11 t3 t4 t5 t6 F fc m1 HF MS1 H2 HE Hj -> -> -> -> ->;
    [lia|].
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  assert (HN1 : (S j < n)%nat -> inner_P (S j)) by (intros _; apply IH; lia).
  assert (HN2 : (S (S j) < n)%nat -> inner_P (S (S j))) by (intros _; apply IH; lia).
  rewrite (skipn_nth_cons es j (Ent 0 0 []) Hj), rop_cons in HE.
  pose proof (ent_wf_nth r j HWF Hj) as (Ht0 & Hb & Hsz).
  pose proof MS1 as (MT & HPPB & H50 & H80 & HC & TM).
  pose proof (bytes_at_ent rsegs m1 pp r j HPPB HWF Hj) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat j) with (pp + 16404 + 104 * Z.of_nat j) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  (* 0x14000 lw a0,-8(a1); bne a0,s8 *)
  pose proof (ent_type_read rsegs m1 _ _ HEB Ht0) as HR. step. clear HR.
  step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth j es (Ent 0 0 []))) 8) as [Et|Et]; cbn [negb]; cbv beta iota.
  2:{ assert (EK : key_of (nth j es (Ent 0 0 [])) = None)
        by (rewrite key_of_cases; unfold POD_STRING; rewrite (proj2 (Z.eqb_neq _ _) Et); reflexivity).
      rewrite EK in HE. eapply nokey_ok; [exact Hj | exact HN1 | exact HF | exact MS1 | exact H2 | exact HE]. }
  (* 0x14008 lw a0,-4(a1); beqz a0 *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec (e_size (nth j es (Ent 0 0 []))) 0) as [Ez|Ez]; cbv beta iota.
  { assert (EK : key_of (nth j es (Ent 0 0 [])) = None)
      by (rewrite key_of_cases; rewrite Ez; cbn [Z.leb Z.compare]; rewrite andb_false_r; reflexivity).
    rewrite EK in HE. eapply nokey_ok; [exact Hj | exact HN1 | exact HF | exact MS1 | exact H2 | exact HE]. }
  (* 0x14010 addi a0,a0,-1; slli a0,a0,32; srli a0,a0,32; add a0,a1,a0; lbu a2,0(a0) *)
  step. step. step. rewrite zext32_small by lia. step.
  pose proof (ent_byte_read rsegs m1 _ _ (Z.to_nat (e_size (nth j es (Ent 0 0 [])) - 1)) HEB ltac:(lia)) as HR.
  step. clear HR.
  (* 0x14024 mv a0,a1; beqz a2 *)
  step. step. rewrite zxb_eqb0.
  destruct (Z.eqb_spec (bv_unsigned (nth (Z.to_nat (e_size (nth j es (Ent 0 0 [])) - 1))
                                         (e_body (nth j es (Ent 0 0 []))) NUL)) 0) as [Eb|Eb]; cbv beta iota.
  - (* a key: 0x14030 *)
    assert (EK : key_of (nth j es (Ent 0 0 [])) = Some (cstr (e_body (nth j es (Ent 0 0 []))))).
    { rewrite key_of_cases. unfold POD_STRING, last_body_byte. rewrite (proj2 (Z.eqb_eq _ _) Et), Eb.
      rewrite (proj2 (Z.leb_le 1 _)) by lia. reflexivity. }
    rewrite EK in HE.
    assert (HNI : (nul_idx (e_body (nth j es (Ent 0 0 []))) < length (e_body (nth j es (Ent 0 0 []))))%nat).
    { pose proof (nul_idx_le_k (e_body (nth j es (Ent 0 0 []))) (Z.to_nat (e_size (nth j es (Ent 0 0 [])) - 1))
                    ltac:(lia) Eb). lia. }
    pose proof (ent_key_bytes rsegs m1 _ _ HEB HNI) as HKB.
    replace (pp + 16404 + 104 * Z.of_nat j + 8) with (pp + 16412 + 104 * Z.of_nat j) in HKB by lia.
    eapply key_ok; [exact Hj | exact HN2 | exact HF | exact MS1 | exact H2 | exact HE | exact HKB | apply cstr_no_nul].
  - (* not NUL-terminated: 0x1402c *)
    assert (EK : key_of (nth j es (Ent 0 0 [])) = None).
    { rewrite key_of_cases. unfold last_body_byte. rewrite (proj2 (Z.eqb_neq _ _) Eb). rewrite andb_false_r. reflexivity. }
    rewrite EK in HE. eapply nokey_ok; [exact Hj | exact HN1 | exact HF | exact MS1 | exact H2 | exact HE].
Qed.

(** ** The head: memcpy, the parse, the corrupt, NULL, is_props and params_struct tests, the scan's set-up *)
Variable fl : Z.
Hypothesis HFL : 0 <= fl < 256.
Hypothesis HLEN : len = Z.of_nat (length (buf r)).
Hypothesis HPODA : pod mod 16 = 0.
Hypothesis HSEP : or_h (pod + len <= pp) (pp + 19744 <= pod).
Hypothesis HPM : corrupt r = false -> parse_model (buf r) = E0.

(** The memory before the scan's set-up: the cell sp + 0x80 still holds &pp->len. *)
Definition MemP (m1 : word -> option byte) (c : Z) : Prop :=
  MemT m1 /\ bytes_at rsegs m1 pp (pp_bytes r) /\ bytes_at rsegs m1 (SP + 80) (le8 (Z_to_bv 64 pp)) /\
  bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 (pp + 16384))) /\ bytes_at rsegs m1 (SP + 296) (le4 (Z_to_bv 64 c)) /\
  MemNorm.task_mem rsegs m1.

Lemma len_buf : 8 <= len <= 5440.
Proof. destruct (buf_header r HWF) as (_ & _ & _ & H). lia. Qed.

(** 0x13fac .. 0x13fe8: at = 0, n = n_ent, the constants, sp + 0x80 := &pp->ent[0]. *)
Lemma setup_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemP m1 (rcell (fst E0)) -> bv_unsigned s2 = snd E0 mod 2^64 ->
  is_props r = true -> params_struct r = true ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (pp + 19732)) s5 s6
             s7 s8 s9 s10 (Z_to_bv 64 pp) t3 t4 t5 t6) F (Z_to_bv 64 0x13fac) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m1 HF MP H2 EI EP.
  pose proof (proj1 (ents_wf r HWF)) as Hn. pose proof len_pp as LP.
  pose proof MP as (MT & HPPB & H50 & H80 & HC & TM). pose proof MT as (MU & WM & MI & ST).
  (* 0x13fac mv s6,zero; lui a0,4; lw s5,0(s4) *)
  step. step.
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 19732)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (ents r)))))).
  { apply (read_field rsegs m1 pp r 19732 _ HPPB HWF); [exact (pp_n_ent r HWF) | lia | unfold PP_SIZE; lia | lia]. }
  step. clear HR. rewrite sx32_small by lia.
  (* 0x13fb8 .. 0x13fd0: addi a1; addi s7; addi s8; addi s9; auipc a2; addiw a3; addiw a0 *)
  step. step. step. step. step. step. step.
  (* 0x13fd4 ld s10,0x50(sp); add a3,s10,a3; sd a3,0x80(sp) *)
  pose proof (read_le8 rsegs m1 (SP + 80) _ H50) as HR. step. clear HR. step.
  assert (HS : store_ok rsegs m1 (wa (SP + 128)) 8 = true)
    by exact (stk_store_ok rsegs m1 lo (SP + 392) (SP + 128) 8 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 128));
    assert (MS2 : MemS (write_to_mem m1 (wa (SP + 128)) BS) (rcell (fst E0)));
    [ pose proof (length_le8 (Z_to_bv 64 pp)) as L8;
      split; [apply MemT_store; rewrite ?length_le8; [exact MT | exact HS | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8; [exact HPPB | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8; [exact H50 | lia | lia | lia]|];
      split; [apply bytes_at_write_same; rewrite ?length_le8; lia|];
      split; [apply bytes_at_write_other; rewrite ?length_le8, ?length_le4; [exact HC | lia | lia | lia]|];
      apply task_mem_write; rewrite ?length_le8; [exact TM | exact HS]
    | revert MS2; generalize (write_to_mem m1 (wa (SP + 128)) BS) as m2; intros m2 MS2 ]
  end.
  (* 0x13fe0 add s10,s10,a0; sub s11,a1,s5; addi s3,a2,0x366 *)
  step. step. step.
  eapply (outer_ok 0).
  - intros Hl. apply (inner_ok (length (ents r)) 0). lia.
  - exact HF.
  - exact MS2.
  - exact H2.
  - exact (expect_struct r EI EP).
  - lia.
  - weq.
  - weq.
  - weq.
Qed.

(** 0x13f88 .. 0x13fa8: corrupt, the NULL flag, is_props, params_struct. *)
Lemma after_parse : forall (ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                           (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemP m1 (rcell (fst (parse_res (Z.testbit fl 0) (buf r)))) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) (Z_to_bv 64 (snd (parse_res (Z.testbit fl 0) (buf r))))
             a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fl)) 1)) (Z_to_bv 64 (pp + 19732))
             (Z_to_bv 64 fl) s6 s7 s8 s9 s10 (Z_to_bv 64 pp) t3 t4 t5 t6) F (Z_to_bv 64 0x13f88) fc None m1
        (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m1 HF MP.
  pose proof len_pp as LP.
  pose proof MP as (MT & HPPB & H50 & H80 & HC & TM).
  (* 0x13f88 lw a1,4(s4); mv s2,a0; bnez a1 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 19736)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (corrupt r))))).
  { apply (read_field rsegs m1 pp r 19736 _ HPPB HWF);
      [exact (pp_corrupt r HWF) | lia | unfold PP_SIZE; lia | destruct (corrupt r); cbn; lia]. }
  revert HR. destruct (corrupt r) eqn:EC; cbn [Z.b2z]; intros HR.
  { step. clear HR. rewrite sx32_small by lia. step. step. if_true. eapply tail_ok; [exact HF | exact MT]. }
  step. clear HR. rewrite sx32_small by lia. step. step. if_false.
  (* 0x13f94 ld a1,0x80(sp); bnez s3 *)
  pose proof (read_le8 rsegs m1 (SP + 128) _ H80) as HR. step. clear HR.
  step. rewrite (unsigned_lit fl) by lia. rewrite (land1_bit fl HFL).
  revert MP HC. destruct (Z.testbit fl 0) eqn:EB; intros MP HC; cbv beta iota.
  { (* the NULL argument: check_malformed *)
    if_true. cbn [parse_res fst snd rcell] in HC |- *.
    eapply malformed_ok; [exact HF | exact MT | reflexivity | exact HC]. }
  if_false. change (parse_res false (buf r)) with (parse_model (buf r)) in MP, HC |- *. rewrite HPM in MP, HC |- * by first [exact EC | reflexivity].
  (* 0x13f9c lw a0,8(a1); beqz a0 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 16392)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (is_props r))))).
  { apply (read_field rsegs m1 pp r 16392 _ HPPB HWF);
      [exact (pp_is_props r HWF) | lia | unfold PP_SIZE; lia | destruct (is_props r); cbn; lia]. }
  revert HR. destruct (is_props r) eqn:EI; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      rewrite (expect_not_props r EI) in HC |- *. cbn [fst snd rcell] in HC |- *.
      eapply malformed_ok; [exact HF | exact MT | reflexivity | exact HC]. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  (* 0x13fa4 lw a0,0x10(a1); beqz a0 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 16400)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (params_struct r))))).
  { apply (read_field rsegs m1 pp r 16400 _ HPPB HWF);
      [exact (pp_params_struct r HWF) | lia | unfold PP_SIZE; lia | destruct (params_struct r); cbn; lia]. }
  revert HR. destruct (params_struct r) eqn:EP; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      rewrite (expect_no_struct r EI EP) in HC |- *. cbn [fst snd rcell] in HC |- *.
      eapply absent_ok; [exact HF | exact MT | reflexivity | exact HC | exact H50]. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  eapply setup_ok; [exact HF | exact MP | apply unsigned_lit_wrap | exact EI | exact EP].
Qed.

Hypothesis MCPY : memcpy_contract.
Hypothesis PARSE : reac_role_prop_parse_contract.

(** The parse's memory: its frame, and the role cell when it answers a role. *)
Lemma MemP_parse : forall m2 m3 o, MemP m2 0x5a -> role_mem m2 m3 SP (SP + 296) o -> wmono rsegs m2 m3 ->
  mem_inv rsegs m3 -> stk rsegs m3 lo SP -> MemP m3 (rcell o).
Proof.
  intros m2 m3 o (MT & HPPB & H50 & H80 & HC & TM) RM WM3 MI3 ST3. pose proof len_pp as LP.
  pose proof MT as (_ & _ & _ & ST).
  destruct o as [w|]; cbn [role_mem rcell] in RM |- *.
  - destruct RM as (MU3 & HW). unfold PARSE_FRAME in MU3.
    split.
    { apply (MemT_call m2 m3 _ MT MU3 WM3 MI3 ST3).
      - unfold sub_fp, WC. cbn [outside]. intros x (O1 & _ & _). repeat split; try exact I; lia.
      - intros x Hx. destruct (Z_lt_le_dec x (SP + 296)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; lia|].
        destruct (Z_lt_le_dec x (SP + 300)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; lia].
        apply (bytes_at_some rsegs m3 (SP + 296) _ x HW); rewrite length_le4; [intros a Ha; apply HROM | ]; lia. }
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HPPB MU3); cbn [disjoint_from]; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ H50 MU3); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ H80 MU3); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [exact HW|].
    apply (task_mem_munch rsegs _ m2 m3 TM MU3). apply (stk_wview rsegs m2 lo (SP + 392)); [exact ST|].
    intros x Hx. cbn [outside] in Hx. lia.
  - unfold PARSE_FRAME in RM.
    split; [apply (MemT_below m2 m3 80 MT RM WM3 MI3 ST3); lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HPPB RM); cbn [disjoint_from]; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ H50 RM); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ H80 RM); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HC RM); cbn [disjoint_from]; rewrite length_le4; repeat split; lia|].
    apply (task_mem_munch rsegs _ m2 m3 TM RM). apply (stk_wview rsegs m2 lo (SP + 392)); [exact ST|].
    intros x Hx. cbn [outside] in Hx. lia.
Qed.

(** 0x13f68 .. 0x13f84: cur = fl bit 1, role := 0x5a, rc = reac_role_prop_parse(fl & 1 ? NULL : pod, &role). *)
Lemma after_cpy : forall (ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bytes_at rsegs m1 pp (pp_bytes r) -> bytes_at rsegs m1 (SP + 80) (le8 (Z_to_bv 64 pp)) ->
  bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 (pp + 16384))) -> MemNorm.task_mem rsegs m1 ->
  bytes_at rsegs m1 pod (buf r) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pod) (Z_to_bv 64 pod) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) s3
             (Z_to_bv 64 (pp + 19732)) (Z_to_bv 64 fl) s6 s7 s8 s9 s10 (Z_to_bv 64 pp) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f68) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m1 HF MT HPPB H50 H80 TM HPB.
  pose proof len_pp as LP. pose proof len_buf as LB. pose proof (buf_header r HWF) as (_ & _ & HU & _).
  pose proof MT as (MU & WM & MI & ST).
  (* 0x13f68 slli s0,s5,62; addi a0,zero,0x5a; andi s3,s5,1; sw a0,0x128(sp) *)
  step. step. step.
  assert (HS : store_ok rsegs m1 (wa (SP + 296)) 4 = true)
    by exact (stk_store_ok rsegs m1 lo (SP + 392) (SP + 296) 4 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 296));
    assert (MP2 : MemP (write_to_mem m1 (wa (SP + 296)) BS) 0x5a);
    [ split; [apply MemT_store; rewrite ?length_le4; [exact MT | exact HS | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le4; [exact HPPB | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H50 | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H80 | lia | lia | lia]|];
      split; [apply bytes_at_write_same; rewrite ?length_le4; lia|];
      apply task_mem_write; rewrite ?length_le4; [exact TM | exact HS]
    | assert (HPB2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 296)) BS) pod (buf r))
        by (apply bytes_at_write_other; rewrite ?length_le4; [exact HPB | lia | lia | lia]);
      revert MP2 HPB2; generalize (write_to_mem m1 (wa (SP + 296)) BS) as m2; intros m2 MP2 HPB2 ]
  end.
  clear MU WM MI ST MT HPPB H50 H80 TM HS.
  pose proof MP2 as (MT & HPPB & H50 & H80 & HC & TM). pose proof MT as (MU & WM & MI & ST).
  (* 0x13f78 addi a0,s3,-1; and a0,a0,s1; addi a1,sp,0x128; jal reac_role_prop_parse *)
  step. step. step. step.
  eapply evt_cut.
  { eapply PARSE with (null := Z.testbit fl 0) (lo := lo) (P := pod) (Q := SP + 296) (bs := buf r).
    - f_equal. apply parse_arg; lia.
    - reflexivity.
    - unfold role_args. split; [exact HPB2|]. split; [lia|]. split; [exact HPODA|]. split; [lia|].
      split; [rewrite HU; reflexivity|]. split; [lia|].
      split; [apply (stk_wr_at rsegs m2 lo (SP + 392)); [exact ST | lia | lia | lia]|]. split; lia.
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

(** 0x13f4c .. 0x13f64: pod <> 0; memcpy(pod, pp, len) (len >= 8). *)
Lemma head_ok : forall (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (junk : list byte),
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> stk rsegs m lo (SP + 392) ->
  bytes_at rsegs m pp (pp_bytes r) -> bytes_at rsegs m (SP + 80) (le8 (Z_to_bv 64 pp)) ->
  bytes_at rsegs m (SP + 128) (le8 (Z_to_bv 64 (pp + 16384))) -> rw_cells rsegs m pod [CB (Z.to_nat len) junk] ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pod) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) s3
             (Z_to_bv 64 (pp + 19732)) (Z_to_bv 64 fl) s6 s7 s8 s9 s10 (Z_to_bv 64 pp) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f4c) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc junk HF HMI HTM HST HPPB H50 H80 HPC.
  pose proof len_pp as LP. pose proof len_buf as LB. pose proof HST as (HS0 & HS1 & _).
  (* 0x13f4c beqz a0; mv s1,a0; beqz s2 *)
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  step. step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x13f58 mv a0,s1; mv a1,s11; mv a2,s2; jal memcpy *)
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
    apply (stk_transport_disjoint rsegs _ m m1 _ _ HST MU1 WM1). cbn [disjoint_from]. split; [lia | exact I]. }
  assert (DJ : forall A k, lo <= A -> A + k <= SP + 392 -> disjoint_from [(pod, pod + len)] A k)
    by (intros A k H1 H2; cbn [disjoint_from]; split; [lia | exact I]).
  eapply after_cpy.
  - exact HF.
  - exact MT1.
  - apply (bytes_at_transport rsegs _ m m1 _ _ HPPB MU1). cbn [disjoint_from]. unfold or_h in HSEP. split; [lia | exact I].
  - apply (bytes_at_transport rsegs _ m m1 _ _ H50 MU1). rewrite length_le8. apply DJ; lia.
  - apply (bytes_at_transport rsegs _ m m1 _ _ H80 MU1). rewrite length_le8. apply DJ; lia.
  - apply (task_mem_munch rsegs _ m m1 HTM MU1). intros x Hx. cbn [outside] in Hx.
    destruct (rw_cells_bound rsegs m pod _ HPC) as [B1 B2]. cbn [cells_size csize] in B2.
    destruct HPC as [_ (W0 & W1 & W)]. cbn [cells_size csize] in W.
    pose proof (W (bv_unsigned x - pod)) as Wx. replace (pod + (bv_unsigned x - pod)) with (bv_unsigned x) in Wx by lia.
    unfold wa in Wx. rewrite Z_to_bv_lit_self in Wx. apply Wx. lia.
  - exact (rw_cells_CB_bytes rsegs m1 pod _ _ CB1).
Qed.

End Check.
