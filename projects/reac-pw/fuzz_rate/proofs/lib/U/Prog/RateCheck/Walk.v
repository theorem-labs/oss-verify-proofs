(** The walk of reac-pw/fuzz_rate's LLVMFuzzerTestOneInput (UBSan) from malloc(pod)'s return (0x1420c) to the pc
    after check_code(refuse_code(MALFORMED), MALFORMED) returned (0x14614), against U/Prog/LLVMFuzzerTestOneInput_c.v's
    rate_check_contract, with the callee contracts (U/Prog/*_c.v) as Section hypotheses. The form is reac-pw/fuzz_role's
    U/Prog/RoleCheck/Walk.v, re-walked at rate's registers, stack slots and
    addresses. Walked backwards: QC_done (0x14614), end_ok (0x14604); the decide loop 0x1451c .. 0x14600 (counter
    s1 = 0, 1; one round, body_ok, over any asked word, applied twice by loop_ok: next_ok 0x145fc, list_ok 0x145c0,
    code_loop_ok 0x145a8, the inline expect_decide 0x1453c .. 0x145a4 (inline_ok, closed_ok) against
    reac_rate_cfg_decide's decide_res); its set-up asked_ok (0x144f8, asked[] stores 0x14500-0x14504) and tail_ok
    (0x144bc); reload_ok (0x143c8), absent_ok (0x143bc), rate_ok (0x1449c), malformed_ok (0x144b0) and malformed_ld
    (0x144ac); float_ok (0x14470, pod_nearest(f, sp + 0xe8)), value_ok (0x14378); the pod_next_pair scan (outer_ok
    0x142b4; at 0x142dc an empty key slot, none_ok, or a key in it, some_ok with strcmp against "reac.cfg.rate" at
    0x1045e and s10 spilled to sp + 0xe0; next_ent_ok 0x14330), by induction on the entries left (scan_ok); setup_ok
    (0x1426c), after_parse (0x14248), MemP_parse, after_cpy (0x14228, the hz cell sp + 0x188) and head_ok (0x1420c,
    memcpy). The head (from `Variable r` on) was written from role's lines 270-989.

    The six UBSan checks of the range (all to the `unimp` at 0x146bc) are each shown not taken, as role's: the bound 33
    of ent[*at] (0x142e0 `beq a2,s11`) and of ent[v] (0x1437c `bgeu s11,a0`) by n_ent <= 32; the pointer overflow of
    ent + 104 at (0x142e4, 0x14384 `bltu s7,s2`, s7 = ~(pp + 0x4014)) and of body + size - 1 (0x14308 `bltu a3,a0`,
    a3 = ~(pp + 0x401c + 104 at)) because the pp block lies below the stack (pp + 19744 <= lo < 2^64) and
    e_size <= 45 <= 96; the overflow of at + 1 (0x1434c `blt s5,a5`) by at < 32. None lies in the decide loop.

    The decide loop needs no value of asked[]: each callee contract there is unconditional in its argument registers,
    and the inlined bit_of scans (closed_list at .rodata 0x10628) compare the whole 64-bit register s6, so the inline
    expect_decide is decide_res (bv_unsigned s4) (bv_unsigned s6) (bv_unsigned s10) for ANY word s6 and for s4 the top
    bit of s2 << 62, 0 or 1 (Pod/RateCfg.v). The memory carries refuse_code's codes[] table (U/Prog/RateCheck/Facts.v
    ctbl), which no write of the segment reaches, and the cells sp + 0x10 = mask, sp + 0x30 = buflen, sp + 0xd8 = pp,
    which no store of the segment reaches (every store lies at or above sp + 0xe0). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import memcpy_c reac_rate_prop_parse_c strcmp_c
  pod_nearest_c check_absent_c check_rate_c check_malformed_c reac_rate_cfg_decide_c check_decide_c
  reac_rate_refuse_code_c check_code_c reac_rate_bit_c reac_rate_is_closed_c reac_rate_best_drivable_c check_list_c
  SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa Nearest Rate
  RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateCheck Require Import Facts.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateCheck Require Import Facts.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).
(* Register equations at a loop head. *)
Ltac weq := first [ reflexivity
                  | (rewrite addiw1_small by lia; f_equal; lia)
                  | (f_equal; lia)
                  | (f_equal; rewrite ?unsigned_lit by lia; lia)
                  | (f_equal; rewrite ?unsigned_lit by lia; rewrite ?Z.shiftl_mul_pow2 by lia;
                     rewrite ?unsigned_lit by lia; lia) ].

Section Check.
Variables (sp gp tp : word) (m : word -> option byte) (len pp pod lo mask buflen fl : Z).

Local Abbreviation SP := (bv_unsigned sp).

Hypothesis HPOD : 0 < pod.
Hypothesis HLEN0 : 0 <= len.
Hypothesis HPODLO : pod + len <= lo.
Hypothesis HPP0 : 0 <= pp.
Hypothesis HPPLO : pp + 19744 <= lo.
Hypothesis HLO0 : 0 <= lo.
Hypothesis HLO : lo + 4096 <= SP.
Hypothesis HSPT : SP + 488 <= 2^64.
Hypothesis HSPA : SP mod 16 = 0.
Hypothesis HROM : forall a, lo <= a < SP + 488 -> seg_rom rsegs (wa a) = None.
Hypothesis HPROM : forall a, pod <= a < pod + len -> seg_rom rsegs (wa a) = None.
Hypothesis HFL : 0 <= fl < 256.

Definition QC : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s6' s7' s8' s9' s11'
                     t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                  s2' (Z_to_bv 64 pod) s4' s5' s6' s7' s8' s9' (Z_to_bv 64 mask) s11' t3' t4' t5' t6')
             F' (Z_to_bv 64 RATE_CHECK_END) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\
    bytes_at rsegs m' (SP + 0x30) (le8 (Z_to_bv 64 buflen)) /\
    bytes_at rsegs m' (SP + 0xd8) (le8 (Z_to_bv 64 pp)) /\
    munch [(SP - MID_STACK, SP + FRAME_LOCALS); (pod, pod + len)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (SP + FRAME_LOCALS).

(** The footprint and the memory the walk carries: refuse_code's table read as the image and the three cells the
    tail reads or the contract returns (sp + 0x10 = mask, sp + 0x30 = buflen, sp + 0xd8 = pp). *)
Definition WC : list (Z * Z) := [(SP - 4096, SP + 488); (pod, pod + len)].
Definition MemT (m1 : word -> option byte) : Prop :=
  munch WC m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (SP + 488) /\ ctbl m1 /\
  bytes_at rsegs m1 (SP + 16) (le8 (Z_to_bv 64 mask)) /\ bytes_at rsegs m1 (SP + 48) (le8 (Z_to_bv 64 buflen)) /\
  bytes_at rsegs m1 (SP + 216) (le8 (Z_to_bv 64 pp)).

Lemma table_out : forall a, CODES_LO <= a < CODES_HI -> outside WC a.
Proof.
  intros a Ha. unfold WC. cbn [outside]. pose proof (codes_apart lo (SP + 488) HROM a Ha) as H1.
  pose proof (codes_apart pod (pod + len) HPROM a Ha) as H2. split; [lia|]. split; [exact H2 | exact I].
Qed.

(** A store at or above sp + 0xe0 (the s10 spill, pod_nearest's and asked[]'s cells, the hz cell). *)
Lemma MemT_store : forall m1 a bs, MemT m1 -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP + 224 <= a -> a + Z.of_nat (length bs) <= SP + 488 -> MemT (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs (MU & WM & MI & ST & TB & H10 & H30 & HD8) HS H1 H2. pose proof ST as (ST0 & ST1 & _).
  split; [apply munch_write; [exact MU | lia | lia | unfold WC; cbn [inside]; left; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | exact HS]|].
  split; [apply stk_write; [exact ST | lia | lia]|].
  split.
  { apply (ctbl_munch [(a, a + Z.of_nat (length bs))] m1); [exact TB | |].
    - apply munch_write; [apply munch_refl | lia | lia | cbn [inside]; left; lia].
    - intros x Hx. pose proof (table_out x Hx) as O. unfold WC in O. cbn [outside] in O |- *.
      destruct O as (O1 & _). split; [lia | exact I]. }
  split; [apply bytes_at_write_other; [exact H10 | lia | lia | rewrite length_le8; lia]|].
  split; [apply bytes_at_write_other; [exact H30 | lia | lia | rewrite length_le8; lia]|].
  apply bytes_at_write_other; [exact HD8 | lia | lia | rewrite length_le8; lia].
Qed.

(** A callee whose footprint lies below the stack top or in the frame's locals at or above sp + 0xe0. *)
Lemma MemT_call : forall m1 m2 W, MemT m1 -> munch W m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo SP -> sub_fp W WC -> (forall x, SP <= x < SP + 224 -> outside W x) ->
  (forall x, SP <= x < SP + 488 -> outside W x \/ exists b, m2 (wa x) = Some b) -> MemT m2.
Proof.
  intros m1 m2 W (MU & WM & MI & ST & TB & H10 & H30 & HD8) MU2 WM2 MI2 ST2 SUB HC HX.
  split; [exact (munch_trans WC m m1 m2 MU (munch_weaken W WC m1 m2 SUB MU2))|].
  split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
  split; [exact MI2|].
  split.
  { destruct (stk_split rsegs m1 lo SP (SP + 488) ST ltac:(lia)) as [_ ST1].
    apply (stk_merge rsegs m2 lo SP); [exact ST2 | | lia].
    exact (stk_transport rsegs W m1 m2 SP (SP + 488) ST1 MU2 WM2 HX). }
  split; [apply (ctbl_munch W m1 m2 TB MU2); intros a Ha; apply SUB; exact (table_out a Ha)|].
  split; [apply (bytes_at_munch_out rsegs W m1 m2 _ _ MU2); [rewrite length_le8; intros i Hi; apply HC; lia | exact H10]|].
  split; [apply (bytes_at_munch_out rsegs W m1 m2 _ _ MU2); [rewrite length_le8; intros i Hi; apply HC; lia | exact H30]|].
  apply (bytes_at_munch_out rsegs W m1 m2 _ _ MU2); [rewrite length_le8; intros i Hi; apply HC; lia | exact HD8].
Qed.

Lemma MemT_below : forall m1 m2 k, MemT m1 -> munch [(SP - k, SP)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo SP -> 0 <= k <= 4096 -> MemT m2.
Proof.
  intros m1 m2 k MT MU WM MI ST Hk. apply (MemT_call m1 m2 [(SP - k, SP)] MT MU WM MI ST).
  - unfold sub_fp, WC. cbn [outside]. intros x (O1 & _ & _). split; [lia | exact I].
  - intros x Hx. cbn [outside]. split; [lia | exact I].
  - intros x Hx. left. cbn [outside]. split; [lia | exact I].
Qed.

Lemma MemT_stk : forall m1, MemT m1 -> stk rsegs m1 lo SP.
Proof. intros m1 (_ & _ & _ & ST & _). exact (proj1 (stk_split rsegs m1 lo SP (SP + 488) ST ltac:(lia))). Qed.

Hypothesis RFC : reac_rate_refuse_code_contract.
Hypothesis CKC : check_code_contract.

(** 0x14614: the contract's postcondition. *)
Lemma QC_done : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 s9
             (Z_to_bv 64 mask) s11 t3 t4 t5 t6) F (Z_to_bv 64 RATE_CHECK_END) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m1 HF
    (MU & WM & MI & ST & _ & _ & H30 & HD8).
  apply evt_done. exists ra, t0, t1, t2, s0, s1, a0, a1, a2, a3, a4, a5, a6, a7, s2, s4, s5, s6, s7, s8, s9, s11,
    t3, t4, t5, t6, F, fc, m1.
  split; [reflexivity|]. split; [exact HF|]. split; [exact H30|]. split; [exact HD8|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST].
Qed.

(** 0x14604 .. 0x14614: check_code(refuse_code(MALFORMED), MALFORMED). *)
Lemma end_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
                      (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 s9
             (Z_to_bv 64 mask) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14604) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m1 HF MT.
  pose proof MT as (_ & _ & MI & _ & TB & _).
  (* 0x14604 addi a0,zero,4; jal reac_rate_refuse_code *)
  step. step.
  eapply evt_cut; [eapply RFC; exact (ctbl_refuse m1 TB)|]. intros ms' (a1x & a2x & a3x & ->). ret_even.
  (* 0x1460c addi a1,zero,4; jal check_code *)
  step. step.
  eapply evt_cut.
  { eapply CKC with (lo := lo);
      [ rewrite unsigned_lit by lia; lia | reflexivity | exact (MemT_stk m1 MT) | unfold CHECK_CODE_FRAME; lia
      | intros a Ha; apply HROM; lia | exact MI]. }
  intros ms' (a0' & a1' & a2' & a3' & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'. ret_even.
  apply QC_done; [exact HF|].
  apply (MemT_below m1 m2 CHECK_CODE_FRAME MT MU2 WM2 MI2 ST2). unfold CHECK_CODE_FRAME. lia.
Qed.

(** ** The decide loop 0x1451c .. 0x14600 *)
(** The loop head at round i (s1 = i): s0 = 1, s2 = sp + 0xe8 (asked[]), s3 = pod, s4 the role bit (0 or 1),
    s8 = closed_list (0x10628), s9 = 2, s10 = mask. *)
Definition loop_P (i : Z) : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s4 <= 1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 i) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 232))
             (Z_to_bv 64 pod) s4 s5 s6 s7 (Z_to_bv 64 0x10628) (Z_to_bv 64 2) (Z_to_bv 64 mask) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1451c) fc None m1 (seg_rom rsegs)).

(** 0x145fc .. 0x14600: i + 1, the next round or the end. *)
Lemma next_ok : forall i, 0 <= i <= 1 -> (i + 1 < 2 -> loop_P (i + 1)) ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s4 <= 1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 i) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 232))
             (Z_to_bv 64 pod) s4 s5 s6 s7 (Z_to_bv 64 0x10628) (Z_to_bv 64 2) (Z_to_bv 64 mask) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x145fc) fc None m1 (seg_rom rsegs)).
Proof.
  intros i Hi HN ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s11 t3 t4 t5 t6 F fc m1 HF MT H4.
  (* 0x145fc addi s1,s1,1; bne s1,s9 *)
  step. step.
  match goal with |- context [bv_eqb ?X (Z_to_bv 64 2)] =>
    replace (bv_eqb X (Z_to_bv 64 2)) with (i + 1 =? 2)
      by (symmetry; unfold bv_eqb; rewrite !unsigned_lit by lia; rewrite ?(unsigned_lit i) by lia; reflexivity)
  end.
  destruct (Z.eqb_spec (i + 1) 2) as [E|E]; cbn [negb]; cbv beta iota.
  - eapply end_ok; [exact HF | exact MT].
  - eapply (HN ltac:(lia)); [exact HF | exact MT | exact H4].
Qed.

Hypothesis RBIT : reac_rate_bit_contract.
Hypothesis RCL : reac_rate_is_closed_contract.
Hypothesis RBEST : reac_rate_best_drivable_contract.
Hypothesis CKL : check_list_contract.

(** 0x145c0 .. 0x145f8: check_list(asked[i], bit(asked[i]), is_closed(asked[i]), mask, best_drivable(mask)), asked[i]
    read again from its cell: any word. *)
Lemma list_ok : forall i, 0 <= i <= 1 -> (i + 1 < 2 -> loop_P (i + 1)) ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s4 <= 1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 i) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 232))
             (Z_to_bv 64 pod) s4 s5 s6 (Z_to_bv 64 (SP + 232 + 4 * i)) (Z_to_bv 64 0x10628) (Z_to_bv 64 2)
             (Z_to_bv 64 mask) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x145c0) fc None m1 (seg_rom rsegs)).
Proof.
  intros i Hi HN ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s11 t3 t4 t5 t6 F fc m1 HF MT H4.
  pose proof MT as (_ & _ & MI & ST & _).
  destruct (stk_read rsegs m1 lo (SP + 488) (SP + 232 + 4 * i) 4 ST ltac:(lia) ltac:(lia)) as (bs & HR).
  (* 0x145c0 lw s5,0(s7); mv a0,s5; jal reac_rate_bit *)
  step. clear HR. step. step.
  eapply evt_cut; [eapply RBIT|]. intros ms' (a1x & ->). ret_even.
  (* 0x145cc mv s6,a0; mv a0,s5; jal reac_rate_is_closed *)
  step. step. step.
  eapply evt_cut; [eapply RCL|]. intros ms' (a1y & a2y & ->). ret_even.
  (* 0x145d8 mv s7,a0; mv a0,s10; jal reac_rate_best_drivable *)
  step. step. step.
  eapply evt_cut; [eapply RBEST|]. intros ms' (a1z & ->). ret_even.
  (* 0x145e4 mv a4,a0; mv a0,s5; mv a1,s6; mv a2,s7; mv a3,s10; jal check_list *)
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply CKL with (lo := lo); [reflexivity | reflexivity | reflexivity | exact (MemT_stk m1 MT)
                                | unfold CHECK_LIST_FRAME; lia | intros a Ha; apply HROM; lia | exact MI]. }
  intros ms' (a0' & a1' & a3' & a5' & a6' & a7' & t0' & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'. ret_even.
  eapply next_ok; [exact Hi | exact HN | exact HF | | exact H4].
  apply (MemT_below m1 m2 CHECK_LIST_FRAME MT MU2 WM2 MI2 ST2). unfold CHECK_LIST_FRAME. lia.
Qed.

Hypothesis CKD : check_decide_contract.

(** 0x145a8 .. 0x145bc: check_decide(decide, expect), check_code(refuse_code(decide), decide). *)
Lemma code_loop_ok : forall i, 0 <= i <= 1 -> (i + 1 < 2 -> loop_P (i + 1)) ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s4 <= 1 ->
  a1 = Z_to_bv 64 (decide_res (bv_unsigned s4) (bv_unsigned s6) (bv_unsigned (Z_to_bv 64 mask))) ->
  s5 = Z_to_bv 64 (decide_res (bv_unsigned s4) (bv_unsigned s6) (bv_unsigned (Z_to_bv 64 mask))) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 i) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 232))
             (Z_to_bv 64 pod) s4 s5 s6 (Z_to_bv 64 (SP + 232 + 4 * i)) (Z_to_bv 64 0x10628) (Z_to_bv 64 2)
             (Z_to_bv 64 mask) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x145a8) fc None m1 (seg_rom rsegs)).
Proof.
  intros i Hi HN ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s11 t3 t4 t5 t6 F fc m1 HF MT H4 -> ->.
  pose proof MT as (_ & _ & MI & _ & TB & _).
  (* 0x145a8 mv a0,s5; jal check_decide *)
  step. step.
  eapply evt_cut; [eapply CKD; reflexivity|]. intros ms' ->. ret_even.
  (* 0x145b0 mv a0,s5; jal reac_rate_refuse_code *)
  step. step.
  eapply evt_cut; [eapply RFC; exact (ctbl_refuse m1 TB)|]. intros ms' (a1x & a2x & a3x & ->). ret_even.
  (* 0x145b8 mv a1,s5; jal check_code *)
  step. step.
  eapply evt_cut.
  { eapply CKC with (lo := lo);
      [ rewrite (proj1 (decide_res_word _ _ _)); exact (proj2 (decide_res_word _ _ _)) | reflexivity
      | exact (MemT_stk m1 MT) | unfold CHECK_CODE_FRAME; lia
      | intros a Ha; apply HROM; lia | exact MI]. }
  intros ms' (a0' & a1' & a2' & a3' & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'. ret_even.
  eapply list_ok; [exact Hi | exact HN | exact HF | | exact H4].
  apply (MemT_below m1 m2 CHECK_CODE_FRAME MT MU2 WM2 MI2 ST2). unfold CHECK_CODE_FRAME. lia.
Qed.

(** 0x1459c .. 0x145a4: a closed rate's bit b in a0: expect = (b & mask) == 0 ? NOT_DRIVABLE : NONE. *)
Lemma closed_ok : forall i, 0 <= i <= 1 -> (i + 1 < 2 -> loop_P (i + 1)) ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s4 = 0 -> rate_bit (bv_unsigned s6) <> 0 ->
  a0 = Z_to_bv 64 (rate_bit (bv_unsigned s6)) ->
  s5 = Z_to_bv 64 (decide_res (bv_unsigned s4) (bv_unsigned s6) (bv_unsigned (Z_to_bv 64 mask))) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 i) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 232))
             (Z_to_bv 64 pod) s4 s5 s6 (Z_to_bv 64 (SP + 232 + 4 * i)) (Z_to_bv 64 0x10628) (Z_to_bv 64 2)
             (Z_to_bv 64 mask) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1459c) fc None m1 (seg_rom rsegs)).
Proof.
  intros i Hi HN ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s11 t3 t4 t5 t6 F fc m1 HF MT H4 HB -> H5.
  pose proof (rate_bit_range (bv_unsigned s6)) as RB.
  (* 0x1459c and a0,a0,s10; seqz a1,a0; slli a1,a1,1 *)
  step. step. step.
  eapply code_loop_ok; [exact Hi | exact HN | exact HF | exact MT | lia | | exact H5].
  rewrite H4, (decide_res_closed _ _ HB). f_equal.
  rewrite (unsigned_lit (rate_bit _)) by lia.
  pose proof (land_lt64 (rate_bit (bv_unsigned s6)) (bv_unsigned (Z_to_bv 64 mask)) ltac:(lia)
                (proj1 (bv_unsigned_in_range _ _))) as L.
  apply seqz_slli. exact L.
Qed.

(** 0x1453c .. 0x14598: the inline expect_decide (fuzz_rate.c:89-98): role != 0 is ROLE_SLAVE; else the two bit_of
    scans of closed_list (0x10628: 44100, 48000, 96000) over the whole word s6. *)
Lemma inline_ok : forall i, 0 <= i <= 1 -> (i + 1 < 2 -> loop_P (i + 1)) ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s4 <= 1 ->
  s5 = Z_to_bv 64 (decide_res (bv_unsigned s4) (bv_unsigned s6) (bv_unsigned (Z_to_bv 64 mask))) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 i) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 232))
             (Z_to_bv 64 pod) s4 s5 s6 (Z_to_bv 64 (SP + 232 + 4 * i)) (Z_to_bv 64 0x10628) (Z_to_bv 64 2)
             (Z_to_bv 64 mask) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1453c) fc None m1 (seg_rom rsegs)).
Proof.
  intros i Hi HN ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s11 t3 t4 t5 t6 F fc m1 HF MT H4 H5.
  pose proof MT as (_ & _ & MI & _).
  (* 0x1453c bnez s4 *)
  step. rewrite bv_eqb_lit by lia.
  destruct (Z.eqb_spec (bv_unsigned s4) 0) as [E4|E4]; cbn [negb]; cbv beta iota.
  2:{ (* 0x14564 addi a1,zero,3; j 0x145a8 *)
      step. step.
      eapply code_loop_ok; [exact Hi | exact HN | exact HF | exact MT | exact H4 | | exact H5].
      pose proof (u64_range s4). replace (bv_unsigned s4) with 1 by lia. rewrite decide_res_slave. reflexivity. }
  assert (EQB : forall c, 0 <= c < 2^64 -> bv_eqb s6 (Z_to_bv 64 c) = (bv_unsigned s6 =? c))
    by (intros c Hc; apply bv_eqb_lit; exact Hc).
  (* 0x14540 addi a0,zero,3; mv a1,s8; 0x14548 lw a2,0(a1) = 44100; beq s6,a2 *)
  step. step. step. step. rewrite EQB by lia.
  destruct (Z.eqb_spec (bv_unsigned s6) 44100) as [E1|E1]; cbv beta iota.
  { (* 0x1456c mv a0,zero; addi a1,zero,3; mv a2,s8; lw a3,0(a2); beq s6,a3 (taken); 0x14598 sllw a0,s0,a0 *)
    step. step. step. step. step. rewrite EQB by lia. rewrite (proj2 (Z.eqb_eq _ _) E1). cbv beta iota.
    step.
    eapply closed_ok; [exact Hi | exact HN | exact HF | exact MT | exact E4 | rewrite E1; discriminate | | exact H5].
    rewrite E1. vm_compute. reflexivity. }
  (* 0x14550 addi a0,a0,-1; addi a1,a1,4; bnez a0; lw a2,0(a1) = 48000; beq s6,a2 *)
  step. step. step. try if_true. step. step. rewrite EQB by lia.
  destruct (Z.eqb_spec (bv_unsigned s6) 48000) as [E2|E2]; cbv beta iota.
  { step. step. step. step. step. rewrite EQB by lia. rewrite (proj2 (Z.eqb_neq _ _) E1). cbv beta iota.
    (* 0x14580 addi a0,a0,1; addi a1,a1,-1; addi a2,a2,4; bnez a1; lw a3 = 48000; beq s6,a3 (taken) *)
    step. step. step. step. try if_true. step. step. rewrite EQB by lia. rewrite (proj2 (Z.eqb_eq _ _) E2).
    cbv beta iota. step.
    eapply closed_ok; [exact Hi | exact HN | exact HF | exact MT | exact E4 | rewrite E2; discriminate | | exact H5].
    rewrite E2. vm_compute. reflexivity. }
  step. step. step. try if_true. step. step. rewrite EQB by lia.
  destruct (Z.eqb_spec (bv_unsigned s6) 96000) as [E3|E3]; cbv beta iota.
  { step. step. step. step. step. rewrite EQB by lia. rewrite (proj2 (Z.eqb_neq _ _) E1). cbv beta iota.
    step. step. step. step. try if_true. step. step. rewrite EQB by lia. rewrite (proj2 (Z.eqb_neq _ _) E2).
    cbv beta iota.
    step. step. step. step. try if_true. step. step. rewrite EQB by lia. rewrite (proj2 (Z.eqb_eq _ _) E3).
    cbv beta iota. step.
    eapply closed_ok; [exact Hi | exact HN | exact HF | exact MT | exact E4 | rewrite E3; discriminate | | exact H5].
    rewrite E3. vm_compute. reflexivity. }
  (* no closed rate: 0x14550 .. 0x14558 (a0 = 0), 0x1455c addi a1,zero,1; j 0x145a8 *)
  step. step. step. try if_false. step. step.
  eapply code_loop_ok; [exact Hi | exact HN | exact HF | exact MT | exact H4 | | exact H5].
  rewrite E4, decide_res_open; [reflexivity|].
  unfold rate_bit, RATE_44K1, RATE_48K, RATE_96K.
  rewrite (proj2 (Z.eqb_neq _ _) E1), (proj2 (Z.eqb_neq _ _) E2), (proj2 (Z.eqb_neq _ _) E3). reflexivity.
Qed.

Hypothesis DEC : reac_rate_cfg_decide_contract.

(** 0x1451c .. 0x14538: asked[i] (any word) from sp + 0xe8 + 4 i, reac_rate_cfg_decide(role, asked[i], mask). *)
Lemma body_ok : forall i, 0 <= i <= 1 -> (i + 1 < 2 -> loop_P (i + 1)) -> loop_P i.
Proof.
  intros i Hi HN. unfold loop_P.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s11 t3 t4 t5 t6 F fc m1 HF MT H4.
  pose proof MT as (_ & _ & MI & ST & _).
  destruct (stk_read rsegs m1 lo (SP + 488) (SP + 232 + 4 * i) 4 ST ltac:(lia) ltac:(lia)) as (bs & HR).
  (* 0x1451c slli s7,s1,2; add s7,s2,s7 *)
  step. step.
  replace (SP + 232 + Z.shiftl (bv_unsigned (Z_to_bv 64 i)) 2) with (SP + 232 + 4 * i)
    by (rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  (* 0x14524 lw s6,0(s7) *)
  step. clear HR.
  (* 0x14528 mv a0,s4; mv a1,s6; mv a2,s10; jal reac_rate_cfg_decide *)
  step. step. step. step.
  eapply evt_cut; [eapply DEC|]. intros ms' (a2x & a3x & ->). ret_even.
  (* 0x14538 mv s5,a0 *)
  step.
  eapply inline_ok; [exact Hi | exact HN | exact HF | exact MT | exact H4 | reflexivity].
Qed.

Lemma loop_ok : loop_P 0.
Proof.
  apply body_ok; [lia|]. intros _. apply body_ok; [lia|]. intros H. lia.
Qed.

(** 0x144f8 .. 0x14518: asked[0] = a2, asked[1] = a0 (any words) into sp + 0xe8 / sp + 0xec; the loop's registers. *)
Lemma asked_ok : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 1) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x144f8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT.
  pose proof MT as (_ & _ & _ & ST & _).
  (* 0x144f8 mv s1,zero; srli s4,a1,63; sw a2,0xe8(sp) *)
  step. step.
  assert (HS : store_ok rsegs m1 (wa (SP + 232)) 4 = true)
    by exact (stk_store_ok rsegs m1 lo (SP + 488) (SP + 232) 4 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 232));
    assert (MT2 : MemT (write_to_mem m1 (wa (SP + 232)) BS))
      by (apply MemT_store; rewrite ?length_le4, ?length_Z_to_le_bytes; [exact MT | exact HS | lia | lia]);
    revert MT2; generalize (write_to_mem m1 (wa (SP + 232)) BS) as m2; intros m2 MT2
  end.
  clear HS ST. pose proof MT2 as (_ & _ & _ & ST2 & _).
  (* 0x14504 sw a0,0xec(sp) *)
  assert (HS : store_ok rsegs m2 (wa (SP + 236)) 4 = true)
    by exact (stk_store_ok rsegs m2 lo (SP + 488) (SP + 236) 4 ST2 ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m2 ?A ?BS) _) =>
    change A with (wa (SP + 236));
    assert (MT3 : MemT (write_to_mem m2 (wa (SP + 236)) BS))
      by (apply MemT_store; rewrite ?length_le4, ?length_Z_to_le_bytes; [exact MT2 | exact HS | lia | lia]);
    revert MT3; generalize (write_to_mem m2 (wa (SP + 236)) BS) as m3; intros m3 MT3
  end.
  clear HS ST2 MT MT2.
  (* 0x14508 addi s2,sp,0xe8; auipc a0; addi s8,a0,0x11c; addi s9,zero,2; ld s10,0x10(sp) *)
  step. step. step. step.
  pose proof MT3 as (_ & _ & _ & _ & _ & H10 & _).
  pose proof (read_le8 rsegs m3 (SP + 16) _ H10) as HR. step. clear HR.
  pose proof (srl63_range a1) as R1.
  eapply loop_ok; [exact HF | exact MT3 | rewrite unsigned_lit by lia; lia].
Qed.

(** 0x144bc .. 0x144f4: asked[] = {rc == 1 ? hz : 48000, other} (any words: the loop needs no value of them), role =
    bit 1 of s2 (`slli a1,s2,62; srli s4,a1,63`, 0 or 1 for any s2), then asked_ok. *)
Lemma tail_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x144bc) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT.
  pose proof MT as (_ & _ & _ & ST & _).
  (* 0x144bc ld a0,0x20(sp); ld a1,0x18(sp); or a0,a1,a0; ld a1,8(sp); ld a2,0x28(sp); or a1,a2,a1 *)
  destruct (stk_read rsegs m1 lo (SP + 488) (SP + 32) 8 ST ltac:(lia) ltac:(lia)) as (b20 & HR). step. clear HR.
  destruct (stk_read rsegs m1 lo (SP + 488) (SP + 24) 8 ST ltac:(lia) ltac:(lia)) as (b18 & HR). step. clear HR.
  step.
  destruct (stk_read rsegs m1 lo (SP + 488) (SP + 8) 8 ST ltac:(lia) ltac:(lia)) as (b08 & HR). step. clear HR.
  destruct (stk_read rsegs m1 lo (SP + 488) (SP + 40) 8 ST ltac:(lia) ltac:(lia)) as (b28 & HR). step. clear HR.
  step.
  (* 0x144d4 addi s0,zero,1; slli a0,a0,16; or a0,a1,a0; slli a1,s2,62; beq s4,s0 *)
  step. step. step. step. step.
  if_cases E.
  - (* 0x144f4 lw a2,0x188(sp) *)
    destruct (stk_read rsegs m1 lo (SP + 488) (SP + 392) 4 ST ltac:(lia) ltac:(lia)) as (bh & HR). step. clear HR.
    eapply asked_ok; [exact HF | exact MT].
  - (* 0x144e8 lui a2,0xc; addi a2,a2,-0x480; j 0x144f8 *)
    step. step. step. eapply asked_ok; [exact HF | exact MT].
Qed.

Hypothesis CKAB : check_absent_contract.
Hypothesis CKR : check_rate_contract.
Hypothesis CKM : check_malformed_contract.

(** 0x143c8 .. 0x143cc: `ld s2,0x38(sp); j 0x144bc`. *)
Lemma reload_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x143c8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT.
  pose proof MT as (_ & _ & _ & ST & _).
  destruct (stk_read rsegs m1 lo (SP + 488) (SP + 56) 8 ST ltac:(lia) ltac:(lia)) as (b38 & HR). step. clear HR.
  step. eapply tail_ok; [exact HF | exact MT].
Qed.

(** 0x143bc .. 0x143c4: check_absent(rc, hz), then reload_ok. *)
Lemma absent_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s4 = 0 -> bytes_at rsegs m1 (SP + 392) (le4 (Z_to_bv 64 0x5a5a5a5a)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x143bc) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT H4 HC.
  pose proof (read_le4_cell rsegs m1 (SP + 392) _ HC) as HR.
  (* 0x143bc lw a1,0x188(sp); mv a0,s4; jal check_absent *)
  step. clear HR. rewrite sx32_small by lia. step. step.
  eapply evt_cut; [eapply CKAB; [exact H4 | apply unsigned_lit; lia]|]. intros ms' ->. ret_even.
  eapply reload_ok; [exact HF | exact MT].
Qed.

(** 0x144b0 .. 0x144b8: check_malformed(rc, hz), returning to 0x144bc. *)
Lemma malformed_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                            (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s4 = 2^64 - 1 -> bytes_at rsegs m1 (SP + 392) (le4 (Z_to_bv 64 0x5a5a5a5a)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x144b0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT H4 HC.
  pose proof (read_le4_cell rsegs m1 (SP + 392) _ HC) as HR.
  (* 0x144b0 lw a1,0x188(sp); mv a0,s4; jal check_malformed *)
  step. clear HR. rewrite sx32_small by lia. step. step.
  eapply evt_cut; [eapply CKM; [exact H4 | apply unsigned_lit; lia]|]. intros ms' ->. ret_even.
  eapply tail_ok; [exact HF | exact MT].
Qed.

(** 0x144ac: `ld s2,0x38(sp)`, then malformed_ok. *)
Lemma malformed_ld : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                            (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bv_unsigned s4 = 2^64 - 1 -> bytes_at rsegs m1 (SP + 392) (le4 (Z_to_bv 64 0x5a5a5a5a)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x144ac) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MT H4 HC.
  pose proof MT as (_ & _ & _ & ST & _).
  destruct (stk_read rsegs m1 lo (SP + 488) (SP + 56) 8 ST ltac:(lia) ltac:(lia)) as (b38 & HR). step. clear HR.
  eapply malformed_ok; [exact HF | exact MT | exact H4 | exact HC].
Qed.

(** 0x1449c .. 0x144a8: check_rate(rc, hz, want) with want = v in a2 and the hz cell = v, then `j 0x143c8`. *)
Lemma rate_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (v : Z),
  frm0 fc -> MemT m1 -> bv_unsigned s4 = 1 -> -2^31 <= v < 2^31 ->
  bytes_at rsegs m1 (SP + 392) (le4 (Z_to_bv 64 v)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1449c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 v HF MT H4 Hv HC.
  pose proof (read_le4_cell rsegs m1 (SP + 392) _ HC) as HR.
  (* 0x1449c lw a1,0x188(sp); mv a0,s4; jal check_rate *)
  step. clear HR. rewrite sx32_int by lia. step. step.
  eapply evt_cut; [eapply CKR; [exact H4 | reflexivity]|]. intros ms' ->. ret_even.
  (* 0x144a8 j 0x143c8 *)
  step. eapply reload_ok; [exact HF | exact MT].
Qed.

(** ** expect_rate over the record in pp *)
Variable r : pod_rec.
Hypothesis HWF : pod_rec_wf r.
Local Abbreviation es := (ents r).
Local Abbreviation n := (length (ents r)).
Local Abbreviation E0 := (expect_model false r).

(** The memory of the scan: MemT, the record at pp, the hz cell (sp + 0x188, 4 bytes), MemNorm.task_mem. *)
Definition MemS (m1 : word -> option byte) (c : Z) : Prop :=
  MemT m1 /\ bytes_at rsegs m1 pp (pp_bytes r) /\ bytes_at rsegs m1 (SP + 392) (le4 (Z_to_bv 64 c)) /\
  MemNorm.task_mem rsegs m1.

Lemma len_pp : Z.of_nat (length (pp_bytes r)) = 19744.
Proof. exact (length_pp_bytes r HWF). Qed.

(** A store into the frame's locals at or above sp + 0xe0, off the hz cell. *)
Lemma MemS_store : forall m1 c a bs, MemS m1 c -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP + 224 <= a -> a + Z.of_nat (length bs) <= SP + 488 ->
  or_h (a + Z.of_nat (length bs) <= SP + 392) (SP + 396 <= a) ->
  MemS (write_to_mem m1 (wa a) bs) c.
Proof.
  intros m1 c a bs (MT & HP & HC & TM) HS H1 H2 D3. unfold or_h in *.
  pose proof len_pp as LP.
  split; [exact (MemT_store m1 a bs MT HS H1 H2)|].
  split; [apply bytes_at_write_other; [exact HP | lia | lia | lia]|].
  split; [apply bytes_at_write_other; [exact HC | lia | lia | rewrite length_le4; lia]|].
  exact (task_mem_write_u m1 (wa a) bs TM HS).
Qed.

Lemma rate_key_at : forall m1, mem_inv rsegs m1 -> bytes_at rsegs m1 0x1045e (RATE_KEY ++ [Z_to_bv 8 0]).
Proof.
  intros m1 MI.
  assert (RO : ro_cells rsegs m1 0x1045e [CB (length (RATE_KEY ++ [Z_to_bv 8 0])) (RATE_KEY ++ [Z_to_bv 8 0])]).
  { apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | vm_compute; congruence]. }
  destruct RO as [_ RB]. cbn [cells_bytes cbytes] in RB. rewrite app_nil_r in RB. exact RB.
Qed.

Lemma rate_key_no_nul : ~ In (Z_to_bv 8 0) RATE_KEY.
Proof.
  intros H. assert (F : forallb (fun b : byte => negb (bv_unsigned b =? 0)) RATE_KEY = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. specialize (F _ H). revert F. vm_compute. intros F. discriminate F.
Qed.

Hypothesis STRC : strcmp_contract.
Hypothesis NEAR : pod_nearest_contract.

(** 0x14470 .. 0x14498: pod_float, pod_nearest(f, INT_MIN, INT_MAX, sp + 0xe8), the low word of its answer. *)
Lemma float_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (i : nat),
  frm0 fc -> MemS m1 (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  (i < n)%nat -> E0 = expect_value (nth i es (Ent 0 0 [])) -> e_type (nth i es (Ent 0 0 [])) = POD_FLOAT ->
  s1 = Z_to_bv 64 (pp + 16404 + 104 * Z.of_nat i) -> s2 = Z_to_bv 64 (104 * Z.of_nat i) -> a2 = Z_to_bv 64 pp ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x14470) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 i HF MS1 H4 Hi HV Ht
    -> -> ->.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof (ent_wf_nth r i HWF Hi) as (Ht0 & Hb & Hsz).
  pose proof MS1 as (MT & HPPB & HC & TM). pose proof MT as (MU & WM & MI & ST & TB & H10 & H30 & HD8).
  pose proof (bytes_at_ent rsegs m1 pp r i HPPB HWF Hi) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat i) with (pp + 16404 + 104 * Z.of_nat i) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  rewrite HV, (ev_float _ Ht) in H4, HC.
  (* 0x14470 lw a0,4(s1); addi a1,zero,4; bltu a0,a1 *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size (nth i es (Ent 0 0 []))) 4) as [Es|Es]; cbv beta iota.
  { rewrite (proj2 (Z.leb_gt 4 _) Es) in H4, HC. cbn [fst snd written_or] in H4, HC.
    eapply malformed_ld; [exact HF | exact MT | rewrite H4; reflexivity | exact HC]. }
  rewrite (proj2 (Z.leb_le 4 _) Es) in H4, HC.
  (* 0x1447c add s2,a2,s2; lui a0,4; add a0,s2,a0; flw fa0,0x1c(a0); addi a0,sp,0xe8; jal pod_nearest *)
  step. step. step.
  pose proof (ent_word_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR.
  rewrite extract_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn.
  step. step.
  eapply evt_cut.
  { eapply NEAR with (lo := lo) (b := rd32 (e_body (nth i es (Ent 0 0 [])))).
    - apply rd32_range.
    - apply freg_get_same. reflexivity.
    - rewrite unsigned_lit by lia. apply (stk_wr_at rsegs m1 lo (SP + 488)); [exact ST | lia | lia | lia].
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
  revert H4 HC PNM. change NEAR_LO with INT32_MIN. change NEAR_HI with INT32_MAX.
  destruct (nearest (rd32 (e_body (nth i es (Ent 0 0 [])))) INT32_MIN INT32_MAX) as [w|] eqn:EN; intros H4 HC PNM;
    cbn [pod_near_mem pod_near_rc] in PNM |- *; cbn [fst snd written_or] in H4, HC.
  - (* a nearest integer w: 0x14494 beqz a0 not taken; 0x14498 lw a2,0xe8(sp) *)
    destruct PNM as (MU2 & HW).
    assert (MT2 : MemT m2).
    { apply (MemT_call m1 m2 _ MT MU2 WM2 MI2 ST2).
      - unfold sub_fp, WC, POD_NEAREST_STACK. cbn [outside]. intros x (O1 & _ & _). repeat split; try exact I; lia.
      - intros x Hx. unfold POD_NEAREST_STACK. cbn [outside]. repeat split; try exact I; lia.
      - intros x Hx. unfold POD_NEAREST_STACK.
        destruct (Z_lt_le_dec x (SP + 232)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; lia|].
        destruct (Z_lt_le_dec x (SP + 240)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; lia].
        apply (bytes_at_some rsegs m2 (SP + 232) _ x HW); rewrite length_le8; [intros a Ha; apply HROM | ]; lia. }
    assert (HC2 : bytes_at rsegs m2 (SP + 392) (le4 (Z_to_bv 64 w))).
    { apply (bytes_at_transport rsegs _ m1 m2 _ _ HC MU2). cbn [disjoint_from]. rewrite length_le4.
      unfold POD_NEAREST_STACK. repeat split; lia. }
    step. if_false.
    pose proof (read_le4_cell rsegs m2 (SP + 232) _ (bytes_at_le8_le4 rsegs m2 (SP + 232) _ HW)) as HR.
    step. clear HR.
    pose proof (nearest_range _ _ EN) as Hw. unfold INT32_MIN, INT32_MAX in Hw.
    rewrite sx32_int by lia.
    eapply rate_ok; [exact HF' | exact MT2 | rewrite H4; reflexivity | lia | exact HC2].
  - (* none: 0x14494 beqz a0 to 0x144ac *)
    assert (MT2 : MemT m2)
      by (apply (MemT_below m1 m2 POD_NEAREST_STACK MT PNM WM2 MI2 ST2); unfold POD_NEAREST_STACK; lia).
    assert (HC2 : bytes_at rsegs m2 (SP + 392) (le4 (Z_to_bv 64 0x5a5a5a5a))).
    { apply (bytes_at_transport rsegs _ m1 m2 _ _ HC PNM). cbn [disjoint_from]. rewrite length_le4.
      unfold POD_NEAREST_STACK. repeat split; lia. }
    step. if_true.
    eapply malformed_ld; [exact HF' | exact MT2 | rewrite H4; reflexivity | exact HC2].
Qed.

(** 0x14378 .. 0x143b8: the value ent[v] of the rate key: the bound and overflow checks, pod_int, else pod_float. *)
Lemma value_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (v : nat),
  frm0 fc -> MemS m1 (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  (v < n)%nat -> E0 = expect_value (nth v es (Ent 0 0 [])) ->
  s11 = Z_to_bv 64 (Z.of_nat v) -> s2 = Z_to_bv 64 (104 * Z.of_nat v) -> s1 = Z_to_bv 64 (pp + 16404) ->
  bv_unsigned s7 = 2^64 - 1 - (pp + 16404) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x14378) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 v HF MS1 H4 Hv HV
    -> -> -> H7.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof (ent_wf_nth r v HWF Hv) as (Ht0 & Hb & Hsz).
  pose proof MS1 as (MT & HPPB & HC & TM). pose proof MT as (MU & WM & MI & ST & TB & H10 & H30 & HD8).
  pose proof (bytes_at_ent rsegs m1 pp r v HPPB HWF Hv) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat v) with (pp + 16404 + 104 * Z.of_nat v) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  (* 0x14378 addi a0,zero,33; bgeu s11,a0: the bound of ent[v] *)
  step. step. rewrite ltu_u by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [negb]. cbv beta iota.
  (* 0x14380 ld a2,0xd8(sp) *)
  pose proof (read_le8 rsegs m1 (SP + 216) _ HD8) as HR. step. clear HR.
  (* 0x14384 bltu s7,s2: ent + 104 v does not wrap *)
  step. unfold bv_ltu at 1. rewrite H7, (unsigned_lit (104 * Z.of_nat v)) by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x14388 add s1,s1,s2; lw a0,0(s1); addi a1,zero,6; beq a0,a1 *)
  step.
  pose proof (ent_type_read rsegs m1 _ _ HEB Ht0) as HR. step. clear HR.
  step. step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth v es (Ent 0 0 []))) 6) as [Et|Et]; cbv beta iota.
  { eapply float_ok; [exact HF | exact MS1 | exact H4 | exact Hv | exact HV | exact Et | weq | weq | weq]. }
  (* 0x14398 addi a1,zero,4; bne a0,a1 *)
  step. step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth v es (Ent 0 0 []))) 4) as [Et4|Et4]; cbn [negb]; cbv beta iota.
  2:{ assert (EV : E0 = (None, -1)) by (rewrite HV; apply ev_other; unfold POD_FLOAT, POD_INT; lia).
      rewrite EV in H4, HC. cbn [fst snd written_or] in H4, HC.
      eapply malformed_ld; [exact HF | exact MT | rewrite H4; reflexivity | exact HC]. }
  (* 0x143a0 lw a0,4(s1); bltu a0,a1 *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size (nth v es (Ent 0 0 []))) 4) as [Es|Es]; cbv beta iota.
  { assert (EV : E0 = (None, -1)) by (rewrite HV, ev_int by exact Et4; rewrite (proj2 (Z.leb_gt 4 _) Es); reflexivity).
    rewrite EV in H4, HC. cbn [fst snd written_or] in H4, HC.
    eapply malformed_ld; [exact HF | exact MT | rewrite H4; reflexivity | exact HC]. }
  (* 0x143a8 add s2,a2,s2; lui a0,4; add a0,s2,a0; lw a2,0x1c(a0); j 0x1449c *)
  step. step. step.
  pose proof (ent_word_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR.
  rewrite sext_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn. step.
  assert (EV : E0 = (Some (s32 (rd32 (e_body (nth v es (Ent 0 0 []))))), 1))
    by (rewrite HV, ev_int by exact Et4; rewrite (proj2 (Z.leb_le 4 _) Es); reflexivity).
  rewrite EV in H4, HC. cbn [fst snd written_or] in H4, HC.
  pose proof (s32_range _ (rd32_range (e_body (nth v es (Ent 0 0 []))))) as Hw.
  eapply rate_ok; [exact HF | exact MT | rewrite H4; reflexivity | lia | exact HC].
Qed.

(** ** pod_next_pair's scan (0x142b4 .. 0x14378), by induction on the entries left *)
Definition outer_P (j : nat) : Prop :=
  forall (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS m1 (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  E0 = rate_of_pairs expect_value (pairs_by key_of (skipn j es) None) -> (j <= n)%nat ->
  a5 = Z_to_bv 64 (Z.of_nat j) -> bv_unsigned s7 = 2^64 - 1 - (pp + 16404) -> bv_unsigned s10 = 2^64 - (pp + 16413) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (pp + 16404)) a0 (Z_to_bv 64 0x1045e) a2 a3
             a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 (Z_to_bv 64 8) s7 (Z_to_bv 64 446676598784) (Z_to_bv 64 (pp + 16412))
             s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x142b4) fc None m1 (seg_rom rsegs)).

(** At 0x142dc with the key slot empty (a0 = NULL) and the scan at entry j. *)
Definition inner_none_P (j : nat) : Prop :=
  forall (ra t0 t1 t2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS m1 (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  E0 = rate_of_pairs expect_value (pairs_by key_of (skipn j es) None) -> (j < n)%nat ->
  a5 = Z_to_bv 64 (Z.of_nat j) -> s11 = Z_to_bv 64 (Z.of_nat j) -> s2 = Z_to_bv 64 (104 * Z.of_nat j) ->
  bv_unsigned a3 = 2^64 - (pp + 16413 + 104 * Z.of_nat j) ->
  bv_unsigned s7 = 2^64 - 1 - (pp + 16404) -> bv_unsigned s10 = 2^64 - (pp + 16413) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (pp + 16404)) (Z_to_bv 64 0)
             (Z_to_bv 64 0x1045e) (Z_to_bv 64 33) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 (Z_to_bv 64 8) s7
             (Z_to_bv 64 446676598784) (Z_to_bv 64 (pp + 16412)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x142dc) fc None m1
        (seg_rom rsegs)).

(** At 0x142dc with the key k at ka in the slot: entry j is its value. *)
Definition inner_some_P (j : nat) (k : list byte) (ka : Z) : Prop :=
  forall (ra t0 t1 t2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS m1 (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  E0 = rate_of_pairs expect_value (pairs_by key_of (skipn j es) (Some k)) -> (j < n)%nat ->
  0 < ka -> bytes_at rsegs m1 ka (k ++ [Z_to_bv 8 0]) -> ka + Z.of_nat (length (k ++ [Z_to_bv 8 0])) <= lo ->
  ~ In (Z_to_bv 8 0) k ->
  a5 = Z_to_bv 64 (Z.of_nat j) -> s11 = Z_to_bv 64 (Z.of_nat j) -> s2 = Z_to_bv 64 (104 * Z.of_nat j) ->
  bv_unsigned a3 = 2^64 - (pp + 16413 + 104 * Z.of_nat j) ->
  bv_unsigned s7 = 2^64 - 1 - (pp + 16404) -> bv_unsigned s10 = 2^64 - (pp + 16413) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (pp + 16404)) (Z_to_bv 64 ka)
             (Z_to_bv 64 0x1045e) (Z_to_bv 64 33) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 (Z_to_bv 64 8) s7
             (Z_to_bv 64 446676598784) (Z_to_bv 64 (pp + 16412)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x142dc) fc None m1
        (seg_rom rsegs)).

(** The key slot after entry j: empty, or the key k at ka. *)
Definition slot_ok (m1 : word -> option byte) (ko : option (list byte)) (ka : Z) : Prop :=
  match ko with
  | Some k => 0 < ka /\ bytes_at rsegs m1 ka (k ++ [Z_to_bv 8 0]) /\
              ka + Z.of_nat (length (k ++ [Z_to_bv 8 0])) <= lo /\ ~ In (Z_to_bv 8 0) k
  | None => True
  end.

(** 0x142b4 .. 0x142d8: `at < n_ent`, else no pair is left; the bound 33 of ent[*at], ent + 104 at, k = NULL. *)
Lemma outer_ok : forall j, ((j < n)%nat -> inner_none_P j) -> outer_P j.
Proof.
  intros j HI. unfold outer_P.
  intros ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s10 s11 t3 t4 t5 t6 F fc m1 HF MS1 H4 HE Hj -> H7 H10.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  (* 0x142b4 bge a5,s0 *)
  step. rewrite lts_s by lia.
  destruct (Z.ltb_spec (Z.of_nat j) (Z.of_nat n)) as [Hl|Hl]; cbn [negb]; cbv beta iota.
  2:{ assert (EA : E0 = (None, 0)) by (rewrite HE, skipn_all2 by lia; reflexivity).
      pose proof MS1 as (MT & _ & HC & _). rewrite EA in H4, HC. cbn [fst snd written_or] in H4, HC.
      eapply absent_ok; [exact HF | exact MT | rewrite H4; reflexivity | exact HC]. }
  (* 0x142b8 slli a3,a5,32; srli s11,a3,32; addi a0,zero,33; mv a2,s11; bltu a0,s11 *)
  step. step. rewrite zext32_small by lia. step. step. step. rewrite ltu_u by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x142cc addi a2,zero,33; mv a0,zero; mulhu s2,a3,s8; sub a3,s10,s2 *)
  step. step. step. rewrite mulhu_idx by lia. step.
  eapply (HI ltac:(lia)); [exact HF | exact MS1 | exact H4 | exact HE | lia | weq | weq | weq | | exact H7 | exact H10].
  rewrite (unsigned_lit (104 * Z.of_nat j)) by lia. apply (unsigned_sub_bound s10 (pp + 16413)); [exact H10 | lia | lia | lia].
Qed.

(** 0x14330 .. 0x14344: the next entry, or no pair is left. *)
Lemma next_ent_ok : forall j, (j < n)%nat ->
  ((S j < n)%nat -> inner_none_P (S j) /\ (forall k ka, inner_some_P (S j) k ka)) ->
  forall (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 s2 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (ko : option (list byte)) (ka : Z),
  frm0 fc -> MemS m1 (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  E0 = rate_of_pairs expect_value (pairs_by key_of (skipn (S j) es) ko) -> slot_ok m1 ko ka ->
  a0 = Z_to_bv 64 (match ko with Some _ => ka | None => 0 end) ->
  a5 = Z_to_bv 64 (Z.of_nat j) -> s11 = Z_to_bv 64 (Z.of_nat j) -> s2 = Z_to_bv 64 (104 * Z.of_nat j) ->
  bv_unsigned a3 = 2^64 - (pp + 16413 + 104 * Z.of_nat j) ->
  bv_unsigned s7 = 2^64 - 1 - (pp + 16404) -> bv_unsigned s10 = 2^64 - (pp + 16413) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (pp + 16404)) a0 (Z_to_bv 64 0x1045e)
             (Z_to_bv 64 33) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 (Z_to_bv 64 8) s7
             (Z_to_bv 64 446676598784) (Z_to_bv 64 (pp + 16412)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14330) fc None m1
        (seg_rom rsegs)).
Proof.
  intros j Hj HI ra t0 t1 t2 a0 a3 a4 a5 a6 a7 s2 s4 s5 s7 s10 s11 t3 t4 t5 t6 F fc m1 ko ka HF MS1 H4 HE HS -> -> -> ->
    H3 H7 H10.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  (* 0x14330 addi s11,s11,1; addi s2,s2,0x68; addiw a5,a5,1; addi a3,a3,-0x68; bltu s11,s0 *)
  step. step. step. step. step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (Z.of_nat j + 1) (Z.of_nat n)) as [Hl|Hl]; cbv beta iota.
  - assert (A3 : bv_unsigned (Z_to_bv 64 (bv_unsigned a3 + -104)) = 2^64 - (pp + 16413 + 104 * Z.of_nat (S j))).
    { rewrite H3. rewrite unsigned_lit by lia. lia. }
    destruct (HI ltac:(lia)) as [HN HSm]. destruct ko as [k|].
    + destruct HS as (Hka & HK & HKl & HNK).
      eapply (HSm k ka); [exact HF | exact MS1 | exact H4 | exact HE | lia | exact Hka | exact HK | exact HKl | exact HNK
                         | weq | weq | weq | exact A3 | exact H7 | exact H10].
    + eapply HN; [exact HF | exact MS1 | exact H4 | exact HE | lia | weq | weq | weq | exact A3 | exact H7 | exact H10].
  - (* 0x14344 j 0x143bc: no pair is left *)
    step.
    assert (EA : E0 = (None, 0)) by (rewrite HE, skipn_all2 by lia; destruct ko; reflexivity).
    pose proof MS1 as (MT & _ & HC & _). rewrite EA in H4, HC. cbn [fst snd written_or] in H4, HC.
    eapply absent_ok; [exact HF | exact MT | rewrite H4; reflexivity | exact HC].
Qed.

(** 0x142dc .. 0x1432c: pod_string(&pp->ent[j]) on an empty key slot, with the bound of ent[*at] and the overflow
    checks of ent + 104 j and body + size - 1. *)
Lemma none_ok : forall j, ((S j < n)%nat -> inner_none_P (S j) /\ (forall k ka, inner_some_P (S j) k ka)) ->
  inner_none_P j.
Proof.
  intros j HI. unfold inner_none_P.
  intros ra t0 t1 t2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s10 s11 t3 t4 t5 t6 F fc m1 HF MS1 H4 HE Hj -> -> -> H3 H7 H10.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  rewrite (skipn_nth_cons es j (Ent 0 0 []) Hj), rop_cons in HE.
  pose proof (ent_wf_nth r j HWF Hj) as (Ht0 & Hb & Hsz).
  pose proof MS1 as (MT & HPPB & HC & TM).
  pose proof (bytes_at_ent rsegs m1 pp r j HPPB HWF Hj) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat j) with (pp + 16404 + 104 * Z.of_nat j) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  (* 0x142dc bnez a0; beq a2,s11; bltu s7,s2 *)
  step. if_false.
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  step. unfold bv_ltu at 1. rewrite H7, (unsigned_lit (104 * Z.of_nat j)) by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x142e8 add a0,s1,s2; lw a4,0(a0); bne a4,s6 *)
  step. pose proof (ent_type_read rsegs m1 _ _ HEB Ht0) as HR. step. clear HR.
  step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth j es (Ent 0 0 []))) 8) as [Et|Et]; cbn [negb]; cbv beta iota.
  2:{ (* not a String: 0x1432c mv a0,zero *)
      assert (EK : key_of (nth j es (Ent 0 0 [])) = None)
        by (rewrite key_of_cases; unfold POD_STRING; rewrite (proj2 (Z.eqb_neq _ _) Et); reflexivity).
      rewrite EK in HE. step.
      eapply (next_ent_ok j Hj HI) with (ko := None) (ka := 0);
        [exact HF | exact MS1 | exact H4 | exact HE | exact I | reflexivity | reflexivity | reflexivity | reflexivity
        | exact H3 | exact H7 | exact H10]. }
  (* 0x142f4 lw a0,4(a0); beqz a0 *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec (e_size (nth j es (Ent 0 0 []))) 0) as [Ez|Ez]; cbv beta iota.
  { assert (EK : key_of (nth j es (Ent 0 0 [])) = None)
      by (rewrite key_of_cases; rewrite Ez; cbn [Z.leb Z.compare]; rewrite andb_false_r; reflexivity).
    rewrite EK in HE.
    eapply (next_ent_ok j Hj HI) with (ko := None) (ka := 0);
      [exact HF | exact MS1 | exact H4 | exact HE | exact I | rewrite Ez; reflexivity | reflexivity | reflexivity
      | reflexivity | exact H3 | exact H7 | exact H10]. }
  (* 0x142fc addi a0,a0,-1; slli a0,a0,32; srli a0,a0,32; bltu a3,a0 *)
  step. step. step. rewrite zext32_small by lia.
  step. unfold bv_ltu at 1. rewrite H3, (unsigned_lit (e_size (nth j es (Ent 0 0 [])) + -1)) by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x1430c add a0,s2,a0; add a0,s9,a0; lbu a0,0(a0) *)
  step. step.
  pose proof (ent_byte_read rsegs m1 _ _ (Z.to_nat (e_size (nth j es (Ent 0 0 [])) - 1)) HEB ltac:(lia)) as HR.
  step. clear HR.
  (* 0x14318 add a4,s9,s2; snez a0,a0; addi a0,a0,-1; and a0,a0,a4; j 0x14330 *)
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
    eapply (next_ent_ok j Hj HI) with (ko := Some (cstr (e_body (nth j es (Ent 0 0 []))))) (ka := pp + 16412 + 104 * Z.of_nat j);
      [exact HF | exact MS1 | exact H4 | exact HE | | reflexivity | reflexivity | reflexivity | reflexivity
      | exact H3 | exact H7 | exact H10].
    cbn [slot_ok]. split; [lia|]. split; [exact HKB|]. split; [lia | apply cstr_no_nul].
  - (* not NUL-terminated *)
    assert (EK : key_of (nth j es (Ent 0 0 [])) = None).
    { rewrite key_of_cases. unfold last_body_byte. rewrite (proj2 (Z.eqb_neq _ _) Eb). rewrite andb_false_r. reflexivity. }
    rewrite EK in HE.
    eapply (next_ent_ok j Hj HI) with (ko := None) (ka := 0);
      [exact HF | exact MS1 | exact H4 | exact HE | exact I | reflexivity | reflexivity | reflexivity | reflexivity
      | exact H3 | exact H7 | exact H10].
Qed.

(** 0x142dc, 0x14348 .. 0x14374: the key k in the slot: v = j; strcmp(k, "reac.cfg.rate") with s10 spilled at
    sp + 0xe0. *)
Lemma some_ok : forall j, ((S j < n)%nat -> inner_none_P (S j)) -> forall k ka, inner_some_P j k ka.
Proof.
  intros j HI k ka. unfold inner_some_P.
  intros ra t0 t1 t2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s10 s11 t3 t4 t5 t6 F fc m1 HF MS1 H4 HE Hj Hka HK HKl HNK -> -> -> H3 H7
    H10.
  pose proof (proj1 (ents_wf r HWF)) as Hn. pose proof (bytes_at_bound rsegs m1 ka _ HK) as (KB0 & KB1).
  pose proof MS1 as (MT & HPPB & HC & TM). pose proof MT as (_ & _ & MI & ST & _).
  (* 0x142dc bnez a0 taken *)
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbn [negb]. cbv beta iota.
  (* 0x14348 addiw s5,a5,1; blt s5,a5; bltz a5 *)
  step. rewrite addiw1_small by lia.
  step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x14354 sd s10,0xe0(sp) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 224)) 8 = true)
    by exact (stk_store_ok rsegs m1 lo (SP + 488) (SP + 224) 8 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 224));
    assert (MS2 : MemS (write_to_mem m1 (wa (SP + 224)) BS) (written_or 0x5a5a5a5a E0))
      by (apply MemS_store; unfold or_h; rewrite ?length_le8; [exact MS1 | exact HS | lia | lia | lia]);
    assert (HK2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 224)) BS) ka (k ++ [Z_to_bv 8 0]))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact HK | lia | lia | lia]);
    assert (HSP : bytes_at rsegs (write_to_mem m1 (wa (SP + 224)) BS) (SP + 224) BS)
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    revert MS2 HK2 HSP; generalize (write_to_mem m1 (wa (SP + 224)) BS) as m2; intros m2 MS2 HK2 HSP
  end.
  clear HS HK MT HPPB HC TM MI ST.
  pose proof MS2 as (MT & HPPB & HC & TM). pose proof MT as (_ & _ & MI & ST & _).
  (* 0x14358 mv s10,s8; mv s8,a1; jal strcmp *)
  step. step. step.
  eapply evt_cut.
  { eapply STRC with (sx := k) (sy := RATE_KEY).
    - rewrite unsigned_lit by lia. exact HK2.
    - exact HNK.
    - change (bv_unsigned (Z_to_bv 64 0x1045e)) with 0x1045e. exact (rate_key_at m2 MI).
    - exact rate_key_no_nul. }
  intros ms' (rr & x11 & x12 & x13 & E & Hr). subst ms'. ret_even.
  (* 0x14364 mv a1,s8; mv s8,s10; ld s10,0xe0(sp); mv a5,s5; bnez a0 *)
  step. step. pose proof (read_le8 rsegs m2 (SP + 224) _ HSP) as HR. step. clear HR. step.
  rewrite (skipn_nth_cons es j (Ent 0 0 []) Hj), rop_some in HE.
  revert HE. destruct (bytes_eqb k RATE_KEY) eqn:EK; intros HE.
  - (* the rate key: 0x14378 *)
    apply bytes_eqb_eq in EK. rewrite (proj2 Hr EK).
    step. if_false.
    eapply value_ok with (v := j); [exact HF | exact MS2 | exact H4 | exact Hj | exact HE | weq | weq | weq | exact H7].
  - (* another key: back to the outer loop with at = j + 1 *)
    assert (Hrr : bv_eqb rr (Z_to_bv 64 0) = false).
    { destruct (bv_eqb rr (Z_to_bv 64 0)) eqn:X; [|reflexivity]. apply bv_eqb_true in X. apply Hr in X. subst k.
      rewrite (proj2 (bytes_eqb_eq RATE_KEY RATE_KEY) eq_refl) in EK. discriminate. }
    step. rewrite Hrr. cbn [negb]. cbv beta iota.
    eapply (outer_ok (S j) HI); [exact HF | exact MS2 | exact H4 | exact HE | lia | weq | exact H7 | exact H10].
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
Hypothesis HPM : corrupt r = false -> parse_model (buf r) = expect_model false r.

(** The memory before the scan's set-up: MemS and the cell sp + 0x98 = &pp->n_ent. *)
Definition MemP (m1 : word -> option byte) (c : Z) : Prop :=
  MemS m1 c /\ bytes_at rsegs m1 (SP + 152) (le8 (Z_to_bv 64 (pp + 19732))).

Lemma len_buf : 8 <= len <= 5440.
Proof. destruct (buf_header r HWF) as (_ & _ & _ & H). lia. Qed.

(** 0x1426c .. 0x142b0: at = 0, n = n_ent, the constants and the overflow bounds of the scan. *)
Lemma setup_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS m1 (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  is_props r = true -> params_struct r = true ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (pp + 19732)) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6
             s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1426c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MS1 H4 EI EP.
  pose proof (proj1 (ents_wf r HWF)) as Hn. pose proof len_pp as LP.
  pose proof MS1 as (MT & HPPB & HC & TM). pose proof MT as (_ & _ & _ & _ & _ & _ & _ & HD8).
  (* 0x1426c mv a5,zero; lui a0,4; lw s0,0(a2) *)
  step. step.
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 19732)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (ents r)))))).
  { apply (read_field rsegs m1 pp r 19732 _ HPPB HWF); [exact (pp_n_ent r HWF) | lia | unfold PP_SIZE; lia | lia]. }
  step. clear HR. rewrite sx32_small by lia.
  (* 0x14278 lui a2,0xffffc; addi s8,zero,13; addi s6,zero,8; auipc a3,0xffffc; addiw s1,a0,0x14; addiw a0,a0,0x1c;
     addiw a2,a2,3; slli s8,s8,35 *)
  step. step. step. step. step. step. step. step.
  (* 0x14298 ld a4,0xd8(sp) *)
  pose proof (read_le8 rsegs m1 (SP + 216) _ HD8) as HR. step. clear HR.
  (* 0x1429c add s1,a4,s1; add s9,a4,a0; sub s10,a2,a4; not s7,s1; addi s10,s10,-32; addi a1,a3,0x1da *)
  step. step. step. step. step. step.
  eapply (outer_ok 0).
  - intros Hl. exact (proj1 (scan_ok (length (ents r)) 0 ltac:(lia))).
  - exact HF.
  - exact MS1.
  - exact H4.
  - exact (expect_struct r EI EP).
  - lia.
  - weq.
  - rewrite (unsigned_lit (pp + 16404)) by lia. rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia. lia.
  - rewrite (unsigned_lit pp) by lia. rewrite unsigned_lit by lia. lia.
Qed.

(** 0x14248 .. 0x14268: corrupt, the NULL flag, is_props, params_struct. *)
Lemma after_parse : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s4 s5 s6 s7 s9 s10 t3 t4 t5 t6 : word)
                           (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemP m1 (written_or 0x5a5a5a5a (harness_parse (Z.testbit fl 0) (buf r))) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fl)) 1)) s1
             (Z_to_bv 64 (snd (harness_parse (Z.testbit fl 0) (buf r)))) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 fl)
             (Z_to_bv 64 pod) s4 s5 s6 s7 (Z_to_bv 64 pp) s9 s10 (Z_to_bv 64 (pp + 16384)) t3 t4 t5 t6) F
        (Z_to_bv 64 0x14248) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s4 s5 s6 s7 s9 s10 t3 t4 t5 t6 F fc m1 HF (MS1 & H98).
  pose proof len_pp as LP.
  pose proof MS1 as (MT & HPPB & HC & TM).
  (* 0x14248 ld a2,0x98(sp); lw a1,4(a2); mv s4,a0; bnez a1 *)
  pose proof (read_le8 rsegs m1 (SP + 152) _ H98) as HR. step. clear HR.
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 19736)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (corrupt r))))).
  { apply (read_field rsegs m1 pp r 19736 _ HPPB HWF);
      [exact (pp_corrupt r HWF) | lia | unfold PP_SIZE; lia | destruct (corrupt r); cbn; lia]. }
  revert HR. destruct (corrupt r) eqn:EC; cbn [Z.b2z]; intros HR.
  { step. clear HR. rewrite sx32_small by lia. step. step. if_true. eapply tail_ok; [exact HF | exact MT]. }
  step. clear HR. rewrite sx32_small by lia. step. step. if_false.
  (* 0x14258 bnez s0 *)
  step. rewrite (unsigned_lit fl) by lia. rewrite (land1_bit fl HFL).
  revert MS1 HC. destruct (Z.testbit fl 0) eqn:EB; intros MS1 HC; cbv beta iota.
  { (* the NULL argument: check_malformed *)
    if_true. cbn [harness_parse fst snd written_or] in HC |- *.
    eapply malformed_ok; [exact HF | exact MT | reflexivity | exact HC]. }
  if_false. change (harness_parse false (buf r)) with (parse_model (buf r)) in MS1, HC |- *.
  rewrite HPM in MS1, HC |- * by first [exact EC | reflexivity].
  (* 0x1425c lw a0,8(s11); beqz a0 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 16392)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (is_props r))))).
  { apply (read_field rsegs m1 pp r 16392 _ HPPB HWF);
      [exact (pp_is_props r HWF) | lia | unfold PP_SIZE; lia | destruct (is_props r); cbn; lia]. }
  revert HR. destruct (is_props r) eqn:EI; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      rewrite (expect_not_props r EI) in HC |- *. cbn [fst snd written_or] in HC |- *.
      eapply malformed_ok; [exact HF | exact MT | reflexivity | exact HC]. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  (* 0x14264 lw a0,0x10(s11); beqz a0 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 16400)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (params_struct r))))).
  { apply (read_field rsegs m1 pp r 16400 _ HPPB HWF);
      [exact (pp_params_struct r HWF) | lia | unfold PP_SIZE; lia | destruct (params_struct r); cbn; lia]. }
  revert HR. destruct (params_struct r) eqn:EP; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      rewrite (expect_no_struct r EI EP) in HC |- *. cbn [fst snd written_or] in HC |- *.
      eapply absent_ok; [exact HF | exact MT | reflexivity | exact HC]. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  eapply setup_ok; [exact HF | exact MS1 | apply unsigned_lit_wrap | exact EI | exact EP].
Qed.

Hypothesis MCPY : memcpy_contract.
Hypothesis PARSE : rate_prop_parse_contract.

(** The parse's memory: its frame, and the hz cell when it writes a value. *)
Lemma MemP_parse : forall m2 m3 a, MemP m2 0x5a5a5a5a -> rate_mem m2 m3 SP (SP + 392) (fst a) -> wmono rsegs m2 m3 ->
  mem_inv rsegs m3 -> stk rsegs m3 lo SP -> MemP m3 (written_or 0x5a5a5a5a a).
Proof.
  intros m2 m3 [o rc] ((MT & HPPB & HC & TM) & H98) RM WM3 MI3 ST3. pose proof len_pp as LP.
  pose proof MT as (_ & _ & _ & ST & _).
  destruct o as [w|]; cbn [rate_mem written_or fst] in RM |- *.
  - destruct RM as (MU3 & HW). unfold PARSE_FRAME in MU3.
    split; [split|].
    { apply (MemT_call m2 m3 _ MT MU3 WM3 MI3 ST3).
      - unfold sub_fp, WC. cbn [outside]. intros x (O1 & _ & _). repeat split; try exact I; lia.
      - intros x Hx. cbn [outside]. repeat split; try exact I; lia.
      - intros x Hx. destruct (Z_lt_le_dec x (SP + 392)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; lia|].
        destruct (Z_lt_le_dec x (SP + 396)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; lia].
        apply (bytes_at_some rsegs m3 (SP + 392) _ x HW); rewrite length_le4; [intros a Ha; apply HROM | ]; lia. }
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HPPB MU3); cbn [disjoint_from]; repeat split; lia|].
    split; [exact HW|].
    { apply (task_mem_munch_u _ m2 m3 TM MU3). apply (stk_wview rsegs m2 lo (SP + 488)); [exact ST|].
      intros x Hx. cbn [outside] in Hx. lia. }
    apply (bytes_at_transport rsegs _ m2 m3 _ _ H98 MU3). cbn [disjoint_from]. rewrite length_le8. repeat split; lia.
  - unfold PARSE_FRAME in RM.
    split; [split|].
    { apply (MemT_below m2 m3 80 MT RM WM3 MI3 ST3). lia. }
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HPPB RM); cbn [disjoint_from]; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HC RM); cbn [disjoint_from]; rewrite length_le4; repeat split; lia|].
    { apply (task_mem_munch_u _ m2 m3 TM RM). apply (stk_wview rsegs m2 lo (SP + 488)); [exact ST|].
      intros x Hx. cbn [outside] in Hx. lia. }
    apply (bytes_at_transport rsegs _ m2 m3 _ _ H98 RM). cbn [disjoint_from]. rewrite length_le8. repeat split; lia.
Qed.

(** 0x14228 .. 0x14244: hz := 0x5a5a5a5a, rc = reac_rate_prop_parse(fl & 1 ? NULL : pod, &hz). *)
Lemma after_cpy : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s9 s10 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bytes_at rsegs m1 pp (pp_bytes r) ->
  bytes_at rsegs m1 (SP + 152) (le8 (Z_to_bv 64 (pp + 19732))) ->
  MemNorm.task_mem rsegs m1 -> bytes_at rsegs m1 pod (buf r) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 fl) (Z_to_bv 64 pod) s4 s5 s6 s7
             (Z_to_bv 64 pp) s9 s10
             (Z_to_bv 64 (pp + 16384)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14228) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s9 s10 t3 t4 t5 t6 F fc m1 HF MT HPPB H98 TM HPB.
  pose proof len_pp as LP. pose proof len_buf as LB. pose proof (buf_header r HWF) as (_ & _ & HU & _).
  pose proof MT as (MU & WM & MI & ST & TB & H10 & H30 & HD8).
  (* 0x14228 lui a0,0x5a5a6; andi s0,s2,1; addi a0,a0,-0x5a6; sw a0,0x188(sp) *)
  step. step. step.
  assert (HS : store_ok rsegs m1 (wa (SP + 392)) 4 = true)
    by exact (stk_store_ok rsegs m1 lo (SP + 488) (SP + 392) 4 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 392));
    assert (MP2 : MemP (write_to_mem m1 (wa (SP + 392)) BS) 0x5a5a5a5a);
    [ split; [split|];
      [ apply MemT_store; rewrite ?length_le4; [exact MT | exact HS | lia | lia]
      | split; [apply bytes_at_write_other; rewrite ?length_le4; [exact HPPB | lia | lia | lia]|];
        split; [apply bytes_at_write_same; rewrite ?length_le4; lia|];
        apply task_mem_write_u; rewrite ?length_le4; [exact TM | exact HS]
      | apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H98 | lia | lia | lia] ]
    | assert (HPB2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 392)) BS) pod (buf r))
        by (apply bytes_at_write_other; rewrite ?length_le4; [exact HPB | lia | lia | lia]);
      revert MP2 HPB2; generalize (write_to_mem m1 (wa (SP + 392)) BS) as m2; intros m2 MP2 HPB2 ]
  end.
  clear MU WM MI ST TB MT HPPB H98 TM HS H10 H30 HD8.
  pose proof MP2 as ((MT & HPPB & HC & TM) & H98). pose proof MT as (MU & WM & MI & ST & TB & H10 & H30 & HD8).
  (* 0x14238 addi a0,s0,-1; and a0,a0,s3; addi a1,sp,0x188; jal reac_rate_prop_parse *)
  step. step. step. step.
  eapply evt_cut.
  { eapply PARSE with (null := Z.testbit fl 0) (lo := lo) (P := pod) (Q := SP + 392) (bs := buf r).
    - f_equal. apply parse_arg; lia.
    - reflexivity.
    - unfold rate_args. split; [exact HPB2|]. split; [lia|]. split; [exact HPODA|]. split; [lia|].
      split; [rewrite HU; reflexivity|]. split; [lia|].
      split; [apply (stk_wr_at rsegs m2 lo (SP + 488)); [exact ST | lia | lia | lia]|]. split; lia.
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

(** 0x1420c .. 0x14224: pod <> 0, s3 = pod, len <> 0; memcpy(pod, pp, len). *)
Lemma head_ok : forall (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s9 s10 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (junk : list byte),
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> stk rsegs m lo (SP + 488) -> ctbl m ->
  bytes_at rsegs m pp (pp_bytes r) ->
  bytes_at rsegs m (SP + 16) (le8 (Z_to_bv 64 mask)) -> bytes_at rsegs m (SP + 48) (le8 (Z_to_bv 64 buflen)) ->
  bytes_at rsegs m (SP + 152) (le8 (Z_to_bv 64 (pp + 19732))) -> bytes_at rsegs m (SP + 216) (le8 (Z_to_bv 64 pp)) ->
  rw_cells rsegs m pod [CB (Z.to_nat len) junk] ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pod) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 fl) s3
             (Z_to_bv 64 len) s5 s6 s7 (Z_to_bv 64 pp) s9 s10 (Z_to_bv 64 (pp + 16384)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x1420c) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s9 s10 t3 t4 t5 t6 F fc junk HF HMI HTM HST HTB HPPB
    H10 H30 H98 HD8 HPC.
  pose proof len_pp as LP. pose proof len_buf as LB. pose proof HST as (HS0 & HS1 & _).
  (* 0x1420c beqz a0; mv s3,a0; beqz s4 *)
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  step. step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x14218 mv a0,s3; mv a1,s8; mv a2,s4; jal memcpy *)
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
  assert (DJ : forall A k, lo <= A -> A + k <= SP + 488 -> disjoint_from [(pod, pod + len)] A k)
    by (intros A k H1 H2; cbn [disjoint_from]; split; [lia | exact I]).
  assert (MT1 : MemT m1).
  { split; [apply (munch_weaken [(pod, pod + len)] WC m m1); [|exact MU1]|].
    { unfold sub_fp, WC. cbn [outside]. intros x (_ & O2 & _). split; [exact O2 | exact I]. }
    split; [exact WM1|]. split; [exact MI1|].
    split; [apply (stk_transport_disjoint rsegs _ m m1 _ _ HST MU1 WM1); cbn [disjoint_from]; split; [lia | exact I]|].
    split.
    { apply (ctbl_munch _ m m1 HTB MU1). intros a Ha. cbn [outside].
      split; [exact (codes_apart pod (pod + len) HPROM a Ha) | exact I]. }
    split; [apply (bytes_at_transport rsegs _ m m1 _ _ H10 MU1); rewrite length_le8; apply DJ; lia|].
    split; [apply (bytes_at_transport rsegs _ m m1 _ _ H30 MU1); rewrite length_le8; apply DJ; lia|].
    apply (bytes_at_transport rsegs _ m m1 _ _ HD8 MU1). rewrite length_le8. apply DJ; lia. }
  eapply after_cpy.
  - exact HF.
  - exact MT1.
  - apply (bytes_at_transport rsegs _ m m1 _ _ HPPB MU1). cbn [disjoint_from]. unfold or_h in HSEP. split; [lia | exact I].
  - apply (bytes_at_transport rsegs _ m m1 _ _ H98 MU1). rewrite length_le8. apply DJ; lia.
  - apply (task_mem_munch_u _ m m1 HTM MU1). intros x Hx. cbn [outside] in Hx.
    destruct HPC as [_ (W0 & W1 & W)]. cbn [cells_size csize] in W.
    pose proof (W (bv_unsigned x - pod)) as Wx. replace (pod + (bv_unsigned x - pod)) with (bv_unsigned x) in Wx by lia.
    unfold wa in Wx. rewrite Z_to_bv_lit_self in Wx. apply Wx. lia.
  - exact (rw_cells_CB_bytes rsegs m1 pod _ _ CB1).
Qed.

End Check.
