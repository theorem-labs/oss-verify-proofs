(** The walk of reac-pw/fuzz_rate's LLVMFuzzerTestOneInput (plain) from malloc(pod)'s return (0x141e4) to the pc
    after check_code(refuse_code(4), 4) returned (0x14504), against rate_check_contract
    (Prog/LLVMFuzzerTestOneInput_c.v), with the callee contracts as Section hypotheses. Section Check fixes the
    contract's frame (sp, gp, tp, the entry memory m), the record r pod_build made with its buffer length len, pp,
    pod, lo and the header values fl, mask, buflen; QC is the contract's postcondition. Walked backwards: QC_done
    (0x14504), fin_ok (0x144f4: check_code(refuse_code(4), 4)), the decide loop (inl_ok 0x14494: check_decide,
    refuse_code, check_code, reac_rate_bit, reac_rate_is_closed, reac_rate_best_drivable, check_list; body_ok
    0x14414: reac_rate_cfg_decide and the inline expect_decide with its two closed_list scans at .rodata 0x10648;
    loop0_ok / loop1_ok for the flag s0 = 0, then 1) and its set-up decide_ok (0x143dc: asked[0] = rc = 1 ? hz :
    48000, other, role = flags bit 1); absent_ok (0x14360), malformed_ok (0x143d0) / malformed2_ok (0x143c8),
    rate_ok (0x143b0); float_ok (0x14384: pod_float, pod_nearest(f, sp + 0xb8)), value_ok (0x14314: ent[j + 1] of
    the rate key, pod_int or pod_float); the pod_next_pair scan by induction on the entries left (outer_ok 0x142a4,
    inner_ok 0x142b8, nokey_ok 0x142e4, key_ok 0x142e8 with strcmp against "reac.cfg.rate" at 0x1045e); setup_ok
    (0x14264), after_parse (0x14228: corrupt, the NULL flag, is_props, the spills of s2, s7, s6, s10 to sp + 0x30,
    0x10, 0x18, 0x20, params_struct), after_cpy (0x14200: the hz cell sp + 0x158 and reac_rate_prop_parse) and
    head_ok (0x141e4: memcpy). The answers agree because the scan computes expect_model false r (Pod/Rate.v) step by
    step and the parse's answer is parse_model of the uncorrupted buffer, which is the same (hypothesis HPM); the
    asked values of the decide loop are not tracked: the inline scans compare the whole 64-bit asked word against
    the sign-extended closed rates, so the inline expect_decide is decide_res (role, asked, mask) for any asked word
    (Pod/RateCfg.v expect_decide_res; the contract review's site_check_decide), and every callee contract
    in the loop holds for any argument word.
    Ported from reac-pw/fuzz_role's Prog/RoleCheck/Walk.v, re-walked at rate's registers, stack slots and
    addresses. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP
  ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import memcpy_c reac_rate_prop_parse_c strcmp_c
  pod_nearest_c check_absent_c check_rate_c check_malformed_c reac_rate_cfg_decide_c check_decide_c
  reac_rate_refuse_code_c check_code_c reac_rate_bit_c reac_rate_is_closed_c reac_rate_best_drivable_c check_list_c
  SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa Nearest Rate
  RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateCheck Require Import Facts.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).
(* Register equations at a loop head. *)
Ltac weq := first [ reflexivity
                  | (rewrite addiw1_small by lia; f_equal; lia)
                  | (f_equal; lia)
                  | (f_equal; rewrite ?unsigned_lit by lia; lia) ].

Lemma word_of_unsigned : forall (x : word) z, bv_unsigned x = z -> x = Z_to_bv 64 z.
Proof. intros x z H. rewrite <- H. symmetry. apply Z_to_bv_lit_self. Qed.

Lemma land_ww_range : forall (y x : word), 0 <= Z.land (bv_unsigned y) (bv_unsigned x) < 2^64.
Proof.
  intros y x. pose proof (bv_unsigned_in_range 64 x) as R. pose proof (bv_unsigned_in_range 64 y) as Ry.
  change (bv_modulus 64) with (2^64) in R, Ry. split; [apply Z.land_nonneg; left; lia|].
  assert (E : Z.land (bv_unsigned y) (bv_unsigned x) = Z.land (Z.land (bv_unsigned y) (bv_unsigned x)) (Z.ones 64)).
  { rewrite <- Z.land_assoc. f_equal. rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
  rewrite E, Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Section Check.
Variables (sp gp tp : word) (m : word -> option byte) (len pp pod lo mask buflen fl : Z) (r : pod_rec).

Local Abbreviation SP := (bv_unsigned sp).

Hypothesis HPOD : 0 < pod.
Hypothesis HLEN0 : 0 <= len.
Hypothesis HPODLO : pod + len <= lo.
Hypothesis HPP0 : 0 <= pp.
Hypothesis HPPLO : pp + 19744 <= lo.
Hypothesis HLO0 : 0 <= lo.
Hypothesis HLO : lo + 4096 <= SP.
Hypothesis HSPT : SP + 440 <= 2^64.
Hypothesis HSPA : SP mod 16 = 0.
Hypothesis HROM : forall a, lo <= a < SP + 440 -> seg_rom rsegs (wa a) = None.
Hypothesis HMASK : 0 <= mask < 256.
Hypothesis HFL : 0 <= fl < 256.
Hypothesis HWF : pod_rec_wf r.

Definition QC : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s6' s7' s8' s11'
                     t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                  s2' (Z_to_bv 64 pod) s4' s5' s6' s7' s8' (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11'
                  t3' t4' t5' t6')
             F' (Z_to_bv 64 RATE_CHECK_END) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\
    bytes_at rsegs m' (SP + 0x80) (le8 (Z_to_bv 64 pp)) /\
    munch [(SP - MID_STACK, SP + FRAME_LOCALS); (pod, pod + len)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (SP + FRAME_LOCALS).

(** The footprint and the memory the walk carries: changed only in the frame's locals, the callees' stack and the
    pod block; the stack region with the frame's locals present and writable. *)
Definition WC : list (Z * Z) := [(SP - 4096, SP + 440); (pod, pod + len)].
Definition MemT (m1 : word -> option byte) : Prop :=
  munch WC m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (SP + 440).

Lemma MemT_store : forall m1 a bs, MemT m1 -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP - 4096 <= a -> a + Z.of_nat (length bs) <= SP + 440 -> MemT (write_to_mem m1 (wa a) bs).
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
  (forall x, SP <= x < SP + 440 -> outside W x \/ exists b, m2 (wa x) = Some b) -> MemT m2.
Proof.
  intros m1 m2 W (MU & WM & MI & ST) MU2 WM2 MI2 ST2 SUB HX.
  split; [exact (munch_trans WC m m1 m2 MU (munch_weaken W WC m1 m2 SUB MU2))|].
  split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
  split; [exact MI2|].
  destruct (stk_split rsegs m1 lo SP (SP + 440) ST ltac:(lia)) as [_ ST1].
  apply (stk_merge rsegs m2 lo SP); [exact ST2 | | lia].
  exact (stk_transport rsegs W m1 m2 SP (SP + 440) ST1 MU2 WM2 HX).
Qed.

Lemma MemT_below : forall m1 m2 k, MemT m1 -> munch [(SP - k, SP)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo SP -> 0 <= k <= 4096 -> MemT m2.
Proof.
  intros m1 m2 k MT MU WM MI ST Hk. apply (MemT_call m1 m2 [(SP - k, SP)] MT MU WM MI ST).
  - unfold sub_fp, WC. cbn [outside]. intros x (O1 & _ & _). split; [lia | exact I].
  - intros x Hx. left. cbn [outside]. split; [lia | exact I].
Qed.

Lemma MemT_stk : forall m1, MemT m1 -> stk rsegs m1 lo SP.
Proof. intros m1 (_ & _ & _ & ST). exact (proj1 (stk_split rsegs m1 lo SP (SP + 440) ST ltac:(lia))). Qed.

(** A cell at or above sp survives a callee that writes only below sp. *)
Lemma cell_below : forall m1 m2 k A bs, munch [(SP - k, SP)] m1 m2 -> bytes_at rsegs m1 A bs -> SP <= A ->
  bytes_at rsegs m2 A bs.
Proof.
  intros m1 m2 k A bs MU H HA. apply (bytes_at_transport rsegs _ m1 m2 _ _ H MU). cbn [disjoint_from].
  split; [lia | exact I].
Qed.

Hypothesis RFC : reac_rate_refuse_code_contract.
Hypothesis CKC : check_code_contract.

(** 0x14504: the contract's postcondition. *)
Lemma QC_done : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 (Z_to_bv 64 mask)
             (Z_to_bv 64 buflen) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14504) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 F fc m1 HF (MU & WM & MI & ST) H80.
  apply evt_done. exists ra, t0, t1, t2, s0, s1, a0, a1, a2, a3, a4, a5, a6, a7, s2, s4, s5, s6, s7, s8, s11,
    t3, t4, t5, t6, F, fc, m1.
  split; [reflexivity|]. split; [exact HF|]. split; [exact H80|]. split; [exact MU|]. split; [exact WM|].
  split; [exact MI | exact ST].
Qed.

(** 0x144f4 .. 0x14504: check_code(refuse_code(4), 4). *)
Lemma fin_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 : word)
                      (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 (Z_to_bv 64 mask)
             (Z_to_bv 64 buflen) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x144f4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 F fc m1 HF MT H80.
  pose proof MT as (_ & _ & MI & _).
  (* 0x144f4 addi a0,zero,4; jal reac_rate_refuse_code *)
  step. step.
  eapply evt_cut; [eapply RFC; exact MI|]. intros ms' (a1x & ->). ret_even.
  (* 0x144fc addi a1,zero,4; jal check_code *)
  step. step.
  eapply evt_cut.
  { eapply CKC with (lo := lo); [ first [ (rewrite unsigned_lit by lia; lia) | (vm_compute; let Hc := fresh in intro Hc; discriminate Hc) ]
                                | first [reflexivity | vm_compute; reflexivity]
                                | exact (MemT_stk m1 MT) | unfold CHECK_CODE_FRAME; lia
                                | intros a Ha; apply HROM; lia | exact MI ]. }
  intros ms' (a0' & a1' & a2' & a3' & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'. ret_even.
  apply QC_done; [exact HF | |].
  - apply (MemT_below m1 m2 CHECK_CODE_FRAME MT MU2 WM2 MI2 ST2). unfold CHECK_CODE_FRAME. lia.
  - apply (cell_below m1 m2 CHECK_CODE_FRAME _ _ MU2 H80). lia.
Qed.

Hypothesis DEC : reac_rate_cfg_decide_contract.
Hypothesis CKD : check_decide_contract.
Hypothesis BIT : reac_rate_bit_contract.
Hypothesis CLO : reac_rate_is_closed_contract.
Hypothesis BEST : reac_rate_best_drivable_contract.
Hypothesis CKL : check_list_contract.

(** The state at 0x144e4 the loop body leaves, for the role rl, the flag s0, the next value s1 and the asked word
    s5: the continuation each round supplies. *)
Definition KB (rl : Z) (s0 s1 s5 s11 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) : Prop :=
  forall (ra t0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 : word) (m2 : word -> option byte),
  MemT m2 -> bytes_at rsegs m2 (SP + 128) (le8 (Z_to_bv 64 pp)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x10648) (Z_to_bv 64 pod) (Z_to_bv 64 rl)
             s5 s6 s7 (Z_to_bv 64 1) (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x144e4) fc None m2 (seg_rom rsegs)).

(** 0x14494 .. 0x144e0: check_decide(r, r), check_code(refuse_code(r), r), check_list(asked, bit, closed, mask,
    best) for r = decide_res (role, asked, mask). *)
Lemma inl_ok : forall (rl : Z) (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s11 t3 t4 t5 t6 : word)
                      (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  MemT m1 -> bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) ->
  a1 = Z_to_bv 64 (decide_res rl (bv_unsigned s5) mask) -> s6 = Z_to_bv 64 (decide_res rl (bv_unsigned s5) mask) ->
  KB rl s0 s1 s5 s11 t1 t2 t3 t4 t5 t6 F fc ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x10648) (Z_to_bv 64 pod) (Z_to_bv 64 rl)
             s5 s6 s7 (Z_to_bv 64 1) (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14494) fc None m1 (seg_rom rsegs)).
Proof.
  intros rl ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s11 t3 t4 t5 t6 F fc m1 MT H80 -> -> K.
  pose proof MT as (_ & _ & MI & _).
  destruct (decide_res_word rl (bv_unsigned s5) mask) as [EW LE].
  (* 0x14494 mv a0,s6; jal check_decide *)
  step. step.
  eapply evt_cut; [eapply CKD; reflexivity|]. intros ms' ->. ret_even.
  (* 0x1449c mv a0,s6; jal reac_rate_refuse_code *)
  step. step.
  eapply evt_cut; [eapply RFC; exact MI|]. intros ms' (a1x & ->). ret_even.
  (* 0x144a4 mv a1,s6; jal check_code *)
  step. step.
  eapply evt_cut.
  { eapply CKC with (lo := lo); [ rewrite EW; exact LE | reflexivity
                                | exact (MemT_stk m1 MT) | unfold CHECK_CODE_FRAME; lia
                                | intros a Ha; apply HROM; lia | exact MI ]. }
  intros ms' (a0' & a1' & a2' & a3' & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'. ret_even.
  assert (MT2 : MemT m2) by (apply (MemT_below m1 m2 CHECK_CODE_FRAME MT MU2 WM2 MI2 ST2); unfold CHECK_CODE_FRAME; lia).
  assert (H80b : bytes_at rsegs m2 (SP + 128) (le8 (Z_to_bv 64 pp))) by (apply (cell_below m1 m2 CHECK_CODE_FRAME _ _ MU2 H80); lia).
  clear MU2 WM2 ST2.
  (* 0x144ac mv a0,s5; jal reac_rate_bit *)
  step. step.
  eapply evt_cut; [eapply BIT|]. intros ms' (a1y & ->). ret_even.
  (* 0x144b4 mv s6,a0; mv a0,s5; jal reac_rate_is_closed *)
  step. step. step.
  eapply evt_cut; [eapply CLO|]. intros ms' (a1z & a2z & ->). ret_even.
  (* 0x144c0 mv s7,a0; mv a0,s9; jal reac_rate_best_drivable *)
  step. step. step.
  eapply evt_cut; [eapply BEST|]. intros ms' (a1w & ->). ret_even.
  (* 0x144cc mv a4,a0; mv a0,s5; mv a1,s6; mv a2,s7; mv a3,s9; jal check_list *)
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply CKL with (lo := lo); [ reflexivity | reflexivity | reflexivity
                                | exact (MemT_stk m2 MT2) | unfold CHECK_LIST_FRAME; lia
                                | intros a Ha; apply HROM; lia | exact MI2 ]. }
  intros ms' (a0b & a1b & a3b & a5b & a6b & a7b & t0b & m3 & E & MU3 & WM3 & MI3 & ST3). subst ms'. ret_even.
  apply K.
  - apply (MemT_below m2 m3 CHECK_LIST_FRAME MT2 MU3 WM3 MI3 ST3). unfold CHECK_LIST_FRAME. lia.
  - apply (cell_below m2 m3 CHECK_LIST_FRAME _ _ MU3 H80b). lia.
Qed.

(** A closed rate: the inline `sllw a0,s8,a0; and a0,a0,s9; seqz a1,a0; slli a1,a1,1` is decide_res, the bit
    1 << index being rate_bit of the rate (both closed terms). *)
Ltac inl_closed :=
  rewrite seqz_slli by apply land_ww_range; rewrite (unsigned_lit mask) by lia;
  rewrite decide_res_closed by (vm_compute; let Hc := fresh in intro Hc; discriminate Hc); reflexivity.

(** 0x14414 .. 0x14490: reac_rate_cfg_decide(role, asked, mask), then the inline expect_decide. *)
Lemma body_ok : forall (rl : Z) (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  MemT m1 -> bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) -> or_h (rl = 0) (rl = 1) ->
  KB rl s0 s1 s5 s11 t1 t2 t3 t4 t5 t6 F fc ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x10648) (Z_to_bv 64 pod) (Z_to_bv 64 rl)
             s5 s6 s7 (Z_to_bv 64 1) (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14414) fc None m1 (seg_rom rsegs)).
Proof.
  intros rl ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s11 t3 t4 t5 t6 F fc m1 MT H80 Hrl K.
  pose proof MT as (_ & _ & MI & _).
  (* 0x14414 mv a0,s4; mv a1,s5; mv a2,s9; jal reac_rate_cfg_decide *)
  step. step. step. step.
  eapply evt_cut; [eapply DEC|]. intros ms' (a2x & a3x & ->). ret_even.
  rewrite (unsigned_lit mask) by lia.
  destruct Hrl as [-> | ->]; [change (bv_unsigned (Z_to_bv 64 0)) with 0 | change (bv_unsigned (Z_to_bv 64 1)) with 1].
  - (* role 0 (master): 0x14424 mv s6,a0; bnez s4 not taken *)
    step. step. if_false.
    destruct (rate_bit_cases (bv_unsigned s5)) as [[E R]|[[E R]|[[E R]|(N1&N2&N3&R)]]].
    + (* 44100: the first scan hits at pass 1, the second at index 0 *)
      apply word_of_unsigned in E. unfold RATE_44K1 in E. subst s5.
      (* 0x1442c addi a0,zero,3; mv a1,s2; lw a2,0(a1); beq s5,a2 taken *)
      step. step. step. step. if_true.
      (* 0x14458 mv a0,zero; addi a1,zero,3; mv a2,s2; lw a3,0(a2); beq s5,a3 taken *)
      step. step. step. step. step. if_true.
      (* 0x14484 sllw a0,s8,a0; and a0,a0,s9; seqz a1,a0; slli a1,a1,1 *)
      step. step. step. step.
      eapply inl_ok; [exact MT | exact H80 | | reflexivity | exact K]. inl_closed.
    + (* 48000: pass 2 *)
      apply word_of_unsigned in E. unfold RATE_48K in E. subst s5.
      step. step. step. step. if_false. step. step. step. if_true. step. step. if_true.
      step. step. step. step. step. if_false. step. step. step. step. if_true. step. step. if_true.
      step. step. step. step.
      eapply inl_ok; [exact MT | exact H80 | | reflexivity | exact K]. inl_closed.
    + (* 96000: pass 3 *)
      apply word_of_unsigned in E. unfold RATE_96K in E. subst s5.
      step. step. step. step. if_false. step. step. step. if_true. step. step. if_false. step. step. step. if_true.
      step. step. if_true.
      step. step. step. step. step. if_false. step. step. step. step. if_true. step. step. if_false.
      step. step. step. step. if_true. step. step. if_true.
      step. step. step. step.
      eapply inl_ok; [exact MT | exact H80 | | reflexivity | exact K]. inl_closed.
    + (* no closed rate: three misses, a1 = 1 *)
      unfold RATE_44K1, RATE_48K, RATE_96K in *.
      step. step. step. step. if_false. step. step. step. if_true. step. step. if_false. step. step. step. if_true.
      step. step. if_false. step. step. step. if_false.
      (* 0x14448 addi a1,zero,1; j 0x14494 *)
      step. step.
      eapply inl_ok; [exact MT | exact H80 | | reflexivity | exact K].
      rewrite decide_res_open by exact R. reflexivity.
  - (* role 1 (slave): 0x14424 mv s6,a0; bnez s4 taken; 0x14450 addi a1,zero,3; j 0x14494 *)
    step. step. if_true. step. step.
    eapply inl_ok; [exact MT | exact H80 | | reflexivity | exact K].
    rewrite decide_res_slave. reflexivity.
Qed.

(** 0x14414 with the flag s0 = 0: the second round, then 0x144f4. *)
Lemma loop0_ok : forall (rl : Z) (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) -> or_h (rl = 0) (rl = 1) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x10648) (Z_to_bv 64 pod)
             (Z_to_bv 64 rl) s5 s6 s7 (Z_to_bv 64 1) (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14414) fc None m1 (seg_rom rsegs)).
Proof.
  intros rl ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s11 t3 t4 t5 t6 F fc m1 HF MT H80 Hrl.
  apply body_ok; [exact MT | exact H80 | exact Hrl |].
  intros ra' t0' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' m2 MT2 H802.
  (* 0x144e4 andi a0,s0,1; mv s5,s1; mv s0,zero; bnez a0 not taken *)
  step. step. step. step. if_false.
  apply fin_ok; [exact HF | exact MT2 | exact H802].
Qed.

(** 0x14414 with the flag s0 = 1: the first round, then the second with asked = s1. *)
Lemma loop1_ok : forall (rl : Z) (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) -> or_h (rl = 0) (rl = 1) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 1) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x10648) (Z_to_bv 64 pod)
             (Z_to_bv 64 rl) s5 s6 s7 (Z_to_bv 64 1) (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14414) fc None m1 (seg_rom rsegs)).
Proof.
  intros rl ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s11 t3 t4 t5 t6 F fc m1 HF MT H80 Hrl.
  apply body_ok; [exact MT | exact H80 | exact Hrl |].
  intros ra' t0' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' m2 MT2 H802.
  (* 0x144e4 andi a0,s0,1; mv s5,s1; mv s0,zero; bnez a0 taken *)
  step. step. step. step. if_true.
  apply loop0_ok; [exact HF | exact MT2 | exact H802 | exact Hrl].
Qed.

(** 0x143dc .. 0x14410: other = b3 | b4 << 8 | b5 << 16 | b6 << 24 (s2 | s7, s0 << 16), asked[0] = rc = 1 ? hz :
    48000, role = flags bit 1, closed_list, the flag s0 = 1. *)
Lemma decide_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s11 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 (Z_to_bv 64 fl) s7 s8
             (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x143dc) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s11 t3 t4 t5 t6 F fc m1 HF MT H80.
  pose proof MT as (_ & _ & _ & ST).
  assert (ER : Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 fl)) 62))) 63)
               = Z_to_bv 64 (Z.b2z (Z.testbit fl 1))).
  { f_equal. rewrite (unsigned_lit fl) by lia. rewrite unsigned_lit_wrap. apply role_bit_z. exact HFL. }
  assert (HRL : or_h (Z.b2z (Z.testbit fl 1) = 0) (Z.b2z (Z.testbit fl 1) = 1)) by exact (b2z_01 _).
  (* 0x143dc or a0,s2,s7; slliw s1,s0,0x10; addi s0,zero,1; slli a1,s6,0x3e; beq s4,s0 *)
  step. step. step. step. step. if_cases EQ.
  - (* rc = 1: 0x143fc lw s5,0x158(sp) *)
    destruct (stk_read rsegs m1 lo (SP + 440) (SP + 344) 4 ST ltac:(lia) ltac:(lia)) as (bs & HR).
    step. clear HR.
    (* 0x14400 or s1,a0,s1; srli s4,a1,0x3f; auipc a0; addi s2,a0,0x240; addi s8,zero,1 *)
    step. step. step. step. step. rewrite ER.
    apply loop1_ok; [exact HF | exact MT | exact H80 | exact HRL].
  - (* rc <> 1: 0x143f0 lui a2,0xc; addiw s5,a2,-0x480; j 0x14400 *)
    step. step. step.
    step. step. step. step. step. rewrite ER.
    apply loop1_ok; [exact HF | exact MT | exact H80 | exact HRL].
Qed.

Hypothesis CKAB : check_absent_contract.
Hypothesis CKR : check_rate_contract.
Hypothesis CKM : check_malformed_contract.

(** The cells the check calls and the decide set-up read: sp + 0x80 = pp, the hz cell, the spills of fl and
    buflen. *)
Definition MemR (m1 : word -> option byte) (c : Z) : Prop :=
  MemT m1 /\ bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) /\ bytes_at rsegs m1 (SP + 344) (le4 (Z_to_bv 64 c)) /\
  bytes_at rsegs m1 (SP + 24) (le8 (Z_to_bv 64 fl)) /\ bytes_at rsegs m1 (SP + 32) (le8 (Z_to_bv 64 buflen)).

(** 0x14360 .. 0x14380: check_absent(rc, hz), then s9, s10, s6, s7, s2 back from s7 and the spills. *)
Lemma absent_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemR m1 0x5a5a5a5a -> bv_unsigned s4 = 0 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 (Z_to_bv 64 mask) s8 s9 s10
             s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14360) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF
    (MT & H80 & HC & H18 & H20) H4.
  pose proof MT as (_ & _ & _ & ST).
  (* 0x14360 lw a1,0x158(sp); mv a0,s4; jal check_absent *)
  pose proof (read_le4_cell rsegs m1 (SP + 344) _ HC) as HR. step. clear HR. rewrite ?sx32_small by lia. step. step.
  eapply evt_cut; [eapply CKAB; [exact H4 | first [ (rewrite unsigned_lit by lia; reflexivity) | (vm_compute; reflexivity) ]]|].
  intros ms' ->. ret_even.
  (* 0x1436c mv s9,s7; ld s10,0x20(sp); ld s6,0x18(sp); ld s7,0x10(sp); ld s2,0x30(sp); j 0x143dc *)
  step.
  pose proof (read_le8 rsegs m1 (SP + 32) _ H20) as HR. step. clear HR.
  pose proof (read_le8 rsegs m1 (SP + 24) _ H18) as HR. step. clear HR.
  destruct (stk_read rsegs m1 lo (SP + 440) (SP + 16) 8 ST ltac:(lia) ltac:(lia)) as (bs1 & HR). step. clear HR.
  destruct (stk_read rsegs m1 lo (SP + 440) (SP + 48) 8 ST ltac:(lia) ltac:(lia)) as (bs2 & HR). step. clear HR.
  step.
  apply decide_ok; [exact HF | exact MT | exact H80].
Qed.

(** 0x143d0 .. 0x143d8: check_malformed(rc, hz). *)
Lemma malformed_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s11 t3 t4 t5 t6 : word)
                            (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) ->
  bytes_at rsegs m1 (SP + 344) (le4 (Z_to_bv 64 0x5a5a5a5a)) -> bv_unsigned s4 = 2^64 - 1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 (Z_to_bv 64 fl) s7 s8
             (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x143d0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s11 t3 t4 t5 t6 F fc m1 HF MT H80 HC H4.
  (* 0x143d0 lw a1,0x158(sp); mv a0,s4; jal check_malformed *)
  pose proof (read_le4_cell rsegs m1 (SP + 344) _ HC) as HR. step. clear HR. rewrite ?sx32_small by lia. step. step.
  eapply evt_cut; [eapply CKM; [exact H4 | first [ (rewrite unsigned_lit by lia; reflexivity) | (vm_compute; reflexivity) ]]|].
  intros ms' ->. ret_even.
  apply decide_ok; [exact HF | exact MT | exact H80].
Qed.

(** 0x143c8 .. 0x143cc: s6 and s7 back from the spills, then check_malformed. *)
Lemma malformed2_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 : word)
                             (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemR m1 0x5a5a5a5a -> bv_unsigned s4 = 2^64 - 1 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8 (Z_to_bv 64 mask)
             (Z_to_bv 64 buflen) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x143c8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 F fc m1 HF
    (MT & H80 & HC & H18 & H20) H4.
  pose proof MT as (_ & _ & _ & ST).
  (* 0x143c8 ld s6,0x18(sp); ld s7,0x10(sp) *)
  pose proof (read_le8 rsegs m1 (SP + 24) _ H18) as HR. step. clear HR.
  destruct (stk_read rsegs m1 lo (SP + 440) (SP + 16) 8 ST ltac:(lia) ltac:(lia)) as (bs1 & HR). step. clear HR.
  eapply malformed_ok; [exact HF | exact MT | exact H80 | exact HC | exact H4].
Qed.

(** 0x143b0 .. 0x143c4: s6, s7 back; check_rate(rc, hz, want) with hz = want = v, an int32. *)
Lemma rate_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (v : Z),
  frm0 fc -> MemR m1 v -> bv_unsigned s4 = 1 -> -2^31 <= v < 2^31 ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 s7 s8
             (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x143b0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 F fc m1 v HF
    (MT & H80 & HC & H18 & H20) H4 Hv.
  pose proof MT as (_ & _ & _ & ST).
  (* 0x143b0 ld s6,0x18(sp); ld s7,0x10(sp) *)
  pose proof (read_le8 rsegs m1 (SP + 24) _ H18) as HR. step. clear HR.
  destruct (stk_read rsegs m1 lo (SP + 440) (SP + 16) 8 ST ltac:(lia) ltac:(lia)) as (bs1 & HR). step. clear HR.
  (* 0x143b8 lw a1,0x158(sp); mv a0,s4; jal check_rate *)
  pose proof (read_le4_cell rsegs m1 (SP + 344) _ HC) as HR. step. clear HR. rewrite sx32_int by lia. step. step.
  eapply evt_cut; [eapply CKR; [exact H4 | reflexivity]|]. intros ms' ->. ret_even.
  (* 0x143c4 j 0x143dc *)
  step.
  apply decide_ok; [exact HF | exact MT | exact H80].
Qed.

(** ** expect_rate over the record in pp *)
Local Abbreviation es := (ents r).
Local Abbreviation n := (length (ents r)).
Local Abbreviation E0 := (expect_model false r).

(** The memory of the scan: MemT, the record at pp, the cells sp + 0x80 = pp and sp + 0xb0 = b (pp + 0x4000 before
    the scan's set-up, &pp->ent[0] after it), the hz cell c, the spills of fl and buflen, MemNorm.task_mem
    (pod_nearest's soft-float callees take it). *)
Definition MemX (m1 : word -> option byte) (b c : Z) : Prop :=
  MemT m1 /\ bytes_at rsegs m1 pp (pp_bytes r) /\ bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) /\
  bytes_at rsegs m1 (SP + 176) (le8 (Z_to_bv 64 b)) /\ bytes_at rsegs m1 (SP + 344) (le4 (Z_to_bv 64 c)) /\
  bytes_at rsegs m1 (SP + 24) (le8 (Z_to_bv 64 fl)) /\ bytes_at rsegs m1 (SP + 32) (le8 (Z_to_bv 64 buflen)) /\
  MemNorm.task_mem rsegs m1.

Lemma MemX_R : forall m1 b c, MemX m1 b c -> MemR m1 c.
Proof. intros m1 b c (MT & _ & H80 & _ & HC & H18 & H20 & _). split; [exact MT|]. split; [exact H80|]. split; [exact HC|]. split; [exact H18 | exact H20]. Qed.

Lemma len_pp : Z.of_nat (length (pp_bytes r)) = 19744.
Proof. exact (length_pp_bytes r HWF). Qed.

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
  rewrite forallb_forall in F. specialize (F _ H). cbv beta in F.
  assert (E : negb (bv_unsigned (Z_to_bv 8 0) =? 0) = false) by (vm_compute; reflexivity).
  rewrite E in F. discriminate F.
Qed.

Hypothesis STRC : strcmp_contract.
Hypothesis NEAR : pod_nearest_contract.

(** The cells of MemR survive pod_nearest, which writes below sp and, on an answer, the 8 bytes at sp + 0xb8. *)
Lemma near_cell : forall m1 m2 A bs, munch [(SP - POD_NEAREST_STACK, SP); (SP + 184, SP + 184 + 8)] m1 m2 ->
  bytes_at rsegs m1 A bs -> SP <= A -> or_h (A + Z.of_nat (length bs) <= SP + 184) (SP + 192 <= A) ->
  bytes_at rsegs m2 A bs.
Proof.
  intros m1 m2 A bs MU H HA D. unfold or_h in D. apply (bytes_at_transport rsegs _ m1 m2 _ _ H MU). cbn [disjoint_from].
  unfold POD_NEAREST_STACK. split; [lia|]. split; [lia | exact I].
Qed.

(** 0x14384 .. 0x143ac: pod_float, pod_nearest(f, sp + 0xb8), then lw of its answer. *)
Lemma float_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (i : nat),
  frm0 fc -> MemX m1 (pp + 16404) (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  (i < n)%nat -> E0 = expect_value (nth i es (Ent 0 0 [])) -> e_type (nth i es (Ent 0 0 [])) = POD_FLOAT ->
  a0 = Z_to_bv 64 (pp + 16404 + 104 * Z.of_nat i) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 (Z_to_bv 64 mask) s8 s9 s10
             s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14384) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 i HF MX H4 Hi HV Ht ->.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof (ent_wf_nth r i HWF Hi) as (Ht0 & Hb & Hsz).
  pose proof MX as (MT & HPPB & H80 & Hb0 & HC & H18 & H20 & TM). pose proof MT as (MU & WM & MI & ST).
  pose proof (bytes_at_ent rsegs m1 pp r i HPPB HWF Hi) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat i) with (pp + 16404 + 104 * Z.of_nat i) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  rewrite HV, (ev_float _ Ht) in H4, HC.
  (* 0x14384 lw a1,4(a0); addi a2,zero,4; mv s9,s7; ld s10,0x20(sp); ld s2,0x30(sp) *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. step.
  pose proof (read_le8 rsegs m1 (SP + 32) _ H20) as HR. step. clear HR.
  destruct (stk_read rsegs m1 lo (SP + 440) (SP + 48) 8 ST ltac:(lia) ltac:(lia)) as (bs2 & HR). step. clear HR.
  (* 0x14398 bltu a1,a2 *)
  step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size (nth i es (Ent 0 0 []))) 4) as [Es|Es]; cbv beta iota.
  { rewrite (proj2 (Z.leb_gt 4 _) Es) in H4, HC. cbn [fst snd written_or] in H4, HC.
    eapply malformed2_ok; [exact HF | exact (conj MT (conj H80 (conj HC (conj H18 H20)))) | rewrite H4; reflexivity]. }
  rewrite (proj2 (Z.leb_le 4 _) Es) in H4, HC.
  (* 0x1439c flw fa0,8(a0); addi a0,sp,0xb8; jal pod_nearest *)
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
  revert H4 HC PNM. change NEAR_LO with INT32_MIN. change NEAR_HI with INT32_MAX.
  destruct (nearest (rd32 (e_body (nth i es (Ent 0 0 [])))) INT32_MIN INT32_MAX) as [w|] eqn:EN; intros H4 HC PNM;
    cbn [pod_near_mem pod_near_rc] in PNM |- *; cbn [fst snd written_or] in H4, HC.
  - (* a nearest integer w: 0x143a8 beqz a0 not taken; 0x143ac lw a2,0xb8(sp) *)
    destruct PNM as (MU2 & HW).
    assert (MT2 : MemT m2).
    { apply (MemT_call m1 m2 _ MT MU2 WM2 MI2 ST2).
      - unfold sub_fp, WC, POD_NEAREST_STACK. cbn [outside]. intros x (O1 & _ & _). repeat split; try exact I; lia.
      - intros x Hx. unfold POD_NEAREST_STACK.
        destruct (Z_lt_le_dec x (SP + 184)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; lia|].
        destruct (Z_lt_le_dec x (SP + 192)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; lia].
        apply (bytes_at_some rsegs m2 (SP + 184) _ x HW); rewrite length_le8; [intros a Ha; apply HROM | ]; lia. }
    assert (MR2 : MemR m2 w).
    { split; [exact MT2|].
      split; [apply (near_cell m1 m2 _ _ MU2 H80); try unfold or_h; rewrite ?length_le8; lia|].
      split; [apply (near_cell m1 m2 _ _ MU2 HC); try unfold or_h; rewrite ?length_le4; lia|].
      split; [apply (near_cell m1 m2 _ _ MU2 H18); try unfold or_h; rewrite ?length_le8; lia|].
      apply (near_cell m1 m2 _ _ MU2 H20); try unfold or_h; rewrite ?length_le8; lia. }
    step. if_false.
    pose proof (read_le4_cell rsegs m2 (SP + 184) _ (bytes_at_le8_le4 rsegs m2 (SP + 184) _ HW)) as HR. step. clear HR.
    pose proof (nearest_range _ _ EN) as Hw. unfold INT32_MIN, INT32_MAX in Hw. rewrite sx32_int by lia.
    eapply rate_ok; [exact HF' | exact MR2 | rewrite H4; reflexivity | lia].
  - (* none: 0x143a8 beqz a0 to 0x143c8 *)
    assert (MT2 : MemT m2) by (apply (MemT_below m1 m2 POD_NEAREST_STACK MT PNM WM2 MI2 ST2); unfold POD_NEAREST_STACK; lia).
    assert (MR2 : MemR m2 0x5a5a5a5a).
    { split; [exact MT2|].
      split; [apply (cell_below m1 m2 _ _ _ PNM H80); lia|].
      split; [apply (cell_below m1 m2 _ _ _ PNM HC); lia|].
      split; [apply (cell_below m1 m2 _ _ _ PNM H18); lia|].
      apply (cell_below m1 m2 _ _ _ PNM H20); lia. }
    step. if_true.
    eapply malformed2_ok; [exact HF' | exact MR2 | rewrite H4; reflexivity].
Qed.

(** 0x14314 .. 0x1435c: the value ent[j + 1] of the rate key: pod_int, else pod_float. *)
Lemma value_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (j : nat),
  frm0 fc -> MemX m1 (pp + 16404) (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  (S j < n)%nat -> E0 = expect_value (nth (S j) es (Ent 0 0 [])) -> s1 = Z_to_bv 64 (Z.of_nat j) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6 (Z_to_bv 64 mask) s8 s9 s10
             s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14314) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 j HF MX H4 Hj HV ->.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof (ent_wf_nth r (S j) HWF Hj) as (Ht0 & Hb & Hsz).
  pose proof MX as (MT & HPPB & H80 & Hb0 & HC & H18 & H20 & TM). pose proof MT as (MU & WM & MI & ST).
  pose proof (bytes_at_ent rsegs m1 pp r (S j) HPPB HWF Hj) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat (S j)) with (pp + 16404 + 104 * Z.of_nat (S j)) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  assert (MR : MemR m1 (written_or 0x5a5a5a5a E0)) by exact (MemX_R m1 _ _ MX).
  (* 0x14314 addi s1,s1,1; addi a0,zero,13; slli a0,a0,35; slli s1,s1,32; mulhu a0,s1,a0 *)
  step. step. step. step. step. rewrite mulhu_idx by lia.
  (* 0x14328 ld a1,0xb0(sp); add a0,a1,a0 *)
  pose proof (read_le8 rsegs m1 (SP + 176) _ Hb0) as HR. step. clear HR. step.
  (* 0x14330 lw a1,0(a0) *)
  pose proof (ent_type_read rsegs m1 _ _ HEB Ht0) as HR. step. clear HR.
  (* 0x14334 addi a2,zero,6; beq a1,a2 *)
  step. step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth (S j) es (Ent 0 0 []))) 6) as [Et|Et]; cbv beta iota.
  { eapply float_ok; [exact HF | exact MX | exact H4 | exact Hj | exact HV | exact Et | weq]. }
  (* 0x1433c addi a2,zero,4; mv s9,s7; ld s10,0x20(sp); ld s2,0x30(sp); bne a1,a2 *)
  step. step.
  pose proof (read_le8 rsegs m1 (SP + 32) _ H20) as HR. step. clear HR.
  destruct (stk_read rsegs m1 lo (SP + 440) (SP + 48) 8 ST ltac:(lia) ltac:(lia)) as (bs2 & HR). step. clear HR.
  step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth (S j) es (Ent 0 0 []))) 4) as [Et4|Et4]; cbn [negb]; cbv beta iota.
  2:{ assert (EV : E0 = (None, -1)) by (rewrite HV; apply ev_other; unfold POD_FLOAT, POD_INT; lia).
      rewrite EV in H4, MR. cbn [fst snd written_or] in H4, MR.
      eapply malformed2_ok; [exact HF | exact MR | rewrite H4; reflexivity]. }
  (* 0x14350 lw a1,4(a0); bltu a1,a2 *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. rewrite ltu_u by lia.
  destruct (Z.ltb_spec (e_size (nth (S j) es (Ent 0 0 []))) 4) as [Es|Es]; cbv beta iota.
  { assert (EV : E0 = (None, -1)) by (rewrite HV, ev_int by exact Et4; rewrite (proj2 (Z.leb_gt 4 _) Es); reflexivity).
    rewrite EV in H4, MR. cbn [fst snd written_or] in H4, MR.
    eapply malformed2_ok; [exact HF | exact MR | rewrite H4; reflexivity]. }
  (* 0x14358 lw a2,8(a0); j 0x143b0 *)
  pose proof (ent_word_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR.
  rewrite sext_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn. step.
  assert (EV : E0 = (Some (s32 (rd32 (e_body (nth (S j) es (Ent 0 0 []))))), 1))
    by (rewrite HV, ev_int by exact Et4; rewrite (proj2 (Z.leb_le 4 _) Es); reflexivity).
  rewrite EV in H4, MR. cbn [fst snd written_or] in H4, MR.
  pose proof (s32_range _ (rd32_range (e_body (nth (S j) es (Ent 0 0 []))))) as Hv.
  eapply rate_ok; [exact HF | exact MR | rewrite H4; reflexivity | lia].
Qed.

(** ** pod_next_pair's scan (0x142a4 .. 0x14310), by induction on the entries left *)
Definition outer_P (j : nat) : Prop :=
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s4 s6 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemX m1 (pp + 16404) (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  E0 = rate_of_pairs expect_value (pairs_by key_of (skipn j es) None) -> (j <= n)%nat ->
  s6 = Z_to_bv 64 (Z.of_nat j) -> s2 = Z_to_bv 64 (Z.of_nat n) -> s11 = Z_to_bv 64 (1 - Z.of_nat n) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 104) a5 a6 a7 s2 (Z_to_bv 64 pod) s4
             (Z_to_bv 64 0x1045e) s6 (Z_to_bv 64 mask) (Z_to_bv 64 8) (Z_to_bv 64 (-1)) (Z_to_bv 64 (pp + 16412)) s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x142a4) fc None m1 (seg_rom rsegs)).

Definition inner_P (j : nat) : Prop :=
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s4 s6 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemX m1 (pp + 16404) (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  E0 = rate_of_pairs expect_value (pairs_by key_of (skipn j es) None) -> (j < n)%nat ->
  a3 = Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat j) -> s1 = Z_to_bv 64 (Z.of_nat j - 1) ->
  s6 = Z_to_bv 64 (Z.of_nat j + 1) -> s2 = Z_to_bv 64 (Z.of_nat n) -> s11 = Z_to_bv 64 (1 - Z.of_nat n) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 104) a5 a6 a7 s2 (Z_to_bv 64 pod) s4
             (Z_to_bv 64 0x1045e) s6 (Z_to_bv 64 mask) (Z_to_bv 64 8) (Z_to_bv 64 (-1)) (Z_to_bv 64 (pp + 16412)) s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x142b8) fc None m1 (seg_rom rsegs)).

(** No pair is left: check_absent with rc 0 and the hz cell untouched. *)
Lemma none_left : forall m1 (s4 : word), MemX m1 (pp + 16404) (written_or 0x5a5a5a5a E0) ->
  bv_unsigned s4 = snd E0 mod 2^64 -> E0 = (None, 0) -> MemR m1 0x5a5a5a5a /\ bv_unsigned s4 = 0.
Proof.
  intros m1 s4 MX H4 EA. apply MemX_R in MX. rewrite EA in MX, H4. cbn [fst snd written_or] in MX, H4.
  split; [exact MX | exact H4].
Qed.

(** 0x142a4 .. 0x142b4: `at < n_ent`, else no pair is left (check_absent). *)
Lemma outer_ok : forall j, ((j < n)%nat -> inner_P j) -> outer_P j.
Proof.
  intros j HI. unfold outer_P.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s4 s6 s11 t3 t4 t5 t6 F fc m1 HF MX H4 HE Hj -> -> ->.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  (* 0x142a4 bge s6,s2 *)
  step. rewrite lts_s by lia.
  destruct (Z.ltb_spec (Z.of_nat j) (Z.of_nat n)) as [Hl|Hl]; cbn [negb]; cbv beta iota.
  - (* 0x142a8 addi s1,s6,-1; mul a3,s6,a4; addi s6,s6,1; add a3,s10,a3 *)
    step. step. step. step.
    eapply (HI ltac:(lia)); [exact HF | exact MX | exact H4 | exact HE | lia | weq | weq | weq | reflexivity | reflexivity].
  - assert (EA : E0 = (None, 0)) by (rewrite HE, skipn_all2 by lia; reflexivity).
    destruct (none_left m1 s4 MX H4 EA) as [MR H40].
    eapply absent_ok; [exact HF | exact MR | exact H40].
Qed.

(** 0x142e4 .. 0x142fc: ent[j] is not a key: the next entry, or no pair is left. *)
Lemma nokey_ok : forall j, (j < n)%nat -> ((S j < n)%nat -> inner_P (S j)) ->
  forall (ra t0 t1 t2 s0 a0 a1 a2 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte),
  frm0 fc -> MemX m1 (pp + 16404) (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  E0 = rate_of_pairs expect_value (pairs_by key_of (skipn (S j) es) None) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.of_nat j - 1)) a0 a1 a2 (Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat j))
             (Z_to_bv 64 104) a5 a6 a7 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 pod) s4 (Z_to_bv 64 0x1045e)
             (Z_to_bv 64 (Z.of_nat j + 1)) (Z_to_bv 64 mask) (Z_to_bv 64 8) (Z_to_bv 64 (-1))
             (Z_to_bv 64 (pp + 16412)) (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x142e4) fc None m1 (seg_rom rsegs)).
Proof.
  intros j Hj HI ra t0 t1 t2 s0 a0 a1 a2 a5 a6 a7 s4 t3 t4 t5 t6 F fc m1 HF MX H4 HE.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  (* 0x142e4 mv a0,zero; add a2,s11,s1; beq a2,s9 *)
  step. step. step. rewrite eqb_s by lia.
  destruct (Z.eqb_spec (1 - Z.of_nat n + (Z.of_nat j - 1)) (-1)) as [Ee|Ee]; cbv beta iota.
  - assert (EA : E0 = (None, 0)) by (rewrite HE, skipn_all2 by lia; reflexivity).
    destruct (none_left m1 s4 MX H4 EA) as [MR H40].
    eapply absent_ok; [exact HF | exact MR | exact H40].
  - (* 0x142f0 addi s1,s1,1; addiw s6,s6,1; addi a3,a3,0x68; beqz a0 *)
    step. step. step. step. if_true.
    eapply (HI ltac:(lia)); [exact HF | exact MX | exact H4 | exact HE | lia | weq | weq | weq | reflexivity | reflexivity].
Qed.

(** 0x142e8 .. 0x14310: ent[j] is a key k: no value after it, or strcmp(k, "reac.cfg.rate"). *)
Lemma key_ok : forall j k, (j < n)%nat -> ((S (S j) < n)%nat -> inner_P (S (S j))) ->
  forall (ra t0 t1 t2 s0 a1 a2 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte),
  frm0 fc -> MemX m1 (pp + 16404) (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  E0 = rate_of_pairs expect_value (pairs_by key_of (skipn (S j) es) (Some k)) ->
  bytes_at rsegs m1 (pp + 16412 + 104 * Z.of_nat j) (k ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) k ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.of_nat j - 1)) (Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat j)) a1 a2
             (Z_to_bv 64 (pp + 16412 + 104 * Z.of_nat j))
             (Z_to_bv 64 104) a5 a6 a7 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 pod) s4 (Z_to_bv 64 0x1045e)
             (Z_to_bv 64 (Z.of_nat j + 1)) (Z_to_bv 64 mask) (Z_to_bv 64 8) (Z_to_bv 64 (-1))
             (Z_to_bv 64 (pp + 16412)) (Z_to_bv 64 (1 - Z.of_nat n)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x142e8) fc None m1 (seg_rom rsegs)).
Proof.
  intros j k Hj HI ra t0 t1 t2 s0 a1 a2 a5 a6 a7 s4 t3 t4 t5 t6 F fc m1 HF MX H4 HE HK HNK.
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof MX as (MT & HPPB & H80 & Hb0 & HC & H18 & H20 & TM). pose proof MT as (_ & _ & MI & _).
  (* 0x142e8 add a2,s11,s1; beq a2,s9 *)
  step. step. rewrite eqb_s by lia.
  destruct (Z.eqb_spec (1 - Z.of_nat n + (Z.of_nat j - 1)) (-1)) as [Ee|Ee]; cbv beta iota.
  { assert (EA : E0 = (None, 0)) by (rewrite HE, skipn_all2 by lia; reflexivity).
    destruct (none_left m1 s4 MX H4 EA) as [MR H40].
    eapply absent_ok; [exact HF | exact MR | exact H40]. }
  (* 0x142f0 addi s1,s1,1; addiw s6,s6,1; addi a3,a3,0x68; beqz a0 *)
  step. step. step. step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x14300 blt s1,s9 *)
  step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x14304 mv a1,s5; jal strcmp *)
  step. step.
  eapply evt_cut.
  { eapply STRC with (sx := k) (sy := RATE_KEY).
    - rewrite unsigned_lit by lia. exact HK.
    - exact HNK.
    - change (bv_unsigned (Z_to_bv 64 0x1045e)) with 0x1045e. exact (rate_key_at m1 MI).
    - exact rate_key_no_nul. }
  intros ms' (rr & x11 & x12 & x13 & E & Hr). subst ms'. ret_even.
  rewrite (skipn_nth_cons es (S j) (Ent 0 0 [])) in HE by lia. rewrite rop_some in HE.
  (* 0x1430c addi a4,zero,0x68 *)
  step.
  revert HE. destruct (bytes_eqb k RATE_KEY) eqn:EK; intros HE.
  - (* the rate key: 0x14310 bnez a0 not taken *)
    apply bytes_eqb_eq in EK. rewrite (proj2 Hr EK).
    step. if_false.
    eapply value_ok with (j := j); [exact HF | exact MX | exact H4 | lia | exact HE | weq].
  - (* another key: back to the outer loop with at = j + 2 *)
    assert (Hrr : bv_eqb rr (Z_to_bv 64 0) = false).
    { destruct (bv_eqb rr (Z_to_bv 64 0)) eqn:X; [|reflexivity]. apply bv_eqb_true in X. apply Hr in X. subst k.
      rewrite (proj2 (bytes_eqb_eq RATE_KEY RATE_KEY) eq_refl) in EK. discriminate. }
    step. rewrite Hrr. cbn [negb]. cbv beta iota.
    eapply (outer_ok (S (S j)) HI); [exact HF | exact MX | exact H4 | exact HE | lia | weq | reflexivity | reflexivity].
Qed.

(** 0x142b8 .. 0x142e0: pod_string(&pp->ent[j]) on an empty key slot. *)
Lemma inner_ok : forall K j, (n - j <= K)%nat -> inner_P j.
Proof.
  induction K as [|K IH]; intros j HK; unfold inner_P;
    intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s4 s6 s11 t3 t4 t5 t6 F fc m1 HF MX H4 HE Hj -> -> -> -> ->;
    [lia|].
  pose proof (proj1 (ents_wf r HWF)) as Hn.
  assert (HN1 : (S j < n)%nat -> inner_P (S j)) by (intros _; apply IH; lia).
  assert (HN2 : (S (S j) < n)%nat -> inner_P (S (S j))) by (intros _; apply IH; lia).
  rewrite (skipn_nth_cons es j (Ent 0 0 []) Hj), rop_cons in HE.
  pose proof (ent_wf_nth r j HWF Hj) as (Ht0 & Hb & Hsz).
  pose proof MX as (MT & HPPB & H80 & Hb0 & HC & H18 & H20 & TM).
  pose proof (bytes_at_ent rsegs m1 pp r j HPPB HWF Hj) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat j) with (pp + 16404 + 104 * Z.of_nat j) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  (* 0x142b8 lw a0,-8(a3); bne a0,s8 *)
  pose proof (ent_type_read rsegs m1 _ _ HEB Ht0) as HR. step. clear HR.
  step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth j es (Ent 0 0 []))) 8) as [Et|Et]; cbn [negb]; cbv beta iota.
  2:{ assert (EK : key_of (nth j es (Ent 0 0 [])) = None)
        by (rewrite key_of_cases; unfold POD_STRING; rewrite (proj2 (Z.eqb_neq _ _) Et); reflexivity).
      rewrite EK in HE. eapply nokey_ok; [exact Hj | exact HN1 | exact HF | exact MX | exact H4 | exact HE]. }
  (* 0x142c0 lw a0,-4(a3); beqz a0 *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR. rewrite sx32_small by lia.
  step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec (e_size (nth j es (Ent 0 0 []))) 0) as [Ez|Ez]; cbv beta iota.
  { assert (EK : key_of (nth j es (Ent 0 0 [])) = None)
      by (rewrite key_of_cases; rewrite Ez; cbn [Z.leb Z.compare]; rewrite andb_false_r; reflexivity).
    rewrite EK in HE. eapply nokey_ok; [exact Hj | exact HN1 | exact HF | exact MX | exact H4 | exact HE]. }
  (* 0x142c8 addi a0,a0,-1; slli a0,a0,32; srli a0,a0,32; add a0,a3,a0; lbu a2,0(a0) *)
  step. step. step. rewrite zext32_small by lia. step.
  pose proof (ent_byte_read rsegs m1 _ _ (Z.to_nat (e_size (nth j es (Ent 0 0 [])) - 1)) HEB ltac:(lia)) as HR.
  step. clear HR.
  (* 0x142dc mv a0,a3; beqz a2 *)
  step. step. rewrite zxb_eqb0.
  destruct (Z.eqb_spec (bv_unsigned (nth (Z.to_nat (e_size (nth j es (Ent 0 0 [])) - 1))
                                         (e_body (nth j es (Ent 0 0 []))) NUL)) 0) as [Eb|Eb]; cbv beta iota.
  - (* a key: 0x142e8 *)
    assert (EK : key_of (nth j es (Ent 0 0 [])) = Some (cstr (e_body (nth j es (Ent 0 0 []))))).
    { rewrite key_of_cases. unfold POD_STRING, last_body_byte. rewrite (proj2 (Z.eqb_eq _ _) Et), Eb.
      rewrite (proj2 (Z.leb_le 1 _)) by lia. reflexivity. }
    rewrite EK in HE.
    assert (HNI : (nul_idx (e_body (nth j es (Ent 0 0 []))) < length (e_body (nth j es (Ent 0 0 []))))%nat).
    { pose proof (nul_idx_le_k (e_body (nth j es (Ent 0 0 []))) (Z.to_nat (e_size (nth j es (Ent 0 0 [])) - 1))
                    ltac:(lia) Eb). lia. }
    pose proof (ent_key_bytes rsegs m1 _ _ HEB HNI) as HKB.
    replace (pp + 16404 + 104 * Z.of_nat j + 8) with (pp + 16412 + 104 * Z.of_nat j) in HKB by lia.
    eapply key_ok; [exact Hj | exact HN2 | exact HF | exact MX | exact H4 | exact HE | exact HKB | apply cstr_no_nul].
  - (* not NUL-terminated: 0x142e4 *)
    assert (EK : key_of (nth j es (Ent 0 0 [])) = None).
    { rewrite key_of_cases. unfold last_body_byte. rewrite (proj2 (Z.eqb_neq _ _) Eb). rewrite andb_false_r. reflexivity. }
    rewrite EK in HE. eapply nokey_ok; [exact Hj | exact HN1 | exact HF | exact MX | exact H4 | exact HE].
Qed.

(** ** The head: memcpy, the hz cell and the parse, the corrupt, NULL, is_props and params_struct tests, the
    spills, the scan's set-up *)
Hypothesis HLEN : len = Z.of_nat (length (buf r)).
Hypothesis HPODA : pod mod 16 = 0.
Hypothesis HSEP : or_h (pod + len <= pp) (pp + 19744 <= pod).
Hypothesis HPM : corrupt r = false -> parse_model (buf r) = E0.

Lemma len_buf : 8 <= len <= 5440.
Proof. destruct (buf_header r HWF) as (_ & _ & _ & H). lia. Qed.

(** 0x14264 .. 0x142a0: at = 0, n = n_ent, the constants, sp + 0xb0 := &pp->ent[0]. *)
Lemma setup_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemX m1 (pp + 16384) (written_or 0x5a5a5a5a E0) -> bv_unsigned s4 = snd E0 mod 2^64 ->
  is_props r = true -> params_struct r = true ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (pp + 19732)) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 s6
             (Z_to_bv 64 mask) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14264) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MX H4 EI EP.
  pose proof (proj1 (ents_wf r HWF)) as Hn. pose proof len_pp as LP.
  pose proof MX as (MT & HPPB & H80 & Hb0 & HC & H18 & H20 & TM). pose proof MT as (MU & WM & MI & ST).
  (* 0x14264 mv s6,zero; lui a0,4; lw s2,0(a2) *)
  step. step.
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 19732)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (ents r)))))).
  { apply (read_field rsegs m1 pp r 19732 _ HPPB HWF); [exact (pp_n_ent r HWF) | lia | unfold PP_SIZE; lia | lia]. }
  step. clear HR. rewrite sx32_small by lia.
  (* 0x14270 .. 0x14288: addi a1; addi a4; addi s8; addi s9; auipc a2; addiw a3; addiw a0 *)
  step. step. step. step. step. step. step.
  (* 0x1428c ld s10,0x80(sp); add a3,s10,a3; sd a3,0xb0(sp) *)
  pose proof (read_le8 rsegs m1 (SP + 128) _ H80) as HR. step. clear HR. step.
  assert (HS : store_ok rsegs m1 (wa (SP + 176)) 8 = true)
    by exact (stk_store_ok rsegs m1 lo (SP + 440) (SP + 176) 8 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 176));
    assert (MX2 : MemX (write_to_mem m1 (wa (SP + 176)) BS) (pp + 16404) (written_or 0x5a5a5a5a E0));
    [ pose proof (length_le8 (Z_to_bv 64 pp)) as L8;
      split; [apply MemT_store; rewrite ?length_le8; [exact MT | exact HS | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8; [exact HPPB | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8; [exact H80 | lia | lia | lia]|];
      split; [apply bytes_at_write_same; rewrite ?length_le8; lia|];
      split; [apply bytes_at_write_other; rewrite ?length_le8, ?length_le4; [exact HC | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8; [exact H18 | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8; [exact H20 | lia | lia | lia]|];
      apply task_mem_write; rewrite ?length_le8; [exact TM | exact HS]
    | revert MX2; generalize (write_to_mem m1 (wa (SP + 176)) BS) as m2; intros m2 MX2 ]
  end.
  (* 0x14298 add s10,s10,a0; sub s11,a1,s2; addi s5,a2,0x1de *)
  step. step. step.
  eapply (outer_ok 0).
  - intros Hl. apply (inner_ok (length (ents r)) 0). lia.
  - exact HF.
  - exact MX2.
  - exact H4.
  - exact (expect_struct r EI EP).
  - lia.
  - weq.
  - weq.
  - weq.
Qed.

(** The memory between the parse and the spills: MemT, the record, sp + 0x80 = pp, sp + 0xb0 = pp + 0x4000, the hz
    cell c, MemNorm.task_mem. *)
Definition MemQ (m1 : word -> option byte) (c : Z) : Prop :=
  MemT m1 /\ bytes_at rsegs m1 pp (pp_bytes r) /\ bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) /\
  bytes_at rsegs m1 (SP + 176) (le8 (Z_to_bv 64 (pp + 16384))) /\ bytes_at rsegs m1 (SP + 344) (le4 (Z_to_bv 64 c)) /\
  MemNorm.task_mem rsegs m1.

Lemma MemQ_store : forall m1 c a bs, MemQ m1 c -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP <= a -> a + Z.of_nat (length bs) <= SP + 128 -> MemQ (write_to_mem m1 (wa a) bs) c.
Proof.
  intros m1 c a bs (MT & HP & H80 & Hb0 & HC & TM) HS H1 H2.
  pose proof len_pp as LP. pose proof (length_le8 (Z_to_bv 64 pp)) as L8.
  pose proof (length_le8 (Z_to_bv 64 (pp + 16384))) as L8b. pose proof (length_le4 (Z_to_bv 64 c)) as L4.
  split; [exact (MemT_store m1 a bs MT HS ltac:(lia) ltac:(lia))|].
  split; [apply bytes_at_write_other; [exact HP | lia | lia | lia]|].
  split; [apply bytes_at_write_other; [exact H80 | lia | lia | rewrite L8; lia]|].
  split; [apply bytes_at_write_other; [exact Hb0 | lia | lia | rewrite L8b; lia]|].
  split; [apply bytes_at_write_other; [exact HC | lia | lia | rewrite L4; lia]|].
  exact (task_mem_write rsegs m1 (wa a) bs TM HS).
Qed.

(** One spill `sd x, off(sp)` below sp + 0x80 (0x14248 s2 -> 0x30, 0x1424c s7 -> 0x10): the memory stays MemQ. *)
Ltac spill1 off :=
  lazymatch goal with
  | MQ : MemQ ?m1 ?c |- _ =>
      let ST := fresh "ST" in pose proof MQ as ((_ & _ & _ & ST) & _);
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs m1 (wa (SP + off)) 8 = true)
        by exact (stk_store_ok rsegs m1 lo (SP + 440) (SP + off) 8 ST ltac:(lia) ltac:(lia));
      step;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
        change A with (wa (SP + off));
        let MQ2 := fresh "MQ" in
        assert (MQ2 : MemQ (write_to_mem m1 (wa (SP + off)) BS) c)
          by (apply MemQ_store; rewrite ?length_le8; [exact MQ | exact HS | lia | lia]);
        clear ST HS MQ; revert MQ2; generalize (write_to_mem m1 (wa (SP + off)) BS); intros ?m MQ
      end
  end.

(** 0x14228 .. 0x14260: corrupt, the NULL flag, is_props, the spills, params_struct. *)
Lemma after_parse : forall (ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s11 t3 t4 t5 t6 : word)
                           (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemQ m1 (written_or 0x5a5a5a5a (harness_parse (Z.testbit fl 0) (buf r))) ->
  bytes_at rsegs m1 (SP + 112) (le8 (Z_to_bv 64 (pp + 19732))) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fl)) 1))
             (Z_to_bv 64 (snd (harness_parse (Z.testbit fl 0) (buf r)))) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5
             (Z_to_bv 64 fl) s7 s8 (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14228) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s11 t3 t4 t5 t6 F fc m1 HF MQ H70.
  pose proof len_pp as LP.
  pose proof MQ as (MT & HPPB & H80 & Hb0 & HC & TM).
  (* 0x14228 ld a2,0x70(sp); lw a1,4(a2); mv s4,a0; bnez a1 *)
  pose proof (read_le8 rsegs m1 (SP + 112) _ H70) as HR. step. clear HR.
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 19736)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (corrupt r))))).
  { apply (read_field rsegs m1 pp r 19736 _ HPPB HWF);
      [exact (pp_corrupt r HWF) | lia | unfold PP_SIZE; lia | destruct (corrupt r); cbn; lia]. }
  revert HR. destruct (corrupt r) eqn:EC; cbn [Z.b2z]; intros HR.
  { (* corrupted: no check, 0x143dc *)
    step. clear HR. rewrite sx32_small by lia. step. step. if_true.
    apply decide_ok; [exact HF | exact MT | exact H80]. }
  step. clear HR. rewrite sx32_small by lia. step. step. if_false.
  (* 0x14238 ld a1,0xb0(sp); bnez s1 *)
  pose proof (read_le8 rsegs m1 (SP + 176) _ Hb0) as HR. step. clear HR.
  step. rewrite (unsigned_lit fl) by lia. rewrite (land1_bit fl HFL).
  revert MQ HC. destruct (Z.testbit fl 0) eqn:EB; intros MQ HC; cbv beta iota.
  { (* the NULL argument: check_malformed *)
    if_true. cbn [harness_parse fst snd written_or] in HC |- *.
    eapply malformed_ok; [exact HF | exact MT | exact H80 | exact HC | reflexivity]. }
  if_false. change (harness_parse false (buf r)) with (parse_model (buf r)) in MQ, HC |- *.
  rewrite HPM in MQ, HC |- * by first [exact EC | reflexivity].
  (* 0x14240 lw a0,8(a1); beqz a0 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 16392)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (is_props r))))).
  { apply (read_field rsegs m1 pp r 16392 _ HPPB HWF);
      [exact (pp_is_props r HWF) | lia | unfold PP_SIZE; lia | destruct (is_props r); cbn; lia]. }
  revert HR. destruct (is_props r) eqn:EI; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      rewrite (expect_not_props r EI) in HC |- *. cbn [fst snd written_or] in HC |- *.
      eapply malformed_ok; [exact HF | exact MT | exact H80 | exact HC | reflexivity]. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  clear MT HPPB H80 Hb0 HC TM H70.
  (* 0x14248 sd s2,0x30(sp); 0x1424c sd s7,0x10(sp) *)
  spill1 48. spill1 16.
  (* 0x14250 sd s6,0x18(sp): the spill of fl *)
  lazymatch goal with
  | MQ : MemQ ?m3 ?c |- _ =>
      pose proof MQ as ((_ & _ & _ & ST) & _);
      assert (HS : store_ok rsegs m3 (wa (SP + 24)) 8 = true)
        by exact (stk_store_ok rsegs m3 lo (SP + 440) (SP + 24) 8 ST ltac:(lia) ltac:(lia));
      step;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m3 ?A ?BS) _) =>
        change A with (wa (SP + 24));
        assert (MQ4 : MemQ (write_to_mem m3 (wa (SP + 24)) BS) c)
          by (apply MemQ_store; rewrite ?length_le8; [exact MQ | exact HS | lia | lia]);
        assert (H18 : bytes_at rsegs (write_to_mem m3 (wa (SP + 24)) BS) (SP + 24) (le8 (Z_to_bv 64 fl)))
          by (apply bytes_at_write_same; rewrite ?length_le8; lia);
        clear ST HS MQ; revert MQ4 H18; generalize (write_to_mem m3 (wa (SP + 24)) BS) as m4; intros m4 MQ H18
      end
  end.
  (* 0x14254 sd s10,0x20(sp): the spill of buflen *)
  pose proof MQ as ((_ & _ & _ & ST) & _).
  assert (HS : store_ok rsegs m4 (wa (SP + 32)) 8 = true)
    by exact (stk_store_ok rsegs m4 lo (SP + 440) (SP + 32) 8 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m4 ?A ?BS) _) =>
    change A with (wa (SP + 32));
    assert (MX : MemX (write_to_mem m4 (wa (SP + 32)) BS) (pp + 16384) (written_or 0x5a5a5a5a E0));
    [ destruct MQ as (MT & HPPB & H80 & Hb0 & HC & TM);
      pose proof (length_le8 (Z_to_bv 64 pp)) as L8;
      split; [apply MemT_store; rewrite ?length_le8; [exact MT | exact HS | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8; [exact HPPB | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8; [exact H80 | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8; [exact Hb0 | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8, ?length_le4; [exact HC | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le8; [exact H18 | lia | lia | lia]|];
      split; [apply bytes_at_write_same; rewrite ?length_le8; lia|];
      apply task_mem_write; rewrite ?length_le8; [exact TM | exact HS]
    | clear ST HS MQ H18; revert MX; generalize (write_to_mem m4 (wa (SP + 32)) BS) as m5; intros m5 MX ]
  end.
  pose proof MX as (MT & HPPB & H80 & Hb0 & HC & H18 & H20 & TM).
  (* 0x14258 mv s7,s9; lw a0,0x10(a1); beqz a0 *)
  step.
  assert (HR : ov_read_bytes rsegs m5 (wa (pp + 16400)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (params_struct r))))).
  { apply (read_field rsegs m5 pp r 16400 _ HPPB HWF);
      [exact (pp_params_struct r HWF) | lia | unfold PP_SIZE; lia | destruct (params_struct r); cbn; lia]. }
  revert HR. destruct (params_struct r) eqn:EP; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      apply MemX_R in MX. rewrite (expect_no_struct r EI EP) in MX |- *. cbn [fst snd written_or] in MX |- *.
      eapply absent_ok; [exact HF | exact MX | reflexivity]. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  eapply setup_ok; [exact HF | exact MX | apply unsigned_lit_wrap | exact EI | exact EP].
Qed.

Hypothesis MCPY : memcpy_contract.
Hypothesis PARSE : rate_prop_parse_contract.

(** The parse's memory: its frame, and the hz cell when it writes a rate. *)
Lemma MemQ_parse : forall m2 m3 o, MemQ m2 0x5a5a5a5a -> bytes_at rsegs m2 (SP + 112) (le8 (Z_to_bv 64 (pp + 19732))) ->
  rate_mem m2 m3 SP (SP + 344) o -> wmono rsegs m2 m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo SP ->
  MemQ m3 (written_or 0x5a5a5a5a (o, 0)) /\ bytes_at rsegs m3 (SP + 112) (le8 (Z_to_bv 64 (pp + 19732))).
Proof.
  intros m2 m3 o (MT & HPPB & H80 & Hb0 & HC & TM) H70 RM WM3 MI3 ST3. pose proof len_pp as LP.
  pose proof MT as (_ & _ & _ & ST).
  destruct o as [w|]; cbn [rate_mem written_or fst] in RM |- *.
  - destruct RM as (MU3 & HW). unfold PARSE_FRAME in MU3.
    split; [|apply (bytes_at_transport rsegs _ m2 m3 _ _ H70 MU3); cbn [disjoint_from]; rewrite length_le8;
             repeat split; lia].
    split.
    { apply (MemT_call m2 m3 _ MT MU3 WM3 MI3 ST3).
      - unfold sub_fp, WC. cbn [outside]. intros x (O1 & _ & _). repeat split; try exact I; lia.
      - intros x Hx. destruct (Z_lt_le_dec x (SP + 344)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; lia|].
        destruct (Z_lt_le_dec x (SP + 348)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; lia].
        apply (bytes_at_some rsegs m3 (SP + 344) _ x HW); rewrite length_le4; [intros a Ha; apply HROM | ]; lia. }
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HPPB MU3); cbn [disjoint_from]; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ H80 MU3); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ Hb0 MU3); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [exact HW|].
    apply (task_mem_munch rsegs _ m2 m3 TM MU3). apply (stk_wview rsegs m2 lo (SP + 440)); [exact ST|].
    intros x Hx. cbn [outside] in Hx. lia.
  - unfold PARSE_FRAME in RM.
    split; [|apply (bytes_at_transport rsegs _ m2 m3 _ _ H70 RM); cbn [disjoint_from]; rewrite length_le8;
             repeat split; lia].
    split; [apply (MemT_below m2 m3 80 MT RM WM3 MI3 ST3); lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HPPB RM); cbn [disjoint_from]; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ H80 RM); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ Hb0 RM); cbn [disjoint_from]; rewrite length_le8; repeat split; lia|].
    split; [apply (bytes_at_transport rsegs _ m2 m3 _ _ HC RM); cbn [disjoint_from]; rewrite length_le4; repeat split; lia|].
    apply (task_mem_munch rsegs _ m2 m3 TM RM). apply (stk_wview rsegs m2 lo (SP + 440)); [exact ST|].
    intros x Hx. cbn [outside] in Hx. lia.
Qed.

(** 0x14200 .. 0x14224: hz := 0x5a5a5a5a, rc = reac_rate_prop_parse(fl & 1 ? NULL : pod, &hz). *)
Lemma after_cpy : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s11 t3 t4 t5 t6 : word)
                         (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemT m1 -> bytes_at rsegs m1 pp (pp_bytes r) -> bytes_at rsegs m1 (SP + 128) (le8 (Z_to_bv 64 pp)) ->
  bytes_at rsegs m1 (SP + 176) (le8 (Z_to_bv 64 (pp + 16384))) ->
  bytes_at rsegs m1 (SP + 112) (le8 (Z_to_bv 64 (pp + 19732))) -> MemNorm.task_mem rsegs m1 ->
  bytes_at rsegs m1 pod (buf r) ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 pod) s4 s5 (Z_to_bv 64 fl) s7 s8
             (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14200) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s11 t3 t4 t5 t6 F fc m1 HF MT HPPB H80 Hb0 H70 TM HPB.
  pose proof len_pp as LP. pose proof len_buf as LB. pose proof (buf_header r HWF) as (_ & _ & HU & _).
  pose proof MT as (MU & WM & MI & ST).
  (* 0x14200 ld a0,0x28(sp); or s0,a0,s11; lui a0,0x5a5a6; andi s1,s6,1; addi a0,a0,-0x5a6; sw a0,0x158(sp) *)
  destruct (stk_read rsegs m1 lo (SP + 440) (SP + 40) 8 ST ltac:(lia) ltac:(lia)) as (bs0 & HR). step. clear HR.
  step. step. step. step.
  assert (HS : store_ok rsegs m1 (wa (SP + 344)) 4 = true)
    by exact (stk_store_ok rsegs m1 lo (SP + 440) (SP + 344) 4 ST ltac:(lia) ltac:(lia)).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 344));
    assert (MQ2 : MemQ (write_to_mem m1 (wa (SP + 344)) BS) 0x5a5a5a5a);
    [ split; [apply MemT_store; rewrite ?length_le4; [exact MT | exact HS | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le4; [exact HPPB | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H80 | lia | lia | lia]|];
      split; [apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact Hb0 | lia | lia | lia]|];
      split; [apply bytes_at_write_same; rewrite ?length_le4; lia|];
      apply task_mem_write; rewrite ?length_le4; [exact TM | exact HS]
    | assert (H702 : bytes_at rsegs (write_to_mem m1 (wa (SP + 344)) BS) (SP + 112) (le8 (Z_to_bv 64 (pp + 19732))))
        by (apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H70 | lia | lia | lia]);
      assert (HPB2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 344)) BS) pod (buf r))
        by (apply bytes_at_write_other; rewrite ?length_le4; [exact HPB | lia | lia | lia]);
      revert MQ2 H702 HPB2; generalize (write_to_mem m1 (wa (SP + 344)) BS) as m2; intros m2 MQ2 H702 HPB2 ]
  end.
  clear MU WM MI ST MT HPPB H80 Hb0 H70 TM HS.
  pose proof MQ2 as (MT & HPPB & H80 & Hb0 & HC & TM). pose proof MT as (MU & WM & MI & ST).
  (* 0x14218 addi a0,s1,-1; and a0,a0,s3; addi a1,sp,0x158; jal reac_rate_prop_parse *)
  step. step. step. step.
  eapply evt_cut.
  { eapply PARSE with (null := Z.testbit fl 0) (lo := lo) (P := pod) (Q := SP + 344) (bs := buf r).
    - f_equal. apply parse_arg; lia.
    - reflexivity.
    - unfold rate_args. split; [exact HPB2|]. split; [lia|]. split; [exact HPODA|]. split; [lia|].
      split; [exact HU|]. split; [lia|].
      split; [apply (stk_wr_at rsegs m2 lo (SP + 440)); [exact ST | lia | lia | lia]|]. split; lia.
    - exact (MemT_stk m2 MT).
    - unfold PARSE_FRAME. lia.
    - intros a Ha. apply HROM. lia.
    - exact HF.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m3 &
              E & HFk & HF' & RM & WM3 & MI3 & ST3).
  subst ms'. ret_even.
  destruct (MemQ_parse m2 m3 _ MQ2 H702 RM WM3 MI3 ST3) as [MQ3 H703].
  eapply after_parse; [exact HF' | exact MQ3 | exact H703].
Qed.

(** 0x141e4 .. 0x141fc: pod <> 0; memcpy(pod, pp, len) (len >= 8). *)
Lemma head_ok : forall (ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (junk : list byte),
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> stk rsegs m lo (SP + 440) ->
  bytes_at rsegs m pp (pp_bytes r) -> bytes_at rsegs m (SP + 128) (le8 (Z_to_bv 64 pp)) ->
  bytes_at rsegs m (SP + 176) (le8 (Z_to_bv 64 (pp + 16384))) ->
  bytes_at rsegs m (SP + 112) (le8 (Z_to_bv 64 (pp + 19732))) -> rw_cells rsegs m pod [CB (Z.to_nat len) junk] ->
  evt rsegs QC
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pp) (Z_to_bv 64 pod) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 len) s5
             (Z_to_bv 64 fl) s7 s8 (Z_to_bv 64 mask) (Z_to_bv 64 buflen) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141e4) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s11 t3 t4 t5 t6 F fc junk HF HMI HTM HST HPPB H80 Hb0 H70
    HPC.
  pose proof len_pp as LP. pose proof len_buf as LB. pose proof HST as (HS0 & HS1 & _).
  (* 0x141e4 beqz a0; mv s3,a0; beqz s4 *)
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  step. step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x141f0 mv a0,s3; mv a1,s1; mv a2,s4; jal memcpy *)
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
  assert (DJ : forall A k, lo <= A -> A + k <= SP + 440 -> disjoint_from [(pod, pod + len)] A k)
    by (intros A k H1 H2; cbn [disjoint_from]; split; [lia | exact I]).
  eapply after_cpy.
  - exact HF.
  - exact MT1.
  - apply (bytes_at_transport rsegs _ m m1 _ _ HPPB MU1). cbn [disjoint_from]. unfold or_h in HSEP. split; [lia | exact I].
  - apply (bytes_at_transport rsegs _ m m1 _ _ H80 MU1). rewrite length_le8. apply DJ; lia.
  - apply (bytes_at_transport rsegs _ m m1 _ _ Hb0 MU1). rewrite length_le8. apply DJ; lia.
  - apply (bytes_at_transport rsegs _ m m1 _ _ H70 MU1). rewrite length_le8. apply DJ; lia.
  - apply (task_mem_munch rsegs _ m m1 HTM MU1). intros x Hx. cbn [outside] in Hx.
    destruct (rw_cells_bound rsegs m pod _ HPC) as [B1 B2]. cbn [cells_size csize] in B2.
    destruct HPC as [_ (W0 & W1 & W)]. cbn [cells_size csize] in W.
    pose proof (W (bv_unsigned x - pod)) as Wx. replace (pod + (bv_unsigned x - pod)) with (bv_unsigned x) in Wx by lia.
    unfold wa in Wx. rewrite Z_to_bv_lit_self in Wx. apply Wx. lia.
  - exact (rw_cells_CB_bytes rsegs m1 pod _ _ CB1).
Qed.

End Check.
