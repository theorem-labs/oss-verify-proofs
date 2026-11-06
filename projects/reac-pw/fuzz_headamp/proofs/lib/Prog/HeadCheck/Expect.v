(** expect_of(pp, null, cap, &x) inlined in the plain LLVMFuzzerTestOneInput (fuzz_headamp.c:109-157), 0x140f0 ->
    0x14108: Prog/HeadCheck/Cut.v's [expect_stmt], from memset_contract, strncmp_contract and [key_stmt]. The
    Section fixes the frame (sp, gp, tp and the callee-saved s1, s3-s6), the entry memory m, the record r at pp,
    the NULL flag nl, cap, lo, the continuation Q and its answer E = Pod/Headamp.v [expect_model] (nl = 1) cap r.
    Walked backwards: [exit_z] (0x14108 with no cell: the NULL flag, not props, no params, no entries),
    [setup_ok] (0x14220: is_props, params_struct and n_ent through the cell sp + 0x50 = &pp->len, then the
    constants of the loop 0x1423c-0x142b0 and Prog/HeadCheck/Pairs.v's [pairs_loop]), [entry_ok] (0x140f0:
    memset(x, 0, 0x88), s0 := -1, `beqz s7`). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c
  strncmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts Cut PairFacts Pairs.
Import ListNotations.
Open Scope Z_scope.

(* A register equation at a cut whose value is a folded literal or a small sum. *)
Ltac leq := first [ reflexivity | (apply bv_eq; reflexivity) | weq | (apply Z_to_bv_eqm; reflexivity) ].

(** x right after memset(x, 0, 0x88): x->rc, then x past x->rc for no cell, no key, no refusal. *)
Lemma zeros136 : repeat (Z_to_bv 8 0) 136 =
  repeat (Z_to_bv 8 0) 4 ++ x_cellz [] ++ le4 (Z_to_bv 64 (Z.of_nat (length ([] : list cell)))) ++
  le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 REFUSE_NONE).
Proof. vm_compute. reflexivity. Qed.

Lemma zeros_tail : repeat (Z_to_bv 8 0) 136 = repeat (Z_to_bv 8 0) 4 ++ repeat (Z_to_bv 8 0) 132.
Proof. rewrite <- repeat_app. reflexivity. Qed.

Section Expect.
Variables (sp gp tp s1 s3 s4 s5 s6 : word) (m : word -> option byte) (r : pod_rec) (nl cap pp lo : Z)
          (Q : machine_state -> Prop) (E : answer).

Local Abbreviation SP := (bv_unsigned sp).

Hypothesis HWF : pod_rec_wf r.
Hypothesis HNL : 0 <= nl <= 1.
Hypothesis HCAP : 0 <= cap <= 9.
Hypothesis HPP0 : 0 <= pp.
Hypothesis HPPLO : pp + POD_PROPS <= lo.
Hypothesis HST : stk rsegs m lo (SP + FRAME_LOCALS).
Hypothesis HLO : lo + NEAR_STACK <= SP.
Hypothesis HSPA : SP mod 16 = 0.
Hypothesis HROM : forall a, lo <= a < SP + FRAME_LOCALS -> seg_rom rsegs (wa a) = None.
Hypothesis HMI : mem_inv rsegs m.
Hypothesis HTM : MemNorm.task_mem rsegs m.
Hypothesis HPPB : bytes_at rsegs m pp (pp_bytes r).
Hypothesis HM50 : bytes_at rsegs m (SP + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))).
Hypothesis HM58 : bytes_at rsegs m (SP + 0x58) (le8 (Z_to_bv 64 pp)).
Hypothesis KEY : key_stmt.
Hypothesis STRN : strncmp_contract.
Hypothesis MSET : memset_contract.
Hypothesis HEdef : E = expect_model (nl =? 1) cap r.
Hypothesis HQ : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
  frm0 fc' ->
  munch (EXPECT_W SP) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
  stk rsegs m' lo (SP + FRAME_LOCALS) ->
  bytes_at rsegs m' (SP + 0x94) (x_tail E) ->
  evt rsegs Q
    (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 (ans_rc E)) s1
             a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 cap) s3 s4 s5 s6 s7' s8' s9' s10' s11' t3' t4' t5' t6')
        F' (Z_to_bv 64 0x14108) fc' None m' (seg_rom rsegs)).

Lemma bnde : 0 <= pp /\ pp + 19744 <= lo /\ 0 <= lo /\ lo + 48 <= SP /\ SP + 432 <= 2^64 /\ 0 <= cap <= 9 /\
             (length (ents r) <= 32)%nat.
Proof.
  pose proof HST as (H0 & H1 & _). pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof HPPLO as H2. pose proof HLO as H3. unfold POD_PROPS, NEAR_STACK, FRAME_LOCALS in *. lia.
Qed.

Lemma len_ppe : Z.of_nat (length (pp_bytes r)) = 19744.
Proof. exact (length_pp_bytes r HWF). Qed.

(** ** The memory of the set-up: changed only in EXPECT_W, the record, the cell sp + 0x58 = pp, and x all zero. *)
Definition MemS0 (m1 : word -> option byte) : Prop :=
  munch (EXPECT_W SP) m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ MemNorm.task_mem rsegs m1 /\
  stk rsegs m1 lo (SP + FRAME_LOCALS) /\ bytes_at rsegs m1 pp (pp_bytes r) /\
  bytes_at rsegs m1 (SP + 0x58) (le8 (Z_to_bv 64 pp)) /\ bytes_at rsegs m1 (SP + 0x90) (repeat (Z_to_bv 8 0) 136).

(** A store of the constants into [sp + 0x50, sp + 0x90) apart from the cell sp + 0x58. *)
Lemma MemS0_store : forall m1 a bs, MemS0 m1 -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP + 0x50 <= a -> a + Z.of_nat (length bs) <= SP + 0x90 ->
  a + Z.of_nat (length bs) <= SP + 0x58 \/ SP + 0x60 <= a ->
  MemS0 (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs (MU & WM & MI & TM & ST & HP & H58 & HZ) HS H1 H2 H3.
  pose proof bnde as (B1 & B2 & B3 & B4 & B5 & _). pose proof len_ppe as LP.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - apply munch_write; [exact MU | lia | lia |]. unfold EXPECT_W. cbn [inside].
    destruct H3 as [H3|H3]; [right; left; lia | right; right; left; lia].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HS].
  - apply task_mem_write; [exact TM | exact HS].
  - apply stk_write; [exact ST | lia | lia].
  - apply bytes_at_write_other; [exact HP | lia | lia | lia].
  - apply bytes_at_write_other; rewrite ?length_le8; [exact H58 | lia | lia | lia].
  - apply bytes_at_write_other; rewrite ?repeat_length; [exact HZ | lia | lia | lia].
Qed.

(** ** 0x14108 with no cell: x->rc = rc, x past x->rc all zero *)
Lemma exit_z : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (rc : Z),
  frm0 fc -> MemS0 m1 -> E = (rc, [], (0, 0, REFUSE_NONE)) -> s0 = Z_to_bv 64 rc ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x14108) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 rc HF
    (MU & WM & MI & TM & ST & _ & _ & HZ) HE ->.
  replace rc with (ans_rc E) by (rewrite HE; reflexivity).
  apply HQ; try assumption.
  rewrite HE, x_tail_empty. rewrite zeros_tail in HZ. apply bytes_at_app in HZ as [_ HZ].
  rewrite repeat_length in HZ. replace (SP + 0x90 + Z.of_nat 4) with (SP + 0x94) in HZ by lia. exact HZ.
Qed.

(** The loop's first head, its registers by equations. *)
Lemma loop_entry : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                          (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> FPinv F -> MemL sp m r pp lo m1 [] 0 REFUSE_NONE -> (0 < length (ents r))%nat ->
  E = expect_model false cap r -> is_props r = true -> params_struct r = true ->
  t0 = Z_to_bv 64 (Z.of_nat (length (ents r))) -> t1 = Z_to_bv 64 104 -> t2 = Z_to_bv 64 8 -> s0 = Z_to_bv 64 0 ->
  a2 = Z_to_bv 64 (pp + 16412) -> s7 = Z_to_bv 64 (-1) -> s8 = Z_to_bv 64 0 ->
  s11 = Z_to_bv 64 (1 - Z.of_nat (length (ents r))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x142b4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF HFP ML Hn HE EI EP
    -> -> -> -> -> -> -> ->.
  eapply pairs_loop; try eassumption.
  rewrite HE. unfold expect_model. rewrite EI, EP. reflexivity.
Qed.

(** ** 0x14220 .. 0x142b0: is_props, params_struct, n_ent; the loop's constants *)
Lemma setup_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS0 m1 -> bytes_at rsegs m1 (SP + 0x50) (le8 (Z_to_bv 64 (pp + 16384))) ->
  E = expect_model false cap r -> s0 = Z_to_bv 64 (-1) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6 s7
             (Z_to_bv 64 (pp + 19732)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14220) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MS0h H50 HE ->.
  pose proof bnde as (B1 & B2 & B3 & B4 & B5 & B6 & Hn32). pose proof len_ppe as LP.
  pose proof MS0h as (MU & WM & MI & TM & ST & HP & H58 & HZ).
  (* 0x14220 ld a1,0x50(sp) *)
  pose proof (read_le8 rsegs m1 (SP + 80) _ H50) as HR. step. clear HR.
  (* 0x14224 lw a0,8(a1); beqz a0 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 16392)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (is_props r))))).
  { apply (read_field rsegs m1 pp r 16392 _ HP HWF);
      [exact (pp_is_props r HWF) | lia | unfold PP_SIZE; lia | destruct (is_props r); cbn; lia]. }
  revert HR. destruct (is_props r) eqn:EI; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      eapply exit_z with (rc := -1); [exact HF | exact MS0h | rewrite HE; unfold expect_model; rewrite EI; reflexivity
                                     | leq]. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  (* 0x1422c lw a0,0x10(a1); beqz a0 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 16400)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (params_struct r))))).
  { apply (read_field rsegs m1 pp r 16400 _ HP HWF);
      [exact (pp_params_struct r HWF) | lia | unfold PP_SIZE; lia | destruct (params_struct r); cbn; lia]. }
  revert HR. destruct (params_struct r) eqn:EP; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      (* 0x14674 mv s0,zero; j 0x14108 *)
      step. step.
      eapply exit_z with (rc := 0); [exact HF | exact MS0h | rewrite HE; unfold expect_model; rewrite EI, EP; reflexivity
                                    | leq]. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  (* 0x14234 lw t0,0(s8); blez t0 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 19732)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (ents r)))))).
  { apply (read_field rsegs m1 pp r 19732 _ HP HWF); [exact (pp_n_ent r HWF) | lia | unfold PP_SIZE; lia | lia]. }
  step. clear HR. rewrite sx32_small by lia.
  step. rewrite lts_s by lia.
  destruct (Z.ltb_spec 0 (Z.of_nat (length (ents r)))) as [Hn|Hn]; cbn [negb]; cbv beta iota.
  2:{ (* 0x14674 mv s0,zero; j 0x14108 *)
      step. step.
      eapply exit_z with (rc := 0); [exact HF | exact MS0h | | leq].
      rewrite HE. unfold expect_model. rewrite EI, EP.
      destruct (ents r) as [|e0 l0] eqn:Ee; [reflexivity | cbn [length] in Hn; lia]. }
  (* 0x1423c .. 0x14280: the constants *)
  do 18 step.
  (* 0x14284 sd a1,0x88(sp) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 136)) 8 = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 0x88));
    assert (MS2 : MemS0 (write_to_mem m1 (wa (SP + 0x88)) BS))
      by (apply MemS0_store; rewrite ?length_le8; [exact MS0h | exact HS | lia | lia | lia]);
    assert (C88 : bytes_at rsegs (write_to_mem m1 (wa (SP + 0x88)) BS) (SP + 0x88) (le8 (Z_to_bv 64 PREFIX_AT)))
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    revert MS2 C88; generalize (write_to_mem m1 (wa (SP + 0x88)) BS) as m2; intros m2 MS2 C88
  end.
  clear MU WM MI TM ST HP H58 HZ HS MS0h H50.
  pose proof MS2 as (_ & _ & _ & _ & ST & _).
  (* 0x14288 addiw a1,a3,0x240; sd a1,0x70(sp) *)
  step.
  assert (HS : store_ok rsegs m2 (wa (SP + 112)) 8 = true)
    by (apply (stk_store_ok rsegs m2 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m2 ?A ?BS) _) =>
    change A with (wa (SP + 0x70));
    assert (MS3 : MemS0 (write_to_mem m2 (wa (SP + 0x70)) BS))
      by (apply MemS0_store; rewrite ?length_le8; [exact MS2 | exact HS | lia | lia | lia]);
    assert (C70 : bytes_at rsegs (write_to_mem m2 (wa (SP + 0x70)) BS) (SP + 0x70) (le8 (Z_to_bv 64 RC_BIG)))
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    assert (C88' : bytes_at rsegs (write_to_mem m2 (wa (SP + 0x70)) BS) (SP + 0x88) (le8 (Z_to_bv 64 PREFIX_AT)))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact C88 | lia | lia | lia]);
    revert MS3 C70 C88'; generalize (write_to_mem m2 (wa (SP + 0x70)) BS) as m3; intros m3 MS3 C70 C88'
  end.
  clear ST HS MS2 C88.
  pose proof MS3 as (_ & _ & _ & _ & ST & _).
  (* 0x14290 fmv.w.x fs2,a5; slli a6,a6,0x25; sd a6,0x60(sp) *)
  step. step.
  assert (HS : store_ok rsegs m3 (wa (SP + 96)) 8 = true)
    by (apply (stk_store_ok rsegs m3 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m3 ?A ?BS) _) =>
    change A with (wa (SP + 0x60));
    assert (MS4 : MemS0 (write_to_mem m3 (wa (SP + 0x60)) BS))
      by (apply MemS0_store; rewrite ?length_le8; [exact MS3 | exact HS | lia | lia | lia]);
    assert (C60 : bytes_at rsegs (write_to_mem m3 (wa (SP + 0x60)) BS) (SP + 0x60) (le8 (Z_to_bv 64 HALF_HI)))
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    assert (C70' : bytes_at rsegs (write_to_mem m3 (wa (SP + 0x60)) BS) (SP + 0x70) (le8 (Z_to_bv 64 RC_BIG)))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact C70 | lia | lia | lia]);
    assert (C88 : bytes_at rsegs (write_to_mem m3 (wa (SP + 0x60)) BS) (SP + 0x88) (le8 (Z_to_bv 64 PREFIX_AT)))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact C88' | lia | lia | lia]);
    revert MS4 C60 C70' C88; generalize (write_to_mem m3 (wa (SP + 0x60)) BS) as m4; intros m4 MS4 C60 C70' C88
  end.
  clear ST HS MS3 C70 C88'.
  pose proof MS4 as (_ & _ & _ & _ & ST & _).
  (* 0x1429c slli a7,a7,0x25; sd a7,0x50(sp) *)
  step.
  assert (HS : store_ok rsegs m4 (wa (SP + 80)) 8 = true)
    by (apply (stk_store_ok rsegs m4 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m4 ?A ?BS) _) =>
    change A with (wa (SP + 0x50));
    assert (MS5 : MemS0 (write_to_mem m4 (wa (SP + 0x50)) BS))
      by (apply MemS0_store; rewrite ?length_le8; [exact MS4 | exact HS | lia | lia | lia]);
    assert (C50 : bytes_at rsegs (write_to_mem m4 (wa (SP + 0x50)) BS) (SP + 0x50) (le8 (Z_to_bv 64 MHALF_HI)))
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    assert (C60' : bytes_at rsegs (write_to_mem m4 (wa (SP + 0x50)) BS) (SP + 0x60) (le8 (Z_to_bv 64 HALF_HI)))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact C60 | lia | lia | lia]);
    assert (C70 : bytes_at rsegs (write_to_mem m4 (wa (SP + 0x50)) BS) (SP + 0x70) (le8 (Z_to_bv 64 RC_BIG)))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact C70' | lia | lia | lia]);
    assert (C88' : bytes_at rsegs (write_to_mem m4 (wa (SP + 0x50)) BS) (SP + 0x88) (le8 (Z_to_bv 64 PREFIX_AT)))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact C88 | lia | lia | lia]);
    revert MS5 C50 C60' C70 C88'; generalize (write_to_mem m4 (wa (SP + 0x50)) BS) as m5;
    intros m5 MS5 C50 C60' C70 C88'
  end.
  clear ST HS MS4 C60 C70' C88.
  pose proof MS5 as (_ & _ & _ & _ & ST & _ & H58 & _).
  (* 0x142a4 ld a1,0x58(sp); add a4,a1,a4; sd a4,0x68(sp) *)
  pose proof (read_le8 rsegs m5 (SP + 88) _ H58) as HR. step. clear HR.
  step.
  assert (HS : store_ok rsegs m5 (wa (SP + 104)) 8 = true)
    by (apply (stk_store_ok rsegs m5 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m5 ?A ?BS) _) =>
    change A with (wa (SP + 0x68));
    assert (MS6 : MemS0 (write_to_mem m5 (wa (SP + 0x68)) BS))
      by (apply MemS0_store; rewrite ?length_le8; [exact MS5 | exact HS | lia | lia | lia]);
    assert (C68 : bytes_at rsegs (write_to_mem m5 (wa (SP + 0x68)) BS) (SP + 0x68) (le8 (Z_to_bv 64 (pp + OFF_ENT))))
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    assert (C50' : bytes_at rsegs (write_to_mem m5 (wa (SP + 0x68)) BS) (SP + 0x50) (le8 (Z_to_bv 64 MHALF_HI)))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact C50 | lia | lia | lia]);
    assert (C60 : bytes_at rsegs (write_to_mem m5 (wa (SP + 0x68)) BS) (SP + 0x60) (le8 (Z_to_bv 64 HALF_HI)))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact C60' | lia | lia | lia]);
    assert (C70' : bytes_at rsegs (write_to_mem m5 (wa (SP + 0x68)) BS) (SP + 0x70) (le8 (Z_to_bv 64 RC_BIG)))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact C70 | lia | lia | lia]);
    assert (C88 : bytes_at rsegs (write_to_mem m5 (wa (SP + 0x68)) BS) (SP + 0x88) (le8 (Z_to_bv 64 PREFIX_AT)))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact C88' | lia | lia | lia]);
    revert MS6 C68 C50' C60 C70' C88; generalize (write_to_mem m5 (wa (SP + 0x68)) BS) as m6;
    intros m6 MS6 C68 C50' C60 C70' C88
  end.
  clear ST H58 HS MS5 C50 C60' C70 C88'.
  (* 0x142b0 add a2,a1,a0 *)
  step.
  pose proof MS6 as (MU & WM & MI & TM & ST & HP & _ & HZ).
  assert (ML : MemL sp m r pp lo m6 [] 0 REFUSE_NONE).
  { split.
    - apply MemB_intro; assumption.
    - rewrite zeros136 in HZ. apply bytes_at_app in HZ as [_ HZ]. rewrite repeat_length in HZ.
      replace (SP + 0x90 + Z.of_nat 4) with (SP + 0x94) in HZ by lia.
      apply bytes_at_app in HZ as [HX HZ]. rewrite length_x_cellz in HZ by (cbn; unfold X_CELLS; lia).
      replace (SP + 0x94 + Z.of_nat 120) with (SP + 0x10c) in HZ by lia.
      apply bytes_at_app in HZ as [HN HZ]. rewrite length_le4 in HZ.
      replace (SP + 0x10c + Z.of_nat 4) with (SP + 0x110) in HZ by lia.
      apply bytes_at_app in HZ as [HK HR]. rewrite length_le4 in HR.
      replace (SP + 0x110 + Z.of_nat 4) with (SP + 0x114) in HR by lia.
      exact (conj HX (conj HN (conj HK HR))). }
  match goal with |- evt _ _ (MS _ ?F' _ _ _ _ _) =>
    assert (HFP : FPinv F')
      by (unfold FPinv; split;
          repeat first [rewrite freg_get_same by reflexivity | rewrite freg_get_other by reflexivity];
          first [reflexivity | apply bv_eq; reflexivity])
  end.
  eapply loop_entry; [exact HF | exact HFP | exact ML | lia | exact HE | exact EI | exact EP | leq ..].
Qed.

(** ** 0x140f0 .. 0x14104: memset(x, 0, 0x88), s0 := -1, `beqz s7` on the NULL flag *)
Lemma entry_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32),
  frm0 fc ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6 (Z_to_bv 64 nl)
             (Z_to_bv 64 (pp + POD_NENT_OFF)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x140f0) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc HF.
  pose proof bnde as (B1 & B2 & B3 & B4 & B5 & B6 & Hn32). pose proof len_ppe as LP.
  (* 0x140f0 addi a0,sp,0x90; addi a2,zero,0x88; mv a1,zero; jal memset *)
  step. step. step. step.
  destruct (stk_rw_cells rsegs m lo (SP + FRAME_LOCALS) (SP + 0x90) 136 HST ltac:(lia) ltac:(unfold FRAME_LOCALS; lia))
    as (junk & Lj & CJ).
  eapply evt_cut.
  { eapply MSET with (junk := junk); [rewrite !unsigned_lit by lia; exact CJ | exact HMI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & Ems & MU1 & WM1 &
              MI1 & CB1).
  subst ms'. ret_even. rewrite !unsigned_lit in MU1, CB1 by lia.
  assert (HZ : bytes_at rsegs m1 (SP + 0x90) (repeat (Z_to_bv 8 0) 136))
    by exact (rw_cells_CB_bytes rsegs m1 _ _ _ CB1).
  assert (ST1 : stk rsegs m1 lo (SP + FRAME_LOCALS)).
  { apply (stk_transport rsegs _ m m1 lo _ HST MU1 WM1). intros x Hx.
    destruct (Z_lt_le_dec x (SP + 144)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; lia|].
    destruct (Z_lt_le_dec x (SP + 280)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; lia].
    apply (bytes_at_some rsegs m1 (SP + 144) _ x HZ); rewrite repeat_length;
      [intros a Ha; apply HROM; unfold FRAME_LOCALS; lia | lia]. }
  assert (MS1 : MemS0 m1).
  { refine (conj _ (conj WM1 (conj MI1 (conj _ (conj ST1 (conj _ (conj _ HZ))))))).
    - refine (munch_weaken _ (EXPECT_W SP) m m1 _ MU1).
      unfold sub_fp, EXPECT_W, NEAR_STACK. cbn [outside]. intros x (O1 & O2 & O3 & _). repeat split; try exact I; lia.
    - apply (task_mem_munch rsegs _ m m1 HTM MU1). apply (stk_wview rsegs m lo (SP + FRAME_LOCALS)); [exact HST|].
      intros x Hx. cbn [outside] in Hx. unfold FRAME_LOCALS. lia.
    - apply (bytes_at_transport rsegs _ m m1 _ _ HPPB MU1). cbn [disjoint_from]. split; [lia | exact I].
    - apply (bytes_at_transport rsegs _ m m1 _ _ HM58 MU1). cbn [disjoint_from]. rewrite length_le8.
      split; [lia | exact I]. }
  assert (H50 : bytes_at rsegs m1 (SP + 0x50) (le8 (Z_to_bv 64 (pp + 16384)))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HM50 MU1). cbn [disjoint_from]. rewrite length_le8.
    split; [lia | exact I]. }
  clear CB1 HZ ST1 MU1 WM1 MI1.
  (* 0x14100 addi s0,zero,-1; beqz s7 *)
  step. step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec nl 0) as [En|En]; cbv beta iota.
  - (* 0x14220 *)
    eapply setup_ok; [exact HF | exact MS1 | exact H50 | | leq].
    rewrite HEdef. replace (nl =? 1) with false by (rewrite En; reflexivity). reflexivity.
  - (* the NULL flag: 0x14108 *)
    eapply exit_z with (rc := -1); [exact HF | exact MS1 | | leq].
    rewrite HEdef. replace (nl =? 1) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
Qed.

End Expect.

(** ** The statement *)
Theorem expect_holds : memset_contract -> strncmp_contract -> key_stmt -> expect_stmt.
Proof.
  intros MSET STRN KEY. unfold expect_stmt.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r nl cap
    pp lo HWF HNL HCAP -> -> -> H50 H58 HPPB HPP0 HPPLO HST HLO HSPA HROM HF HMI HTM HQ.
  eapply (entry_ok sp gp tp s1 s3 s4 s5 s6 m r nl cap pp lo Q (expect_model (nl =? 1) cap r));
    try eassumption; reflexivity.
Qed.
