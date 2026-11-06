(** The head of expect_of(pp, null, cap, &x) inlined in the UBSan LLVMFuzzerTestOneInput (fuzz_headamp.c:109-119),
    0x14198 -> 0x14268 / 0x14784: U/Prog/HeadCheck/Cut.v's [expect_stmt] from memset_contract and
    U/Prog/HeadCheck/PairInv.v's [loop_stmt] (the pair loop from its first head). The Section fixes the frame (sp, gp,
    tp and the callee-saved s1, s3-s6), the entry memory m, the record r at pp, the NULL flag nl, cap, lo and the
    continuation Q at 0x14784 for the answer Pod/Headamp.v [expect_model] (nl = 1) cap r. Walked backwards:
    [exit_z] (0x14780: x->rc := s9 over x all zero; the NULL flag and not props with s9 = (uint32)-1, no params with
    s9 = 0 through 0x1477c), [loop_entry] (0x14268: the loop's registers by equations, then [loop_stmt]),
    [setup_ok] (0x141b4: is_props and params_struct through s7 = &pp->len, then the constants 0x141c4-0x14264),
    [entry_ok] (0x14198: memset(x, 0, 0x88), s9 := (uint32)-1, `beqz s8` on the NULL flag's complement). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts PairFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require Import Cut ExpectFacts PairInv.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).

(** x right after memset(x, 0, 0x88): x->rc, then x past x->rc for no cell, no key, no refusal. *)
Lemma zeros136 : repeat (Z_to_bv 8 0) 136 =
  repeat (Z_to_bv 8 0) 4 ++ x_cellz [] ++ le4 (Z_to_bv 64 (Z.of_nat (length ([] : list cell)))) ++
  le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 REFUSE_NONE).
Proof. vm_compute. reflexivity. Qed.

Lemma zeros_tail : repeat (Z_to_bv 8 0) 136 = repeat (Z_to_bv 8 0) 4 ++ repeat (Z_to_bv 8 0) 132.
Proof. rewrite <- repeat_app. reflexivity. Qed.

(** The answer of the NULL flag, of no props and of no params: x->rc, then 132 zero bytes. *)
Lemma x_bytes_empty : forall rc, x_bytes (rc, [], (0, 0, REFUSE_NONE)) = le4 (Z_to_bv 64 rc) ++ repeat (Z_to_bv 8 0) 132.
Proof. intros rc. rewrite lib.Prog.HeadCheck.Cut.x_bytes_tail, x_tail_empty. reflexivity. Qed.

Section ExpectHead.
Variables (sp gp tp s1 s3 s4 s5 s6 : word) (m : word -> option byte) (r : pod_rec) (nl cap pp lo : Z)
          (Q : machine_state -> Prop).

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
Hypothesis HM68 : bytes_at rsegs m (SP + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))).
Hypothesis HM70 : bytes_at rsegs m (SP + 0x70) (le8 (Z_to_bv 64 pp)).
Hypothesis HM78 : bytes_at rsegs m (SP + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))).
Hypothesis MSET : memset_contract.
Hypothesis LOOP : loop_stmt.
Hypothesis HQ : expect_cont Q sp gp tp s1 s3 s4 s5 s6 m cap lo (expect_model (nl =? 1) cap r).

Lemma bnde : 0 <= pp /\ pp + 19744 <= lo /\ 0 <= lo /\ lo + 48 <= SP /\ SP + 472 <= 2^64 /\ 0 <= cap <= 9.
Proof.
  pose proof HST as (H0 & H1 & _). pose proof HPPLO as H2. pose proof HLO as H3.
  unfold POD_PROPS, NEAR_STACK, FRAME_LOCALS in *. lia.
Qed.

Lemma len_ppe : Z.of_nat (length (pp_bytes r)) = 19744.
Proof. exact (length_pp_bytes r HWF). Qed.

(** A register equation at the loop's first head: a folded literal, a sum with pp, or ~(pp + k). *)
Ltac leq := first [ reflexivity
                  | (f_equal; unfold NOT_BODY, NOT_ENT, OFF_ENT; rewrite ?(unsigned_lit pp) by lia; lia)
                  | (f_equal; unfold NOT_BODY, NOT_ENT, OFF_ENT; rewrite (unsigned_lit (pp + 16404)) by lia;
                     rewrite zb_lxor_ones by lia; lia) ].

(** ** The memory of the set-up: changed only in EXPECT_W, the record, the cells sp + 0x68 = &pp->n_ent, sp + 0x70 = pp,
    sp + 0x78 = &pp->len, and x all zero. *)
Definition MemS0 (m1 : word -> option byte) : Prop :=
  munch (EXPECT_W SP) m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ MemNorm.task_mem rsegs m1 /\
  stk rsegs m1 lo (SP + FRAME_LOCALS) /\ bytes_at rsegs m1 pp (pp_bytes r) /\
  bytes_at rsegs m1 (SP + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
  bytes_at rsegs m1 (SP + 0x70) (le8 (Z_to_bv 64 pp)) /\
  bytes_at rsegs m1 (SP + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
  bytes_at rsegs m1 (SP + 0xb8) (repeat (Z_to_bv 8 0) 136).

(** A store of the constants into [sp + 0x48, sp + 0x90) apart from the cells [sp + 0x68, sp + 0x80). *)
Lemma MemS0_store : forall m1 a bs, MemS0 m1 -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP + 0x48 <= a -> a + Z.of_nat (length bs) <= SP + 0x90 ->
  a + Z.of_nat (length bs) <= SP + 0x68 \/ SP + 0x80 <= a ->
  MemS0 (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs (MU & WM & MI & TM & ST & HP & H68 & H70 & H78 & HZ) HS H1 H2 H3.
  pose proof bnde as (B1 & B2 & B3 & B4 & B5 & _). pose proof len_ppe as LP.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
  - apply munch_write; [exact MU | lia | lia |]. unfold EXPECT_W. cbn [inside].
    destruct H3 as [H3|H3]; [right; left; lia | right; right; left; lia].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HS].
  - apply task_mem_write; [exact TM | exact HS].
  - apply stk_write; [exact ST | lia | lia].
  - apply bytes_at_write_other; [exact HP | lia | lia | lia].
  - apply bytes_at_write_other; rewrite ?length_le8; [exact H68 | lia | lia | lia].
  - apply bytes_at_write_other; rewrite ?length_le8; [exact H70 | lia | lia | lia].
  - apply bytes_at_write_other; rewrite ?length_le8; [exact H78 | lia | lia | lia].
  - apply bytes_at_write_other; rewrite ?repeat_length; [exact HZ | lia | lia | lia].
Qed.

(** The set-up's memory with the 8-byte frame cells (offset, value) the constants wrote. *)
Definition cells_at (m1 : word -> option byte) (cs : list (Z * Z)) : Prop :=
  Forall (fun c => bytes_at rsegs m1 (SP + fst c) (le8 (Z_to_bv 64 (snd c)))) cs.

Definition MemC (m1 : word -> option byte) (cs : list (Z * Z)) : Prop := MemS0 m1 /\ cells_at m1 cs.

Lemma MemC_ok : forall m1 cs o, MemC m1 cs -> 0 <= o -> o + 8 <= FRAME_LOCALS ->
  store_ok rsegs m1 (wa (SP + o)) 8 = true.
Proof.
  intros m1 cs o ((_ & _ & _ & _ & ST & _) & _) H1 H2. pose proof bnde as (B1 & B2 & B3 & B4 & B5 & _).
  apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | lia].
Qed.

Lemma MemC_store : forall m1 cs o v, MemC m1 cs -> 0x48 <= o -> o + 8 <= 0x68 \/ (0x80 <= o /\ o + 8 <= 0x90) ->
  Forall (fun c => fst c + 8 <= o \/ o + 8 <= fst c) cs ->
  MemC (write_to_mem m1 (wa (SP + o)) (le8 (Z_to_bv 64 v))) ((o, v) :: cs).
Proof.
  intros m1 cs o v (MS & CS) H1 H2 HD. pose proof bnde as (B1 & B2 & B3 & B4 & B5 & _).
  pose proof (MemC_ok m1 cs o (conj MS CS) ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as HS.
  split.
  - apply MemS0_store; rewrite ?length_le8; [exact MS | exact HS | lia | lia | lia].
  - unfold cells_at in *. constructor.
    + cbn [fst snd]. apply bytes_at_write_same; rewrite ?length_le8; lia.
    + clear MS. induction cs as [|c cs IH]; [constructor|].
      apply Forall_cons_iff in CS as [Hc CS']. apply Forall_cons_iff in HD as [Hd HD'].
      constructor; [|exact (IH CS' HD')].
      apply bytes_at_write_other; rewrite ?length_le8; [exact Hc | lia | lia | lia].
Qed.

(** After the step of `sd _, o(sp)` writing v, with MC : MemC m1 cs in context: the new memory, generalized, and
    MC : MemC m2 ((o, v) :: cs). *)
Ltac cstore MC o v :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?A ?BS) _) =>
    change A with (wa (SP + o));
    replace BS with (le8 (Z_to_bv 64 v)) by (first [reflexivity | vm_compute; reflexivity]);
    let MC' := fresh "MCn" in
    pose proof (MemC_store m1 _ o v MC ltac:(lia) ltac:(lia)
                  ltac:(repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil)) as MC';
    clear MC; revert MC'; generalize (write_to_mem m1 (wa (SP + o)) (le8 (Z_to_bv 64 v)));
    let mn := fresh "m" in intros mn MC; try clear m1
  end.

(** ** 0x14780 with no cell: x->rc := s9, x past x->rc all zero *)
Lemma exit_z : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (rc : Z),
  frm0 fc -> MemS0 m1 -> expect_model (nl =? 1) cap r = (rc, [], (0, 0, REFUSE_NONE)) ->
  le4 s9 = le4 (Z_to_bv 64 rc) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x14780) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 rc HF
    (MU & WM & MI & TM & ST & _ & _ & _ & _ & HZ) HE H9.
  pose proof bnde as (B1 & B2 & B3 & B4 & B5 & _).
  assert (HS : store_ok rsegs m1 (wa (SP + 184)) 4 = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  (* 0x14780 sw s9,0xb8(sp) *)
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 0xb8)); replace BS with (le4 (Z_to_bv 64 rc)) by (rewrite <- H9; reflexivity)
  end.
  pose proof (length_le4 (Z_to_bv 64 rc)) as L4.
  apply HQ.
  - exact HF.
  - apply munch_write; [exact MU | lia | lia |]. unfold EXPECT_W. cbn [inside]. right; right; left; lia.
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | rewrite L4; exact HS].
  - apply task_mem_write; [exact TM | rewrite L4; exact HS].
  - apply stk_write; [exact ST | lia | lia].
  - rewrite HE, x_bytes_empty. rewrite zeros_tail in HZ.
    pose proof (bytes_at_write_mid rsegs m1 (SP + 0xb8) [] (repeat (Z_to_bv 8 0) 4) (le4 (Z_to_bv 64 rc))
                  (repeat (Z_to_bv 8 0) 132) HZ ltac:(rewrite L4; reflexivity)) as X.
    cbn [length Z.of_nat app] in X. rewrite Z.add_0_r in X. exact X.
Qed.

(** ** 0x14268: the loop's first head, its registers by equations *)
Lemma loop_entry : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                          (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> FPinv F -> MemL sp m r pp lo m1 [] 0 REFUSE_NONE -> nl = 0 -> is_props r = true ->
  params_struct r = true ->
  ra = Z_to_bv 64 (NOT_BODY pp) -> s0 = Z_to_bv 64 (NOT_ENT pp) -> a0 = Z_to_bv 64 0 ->
  a2 = Z_to_bv 64 (pp + POD_NENT_OFF) -> a6 = Z_to_bv 64 MULHU_104 -> a7 = Z_to_bv 64 (pp + OFF_ENT + 8) ->
  s8 = Z_to_bv 64 (pp + OFF_ENT) -> s9 = Z_to_bv 64 0 -> t5 = Z_to_bv 64 POD_STRING -> t6 = Z_to_bv 64 1 ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x14268) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF HFP ML Hnl EI EP
    -> -> -> -> -> -> -> -> -> ->.
  assert (HE : expect_model (nl =? 1) cap r = ha_result (ha_fold expect_cell cap (pairs (ents r)) [] 0 REFUSE_NONE))
    by (rewrite Hnl; unfold expect_model; rewrite EI, EP; reflexivity).
  pose proof HQ as HQ'. rewrite HE in HQ'.
  exact (LOOP Q sp gp tp s1 s3 s4 s5 s6 m r cap pp lo HWF HCAP HPP0 HPPLO HST HLO HSPA HROM EP HQ'
           t0 t1 t2 a1 a3 a4 a5 s7 s10 s11 t3 t4 F fc m1 HF HFP ML).
Qed.

(** ** 0x141b4 .. 0x14264: is_props, params_struct; the loop's constants *)
Lemma setup_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte),
  frm0 fc -> MemS0 m1 -> nl = 0 -> le4 s9 = le4 (Z_to_bv 64 (-1)) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (pp + 16384)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141b4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HF MS Hnl H9.
  pose proof bnde as (B1 & B2 & B3 & B4 & B5 & B6). pose proof len_ppe as LP.
  pose proof MS as (_ & _ & _ & _ & _ & HP & _).
  (* 0x141b4 lw a0,8(s7); beqz a0 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 16392)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (is_props r))))).
  { apply (read_field rsegs m1 pp r 16392 _ HP HWF);
      [exact (pp_is_props r HWF) | lia | unfold PP_SIZE; lia | destruct (is_props r); cbn; lia]. }
  revert HR. destruct (is_props r) eqn:EI; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      eapply exit_z with (rc := -1); [exact HF | exact MS | | exact H9].
      rewrite Hnl. unfold expect_model. rewrite EI. reflexivity. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  (* 0x141bc lw t6,0x10(s7); beqz t6 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 16400)) 4 = Some (le4 (Z_to_bv 64 (Z.b2z (params_struct r))))).
  { apply (read_field rsegs m1 pp r 16400 _ HP HWF);
      [exact (pp_params_struct r HWF) | lia | unfold PP_SIZE; lia | destruct (params_struct r); cbn; lia]. }
  revert HR. destruct (params_struct r) eqn:EP; cbn [Z.b2z]; intros HR.
  2:{ step. clear HR. rewrite sx32_small by lia. step. if_true.
      (* 0x1477c mv s9,zero *)
      step.
      eapply exit_z with (rc := 0); [exact HF | exact MS | | reflexivity].
      rewrite Hnl. unfold expect_model. rewrite EI, EP. reflexivity. }
  step. clear HR. rewrite sx32_small by lia. step. if_false.
  clear HP.
  (* 0x141c4 .. 0x1421c: the constants in registers *)
  do 23 step.
  assert (MC : MemC m1 []) by exact (conj MS (Forall_nil _)). clear MS.
  (* 0x14220 sd a3,0x88(sp) *)
  pose proof (MemC_ok _ _ 0x88 MC ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as HS. step. clear HS.
  cstore MC 0x88 RC_BIG.
  (* 0x14224 slli t0,t0,0x31; sd t0,0x60(sp) *)
  step.
  pose proof (MemC_ok _ _ 0x60 MC ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as HS. step. clear HS.
  cstore MC 0x60 C2_LO.
  (* 0x1422c slli t1,t1,0x25; sd t1,0x58(sp) *)
  step.
  pose proof (MemC_ok _ _ 0x58 MC ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as HS. step. clear HS.
  cstore MC 0x58 C2_HI.
  (* 0x14234 slli t2,t2,0x25; sd t2,0x50(sp) *)
  step.
  pose proof (MemC_ok _ _ 0x50 MC ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as HS. step. clear HS.
  cstore MC 0x50 HALF_HI.
  (* 0x1423c slli t3,t3,0x25; sd t3,0x48(sp) *)
  step.
  pose proof (MemC_ok _ _ 0x48 MC ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as HS. step. clear HS.
  cstore MC 0x48 MHALF_HI.
  (* 0x14244 ld a3,0x70(sp); add s8,a3,s8; add a7,a3,a1; sub a1,a2,a3 *)
  pose proof MC as ((_ & _ & _ & _ & _ & _ & H68 & H70 & _) & _).
  pose proof (read_le8 rsegs _ (SP + 0x70) _ H70) as HR. step. clear HR H70.
  step. step. step.
  (* 0x14254 ld a2,0x68(sp); addi ra,a1,-0x20; not a1,t4 *)
  pose proof (read_le8 rsegs _ (SP + 0x68) _ H68) as HR. step. clear HR H68.
  step. step.
  (* 0x14260 sd a1,0x80(sp) *)
  pose proof (MemC_ok _ _ 0x80 MC ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as HS. step. clear HS.
  replace (Z.lxor (bv_unsigned (Z_to_bv 64 (SP + 188))) 18446744073709551615) with (2^64 - 1 - (SP + 0xbc))
    by (rewrite unsigned_lit by lia; rewrite zb_lxor_ones by lia; lia).
  cstore MC 0x80 (2^64 - 1 - (SP + 0xbc)).
  (* 0x14264 not s0,s8 *)
  step.
  destruct MC as ((MU & WM & MI & TM & ST & HP & H68 & _ & H78 & HZ) & CS).
  unfold cells_at in CS. repeat rewrite Forall_cons_iff in CS. cbn [fst snd] in CS.
  destruct CS as (C80 & C48 & C50 & C58 & C60 & C88 & _).
  rewrite zeros136 in HZ. apply bytes_at_app in HZ as [_ HZ]. rewrite repeat_length in HZ.
  replace (SP + 0xb8 + Z.of_nat 4) with (SP + 0xbc) in HZ by lia.
  apply bytes_at_app in HZ as [HX HZ]. rewrite length_x_cellz in HZ by (cbn; unfold X_CELLS; lia).
  replace (SP + 0xbc + Z.of_nat 120) with (SP + 0x134) in HZ by lia.
  apply bytes_at_app in HZ as [HN HZ]. rewrite length_le4 in HZ.
  replace (SP + 0x134 + Z.of_nat 4) with (SP + 0x138) in HZ by lia.
  apply bytes_at_app in HZ as [HK HR]. rewrite length_le4 in HR.
  replace (SP + 0x138 + Z.of_nat 4) with (SP + 0x13c) in HR by lia.
  match goal with |- evt _ _ (MS _ ?F' _ _ _ ?mf _) =>
    assert (ML : MemL sp m r pp lo mf [] 0 REFUSE_NONE)
      by exact (conj (conj MU (conj WM (conj MI (conj TM (conj ST (conj HP (conj C48 (conj C50 (conj C58 (conj C60
                  (conj H68 (conj H78 (conj C80 C88)))))))))))))
                (conj HX (conj HN (conj HK HR))));
    assert (HFP : FPinv F')
      by (unfold FPinv; refine (conj _ (conj _ _));
          repeat first [rewrite freg_get_same by reflexivity | rewrite freg_get_other by reflexivity];
          first [reflexivity | apply bv_eq; reflexivity | vm_compute; reflexivity])
  end.
  eapply loop_entry; [exact HF | exact HFP | exact ML | exact Hnl | exact EI | exact EP | leq ..].
Qed.

(** ** 0x14198 .. 0x141b0: memset(x, 0, 0x88), s9 := (uint32)-1, `beqz s8` on the NULL flag's complement *)
Lemma entry_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word)
                        (F : bvmap 5 word) (fc : bv 32),
  frm0 fc ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (1 - nl)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14198) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc HF.
  pose proof bnde as (B1 & B2 & B3 & B4 & B5 & B6). pose proof len_ppe as LP.
  (* 0x14198 addi a0,sp,0xb8; addi a2,zero,0x88; mv a1,zero; jal memset *)
  step. step. step. step.
  destruct (stk_rw_cells rsegs m lo (SP + FRAME_LOCALS) (SP + 0xb8) 136 HST ltac:(lia) ltac:(unfold FRAME_LOCALS; lia))
    as (junk & Lj & CJ).
  eapply evt_cut.
  { eapply MSET with (junk := junk); [rewrite !unsigned_lit by lia; exact CJ | exact HMI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & Ems & MU1 & WM1 &
              MI1 & CB1).
  subst ms'. ret_even. rewrite !unsigned_lit in MU1, CB1 by lia.
  assert (HZ : bytes_at rsegs m1 (SP + 0xb8) (repeat (Z_to_bv 8 0) 136))
    by exact (rw_cells_CB_bytes rsegs m1 _ _ _ CB1).
  assert (ST1 : stk rsegs m1 lo (SP + FRAME_LOCALS)).
  { apply (stk_transport rsegs _ m m1 lo _ HST MU1 WM1). intros x Hx.
    destruct (Z_lt_le_dec x (SP + 184)) as [X1|X1]; [left; cbn [outside]; repeat split; try exact I; lia|].
    destruct (Z_lt_le_dec x (SP + 320)) as [X2|X2]; [right | left; cbn [outside]; repeat split; try exact I; lia].
    apply (bytes_at_some rsegs m1 (SP + 184) _ x HZ); rewrite repeat_length;
      [intros a Ha; apply HROM; unfold FRAME_LOCALS; lia | lia]. }
  assert (MS1 : MemS0 m1).
  { refine (conj _ (conj WM1 (conj MI1 (conj _ (conj ST1 (conj _ (conj _ (conj _ (conj _ HZ))))))))).
    - apply (munch_weaken [(SP + 184, SP + 184 + 136)] (EXPECT_W SP) m m1); [|exact MU1].
      unfold sub_fp, EXPECT_W, NEAR_STACK. cbn [outside]. intros x (O1 & O2 & O3 & _). repeat split; try exact I; lia.
    - apply (task_mem_munch rsegs _ m m1 HTM MU1). apply (stk_wview rsegs m lo (SP + FRAME_LOCALS)); [exact HST|].
      intros x Hx. cbn [outside] in Hx. unfold FRAME_LOCALS. lia.
    - apply (bytes_at_transport rsegs _ m m1 _ _ HPPB MU1). cbn [disjoint_from]. split; [lia | exact I].
    - apply (bytes_at_transport rsegs _ m m1 _ _ HM68 MU1). cbn [disjoint_from]. rewrite length_le8.
      split; [lia | exact I].
    - apply (bytes_at_transport rsegs _ m m1 _ _ HM70 MU1). cbn [disjoint_from]. rewrite length_le8.
      split; [lia | exact I].
    - apply (bytes_at_transport rsegs _ m m1 _ _ HM78 MU1). cbn [disjoint_from]. rewrite length_le8.
      split; [lia | exact I]. }
  clear CB1 HZ ST1 MU1 WM1 MI1.
  (* 0x141a8 addi a0,zero,-1; srli s9,a0,0x20; beqz s8 *)
  step. step. step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec (1 - nl) 0) as [En|En]; cbv beta iota.
  - (* the NULL flag: 0x14780 with x->rc = -1 *)
    eapply exit_z with (rc := -1); [exact HF | exact MS1 | | exact le4_m1].
    replace (nl =? 1) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - (* 0x141b4 *)
    eapply setup_ok; [exact HF | exact MS1 | lia | exact le4_m1].
Qed.

End ExpectHead.

(** ** The statement *)
Theorem head_holds : memset_contract -> loop_stmt -> expect_stmt.
Proof.
  intros MSET LOOP. unfold expect_stmt.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r nl cap
    pp lo HWF HNL HCAP -> -> -> H68 H70 H78 HPPB HPP0 HPPLO HST HLO HSPA HROM HF HMI HTM HQ.
  exact (entry_ok sp gp tp s1 s3 s4 s5 s6 m r nl cap pp lo Q HWF HNL HCAP HPP0 HPPLO HST HLO HSPA HROM HMI HTM HPPB
           H68 H70 H78 MSET LOOP HQ ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc HF).
Qed.
