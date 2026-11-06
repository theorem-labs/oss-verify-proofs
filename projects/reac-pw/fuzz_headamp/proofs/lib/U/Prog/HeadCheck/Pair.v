(** The pair loop of expect_of (fuzz_headamp.c:119-155) in the UBSan LLVMFuzzerTestOneInput, from the loop head
    0x14268 to 0x14784 (after the store of x->rc at 0x14780): PairInv.v [loop_stmt], with U/Prog/HeadCheck/Cut.v
    [key_stmt] (the pair with the prefix, 0x14354 -> 0x144f4 / 0x146fc) and strncmp_contract as Section hypotheses.
    The Section fixes the frame (sp, gp, tp and the callee-saved s1, s3-s6), the entry memory m, the record r at pp,
    cap, lo, the continuation Q and the answer E it expects. Walked backwards: [exit_ok] (0x14780: x->rc), [back_ok]
    (0x14504: at := the saved next at, back to the head), [fold_ok] (0x144f4: the first refusal is kept), the cap test
    and the cell write ([cap_ok] 0x146fc with its traps 0x14708 / 0x14720 / 0x14734 / 0x14748, [cellw_ok]),
    [pair_ok] (0x14354: the key piece), [some_ok] (0x14294 with a key in the slot: the overflow check of at + 1, the
    saves, strncmp(k, "reac.headamp.", 13)), the pod_next_pair scan by induction on the entries left ([none_ok]
    0x14294 with its traps 0x14298 / 0x1429c / 0x142c0, [end_ok] 0x142e8), [head_ok] (0x14268: at < n_ent, the
    bound 33 of ent[at], 104 at by mulhu). The loop computes Pod/Headamp.v [ha_fold] over the pairs left
    ([pairs_by key_of] of the entries from the scan's index) step by step: at the exit the fold's (cells, keys,
    refusal) is what x holds past x->rc, and s9 its number of cells. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Cut.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c strncmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require ParseSites.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require Import Cut ExpectFacts PairInv.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).
(* Register equations at a cut. *)
Ltac weq := first [ reflexivity
                  | (rewrite addiw1_small by lia; f_equal; lia)
                  | (f_equal; lia)
                  | (f_equal; rewrite ?unsigned_lit by lia; lia) ].

(** x after the store of x->rc, for the fold's state. *)
Lemma x_bytes_res : forall cells keys rf,
  x_bytes (ha_result (cells, keys, rf)) =
  le4 (Z_to_bv 64 (Z.of_nat (length cells))) ++ x_cellz cells ++ le4 (Z_to_bv 64 (Z.of_nat (length cells))) ++
  le4 (Z_to_bv 64 keys) ++ le4 (Z_to_bv 64 rf).
Proof. intros cells keys rf. rewrite lib.Prog.HeadCheck.Cut.x_bytes_tail, x_tail_res. reflexivity. Qed.

(** lwu of a small value. *)
Lemma zx32_lit : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Section Pairs.
Variables (sp gp tp s1 s3 s4 s5 s6 : word) (m : word -> option byte) (r : pod_rec) (cap pp lo : Z)
          (Q : machine_state -> Prop) (E : answer).

Local Abbreviation SP := (bv_unsigned sp).
Local Abbreviation es := (ents r).
Local Abbreviation n := (length (ents r)).
Local Abbreviation MB := (MemB sp m r pp lo).
Local Abbreviation ML := (MemL sp m r pp lo).
Local Abbreviation MP := (MemP sp m r pp lo).
Local Abbreviation MX := (MemX sp).

Hypothesis HWF : pod_rec_wf r.
Hypothesis HCAP : 0 <= cap <= 9.
Hypothesis HPP0 : 0 <= pp.
Hypothesis HPPLO : pp + POD_PROPS <= lo.
Hypothesis HST : stk rsegs m lo (SP + FRAME_LOCALS).
Hypothesis HLO : lo + NEAR_STACK <= SP.
Hypothesis HSPA : SP mod 16 = 0.
Hypothesis HROM : forall a, lo <= a < SP + FRAME_LOCALS -> seg_rom rsegs (wa a) = None.
Hypothesis HPS : params_struct r = true.
Hypothesis KEY : key_stmt.
Hypothesis STRN : strncmp_contract.
Hypothesis HQ : expect_cont Q sp gp tp s1 s3 s4 s5 s6 m cap lo E.

(** The numbers lia needs. *)
Lemma bnd : 0 <= pp /\ pp + 19744 <= lo /\ 0 <= lo /\ lo + 48 <= SP /\ SP + 472 <= 2^64 /\ 0 <= cap <= 9 /\
            (n <= 32)%nat.
Proof.
  pose proof HST as (H0 & H1 & _). pose proof (proj1 (ents_wf r HWF)) as Hn.
  pose proof HPPLO as H2. pose proof HLO as H3. unfold POD_PROPS, NEAR_STACK, FRAME_LOCALS, POD_ENT_MAX in *. lia.
Qed.

Lemma len_pp : Z.of_nat (length (pp_bytes r)) = 19744.
Proof. exact (length_pp_bytes r HWF). Qed.

(** ** The memory of the loop *)
(** A store into [sp + 0x90, sp + 0x140) keeps MemB. *)
Lemma MemB_store : forall m1 a bs, MB m1 -> store_ok rsegs m1 (wa a) (length bs) = true ->
  SP + 0x90 <= a -> a + Z.of_nat (length bs) <= SP + 0x140 -> MB (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs (MU & WM & MI & TM & ST & HP & H48 & H50 & H58 & H60 & H68 & H78 & H80 & H88) HS HA1 HA2.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _). pose proof len_pp as LP.
  assert (HIn : inside (EXPECT_W SP) a (Z.of_nat (length bs))).
  { unfold EXPECT_W. cbn [inside]. right; right; left. lia. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
            (conj _ _))))))))))))).
  - apply munch_write; [exact MU | lia | lia | exact HIn].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HS].
  - apply task_mem_write; [exact TM | exact HS].
  - apply stk_write; [exact ST | lia | lia].
  - apply bytes_at_write_other; [exact HP | lia | lia | lia].
  - apply bytes_at_write_other; [exact H48 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H50 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H58 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H60 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H68 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H78 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H80 | lia | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H88 | lia | lia | rewrite length_le8; lia].
Qed.

(** A store into [sp + 0x90, sp + 0xbc) (the saves) keeps MemL. *)
Lemma MemL_store_save : forall m1 cells keys rf a bs, ML m1 cells keys rf -> (length cells <= X_CELLS)%nat ->
  store_ok rsegs m1 (wa a) (length bs) = true -> SP + 0x90 <= a -> a + Z.of_nat (length bs) <= SP + 0xb8 ->
  ML (write_to_mem m1 (wa a) bs) cells keys rf.
Proof.
  intros m1 cells keys rf a bs (MB1 & HX & HN & HK & HR) Hl HS H1 H2.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _).
  assert (LX : length (x_cellz cells) = 120%nat) by (apply length_x_cellz; exact Hl).
  split; [apply MemB_store; [exact MB1 | exact HS | lia | lia]|].
  refine (conj _ (conj _ (conj _ _))); apply bytes_at_write_other; rewrite ?LX, ?length_le4;
    first [eassumption | lia].
Qed.

(** Across strncmp (no store). *)
Lemma MemP_none : forall m1 m2 cells keys rf v, MP m1 cells keys rf v ->
  munch [] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> MP m2 cells keys rf v.
Proof.
  intros m1 m2 cells keys rf v
    (((MU & WM & MI & TM & ST & HP & H48 & H50 & H58 & H60 & H68 & H78 & H80 & H88) & (HX & HN & HK & HR)) &
     H90 & H98 & Ha0 & Ha8 & Hb0) MU2 WM2 MI2.
  assert (T : forall A bs, bytes_at rsegs m1 A bs -> bytes_at rsegs m2 A bs)
    by (intros A bs H; exact (bytes_at_transport rsegs [] m1 m2 A bs H MU2 I)).
  split; [split|].
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + exact (munch_trans _ m m1 m2 MU (munch_weaken [] _ m1 m2 (fun x _ => I) MU2)).
    + exact (wmono_trans rsegs m m1 m2 WM WM2).
    + exact MI2.
    + apply (task_mem_munch rsegs [] m1 m2 TM MU2). intros x Hx. exfalso. apply Hx. exact I.
    + exact (stk_transport_disjoint rsegs [] m1 m2 lo (SP + FRAME_LOCALS) ST MU2 WM2 I).
    + refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); apply T; assumption.
  - refine (conj _ (conj _ (conj _ _))); apply T; assumption.
  - refine (conj _ (conj _ (conj _ (conj _ _)))); apply T; assumption.
Qed.

(** Across the key piece: its footprint KEY_W, keys + 1 at sp + 0x138. *)
Lemma MemP_key : forall m1 m2 cells keys rf v, MP m1 cells keys rf v -> (length cells <= X_CELLS)%nat ->
  munch (KEY_W SP) m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> MemNorm.task_mem rsegs m2 ->
  stk rsegs m2 lo (SP + FRAME_LOCALS) -> bytes_at rsegs m2 (SP + 0x138) (le4 (Z_to_bv 64 (keys + 1))) ->
  MP m2 cells (keys + 1) rf v.
Proof.
  intros m1 m2 cells keys rf v
    (((MU & WM & MI & TM & ST & HP & H48 & H50 & H58 & H60 & H68 & H78 & H80 & H88) & (HX & HN & HK & HR)) &
     H90 & H98 & Ha0 & Ha8 & Hb0) Hc MU2 WM2 MI2 TM2 ST2 HK2.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _). pose proof len_pp as LP.
  assert (LX : length (x_cellz cells) = 120%nat) by (apply length_x_cellz; exact Hc).
  assert (T : forall A bs, bytes_at rsegs m1 A bs -> A + Z.of_nat (length bs) <= SP - 48 \/ SP <= A ->
                A + Z.of_nat (length bs) <= SP + 0x28 \/ SP + 0x48 <= A ->
                A + Z.of_nat (length bs) <= SP + 0x138 \/ SP + 0x13c <= A -> bytes_at rsegs m2 A bs).
  { intros A bs H D1 D2 D3. apply (bytes_at_transport rsegs _ m1 m2 A bs H MU2). unfold KEY_W, NEAR_STACK.
    cbn [disjoint_from]. repeat split; lia. }
  split; [split|].
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + apply (munch_trans _ m m1 m2 MU). apply (munch_weaken (KEY_W SP) _ m1 m2); [|exact MU2].
      unfold sub_fp, KEY_W, EXPECT_W, NEAR_STACK. cbn [outside]. intros x (O1 & O2 & O3 & _).
      repeat split; try exact I; lia.
    + exact (wmono_trans rsegs m m1 m2 WM WM2).
    + exact MI2.
    + exact TM2.
    + exact ST2.
    + refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
      * apply T; [exact HP | lia | lia | lia].
      * apply T; [exact H48 | rewrite length_le8; lia ..].
      * apply T; [exact H50 | rewrite length_le8; lia ..].
      * apply T; [exact H58 | rewrite length_le8; lia ..].
      * apply T; [exact H60 | rewrite length_le8; lia ..].
      * apply T; [exact H68 | rewrite length_le8; lia ..].
      * apply T; [exact H78 | rewrite length_le8; lia ..].
      * apply T; [exact H80 | rewrite length_le8; lia ..].
      * apply T; [exact H88 | rewrite length_le8; lia ..].
  - refine (conj _ (conj _ (conj _ _))).
    + apply T; [exact HX | rewrite LX; lia ..].
    + apply T; [exact HN | rewrite length_le4; lia ..].
    + exact HK2.
    + apply T; [exact HR | rewrite length_le4; lia ..].
  - refine (conj _ (conj _ (conj _ (conj _ _)))).
    + apply T; [exact H90 | rewrite length_le8; lia ..].
    + apply T; [exact H98 | rewrite length_le8; lia ..].
    + apply T; [exact Ha0 | rewrite length_le8; lia ..].
    + apply T; [exact Ha8 | rewrite length_le8; lia ..].
    + apply T; [exact Hb0 | rewrite length_le8; lia ..].
Qed.

(** A store into [sp + 0xb8, sp + 0x134) (x->rc and x's cells part) keeps MemP but MemX's cells part. *)
Lemma MemP_store_cells : forall m1 (cells : list cell) keys rf a bs, MB m1 ->
  bytes_at rsegs m1 (SP + 0x134) (le4 (Z_to_bv 64 (Z.of_nat (length cells)))) ->
  bytes_at rsegs m1 (SP + 0x138) (le4 (Z_to_bv 64 keys)) -> bytes_at rsegs m1 (SP + 0x13c) (le4 (Z_to_bv 64 rf)) ->
  store_ok rsegs m1 (wa a) (length bs) = true -> SP + 0xb8 <= a -> a + Z.of_nat (length bs) <= SP + 0x134 ->
  MB (write_to_mem m1 (wa a) bs) /\
  bytes_at rsegs (write_to_mem m1 (wa a) bs) (SP + 0x134) (le4 (Z_to_bv 64 (Z.of_nat (length cells)))) /\
  bytes_at rsegs (write_to_mem m1 (wa a) bs) (SP + 0x138) (le4 (Z_to_bv 64 keys)) /\
  bytes_at rsegs (write_to_mem m1 (wa a) bs) (SP + 0x13c) (le4 (Z_to_bv 64 rf)).
Proof.
  intros m1 cells keys rf a bs MB1 HN HK HR HS H1 H2. pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _).
  split; [apply MemB_store; [exact MB1 | exact HS | lia | lia]|].
  refine (conj _ (conj _ _)); apply bytes_at_write_other; rewrite ?length_le4; first [eassumption | lia].
Qed.

(** ** 0x14780 .. 0x14784: x->rc := s9 = the number of cells; x is then the fold's answer *)
Lemma exit_ok : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte) (cells : list cell) (keys rf : Z),
  frm0 fc -> ML m1 cells keys rf -> Z.of_nat (length cells) <= cap -> E = ha_result (cells, keys, rf) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6 s7 s8
             (Z_to_bv 64 (Z.of_nat (length cells))) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14780) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s10 s11 t3 t4 t5 t6 F fc m1 cells keys rf HF
    ((MU & WM & MI & TM & ST & _) & (HX & HN & HK & HR)) Hc HE.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  assert (LX : length (x_cellz cells) = 120%nat) by (apply length_x_cellz; unfold X_CELLS; lia).
  (* 0x14780 sw s9,0xb8(sp) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 184)) 4 = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 0xb8))
  end.
  apply HQ.
  - exact HF.
  - apply munch_write; [exact MU | lia | rewrite length_le4; lia | unfold EXPECT_W; cbn [inside]; right; right; left;
      rewrite length_le4; lia].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | rewrite length_le4; exact HS].
  - apply task_mem_write; [exact TM | rewrite length_le4; exact HS].
  - apply stk_write; [exact ST | lia | rewrite length_le4; lia].
  - rewrite HE, x_bytes_res. apply bytes_at_app. split; [apply bytes_at_write_same; rewrite ?length_le4; lia|].
    rewrite length_le4. replace (SP + 0xb8 + Z.of_nat 4) with (SP + 0xbc) by lia.
    apply bytes_at_app. split; [apply bytes_at_write_other; rewrite ?LX, ?length_le4; [exact HX | lia | lia | lia]|].
    rewrite LX. replace (SP + 0xbc + Z.of_nat 120) with (SP + 0x134) by lia.
    apply bytes_at_app. split; [apply bytes_at_write_other; rewrite ?length_le4; [exact HN | lia | lia | lia]|].
    rewrite length_le4. replace (SP + 0x134 + Z.of_nat 4) with (SP + 0x138) by lia.
    apply bytes_at_app. split; [apply bytes_at_write_other; rewrite ?length_le4; [exact HK | lia | lia | lia]|].
    rewrite length_le4. replace (SP + 0x138 + Z.of_nat 4) with (SP + 0x13c) by lia.
    apply bytes_at_write_other; rewrite ?length_le4; [exact HR | lia | lia | lia].
Qed.

(** ** The loop head 0x14268 *)
Definition head_P (j : nat) : Prop :=
  forall (t0 t1 t2 a1 a3 a4 a5 s7 s10 s11 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte)
         (cells : list cell) (keys rf : Z),
  frm0 fc -> FPinv F -> ML m1 cells keys rf -> Linv cap cells keys rf j ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn j es) None) cells keys rf) -> (j <= n)%nat ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 (NOT_BODY pp)) sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 (Z_to_bv 64 (Z.of_nat j)) a1
             (Z_to_bv 64 (pp + POD_NENT_OFF)) a3 a4 a5 (Z_to_bv 64 MULHU_104) (Z_to_bv 64 (pp + OFF_ENT + 8))
             (Z_to_bv 64 cap) s3 s4 s5 s6 s7 (Z_to_bv 64 (pp + OFF_ENT)) (Z_to_bv 64 (Z.of_nat (length cells))) s10 s11
             t3 t4 (Z_to_bv 64 POD_STRING) (Z_to_bv 64 1))
        F (Z_to_bv 64 0x14268) fc None m1 (seg_rom rsegs)).

(** ** 0x14504 .. 0x1450c: at := the saved next at; t6 = params_struct is set; back to the head *)
Lemma back_ok : forall v, head_P (S v) ->
  forall (t0 t1 t2 a0 a1 a3 a4 a5 s7 s9 s10 s11 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf : Z),
  frm0 fc -> FPinv F -> MP m1 cells keys rf v -> Linv cap cells keys rf (S v) ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn (S v) es) None) cells keys rf) -> (S v <= n)%nat ->
  s9 = Z_to_bv 64 (Z.of_nat (length cells)) ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 (NOT_BODY pp)) sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 a0 a1
             (Z_to_bv 64 (pp + POD_NENT_OFF)) a3 a4 a5 (Z_to_bv 64 MULHU_104) (Z_to_bv 64 (pp + OFF_ENT + 8))
             (Z_to_bv 64 cap) s3 s4 s5 s6 s7 (Z_to_bv 64 (pp + OFF_ENT)) s9 s10 s11
             t3 t4 (Z_to_bv 64 POD_STRING) (Z_to_bv 64 1))
        F (Z_to_bv 64 0x14504) fc None m1 (seg_rom rsegs)).
Proof.
  intros v HH t0 t1 t2 a0 a1 a3 a4 a5 s7 s9 s10 s11 t3 t4 F fc m1 cells keys rf HF HFP (ML1 & H90 & _) HL HE Hv ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  (* 0x14504 ld a0,0x90(sp); beqz t6; j 0x14268 *)
  pose proof (read_le8 rsegs m1 (SP + 144) _ H90) as HR. step. clear HR.
  step. if_false. step.
  replace (Z.of_nat v + 1) with (Z.of_nat (S v)) by lia.
  eapply HH; [exact HF | exact HFP | exact ML1 | exact HL | exact HE | exact Hv].
Qed.

(** The refusal store 0x144fc `sw a5,0x13c(sp)`. *)
Lemma MemP_rf : forall m1 cells keys rf bad v, MP m1 cells keys rf v -> (length cells <= X_CELLS)%nat ->
  store_ok rsegs m1 (wa (SP + 0x13c)) (length (le4 (Z_to_bv 64 bad))) = true ->
  MP (write_to_mem m1 (wa (SP + 0x13c)) (le4 (Z_to_bv 64 bad))) cells keys bad v.
Proof.
  intros m1 cells keys rf bad v ((MB1 & HX & HN & HK & HR) & H90 & H98 & Ha0 & Ha8 & Hb0) Hc HS.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _). rewrite length_le4 in HS.
  assert (LX : length (x_cellz cells) = 120%nat) by (apply length_x_cellz; exact Hc).
  split; [split|].
  - apply MemB_store; rewrite ?length_le4; [exact MB1 | exact HS | lia | lia].
  - refine (conj _ (conj _ (conj _ _))).
    + apply bytes_at_write_other; rewrite ?length_le4, ?LX; [exact HX | lia | lia | lia].
    + apply bytes_at_write_other; rewrite ?length_le4; [exact HN | lia | lia | lia].
    + apply bytes_at_write_other; rewrite ?length_le4; [exact HK | lia | lia | lia].
    + apply bytes_at_write_same; rewrite ?length_le4; lia.
  - refine (conj _ (conj _ (conj _ (conj _ _)))); apply bytes_at_write_other; rewrite ?length_le4, ?length_le8;
      first [eassumption | lia].
Qed.

(** ** 0x144f4 .. 0x14500: the refusal a5 is stored when x->refusal is still NONE; s9 := n; then 0x14504 *)
Lemma fold_ok : forall v, head_P (S v) ->
  forall (t0 t1 t2 a0 a1 a3 a4 s7 s9 s10 s11 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf bad : Z),
  frm0 fc -> FPinv F -> MP m1 cells keys rf v -> Linv cap cells keys rf (S v) -> 0 <= bad <= 5 ->
  bytes_at rsegs m1 (SP + 0x40) (le8 (Z_to_bv 64 (Z.of_nat (length cells)))) ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn (S v) es) None) cells keys
                   (if rf =? REFUSE_NONE then bad else rf)) -> (S v <= n)%nat ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 (NOT_BODY pp)) sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 a0 a1
             (Z_to_bv 64 (pp + POD_NENT_OFF)) a3 a4 (Z_to_bv 64 bad) (Z_to_bv 64 MULHU_104)
             (Z_to_bv 64 (pp + OFF_ENT + 8)) (Z_to_bv 64 cap) s3 s4 s5 s6 s7 (Z_to_bv 64 (pp + OFF_ENT)) s9 s10 s11
             t3 t4 (Z_to_bv 64 POD_STRING) (Z_to_bv 64 1))
        F (Z_to_bv 64 0x144f4) fc None m1 (seg_rom rsegs)).
Proof.
  intros v HH t0 t1 t2 a0 a1 a3 a4 s7 s9 s10 s11 t3 t4 F fc m1 cells keys rf bad HF HFP MP1 HL Hb H40 HE Hv.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  pose proof MP1 as ((MB1 & HX & HN & HK & HR) & _). pose proof MB1 as (MU & WM & MI & TM & ST & _).
  destruct HL as (HL1 & HL2 & HL3).
  (* 0x144f4 lw a0,0x13c(sp); bnez a0 *)
  pose proof (read_le4_cell rsegs m1 (SP + 316) _ HR) as HRd. step. clear HRd. rewrite sx32_small by lia.
  step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec rf 0) as [Er|Er]; cbn [negb]; cbv beta iota.
  - (* 0x144fc sw a5,0x13c(sp) *)
    assert (HS : store_ok rsegs m1 (wa (SP + 316)) 4 = true)
      by (apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
    step.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
      change A with (wa (SP + 0x13c));
      assert (MP2 : MP (write_to_mem m1 (wa (SP + 0x13c)) BS) cells keys bad v)
        by (apply MemP_rf with (rf := rf); [exact MP1 | unfold X_CELLS; lia | rewrite length_le4; exact HS]);
      assert (H40' : bytes_at rsegs (write_to_mem m1 (wa (SP + 0x13c)) BS) (SP + 0x40)
                       (le8 (Z_to_bv 64 (Z.of_nat (length cells)))))
        by (apply bytes_at_write_other; rewrite ?length_le4, ?length_le8; [exact H40 | lia | lia | lia]);
      revert MP2 H40'; generalize (write_to_mem m1 (wa (SP + 0x13c)) BS) as m2; intros m2 MP2 H40'
    end.
    subst rf. cbn [Z.eqb REFUSE_NONE] in HE.
    (* 0x14500 ld s9,0x40(sp) *)
    pose proof (read_le8 rsegs m2 (SP + 64) _ H40') as HRd. step. clear HRd.
    eapply back_ok; [exact HH | exact HF | exact HFP | exact MP2 | split; [exact HL1 | split; lia] | exact HE
                    | exact Hv | reflexivity].
  - replace (if rf =? REFUSE_NONE then bad else rf) with rf in HE
      by (unfold REFUSE_NONE; rewrite (proj2 (Z.eqb_neq _ _) Er); reflexivity).
    (* 0x14500 ld s9,0x40(sp) *)
    pose proof (read_le8 rsegs m1 (SP + 64) _ H40) as HRd. step. clear HRd.
    eapply back_ok; [exact HH | exact HF | exact HFP | exact MP1 | split; [exact HL1 | split; lia] | exact HE
                    | exact Hv | reflexivity].
Qed.

(** The memory of the cell write (0x1472c-0x14760): MemB, n in sp + 0x40, x->n, keys, refusal and the five saves;
    x's cells part apart. *)
Definition MemW (m1 : word -> option byte) (c keys rf : Z) (v : nat) : Prop :=
  MB m1 /\ bytes_at rsegs m1 (SP + 0x40) (le8 (Z_to_bv 64 c)) /\
  bytes_at rsegs m1 (SP + 0x134) (le4 (Z_to_bv 64 c)) /\ bytes_at rsegs m1 (SP + 0x138) (le4 (Z_to_bv 64 keys)) /\
  bytes_at rsegs m1 (SP + 0x13c) (le4 (Z_to_bv 64 rf)) /\
  bytes_at rsegs m1 (SP + 0x90) (le8 (Z_to_bv 64 (Z.of_nat v + 1))) /\
  bytes_at rsegs m1 (SP + 0x98) (le8 (Z_to_bv 64 MULHU_104)) /\
  bytes_at rsegs m1 (SP + 0xa0) (le8 (Z_to_bv 64 (pp + OFF_ENT + 8))) /\
  bytes_at rsegs m1 (SP + 0xa8) (le8 (Z_to_bv 64 (NOT_BODY pp))) /\
  bytes_at rsegs m1 (SP + 0xb0) (le8 (Z_to_bv 64 1)).

(** A store into x's cells part. *)
Lemma MemW_store : forall m1 c keys rf v a bs, MemW m1 c keys rf v ->
  store_ok rsegs m1 (wa a) (length bs) = true -> SP + 0xbc <= a -> a + Z.of_nat (length bs) <= SP + 0x134 ->
  MemW (write_to_mem m1 (wa a) bs) c keys rf v.
Proof.
  intros m1 c keys rf v a bs (MB1 & H40 & HN & HK & HR & H90 & H98 & Ha0 & Ha8 & Hb0) HS H1 H2.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _).
  split; [apply MemB_store; [exact MB1 | exact HS | lia | lia]|].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); apply bytes_at_write_other;
    rewrite ?length_le4, ?length_le8; first [eassumption | lia].
Qed.

(** The last store of the cell write, 0x14760 `sw s9,0x134(sp)`: n + 1 cells. *)
Lemma MemW_fin : forall m1 (cells : list cell) keys rf v cl, MemW m1 (Z.of_nat (length cells)) keys rf v ->
  bytes_at rsegs m1 (SP + 0xbc) (x_cellz cl) -> (length cl = S (length cells))%nat -> (length cl <= X_CELLS)%nat ->
  store_ok rsegs m1 (wa (SP + 0x134)) (length (le4 (Z_to_bv 64 (Z.of_nat (length cells) + 1)))) = true ->
  MP (write_to_mem m1 (wa (SP + 0x134)) (le4 (Z_to_bv 64 (Z.of_nat (length cells) + 1)))) cl keys rf v.
Proof.
  intros m1 cells keys rf v cl (MB1 & H40 & HN & HK & HR & H90 & H98 & Ha0 & Ha8 & Hb0) HX Hl Hc HS.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & _). rewrite length_le4 in HS.
  assert (LX : length (x_cellz cl) = 120%nat) by (apply length_x_cellz; exact Hc).
  split; [split|].
  - apply MemB_store; rewrite ?length_le4; [exact MB1 | exact HS | lia | lia].
  - refine (conj _ (conj _ (conj _ _))).
    + apply bytes_at_write_other; rewrite ?length_le4, ?LX; [exact HX | lia | lia | lia].
    + replace (Z.of_nat (length cl)) with (Z.of_nat (length cells) + 1) by lia.
      apply bytes_at_write_same; rewrite ?length_le4; lia.
    + apply bytes_at_write_other; rewrite ?length_le4; [exact HK | lia | lia | lia].
    + apply bytes_at_write_other; rewrite ?length_le4; [exact HR | lia | lia | lia].
  - refine (conj _ (conj _ (conj _ (conj _ _)))); apply bytes_at_write_other; rewrite ?length_le4, ?length_le8;
      first [eassumption | lia].
Qed.

(** A store over one int of x's cells part. *)
Lemma bytes_at_write_at : forall m1 A X Y Y' Z a, bytes_at rsegs m1 A (X ++ Y ++ Z) -> length Y' = length Y ->
  a = A + Z.of_nat (length X) -> bytes_at rsegs (write_to_mem m1 (wa a) Y') A (X ++ Y' ++ Z).
Proof. intros m1 A X Y Y' Z a H L ->. exact (bytes_at_write_mid rsegs m1 A X Y Y' Z H L). Qed.

(** 0x14744 .. 0x14778: the overflow check of &x->cell[x->n], x->cell[n].param and .value, x->n = n + 1, t6 :=
    pp->params_struct, the reloads; then 0x14504. *)
Lemma cellw2_ok : forall v, head_P (S v) ->
  forall (t0 t1 t2 a0 a1 a2 a5 s10 s11 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf ch p val : Z),
  frm0 fc -> FPinv F -> MemW m1 (Z.of_nat (length cells)) keys rf v ->
  bytes_at rsegs m1 (SP + 0xbc)
    (x_cells_bytes cells ++ le4 (Z_to_bv 64 ch) ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++
     repeat (Z_to_bv 8 0) (12 * (X_CELLS - S (length cells)))) ->
  Z.of_nat (length cells) < cap -> 0 <= keys <= Z.of_nat (S v) -> 0 <= rf <= 5 ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn (S v) es) None) (cells ++ [(ch, p, val)]) keys rf) ->
  (S v <= n)%nat ->
  a0 = Z_to_bv 64 (Z.of_nat (length cells)) -> a1 = Z_to_bv 64 (12 * Z.of_nat (length cells)) ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 (NOT_BODY pp)) sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 a0 a1 a2 (Z_to_bv 64 9)
             (Z_to_bv 64 p) a5 (Z_to_bv 64 MULHU_104) (Z_to_bv 64 (pp + OFF_ENT + 8)) (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 val) (Z_to_bv 64 (pp + OFF_ENT)) (Z_to_bv 64 ch) s10 s11 t3 t4 (Z_to_bv 64 POD_STRING)
             (Z_to_bv 64 1))
        F (Z_to_bv 64 0x14744) fc None m1 (seg_rom rsegs)).
Proof.
  intros v HH t0 t1 t2 a0 a1 a2 a5 s10 s11 t3 t4 F fc m1 cells keys rf ch p val HF HFP MW HX Hc HK HR HE Hv -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  assert (HL10 : (length cells < X_CELLS)%nat) by (unfold X_CELLS; lia).
  pose proof MW as ((MU & WM & MI & TM & ST & HPPB & _ & _ & _ & _ & H68 & H78 & H80 & _) & _).
  (* 0x14744 ld a2,0x80(sp); bltu a2,a1 *)
  pose proof (read_le8 rsegs m1 (SP + 128) _ H80) as HRd. step. clear HRd.
  step. rewrite ltu_u by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x1474c addi a2,sp,0xbc; add a1,a2,a1; addi s9,a0,1 *)
  step. step. step.
  (* 0x14758 sw a4,4(a1) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 192 + 12 * Z.of_nat (length cells))) 4 = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 192 + 12 * Z.of_nat (length cells)));
    assert (MW2 : MemW (write_to_mem m1 (wa (SP + 192 + 12 * Z.of_nat (length cells))) BS)
                    (Z.of_nat (length cells)) keys rf v)
      by (apply MemW_store; rewrite ?length_le4; [exact MW | exact HS | lia | lia]);
    assert (HX2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 192 + 12 * Z.of_nat (length cells))) BS) (SP + 0xbc)
                    ((x_cells_bytes cells ++ le4 (Z_to_bv 64 ch)) ++ BS ++ le4 (Z_to_bv 64 0) ++
                     repeat (Z_to_bv 8 0) (12 * (X_CELLS - S (length cells)))))
      by (apply bytes_at_write_at with (Y := le4 (Z_to_bv 64 0));
          [rewrite <- app_assoc; exact HX | rewrite !length_le4; reflexivity
          | rewrite length_app, length_x_cells_bytes, length_le4; lia]);
    revert MW2 HX2; generalize (write_to_mem m1 (wa (SP + 192 + 12 * Z.of_nat (length cells))) BS) as m2;
    intros m2 MW2 HX2
  end.
  clear MU WM MI TM ST HPPB H68 H78 H80 HS MW HX.
  pose proof MW2 as ((MU & WM & MI & TM & ST & _) & _).
  (* 0x1475c sw s7,8(a1) *)
  assert (HS : store_ok rsegs m2 (wa (SP + 196 + 12 * Z.of_nat (length cells))) 4 = true)
    by (apply (stk_store_ok rsegs m2 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m2 ?A ?BS) _) =>
    change A with (wa (SP + 196 + 12 * Z.of_nat (length cells)));
    assert (MW3 : MemW (write_to_mem m2 (wa (SP + 196 + 12 * Z.of_nat (length cells))) BS)
                    (Z.of_nat (length cells)) keys rf v)
      by (apply MemW_store; rewrite ?length_le4; [exact MW2 | exact HS | lia | lia]);
    assert (HX3 : bytes_at rsegs (write_to_mem m2 (wa (SP + 196 + 12 * Z.of_nat (length cells))) BS) (SP + 0xbc)
                    (((x_cells_bytes cells ++ le4 (Z_to_bv 64 ch)) ++ le4 (Z_to_bv 64 p)) ++ BS ++
                     repeat (Z_to_bv 8 0) (12 * (X_CELLS - S (length cells)))))
      by (apply bytes_at_write_at with (Y := le4 (Z_to_bv 64 0));
          [rewrite <- (app_assoc (x_cells_bytes cells ++ le4 (Z_to_bv 64 ch))); exact HX2
          | rewrite !length_le4; reflexivity
          | rewrite !length_app, length_x_cells_bytes, !length_le4; lia]);
    revert MW3 HX3; generalize (write_to_mem m2 (wa (SP + 196 + 12 * Z.of_nat (length cells))) BS) as m3;
    intros m3 MW3 HX3
  end.
  clear MU WM MI TM ST HS MW2 HX2.
  rewrite <- !app_assoc in HX3. rewrite <- x_cellz_add in HX3 by exact HL10.
  pose proof MW3 as ((MU & WM & MI & TM & ST & _) & _).
  (* 0x14760 sw s9,0x134(sp) *)
  assert (HS : store_ok rsegs m3 (wa (SP + 308)) 4 = true)
    by (apply (stk_store_ok rsegs m3 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m3 ?A ?BS) _) =>
    change A with (wa (SP + 0x134));
    assert (MP4 : MP (write_to_mem m3 (wa (SP + 0x134)) BS) (cells ++ [(ch, p, val)]) keys rf v)
      by (apply MemW_fin with (cells := cells);
          [exact MW3 | exact HX3 | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
          | rewrite length_le4; exact HS]);
    revert MP4; generalize (write_to_mem m3 (wa (SP + 0x134)) BS) as m4; intros m4 MP4
  end.
  clear MU WM MI TM ST HS MW3 HX3.
  pose proof MP4 as ((MB4 & _) & _). pose proof MB4 as (_ & _ & _ & _ & _ & HPPB & _ & _ & _ & _ & H68 & H78 & _).
  (* 0x14764 ld a0,0x78(sp); lw t6,0x10(a0); ld a2,0x68(sp); ld a6,0x98(sp); ld a7,0xa0(sp); j 0x14504 *)
  change POD_LEN_OFF with 16384 in H78.
  pose proof (read_le8 rsegs m4 (SP + 120) _ H78) as HRd. step. clear HRd.
  assert (HRd : ov_read_bytes rsegs m4 (wa (pp + 16400)) 4 = Some (le4 (Z_to_bv 64 1))).
  { apply (read_field rsegs m4 pp r 16400 1 HPPB HWF); [|lia | unfold PP_SIZE; lia | lia].
    pose proof (pp_params_struct r HWF) as X. rewrite HPS in X. exact X. }
  step. clear HRd. rewrite sx32_small by lia.
  pose proof (read_le8 rsegs m4 (SP + 104) _ H68) as HRd. step. clear HRd.
  pose proof MP4 as (_ & _ & H98 & Ha0 & _).
  pose proof (read_le8 rsegs m4 (SP + 152) _ H98) as HRd. step. clear HRd.
  pose proof (read_le8 rsegs m4 (SP + 160) _ Ha0) as HRd. step. clear HRd.
  step.
  eapply back_ok; [exact HH | exact HF | exact HFP | exact MP4 | | exact HE | exact Hv | ].
  - split; [rewrite length_app; cbn [length]; lia | split; lia].
  - rewrite length_app. cbn [length]. weq.
Qed.

(** 0x1471c .. 0x14740: the overflow check of &x->cell[n], x->cell[n].ch = ch, x->n read back (lwu) with its bound
    9 and 12 x->n. *)
Lemma cellw_ok : forall v, head_P (S v) ->
  forall (t0 t1 t2 a0 a1 a2 a5 s10 s11 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf ch p val : Z),
  frm0 fc -> FPinv F -> MemW m1 (Z.of_nat (length cells)) keys rf v ->
  bytes_at rsegs m1 (SP + 0xbc) (x_cellz cells) ->
  Z.of_nat (length cells) < cap -> 0 <= keys <= Z.of_nat (S v) -> 0 <= rf <= 5 ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn (S v) es) None) (cells ++ [(ch, p, val)]) keys rf) ->
  (S v <= n)%nat ->
  a0 = Z_to_bv 64 (12 * Z.of_nat (length cells)) ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 (NOT_BODY pp)) sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 a0 a1 a2 (Z_to_bv 64 9)
             (Z_to_bv 64 p) a5 (Z_to_bv 64 MULHU_104) (Z_to_bv 64 (pp + OFF_ENT + 8)) (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 val) (Z_to_bv 64 (pp + OFF_ENT)) (Z_to_bv 64 ch) s10 s11 t3 t4 (Z_to_bv 64 POD_STRING)
             (Z_to_bv 64 1))
        F (Z_to_bv 64 0x1471c) fc None m1 (seg_rom rsegs)).
Proof.
  intros v HH t0 t1 t2 a0 a1 a2 a5 s10 s11 t3 t4 F fc m1 cells keys rf ch p val HF HFP MW HX Hc HK HR HE Hv ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  assert (HL10 : (length cells < X_CELLS)%nat) by (unfold X_CELLS; lia).
  rewrite x_cellz_open in HX by exact HL10.
  pose proof MW as ((MU & WM & MI & TM & ST & _ & _ & _ & _ & _ & _ & _ & H80 & _) & _).
  (* 0x1471c ld a1,0x80(sp); bltu a1,a0 *)
  pose proof (read_le8 rsegs m1 (SP + 128) _ H80) as HRd. step. clear HRd.
  step. rewrite ltu_u by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x14724 addi a1,sp,0xbc; add a0,a1,a0; sw s9,0(a0) *)
  step. step.
  assert (HS : store_ok rsegs m1 (wa (SP + 188 + 12 * Z.of_nat (length cells))) 4 = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 188 + 12 * Z.of_nat (length cells)));
    assert (MW2 : MemW (write_to_mem m1 (wa (SP + 188 + 12 * Z.of_nat (length cells))) BS)
                    (Z.of_nat (length cells)) keys rf v)
      by (apply MemW_store; rewrite ?length_le4; [exact MW | exact HS | lia | lia]);
    assert (HX2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 188 + 12 * Z.of_nat (length cells))) BS) (SP + 0xbc)
                    (x_cells_bytes cells ++ BS ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++
                     repeat (Z_to_bv 8 0) (12 * (X_CELLS - S (length cells)))))
      by (apply bytes_at_write_at with (Y := le4 (Z_to_bv 64 0));
          [exact HX | rewrite !length_le4; reflexivity | rewrite length_x_cells_bytes; lia]);
    revert MW2 HX2; generalize (write_to_mem m1 (wa (SP + 188 + 12 * Z.of_nat (length cells))) BS) as m2;
    intros m2 MW2 HX2
  end.
  clear MU WM MI TM ST H80 HS MW HX.
  pose proof MW2 as (_ & _ & HN2 & _).
  (* 0x14730 lwu a0,0x134(sp); bltu a3,a0 *)
  pose proof (read_le4_cell rsegs m2 (SP + 308) _ HN2) as HRd. step. clear HRd.
  step. rewrite (zx32_lit (Z.of_nat (length cells))) by lia.
  rewrite ltu_u by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x14738 slli a1,a0,2; slli a2,a0,4; sub a1,a2,a1 *)
  step. step. step.
  eapply cellw2_ok; [exact HH | exact HF | exact HFP | exact MW2 | exact HX2 | exact Hc | exact HK | exact HR | exact HE
                    | exact Hv | reflexivity | ].
  apply Z_to_bv_eqm. rewrite ?unsigned_lit_wrap. rewrite ?Z.shiftl_mul_pow2 by lia. Z.div_mod_to_equations. lia.
Qed.

(** ** 0x146fc .. 0x14718: the cap test `bge n,s2` (n >= cap: the loop stops, s9 := n), the bound 9 of x->cell[n]
    and 12 n *)
Lemma cap_ok : forall v k e, head_P (S v) -> ha_prefix k = true ->
  forall (t0 t1 t2 a0 a1 a5 s10 s11 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf ch p val : Z),
  frm0 fc -> FPinv F -> MP m1 cells (keys + 1) rf v -> Linv cap cells (keys + 1) rf (S v) ->
  bytes_at rsegs m1 (SP + 0x40) (le8 (Z_to_bv 64 (Z.of_nat (length cells)))) ->
  expect_cell k e = inr (ch, p, val) ->
  E = ha_result (ha_fold expect_cell cap ((k, e) :: pairs_by key_of (skipn (S v) es) None) cells keys rf) ->
  (S v <= n)%nat ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 (NOT_BODY pp)) sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 a0 a1
             (Z_to_bv 64 (pp + POD_NENT_OFF)) (Z_to_bv 64 9) (Z_to_bv 64 p) a5 (Z_to_bv 64 MULHU_104)
             (Z_to_bv 64 (pp + OFF_ENT + 8)) (Z_to_bv 64 cap) s3 s4 s5 s6 (Z_to_bv 64 val) (Z_to_bv 64 (pp + OFF_ENT))
             (Z_to_bv 64 ch) s10 s11 t3 t4 (Z_to_bv 64 POD_STRING) (Z_to_bv 64 1))
        F (Z_to_bv 64 0x146fc) fc None m1 (seg_rom rsegs)).
Proof.
  intros v k e HH HP t0 t1 t2 a0 a1 a5 s10 s11 t3 t4 F fc m1 cells keys rf ch p val HF HFP MP1 HL H40 HC HE Hv.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn). destruct HL as (HL1 & HL2 & HL3).
  (* 0x146fc ld a1,0x40(sp); sext.w a0,a1; bge a0,s2 *)
  pose proof (read_le8 rsegs m1 (SP + 64) _ H40) as HRd. step. clear HRd.
  step. rewrite sextw_small by lia.
  step. rewrite lts_s by lia.
  destruct (Z.ltb_spec (Z.of_nat (length cells)) cap) as [Hc|Hc]; cbn [negb]; cbv beta iota.
  2:{ (* 0x148a4 mv s9,a1; j 0x14780 *)
      rewrite (ha_fold_full expect_cell cap k e _ cells keys rf _ HP HC Hc) in HE.
      step. step.
      eapply exit_ok; [exact HF | exact (proj1 MP1) | exact HL1 | exact HE]. }
  rewrite (ha_fold_add expect_cell cap k e _ cells keys rf _ HP HC Hc) in HE.
  pose proof MP1 as ((MB1 & HX & HN & HK & HR) & H90 & H98 & Ha0 & Ha8 & Hb0).
  assert (MW : MemW m1 (Z.of_nat (length cells)) (keys + 1) rf v)
    by (exact (conj MB1 (conj H40 (conj HN (conj HK (conj HR (conj H90 (conj H98 (conj Ha0 (conj Ha8 Hb0)))))))))).
  (* 0x14708 bltu a3,a1 *)
  step. rewrite ltu_u by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x1470c ld a1,0x40(sp); slli a0,a1,2; slli a1,a1,4; sub a0,a1,a0 *)
  pose proof (read_le8 rsegs m1 (SP + 64) _ H40) as HRd. step. clear HRd.
  step. step. step.
  eapply cellw_ok; [exact HH | exact HF | exact HFP | exact MW | exact HX | exact Hc | lia | exact HL3 | exact HE
                   | exact Hv | ].
  apply Z_to_bv_eqm. rewrite ?unsigned_lit_wrap. rewrite ?Z.shiftl_mul_pow2 by lia. Z.div_mod_to_equations. lia.
Qed.

(** ** 0x14354: the pair (k, ent[v]) with the prefix: the key piece, then the refusal fold or the cap test *)
Lemma pair_ok : forall v k K, (v < n)%nat -> head_P (S v) -> ha_prefix k = true ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte) (cells : list cell) (keys rf : Z),
  frm0 fc -> FPinv F -> MP m1 cells keys rf v -> Linv cap cells keys rf v ->
  E = ha_result (ha_fold expect_cell cap ((k, nth v es (Ent 0 0 [])) :: pairs_by key_of (skipn (S v) es) None)
                   cells keys rf) ->
  0 < K -> bytes_at rsegs m1 K (k ++ [NUL]) -> K + Z.of_nat (length k) + 1 <= lo -> ~ In NUL k ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
             (Z_to_bv 64 (104 * Z.of_nat v)) (Z_to_bv 64 (pp + OFF_ENT)) (Z_to_bv 64 (Z.of_nat (length cells)))
             (Z_to_bv 64 (Z.of_nat v)) (Z_to_bv 64 K) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14354) fc None m1 (seg_rom rsegs)).
Proof.
  intros v k K Hv HH HP ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 cells keys rf
    HF HFP MP1 HL HE HK0 HKB HKL HNK.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn). destruct HL as (HL1 & HL2 & HL3).
  pose proof MP1 as ((MB1 & HX & HN & HK & HR) & H90 & H98 & Ha0 & Ha8 & Hb0).
  pose proof MB1 as (MU & WM & MI & TM & ST & HPPB & H48 & H50 & H58 & H60 & H68 & H78 & H80 & H88).
  pose proof (ent_wf_nth r v HWF Hv) as HEW.
  pose proof (bytes_at_ent rsegs m1 pp r v HPPB HWF Hv) as HEB.
  pose proof HFP as (HF9 & HF18 & HF19).
  apply (KEY Q ra sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) s3 s4 s5 s6
           (Z_to_bv 64 (104 * Z.of_nat v)) (Z_to_bv 64 (pp + OFF_ENT)) (Z_to_bv 64 (Z.of_nat (length cells)))
           (Z_to_bv 64 (Z.of_nat v)) (Z_to_bv 64 K) t3 t4 t5 t6 F fc m1 lo pp K keys k v (nth v es (Ent 0 0 []))
           (Z_to_bv 64 (pp + POD_NENT_OFF)) (Z_to_bv 64 MULHU_104) (Z_to_bv 64 (NOT_BODY pp)) (Z_to_bv 64 1));
    [ reflexivity | exact HKB | exact HNK | exact HP | exact HK0 | lia | reflexivity | reflexivity | reflexivity
    | reflexivity | lia | exact HEB | exact HEW | exact HPP0 | exact HPPLO | exact H68 | exact H88 | exact H98
    | exact Ha0 | exact Ha8 | exact Hb0 | exact HK | lia | exact HF9 | exact HF18 | exact HF19 | exact H48 | exact H50
    | exact H58 | exact H60 | exact ST | exact HLO | exact HSPA | exact HROM | exact HF | exact MI | exact TM | | ].
  - (* a refusal: 0x144f4 *)
    intros t0' t1' t2' a0' a1' a3' a4' s7' s9' s10' s11' t3' t4' F' fc' m' bad HC HF' HFF MU' WM' MI' TM' ST' HK' H40.
    rewrite (ha_fold_bad expect_cell cap k _ _ cells keys rf bad HP HC) in HE.
    eapply fold_ok; [exact HH | exact HF' | exact (FPinv_keep F F' HFP HFF)
                    | exact (MemP_key m1 m' cells keys rf v MP1 ltac:(unfold X_CELLS; lia) MU' WM' MI' TM' ST' HK')
                    | split; [exact HL1 | split; lia]
                    | destruct (expect_cell_bad k _ bad HC) as [-> | ->]; unfold REFUSE_BAD_KEY, REFUSE_OUT_OF_RANGE; lia
                    | exact H40 | exact HE | lia].
  - (* a cell: 0x146fc *)
    intros t0' t1' t2' a0' a1' a5' s10' s11' t3' t4' F' fc' m' ch p val HC HF' HFF MU' WM' MI' TM' ST' HK' H40.
    eapply cap_ok; [exact HH | exact HP | exact HF' | exact (FPinv_keep F F' HFP HFF)
                   | exact (MemP_key m1 m' cells keys rf v MP1 ltac:(unfold X_CELLS; lia) MU' WM' MI' TM' ST' HK')
                   | split; [exact HL1 | split; lia] | exact H40 | exact HC | exact HE | lia].
Qed.

(** ** pod_next_pair's scan (0x14294 .. 0x14350), by induction on the entries left *)
(** The key slot after entry i: empty, or the key k at K (inside the pp block). *)
Definition slot_ok (m1 : word -> option byte) (ko : option (list byte)) (K : Z) : Prop :=
  match ko with
  | Some k => 0 < K /\ bytes_at rsegs m1 K (k ++ [NUL]) /\ K + Z.of_nat (length k) + 1 <= lo /\ ~ In NUL k
  | None => True
  end.

(** At 0x14294 with the key slot empty (s11 = NULL) and the scan at entry i: s10 = a0 = i, s7 = 104 i, a3 = ~&ent[i].body
    (the sanitizer's bound of body + size - 1), a1 = n_ent, a2 = 33 (the bound of ent[i]). *)
Definition none_P (i : nat) : Prop :=
  forall (t0 t1 t2 a0 a3 a4 a5 s7 s10 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte)
         (cells : list cell) (keys rf : Z),
  frm0 fc -> FPinv F -> ML m1 cells keys rf -> Linv cap cells keys rf i ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn i es) None) cells keys rf) -> (i < n)%nat ->
  a0 = Z_to_bv 64 (Z.of_nat i) -> a3 = Z_to_bv 64 (NOT_BODY pp - 104 * Z.of_nat i) ->
  s7 = Z_to_bv 64 (104 * Z.of_nat i) -> s10 = Z_to_bv 64 (Z.of_nat i) ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 (NOT_BODY pp)) sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 a0 (Z_to_bv 64 (Z.of_nat n))
             (Z_to_bv 64 33) a3 a4 a5 (Z_to_bv 64 MULHU_104) (Z_to_bv 64 (pp + OFF_ENT + 8)) (Z_to_bv 64 cap)
             s3 s4 s5 s6 s7 (Z_to_bv 64 (pp + OFF_ENT)) (Z_to_bv 64 (Z.of_nat (length cells))) s10 (Z_to_bv 64 0)
             t3 t4 (Z_to_bv 64 POD_STRING) (Z_to_bv 64 1))
        F (Z_to_bv 64 0x14294) fc None m1 (seg_rom rsegs)).

(** At 0x14294 with the key k at K in the slot: entry v is its value. *)
Definition some_P (v : nat) (k : list byte) (K : Z) : Prop :=
  forall (t0 t1 t2 a0 a3 a4 a5 s7 s10 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte)
         (cells : list cell) (keys rf : Z),
  frm0 fc -> FPinv F -> ML m1 cells keys rf -> Linv cap cells keys rf v ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn v es) (Some k)) cells keys rf) -> (v < n)%nat ->
  0 < K -> bytes_at rsegs m1 K (k ++ [NUL]) -> K + Z.of_nat (length k) + 1 <= lo -> ~ In NUL k ->
  a0 = Z_to_bv 64 (Z.of_nat v) -> a3 = Z_to_bv 64 (NOT_BODY pp - 104 * Z.of_nat v) ->
  s7 = Z_to_bv 64 (104 * Z.of_nat v) -> s10 = Z_to_bv 64 (Z.of_nat v) ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 (NOT_BODY pp)) sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 a0 (Z_to_bv 64 (Z.of_nat n))
             (Z_to_bv 64 33) a3 a4 a5 (Z_to_bv 64 MULHU_104) (Z_to_bv 64 (pp + OFF_ENT + 8)) (Z_to_bv 64 cap)
             s3 s4 s5 s6 s7 (Z_to_bv 64 (pp + OFF_ENT)) (Z_to_bv 64 (Z.of_nat (length cells))) s10 (Z_to_bv 64 K)
             t3 t4 (Z_to_bv 64 POD_STRING) (Z_to_bv 64 1))
        F (Z_to_bv 64 0x14294) fc None m1 (seg_rom rsegs)).

(** The constants of the scan as equations lia uses, the definitions staying folded in the states. *)
Lemma consts_eq : NOT_BODY pp = 2^64 - 1 - (pp + 16412) /\ NOT_ENT pp = 2^64 - 1 - (pp + 16404) /\ OFF_ENT = 16404 /\
  MULHU_104 = 446676598784 /\ POD_STRING = 8 /\ POD_NENT_OFF = 19732 /\ ENT_SIZE = 104.
Proof. unfold NOT_BODY, NOT_ENT, OFF_ENT, MULHU_104, POD_STRING, POD_NENT_OFF, ENT_SIZE. repeat split; lia. Qed.

Ltac weqn := weq.
(* A sanitizer check `bltu x, y` to the trap that is not taken. *)
Ltac ltu_no := rewrite ltu_u by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; cbv beta iota.

(** 0x142e8 .. 0x142fc: the next entry, or no pair is left. *)
Lemma end_ok : forall i, (i < n)%nat -> ((S i < n)%nat -> none_P (S i) /\ (forall k K, some_P (S i) k K)) ->
  forall (t0 t1 t2 a0 a3 a4 a5 s7 s10 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : word -> option byte)
         (cells : list cell) (keys rf : Z) (ko : option (list byte)) (K : Z),
  frm0 fc -> FPinv F -> ML m1 cells keys rf -> Linv cap cells keys rf i ->
  E = ha_result (ha_fold expect_cell cap (pairs_by key_of (skipn (S i) es) ko) cells keys rf) -> slot_ok m1 ko K ->
  a0 = Z_to_bv 64 (Z.of_nat i) -> a3 = Z_to_bv 64 (NOT_BODY pp - 104 * Z.of_nat i) ->
  s7 = Z_to_bv 64 (104 * Z.of_nat i) -> s10 = Z_to_bv 64 (Z.of_nat i) ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 (NOT_BODY pp)) sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 a0 (Z_to_bv 64 (Z.of_nat n))
             (Z_to_bv 64 33) a3 a4 a5 (Z_to_bv 64 MULHU_104) (Z_to_bv 64 (pp + OFF_ENT + 8)) (Z_to_bv 64 cap)
             s3 s4 s5 s6 s7 (Z_to_bv 64 (pp + OFF_ENT)) (Z_to_bv 64 (Z.of_nat (length cells))) s10
             (match ko with Some _ => Z_to_bv 64 K | None => Z_to_bv 64 0 end)
             t3 t4 (Z_to_bv 64 POD_STRING) (Z_to_bv 64 1))
        F (Z_to_bv 64 0x142e8) fc None m1 (seg_rom rsegs)).
Proof.
  intros i Hi HI t0 t1 t2 a0 a3 a4 a5 s7 s10 t3 t4 F fc m1 cells keys rf ko K HF HFP ML1 HL HE HS -> -> -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  destruct HL as (HL1 & HL2 & HL3).
  pose proof consts_eq as (EC1 & EC2 & EC3 & EC4 & EC5 & EC6 & EC7).
  (* 0x142e8 addi s10,s10,1; addi s7,s7,0x68; addiw a0,a0,1; addi a3,a3,-0x68; bge s10,a1 *)
  step. step. step. step. step. rewrite lts_s by lia.
  destruct (Z.ltb_spec (Z.of_nat i + 1) (Z.of_nat n)) as [Hl|Hl]; cbn [negb]; cbv beta iota.
  - (* 0x142fc j 0x14294 *)
    step.
    destruct (HI ltac:(lia)) as [HN HSm]. unfold none_P in HN. unfold some_P in HSm. destruct ko as [k|].
    + destruct HS as (HK0 & HKB & HKL & HNK).
      eapply (HSm k K); [exact HF | exact HFP | exact ML1 | split; [exact HL1 | split; lia] | exact HE | lia
                        | exact HK0 | exact HKB | exact HKL | exact HNK | weqn ..].
    + eapply HN; [exact HF | exact HFP | exact ML1 | split; [exact HL1 | split; lia] | exact HE | lia | weqn ..].
  - (* no pair is left: 0x14780 *)
    rewrite (pairs_end es (S i) ko) in HE by lia. rewrite ha_fold_nil in HE.
    eapply exit_ok; [exact HF | exact ML1 | exact HL1 | exact HE].
Qed.

(** 0x14294 .. 0x142e4: pod_string(&pp->ent[i]) on an empty key slot, with the bound 33 of ent[i] and the overflow
    checks of &ent[0] + 104 i and body + size - 1. *)
Lemma none_ok : forall i, ((S i < n)%nat -> none_P (S i) /\ (forall k K, some_P (S i) k K)) -> none_P i.
Proof.
  intros i HI. unfold none_P.
  intros t0 t1 t2 a0 a3 a4 a5 s7 s10 t3 t4 F fc m1 cells keys rf HF HFP ML1 HL HE Hi -> -> -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  pose proof (ent_wf_nth r i HWF Hi) as (Ht0 & Hb & Hsz).
  pose proof ML1 as ((MU & WM & MI & TM & ST & HPPB & _) & _).
  pose proof (bytes_at_ent rsegs m1 pp r i HPPB HWF Hi) as HEB.
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat i) with (pp + 16404 + 104 * Z.of_nat i) in HEB
    by (unfold OFF_ENT, ENT_SIZE; lia).
  pose proof consts_eq as (EC1 & EC2 & EC3 & EC4 & EC5 & EC6 & EC7).
  (* 0x14294 bnez s11; beq a2,s10; bltu s0,s7 *)
  step. if_false.
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  step. ltu_no.
  (* 0x142a0 add a4,s8,s7; lw a5,0(a4); bne a5,t5 *)
  step. pose proof (ent_type_read rsegs m1 _ _ HEB Ht0) as HR. step. clear HR.
  step. rewrite sx32_eqb by lia.
  destruct (Z.eqb_spec (e_type (nth i es (Ent 0 0 []))) POD_STRING) as [Et|Et]; cbn [negb]; cbv beta iota.
  2:{ (* not a String: 0x142e4 mv s11,zero *)
      assert (EK : key_of (nth i es (Ent 0 0 [])) = None)
        by (rewrite key_of_cases; rewrite (proj2 (Z.eqb_neq _ _) Et); reflexivity).
      rewrite (pairs_skip es i Hi EK) in HE.
      step.
      eapply (end_ok i Hi HI) with (ko := None) (K := 0);
        [exact HF | exact HFP | exact ML1 | exact HL | exact HE | exact I | reflexivity ..]. }
  (* 0x142ac lw a4,4(a4); beqz a4 *)
  pose proof (ent_size_read rsegs m1 _ _ HEB ltac:(lia)) as HR. step. clear HR.
  rewrite (sx32_small (e_size (nth i es (Ent 0 0 [])))) by lia.
  step. rewrite eqb_u by lia.
  destruct (Z.eqb_spec (e_size (nth i es (Ent 0 0 []))) 0) as [Ez|Ez]; cbv beta iota.
  { assert (EK : key_of (nth i es (Ent 0 0 [])) = None)
      by (rewrite key_of_cases; rewrite Ez; cbn [Z.leb Z.compare]; rewrite andb_false_r; reflexivity).
    rewrite (pairs_skip es i Hi EK) in HE.
    step.
    eapply (end_ok i Hi HI) with (ko := None) (K := 0);
      [exact HF | exact HFP | exact ML1 | exact HL | exact HE | exact I | reflexivity ..]. }
  (* 0x142b4 addi a4,a4,-1; slli a4,a4,32; srli a4,a4,32; bltu a3,a4 *)
  step. step. step. rewrite zext32_small by lia.
  step. ltu_no.
  (* 0x142c4 add a4,s7,a4; add a4,a7,a4; lbu a4,0(a4) *)
  step. step.
  pose proof (ent_byte_read rsegs m1 _ _ (Z.to_nat (e_size (nth i es (Ent 0 0 [])) - 1)) HEB ltac:(lia)) as HR.
  step. clear HR.
  (* 0x142d0 add a5,a7,s7; snez a4,a4; addi a4,a4,-1; and s11,a4,a5; j 0x142e8 *)
  step. step. step. step. rewrite snez_mask by lia. step.
  destruct (Z.eqb_spec (bv_unsigned (nth (Z.to_nat (e_size (nth i es (Ent 0 0 [])) - 1))
                                         (e_body (nth i es (Ent 0 0 []))) NUL)) 0) as [Eb|Eb]; cbv beta iota.
  - (* a key *)
    assert (EK : key_of (nth i es (Ent 0 0 [])) = Some (cstr (e_body (nth i es (Ent 0 0 []))))).
    { rewrite key_of_cases. unfold last_body_byte. rewrite (proj2 (Z.eqb_eq _ _) Et), Eb.
      rewrite (proj2 (Z.leb_le 1 _)) by lia. reflexivity. }
    rewrite (pairs_key es i _ Hi EK) in HE.
    assert (HNI : (nul_idx (e_body (nth i es (Ent 0 0 []))) < length (e_body (nth i es (Ent 0 0 []))))%nat).
    { pose proof (nul_idx_le_k (e_body (nth i es (Ent 0 0 []))) (Z.to_nat (e_size (nth i es (Ent 0 0 [])) - 1))
                    ltac:(lia) Eb). lia. }
    pose proof (ent_key_bytes rsegs m1 _ _ HEB HNI) as HKB.
    replace (pp + 16404 + 104 * Z.of_nat i + 8) with (pp + 16412 + 104 * Z.of_nat i) in HKB by lia.
    assert (LK : (length (cstr (e_body (nth i es (Ent 0 0 [])))) <= 45)%nat).
    { unfold cstr. rewrite length_firstn. lia. }
    eapply (end_ok i Hi HI) with (ko := Some (cstr (e_body (nth i es (Ent 0 0 [])))));
      [exact HF | exact HFP | exact ML1 | exact HL | exact HE | | weqn ..].
    match goal with |- slot_ok _ _ ?K => replace K with (pp + 16412 + 104 * Z.of_nat i) by lia end.
    cbn [slot_ok]. split; [lia|]. split; [exact HKB|]. split; [lia | apply cstr_no_nul].
  - (* not NUL-terminated *)
    assert (EK : key_of (nth i es (Ent 0 0 [])) = None).
    { rewrite key_of_cases. unfold last_body_byte. rewrite (proj2 (Z.eqb_neq _ _) Eb). rewrite andb_false_r. reflexivity. }
    rewrite (pairs_skip es i Hi EK) in HE.
    eapply (end_ok i Hi HI) with (ko := None) (K := 0);
      [exact HF | exact HFP | exact ML1 | exact HL | exact HE | exact I | weqn ..].
Qed.

(** 0x14294, 0x14300 .. 0x14350: the key k in the slot, its value ent[v]: the overflow check of at + 1, the saves
    of the next at, ra, a7, a6 and t6, strncmp(k, "reac.headamp.", 13); 0 goes to the key piece, else back to the
    head with the reloads. *)
Lemma some_ok : forall v k K, head_P (S v) -> some_P v k K.
Proof.
  intros v k K HH. unfold some_P.
  intros t0 t1 t2 a0 a3 a4 a5 s7 s10 t3 t4 F fc m1 cells keys rf HF HFP ML1 HL HE Hv HK0 HKB HKL HNK -> -> -> ->.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn). pose proof (proj1 HL) as HLc.
  pose proof consts_eq as (EC1 & EC2 & EC3 & EC4 & EC5 & EC6 & EC7).
  pose proof (bytes_at_bound rsegs m1 K _ HKB) as (KB0 & KB1).
  pose proof ML1 as ((MU & WM & MI & TM & ST & _) & _).
  assert (HLK : Z.of_nat (length (k ++ [NUL])) = Z.of_nat (length k) + 1) by (rewrite length_app; cbn [length]; lia).
  (* 0x14294 bnez s11 taken *)
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbn [negb]. cbv beta iota.
  (* 0x14300 addiw a1,a0,1; blt a1,a0; bltz a0 *)
  step. rewrite addiw1_small by lia.
  step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  step. rewrite lts_s by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x1430c sd a1,0x90(sp) *)
  assert (HS : store_ok rsegs m1 (wa (SP + 144)) 8 = true)
    by (apply (stk_store_ok rsegs m1 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?BS) _) =>
    change A with (wa (SP + 0x90));
    assert (ML2 : ML (write_to_mem m1 (wa (SP + 0x90)) BS) cells keys rf)
      by (apply MemL_store_save; rewrite ?length_le8; [exact ML1 | unfold X_CELLS; lia | exact HS | lia | lia]);
    assert (HKB2 : bytes_at rsegs (write_to_mem m1 (wa (SP + 0x90)) BS) K (k ++ [NUL]))
      by (apply bytes_at_write_other; rewrite ?length_le8, ?HLK; [exact HKB | lia | lia | lia]);
    assert (H90 : bytes_at rsegs (write_to_mem m1 (wa (SP + 0x90)) BS) (SP + 0x90) BS)
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    revert ML2 HKB2 H90; generalize (write_to_mem m1 (wa (SP + 0x90)) BS) as m2; intros m2 ML2 HKB2 H90
  end.
  clear MU WM MI TM ST HS ML1 HKB.
  pose proof ML2 as ((MU & WM & MI & TM & ST & _) & _).
  (* 0x14310 sd ra,0xa8(sp) *)
  assert (HS : store_ok rsegs m2 (wa (SP + 168)) 8 = true)
    by (apply (stk_store_ok rsegs m2 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m2 ?A ?BS) _) =>
    change A with (wa (SP + 0xa8));
    assert (ML3 : ML (write_to_mem m2 (wa (SP + 0xa8)) BS) cells keys rf)
      by (apply MemL_store_save; rewrite ?length_le8; [exact ML2 | unfold X_CELLS; lia | exact HS | lia | lia]);
    assert (HKB3 : bytes_at rsegs (write_to_mem m2 (wa (SP + 0xa8)) BS) K (k ++ [NUL]))
      by (apply bytes_at_write_other; rewrite ?length_le8, ?HLK; [exact HKB2 | lia | lia | lia]);
    assert (H90' : bytes_at rsegs (write_to_mem m2 (wa (SP + 0xa8)) BS) (SP + 0x90)
                     (le8 (Z_to_bv 64 (Z.of_nat v + 1))))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact H90 | lia | lia | lia]);
    assert (Ha8 : bytes_at rsegs (write_to_mem m2 (wa (SP + 0xa8)) BS) (SP + 0xa8) BS)
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    revert ML3 HKB3 H90' Ha8; generalize (write_to_mem m2 (wa (SP + 0xa8)) BS) as m3; intros m3 ML3 HKB3 H90' Ha8
  end.
  clear MU WM MI TM ST HS ML2 HKB2 H90.
  pose proof ML3 as ((MU & WM & MI & TM & ST & _) & _).
  (* 0x14314 sd a7,0xa0(sp) *)
  assert (HS : store_ok rsegs m3 (wa (SP + 160)) 8 = true)
    by (apply (stk_store_ok rsegs m3 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m3 ?A ?BS) _) =>
    change A with (wa (SP + 0xa0));
    assert (ML4 : ML (write_to_mem m3 (wa (SP + 0xa0)) BS) cells keys rf)
      by (apply MemL_store_save; rewrite ?length_le8; [exact ML3 | unfold X_CELLS; lia | exact HS | lia | lia]);
    assert (HKB4 : bytes_at rsegs (write_to_mem m3 (wa (SP + 0xa0)) BS) K (k ++ [NUL]))
      by (apply bytes_at_write_other; rewrite ?length_le8, ?HLK; [exact HKB3 | lia | lia | lia]);
    assert (H90 : bytes_at rsegs (write_to_mem m3 (wa (SP + 0xa0)) BS) (SP + 0x90)
                    (le8 (Z_to_bv 64 (Z.of_nat v + 1))))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact H90' | lia | lia | lia]);
    assert (Ha8' : bytes_at rsegs (write_to_mem m3 (wa (SP + 0xa0)) BS) (SP + 0xa8)
                     (le8 (Z_to_bv 64 (NOT_BODY pp))))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact Ha8 | lia | lia | lia]);
    assert (Ha0 : bytes_at rsegs (write_to_mem m3 (wa (SP + 0xa0)) BS) (SP + 0xa0) BS)
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    revert ML4 HKB4 H90 Ha8' Ha0; generalize (write_to_mem m3 (wa (SP + 0xa0)) BS) as m4;
    intros m4 ML4 HKB4 H90 Ha8' Ha0
  end.
  clear MU WM MI TM ST HS ML3 HKB3 H90' Ha8.
  pose proof ML4 as ((MU & WM & MI & TM & ST & _) & _).
  (* 0x14318 sd a6,0x98(sp) *)
  assert (HS : store_ok rsegs m4 (wa (SP + 152)) 8 = true)
    by (apply (stk_store_ok rsegs m4 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m4 ?A ?BS) _) =>
    change A with (wa (SP + 0x98));
    assert (ML5 : ML (write_to_mem m4 (wa (SP + 0x98)) BS) cells keys rf)
      by (apply MemL_store_save; rewrite ?length_le8; [exact ML4 | unfold X_CELLS; lia | exact HS | lia | lia]);
    assert (HKB5 : bytes_at rsegs (write_to_mem m4 (wa (SP + 0x98)) BS) K (k ++ [NUL]))
      by (apply bytes_at_write_other; rewrite ?length_le8, ?HLK; [exact HKB4 | lia | lia | lia]);
    assert (H90' : bytes_at rsegs (write_to_mem m4 (wa (SP + 0x98)) BS) (SP + 0x90)
                     (le8 (Z_to_bv 64 (Z.of_nat v + 1))))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact H90 | lia | lia | lia]);
    assert (Ha8 : bytes_at rsegs (write_to_mem m4 (wa (SP + 0x98)) BS) (SP + 0xa8)
                    (le8 (Z_to_bv 64 (NOT_BODY pp))))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact Ha8' | lia | lia | lia]);
    assert (Ha0' : bytes_at rsegs (write_to_mem m4 (wa (SP + 0x98)) BS) (SP + 0xa0)
                     (le8 (Z_to_bv 64 (pp + OFF_ENT + 8))))
      by (apply bytes_at_write_other; rewrite ?length_le8; [exact Ha0 | lia | lia | lia]);
    assert (H98 : bytes_at rsegs (write_to_mem m4 (wa (SP + 0x98)) BS) (SP + 0x98) BS)
      by (apply bytes_at_write_same; rewrite ?length_le8; lia);
    revert ML5 HKB5 H90' Ha8 Ha0' H98; generalize (write_to_mem m4 (wa (SP + 0x98)) BS) as m5;
    intros m5 ML5 HKB5 H90' Ha8 Ha0' H98
  end.
  clear MU WM MI TM ST HS ML4 HKB4 H90 Ha8' Ha0.
  pose proof ML5 as ((MU & WM & MI & TM & ST & _) & _).
  (* 0x1431c sd t6,0xb0(sp) *)
  assert (HS : store_ok rsegs m5 (wa (SP + 176)) 8 = true)
    by (apply (stk_store_ok rsegs m5 lo (SP + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m5 ?A ?BS) _) =>
    change A with (wa (SP + 0xb0));
    assert (MP6 : MP (write_to_mem m5 (wa (SP + 0xb0)) BS) cells keys rf v);
    [ refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
      [ apply MemL_store_save; rewrite ?length_le8; [exact ML5 | unfold X_CELLS; lia | exact HS | lia | lia]
      | apply bytes_at_write_other; rewrite ?length_le8; [exact H90' | lia | lia | lia]
      | apply bytes_at_write_other; rewrite ?length_le8; [exact H98 | lia | lia | lia]
      | apply bytes_at_write_other; rewrite ?length_le8; [exact Ha0' | lia | lia | lia]
      | apply bytes_at_write_other; rewrite ?length_le8; [exact Ha8 | lia | lia | lia]
      | apply bytes_at_write_same; rewrite ?length_le8; lia ]
    | assert (HKB6 : bytes_at rsegs (write_to_mem m5 (wa (SP + 0xb0)) BS) K (k ++ [NUL]))
        by (apply bytes_at_write_other; rewrite ?length_le8, ?HLK; [exact HKB5 | lia | lia | lia]);
      revert MP6 HKB6; generalize (write_to_mem m5 (wa (SP + 0xb0)) BS) as m6; intros m6 MP6 HKB6 ]
  end.
  clear MU WM MI TM ST HS ML5 HKB5 H90' Ha8 Ha0' H98.
  pose proof MP6 as (((_ & _ & MI6 & _) & _) & _).
  (* 0x14320 auipc a0,0xffffc; addi a1,a0,-0x63; addi a2,zero,13; mv a0,s11; jal strncmp *)
  step. step. step. step. step.
  destruct (strncmp_prefix_u k HNK) as (w & HW & Hw & Hiff).
  eapply evt_cut.
  { eapply STRN with (ls := k ++ [NUL]) (rs := HA_PREFIX ++ [NUL]) (v := w).
    - rewrite unsigned_lit by lia. exact HKB6.
    - rewrite unsigned_lit by lia. exact (proj1 (ParseSites.lits_at m6 MI6)).
    - rewrite unsigned_lit by lia. exact HW.
    - exact MI6. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m7 & Ems & MU7 &
              WM7 & MI7 & HKB7 & _).
  subst ms'. ret_even. rewrite unsigned_lit in HKB7 by lia.
  pose proof (MemP_none m6 m7 cells keys rf v MP6 MU7 WM7 MI7) as MP7.
  clear MP6 HKB6 MI6.
  rewrite (skipn_nth_cons es v (Ent 0 0 []) Hv) in HE. cbn [pairs_by] in HE.
  (* 0x14334 beqz a0 *)
  step. rewrite eqb_s by lia.
  destruct (Z.eqb_spec w 0) as [Ew|Ew]; cbv beta iota.
  - (* the prefix: 0x14354 *)
    assert (HP : ha_prefix k = true) by (apply Hiff; exact Ew). subst w.
    eapply pair_ok; [exact Hv | exact HH | exact HP | exact HF | exact HFP | exact MP7 | exact HL | exact HE
                    | exact HK0 | exact HKB7 | exact HKL | exact HNK].
  - (* no prefix: 0x14338 ld a2,0x68(sp); addi t5,zero,8; ld t6,0xb0(sp); ld a6,0x98(sp); ld a7,0xa0(sp);
       ld ra,0xa8(sp); j 0x14504 *)
    assert (HP : ha_prefix k = false)
      by (destruct (ha_prefix k) eqn:X; [exfalso; apply Ew, Hiff; reflexivity | reflexivity]).
    rewrite (ha_fold_skip expect_cell cap k _ _ cells keys rf HP) in HE.
    pose proof MP7 as (((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H68 & _) & _) & _ & H98 & Ha0 & Ha8 & Hb0).
    pose proof (read_le8 rsegs m7 (SP + 104) _ H68) as HRd. step. clear HRd.
    step.
    pose proof (read_le8 rsegs m7 (SP + 176) _ Hb0) as HRd. step. clear HRd.
    pose proof (read_le8 rsegs m7 (SP + 152) _ H98) as HRd. step. clear HRd.
    pose proof (read_le8 rsegs m7 (SP + 160) _ Ha0) as HRd. step. clear HRd.
    pose proof (read_le8 rsegs m7 (SP + 168) _ Ha8) as HRd. step. clear HRd.
    step.
    destruct HL as (HL1 & HL2 & HL3).
    eapply back_ok; [exact HH | exact HF | exact HFP | exact MP7 | split; [exact HL1 | split; lia] | exact HE | lia
                    | reflexivity].
Qed.

(** ** The loop head 0x14268: `at < n_ent` (else no pair is left), the bound 33 of ent[at], 104 at by mulhu *)
Lemma head_ok : forall j, ((j < n)%nat -> none_P j) -> head_P j.
Proof.
  intros j HN. unfold head_P.
  intros t0 t1 t2 a1 a3 a4 a5 s7 s10 s11 t3 t4 F fc m1 cells keys rf HF HFP ML1 HL HE Hj.
  pose proof bnd as (B1 & B2 & B3 & B4 & B5 & B6 & Hn).
  pose proof consts_eq as (EC1 & EC2 & EC3 & EC4 & EC5 & EC6 & EC7).
  pose proof ML1 as ((MU & WM & MI & TM & ST & HPPB & _) & _).
  (* 0x14268 lw a1,0(a2); bge a0,a1 *)
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + 19732)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat n)))).
  { apply (read_field rsegs m1 pp r 19732 _ HPPB HWF); [exact (pp_n_ent r HWF) | lia | unfold PP_SIZE; lia | lia]. }
  change POD_NENT_OFF with 19732. change MULHU_104 with 446676598784.
  step. clear HR. rewrite sx32_small by lia.
  step. rewrite lts_s by lia.
  destruct (Z.ltb_spec (Z.of_nat j) (Z.of_nat n)) as [Hl|Hl]; cbn [negb]; cbv beta iota.
  2:{ rewrite (pairs_end es j None) in HE by lia. rewrite ha_fold_nil in HE.
      eapply exit_ok; [exact HF | exact ML1 | exact (proj1 HL) | exact HE]. }
  (* 0x14270 slli a3,a0,32; srli s10,a3,32; addi a4,zero,33; mv a2,s10; bltu a4,s10 *)
  step. step. rewrite zext32_small by lia. step. step. step. rewrite ltu_u by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv beta iota.
  (* 0x14284 addi a2,zero,33; mv s11,zero; mulhu s7,a3,a6; sub a3,ra,s7 *)
  step. step. step. rewrite mulhu_idx by lia. step.
  eapply (HN ltac:(lia)); [exact HF | exact HFP | exact ML1 | exact HL | exact HE | lia | weqn ..].
Qed.

Lemma scan_ok : forall K i, (n - i <= K)%nat -> head_P i /\ none_P i /\ (forall k A, some_P i k A).
Proof.
  induction K as [|K IH]; intros i HK.
  - assert (HNo : none_P i) by (unfold none_P; intros; lia).
    split; [apply head_ok; intros _; exact HNo|]. split; [exact HNo|].
    intros k A. unfold some_P. intros. lia.
  - destruct (IH (S i) ltac:(lia)) as (HH & HN & HSm).
    assert (HNo : none_P i) by (apply none_ok; intros _; exact (conj HN HSm)).
    split; [apply head_ok; intros _; exact HNo|]. split; [exact HNo|].
    intros k A. apply some_ok. exact HH.
Qed.

(** The loop from its first head (at = 0, no cell, no key, no refusal). *)
Lemma loop_start : forall (t0 t1 t2 a1 a3 a4 a5 s7 s10 s11 t3 t4 : word) (F : bvmap 5 word) (fc : bv 32)
                          (m1 : word -> option byte),
  frm0 fc -> FPinv F -> ML m1 [] 0 REFUSE_NONE ->
  E = ha_result (ha_fold expect_cell cap (pairs es) [] 0 REFUSE_NONE) ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 (NOT_BODY pp)) sp gp tp t0 t1 t2 (Z_to_bv 64 (NOT_ENT pp)) s1 (Z_to_bv 64 0) a1
             (Z_to_bv 64 (pp + POD_NENT_OFF)) a3 a4 a5 (Z_to_bv 64 MULHU_104) (Z_to_bv 64 (pp + OFF_ENT + 8))
             (Z_to_bv 64 cap) s3 s4 s5 s6 s7 (Z_to_bv 64 (pp + OFF_ENT)) (Z_to_bv 64 0) s10 s11 t3 t4
             (Z_to_bv 64 POD_STRING) (Z_to_bv 64 1))
        F (Z_to_bv 64 0x14268) fc None m1 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a1 a3 a4 a5 s7 s10 s11 t3 t4 F fc m1 HF HFP ML1 HE.
  destruct (scan_ok n 0 ltac:(lia)) as [HH _].
  exact (HH t0 t1 t2 a1 a3 a4 a5 s7 s10 s11 t3 t4 F fc m1 [] 0 REFUSE_NONE HF HFP ML1
            ltac:(unfold Linv, REFUSE_NONE; cbn [length Z.of_nat]; lia) HE ltac:(lia)).
Qed.

End Pairs.

(** ** The pair loop from its first head to 0x14784 *)
Theorem loop_holds : strncmp_contract -> key_stmt -> loop_stmt.
Proof.
  intros STRN KEY. unfold loop_stmt.
  intros Q sp gp tp s1 s3 s4 s5 s6 m r cap pp lo HWF HCAP HPP0 HPPLO HST HLO HSPA HROM HPS HQ
    t0 t1 t2 a1 a3 a4 a5 s7 s10 s11 t3 t4 F fc m1 HF HFP ML1.
  exact (loop_start sp gp tp s1 s3 s4 s5 s6 m r cap pp lo Q _ HWF HCAP HPP0 HPPLO HST HLO HSPA HROM HPS KEY STRN HQ
           t0 t1 t2 a1 a3 a4 a5 s7 s10 s11 t3 t4 F fc m1 HF HFP ML1 eq_refl).
Qed.
