From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_find_c reac_segconf_role_c
  reac_segconf_ignored_c reac_segconf_model_c check_absent_c.
Import ListNotations.
Open Scope Z_scope.

(** check_absent of the UBSan image (0x14d9c, 28 instructions).
    Prologue: a 32-byte frame holding ra, s0 = name, s1 = c. Then reac_segconf_find(c, name),
    reac_segconf_role(c, name, NULL), reac_segconf_ignored(c, name) and reac_segconf_model(c, name), each at
    sp - 32 and each followed by `bnez a0` to the `jal abort` at 0x14e04 (its `unimp` follows); then the epilogue
    and `ret`. The function has no UBSan check of its own.
    The premise absent rc nm = true makes every answer NULL / 0 (no entry has the name), so each `bnez` falls
    through and the abort is dead. The callees write only below sp - 32, inside [sp - 112, sp) (find's frame is 64
    bytes in this build). *)

(** ** The model: absent means no entry has the name, so every accessor answers None / false *)
Lemma absent_none : forall rc nm, absent rc nm = true ->
  r_find rc nm = None /\ r_role rc nm = None /\ r_ignored rc nm = false /\ r_model rc nm = None.
Proof.
  intros rc nm H. unfold absent in H.
  destruct (r_find rc nm) eqn:E1; cbv beta iota in H; [discriminate|].
  destruct (r_role rc nm) eqn:E2; cbv beta iota in H; [discriminate|].
  destruct (r_ignored rc nm) eqn:E3; cbv beta iota in H; [discriminate|].
  destruct (r_model rc nm) eqn:E4; cbv beta iota in H; [discriminate|].
  repeat split.
Qed.

(** ** Moving a reader query's premise to a callee's stack pointer and to a later memory *)
Lemma munch_widen : forall a b lo m m', munch [(a, b)] m m' -> lo <= a -> munch [(lo, b)] m m'.
Proof.
  intros a b lo m m' H L. eapply munch_weaken; [|exact H].
  intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I].
Qed.

Lemma mod16_m32 : forall x, x mod 16 = 0 -> (x + -32) mod 16 = 0.
Proof.
  intros x H. replace (x + -32) with (x + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact H.
Qed.

(** c and name lie apart from the whole stack region [lo, sp), so a memory that changed only inside it still holds
    them; the callee's region [lo, sp') is a prefix of it. *)
Lemma qp_shift : forall D D' m m' sp sp' lo c name rc nm,
  query_pre D m sp lo c name rc nm ->
  munch [(lo, sp)] m m' -> mem_inv rsegs m' -> stk rsegs m' lo sp' ->
  sp' <= sp -> sp' mod 16 = 0 -> lo + D' <= sp' ->
  query_pre D' m' sp' lo c name rc nm.
Proof.
  intros D D' m m' sp sp' lo c name rc nm
    (C0 & C16 & (bs & B & E) & AC & N0 & (bn & BN & ZN & NN) & AN & (_ & _ & _ & RO) & _) MU MI ST H1 H2 H3.
  unfold query_pre.
  refine (conj C0 (conj C16 (conj _ (conj _ (conj N0 (conj _ (conj _ (conj _ MI)))))))).
  - exists bs. split; [|exact E]. eapply bytes_at_transport; [exact B | exact MU |].
    pose proof E as [L _]. cbn [disjoint_from]. rewrite L. unfold apart in AC. split; [lia | exact I].
  - unfold apart in *. lia.
  - exists bn. split; [|split; assumption]. eapply bytes_at_transport; [exact BN | exact MU |].
    rewrite <- ZN in AN. unfold zs in AN. rewrite length_map in AN. unfold apart in AN.
    cbn [disjoint_from]. rewrite length_app. cbn [length]. split; [lia | exact I].
  - unfold apart in *. lia.
  - unfold stack_ok. refine (conj ST (conj H3 (conj H2 _))). intros a Ha. apply RO. lia.
Qed.

(** A `bnez a0` with a0 = 0: the branch to the abort is not taken. *)
Ltac fall :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; [exfalso; first [discriminate K | zify_cond K; lia] | clear K]
  | _ => idtac
  end.

Ltac rn_stk lo := match goal with H : stk _ _ lo _ |- _ => rename H into ST end.

Theorem check_absent_holds : reac_segconf_find_contract -> reac_segconf_role_contract ->
  reac_segconf_ignored_contract -> reac_segconf_model_contract -> check_absent_contract.
Proof.
  intros HF HR HI HM. unfold check_absent_contract, check_absent_pre, CHECK_ABSENT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo rc nm
    [QP AB].
  destruct (absent_none rc nm AB) as (RF & RR & RI & RM).
  assert (FP0 : find_ptr (bv_unsigned a0) rc nm = 0) by (unfold find_ptr; rewrite RF; reflexivity).
  assert (MP0 : model_ptr (bv_unsigned a0) rc nm = 0) by (unfold model_ptr; rewrite RF; reflexivity).
  assert (HCS : CHECK_ABSENT_STACK = 112) by reflexivity.
  pose proof QP as (_ & _ & _ & _ & _ & _ & _ & (ST & LD & SPM & _) & MI).
  rewrite HCS in LD |- *.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  (* addi sp; sd ra, s0, s1; mv s0, a1; mv s1, a0; jal reac_segconf_find *)
  do 7 zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HF with (lo := lo) (rc := rc) (nm := nm)
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold ret_post, FIND_STACK in PO; rewrite FP0 in PO;
      rewrite (unsigned_lit (bv_unsigned sp + -32)) in PO by lia;
      revert ms' PO; post_call segs mm ]
  end;
  [ rewrite (unsigned_lit (bv_unsigned sp + -32)) by lia;
    eapply qp_shift;
    [ exact QP | eapply munch_widen; [exact MU | lia] | eassumption | eassumption | lia
    | apply mod16_m32; exact SPM | unfold FIND_STACK; lia ]
  | ].
  rn_stk lo.
  zstep. fall.
  (* mv a0, s1; mv a1, s0; mv a2, zero; jal reac_segconf_role *)
  do 4 zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HR with (lo := lo) (rc := rc) (nm := nm)
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold ret_post in PO; rewrite RR in PO;
      unfold role_W, ROLE_STACK, FIND_STACK in PO; cbv beta iota in PO;
      rewrite (unsigned_lit (bv_unsigned sp + -32)) in PO by lia;
      revert ms' PO; post_call segs mm ]
  end;
  [ rewrite (unsigned_lit (bv_unsigned sp + -32)) by lia;
    unfold role_pre; split;
    [ eapply qp_shift;
      [ exact QP | eapply munch_widen; [exact MU | lia] | eassumption | eassumption | lia
      | apply mod16_m32; exact SPM | unfold ROLE_STACK, FIND_STACK; lia ]
    | left; first [reflexivity | vm_compute; reflexivity | rewrite unsigned_lit by lia; reflexivity] ]
  | ].
  rn_stk lo.
  zstep. fall.
  (* mv a0, s1; mv a1, s0; jal reac_segconf_ignored *)
  do 3 zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HI with (lo := lo) (rc := rc) (nm := nm)
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold ret_post in PO; rewrite RI in PO;
      unfold b2z, IGNORED_STACK, FIND_STACK in PO; cbv beta iota in PO;
      rewrite (unsigned_lit (bv_unsigned sp + -32)) in PO by lia;
      revert ms' PO; post_call segs mm ]
  end;
  [ rewrite (unsigned_lit (bv_unsigned sp + -32)) by lia;
    eapply qp_shift;
    [ exact QP | eapply munch_widen; [exact MU | lia] | eassumption | eassumption | lia
    | apply mod16_m32; exact SPM | unfold IGNORED_STACK, FIND_STACK; lia ]
  | ].
  rn_stk lo.
  zstep. fall.
  (* mv a0, s1; mv a1, s0; jal reac_segconf_model *)
  do 3 zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HM with (lo := lo) (rc := rc) (nm := nm)
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold ret_post, MODEL_STACK, FIND_STACK in PO; rewrite MP0 in PO;
      rewrite (unsigned_lit (bv_unsigned sp + -32)) in PO by lia;
      revert ms' PO; post_call segs mm ]
  end;
  [ rewrite (unsigned_lit (bv_unsigned sp + -32)) by lia;
    eapply qp_shift;
    [ exact QP | eapply munch_widen; [exact MU | lia] | eassumption | eassumption | lia
    | apply mod16_m32; exact SPM | unfold MODEL_STACK, FIND_STACK; lia ]
  | ].
  rn_stk lo.
  zstep. fall.
  (* ld ra, s0, s1; addi sp; ret *)
  do 4 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish; try exact I.
Qed.
