(* check_bounds (fuzz_link.c:555-566), PLAIN build: the walk of its contract
   (lib/Prog/check_bounds_c.v) on the plain image.
   0x151c0, 80 bytes, 21 instructions: push a 32-byte frame (ra, s0, s1), call memchr(buf, 0, cap)
   (0x1eb60), `beqz a0` to abort (0x1520c), load buf[cap], `bne` against 0x5a to abort, pop, ret.

   The abort branches are not taken: memchr finds the NUL at index i < cap, so it answers
   buf + i, which is not 0 (buf <> 0, buf + cap + 1 <= 2^64 from tbuf_at); the byte at buf + cap
   is the guard 0x5a (tbuf_at), and memchr writes nothing (its post, munch []). The premise
   `arg regs 0 <> 0` is what rules out the first: at buf = 0 with the NUL at index 0 memchr answers
   0 + 0 = NULL and `beqz a0` at 0x151e4 jumps to `jal abort`. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf check_bounds_c memchr_c memchr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
Local Open Scope Z_scope.

(* the two pieces of a text buffer: its cap bytes and the guard byte after them *)
Lemma cb_tbuf : forall m A cap bs, 1 <= cap -> tbuf_at m A cap bs ->
  Z.of_nat (length bs) = cap /\ bytes_at rsegs m A bs /\ bytes_at rsegs m (A + cap) [Z_to_bv 8 90]
  /\ A + cap + 1 <= 2 ^ 64 /\ 0 <= A.
Proof.
  intros m A cap bs Hc [[WF BY] _].
  cbn [cells_wf cell_wf] in WF. destruct WF as [L _].
  cbn [cells_bytes cbytes app] in BY.
  apply (bytes_at_app rsegs) in BY. destruct BY as [B1 B2].
  rewrite L, Z2Nat.id in B2 by lia.
  pose proof (bytes_at_bound _ _ _ _ B1) as HB1.
  pose proof (bytes_at_bound _ _ _ _ B2) as HB. cbn [length] in HB.
  split; [rewrite L; lia|]. split; [exact B1|]. split; [exact B2|]. lia.
Qed.

Lemma cb_find_nul : forall bs, In (Z_to_bv 8 0) bs -> exists i, find_byte 0 bs = Some i.
Proof.
  intros bs H. destruct (find_byte 0 bs) as [i|] eqn:F; [eauto|].
  exfalso. destruct (In_nth_error _ _ H) as [j Hj].
  apply (find_byte_None 0 bs F j (Z_to_bv 8 0) Hj). reflexivity.
Qed.

Lemma cb_memchr_ok : forall A c n bs, n <= Z.of_nat (length bs) -> memchr_ok A c n bs.
Proof. intros A c n bs H. unfold memchr_ok. destruct (find_byte c (firstn (Z.to_nat n) bs)); [left|]; exact H. Qed.

Lemma cb_memchr_res : forall A c n bs i, c = 0 -> n = Z.of_nat (length bs) -> find_byte 0 bs = Some i ->
  memchr_res A c n bs = A + Z.of_nat i.
Proof. intros A c n bs i -> -> F. unfold memchr_res. rewrite Nat2Z.id, firstn_all, F. reflexivity. Qed.

(* a branch: split on its test and drop the side the hypotheses refute *)
Ltac cb_br :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; lia)
  | _ => idtac
  end.

Section Walk.
Hypothesis MC : memchr_contract.

Theorem check_bounds_walk : check_bounds_contract.
Proof.
  unfold check_bounds_contract. apply leaf_intro.
  - intros r1 r2 m E [bs H]. exists bs. unfold arg, apart_frame, spZ in *. rewrite <- !E. exact H.
  - intros r1 r2 m _. reflexivity.
  - intros r1 r2 m q1 q2 m' _ _ H. exact H.
  - unfold leaf_walk, CHECK_BOUNDS.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros (bs & NZ & CAP & TB & NUL & AP) MI ST LO SP.
    change (bv_unsigned a0 <> 0) in NZ.
    change (1 <= bv_unsigned a1) in CAP.
    change (tbuf_at m (bv_unsigned a0) (bv_unsigned a1) bs) in TB.
    change (bv_unsigned a0 + (bv_unsigned a1 + 1) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0) in AP.
    unfold writes_nothing, only_frame.
    destruct (cb_tbuf m _ _ bs CAP TB) as (LEN & BUF & GB & HI & A0). clear TB.
    destruct (cb_find_nul bs NUL) as [i FB].
    destruct (find_byte_Some _ _ _ FB) as (Hi & _ & _).
    pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1. pose proof (zr_word sp) as Rsp.
    unfold inr64 in Ra0, Ra1, Rsp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST.
    (* addi sp; sd ra; sd s0; sd s1; mv s0, a1; mv s1, a0; mv a1, zero; mv a2, s0; jal memchr *)
    do 9 zstep.
    call MC; [ exact BUF | apply cb_memchr_ok; rewrite ?Z_to_bv_bv_unsigned; lia | assumption | ].
    rewrite (cb_memchr_res (bv_unsigned a0) _ _ bs i)
      by (first [ reflexivity | exact FB | rewrite ?Z_to_bv_bv_unsigned; lia ]).
    (* beqz a0, abort: memchr answered buf + i <> 0 *)
    zstep. cb_br.
    pose proof (bytes_at_ov_read _ _ _ _ 0%nat 1%nat GB ltac:(cbn; lia)) as HR.
    cbn [firstn skipn] in HR. change (Z.of_nat 0) with 0 in HR. rewrite Z.add_0_r in HR.
    (* add s0, s1, s0; lbu a0, 0(s0); li a1, 0x5a; bne a0, a1, abort *)
    zstep. zstep. zstep. zstep. cb_br.
    (* ld ra; ld s0; ld s1; addi sp *)
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: first [ exact I | apply regs_preserved_mkR | assumption ].
Qed.

End Walk.

Theorem check_bounds_holds : check_bounds_contract.
Proof. exact (check_bounds_walk memchr_holds). Qed.

About check_bounds_walk.
Print Assumptions check_bounds_walk.
Print Assumptions check_bounds_holds.
