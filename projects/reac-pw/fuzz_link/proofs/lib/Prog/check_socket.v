(* check_socket (fuzz_link.c:487-496), PLAIN build: the walk of its contract
   (lib/Prog/check_socket_c.v) on the plain image. The returning path, 12 instructions:
     lui a0, 0x40; auipc a1, 0x1d; addi a1, a1, -0x568   (a1 = g_nl = 0x31b80)
     add a0, a1, a0                                      (a0 = g_nl + 0x40000)
     lw a1, 0x214(a0); bnez a1, +0x1c                    (g_nl.open, NK_OPEN)
     lw a1, 0x218(a0); lw a2, 0x21c(a0); bne a1, a2, +0x10   (g_nl.opened, g_nl.closed)
     lw a0, 0x220(a0); bnez a0, +8                       (g_nl.misuse)
     ret
   Each branch goes to the abort path at +0x30 and is not taken under the premise: the four `lw`
   read the four 4-byte fields of nlk_at's byte list that link_spec's nk_open, nk_opened, nk_closed
   and nk_misuse decode, and `lw` sign-extends a function of those four bytes, so equal fields give
   equal registers. Only a0, a1, a2 change; no memory is written. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf hp_cka_kit check_socket_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

(* a 4-byte field of the fake kernel at offset off: the bytes a 4-byte load from g_nl + off reads *)
Lemma nlk_read4 : forall m bs off,
  nlk_at m bs -> 0 <= off -> off + 4 <= NK_SIZE ->
  ov_read_bytes rsegs m (wa (A_G_NL + off)) 4 = Some (slice bs off 4).
Proof.
  intros m bs off [[HB _] HL] H0 H1. unfold slice.
  change (Z.to_nat 4) with 4%nat.
  apply bytes_at_read; [exact HB | exact H0 | lia].
Qed.

(* the word a load forms from the bytes it read is the little-endian value of those bytes *)
Lemma lbw : forall bs, le_bytes_to_word bs = Z_to_bv 64 (bytes_le_to_Z bs).
Proof. reflexivity. Qed.

Theorem check_socket_holds : check_socket_contract.
Proof.
  unfold check_socket_contract. apply leaf_intro.
  - intros r1 r2 m _ H. exact H.
  - intros r1 r2 m _. reflexivity.
  - intros r1 r2 m q1 q2 m' _ _ H. exact H.
  - unfold leaf_walk, CHECK_SOCKET.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros HP MI ST LO SP.
    destruct HP as (bs & HN & Hopen & Heq & Hmis).
    pose proof (nlk_read4 m bs NK_OPEN HN ltac:(unfold NK_OPEN; lia)
                  ltac:(unfold NK_OPEN, NK_SIZE; lia)) as R1.
    pose proof (nlk_read4 m bs NK_OPENED HN ltac:(unfold NK_OPENED; lia)
                  ltac:(unfold NK_OPENED, NK_SIZE; lia)) as R2.
    pose proof (nlk_read4 m bs NK_CLOSED HN ltac:(unfold NK_CLOSED; lia)
                  ltac:(unfold NK_CLOSED, NK_SIZE; lia)) as R3.
    pose proof (nlk_read4 m bs NK_MISUSE HN ltac:(unfold NK_MISUSE; lia)
                  ltac:(unfold NK_MISUSE, NK_SIZE; lia)) as R4.
    (* nk_open, nk_opened, nk_closed, nk_misuse are the values of exactly those bytes *)
    assert (V1 : bytes_le_to_Z (slice bs NK_OPEN 4) = 0) by exact Hopen.
    assert (V23 : bytes_le_to_Z (slice bs NK_OPENED 4) = bytes_le_to_Z (slice bs NK_CLOSED 4)) by exact Heq.
    assert (V4 : bytes_le_to_Z (slice bs NK_MISUSE 4) = 0) by exact Hmis.
    change (wa (A_G_NL + NK_OPEN)) with (Z_to_bv 64 466324) in R1.
    change (wa (A_G_NL + NK_OPENED)) with (Z_to_bv 64 466328) in R2.
    change (wa (A_G_NL + NK_CLOSED)) with (Z_to_bv 64 466332) in R3.
    change (wa (A_G_NL + NK_MISUSE)) with (Z_to_bv 64 466336) in R4.
    remember (slice bs NK_OPEN 4) as B1 eqn:E1.
    remember (slice bs NK_OPENED 4) as B2 eqn:E2.
    remember (slice bs NK_CLOSED 4) as B3 eqn:E3.
    remember (slice bs NK_MISUSE 4) as B4 eqn:E4.
    clear E1 E2 E3 E4 Hopen Heq Hmis HN.
    step. step. step. step.
    (* lw a1, 0x214(a0): g_nl.open *)
    step. rewrite !lbw, V1.
    step. if_false.
    (* lw a1, 0x218(a0); lw a2, 0x21c(a0): g_nl.opened, g_nl.closed *)
    step. step. rewrite !lbw, V23.
    step. if_false.
    (* lw a0, 0x220(a0): g_nl.misuse *)
    step. rewrite !lbw, V4.
    step. if_false.
    step.
    ret_unchanged MI ST.
Qed.

Print Assumptions check_socket_holds.
