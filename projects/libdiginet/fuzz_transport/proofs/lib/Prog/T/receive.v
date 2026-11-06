(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_entry.v, with its module paths, addresses and numbers changed; 1150 of its 1185 lines of code are new or changed and 49 lines of the source are left out. *)
(* The plain-image walk of receive (fuzz/fuzz_transport.c:995-1025 of the harness fix, c47f6290) at 0x14afc,
   556 bytes, against receive_c.v's receive_contract (receive_holds). It is an SR walk in four parts (the donor's
   flow, libdiginet/fuzz_decode lib/Prog/LLVMFuzzerTestOneInput.v):
     entry  0x14afc-0x14b30: the prologue to malloc (r_entry, evt, TSRGlue.g_run);
     malloc the SR call (TSRGlue.g_malloc), a = the heap frame of max (1, n) bytes;
     body   0x14b34-0x14cc8: the frame copy, op_begin, g_rx_send, the poll or m_rx + diginet_session_rx branch,
            settle, the epilogue, to the tail call of free (r_body, evt, TSRGlue.g_run). The abort at 0x14d24 is
            unreachable: malloc's post gives a >= 4096. Pieces: r_b50 (0x14b50: the two memsets, M.fail,
            OW.desk_off), r_snd_np / r_snd_p (g_rx_send of the frame, as spec_read_frame decides it), r_mrx
            (0x14c78), r_poll_tail (0x14c40), r_tail (0x14ca0: settle, the epilogue);
     free   the SR tail call (TSRGlue.g_free), which returns to receive's caller.
   The post is built by TSRGlue.sr_post. The model receive_m is cut where the binary branches (rb_eq). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0 MemNorm AllocSlots.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import StrFun DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem
  TSess0 TCb TSess TOps TRxFacts TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memcpy_c memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract TSessC receive_c
  TSRGlue diginet_session_poll_c m_rx_c diginet_session_rx_c settle_c.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- entry: 0x14afc-0x14b30 *)

Definition R_MALLOC_RET : Z := 0x14b34.

(* The state at malloc's entry: sp is receive's sp - 48, the six saved registers in [sp - 48, sp), s1 = n,
   s2 = poll_flags, s3 = by_poll, s4 = p, a0 = n ? n : 1; every other register as receive was entered. *)
Definition q_mal (F : bvmap 5 word) (fc : bv 32)
    (gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (m0 : word -> option byte) (Sp lo p n : Z) (sv : list cell) (ms : machine_state) : Prop :=
  exists m', ms = MS (mkR (Z_to_bv 64 R_MALLOC_RET) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 a1 (Z_to_bv 64 (Z.max 1 n))
                          a1 a2 a3 a4 a5 a6 a7 a3 a2 (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 H_MALLOC) fc None m' (seg_rom rsegs) /\
    munch [(Sp, Sp + 48)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp /\
    rw_cells rsegs m' Sp sv.

(* a0 = a1 + (a1 == 0) for a1 = n, 0 <= n < 2^63 *)
Lemma r_a0 : forall n, 0 <= n < 2 ^ 63 ->
  Z_to_bv 64 (n + bv_unsigned (v_sltiu (Z_to_bv 64 n) 1)) = Z_to_bv 64 (Z.max 1 n).
Proof.
  intros n Hn. unfold v_sltiu. rewrite (unsigned_lit n) by lia.
  change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec n 1) as [H|H].
  - rewrite (unsigned_lit 1) by lia. f_equal. lia.
  - rewrite (unsigned_lit 0) by lia. f_equal. lia.
Qed.

Lemma r_a0' : forall n, 0 <= n < 2 ^ 63 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 n) + bv_unsigned (v_sltiu (Z_to_bv 64 n) 1)) = Z_to_bv 64 (Z.max 1 n).
Proof. intros n Hn. rewrite (unsigned_lit n) by lia. apply r_a0. exact Hn. Qed.

Lemma r_entry :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p n : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> mem_inv rsegs m -> bv_unsigned sp < 2 ^ 63 ->
    0 <= n < 2 ^ 63 ->
    evt rsegs (q_mal F fc gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 m (bv_unsigned sp - 48) lo p n [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
               s11 t3 t4 t5 t6)
          F (Z_to_bv 64 receive_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo p n
    ST LO MI H63 Hn.
  unfold receive_ENTRY.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp - 48 + 48)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  carve_frame 48%nat ST.
  (* 0x14afc-0x14b14: addi sp, sp, -48; sd ra, s0, s1, s2, s3, s4 *)
  do 7 step.
  (* 0x14b18-0x14b2c: mv s2, a3; mv s3, a2; mv s1, a1; mv s4, a0; seqz a0, a1; add a0, a1, a0 *)
  do 6 step.
  (* 0x14b30: jal malloc *)
  step.
  apply evt_done. unfold q_mal. eexists. split.
  { rewrite ?r_a0' by exact Hn. rewrite ?r_a0 by exact Hn.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia. reflexivity. }
  replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in * by lia.
  split; [exact MU0|]. split; [exact WM0|]. split; [exact MI|]. split; [exact ST|]. exact FR.
Qed.

(* ---------------------------------------------------------------- the model, cut where the binary branches *)

Local Notation "'let?' p ':=' e 'in' b" :=
  (match e with Some p => b | None => None end)
  (at level 200, p pattern, e at level 100, b at level 200, right associativity).

(* g_rx_send of a frame b (spec_read_frame: f.send is 0 unless the code is SPEC_OK) *)
Definition rb_snd (b : list byte) : Z := if fr_code b =? 0 then fr_send b else 0.

(* the by-poll branch's got = min (n, SPEC_MAX_FRAME) *)
Definition rb_got (n : Z) : Z := if SPEC_MAX_FRAME <? n then SPEC_MAX_FRAME else n.

(* the world after op_begin *)
Definition rb_b1 (B : list byte) : list byte :=
  let B1 := upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW)) in
  let B2 := upd B1 OFF_GOT (repeat (b8 0) (Z.to_nat SZ_GOT)) in
  let B3 := set_OW_desk_off B2 (-1) in
  set_M_fail B3 (g_fail_next B3).

(* fuzz_transport.c:1004-1018, the by-poll branch, from the world B2 after :1002-1003 *)
Definition rb_poll (fa : Z) (bytes : list byte) (pf : Z) (B2 : list byte) : option (list byte * Z) :=
  let got := rb_got (Z.of_nat (length bytes)) in
  let twice := Z.land pf 1 in
  let fails := Z.land (Z.shiftr pf 1) 1 in
  let B2a := set_g_rx_send B2 (rb_snd (firstn (Z.to_nat got) bytes)) in
  let ticked := if fails =? 0 then 1 else 0 in
  let B2c := set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx B2a fa) got) (if twice =? 0 then 1 else 2))
               fails in
  let? (B2d, _) := diginet_session_poll_m timg_plain (Some (TFrame fa bytes)) B2c 0 in
  Some (set_g_rx_fail (set_g_rx B2d 0) 0, ticked).

(* fuzz_transport.c:1019-1022, the m_rx branch *)
Definition rb_mrx (fa : Z) (bytes : list byte) (B2 : list byte) : option (list byte * Z) :=
  let? (Bx, ticked) := m_rx_m timg_plain (Some (TFrame fa bytes)) B2 (Z.of_nat (length bytes)) in
  let? (By, _) := diginet_session_rx_m timg_plain (Some (TFrame fa bytes)) Bx bytes (g_now Bx) in
  Some (By, ticked).

(* fuzz_transport.c:1023-1024, settle *)
Definition rb_fin (o : option (list byte * Z)) : option (list byte * unit) :=
  let? (B3, ticked) := o in
  let? (B4, _) := settle_m B3 ticked in
  Some (B4, tt).

Lemma rb_eq : forall B fa bytes by_poll pf, fa <> 0 ->
  receive_m timg_plain B fa bytes by_poll pf =
  rb_fin (if negb (by_poll =? 0) then rb_poll fa bytes pf (set_g_rx_send (rb_b1 B) (rb_snd bytes))
          else rb_mrx fa bytes (set_g_rx_send (rb_b1 B) (rb_snd bytes))).
Proof.
  intros B fa bytes by_poll pf H. unfold receive_m, fuzz_dup_m, fuzz_alloc_m, op_begin_m.
  rewrite (proj2 (Z.eqb_neq fa 0) H).
  unfold rb_fin, rb_poll, rb_mrx, rb_b1, rb_snd, rb_got. cbv beta iota zeta.
  reflexivity.
Qed.

(* the code of rb_snd, as the binary tests it *)
Lemma rb_snd_char : forall l, rb_snd l =
  if (length l <? 30)%nat then 0 else if negb (be16 l 12 =? 34911) then 0
  else if (be16 l 14 <? 16) || (Z.of_nat (length l) - 14 <? be16 l 14) then 0 else be32 l 18.
Proof.
  intros l. unfold rb_snd, fr_code, fr_ethertype, fr_numbytes, fr_send.
  destruct (length l <? 30)%nat; [reflexivity|]. destruct (negb _); [reflexivity|].
  destruct (_ || _); reflexivity.
Qed.

Lemma rb_snd_short : forall l, (length l < 30)%nat -> rb_snd l = 0.
Proof. intros l H. rewrite rb_snd_char. rewrite (proj2 (Nat.ltb_lt _ _) H). reflexivity. Qed.

Lemma rb_snd_eth : forall l, (30 <= length l)%nat -> be16 l 12 <> 34911 -> rb_snd l = 0.
Proof.
  intros l H E. rewrite rb_snd_char. rewrite (proj2 (Nat.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) E). reflexivity.
Qed.

Lemma rb_snd_len : forall l, (30 <= length l)%nat -> be16 l 12 = 34911 ->
  be16 l 14 < 16 \/ Z.of_nat (length l) - 14 < be16 l 14 -> rb_snd l = 0.
Proof.
  intros l H E Hn. rewrite rb_snd_char. rewrite (proj2 (Nat.ltb_ge _ _) H), E. cbn [Z.eqb negb Pos.eqb].
  destruct Hn as [Hn|Hn].
  - rewrite (proj2 (Z.ltb_lt _ _) Hn). reflexivity.
  - rewrite (proj2 (Z.ltb_lt _ _) Hn), orb_true_r. reflexivity.
Qed.

Lemma rb_snd_ok : forall l, (30 <= length l)%nat -> be16 l 12 = 34911 ->
  16 <= be16 l 14 <= Z.of_nat (length l) - 14 -> rb_snd l = be32 l 18.
Proof.
  intros l H E Hn. rewrite rb_snd_char. rewrite (proj2 (Nat.ltb_ge _ _) H), E. cbn [Z.eqb negb Pos.eqb].
  rewrite (proj2 (Z.ltb_ge _ _) (proj1 Hn)), (proj2 (Z.ltb_ge _ _) (proj2 Hn)). reflexivity.
Qed.

Lemma r_nth_firstn : forall (l : list byte) i k d, (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros i k d H.
  - rewrite firstn_nil. reflexivity.
  - destruct k as [|k]; [lia|]. destruct i as [|i]; cbn [firstn nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma r_be16_fn : forall l k i, (S i < k)%nat -> be16 (firstn k l) i = be16 l i.
Proof. intros l k i H. unfold be16, at8. rewrite !r_nth_firstn by lia. reflexivity. Qed.

Lemma r_be32_fn : forall l k i, (S (S (S i)) < k)%nat -> be32 (firstn k l) i = be32 l i.
Proof. intros l k i H. unfold be32, at8. rewrite !r_nth_firstn by lia. reflexivity. Qed.

Lemma r_byte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma r_at8_range : forall l i, 0 <= at8 l i < 256.
Proof. intros l i. unfold at8, bz. apply r_byte. Qed.

Lemma r_be16_range : forall l i, 0 <= be16 l i < 65536.
Proof. intros l i. unfold be16. pose proof (r_at8_range l i). pose proof (r_at8_range l (S i)). lia. Qed.

(* the 16- and 32-bit big-endian assemblies of the disassembly (lbu, slli, or) *)
Lemma r_be16 : forall b0 b1 : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b0) ≪ 8))) (bv_unsigned (zxb b1)) =
  bv_unsigned b0 * 2 ^ 8 + bv_unsigned b1.
Proof.
  intros b0 b1. pose proof (r_byte b0). pose proof (r_byte b1). unfold zxb.
  rewrite (unsigned_lit (bv_unsigned b0)), (unsigned_lit (bv_unsigned b1)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned b0 * 2 ^ 8)) by lia.
  apply (lor_add _ _ 8); [lia | lia |]. rewrite Z_mod_mult. reflexivity.
Qed.

Lemma r_be32 : forall b0 b1 b2 b3 : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b1) ≪ 16)))
                                        (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b0) ≪ 24))))))
        (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b2) ≪ 8)))
                                        (bv_unsigned (zxb b3)))))
  = bv_unsigned b0 * 2 ^ 24 + bv_unsigned b1 * 2 ^ 16 + bv_unsigned b2 * 2 ^ 8 + bv_unsigned b3.
Proof.
  intros b0 b1 b2 b3.
  pose proof (r_byte b0). pose proof (r_byte b1). pose proof (r_byte b2). pose proof (r_byte b3). unfold zxb.
  rewrite (unsigned_lit (bv_unsigned b0)), (unsigned_lit (bv_unsigned b1)), (unsigned_lit (bv_unsigned b2)),
    (unsigned_lit (bv_unsigned b3)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (bv_unsigned b0 * 2 ^ 24)), (unsigned_lit (bv_unsigned b1 * 2 ^ 16)),
    (unsigned_lit (bv_unsigned b2 * 2 ^ 8)) by lia.
  rewrite (lor_add' (bv_unsigned b1 * 2 ^ 16) (bv_unsigned b0 * 2 ^ 24) 24); [| lia | lia |].
  2:{ replace (bv_unsigned b0 * 2 ^ 24) with (bv_unsigned b0 * 2 ^ 24) by reflexivity. apply Z_mod_mult. }
  rewrite (lor_add (bv_unsigned b2 * 2 ^ 8) (bv_unsigned b3) 8); [| lia | lia | apply Z_mod_mult].
  rewrite (unsigned_lit (bv_unsigned b1 * 2 ^ 16 + bv_unsigned b0 * 2 ^ 24)),
    (unsigned_lit (bv_unsigned b2 * 2 ^ 8 + bv_unsigned b3)) by lia.
  rewrite (lor_add (bv_unsigned b1 * 2 ^ 16 + bv_unsigned b0 * 2 ^ 24) (bv_unsigned b2 * 2 ^ 8 + bv_unsigned b3) 16);
    [lia | lia | lia |].
  replace (bv_unsigned b1 * 2 ^ 16 + bv_unsigned b0 * 2 ^ 24) with ((bv_unsigned b1 + bv_unsigned b0 * 2 ^ 8) * 2 ^ 16)
    by lia.
  apply Z_mod_mult.
Qed.

(* the poll flags: andi a1, s2, 1; slli a2, s2, 62; srli a2, a2, 63; addi a1, a1, 1; xori s2, a2, 1 *)
Lemma r_twice : forall w : word, Z.land (bv_unsigned w) 1 = Z.land (bv_unsigned w mod 2 ^ 32) 1.
Proof. intros w. rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity. Qed.

Lemma r_fails : forall w : word,
  bv_unsigned (Z_to_bv 64 (bv_unsigned w ≪ 62)) ≫ 63 = Z.land (Z.shiftr (bv_unsigned w mod 2 ^ 32) 1) 1.
Proof.
  intros w. rewrite unsigned_lit_wrap. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftl_spec by lia. rewrite Z.mod_pow2_bits_low by lia.
    change (Z.testbit 1 0) with true. rewrite andb_true_r. f_equal; lia.
  - rewrite Z.mod_pow2_bits_high by lia.
    replace (Z.testbit 1 i) with false; [rewrite andb_false_r; reflexivity|].
    symmetry. apply Z.bits_above_log2; [lia | cbn; lia].
Qed.

Lemma r_land1 : forall x, Z.land x 1 = 0 \/ Z.land x 1 = 1.
Proof.
  intros x. assert (E : Z.land x 1 = x mod 2) by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
  rewrite E. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

Lemma r_times : forall x, Z.land x 1 = 0 \/ Z.land x 1 = 1 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land x 1)) + 1) = Z_to_bv 64 (if Z.land x 1 =? 0 then 1 else 2).
Proof. intros x [E|E]; rewrite E; reflexivity. Qed.

Lemma r_times' : forall x, Z.land x 1 = 0 \/ Z.land x 1 = 1 ->
  Z_to_bv 64 (Z.land x 1 + 1) = Z_to_bv 64 (if Z.land x 1 =? 0 then 1 else 2).
Proof. intros x [E|E]; rewrite E; reflexivity. Qed.

Lemma r_ticked : forall f, f = 0 \/ f = 1 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 f)) 1) = Z_to_bv 64 (if f =? 0 then 1 else 0).
Proof. intros f [E|E]; rewrite E; reflexivity. Qed.

Lemma r_ticked' : forall f, f = 0 \/ f = 1 -> Z_to_bv 64 (Z.lxor f 1) = Z_to_bv 64 (if f =? 0 then 1 else 0).
Proof. intros f [E|E]; rewrite E; reflexivity. Qed.

(* ---------------------------------------------------------------- bit-vector facts *)

Lemma r_mod_neg : forall z, -2^64 <= z < 0 -> z mod 2^64 = z + 2^64.
Proof. intros z Hz. rewrite <- (Z_mod_plus_full z 1 (2^64)). rewrite Z.mod_small by lia. lia. Qed.

Lemma r_eqb : forall v k, 0 <= v < 2^64 -> 0 <= k < 2^64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 k) = (v =? k).
Proof. intros v k Hv Hk. unfold bv_eqb. rewrite (unsigned_lit v), (unsigned_lit k) by lia. reflexivity. Qed.

Lemma r_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma r_ltu : forall a c, 0 <= a < 2^64 -> 0 <= c < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 c) = (a <? c).
Proof. intros a c Ha Hc. unfold bv_ltu. rewrite (unsigned_lit a), (unsigned_lit c) by lia. reflexivity. Qed.

Ltac r_br v tac :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v; [cbv iota | symmetry; tac]
  end.

(* ---------------------------------------------------------------- memory facts *)

(* byte i of the bytes at a, as lbu reads it *)
Lemma rd0 : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi.
  change (Z_to_bv 64 (a + Z.of_nat i)) with (wa (a + Z.of_nat i)).
  rewrite (bytes_at_ov_read rsegs m a bs i 1 H ltac:(lia)).
  f_equal. clear H. revert i Hi. induction bs as [|x bs IH]; intros [|i] Hi; cbn [length] in Hi.
  - lia.
  - lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Ltac r_rd H k :=
  let R := fresh "RD" in
  pose proof (rd0 _ _ _ k H ltac:(lia)) as R; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in R.

Lemma r_cb_bytes : forall m A k bs, rw_cells rsegs m A [CB k bs] -> bytes_at rsegs m A bs.
Proof. intros m A k bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma r_bytes_nil : forall m A, 0 <= A < 2 ^ 64 -> bytes_at rsegs m A [].
Proof. intros m A H. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

(* the body's footprint misses .data.rel.ro: relro_img carries over *)
Lemma r_relro : forall m0 m (sp : word) fa n, relro_img m0 ->
  munch [(bv_unsigned sp - 3840, bv_unsigned sp + 48); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN); (fa, fa + Z.max 1 n)] m0 m ->
  W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 3840 ->
  (fa + Z.max 1 n <= RELRO_BASE \/ RELRO_BASE + RELRO_LEN <= fa) -> relro_img m.
Proof.
  intros m0 m sp fa n R MU H Hf i Hi. unfold mrd. rewrite (MU (wa (RELRO_BASE + i))); [exact (R i Hi)|].
  unfold RELRO_BASE, RELRO_LEN in *. cbn [outside]. rewrite wa_unsigned by lia.
  unfold W_BASE_PLAIN, W_LEN in *. refine (conj _ (conj _ (conj _ I))); lia.
Qed.

(* the heap frame as the callee contracts ask for it *)
Lemma r_tframe : forall m (sp : word) K fa bytes, 0 < fa -> bytes_at rsegs m fa bytes ->
  off_world fa (Z.of_nat (length bytes)) -> off_window sp K fa (Z.of_nat (length bytes)) ->
  tframe_at m sp K (Some (TFrame fa bytes)).
Proof. intros m sp K fa bytes H0 H1 H2 H3. unfold tframe_at. cbn [tf_addr tf_bytes]. tauto. Qed.

(* ---------------------------------------------------------------- world algebra *)

Lemma r_len_upd : forall bs k v, Z.of_nat (length bs) = 65616 -> 0 <= k -> k + Z.of_nat (length v) <= 65616 ->
  Z.of_nat (length (upd bs k v)) = 65616.
Proof. intros bs k v H Hk Hv. rewrite length_upd by lia. exact H. Qed.

Ltac r_len := first [ assumption
                    | apply r_len_upd; [ r_len | lia | rewrite ?repeat_length, ?length_put; lia ] ].

Lemma r_comm : forall bs v w k k', Z.of_nat (length bs) = 65616 -> 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat (length w) <= k \/ k + Z.of_nat (length v) <= k') ->
  k + Z.of_nat (length v) <= 65616 -> k' + Z.of_nat (length w) <= 65616 ->
  upd (upd bs k v) k' w = upd (upd bs k' w) k v.
Proof. intros bs v w k k' H H1 H2 H3 H4 H5. apply upd_upd_comm; lia. Qed.

Lemma r_gf_upd : forall X k v, Z.of_nat (length X) = 65616 -> 0 <= k -> k + Z.of_nat (length v) <= 65616 ->
  (64969 <= k \/ k + Z.of_nat (length v) <= 64968) -> g_fail_next (upd X k v) = g_fail_next X.
Proof.
  intros X k v H H1 H2 H3. unfold g_fail_next, OFF_g_fail_next. apply u_at_upd_out; cbn [Z.of_nat]; lia.
Qed.

Ltac r_gf := repeat (rewrite r_gf_upd by (first [r_len | lia | rewrite ?repeat_length, ?length_put; lia])).

Lemma r_zsrc : forall k, 0 <= k < 2 ^ 64 ->
  repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) (Z.to_nat (bv_unsigned (Z_to_bv 64 k))) =
  repeat (b8 0) (Z.to_nat k).
Proof. intros k Hk. rewrite (unsigned_lit 0) by lia. rewrite (unsigned_lit k) by lia. reflexivity. Qed.

(* op_begin's stores, in the binary's order (memset OW, memset GOT, M.fail, OW.desk_off) *)
Lemma r_b1_eq : forall B, length B = Z.to_nat W_LEN ->
  upd (upd (upd (upd B 65312 (repeat (b8 0) 304)) 65084 (repeat (b8 0) 224)) 88
         (put 4 (u_at (upd (upd B 65312 (repeat (b8 0) 304)) 65084 (repeat (b8 0) 224)) 64968 1)))
      65544 (put 4 (-1)) = rb_b1 B.
Proof.
  intros B LB. pose proof (len_w B LB) as LB'. unfold W_LEN in LB'.
  unfold rb_b1, set_M_fail, set_OW_desk_off, A_M_fail, A_OW_desk_off, OFF_M, OFF_OW, OFF_GOT, SZ_OW, SZ_GOT.
  cbv zeta. change (0xff20 + 232) with 65544. change (0x0 + 88) with 88.
  change 0xff20 with 65312. change 0xfe3c with 65084.
  change (Z.to_nat 304) with 304%nat. change (Z.to_nat 224) with 224%nat.
  set (B2 := upd (upd B 65312 (repeat (b8 0) 304)) 65084 (repeat (b8 0) 224)).
  assert (L2 : Z.of_nat (length B2) = 65616) by (unfold B2; r_len).
  assert (G : g_fail_next (upd B2 65544 (put 4 (-1))) = u_at B2 64968 1)
    by (rewrite r_gf_upd by (first [exact L2 | rewrite ?length_put; cbn; lia]); reflexivity).
  rewrite G. apply r_comm; [exact L2 | lia | lia | rewrite !length_put; cbn; lia | rewrite length_put; cbn; lia
    | rewrite length_put; cbn; lia].
Qed.

Lemma r_gf_b1 : forall B, length B = Z.to_nat W_LEN -> g_fail_next (rb_b1 B) = g_fail_next B.
Proof.
  intros B LB. pose proof (len_w B LB) as LB'. unfold W_LEN in LB'.
  unfold rb_b1, set_M_fail, set_OW_desk_off, A_M_fail, A_OW_desk_off, OFF_M, OFF_OW, OFF_GOT, SZ_OW, SZ_GOT.
  cbv zeta. change (0xff20 + 232) with 65544. change (0x0 + 88) with 88.
  change 0xff20 with 65312. change 0xfe3c with 65084.
  change (Z.to_nat 304) with 304%nat. change (Z.to_nat 224) with 224%nat.
  r_gf. reflexivity.
Qed.

(* the by-poll stores (g_rx_fail, g_rx_times, g_rx, g_rx_len), in the binary's order *)
Lemma r_poll_w : forall X f t a g, Z.of_nat (length X) = 65616 ->
  upd (upd (upd (upd X 64992 (put 4 f)) 64996 (put 4 t)) 65008 (put 8 a)) 65016 (put 8 g) =
  set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx X a) g) t) f.
Proof.
  intros X f t a g L. unfold set_g_rx_fail, set_g_rx_times, set_g_rx_len, set_g_rx, OFF_g_rx_fail, OFF_g_rx_times,
    OFF_g_rx_len, OFF_g_rx.
  change 0xfde0 with 64992. change 0xfde4 with 64996. change 0xfdf0 with 65008. change 0xfdf8 with 65016.
  rewrite (r_comm X (put 4 f) (put 4 t) 64992 64996) by (first [r_len | rewrite ?length_put; cbn; lia]).
  rewrite (r_comm (upd X 64996 (put 4 t)) (put 4 f) (put 8 a) 64992 65008)
    by (first [r_len | rewrite ?length_put; cbn; lia]).
  rewrite (r_comm (upd (upd X 64996 (put 4 t)) 65008 (put 8 a)) (put 4 f) (put 8 g) 64992 65016)
    by (first [r_len | rewrite ?length_put; cbn; lia]).
  rewrite (r_comm X (put 4 t) (put 8 a) 64996 65008) by (first [r_len | rewrite ?length_put; cbn; lia]).
  rewrite (r_comm (upd X 65008 (put 8 a)) (put 4 t) (put 8 g) 64996 65016)
    by (first [r_len | rewrite ?length_put; cbn; lia]).
  reflexivity.
Qed.

(* after the poll: g_rx_fail = 0, g_rx = 0 *)
Lemma r_poll_w2 : forall X, Z.of_nat (length X) = 65616 ->
  upd (upd X 64992 (put 4 0)) 65008 (put 8 0) = set_g_rx_fail (set_g_rx X 0) 0.
Proof.
  intros X L. unfold set_g_rx_fail, set_g_rx, OFF_g_rx_fail, OFF_g_rx.
  change 0xfde0 with 64992. change 0xfdf0 with 65008.
  apply r_comm; first [exact L | rewrite ?length_put; cbn; lia].
Qed.

(* ---------------------------------------------------------------- the body's shared facts *)

(* What no instruction of the body changes: the stack (sp is receive's sp - 48, the window [lo, sp) above the world),
   the heap frame (fa, the n bytes, off the world, off .data.rel.ro, below the window) and the entry memory's RELRO
   bytes. *)
Definition r_inv (sp : word) (lo fa : Z) (bytes : list byte) (m0 : word -> option byte) : Prop :=
  W_BASE_PLAIN + W_LEN <= lo /\ lo + 3840 <= bv_unsigned sp /\ bv_unsigned sp mod 16 = 0 /\
  bv_unsigned sp + 48 < 2 ^ 63 /\ Z.of_nat (length bytes) <= 65535 /\
  0 < fa /\ fa + Z.max 1 (Z.of_nat (length bytes)) <= lo /\
  (fa + Z.max 1 (Z.of_nat (length bytes)) <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= fa) /\
  (fa + Z.max 1 (Z.of_nat (length bytes)) <= RELRO_BASE \/ RELRO_BASE + RELRO_LEN <= fa) /\
  relro_img m0.

Ltac r_inv_d H :=
  let I1 := fresh "I_lo" in let I2 := fresh "I_sp" in let I3 := fresh "I_al" in let I4 := fresh "I_63" in
  let I5 := fresh "I_n" in let I6 := fresh "I_fa" in let I7 := fresh "I_fl" in let I8 := fresh "I_fw" in
  let I9 := fresh "I_fr" in let I10 := fresh "I_rr" in
  destruct H as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10).

(* The state at free's entry (the tail call at 0x14cc8): receive's own sp, ra and s0-s4 back, a0 = the frame; the
   body wrote the window, the world and the frame, and leaves the world receive_m gives. *)
Definition q_body (F : bvmap 5 word) (fc : bv 32) (gp tp ra0 o0 o1 o2 o3 o4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m0 : word -> option byte) (sp fa n : Z) (B' : list byte) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms = MS (mkR ra0 (Z_to_bv 64 (sp + 48)) gp tp t0 t1 t2 o0 o1 (Z_to_bv 64 fa) a1 a2 a3 a4 a5 a6 a7
                 o2 o3 o4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 H_FREE) fc None m' (seg_rom rsegs) /\
    munch [(sp - 3840, sp + 48); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN); (fa, fa + Z.max 1 n)] m0 m' /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    wmem rsegs m' B' /\ g_fail_next B' <= 1 /\ relro_img m'.

(* ---------------------------------------------------------------- 0x14ca0-0x14cc8: settle, the epilogue, j free *)
Lemma r_tail : settle_contract ->
  forall (x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
          ra0 o0 o1 o2 o3 o4 : word) (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (lo fa : Z)
         (bytes B3 B' : list byte) (ticked : Z),
    r_inv sp lo fa bytes m0 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 o4; C8 o3; C8 o2; C8 o1; C8 o0; C8 ra0] ->
    stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
    munch [(bv_unsigned sp - 3840, bv_unsigned sp + 48); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN);
           (fa, fa + Z.max 1 (Z.of_nat (length bytes)))] m0 m ->
    wmono rsegs m0 m ->
    wmem rsegs m B3 -> g_fail_next B3 <= 1 ->
    ticked = 0 \/ ticked = 1 ->
    settle_m B3 ticked = Some (B', tt) ->
    evt rsegs (q_body F fc gp tp ra0 o0 o1 o2 o3 o4 s5 s6 s7 s8 s9 s10 s11 m0 (bv_unsigned sp) fa
                 (Z.of_nat (length bytes)) B')
      (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length bytes))) x10 x11 x12 x13 x14 x15
               x16 x17 (Z_to_bv 64 ticked) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14ca0) fc None m (seg_rom rsegs)).
Proof.
  intros SET x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
    ra0 o0 o1 o2 o3 o4 F fc m m0 lo fa bytes B3 B' ticked INV FR ST MI MU WMo WM GF Ht HS.
  unfold settle_contract, settle_ENTRY, settle_FRAME in SET.
  pose proof INV as INV0. r_inv_d INV.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  wk_facts.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* 0x14ca0: mv a0, s2; 0x14ca4: jal settle *)
  do 2 step.
  eapply evt_cut;
    [ eapply SET with (lo := lo) (B := B3) (B' := B') (ticked := ticked);
      [ reflexivity | lia | exact WM | exact HS | exact I_al | exact ST | lia | unfold w_off_stack; lia | exact MI ]
    | wk_post_call rsegs m ].
  lazymatch goal with H : B' = B3 |- _ => subst B' end.
  (* 0x14ca8: mv a0, s0; ld ra, s0, s1, s2, s3, s4; addi sp, sp, 48; j free *)
  do 9 step.
  apply evt_done. unfold QQ, q_body. do 15 eexists.
  split; [reflexivity|].
  lazymatch goal with H : munch _ m0 ?mm |- _ =>
    split; [exact H|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact GF|];
    exact (r_relro m0 mm sp fa (Z.of_nat (length bytes)) I_rr H ltac:(lia) I_fr)
  end.
Qed.

(* ---------------------------------------------------------------- 0x14c78-0x14ca0: m_rx, diginet_session_rx *)
Lemma r_mrx : m_rx_contract -> diginet_session_rx_contract -> settle_contract ->
  forall (x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
          ra0 o0 o1 o2 o3 o4 : word) (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (lo fa : Z)
         (bytes B2 B' : list byte),
    r_inv sp lo fa bytes m0 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 o4; C8 o3; C8 o2; C8 o1; C8 o0; C8 ra0] ->
    stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
    munch [(bv_unsigned sp - 3840, bv_unsigned sp + 48); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN);
           (fa, fa + Z.max 1 (Z.of_nat (length bytes)))] m0 m ->
    wmono rsegs m0 m ->
    bytes_at rsegs m fa bytes ->
    wmem rsegs m B2 -> g_fail_next B2 <= 1 ->
    rb_fin (rb_mrx fa bytes B2) = Some (B', tt) ->
    evt rsegs (q_body F fc gp tp ra0 o0 o1 o2 o3 o4 s5 s6 s7 s8 s9 s10 s11 m0 (bv_unsigned sp) fa
                 (Z.of_nat (length bytes)) B')
      (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length bytes))) x10 x11 x12 x13 x14 x15
               x16 x17 s2 s3 (Z_to_bv 64 271704) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14c78) fc None m (seg_rom rsegs)).
Proof.
  intros MRX RXC SET x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
    ra0 o0 o1 o2 o3 o4 F fc m m0 lo fa bytes B2 B' INV FR ST MI MU WMo BF WM GF HM.
  unfold m_rx_contract, m_rx_ENTRY, m_rx_FRAME in MRX.
  unfold diginet_session_rx_contract, diginet_session_rx_ENTRY, diginet_session_rx_FRAME in RXC.
  pose proof INV as INV0. r_inv_d INV.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB2.
  wk_facts.
  set (n := Z.of_nat (length bytes)) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  unfold rb_fin, rb_mrx in HM. fold n in HM.
  destruct (m_rx_m timg_plain (Some (TFrame fa bytes)) B2 n) as [[Bx t]|] eqn:HX; cbv beta iota in HM; [|discriminate HM].
  destruct (diginet_session_rx_m timg_plain (Some (TFrame fa bytes)) Bx bytes (g_now Bx)) as [[By r']|] eqn:HR;
    cbv beta iota in HM; [|discriminate HM].
  destruct (settle_m By t) as [[B4 []]|] eqn:HS; cbv beta iota in HM; [|discriminate HM].
  injection HM as EB. subst B4.
  pose proof (m_rx_m_01 _ _ _ _ _ _ HX) as Ht.
  destruct (m_rx_gk B2 LB2 timg_plain (Some (TFrame fa bytes)) B2 Bx n t (gkeep_refl B2) HX) as [LBx GBx].
  (* 0x14c78: mv a0, s0; mv a1, s1; jal m_rx *)
  do 3 step.
  eapply evt_cut;
    [ eapply MRX with (lo := lo) (B := B2) (B' := Bx) (fr := TFrame fa bytes) (n := n) (r := t);
      [ reflexivity | reflexivity
      | apply r_tframe; [lia | exact BF | unfold off_world; lia | unfold off_window; lia]
      | cbn [tf_addr]; lia | exact I_al | exact ST | lia | unfold w_off_stack; lia | exact MI | exact WM | exact HX ]
    | wk_post_call rsegs m ].
  (* 0x14c84: ld a3, 0x20(s4) = g_now *)
  step.
  change (u_at Bx 65000 8) with (g_now Bx).
  pose proof (u_at_range Bx 65000 8) as Rnow. change (u_at Bx 65000 8) with (g_now Bx) in Rnow.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rnow.
  (* 0x14c88: mv s2, a0; auipc a0; addi a0 (&g_s); mv a1, s0; mv a2, s1; jal diginet_session_rx *)
  do 6 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with H : munch _ m0 mm |- _ => pose proof (r_relro m0 mm sp fa n I_rr H ltac:(lia) I_fr) as RR end;
    eapply evt_cut;
      [ eapply RXC with (lo := lo) (bufp := fa) (now := g_now Bx) (r := r') (b := bytes) (B := Bx) (B' := By)
          (TF := Some (TFrame fa bytes));
        [ reflexivity | reflexivity | reflexivity | reflexivity | exact Rnow | assumption
        | unfold arg_blk, off_world, off_window; lia | assumption | rewrite GBx; exact GF | exact HR
        | apply r_tframe; [lia | assumption | unfold off_world; lia | unfold off_window; lia]
        | exact RR | exact I_al | assumption | lia | unfold w_off_stack; lia | assumption ]
      | wk_post_call rsegs mm ]
  end.
  (* 0x14ca0: settle *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply (r_tail SET) with (m := mm) (B3 := By) (ticked := t);
      [ exact INV0 | assumption | assumption | assumption | assumption | assumption | assumption | assumption
      | exact Ht | exact HS ]
  end.
Qed.

(* ---------------------------------------------------------------- 0x14c40-0x14ca0: the by-poll stores and the poll *)
Lemma r_poll_tail : diginet_session_poll_contract -> settle_contract ->
  forall (x1 sp gp tp x5 x6 x7 x14 x15 x16 x17 s2 s3 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
          ra0 o0 o1 o2 o3 o4 : word) (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (lo fa got pf : Z)
         (bytes B2 B' : list byte),
    r_inv sp lo fa bytes m0 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 o4; C8 o3; C8 o2; C8 o1; C8 o0; C8 ra0] ->
    stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
    munch [(bv_unsigned sp - 3840, bv_unsigned sp + 48); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN);
           (fa, fa + Z.max 1 (Z.of_nat (length bytes)))] m0 m ->
    wmono rsegs m0 m ->
    bytes_at rsegs m fa bytes ->
    wmem rsegs m B2 -> g_fail_next B2 <= 1 ->
    got = rb_got (Z.of_nat (length bytes)) ->
    rb_fin (rb_poll fa bytes pf B2) = Some (B', tt) ->
    evt rsegs (q_body F fc gp tp ra0 o0 o1 o2 o3 o4 s5 s6 s7 s8 s9 s10 s11 m0 (bv_unsigned sp) fa
                 (Z.of_nat (length bytes)) B')
      (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length bytes))) (Z_to_bv 64 got)
               (Z_to_bv 64 (Z.land pf 1)) (Z_to_bv 64 (Z.land (Z.shiftr pf 1) 1))
               (Z_to_bv 64 (rb_snd (firstn (Z.to_nat got) bytes))) x14 x15 x16 x17
               s2 s3 (Z_to_bv 64 271704) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14c40) fc None m (seg_rom rsegs)).
Proof.
  intros POLL SET x1 sp gp tp x5 x6 x7 x14 x15 x16 x17 s2 s3 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
    ra0 o0 o1 o2 o3 o4 F fc m m0 lo fa got pf bytes B2 B' INV FR ST MI MU WMo BF WM GF Hgot HM.
  unfold diginet_session_poll_contract, diginet_session_poll_ENTRY, diginet_session_poll_FRAME in POLL.
  pose proof INV as INV0. r_inv_d INV.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB2. pose proof (len_w B2 LB2) as LB2'. unfold W_LEN in LB2'.
  wk_facts.
  set (n := Z.of_nat (length bytes)) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  assert (Hg : 0 <= got <= 1514) by (rewrite Hgot; unfold rb_got, SPEC_MAX_FRAME; destruct (Z.ltb_spec 1514 n); lia).
  set (fails := Z.land (Z.shiftr pf 1) 1) in *.
  set (s := rb_snd (firstn (Z.to_nat got) bytes)) in *.
  pose proof (r_land1 (Z.shiftr pf 1)) as Hf. fold fails in Hf.
  pose proof (r_land1 pf) as Htw.
  unfold rb_fin, rb_poll in HM. cbv zeta in HM. fold n in HM. rewrite <- Hgot in HM. fold s in HM. fold fails in HM.
  destruct (diginet_session_poll_m timg_plain (Some (TFrame fa bytes))
             (set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx (set_g_rx_send B2 s) fa) got)
                (if Z.land pf 1 =? 0 then 1 else 2)) fails) 0) as [[B2d rp]|] eqn:HP; cbv beta iota in HM; [|discriminate HM].
  destruct (settle_m (set_g_rx_fail (set_g_rx B2d 0) 0) (if fails =? 0 then 1 else 0)) as [[B4 []]|] eqn:HS;
    [|discriminate HM].
  injection HM as EB. subst B4.
  (* 0x14c40: xori s2, a2, 1; addi a1, a1, 1 *)
  do 2 step.
  rewrite ?(r_ticked fails Hf), ?(r_ticked' fails Hf), ?(r_times pf Htw), ?(r_times' pf Htw).
  (* 0x14c48-0x14c58: sw a3 (g_rx_send), sw a2 (g_rx_fail), sw a1 (g_rx_times), sd s0 (g_rx), sd a0 (g_rx_len) *)
  do 5 step.
  lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?X] |- _ =>
    replace X with (set_g_rx_fail (set_g_rx_times (set_g_rx_len (set_g_rx (set_g_rx_send B2 s) fa) got)
                     (if Z.land pf 1 =? 0 then 1 else 2)) fails) in H
      by (symmetry; apply r_poll_w; unfold set_g_rx_send, OFF_g_rx_send; change 0xfddc with 64988; r_len)
  end.
  (* 0x14c5c: auipc a0; addi a0 (&g_s); mv a1, zero; jal diginet_session_poll *)
  do 4 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with H : munch _ m0 mm |- _ => pose proof (r_relro m0 mm sp fa n I_rr H ltac:(lia) I_fr) as RR end;
    eapply evt_cut;
      [ eapply POLL with (lo := lo) (w := 0) (r := rp) (TF := Some (TFrame fa bytes)) (B' := B2d);
        [ reflexivity | reflexivity | lia | eassumption
        | unfold set_g_rx_fail, set_g_rx_times, set_g_rx_len, set_g_rx, set_g_rx_send, OFF_g_rx_fail, OFF_g_rx_times,
            OFF_g_rx_len, OFF_g_rx, OFF_g_rx_send;
          change 0xfde0 with 64992; change 0xfde4 with 64996; change 0xfdf0 with 65008; change 0xfdf8 with 65016;
          change 0xfddc with 64988; r_gf; exact GF
        | exact HP
        | apply r_tframe; [lia | assumption | unfold off_world; lia | unfold off_window; lia]
        | cbn [tframe_ok tf_addr tf_bytes]; lia
        | exact RR | exact I_al | assumption | lia | unfold w_off_stack; lia | assumption ]
      | wk_post_call rsegs mm ]
  end.
  lazymatch goal with H : g_fail_next B2d <= 1 |- _ => rename H into GFd end.
  lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ B2d] |- _ =>
    pose proof (wm_len _ _ _ _ H) as LBd; pose proof (len_w B2d LBd) as LBd'; unfold W_LEN in LBd' end.
  (* 0x14c6c: sw zero (g_rx_fail); sd zero (g_rx); j 0x14ca0 *)
  do 3 step.
  lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?X] |- _ =>
    replace X with (set_g_rx_fail (set_g_rx B2d 0) 0) in H by (symmetry; apply r_poll_w2; exact LBd')
  end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply (r_tail SET) with (m := mm) (B3 := set_g_rx_fail (set_g_rx B2d 0) 0) (ticked := if fails =? 0 then 1 else 0);
      [ exact INV0 | assumption | assumption | assumption | assumption | assumption | assumption
      | unfold set_g_rx_fail, set_g_rx, OFF_g_rx_fail, OFF_g_rx; change 0xfde0 with 64992; change 0xfdf0 with 65008;
        r_gf; exact GFd
      | destruct (Z.eqb fails 0); [right|left]; reflexivity | exact HS ]
  end.
Qed.

(* ---------------------------------------------------------------- 0x14b90-0x14bd4: g_rx_send of the frame *)
Lemma r_snd_np :
  forall (ra sp gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (fa : Z)
         (bytes : list byte),
    bytes_at rsegs m fa bytes -> Z.of_nat (length bytes) <= 65535 ->
    (forall x11 x12 x13 : word,
       evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length bytes)))
                          (Z_to_bv 64 (rb_snd bytes)) x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14bd4) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length bytes)))
                       a0 (Z_to_bv 64 30) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14b90) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q fa bytes
    HB HL K.
  pose proof (bytes_at_bound rsegs m fa bytes HB) as [Hfa0 Hfa1].
  (* 0x14b90: bltu s1, a1 (n < 30) *)
  step.
  destruct (Z.ltb_spec (Z.of_nat (length bytes)) 30) as [Hs|Hs].
  { r_br true ltac:(rewrite r_ltu by lia; apply Z.ltb_lt; lia).
    (* 0x14bd0: li a0, 0 *)
    step.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (rb_snd bytes)) by (rewrite (rb_snd_short bytes ltac:(lia)); reflexivity).
    apply K. }
  r_br false ltac:(rewrite r_ltu by lia; apply Z.ltb_ge; lia).
  (* 0x14b94-0x14bac: the ethertype (bytes 12, 13) against 0x885f *)
  r_rd HB 12%nat. r_rd HB 13%nat.
  do 7 step.
  rewrite r_be16.
  change (bv_unsigned (nth 12 bytes (Z_to_bv 8 0)) * 2 ^ 8 + bv_unsigned (nth 13 bytes (Z_to_bv 8 0)))
    with (be16 bytes 12).
  pose proof (r_be16_range bytes 12) as R12.
  destruct (Z.eqb_spec (be16 bytes 12) 34911) as [He|He].
  2:{ r_br true ltac:(rewrite r_eqb by lia; rewrite (proj2 (Z.eqb_neq _ _) He); reflexivity).
      step.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (rb_snd bytes)) by (rewrite (rb_snd_eth bytes ltac:(lia) He); reflexivity).
      apply K. }
  r_br false ltac:(rewrite r_eqb by lia; rewrite He; reflexivity).
  (* 0x14bb0-0x14bc4: numbytes (bytes 14, 15) < 16 *)
  r_rd HB 14%nat. r_rd HB 15%nat.
  do 6 step.
  rewrite r_be16.
  change (bv_unsigned (nth 14 bytes (Z_to_bv 8 0)) * 2 ^ 8 + bv_unsigned (nth 15 bytes (Z_to_bv 8 0)))
    with (be16 bytes 14).
  pose proof (r_be16_range bytes 14) as R14.
  destruct (Z.ltb_spec (be16 bytes 14) 16) as [Hb|Hb].
  { r_br true ltac:(rewrite r_ltu by lia; apply Z.ltb_lt; lia).
    step.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (rb_snd bytes)) by (rewrite (rb_snd_len bytes ltac:(lia) He ltac:(lia)); reflexivity).
    apply K. }
  r_br false ltac:(rewrite r_ltu by lia; apply Z.ltb_ge; lia).
  (* 0x14bc8-0x14bcc: addi a1, s1, -14; bgeu a1, a0 *)
  do 2 step.
  destruct (Z.ltb_spec (Z.of_nat (length bytes) + -14) (be16 bytes 14)) as [Hl|Hl].
  { r_br false ltac:(rewrite r_ltu by lia; rewrite (proj2 (Z.ltb_lt _ _) Hl); reflexivity).
    step.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (rb_snd bytes)) by (rewrite (rb_snd_len bytes ltac:(lia) He ltac:(lia)); reflexivity).
    apply K. }
  r_br true ltac:(rewrite r_ltu by lia; rewrite (proj2 (Z.ltb_ge _ _) Hl); reflexivity).
  (* 0x14ccc-0x14cf4: send = the big-endian 32 bits at byte 18; j 0x14bd4 *)
  r_rd HB 18%nat. r_rd HB 19%nat. r_rd HB 20%nat. r_rd HB 21%nat.
  do 11 step.
  rewrite r_be32.
  change (bv_unsigned (nth 18 bytes (Z_to_bv 8 0)) * 2 ^ 24 + bv_unsigned (nth 19 bytes (Z_to_bv 8 0)) * 2 ^ 16 +
          bv_unsigned (nth 20 bytes (Z_to_bv 8 0)) * 2 ^ 8 + bv_unsigned (nth 21 bytes (Z_to_bv 8 0)))
    with (be32 bytes 18).
  rewrite <- (rb_snd_ok bytes ltac:(lia) He ltac:(lia)).
  apply K.
Qed.

(* ---------------------------------------------------------------- 0x14bfc-0x14c40: g_rx_send of the polled frame *)
Lemma rb_snd_gb : forall bytes got, got = rb_got (Z.of_nat (length bytes)) ->
  rb_snd (firstn (Z.to_nat got) bytes) =
  if Z.of_nat (length bytes) <? 30 then 0 else if negb (be16 bytes 12 =? 34911) then 0
  else if (be16 bytes 14 <? 16) || (got - 14 <? be16 bytes 14) then 0 else be32 bytes 18.
Proof.
  intros bytes got Hg.
  assert (Hr : 0 <= got <= Z.of_nat (length bytes) /\
               (got = Z.of_nat (length bytes) \/ (got = 1514 /\ 1514 < Z.of_nat (length bytes))))
    by (rewrite Hg; unfold rb_got, SPEC_MAX_FRAME; destruct (Z.ltb_spec 1514 (Z.of_nat (length bytes))); lia).
  rewrite rb_snd_char. rewrite firstn_length_le by lia.
  destruct (Z.ltb_spec (Z.of_nat (length bytes)) 30) as [Hs|Hs].
  - rewrite (proj2 (Nat.ltb_lt _ _)) by lia. reflexivity.
  - rewrite (proj2 (Nat.ltb_ge _ _)) by lia.
    rewrite !r_be16_fn by lia. rewrite r_be32_fn by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma r_snd_p :
  forall (ra sp gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (fa : Z)
         (bytes : list byte) (got : Z),
    bytes_at rsegs m fa bytes -> Z.of_nat (length bytes) <= 65535 -> got = rb_got (Z.of_nat (length bytes)) ->
    (forall x14 x15 x16 : word,
       evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length bytes)))
                          (Z_to_bv 64 got) a1 a2 (Z_to_bv 64 (rb_snd (firstn (Z.to_nat got) bytes))) x14 x15 x16 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14c40) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length bytes)))
                       (Z_to_bv 64 got) a1 a2 (Z_to_bv 64 30) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14bfc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q fa bytes got
    HB HL Hgot K.
  pose proof (bytes_at_bound rsegs m fa bytes HB) as [Hfa0 Hfa1].
  assert (Hr : 0 <= got <= Z.of_nat (length bytes) /\
               (got = Z.of_nat (length bytes) \/ (got = 1514 /\ 1514 < Z.of_nat (length bytes))))
    by (rewrite Hgot; unfold rb_got, SPEC_MAX_FRAME; destruct (Z.ltb_spec 1514 (Z.of_nat (length bytes))); lia).
  pose proof (rb_snd_gb bytes got Hgot) as Esv.
  set (sv := rb_snd (firstn (Z.to_nat got) bytes)) in K, Esv.
  (* 0x14bfc: bltu s1, a3 (n < 30) *)
  step.
  destruct (Z.ltb_spec (Z.of_nat (length bytes)) 30) as [Hs|Hs].
  { r_br true ltac:(rewrite r_ltu by lia; apply Z.ltb_lt; lia).
    (* 0x14c3c: li a3, 0 *)
    step.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 sv) by (rewrite Esv; rewrite ?(proj2 (Z.ltb_lt _ _) Hs); reflexivity).
    apply K. }
  r_br false ltac:(rewrite r_ltu by lia; apply Z.ltb_ge; lia).
  (* 0x14c00-0x14c18: the ethertype against 0x885f *)
  r_rd HB 12%nat. r_rd HB 13%nat.
  do 7 step.
  rewrite r_be16.
  change (bv_unsigned (nth 12 bytes (Z_to_bv 8 0)) * 2 ^ 8 + bv_unsigned (nth 13 bytes (Z_to_bv 8 0)))
    with (be16 bytes 12).
  pose proof (r_be16_range bytes 12) as R12.
  destruct (Z.eqb_spec (be16 bytes 12) 34911) as [He|He].
  2:{ r_br true ltac:(rewrite r_eqb by lia; rewrite (proj2 (Z.eqb_neq _ _) He); reflexivity).
      step.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 sv)
        by (rewrite Esv; rewrite ?(proj2 (Z.ltb_ge _ _) Hs), ?(proj2 (Z.eqb_neq _ _) He); reflexivity).
      apply K. }
  r_br false ltac:(rewrite r_eqb by lia; rewrite He; reflexivity).
  (* 0x14c1c-0x14c30: numbytes < 16 *)
  r_rd HB 14%nat. r_rd HB 15%nat.
  do 6 step.
  rewrite r_be16.
  change (bv_unsigned (nth 14 bytes (Z_to_bv 8 0)) * 2 ^ 8 + bv_unsigned (nth 15 bytes (Z_to_bv 8 0)))
    with (be16 bytes 14).
  pose proof (r_be16_range bytes 14) as R14.
  destruct (Z.ltb_spec (be16 bytes 14) 16) as [Hb|Hb].
  { r_br true ltac:(rewrite r_ltu by lia; apply Z.ltb_lt; lia).
    step.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 sv)
      by (rewrite Esv; rewrite ?(proj2 (Z.ltb_ge _ _) Hs), ?He, ?(proj2 (Z.ltb_lt _ _) Hb); reflexivity).
    apply K. }
  r_br false ltac:(rewrite r_ltu by lia; apply Z.ltb_ge; lia).
  (* 0x14c34-0x14c38: addi a4, a0, -14; bgeu a4, a3 *)
  do 2 step.
  assert (Ug : bv_unsigned (Z_to_bv 64 got) = got) by (apply unsigned_lit; lia).
  rewrite ?Ug.
  destruct (Z.ltb_spec (got + -14) (be16 bytes 14)) as [Hl|Hl].
  { r_br false ltac:(rewrite r_ltu by lia; rewrite (proj2 (Z.ltb_lt _ _) Hl); reflexivity).
    step.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 sv)
      by (rewrite Esv; rewrite ?(proj2 (Z.ltb_ge _ _) Hs), ?He, ?(proj2 (Z.ltb_ge _ _) Hb),
            ?(proj2 (Z.ltb_lt (got - 14) (be16 bytes 14)) ltac:(lia)); reflexivity).
    apply K. }
  r_br true ltac:(rewrite r_ltu by lia; rewrite (proj2 (Z.ltb_ge _ _) Hl); reflexivity).
  (* 0x14cf8-0x14d20: the big-endian 32 bits at byte 18; j 0x14c40 *)
  r_rd HB 18%nat. r_rd HB 19%nat. r_rd HB 20%nat. r_rd HB 21%nat.
  do 11 step.
  rewrite r_be32.
  change (bv_unsigned (nth 18 bytes (Z_to_bv 8 0)) * 2 ^ 24 + bv_unsigned (nth 19 bytes (Z_to_bv 8 0)) * 2 ^ 16 +
          bv_unsigned (nth 20 bytes (Z_to_bv 8 0)) * 2 ^ 8 + bv_unsigned (nth 21 bytes (Z_to_bv 8 0)))
    with (be32 bytes 18).
  replace (be32 bytes 18) with sv
    by (rewrite Esv; rewrite ?(proj2 (Z.ltb_ge _ _) Hs), ?He, ?(proj2 (Z.ltb_ge _ _) Hb),
          ?(proj2 (Z.ltb_ge (got - 14) (be16 bytes 14)) ltac:(lia)); reflexivity).
  apply K.
Qed.

(* ---------------------------------------------------------------- 0x14b50-0x14bfc: op_begin, g_rx_send, the branch *)
Lemma r_b50 : memset_contract -> diginet_session_poll_contract -> m_rx_contract -> diginet_session_rx_contract ->
  settle_contract ->
  forall (x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
          ra0 o0 o1 o2 o3 o4 : word) (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte)
         (lo fa by_poll pf : Z) (bytes B B' : list byte),
    r_inv sp lo fa bytes m0 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 o4; C8 o3; C8 o2; C8 o1; C8 o0; C8 ra0] ->
    stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
    munch [(bv_unsigned sp - 3840, bv_unsigned sp + 48); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN);
           (fa, fa + Z.max 1 (Z.of_nat (length bytes)))] m0 m ->
    wmono rsegs m0 m ->
    bytes_at rsegs m fa bytes ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    - 2 ^ 31 <= by_poll < 2 ^ 31 -> bv_unsigned s2 mod 2 ^ 32 = pf ->
    rb_fin (if negb (by_poll =? 0) then rb_poll fa bytes pf (set_g_rx_send (rb_b1 B) (rb_snd bytes))
            else rb_mrx fa bytes (set_g_rx_send (rb_b1 B) (rb_snd bytes))) = Some (B', tt) ->
    evt rsegs (q_body F fc gp tp ra0 o0 o1 o2 o3 o4 s5 s6 s7 s8 s9 s10 s11 m0 (bv_unsigned sp) fa
                 (Z.of_nat (length bytes)) B')
      (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length bytes))) x10 x11 x12 x13 x14 x15
               x16 x17 s2 (Z_to_bv 64 by_poll) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14b50) fc None m (seg_rom rsegs)).
Proof.
  intros MSET POLL MRX RXC SET x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 x20 s5 s6 s7 s8 s9 s10 s11
    x28 x29 x30 x31 ra0 o0 o1 o2 o3 o4 F fc m m0 lo fa by_poll pf bytes B B' INV FR ST MI MU WMo BF WM GF Hbp Hpf HM.
  unfold memset_contract, MEMSET in MSET.
  pose proof INV as INV0. r_inv_d INV.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts.
  (* 0x14b50-0x14b64: auipc a0; addi s4, a0, -0x5f8 (s4 = &g_fail_next); addi a0, s4, 0x158 (&OW); li a2, 0x130;
     mv a1, zero; jal memset *)
  do 6 step.
  assert (DST : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 272048))
                  [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 304))) (sub B 65312 304)]).
  { rewrite (unsigned_lit 272048), (unsigned_lit 304) by lia.
    apply (wm_piece rsegs W_BASE_PLAIN m B 65312 304); [exact WM | rewrite Ew0; reflexivity | lia | lia | lia]. }
  assert (U1 : bv_unsigned (Z_to_bv 64 272048) = 272048) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 304) = 304) by (apply unsigned_lit; lia).
  eapply evt_cut; [eapply MSET; [exact DST | exact MI] | wk_post_call rsegs m].
  lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB _ (upd B 65312 _)] |- _ =>
    rewrite (r_zsrc 304) in H by lia end.
  (* 0x14b68-0x14b74: addi a0, s4, 0x74 (&GOT); li a2, 0xe0; mv a1, zero; jal memset *)
  do 4 step.
  lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?Bc] |- _ =>
    assert (DST2 : rw_cells rsegs mm (bv_unsigned (Z_to_bv 64 271820))
                     [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 224))) (sub Bc 65084 224)])
      by (rewrite (unsigned_lit 271820), (unsigned_lit 224) by lia;
          apply (wm_piece rsegs W_BASE_PLAIN mm Bc 65084 224); [exact H | rewrite Ew0; reflexivity | lia | lia | lia])
  end.
  assert (U3 : bv_unsigned (Z_to_bv 64 271820) = 271820) by (apply unsigned_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 224) = 224) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply MSET; [exact DST2 | assumption] | wk_post_call rsegs mm] end.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB _ (upd _ 65084 _)] |- _ =>
    rewrite (r_zsrc 224) in H by lia end.
  (* 0x14b78-0x14b8c: lbu a0, 0(s4) (g_fail_next); auipc a1; sw a0 (M.fail); li a0, -1; li a1, 30;
     sw a0, 0x240(s4) (OW.desk_off) *)
  do 6 step.
  lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?X] |- _ =>
    replace X with (rb_b1 B) in H by (symmetry; rewrite <- (r_b1_eq B LB); reflexivity);
    pose proof (wm_len _ _ _ _ H) as LB1
  end.
  pose proof (len_w _ LB1) as LB1'. unfold W_LEN in LB1'.
  pose proof (r_gf_b1 B LB) as GB1.
  (* 0x14b90-0x14bd0: g_rx_send of the frame *)
  apply r_snd_np; [assumption | lia |].
  intros a1' a2' a3'.
  (* 0x14bd4: sw a0, 0x14(s4) (g_rx_send) *)
  step.
  lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?X] |- _ =>
    change X with (set_g_rx_send (rb_b1 B) (rb_snd bytes)) in H end.
  assert (GB2 : g_fail_next (set_g_rx_send (rb_b1 B) (rb_snd bytes)) <= 1).
  { unfold set_g_rx_send, OFF_g_rx_send. change 0xfddc with 64988. r_gf. rewrite GB1. exact GF. }
  (* 0x14bd8: beqz s3 (by_poll), 0x14c78 *)
  step.
  destruct (Z.eqb_spec by_poll 0) as [Hz|Hz].
  { r_br true ltac:(rewrite r_eqb0 by lia; apply Z.eqb_eq; exact Hz).
    try rewrite (proj2 (Z.eqb_eq _ _) Hz) in HM. cbn [negb] in HM.
    eapply (r_mrx MRX RXC SET);
      [ exact INV0 | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
      | exact GB2 | exact HM ]. }
  r_br false ltac:(rewrite r_eqb0 by lia; apply Z.eqb_neq; exact Hz).
  try rewrite (proj2 (Z.eqb_neq _ _) Hz) in HM. cbn [negb] in HM.
  (* 0x14bdc-0x14be8: li a1, 1514; mv a0, s1; bltu s1, a1; li a0, 1514 (got) *)
  do 3 step.
  destruct (Z.ltb_spec (Z.of_nat (length bytes)) 1514) as [Hg|Hg].
  - r_br true ltac:(rewrite r_ltu by lia; apply Z.ltb_lt; exact Hg).
    (* 0x14bec-0x14bf8: andi a1, s2, 1; slli a2, s2, 62; li a3, 30; srli a2, a2, 63 *)
    do 4 step.
    rewrite (r_twice s2), (r_fails s2), Hpf.
    eapply r_snd_p with (got := Z.of_nat (length bytes));
      [ assumption | lia
      | unfold rb_got, SPEC_MAX_FRAME; rewrite (proj2 (Z.ltb_ge 1514 (Z.of_nat (length bytes))) ltac:(lia)); reflexivity
      | ].
    intros a4' a5' a6'.
    eapply (r_poll_tail POLL SET) with (got := Z.of_nat (length bytes)) (pf := pf)
      (B2 := set_g_rx_send (rb_b1 B) (rb_snd bytes));
      [ exact INV0 | assumption | assumption | assumption | assumption | assumption | assumption | assumption
      | exact GB2
      | unfold rb_got, SPEC_MAX_FRAME; rewrite (proj2 (Z.ltb_ge 1514 (Z.of_nat (length bytes))) ltac:(lia)); reflexivity
      | exact HM ].
  - r_br false ltac:(rewrite r_ltu by lia; apply Z.ltb_ge; exact Hg).
    step.
    do 4 step.
    rewrite (r_twice s2), (r_fails s2), Hpf.
    eapply r_snd_p with (got := 1514);
      [ assumption | lia
      | unfold rb_got, SPEC_MAX_FRAME; destruct (Z.ltb_spec 1514 (Z.of_nat (length bytes))); cbv beta iota; lia
      | ].
    intros a4' a5' a6'.
    eapply (r_poll_tail POLL SET) with (got := 1514) (pf := pf)
      (B2 := set_g_rx_send (rb_b1 B) (rb_snd bytes));
      [ exact INV0 | assumption | assumption | assumption | assumption | assumption | assumption | assumption
      | exact GB2
      | unfold rb_got, SPEC_MAX_FRAME; destruct (Z.ltb_spec 1514 (Z.of_nat (length bytes))); cbv beta iota; lia
      | exact HM ].
Qed.

(* ---------------------------------------------------------------- body: 0x14b34-0x14cc8 *)
Lemma r_body : memset_contract -> memcpy_contract -> diginet_session_poll_contract -> m_rx_contract ->
  diginet_session_rx_contract -> settle_contract ->
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ra0 o0 o1 o2 o3 o4 : word) (fa p : Z) (bytes junk : list byte) (by_poll pf : Z) (B B' : list byte),
    r_inv sp lo fa bytes m ->
    - 2 ^ 31 <= by_poll < 2 ^ 31 -> bv_unsigned s2 mod 2 ^ 32 = pf ->
    rw_cells rsegs m (bv_unsigned sp) [C8 o4; C8 o3; C8 o2; C8 o1; C8 o0; C8 ra0] ->
    stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    (bytes = [] \/ (bytes_at rsegs m p bytes /\ (p + Z.of_nat (length bytes) <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= p) /\
        (p + Z.of_nat (length bytes) <= bv_unsigned sp - 3840 \/ bv_unsigned sp + 48 <= p) /\
        (p + Z.of_nat (length bytes) <= fa \/ fa + Z.max 1 (Z.of_nat (length bytes)) <= p))) ->
    rw_cells rsegs m fa [CB (Z.to_nat (Z.max 1 (Z.of_nat (length bytes)))) junk] ->
    receive_m timg_plain B fa bytes by_poll pf = Some (B', tt) ->
    evt rsegs (q_body F fc gp tp ra0 o0 o1 o2 o3 o4 s5 s6 s7 s8 s9 s10 s11 m (bv_unsigned sp) fa
                 (Z.of_nat (length bytes)) B')
      (MS (mkR ra sp gp tp t0 t1 t2 o0 (Z_to_bv 64 (Z.of_nat (length bytes))) (Z_to_bv 64 fa) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 by_poll) (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 R_MALLOC_RET) fc None m (seg_rom rsegs)).
Proof.
  intros MSET MCPY POLL MRX RXC SET ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ra0 o0 o1 o2 o3 o4 fa p bytes junk by_poll pf B B' HINV Hbp Hpf FR ST MI WM GF HPd FRA HM.
  unfold memcpy_contract in MCPY.
  pose proof HINV as INV0. r_inv_d HINV.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  rewrite (rb_eq B fa bytes by_poll pf ltac:(lia)) in HM.
  pose proof (munch_refl [(bv_unsigned sp - 3840, bv_unsigned sp + 48); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN);
     (fa, fa + Z.max 1 (Z.of_nat (length bytes)))] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  wk_facts.
  unfold R_MALLOC_RET.
  (* 0x14b34: beqz a0, 0x14d24 (abort): the frame malloc returned is not NULL *)
  step.
  r_br false ltac:(rewrite r_eqb by lia; apply Z.eqb_neq; lia).
  (* 0x14b38: mv s0, a0; 0x14b3c: beqz s1, 0x14b50 *)
  do 2 step.
  destruct (Z.eqb_spec (Z.of_nat (length bytes)) 0) as [Hn|Hn].
  { r_br true ltac:(rewrite r_eqb by lia; apply Z.eqb_eq; exact Hn).
    assert (Eb : bytes = []) by (destruct bytes; [reflexivity | cbn in Hn; lia]).
    eapply (r_b50 MSET POLL MRX RXC SET);
      [ exact INV0 | exact FR | exact ST | exact MI | exact MU0 | exact WM0
      | rewrite Eb; apply r_bytes_nil; lia | exact WM | exact GF | exact Hbp | exact Hpf | exact HM ]. }
  r_br false ltac:(rewrite r_eqb by lia; apply Z.eqb_neq; exact Hn).
  destruct HPd as [Eb|(HP & Hpw & Hps & Hpa)]; [subst bytes; cbn in Hn; lia|].
  pose proof (bytes_at_bound rsegs m p bytes HP) as [Hp0 Hp1].
  assert (Ufa : bv_unsigned (Z_to_bv 64 fa) = fa) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 (Z.of_nat (length bytes))) = Z.of_nat (length bytes))
    by (apply unsigned_lit; lia).
  assert (Up : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (FRA' : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 fa))
                   [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (length bytes))))) junk]).
  { rewrite Ufa, Un. replace (Z.of_nat (length bytes)) with (Z.max 1 (Z.of_nat (length bytes))) at 1 by lia.
    exact FRA. }
  clear FRA.
  (* 0x14b40-0x14b4c: mv a0, s0; mv a1, s4; mv a2, s1; jal memcpy (the n bytes at p into the frame) *)
  do 4 step.
  eapply evt_cut;
    [ eapply MCPY with (src := bytes) (junk := junk);
      [ rewrite Up; exact HP | rewrite Un, Nat2Z.id; reflexivity | exact FRA' | rewrite Ufa, Up, Un; lia | exact MI ]
    | wk_post_call rsegs m ].
  lazymatch goal with H : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 fa)) [CB _ bytes] |- _ =>
    rewrite Ufa in H; pose proof (r_cb_bytes _ _ _ _ H) as BF end.
  eapply (r_b50 MSET POLL MRX RXC SET);
    [ exact INV0 | eassumption | eassumption | eassumption | exact MU0 | eassumption | exact BF | eassumption | exact GF
    | exact Hbp | exact Hpf | exact HM ].
Qed.

(* ---------------------------------------------------------------- glue facts of this walk *)

Lemma r_out1 : forall a b x, ~ Frame.outside [(a, b)] x -> a <= x < b.
Proof.
  intros a b x H. destruct (Z_le_dec a x); destruct (Z_lt_dec x b); try lia.
  all: exfalso; apply H; cbn [Frame.outside]; repeat split; lia.
Qed.

Lemma r_out3 : forall a1 b1 a2 b2 a3 b3 x, ~ Frame.outside [(a1, b1); (a2, b2); (a3, b3)] x ->
  a1 <= x < b1 \/ a2 <= x < b2 \/ a3 <= x < b3.
Proof.
  intros a1 b1 a2 b2 a3 b3 x H.
  destruct (Z_le_dec a1 x); destruct (Z_lt_dec x b1); try (left; lia).
  all: destruct (Z_le_dec a2 x); destruct (Z_lt_dec x b2); try (right; left; lia).
  all: destruct (Z_le_dec a3 x); destruct (Z_lt_dec x b3); try (right; right; lia).
  all: exfalso; apply H; cbn [Frame.outside]; repeat split; lia.
Qed.

(* .data.rel.ro outside one span of a run *)
Lemma r_relro1 : forall m0 m a b, relro_img m0 -> munch [(a, b)] m0 m -> RELRO_BASE + RELRO_LEN <= a ->
  relro_img m.
Proof.
  intros m0 m a b R MU H i Hi. unfold mrd. rewrite (MU (wa (RELRO_BASE + i))); [exact (R i Hi)|].
  unfold RELRO_BASE, RELRO_LEN in *. cbn [outside]. rewrite wa_unsigned by lia. refine (conj _ I); lia.
Qed.

(* .data.rel.ro kept byte by byte *)
Lemma r_relro_kept : forall m m', relro_img m ->
  (forall a, RELRO_BASE <= a < RELRO_BASE + RELRO_LEN -> mbyte rsegs m' a = mbyte rsegs m a) -> relro_img m'.
Proof.
  intros m m' R H i Hi. change (mrd rsegs m' (wa (RELRO_BASE + i))) with (mbyte rsegs m' (RELRO_BASE + i)).
  rewrite (H (RELRO_BASE + i) ltac:(lia)). exact (R i Hi).
Qed.

Lemma r_blk_bytes : forall (Bm : malloc_syms) m A bs, ms_segs Bm = rsegs -> 0 <= A ->
  A + Z.of_nat (length bs) <= 2 ^ 64 -> blk_data Bm m A bs -> bytes_at rsegs m A bs.
Proof.
  intros Bm m A bs HS H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, HS. reflexivity.
Qed.

(* ---------------------------------------------------------------- receive *)

Section Top.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis MSET : memset_contract.
Hypothesis MCPY : memcpy_contract.
Hypothesis POLL : diginet_session_poll_contract.
Hypothesis MRX : m_rx_contract.
Hypothesis RXC : diginet_session_rx_contract.
Hypothesis SET : settle_contract.

Theorem receive_holds_of : @receive_contract fx rc B API.
Proof.
  intros BI L A regs mem md b Bw p bytes by_poll pf Hpre Hfrm Hargs Hroom.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX & ERRNO_LOW & CTX_LOW & WORLD & RELRO).
  pose proof Hpre as ((HM & HW & HB & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Haux) & HID & Hh & Hl & Hro
    & Hres & Hwos & WMw & GFw & RRw).
  destruct Hargs as (E10 & E11 & E12 & Hbp & Hpf & Hpfr & Hn & Hblk & Hsrc & Hmod).
  set (n := Z.of_nat (length bytes)) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof (sr_ceiling) as Hrt. unfold SR_RES_TOP in Hrt.
  unfold receive_FRAME, ALLOC_STACK in Hceil, Hstw, Hwos. unfold w_off_stack in Hwos.
  change (bv_unsigned (YK11.getr regs 2)) with (spZ regs) in Hwos.
  assert (Esp : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  pose proof (bv_unsigned_in_range _ (reg_get regs 2)) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (WE : W_BASE_PLAIN + W_LEN = 0x427e0) by reflexivity.
  rewrite SEGS in Hro.
  assert (FR0 : sr_fr B API receive_FRAME (spZ regs) L A mem md L A mem md)
    by (eapply sr_fr_init; eassumption).
  assert (E10' : reg_get regs 10 = Z_to_bv 64 p) by exact E10.
  assert (E11' : reg_get regs 11 = Z_to_bv 64 n) by exact E11.
  assert (ST0 : Frame.stk rsegs (normalize rsegs mem) (spZ regs - 8240) (bv_unsigned (reg_get regs 2))).
  { rewrite <- Esp. eapply norm_stk; try eassumption; try (unfold SR_RES_TOP; lia).
    all: intros a Ha; apply Hstw; lia. }
  pose proof (sr_wmem_norm mem Bw Hro WMw) as WMn.
  pose proof (sr_relro_norm mem Hro RRw) as RRn.
  rewrite SEGS.
  (* ---- entry: 0x14afc-0x14b30, on the normalized memory *)
  eapply (g_run B API) with (stk := receive_FRAME) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md).
  all: try eassumption.
  all: try (unfold receive_FRAME, ALLOC_STACK; lia).
  { unfold Regs6ss.mkR_of, receive_ENTRY. rewrite E10', E11'.
    eapply r_entry with (lo := spZ regs - 8240); [exact ST0 | lia | apply mem_inv_normalize | lia | lia]. }
  { intros ms (m' & -> & MU & WMo & _).
    do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WMo|].
    intros x Hx NO. left. apply r_out1 in NO. unfold receive_FRAME, ALLOC_STACK. lia. }
  intros R F pc' fc ma HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (m'' & HE & MU1 & WMo1 & MI1 & ST1 & RW1).
  injection HE as ER EF EP EC EM. subst R F pc' fc m''.
  set (sp1 := Z_to_bv 64 (bv_unsigned (reg_get regs 2) - 48)) in *.
  assert (Usp1 : bv_unsigned sp1 = bv_unsigned (reg_get regs 2) - 48) by (apply unsigned_lit; lia).
  assert (G11 : YK11.getr regs1 1 = Z_to_bv 64 R_MALLOC_RET) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G12 : YK11.getr regs1 2 = sp1) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (Hsp1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G12; rewrite Usp1; reflexivity).
  (* the world and .data.rel.ro after the entry run *)
  assert (WM1' : wmem rsegs ma Bw).
  { eapply rw_cells_transport; [exact WMn | exact MU1 | exact WMo1 |]. cbn [disjoint_from cells_size csize].
    rewrite Nat.add_0_r, Z2Nat.id by (unfold W_LEN; lia). refine (conj _ I). lia. }
  pose proof (sr_wmem_back m1 ma Bw Hrel WM1') as WM1.
  assert (RR1 : relro_img m1).
  { apply (sr_relro_back m1 ma Hrel). apply (r_relro1 (normalize rsegs mem) ma _ _ RRn MU1).
    unfold RELRO_BASE, RELRO_LEN. lia. }
  pose proof (sr_rw_cells_rel m1 ma _ _ Hrel RW1) as RW1'.
  (* ---- malloc (n ? n : 1) *)
  rewrite <- SEGS. rewrite <- HMAL.
  eapply (g_malloc B API) with (stk := receive_FRAME) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (n := Z.max 1 n) (bres := b).
  all: try eassumption.
  all: try (rewrite ?Hsp1; unfold receive_FRAME, ALLOC_STACK; lia).
  all: try (rewrite G11; apply ret_ok_even; reflexivity).
  all: try (rewrite Hsp1; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z.mod_add by lia;
            exact Hal).
  all: try (rewrite (sr_getr_eqv _ _ _ Hx); exact Htp).
  all: try (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  intros L1 A1 regs2 mem2 md2 res FR2 Hrp2 G210 Hr1 Hr2 Hr16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2 Hsk2.
  rewrite G11, SEGS.
  set (nb := Z.max 1 n) in *.
  assert (Hnbe : nb = Z.max 1 n) by reflexivity.
  assert (Hne : n = Z.of_nat (length bytes)) by reflexivity.
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & Hmd2 & Hhigh2 & Himg2 & Hub2 & Hbyt2 & Hstw2 & Herr2 & Hgd2 & Hro2
    & Hle2 & Hlen2).
  assert (Hres_in : In (res, nb) (blocks L1 A1)) by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (PW : pairwise ranges_disjoint (b1 ++ (res, nb) :: b2)).
  { rewrite <- Eb1. exact (mr_blocks_disjoint B _ (aa_laws API) L1 A1 mem2 md2 HM2). }
  assert (MINE : forall a k, In (a, k) (blocks L A) -> a + k <= res \/ res + nb <= a).
  { intros a k Hak. rewrite Eb2 in Hak. pose proof (sr_disj_mid b1 (res, nb) b2 (a, k) PW Hak) as H.
    cbn [fst snd] in H. lia. }
  (* registers after malloc *)
  assert (E22 : reg_get regs2 2 = sp1)
    by (change (reg_get regs2 2) with (YK11.getr regs2 (Z_to_bv 5 2)); rewrite (Hrp2 2 ltac:(unfold callee_saved; lia));
        exact G12).
  assert (E2k : forall k, (k = 3 \/ k = 4 \/ k = 8 \/ 21 <= k <= 27) ->
                  YK11.getr regs2 (Z_to_bv 5 k) = YK11.getr regs (Z_to_bv 5 k)).
  { intros k Hk. rewrite (Hrp2 k ltac:(unfold callee_saved; lia)), (sr_getr_eqv _ _ _ Hx).
    destruct Hk as [->|[->|[->|Hk]]]; [reflexivity | reflexivity | reflexivity |].
    assert (k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) as Hc by lia.
    repeat (destruct Hc as [->|Hc]; [reflexivity|]). subst k. reflexivity. }
  assert (E23 : reg_get regs2 3 = reg_get regs 3) by exact (E2k 3 ltac:(lia)).
  assert (E24 : reg_get regs2 4 = reg_get regs 4) by exact (E2k 4 ltac:(lia)).
  assert (E28 : reg_get regs2 8 = reg_get regs 8) by exact (E2k 8 ltac:(lia)).
  assert (E221 : reg_get regs2 21 = reg_get regs 21) by exact (E2k 21 ltac:(lia)).
  assert (E222 : reg_get regs2 22 = reg_get regs 22) by exact (E2k 22 ltac:(lia)).
  assert (E223 : reg_get regs2 23 = reg_get regs 23) by exact (E2k 23 ltac:(lia)).
  assert (E224 : reg_get regs2 24 = reg_get regs 24) by exact (E2k 24 ltac:(lia)).
  assert (E225 : reg_get regs2 25 = reg_get regs 25) by exact (E2k 25 ltac:(lia)).
  assert (E226 : reg_get regs2 26 = reg_get regs 26) by exact (E2k 26 ltac:(lia)).
  assert (E227 : reg_get regs2 27 = reg_get regs 27) by exact (E2k 27 ltac:(lia)).
  assert (E29 : reg_get regs2 9 = Z_to_bv 64 n)
    by (change (reg_get regs2 9) with (YK11.getr regs2 (Z_to_bv 5 9));
        rewrite (Hrp2 9 ltac:(unfold callee_saved; lia)), (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (E210 : reg_get regs2 10 = Z_to_bv 64 res) by exact G210.
  assert (E218 : reg_get regs2 18 = reg_get regs 13)
    by (change (reg_get regs2 18) with (YK11.getr regs2 (Z_to_bv 5 18));
        rewrite (Hrp2 18 ltac:(unfold callee_saved; lia)), (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (E219 : reg_get regs2 19 = Z_to_bv 64 by_poll)
    by (change (reg_get regs2 19) with (YK11.getr regs2 (Z_to_bv 5 19));
        rewrite (Hrp2 19 ltac:(unfold callee_saved; lia)), (sr_getr_eqv _ _ _ Hx); exact E12).
  assert (E220 : reg_get regs2 20 = Z_to_bv 64 p)
    by (change (reg_get regs2 20) with (YK11.getr regs2 (Z_to_bv 5 20));
        rewrite (Hrp2 20 ltac:(unfold callee_saved; lia)), (sr_getr_eqv _ _ _ Hx); reflexivity).
  (* memory facts for the body, on the normalized memory after malloc *)
  assert (WM2 : wmem rsegs mem2 Bw).
  { apply (sr_rw_cells_frame m1 mem2 _ _ WM1). intros a Ha. cbn [cells_size csize] in Ha.
    rewrite Nat.add_0_r, Z2Nat.id in Ha by (unfold W_LEN; lia).
    destruct (Hsk2 a (or_introl Ha)) as [E1 E2]. rewrite SEGS in E1, E2. split; [exact E1 | tauto]. }
  assert (RR2 : relro_img mem2).
  { apply (r_relro_kept m1 mem2 RR1). intros a Ha. destruct (Hsk2 a (or_intror Ha)) as [E1 _].
    rewrite SEGS in E1. exact E1. }
  assert (RW2 : rw_cells rsegs mem2 (bv_unsigned sp1)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { rewrite Usp1. apply (sr_rw_cells_frame m1 mem2 _ _ RW1'). intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    destruct (Habove2 a ltac:(rewrite Hsp1; lia)) as [E1 E2]. rewrite SEGS in E1, E2. split; [exact E1 | tauto]. }
  assert (NIhi : forall a, 0x64000 <= a -> ~ in_img B a)
    by (intros a Ha Hi; pose proof (sr_in_img_top B a SEGS Hi) as H; unfold SR_RES_TOP in H; lia).
  assert (RW3 : rw_cells rsegs (normalize rsegs mem2) (bv_unsigned sp1)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (sr_rw_cells_norm B mem2 _ _ SEGS Hro2); [| exact RW2].
    intros i Hi. cbn [cells_size csize Nat.add] in Hi. apply NIhi. lia. }
  assert (ST2 : Frame.stk rsegs (normalize rsegs mem2) (spZ regs - 8240) (bv_unsigned sp1)).
  { eapply norm_stk; try eassumption; try (unfold SR_RES_TOP; lia).
    all: intros a Ha; apply Hstw2; unfold receive_FRAME, ALLOC_STACK; lia. }
  destruct (norm_blk B API SEGS AX L1 A1 mem2 md2 res nb HM2 Hres_in ltac:(lia) Hro2) as [junk HJ].
  assert (Hfw : res + nb <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= res)
    by exact (wmem_off_heap B res nb SEGS ltac:(lia) Hnimg).
  assert (Hfr : res + nb <= RELRO_BASE \/ RELRO_BASE + RELRO_LEN <= res).
  { destruct (Z_le_gt_dec (res + nb) RELRO_BASE) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec (RELRO_BASE + RELRO_LEN) res) as [H2|H2]; [right; exact H2|].
    exfalso. apply (Hnimg (Z.max res RELRO_BASE - res)); [lia|].
    replace (res + (Z.max res RELRO_BASE - res)) with (Z.max res RELRO_BASE) by lia.
    apply (proj1 (RELRO (Z.max res RELRO_BASE) ltac:(unfold RELRO_BASE, RELRO_LEN in *; lia))). }
  assert (Haddr : h_addr_ok res) by (unfold h_addr_ok; lia).
  destruct (receive_m timg_plain Bw res bytes by_poll pf) as [[B' []]|] eqn:HRM;
    [| exfalso; exact (Hmod res Haddr HRM)].
  (* the n bytes at p after malloc *)
  assert (HPS : bytes = [] \/
     (bytes_at rsegs (normalize rsegs mem2) p bytes /\
      (p + Z.of_nat (length bytes) <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= p) /\
      (p + Z.of_nat (length bytes) <= bv_unsigned sp1 - 3840 \/ bv_unsigned sp1 + 48 <= p) /\
      (p + Z.of_nat (length bytes) <= res \/ res + Z.max 1 (Z.of_nat (length bytes)) <= p))).
  { destruct Hsrc as [H0 | (Hpw & [(q & k & Hqk & Hq1 & Hq2) | (Hq1 & Hq2)])].
    - left. destruct bytes; [reflexivity | unfold n in H0; cbn in H0; lia].
    - right. assert (Hin : In (ptr_addr L q, k) (blocks L A)) by (apply blocks_In; exists q; split; [reflexivity | exact Hqk]).
      destruct (mr_blocks_range B _ (aa_laws API) L A mem md q k HM Hqk) as [Hk1 Hk2].
      split; [|split; [exact Hpw|split]].
      + apply bytes_at_normalize; [exact Hro2|]. apply (r_blk_bytes B); [exact SEGS | lia | lia |].
        intros i Hi. rewrite <- (Hblk i Hi). replace (p + i) with (ptr_addr L q + (p - ptr_addr L q + i)) by lia.
        apply (Hbyt2 _ k); [exact Hin | lia].
      + left. rewrite Usp1. lia.
      + destruct (MINE _ _ Hin); lia.
    - right. split; [|split; [exact Hpw|split]].
      + apply bytes_at_normalize; [exact Hro2|]. apply (r_blk_bytes B); [exact SEGS | lia | lia |].
        intros i Hi. rewrite <- (Hblk i Hi).
        destruct (Hhigh2 (p + i) ltac:(lia) ltac:(rewrite <- Esp in *; lia) ltac:(lia) ltac:(lia)) as [E1 _].
        exact E1.
      + right. rewrite Usp1. rewrite <- Esp. lia.
      + right. lia. }
  assert (INV : r_inv sp1 (spZ regs - 8240) res bytes (normalize rsegs mem2)).
  { unfold r_inv. fold n. rewrite Usp1. rewrite <- Esp.
    split; [lia|]. split; [lia|]. split; [replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia;
      rewrite Z.mod_add by lia; exact Hal|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold nb in *; lia|].
    split; [exact Hfw|]. split; [exact Hfr|]. apply sr_relro_norm; [exact Hro2 | exact RR2]. }
  (* ---- body: 0x14b34-0x14cc8, on the normalized memory *)
  eapply (g_run B API) with (stk := receive_FRAME) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md).
  all: try eassumption.
  all: try (unfold receive_FRAME, ALLOC_STACK; lia).
  { unfold Regs6ss.mkR_of. rewrite E22, E23, E24, E28, E29, E210, E218, E219, E220, E221, E222, E223, E224, E225,
      E226, E227.
    eapply (r_body MSET MCPY POLL MRX RXC SET) with (junk := junk);
      [ exact INV | exact Hbp | exact Hpf | exact RW3 | exact ST2 | apply mem_inv_normalize
      | exact (sr_wmem_norm mem2 Bw Hro2 WM2) | exact GFw | exact HPS | exact HJ | exact HRM ]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WMo & _).
    do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WMo|].
    intros x Hx' NO. apply r_out3 in NO. rewrite Usp1, <- Esp in NO.
    destruct NO as [N|[N|N]].
    - left. unfold receive_FRAME, ALLOC_STACK. lia.
    - right. left. exact N.
    - right. right. exists res, nb. split; [|exact N].
      unfold sr_mine. split; [exact Hres_in|]. split; [lia | exact MINE]. }
  intros R F pc' fc mb HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & HE & MU3 & WMo3
    & MI3 & WM3 & GF3 & RR3).
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  assert (G31 : YK11.getr regs3 1 = reg_get regs 1) by (rewrite (sr_getr_eqv _ _ _ Hx3); reflexivity).
  assert (G32 : YK11.getr regs3 2 = Z_to_bv 64 (bv_unsigned sp1 + 48)) by (rewrite (sr_getr_eqv _ _ _ Hx3); reflexivity).
  assert (Hsp3 : spZ regs3 = spZ regs).
  { unfold spZ at 1. rewrite G32, Usp1, <- Esp. replace (spZ regs - 48 + 48) with (spZ regs) by lia.
    apply unsigned_lit. lia. }
  pose proof (sr_wmem_back m3 mb B' Hrel3 WM3) as WM3'.
  pose proof (sr_relro_back m3 mb Hrel3 RR3) as RR3'.
  (* ---- free (the frame), the tail call: it returns to receive's caller *)
  rewrite <- SEGS. rewrite <- HFRE.
  eapply (g_free B API) with (stk := receive_FRAME) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (x := res) (n := nb) (bres := sb_malloc b nb).
  all: try eassumption.
  all: try (rewrite ?Hsp3; unfold receive_FRAME, ALLOC_STACK; lia).
  all: try (rewrite G31; exact Hra).
  all: try (rewrite Hsp3; exact Hal).
  all: try (rewrite (sr_getr_eqv _ _ _ Hx3); exact Htp).
  all: try (rewrite (sr_getr_eqv _ _ _ Hx3); reflexivity).
  intros L2 A2 regs4 mem4 md4 FR4 Hrp4 (c1 & c2 & Ec1 & Ec2) Hres4 Habove4 Hkept4 Hsk4.
  apply SR_ret.
  pose proof FR4 as (HM4 & HW4 & HB4 & HID4 & Hmd4 & Hhigh4 & Himg4 & Hub4 & Hbyt4 & Hstw4 & Herr4 & Hgd4 & Hro4
    & Hle4 & Hlen4).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM4) as (Hh4 & Hl4 & _).
  unfold receive_ret. exists res, B'.
  split; [exact Haddr|]. split; [lia|]. split; [exact Hnimg|]. split; [exact HRM|].
  unfold h_post. exists (mkFP (@fp_regs fx) (@fp_csr fx)), L2, A2, regs4, mem4, md4.
  split; [rewrite G31, SEGS; reflexivity|].
  split; [exact Hfrm|].
  assert (RP : regs_preserved regs regs4).
  { intros r Hr. rewrite (Hrp4 r Hr), (sr_getr_eqv _ _ _ Hx3). unfold callee_saved in Hr.
    destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [| reflexivity | reflexivity | reflexivity | reflexivity |].
    - transitivity (Z_to_bv 64 (bv_unsigned sp1 + 48)); [reflexivity|].
      rewrite Usp1. replace (bv_unsigned (reg_get regs 2) - 48 + 48) with (bv_unsigned (reg_get regs 2)) by lia.
      apply Z_to_bv_bv_unsigned.
    - assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
        as Hc by lia.
      destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
  split.
  { eapply (sr_post B API);
      first [ exact FR4 | exact RP | (intros a Ha; left; exact Ha) | (intros a Ha; right; right; exact Ha)
            | eassumption ]. }
  split; [exact HID4|]. split; [exact Hh4|]. split; [exact Hl4|].
  split.
  { rewrite Ec2, Eb2. rewrite Eb1 in Ec1.
    assert (N1 : ~ In (res, nb) (b1 ++ b2)) by (apply (sr_nonempty_not_twice b1 b2 res nb PW); lia).
    assert (PW' : pairwise ranges_disjoint (c1 ++ (res, nb) :: c2)) by (rewrite <- Ec1; exact PW).
    assert (N2 : ~ In (res, nb) (c1 ++ c2)) by (apply (sr_nonempty_not_twice c1 c2 res nb PW'); lia).
    destruct (sr_app_mid_inv (res, nb) b1 b2 c1 c2 ltac:(intros Hi; apply N1; apply in_or_app; left; exact Hi)
      ltac:(intros Hi; apply N2; apply in_or_app; left; exact Hi) Ec1) as [-> ->].
    reflexivity. }
  split; [intros q k Hqk; exact (proj1 (Hub4 q k Hqk))|].
  split; [exact Hlen4|].
  split; [rewrite sb_free_malloc in Hres4; exact Hres4|].
  split; [rewrite SEGS; exact Hro4|].
  split; [intros i Hi; exact (Hgd4 i Hi)|].
  split.
  { apply (sr_rw_cells_frame m3 mem4 _ _ WM3'). intros a Ha. cbn [cells_size csize] in Ha.
    rewrite Nat.add_0_r, Z2Nat.id in Ha by (unfold W_LEN; lia).
    destruct (Hsk4 a (or_introl Ha)) as [E1 E2]. rewrite SEGS in E1, E2. split; [exact E1 | tauto]. }
  split; [exact GF3|].
  apply (r_relro_kept m3 mem4 RR3'). intros a Ha. destruct (Hsk4 a (or_intror Ha)) as [E1 _].
  rewrite SEGS in E1. exact E1.
Qed.

End Top.

Theorem receive_holds : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B),
  (forall fx', @malloc_contract fx' rc B API) -> (forall fx', @free_contract fx' rc B API) ->
  memset_contract -> memcpy_contract -> diginet_session_poll_contract -> m_rx_contract ->
  diginet_session_rx_contract -> settle_contract -> @receive_contract fx rc B API.
Proof.
  intros fx rc B API MALLOC FREE MSET MCPY POLL MRX RXC SET.
  exact (@receive_holds_of fx rc B API MALLOC FREE MSET MCPY POLL MRX RXC SET).
Qed.
