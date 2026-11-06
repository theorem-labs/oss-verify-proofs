(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_entry.v, with its module paths, addresses and numbers changed; 1150 of its 1185 lines of code are new or changed and 49 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Prog/T/receive.v, with its module paths, module names, addresses and numbers changed; 1321 of its 1481 lines of code are new or changed and 1025 lines of the source are left out. *)
(* The ubsan-image walk of receive (fuzz/fuzz_transport.c:995-1025 of the harness fix, c47f6290) at 0x14d1c,
   368 bytes, against U/Prog/T/receive_c.v's receive_contract. An SR walk in five parts (the donor's flow,
   libdiginet/fuzz_decode lib/Prog/LLVMFuzzerTestOneInput.v):
     entry    0x14d1c-0x14d50: the prologue to malloc (r_entry, evt);
     malloc   the SR call (TSRGlue.g_malloc), fa = the heap frame;
     body     0x14d54-0x14e60: the frame copy, op_begin, the poll or m_rx + diginet_session_rx branch, settle, to the
              call of free (r_body, evt; the abort at 0x14e84 is unreachable: fa <> 0);
     free     the SR call (TSRGlue.g_free), which returns to 0x14e64;
     epilogue 0x14e64-0x14e80: ra and s0-s4 back, sp + 128, ret (an evt run on the memory as it is, r_run).
   The post is built by TSRGlue.sr_post. receive_holds is the SR form; the callee contracts are its premises. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Contract Img0 SlotAgree AgreeLift.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TOps TRxFacts TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC
  receive_c TSRGlue spec_read_frame_c diginet_session_poll_c m_rx_c diginet_session_rx_c settle_c.
Import ListNotations.
Open Scope Z_scope.

Definition R_MALLOC_RET : Z := 0x14d54.
Definition R_FREE_RET : Z := 0x14e64.

(* The deepest callee window below receive's sp: diginet_session_poll's 3824 (diginet_session_rx 2256, m_rx 208,
   settle 96, spec_read_frame 32, memcpy / memset 0). *)
Definition R_K : Z := 3824.

(* ---------------------------------------------------------------- bit-vector facts *)

Lemma r_eqb : forall v k, 0 <= v < 2^64 -> 0 <= k < 2^64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 k) = (v =? k).
Proof. intros v k Hv Hk. unfold bv_eqb. rewrite (unsigned_lit v), (unsigned_lit k) by lia. reflexivity. Qed.

Lemma r_ltu : forall a c, 0 <= a < 2^64 -> 0 <= c < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 c) = (a <? c).
Proof. intros a c Ha Hc. unfold bv_ltu. rewrite (unsigned_lit a), (unsigned_lit c) by lia. reflexivity. Qed.

Lemma r_eqbs : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 63) with 9223372036854775808 in *.
  destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. revert E. Z.div_mod_to_equations. lia.
Qed.

Lemma r_swrap32_eq : forall v, bv_swrap 32 v = (v + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31.
Proof.
  intros v. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). reflexivity.
Qed.

Lemma r_put4_swrap : forall v, put 4 (bv_swrap 32 v) = put 4 v.
Proof.
  intros v. unfold put.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 v) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 v 32) by lia. f_equal.
  rewrite r_swrap32_eq. change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

(* ---------------------------------------------------------------- memory facts *)

(* relro_img across a footprint that misses .data.rel.ro *)
Lemma r_relro : forall W m0 m, relro_img m0 -> munch W m0 m ->
  (forall i, 0 <= i < RELRO_LEN -> outside W (RELRO_BASE + i)) -> relro_img m.
Proof.
  intros W m0 m H MU HO i Hi. rewrite <- (H i Hi). unfold mrd.
  rewrite (MU (wa (RELRO_BASE + i))); [reflexivity|].
  rewrite wa_unsigned by (unfold RELRO_BASE, RELRO_LEN in *; lia). exact (HO i Hi).
Qed.

(* bytes off the image and bytes in it do not overlap *)
Lemma r_off_img : forall (Bm : malloc_syms) p n q k, 0 < n -> 0 < k ->
  (forall i, 0 <= i < n -> ~ in_img Bm (p + i)) -> (forall j, 0 <= j < k -> in_img Bm (q + j)) ->
  p + n <= q \/ q + k <= p.
Proof.
  intros Bm p n q k Hn Hk Hp Hq.
  destruct (Z_le_gt_dec (p + n) q) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (q + k) p) as [H'|H']; [right; exact H'|].
  exfalso. destruct (Z_le_gt_dec p q) as [L|L].
  - apply (Hp (q - p) ltac:(lia)). replace (p + (q - p)) with (q + 0) by lia. apply Hq. lia.
  - apply (Hp 0 ltac:(lia)). replace (p + 0) with (q + (p - q)) by lia. apply Hq. lia.
Qed.

(* the world fact of the current memory, by its base (never by assumption: the conversion of another cell's size
   against Z.to_nat W_LEN is unary) *)
Ltac r_wm :=
  lazymatch goal with |- rw_cells rsegs ?mm W_BASE_UBSAN _ =>
    lazymatch goal with H : rw_cells rsegs mm W_BASE_UBSAN _ |- _ => exact H end end.

(* ---------------------------------------------------------------- entry: 0x14d1c-0x14d50 *)

(* a0 = a1 + (a1 == 0) for a1 = n, 0 <= n < 2^63 *)
Lemma r_a0 : forall n, 0 <= n < 2 ^ 63 ->
  Z_to_bv 64 (n + bv_unsigned (v_sltiu (Z_to_bv 64 n) 1)) = Z_to_bv 64 (Z.max 1 n).
Proof.
  intros n Hn. unfold v_sltiu. rewrite (unsigned_lit n) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec n 1) as [H|H]; rewrite unsigned_lit by lia; f_equal; lia.
Qed.

(* The state at malloc's entry: sp is receive's sp - 128, the six saved registers in [sp + 80, sp + 128), s1..s4 the
   arguments (n, poll_flags, by_poll, p), a0 = n ? n : 1; the world as it was. *)
Definition q_mal (F : bvmap 5 word) (fc : bv 32) (gp tp s0 a1 a2 a3 s5 s6 s7 s8 s9 s10 s11 : word)
    (m0 : word -> option byte) (Sp lo p n : Z) (sv : list cell) (Bw : list byte) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 x11 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 : word) m' j,
    ms = MS (mkR (Z_to_bv 64 R_MALLOC_RET) (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 a1 (Z_to_bv 64 (Z.max 1 n))
               x11 x12 x13 x14 x15 x16 x17 a3 a2 (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 H_MALLOC) fc None m' (seg_rom rsegs) /\
    munch [(Sp, Sp + 128)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp /\
    rw_cells rsegs m' Sp (CB 80 j :: sv) /\ wmem rsegs m' Bw.

Lemma r_entry :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p n : Z) (Bw : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> mem_inv rsegs m -> bv_unsigned sp < 2 ^ 63 ->
    a1 = Z_to_bv 64 n -> 0 <= n < 2 ^ 63 ->
    wmem rsegs m Bw -> W_BASE_UBSAN + W_LEN <= lo ->
    evt rsegs (q_mal F fc gp tp s0 a1 a2 a3 s5 s6 s7 s8 s9 s10 s11 m (bv_unsigned sp - 128) lo p n
                 [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
               s11 t3 t4 t5 t6)
          F (Z_to_bv 64 receive_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo p n Bw
    ST LO MI H63 -> Hn WMW HWL.
  unfold receive_ENTRY.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp - 128 + 128)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  rename m into m0.
  wk_facts.
  carve_frame 128%nat ST.
  (* 0x14d1c-0x14d34: addi sp, sp, -128; sd ra, s0, s1, s2, s3, s4 *)
  do 7 step.
  (* 0x14d38-0x14d4c: mv s2, a3; mv s3, a2; mv s1, a1; mv s4, a0; seqz a0, a1; add a0, a1, a0 *)
  do 6 step.
  (* 0x14d50: jal malloc *)
  step.
  try rewrite (r_a0 n Hn).
  apply evt_done. unfold q_mal, H_MALLOC, R_MALLOC_RET. do 16 eexists.
  split; [reflexivity|].
  split; [exact MU0|]. split; [exact WM0|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|]. r_wm.
Qed.

(* ---------------------------------------------------------------- body: 0x14d54-0x14e60 *)

(* The state at free's entry (the call at 0x14e60, ra = 0x14e64): receive's sp, gp, tp and s5-s11 as they were,
   a0 = the frame; the body wrote its window [sp - 3824, sp + 80), the world and the frame, and leaves the world
   receive_m gives. The saved registers are still at sp + 80. *)
Definition q_body (F : bvmap 5 word) (fc : bv 32) (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word)
    (m0 : word -> option byte) (fa n : Z) (sv : list cell) (B' : list byte) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 o0 o1 x11 x12 x13 x14 x15 x16 x17 o2 o3 o4 t3 t4 t5 t6 : word) m',
    ms = MS (mkR (Z_to_bv 64 R_FREE_RET) sp gp tp t0 t1 t2 o0 o1 (Z_to_bv 64 fa) x11 x12 x13 x14 x15 x16 x17
                 o2 o3 o4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 H_FREE) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 3824, bv_unsigned sp + 80); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
           (fa, fa + Z.max 1 n)] m0 m' /\
    wmono rsegs m0 m' /\
    rw_cells rsegs m' (bv_unsigned sp + 80) sv /\ wmem rsegs m' B' /\ g_fail_next B' <= 1.

(* ---- receive_m (TModel/TOps.v:93-119) cut at the points the walk reaches ---- *)

(* :1001 op_begin's world *)
Definition rx_ob (B : list byte) : list byte :=
  let B1 := upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW)) in
  let B2 := upd B1 OFF_GOT (repeat (b8 0) (Z.to_nat SZ_GOT)) in
  let B3 := set_OW_desk_off B2 (-1) in
  set_M_fail B3 (g_fail_next B3).

(* :1002-1003, :1007-1008 f.send after spec_read_frame of bs (0 unless the parse succeeded) *)
Definition rx_send (bs : list byte) : Z := if fr_code bs =? 0 then fr_send bs else 0.

(* :1005, :1006 *)
Definition rx_got (n : Z) : Z := if SPEC_MAX_FRAME <? n then SPEC_MAX_FRAME else n.
Definition rx_fails (pf : Z) : Z := Z.land (Z.shiftr pf 1) 1.
Definition rx_times (pf : Z) : Z := if Z.land pf 1 =? 0 then 1 else 2.

(* :1003 *)
Definition rx_B2 (B : list byte) (bytes : list byte) : list byte := set_g_rx_send (rx_ob B) (rx_send bytes).

(* :1007-1015, the world diginet_session_poll is called on *)
Definition rx_B2c (B2 : list byte) (fa n pf : Z) (bytes : list byte) : list byte :=
  set_g_rx_fail
    (set_g_rx_times (set_g_rx_len (set_g_rx (set_g_rx_send B2 (rx_send (firstn (Z.to_nat (rx_got n)) bytes))) fa)
       (rx_got n)) (rx_times pf))
    (rx_fails pf).

Lemma rx_poll_eq : forall I B a bytes by_poll pf, a <> 0 -> by_poll <> 0 ->
  receive_m I B a bytes by_poll pf =
  match diginet_session_poll_m I (Some (TFrame a bytes))
          (rx_B2c (rx_B2 B bytes) a (Z.of_nat (length bytes)) pf bytes) 0 with
  | Some (B2d, _) =>
      match settle_m (set_g_rx_fail (set_g_rx B2d 0) 0) (if rx_fails pf =? 0 then 1 else 0) with
      | Some (B4, _) => Some (B4, tt)
      | None => None
      end
  | None => None
  end.
Proof.
  intros I B a bytes by_poll pf Ha Hb.
  unfold receive_m, fuzz_dup_m, fuzz_alloc_m, op_begin_m.
  rewrite (proj2 (Z.eqb_neq a 0) Ha), (proj2 (Z.eqb_neq by_poll 0) Hb). cbn [negb tf_addr].
  unfold rx_B2c, rx_B2, rx_ob, rx_send, rx_got, rx_times, rx_fails. cbv zeta.
  destruct (diginet_session_poll_m _ _ _ _) as [[B2d r]|]; reflexivity.
Qed.

Lemma rx_mrx_eq : forall I B a bytes pf, a <> 0 ->
  receive_m I B a bytes 0 pf =
  match m_rx_m I (Some (TFrame a bytes)) (rx_B2 B bytes) (Z.of_nat (length bytes)) with
  | Some (Bx, t) =>
      match diginet_session_rx_m I (Some (TFrame a bytes)) Bx bytes (g_now Bx) with
      | Some (By, _) =>
          match settle_m By t with
          | Some (B4, _) => Some (B4, tt)
          | None => None
          end
      | None => None
      end
  | None => None
  end.
Proof.
  intros I B a bytes pf Ha.
  unfold receive_m, fuzz_dup_m, fuzz_alloc_m, op_begin_m.
  rewrite (proj2 (Z.eqb_neq a 0) Ha). cbn [negb Z.eqb].
  unfold rx_B2, rx_ob, rx_send. cbv zeta.
  destruct (m_rx_m _ _ _ _) as [[Bx t]|]; [|reflexivity].
  destruct (diginet_session_rx_m _ _ _ _ _) as [[By r]|]; reflexivity.
Qed.

(* the struct spec_frame at receive's sp, cut into the fields (TContract.sf_bytes; m_rx.v's sf_cells) *)
Definition r_sf_cells (fa : Z) (f : spec_frame) : list cell :=
  [CB 8 (put 4 (sf_code f) ++ repeat (b8 0) 4);
   C8 (Z_to_bv 64 (sf_ptr fa f (sf_dst f)));
   C8 (Z_to_bv 64 (sf_ptr fa f (sf_src f)));
   CB 6 (put 2 (sf_ethertype f) ++ put 2 (sf_numbytes f) ++ put 2 (sf_sum f));
   C2 (Z_to_bv 64 (sf_retry f));
   C4 (Z_to_bv 64 (sf_send f));
   C4 (Z_to_bv 64 (sf_ack f));
   C1 (Z_to_bv 8 (sf_cmd f));
   CB 7 (put 1 (sf_ncmds f) ++ repeat (b8 0) 6);
   C8 (Z_to_bv 64 (sf_ptr fa f (sf_body f)));
   C8 (Z_to_bv 64 (sf_body_len f));
   CB 16 (put 8 (sf_pad_len f) ++ put 2 (sf_body_sum f) ++ repeat (b8 0) 6)].

Lemma r_sf_bytes : forall fa f, cells_bytes (r_sf_cells fa f) = sf_bytes fa f.
Proof.
  intros fa f. unfold r_sf_cells, sf_bytes. cbn [cells_bytes cbytes].
  rewrite !le8_put, !le4_put, le2_put.
  change [Z_to_bv 8 (sf_cmd f)] with (put 1 (sf_cmd f)).
  rewrite <- !app_assoc. rewrite app_nil_r. reflexivity.
Qed.

Lemma r_sf_cells_of : forall m fp fa f,
  rw_cells rsegs m fp [CB 80 (sf_bytes fa f)] -> rw_cells rsegs m fp (r_sf_cells fa f).
Proof.
  intros m fp fa f [[_ Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf r_sf_cells].
    rewrite !length_app, !length_put, !repeat_length. repeat split.
  - rewrite r_sf_bytes. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - change (cells_size (r_sf_cells fa f)) with 80%nat. exact Hw.
Qed.

(* f.send after spec_read_frame of the first len bytes of bs *)
Lemma r_srf_send0 : forall b len, sf_code (spec_read_frame b len) <> SPEC_OK -> sf_send (spec_read_frame b len) = 0.
Proof.
  intros b len. unfold spec_read_frame.
  destruct (len <? SPEC_BODY_AT); [reflexivity|].
  destruct (negb (spec_be16 b 12 =? SPEC_ETHERTYPE)); [reflexivity|].
  destruct ((spec_be16 b SPEC_AT_NUMBYTES <? SPEC_HDR) || (len - SPEC_ETH_HDR <? spec_be16 b SPEC_AT_NUMBYTES));
    [reflexivity|].
  cbn [sf_code]. intros H. exfalso. exact (H eq_refl).
Qed.

Lemma r_srf_send : forall (bs : list byte) k, (k <= length bs)%nat ->
  sf_send (spec_read_frame (zs bs) (Z.of_nat k)) = rx_send (firstn k bs).
Proof.
  intros bs k Hk.
  assert (HB : holds_body (zs bs) (firstn k bs)).
  { intros i Hi. rewrite length_firstn in Hi. unfold byte_at, at8, zs, bz. rewrite Nat2Z.id.
    rewrite nth_firstn. replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite <- (map_nth bv_unsigned bs (b8 0) i). reflexivity. }
  assert (Lk : length (firstn k bs) = k) by (rewrite length_firstn; lia).
  destruct (spec_read_frame_fr (zs bs) (firstn k bs) HB) as [C Fk]. rewrite Lk in C, Fk.
  unfold rx_send. destruct (Z.eqb_spec (fr_code (firstn k bs)) 0) as [E|E].
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (Fk E))))))).
  - rewrite (r_srf_send0 _ _ ltac:(rewrite C; exact E)). reflexivity.
Qed.

(* ---- the poll branch's register values (fuzz_transport.c:1006, :1011) ---- *)

Lemma r_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. apply (Z.land_ones x 1). lia. Qed.

Lemma r_fails : forall (pfr : word) pf, bv_unsigned pfr mod 2 ^ 32 = pf ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned pfr) 62))) 63 = rx_fails pf.
Proof.
  intros pfr pf Hpf. unfold rx_fails. rewrite r_land1, unsigned_lit_wrap.
  rewrite Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia. subst pf.
  pose proof (bv_unsigned_in_range 64 pfr) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  change (2 ^ 62) with 4611686018427387904. change (2 ^ 63) with 9223372036854775808.
  change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 32) with 4294967296. change (2 ^ 1) with 2.
  Z.div_mod_to_equations. lia.
Qed.

Lemma r_fails_01 : forall pf, rx_fails pf = 0 \/ rx_fails pf = 1.
Proof. intros pf. unfold rx_fails. rewrite r_land1. pose proof (Z.mod_pos_bound (Z.shiftr pf 1) 2). lia. Qed.

Lemma r_times : forall (pfr : word) pf, bv_unsigned pfr mod 2 ^ 32 = pf ->
  Z.land (bv_unsigned pfr) 1 + 1 = rx_times pf.
Proof.
  intros pfr pf Hpf. unfold rx_times. rewrite !r_land1. subst pf.
  assert (E : (bv_unsigned pfr mod 2 ^ 32) mod 2 = bv_unsigned pfr mod 2).
  { change (2 ^ 32) with 4294967296. Z.div_mod_to_equations. lia. }
  rewrite E. pose proof (Z.mod_pos_bound (bv_unsigned pfr) 2).
  destruct (Z.eqb_spec (bv_unsigned pfr mod 2) 0); lia.
Qed.

Lemma r_ticked : forall pf,
  Z.lxor (bv_unsigned (Z_to_bv 64 (rx_fails pf))) 1 = (if rx_fails pf =? 0 then 1 else 0).
Proof.
  intros pf. destruct (r_fails_01 pf) as [E|E]; rewrite E; reflexivity.
Qed.

Lemma r_sx32 : forall v, sx32 (Z_to_bv 64 v) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
  intros v. unfold sx32. f_equal. rewrite unsigned_lit_wrap, !r_swrap32_eq. f_equal.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

(* ---- the world's length across writes, and writes that commute or miss a read ---- *)

Lemma r_lu : forall (Bx v : list byte) k, length Bx = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> length (upd Bx k v) = Z.to_nat W_LEN.
Proof.
  intros Bx v k L Hk Hv. rewrite length_upd; [exact L | lia | rewrite L; unfold W_LEN in *; lia].
Qed.

Ltac r_wlen L :=
  first [ exact L | apply r_lu; [ r_wlen L | lia | rewrite ?length_put, ?repeat_length; unfold W_LEN; lia ] ].

Lemma r_comm : forall (bs v w : list byte) k k', length bs = Z.to_nat W_LEN -> 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat (length w) <= k \/ k + Z.of_nat (length v) <= k') ->
  k + Z.of_nat (length v) <= W_LEN -> k' + Z.of_nat (length w) <= W_LEN ->
  upd (upd bs k v) k' w = upd (upd bs k' w) k v.
Proof. intros bs v w k k' L H1 H2 H3 H4 H5. apply upd_upd_comm; try lia; rewrite L; unfold W_LEN in *; lia. Qed.

Lemma r_uo : forall (Bx v : list byte) (k k' : Z) (nn : nat),
  length Bx = Z.to_nat W_LEN -> 0 <= k -> 0 <= k' -> k + Z.of_nat (length v) <= W_LEN ->
  (k' + Z.of_nat nn <= k \/ k + Z.of_nat (length v) <= k') ->
  u_at (upd Bx k v) k' nn = u_at Bx k' nn.
Proof.
  intros Bx v k k' nn L Hk Hk' Hv Hd. apply u_at_upd_out; [lia | lia | lia |].
  rewrite L. unfold W_LEN in *. lia.
Qed.

Ltac r_side L := first [ r_wlen L | (rewrite ?length_put, ?repeat_length; unfold W_LEN; lia) | lia ].
Ltac r_cm L k k' := rewrite (r_comm _ _ _ k k') by r_side L.
Ltac r_push L := repeat (rewrite r_uo by r_side L).

(* the poll branch's five g_rx stores (machine order) are rx_B2c's setters (model order) *)
Lemma r_B2c_eq : forall B2 fa n pf bytes, length B2 = Z.to_nat W_LEN ->
  upd (upd (upd (upd (upd B2 64988 (put 4 (rx_send (firstn (Z.to_nat (rx_got n)) bytes))))
     64992 (put 4 (rx_fails pf))) 64996 (put 4 (rx_times pf))) 65008 (put 8 fa)) 65016 (put 8 (rx_got n))
  = rx_B2c B2 fa n pf bytes.
Proof.
  intros B2 fa n pf bytes L.
  unfold rx_B2c, set_g_rx_fail, set_g_rx_times, set_g_rx_len, set_g_rx, set_g_rx_send,
    OFF_g_rx_fail, OFF_g_rx_times, OFF_g_rx_len, OFF_g_rx, OFF_g_rx_send.
  r_cm L 64992 64996. r_cm L 64992 65008. r_cm L 64992 65016. r_cm L 64996 65008. r_cm L 64996 65016.
  reflexivity.
Qed.

Lemma r_B3_eq : forall B2d, length B2d = Z.to_nat W_LEN ->
  upd (upd B2d 64992 (put 4 0)) 65008 (put 8 0) = set_g_rx_fail (set_g_rx B2d 0) 0.
Proof.
  intros B2d L. unfold set_g_rx_fail, set_g_rx, OFF_g_rx_fail, OFF_g_rx. r_cm L 64992 65008. reflexivity.
Qed.

Lemma r_B2c_gf : forall B2 fa n pf bytes, length B2 = Z.to_nat W_LEN ->
  g_fail_next (rx_B2c B2 fa n pf bytes) = g_fail_next B2.
Proof.
  intros B2 fa n pf bytes L. rewrite <- r_B2c_eq by exact L. unfold g_fail_next, OFF_g_fail_next. r_push L.
  reflexivity.
Qed.

Lemma r_B3_gf : forall B2d, length B2d = Z.to_nat W_LEN ->
  g_fail_next (set_g_rx_fail (set_g_rx B2d 0) 0) = g_fail_next B2d.
Proof.
  intros B2d L. rewrite <- r_B3_eq by exact L. unfold g_fail_next, OFF_g_fail_next. r_push L. reflexivity.
Qed.

Section Body.
Hypothesis MSET : memset_contract.
Hypothesis MCPY : memcpy_contract.
Hypothesis SRF : spec_read_frame_contract.
Hypothesis POLL : diginet_session_poll_contract.
Hypothesis MRX : m_rx_contract.
Hypothesis RXC : diginet_session_rx_contract.
Hypothesis SET : settle_contract.

(* 0x14e54-0x14e60: settle (ticked), then free (frame). *)
Lemma r_tail :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (v4 v3 v2 v1 v0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo fa n ticked : Z) (B3 B' : list byte),
    -2 ^ 31 <= ticked < 2 ^ 31 -> settle_m B3 ticked = Some (B', tt) -> g_fail_next B3 <= 1 ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + 3824 <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp 3824 -> mem_inv rsegs m -> wmem rsegs m B3 ->
    rw_cells rsegs m (bv_unsigned sp + 80) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    munch [(bv_unsigned sp - 3824, bv_unsigned sp + 80); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
           (fa, fa + Z.max 1 n)] m0 m ->
    wmono rsegs m0 m ->
    evt rsegs (q_body F fc sp gp tp s5 s6 s7 s8 s9 s10 s11 m0 fa n [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] B')
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ticked) s3 s4
               s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14e54) fc None m (seg_rom rsegs)).
Proof.
  pose proof SET as SET0. unfold settle_contract, settle_ENTRY, settle_FRAME in SET0.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    v4 v3 v2 v1 v0 vra F fc m0 m lo fa n ticked B3 B' HT MOD GF S16 ST LO WOS MI WM SV MU WMo.
  unfold w_off_stack in WOS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  wk_facts.
  (* 0x14e54: mv a0, s2; 0x14e58: jal settle *)
  step. step.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply SET0 with (lo := lo) (B := B3) (B' := B') (ticked := ticked);
        [ reflexivity | lia | exact WM | exact MOD | exact S16 | exact ST | lia | unfold w_off_stack; lia
        | exact MI ]
      | wk_post_call sg mm ]
  end.
  lazymatch goal with H : B' = B3 |- _ => subst B' end.
  (* 0x14e5c: mv a0, s0; 0x14e60: jal free *)
  step. step.
  apply evt_done. unfold q_body, H_FREE, R_FREE_RET. do 20 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WMo|]. split; [exact SV|].
  split; [|exact GF].
  lazymatch goal with H : rw_cells rsegs ?mm W_BASE_UBSAN _ |- rw_cells rsegs ?mm W_BASE_UBSAN _ => exact H end.
Qed.

(* .data.rel.ro lies outside the body's footprint *)
Lemma r_relro_out : forall (sp : word) fa n1, 0 <= n1 ->
  W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 3824 -> (fa + n1 <= RELRO_BASE \/ RELRO_BASE + RELRO_LEN <= fa) ->
  forall i, 0 <= i < RELRO_LEN ->
    outside [(bv_unsigned sp - 3824, bv_unsigned sp + 80); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
             (fa, fa + n1)] (RELRO_BASE + i).
Proof.
  intros sp fa n1 Hn Hsp Hfa i Hi. unfold RELRO_BASE, RELRO_LEN, W_BASE_UBSAN, W_LEN in *.
  cbn [outside]. lia.
Qed.

(* 0x14e2c-0x14e50: m_rx (frame, n), then diginet_session_rx (&g_s, frame, n, g_now), on to 0x14e54. *)
Lemma r_mrx :
  forall (ra sp gp tp t0 t1 t2 s2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (v4 v3 v2 v1 v0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo fa t r : Z)
         (bytes : list byte) (B2 Bx By B' : list byte),
    m_rx_m timg_ubsan (Some (TFrame fa bytes)) B2 (Z.of_nat (length bytes)) = Some (Bx, t) ->
    diginet_session_rx_m timg_ubsan (Some (TFrame fa bytes)) Bx bytes (g_now Bx) = Some (By, r) ->
    settle_m By t = Some (B', tt) ->
    g_fail_next B2 <= 1 ->
    0 < fa -> fa + Z.max 1 (Z.of_nat (length bytes)) <= lo -> off_world fa (Z.max 1 (Z.of_nat (length bytes))) ->
    bytes_at rsegs m fa bytes ->
    relro_img m0 -> (fa + Z.max 1 (Z.of_nat (length bytes)) <= RELRO_BASE \/ RELRO_BASE + RELRO_LEN <= fa) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + 3824 <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp 3824 -> mem_inv rsegs m -> wmem rsegs m B2 ->
    rw_cells rsegs m (bv_unsigned sp + 80) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    munch [(bv_unsigned sp - 3824, bv_unsigned sp + 80); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
           (fa, fa + Z.max 1 (Z.of_nat (length bytes)))] m0 m ->
    wmono rsegs m0 m ->
    evt rsegs (q_body F fc sp gp tp s5 s6 s7 s8 s9 s10 s11 m0 fa (Z.of_nat (length bytes))
                 [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] B')
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length bytes))) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 274632) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14e2c) fc None m (seg_rom rsegs)).
Proof.
  pose proof MRX as MRX0. unfold m_rx_contract, m_rx_ENTRY, m_rx_FRAME in MRX0.
  pose proof RXC as RXC0. unfold diginet_session_rx_contract, diginet_session_rx_ENTRY,
    diginet_session_rx_FRAME in RXC0.
  intros ra sp gp tp t0 t1 t2 s2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    v4 v3 v2 v1 v0 vra F fc m0 m lo fa t r bytes B2 Bx By B' MOD1 MOD2 MOD3 GF2 Hfa0 Hfalo OWfa FB RI0 RLfa
    S16 ST LO WOS MI WM SV MU WMo.
  set (n := Z.of_nat (length bytes)) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  unfold w_off_stack in WOS. unfold off_world in OWfa.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (wm_len rsegs W_BASE_UBSAN m B2 WM) as LB2.
  pose proof (m_rx_m_01 _ _ _ _ _ _ MOD1) as T01.
  pose proof (m_rx_gk B2 LB2 _ _ _ _ _ _ (gkeep_refl B2) MOD1) as [_ GFx].
  wk_facts.
  (* 0x14e2c: mv a0, s0; mv a1, s1; 0x14e34: jal m_rx *)
  step. step. step.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply MRX0 with (lo := lo) (B := B2) (B' := Bx) (fr := TFrame fa bytes) (n := n) (r := t);
        [ reflexivity | reflexivity
        | unfold tframe_at, off_world, off_window; cbn [tf_addr tf_bytes]; fold n;
          split; [exact Hfa0|]; split; [exact FB|]; split; lia
        | cbn [tf_addr]; lia
        | exact S16 | exact ST | lia | unfold w_off_stack; lia | exact MI | exact WM | exact MOD1 ]
      | wk_post_call sg mm ]
  end.
  (* 0x14e38: ld a3, 32(s4) (g_now); mv s2, a0; auipc / addi a0 (&g_s); mv a1, s0; mv a2, s1;
     0x14e50: jal diginet_session_rx *)
  step.
  lazymatch goal with |- context [u_at Bx ?k 8] => change (u_at Bx k 8) with (g_now Bx) end.
  pose proof (u_at_range Bx OFF_g_now 8) as RNOW. change (u_at Bx OFF_g_now 8) with (g_now Bx) in RNOW.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RNOW.
  step. step. step. step. step. step.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply RXC0 with (lo := lo) (bufp := fa) (now := g_now Bx) (r := r) (b := bytes) (B := Bx) (B' := By)
          (TF := Some (TFrame fa bytes));
        [ reflexivity | reflexivity | reflexivity | reflexivity | exact RNOW | exact FB
        | unfold arg_blk, off_world, off_window; fold n; split; [exact Hfa0|]; split; [lia|]; split; lia
        | r_wm | lia | exact MOD2
        | unfold tframe_at, off_world, off_window; cbn [tf_addr tf_bytes]; fold n;
          split; [exact Hfa0|]; split; [exact FB|]; split; lia
        | apply (r_relro _ m0 mm RI0 MU); apply r_relro_out; lia
        | exact S16 | assumption | lia | unfold w_off_stack; lia | assumption ]
      | wk_post_call sg mm ]
  end.
  eapply r_tail with (lo := lo) (B3 := By);
    [ lia | exact MOD3 | assumption | exact S16 | assumption | exact LO | unfold w_off_stack; lia
    | assumption | r_wm | exact SV | exact MU | exact WMo ].
Qed.

(* 0x14dd4-0x14e28: spec_read_frame (frame, got, &f), the g_rx fields, diginet_session_poll (&g_s, 0), g_rx_fail = 0
   and g_rx = NULL, on to 0x14e54. *)
Lemma r_poll2 :
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 pfr s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (v4 v3 v2 v1 v0 vra : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (lo fa pf got r : Z) (bytes j80 : list byte) (B2 B2d B' : list byte),
    got = rx_got (Z.of_nat (length bytes)) ->
    bv_unsigned pfr mod 2 ^ 32 = pf -> 0 <= pf < 2 ^ 32 ->
    diginet_session_poll_m timg_ubsan (Some (TFrame fa bytes)) (rx_B2c B2 fa (Z.of_nat (length bytes)) pf bytes) 0
      = Some (B2d, r) ->
    settle_m (set_g_rx_fail (set_g_rx B2d 0) 0) (if rx_fails pf =? 0 then 1 else 0) = Some (B', tt) ->
    g_fail_next B2 <= 1 ->
    0 < fa -> fa + Z.max 1 (Z.of_nat (length bytes)) <= lo -> off_world fa (Z.max 1 (Z.of_nat (length bytes))) ->
    bytes_at rsegs m fa bytes ->
    relro_img m0 -> (fa + Z.max 1 (Z.of_nat (length bytes)) <= RELRO_BASE \/ RELRO_BASE + RELRO_LEN <= fa) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + 3824 <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp 3824 -> mem_inv rsegs m -> wmem rsegs m B2 ->
    rw_cells rsegs m (bv_unsigned sp) [CB 80 j80] ->
    rw_cells rsegs m (bv_unsigned sp + 80) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    munch [(bv_unsigned sp - 3824, bv_unsigned sp + 80); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
           (fa, fa + Z.max 1 (Z.of_nat (length bytes)))] m0 m ->
    wmono rsegs m0 m ->
    evt rsegs (q_body F fc sp gp tp s5 s6 s7 s8 s9 s10 s11 m0 fa (Z.of_nat (length bytes))
                 [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] B')
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 got) a0 a1 a2 a3 a4 a5 a6 a7
               pfr s3 (Z_to_bv 64 274632) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14dd4) fc None m (seg_rom rsegs)).
Proof.
  pose proof SRF as SRF0. unfold spec_read_frame_contract, spec_read_frame_ENTRY, spec_read_frame_FRAME in SRF0.
  pose proof POLL as POLL0. unfold diginet_session_poll_contract, diginet_session_poll_ENTRY,
    diginet_session_poll_FRAME in POLL0.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 pfr s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    v4 v3 v2 v1 v0 vra F fc m0 m lo fa pf got r bytes j80 B2 B2d B' Hgot Hpf Rpf MODP MODS GF2 Hfa0 Hfalo OWfa FB
    RI0 RLfa S16 ST LO WOS MI WM SF SV MU WMo.
  set (n := Z.of_nat (length bytes)) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  assert (Rgot : 0 <= got <= n /\ got <= 1514) by (rewrite Hgot; unfold rx_got, SPEC_MAX_FRAME;
    destruct (Z.ltb_spec 1514 n); lia).
  unfold w_off_stack in WOS. unfold off_world in OWfa.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (wm_len rsegs W_BASE_UBSAN m B2 WM) as LB2.
  wk_facts.
  (* 0x14dd4: mv a2, sp; mv a0, s0; mv a1, s1; 0x14de0: jal spec_read_frame *)
  step. step. step. step.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply SRF0 with (p := fa) (len := got) (fp := bv_unsigned sp) (lo := lo) (B := B2) (fr := bytes)
          (junk := j80);
        [ reflexivity | reflexivity | symmetry; apply Z_to_bv_bv_unsigned | exact Hfa0 | exact FB | fold n; lia
        | lia | Z.div_mod_to_equations; lia | lia | exact SF | fold n; lia
        | unfold off_window; fold n; lia
        | exact S16 | exact ST | lia | unfold w_off_stack; lia | exact MI | exact WM ]
      | wk_post_call sg mm ]
  end.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp) [CB 80 (sf_bytes _ _)] |- _ =>
    apply r_sf_cells_of in H; rename H into SFc end.
  assert (ES : sf_send (spec_read_frame (zs bytes) got) = rx_send (firstn (Z.to_nat got) bytes))
    by (rewrite <- (Z2Nat.id got) at 1 by lia; apply r_srf_send; lia).
  cbv beta delta [r_sf_cells] in SFc.
  rewrite ES in SFc.
  (* 0x14de4-0x14df8: slli a0, s2, 62; andi a1, s2, 1; lw a2, 32(sp); srli a0, a0, 63; addi a1, a1, 1;
     xori s2, a0, 1 *)
  step. step. step. step. step. step.
  rewrite (r_fails pfr pf Hpf). rewrite r_ticked. rewrite (r_times pfr pf Hpf). rewrite r_sx32.
  (* 0x14dfc-0x14e0c: sw a2, 20(s4) (g_rx_send); sw a0, 24(s4) (g_rx_fail); sw a1, 28(s4) (g_rx_times);
     sd s0, 40(s4) (g_rx); sd s1, 48(s4) (g_rx_len) *)
  step. step. step. step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with H : rw_cells rsegs mm W_BASE_UBSAN _ |- _ =>
        rewrite r_put4_swrap in H; rewrite Hgot in H; rewrite (r_B2c_eq B2 fa n pf bytes LB2) in H end
  end.
  (* 0x14e10-0x14e1c: auipc / addi a0 (&g_s); li a1, 0; jal diginet_session_poll *)
  step. step. step. step.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply POLL0 with (lo := lo) (w := 0) (r := r) (B := rx_B2c B2 fa n pf bytes) (B' := B2d)
          (TF := Some (TFrame fa bytes));
        [ reflexivity | reflexivity | lia | r_wm | rewrite r_B2c_gf by exact LB2; exact GF2 | exact MODP
        | unfold tframe_at, off_world, off_window; cbn [tf_addr tf_bytes]; fold n;
          split; [exact Hfa0|]; split; [assumption|]; split; lia
        | unfold tframe_ok; cbn [tf_addr tf_bytes]; fold n; lia
        | apply (r_relro _ m0 mm RI0 MU); apply r_relro_out; lia
        | exact S16 | assumption | lia | unfold w_off_stack; lia | assumption ]
      | wk_post_call sg mm ]
  end.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with H : rw_cells rsegs mm W_BASE_UBSAN _ |- _ =>
        pose proof (wm_len rsegs W_BASE_UBSAN mm _ H) as LB2d end
  end.
  (* 0x14e20-0x14e28: sw zero, 24(s4) (g_rx_fail = 0); sd zero, 40(s4) (g_rx = NULL); j 0x14e54 *)
  step. step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with H : rw_cells rsegs mm W_BASE_UBSAN _ |- _ => rewrite (r_B3_eq B2d LB2d) in H end
  end.
  eapply r_tail with (lo := lo) (B3 := set_g_rx_fail (set_g_rx B2d 0) 0);
    [ destruct (r_fails_01 pf) as [E|E]; rewrite E; cbn; lia | exact MODS
    | rewrite (r_B3_gf B2d LB2d); assumption
    | exact S16 | assumption | exact LO | unfold w_off_stack; lia
    | assumption | r_wm | exact SV | exact MU | exact WMo ].
Qed.

(* 0x14dc8-0x14dd0: got = n < 1514 ? n : 1514, on to 0x14dd4. *)
Lemma r_poll :
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 pfr s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (v4 v3 v2 v1 v0 vra : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (lo fa pf r : Z) (bytes j80 : list byte) (B2 B2d B' : list byte),
    bv_unsigned pfr mod 2 ^ 32 = pf -> 0 <= pf < 2 ^ 32 ->
    diginet_session_poll_m timg_ubsan (Some (TFrame fa bytes)) (rx_B2c B2 fa (Z.of_nat (length bytes)) pf bytes) 0
      = Some (B2d, r) ->
    settle_m (set_g_rx_fail (set_g_rx B2d 0) 0) (if rx_fails pf =? 0 then 1 else 0) = Some (B', tt) ->
    g_fail_next B2 <= 1 ->
    0 < fa -> fa + Z.max 1 (Z.of_nat (length bytes)) <= lo -> off_world fa (Z.max 1 (Z.of_nat (length bytes))) ->
    bytes_at rsegs m fa bytes ->
    relro_img m0 -> (fa + Z.max 1 (Z.of_nat (length bytes)) <= RELRO_BASE \/ RELRO_BASE + RELRO_LEN <= fa) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + 3824 <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp 3824 -> mem_inv rsegs m -> wmem rsegs m B2 ->
    rw_cells rsegs m (bv_unsigned sp) [CB 80 j80] ->
    rw_cells rsegs m (bv_unsigned sp + 80) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    munch [(bv_unsigned sp - 3824, bv_unsigned sp + 80); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
           (fa, fa + Z.max 1 (Z.of_nat (length bytes)))] m0 m ->
    wmono rsegs m0 m ->
    evt rsegs (q_body F fc sp gp tp s5 s6 s7 s8 s9 s10 s11 m0 fa (Z.of_nat (length bytes))
                 [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] B')
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length bytes))) a0 a1 a2 a3 a4 a5 a6 a7
               pfr s3 (Z_to_bv 64 274632) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14dc8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 pfr s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    v4 v3 v2 v1 v0 vra F fc m0 m lo fa pf r bytes j80 B2 B2d B' Hpf Rpf MODP MODS GF2 Hfa0 Hfalo OWfa FB
    RI0 RLfa S16 ST LO WOS MI WM SF SV MU WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (Hn0 : 0 <= Z.of_nat (length bytes)) by lia.
  (* 0x14dc8: li a0, 1514; 0x14dcc: bltu s1, a0, 0x14dd4 *)
  step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with (Z.of_nat (length bytes) <? 1514) by (symmetry; apply r_ltu; lia)
  end.
  destruct (Z.ltb_spec (Z.of_nat (length bytes)) 1514) as [Hlt|Hge]; cbv iota.
  - eapply r_poll2 with (got := Z.of_nat (length bytes)) (lo := lo) (B2 := B2) (j80 := j80);
      [ unfold rx_got, SPEC_MAX_FRAME; destruct (Z.ltb_spec 1514 (Z.of_nat (length bytes))); lia
      | exact Hpf | exact Rpf | exact MODP | exact MODS | exact GF2 | exact Hfa0 | exact Hfalo | exact OWfa
      | exact FB | exact RI0 | exact RLfa | exact S16 | exact ST | exact LO | exact WOS | exact MI | exact WM
      | exact SF | exact SV | exact MU | exact WMo ].
  - (* 0x14dd0: li s1, 1514 *)
    step.
    eapply r_poll2 with (got := 1514) (lo := lo) (B2 := B2) (j80 := j80);
      [ unfold rx_got, SPEC_MAX_FRAME; destruct (Z.ltb_spec 1514 (Z.of_nat (length bytes))); lia
      | exact Hpf | exact Rpf | exact MODP | exact MODS | exact GF2 | exact Hfa0 | exact Hfalo | exact OWfa
      | exact FB | exact RI0 | exact RLfa | exact S16 | exact ST | exact LO | exact WOS | exact MI | exact WM
      | exact SF | exact SV | exact MU | exact WMo ].
Qed.

Lemma r_B2_gf : forall Bw bytes, length Bw = Z.to_nat W_LEN -> g_fail_next (rx_B2 Bw bytes) = g_fail_next Bw.
Proof.
  intros Bw bytes L. unfold rx_B2, rx_ob. cbv zeta.
  unfold set_g_rx_send, set_M_fail, set_OW_desk_off, g_fail_next, OFF_g_rx_send, A_M_fail, A_OW_desk_off,
    OFF_M, OFF_OW, OFF_GOT, OFF_g_fail_next, SZ_OW, SZ_GOT.
  r_push L. reflexivity.
Qed.

(* 0x14d70-0x14dc4: op_begin (two memsets, OW.desk_off = -1, M.fail = g_fail_next), spec_read_frame (frame, n, &f),
   g_rx_send = f.send, then the branch on by_poll. *)
Lemma r_mid :
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 pfr s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (v4 v3 v2 v1 v0 vra : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (lo fa by_poll pf : Z) (bytes j80 : list byte) (Bw Bw' : list byte),
    - 2 ^ 31 <= by_poll < 2 ^ 31 -> bv_unsigned pfr mod 2 ^ 32 = pf -> 0 <= pf < 2 ^ 32 ->
    receive_m timg_ubsan Bw fa bytes by_poll pf = Some (Bw', tt) ->
    g_fail_next Bw <= 1 ->
    0 < fa -> fa + Z.max 1 (Z.of_nat (length bytes)) <= lo -> W_BASE_UBSAN + W_LEN <= lo ->
    off_world fa (Z.max 1 (Z.of_nat (length bytes))) ->
    bytes_at rsegs m fa bytes ->
    relro_img m0 -> (fa + Z.max 1 (Z.of_nat (length bytes)) <= RELRO_BASE \/ RELRO_BASE + RELRO_LEN <= fa) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + 3824 <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp 3824 -> mem_inv rsegs m -> wmem rsegs m Bw ->
    rw_cells rsegs m (bv_unsigned sp) [CB 80 j80] ->
    rw_cells rsegs m (bv_unsigned sp + 80) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    munch [(bv_unsigned sp - 3824, bv_unsigned sp + 80); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
           (fa, fa + Z.max 1 (Z.of_nat (length bytes)))] m0 m ->
    wmono rsegs m0 m ->
    evt rsegs (q_body F fc sp gp tp s5 s6 s7 s8 s9 s10 s11 m0 fa (Z.of_nat (length bytes))
                 [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] Bw')
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length bytes))) a0 a1 a2 a3 a4 a5 a6 a7
               pfr (Z_to_bv 64 by_poll) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14d70) fc None m (seg_rom rsegs)).
Proof.
  pose proof MSET as MSET0. unfold memset_contract, MEMSET in MSET0.
  pose proof SRF as SRF0. unfold spec_read_frame_contract, spec_read_frame_ENTRY, spec_read_frame_FRAME in SRF0.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 pfr s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    v4 v3 v2 v1 v0 vra F fc m0 m lo fa by_poll pf bytes j80 Bw Bw' Hbp Hpf Rpf MOD GF0 Hfa0 Hfalo Hwlo OWfa FB
    RI0 RLfa S16 ST LO WOS MI WM SF SV MU WMo.
  set (n := Z.of_nat (length bytes)) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  unfold w_off_stack in WOS. pose proof OWfa as OWfa'. unfold off_world in OWfa'.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (wm_len rsegs W_BASE_UBSAN m Bw WM) as LBw.
  wk_facts.
  (* 0x14d70-0x14d84: auipc a0; addi s4, a0, 856; addi a0, s4, 344 (OW); li a2, 304; li a1, 0; jal memset *)
  step. step. step. step. step. step.
  assert (U1 : bv_unsigned (Z_to_bv 64 274976) = 274976) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 304) = 304) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wm_piece rsegs W_BASE_UBSAN mm Bw 65312 (bv_unsigned (Z_to_bv 64 304))
                  (bv_unsigned (Z_to_bv 64 274976)) WM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DST end.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply MSET0; [exact DST | exact MI] | wk_post_call sg mm ]
  end.
  (* 0x14d88-0x14d94: addi a0, s4, 116 (GOT); li a2, 224; li a1, 0; jal memset *)
  step. step. step. step.
  assert (U3 : bv_unsigned (Z_to_bv 64 274748) = 274748) by (apply unsigned_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 224) = 224) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with H : rw_cells rsegs mm W_BASE_UBSAN [CB _ ?BW] |- _ =>
      pose proof (wm_piece rsegs W_BASE_UBSAN mm BW 65084 (bv_unsigned (Z_to_bv 64 224))
                    (bv_unsigned (Z_to_bv 64 274748)) H ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DST2 end end.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply MSET0; [exact DST2 | assumption] | wk_post_call sg mm ]
  end.
  (* 0x14d98-0x14da8: lbu a0, 0(s4) (g_fail_next); li a1, -1; sw a1, 576(s4) (OW.desk_off); auipc a1;
     sw a0, 1460(a1) (M.fail) *)
  step. step. step. step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with H : rw_cells rsegs mm W_BASE_UBSAN [CB _ ?BW] |- _ =>
        assert (EOB : BW = rx_ob Bw);
        [ unfold rx_ob; cbv zeta;
          unfold set_M_fail, set_OW_desk_off, g_fail_next, A_M_fail, A_OW_desk_off, OFF_M, OFF_OW, OFF_GOT,
            OFF_g_fail_next, SZ_OW, SZ_GOT;
          rewrite (r_uo _ (put 4 (-1)) 65544 64968 1) by r_side LBw;
          reflexivity
        | rewrite EOB in H ]
      end
  end.
  (* 0x14dac-0x14db8: mv a2, sp; mv a0, s0; mv a1, s1; jal spec_read_frame *)
  step. step. step. step.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply SRF0 with (p := fa) (len := n) (fp := bv_unsigned sp) (lo := lo) (B := rx_ob Bw) (fr := bytes)
          (junk := j80);
        [ reflexivity | reflexivity | symmetry; apply Z_to_bv_bv_unsigned | exact Hfa0 | assumption | fold n; lia
        | lia | Z.div_mod_to_equations; lia | lia | exact SF | fold n; lia
        | unfold off_window; fold n; lia
        | exact S16 | assumption | lia | unfold w_off_stack; lia | assumption | r_wm ]
      | wk_post_call sg mm ]
  end.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp) [CB 80 (sf_bytes _ _)] |- _ =>
    apply r_sf_cells_of in H; rename H into SFc end.
  assert (ES : sf_send (spec_read_frame (zs bytes) n) = rx_send bytes)
    by (unfold n; rewrite r_srf_send by lia; rewrite firstn_all; reflexivity).
  cbv beta delta [r_sf_cells] in SFc.
  rewrite ES in SFc.
  (* 0x14dbc: lw a0, 32(sp) (f.send); 0x14dc0: sw a0, 20(s4) (g_rx_send) *)
  step. rewrite r_sx32. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with H : rw_cells rsegs mm W_BASE_UBSAN _ |- _ =>
        rewrite r_put4_swrap in H; change (upd (rx_ob Bw) 64988 (put 4 (rx_send bytes))) with (rx_B2 Bw bytes) in H
      end
  end.
  assert (GF2 : g_fail_next (rx_B2 Bw bytes) <= 1) by (rewrite (r_B2_gf Bw bytes LBw); exact GF0).
  (* 0x14dc4: beqz s3, 0x14e2c *)
  step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with (by_poll =? 0) by (symmetry; apply r_eqbs; lia)
  end.
  destruct (Z.eqb_spec by_poll 0) as [Hb0|Hb0]; cbv iota.
  - subst by_poll.
    rewrite (rx_mrx_eq timg_ubsan Bw fa bytes pf ltac:(lia)) in MOD.
    lazymatch type of MOD with context [m_rx_m ?I ?F ?B ?k] =>
      destruct (m_rx_m I F B k) as [[Bx t]|] eqn:M1; [|discriminate MOD] end.
    lazymatch type of MOD with context [diginet_session_rx_m ?I ?F ?B ?b ?w] =>
      destruct (diginet_session_rx_m I F B b w) as [[By r]|] eqn:M2; [|discriminate MOD] end.
    lazymatch type of MOD with context [settle_m ?B ?t] =>
      destruct (settle_m B t) as [[B4 u]|] eqn:M3; [|discriminate MOD] end.
    injection MOD as EB. destruct u. subst B4.
    eapply r_mrx with (lo := lo) (B2 := rx_B2 Bw bytes);
      [ exact M1 | exact M2 | exact M3 | exact GF2 | exact Hfa0 | exact Hfalo | exact OWfa | assumption
      | exact RI0 | exact RLfa | exact S16 | assumption | exact LO | unfold w_off_stack; lia | assumption
      | r_wm | exact SV | exact MU | exact WMo ].
  - rewrite (rx_poll_eq timg_ubsan Bw fa bytes by_poll pf ltac:(lia) Hb0) in MOD.
    lazymatch type of MOD with context [diginet_session_poll_m ?I ?F ?B ?w] =>
      destruct (diginet_session_poll_m I F B w) as [[B2d r]|] eqn:M1; [|discriminate MOD] end.
    lazymatch type of MOD with context [settle_m ?B ?t] =>
      destruct (settle_m B t) as [[B4 u]|] eqn:M3; [|discriminate MOD] end.
    injection MOD as EB. destruct u. subst B4.
    destruct (rw_cells_forget _ _ _ _ SFc) as [j80' SF']. cbn [cells_size csize Nat.add] in SF'.
    eapply r_poll with (lo := lo) (B2 := rx_B2 Bw bytes) (j80 := j80');
      [ exact Hpf | exact Rpf | exact M1 | exact M3 | exact GF2 | exact Hfa0 | exact Hfalo | exact OWfa
      | assumption | exact RI0 | exact RLfa | exact S16 | assumption | exact LO | unfold w_off_stack; lia
      | assumption | r_wm | exact SF' | exact SV | exact MU | exact WMo ].
Qed.

(* 0x14d54-0x14d6c: malloc's frame is not NULL (the abort at 0x14e84 is not reached); s0 = frame; memcpy of the n
   bytes into it when n != 0; on to 0x14d70. *)
Lemma r_body :
  forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 pfr s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (v4 v3 v2 v1 v0 vra : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (lo fa p by_poll pf : Z) (bytes junk j80 : list byte) (Bw Bw' : list byte),
    - 2 ^ 31 <= by_poll < 2 ^ 31 -> bv_unsigned pfr mod 2 ^ 32 = pf -> 0 <= pf < 2 ^ 32 ->
    receive_m timg_ubsan Bw fa bytes by_poll pf = Some (Bw', tt) ->
    g_fail_next Bw <= 1 ->
    (Z.of_nat (length bytes) <> 0 -> bytes_at rsegs m p bytes) ->
    (Z.of_nat (length bytes) = 0 \/ p + Z.of_nat (length bytes) <= fa \/ fa + Z.of_nat (length bytes) <= p) ->
    0 < fa -> fa + Z.max 1 (Z.of_nat (length bytes)) <= lo -> W_BASE_UBSAN + W_LEN <= lo ->
    off_world fa (Z.max 1 (Z.of_nat (length bytes))) ->
    rw_cells rsegs m fa [CB (Z.to_nat (Z.max 1 (Z.of_nat (length bytes)))) junk] ->
    relro_img m0 -> (fa + Z.max 1 (Z.of_nat (length bytes)) <= RELRO_BASE \/ RELRO_BASE + RELRO_LEN <= fa) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + 3824 <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp 3824 -> mem_inv rsegs m -> wmem rsegs m Bw ->
    rw_cells rsegs m (bv_unsigned sp) [CB 80 j80] ->
    rw_cells rsegs m (bv_unsigned sp + 80) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    munch [(bv_unsigned sp - 3824, bv_unsigned sp + 80); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
           (fa, fa + Z.max 1 (Z.of_nat (length bytes)))] m0 m ->
    wmono rsegs m0 m ->
    evt rsegs (q_body F fc sp gp tp s5 s6 s7 s8 s9 s10 s11 m0 fa (Z.of_nat (length bytes))
                 [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] Bw')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.of_nat (length bytes))) (Z_to_bv 64 fa) a1 a2 a3 a4 a5 a6 a7
               pfr (Z_to_bv 64 by_poll) (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 R_MALLOC_RET) fc None m (seg_rom rsegs)).
Proof.
  pose proof MCPY as MCPY0. unfold memcpy_contract in MCPY0.
  intros ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 pfr s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    v4 v3 v2 v1 v0 vra F fc m0 m lo fa p by_poll pf bytes junk j80 Bw Bw' Hbp Hpf Rpf MOD GF0 FP DISJ
    Hfa0 Hfalo Hwlo OWfa FC RI0 RLfa S16 ST LO WOS MI WM SF SV MU WMo.
  unfold R_MALLOC_RET.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo0 & _ & _).
  assert (Hn0 : 0 <= Z.of_nat (length bytes)) by lia.
  unfold w_off_stack in WOS. pose proof OWfa as OWfa'. unfold off_world in OWfa'.
  wk_facts.
  (* 0x14d54: beqz a0, 0x14e84: fa <> 0 *)
  step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; rewrite r_eqb by lia; apply Z.eqb_neq; lia)
  end.
  cbv iota.
  (* 0x14d58: mv s0, a0; 0x14d5c: beqz s1, 0x14d70 *)
  step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with (Z.of_nat (length bytes) =? 0) by (symmetry; apply r_eqb; lia)
  end.
  destruct (Z.eqb_spec (Z.of_nat (length bytes)) 0) as [Hn|Hn]; cbv iota.
  - destruct bytes as [|b0 bs]; [|cbn [length] in Hn; lia].
    eapply r_mid with (lo := lo) (j80 := j80) (Bw := Bw);
      [ exact Hbp | exact Hpf | exact Rpf | exact MOD | exact GF0 | exact Hfa0 | exact Hfalo | exact Hwlo | exact OWfa
      | split; [lia|]; split; [cbn [length]; lia|]; intros i Hi; cbn [length] in Hi; lia
      | exact RI0 | exact RLfa | exact S16 | exact ST | exact LO | unfold w_off_stack; lia | exact MI | exact WM
      | exact SF | exact SV | exact MU | exact WMo ].
  - (* 0x14d60-0x14d6c: mv a0, s0; mv a1, s4; mv a2, s1; jal memcpy *)
    step. step. step. step.
    specialize (FP Hn). pose proof (bytes_at_bound rsegs m _ _ FP) as FPB.
    assert (Ufa : bv_unsigned (Z_to_bv 64 fa) = fa) by (apply unsigned_lit; lia).
    assert (Up : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
    assert (Un : bv_unsigned (Z_to_bv 64 (Z.of_nat (length bytes))) = Z.of_nat (length bytes))
      by (apply unsigned_lit; lia).
    assert (FC' : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 fa))
                    [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (length bytes))))) junk]).
    { rewrite Ufa, Un. replace (Z.of_nat (length bytes)) with (Z.max 1 (Z.of_nat (length bytes))) at 1 by lia.
      exact FC. }
    clear FC.
    lazymatch goal with
    | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply MCPY0 with (src := bytes) (junk := junk);
          [ rewrite Up; exact FP | rewrite Un; lia | exact FC' | rewrite Ufa, Up, Un; lia | exact MI ]
        | wk_post_call sg mm ]
    end.
    lazymatch goal with H : rw_cells rsegs _ (bv_unsigned (Z_to_bv 64 fa)) [CB _ bytes] |- _ =>
      destruct H as [[_ FB] _]; cbn [cells_bytes cbytes] in FB; rewrite app_nil_r, Ufa in FB end.
    eapply r_mid with (lo := lo) (j80 := j80) (Bw := Bw);
      [ exact Hbp | exact Hpf | exact Rpf | exact MOD | exact GF0 | exact Hfa0 | exact Hfalo | exact Hwlo | exact OWfa
      | exact FB | exact RI0 | exact RLfa | exact S16 | assumption | exact LO | unfold w_off_stack; lia
      | assumption | r_wm | exact SF | exact SV | exact MU | exact WMo ].
Qed.

End Body.

(* ---------------------------------------------------------------- the SR walk *)

Lemma r_cells_split2 : forall m A B cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [assumption|]|].
    + rewrite cells_bytes_length in B2 by assumption. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply Hw. lia.
Qed.

Lemma r_blk_bytes : forall (Bm : malloc_syms) m A bs, ms_segs Bm = rsegs -> 0 <= A ->
  A + Z.of_nat (length bs) <= 2 ^ 64 -> blk_data Bm m A bs -> bytes_at rsegs m A bs.
Proof.
  intros Bm m A bs HS H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, HS. reflexivity.
Qed.

Lemma r_getr_cs : forall R x, callee_saved x -> YK11.getr R (Z_to_bv 5 x) = reg_get R (Z_to_bv 5 x).
Proof.
  intros R x Hx. unfold callee_saved in Hx.
  assert (Hc : x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ x = 9 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/
               x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27) by lia.
  repeat (destruct Hc as [-> | Hc]; [reflexivity|]). subst x. reflexivity.
Qed.

(* An SR config whose machine state runs, as an evt run on its memory as it is, to Q (the donor's llvm_run). *)
Lemma r_run : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs Q (MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m', Q (MS R F pc' fc None m' (seg_rom rsegs)) ->
     forall regs', Regs6ss.xregs_eqv R regs' ->
     SR rsegs (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (YK11.seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros fx' regs pc mem md Q P Hh Hl HE Hform HK.
  apply (evt_SR_canon rsegs _ Q md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & HQ & Heq). destruct (Hform can HQ) as (R & F & pc' & fc & m' & ->).
  destruct (sr_eqv_mkst R F pc' fc m' (seg_rom rsegs) ms' Heq) as [Ems Hx]. rewrite Ems.
  exact (HK R F pc' fc m' HQ _ Hx).
Qed.

(* a register the callee keeps, read through regs_preserved and the run's register relation *)
Ltac r_rp Hrp Hx k :=
  lazymatch goal with |- reg_get ?R ?r = _ => change (reg_get R r) with (YK11.getr R (Z_to_bv 5 k)) end;
  rewrite (Hrp k ltac:(unfold callee_saved; lia)); rewrite (sr_getr_eqv _ _ _ Hx); reflexivity.

Ltac r_g Hx := rewrite (sr_getr_eqv _ _ _ Hx); reflexivity.

Theorem receive_holds : forall {fx : FPState} {rc : RunCeil} (B : malloc_syms) (API : AllocAPI B),
  (forall fx', @malloc_contract fx' rc B API) -> (forall fx', @free_contract fx' rc B API) ->
  memset_contract -> memcpy_contract -> spec_read_frame_contract -> diginet_session_poll_contract ->
  m_rx_contract -> diginet_session_rx_contract -> settle_contract -> @receive_contract fx rc B API.
Proof.
  intros fx rc B API MALLOC FREE MSET MCPY SRF POLL MRX RXC SET.
  unfold receive_contract.
  intros BI L0 A0 regs0 mem0 md0 b Bw p bytes by_poll pf Hpre Hfrm Hargs Hroom.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX & ERRNO & CTXLO & WORLD & RELRO).
  pose proof Hpre as (Hcall & HID & Hhalt0 & Hlazy0 & Hro0 & Hres0 & Hwos0 & WM0 & GF0 & RI0).
  pose proof Hcall as (HM0 & HW0 & HB0 & Hra0 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & _).
  pose proof Hargs as (E10 & E11 & E12 & Hbp & Epf & Rpf & Hn65 & Hblk & Hsrc & Hmod).
  rewrite SEGS in Hro0.
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (HRF : receive_FRAME = 8320) by reflexivity.
  assert (Hn0 : 0 <= Z.of_nat (length bytes)) by lia.
  assert (Esp0 : spZ regs0 = bv_unsigned (reg_get regs0 2)) by reflexivity.
  pose proof (bv_unsigned_in_range 64 (reg_get regs0 2)) as Rsp0. unfold bv_modulus in Rsp0.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp0.
  pose proof (sr_fr_init B API SEGS receive_FRAME L0 A0 regs0 mem0 md0 b Bw Hpre) as FR0.
  (* ---- the entry, 0x14d1c-0x14d50 ---- *)
  assert (ST0 : stk rsegs (normalize rsegs mem0) (spZ regs0 - receive_FRAME) (bv_unsigned (reg_get regs0 2))).
  { apply (norm_stk B SEGS); [exact Hro0 | unfold SR_RES_TOP; lia | lia |]. intros a Ha. apply Hstw0. lia. }
  pose proof (sr_wmem_norm mem0 Bw Hro0 WM0) as WMn0.
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG WORLD) with (stk := receive_FRAME) (S := spZ regs0) (L0 := L0) (A0 := A0)
    (mem0 := mem0) (md0 := md0) (L := L0) (A := A0)
    (Q := q_mal (@fp_regs fx) (@fp_csr fx) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 8)
            (reg_get regs0 11) (reg_get regs0 12) (reg_get regs0 13) (reg_get regs0 21) (reg_get regs0 22)
            (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27)
            (normalize rsegs mem0) (bv_unsigned (reg_get regs0 2) - 128) (spZ regs0 - receive_FRAME) p
            (Z.of_nat (length bytes))
            [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18); C8 (reg_get regs0 9);
             C8 (reg_get regs0 8); C8 (reg_get regs0 1)] Bw).
  { exact FR0. }
  { lia. }
  { lia. }
  { unfold Regs6ss.mkR_of. rewrite (E10 : reg_get regs0 10 = Z_to_bv 64 p).
    eapply r_entry;
      [ exact ST0 | lia | apply mem_inv_normalize | lia | exact E11 | lia | exact WMn0
      | unfold W_BASE_UBSAN, W_LEN; lia ]. }
  { intros ms HQ.
    destruct HQ as (t0' & t1' & t2' & x11 & x12 & x13 & x14 & x15 & x16 & x17 & t3' & t4' & t5' & t6' & m' & j
                    & -> & MU & WMo & _).
    do 5 eexists. exists [(bv_unsigned (reg_get regs0 2) - 128, bv_unsigned (reg_get regs0 2) - 128 + 128)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WMo|].
    intros x Hx NO. left. cbn [outside] in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (t0' & t1' & t2' & x11 & x12 & x13 & x14 & x15 & x16 & x17 & t3' & t4' & t5' & t6' & mq & j
                  & HE & MU1 & WMo1 & MI1 & ST1 & RW1 & WMq).
  injection HE as ER EF EP EC EM. subst R F pc' fc. subst m0'.
  assert (G11 : YK11.getr regs1 1 = Z_to_bv 64 R_MALLOC_RET) by r_g Hx1.
  assert (G12 : YK11.getr regs1 2 = Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) by r_g Hx1.
  assert (G14 : YK11.getr regs1 4 = reg_get regs0 4) by r_g Hx1.
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 (Z.max 1 (Z.of_nat (length bytes)))) by r_g Hx1.
  assert (Hsp1 : spZ regs1 = spZ regs0 - 128) by (unfold spZ at 1; rewrite G12; rewrite unsigned_lit by lia; lia).
  (* ---- malloc (n ? n : 1) ---- *)
  rewrite <- SEGS, <- HMAL.
  eapply (g_malloc B API SEGS AX ERRNO WORLD RELRO) with (stk := receive_FRAME) (S := spZ regs0) (L0 := L0)
    (A0 := A0) (mem0 := mem0) (md0 := md0) (n := Z.max 1 (Z.of_nat (length bytes))) (bres := b).
  { exact MALLOC. }
  { exact FR1. }
  { lia. }
  { lia. }
  { rewrite G11. apply ret_ok_even. reflexivity. }
  { rewrite Hsp1. Z.div_mod_to_equations. lia. }
  { rewrite Hsp1. unfold ALLOC_STACK. lia. }
  { lia. }
  { lia. }
  { rewrite G14. exact Htp0. }
  { exact G110. }
  { exact Hres0. }
  { exact Hroom. }
  intros L1 A1 regs2 mem2 md2 fa FR2 Hrp2 G210 Hfa1 Hfa2 Hfa16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2
    Hsrk2.
  rewrite G11, SEGS.
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & Hmd2 & Hhigh2 & Himg2 & Hub2 & Hbyt2 & Hstw2 & Herr2 & Hgd2 & Hro2
                     & Hle2 & Hlen2).
  assert (Haddr : h_addr_ok fa) by (unfold h_addr_ok; lia).
  destruct (receive_m timg_ubsan Bw fa bytes by_poll pf) as [[Bw' []]|] eqn:MODfa;
    [| exfalso; exact (Hmod fa Haddr MODfa)].
  (* the heap frame: born here, apart from every entry block, off the world and .data.rel.ro *)
  assert (Hin1 : In (fa, Z.max 1 (Z.of_nat (length bytes))) (blocks L1 A1))
    by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (PW : pairwise ranges_disjoint (b1 ++ (fa, Z.max 1 (Z.of_nat (length bytes))) :: b2))
    by (rewrite <- Eb1; exact (mr_blocks_disjoint B _ (aa_laws API) L1 A1 mem2 md2 HM2)).
  assert (MINE : forall a k, In (a, k) (blocks L0 A0) -> a + k <= fa \/ fa + Z.max 1 (Z.of_nat (length bytes)) <= a).
  { intros a k Hak. rewrite Eb2 in Hak. pose proof (sr_disj_mid b1 _ b2 (a, k) PW Hak) as H. cbn [fst snd] in H.
    lia. }
  assert (OWfa : off_world fa (Z.max 1 (Z.of_nat (length bytes)))).
  { unfold off_world. apply (r_off_img B fa _ W_BASE_UBSAN W_LEN); [lia | unfold W_LEN; lia | exact Hnimg |].
    intros j0 Hj. exact (proj1 (WORLD (W_BASE_UBSAN + j0) ltac:(unfold h_world; lia))). }
  assert (RLfa : fa + Z.max 1 (Z.of_nat (length bytes)) <= RELRO_BASE \/ RELRO_BASE + RELRO_LEN <= fa).
  { apply (r_off_img B fa _ RELRO_BASE RELRO_LEN); [lia | unfold RELRO_LEN; lia | exact Hnimg |].
    intros j0 Hj. exact (proj1 (RELRO (RELRO_BASE + j0) ltac:(lia))). }
  (* the n source bytes, kept from the entry (an entry block, or above the caller's sp) *)
  assert (FP2 : Z.of_nat (length bytes) <> 0 -> bytes_at rsegs (normalize rsegs mem2) p bytes).
  { intros Hn. apply bytes_at_normalize; [exact Hro2|].
    destruct Hsrc as [Hz | (Hpo & [(q & k & Hq & Hq1 & Hq2) | (Hs1 & Hs2)])]; [contradiction | |].
    - assert (Hb : In (ptr_addr L0 q, k) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
      pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q k HM0 Hq) as (R1 & R2).
      apply (r_blk_bytes B mem2 p bytes SEGS); [lia | lia |].
      intros i Hi. rewrite <- (Hblk i Hi).
      replace (p + i) with (ptr_addr L0 q + (p + i - ptr_addr L0 q)) by lia.
      apply (Hbyt2 (ptr_addr L0 q) k); [exact Hb | lia].
    - apply (r_blk_bytes B mem2 p bytes SEGS); [lia | lia |].
      intros i Hi. rewrite <- (Hblk i Hi).
      apply (proj1 (Hhigh2 (p + i) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }
  assert (DISJ : Z.of_nat (length bytes) = 0 \/ p + Z.of_nat (length bytes) <= fa \/
                 fa + Z.of_nat (length bytes) <= p).
  { destruct Hsrc as [Hz | (Hpo & [(q & k & Hq & Hq1 & Hq2) | (Hs1 & Hs2)])]; [left; exact Hz | right | right].
    - assert (Hb : In (ptr_addr L0 q, k) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
      destruct (MINE _ _ Hb); lia.
    - right. lia. }
  destruct (norm_blk B API SEGS AX L1 A1 mem2 md2 fa (Z.max 1 (Z.of_nat (length bytes))) HM2 Hin1 ltac:(lia) Hro2)
    as [junk FC].
  (* receive's frame, the world and .data.rel.ro on the normalized memory after malloc *)
  pose proof (sr_rw_cells_rel m1 _ _ _ Hrel1 RW1) as RW1'.
  assert (RW2 : rw_cells rsegs mem2 (bv_unsigned (reg_get regs0 2) - 128)
                  (CB 80 j :: [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
                               C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)])).
  { apply (sr_rw_cells_frame m1 mem2 _ _ RW1'). intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    pose proof (Habove2 a ltac:(rewrite Hsp1; lia)) as E. rewrite SEGS in E. exact E. }
  assert (RW3 : rw_cells rsegs (normalize rsegs mem2) (bv_unsigned (reg_get regs0 2) - 128)
                  (CB 80 j :: [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
                               C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)])).
  { apply (sr_rw_cells_norm B mem2 _ _ SEGS Hro2); [|exact RW2]. intros i Hi Himg.
    pose proof (sr_in_img_top B _ SEGS Himg). unfold SR_RES_TOP in *. cbn [cells_size csize Nat.add] in Hi. lia. }
  assert (EB80 : bv_unsigned (reg_get regs0 2) - 128 + 80 =
                 bv_unsigned (reg_get regs0 2) - 128 + Z.of_nat (cells_size [CB 80 j]))
    by (change (Z.of_nat (cells_size [CB 80 j])) with 80; reflexivity).
  destruct (r_cells_split2 _ (bv_unsigned (reg_get regs0 2) - 128) (bv_unsigned (reg_get regs0 2) - 128 + 80) [CB 80 j]
              [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
               C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)] RW3 EB80) as [SF SV].
  assert (ST2 : stk rsegs (normalize rsegs mem2) (spZ regs0 - receive_FRAME) (bv_unsigned (reg_get regs0 2) - 128)).
  { apply (norm_stk B SEGS); [exact Hro2 | unfold SR_RES_TOP; lia | lia |]. intros a Ha. apply Hstw2. lia. }
  pose proof (sr_wmem_back m1 _ Bw Hrel1 WMq) as WM1.
  assert (WM2 : wmem rsegs mem2 Bw).
  { apply (sr_rw_cells_frame m1 mem2 _ _ WM1). intros a Ha. rewrite wm_size in Ha.
    pose proof (Hsrk2 a (or_introl Ha)) as E. rewrite SEGS in E. exact E. }
  pose proof (sr_wmem_norm mem2 Bw Hro2 WM2) as WMn2.
  assert (RI2 : relro_img mem2).
  { intros i Hi. rewrite <- (RI0 i Hi).
    destruct (RELRO (RELRO_BASE + i) ltac:(lia)) as (H1 & H2 & H3 & H4).
    pose proof (proj1 (Himg2 (RELRO_BASE + i) H1 H2 H3 H4
                  ltac:(unfold h_world, RELRO_BASE, RELRO_LEN, W_BASE_UBSAN in *; lia))) as E.
    rewrite SEGS in E. exact E. }
  pose proof (sr_relro_norm mem2 Hro2 RI2) as RIn2.
  (* the registers after malloc *)
  assert (E22 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) by r_rp Hrp2 Hx1 2.
  assert (E23 : reg_get regs2 3 = reg_get regs0 3) by r_rp Hrp2 Hx1 3.
  assert (E24 : reg_get regs2 4 = reg_get regs0 4) by r_rp Hrp2 Hx1 4.
  assert (E28 : reg_get regs2 8 = reg_get regs0 8) by r_rp Hrp2 Hx1 8.
  assert (E29 : reg_get regs2 9 = reg_get regs0 11) by r_rp Hrp2 Hx1 9.
  assert (E210 : reg_get regs2 10 = Z_to_bv 64 fa) by exact G210.
  assert (E218 : reg_get regs2 18 = reg_get regs0 13) by r_rp Hrp2 Hx1 18.
  assert (E219 : reg_get regs2 19 = reg_get regs0 12) by r_rp Hrp2 Hx1 19.
  assert (E220 : reg_get regs2 20 = Z_to_bv 64 p) by r_rp Hrp2 Hx1 20.
  assert (E221 : reg_get regs2 21 = reg_get regs0 21) by r_rp Hrp2 Hx1 21.
  assert (E222 : reg_get regs2 22 = reg_get regs0 22) by r_rp Hrp2 Hx1 22.
  assert (E223 : reg_get regs2 23 = reg_get regs0 23) by r_rp Hrp2 Hx1 23.
  assert (E224 : reg_get regs2 24 = reg_get regs0 24) by r_rp Hrp2 Hx1 24.
  assert (E225 : reg_get regs2 25 = reg_get regs0 25) by r_rp Hrp2 Hx1 25.
  assert (E226 : reg_get regs2 26 = reg_get regs0 26) by r_rp Hrp2 Hx1 26.
  assert (E227 : reg_get regs2 27 = reg_get regs0 27) by r_rp Hrp2 Hx1 27.
  assert (Usp : bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) = bv_unsigned (reg_get regs0 2) - 128)
    by (apply unsigned_lit; lia).
  (* ---- the body, 0x14d54-0x14e60 ---- *)
  eapply (g_run B API SEGS AX HGG WORLD) with (stk := receive_FRAME) (S := spZ regs0) (L0 := L0) (A0 := A0)
    (mem0 := mem0) (md0 := md0) (L := L1) (A := A1)
    (Q := q_body (@fp_regs fx) (@fp_csr fx) (Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) (reg_get regs0 3)
            (reg_get regs0 4) (reg_get regs0 21) (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24)
            (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) (normalize rsegs mem2) fa
            (Z.of_nat (length bytes))
            [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18); C8 (reg_get regs0 9);
             C8 (reg_get regs0 8); C8 (reg_get regs0 1)] Bw').
  { exact FR2. }
  { lia. }
  { lia. }
  { unfold Regs6ss.mkR_of.
    rewrite E22, E23, E24, E28, E29, E210, E218, E219, E220, E221, E222, E223, E224, E225, E226, E227.
    rewrite (E11 : reg_get regs0 11 = Z_to_bv 64 (Z.of_nat (length bytes))).
    rewrite (E12 : reg_get regs0 12 = Z_to_bv 64 by_poll).
    eapply (r_body MSET MCPY SRF POLL MRX RXC SET) with (lo := spZ regs0 - receive_FRAME) (j80 := j) (junk := junk)
      (Bw := Bw);
      [ exact Hbp | exact Epf | exact Rpf | exact MODfa | exact GF0
      | exact FP2 | exact DISJ | lia | lia | unfold W_BASE_UBSAN, W_LEN; lia | exact OWfa | exact FC
      | exact RIn2 | exact RLfa
      | rewrite Usp; Z.div_mod_to_equations; lia | rewrite Usp; exact ST2 | rewrite Usp; lia
      | unfold w_off_stack; rewrite Usp; unfold W_BASE_UBSAN, W_LEN; lia | apply mem_inv_normalize | exact WMn2
      | rewrite Usp; exact SF | rewrite Usp; exact SV
      | apply munch_refl | apply wmono_refl ]. }
  { intros ms HQ.
    destruct HQ as (z0 & z1 & z2 & o0 & o1 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & o2 & o3 & o4
                    & z3 & z4 & z5 & z6 & m' & -> & MU & WMo & _).
    do 5 eexists. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WMo|].
    intros x Hx NO. cbn [outside] in NO. rewrite Usp in NO.
    assert (Hcase : (spZ regs0 - receive_FRAME <= x < spZ regs0) \/ h_world x \/
                    (fa <= x < fa + Z.max 1 (Z.of_nat (length bytes)))) by (unfold h_world; lia).
    destruct Hcase as [Hc | [Hc | Hc]]; [left; exact Hc | right; left; exact Hc | right; right].
    exists fa, (Z.max 1 (Z.of_nat (length bytes))). split; [|exact Hc].
    split; [exact Hin1|]. split; [lia|]. exact MINE. }
  intros R F pc' fc m0'' HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as (z0 & z1 & z2 & o0 & o1 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & o2 & o3 & o4
                  & z3 & z4 & z5 & z6 & mq3 & HE & MU3 & WMo3 & SV3 & WMb & GFb).
  injection HE as ER EF EP EC EM. subst R F pc' fc. subst m0''.
  assert (G31 : YK11.getr regs3 1 = Z_to_bv 64 R_FREE_RET) by r_g Hx3.
  assert (G32 : YK11.getr regs3 2 = Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) by r_g Hx3.
  assert (G34 : YK11.getr regs3 4 = reg_get regs0 4) by r_g Hx3.
  assert (G310 : YK11.getr regs3 10 = Z_to_bv 64 fa) by r_g Hx3.
  assert (Hsp3 : spZ regs3 = spZ regs0 - 128) by (unfold spZ at 1; rewrite G32; rewrite unsigned_lit by lia; lia).
  (* ---- free (frame) ---- *)
  rewrite <- SEGS, <- HFRE.
  eapply (g_free B API SEGS AX ERRNO WORLD RELRO) with (stk := receive_FRAME) (S := spZ regs0) (L0 := L0)
    (A0 := A0) (mem0 := mem0) (md0 := md0) (x := fa) (n := Z.max 1 (Z.of_nat (length bytes)))
    (bres := sb_malloc b (Z.max 1 (Z.of_nat (length bytes)))).
  { exact FREE. }
  { exact FR3. }
  { lia. }
  { lia. }
  { rewrite G31. apply ret_ok_even. reflexivity. }
  { rewrite Hsp3. Z.div_mod_to_equations. lia. }
  { rewrite Hsp3. unfold ALLOC_STACK. lia. }
  { lia. }
  { lia. }
  { rewrite G34. exact Htp0. }
  { exact G310. }
  { exact Hin1. }
  { lia. }
  { exact MINE. }
  { exact Hres2. }
  intros L2 A2 regs4 mem4 md4 FR4 Hrp4 (c1 & c2 & Ec1 & Ec2) Hres4 Habove4 Hkept4 Hsrk4.
  rewrite G31, SEGS.
  pose proof FR4 as (HM4 & HW4 & HB4 & HID4 & Hmd4 & Hhigh4 & Himg4 & Hub4 & Hbyt4 & Hstw4 & Herr4 & Hgd4 & Hro4
                     & Hle4 & Hlen4).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM4) as (Hh4 & Hl4 & _).
  pose proof (sr_rw_cells_rel m3 _ _ _ Hrel3 SV3) as SV3'.
  assert (SV4 : rw_cells rsegs mem4 (bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) + 80)
                  [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
                   C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)]).
  { apply (sr_rw_cells_frame m3 mem4 _ _ SV3'). intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    pose proof (Habove4 a ltac:(rewrite Hsp3; lia)) as E. rewrite SEGS in E. exact E. }
  pose proof (sr_wmem_back m3 _ Bw' Hrel3 WMb) as WM3.
  assert (WM4 : wmem rsegs mem4 Bw').
  { apply (sr_rw_cells_frame m3 mem4 _ _ WM3). intros a Ha. rewrite wm_size in Ha.
    pose proof (Hsrk4 a (or_introl Ha)) as E. rewrite SEGS in E. exact E. }
  assert (E42 : reg_get regs4 2 = Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) by r_rp Hrp4 Hx3 2.
  assert (E43 : reg_get regs4 3 = reg_get regs0 3) by r_rp Hrp4 Hx3 3.
  assert (E44 : reg_get regs4 4 = reg_get regs0 4) by r_rp Hrp4 Hx3 4.
  assert (E421 : reg_get regs4 21 = reg_get regs0 21) by r_rp Hrp4 Hx3 21.
  assert (E422 : reg_get regs4 22 = reg_get regs0 22) by r_rp Hrp4 Hx3 22.
  assert (E423 : reg_get regs4 23 = reg_get regs0 23) by r_rp Hrp4 Hx3 23.
  assert (E424 : reg_get regs4 24 = reg_get regs0 24) by r_rp Hrp4 Hx3 24.
  assert (E425 : reg_get regs4 25 = reg_get regs0 25) by r_rp Hrp4 Hx3 25.
  assert (E426 : reg_get regs4 26 = reg_get regs0 26) by r_rp Hrp4 Hx3 26.
  assert (E427 : reg_get regs4 27 = reg_get regs0 27) by r_rp Hrp4 Hx3 27.
  (* ---- the epilogue, 0x14e64-0x14e80: ra and s0-s4 back, sp + 128, ret ---- *)
  apply (r_run (mkFP (@fp_regs fx) (@fp_csr fx)) regs4 (Z_to_bv 64 R_FREE_RET) mem4 md4
    (fun ms => exists R, ms = MS R (@fp_regs fx) (ret_pc (YK11.getr regs0 1)) (@fp_csr fx) None mem4 (seg_rom rsegs) /\
       forall x, callee_saved x -> reg_get R (Z_to_bv 5 x) = YK11.getr regs0 (Z_to_bv 5 x)));
    [exact Hh4 | exact Hl4 | | |].
  { unfold Regs6ss.mkR_of. rewrite E42, E43, E44, E421, E422, E423, E424, E425, E426, E427. unfold R_FREE_RET.
    set (spw := Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) in *.
    do 8 step.
    apply evt_done. eexists. split; [reflexivity|].
    intros x Hx. unfold callee_saved in Hx.
    assert (Hc : x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ x = 9 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/
                 x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27) by lia.
    destruct Hc as [->|Hc]; [|repeat (destruct Hc as [-> | Hc]; [reflexivity|]); subst x; reflexivity].
    change (Z_to_bv 64 (bv_unsigned spw + 128) = YK11.getr regs0 (Z_to_bv 5 2)).
    rewrite Usp. replace (bv_unsigned (reg_get regs0 2) - 128 + 128) with (bv_unsigned (reg_get regs0 2)) by lia.
    apply Z_to_bv_bv_unsigned. }
  { intros ms (R2 & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R2 & HE & Hcs) regs5 Hx5.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  apply SR_ret.
  assert (RP : regs_preserved regs0 regs5).
  { intros x Hx. rewrite (sr_getr_eqv _ _ _ Hx5), r_getr_cs by exact Hx. exact (Hcs x Hx). }
  (* ---- receive_ret ---- *)
  unfold receive_ret. exists fa, Bw'.
  split; [exact Haddr|]. split; [lia|]. split; [exact Hnimg|]. split; [exact MODfa|].
  unfold h_post. exists (mkFP (@fp_regs fx) (@fp_csr fx)), L2, A2, regs5, mem4, md4.
  split; [rewrite (sr_ret_pc _ Hra0), SEGS; reflexivity|].
  split; [exact Hfrm|].
  split; [apply (sr_post B API receive_FRAME _ L0 A0 regs0 mem0 md0 L2 A2 regs5 mem4 md4 FR4 RP);
          intros a Ha; [left; exact Ha | right; right; exact Ha]|].
  split; [exact HID4|].
  split; [exact Hh4|]. split; [exact Hl4|].
  split.
  { rewrite Ec2, Eb2.
    assert (Hnb : ~ In (fa, Z.max 1 (Z.of_nat (length bytes))) (b1 ++ b2))
      by (apply (sr_nonempty_not_twice b1 b2 fa _ PW); lia).
    assert (Hnc : ~ In (fa, Z.max 1 (Z.of_nat (length bytes))) (c1 ++ c2))
      by (apply (sr_nonempty_not_twice c1 c2 fa _); [rewrite <- Ec1, Eb1; exact PW | lia]).
    destruct (sr_app_mid_inv (fa, Z.max 1 (Z.of_nat (length bytes))) b1 b2 c1 c2
                ltac:(intros H; apply Hnb; apply in_or_app; left; exact H)
                ltac:(intros H; apply Hnc; apply in_or_app; left; exact H)
                ltac:(rewrite <- Eb1, <- Ec1; reflexivity)) as [-> ->].
    reflexivity. }
  split; [intros q k Hq; exact (proj1 (Hub4 q k Hq))|].
  split; [exact Hlen4|].
  split; [rewrite sb_free_malloc in Hres4; exact Hres4|].
  split; [rewrite SEGS; exact Hro4|].
  split; [exact Hgd4|].
  split; [exact WM4|].
  split; [exact GFb|].
  intros i Hi. rewrite <- (RI0 i Hi).
  destruct (RELRO (RELRO_BASE + i) ltac:(lia)) as (H1 & H2 & H3 & H4).
  pose proof (proj1 (Himg4 (RELRO_BASE + i) H1 H2 H3 H4
                ltac:(unfold h_world, RELRO_BASE, RELRO_LEN, W_BASE_UBSAN in *; lia))) as E.
  rewrite SEGS in E. exact E.
Qed.

(* r_run with SRcf (U/AgreeLift.v evt_SRcf_canon). *)
Lemma r_run_cf : forall (Bm : malloc_syms) (fx' : FPState) regs pc mem md (Q : machine_state -> Prop)
    (P : config -> Prop),
  ms_segs Bm = rsegs -> m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs Q (MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m', Q (MS R F pc' fc None m' (seg_rom rsegs)) ->
     forall regs', Regs6ss.xregs_eqv R regs' ->
     SRcf Bm (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (YK11.seg_rom rsegs)) md) P) ->
  SRcf Bm (mkCfg (@YK11.mkst fx' regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros Bm fx' regs pc mem md Q P HS Hh Hl HE Hform HK.
  pose proof (evt_SRcf_canon Bm) as EC. cbv zeta in EC. rewrite HS in EC.
  apply (EC _ Q md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & HQ & Heq). destruct (Hform can HQ) as (R & F & pc' & fc & m' & ->).
  destruct (sr_eqv_mkst R F pc' fc m' (seg_rom rsegs) ms' Heq) as [Ems Hx]. rewrite Ems.
  exact (HK R F pc' fc m' HQ _ Hx).
Qed.

(* The cut-free (SRcf) form, for ubsan_agrees: the same walk with the allocator's _cf contracts and the
   glue's _cf steps. *)
Theorem receive_holds_cf : forall {fx : FPState} {rc : RunCeil} (B : malloc_syms) (API : AllocAPI B),
  (forall fx', @malloc_contract_cf fx' rc B API) -> (forall fx', @free_contract_cf fx' rc B API) ->
  memset_contract -> memcpy_contract -> spec_read_frame_contract -> diginet_session_poll_contract ->
  m_rx_contract -> diginet_session_rx_contract -> settle_contract -> @receive_contract_cf fx rc B API.
Proof.
  intros fx rc B API MALLOC FREE MSET MCPY SRF POLL MRX RXC SET.
  unfold receive_contract_cf.
  intros BI L0 A0 regs0 mem0 md0 b Bw p bytes by_poll pf Hpre Hfrm Hargs Hroom.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX & ERRNO & CTXLO & WORLD & RELRO).
  pose proof Hpre as (Hcall & HID & Hhalt0 & Hlazy0 & Hro0 & Hres0 & Hwos0 & WM0 & GF0 & RI0).
  pose proof Hcall as (HM0 & HW0 & HB0 & Hra0 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & _).
  pose proof Hargs as (E10 & E11 & E12 & Hbp & Epf & Rpf & Hn65 & Hblk & Hsrc & Hmod).
  rewrite SEGS in Hro0.
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (HRF : receive_FRAME = 8320) by reflexivity.
  assert (Hn0 : 0 <= Z.of_nat (length bytes)) by lia.
  assert (Esp0 : spZ regs0 = bv_unsigned (reg_get regs0 2)) by reflexivity.
  pose proof (bv_unsigned_in_range 64 (reg_get regs0 2)) as Rsp0. unfold bv_modulus in Rsp0.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp0.
  pose proof (sr_fr_init B API SEGS receive_FRAME L0 A0 regs0 mem0 md0 b Bw Hpre) as FR0.
  (* ---- the entry, 0x14d1c-0x14d50 ---- *)
  assert (ST0 : stk rsegs (normalize rsegs mem0) (spZ regs0 - receive_FRAME) (bv_unsigned (reg_get regs0 2))).
  { apply (norm_stk B SEGS); [exact Hro0 | unfold SR_RES_TOP; lia | lia |]. intros a Ha. apply Hstw0. lia. }
  pose proof (sr_wmem_norm mem0 Bw Hro0 WM0) as WMn0.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG WORLD) with (stk := receive_FRAME) (S := spZ regs0) (L0 := L0) (A0 := A0)
    (mem0 := mem0) (md0 := md0) (L := L0) (A := A0)
    (Q := q_mal (@fp_regs fx) (@fp_csr fx) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 8)
            (reg_get regs0 11) (reg_get regs0 12) (reg_get regs0 13) (reg_get regs0 21) (reg_get regs0 22)
            (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27)
            (normalize rsegs mem0) (bv_unsigned (reg_get regs0 2) - 128) (spZ regs0 - receive_FRAME) p
            (Z.of_nat (length bytes))
            [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18); C8 (reg_get regs0 9);
             C8 (reg_get regs0 8); C8 (reg_get regs0 1)] Bw).
  { exact FR0. }
  { lia. }
  { lia. }
  { unfold Regs6ss.mkR_of. rewrite (E10 : reg_get regs0 10 = Z_to_bv 64 p).
    eapply r_entry;
      [ exact ST0 | lia | apply mem_inv_normalize | lia | exact E11 | lia | exact WMn0
      | unfold W_BASE_UBSAN, W_LEN; lia ]. }
  { intros ms HQ.
    destruct HQ as (t0' & t1' & t2' & x11 & x12 & x13 & x14 & x15 & x16 & x17 & t3' & t4' & t5' & t6' & m' & j
                    & -> & MU & WMo & _).
    do 5 eexists. exists [(bv_unsigned (reg_get regs0 2) - 128, bv_unsigned (reg_get regs0 2) - 128 + 128)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WMo|].
    intros x Hx NO. left. cbn [outside] in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (t0' & t1' & t2' & x11 & x12 & x13 & x14 & x15 & x16 & x17 & t3' & t4' & t5' & t6' & mq & j
                  & HE & MU1 & WMo1 & MI1 & ST1 & RW1 & WMq).
  injection HE as ER EF EP EC EM. subst R F pc' fc. subst m0'.
  assert (G11 : YK11.getr regs1 1 = Z_to_bv 64 R_MALLOC_RET) by r_g Hx1.
  assert (G12 : YK11.getr regs1 2 = Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) by r_g Hx1.
  assert (G14 : YK11.getr regs1 4 = reg_get regs0 4) by r_g Hx1.
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 (Z.max 1 (Z.of_nat (length bytes)))) by r_g Hx1.
  assert (Hsp1 : spZ regs1 = spZ regs0 - 128) by (unfold spZ at 1; rewrite G12; rewrite unsigned_lit by lia; lia).
  (* ---- malloc (n ? n : 1) ---- *)
  rewrite <- SEGS, <- HMAL.
  eapply (g_malloc_cf B API SEGS AX ERRNO WORLD RELRO) with (stk := receive_FRAME) (S := spZ regs0) (L0 := L0)
    (A0 := A0) (mem0 := mem0) (md0 := md0) (n := Z.max 1 (Z.of_nat (length bytes))) (bres := b).
  { exact MALLOC. }
  { exact FR1. }
  { lia. }
  { lia. }
  { rewrite G11. apply ret_ok_even. reflexivity. }
  { rewrite Hsp1. Z.div_mod_to_equations. lia. }
  { rewrite Hsp1. unfold ALLOC_STACK. lia. }
  { lia. }
  { lia. }
  { rewrite G14. exact Htp0. }
  { exact G110. }
  { exact Hres0. }
  { exact Hroom. }
  intros L1 A1 regs2 mem2 md2 fa FR2 Hrp2 G210 Hfa1 Hfa2 Hfa16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2
    Hsrk2.
  rewrite G11, SEGS.
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & Hmd2 & Hhigh2 & Himg2 & Hub2 & Hbyt2 & Hstw2 & Herr2 & Hgd2 & Hro2
                     & Hle2 & Hlen2).
  assert (Haddr : h_addr_ok fa) by (unfold h_addr_ok; lia).
  destruct (receive_m timg_ubsan Bw fa bytes by_poll pf) as [[Bw' []]|] eqn:MODfa;
    [| exfalso; exact (Hmod fa Haddr MODfa)].
  (* the heap frame: born here, apart from every entry block, off the world and .data.rel.ro *)
  assert (Hin1 : In (fa, Z.max 1 (Z.of_nat (length bytes))) (blocks L1 A1))
    by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (PW : pairwise ranges_disjoint (b1 ++ (fa, Z.max 1 (Z.of_nat (length bytes))) :: b2))
    by (rewrite <- Eb1; exact (mr_blocks_disjoint B _ (aa_laws API) L1 A1 mem2 md2 HM2)).
  assert (MINE : forall a k, In (a, k) (blocks L0 A0) -> a + k <= fa \/ fa + Z.max 1 (Z.of_nat (length bytes)) <= a).
  { intros a k Hak. rewrite Eb2 in Hak. pose proof (sr_disj_mid b1 _ b2 (a, k) PW Hak) as H. cbn [fst snd] in H.
    lia. }
  assert (OWfa : off_world fa (Z.max 1 (Z.of_nat (length bytes)))).
  { unfold off_world. apply (r_off_img B fa _ W_BASE_UBSAN W_LEN); [lia | unfold W_LEN; lia | exact Hnimg |].
    intros j0 Hj. exact (proj1 (WORLD (W_BASE_UBSAN + j0) ltac:(unfold h_world; lia))). }
  assert (RLfa : fa + Z.max 1 (Z.of_nat (length bytes)) <= RELRO_BASE \/ RELRO_BASE + RELRO_LEN <= fa).
  { apply (r_off_img B fa _ RELRO_BASE RELRO_LEN); [lia | unfold RELRO_LEN; lia | exact Hnimg |].
    intros j0 Hj. exact (proj1 (RELRO (RELRO_BASE + j0) ltac:(lia))). }
  (* the n source bytes, kept from the entry (an entry block, or above the caller's sp) *)
  assert (FP2 : Z.of_nat (length bytes) <> 0 -> bytes_at rsegs (normalize rsegs mem2) p bytes).
  { intros Hn. apply bytes_at_normalize; [exact Hro2|].
    destruct Hsrc as [Hz | (Hpo & [(q & k & Hq & Hq1 & Hq2) | (Hs1 & Hs2)])]; [contradiction | |].
    - assert (Hb : In (ptr_addr L0 q, k) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
      pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q k HM0 Hq) as (R1 & R2).
      apply (r_blk_bytes B mem2 p bytes SEGS); [lia | lia |].
      intros i Hi. rewrite <- (Hblk i Hi).
      replace (p + i) with (ptr_addr L0 q + (p + i - ptr_addr L0 q)) by lia.
      apply (Hbyt2 (ptr_addr L0 q) k); [exact Hb | lia].
    - apply (r_blk_bytes B mem2 p bytes SEGS); [lia | lia |].
      intros i Hi. rewrite <- (Hblk i Hi).
      apply (proj1 (Hhigh2 (p + i) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }
  assert (DISJ : Z.of_nat (length bytes) = 0 \/ p + Z.of_nat (length bytes) <= fa \/
                 fa + Z.of_nat (length bytes) <= p).
  { destruct Hsrc as [Hz | (Hpo & [(q & k & Hq & Hq1 & Hq2) | (Hs1 & Hs2)])]; [left; exact Hz | right | right].
    - assert (Hb : In (ptr_addr L0 q, k) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
      destruct (MINE _ _ Hb); lia.
    - right. lia. }
  destruct (norm_blk B API SEGS AX L1 A1 mem2 md2 fa (Z.max 1 (Z.of_nat (length bytes))) HM2 Hin1 ltac:(lia) Hro2)
    as [junk FC].
  (* receive's frame, the world and .data.rel.ro on the normalized memory after malloc *)
  pose proof (sr_rw_cells_rel m1 _ _ _ Hrel1 RW1) as RW1'.
  assert (RW2 : rw_cells rsegs mem2 (bv_unsigned (reg_get regs0 2) - 128)
                  (CB 80 j :: [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
                               C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)])).
  { apply (sr_rw_cells_frame m1 mem2 _ _ RW1'). intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    pose proof (Habove2 a ltac:(rewrite Hsp1; lia)) as E. rewrite SEGS in E. exact E. }
  assert (RW3 : rw_cells rsegs (normalize rsegs mem2) (bv_unsigned (reg_get regs0 2) - 128)
                  (CB 80 j :: [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
                               C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)])).
  { apply (sr_rw_cells_norm B mem2 _ _ SEGS Hro2); [|exact RW2]. intros i Hi Himg.
    pose proof (sr_in_img_top B _ SEGS Himg). unfold SR_RES_TOP in *. cbn [cells_size csize Nat.add] in Hi. lia. }
  assert (EB80 : bv_unsigned (reg_get regs0 2) - 128 + 80 =
                 bv_unsigned (reg_get regs0 2) - 128 + Z.of_nat (cells_size [CB 80 j]))
    by (change (Z.of_nat (cells_size [CB 80 j])) with 80; reflexivity).
  destruct (r_cells_split2 _ (bv_unsigned (reg_get regs0 2) - 128) (bv_unsigned (reg_get regs0 2) - 128 + 80) [CB 80 j]
              [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
               C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)] RW3 EB80) as [SF SV].
  assert (ST2 : stk rsegs (normalize rsegs mem2) (spZ regs0 - receive_FRAME) (bv_unsigned (reg_get regs0 2) - 128)).
  { apply (norm_stk B SEGS); [exact Hro2 | unfold SR_RES_TOP; lia | lia |]. intros a Ha. apply Hstw2. lia. }
  pose proof (sr_wmem_back m1 _ Bw Hrel1 WMq) as WM1.
  assert (WM2 : wmem rsegs mem2 Bw).
  { apply (sr_rw_cells_frame m1 mem2 _ _ WM1). intros a Ha. rewrite wm_size in Ha.
    pose proof (Hsrk2 a (or_introl Ha)) as E. rewrite SEGS in E. exact E. }
  pose proof (sr_wmem_norm mem2 Bw Hro2 WM2) as WMn2.
  assert (RI2 : relro_img mem2).
  { intros i Hi. rewrite <- (RI0 i Hi).
    destruct (RELRO (RELRO_BASE + i) ltac:(lia)) as (H1 & H2 & H3 & H4).
    pose proof (proj1 (Himg2 (RELRO_BASE + i) H1 H2 H3 H4
                  ltac:(unfold h_world, RELRO_BASE, RELRO_LEN, W_BASE_UBSAN in *; lia))) as E.
    rewrite SEGS in E. exact E. }
  pose proof (sr_relro_norm mem2 Hro2 RI2) as RIn2.
  (* the registers after malloc *)
  assert (E22 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) by r_rp Hrp2 Hx1 2.
  assert (E23 : reg_get regs2 3 = reg_get regs0 3) by r_rp Hrp2 Hx1 3.
  assert (E24 : reg_get regs2 4 = reg_get regs0 4) by r_rp Hrp2 Hx1 4.
  assert (E28 : reg_get regs2 8 = reg_get regs0 8) by r_rp Hrp2 Hx1 8.
  assert (E29 : reg_get regs2 9 = reg_get regs0 11) by r_rp Hrp2 Hx1 9.
  assert (E210 : reg_get regs2 10 = Z_to_bv 64 fa) by exact G210.
  assert (E218 : reg_get regs2 18 = reg_get regs0 13) by r_rp Hrp2 Hx1 18.
  assert (E219 : reg_get regs2 19 = reg_get regs0 12) by r_rp Hrp2 Hx1 19.
  assert (E220 : reg_get regs2 20 = Z_to_bv 64 p) by r_rp Hrp2 Hx1 20.
  assert (E221 : reg_get regs2 21 = reg_get regs0 21) by r_rp Hrp2 Hx1 21.
  assert (E222 : reg_get regs2 22 = reg_get regs0 22) by r_rp Hrp2 Hx1 22.
  assert (E223 : reg_get regs2 23 = reg_get regs0 23) by r_rp Hrp2 Hx1 23.
  assert (E224 : reg_get regs2 24 = reg_get regs0 24) by r_rp Hrp2 Hx1 24.
  assert (E225 : reg_get regs2 25 = reg_get regs0 25) by r_rp Hrp2 Hx1 25.
  assert (E226 : reg_get regs2 26 = reg_get regs0 26) by r_rp Hrp2 Hx1 26.
  assert (E227 : reg_get regs2 27 = reg_get regs0 27) by r_rp Hrp2 Hx1 27.
  assert (Usp : bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) = bv_unsigned (reg_get regs0 2) - 128)
    by (apply unsigned_lit; lia).
  (* ---- the body, 0x14d54-0x14e60 ---- *)
  eapply (g_run_cf B API SEGS AX HGG WORLD) with (stk := receive_FRAME) (S := spZ regs0) (L0 := L0) (A0 := A0)
    (mem0 := mem0) (md0 := md0) (L := L1) (A := A1)
    (Q := q_body (@fp_regs fx) (@fp_csr fx) (Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) (reg_get regs0 3)
            (reg_get regs0 4) (reg_get regs0 21) (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24)
            (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) (normalize rsegs mem2) fa
            (Z.of_nat (length bytes))
            [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18); C8 (reg_get regs0 9);
             C8 (reg_get regs0 8); C8 (reg_get regs0 1)] Bw').
  { exact FR2. }
  { lia. }
  { lia. }
  { unfold Regs6ss.mkR_of.
    rewrite E22, E23, E24, E28, E29, E210, E218, E219, E220, E221, E222, E223, E224, E225, E226, E227.
    rewrite (E11 : reg_get regs0 11 = Z_to_bv 64 (Z.of_nat (length bytes))).
    rewrite (E12 : reg_get regs0 12 = Z_to_bv 64 by_poll).
    eapply (r_body MSET MCPY SRF POLL MRX RXC SET) with (lo := spZ regs0 - receive_FRAME) (j80 := j) (junk := junk)
      (Bw := Bw);
      [ exact Hbp | exact Epf | exact Rpf | exact MODfa | exact GF0
      | exact FP2 | exact DISJ | lia | lia | unfold W_BASE_UBSAN, W_LEN; lia | exact OWfa | exact FC
      | exact RIn2 | exact RLfa
      | rewrite Usp; Z.div_mod_to_equations; lia | rewrite Usp; exact ST2 | rewrite Usp; lia
      | unfold w_off_stack; rewrite Usp; unfold W_BASE_UBSAN, W_LEN; lia | apply mem_inv_normalize | exact WMn2
      | rewrite Usp; exact SF | rewrite Usp; exact SV
      | apply munch_refl | apply wmono_refl ]. }
  { intros ms HQ.
    destruct HQ as (z0 & z1 & z2 & o0 & o1 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & o2 & o3 & o4
                    & z3 & z4 & z5 & z6 & m' & -> & MU & WMo & _).
    do 5 eexists. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WMo|].
    intros x Hx NO. cbn [outside] in NO. rewrite Usp in NO.
    assert (Hcase : (spZ regs0 - receive_FRAME <= x < spZ regs0) \/ h_world x \/
                    (fa <= x < fa + Z.max 1 (Z.of_nat (length bytes)))) by (unfold h_world; lia).
    destruct Hcase as [Hc | [Hc | Hc]]; [left; exact Hc | right; left; exact Hc | right; right].
    exists fa, (Z.max 1 (Z.of_nat (length bytes))). split; [|exact Hc].
    split; [exact Hin1|]. split; [lia|]. exact MINE. }
  intros R F pc' fc m0'' HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as (z0 & z1 & z2 & o0 & o1 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & o2 & o3 & o4
                  & z3 & z4 & z5 & z6 & mq3 & HE & MU3 & WMo3 & SV3 & WMb & GFb).
  injection HE as ER EF EP EC EM. subst R F pc' fc. subst m0''.
  assert (G31 : YK11.getr regs3 1 = Z_to_bv 64 R_FREE_RET) by r_g Hx3.
  assert (G32 : YK11.getr regs3 2 = Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) by r_g Hx3.
  assert (G34 : YK11.getr regs3 4 = reg_get regs0 4) by r_g Hx3.
  assert (G310 : YK11.getr regs3 10 = Z_to_bv 64 fa) by r_g Hx3.
  assert (Hsp3 : spZ regs3 = spZ regs0 - 128) by (unfold spZ at 1; rewrite G32; rewrite unsigned_lit by lia; lia).
  (* ---- free (frame) ---- *)
  rewrite <- SEGS, <- HFRE.
  eapply (g_free_cf B API SEGS AX ERRNO WORLD RELRO) with (stk := receive_FRAME) (S := spZ regs0) (L0 := L0)
    (A0 := A0) (mem0 := mem0) (md0 := md0) (x := fa) (n := Z.max 1 (Z.of_nat (length bytes)))
    (bres := sb_malloc b (Z.max 1 (Z.of_nat (length bytes)))).
  { exact FREE. }
  { exact FR3. }
  { lia. }
  { lia. }
  { rewrite G31. apply ret_ok_even. reflexivity. }
  { rewrite Hsp3. Z.div_mod_to_equations. lia. }
  { rewrite Hsp3. unfold ALLOC_STACK. lia. }
  { lia. }
  { lia. }
  { rewrite G34. exact Htp0. }
  { exact G310. }
  { exact Hin1. }
  { lia. }
  { exact MINE. }
  { exact Hres2. }
  intros L2 A2 regs4 mem4 md4 FR4 Hrp4 (c1 & c2 & Ec1 & Ec2) Hres4 Habove4 Hkept4 Hsrk4.
  rewrite G31, SEGS.
  pose proof FR4 as (HM4 & HW4 & HB4 & HID4 & Hmd4 & Hhigh4 & Himg4 & Hub4 & Hbyt4 & Hstw4 & Herr4 & Hgd4 & Hro4
                     & Hle4 & Hlen4).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM4) as (Hh4 & Hl4 & _).
  pose proof (sr_rw_cells_rel m3 _ _ _ Hrel3 SV3) as SV3'.
  assert (SV4 : rw_cells rsegs mem4 (bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) + 80)
                  [C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
                   C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)]).
  { apply (sr_rw_cells_frame m3 mem4 _ _ SV3'). intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    pose proof (Habove4 a ltac:(rewrite Hsp3; lia)) as E. rewrite SEGS in E. exact E. }
  pose proof (sr_wmem_back m3 _ Bw' Hrel3 WMb) as WM3.
  assert (WM4 : wmem rsegs mem4 Bw').
  { apply (sr_rw_cells_frame m3 mem4 _ _ WM3). intros a Ha. rewrite wm_size in Ha.
    pose proof (Hsrk4 a (or_introl Ha)) as E. rewrite SEGS in E. exact E. }
  assert (E42 : reg_get regs4 2 = Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) by r_rp Hrp4 Hx3 2.
  assert (E43 : reg_get regs4 3 = reg_get regs0 3) by r_rp Hrp4 Hx3 3.
  assert (E44 : reg_get regs4 4 = reg_get regs0 4) by r_rp Hrp4 Hx3 4.
  assert (E421 : reg_get regs4 21 = reg_get regs0 21) by r_rp Hrp4 Hx3 21.
  assert (E422 : reg_get regs4 22 = reg_get regs0 22) by r_rp Hrp4 Hx3 22.
  assert (E423 : reg_get regs4 23 = reg_get regs0 23) by r_rp Hrp4 Hx3 23.
  assert (E424 : reg_get regs4 24 = reg_get regs0 24) by r_rp Hrp4 Hx3 24.
  assert (E425 : reg_get regs4 25 = reg_get regs0 25) by r_rp Hrp4 Hx3 25.
  assert (E426 : reg_get regs4 26 = reg_get regs0 26) by r_rp Hrp4 Hx3 26.
  assert (E427 : reg_get regs4 27 = reg_get regs0 27) by r_rp Hrp4 Hx3 27.
  (* ---- the epilogue, 0x14e64-0x14e80: ra and s0-s4 back, sp + 128, ret ---- *)
  apply (r_run_cf B (mkFP (@fp_regs fx) (@fp_csr fx)) regs4 (Z_to_bv 64 R_FREE_RET) mem4 md4
    (fun ms => exists R, ms = MS R (@fp_regs fx) (ret_pc (YK11.getr regs0 1)) (@fp_csr fx) None mem4 (seg_rom rsegs) /\
       forall x, callee_saved x -> reg_get R (Z_to_bv 5 x) = YK11.getr regs0 (Z_to_bv 5 x)));
    [exact SEGS | exact Hh4 | exact Hl4 | | |].
  { unfold Regs6ss.mkR_of. rewrite E42, E43, E44, E421, E422, E423, E424, E425, E426, E427. unfold R_FREE_RET.
    set (spw := Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 128)) in *.
    do 8 step.
    apply evt_done. eexists. split; [reflexivity|].
    intros x Hx. unfold callee_saved in Hx.
    assert (Hc : x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ x = 9 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/
                 x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27) by lia.
    destruct Hc as [->|Hc]; [|repeat (destruct Hc as [-> | Hc]; [reflexivity|]); subst x; reflexivity].
    change (Z_to_bv 64 (bv_unsigned spw + 128) = YK11.getr regs0 (Z_to_bv 5 2)).
    rewrite Usp. replace (bv_unsigned (reg_get regs0 2) - 128 + 128) with (bv_unsigned (reg_get regs0 2)) by lia.
    apply Z_to_bv_bv_unsigned. }
  { intros ms (R2 & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R2 & HE & Hcs) regs5 Hx5.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  apply (SRcf_ret B).
  assert (RP : regs_preserved regs0 regs5).
  { intros x Hx. rewrite (sr_getr_eqv _ _ _ Hx5), r_getr_cs by exact Hx. exact (Hcs x Hx). }
  (* ---- receive_ret ---- *)
  unfold receive_ret. exists fa, Bw'.
  split; [exact Haddr|]. split; [lia|]. split; [exact Hnimg|]. split; [exact MODfa|].
  unfold h_post. exists (mkFP (@fp_regs fx) (@fp_csr fx)), L2, A2, regs5, mem4, md4.
  split; [rewrite (sr_ret_pc _ Hra0), SEGS; reflexivity|].
  split; [exact Hfrm|].
  split; [apply (sr_post B API receive_FRAME _ L0 A0 regs0 mem0 md0 L2 A2 regs5 mem4 md4 FR4 RP);
          intros a Ha; [left; exact Ha | right; right; exact Ha]|].
  split; [exact HID4|].
  split; [exact Hh4|]. split; [exact Hl4|].
  split.
  { rewrite Ec2, Eb2.
    assert (Hnb : ~ In (fa, Z.max 1 (Z.of_nat (length bytes))) (b1 ++ b2))
      by (apply (sr_nonempty_not_twice b1 b2 fa _ PW); lia).
    assert (Hnc : ~ In (fa, Z.max 1 (Z.of_nat (length bytes))) (c1 ++ c2))
      by (apply (sr_nonempty_not_twice c1 c2 fa _); [rewrite <- Ec1, Eb1; exact PW | lia]).
    destruct (sr_app_mid_inv (fa, Z.max 1 (Z.of_nat (length bytes))) b1 b2 c1 c2
                ltac:(intros H; apply Hnb; apply in_or_app; left; exact H)
                ltac:(intros H; apply Hnc; apply in_or_app; left; exact H)
                ltac:(rewrite <- Eb1, <- Ec1; reflexivity)) as [-> ->].
    reflexivity. }
  split; [intros q k Hq; exact (proj1 (Hub4 q k Hq))|].
  split; [exact Hlen4|].
  split; [rewrite sb_free_malloc in Hres4; exact Hres4|].
  split; [rewrite SEGS; exact Hro4|].
  split; [exact Hgd4|].
  split; [exact WM4|].
  split; [exact GFb|].
  intros i Hi. rewrite <- (RI0 i Hi).
  destruct (RELRO (RELRO_BASE + i) ltac:(lia)) as (H1 & H2 & H3 & H4).
  pose proof (proj1 (Himg4 (RELRO_BASE + i) H1 H2 H3 H4
                ltac:(unfold h_world, RELRO_BASE, RELRO_LEN, W_BASE_UBSAN in *; lia))) as E.
  rewrite SEGS in E. exact E.
Qed.
