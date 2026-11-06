(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 470 of its 484 lines of code are new or changed and 46 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import
  memset_c memcpy_c check_personality_c diginet_personality_of_c text_arg_c check_text_scribble_c
  diginet_scribble_encode_c check_text_seg7_c check_text_counter_c owed_counter_text_c diginet_sysex_encode_c
  diginet_jog_encode_c diginet_counter_encode_c diginet_touch_encode_c diginet_vpot_encode_c
  diginet_strip_leds_encode_c diginet_fader_encode_c diginet_button_encode_c diginet_ring_encode_c
  diginet_meter_encode_c diginet_counter_leds_encode_c check_refusal_c check_range_c check_bytes_c
  check_text_masks_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_contract_sat.
Import ListNotations.
Open Scope Z_scope.

(** The walk of LLVMFuzzerTestOneInput (fuzz_codec.c:556-658; 6084 bytes at 0x13228 in the plain image) is cut
    at the pcs below; each cut has a predicate [X_ok] saying "every machine state at pc X of this shape
    eventually reaches the contract's post [Qk]", and each segment lemma [S_X] proves [X_ok] from the
    predicates of the cuts the segment reaches (continuation style, so the segments are proved apart).

    Frame (sp' = entry sp - 0x190 = FP; all offsets from FP):
      0x000 8   constant 0x5cb0 (bytes B0 5C, JOG's command head)
      0x008 8   constant 0x13f0 (bytes F0 13, the sysex head)
      0x010 184 struct call k (codec_cells.kcall_cells)
      0x0c8 8   in.p (the input cursor, p + c)
      0x0d0 8   in.n (the bytes left); not stored before the loop: at HEAD it is in s5
      0x0d8 80  5 unused bytes, char text[65] at 0x0dd, the dots byte / owe()'s pl[10] at 0x11e
      0x128 104 s11 .. s0, ra of the caller (saved)
    Registers at every cut inside the loop (set at 0x13284-0x132c4, callee-saved by every callee):
      s0 = FP + 0x5c (&k.before), s1 = 0x1f1f0 (SPEC_DESK), s2 = 9, s3 = 0xfe, s4 = 0xd, s6 = ops,
      s7 = FP + 0xb8 (&k.want_len), s9 = FP + 0x40 (&k.bytes[8]), s11 = 0x104d4 (DESK).
    Cuts: ENTRY 0x13228, HEAD 0x132c8 (loop head), RDk = T1[k] (k = 0..13) / 0x139a8 (k = 14, MASKS),
    ENC9 0x13560 (scribble_encode call), ENC10 0x13c4c (counter_encode call), JOIN 0x1435c (encoder
    returned; owe() starts), OWEk = T3[k] (k = 0..10) / 0x1483c (k = 11, SYSEX), CHK 0x14808 (the three
    checks), LATCH 0x14828 (ops test) and LATCH2 0x1482c (in.n test), EXIT 0x149ac (epilogue). *)

(** ---- the entry values ---- *)

Record env := mkEnv {
  e_ra : word; e_sp : word; e_gp : word; e_tp : word;
  e_s0 : word; e_s1 : word; e_s2 : word; e_s3 : word; e_s4 : word; e_s5 : word;
  e_s6 : word; e_s7 : word; e_s8 : word; e_s9 : word; e_s10 : word; e_s11 : word;
  e_F : bvmap 5 word; e_fc : bv 32; e_m : word -> option byte; e_lo : Z;
  e_p : word; e_data : list byte }.

(** The premises of codec_main_contract on the entry values (a0 = p, a1 = length data), with the
    disjointness of the stack window and the RELRO tables. *)
Definition env_ok (e : env) : Prop :=
  bytes_at rsegs (e_m e) (bv_unsigned (e_p e)) (e_data e) /\
  mem_inv rsegs (e_m e) /\
  stk rsegs (e_m e) (e_lo e) (bv_unsigned (e_sp e)) /\
  e_lo e + LLVM_CODEC_STACK <= bv_unsigned (e_sp e) /\
  bv_unsigned (e_sp e) mod 16 = 0 /\
  (bv_unsigned (e_p e) + Z.of_nat (length (e_data e)) <= e_lo e \/ bv_unsigned (e_sp e) <= bv_unsigned (e_p e)) /\
  bv_unsigned (e_p e) + Z.of_nat (length (e_data e)) < 2 ^ 63 /\
  relro_img (e_m e) /\
  disj (e_lo e) (bv_unsigned (e_sp e) - e_lo e) RELRO_BASE RELRO_LEN.

(** The post of codec_main_contract. *)
Definition Qk (e : env) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR (e_ra e) (e_sp e) (e_gp e) (e_tp e) t0' t1' t2' (e_s0 e) (e_s1 e) (Z_to_bv 64 0)
                  a1' a2' a3' a4' a5' a6' a7'
                  (e_s2 e) (e_s3 e) (e_s4 e) (e_s5 e) (e_s6 e) (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e) (e_s11 e)
                  t3' t4' t5' t6')
             (e_F e) (ret_pc (e_ra e)) (e_fc e) None m' (seg_rom rsegs) /\
    munch [(bv_unsigned (e_sp e) - LLVM_CODEC_STACK, bv_unsigned (e_sp e))] (e_m e) m' /\
    wmono rsegs (e_m e) m' /\
    mem_inv rsegs m' /\
    stk rsegs m' (e_lo e) (bv_unsigned (e_sp e)).

(** The prologue's saves, at FP + 0x128 = entry sp - 104. *)
Definition saved (e : env) : list cell :=
  [C8 (e_s11 e); C8 (e_s10 e); C8 (e_s9 e); C8 (e_s8 e); C8 (e_s7 e); C8 (e_s6 e); C8 (e_s5 e);
   C8 (e_s4 e); C8 (e_s3 e); C8 (e_s2 e); C8 (e_s1 e); C8 (e_s0 e); C8 (e_ra e)].

(** The memory facts every cut after the prologue has: the saves, the stack below the frame, and how m1
    relates to the entry memory. *)
Definition fr_ok (e : env) (m1 : word -> option byte) : Prop :=
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -104) (saved e) /\
  stk rsegs m1 (e_lo e) (bv_unsigned (e_sp e) + -400) /\
  munch [(bv_unsigned (e_sp e) - LLVM_CODEC_STACK, bv_unsigned (e_sp e))] (e_m e) m1 /\
  wmono rsegs (e_m e) m1 /\
  mem_inv rsegs m1.

(** The input cursor: c bytes consumed, rem left. *)
Definition cur_ok (e : env) (c rem : Z) : Prop :=
  0 <= c /\ 0 <= rem /\ c + rem = Z.of_nat (length (e_data e)).

(** The 296 bytes of the frame below the saves, at HEAD (k, in.n and the tail arbitrary). *)
Definition head_cells (e : env) (c : Z) (kj rj : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0); CB 184 kj;
   C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); CB 88 rj].

(** The 296 bytes of the frame below the saves inside an iteration: the call record k, in.p, in.n and
    the 80-byte tail (text, dots, pl[]). *)
Definition body_cells (e : env) (k : kcall) (c rem : Z) (tl : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0)] ++ kcall_cells k ++
  [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 tl].

(** The registers at a cut inside the loop: the invariant ones fixed, the others given. *)
Definition body_regs (e : env) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s8' s10' t3' t4' t5' t6' : word)
  : bvmap 5 word :=
  mkR ra' (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) (e_gp e) (e_tp e) t0' t1' t2'
      (Z_to_bv 64 (bv_unsigned (e_sp e) + -308)) (Z_to_bv 64 0x1f1f0)
      a0' a1' a2' a3' a4' a5' a6' a7'
      (Z_to_bv 64 9) (Z_to_bv 64 0xfe) (Z_to_bv 64 0xd) s5' s6'
      (Z_to_bv 64 (bv_unsigned (e_sp e) + -216)) s8' (Z_to_bv 64 (bv_unsigned (e_sp e) + -336)) s10'
      (Z_to_bv 64 0x104d4) t3' t4' t5' t6'.

(** The machine state at pc with registers R and memory m1. *)
Definition st (e : env) (R : bvmap 5 word) (pc : Z) (m1 : word -> option byte) : machine_state :=
  MS R (e_F e) (Z_to_bv 64 pc) (e_fc e) None m1 (seg_rom rsegs).

(** ---- the call record ---- *)

(** k.p and k.desk as HEAD sets them from DESK[op / 15 % 3] (and the text readers when k.p is NULL):
    personality_of(0..2) = NULL, &personalities[0], &personalities[1]; SPEC_DESK[0..2] = NULL, &SPEC_C24,
    &SPEC_PC; od the desk both describe. *)
Definition pd_ok (pv dv : Z) (od : option desk) : Prop :=
  (pv = 0 /\ dv = 0 /\ od = None) \/
  (pv = PERS /\ dv = 0x1f208 /\ od = Some c24) \/
  (pv = PERS + 24 /\ dv = 0x1f218 /\ od = Some pc).

Definition fz0 (n : nat) : list byte := repeat (b8 0) n.
Definition fa5 (n : nat) : list byte := repeat (b8 0xa5) n.

(** k as HEAD leaves it: memset to 0, kind, p and desk stored, before and out memset to 0xa5. *)
Definition k_rd (kind pv dv : Z) : kcall :=
  mkKcall kind (fz0 4) pv dv 0 0 0 0 (fz0 24) 0 0 (fa5 32) (fa5 32) 0 (fz0 24) 0 0 0.

(** The library call run() makes for k, owe()'s answer for k, and the reader widths of k. *)
Definition enc_k (k : kcall) (od : option desk) : Z * option cmd :=
  enc_of_call (k_kind k) od (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k).
Definition owe_k (k : kcall) (od : option desk) : Z * cmd :=
  owe_spec (k_kind k) od (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k).
Definition rdr_k (k : kcall) : Prop :=
  reader_ok (k_kind k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k).

(** The record after run(): a kind run() handles, the personality pair, reader widths, before = 0xa5^32
    and out = what the encoder wrote over 0xa5^32. *)
Definition rec_ok (k : kcall) (od : option desk) : Prop :=
  0 <= k_kind k <= 11 /\
  pd_ok (k_p k) (k_desk k) od /\
  rdr_k k /\
  k_before k = fa5 32 /\
  k_out k = cmd_out (fa5 32) (snd (enc_k k od)).

(** The want fields after owe(): want_rc its code; on success want[0..len), want_len, want_key,
    want_display its command; on failure want_len = want_key = want_display = 0. *)
Definition owe_want_ok (k : kcall) (od : option desk) : Prop :=
  k_want_rc k = fst (owe_k k od) /\
  (if fst (owe_k k od) =? 0 then
     let '(bs, key, dp) := snd (owe_k k od) in
     k_want_len k = Z.of_nat (length bs) /\ firstn (length bs) (k_want k) = bz bs /\
     k_want_key k = key /\ k_want_display k = dp
   else k_want_len k = 0 /\ k_want_key k = 0 /\ k_want_display k = 0).

(** ---- the cut predicates ---- *)

(** The fuel of the loop: at most 256 iterations, measured by 256 - ops. Body cuts are at fuel S f when
    the head they lead back to is at f. *)
Definition fuel_ok (ops : word) (n : nat) : Prop :=
  (Z.to_nat (256 - bv_unsigned ops) <= n)%nat /\ bv_unsigned ops <= 255.

(** EXIT 0x149ac: the epilogue (a0 = 0, restore s0..s11 and ra, sp += 0x190, ret). *)
Definition exit_ok (e : env) : Prop :=
  forall (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
          t3' t4' t5' t6' : word) (cs : list cell) (m1 : word -> option byte),
    cells_size cs = 296%nat ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) cs ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (mkR ra' (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) (e_gp e) (e_tp e) t0' t1' t2' x8 x9
                 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
          0x149ac m1).

(** HEAD 0x132c8: in.p = p + c stored, in.n = rem in s5 (rem >= 1), k and the rest of the frame arbitrary. *)
Definition head_ok (e : env) (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops : word)
         (c rem : Z) (kj rj : list byte) (m1 : word -> option byte),
    fuel_ok ops fuel ->
    1 <= rem -> cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (head_cells e c kj rj) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 rem) ops s8' s10' t3' t4' t5' t6')
          0x132c8 m1).

(** The pc of reader kind (kinds 0..13 through T1, MASKS = 14 the default). *)
Definition rd_pc (kind : Z) : Z := if kind =? 14 then 0x139a8 else nth (Z.to_nat kind) codec_T1 0.

(** RDk: after the op byte (cursor c, rem), k = k_rd kind p desk, a0 = kind (lw), s5 = k.p. *)
Definition rd_ok (e : env) (kind : Z) (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops : word)
         (pv dv : Z) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) ->
    pd_ok pv dv od -> cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e (k_rd kind pv dv) c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' (Z_to_bv 64 kind) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10'
                       t3' t4' t5' t6')
          (rd_pc kind) m1).

(** ENC9 0x13560: the SCRIBBLE call of run() (from the SCRIBBLE reader through T2, and from
    SCRIBBLE_TEXT): kind = 9, s5 = k.p, out = before = 0xa5^32. *)
Definition enc9_ok (e : env) (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops : word)
         (k : kcall) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) ->
    k_kind k = 9 -> pd_ok (k_p k) (k_desk k) od -> rdr_k k ->
    k_before k = fa5 32 -> k_out k = fa5 32 ->
    cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (k_p k)) ops s8' s10'
                       t3' t4' t5' t6')
          0x13560 m1).

(** ENC10 0x13c4c: the COUNTER call of run() (from the COUNTER reader through T2 after its lbu of k.b, and
    from COUNTER_TEXT): kind = 10, a0 = k.b (< 256), s5 = k.p, out = before = 0xa5^32. *)
Definition enc10_ok (e : env) (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops : word)
         (k : kcall) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) ->
    k_kind k = 10 -> pd_ok (k_p k) (k_desk k) od -> rdr_k k ->
    k_before k = fa5 32 -> k_out k = fa5 32 ->
    cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' (Z_to_bv 64 (k_b k)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (k_p k)) ops
                       s8' s10' t3' t4' t5' t6')
          0x13c4c m1).

(** JOIN 0x1435c: the encoder returned a0 = its code; k is the call record with out written (rec_ok);
    k.rc and the want fields arbitrary (owe() writes them). *)
Definition join_ok (e : env) (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops : word)
         (k : kcall) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) ->
    rec_ok k od ->
    cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' (Z_to_bv 64 (fst (enc_k k od))) a1' a2' a3' a4' a5' a6' a7' s5' ops s8' s10'
                       t3' t4' t5' t6')
          0x1435c m1).

(** The pc of owe()'s case for kind (0..10 through T3, SYSEX = 11 the default). *)
Definition owe_pc (kind : Z) : Z := if kind =? 11 then 0x1483c else nth (Z.to_nat kind) codec_T3 0.

(** OWEk: owe() past its common part: k.rc = the encoder's code, want_rc = want_len = want_key =
    want_display = 0, the desk test passed (a NULL desk only for BUTTON, JOG, SYSEX), s10 = k.desk. *)
Definition owe_ok (e : env) (kind : Z) (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops : word)
         (k : kcall) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) ->
    rec_ok k od -> k_kind k = kind ->
    (od = None -> kind = 1 \/ kind = 4 \/ kind = 11) ->
    k_rc k = fst (enc_k k od) ->
    k_want_rc k = 0 -> k_want_len k = 0 -> k_want_key k = 0 -> k_want_display k = 0 ->
    cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' ops s8' (Z_to_bv 64 (k_desk k))
                       t3' t4' t5' t6')
          (owe_pc kind) m1).

(** CHK 0x14808: owe() done: k.rc = the encoder's code, the want fields owe()'s answer. *)
Definition chk_ok (e : env) (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops : word)
         (k : kcall) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) ->
    rec_ok k od ->
    k_rc k = fst (enc_k k od) ->
    owe_want_ok k od ->
    cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' ops s8' s10' t3' t4' t5' t6')
          0x14808 m1).

(** LATCH 0x14828 (bltu s3, s6 -> EXIT): end of an iteration, from CHK and from COUNTER_TEXT's refusal;
    k any record, cursor (c, rem) in in.p / in.n. *)
Definition latch_ok (e : env) (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops : word)
         (k : kcall) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) ->
    cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' ops s8' s10' t3' t4' t5' t6')
          0x14828 m1).

(** LATCH2 0x1482c (ld s5 = in.n; ops + 1; beqz s5 -> EXIT; j HEAD): as LATCH, the ops test passed
    (from LATCH and from MASKS's copy of the test). *)
Definition latch2_ok (e : env) (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops : word)
         (k : kcall) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) -> bv_unsigned ops <= 254 ->
    cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' ops s8' s10' t3' t4' t5' t6')
          0x1482c m1).

(** ENTRY 0x13228: the contract's entry state. *)
Definition entry_goal (e : env) : Prop :=
  forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    bv_unsigned a1 = Z.of_nat (length (e_data e)) ->
    evt rsegs (Qk e)
      (st e (mkR (e_ra e) (e_sp e) (e_gp e) (e_tp e) t0 t1 t2 (e_s0 e) (e_s1 e) (e_p e) a1 a2 a3 a4 a5 a6 a7
                 (e_s2 e) (e_s3 e) (e_s4 e) (e_s5 e) (e_s6 e) (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e) (e_s11 e)
                 t3 t4 t5 t6)
          LLVM_CODEC (e_m e)).

(** ---- the segment statements (each proved in its own file, composed in LLVMFuzzerTestOneInput.v) ---- *)

(** ENTRY + prologue + size test + check_personality + loop constants (0x13228-0x132c4). *)
Definition S_entry : Prop :=
  check_personality_contract ->
  forall e, env_ok e -> exit_ok e -> head_ok e 256 -> entry_goal e.

(** EXIT (0x149ac-0x149e8). *)
Definition S_exit : Prop := forall e, env_ok e -> exit_ok e.

(** HEAD (0x132c8-0x13388): op byte, memset(k, 0), op / 15, op % 15, op / 15 % 3, personality_of,
    SPEC_DESK, memset(before + out, 0xa5), T1. *)
Definition S_head : Prop :=
  memset_contract -> diginet_personality_of_contract ->
  forall e fuel, env_ok e ->
    (forall kind, 0 <= kind <= 14 -> rd_ok e kind fuel) -> head_ok e (S fuel).

(** The readers that call their encoder themselves and reach JOIN. *)
Definition S_rd0 : Prop := diginet_fader_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> rd_ok e 0 fuel.
Definition S_rd1 : Prop := diginet_button_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> rd_ok e 1 fuel.
Definition S_rd2 : Prop := diginet_touch_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> rd_ok e 2 fuel.
Definition S_rd3 : Prop := diginet_vpot_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> rd_ok e 3 fuel.
Definition S_rd4 : Prop := diginet_jog_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> rd_ok e 4 fuel.
Definition S_rd5 : Prop := diginet_ring_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> rd_ok e 5 fuel.
Definition S_rd6 : Prop := diginet_meter_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> rd_ok e 6 fuel.
Definition S_rd7 : Prop := diginet_strip_leds_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> rd_ok e 7 fuel.
Definition S_rd8 : Prop := diginet_counter_leds_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> rd_ok e 8 fuel.
Definition S_rd11 : Prop := memcpy_contract -> diginet_sysex_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> rd_ok e 11 fuel.

(** SCRIBBLE and COUNTER: the reader, its 8-byte loop and run()'s switch T2 (0x13c24-0x13c48). *)
Definition S_rd9 : Prop := forall e fuel, env_ok e -> enc9_ok e fuel -> rd_ok e 9 fuel.
Definition S_rd10 : Prop := forall e fuel, env_ok e -> enc10_ok e fuel -> rd_ok e 10 fuel.

(** SCRIBBLE_TEXT (0x134f4-0x1355c). *)
Definition S_rd12 : Prop :=
  diginet_personality_of_contract -> text_arg_contract -> check_text_scribble_contract ->
  forall e fuel, env_ok e -> enc9_ok e fuel -> rd_ok e 12 fuel.

(** COUNTER_TEXT (0x13830-0x13898): to ENC10, or to LATCH when owed_counter_text refuses the text. *)
Definition S_rd13 : Prop :=
  diginet_personality_of_contract -> text_arg_contract -> check_text_seg7_contract ->
  check_text_counter_contract -> owed_counter_text_contract ->
  forall e fuel, env_ok e -> enc10_ok e fuel -> latch_ok e fuel -> rd_ok e 13 fuel.

(** MASKS (0x139a8-0x13a20, 0x13b3c-0x13b44, 0x13b88-0x13b8c, 0x148c8-0x14930): check_text_masks, then its copy of
    the ops test. *)
Definition S_rd14 : Prop :=
  check_text_masks_contract ->
  forall e fuel, env_ok e -> latch2_ok e fuel -> exit_ok e -> rd_ok e 14 fuel.

(** The two encoder calls shared by two readers each. *)
Definition S_enc9 : Prop := diginet_scribble_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> enc9_ok e fuel.
Definition S_enc10 : Prop := diginet_counter_encode_contract ->
  forall e fuel, env_ok e -> join_ok e fuel -> enc10_ok e fuel.

(** owe()'s common part (0x1435c-0x143b0, 0x1440c-0x1441c, E_ARG 0x14848-0x1484c, 0x14804). *)
Definition S_oweh : Prop :=
  forall e fuel, env_ok e ->
    (forall kind, 0 <= kind <= 11 -> owe_ok e kind fuel) -> chk_ok e fuel -> join_ok e fuel.

(** owe()'s cases, each with the shared tails it runs through, to CHK. *)
Definition S_owe0 : Prop := forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 0 fuel.
Definition S_owe1 : Prop := forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 1 fuel.
Definition S_owe2 : Prop := forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 2 fuel.
Definition S_owe3 : Prop := forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 3 fuel.
Definition S_owe4 : Prop := forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 4 fuel.
Definition S_owe5 : Prop := forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 5 fuel.
Definition S_owe6 : Prop := forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 6 fuel.
Definition S_owe7 : Prop := forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 7 fuel.
Definition S_owe8 : Prop := forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 8 fuel.
Definition S_owe9 : Prop := memcpy_contract -> forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 9 fuel.
Definition S_owe10 : Prop := memcpy_contract -> forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 10 fuel.
Definition S_owe11 : Prop := memcpy_contract -> forall e fuel, env_ok e -> chk_ok e fuel -> owe_ok e 11 fuel.

(** The checks (0x14808-0x14824). *)
Definition S_chk : Prop :=
  check_refusal_contract -> check_range_contract -> check_bytes_contract ->
  forall e fuel, env_ok e -> latch_ok e fuel -> chk_ok e fuel.

(** The latch (0x14828-0x14838). *)
Definition S_latch : Prop :=
  forall e fuel, env_ok e -> head_ok e fuel -> exit_ok e -> latch_ok e fuel /\ latch2_ok e fuel.

(** ---- the segments compose: the loop by fuel 256 - ops, the body by case on the kind ---- *)

Lemma kind_cases_14 : forall (P : Z -> Prop) kind, 0 <= kind <= 14 ->
  P 0 -> P 1 -> P 2 -> P 3 -> P 4 -> P 5 -> P 6 -> P 7 -> P 8 -> P 9 -> P 10 -> P 11 -> P 12 -> P 13 -> P 14 ->
  P kind.
Proof.
  intros P kind Hk H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
  assert (E : kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/ kind = 5 \/ kind = 6 \/ kind = 7 \/
              kind = 8 \/ kind = 9 \/ kind = 10 \/ kind = 11 \/ kind = 12 \/ kind = 13 \/ kind = 14) by lia.
  repeat (destruct E as [-> | E]; [assumption |]). subst kind. assumption.
Qed.

Theorem main_of_segments :
  S_entry -> S_exit -> S_head ->
  S_rd0 -> S_rd1 -> S_rd2 -> S_rd3 -> S_rd4 -> S_rd5 -> S_rd6 -> S_rd7 -> S_rd8 -> S_rd9 -> S_rd10 ->
  S_rd11 -> S_rd12 -> S_rd13 -> S_rd14 -> S_enc9 -> S_enc10 -> S_oweh ->
  S_owe0 -> S_owe1 -> S_owe2 -> S_owe3 -> S_owe4 -> S_owe5 -> S_owe6 -> S_owe7 -> S_owe8 -> S_owe9 ->
  S_owe10 -> S_owe11 -> S_chk -> S_latch ->
  memset_contract -> memcpy_contract -> check_personality_contract -> diginet_personality_of_contract ->
  text_arg_contract -> check_text_scribble_contract -> diginet_scribble_encode_contract ->
  check_text_seg7_contract -> check_text_counter_contract -> owed_counter_text_contract ->
  diginet_sysex_encode_contract -> diginet_jog_encode_contract -> diginet_counter_encode_contract ->
  diginet_touch_encode_contract -> diginet_vpot_encode_contract -> diginet_strip_leds_encode_contract ->
  diginet_fader_encode_contract -> diginet_button_encode_contract -> diginet_ring_encode_contract ->
  diginet_meter_encode_contract -> diginet_counter_leds_encode_contract -> check_refusal_contract ->
  check_range_contract -> check_bytes_contract -> check_text_masks_contract ->
  forall e, env_ok e -> entry_goal e.
Proof.
  intros SE SX SH R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 E9 E10 OH
         O0 O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 SC SL
         Cmset Cmcpy Cpers Cpof Ctarg Ctscr Cscr Cseg7 Ctcnt Cocnt Csx Cjog Ccnt Ctouch Cvpot Csled
         Cfader Cbutton Cring Cmeter Ccled Cref Crange Cbytes Cmasks e HE.
  pose proof (SX e HE) as EX.
  assert (LOOP : forall fuel, head_ok e fuel).
  { induction fuel as [|f IH].
    - unfold head_ok. intros * [HF HO]. exfalso. lia.
    - destruct (SL e f HE IH EX) as [LA LA2].
      pose proof (SC Cref Crange Cbytes e f HE LA) as CH.
      assert (OW : forall kind, 0 <= kind <= 11 -> owe_ok e kind f).
      { intros kind Hk. assert (Hk' : 0 <= kind <= 14) by lia. revert Hk.
        apply (kind_cases_14 (fun k => 0 <= k <= 11 -> owe_ok e k f) kind Hk'); intros Hk;
          first [ exact (O0 e f HE CH) | exact (O1 e f HE CH) | exact (O2 e f HE CH)
                | exact (O3 e f HE CH) | exact (O4 e f HE CH) | exact (O5 e f HE CH)
                | exact (O6 e f HE CH) | exact (O7 e f HE CH) | exact (O8 e f HE CH)
                | exact (O9 Cmcpy e f HE CH) | exact (O10 Cmcpy e f HE CH) | exact (O11 Cmcpy e f HE CH)
                | exfalso; lia ]. }
      pose proof (OH e f HE OW CH) as JN.
      pose proof (E9 Cscr e f HE JN) as EN9.
      pose proof (E10 Ccnt e f HE JN) as EN10.
      apply (SH Cmset Cpof e f HE).
      intros kind Hk. apply (kind_cases_14 (fun k => rd_ok e k f) kind Hk).
      + exact (R0 Cfader e f HE JN).
      + exact (R1 Cbutton e f HE JN).
      + exact (R2 Ctouch e f HE JN).
      + exact (R3 Cvpot e f HE JN).
      + exact (R4 Cjog e f HE JN).
      + exact (R5 Cring e f HE JN).
      + exact (R6 Cmeter e f HE JN).
      + exact (R7 Csled e f HE JN).
      + exact (R8 Ccled e f HE JN).
      + exact (R9 e f HE EN9).
      + exact (R10 e f HE EN10).
      + exact (R11 Cmcpy Csx e f HE JN).
      + exact (R12 Cpof Ctarg Ctscr e f HE EN9).
      + exact (R13 Cpof Ctarg Cseg7 Ctcnt Cocnt e f HE EN10 LA).
      + exact (R14 Cmasks e f HE LA2 EX). }
  exact (SE Cpers e HE EX (LOOP 256%nat)).
Qed.

(** ---- facts the segments share ---- *)

(** Cutting a frame description in two and gluing it back (the lemmas of libreac/fuzz_knock's lib). *)
Lemma rw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hl, Hw.
  rewrite cells_bytes_length in B2 by exact W1.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma rw_cells_app_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

(** One input byte. *)
Lemma bytes_at_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma kcall_cells_size : forall k, cells_size (kcall_cells k) = 184%nat.
Proof. intros k. reflexivity. Qed.

Lemma body_cells_size : forall e k c rem tl, cells_size (body_cells e k c rem tl) = 296%nat.
Proof. intros. reflexivity. Qed.

(** The RELRO tables still hold the image in any memory that differs from the entry one only in the
    stack window (so at every cut): the window is disjoint from them. *)
Lemma relro_of_munch : forall e m1, env_ok e ->
  munch [(bv_unsigned (e_sp e) - LLVM_CODEC_STACK, bv_unsigned (e_sp e))] (e_m e) m1 -> relro_img m1.
Proof.
  intros e m1 HE MU.
  destruct HE as (_ & _ & _ & HLO & _ & _ & _ & HR & HDJ).
  unfold munch in MU.
  intros i Hi. specialize (HR i Hi). unfold mrd in *.
  rewrite MU; [exact HR|].
  unfold LLVM_CODEC_STACK, RELRO_BASE, RELRO_LEN, disj in *.
  rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

Lemma relro_of_fr : forall e m1, env_ok e -> fr_ok e m1 -> relro_img m1.
Proof. intros e m1 HE (_ & _ & MU & _ & _). exact (relro_of_munch e m1 HE MU). Qed.

(** Likewise the input bytes. *)
Lemma data_of_munch : forall e m1, env_ok e ->
  munch [(bv_unsigned (e_sp e) - LLVM_CODEC_STACK, bv_unsigned (e_sp e))] (e_m e) m1 ->
  bytes_at rsegs m1 (bv_unsigned (e_p e)) (e_data e).
Proof.
  intros e m1 HE MU.
  destruct HE as (HD & _ & _ & HLO & _ & DJ & _ & _ & _).
  eapply (bytes_at_transport rsegs); [exact HD | exact MU |].
  cbn [disjoint_from]. unfold LLVM_CODEC_STACK in *. split; [lia | exact I].
Qed.

Lemma data_of_fr : forall e m1, env_ok e -> fr_ok e m1 -> bytes_at rsegs m1 (bv_unsigned (e_p e)) (e_data e).
Proof. intros e m1 HE (_ & _ & MU & _ & _). exact (data_of_munch e m1 HE MU). Qed.

(** The personality argument the encoders take, from k.p. *)
Lemma pers_arg_of_pd : forall m pv dv od, relro_img m -> pd_ok pv dv od -> pers_arg m (Z_to_bv 64 pv) od.
Proof.
  intros m pv dv od HR [(-> & -> & ->) | [(-> & -> & ->) | (-> & -> & ->)]]; cbv [pers_arg pers_ok].
  - reflexivity.
  - rewrite unsigned_lit by (unfold PERS; lia). split; [unfold PERS; lia|]. split.
    + cbv [codec_cells.desk_ok c24 d_dev d_strips d_chars d_counter]. lia.
    + apply (img_mrd_bytes_at rsegs m RELRO_BASE RELRO_LEN); [exact HR | .. | vm_compute; reflexivity];
        cbn [bz map length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold RELRO_BASE, RELRO_LEN, PERS; lia.
  - rewrite unsigned_lit by (unfold PERS; lia). split; [unfold PERS; lia|]. split.
    + cbv [codec_cells.desk_ok pc d_dev d_strips d_chars d_counter]. lia.
    + apply (img_mrd_bytes_at rsegs m RELRO_BASE RELRO_LEN); [exact HR | .. | vm_compute; reflexivity];
        cbn [bz map length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold RELRO_BASE, RELRO_LEN, PERS; lia.
Qed.

(** The four desk bytes owe() and SCRIBBLE_TEXT read at k.desk + 8 (device, strips, chars, counter). *)
Lemma desk_bytes_of_pd : forall m pv dv d, relro_img m -> pd_ok pv dv (Some d) ->
  bytes_at rsegs m (dv + 8) (bz [d_dev d; d_strips d; d_chars d; d_counter d]).
Proof.
  intros m pv dv d HR [(_ & _ & H) | [(-> & -> & H) | (-> & -> & H)]]; [discriminate|..];
    injection H as ->;
    (apply (img_mrd_bytes_at rsegs m RELRO_BASE RELRO_LEN); [exact HR | .. | vm_compute; reflexivity]);
    cbn [bz map length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold RELRO_BASE, RELRO_LEN; lia.
Qed.

(** Any range of the stack window [lo, sp) misses the RELRO tables. *)
Lemma stack_disj_relro : forall e A n, env_ok e -> e_lo e <= A -> A + n <= bv_unsigned (e_sp e) ->
  disj A n RELRO_BASE RELRO_LEN.
Proof.
  intros e A n HE H1 H2. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & HDJ).
  unfold disj, RELRO_BASE, RELRO_LEN in *. lia.
Qed.

(** The stack-window premise of a callee whose sp is at most the entry sp. *)
Lemma callee_relro_disj : forall e x, env_ok e -> x <= bv_unsigned (e_sp e) ->
  disj (e_lo e) (x - e_lo e) RELRO_BASE RELRO_LEN.
Proof.
  intros e x HE Hx. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & HDJ).
  unfold disj, RELRO_BASE, RELRO_LEN in *. lia.
Qed.

(** The personality bytes p + 16 .. p + 19 miss any range of the stack window (a callee's frame, k.out). *)
Lemma pers_disj : forall e pv dv d A n, env_ok e -> pd_ok pv dv (Some d) ->
  e_lo e <= A -> A + n <= bv_unsigned (e_sp e) -> disj (pv + 16) 4 A n.
Proof.
  intros e pv dv d A n HE Hpd H1 H2. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & HDJ).
  unfold disj, RELRO_BASE, RELRO_LEN in *.
  destruct Hpd as [(_ & _ & H) | [(-> & _ & _) | (-> & _ & _)]]; [discriminate | unfold PERS; lia ..].
Qed.

(** ---- the HEAD invariant holds in a concrete state ---- *)

Module Sat.
Import codec_contract_sat.

(** The driver's input and stack; the frame holds the two constants and in.p = the input. *)
Definition sat_mem : word -> option byte :=
  smem [(SDATA, sat_input);
        (MSP, le8 (Z_to_bv 64 0x5cb0) ++ le8 (Z_to_bv 64 0x13f0));
        (MSP + 0xc8, le8 (Z_to_bv 64 SDATA))].

Definition w0 : word := Z_to_bv 64 0.

Definition sat_env : env :=
  mkEnv w0 (Z_to_bv 64 SAT_SP) w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0
        (mkR w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0)
        (Z_to_bv 32 0) sat_mem SAT_LO (Z_to_bv 64 SDATA) sat_input.

(** The premises of head_ok at fuel 256 (the fuel ENTRY gives) hold for an environment satisfying the
    contract's premises: ops = 0, nothing consumed, in.p = the input, the frame as the prologue leaves it. *)
Lemma head_inv_sat : exists (e : env) (ops : word) (c rem : Z) (kj rj : list byte) (m1 : word -> option byte),
  env_ok e /\ fuel_ok ops 256 /\ 1 <= rem /\ cur_ok e c rem /\
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (head_cells e c kj rj) /\ fr_ok e m1.
Proof.
  exists sat_env, w0, 0, 10, (sat_z0 184), (sat_z0 88), sat_mem.
  cbv [env_ok fuel_ok cur_ok fr_ok head_cells saved sat_env e_m e_sp e_p e_data e_lo
       e_ra e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 disj].
  repeat match goal with |- _ /\ _ => split end;
    first [ apply munch_refl | apply wmono_refl | sat1 ].
Qed.

End Sat.
