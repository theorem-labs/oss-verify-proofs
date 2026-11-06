(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/varnish/esi_parse_fuzzer/lib/Yd/DA_Tac.v, with its module paths and module names changed; 635 of its 698 lines of code are new or changed and 187 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/TModel/TWorldMem.v, with its module paths and module names changed; 703 of its 783 lines of code are new or changed and 618 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Prog/T/diginet_session_init.v; 2402 of its 2499 lines of code are new or changed and 686 lines of the source are left out. *)
(* The ENTRY of LLVMFuzzerTestOneInput in the plain image: 0x13664 to the loop head 0x138ac
   (fuzz/fuzz_transport.c:1121-1165). Every callee it reaches (diginet_session_config_default, memcpy, memset,
   diginet_session_init) is evt-shaped, so the whole stretch is ONE evt segment: no SR seam.

   The machine, from tr6/llvmf-plain.dis (every address below is read off it):
     0x13664-0x13698  addi sp,sp,-0xe0 and the 13 callee-saved registers to sp+0x78 .. sp+0xd8
     0x1369c-0x136c8  s4 = data; the struct diginet_io of .data.rel.ro at 0x213c8 ({NULL, io_send, io_recv,
                      io_now}, TImgP.v timg_plain) read as four 8-byte loads and stored to sp+0x30 .. sp+0x48
     0x136cc          srli a2,a1,0x1a; bnez a2 -> 0x14320: size >= 2^26 = FUZZ_INPUT_MAX, the model's
                      `if FUZZ_INPUT_MAX <=? size then Some (B, 0)` (TOps.v :1127-1128)
     0x136d0-0x136e8  fuzz_u8 of the flags byte (s0), with the empty-input arm at 0x136e4
     0x136ec-0x13710  s9 = &g_fail_next, s1 = &g_cfg; diginet_session_config_default(&g_cfg);
                      memcpy(&g_cfg.host_mac, HOST, 6)    (:1131-1132)
     0x13714-0x137f8  the config fields the flags byte and the next bytes set (:1133-1145). The cursor can run
                      out at any read, so the stretch is FIFTEEN straight paths, one per count of bytes left;
                      they join at 0x1376c, 0x13778, 0x13780, 0x13788, 0x13794, 0x137a0, 0x137a4 and 0x137b8.
                      The out-of-line arms are 0x14360-0x144e4.
     0x137fc-0x13808  g_fail_next = 0 (sb), g_raw = flags>>3&1, g_last_counter = 0, g_now = 0xf4240 (:1147-1150)
     0x1380c-0x13838  memset(&M + 8, 0, 0x668) and M.desk_known / memcpy(&M.desk, DESK, 6)  (:1151-1153)
     0x1383c-0x13868  g_nq = g_ncmd = 0, g_rx = 0; diginet_session_init(&g_s, &g_cfg, sp+0x30, notice, NULL)
     0x1386c          bnez a0 -> 0x144e8 abort(): the model's `if negb (rc =? SPEC_OK) then None` (:1163)
     0x13870          beqz s7 -> 0x14320: no input left, the loop runs zero passes
     0x13874-0x138a8  the loop's registers and the four frame constants (sp+0x18 = 0x610f, sp+0x00 = 2^32-3,
                      sp+0x20 = 0xffff, sp+0x08 = &g_s), then 0x138ac, the head.

   The two ways out and llvm_out0. Both exits to 0x14320 leave BEFORE the four frame-constant stores of
   0x13894-0x138a8, so llvm_out (_lh.v), whose llvm_mem asks for those cells, cannot hold there. llvm_out0
   below is llvm_out with the frame's first 120 bytes left as junk; llvm_out_weaken turns the loop's llvm_out
   into it, so llvm_exit0 is the one epilogue for every path. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess0 TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract TSessC
  diginet_session_config_default_c diginet_session_config_default diginet_session_init_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(* ================================ .data.rel.ro: the struct diginet_io ================================ *)

(* TContract.v relro_img says the image's bytes are still at [0x213c8, 0x213c8 + 0x98); as bytes_at. *)
Lemma ent_img_nth : forall n a bs i, image_bytes rsegs a n = Some bs -> (i < n)%nat ->
  seg_rom rsegs (wa (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros a bs i H Hi; cbn in H; [lia|].
  destruct (seg_rom rsegs (wa a)) as [b|] eqn:E1; [|discriminate].
  destruct (image_bytes rsegs (a + 1) n) as [bs'|] eqn:E2; [|discriminate].
  injection H as <-. destruct i as [|i]; cbn [nth_error].
  - rewrite Z.add_0_r. exact E1.
  - rewrite <- (IH (a + 1) bs' i E2 ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

Lemma ent_relro_bytes : forall m a bs, relro_img m ->
  RELRO_BASE <= a -> a + Z.of_nat (length bs) <= RELRO_BASE + RELRO_LEN ->
  image_bytes rsegs a (length bs) = Some bs -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RE H1 H2 HI. unfold RELRO_BASE, RELRO_LEN in H1, H2.
  split; [lia|]. split; [lia|].
  intros i Hi. rewrite <- (ent_img_nth (length bs) a bs i HI Hi).
  replace (a + Z.of_nat i) with (RELRO_BASE + (a + Z.of_nat i - RELRO_BASE)) by (unfold RELRO_BASE; lia).
  apply RE. unfold RELRO_BASE, RELRO_LEN. lia.
Qed.

(* the struct diginet_io the harness hands diginet_session_init (fuzz_transport.c:1124): .data.rel.ro at
   0x213c8, {NULL, io_send, io_recv, io_now} = {0, 0x144ec, 0x1492c, 0x149d8} (TImgP.v timg_plain) *)
Definition ent_io_bytes : list byte :=
  put 8 0 ++ put 8 (ti_io_send timg_plain) ++ put 8 (ti_io_recv timg_plain) ++ put 8 (ti_io_now timg_plain).

Lemma ent_io_len : length ent_io_bytes = 32%nat.
Proof. unfold ent_io_bytes. rewrite !length_app, !length_put. reflexivity. Qed.

Lemma ent_io_img : image_bytes rsegs 0x213c8 (length ent_io_bytes) = Some ent_io_bytes.
Proof.
  rewrite ent_io_len.
  lazymatch goal with |- ?L = Some _ => let v := eval vm_compute in L in change L with v end.
  f_equal. apply bytes_eq_of_zs. vm_compute. reflexivity.
Qed.

Lemma ent_io_at : forall m, relro_img m -> bytes_at rsegs m 0x213c8 ent_io_bytes.
Proof.
  intros m R. apply (ent_relro_bytes m 0x213c8 ent_io_bytes R);
    [ unfold RELRO_BASE; lia
    | rewrite ent_io_len; unfold RELRO_BASE, RELRO_LEN; cbn; lia
    | exact ent_io_img ].
Qed.

(* one 8-byte field of it, in the form a load consumes *)
Lemma ent_rd8 : forall m k v, relro_img m -> 0 <= k -> k + 8 <= 32 ->
  firstn 8 (skipn (Z.to_nat k) ent_io_bytes) = le8 (Z_to_bv 64 v) ->
  ov_read_bytes rsegs m (wa (0x213c8 + k)) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m k v R Hk Hn E. rewrite <- E.
  apply (bytes_at_read rsegs m 0x213c8 ent_io_bytes k 8 (ent_io_at m R) Hk).
  rewrite ent_io_len. lia.
Qed.

Section ENTRY.
Context (data : Z) (D : list byte).

(* ================================ the model, cut at the machine's join points ================================
   TOps.v LLVMFuzzerTestOneInput_m reads the config fields in one straight let-chain (:1133-1145). The machine
   cannot: the cursor may run out at any read, so it has an out-of-line arm per read. ecfg_t<k> below is the
   model's TAIL from the k-th read on, which is what the machine's join point for that read reaches. *)

(* :1145 max_body *)
Definition ecfg_t9 (c : fuzz_in) (B : list byte) : list byte * fuzz_in :=
  let (c10, v9) := fuzz_u16_m D c in
  (set_Cfg_max_body B ((SPEC_CMD_MAX + v9 mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2 ^ 32), c10).

(* :1144 max_cmds *)
Definition ecfg_t8 (c : fuzz_in) (B : list byte) : list byte * fuzz_in :=
  let (c9, v8) := fuzz_u8_m D c in
  ecfg_t9 c9 (set_Cfg_max_cmds B ((1 + v8 mod 255) mod 2 ^ 32)).

(* :1143 display_gap_us *)
Definition ecfg_t7 (c : fuzz_in) (B : list byte) : list byte * fuzz_in :=
  let (c8, v7) := fuzz_u16_m D c in
  ecfg_t8 c8 (set_Cfg_display_gap_us B v7).

(* :1142 wake_timeout_ms *)
Definition ecfg_t6 (c : fuzz_in) (B : list byte) : list byte * fuzz_in :=
  let (c7, v6) := fuzz_u16_m D c in
  ecfg_t7 c7 (set_Cfg_wake_timeout_ms B ((1 + v6) mod 2 ^ 32)).

(* :1141 offline_ms *)
Definition ecfg_t5 (c : fuzz_in) (B : list byte) : list byte * fuzz_in :=
  let (c6, v5) := fuzz_u16_m D c in
  ecfg_t6 c6 (set_Cfg_offline_ms B ((1 + v5) mod 2 ^ 32)).

(* :1140 backoff_ms *)
Definition ecfg_t4 (c : fuzz_in) (B : list byte) : list byte * fuzz_in :=
  let (c5, v4) := fuzz_u8_m D c in
  ecfg_t5 c5 (set_Cfg_backoff_ms B v4).

(* :1139 keepalive_ms *)
Definition ecfg_t3 (c : fuzz_in) (B : list byte) : list byte * fuzz_in :=
  let (c4, v3) := fuzz_u16_m D c in
  ecfg_t4 c4 (set_Cfg_keepalive_ms B ((1 + v3) mod 2 ^ 32)).

(* :1138 ack_timeout_ms *)
Definition ecfg_t2 (c : fuzz_in) (B : list byte) : list byte * fuzz_in :=
  let (c3, v2) := fuzz_u8_m D c in
  ecfg_t3 c3 (set_Cfg_ack_timeout_ms B ((1 + v2) mod 2 ^ 32)).

(* :1137 max_retries *)
Definition ecfg_t1 (c : fuzz_in) (B : list byte) : list byte * fuzz_in :=
  let (c2, v1) := fuzz_u8_m D c in
  ecfg_t2 c2 (set_Cfg_max_retries B (v1 mod 8)).

(* :1132-1136, the fields the flags byte sets, then the chain above *)
Definition ecfg_flags (flags : Z) (c : fuzz_in) (B : list byte) : list byte * fuzz_in :=
  ecfg_t1 c (set_Cfg_desk_mac
               (set_Cfg_desk_mac_set
                  (set_Cfg_sum_mode
                     (set_Cfg_auto_wake (set_Cfg_host_mac B HOST) (Z.land flags 1))
                     (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO))
                  (Z.land (Z.shiftr flags 2) 1))
               DESK).

(* :1147-1155, the scalars and M, after the config *)
Definition ent_tail_world (flags : Z) (B : list byte) : list byte :=
  let B16 := set_g_raw B (Z.land (Z.shiftr flags 3) 1) in
  let B17 := set_g_now B16 1000000 in
  let B18 := set_g_fail_next B17 0 in
  let B19 := set_g_last_counter B18 0 in
  let B20 := upd B19 OFF_M (repeat (b8 0) (Z.to_nat SZ_M)) in
  let B21 := set_M_desk_known B20 (Cfg_desk_mac_set B20) in
  let B22 := set_M_desk B21 DESK in
  let B23 := set_g_ncmd (set_g_nq B22 0) 0 in
  set_g_rx B23 0.

(* The world and the cursor the entry hands the loop: everything of LLVMFuzzerTestOneInput_m up to, but not
   including, diginet_session_init (:1131-1155). *)
Definition ent_world (B : list byte) : option (list byte * fuzz_in) :=
  let (c1, flags) := fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D))) in
  match diginet_session_config_default_m B with
  | None => None
  | Some (B1, _) =>
      let (Bc, c10) := ecfg_flags flags c1 B1 in
      Some (ent_tail_world flags Bc, c10)
  end.

(* ent_world is the model's own prologue: LLVMFuzzerTestOneInput_m, for an input the size test lets through. *)
Lemma ent_model : forall (I : timg) (B : list byte) (A : nat -> Z),
  Z.of_nat (length D) < FUZZ_INPUT_MAX ->
  LLVMFuzzerTestOneInput_m I B A D =
  match ent_world B with
  | None => None
  | Some (B24, c10) =>
      match diginet_session_init_m B24 0 (ti_io_send I) (ti_io_recv I) (ti_io_now I) (ti_notice I) 0 with
      | None => None
      | Some (B25, rc) =>
          if negb (rc =? SPEC_OK) then None
          else match LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) I B25 A D c10 O with
               | None => None
               | Some (B26, _) => Some (B26, 0)
               end
      end
  end.
Proof.
  intros I B A HS.
  unfold LLVMFuzzerTestOneInput_m, ent_world.
  rewrite (proj2 (Z.leb_gt FUZZ_INPUT_MAX (Z.of_nat (length D))) HS). cbv beta iota zeta.
  destruct (fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D)))) as [c1 flags].
  destruct (diginet_session_config_default_m B) as [[B1 u1]|]; [|reflexivity].
  unfold ecfg_flags, ecfg_t1, ecfg_t2, ecfg_t3, ecfg_t4, ecfg_t5, ecfg_t6, ecfg_t7, ecfg_t8, ecfg_t9,
         ent_tail_world.
  repeat first [ destruct (fuzz_u8_m D _) | destruct (fuzz_u16_m D _) ].
  reflexivity.
Qed.

(* ---- the model's config tail once the input is spent ----
   The machine's out-of-line arms (0x14360-0x144e4) all rejoin the straight chain 0x1376c-0x137b8 only after
   the last byte, so at every join point the cursor is empty and every read left is 0. *)

Lemma ent_u8_z : forall c, fi_n c = 0 -> fuzz_u8_m D c = (c, 0).
Proof. intros c H. unfold fuzz_u8_m. rewrite H. reflexivity. Qed.

Lemma ent_u16_z : forall c, fi_n c = 0 -> fuzz_u16_m D c = (c, 0).
Proof. intros c H. unfold fuzz_u16_m. rewrite (ent_u8_z c H), (ent_u8_z c H). reflexivity. Qed.

Lemma ecfg_t9_z : forall c B, fi_n c = 0 -> ecfg_t9 c B = (set_Cfg_max_body B 24, c).
Proof. intros c B H. unfold ecfg_t9. rewrite (ent_u16_z c H). reflexivity. Qed.

Lemma ecfg_t8_z : forall c B, fi_n c = 0 ->
  ecfg_t8 c B = (set_Cfg_max_body (set_Cfg_max_cmds B 1) 24, c).
Proof. intros c B H. unfold ecfg_t8. rewrite (ent_u8_z c H). apply ecfg_t9_z. exact H. Qed.

Lemma ecfg_t7_z : forall c B, fi_n c = 0 ->
  ecfg_t7 c B = (set_Cfg_max_body (set_Cfg_max_cmds (set_Cfg_display_gap_us B 0) 1) 24, c).
Proof. intros c B H. unfold ecfg_t7. rewrite (ent_u16_z c H). apply ecfg_t8_z. exact H. Qed.

Lemma ecfg_t6_z : forall c B, fi_n c = 0 ->
  ecfg_t6 c B = (set_Cfg_max_body (set_Cfg_max_cmds (set_Cfg_display_gap_us
                   (set_Cfg_wake_timeout_ms B 1) 0) 1) 24, c).
Proof. intros c B H. unfold ecfg_t6. rewrite (ent_u16_z c H). apply ecfg_t7_z. exact H. Qed.

Lemma ecfg_t5_z : forall c B, fi_n c = 0 ->
  ecfg_t5 c B = (set_Cfg_max_body (set_Cfg_max_cmds (set_Cfg_display_gap_us
                   (set_Cfg_wake_timeout_ms (set_Cfg_offline_ms B 1) 1) 0) 1) 24, c).
Proof. intros c B H. unfold ecfg_t5. rewrite (ent_u16_z c H). apply ecfg_t6_z. exact H. Qed.

Lemma ecfg_t4_z : forall c B, fi_n c = 0 ->
  ecfg_t4 c B = (set_Cfg_max_body (set_Cfg_max_cmds (set_Cfg_display_gap_us
                   (set_Cfg_wake_timeout_ms (set_Cfg_offline_ms (set_Cfg_backoff_ms B 0) 1) 1) 0) 1) 24, c).
Proof. intros c B H. unfold ecfg_t4. rewrite (ent_u8_z c H). apply ecfg_t5_z. exact H. Qed.

Lemma ecfg_t3_z : forall c B, fi_n c = 0 ->
  ecfg_t3 c B = (set_Cfg_max_body (set_Cfg_max_cmds (set_Cfg_display_gap_us
                   (set_Cfg_wake_timeout_ms (set_Cfg_offline_ms (set_Cfg_backoff_ms
                      (set_Cfg_keepalive_ms B 1) 0) 1) 1) 0) 1) 24, c).
Proof. intros c B H. unfold ecfg_t3. rewrite (ent_u16_z c H). apply ecfg_t4_z. exact H. Qed.

Lemma ecfg_t2_z : forall c B, fi_n c = 0 ->
  ecfg_t2 c B = (set_Cfg_max_body (set_Cfg_max_cmds (set_Cfg_display_gap_us
                   (set_Cfg_wake_timeout_ms (set_Cfg_offline_ms (set_Cfg_backoff_ms
                      (set_Cfg_keepalive_ms (set_Cfg_ack_timeout_ms B 1) 1) 0) 1) 1) 0) 1) 24, c).
Proof. intros c B H. unfold ecfg_t2. rewrite (ent_u8_z c H). apply ecfg_t3_z. exact H. Qed.

Lemma ecfg_t1_z : forall c B, fi_n c = 0 ->
  ecfg_t1 c B = (set_Cfg_max_body (set_Cfg_max_cmds (set_Cfg_display_gap_us
                   (set_Cfg_wake_timeout_ms (set_Cfg_offline_ms (set_Cfg_backoff_ms
                      (set_Cfg_keepalive_ms (set_Cfg_ack_timeout_ms
                         (set_Cfg_max_retries B 0) 1) 1) 0) 1) 1) 0) 1) 24, c).
Proof. intros c B H. unfold ecfg_t1. rewrite (ent_u8_z c H). apply ecfg_t2_z. exact H. Qed.

(* 0x137d0-0x137d4: the compiler's division by 1461 (SPEC_MAX_BODY - SPEC_CMD_MAX + 1), as a multiply by
   22967 = ceil (2^25 / 1461) and a shift of 25. 1461 * 22967 = 2^25 + 355, and for v < 2^16 the error term
   355 * (v / 1461) + 22967 * (v mod 1461) stays below 2^25. *)
Lemma ent_div1461 : forall v, 0 <= v < 65536 -> v * 22967 / 33554432 = v / 1461.
Proof.
  intros v Hv.
  assert (Hr : 0 <= v mod 1461 < 1461) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod v 1461 ltac:(lia)) as E.
  assert (Hq : 0 <= v / 1461 <= 44).
  { split; [apply Z.div_pos; lia|].
    assert (v / 1461 < 45) by (apply Z.div_lt_upper_bound; lia). lia. }
  replace (v * 22967) with (33554432 * (v / 1461) + (355 * (v / 1461) + 22967 * (v mod 1461)))
    by lia.
  rewrite Z.mul_comm, Z.div_add_l by lia.
  rewrite (Z.div_small (355 * (v / 1461) + 22967 * (v mod 1461)) 33554432) by lia. lia.
Qed.

(* ================================ the predicates ================================ *)

(* What the caller says about the input buffer. An EMPTY payload has no block at all, so the clauses about D
   hold only when there is a byte to read; every read of the walk is behind a test on the cursor's n, and
   n = 0 for an empty input. Stated over the entry memory m0, which the walk never changes outside its own
   footprint, so it is never transported. *)
Definition ent_dok (lo : Z) (m0 : word -> option byte) : Prop :=
  D = [] \/ (0 < data /\ data + Z.of_nat (length D) <= lo /\ off_world data (Z.of_nat (length D)) /\
             bytes_at rsegs m0 data D).

Lemma ent_dok_pos : forall lo m0, ent_dok lo m0 -> 0 < Z.of_nat (length D) ->
  0 < data /\ data + Z.of_nat (length D) <= lo /\ off_world data (Z.of_nat (length D)) /\
  bytes_at rsegs m0 data D.
Proof.
  intros lo m0 H Hp. destruct H as [HE|H]; [|exact H].
  exfalso. rewrite HE in Hp. cbn in Hp. lia.
Qed.

(* the three clauses llvm_mem asks about the input, for the memory of any point of the walk *)
Lemma ent_dok_mem : forall lo Sp m0 m, ent_dok lo m0 -> munch (LLVM_FP Sp) m0 m ->
  W_BASE_PLAIN + W_LEN <= lo -> lo + LLVM_LOOP_K <= Sp -> Sp + LLVM_FRAME < 2 ^ 63 ->
  0 < Z.of_nat (length D) ->
  bytes_at rsegs m data D /\ off_world data (Z.of_nat (length D)) /\
  off_window (Z_to_bv 64 (Sp + LLVM_FRAME)) (LLVM_LOOP_K + LLVM_FRAME) data (Z.of_nat (length D)).
Proof.
  intros lo Sp m0 m HD MU HOWS HLO HSP Hp.
  destruct (ent_dok_pos lo m0 HD Hp) as (Hd0 & Hdl & HOW & HB).
  assert (HL0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP in MU. unfold LLVM_LOOP_K, LLVM_FRAME in *. unfold off_world in HOW.
  split; [|split].
  - eapply bytes_at_transport; [exact HB | exact MU |].
    cbn [disjoint_from].
    split; [lia | split; [exact HOW | exact I]].
  - exact HOW.
  - unfold off_window. rewrite unsigned_lit by lia. lia.
Qed.

(* The state the caller is in at 0x13664: sp above the frame, a0 = the input pointer, a1 = its length, the 13
   callee-saved registers as the caller left them, and everything llvm_mem (_lh.v) asks of memory except the
   frame's own cells, which the prologue has not written yet. *)
Definition llvm_pre (m0 : word -> option byte) (gp tp : word) (Sp lo : Z) (B : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR ra (Z_to_bv 64 (Sp + LLVM_FRAME)) gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 data) (Z_to_bv 64 (Z.of_nat (length D))) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LLVM_ENTRY_PC) fc None m0 (seg_rom rsegs) /\
    ent_dok lo m0 /\
    Sp mod 16 = 0 /\ stk rsegs m0 lo (Sp + LLVM_FRAME) /\ lo + LLVM_LOOP_K <= Sp /\
    Sp + LLVM_FRAME < 2 ^ 63 /\ W_BASE_PLAIN + W_LEN <= lo /\
    mem_inv rsegs m0 /\ relro_img m0 /\ wmem rsegs m0 B.

(* The invariant the entry walk keeps from 0x136c8 (the io block is in the frame) to 0x13890 (the first frame
   constant): llvm_mem's clauses, with the frame as the io block at sp+0x30 and junk around it. g_fail_next is
   NOT asked for here: the entry writes it (0x137fc) and the two exits prove their own. *)
Definition ent_mem (Sp lo : Z) (B : list byte) (m0 m : word -> option byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j30 j50 : list byte) : Prop :=
  munch (LLVM_FP Sp) m0 m /\ wmono rsegs m0 m /\
  ent_dok lo m0 /\
  Sp mod 16 = 0 /\ stk rsegs m lo Sp /\ lo + LLVM_LOOP_K <= Sp /\ Sp + LLVM_FRAME < 2 ^ 63 /\
  w_off_stack W_BASE_PLAIN (Z_to_bv 64 Sp) LLVM_LOOP_K /\ W_BASE_PLAIN + W_LEN <= lo /\
  mem_inv rsegs m /\ relro_img m /\ wmem rsegs m B /\
  length j30 = 48%nat /\ length j50 = 40%nat /\
  rw_cells rsegs m Sp
    ([CB 48 j30; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (ti_io_send timg_plain));
      C8 (Z_to_bv 64 (ti_io_recv timg_plain)); C8 (Z_to_bv 64 (ti_io_now timg_plain)); CB 40 j50]
     ++ llvm_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

(* across a callee whose footprint is its window [Sp - K, Sp) and the world (_fr.v llvm_mem_after_call) *)
Lemma ent_mem_after_call : forall Sp lo K B B' m0 m m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50,
  ent_mem Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  0 <= K <= LLVM_LOOP_K ->
  munch [(Sp - K, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp -> wmem rsegs m' B' ->
  ent_mem Sp lo B' m0 m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50.
Proof.
  intros Sp lo K B B' m0 m m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 HM HK MU WMO MI ST WM.
  unfold ent_mem in HM |- *.
  destruct HM as (HMU0 & HWMO0 & HDOK & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HMI & HRO & HWM
                  & HJ1 & HJ2 & HRW).
  split; [ eapply munch_trans; [exact HMU0|];
    intros x Hx; apply MU; cbn [outside] in Hx |- *;
      unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in Hx, HK; destruct Hx as (Hx1 & Hx2 & _);
      split; [lia | split; [exact Hx2 | exact I]] |].
  split; [eapply wmono_trans; [exact HWMO0 | exact WMO]|].
  unfold LLVM_LOOP_K, LLVM_FRAME in *.
  split; [exact HDOK|].
  split; [exact HSP|]. split; [exact ST|]. split; [exact HLO|]. split; [exact HSP2|].
  split; [exact HWOS|]. split; [exact HOWS|].
  split; [exact MI|].
  split; [eapply relro_munch_hi; [exact HRO | exact MU | unfold w_off_stack in HWOS;
            rewrite unsigned_lit in HWOS by (unfold W_BASE_PLAIN, W_LEN in *; lia); lia]|].
  split; [exact WM|]. split; [exact HJ1|]. split; [exact HJ2|].
  eapply rw_cells_transport; [exact HRW | exact MU | exact WMO |].
  unfold llvm_saved. cbn [disjoint_from cells_size csize app Nat.add].
  unfold w_off_stack in HWOS. rewrite unsigned_lit in HWOS by (unfold W_BASE_PLAIN, W_LEN in *; lia).
  split; [lia|]. split; [unfold W_BASE_PLAIN, W_LEN in *; lia | exact I].
Qed.

(* a callee that fills one span of the world: memset / memcpy on a world field (_fr.v llvm_mem_after_fill) *)
Lemma ent_mem_after_fill : forall Sp lo B m0 m m' k n src
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50,
  ent_mem Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  munch [(W_BASE_PLAIN + k, W_BASE_PLAIN + k + n)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' (W_BASE_PLAIN + k) [CB (Z.to_nat n) src] ->
  0 <= k -> 0 <= n -> k + n <= W_LEN ->
  ent_mem Sp lo (upd B k src) m0 m' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50.
Proof.
  intros Sp lo B m0 m m' k n src ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 HM MU WMO MI CZ Hk Hn Hkn.
  pose proof HM as HM1. unfold ent_mem in HM1.
  destruct HM1 as (_ & _ & _ & _ & HSTK & HLO & _ & _ & HOWS & _ & _ & HWM & _).
  assert (MUw : munch [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m').
  { replace (Sp - 0) with Sp by lia.
    apply (munch_span_in_world (W_BASE_PLAIN + k) n m m'); [exact MU | lia | lia]. }
  eapply (ent_mem_after_call Sp lo 0 B (upd B k src) m0 m m');
    [exact HM | unfold LLVM_LOOP_K; lia | exact MUw | exact WMO | exact MI | | ].
  - eapply stk_transport_disjoint; [exact HSTK | exact MU | exact WMO |].
    cbn [disjoint_from]. split; [lia | exact I].
  - exact (wm_fill rsegs W_BASE_PLAIN m m' B (W_BASE_PLAIN + k) k n src HWM MU WMO CZ eq_refl Hk Hn Hkn).
Qed.

(* llvm_mem (_lh.v) with the frame's first 120 bytes (sp+0x00 .. sp+0x77) left as junk: what holds at 0x14320
   on EVERY path, the loop's and the entry's two. *)
Definition llvm_mem0 (Sp lo : Z) (B : list byte) (m0 m : word -> option byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jf : list byte) : Prop :=
  munch (LLVM_FP Sp) m0 m /\ wmono rsegs m0 m /\
  Sp mod 16 = 0 /\ stk rsegs m lo Sp /\ lo + LLVM_LOOP_K <= Sp /\ Sp + LLVM_FRAME < 2 ^ 63 /\
  w_off_stack W_BASE_PLAIN (Z_to_bv 64 Sp) LLVM_LOOP_K /\ W_BASE_PLAIN + W_LEN <= lo /\
  mem_inv rsegs m /\ relro_img m /\ wmem rsegs m B /\
  length jf = 120%nat /\
  rw_cells rsegs m Sp ([CB 120 jf] ++ llvm_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Definition llvm_out0 (m0 : word -> option byte) (gp tp : word) (Sp lo : Z) (B : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
          t3 t4 t5 t6 : word) (m : word -> option byte) (jf : list byte),
    ms = MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2 r8 r9 a0 a1 a2 a3 a4 a5 a6 a7
                 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3 t4 t5 t6)
            F (Z_to_bv 64 LLVM_OUT_PC) fc None m (seg_rom rsegs) /\
    llvm_mem0 Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 jf.

(* what the epilogue leaves: a0 = 0, the 13 registers back, sp above the frame again *)
Definition llvm_ret0 (m0 : word -> option byte) (gp tp : word) (Sp lo : Z) (B : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (m : word -> option byte) (jf : list byte),
    ms = MS (mkR ra (Z_to_bv 64 (Sp + LLVM_FRAME)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m (seg_rom rsegs) /\
    llvm_mem0 Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 jf.

(* The loop's exit state is one of these: its four frame constants are 120 bytes of the junk block. *)
Lemma llvm_out_weaken : forall m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms,
  llvm_out data D m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  llvm_out0 m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms.
Proof.
  intros m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms HO.
  destruct HO as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r9 & r18 & r19 &
                  r20 & r21 & r22 & r23 & r24 & r25 & r26 & r27 & t3 & t4 & t5 & t6 & m & j10 & j28 & -> & HM).
  unfold llvm_mem in HM.
  destruct HM as (HMU & HWMO & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM
                  & HFN & HJ1 & HJ2 & HRW).
  unfold llvm_out0, llvm_mem0.
  pose proof (rw_cells_merge rsegs m Sp []
                (llvm_frame_consts ++ [CB 8 j10; C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); CB 80 j28])
                (llvm_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) as M.
  cbn [app] in M. rewrite <- app_assoc in M.
  specialize (M HRW).
  unfold llvm_frame_consts in M. cbn [cells_size csize Nat.add] in M. cbn [app] in M.
  pose proof M as M2. destruct M2 as [[Mwf _] _]. cbn [cells_wf cell_wf] in Mwf. destruct Mwf as [ML _].
  do 30 eexists. split; [reflexivity|].
  split; [exact HMU|]. split; [exact HWMO|]. split; [exact HSP|].
  split; [exact HSTK|]. split; [exact HLO|]. split; [exact HSP2|]. split; [exact HWOS|].
  split; [exact HOWS|]. split; [exact HMI|].
  split; [exact HRO|]. split; [exact HWM|].
  split; [exact ML | cbn [app]; exact M].
Qed.

(* 0x14320-0x1435c: a0 = 0, the 13 loads, addi sp,sp,0xe0, ret. Memory is only read. *)
Lemma llvm_exit0 : forall m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  llvm_out0 m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  (forall ms', llvm_ret0 m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q HO HK.
  destruct HO as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r9 & r18 & r19 &
                  r20 & r21 & r22 & r23 & r24 & r25 & r26 & r27 & t3 & t4 & t5 & t6 & m & jf & -> & HM).
  pose proof HM as HM0. unfold llvm_mem0 in HM.
  destruct HM as (_ & _ & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HMI & HRO & HWM & HJF & HRW).
  unfold llvm_saved in HRW. cbn [app] in HRW.
  unfold LLVM_OUT_PC, LLVM_LOOP_K, LLVM_FRAME in *.
  do 16 zstep.
  apply HK. unfold llvm_ret0, LLVM_FRAME. do 16 eexists. split; [reflexivity|]. exact HM0.
Qed.

(* ================================ 0x1386c-0x138ac: the two tests and the loop's registers ============== *)

(* At 0x1386c diginet_session_init has returned: a0 = its result (SPEC_OK on the model's path), s4 / s7 the
   cursor, s5 = &g_s, s9 = &g_fail_next, s10 = &M. 0x1386c `bnez a0` is the abort at 0x144e8 (the model's
   :1163); 0x13870 `beqz s7` leaves at 0x14320 with no pass of the loop; else 0x13874-0x138a8 load the loop's
   registers and the four frame constants and fall into the head at 0x138ac. *)
Lemma llvm_ent_after_init : forall Sp lo c10 B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    j30 j50 F fc Q rz q0 q1 q2 p1 p2 p3 p4 p5 p6 p7 x8 x9 x18 x19 x22 x24 x27 e3 e4 e5 e6,
  ent_mem Sp lo B25 m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  llvm_cursor D c10 -> g_fail_next B25 <= 1 ->
  (fi_n c10 = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 c10 B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2 x8 x9
             (Z_to_bv 64 0) p1 p2 p3 p4 p5 p6 p7
             x18 x19 (Z_to_bv 64 (data + fi_off c10)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             x22 (Z_to_bv 64 (fi_n c10)) x24 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) x27 e3 e4 e5 e6)
        F (Z_to_bv 64 0x1386c) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo c10 B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 F fc Q rz
    q0 q1 q2 p1 p2 p3 p4 p5 p6 p7 x8 x9 x18 x19 x22 x24 x27 e3 e4 e5 e6
    HM HC HFN HBf KHEAD KOUT.
  pose proof HM as HM0. unfold ent_mem in HM.
  destruct HM as (HMU & HWMO & HDOK & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HMI & HRO & HWM
                  & HJ1 & HJ2 & HRW).
  pose proof HC as HC0. unfold llvm_cursor, FUZZ_INPUT_MAX in HC.
  destruct HC as (HCa & HCb & HCc & HCd).
  pose proof HMU as HMUf0.
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  wk_facts. wk_eq_fact W_BASE_PLAIN.
  unfold w_off_stack in HWOS. rewrite unsigned_lit in HWOS by lia.
  unfold llvm_saved in HRW. cbn [app] in HRW.
  pose proof (munch_refl [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MUf.
  (* 0x1386c bnez a0: init returned SPEC_OK, the abort at 0x144e8 is not taken *)
  zstep. if_false.
  (* 0x13870 beqz s7 *)
  zstep.
  if_cases K; zify_cond K.
  - (* no input left: out at 0x14320, the frame constants never written *)
    assert (EN : fi_n c10 = 0) by lia.
    apply KOUT. rewrite (HBf EN).
    pose proof (rw_cells_merge rsegs m Sp []
                  [CB 48 j30; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (ti_io_send timg_plain));
                   C8 (Z_to_bv 64 (ti_io_recv timg_plain)); C8 (Z_to_bv 64 (ti_io_now timg_plain)); CB 40 j50]
                  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      as M.
    cbn [app] in M. specialize (M HRW). cbn [cells_size csize Nat.add] in M.
    pose proof M as M2. destruct M2 as [[Mwf _] _]. cbn [cells_wf cell_wf] in Mwf. destruct Mwf as [ML _].
    unfold llvm_out0, llvm_mem0, LLVM_OUT_PC, LLVM_FP, LLVM_FRAME, LLVM_LOOP_K, llvm_saved.
    do 30 eexists. split; [reflexivity|].
    split; [exact HMU|]. split; [exact HWMO|]. split; [exact HSP|].
    split; [exact HSTK|]. split; [lia|]. split; [lia|].
    split; [unfold w_off_stack; rewrite unsigned_lit by lia; lia|].
    split; [exact HOWS|].
    split; [exact HMI|]. split; [exact HRO|]. split; [exact HWM|].
    split; [exact ML | cbn [app]; exact M].
  - (* a pass to run: 0x13874-0x138a8 (s11 = 0, s8 = 1, s2 = 0x39, s1 = 7, and the four frame constants),
       then the head at 0x138ac *)
    assert (EN : fi_n c10 <> 0) by lia.
    assert (HDP : 0 < Z.of_nat (length D)) by lia.
    do 14 zstep.
    apply KHEAD.
    lazymatch goal with
    | H : rw_cells rsegs ?mf Sp (?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 ::
                                 ?b1 :: ?b2 :: ?b3 :: ?b4 :: ?b5 :: ?b6 :: ?post) |- _ =>
        pose proof (rw_cells_merge rsegs mf Sp [a1; a2; a3; a4; a5] [b1; b2; b3; b4; b5; b6] post H) as M
    end.
    cbn [app cells_size csize Nat.add] in M.
    pose proof M as M2. destruct M2 as [[Mwf _] _]. cbn [cells_wf cell_wf] in Mwf.
    destruct Mwf as (_ & _ & ML10 & _ & _ & ML80 & _).
    lazymatch goal with H : munch _ m0 ?mf |- _ =>
      assert (HMUn : munch (LLVM_FP Sp) m0 mf)
        by (unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME; exact H) end.
    destruct (ent_dok_mem lo Sp m0 _ HDOK HMUn ltac:(lia) ltac:(unfold LLVM_LOOP_K; lia)
                ltac:(unfold LLVM_FRAME; lia) HDP) as (HDb & HDw & HDi).
    unfold LLVM_FRAME, LLVM_LOOP_K in HDi.
    unfold llvm_head, LLVM_HEAD_PC, llvm_mem, LLVM_FP, LLVM_LOOP_K, LLVM_FRAME,
           llvm_frame_consts, llvm_saved.
    do 22 eexists. split; [reflexivity|].
    split; [unfold OPS_MAX; lia|]. split; [exact EN|]. split; [exact HC0|].
    split; [assumption|]. split; [assumption|].
    split; [exact HDb|]. split; [exact HSP|]. split; [assumption|]. split; [lia|]. split; [lia|].
    split; [unfold w_off_stack; rewrite unsigned_lit by lia; lia|].
    split; [exact HOWS|]. split; [exact HDw|]. split; [exact HDi|].
    split; [assumption|].
    split; [eapply relro_munch_hi; [exact HRO | eassumption | lia]|].
    split; [assumption|]. split; [exact HFN|].
    split; [exact ML10|]. split; [exact ML80|].
    cbn [app]. exact M.
Qed.

(* ================================ the world the scalars and M build ================================ *)

Lemma ent_len_upd : forall (Bx v : list byte) k, 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length Bx) ->
  Z.of_nat (length (upd Bx k v)) = Z.of_nat (length Bx).
Proof. intros Bx v k Hk Hl. rewrite length_upd; [reflexivity | exact Hk | exact Hl]. Qed.

(* two adjacent writes are one (Prog/T/diginet_session_init.v upd_merge_r, same text) *)
Lemma ent_merge_r : forall (bs v w : list byte) k j, 0 <= k -> j = k + Z.of_nat (length v) ->
  j + Z.of_nat (length w) <= Z.of_nat (length bs) ->
  upd (upd bs k v) j w = upd bs k (v ++ w).
Proof.
  intros bs v w k j Hk -> Hl. apply nth_error_ext. intros i.
  assert (L1 : length (upd bs k v) = length bs) by (apply length_upd; lia).
  rewrite (ne_upd (upd bs k v) w (k + Z.of_nat (length v)) i) by (first [ lia | (rewrite L1; lia) ]).
  rewrite (ne_upd bs v k i) by lia.
  rewrite (ne_upd bs (v ++ w) k i) by (first [ lia | (rewrite length_app; lia) ]).
  rewrite length_app, (Z2Nat.inj_add k (Z.of_nat (length v))) by lia. rewrite Nat2Z.id.
  destruct (Nat.leb_spec (Z.to_nat k + length v) i);
  destruct (Nat.ltb_spec i (Z.to_nat k + length v + length w));
  destruct (Nat.leb_spec (Z.to_nat k) i);
  destruct (Nat.ltb_spec i (Z.to_nat k + (length v + length w)));
  destruct (Nat.ltb_spec i (Z.to_nat k + length v));
  cbn [andb]; try reflexivity; try (exfalso; lia);
  first [ (rewrite nth_error_app1 by lia; reflexivity)
        | (rewrite nth_error_app2 by lia; f_equal; lia) ].
Qed.

(* a write the next write at the same offset covers completely is dead *)
Lemma ent_upd_cover : forall (bs v w : list byte) k, 0 <= k -> (length v <= length w)%nat ->
  k + Z.of_nat (length w) <= Z.of_nat (length bs) ->
  upd (upd bs k v) k w = upd bs k w.
Proof.
  intros bs v w k Hk Hvw Hl. apply nth_error_ext. intros i.
  assert (L1 : length (upd bs k v) = length bs) by (apply length_upd; lia).
  rewrite (ne_upd (upd bs k v) w k i) by (first [ lia | (rewrite L1; lia) ]).
  rewrite (ne_upd bs w k i) by lia.
  destruct ((Z.to_nat k <=? i) && (i <? Z.to_nat k + length w))%nat eqn:C; [reflexivity|].
  apply andb_false_iff in C.
  rewrite (ne_upd bs v k i) by lia.
  destruct ((Z.to_nat k <=? i) && (i <? Z.to_nat k + length v))%nat eqn:C2; [|reflexivity].
  exfalso. apply andb_true_iff in C2. destruct C2 as [C2a C2b].
  apply Nat.leb_le in C2a. apply Nat.ltb_lt in C2b.
  destruct C as [C|C]; [apply Nat.leb_gt in C | apply Nat.ltb_ge in C]; lia.
Qed.

Lemma ent_len_DESK : Z.of_nat (length DESK) = 6.
Proof. reflexivity. Qed.

(* The ten world writes of 0x137fc-0x13844, in the machine's order, are the model's :1147-1155 chain.
   The scalars are written in a different order (all four spans disjoint), and the machine memsets M + 8
   where the model zeroes all of M: the two writes that follow, M.desk_known (4 bytes at M) and M.desk
   (6 bytes at M + 4), cover the 8 bytes the orders differ on. *)
Lemma ent_tail_eq : forall flags Bc dk,
  Z.of_nat (length Bc) = W_LEN -> dk = Cfg_desk_mac_set Bc ->
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd Bc
       64968 (put 1 0))
       64972 (put 4 (Z.land (Z.shiftr flags 3) 1)))
       64976 (put 4 0))
       65000 (put 8 1000000))
       8 (repeat (Z_to_bv 8 0) 1640))
       0 (put 4 dk))
       4 DESK)
       64980 (put 4 0))
       64984 (put 4 0))
       65008 (put 8 0)
  = ent_tail_world flags Bc.
Proof.
  intros flags Bc dk HL Hdk.
  assert (EWL : W_LEN = 65616) by reflexivity.
  assert (P1 : forall v : Z, Z.of_nat (length (put 1 v)) = 1) by (intros; rewrite length_put; reflexivity).
  assert (P4 : forall v : Z, Z.of_nat (length (put 4 v)) = 4) by (intros; rewrite length_put; reflexivity).
  assert (P8 : forall v : Z, Z.of_nat (length (put 8 v)) = 8) by (intros; rewrite length_put; reflexivity).
  assert (R1640 : Z.of_nat (length (repeat (Z_to_bv 8 0) 1640)) = 1640) by (rewrite repeat_length; lia).
  assert (R1648 : Z.of_nat (length (repeat (Z_to_bv 8 0) 1648)) = 1648) by (rewrite repeat_length; lia).
  assert (R8 : Z.of_nat (length (repeat (Z_to_bv 8 0) 8)) = 8) by (rewrite repeat_length; lia).
  pose proof ent_len_DESK as LD.
  (* the four scalar writes, in either order, give the same world *)
  set (p1 := put 1 0) in *. set (p2 := put 4 (Z.land (Z.shiftr flags 3) 1)) in *.
  set (p3 := put 4 0) in *. set (p4 := put 8 1000000) in *.
  assert (Lp1 : Z.of_nat (length p1) = 1) by (unfold p1; apply P1).
  assert (Lp2 : Z.of_nat (length p2) = 4) by (unfold p2; apply P4).
  assert (Lp3 : Z.of_nat (length p3) = 4) by (unfold p3; apply P4).
  assert (Lp4 : Z.of_nat (length p4) = 8) by (unfold p4; apply P8).
  set (S := upd (upd (upd (upd Bc 64968 p1) 64972 p2) 64976 p3) 65000 p4) in *.
  assert (L1 : Z.of_nat (length (upd Bc 64968 p1)) = W_LEN)
    by (rewrite ent_len_upd; [exact HL | lia | rewrite Lp1, HL; lia]).
  assert (L2 : Z.of_nat (length (upd (upd Bc 64968 p1) 64972 p2)) = W_LEN)
    by (rewrite ent_len_upd; [exact L1 | lia | rewrite Lp2, L1; lia]).
  assert (L3 : Z.of_nat (length (upd (upd (upd Bc 64968 p1) 64972 p2) 64976 p3)) = W_LEN)
    by (rewrite ent_len_upd; [exact L2 | lia | rewrite Lp3, L2; lia]).
  assert (LS : Z.of_nat (length S) = W_LEN)
    by (unfold S; rewrite ent_len_upd; [exact L3 | lia | rewrite Lp4, L3; lia]).
  (* the desk_mac_set the model reads is the one the config left *)
  assert (EDK : Cfg_desk_mac_set (upd S 0 (repeat (Z_to_bv 8 0) 1648)) = dk).
  { rewrite Hdk. unfold Cfg_desk_mac_set, A_Cfg_desk_mac_set, OFF_g_cfg.
    rewrite (s32_at_upd_out S (repeat (Z_to_bv 8 0) 1648) 0 (65024 + 12)) by (rewrite ?R1648, ?LS; lia).
    unfold S.
    rewrite (s32_at_upd_out _ p4 65000 (65024 + 12)) by (rewrite ?Lp4, ?L3; lia).
    rewrite (s32_at_upd_out _ p3 64976 (65024 + 12)) by (rewrite ?Lp3, ?L2; lia).
    rewrite (s32_at_upd_out _ p2 64972 (65024 + 12)) by (rewrite ?Lp2, ?L1; lia).
    rewrite (s32_at_upd_out _ p1 64968 (65024 + 12)) by (rewrite ?Lp1, ?HL; lia).
    reflexivity. }
  unfold ent_tail_world, set_g_raw, set_g_now, set_g_fail_next, set_g_last_counter,
         set_M_desk_known, set_M_desk, set_g_nq, set_g_ncmd, set_g_rx,
         A_M_desk_known, A_M_desk, OFF_M, OFF_g_raw, OFF_g_now, OFF_g_fail_next, OFF_g_last_counter,
         OFF_g_nq, OFF_g_ncmd, OFF_g_rx, SZ_M.
  change (b8 0) with (Z_to_bv 8 0). change (Z.to_nat 1648) with 1648%nat.
  cbv beta zeta.
  try replace (0 + 0) with 0 by lia. try replace (0 + 4) with 4 by lia.
  fold p1 p2 p3 p4.
  (* the model writes the four scalars in another order; the four spans are disjoint *)
  assert (M1 : Z.of_nat (length (upd Bc 64972 p2)) = W_LEN)
    by (rewrite ent_len_upd; [exact HL | lia | rewrite Lp2, HL; lia]).
  replace (upd (upd (upd (upd Bc 64972 p2) 65000 p4) 64968 p1) 64976 p3) with S.
  2: { unfold S.
       rewrite (upd_upd_comm (upd Bc 64972 p2) p4 p1 65000 64968)
         by (rewrite ?Lp1, ?Lp4, ?M1; lia).
       rewrite (upd_upd_comm Bc p2 p1 64972 64968) by (rewrite ?Lp1, ?Lp2, ?HL; lia).
       rewrite (upd_upd_comm (upd (upd Bc 64968 p1) 64972 p2) p4 p3 65000 64976)
         by (rewrite ?Lp3, ?Lp4, ?L2; lia).
       reflexivity. }
  rewrite EDK.
  (* the two M arrangements *)
  rewrite (ent_merge_r (upd S 8 (repeat (Z_to_bv 8 0) 1640)) (put 4 dk) DESK 0 4)
    by (rewrite ?P4, ?LD, ?length_upd; rewrite ?R1640, ?LS; lia).
  rewrite (ent_merge_r (upd S 0 (repeat (Z_to_bv 8 0) 1648)) (put 4 dk) DESK 0 4)
    by (rewrite ?P4, ?LD, ?length_upd; rewrite ?R1648, ?LS; lia).
  replace (repeat (Z_to_bv 8 0) 1648)
    with (repeat (Z_to_bv 8 0) 8 ++ repeat (Z_to_bv 8 0) 1640) by (rewrite <- repeat_app; reflexivity).
  rewrite <- (ent_merge_r S (repeat (Z_to_bv 8 0) 8) (repeat (Z_to_bv 8 0) 1640) 0 8)
    by (rewrite ?R8, ?R1640, ?LS; lia).
  rewrite (upd_upd_comm S (repeat (Z_to_bv 8 0) 8) (repeat (Z_to_bv 8 0) 1640) 0 8)
    by (rewrite ?R8, ?R1640, ?LS; lia).
  rewrite (ent_upd_cover (upd S 8 (repeat (Z_to_bv 8 0) 1640)) (repeat (Z_to_bv 8 0) 8)
             (put 4 dk ++ DESK) 0);
    [ reflexivity
    | lia
    | rewrite repeat_length, length_app, length_put; cbn [length]; lia
    | rewrite length_app, length_put, length_upd; [ | lia | rewrite R1640, LS; lia ];
      cbn [Z.of_nat]; rewrite LS; cbn [length]; lia ].
Qed.

(* ================================ g_fail_next through the entry's world ================================ *)

(* one write of the chain: it keeps the world's length, and g_fail_next when it misses the byte.
   The written span's length is a PARAMETER: a side goal that reduces `Z.to_nat SZ_g_s` to a unary natural
   is ruinous (18264 constructors; a 24 GB OOM, 2026-10-31 01:3xZ). *)
Lemma ent_fn_step : forall (Bx v : list byte) (k g n : Z),
  Z.of_nat (length Bx) = W_LEN -> g_fail_next Bx = g -> Z.of_nat (length v) = n ->
  0 <= k -> k + n <= W_LEN ->
  (k + n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  Z.of_nat (length (upd Bx k v)) = W_LEN /\ g_fail_next (upd Bx k v) = g.
Proof.
  intros Bx v k g n HL HG Hv Hk Hn Hd. split.
  - rewrite ent_len_upd; [exact HL | exact Hk | rewrite HL, Hv; exact Hn].
  - rewrite <- HG. unfold g_fail_next.
    rewrite u_at_upd_out; [reflexivity | exact Hk | unfold OFF_g_fail_next; lia
                          | rewrite Hv; cbn [Z.of_nat]; lia | rewrite HL, Hv; exact Hn].
Qed.

Lemma ent_lp1 : forall v, Z.of_nat (length (put 1 v)) = 1.
Proof. intros v. rewrite length_put. reflexivity. Qed.
Lemma ent_lp4 : forall v, Z.of_nat (length (put 4 v)) = 4.
Proof. intros v. rewrite length_put. reflexivity. Qed.
Lemma ent_lp8 : forall v, Z.of_nat (length (put 8 v)) = 8.
Proof. intros v. rewrite length_put. reflexivity. Qed.

Ltac ent_fstep L G v k n Ln :=
  let L' := fresh "LL" in let G' := fresh "GG" in
  destruct (ent_fn_step _ v k _ n L G Ln ltac:(lia)
              ltac:(unfold W_LEN; lia) ltac:(unfold OFF_g_fail_next; lia)) as [L' G'].

(* The entry's world has g_fail_next = 0 (fuzz_transport.c:1149) and the world's length. Read off the
   machine's own chain (ent_tail_eq): the first write is the byte, and the nine after it miss it. *)
Lemma ent_fn_tail : forall flags Bc dk, Z.of_nat (length Bc) = W_LEN -> dk = Cfg_desk_mac_set Bc ->
  g_fail_next (ent_tail_world flags Bc) = 0 /\ Z.of_nat (length (ent_tail_world flags Bc)) = W_LEN.
Proof.
  intros flags Bc dk HL Hdk. rewrite <- (ent_tail_eq flags Bc dk HL Hdk).
  assert (R1640 : Z.of_nat (length (repeat (Z_to_bv 8 0) 1640)) = 1640) by (rewrite repeat_length; lia).
  assert (L0 : Z.of_nat (length (upd Bc 64968 (put 1 0))) = W_LEN)
    by (rewrite ent_len_upd; [exact HL | lia | rewrite ent_lp1, HL; unfold W_LEN; lia]).
  assert (G0 : g_fail_next (upd Bc 64968 (put 1 0)) = 0).
  { unfold g_fail_next, OFF_g_fail_next.
    rewrite u_at_upd_put; [reflexivity | lia | rewrite HL; cbn [Z.of_nat]; unfold W_LEN; lia]. }
  ent_fstep L0 G0 (put 4 (Z.land (Z.shiftr flags 3) 1)) 64972 4 (ent_lp4 (Z.land (Z.shiftr flags 3) 1)).
  ent_fstep LL GG (put 4 0) 64976 4 (ent_lp4 0).
  ent_fstep LL0 GG0 (put 8 1000000) 65000 8 (ent_lp8 1000000).
  ent_fstep LL1 GG1 (repeat (Z_to_bv 8 0) 1640) 8 1640 R1640.
  ent_fstep LL2 GG2 (put 4 dk) 0 4 (ent_lp4 dk).
  ent_fstep LL3 GG3 DESK 4 6 ent_len_DESK.
  ent_fstep LL4 GG4 (put 4 0) 64980 4 (ent_lp4 0).
  ent_fstep LL5 GG5 (put 4 0) 64984 4 (ent_lp4 0).
  ent_fstep LL6 GG6 (put 8 0) 65008 8 (ent_lp8 0).
  split; [exact GG7 | exact LL7].
Qed.

(* diginet_session_init writes only g_s [1648, 19912) (diginet_session.c:63-71), so it leaves g_fail_next
   (0xfdc8 = 64968). *)
Lemma ent_fn_init : forall B c s rc n nt cx B' r, Z.of_nat (length B) = W_LEN ->
  diginet_session_init_m B c s rc n nt cx = Some (B', r) ->
  g_fail_next B' = g_fail_next B /\ Z.of_nat (length B') = W_LEN.
Proof.
  intros B c s rc n nt cx B' r HL H.
  assert (Lgs : Z.of_nat (length (put (Z.to_nat SZ_g_s) 0)) = 18264).
  { rewrite length_put, Z2Nat.id by (unfold SZ_g_s; lia). reflexivity. }
  assert (Lcfg : Z.of_nat (length (sub B OFF_g_cfg (Z.to_nat SZ_g_cfg))) = 60).
  { rewrite length_sub; [rewrite Z2Nat.id by (unfold SZ_g_cfg; lia); reflexivity
                        | unfold OFF_g_cfg; lia
                        | rewrite HL, Z2Nat.id by (unfold SZ_g_cfg; lia);
                          unfold OFF_g_cfg, SZ_g_cfg, W_LEN; lia]. }
  assert (Ldm : Z.of_nat (length (Cfg_desk_mac B)) = 6).
  { unfold Cfg_desk_mac. rewrite length_sub;
      [reflexivity | unfold A_Cfg_desk_mac, OFF_g_cfg; lia
      | rewrite HL; unfold A_Cfg_desk_mac, OFF_g_cfg, W_LEN; cbn [Z.of_nat]; lia]. }
  unfold diginet_session_init_m in H.
  destruct ((s =? 0) || (nt =? 0))%bool;
    [injection H as H1 H2; subst B'; split; [reflexivity | exact HL]|].
  destruct ((Cfg_max_cmds B =? 0) || (Cfg_max_body B <? DIGINET_CMD_MAX_LEN) ||
            (DIGINET_MAX_BODY_LEN <? Cfg_max_body B) || (255 <? Cfg_max_cmds B))%bool;
    [injection H as H1 H2; subst B'; split; [reflexivity | exact HL]|].
  cbv zeta in H.
  unfold set_S_io_ctx, set_S_io_send, set_S_io_recv, set_S_io_now_us, set_S_notify, set_S_notify_ctx,
         set_S_state, set_S_desk_mac, set_S_desk_known,
         A_S_cfg_host_mac, A_S_io_ctx, A_S_io_send, A_S_io_recv, A_S_io_now_us, A_S_notify, A_S_notify_ctx,
         A_S_state, A_S_desk_mac, A_S_desk_known, OFF_g_s in H.
  (* The memset's 18264 zero bytes are `put (Z.to_nat SZ_g_s) 0`. Left as that term, a side goal's lia (or
     any cbn reaching it) reduces Z.to_nat 18264 to a UNARY natural and then the list itself: a 24 GB OOM
     (2026-10-31 01:3xZ-02:2xZ, three builds). clearbody makes both spans opaque, so only their lengths,
     which are hypotheses, are ever used. *)
  set (GZ := put (Z.to_nat SZ_g_s) 0) in *; clearbody GZ.
  set (CFG := sub B OFF_g_cfg (Z.to_nat SZ_g_cfg)) in *; clearbody CFG.
  set (DM := Cfg_desk_mac B) in *; clearbody DM.
  (* H, an equation between two 19912-byte worlds, is substituted away before the chain below. *)
  destruct (negb (Cfg_desk_mac_set B =? 0)); injection H as H1 H2; subst B'; clear H2;
    assert (L0 : Z.of_nat (length (upd B 1648 GZ)) = W_LEN)
      by (rewrite ent_len_upd; [exact HL | lia | rewrite Lgs, HL; unfold W_LEN; lia]);
    assert (G0 : g_fail_next (upd B 1648 GZ) = g_fail_next B)
      by (unfold g_fail_next, OFF_g_fail_next;
          rewrite u_at_upd_out; [reflexivity | lia | lia | rewrite Lgs; lia
                                | rewrite Lgs, HL; unfold W_LEN; lia]);
    ent_fstep L0 G0 CFG 1648 60 Lcfg;
    ent_fstep LL GG (put 8 c) (1648 + 64 + 0) 8 (ent_lp8 c);
    ent_fstep LL0 GG0 (put 8 s) (1648 + 64 + 8) 8 (ent_lp8 s);
    ent_fstep LL1 GG1 (put 8 rc) (1648 + 64 + 16) 8 (ent_lp8 rc);
    ent_fstep LL2 GG2 (put 8 n) (1648 + 64 + 24) 8 (ent_lp8 n);
    ent_fstep LL3 GG3 (put 8 nt) (1648 + 96) 8 (ent_lp8 nt);
    ent_fstep LL4 GG4 (put 8 cx) (1648 + 104) 8 (ent_lp8 cx);
    ent_fstep LL5 GG5 (put 4 DIGINET_S_IDLE) (1648 + 112) 4 (ent_lp4 DIGINET_S_IDLE).
  - ent_fstep LL6 GG6 DM (1648 + 120) 6 Ldm.
    ent_fstep LL7 GG7 (put 4 1) (1648 + 116) 4 (ent_lp4 1).
    split; [exact GG8 | exact LL8].
  - split; [exact GG6 | exact LL6].
Qed.

(* the 6 bytes of DESK in .rodata at 0x10486 (fuzz_transport.c:109-113; TCb.v DESK), read-only *)
Lemma ent_desk_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10486 DESK.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

(* the bytes of a run of cells inside an rw_cells fact (Prog/T/send_data.v cells_bytes_at, same text) *)
Lemma ent_cells_bytes_at : forall m A pre mid post,
  rw_cells rsegs m A (pre ++ mid ++ post) -> cells_wf pre ->
  bytes_at rsegs m (A + Z.of_nat (cells_size pre)) (cells_bytes mid).
Proof.
  intros m A pre mid post H Hp. destruct H as [[Hwf Hb] _].
  rewrite !cells_bytes_app in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hp.
  apply bytes_at_app in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

(* ================================ 0x137fc-0x13868: the scalars, M and the init call ================= *)

(* At 0x137fc the config is built: s0 = (flags >> 3) & 1 (g_raw), s2 = (flags >> 2) & 1 (desk_mac_set),
   s1 = &g_cfg, a2 = 0xf4240 = 1000000 (g_now), s9 = &g_fail_next, s4 / s7 the cursor.
   0x137fc-0x13808 the four scalars; 0x1380c-0x13820 memset(&M + 8, 0, 0x668); 0x13824 M.desk_known;
   0x13838 memcpy(&M.desk, DESK, 6); 0x1383c-0x13844 g_nq = g_ncmd = 0 and g_rx = 0; 0x13868
   diginet_session_init(&g_s, &g_cfg, sp + 0x30, notice, NULL). *)
Lemma llvm_ent_tail : forall Sp lo flags c10 Bc B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    j30 j50 F fc Q rz q0 q1 q2 p0 p1 p3 p4 p5 p6 p7 x19 x21 x22 x24 x26 x27 e3 e4 e5 e6,
  memset_contract -> memcpy_contract -> diginet_session_init_contract ->
  ent_mem Sp lo Bc m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  llvm_cursor D c10 ->
  Cfg_desk_mac_set Bc = Z.land (Z.shiftr flags 2) 1 ->
  diginet_session_init_m (ent_tail_world flags Bc) 0 (ti_io_send timg_plain) (ti_io_recv timg_plain)
    (ti_io_now timg_plain) (ti_notice timg_plain) 0 = Some (B25, SPEC_OK) ->
  (fi_n c10 = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 c10 B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2
             (Z_to_bv 64 (Z.land (Z.shiftr flags 3) 1))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_cfg))
             p0 p1 (Z_to_bv 64 1000000) p3 p4 p5 p6 p7
             (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1))
             x19 (Z_to_bv 64 (data + fi_off c10)) x21 x22 (Z_to_bv 64 (fi_n c10)) x24
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) x26 x27 e3 e4 e5 e6)
        F (Z_to_bv 64 0x137fc) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo flags c10 Bc B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 F fc Q
    rz q0 q1 q2 p0 p1 p3 p4 p5 p6 p7 x19 x21 x22 x24 x26 x27 e3 e4 e5 e6
    MSC MCPY DIC HM HC HDMS HINIT HBf KHEAD KOUT.
  pose proof HM as HM0. unfold ent_mem in HM.
  destruct HM as (HMU & HWMO & HDOK & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HMI & HRO & HWM
                  & HJ1 & HJ2 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length Bc) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  wk_facts. wk_eq_fact W_BASE_PLAIN. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_M. wk_eq_fact OFF_g_cfg.
  unfold w_off_stack in HWOS. rewrite unsigned_lit in HWOS by lia.
  unfold llvm_saved in HRW. cbn [app] in HRW.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MUr.
  pose proof (wmono_refl rsegs m) as WMOr.
  (* 0x137fc-0x13808: g_fail_next = 0, g_raw, g_last_counter = 0, g_now = 0xf4240 *)
  do 4 zstep.
  (* 0x1380c-0x1381c: s10 = &M, then memset(&M + 8, 0, 0x668) at 0x13820 *)
  do 6 zstep.
  lazymatch goal with Hw : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?W] |- _ => set (W4 := W) in * end.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ W4] |- _ =>
    pose proof (wm_len rsegs W_BASE_PLAIN mm W4 Hw) as LW4n end.
  assert (LW4 : Z.of_nat (length W4) = W_LEN)
    by (rewrite LW4n, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ W4] |- _ =>
    assert (CW : rw_cells rsegs mm 206744 [CB (Z.to_nat 1640) (sub W4 8 1640)])
      by (pose proof (wm_cell rsegs W_BASE_PLAIN mm W4 8 1640 206744 Hw ltac:(lia) ltac:(lia) ltac:(lia))
            as P; rewrite length_sub in P by (rewrite ?LW4; unfold W_LEN; lia); exact P) end.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ W4] |- _ =>
    assert (HMW4 : ent_mem Sp lo W4 m0 mm ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 Bc W4 m0 m mm);
            [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
            | assumption | assumption | assumption ]) end.
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (MSC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm
                (sub W4 8 1640)) end.
    - rewrite !unsigned_lit by lia. exact CW.
    - assumption. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m1 &
                     -> & MU1 & WMO1 & MI1 & CZ1).
  rewrite !unsigned_lit in MU1, CZ1 by lia.
  change (0 mod 256) with 0 in CZ1.
  replace 206744 with (W_BASE_PLAIN + 8) in MU1, CZ1 by lia.
  (* ent_mem for the world after the four scalar stores *)
  assert (HM1 : ent_mem Sp lo (upd W4 8 (repeat (Z_to_bv 8 0) (Z.to_nat 1640))) m0 m1
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
    by (eapply (ent_mem_after_fill Sp lo W4 m0 _ m1 8 1640);
          [ exact HMW4 | exact MU1 | exact WMO1 | exact MI1 | exact CZ1 | lia | lia
          | unfold W_LEN; lia ]).
  (* 0x13824 M.desk_known = s2; 0x13828-0x13834 the memcpy arguments; 0x13838 memcpy(&M.desk, DESK, 6) *)
  rewrite (ret_pc_even 0x13824) by (first [lia | reflexivity]).
  set (Wa := upd W4 8 (repeat (Z_to_bv 8 0) (Z.to_nat 1640))) in *.
  assert (LWa : Z.of_nat (length Wa) = W_LEN)
    by (unfold Wa; rewrite ent_len_upd;
        [exact LW4 | lia | rewrite repeat_length, LW4; unfold W_LEN; lia]).
  clear MUr WMOr.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m1) as MUr.
  pose proof HM1 as HM1c. unfold ent_mem in HM1c.
  destruct HM1c as (_ & _ & _ & _ & HSTK1 & _ & _ & _ & _ & HMI1 & HRO1 & HWM1 & _ & _ & HRW1).
  unfold llvm_saved in HRW1. cbn [app] in HRW1.
  try clear HRW. try clear HSTK. try clear HMI. try clear HRO. try clear HWM. clear MU1 CZ1.
  pose proof (wmono_refl rsegs m1) as WMOr.
  do 6 zstep.
  lazymatch goal with Hw : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?W] |- _ => set (Wb := W) in * end.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ Wb] |- _ =>
    pose proof (wm_len rsegs W_BASE_PLAIN mm Wb Hw) as LWbn end.
  assert (LWb : Z.of_nat (length Wb) = W_LEN)
    by (rewrite LWbn, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ Wb] |- _ =>
    assert (HMWb : ent_mem Sp lo Wb m0 mm ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 Wa Wb m0 m1 mm);
            [ exact HM1 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
            | assumption | assumption | assumption ]);
    assert (CWd : rw_cells rsegs mm 206740 [CB (Z.to_nat 6) (sub Wb 4 6)])
      by (pose proof (wm_cell rsegs W_BASE_PLAIN mm Wb 4 6 206740 Hw ltac:(lia) ltac:(lia) ltac:(lia))
            as P; rewrite length_sub in P by (rewrite ?LWb; unfold W_LEN; lia); exact P) end.
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm
                DESK (sub Wb 4 6)) end.
    - rewrite !unsigned_lit by lia. apply ent_desk_at. assumption.
    - rewrite !unsigned_lit by lia. reflexivity.
    - rewrite !unsigned_lit by lia. exact CWd.
    - rewrite !unsigned_lit by lia. lia.
    - assumption. }
  intros ms' Hpost. unfold memcpy_post in Hpost.
  destruct Hpost as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & mc &
                     -> & MU2 & WMO2 & MI2 & CZ2 & BA2).
  rewrite !unsigned_lit in MU2, CZ2 by lia.
  replace 206740 with (W_BASE_PLAIN + 4) in MU2, CZ2 by lia.
  assert (HM2 : ent_mem Sp lo (upd Wb 4 DESK) m0 mc
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
    by (eapply (ent_mem_after_fill Sp lo Wb m0 _ mc 4 6);
          [ exact HMWb | exact MU2 | exact WMO2 | exact MI2 | exact CZ2 | lia | lia
          | unfold W_LEN; lia ]).
  (* 0x1383c-0x13844: g_nq = g_ncmd = 0 and g_rx = 0; 0x13848-0x13864 the arguments of
     diginet_session_init(&g_s, &g_cfg, sp + 0x30, notice, NULL); 0x13868 the call *)
  rewrite (ret_pc_even 0x1383c) by (first [lia | reflexivity]).
  pose proof HM2 as HM2c. unfold ent_mem in HM2c.
  destruct HM2c as (_ & _ & _ & _ & HSTK2 & _ & _ & _ & _ & HMI2 & HRO2 & HWM2 & _ & _ & HRW2).
  unfold llvm_saved in HRW2. cbn [app] in HRW2.
  try clear HRW1. try clear HSTK1. try clear HMI1. try clear HRO1. try clear HWM1.
  clear MU2 CZ2 MUr WMOr.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mc) as MUr.
  pose proof (wmono_refl rsegs mc) as WMOr.
  do 12 zstep.
  lazymatch goal with Hw : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?W] |- _ => set (Wd := W) in * end.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ Wd] |- _ =>
    assert (HMWd : ent_mem Sp lo Wd m0 mm ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 (upd Wb 4 DESK) Wd m0 mc mm);
            [ exact HM2 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
            | assumption | assumption | assumption ]) end.
  (* the world the ten writes built is the model's :1147-1155 chain *)
  assert (EWT : Wd = ent_tail_world flags Bc).
  { unfold Wd, Wb, Wa, W4. unfold OFF_g_fail_next.
    change (Z.to_nat 1640) with 1640%nat.
    apply (ent_tail_eq flags Bc (Z.land (Z.shiftr flags 2) 1) LBz). symmetry. exact HDMS. }
  rewrite EWT in HMWd.
  (* the io block the frame holds at sp + 0x30, as the contract reads it *)
  pose proof HMWd as HMWdc. unfold ent_mem in HMWdc.
  destruct HMWdc as (_ & _ & _ & _ & HSTK3 & _ & _ & _ & _ & HMI3 & HRO3 & HWM3 & _ & _ & HRW3).
  unfold llvm_saved in HRW3. cbn [app] in HRW3.
  lazymatch goal with Hf : rw_cells rsegs ?mm Sp (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) |- _ =>
    pose proof (ent_cells_bytes_at mm Sp [c1] [c2; c3; c4; c5] rest) as BIO end.
  cbn [app cells_size csize cells_bytes cbytes Nat.add] in BIO.
  rewrite !app_nil_r in BIO.
  specialize (BIO ltac:(assumption) ltac:(cbn [cells_wf cell_wf]; split; [exact HJ1 | exact I])).
  rewrite !le8_put in BIO.
  eapply evt_cut.
  { eapply (DIC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo
              (Sp + 48) 0 (ti_io_send timg_plain) (ti_io_recv timg_plain) (ti_io_now timg_plain)
              (ti_notice timg_plain) 0 SPEC_OK (ent_tail_world flags Bc) B25).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - cbv [ti_io_send timg_plain]; lia.
    - cbv [ti_io_recv timg_plain]; lia.
    - cbv [ti_io_now timg_plain]; lia.
    - cbv [ti_notice timg_plain]; lia.
    - lia.
    - exact BIO.
    - unfold arg_blk, off_world, off_window, diginet_session_init_FRAME.
      rewrite unsigned_lit by lia.
      split; [lia|]. split; [lia|]. split; [lia | lia].
    - Z.div_mod_to_equations; lia.
    - exact HWM3.
    - exact HINIT.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK3.
    - rewrite unsigned_lit by lia. unfold diginet_session_init_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold diginet_session_init_FRAME. lia.
    - exact HMI3. }
  intros ms' Hpost.
  destruct Hpost as (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & i3 & i4 & i5 & i6 & mi &
                     -> & MU3 & WMO3 & MI3 & ST3 & WM3).
  rewrite unsigned_lit in MU3, ST3 by lia.
  assert (HM3 : ent_mem Sp lo B25 m0 mi ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
    by (eapply (ent_mem_after_call Sp lo diginet_session_init_FRAME (ent_tail_world flags Bc) B25 m0 _ mi);
          [ exact HMWd | unfold diginet_session_init_FRAME, LLVM_LOOP_K; lia | exact MU3 | exact WMO3
          | exact MI3 | exact ST3 | exact WM3 ]).
  rewrite (ret_pc_even 0x1386c) by (first [lia | reflexivity]).
  change SPEC_OK with 0.
  eapply llvm_ent_after_init;
    [ exact HM3 | exact HC
    | destruct (ent_fn_init (ent_tail_world flags Bc) 0 (ti_io_send timg_plain) (ti_io_recv timg_plain)
                  (ti_io_now timg_plain) (ti_notice timg_plain) 0 B25 SPEC_OK
                  (proj2 (ent_fn_tail flags Bc (Cfg_desk_mac_set Bc) LBz eq_refl)) HINIT) as [EG _];
      rewrite EG, (proj1 (ent_fn_tail flags Bc (Cfg_desk_mac_set Bc) LBz eq_refl)); lia
    | exact HBf | exact KHEAD | exact KOUT ].
Qed.

(* a 4-byte store keeps only the low 32 bits, so the machine's 64-bit wrap and the model's 32-bit one give
   the same bytes *)
Lemma ent_put4_eq : forall x y, x mod 2 ^ 32 = y mod 2 ^ 32 -> put 4 x = put 4 y.
Proof.
  intros x y H. unfold put.
  rewrite <- (Z_to_le_bytes_mod 4 x 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 y 32) by (cbn; lia).
  rewrite H. reflexivity.
Qed.

Lemma ent_mod64_32 : forall x, x mod 2 ^ 64 mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ 32). reflexivity.
Qed.

(* ---- the two arithmetic identities of 0x137b8-0x137f4 ---- *)

Definition ent_allb (f : Z -> bool) (n : nat) : bool := forallb (fun i => f (Z.of_nat i)) (seq 0 n).

Lemma ent_allb_sound : forall f n, ent_allb f n = true -> forall v, 0 <= v < Z.of_nat n -> f v = true.
Proof.
  intros f n H v Hv. unfold ent_allb in H.
  rewrite forallb_forall in H.
  rewrite <- (Z2Nat.id v) by lia. apply H. apply in_seq. lia.
Qed.

(* 0x137c8 slli s0,s0,0x3c and 0x137e0 srli s0,s0,0x3f: bit 3 of the flags byte (g_raw, :1147). Over a
   byte, so settled by running both sides on every value. *)
Lemma ent_bit3 : forall flags, 0 <= flags < 256 ->
  Z.shiftr (Z.shiftl flags 60 mod 18446744073709551616) 63 = Z.land (Z.shiftr flags 3) 1.
Proof.
  intros flags H.
  assert (K : forall v, 0 <= v < Z.of_nat 256 ->
            (Z.shiftr (Z.shiftl v 60 mod 18446744073709551616) 63 =? Z.land (Z.shiftr v 3) 1) = true).
  { apply (ent_allb_sound (fun v => Z.shiftr (Z.shiftl v 60 mod 18446744073709551616) 63 =?
                                    Z.land (Z.shiftr v 3) 1) 256).
    vm_compute. reflexivity. }
  apply Z.eqb_eq. apply K. cbn [Z.of_nat]. lia.
Qed.

(* 0x137b8-0x137f4: ((v - (v * 22967 >> 25) * 1461) + 24) & 0xffff with v = hi << 8 | lo is the model's
   (SPEC_CMD_MAX + v mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2^32 (:1145). *)
Lemma ent_body_mach : forall lo8 hi8, 0 <= lo8 < 256 -> 0 <= hi8 < 256 ->
  (SPEC_CMD_MAX + (Z.lor lo8 (Z.shiftl hi8 8) mod 2 ^ 16)
     mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2 ^ 32
  = (bv_swrap 32 (Z.lor (Z.shiftl hi8 8 mod 18446744073709551616) lo8 -
                  Z.shiftr (Z.lor (Z.shiftl hi8 8 mod 18446744073709551616) lo8 * 22967
                              mod 18446744073709551616) 25 * 1461
                  mod 18446744073709551616) + 24)
    mod 18446744073709551616 mod 65536.
Proof.
  intros lo8 hi8 Hl Hh.
  assert (EL : Z.lor (Z.shiftl hi8 8 mod 18446744073709551616) lo8 = lo8 + 256 * hi8).
  { rewrite (Z.mod_small (Z.shiftl hi8 8)) by (rewrite Z.shiftl_mul_pow2 by lia; cbn; lia).
    rewrite Z.lor_comm. apply lor_shiftl8_add; lia. }
  assert (EL2 : Z.lor lo8 (Z.shiftl hi8 8) = lo8 + 256 * hi8) by (apply lor_shiftl8_add; lia).
  rewrite EL, EL2.
  set (v := lo8 + 256 * hi8) in *.
  assert (Hv : 0 <= v < 65536) by (unfold v; lia).
  rewrite (Z.mod_small v (2 ^ 16)) by (cbn; lia).
  rewrite (Z.mod_small (v * 22967) 18446744073709551616) by (cbn; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 25) with 33554432.
  rewrite ent_div1461 by exact Hv.
  assert (Hr : 0 <= v mod 1461 < 1461) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod v 1461 ltac:(lia)) as E.
  assert (Hq : 0 <= v / 1461 <= 44).
  { split; [apply Z.div_pos; lia|].
    assert (v / 1461 < 45) by (apply Z.div_lt_upper_bound; lia). lia. }
  rewrite (Z.mod_small (v / 1461 * 1461) 18446744073709551616) by (cbn; lia).
  rewrite (bv_swrap_small 32 (v - v / 1461 * 1461))
    by (change (bv_half_modulus 32) with (2 ^ 31); cbn; lia).
  rewrite (Z.mod_small (v - v / 1461 * 1461 + 24) 18446744073709551616) by (cbn; lia).
  rewrite (Z.mod_small (v - v / 1461 * 1461 + 24) 65536) by (cbn; lia).
  unfold SPEC_CMD_MAX, SPEC_MAX_BODY.
  replace (1484 - 24 + 1) with 1461 by lia.
  rewrite (Z.mod_small (24 + v mod 1461) (2 ^ 32)) by (cbn; lia).
  lia.
Qed.

(* ================================ 0x1376c-0x137b4: the join points of the config chain ============== *)

(* The out-of-line arms of 0x14360-0x144e4 write the field they just read and jump back into the straight
   chain at the NEXT field; the cursor is spent at every such jump, so from the join point on every read of
   the model is 0. ecw<k> is the world the chain leaves from join point k. *)
Definition ecw7 (B : list byte) (lo8 hi8 : Z) : list byte :=
  set_Cfg_max_body B ((SPEC_CMD_MAX + (Z.lor lo8 (Z.shiftl hi8 8) mod 2 ^ 16)
                         mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2 ^ 32).
Definition ecw6 (B : list byte) : list byte := ecw7 (set_Cfg_max_cmds B 1) 0 0.
Definition ecw5 (B : list byte) (v7 : Z) : list byte := ecw6 (set_Cfg_display_gap_us B v7).
Definition ecw4 (B : list byte) (v6 : Z) : list byte :=
  ecw5 (set_Cfg_wake_timeout_ms B ((1 + v6) mod 2 ^ 32)) 0.
Definition ecw3 (B : list byte) (v5 : Z) : list byte :=
  ecw4 (set_Cfg_offline_ms B ((1 + v5) mod 2 ^ 32)) 0.
Definition ecw2 (B : list byte) : list byte := ecw3 (set_Cfg_backoff_ms B 0) 0.
Definition ecw1 (B : list byte) (v3 : Z) : list byte :=
  ecw2 (set_Cfg_keepalive_ms B ((1 + v3) mod 2 ^ 32)).
Definition ecw0 (B : list byte) : list byte := ecw1 (set_Cfg_ack_timeout_ms B 1) 0.

(* ================================ 0x137b8-0x137f8: max_body ================================ *)

(* At 0x137b8 a0 / a1 hold the two bytes of the last config read (fuzz_u16 of :1145, low and high), s0 the
   flags byte, s2 = (flags >> 2) & 1. 0x137b8-0x137f4 compute (v mod 1461) + 24 with v = hi << 8 | lo
   (ent_div1461) and keep its low 16 bits; 0x137f8 stores it to g_cfg.max_body. s0 becomes (flags >> 3) & 1
   (0x137c8, 0x137e0) and a2 = 0xf4240 (0x137dc, 0x137e4), what 0x137fc on uses. *)
Lemma ent_cfg_j7 : forall Sp lo flags lo8 hi8 c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    j30 j50 F fc Q rz q0 q1 q2 p2 p3 p4 p5 p6 p7 x19 x21 x22 x24 x26 x27 e3 e4 e5 e6,
  memset_contract -> memcpy_contract -> diginet_session_init_contract ->
  ent_mem Sp lo Bk m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  llvm_cursor D c -> 0 <= flags < 256 -> 0 <= lo8 < 256 -> 0 <= hi8 < 256 ->
  Cfg_desk_mac_set Bk = Z.land (Z.shiftr flags 2) 1 ->
  diginet_session_init_m (ent_tail_world flags (ecw7 Bk lo8 hi8))
    0 (ti_io_send timg_plain) (ti_io_recv timg_plain) (ti_io_now timg_plain) (ti_notice timg_plain) 0
    = Some (B25, SPEC_OK) ->
  (fi_n c = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 c B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2
             (Z_to_bv 64 flags) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_cfg))
             (Z_to_bv 64 lo8) (Z_to_bv 64 hi8) p2 p3 p4 p5 p6 p7
             (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1))
             x19 (Z_to_bv 64 (data + fi_off c)) x21 x22 (Z_to_bv 64 (fi_n c)) x24
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) x26 x27 e3 e4 e5 e6)
        F (Z_to_bv 64 0x137b8) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo flags lo8 hi8 c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 F fc Q
    rz q0 q1 q2 p2 p3 p4 p5 p6 p7 x19 x21 x22 x24 x26 x27 e3 e4 e5 e6
    MSC MCPY DIC HM HC HFL HLO8 HHI8 HDMS HINIT HBf KHEAD KOUT.
  pose proof HM as HM0. unfold ent_mem in HM.
  destruct HM as (HMU & HWMO & HDOK & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HMI & HRO & HWM
                  & HJ1 & HJ2 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length Bk) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  wk_facts. wk_eq_fact W_BASE_PLAIN. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_cfg.
  unfold w_off_stack in HWOS. rewrite unsigned_lit in HWOS by lia.
  unfold llvm_saved in HRW. cbn [app] in HRW.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MUr.
  pose proof (wmono_refl rsegs m) as WMOr.
  (* 0x137b8-0x137f4: max_body's value; 0x137f8 sw a0, 0x70(s9) *)
  do 17 zstep.
  lazymatch goal with Hw : rw_cells rsegs _ W_BASE_PLAIN [CB _ (upd Bk ?k (put 4 ?E))] |- _ =>
    replace E with ((SPEC_CMD_MAX + (Z.lor lo8 (Z.shiftl hi8 8) mod 2 ^ 16)
                       mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2 ^ 32) in Hw
      by (apply ent_body_mach; lia);
    replace (upd Bk k (put 4 ((SPEC_CMD_MAX + (Z.lor lo8 (Z.shiftl hi8 8) mod 2 ^ 16)
                                 mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2 ^ 32)))
      with (set_Cfg_max_body Bk ((SPEC_CMD_MAX + (Z.lor lo8 (Z.shiftl hi8 8) mod 2 ^ 16)
                                    mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2 ^ 32)) in Hw
      by reflexivity end.
  rewrite (ent_bit3 flags HFL).
  unfold ecw7 in HINIT.
  set (Bm := set_Cfg_max_body Bk ((SPEC_CMD_MAX + (Z.lor lo8 (Z.shiftl hi8 8) mod 2 ^ 16)
                                     mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2 ^ 32)) in *.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ Bm] |- _ =>
    assert (HMm : ent_mem Sp lo Bm m0 mm ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 Bk Bm m0 m mm);
            [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
            | assumption | assumption | assumption ]) end.
  eapply llvm_ent_tail; [ exact MSC | exact MCPY | exact DIC | exact HMm | exact HC | | exact HINIT
                        | exact HBf | exact KHEAD | exact KOUT ].
  unfold Bm, set_Cfg_max_body, Cfg_desk_mac_set, A_Cfg_max_body, A_Cfg_desk_mac_set, OFF_g_cfg.
  rewrite s32_at_upd_out by (rewrite ?length_put, ?LBz; cbn [Z.of_nat]; unfold W_LEN; lia).
  exact HDMS.
Qed.

(* The six join points before it. Each writes one field and falls into the next; s7 still holds the count
   the out-of-line arm left (0x137a4 is where it becomes 0), so it is free until then. *)

Ltac ent_j_open :=
  lazymatch goal with
  | HM : ent_mem ?Sp ?lo ?Bk ?m0 ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof HM as HM0; unfold ent_mem in HM;
      destruct HM as (HMU & HWMO & HDOK & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HMI & HRO & HWM
                      & HJ1 & HJ2 & HRW);
      pose proof (wm_len _ _ _ _ HWM) as LB;
      assert (LBz : Z.of_nat (length Bk) = W_LEN)
        by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]);
      unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *;
      wk_facts; wk_eq_fact W_BASE_PLAIN; wk_eq_fact OFF_g_fail_next; wk_eq_fact OFF_g_cfg;
      unfold w_off_stack in HWOS; rewrite unsigned_lit in HWOS by lia;
      unfold llvm_saved in HRW; cbn [app] in HRW;
      pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MUr;
      pose proof (wmono_refl rsegs m) as WMOr
  end.

(* a field the chain keeps: desk_mac_set survives every later config write *)
Lemma ent_dms_set : forall (Bx : list byte) k v, Z.of_nat (length Bx) = W_LEN ->
  0 <= k -> k + 4 <= W_LEN -> (k + 4 <= A_Cfg_desk_mac_set \/ A_Cfg_desk_mac_set + 4 <= k) ->
  Cfg_desk_mac_set (upd Bx k (put 4 v)) = Cfg_desk_mac_set Bx.
Proof.
  intros Bx k v HL Hk Hn Hd. unfold Cfg_desk_mac_set.
  rewrite s32_at_upd_out; [reflexivity | exact Hk | unfold A_Cfg_desk_mac_set, OFF_g_cfg; lia
                          | rewrite length_put; cbn [Z.of_nat]; lia
                          | rewrite length_put, HL; cbn [Z.of_nat]; lia].
Qed.

Ltac ent_put4_side :=
  apply ent_put4_eq; rewrite ?ent_mod64_32; rewrite ?Z.mod_mod by lia;
  first [ reflexivity | (f_equal; lia) | lia ].

Ltac ent_world_eq :=
  first [ reflexivity
        | (f_equal; repeat first [ reflexivity | lia | ent_put4_side ]) ].

Ltac ent_j_dms L :=
  rewrite ent_dms_set;
  [ assumption | exact L | lia | lia | unfold A_Cfg_desk_mac_set; lia ].

(* one byte of the input buffer, as bytes_at reads it (Prog/T/LLVMFuzzerTestOneInput_disp.v disp_sub1) *)
Lemma ent_sub1 : forall (Dx : list byte) k, (k < length Dx)%nat ->
  firstn 1 (skipn k Dx) = [nth k Dx (b8 0)].
Proof.
  induction Dx as [|d Dx IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

(* ---- the hand-off state of the config block ----
   The same registers hold at 0x13748 (the straight chain's first test) and at 0x14360 (the head of the
   out-of-line arms): s0 the flags byte, s1 = &g_cfg, s2 = (flags >> 2) & 1, s4 / s7 the cursor BEFORE the
   max_retries byte, s9 = &g_fail_next. a0 .. a7 and s3, s5, s6, s8, s10, s11 are scratch there. *)
Definition ent_cfg_st (Sp lo flags : Z) (c : fuzz_in) (Bb : list byte) (m0 : word -> option byte)
    (gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (pc : Z) (ms : machine_state) : Prop :=
  exists (rz q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6 : word)
         (m : word -> option byte) (j30 j50 : list byte),
    ms = MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2
                 (Z_to_bv 64 flags) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_cfg))
                 p0 p1 p2 p3 p4 p5 p6 p7
                 (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1))
                 x19 (Z_to_bv 64 (data + fi_off c)) x21 x22 y7 x24
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) x26 x27 e3 e4 e5 e6)
            F (Z_to_bv 64 pc) fc None m (seg_rom rsegs) /\
    y7 = Z_to_bv 64 (fi_n c) /\
    ent_mem Sp lo Bb m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50.

(* :1132-1136, the config fields the flags byte alone sets: what 0x13714-0x13744 leaves *)
Definition ecfg_base (flags : Z) (B1 : list byte) : list byte :=
  set_Cfg_desk_mac
    (set_Cfg_desk_mac_set
       (set_Cfg_sum_mode (set_Cfg_auto_wake (set_Cfg_host_mac B1 HOST) (Z.land flags 1))
          (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO))
       (Z.land (Z.shiftr flags 2) 1))
    DESK.

Lemma ecfg_flags_base : forall flags c B, ecfg_flags flags c B = ecfg_t1 c (ecfg_base flags B).
Proof. reflexivity. Qed.

(* 0x137a4-0x137b4: s7 = 0, a0 = a1 = 0, max_cmds = 1 *)
Lemma ent_cfg_j6 : forall Sp lo flags c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    j30 j50 F fc Q rz q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6,
  memset_contract -> memcpy_contract -> diginet_session_init_contract ->
  ent_mem Sp lo Bk m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  llvm_cursor D c -> fi_n c = 0 -> 0 <= flags < 256 ->
  Cfg_desk_mac_set Bk = Z.land (Z.shiftr flags 2) 1 ->
  diginet_session_init_m (ent_tail_world flags (ecw6 Bk))
    0 (ti_io_send timg_plain) (ti_io_recv timg_plain) (ti_io_now timg_plain) (ti_notice timg_plain) 0
    = Some (B25, SPEC_OK) ->
  (fi_n c = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 c B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2
             (Z_to_bv 64 flags) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_cfg))
             p0 p1 p2 p3 p4 p5 p6 p7
             (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1))
             x19 (Z_to_bv 64 (data + fi_off c)) x21 x22 y7 x24
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) x26 x27 e3 e4 e5 e6)
        F (Z_to_bv 64 0x137a4) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo flags c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 F fc Q
    rz q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6
    MSC MCPY DIC HM HC HN HFL HDMS HINIT HBf KHEAD KOUT.
  destruct c as [coff cn]. cbn [fi_n fi_off] in *. subst cn.
  ent_j_open.
  do 5 zstep.
  unfold ecw6 in HINIT.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?W] |- _ =>
    assert (EW : W = set_Cfg_max_cmds Bk 1) by reflexivity;
    rewrite EW in Hw;
    assert (HMn : ent_mem Sp lo (set_Cfg_max_cmds Bk 1) m0 mm
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 Bk (set_Cfg_max_cmds Bk 1) m0 m mm);
            [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
            | assumption | assumption | assumption ]) end.
  eapply (ent_cfg_j7 Sp lo flags 0 0 (FuzzIn coff 0)).
  all: first [ exact MSC | exact MCPY | exact DIC | exact HMn | exact HC | exact HFL
             | exact HINIT | exact HBf | exact KHEAD | exact KOUT | lia
             | (unfold set_Cfg_max_cmds, A_Cfg_max_cmds; ent_j_dms LBz) ].
Qed.

(* 0x137a0: display_gap_us = a1 *)
Lemma ent_cfg_j5 : forall Sp lo flags v7 c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    j30 j50 F fc Q rz q0 q1 q2 p0 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6,
  memset_contract -> memcpy_contract -> diginet_session_init_contract ->
  ent_mem Sp lo Bk m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  llvm_cursor D c -> fi_n c = 0 -> 0 <= flags < 256 -> 0 <= v7 < 2 ^ 32 ->
  Cfg_desk_mac_set Bk = Z.land (Z.shiftr flags 2) 1 ->
  diginet_session_init_m (ent_tail_world flags (ecw5 Bk v7))
    0 (ti_io_send timg_plain) (ti_io_recv timg_plain) (ti_io_now timg_plain) (ti_notice timg_plain) 0
    = Some (B25, SPEC_OK) ->
  (fi_n c = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 c B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2
             (Z_to_bv 64 flags) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_cfg))
             p0 (Z_to_bv 64 v7) p2 p3 p4 p5 p6 p7
             (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1))
             x19 (Z_to_bv 64 (data + fi_off c)) x21 x22 y7 x24
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) x26 x27 e3 e4 e5 e6)
        F (Z_to_bv 64 0x137a0) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo flags v7 c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 F fc Q
    rz q0 q1 q2 p0 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6
    MSC MCPY DIC HM HC HN HFL HV7 HDMS HINIT HBf KHEAD KOUT.
  destruct c as [coff cn]. cbn [fi_n fi_off] in *. subst cn.
  ent_j_open.
  do 1 zstep.
  unfold ecw5 in HINIT.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?W] |- _ =>
    assert (EW : W = set_Cfg_display_gap_us Bk v7)
      by (unfold set_Cfg_display_gap_us, A_Cfg_display_gap_us, OFF_g_cfg; ent_world_eq);
    rewrite EW in Hw;
    assert (HMn : ent_mem Sp lo (set_Cfg_display_gap_us Bk v7) m0 mm
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 Bk (set_Cfg_display_gap_us Bk v7) m0 m mm);
            [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
            | assumption | assumption | assumption ]) end.
  eapply (ent_cfg_j6 Sp lo flags (FuzzIn coff 0)).
  all: first [ exact MSC | exact MCPY | exact DIC | exact HMn | exact HC | exact HFL
             | exact HINIT | exact HBf | exact KHEAD | exact KOUT | reflexivity | lia
             | (unfold set_Cfg_display_gap_us, A_Cfg_display_gap_us; ent_j_dms LBz) ].
Qed.

(* 0x13794-0x1379c: wake_timeout_ms = a0 + 1, a1 = 0 *)
Lemma ent_cfg_j4 : forall Sp lo flags v6 c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    j30 j50 F fc Q rz q0 q1 q2 p1 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6,
  memset_contract -> memcpy_contract -> diginet_session_init_contract ->
  ent_mem Sp lo Bk m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  llvm_cursor D c -> fi_n c = 0 -> 0 <= flags < 256 -> 0 <= v6 < 2 ^ 32 ->
  Cfg_desk_mac_set Bk = Z.land (Z.shiftr flags 2) 1 ->
  diginet_session_init_m (ent_tail_world flags (ecw4 Bk v6))
    0 (ti_io_send timg_plain) (ti_io_recv timg_plain) (ti_io_now timg_plain) (ti_notice timg_plain) 0
    = Some (B25, SPEC_OK) ->
  (fi_n c = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 c B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2
             (Z_to_bv 64 flags) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_cfg))
             (Z_to_bv 64 v6) p1 p2 p3 p4 p5 p6 p7
             (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1))
             x19 (Z_to_bv 64 (data + fi_off c)) x21 x22 y7 x24
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) x26 x27 e3 e4 e5 e6)
        F (Z_to_bv 64 0x13794) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo flags v6 c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 F fc Q
    rz q0 q1 q2 p1 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6
    MSC MCPY DIC HM HC HN HFL HV HDMS HINIT HBf KHEAD KOUT.
  destruct c as [coff cn]. cbn [fi_n fi_off] in *. subst cn.
  ent_j_open.
  do 3 zstep.
  unfold ecw4 in HINIT.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?W] |- _ =>
    assert (EW : W = set_Cfg_wake_timeout_ms Bk ((1 + v6) mod 2 ^ 32))
      by (unfold set_Cfg_wake_timeout_ms, A_Cfg_wake_timeout_ms, OFF_g_cfg; ent_world_eq);
    rewrite EW in Hw;
    assert (HMn : ent_mem Sp lo (set_Cfg_wake_timeout_ms Bk ((1 + v6) mod 2 ^ 32)) m0 mm
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 Bk (set_Cfg_wake_timeout_ms Bk ((1 + v6) mod 2 ^ 32))
                    m0 m mm);
            [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
            | assumption | assumption | assumption ]) end.
  eapply (ent_cfg_j5 Sp lo flags 0 (FuzzIn coff 0)).
  all: first [ exact MSC | exact MCPY | exact DIC | exact HMn | exact HC | exact HFL
             | exact HINIT | exact HBf | exact KHEAD | exact KOUT | reflexivity | lia
             | (unfold set_Cfg_wake_timeout_ms, A_Cfg_wake_timeout_ms; ent_j_dms LBz) ].
Qed.

(* 0x13788-0x13790: offline_ms = a1 + 1, a0 = 0 *)
Lemma ent_cfg_j3 : forall Sp lo flags v5 c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    j30 j50 F fc Q rz q0 q1 q2 p0 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6,
  memset_contract -> memcpy_contract -> diginet_session_init_contract ->
  ent_mem Sp lo Bk m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  llvm_cursor D c -> fi_n c = 0 -> 0 <= flags < 256 -> 0 <= v5 < 2 ^ 32 ->
  Cfg_desk_mac_set Bk = Z.land (Z.shiftr flags 2) 1 ->
  diginet_session_init_m (ent_tail_world flags (ecw3 Bk v5))
    0 (ti_io_send timg_plain) (ti_io_recv timg_plain) (ti_io_now timg_plain) (ti_notice timg_plain) 0
    = Some (B25, SPEC_OK) ->
  (fi_n c = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 c B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2
             (Z_to_bv 64 flags) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_cfg))
             p0 (Z_to_bv 64 v5) p2 p3 p4 p5 p6 p7
             (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1))
             x19 (Z_to_bv 64 (data + fi_off c)) x21 x22 y7 x24
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) x26 x27 e3 e4 e5 e6)
        F (Z_to_bv 64 0x13788) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo flags v5 c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 F fc Q
    rz q0 q1 q2 p0 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6
    MSC MCPY DIC HM HC HN HFL HV HDMS HINIT HBf KHEAD KOUT.
  destruct c as [coff cn]. cbn [fi_n fi_off] in *. subst cn.
  ent_j_open.
  do 3 zstep.
  unfold ecw3 in HINIT.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?W] |- _ =>
    assert (EW : W = set_Cfg_offline_ms Bk ((1 + v5) mod 2 ^ 32))
      by (unfold set_Cfg_offline_ms, A_Cfg_offline_ms, OFF_g_cfg; ent_world_eq);
    rewrite EW in Hw;
    assert (HMn : ent_mem Sp lo (set_Cfg_offline_ms Bk ((1 + v5) mod 2 ^ 32)) m0 mm
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 Bk (set_Cfg_offline_ms Bk ((1 + v5) mod 2 ^ 32)) m0 m mm);
            [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
            | assumption | assumption | assumption ]) end.
  eapply (ent_cfg_j4 Sp lo flags 0 (FuzzIn coff 0)).
  all: first [ exact MSC | exact MCPY | exact DIC | exact HMn | exact HC | exact HFL
             | exact HINIT | exact HBf | exact KHEAD | exact KOUT | reflexivity | lia
             | (unfold set_Cfg_offline_ms, A_Cfg_offline_ms; ent_j_dms LBz) ].
Qed.

(* 0x13780-0x13784: backoff_ms = 0, a1 = 0 *)
Lemma ent_cfg_j2 : forall Sp lo flags c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    j30 j50 F fc Q rz q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6,
  memset_contract -> memcpy_contract -> diginet_session_init_contract ->
  ent_mem Sp lo Bk m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  llvm_cursor D c -> fi_n c = 0 -> 0 <= flags < 256 ->
  Cfg_desk_mac_set Bk = Z.land (Z.shiftr flags 2) 1 ->
  diginet_session_init_m (ent_tail_world flags (ecw2 Bk))
    0 (ti_io_send timg_plain) (ti_io_recv timg_plain) (ti_io_now timg_plain) (ti_notice timg_plain) 0
    = Some (B25, SPEC_OK) ->
  (fi_n c = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 c B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2
             (Z_to_bv 64 flags) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_cfg))
             p0 p1 p2 p3 p4 p5 p6 p7
             (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1))
             x19 (Z_to_bv 64 (data + fi_off c)) x21 x22 y7 x24
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) x26 x27 e3 e4 e5 e6)
        F (Z_to_bv 64 0x13780) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo flags c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 F fc Q
    rz q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6
    MSC MCPY DIC HM HC HN HFL HDMS HINIT HBf KHEAD KOUT.
  destruct c as [coff cn]. cbn [fi_n fi_off] in *. subst cn.
  ent_j_open.
  do 2 zstep.
  unfold ecw2 in HINIT.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?W] |- _ =>
    assert (EW : W = set_Cfg_backoff_ms Bk 0)
      by (unfold set_Cfg_backoff_ms, A_Cfg_backoff_ms, OFF_g_cfg; ent_world_eq);
    rewrite EW in Hw;
    assert (HMn : ent_mem Sp lo (set_Cfg_backoff_ms Bk 0) m0 mm
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 Bk (set_Cfg_backoff_ms Bk 0) m0 m mm);
            [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
            | assumption | assumption | assumption ]) end.
  eapply (ent_cfg_j3 Sp lo flags 0 (FuzzIn coff 0)).
  all: first [ exact MSC | exact MCPY | exact DIC | exact HMn | exact HC | exact HFL
             | exact HINIT | exact HBf | exact KHEAD | exact KOUT | reflexivity | lia
             | (unfold set_Cfg_backoff_ms, A_Cfg_backoff_ms; ent_j_dms LBz) ].
Qed.

(* 0x13778-0x1377c: keepalive_ms = a0 + 1 *)
Lemma ent_cfg_j1 : forall Sp lo flags v3 c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    j30 j50 F fc Q rz q0 q1 q2 p1 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6,
  memset_contract -> memcpy_contract -> diginet_session_init_contract ->
  ent_mem Sp lo Bk m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  llvm_cursor D c -> fi_n c = 0 -> 0 <= flags < 256 -> 0 <= v3 < 2 ^ 32 ->
  Cfg_desk_mac_set Bk = Z.land (Z.shiftr flags 2) 1 ->
  diginet_session_init_m (ent_tail_world flags (ecw1 Bk v3))
    0 (ti_io_send timg_plain) (ti_io_recv timg_plain) (ti_io_now timg_plain) (ti_notice timg_plain) 0
    = Some (B25, SPEC_OK) ->
  (fi_n c = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 c B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2
             (Z_to_bv 64 flags) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_cfg))
             (Z_to_bv 64 v3) p1 p2 p3 p4 p5 p6 p7
             (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1))
             x19 (Z_to_bv 64 (data + fi_off c)) x21 x22 y7 x24
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) x26 x27 e3 e4 e5 e6)
        F (Z_to_bv 64 0x13778) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo flags v3 c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 F fc Q
    rz q0 q1 q2 p1 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6
    MSC MCPY DIC HM HC HN HFL HV HDMS HINIT HBf KHEAD KOUT.
  destruct c as [coff cn]. cbn [fi_n fi_off] in *. subst cn.
  ent_j_open.
  do 2 zstep.
  unfold ecw1 in HINIT.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?W] |- _ =>
    assert (EW : W = set_Cfg_keepalive_ms Bk ((1 + v3) mod 2 ^ 32))
      by (unfold set_Cfg_keepalive_ms, A_Cfg_keepalive_ms, OFF_g_cfg; ent_world_eq);
    rewrite EW in Hw;
    assert (HMn : ent_mem Sp lo (set_Cfg_keepalive_ms Bk ((1 + v3) mod 2 ^ 32)) m0 mm
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 Bk (set_Cfg_keepalive_ms Bk ((1 + v3) mod 2 ^ 32))
                    m0 m mm);
            [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
            | assumption | assumption | assumption ]) end.
  eapply (ent_cfg_j2 Sp lo flags (FuzzIn coff 0)).
  all: first [ exact MSC | exact MCPY | exact DIC | exact HMn | exact HC | exact HFL
             | exact HINIT | exact HBf | exact KHEAD | exact KOUT | reflexivity | lia
             | (unfold set_Cfg_keepalive_ms, A_Cfg_keepalive_ms; ent_j_dms LBz) ].
Qed.

(* 0x1376c-0x13774: a0 = 0, ack_timeout_ms = 1 *)
Lemma ent_cfg_j0 : forall Sp lo flags c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    j30 j50 F fc Q rz q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6,
  memset_contract -> memcpy_contract -> diginet_session_init_contract ->
  ent_mem Sp lo Bk m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  llvm_cursor D c -> fi_n c = 0 -> 0 <= flags < 256 ->
  Cfg_desk_mac_set Bk = Z.land (Z.shiftr flags 2) 1 ->
  diginet_session_init_m (ent_tail_world flags (ecw0 Bk))
    0 (ti_io_send timg_plain) (ti_io_recv timg_plain) (ti_io_now timg_plain) (ti_notice timg_plain) 0
    = Some (B25, SPEC_OK) ->
  (fi_n c = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 c B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2
             (Z_to_bv 64 flags) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_cfg))
             p0 p1 p2 p3 p4 p5 p6 p7
             (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1))
             x19 (Z_to_bv 64 (data + fi_off c)) x21 x22 y7 x24
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) x26 x27 e3 e4 e5 e6)
        F (Z_to_bv 64 0x1376c) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo flags c Bk B25 Bf m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 F fc Q
    rz q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 x19 x21 x22 y7 x24 x26 x27 e3 e4 e5 e6
    MSC MCPY DIC HM HC HN HFL HDMS HINIT HBf KHEAD KOUT.
  destruct c as [coff cn]. cbn [fi_n fi_off] in *. subst cn.
  ent_j_open.
  do 3 zstep.
  unfold ecw0 in HINIT.
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?W] |- _ =>
    assert (EW : W = set_Cfg_ack_timeout_ms Bk 1)
      by (unfold set_Cfg_ack_timeout_ms, A_Cfg_ack_timeout_ms, OFF_g_cfg; ent_world_eq);
    rewrite EW in Hw;
    assert (HMn : ent_mem Sp lo (set_Cfg_ack_timeout_ms Bk 1) m0 mm
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 Bk (set_Cfg_ack_timeout_ms Bk 1) m0 m mm);
            [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
            | assumption | assumption | assumption ]) end.
  eapply (ent_cfg_j1 Sp lo flags 0 (FuzzIn coff 0)).
  all: first [ exact MSC | exact MCPY | exact DIC | exact HMn | exact HC | exact HFL
             | exact HINIT | exact HBf | exact KHEAD | exact KOUT | reflexivity | lia
             | (unfold set_Cfg_ack_timeout_ms, A_Cfg_ack_timeout_ms; ent_j_dms LBz) ].
Qed.

(* ================================ 0x13748-0x13768: max_retries, and the fork ================== *)

(* 0x13748 `beqz s7`: no byte left, so max_retries = 0 (0x13768) and the straight chain from 0x1376c.
   Else 0x1374c reads the byte, 0x13750 masks it with 7, 0x13758 writes it, and 0x1375c `bne s7, 1`
   either falls to 0x13760 (exactly one byte: the straight chain again, the cursor one on) or leaves to
   0x14360, the out-of-line arms. *)
Lemma ent_cfg_entry : forall Sp lo flags c Bb B25 Bf m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc Q ms,
  memset_contract -> memcpy_contract -> diginet_session_init_contract ->
  ent_cfg_st Sp lo flags c Bb m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0x13748 ms ->
  llvm_cursor D c -> 0 <= flags < 256 ->
  Cfg_desk_mac_set Bb = Z.land (Z.shiftr flags 2) 1 ->
  diginet_session_init_m (ent_tail_world flags (fst (ecfg_t1 c Bb)))
    0 (ti_io_send timg_plain) (ti_io_recv timg_plain) (ti_io_now timg_plain) (ti_notice timg_plain) 0
    = Some (B25, SPEC_OK) ->
  (fi_n (snd (ecfg_t1 c Bb)) = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 (snd (ecfg_t1 c Bb)) B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  (2 <= fi_n c ->
     forall ms', ent_cfg_st Sp lo flags c (set_Cfg_max_retries Bb (snd (fuzz_u8_m D c) mod 8)) m0
                   gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0x14360 ms' ->
       evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros Sp lo flags c Bb B25 Bf m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q ms
    MSC MCPY DIC HST HC HFL HDMS HINIT HBf KHEAD KOUT KARM.
  destruct HST as (rz & q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & x19 & x21 & x22 & y7 &
                   x24 & x26 & x27 & e3 & e4 & e5 & e6 & m & j30 & j50 & -> & -> & HM).
  pose proof HC as HC0. unfold llvm_cursor, FUZZ_INPUT_MAX in HC.
  destruct HC as (HCa & HCb & HCc & HCd).
  ent_j_open.
  (* 0x13748 beqz s7 *)
  zstep. if_cases K; zify_cond K.
  - (* no byte left: max_retries = 0 *)
    assert (EN : fi_n c = 0) by lia.
    zstep.
    assert (EW : fst (ecfg_t1 c Bb) = ecw0 (set_Cfg_max_retries Bb 0) /\ snd (ecfg_t1 c Bb) = c)
      by (rewrite (ecfg_t1_z c Bb EN); split; reflexivity).
    destruct EW as (EW1 & EW2). rewrite EW1 in HINIT. rewrite EW2 in HBf, KHEAD.
    lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?W] |- _ =>
      assert (EWm : W = set_Cfg_max_retries Bb 0)
        by (unfold set_Cfg_max_retries, A_Cfg_max_retries, OFF_g_cfg; ent_world_eq);
      rewrite EWm in Hw;
      assert (HMn : ent_mem Sp lo (set_Cfg_max_retries Bb 0) m0 mm
                      ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
        by (eapply (ent_mem_after_call Sp lo 0 Bb (set_Cfg_max_retries Bb 0) m0 m mm);
              [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
              | assumption | assumption | assumption ]) end.
    eapply (ent_cfg_j0 Sp lo flags c).
    all: first [ exact MSC | exact MCPY | exact DIC | exact HMn | exact HC0 | exact EN | exact HFL
               | exact HINIT | exact HBf | exact KHEAD | exact KOUT | lia
               | (unfold set_Cfg_max_retries, A_Cfg_max_retries; ent_j_dms LBz) ].
  - (* a byte: max_retries = b & 7 *)
    assert (EN : fi_n c <> 0) by lia.
    assert (HDP : 0 < Z.of_nat (length D)) by lia.
    destruct (ent_dok_mem lo Sp m0 m HDOK HMU ltac:(lia) ltac:(unfold LLVM_LOOP_K; lia)
                ltac:(unfold LLVM_FRAME; lia) HDP) as (HDb & _ & _).
    assert (HK1 : (Z.to_nat (fi_off c) + 1 <= length D)%nat) by lia.
    pose proof (bytes_at_read rsegs m data D (fi_off c) 1 HDb ltac:(lia) HK1) as HR.
    rewrite ent_sub1 in HR by lia.
    set (b := nth (Z.to_nat (fi_off c)) D (b8 0)) in *.
    assert (Hb : 0 <= bv_unsigned b < 256).
    { pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
      change (2 ^ Z.of_N 8) with 256 in R. lia. }
    assert (EU : fuzz_u8_m D c = (FuzzIn (fi_off c + 1) (fi_n c - 1), bv_unsigned b)).
    { unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0) as [E|_]; [lia|].
      unfold at8, bz, b. reflexivity. }
    replace (data + fi_off c) with (data + fi_off c + 0) by lia.
    do 5 zstep.
    replace (data + fi_off c + 0) with (data + fi_off c) in * by lia.
    assert (HL7 : Z.land (bv_unsigned b) 7 = bv_unsigned b mod 8)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?W] |- _ =>
      assert (EWm : W = set_Cfg_max_retries Bb (bv_unsigned b mod 8))
        by (unfold set_Cfg_max_retries, A_Cfg_max_retries, OFF_g_cfg; rewrite <- HL7; ent_world_eq);
      rewrite EWm in Hw;
      assert (HMn : ent_mem Sp lo (set_Cfg_max_retries Bb (bv_unsigned b mod 8)) m0 mm
                      ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
        by (eapply (ent_mem_after_call Sp lo 0 Bb (set_Cfg_max_retries Bb (bv_unsigned b mod 8))
                      m0 m mm);
              [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
              | assumption | assumption | assumption ]) end.
    (* 0x1375c bne s7, 1 *)
    if_cases K1; zify_cond K1.
    + (* more than one byte left: the out-of-line arms at 0x14360 *)
      apply KARM; [lia|]. unfold ent_cfg_st. rewrite EU. cbn [snd].
      do 26 eexists. split; [reflexivity|]. split; [reflexivity|]. exact HMn.
    + (* exactly one byte: the straight chain, the cursor one on *)
      assert (EN1 : fi_n c = 1) by lia.
      do 2 zstep.
      replace (data + fi_off c + 1) with (data + (fi_off c + 1)) by lia.
      assert (EC1 : fuzz_u8_m D c = (FuzzIn (fi_off c + 1) 0, bv_unsigned b))
        by (rewrite EU, EN1; reflexivity).
      assert (EZ : fi_n (FuzzIn (fi_off c + 1) 0) = 0) by reflexivity.
      assert (EW : fst (ecfg_t1 c Bb) = ecw0 (set_Cfg_max_retries Bb (bv_unsigned b mod 8)) /\
                   snd (ecfg_t1 c Bb) = FuzzIn (fi_off c + 1) 0).
      { unfold ecfg_t1. rewrite EC1. rewrite (ecfg_t2_z _ _ EZ). split; reflexivity. }
      destruct EW as (EW1 & EW2). rewrite EW1 in HINIT. rewrite EW2 in HBf, KHEAD.
      eapply (ent_cfg_j0 Sp lo flags (FuzzIn (fi_off c + 1) 0)).
      all: first [ exact MSC | exact MCPY | exact DIC | exact HMn | exact HFL
                 | exact HINIT | exact HBf | exact KHEAD | exact KOUT | reflexivity | lia
                 | (unfold llvm_cursor; cbn [fi_off fi_n]; unfold FUZZ_INPUT_MAX; lia)
                 | (unfold set_Cfg_max_retries, A_Cfg_max_retries; ent_j_dms LBz) ].
Qed.

(* ================================ 0x13664-0x13744: the prologue and the flags block ================== *)

(* the 6 bytes of HOST in .rodata at 0x10480 (fuzz_transport.c:109-113; TCb.v HOST), read-only *)
Lemma ent_host_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10480 HOST.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

(* 0x13718 slli a1,s0,0x3e and 0x13720 srli a1,a1,0x3f: bit 1 of the flags byte, the sum mode (:1134) *)
Lemma ent_bit1 : forall flags, 0 <= flags < 256 ->
  Z.shiftr (Z.shiftl flags 62 mod 18446744073709551616) 63 =
  (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO).
Proof.
  intros flags H.
  assert (K : forall v, 0 <= v < Z.of_nat 256 ->
            (Z.shiftr (Z.shiftl v 62 mod 18446744073709551616) 63 =?
             (if Z.land v 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO)) = true).
  { apply (ent_allb_sound (fun v => Z.shiftr (Z.shiftl v 62 mod 18446744073709551616) 63 =?
                                    (if Z.land v 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO)) 256).
    vm_compute. reflexivity. }
  apply Z.eqb_eq. apply K. cbn [Z.of_nat]. lia.
Qed.

(* 0x1371c slli a2,s0,0x3d and 0x13724 srli s2,a2,0x3f: bit 2 of the flags byte, desk_mac_set (:1135) *)
Lemma ent_bit2 : forall flags, 0 <= flags < 256 ->
  Z.shiftr (Z.shiftl flags 61 mod 18446744073709551616) 63 = Z.land (Z.shiftr flags 2) 1.
Proof.
  intros flags H.
  assert (K : forall v, 0 <= v < Z.of_nat 256 ->
            (Z.shiftr (Z.shiftl v 61 mod 18446744073709551616) 63 =? Z.land (Z.shiftr v 2) 1) = true).
  { apply (ent_allb_sound (fun v => Z.shiftr (Z.shiftl v 61 mod 18446744073709551616) 63 =?
                                    Z.land (Z.shiftr v 2) 1) 256).
    vm_compute. reflexivity. }
  apply Z.eqb_eq. apply K. cbn [Z.of_nat]. lia.
Qed.

(* The machine's five config writes of 0x13710-0x13744 (g_cfg = OFF 65024: host_mac +0, desk_mac_set +12,
   auto_wake +16, sum_mode +20, desk_mac +6) are the model's :1132-1136 (ecfg_base). The machine writes
   desk_mac_set before auto_wake and sum_mode, the model after them; the three spans are disjoint. *)
Lemma ent_base_eq : forall flags (B1 : list byte) dms aw sm, Z.of_nat (length B1) = W_LEN ->
  dms = Z.land (Z.shiftr flags 2) 1 -> aw = Z.land flags 1 ->
  sm = (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO) ->
  upd (upd (upd (upd (upd B1 65024 HOST) 65036 (put 4 dms)) 65040 (put 4 aw)) 65044 (put 4 sm)) 65030 DESK
  = ecfg_base flags B1.
Proof.
  intros flags B1 dms aw sm HL -> -> ->.
  unfold ecfg_base, set_Cfg_desk_mac, set_Cfg_desk_mac_set, set_Cfg_sum_mode, set_Cfg_auto_wake,
    set_Cfg_host_mac, A_Cfg_desk_mac, A_Cfg_desk_mac_set, A_Cfg_sum_mode, A_Cfg_auto_wake, A_Cfg_host_mac,
    OFF_g_cfg.
  change (65024 + 0) with 65024. change (65024 + 6) with 65030. change (65024 + 12) with 65036.
  change (65024 + 16) with 65040. change (65024 + 20) with 65044.
  assert (LH : Z.of_nat (length HOST) = 6) by reflexivity.
  assert (LX : Z.of_nat (length (upd B1 65024 HOST)) = W_LEN)
    by (rewrite ent_len_upd; [exact HL | lia | rewrite LH, HL; unfold W_LEN; lia]).
  assert (LX2 : Z.of_nat (length (upd (upd B1 65024 HOST) 65040 (put 4 (Z.land flags 1)))) = W_LEN)
    by (rewrite ent_len_upd; [exact LX | lia | rewrite ent_lp4, LX; unfold W_LEN; lia]).
  rewrite (upd_upd_comm (upd B1 65024 HOST) (put 4 (Z.land (Z.shiftr flags 2) 1)) (put 4 (Z.land flags 1))
             65036 65040) by (rewrite ?ent_lp4, ?LX; unfold W_LEN; lia).
  rewrite (upd_upd_comm (upd (upd B1 65024 HOST) 65040 (put 4 (Z.land flags 1)))
             (put 4 (Z.land (Z.shiftr flags 2) 1))
             (put 4 (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO))
             65036 65044) by (rewrite ?ent_lp4, ?LX2; unfold W_LEN; lia).
  reflexivity.
Qed.

(* At 0x136ec the frame is built (ent_mem), s0 holds the flags byte and s4 / s7 the cursor after it.
   0x136ec-0x136fc s9 = 0x42558 = &g_fail_next, s1 = s9 + 0x38 = &g_cfg, diginet_session_config_default(&g_cfg);
   0x13700-0x13710 memcpy(&g_cfg.host_mac, HOST, 6) with HOST at 0x10480; 0x13714-0x13730 desk_mac_set = bit 2,
   auto_wake = bit 0, sum_mode = bit 1; 0x13734-0x13744 memcpy(&g_cfg.desk_mac, DESK, 6) with DESK at 0x10486. *)
Lemma ent_pro_flags : forall Sp lo flags c B B1 m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    j30 j50 F fc Q rz q0 q1 q2 x9 p0 p1 p2 p3 p4 p5 p6 p7 x18 x19 x21 x22 x24 x25 x26 x27 e3 e4 e5 e6,
  memcpy_contract -> diginet_session_config_default_contract ->
  ent_mem Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 ->
  0 <= flags < 256 ->
  diginet_session_config_default_m B = Some (B1, tt) ->
  (forall ms', ent_cfg_st Sp lo flags c (ecfg_base flags B1) m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc 0x13748 ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp q0 q1 q2 (Z_to_bv 64 flags) x9
             p0 p1 p2 p3 p4 p5 p6 p7
             x18 x19 (Z_to_bv 64 (data + fi_off c)) x21 x22 (Z_to_bv 64 (fi_n c)) x24 x25 x26 x27 e3 e4 e5 e6)
        F (Z_to_bv 64 0x136ec) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo flags c B B1 m0 m gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 F fc Q
    rz q0 q1 q2 x9 p0 p1 p2 p3 p4 p5 p6 p7 x18 x19 x21 x22 x24 x25 x26 x27 e3 e4 e5 e6
    MCPY CFGD HM HFL HCFG KCFG.
  ent_j_open.
  (* 0x136ec auipc a0, 0x2f; 0x136f0 addi s9, a0, -0x194 (0x42558); 0x136f4 addi s1, s9, 0x38 (0x42590);
     0x136f8 mv a0, s1; 0x136fc jal 0x161d8 diginet_session_config_default *)
  do 5 zstep.
  eapply evt_cut.
  { eapply (CFGD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo B B1).
    - reflexivity.
    - exact HWM.
    - exact HCFG.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold diginet_session_config_default_FRAME. lia.
    - unfold w_off_stack, diginet_session_config_default_FRAME. rewrite unsigned_lit by lia. lia.
    - exact HMI. }
  intros ms' Hpost.
  destruct Hpost as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & m1 &
                     -> & MU1 & WMO1 & MI1 & ST1 & WM1).
  rewrite unsigned_lit in MU1, ST1 by lia.
  assert (HM1 : ent_mem Sp lo B1 m0 m1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
    by (eapply (ent_mem_after_call Sp lo diginet_session_config_default_FRAME B B1 m0 m m1);
          [ exact HM0 | unfold diginet_session_config_default_FRAME, LLVM_LOOP_K; lia | exact MU1 | exact WMO1
          | exact MI1 | exact ST1 | exact WM1 ]).
  rewrite (ret_pc_even 0x13700) by (first [lia | reflexivity]).
  try clear HRW. try clear HSTK. try clear HMI. try clear HRO. try clear HWM. clear MUr WMOr MU1 ST1 WM1.
  pose proof HM1 as HM1c. unfold ent_mem in HM1c.
  destruct HM1c as (_ & _ & _ & _ & HSTK1 & _ & _ & _ & _ & HMI1 & HRO1 & HWM1 & _ & _ & HRW1).
  unfold llvm_saved in HRW1. cbn [app] in HRW1.
  pose proof (wm_len _ _ _ _ HWM1) as LB1n.
  assert (LB1 : Z.of_nat (length B1) = W_LEN)
    by (rewrite LB1n, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  (* 0x13700 auipc a0, 0xffffd; 0x13704 addi a1, a0, -0x280 (0x10480, HOST); 0x13708 li a2, 6;
     0x1370c mv a0, s1; 0x13710 jal 0x1f910 memcpy *)
  do 5 zstep.
  (* the destination g_cfg.host_mac: 271760 = 0x42590 = W_BASE_PLAIN + OFF_g_cfg (TWorld.v A_Cfg_host_mac) *)
  assert (CWh : rw_cells rsegs m1 271760 [CB (Z.to_nat 6) (sub B1 65024 6)])
    by (pose proof (wm_cell rsegs W_BASE_PLAIN m1 B1 65024 6 271760 HWM1 ltac:(lia) ltac:(lia) ltac:(lia))
          as P; rewrite length_sub in P by (rewrite ?LB1; unfold W_LEN; lia); exact P).
  eapply evt_cut.
  { eapply (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1
              HOST (sub B1 65024 6)).
    - rewrite !unsigned_lit by lia. apply ent_host_at. exact HMI1.
    - rewrite !unsigned_lit by lia. reflexivity.
    - rewrite !unsigned_lit by lia. exact CWh.
    - rewrite !unsigned_lit by lia. lia.
    - exact HMI1. }
  intros ms' Hpost. unfold memcpy_post in Hpost.
  destruct Hpost as (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & i3 & i4 & i5 & i6 & mc &
                     -> & MU2 & WMO2 & MI2 & CZ2 & BA2).
  rewrite !unsigned_lit in MU2, CZ2 by lia.
  replace 271760 with (W_BASE_PLAIN + 65024) in MU2, CZ2 by lia.
  assert (HM2 : ent_mem Sp lo (upd B1 65024 HOST) m0 mc ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
    by (eapply (ent_mem_after_fill Sp lo B1 m0 _ mc 65024 6);
          [ exact HM1 | exact MU2 | exact WMO2 | exact MI2 | exact CZ2 | lia | lia | unfold W_LEN; lia ]).
  rewrite (ret_pc_even 0x13714) by (first [lia | reflexivity]).
  clear HSTK1 HMI1 HRO1 HWM1 HRW1 CWh MU2 CZ2 BA2.
  pose proof HM2 as HM2c. unfold ent_mem in HM2c.
  destruct HM2c as (_ & _ & _ & _ & HSTK2 & _ & _ & _ & _ & HMI2 & HRO2 & HWM2 & _ & _ & HRW2).
  unfold llvm_saved in HRW2. cbn [app] in HRW2.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mc) as MUc.
  pose proof (wmono_refl rsegs mc) as WMOc.
  (* 0x13714-0x13724 the three bits; 0x13728 sw s2, 0x44(s9) desk_mac_set; 0x1372c sw a0, 0x48(s9) auto_wake;
     0x13730 sw a1, 0x4c(s9) sum_mode; 0x13734 addi a0, s9, 0x3e (&g_cfg.desk_mac); 0x13738 auipc a1, 0xffffd;
     0x1373c addi a1, a1, -0x2b2 (0x10486, DESK); 0x13740 li a2, 6; 0x13744 jal 0x1f910 memcpy *)
  do 13 zstep.
  rewrite (ent_bit2 flags HFL).
  (* the world W the five writes left; it is never named, so no tactic compares it against another world *)
  lazymatch goal with Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?W] |- _ =>
    assert (EWB : upd W 65030 DESK = ecfg_base flags B1)
      by (rewrite (ent_bit2 flags HFL), (ent_bit1 flags HFL);
          apply ent_base_eq; [exact LB1 | reflexivity | reflexivity | reflexivity]);
    pose proof (wm_len rsegs W_BASE_PLAIN mm W Hw) as LWbn;
    assert (LWb : Z.of_nat (length W) = W_LEN)
      by (rewrite LWbn, Z2Nat.id; [reflexivity | unfold W_LEN; lia]);
    assert (HMWb : ent_mem Sp lo W m0 mm ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (eapply (ent_mem_after_call Sp lo 0 (upd B1 65024 HOST) W m0 mc mm);
            [ exact HM2 | unfold LLVM_LOOP_K; lia | exact MUc | exact WMOc
            | assumption | assumption | exact Hw ]);
    (* the destination g_cfg.desk_mac: 271766 = 0x42596 = s9 + 0x3e = W_BASE_PLAIN + A_Cfg_desk_mac *)
    assert (CWd : rw_cells rsegs mm 271766 [CB (Z.to_nat 6) (sub W 65030 6)])
      by (pose proof (wm_cell rsegs W_BASE_PLAIN mm W 65030 6 271766 Hw ltac:(lia) ltac:(lia) ltac:(lia))
            as P; rewrite length_sub in P by (rewrite ?LWb; unfold W_LEN; lia); exact P)
  end.
  eapply evt_cut.
  { lazymatch type of CWd with rw_cells rsegs ?mm _ [CB _ ?J] =>
      eapply (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm DESK J) end.
    - rewrite !unsigned_lit by lia. apply ent_desk_at. assumption.
    - rewrite !unsigned_lit by lia. reflexivity.
    - rewrite !unsigned_lit by lia. exact CWd.
    - rewrite !unsigned_lit by lia. lia.
    - assumption. }
  intros ms' Hpost. unfold memcpy_post in Hpost.
  destruct Hpost as (k0 & k1 & k2 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & n3 & n4 & n5 & n6 & md &
                     -> & MU3 & WMO3 & MI3 & CZ3 & BA3).
  rewrite !unsigned_lit in MU3, CZ3 by lia.
  replace 271766 with (W_BASE_PLAIN + 65030) in MU3, CZ3 by lia.
  (* the five writes are the model's :1132-1136 (EWB) *)
  lazymatch type of HMWb with ent_mem Sp lo ?W m0 _ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50 =>
    assert (HM3 : ent_mem Sp lo (ecfg_base flags B1) m0 md ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
      by (rewrite <- EWB;
          eapply (ent_mem_after_fill Sp lo W m0 _ md 65030 6);
            [ exact HMWb | exact MU3 | exact WMO3 | exact MI3 | exact CZ3 | lia | lia | unfold W_LEN; lia ])
  end.
  rewrite (ret_pc_even 0x13748) by (first [lia | reflexivity]).
  apply KCFG. unfold ent_cfg_st.
  do 26 eexists. split; [reflexivity|]. split; [reflexivity|]. exact HM3.
Qed.

(* the input's first byte, as bytes_at_read gives it *)
Lemma ent_first1 : forall (l : list byte), (0 < length l)%nat ->
  firstn 1 (skipn (Z.to_nat 0) l) = [nth 0 l (b8 0)].
Proof. intros l H. destruct l as [|x l]; [cbn in H; lia | reflexivity]. Qed.

(* The ENTRY to 0x13748: the frame and the io block (0x13664-0x136c8), the size test (0x136cc; its exit to
   0x14320 is the first continuation, with the world B), the flags byte (0x136d0-0x136e8), then ent_pro_flags. *)
Lemma llvm_ent_pro : forall Sp lo B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  memcpy_contract -> diginet_session_config_default_contract ->
  llvm_pre m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  diginet_session_config_default_m B = Some (B1, tt) ->
  (FUZZ_INPUT_MAX <= Z.of_nat (length D) ->
     forall ms', llvm_out0 m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
       evt rsegs Q ms') ->
  (Z.of_nat (length D) < FUZZ_INPUT_MAX ->
     forall ms',
       ent_cfg_st Sp lo (snd (fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D)))))
         (fst (fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D)))))
         (ecfg_base (snd (fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D))))) B1)
         m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0x13748 ms' ->
       evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros Sp lo B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q MCPY CFGD HPRE HCFG KBIG KCFG.
  destruct HPRE as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & -> & HDOK & HSP & HSTK
                    & HLO & HSP2 & HOWS & HMI & HRO & HWM).
  unfold LLVM_FRAME, LLVM_LOOP_K, LLVM_ENTRY_PC in *.
  wk_facts. wk_eq_fact W_BASE_PLAIN.
  (* LLVM_FP Sp, unfolded: LLVM_LOOP_K = 9856, LLVM_FRAME = 224 (_lh.v) *)
  pose proof (munch_refl [(Sp - 9856, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m0) as MU.
  pose proof (wmono_refl rsegs m0) as WMO.
  carve_frame 224%nat HSTK.
  replace (Sp + 0) with Sp in * by lia.
  (* 0x13664 addi sp, sp, -0xe0; 0x13668-0x13698 the 13 saved registers *)
  do 14 zstep.
  (* 0x1369c mv s4, a0; 0x136a0 auipc a0, 0xe; 0x136a4 srli a2, a1, 0x1a; 0x136a8 addi a0, a0, -0x2d8:
     a0 = 0x213c8, the struct diginet_io in .data.rel.ro *)
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HROm : relro_img mm)
      by (eapply relro_munch_hi; [exact HRO | exact MU | lia]);
    (* .data.rel.ro 0x213c8: {NULL, io_send 0x144ec, io_recv 0x1492c, io_now 0x149d8} (TImgP.v timg_plain) *)
    pose proof (ent_rd8 mm 0 0 HROm ltac:(lia) ltac:(lia)
                  ltac:(apply bytes_eq_of_zs; vm_compute; reflexivity)) as RD0;
    pose proof (ent_rd8 mm 8 0x144ec HROm ltac:(lia) ltac:(lia)
                  ltac:(apply bytes_eq_of_zs; vm_compute; reflexivity)) as RD8;
    pose proof (ent_rd8 mm 16 0x1492c HROm ltac:(lia) ltac:(lia)
                  ltac:(apply bytes_eq_of_zs; vm_compute; reflexivity)) as RD16;
    pose proof (ent_rd8 mm 24 0x149d8 HROm ltac:(lia) ltac:(lia)
                  ltac:(apply bytes_eq_of_zs; vm_compute; reflexivity)) as RD24
  end.
  (* 0x136ac-0x136b8 the four loads; 0x136bc-0x136c8 the four stores to sp + 0x30 .. sp + 0x48 *)
  do 8 zstep.
  clear RD0 RD8 RD16 RD24 HROm.
  (* the invariant from here on: the frame holds the io block at sp + 0x30 *)
  lazymatch goal with
  | H : rw_cells rsegs ?mm Sp (CB 48 ?J1 :: _ :: _ :: _ :: _ :: CB 40 ?J2 :: _) |- _ =>
      assert (HME : ent_mem Sp lo B m0 mm ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 J1 J2);
      [ pose proof H as Hc; destruct Hc as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf;
        destruct Hwf as (L1 & _ & _ & _ & _ & L2 & _);
        unfold ent_mem, LLVM_FP, LLVM_LOOP_K, LLVM_FRAME, llvm_saved;
        split; [exact MU|]; split; [exact WMO|]; split; [exact HDOK|]; split; [exact HSP|];
        split; [exact HSTK|]; split; [exact HLO|]; split; [exact HSP2|];
        split; [unfold w_off_stack; rewrite unsigned_lit by lia; lia|];
        split; [exact HOWS|]; split; [exact HMI|];
        split; [eapply relro_munch_hi; [exact HRO | exact MU | lia]|];
        split; [exact HWM|]; split; [exact L1|]; split; [exact L2|];
        cbn [app]; exact H
      | ]
  end.
  assert (HLEN : 0 <= Z.of_nat (length D) < 2 ^ 63).
  { pose proof HDOK as HD'. destruct HD' as [HE|(Hd0 & Hdl & _)]; [rewrite HE; cbn; lia | lia]. }
  (* 0x136cc bnez a2, 0x14320: a2 = size >> 26, nonzero iff size >= FUZZ_INPUT_MAX = 2^26 *)
  zstep.
  if_cases K; zify_cond K;
    rewrite (Z.mod_small (Z.of_nat (length D))) in K by lia;
    rewrite Z.shiftr_div_pow2 in K by lia; change (2 ^ 26) with 67108864 in K.
  - (* size >= 2^26: out at 0x14320 with the world B; the frame constants are never written *)
    assert (HBIG : FUZZ_INPUT_MAX <= Z.of_nat (length D)).
    { unfold FUZZ_INPUT_MAX. destruct (Z_lt_le_dec (Z.of_nat (length D)) 67108864) as [Hl|Hl]; [|exact Hl].
      exfalso. apply K. apply Z.div_small. lia. }
    apply (KBIG HBIG).
    unfold ent_mem in HME.
    destruct HME as (HMU1 & HWMO1 & _ & HSP1 & HSTK1 & HLO1 & HSP21 & HWOS1 & HOWS1 & HMI1 & HRO1 & HWM1
                     & HJ1 & HJ2 & HRW1).
    unfold llvm_saved in HRW1. cbn [app] in HRW1.
    lazymatch type of HRW1 with
    | rw_cells rsegs ?mm Sp (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?post) =>
        pose proof (rw_cells_merge rsegs mm Sp [] [c1; c2; c3; c4; c5; c6] post HRW1) as M
    end.
    cbn [app] in M. cbn [cells_size csize Nat.add] in M.
    pose proof M as M2. destruct M2 as [[Mwf _] _]. cbn [cells_wf cell_wf] in Mwf. destruct Mwf as [ML _].
    unfold llvm_out0, llvm_mem0, LLVM_OUT_PC, LLVM_FP, LLVM_FRAME, LLVM_LOOP_K, llvm_saved.
    do 30 eexists. split; [reflexivity|].
    split; [exact HMU1|]. split; [exact HWMO1|]. split; [exact HSP1|].
    split; [exact HSTK1|]. split; [lia|]. split; [lia|].
    split; [exact HWOS1|]. split; [exact HOWS1|].
    split; [exact HMI1|]. split; [exact HRO1|]. split; [exact HWM1|].
    split; [exact ML | cbn [app]; exact M].
  - (* size < 2^26 *)
    assert (HSM : Z.of_nat (length D) < FUZZ_INPUT_MAX).
    { unfold FUZZ_INPUT_MAX. destruct (Z_lt_le_dec (Z.of_nat (length D)) 67108864) as [Hl|Hl]; [exact Hl|].
      exfalso. pose proof (Z.div_le_lower_bound (Z.of_nat (length D)) 67108864 1 ltac:(lia) ltac:(lia)).
      lia. }
    specialize (KCFG HSM). clear KBIG.
    (* 0x136d0 beqz a1, 0x136e4: the empty input *)
    zstep.
    if_cases K2; zify_cond K2; rewrite ?(Z.mod_small (Z.of_nat (length D))) in K2 by lia.
    + (* 0x136e4 mv s7, zero; 0x136e8 mv s0, zero: flags = 0, the cursor (0, 0) *)
      assert (HE : Z.of_nat (length D) = 0) by lia.
      assert (HU : fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D))) = (FuzzIn 0 0, 0)).
      { unfold fuzz_u8_m, fuzz_in_m. cbn [fi_n]. rewrite HE. reflexivity. }
      rewrite HU in KCFG. cbn [fst snd] in KCFG.
      do 2 zstep.
      replace (Z_to_bv 64 data) with (Z_to_bv 64 (data + fi_off (FuzzIn 0 0))) by (cbn [fi_off]; f_equal; lia).
      eapply (ent_pro_flags Sp lo 0 (FuzzIn 0 0));
        [ exact MCPY | exact CFGD | exact HME | lia | exact HCFG | exact KCFG ].
    + (* 0x136d4 lbu s0, 0(s4); 0x136d8 addi s4, s4, 1; 0x136dc addi s7, a1, -1; 0x136e0 j 0x136ec *)
      assert (HNE : 0 < Z.of_nat (length D)) by lia.
      assert (HU : fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D))) =
                   (FuzzIn (0 + 1) (Z.of_nat (length D) - 1), at8 D (Z.to_nat 0))).
      { unfold fuzz_u8_m, fuzz_in_m. cbn [fi_n fi_off].
        destruct (Z.eqb_spec (Z.of_nat (length D)) 0); [lia | reflexivity]. }
      rewrite HU in KCFG. cbn [fst snd] in KCFG.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (ent_dok_mem lo Sp m0 mm HDOK
                    ltac:(unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME; exact MU)
                    ltac:(lia) ltac:(unfold LLVM_LOOP_K; lia) ltac:(unfold LLVM_FRAME; lia) HNE)
          as (HBD & _ & _);
        pose proof (bytes_at_read rsegs mm data D 0 1 HBD ltac:(lia) ltac:(lia)) as HR
      end.
      rewrite ent_first1 in HR by lia.
      do 4 zstep.
      replace (Z_to_bv 64 (data + 1)) with (Z_to_bv 64 (data + fi_off (FuzzIn (0 + 1) (Z.of_nat (length D) - 1))))
        by (cbn [fi_off]; f_equal; lia).
      replace (Z_to_bv 64 (Z.of_nat (length D) + -1))
        with (Z_to_bv 64 (fi_n (FuzzIn (0 + 1) (Z.of_nat (length D) - 1)))) by (cbn [fi_n]; f_equal; lia).
      eapply (ent_pro_flags Sp lo (at8 D (Z.to_nat 0)) (FuzzIn (0 + 1) (Z.of_nat (length D) - 1)));
        [ exact MCPY | exact CFGD | exact HME | | exact HCFG | exact KCFG ].
      unfold at8, bz. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat 0) D (b8 0))) as R.
      unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.


(* ================================ 0x14360-0x144e4: the out-of-line arms ================================ *)

(* the byte of the input at offset k, as the model (at8, TOps.v fuzz_u8_m) and the machine (lbu k(s4)) read it *)
Local Abbreviation eca_bu k := (bv_unsigned (nth (Z.to_nat k) D (b8 0))).

Lemma eca_sub1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l (b8 0)].
Proof.
  induction l as [|d l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma eca_byte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma eca_lor0 : forall b : byte, Z.lor (bv_unsigned b) (Z.shiftl 0 8) mod 2 ^ 16 = bv_unsigned b.
Proof.
  intros b. pose proof (eca_byte b) as R. rewrite Z.shiftl_0_l, Z.lor_0_r.
  apply Z.mod_small. change (2 ^ 16) with 65536. lia.
Qed.

(* fuzz.h fuzz_u8 / fuzz_u16 on a cursor with bytes left; the cursor after them is a parameter, so a chain of
   reads keeps its offsets as literals (off + 3, not off + 1 + 1 + 1) *)
Lemma eca_u8 : forall o n o' n', n <> 0 -> o' = o + 1 -> n' = n - 1 ->
  fuzz_u8_m D (FuzzIn o n) = (FuzzIn o' n', eca_bu o).
Proof.
  intros o n o' n' H -> ->. unfold fuzz_u8_m. cbn [fi_n fi_off].
  destruct (Z.eqb_spec n 0); [contradiction | reflexivity].
Qed.

Lemma eca_u16_2 : forall o n o1 o' n', 2 <= n -> o1 = o + 1 -> o' = o + 2 -> n' = n - 2 ->
  fuzz_u16_m D (FuzzIn o n) = (FuzzIn o' n', Z.lor (eca_bu o) (Z.shiftl (eca_bu o1) 8) mod 2 ^ 16).
Proof.
  intros o n o1 o' n' H E1 E2 E3. subst o1 o' n'. unfold fuzz_u16_m.
  rewrite (eca_u8 o n (o + 1) (n - 1)) by lia. cbv beta iota.
  rewrite (eca_u8 (o + 1) (n - 1) (o + 2) (n - 2)) by lia. cbv beta iota.
  reflexivity.
Qed.

Lemma eca_u16_1 : forall o o', o' = o + 1 ->
  fuzz_u16_m D (FuzzIn o 1) = (FuzzIn o' 0, Z.lor (eca_bu o) (Z.shiftl 0 8) mod 2 ^ 16).
Proof.
  intros o o' E. subst o'. unfold fuzz_u16_m.
  rewrite (eca_u8 o 1 (o + 1) 0) by lia. cbv beta iota.
  rewrite (ent_u8_z (FuzzIn (o + 1) 0)) by reflexivity. cbv beta iota.
  reflexivity.
Qed.

(* ---- the model's config chain, one read at a time (:1137-1145, the ecfg_t<k> above) ---- *)

Lemma eca_t1_s : forall o n o' n' B, n <> 0 -> o' = o + 1 -> n' = n - 1 ->
  ecfg_t1 (FuzzIn o n) B = ecfg_t2 (FuzzIn o' n') (set_Cfg_max_retries B (eca_bu o mod 8)).
Proof.
  intros o n o' n' B H E1 E2. unfold ecfg_t1.
  rewrite (eca_u8 o n o' n' H E1 E2). reflexivity.
Qed.

Lemma eca_t2_s : forall o n o' n' B, n <> 0 -> o' = o + 1 -> n' = n - 1 ->
  ecfg_t2 (FuzzIn o n) B = ecfg_t3 (FuzzIn o' n') (set_Cfg_ack_timeout_ms B ((1 + eca_bu o) mod 2 ^ 32)).
Proof.
  intros o n o' n' B H E1 E2. unfold ecfg_t2.
  rewrite (eca_u8 o n o' n' H E1 E2). reflexivity.
Qed.

Lemma eca_t3_s2 : forall o n o1 o' n' B, 2 <= n -> o1 = o + 1 -> o' = o + 2 -> n' = n - 2 ->
  ecfg_t3 (FuzzIn o n) B = ecfg_t4 (FuzzIn o' n')
    (set_Cfg_keepalive_ms B ((1 + Z.lor (eca_bu o) (Z.shiftl (eca_bu o1) 8) mod 2 ^ 16) mod 2 ^ 32)).
Proof.
  intros o n o1 o' n' B H E1 E2 E3. unfold ecfg_t3.
  rewrite (eca_u16_2 o n o1 o' n' H E1 E2 E3). reflexivity.
Qed.

Lemma eca_t4_s : forall o n o' n' B, n <> 0 -> o' = o + 1 -> n' = n - 1 ->
  ecfg_t4 (FuzzIn o n) B = ecfg_t5 (FuzzIn o' n') (set_Cfg_backoff_ms B (eca_bu o)).
Proof.
  intros o n o' n' B H E1 E2. unfold ecfg_t4.
  rewrite (eca_u8 o n o' n' H E1 E2). reflexivity.
Qed.

Lemma eca_t5_s2 : forall o n o1 o' n' B, 2 <= n -> o1 = o + 1 -> o' = o + 2 -> n' = n - 2 ->
  ecfg_t5 (FuzzIn o n) B = ecfg_t6 (FuzzIn o' n')
    (set_Cfg_offline_ms B ((1 + Z.lor (eca_bu o) (Z.shiftl (eca_bu o1) 8) mod 2 ^ 16) mod 2 ^ 32)).
Proof.
  intros o n o1 o' n' B H E1 E2 E3. unfold ecfg_t5.
  rewrite (eca_u16_2 o n o1 o' n' H E1 E2 E3). reflexivity.
Qed.

Lemma eca_t6_s2 : forall o n o1 o' n' B, 2 <= n -> o1 = o + 1 -> o' = o + 2 -> n' = n - 2 ->
  ecfg_t6 (FuzzIn o n) B = ecfg_t7 (FuzzIn o' n')
    (set_Cfg_wake_timeout_ms B ((1 + Z.lor (eca_bu o) (Z.shiftl (eca_bu o1) 8) mod 2 ^ 16) mod 2 ^ 32)).
Proof.
  intros o n o1 o' n' B H E1 E2 E3. unfold ecfg_t6.
  rewrite (eca_u16_2 o n o1 o' n' H E1 E2 E3). reflexivity.
Qed.

Lemma eca_t7_s2 : forall o n o1 o' n' B, 2 <= n -> o1 = o + 1 -> o' = o + 2 -> n' = n - 2 ->
  ecfg_t7 (FuzzIn o n) B = ecfg_t8 (FuzzIn o' n')
    (set_Cfg_display_gap_us B (Z.lor (eca_bu o) (Z.shiftl (eca_bu o1) 8) mod 2 ^ 16)).
Proof.
  intros o n o1 o' n' B H E1 E2 E3. unfold ecfg_t7.
  rewrite (eca_u16_2 o n o1 o' n' H E1 E2 E3). reflexivity.
Qed.

Lemma eca_t8_s : forall o n o' n' B, n <> 0 -> o' = o + 1 -> n' = n - 1 ->
  ecfg_t8 (FuzzIn o n) B = ecfg_t9 (FuzzIn o' n') (set_Cfg_max_cmds B ((1 + eca_bu o mod 255) mod 2 ^ 32)).
Proof.
  intros o n o' n' B H E1 E2. unfold ecfg_t8.
  rewrite (eca_u8 o n o' n' H E1 E2). reflexivity.
Qed.

(* ---- the model at a join point: the cursor spent, the tail is ecw<k> (the join point's world), by the
   ecfg_t<k>_z above ---- *)

Lemma eca_t3_j : forall o B, ecfg_t3 (FuzzIn o 0) B = (ecw1 B 0, FuzzIn o 0).
Proof. intros o B. rewrite ecfg_t3_z by reflexivity. reflexivity. Qed.
Lemma eca_t4_j : forall o B, ecfg_t4 (FuzzIn o 0) B = (ecw2 B, FuzzIn o 0).
Proof. intros o B. rewrite ecfg_t4_z by reflexivity. reflexivity. Qed.
Lemma eca_t5_j : forall o B, ecfg_t5 (FuzzIn o 0) B = (ecw3 B 0, FuzzIn o 0).
Proof. intros o B. rewrite ecfg_t5_z by reflexivity. reflexivity. Qed.
Lemma eca_t6_j : forall o B, ecfg_t6 (FuzzIn o 0) B = (ecw4 B 0, FuzzIn o 0).
Proof. intros o B. rewrite ecfg_t6_z by reflexivity. reflexivity. Qed.
Lemma eca_t7_j : forall o B, ecfg_t7 (FuzzIn o 0) B = (ecw5 B 0, FuzzIn o 0).
Proof. intros o B. rewrite ecfg_t7_z by reflexivity. reflexivity. Qed.
Lemma eca_t8_j : forall o B, ecfg_t8 (FuzzIn o 0) B = (ecw6 B, FuzzIn o 0).
Proof. intros o B. rewrite ecfg_t8_z by reflexivity. reflexivity. Qed.
Lemma eca_t9_j : forall o B, ecfg_t9 (FuzzIn o 0) B = (ecw7 B 0 0, FuzzIn o 0).
Proof. intros o B. rewrite ecfg_t9_z by reflexivity. reflexivity. Qed.

(* one byte left at a fuzz_u16 read: its high byte is 0 *)
Lemma eca_t3_1 : forall o o' B, o' = o + 1 -> ecfg_t3 (FuzzIn o 1) B = (ecw1 B (eca_bu o), FuzzIn o' 0).
Proof.
  intros o o' B E. unfold ecfg_t3.
  rewrite (eca_u16_1 o o' E). cbv beta iota. rewrite eca_lor0, eca_t4_j. reflexivity.
Qed.
Lemma eca_t5_1 : forall o o' B, o' = o + 1 -> ecfg_t5 (FuzzIn o 1) B = (ecw3 B (eca_bu o), FuzzIn o' 0).
Proof.
  intros o o' B E. unfold ecfg_t5.
  rewrite (eca_u16_1 o o' E). cbv beta iota. rewrite eca_lor0, eca_t6_j. reflexivity.
Qed.
Lemma eca_t6_1 : forall o o' B, o' = o + 1 -> ecfg_t6 (FuzzIn o 1) B = (ecw4 B (eca_bu o), FuzzIn o' 0).
Proof.
  intros o o' B E. unfold ecfg_t6.
  rewrite (eca_u16_1 o o' E). cbv beta iota. rewrite eca_lor0, eca_t7_j. reflexivity.
Qed.
Lemma eca_t7_1 : forall o o' B, o' = o + 1 -> ecfg_t7 (FuzzIn o 1) B = (ecw5 B (eca_bu o), FuzzIn o' 0).
Proof.
  intros o o' B E. unfold ecfg_t7.
  rewrite (eca_u16_1 o o' E). cbv beta iota. rewrite eca_lor0, eca_t8_j. reflexivity.
Qed.
Lemma eca_t9_1 : forall o o' B, o' = o + 1 -> ecfg_t9 (FuzzIn o 1) B = (ecw7 B (eca_bu o) 0, FuzzIn o' 0).
Proof.
  intros o o' B E. unfold ecfg_t9.
  rewrite (eca_u16_1 o o' E). reflexivity.
Qed.
Lemma eca_t9_2 : forall o n o1 o' n' B, 2 <= n -> o1 = o + 1 -> o' = o + 2 -> n' = n - 2 ->
  ecfg_t9 (FuzzIn o n) B = (ecw7 B (eca_bu o) (eca_bu o1), FuzzIn o' n').
Proof.
  intros o n o1 o' n' B H E1 E2 E3. unfold ecfg_t9.
  rewrite (eca_u16_2 o n o1 o' n' H E1 E2 E3). reflexivity.
Qed.

(* the length of the world under the max_retries store (0x13758 sw a0, 0x58(s9): A_Cfg_max_retries = 0xfe20,
   TWorld.v; 4 bytes, so k + 4 < W_LEN) *)
Lemma eca_len_under : forall (Bx v : list byte) k, 0 <= k -> k + Z.of_nat (length v) < W_LEN ->
  Z.of_nat (length (upd Bx k v)) = W_LEN -> Z.of_nat (length Bx) = W_LEN.
Proof.
  intros Bx v k Hk Hv H. unfold upd in H.
  rewrite !length_app, length_firstn, length_skipn in H. unfold W_LEN in *. lia.
Qed.

(* ---- the arms' arithmetic: a fuzz_u16 value as the machine builds it. slli 8 (0x1439c, 0x143f0, 0x1442c,
   0x14468) wraps at 2^64 = 18446744073709551616, the width of the registers; or (0x143a0, 0x143f4, 0x14430,
   0x1446c) joins the low byte; 256 = 2^8 is the shift, 256 the bound of a byte (lbu) ---- *)
Lemma eca_shl8m : forall x, 0 <= x < 256 -> Z.shiftl x 8 mod 18446744073709551616 = 256 * x.
Proof.
  intros x H. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.

Lemma eca_shl8 : forall x, Z.shiftl x 8 = 256 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia. Qed.

Lemma eca_lor_r : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (256 * y) = x + 256 * y.
Proof. intros x y Hx Hy. rewrite <- (lor_shiftl8_add x y) by lia. rewrite eca_shl8. reflexivity. Qed.

Lemma eca_lor_l : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor (256 * y) x = x + 256 * y.
Proof. intros x y Hx Hy. rewrite Z.lor_comm. apply eca_lor_r; assumption. Qed.

(* 0x1447c-0x14490: andi 0xff, addi -0xff, seqz, addi -1, and, addi 1 is (b == 255 ? 0 : b) + 1 (255 = 0xff
   from the disassembly; 18446744073709551616 = 2^64, the registers' wrap), the model's (1 + b mod 255) mod 2^32
   (:1144, ecfg_t8). Over a byte, so settled by running both sides on every value. *)
Lemma eca_cmds_mach : forall b, 0 <= b < 256 ->
  (Z.land (Z.land b 255)
     ((Z.b2z ((Z.land b 255 + -255) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616) + 1)
    mod 2 ^ 32 = ((1 + b mod 255) mod 2 ^ 32) mod 2 ^ 32.
Proof.
  intros b H.
  assert (K : forall v, 0 <= v < Z.of_nat 256 ->
            ((Z.land (Z.land v 255)
                ((Z.b2z ((Z.land v 255 + -255) mod 18446744073709551616 <? 1) + -1)
                   mod 18446744073709551616) + 1) mod 2 ^ 32
             =? ((1 + v mod 255) mod 2 ^ 32) mod 2 ^ 32) = true).
  { apply (ent_allb_sound (fun v =>
             (Z.land (Z.land v 255)
                ((Z.b2z ((Z.land v 255 + -255) mod 18446744073709551616 <? 1) + -1)
                   mod 18446744073709551616) + 1) mod 2 ^ 32
             =? ((1 + v mod 255) mod 2 ^ 32) mod 2 ^ 32) 256).
    vm_compute. reflexivity. }
  apply Z.eqb_eq. apply K. cbn [Z.of_nat]. lia.
Qed.

(* the 4-byte value a store wrote is the model's field value *)
Ltac eca_v :=
  apply ent_put4_eq; rewrite ?ent_mod64_32; rewrite ?Z.mod_mod by lia;
  rewrite ?eca_shl8m by lia; rewrite ?eca_shl8;
  rewrite ?eca_lor_r by lia; rewrite ?eca_lor_l by lia;
  try change (2 ^ 16) with 65536; try change (2 ^ 32) with 4294967296;
  lia.

(* after a store to g_cfg (0x54(s9) .. 0x6c(s9)): the world of the rw_cells fact is the model's field write W' *)
Ltac eca_w W' :=
  lazymatch goal with Hw : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?W] |- _ =>
    let EW := fresh "EW" in
    assert (EW : W = W')
      by (unfold set_Cfg_ack_timeout_ms, set_Cfg_keepalive_ms, set_Cfg_backoff_ms, set_Cfg_offline_ms,
                 set_Cfg_wake_timeout_ms, set_Cfg_display_gap_us, set_Cfg_max_cmds,
                 A_Cfg_ack_timeout_ms, A_Cfg_keepalive_ms, A_Cfg_backoff_ms, A_Cfg_offline_ms,
                 A_Cfg_wake_timeout_ms, A_Cfg_display_gap_us, A_Cfg_max_cmds, OFF_g_cfg;
          f_equal; first [ lia | eca_v | reflexivity ]);
    rewrite EW in Hw; clear EW
  end.

(* the length of the world of the rw_cells fact *)
Ltac eca_len L :=
  lazymatch goal with Hw : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?W] |- _ =>
    let Ln := fresh "Ln" in
    pose proof (wm_len _ _ _ _ Hw) as Ln;
    assert (L : Z.of_nat (length W) = W_LEN) by (rewrite Ln, Z2Nat.id; [reflexivity | unfold W_LEN; lia]);
    clear Ln
  end.

(* desk_mac_set survives the field write of the rw_cells fact's world *)
Ltac eca_dms DWp LWp DWn :=
  lazymatch goal with Hw : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?W] |- _ =>
    lazymatch type of DWp with Cfg_desk_mac_set _ = ?r =>
      assert (DWn : Cfg_desk_mac_set W = r)
        by (unfold set_Cfg_ack_timeout_ms, set_Cfg_keepalive_ms, set_Cfg_backoff_ms, set_Cfg_offline_ms,
                   set_Cfg_wake_timeout_ms, set_Cfg_display_gap_us, set_Cfg_max_cmds,
                   A_Cfg_ack_timeout_ms, A_Cfg_keepalive_ms, A_Cfg_backoff_ms, A_Cfg_offline_ms,
                   A_Cfg_wake_timeout_ms, A_Cfg_display_gap_us, A_Cfg_max_cmds;
            rewrite ent_dms_set; [exact DWp | exact LWp | lia | lia | unfold A_Cfg_desk_mac_set; lia])
    end
  end.

(* ent_mem at a join point: the entry state's ent_mem (HM0) carried across the arm's stores *)
Ltac eca_mem :=
  lazymatch goal with
  | HM0 : ent_mem ?Sp ?lo ?Bk ?m0 ?m ?ra ?s0 ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?j30 ?j50,
    MUr : munch _ ?m ?mm, WMOr : wmono rsegs ?m ?mm,
    Hw : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ ?W] |- _ =>
      assert (HMn : ent_mem Sp lo W m0 mm ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j30 j50)
        by (eapply (ent_mem_after_call Sp lo 0 Bk W m0 m mm);
              [ exact HM0 | unfold LLVM_LOOP_K; lia | exact MUr | exact WMOr
              | assumption | assumption | assumption ])
  end.

(* the premises of a join point; the ones with evars (the ent_mem fact, the init equation, Bf) by name *)
Ltac eca_close DW HMn HINIT HBf :=
  first [ exact DW | exact HMn | exact HINIT | exact HBf | reflexivity | lia
        | (unfold llvm_cursor, FUZZ_INPUT_MAX; cbn [fi_off fi_n]; lia) | assumption ].

(* At 0x14360 (the head of the out-of-line arms, reached from 0x1375c when 2 <= in.n): max_retries is written
   (0x13758) and s4 / s7 are still the cursor c BEFORE its byte. Each arm reads the bytes 1(s4), 2(s4), ...,
   writes the field it read, and jumps back into the straight chain at the join point of the next field once
   the input is spent, with s4 advanced by the count it read. The thirteen paths by the count n = in.n:
     n = 2   0x14374 -> 0x13778 (ent_cfg_j1, keepalive_ms read as 0)
     n = 3   0x1438c -> 0x13778 (ent_cfg_j1, keepalive_ms read as the one byte left)
     n = 4   0x143cc -> 0x13780 (ent_cfg_j2)
     n = 5   0x143c0 -> 0x13788 (ent_cfg_j3, offline_ms read as 0)
     n = 6   0x143e0 -> 0x13788 (ent_cfg_j3, one byte)
     n = 7   0x14418 -> 0x13794 (ent_cfg_j4, wake_timeout_ms read as 0)
     n = 8   0x14410 -> 0x13794 (ent_cfg_j4, one byte)
     n = 9   0x14454 -> 0x137a0 (ent_cfg_j5, display_gap_us read as 0)
     n = 10  0x1444c -> 0x137a0 (ent_cfg_j5, one byte)
     n = 11  0x144b4 -> 0x137a4 (ent_cfg_j6)
     n = 12  0x144a0 -> 0x137b8 (ent_cfg_j7, max_body read as 0)
     n = 13  0x144c8 -> 0x137b8 (ent_cfg_j7, one byte)
     n >= 14 0x144d8 -> 0x137b8 (ent_cfg_j7, two bytes; s7 = n - 14, the cursor not spent)
   They share their prefixes: one path down the arms, each test closing the path that leaves there. *)
Lemma ent_cfg_arms : forall Sp lo flags c Bb B25 Bf m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc Q ms,
  memset_contract -> memcpy_contract -> diginet_session_init_contract ->
  ent_cfg_st Sp lo flags c (set_Cfg_max_retries Bb (snd (fuzz_u8_m D c) mod 8)) m0
    gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0x14360 ms ->
  llvm_cursor D c -> 2 <= fi_n c -> 0 <= flags < 256 ->
  Cfg_desk_mac_set Bb = Z.land (Z.shiftr flags 2) 1 ->
  diginet_session_init_m (ent_tail_world flags (fst (ecfg_t1 c Bb)))
    0 (ti_io_send timg_plain) (ti_io_recv timg_plain) (ti_io_now timg_plain) (ti_notice timg_plain) 0
    = Some (B25, SPEC_OK) ->
  (fi_n (snd (ecfg_t1 c Bb)) = 0 -> Bf = B25) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 (snd (ecfg_t1 c Bb)) B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros Sp lo flags c Bb B25 Bf m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q ms
    MSC MCPY DIC HST HC HN2 HFL HDMS HINIT HBf KHEAD KOUT.
  destruct HST as (rz & q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & x19 & x21 & x22 & y7 & x24
                   & x26 & x27 & e3 & e4 & e5 & e6 & m & j30 & j50 & -> & -> & HM).
  destruct c as [off n]. cbn [fi_n fi_off] in *.
  pose proof HC as HCc. unfold llvm_cursor, FUZZ_INPUT_MAX in HCc. cbn [fi_off fi_n] in HCc.
  destruct HCc as (HO0 & HN0 & HOL & HDL).
  rewrite (eca_u8 off n (off + 1) (n - 1)) in HM by lia. cbn [snd] in HM.
  (* the model up to the ack_timeout_ms read, which every arm makes *)
  assert (EM : ecfg_t1 (FuzzIn off n) Bb =
               ecfg_t3 (FuzzIn (off + 2) (n - 2))
                 (set_Cfg_ack_timeout_ms (set_Cfg_max_retries Bb (eca_bu off mod 8))
                    ((1 + eca_bu (off + 1)) mod 2 ^ 32))).
  { rewrite (eca_t1_s off n (off + 1) (n - 1)) by lia.
    rewrite (eca_t2_s (off + 1) (n - 1) (off + 2) (n - 2)) by lia. reflexivity. }
  (* ent_mem opened as the join points open it, and the input's bytes in the current memory *)
  pose proof HM as HM0. unfold ent_mem in HM.
  destruct HM as (HMU & HWMO & HDOK & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HMI & HRO & HWM
                  & HJ1 & HJ2 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LW0 : Z.of_nat (length (set_Cfg_max_retries Bb (eca_bu off mod 8))) = W_LEN)
    by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  destruct (ent_dok_mem lo Sp m0 m HDOK HMU HOWS HLO HSP2 ltac:(lia)) as (HDb & HDw & _).
  unfold off_world in HDw.
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  wk_facts. wk_eq_fact W_BASE_PLAIN. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_cfg.
  unfold w_off_stack in HWOS. rewrite unsigned_lit in HWOS by lia.
  unfold llvm_saved in HRW. cbn [app] in HRW.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MUr.
  pose proof (wmono_refl rsegs m) as WMOr.
  (* desk_mac_set under the max_retries store (0x13758, sw at 0x58(s9) = A_Cfg_max_retries) *)
  assert (LBb : Z.of_nat (length Bb) = W_LEN).
  { unfold set_Cfg_max_retries, A_Cfg_max_retries in LW0.
    apply (eca_len_under Bb (put 4 (eca_bu off mod 8)) (OFF_g_cfg + 32)); [lia | | exact LW0].
    rewrite length_put. cbn [Z.of_nat]. unfold W_LEN. lia. }
  assert (DW0 : Cfg_desk_mac_set (set_Cfg_max_retries Bb (eca_bu off mod 8)) = Z.land (Z.shiftr flags 2) 1).
  { unfold set_Cfg_max_retries, A_Cfg_max_retries. ent_j_dms LBb. }
  set (W0 := set_Cfg_max_retries Bb (eca_bu off mod 8)) in *.
  (* ---- 0x14360-0x14370: ack_timeout_ms = byte 1 + 1 (sw at 0x54(s9)); bne s7, 2 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 1) 1 HDb ltac:(lia) ltac:(lia)) as HR1.
  rewrite eca_sub1 in HR1 by lia. replace (data + (off + 1)) with (data + off + 1) in HR1 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 1)) D (b8 0))) as HB1.
  do 5 zstep.
  eca_w (set_Cfg_ack_timeout_ms W0 ((1 + eca_bu (off + 1)) mod 2 ^ 32)).
  eca_dms DW0 LW0 DW1. eca_len LW1.
  set (W1 := set_Cfg_ack_timeout_ms W0 ((1 + eca_bu (off + 1)) mod 2 ^ 32)) in *.
  if_cases K; zify_cond K.
  2: { (* n = 2: 0x14374 a0 = 0, 0x14378 s4 += 2, 0x1437c j 0x13778 *)
       do 3 zstep. eca_mem.
       assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw1 W1 0, FuzzIn (off + 2) 0))
         by (rewrite EM; replace (n - 2) with 0 by lia; apply eca_t3_j).
       rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
       replace (data + off + 2) with (data + (off + 2)) by lia.
       eapply (ent_cfg_j1 Sp lo flags 0 (FuzzIn (off + 2) 0)).
       all: eca_close DW1 HMn HINIT HBf. }
  assert (HN3 : 3 <= n) by lia. clear K.
  (* ---- 0x14380 lbu a0, 2(s4); 0x14384 a1 = 3; 0x14388 bne s7, 3 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 2) 1 HDb ltac:(lia) ltac:(lia)) as HR2.
  rewrite eca_sub1 in HR2 by lia. replace (data + (off + 2)) with (data + off + 2) in HR2 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 2)) D (b8 0))) as HB2.
  do 3 zstep.
  if_cases K; zify_cond K.
  2: { (* n = 3: 0x1438c s4 += 3, 0x14390 j 0x13778 *)
       do 2 zstep. eca_mem.
       assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw1 W1 (eca_bu (off + 2)), FuzzIn (off + 3) 0))
         by (rewrite EM; replace (n - 2) with 1 by lia; apply eca_t3_1; lia).
       rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
       replace (data + off + 3) with (data + (off + 3)) by lia.
       eapply (ent_cfg_j1 Sp lo flags (eca_bu (off + 2)) (FuzzIn (off + 3) 0)).
       all: eca_close DW1 HMn HINIT HBf. }
  assert (HN4 : 4 <= n) by lia. clear K.
  (* ---- 0x14394 lbu a1, 3(s4); a2 = s7 - 4; a0 = (a0 | a1 << 8) + 1; 0x143a8 keepalive_ms (0x50(s9));
     0x143ac beqz a2 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 3) 1 HDb ltac:(lia) ltac:(lia)) as HR3.
  rewrite eca_sub1 in HR3 by lia. replace (data + (off + 3)) with (data + off + 3) in HR3 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 3)) D (b8 0))) as HB3.
  do 7 zstep.
  eca_w (set_Cfg_keepalive_ms W1
               ((1 + Z.lor (eca_bu (off + 2)) (Z.shiftl (eca_bu (off + 3)) 8) mod 2 ^ 16) mod 2 ^ 32)).
  eca_dms DW1 LW1 DW2. eca_len LW2.
  rewrite (eca_t3_s2 (off + 2) (n - 2) (off + 3) (off + 4) (n - 4) W1) in EM by lia.
  set (W2 := set_Cfg_keepalive_ms W1
               ((1 + Z.lor (eca_bu (off + 2)) (Z.shiftl (eca_bu (off + 3)) 8) mod 2 ^ 16) mod 2 ^ 32)) in *.
  if_cases K; zify_cond K.
  { (* n = 4: 0x143cc s4 += 4, 0x143d0 j 0x13780 *)
    do 2 zstep. eca_mem.
    assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw2 W2, FuzzIn (off + 4) 0))
      by (rewrite EM; replace (n - 4) with 0 by lia; apply eca_t4_j).
    rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
    replace (data + off + 4) with (data + (off + 4)) by lia.
    eapply (ent_cfg_j2 Sp lo flags (FuzzIn (off + 4) 0)).
    all: eca_close DW2 HMn HINIT HBf. }
  assert (HN5 : 5 <= n) by lia. clear K.
  (* ---- 0x143b0 lbu a0, 4(s4); a1 = 1; 0x143b8 backoff_ms (0x5c(s9)); 0x143bc bne a2, 1 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 4) 1 HDb ltac:(lia) ltac:(lia)) as HR4.
  rewrite eca_sub1 in HR4 by lia. replace (data + (off + 4)) with (data + off + 4) in HR4 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 4)) D (b8 0))) as HB4.
  do 4 zstep.
  eca_w (set_Cfg_backoff_ms W2 (eca_bu (off + 4))).
  eca_dms DW2 LW2 DW3. eca_len LW3.
  rewrite (eca_t4_s (off + 4) (n - 4) (off + 5) (n - 5) W2) in EM by lia.
  set (W3 := set_Cfg_backoff_ms W2 (eca_bu (off + 4))) in *.
  if_cases K; zify_cond K.
  2: { (* n = 5: 0x143c0 a1 = 0, 0x143c4 s4 += 5, 0x143c8 j 0x13788 *)
       do 3 zstep. eca_mem.
       assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw3 W3 0, FuzzIn (off + 5) 0))
         by (rewrite EM; replace (n - 5) with 0 by lia; apply eca_t5_j).
       rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
       replace (data + off + 5) with (data + (off + 5)) by lia.
       eapply (ent_cfg_j3 Sp lo flags 0 (FuzzIn (off + 5) 0)).
       all: eca_close DW3 HMn HINIT HBf. }
  assert (HN6 : 6 <= n) by lia. clear K.
  (* ---- 0x143d4 lbu a1, 5(s4); a0 = 2; 0x143dc bne a2, 2 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 5) 1 HDb ltac:(lia) ltac:(lia)) as HR5.
  rewrite eca_sub1 in HR5 by lia. replace (data + (off + 5)) with (data + off + 5) in HR5 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 5)) D (b8 0))) as HB5.
  do 3 zstep.
  if_cases K; zify_cond K.
  2: { (* n = 6: 0x143e0 s4 += 6, 0x143e4 j 0x13788 *)
       do 2 zstep. eca_mem.
       assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw3 W3 (eca_bu (off + 5)), FuzzIn (off + 6) 0))
         by (rewrite EM; replace (n - 5) with 1 by lia; apply eca_t5_1; lia).
       rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
       replace (data + off + 6) with (data + (off + 6)) by lia.
       eapply (ent_cfg_j3 Sp lo flags (eca_bu (off + 5)) (FuzzIn (off + 6) 0)).
       all: eca_close DW3 HMn HINIT HBf. }
  assert (HN7 : 7 <= n) by lia. clear K.
  (* ---- 0x143e8 lbu a0, 6(s4); a2 = s7 - 7; a0 = (a1 | a0 << 8) + 1; 0x143fc offline_ms (0x60(s9));
     0x14400 beqz a2 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 6) 1 HDb ltac:(lia) ltac:(lia)) as HR6.
  rewrite eca_sub1 in HR6 by lia. replace (data + (off + 6)) with (data + off + 6) in HR6 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 6)) D (b8 0))) as HB6.
  do 7 zstep.
  eca_w (set_Cfg_offline_ms W3
               ((1 + Z.lor (eca_bu (off + 5)) (Z.shiftl (eca_bu (off + 6)) 8) mod 2 ^ 16) mod 2 ^ 32)).
  eca_dms DW3 LW3 DW4. eca_len LW4.
  rewrite (eca_t5_s2 (off + 5) (n - 5) (off + 6) (off + 7) (n - 7) W3) in EM by lia.
  set (W4 := set_Cfg_offline_ms W3
               ((1 + Z.lor (eca_bu (off + 5)) (Z.shiftl (eca_bu (off + 6)) 8) mod 2 ^ 16) mod 2 ^ 32)) in *.
  if_cases K; zify_cond K.
  { (* n = 7: 0x14418 a0 = 0, 0x1441c s4 += 7, 0x14420 j 0x13794 *)
    do 3 zstep. eca_mem.
    assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw4 W4 0, FuzzIn (off + 7) 0))
      by (rewrite EM; replace (n - 7) with 0 by lia; apply eca_t6_j).
    rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
    replace (data + off + 7) with (data + (off + 7)) by lia.
    eapply (ent_cfg_j4 Sp lo flags 0 (FuzzIn (off + 7) 0)).
    all: eca_close DW4 HMn HINIT HBf. }
  assert (HN8 : 8 <= n) by lia. clear K.
  (* ---- 0x14404 lbu a0, 7(s4); a1 = 1; 0x1440c bne a2, 1 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 7) 1 HDb ltac:(lia) ltac:(lia)) as HR7.
  rewrite eca_sub1 in HR7 by lia. replace (data + (off + 7)) with (data + off + 7) in HR7 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 7)) D (b8 0))) as HB7.
  do 3 zstep.
  if_cases K; zify_cond K.
  2: { (* n = 8: 0x14410 s4 += 8, 0x14414 j 0x13794 *)
       do 2 zstep. eca_mem.
       assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw4 W4 (eca_bu (off + 7)), FuzzIn (off + 8) 0))
         by (rewrite EM; replace (n - 7) with 1 by lia; apply eca_t6_1; lia).
       rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
       replace (data + off + 8) with (data + (off + 8)) by lia.
       eapply (ent_cfg_j4 Sp lo flags (eca_bu (off + 7)) (FuzzIn (off + 8) 0)).
       all: eca_close DW4 HMn HINIT HBf. }
  assert (HN9 : 9 <= n) by lia. clear K.
  (* ---- 0x14424 lbu a1, 8(s4); a2 = s7 - 9; a0 = (a0 | a1 << 8) + 1; 0x14438 wake_timeout_ms (0x64(s9));
     0x1443c beqz a2 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 8) 1 HDb ltac:(lia) ltac:(lia)) as HR8.
  rewrite eca_sub1 in HR8 by lia. replace (data + (off + 8)) with (data + off + 8) in HR8 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 8)) D (b8 0))) as HB8.
  do 7 zstep.
  eca_w (set_Cfg_wake_timeout_ms W4
               ((1 + Z.lor (eca_bu (off + 7)) (Z.shiftl (eca_bu (off + 8)) 8) mod 2 ^ 16) mod 2 ^ 32)).
  eca_dms DW4 LW4 DW5. eca_len LW5.
  rewrite (eca_t6_s2 (off + 7) (n - 7) (off + 8) (off + 9) (n - 9) W4) in EM by lia.
  set (W5 := set_Cfg_wake_timeout_ms W4
               ((1 + Z.lor (eca_bu (off + 7)) (Z.shiftl (eca_bu (off + 8)) 8) mod 2 ^ 16) mod 2 ^ 32)) in *.
  if_cases K; zify_cond K.
  { (* n = 9: 0x14454 a1 = 0, 0x14458 s4 += 9, 0x1445c j 0x137a0 *)
    do 3 zstep. eca_mem.
    assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw5 W5 0, FuzzIn (off + 9) 0))
      by (rewrite EM; replace (n - 9) with 0 by lia; apply eca_t7_j).
    rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
    replace (data + off + 9) with (data + (off + 9)) by lia.
    eapply (ent_cfg_j5 Sp lo flags 0 (FuzzIn (off + 9) 0)).
    all: eca_close DW5 HMn HINIT HBf. }
  assert (HN10 : 10 <= n) by lia. clear K.
  (* ---- 0x14440 lbu a1, 9(s4); a0 = 1; 0x14448 bne a2, 1 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 9) 1 HDb ltac:(lia) ltac:(lia)) as HR9.
  rewrite eca_sub1 in HR9 by lia. replace (data + (off + 9)) with (data + off + 9) in HR9 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 9)) D (b8 0))) as HB9.
  do 3 zstep.
  if_cases K; zify_cond K.
  2: { (* n = 10: 0x1444c s4 += 10, 0x14450 j 0x137a0 *)
       do 2 zstep. eca_mem.
       assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw5 W5 (eca_bu (off + 9)), FuzzIn (off + 10) 0))
         by (rewrite EM; replace (n - 9) with 1 by lia; apply eca_t7_1; lia).
       rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
       replace (data + off + 10) with (data + (off + 10)) by lia.
       eapply (ent_cfg_j5 Sp lo flags (eca_bu (off + 9)) (FuzzIn (off + 10) 0)).
       all: eca_close DW5 HMn HINIT HBf. }
  assert (HN11 : 11 <= n) by lia. clear K.
  (* ---- 0x14460 lbu a0, 10(s4); a2 = s7 - 11; a0 = a0 << 8 | a1; 0x14470 display_gap_us (0x68(s9));
     0x14474 beqz a2 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 10) 1 HDb ltac:(lia) ltac:(lia)) as HR10.
  rewrite eca_sub1 in HR10 by lia. replace (data + (off + 10)) with (data + off + 10) in HR10 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 10)) D (b8 0))) as HB10.
  do 6 zstep.
  eca_w (set_Cfg_display_gap_us W5 (Z.lor (eca_bu (off + 9)) (Z.shiftl (eca_bu (off + 10)) 8) mod 2 ^ 16)).
  eca_dms DW5 LW5 DW6. eca_len LW6.
  rewrite (eca_t7_s2 (off + 9) (n - 9) (off + 10) (off + 11) (n - 11) W5) in EM by lia.
  set (W6 := set_Cfg_display_gap_us W5 (Z.lor (eca_bu (off + 9)) (Z.shiftl (eca_bu (off + 10)) 8) mod 2 ^ 16)) in *.
  if_cases K; zify_cond K.
  { (* n = 11: 0x144b4 s4 += 11, 0x144b8 j 0x137a4 *)
    do 2 zstep. eca_mem.
    assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw6 W6, FuzzIn (off + 11) 0))
      by (rewrite EM; replace (n - 11) with 0 by lia; apply eca_t8_j).
    rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
    replace (data + off + 11) with (data + (off + 11)) by lia.
    eapply (ent_cfg_j6 Sp lo flags (FuzzIn (off + 11) 0)).
    all: eca_close DW6 HMn HINIT HBf. }
  assert (HN12 : 12 <= n) by lia. clear K.
  (* ---- 0x14478-0x14494 a0 = (byte 11 == 255 ? 0 : byte 11) + 1; 0x14498 max_cmds (0x6c(s9));
     0x1449c bne a2, 1 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 11) 1 HDb ltac:(lia) ltac:(lia)) as HR11.
  rewrite eca_sub1 in HR11 by lia. replace (data + (off + 11)) with (data + off + 11) in HR11 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 11)) D (b8 0))) as HB11.
  do 10 zstep.
  lazymatch goal with Hw : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?W] |- _ =>
    let EW := fresh "EW" in
    assert (EW : W = set_Cfg_max_cmds W6 ((1 + eca_bu (off + 11) mod 255) mod 2 ^ 32))
      by (unfold set_Cfg_max_cmds, A_Cfg_max_cmds, OFF_g_cfg;
          f_equal; first [ lia | (apply ent_put4_eq; apply eca_cmds_mach; exact HB11) ]);
    rewrite EW in Hw; clear EW
  end.
  eca_dms DW6 LW6 DW7. eca_len LW7.
  rewrite (eca_t8_s (off + 11) (n - 11) (off + 12) (n - 12) W6) in EM by lia.
  set (W7 := set_Cfg_max_cmds W6 ((1 + eca_bu (off + 11) mod 255) mod 2 ^ 32)) in *.
  if_cases K; zify_cond K.
  2: { (* n = 12: 0x144a0 s7 = 0, a0 = 0, a1 = 0, 0x144ac s4 += 12, 0x144b0 j 0x137b8 *)
       do 5 zstep. eca_mem.
       assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw7 W7 0 0, FuzzIn (off + 12) 0))
         by (rewrite EM; replace (n - 12) with 0 by lia; apply eca_t9_j).
       rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
       replace (data + off + 12) with (data + (off + 12)) by lia.
       eapply (ent_cfg_j7 Sp lo flags 0 0 (FuzzIn (off + 12) 0)).
       all: eca_close DW7 HMn HINIT HBf. }
  assert (HN13 : 13 <= n) by lia. clear K.
  (* ---- 0x144bc lbu a0, 12(s4); 0x144c0 a1 = 2; 0x144c4 bne a2, 2 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 12) 1 HDb ltac:(lia) ltac:(lia)) as HR12.
  rewrite eca_sub1 in HR12 by lia. replace (data + (off + 12)) with (data + off + 12) in HR12 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 12)) D (b8 0))) as HB12.
  do 3 zstep.
  if_cases K; zify_cond K.
  2: { (* n = 13: 0x144c8 s7 = 0, 0x144cc a1 = 0, 0x144d0 s4 += 13, 0x144d4 j 0x137b8 *)
       do 4 zstep. eca_mem.
       assert (EF : ecfg_t1 (FuzzIn off n) Bb = (ecw7 W7 (eca_bu (off + 12)) 0, FuzzIn (off + 13) 0))
         by (rewrite EM; replace (n - 12) with 1 by lia; apply eca_t9_1; lia).
       rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
       replace (data + off + 13) with (data + (off + 13)) by lia.
       eapply (ent_cfg_j7 Sp lo flags (eca_bu (off + 12)) 0 (FuzzIn (off + 13) 0)).
       all: eca_close DW7 HMn HINIT HBf. }
  assert (HN14 : 14 <= n) by lia. clear K.
  (* ---- n >= 14: 0x144d8 lbu a1, 13(s4); 0x144dc s4 += 14; 0x144e0 s7 -= 14; 0x144e4 j 0x137b8 ---- *)
  pose proof (bytes_at_read rsegs _ data D (off + 13) 1 HDb ltac:(lia) ltac:(lia)) as HR13.
  rewrite eca_sub1 in HR13 by lia. replace (data + (off + 13)) with (data + off + 13) in HR13 by lia.
  pose proof (eca_byte (nth (Z.to_nat (off + 13)) D (b8 0))) as HB13.
  do 4 zstep. eca_mem.
  assert (EF : ecfg_t1 (FuzzIn off n) Bb =
               (ecw7 W7 (eca_bu (off + 12)) (eca_bu (off + 13)), FuzzIn (off + 14) (n - 14)))
    by (rewrite EM; apply eca_t9_2; lia).
  rewrite EF in HINIT, HBf, KHEAD. cbn [fst snd] in HINIT, HBf, KHEAD.
  replace (data + off + 14) with (data + (off + 14)) by lia.
  replace (n + -14) with (n - 14) by lia.
  eapply (ent_cfg_j7 Sp lo flags (eca_bu (off + 12)) (eca_bu (off + 13)) (FuzzIn (off + 14) (n - 14))).
  all: eca_close DW7 HMn HINIT HBf.
Qed.

(* ================================ the whole entry ================================ *)

(* the config fields the flags byte sets are below desk_mac_set, and the desk MAC above it *)
Lemma ent_base_dms : forall flags B1, Z.of_nat (length B1) = W_LEN ->
  Cfg_desk_mac_set (ecfg_base flags B1) = Z.land (Z.shiftr flags 2) 1.
Proof.
  intros flags B1 HL.
  assert (HB : 0 <= Z.land (Z.shiftr flags 2) 1 < 2).
  { change (Z.land (Z.shiftr flags 2) 1) with (Z.land (Z.shiftr flags 2) (Z.ones 1)).
    rewrite Z.land_ones by lia. change (2 ^ 1) with 2. apply Z.mod_pos_bound. lia. }
  assert (LD : Z.of_nat (length DESK) = 6) by reflexivity.
  assert (EWL : W_LEN = 65616) by reflexivity.
  unfold ecfg_base, Cfg_desk_mac_set, set_Cfg_desk_mac, set_Cfg_desk_mac_set, set_Cfg_sum_mode,
         set_Cfg_auto_wake, set_Cfg_host_mac, A_Cfg_desk_mac_set, A_Cfg_desk_mac, A_Cfg_sum_mode,
         A_Cfg_auto_wake, A_Cfg_host_mac, OFF_g_cfg.
  assert (LH : Z.of_nat (length HOST) = 6) by reflexivity.
  assert (L1 : Z.of_nat (length (upd B1 (65024 + 0) HOST)) = W_LEN)
    by (rewrite ent_len_upd; [exact HL | lia | rewrite LH, HL; lia]).
  assert (L2 : Z.of_nat (length (upd (upd B1 (65024 + 0) HOST) (65024 + 16)
                                   (put 4 (Z.land flags 1)))) = W_LEN)
    by (rewrite ent_len_upd; [exact L1 | lia | rewrite length_put, L1; cbn [Z.of_nat]; lia]).
  assert (L3 : Z.of_nat (length (upd (upd (upd B1 (65024 + 0) HOST) (65024 + 16)
                                   (put 4 (Z.land flags 1))) (65024 + 20)
                                   (put 4 (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY
                                           else DIGINET_SUM_ZERO)))) = W_LEN)
    by (rewrite ent_len_upd; [exact L2 | lia | rewrite length_put, L2; cbn [Z.of_nat]; lia]).
  assert (L4 : Z.of_nat (length (upd (upd (upd (upd B1 (65024 + 0) HOST) (65024 + 16)
                                   (put 4 (Z.land flags 1))) (65024 + 20)
                                   (put 4 (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY
                                           else DIGINET_SUM_ZERO)))
                                   (65024 + 12) (put 4 (Z.land (Z.shiftr flags 2) 1)))) = W_LEN)
    by (rewrite ent_len_upd; [exact L3 | lia | rewrite length_put, L3; cbn [Z.of_nat]; lia]).
  rewrite s32_at_upd_out by (rewrite ?LD, ?length_put, ?L1, ?L2, ?L3, ?L4; cbn [Z.of_nat]; lia).
  unfold s32_at.
  rewrite u_at_upd_put by (rewrite ?length_put, ?L1, ?L2, ?L3, ?L4; cbn [Z.of_nat]; lia).
  change (8 * Z.of_nat 4) with 32. change (2 ^ 32) with 4294967296.
  rewrite Z.mod_small by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

(* the loop head is reached only for an input the size test let through (llvm_cursor's last clause) *)
Lemma llvm_head_small : forall m0 gp tp Sp lo ops c B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms,
  llvm_head data D m0 gp tp Sp lo ops c B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  Z.of_nat (length D) < FUZZ_INPUT_MAX.
Proof.
  intros m0 gp tp Sp lo ops c B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms H.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r19 & r22 &
                 t3 & t4 & t5 & t6 & m & j10 & j28 & _ & _ & _ & HC & _).
  destruct HC as (_ & _ & _ & HC). exact HC.
Qed.

(* 0x13664 to 0x138ac: the whole entry, from the caller's state to the loop head or to the epilogue. *)
Lemma llvm_entry : forall Sp lo B B24 B25 Bf c10 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
    s10 s11 F fc ms Q,
  memset_contract -> memcpy_contract -> diginet_session_config_default_contract ->
  diginet_session_init_contract ->
  llvm_pre m0 gp tp Sp lo B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  (Z.of_nat (length D) < FUZZ_INPUT_MAX ->
     ent_world B = Some (B24, c10) /\
     diginet_session_init_m B24 0 (ti_io_send timg_plain) (ti_io_recv timg_plain)
       (ti_io_now timg_plain) (ti_notice timg_plain) 0 = Some (B25, SPEC_OK)) ->
  (Z.of_nat (length D) < FUZZ_INPUT_MAX -> fi_n c10 = 0 -> Bf = B25) ->
  (FUZZ_INPUT_MAX <= Z.of_nat (length D) -> Bf = B) ->
  (forall ms', llvm_head data D m0 gp tp Sp lo 0 c10 B25
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  (forall ms', llvm_out0 m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros Sp lo B B24 B25 Bf c10 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q
    MSC MCPY CDC DIC HPRE HMODEL HBfS HBfB KHEAD KOUT.
  pose proof HPRE as HPRE0. unfold llvm_pre in HPRE0.
  destruct HPRE0 as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 &
                     _ & HDOK & HSP & HSTK & HLO & HSP2 & HOWS & HMI & HRO & HWM).
  pose proof (wm_len _ _ _ _ HWM) as LBn.
  assert (LB : Z.of_nat (length B) = W_LEN)
    by (rewrite LBn, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  assert (ECD : diginet_session_config_default_m B = Some (upd B OFF_g_cfg cd_image, tt))
    by (apply cd_model; exact LB).
  set (B1 := upd B OFF_g_cfg cd_image) in *.
  assert (LB1 : Z.of_nat (length B1) = W_LEN).
  { unfold B1. rewrite ent_len_upd; [exact LB | unfold OFF_g_cfg; lia |].
    replace (Z.of_nat (length cd_image)) with 60 by reflexivity.
    rewrite LB. unfold OFF_g_cfg, W_LEN. lia. }
  eapply (llvm_ent_pro Sp lo B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q
            MCPY CDC HPRE ECD).
  - (* the input is too long: the model returns the world it was given *)
    intros HBIG ms' HOUT. apply KOUT. rewrite (HBfB HBIG). exact HOUT.
  - (* the config block *)
    intros HSM ms' HST.
    destruct (HMODEL HSM) as (HEW & HIN).
    destruct (fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D)))) as [c1 flags] eqn:EF.
    cbn [fst snd] in HST.
    unfold ent_world in HEW. rewrite EF, ECD in HEW.
    rewrite ecfg_flags_base in HEW.
    destruct (ecfg_t1 c1 (ecfg_base flags B1)) as [Bc cfin] eqn:ET.
    injection HEW as EB24 Ec10. subst B24 c10.
    assert (HFL : 0 <= flags < 256).
    { assert (Eq : flags = snd (fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D)))))
        by (rewrite EF; reflexivity).
      rewrite Eq. unfold fuzz_u8_m, fuzz_in_m. cbn [fi_n fi_off snd].
      destruct (Z.eqb_spec (Z.of_nat (length D)) 0); [cbn; lia|].
      unfold at8, bz. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat 0) D (b8 0))) as R.
      unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. cbn [snd]. lia. }
    assert (HC1 : llvm_cursor D c1).
    { assert (Eq : c1 = fst (fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D)))))
        by (rewrite EF; reflexivity).
      rewrite Eq. unfold fuzz_u8_m, fuzz_in_m, llvm_cursor. cbn [fi_n fi_off fst].
      destruct (Z.eqb_spec (Z.of_nat (length D)) 0); cbn [fi_n fi_off fst];
        unfold FUZZ_INPUT_MAX in *; lia. }
    eapply (ent_cfg_entry Sp lo flags c1 (ecfg_base flags B1) B25 Bf m0 gp tp
              ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q ms');
      [ exact MSC | exact MCPY | exact DIC | exact HST | exact HC1 | exact HFL
      | apply ent_base_dms; exact LB1
      | rewrite ET; cbn [fst]; exact HIN
      | rewrite ET; cbn [snd]; intros HN0; exact (HBfS HSM HN0)
      | rewrite ET; cbn [snd]; exact KHEAD
      | exact KOUT
      | ].
    (* the out-of-line arms *)
    intros HN2 ms2 HST2.
    eapply (ent_cfg_arms Sp lo flags c1 (ecfg_base flags B1) B25 Bf m0 gp tp
              ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q ms2);
      [ exact MSC | exact MCPY | exact DIC | exact HST2 | exact HC1 | exact HN2 | exact HFL
      | apply ent_base_dms; exact LB1
      | rewrite ET; cbn [fst]; exact HIN
      | rewrite ET; cbn [snd]; intros HN0; exact (HBfS HSM HN0)
      | rewrite ET; cbn [snd]; exact KHEAD
      | exact KOUT ].
Qed.

End ENTRY.

(* reg_get, for the glue's statement *)
Import Prelude Sem.
Open Scope Z_scope.

(* ================================ the statement the glue takes ================================
   LLVMFuzzerTestOneInput_glue.v's Hypothesis llvm_entry, verbatim: from the caller's registers regs0 at 0x13664
   (a0 = data, a1 = |D|, sp = the caller's sp S, the frame is [S - LLVM_FRAME, S)), the walk reaches either the
   return (a0 = 0, the callee-saved registers back) or the loop head with a cursor c and world Bh from which
   the model's loop runs for every heap stream. *)
Lemma llvm_entry_stmt_holds :
forall (data : Z) (D : list byte) (regs0 F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw : list byte),
  memcpy_contract -> memset_contract -> diginet_session_config_default_contract -> diginet_session_init_contract ->
  reg_get regs0 10 = Z_to_bv 64 data -> reg_get regs0 11 = Z_to_bv 64 (Z.of_nat (length D)) ->
  bv_unsigned (reg_get regs0 2) mod 16 = 0 -> stk rsegs m lo (bv_unsigned (reg_get regs0 2)) ->
  lo + LLVM_FRAME + LLVM_LOOP_K <= bv_unsigned (reg_get regs0 2) -> bv_unsigned (reg_get regs0 2) < 2 ^ 63 ->
  W_BASE_PLAIN + W_LEN <= lo ->
  (D = [] \/ (0 < data /\ data + Z.of_nat (length D) <= lo /\ off_world data (Z.of_nat (length D)) /\ bytes_at rsegs m data D)) ->
  mem_inv rsegs m -> relro_img m -> wmem rsegs m Bw ->
  LLVMFuzzerTestOneInput_c.llvm_model_ok Bw D ->
  evt rsegs
    (fun ms =>
       (exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
          ms = MS (mkR (reg_get regs0 1) (Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - LLVM_FRAME + LLVM_FRAME))
                       (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 (reg_get regs0 8) (reg_get regs0 9) (Z_to_bv 64 0)
                       a1 a2 a3 a4 a5 a6 a7 (reg_get regs0 18) (reg_get regs0 19) (reg_get regs0 20)
                       (reg_get regs0 21) (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24)
                       (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) t3 t4 t5 t6)
                  F (ret_pc (reg_get regs0 1)) fc None m' (seg_rom rsegs) /\
          munch (LLVM_FP (bv_unsigned (reg_get regs0 2) - LLVM_FRAME)) m m' /\ wmono rsegs m m') \/
       (exists (c : fuzz_in) (Bh : list byte),
          llvm_head data D m (reg_get regs0 3) (reg_get regs0 4) (bv_unsigned (reg_get regs0 2) - LLVM_FRAME) lo 0 c Bh
            (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19)
            (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24)
            (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) F fc ms /\
          forall As, LLVMFuzzerTestOneInput_c.llvm_heap_ok As ->
            exists Bf, LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) timg_plain Bh As D c O = Some (Bf, tt)))
    (MS (Regs6ss.mkR_of regs0) F (Z_to_bv 64 LLVM_ENTRY_PC) fc None m (seg_rom rsegs)).
Proof.
  intros data D regs0 F fc m lo Bw MCPY MSC CDC DIC H10 H11 HAL HSTK HLO HSP HOWS HDOK HMI HRO HWM HMOK.
  set (Sp := bv_unsigned (reg_get regs0 2) - LLVM_FRAME).
  assert (ESp : bv_unsigned (reg_get regs0 2) = Sp + LLVM_FRAME) by (unfold Sp; lia).
  assert (HSP16 : Sp mod 16 = 0).
  { rewrite ESp in HAL. unfold LLVM_FRAME in HAL.
    replace (Sp + 224) with (Sp + 14 * 16) in HAL by lia.
    rewrite Z.mod_add in HAL by lia. exact HAL. }
  (* the caller's state is llvm_pre: the registers are regs0's, sp = Sp + LLVM_FRAME *)
  assert (HPRE : llvm_pre data D m (reg_get regs0 3) (reg_get regs0 4) Sp lo Bw
                   (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9)
                   (reg_get regs0 18) (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)
                   (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25)
                   (reg_get regs0 26) (reg_get regs0 27) F fc
                   (MS (Regs6ss.mkR_of regs0) F (Z_to_bv 64 LLVM_ENTRY_PC) fc None m (seg_rom rsegs))).
  { unfold llvm_pre.
    exists (reg_get regs0 5), (reg_get regs0 6), (reg_get regs0 7),
      (reg_get regs0 12), (reg_get regs0 13), (reg_get regs0 14), (reg_get regs0 15),
      (reg_get regs0 16), (reg_get regs0 17),
      (reg_get regs0 28), (reg_get regs0 29), (reg_get regs0 30), (reg_get regs0 31).
    rewrite <- ESp.
    split; [unfold Regs6ss.mkR_of; rewrite <- H10, <- H11, Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact HDOK|]. split; [exact HSP16|]. split; [exact HSTK|].
    split; [lia|]. split; [exact HSP|]. split; [exact HOWS|].
    split; [exact HMI|]. split; [exact HRO|]. exact HWM. }
  destruct (Z_lt_le_dec (Z.of_nat (length D)) FUZZ_INPUT_MAX) as [HSM|HBIG].
  - (* the model's path: ent_world and the init call from llvm_model_ok at one heap stream *)
    assert (HA1 : LLVMFuzzerTestOneInput_c.llvm_heap_ok (fun _ => 1)).
    { intros k _. split; [lia | cbn; lia]. }
    destruct (HMOK _ HA1) as (Bw1 & HM1).
    rewrite ent_model in HM1 by exact HSM.
    destruct (ent_world D Bw) as [[B24 c10]|] eqn:EW; [|discriminate HM1].
    destruct (diginet_session_init_m B24 0 (ti_io_send timg_plain) (ti_io_recv timg_plain)
                (ti_io_now timg_plain) (ti_notice timg_plain) 0) as [[B25 rc]|] eqn:EI;
      [|discriminate HM1].
    destruct (negb (rc =? SPEC_OK)) eqn:ERC; [discriminate HM1|].
    apply negb_false_iff, Z.eqb_eq in ERC. subst rc.
    eapply (llvm_entry data D Sp lo Bw B24 B25 B25 c10 m
              (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9)
              (reg_get regs0 18) (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)
              (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25)
              (reg_get regs0 26) (reg_get regs0 27) F fc _ _
              MSC MCPY CDC DIC HPRE).
    + intros _. split; [exact EW | exact EI].
    + intros _ _. reflexivity.
    + intros HB. lia.
    + (* the loop head; the loop runs for every heap stream, since the prefix does not read the stream *)
      intros ms' HH. apply evt_done. right. exists c10, B25. split; [exact HH|].
      intros As HAs. destruct (HMOK As HAs) as (Bw2 & HM2).
      rewrite ent_model in HM2 by exact HSM.
      rewrite EW, EI, Z.eqb_refl in HM2. cbn [negb] in HM2.
      destruct (LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) timg_plain B25 As D c10 O)
        as [[Bf u]|]; [|discriminate HM2].
      exists Bf. destruct u. reflexivity.
    + (* the return, through the epilogue *)
      intros ms' HOUT. eapply llvm_exit0; [exact HOUT|].
      intros ms'' HRET. apply evt_done. left.
      destruct HRET as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & jf &
                        -> & HM0).
      destruct HM0 as (HMU & HWMO & _).
      exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
      split; [reflexivity|]. split; [exact HMU | exact HWMO].
  - (* size >= FUZZ_INPUT_MAX: out at 0x136cc with the world untouched *)
    eapply (llvm_entry data D Sp lo Bw Bw Bw Bw (fuzz_in_m 0) m
              (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9)
              (reg_get regs0 18) (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)
              (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25)
              (reg_get regs0 26) (reg_get regs0 27) F fc _ _
              MSC MCPY CDC DIC HPRE).
    + intros HS. lia.
    + intros HS. lia.
    + intros _. reflexivity.
    + intros ms' HH. exfalso. apply llvm_head_small in HH. lia.
    + intros ms' HOUT. eapply llvm_exit0; [exact HOUT|].
      intros ms'' HRET. apply evt_done. left.
      destruct HRET as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & jf &
                        -> & HM0).
      destruct HM0 as (HMU & HWMO & _).
      exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
      split; [reflexivity|]. split; [exact HMU | exact HWMO].
Qed.
