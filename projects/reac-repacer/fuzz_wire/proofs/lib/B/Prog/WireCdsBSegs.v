(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: the first half of lib/Prog/check_value.v's Section Ev (loop_nl, loop_lb,
   seg_sign, ev_val, ev_cur, ev_sign, ev_lb_nil, ev_60, ev_5c, ev_block and their list and sign helpers) moved to
   image A (fuzz_uci.asan): footprint runs (lib/Lib/ExecF.v evtF, lib/Lib/StepF.v step) instead of evt, this image's
   addresses (UciCvIface.v CV_AT offsets +0x06c .. +0x128) and registers, and the two ASan load checks of each loop
   in the form of proofs/libreac/fuzz_decode/lib/A/Prog/crtA_loop.v at origin/ossv/recipes 88154566652a (cl1_F;
   crt_sh1F, takeF and crt_lits copied as cv_sh1F, takeF and cv_lits, module paths changed to reac_repacer.fuzz_uci). *)
(* Modified by Theorem Labs, 2026-10: the straight-line segments of reac-repacer/fuzz_uci's check_value in image A, in the form
   and with the helpers of proofs/libreac/fuzz_decode/lib/A/Prog/crtA_segs.v (origin/ossv/recipes 88154566652a:
   crt_seg1_F .. crt_seg9_F, Z_to_le_bytes_to_Z, crt_le8_of_bytes, crt_c8s, crt_rw_c8s, crt_frame_words, crt_regs,
   crt_usub, crt_shift, crt_w, crt_finF, crt_memF, crt_pc) and of its lib/A/Prog/ReacDecodeLib.v rd_all. *)
(* Modified by Theorem Labs, 2026-10: the helpers and tactics of reac-repacer/fuzz_uci's lib/A/Prog/UciCvSegs.v
   (cv_le_bytes_to_Z, cv_le8_of_bytes, cv_c8s, cv_c8s_spec, cv_rw_c8s, cv_frame_words, cv_rd_all, cv_regs, cv_usub,
   cv_shift, cv_w, cv_finF, cv_memF, cv_lits, whose own notice names their source crtA_segs.v of
   proofs/libreac/fuzz_decode/lib/A/Prog) and of its lib/A/Prog/UciCvEvA.v (u8lit, zxb_lit, align8_cover, cv_sh1F,
   sh_at, and the steps of the ASan load check cv_ck1_F), renamed cc_* and moved to fuzz_wire's check_copy (image A,
   module paths reac_repacer.fuzz_wire). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/check_copy_cgW_segs.v, with its module paths and numbers changed; 288 of its 360 lines of code are new or changed and 451 lines of the source are left out. *)
(* The footprint (ExecF.evtF) runs of the three straight-line segments of reac-repacer/fuzz_wire's check_downstream in image B, in the form of reac-repacer/fuzz_uci's lib/B/Prog/UciCvBSegs.v (recipes commit 0295462466b2; its frame-word helpers copied), the shadow checks stepped as in this unit's footprint walks of image B (one check lemma per shadow test, StepF's step, one rng fact per access) and the frame's want closed as the released lib/Prog/check_downstream.v closes it (the model lib/Prog/rp_ds_accept_c.v ds_accept_result evaluated on the branch facts of each path). *)
(* WireCdsBSegs: the runs of check_downstream of fuzz_wire.asan-ubsan (0x7ffe8 = wire_sigma WS_check_downstream,
   lib/B/Prog/WirePAddr.v; 97 words, 0x7ffe8 .. 0x8016c), stepped by lib/Lib/StepF.v:
     cds_frame_F  +0x0 .. +0xc: `addi sp, sp, -0x10`, `sd ra, 8(sp)`, `sd s0, 0(sp)`: the frame [sp - 16, sp) written;
     cds_pick_F   +0xc -> rp_ds_accept (`jal` at +0x10c, return address +0x110 = 0x800f8): `li a2, 18`; `bltu a1, a2`
                  (+0x10) to +0x108 `mv s0, zero` when n < 18; else the UBSan checks of f (`unimp` at +0x124 = 0x8010c:
                  +0x18 `bgeu a0, a2` and +0x104 `bgeu a0, a2` with a2 = -12, +0x7c `bgeu a0, a4` with a4 = -12,
                  +0x4c / +0x8c `bltu a2, a0` with a2 = -14, +0xb0 `bgeu a0, a2` with a2 = -16, +0xd8 `bltu a2, a0`
                  with a2 = -18), all fall through; the shadow base through its GOT word (+0x1c `auipc a2, 0x19`,
                  +0x20 `ld a2, -0x78c(a2)`: 0x98878, +0x24 `ld a3, 0(a2)`: the cell 0xa07f8); the shadow bytes of
                  f + 12, f + 13, f + 16, f + 17 (`lb` at +0x34, +0x5c, +0x9c, +0xc0, +0xe8; `bnez` at +0x38, +0x60,
                  +0xa0, +0xc4, +0xec, each slow check `andi` / `blt` back to the load, so the __asan_report_load1
                  calls at +0x140, +0x150, +0x160, +0x170, +0x180 are not reached) and the frame bytes f[12] (+0x3c),
                  f[13] (+0x64, +0xa4), f[16] (+0xc8), f[17] (+0xf0); s0 := ds_accept_result n bs on each of the
                  seven paths (+0x70 `li s0, 1`, +0xf8 `seqz s0, a2`, +0x108 `mv s0, zero`);
     cds_tail_F   +0x110 -> the return: `bne a0, s0` (+0x110) not taken (a0 = s0), `ld ra, 8(sp)`, `ld s0, 0(sp)`,
                  `addi sp, sp, 0x10`, `ret` (+0x120). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof WirePSyms WirePAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ds_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ds_accept_c.

(* ---- the cut points (offsets from the entry, read from the pinned image's code) ---- *)
Definition CDS_ENTRY : Z := wire_sigma WS_check_downstream.
Definition CDS_AT (off : Z) : Z := CDS_ENTRY + off.
(* after the frame stores (`li a2, 18` at +0xc) *)
Definition CDS_PICK : Z := CDS_AT 0xc.
(* the return address of the call of rp_ds_accept (`jal` at +0x10c) *)
Definition CDS_RET : Z := CDS_AT 0x110.
Definition CDS_LEAF : Z := wire_sigma WS_rp_ds_accept.

(* ---- helpers (UciCvBSegs.v cv_le_bytes_to_Z .. cv_rd_all, copied) ---- *)

Lemma cds_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma cds_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply cds_le_bytes_to_Z.
Qed.

Fixpoint cds_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: cds_c8s n' (skipn 8 bs)
  end.

Lemma cds_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (cds_c8s n bs) /\ cells_bytes (cds_c8s n bs) = bs /\ cells_size (cds_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [cds_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite cds_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

Lemma cds_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (cds_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (cds_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* The carved 16 bytes, read as 2 words. *)
Lemma cds_frame_words : forall m A bs, rw_cells rsegs m A [CB 16 bs] ->
  exists v0 v8 : word, rw_cells rsegs m A [C8 v0; C8 v8].
Proof.
  intros m A bs H. apply (cds_rw_c8s rsegs m A 2 bs) in H. cbn [cds_c8s] in H. do 2 eexists. exact H.
Qed.

Lemma cds_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

(* the one-byte window of the shadow range of [p, p + n) at the shadow byte of a *)
Lemma cds_shadow_one : forall RNG p n a,
  ExecF.rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1) ->
  p <= a < p + n -> ExecF.rng RNG (shadow_addr a) 1.
Proof.
  intros RNG p n a H Ha. unfold shadow_addr in *.
  assert (L1 : p / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : a / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* the shadow check of a one-byte access at X passes on shadow byte k *)
Definition cds_shok1 (k : byte) (X : Z) : Prop := bv_signed k = 0 \/ X mod 8 < bv_signed k.

Lemma cds_shok1_of : forall (k : byte) X, shadow_ok X (bv_signed k) -> cds_shok1 k X.
Proof. intros k X [C|[C _]]; [left | right]; exact C. Qed.

(* `addi r, b, -c; seqz s, r` on a loaded byte b: s = (b == c) (lib/Prog/check_downstream.v chk_seqz_byte). *)
Lemma cds_seqz_byte : forall (b : byte) c k, 0 <= c < 256 -> k = - c ->
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + k)) 1 = Z_to_bv 64 (if bv_unsigned b =? c then 1 else 0).
Proof.
  intros b c k Hc ->. pose proof (byte_range b) as Xb. unfold zxb. rewrite zxb_u.
  destruct (Z.eqb_spec (bv_unsigned b) c) as [E|E].
  - rewrite E. replace (c + - c) with 0 by lia. vm_compute. reflexivity.
  - unfold v_sltiu. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
    replace ((bv_unsigned b + - c) mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

(* ---- tactics ---- *)

Ltac cds_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac cds_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cds_w := cds_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac cds_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
(* StepF's step reads the start pc: each proof first computes every closed name of its goal to its value. *)
Ltac cds_lit X := let v := eval vm_compute in X in change X with v.
Ltac cds_lits :=
  repeat match goal with
  | |- context [CDS_RET] => cds_lit CDS_RET
  | |- context [CDS_PICK] => cds_lit CDS_PICK
  | |- context [CDS_LEAF] => cds_lit CDS_LEAF
  | |- context [CDS_AT ?o] => cds_lit (CDS_AT o)
  | |- context [CDS_ENTRY] => cds_lit CDS_ENTRY
  end.

Local Ltac zc H := zify_cond H; rewrite ?zxb_u in H.

(* the shadow check from its `bnez` back to the access: k = 0 falls through, else `andi`; `blt` returns *)
Local Ltac chk1 HX C K :=
  unfold cds_shok1 in C;
  lazymatch type of C with bv_signed ?k = 0 \/ _ =>
  lazymatch type of HX with bv_unsigned _ = ?X =>
    let MB := fresh "MB" in
    pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as MB;
    step; rewrite sxb_eq0; destruct C as [C|C];
    [ rewrite (proj2 (Z.eqb_eq _ _) C); cbn [negb]; apply K
    | rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
      step; step;
      rewrite land7, HX, (lts_low (X mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); apply K ]
  end end.

Section Checks.
Variables (RNG : footprint) (Q : machine_state -> Prop)
  (ra sp1 gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32).

(* the states of the want: sp1 is the frame's sp; r0 .. r5 are a0 .. a5 *)
Local Abbreviation ST pc m r0 r1 r2 r3 r4 r5 :=
  (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 r0 r1 r2 r3 r4 r5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* 0x80020 (+0x38): `bnez a4` on the shadow byte of f + 12 (in a2); its check 0x8011c `andi a5, a2, 7` / 0x80120
   `blt a5, a4` returns to 0x80024: the `jal __asan_report_load1` at 0x80128 is not reached. *)
Lemma cds_ck_80020 : forall m (r0 r1 r2 r3 r5 : word) (k : byte) X,
  bv_unsigned r2 = X -> cds_shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x80024 m r0 r1 r2 r3 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x80020 m r0 r1 r2 r3 (sxb k) r5).
Proof. intros m r0 r1 r2 r3 r5 k X HX C K. chk1 HX C K. Qed.

(* 0x80048 (+0x60): `bnez a3` on the shadow byte of f + 13 (in a2); its check 0x8012c `andi a4, a2, 7` / 0x80130
   `blt a4, a3` returns to 0x8004c: the `jal __asan_report_load1` at 0x80138 is not reached. *)
Lemma cds_ck_80048 : forall m (r0 r1 r2 r4 r5 : word) (k : byte) X,
  bv_unsigned r2 = X -> cds_shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x8004c m r0 r1 r2 (sxb k) v r5)) ->
  evtF rsegs RNG Q (ST 0x80048 m r0 r1 r2 (sxb k) r4 r5).
Proof. intros m r0 r1 r2 r4 r5 k X HX C K. chk1 HX C K. Qed.

(* 0x80088 (+0xa0): `bnez a4` on the shadow byte of f + 13 (in a2); its check 0x8013c `andi a5, a2, 7` / 0x80140
   `blt a5, a4` returns to 0x8008c: the `jal __asan_report_load1` at 0x80148 is not reached. *)
Lemma cds_ck_80088 : forall m (r0 r1 r2 r3 r5 : word) (k : byte) X,
  bv_unsigned r2 = X -> cds_shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x8008c m r0 r1 r2 r3 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x80088 m r0 r1 r2 r3 (sxb k) r5).
Proof. intros m r0 r1 r2 r3 r5 k X HX C K. chk1 HX C K. Qed.

(* 0x800ac (+0xc4): `bnez a4` on the shadow byte of f + 16 (in a2); its check 0x8014c `andi a5, a2, 7` / 0x80150
   `blt a5, a4` returns to 0x800b0: the `jal __asan_report_load1` at 0x80158 is not reached. *)
Lemma cds_ck_800ac : forall m (r0 r1 r2 r3 r5 : word) (k : byte) X,
  bv_unsigned r2 = X -> cds_shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x800b0 m r0 r1 r2 r3 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x800ac m r0 r1 r2 r3 (sxb k) r5).
Proof. intros m r0 r1 r2 r3 r5 k X HX C K. chk1 HX C K. Qed.

(* 0x800d4 (+0xec): `bnez a3` on the shadow byte of f + 17 (in a2); its check 0x8015c `andi a4, a2, 7` / 0x80160
   `blt a4, a3` returns to 0x800d8: the `jal __asan_report_load1` at 0x80168 is not reached. *)
Lemma cds_ck_800d4 : forall m (r0 r1 r2 r4 r5 : word) (k : byte) X,
  bv_unsigned r2 = X -> cds_shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x800d8 m r0 r1 r2 (sxb k) v r5)) ->
  evtF rsegs RNG Q (ST 0x800d4 m r0 r1 r2 (sxb k) r4 r5).
Proof. intros m r0 r1 r2 r4 r5 k X HX C K. chk1 HX C K. Qed.

End Checks.

(* Each byte test the model holds whose answer a path fixed (lib/Prog/check_downstream.v eqb_facts). *)
Local Ltac cds_eqb_facts := repeat match goal with
  | |- context [Z.eqb ?x ?c] =>
      first [ rewrite (proj2 (Z.eqb_eq x c)) by lia | rewrite (proj2 (Z.eqb_neq x c)) by lia ]
  end.

(* the model on the branch facts of the path (lib/Prog/check_downstream.v ds_eval) *)
Local Ltac cds_eval :=
  unfold PDA.ds_accept_result, PDA.ds_byte;
  repeat match goal with Eb : ?b = nth ?i ?l ?d |- context [nth ?i ?l ?d] => rewrite <- Eb end;
  first [ rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia ];
  cds_eqb_facts; cbn [andb orb negb]; reflexivity.

(* an exit at the call: s0 holds the want v, which the model gives on the path *)
Local Ltac cds_fin v :=
  apply evtF_done; cbv beta;
  lazymatch goal with |- context [PDA.ds_accept_result ?n ?l] =>
    replace (PDA.ds_accept_result n l) with v by cds_eval end;
  do 4 eexists; reflexivity.

(* ---- cds_frame_F: entry -> +0xc, the frame written ---- *)
Lemma cds_frame_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    ExecF.rng RNG (bv_unsigned sp - 16) 16 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CDS_PICK) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CDS_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO RFR.
  cds_lits.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  destruct (cds_frame_words _ _ _ FR) as (v0 & v8 & FR'). clear FR. rename FR' into FR.
  (* addi sp, sp, -0x10; sd ra, 8(sp); sd s0, 0(sp) *)
  do 3 step.
  cds_memF ltac:(fun mm => apply evtF_done; exists mm).
  replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia.
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; cds_regs; try cds_w.
Qed.

(* ---- cds_pick_F: +0xc -> rp_ds_accept (ra = CDS_RET), s0 := the want ---- *)
Lemma cds_pick_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte),
    (18 <= bv_unsigned a1 ->
       (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) /\ bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) /\
       addressable m (bv_unsigned a0 + 12) 6) ->
    (18 <= bv_unsigned a1 ->
       ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
       ExecF.rng RNG (bv_unsigned a0 + 12) 6 /\
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
         (shadow_addr (bv_unsigned a0 + 12 + 6 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a2' a3' a4' a5' : word,
         ms' = MS (mkR (Z_to_bv 64 CDS_RET) sp gp tp t0 t1 t2
                    (Z_to_bv 64 (PDA.ds_accept_result (bv_unsigned a1) bs)) s1 a0 a1 a2' a3' a4' a5' a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CDS_LEAF) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CDS_PICK) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    HB RX.
  cds_lits.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2^64) in Ra1.
  (* li a2, 18; bltu a1, a2 *)
  step. step. if_cases HL.
  { (* n < 18: mv s0, zero; jal rp_ds_accept *)
    zc HL. do 2 step. cds_fin 0. }
  zc HL.
  destruct (HB HL) as (LEN & BA & GCK & CK & ADR).
  destruct (RX HL) as (RGC & RCK & RBUF & RSH).
  clear HB RX.
  destruct ADR as (P0 & N0 & PE & AB).
  (* the four bytes it reads, f + 12, 13, 16, 17: each is application memory and its shadow byte passes *)
  destruct (AB 0 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
  destruct (AB 1 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
  destruct (AB 4 ltac:(lia)) as (APP16 & k16 & MK16 & SK16).
  destruct (AB 5 ltac:(lia)) as (APP17 & k17 & MK17 & SK17).
  clear AB.
  rewrite Z.add_0_r in APP12, MK12, SK12.
  replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in APP13, MK13, SK13 by lia.
  replace (bv_unsigned a0 + 12 + 4) with (bv_unsigned a0 + 16) in APP16, MK16, SK16 by lia.
  replace (bv_unsigned a0 + 12 + 5) with (bv_unsigned a0 + 17) in APP17, MK17, SK17 by lia.
  apply cds_shok1_of in SK12, SK13, SK16, SK17.
  pose proof (cds_shadow_one RNG _ 6 (bv_unsigned a0 + 12) RSH ltac:(lia)) as RS12.
  pose proof (cds_shadow_one RNG _ 6 (bv_unsigned a0 + 13) RSH ltac:(lia)) as RS13.
  pose proof (cds_shadow_one RNG _ 6 (bv_unsigned a0 + 16) RSH ltac:(lia)) as RS16.
  pose proof (cds_shadow_one RNG _ 6 (bv_unsigned a0 + 17) RSH ltac:(lia)) as RS17.
  clear RSH.
  unfold GOT_CELL_K, CELL_K, shadow_addr, ASAN_K in *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, APP16, APP17, PE.
  pose proof (cds_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (cds_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  pose proof (bytes_nth m _ bs 12 BA ltac:(lia)) as F12.
  pose proof (bytes_nth m _ bs 13 BA ltac:(lia)) as F13.
  pose proof (bytes_nth m _ bs 16 BA ltac:(lia)) as F16.
  pose proof (bytes_nth m _ bs 17 BA ltac:(lia)) as F17.
  change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
  change (Z.of_nat 16) with 16 in F16. change (Z.of_nat 17) with 17 in F17.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
  remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
  (* the UBSan check of f + 12: `li a2, -12`; `bgeu a0, a2` falls through *)
  step. step. if_false.
  (* the shadow base through its GOT word: auipc a2; ld a2; ld a3 *)
  step. step. step.
  (* f + 12: its shadow byte and check *)
  step. gen_addi a0 w12 U12.
  assert (RW12 : ExecF.rng RNG (bv_unsigned w12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
  step. gen_shr w12 g12 G12. rewrite U12 in G12.
  step. gen_addi g12 h12 H12.
  assert (RH12 : ExecF.rng RNG (bv_unsigned h12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS12); lia).
  pose proof (rdw0 m h12 _ _ MK12 ltac:(lia)) as R. step. clear R.
  eapply cds_ck_80020 with (X := bv_unsigned a0 + 12); [exact U12 | exact SK12 | intros v12].
  (* f[12]; li a4, 0x88; bne a2, a4 *)
  pose proof (rdw0 m w12 _ _ F12 ltac:(lia)) as R. step. clear R.
  step. step. if_cases HC12; zc HC12.
  - (* f[12] <> 0x88 (+0x78): li a4, -12; bgeu a0, a4 (falls through); li a4, 0x81; bne a2, a4 *)
    step. step. if_false.
    step. step. if_cases HC12b; zc HC12b.
    { (* f[12] is neither 0x88 nor 0x81: mv s0, zero; jal *)
      do 2 step. cds_fin 0. }
    (* f[12] = 0x81: li a2, -14; bltu a2, a0 (falls through) *)
    step. step. if_false.
    (* f + 13: its shadow byte and check *)
    step. gen_addi a0 w13 U13.
    assert (RW13 : ExecF.rng RNG (bv_unsigned w13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
    step. gen_shr w13 g13 G13. rewrite U13 in G13.
    step. gen_addi g13 h13 H13.
    assert (RH13 : ExecF.rng RNG (bv_unsigned h13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS13); lia).
    pose proof (rdw0 m h13 _ _ MK13 ltac:(lia)) as R. step. clear R.
    eapply cds_ck_80088 with (X := bv_unsigned a0 + 13); [exact U13 | exact SK13 | intros v13].
    (* f[13]; bnez a2 *)
    pose proof (rdw0 m w13 _ _ F13 ltac:(lia)) as R. step. clear R.
    step. if_cases HC13; zc HC13.
    { (* f[13] <> 0: mv s0, zero; jal *)
      do 2 step. cds_fin 0. }
    (* li a2, -16; bgeu a0, a2 (falls through) *)
    step. step. if_false.
    (* f + 16: its shadow byte and check *)
    step. gen_addi a0 w16 U16.
    assert (RW16 : ExecF.rng RNG (bv_unsigned w16) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
    step. gen_shr w16 g16 G16. rewrite U16 in G16.
    step. gen_addi g16 h16 H16.
    assert (RH16 : ExecF.rng RNG (bv_unsigned h16) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS16); lia).
    pose proof (rdw0 m h16 _ _ MK16 ltac:(lia)) as R. step. clear R.
    eapply cds_ck_800ac with (X := bv_unsigned a0 + 16); [exact U16 | exact SK16 | intros v16].
    (* f[16]; li a4, 0x88; bne a2, a4 *)
    pose proof (rdw0 m w16 _ _ F16 ltac:(lia)) as R. step. clear R.
    step. step. if_cases HC16; zc HC16.
    { (* f[16] <> 0x88: mv s0, zero; jal *)
      do 2 step. cds_fin 0. }
    (* li a2, -18; bltu a2, a0 (falls through) *)
    step. step. if_false.
    (* f + 17: its shadow byte and check *)
    step. gen_addi a0 w17 U17.
    assert (RW17 : ExecF.rng RNG (bv_unsigned w17) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
    step. gen_shr w17 g17 G17. rewrite U17 in G17.
    step. gen_addi g17 h17 H17.
    assert (RH17 : ExecF.rng RNG (bv_unsigned h17) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS17); lia).
    pose proof (rdw0 m h17 _ _ MK17 ltac:(lia)) as R. step. clear R.
    eapply cds_ck_800d4 with (X := bv_unsigned a0 + 17); [exact U17 | exact SK17 | intros v17].
    (* f[17]; addi a2, a2, -0x19; seqz s0, a2; j; jal *)
    pose proof (rdw0 m w17 _ _ F17 ltac:(lia)) as R. step. clear R.
    do 4 step.
    rewrite (cds_seqz_byte _ 25 (-25)) by lia.
    cds_fin (if bv_unsigned b17 =? 25 then 1 else 0).
  - (* f[12] = 0x88 (+0x48): li a2, -14; bltu a2, a0 (falls through) *)
    step. step. if_false.
    (* f + 13: its shadow byte and check *)
    step. gen_addi a0 w13 U13.
    assert (RW13 : ExecF.rng RNG (bv_unsigned w13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
    step. gen_shr w13 g13 G13. rewrite U13 in G13.
    step. gen_addi g13 h13 H13.
    assert (RH13 : ExecF.rng RNG (bv_unsigned h13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS13); lia).
    pose proof (rdw0 m h13 _ _ MK13 ltac:(lia)) as R. step. clear R.
    eapply cds_ck_80048 with (X := bv_unsigned a0 + 13); [exact U13 | exact SK13 | intros v13].
    (* f[13]; li a3, 0x19; bne a2, a3 *)
    pose proof (rdw0 m w13 _ _ F13 ltac:(lia)) as R. step. clear R.
    step. step. if_cases HC13; zc HC13.
    { (* f[13] <> 0x19 (+0x100): li a2, -12; bgeu a0, a2 (falls through); mv s0, zero; jal *)
      step. step. if_false. do 2 step. cds_fin 0. }
    (* f[13] = 0x19: li s0, 1; j; jal *)
    do 3 step. cds_fin 1.
Qed.

(* ---- cds_tail_F: CDS_RET -> the return ---- *)
Lemma cds_tail_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) [C8 c0; C8 cra] ->
    bv_unsigned sp + 16 < 2 ^ 64 ->
    ExecF.rng RNG (bv_unsigned sp) 16 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + 16)) gp tp t0 t1 t2 c0 s1 r a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 r s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CDS_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c0 cra FR HSP RFR.
  cds_lits.
  pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  (* bne a0, s0: a0 = s0 *)
  step. if_false.
  (* ld ra; ld s0; addi sp; ret *)
  do 4 step. apply evtF_done. reflexivity.
Qed.
