(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: the addresses, frame shape and inlined-expected_value statement of reac-repacer/fuzz_uci's
   check_value in image A, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/crtA_iface.v and crtA_loop_stmt.v
   (origin/ossv/recipes 88154566652a); the expected_value statement is the footprint twin of the plain walk's
   continuation form (lib/Prog/check_value.v, Section Ev, ev_block / KFIN). *)
(* UciCvIface: what the pieces of the image-A walk of check_value (fuzz_uci.asan 0x7f62c = uci_sigma US_check_value)
   share, for the caller-journal statement lib/A/Prog/check_value_cg.v.

   FORM: check_value's own body runs as footprint runs (lib/Lib/ExecF.v evtF, stepped by lib/Lib/StepF.v), carried
   into SRr by lib/A/Prog/LeafCgFacts.v bridge_evtF_stmt_YA0n; each call is cut by its callee's contract.

   Control flow (offsets from the entry, read from the pinned image's code):
     +0x000 entry: `addi sp, sp, -0x40`, s5 .. s0 and ra stored at 8(sp) .. 0x38(sp), s0 := cur, s4 := n, s3 := r,
            s5 := the shadow offset (GOT_CELL_K -> CELL_K), a0 := n + (n == 0)
     +0x040 call malloc (trampoline), returns +0x044
     +0x044 `beqz a0` to the abort (+0x254); s1 := a0; `beqz s4` (n = 0) to +0x0ac
     +0x058 call __asan_memcpy(s1, r, n), returns +0x05c
     +0x068 call rp_uci_int(s1, n, cur), returns +0x06c
     +0x06c .. +0x218 the inlined expected_value of the reply r (five loops; __asan_report_load1 calls at +0x0a8,
            +0x10c, +0x188, +0x1f8), which ends at +0x21c with s0 the value
     +0x0ac (n = 0) a1 := 0, a2 := s0; call rp_uci_int(s1, 0, cur) at +0x0b4, returns +0x0b8; s2 := a0, `j` +0x21c
     +0x21c `sext.w s0, s0`; `bne s2, s0` to the abort (+0x254); a0 := s1; call free (trampoline) at +0x228,
            returns +0x22c
     +0x22c a0 := s2; the epilogue; `ret`.
   +0x254 (__asan_handle_no_return) / +0x258 (abort) and the four report calls are the unreachable exits. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Cells Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciPSyms UciPAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
Import ListNotations.
Open Scope Z_scope.

Definition CV_ENTRY : Z := uci_sigma US_check_value.
Definition CV_AT (off : Z) : Z := CV_ENTRY + off.
Definition CV_MALLOC : Z := uci_sigma US___interceptor_trampoline_malloc.
Definition CV_FREE : Z := uci_sigma US___interceptor_trampoline_free.
Definition CV_MEMCPY : Z := uci_sigma US___asan_memcpy.
Definition CV_RUI : Z := uci_sigma US_rp_uci_int.

(* The cut points, as offsets from the entry. *)
Definition CV_RET_MALLOC : Z := CV_AT 0x44.
Definition CV_RET_MEMCPY : Z := CV_AT 0x5c.
Definition CV_RET_RUI : Z := CV_AT 0x6c.
Definition CV_RET_RUI0 : Z := CV_AT 0xb8.
Definition CV_TEST : Z := CV_AT 0x21c.
Definition CV_RET_FREE : Z := CV_AT 0x22c.

(* The frame: the caller's s5, s4, s3, s2, s1, s0, ra at 8(sp) .. 0x38(sp) of the 0x40-byte frame, i.e. the 56 bytes
   [entry sp - 0x38, entry sp). *)
Definition cv_fr (c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
  [C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

(* The i-th reply byte, 0 past the end (lib/Prog/check_value.v nthz). *)
Definition nthz (l : list Z) (i : Z) : Z := nth (Z.to_nat i) l 0.

(* The inlined expected_value, +0x06c .. +0x21c, as a footprint run in continuation form: from the return of
   rp_uci_int (a0 = g, the value it returned) with s0 = cur, s1 = the copy, s3 = r, s4 = n, s5 = the shadow offset,
   every path reaches +0x21c with s2 = g and s0 = expected_value_m of the n reply bytes, the other kept registers
   and the memory unchanged (the block stores nothing). Each loop iteration loads the shadow byte of r + i (1 byte
   inside the 8-aligned cover of the reply's shadow) and then the reply byte r + i (1 byte inside [r, r + n)); the
   reply's shadow allows every such load (addressable), so no report call is reached. *)
Definition cv_ev_stmt_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 g a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r n cur : Z) (zs : list Z)
         (Q : machine_state -> Prop),
    4096 <= r -> 0 < n <= 255 -> Z.of_nat (length zs) = n ->
    (forall i, 0 <= nthz zs i < 256) ->
    (forall i, 0 <= i < n -> mrd rsegs m (wa (r + i)) = Some (Z_to_bv 8 (nthz zs i))) ->
    addressable m r n ->
    ExecF.rng RNG r n ->
    ExecF.rng RNG (shadow_addr r / 8 * 8) (shadow_addr (r + n - 1) / 8 * 8 + 8 - shadow_addr r / 8 * 8) ->
    INT_MIN <= cur <= INT_MAX -> bv_unsigned s0 = cur mod 2 ^ 64 ->
    (forall (s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word),
       bv_unsigned s0' = expected_value_m zs cur mod 2 ^ 64 ->
       ExecF.evtF rsegs RNG Q
         (MS (mkR ra sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7' g (Z_to_bv 64 r) (Z_to_bv 64 n)
                  (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CV_TEST) fc None m (seg_rom rsegs))) ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 g a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 r) (Z_to_bv 64 n)
               (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CV_RET_RUI) fc None m (seg_rom rsegs)).

(* The list facts both halves of the expected_value walk use (lib/Prog/check_value.v:23-42 skipn_nth_cons,
   first_line_nth, first_line_le and :265-274 fl_nth_zs, flsfx_cons, stated over the reply list). *)
Lemma cv_skipn_nth_cons : forall (l : list Z) (i : nat), (i < length l)%nat ->
  skipn i l = nth i l 0 :: skipn (S i) l.
Proof.
  induction l as [|c t IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [skipn nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma cv_first_line_nth : forall (l : list Z) i, (i < length (first_line l))%nat ->
  nth i (first_line l) 0 = nth i l 0.
Proof.
  induction l as [|c t IH]; intros i Hi; [cbn in Hi; lia|].
  cbn [first_line] in Hi |- *. destruct (c =? 10); [cbn in Hi; lia|].
  destruct i as [|i]; cbn [nth]; [reflexivity|]. apply IH. cbn [length] in Hi. lia.
Qed.

Lemma cv_first_line_le : forall (l : list Z), (length (first_line l) <= length l)%nat.
Proof.
  induction l as [|c t IH]; cbn [first_line length]; [lia|].
  destruct (c =? 10); cbn [length]; lia.
Qed.

Lemma cv_fl_nthz : forall zs j, 0 <= j < Z.of_nat (length (first_line zs)) ->
  nthz (first_line zs) j = nthz zs j.
Proof. intros zs j Hj. unfold nthz. apply cv_first_line_nth. lia. Qed.

Lemma cv_flsfx_cons : forall zs j, 0 <= j < Z.of_nat (length (first_line zs)) ->
  skipn (Z.to_nat j) (first_line zs) = nthz zs j :: skipn (Z.to_nat (j + 1)) (first_line zs).
Proof.
  intros zs j Hj. rewrite <- (cv_fl_nthz zs j Hj). unfold nthz.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  apply cv_skipn_nth_cons. lia.
Qed.

(* The digit loop's set-up and everything after it, +0x128 .. +0x21c: the hand-off point of cv_ev_stmt_F's walk
   (lib/Prog/check_value.v ev_dgt is its plain twin). At +0x128 the leading blanks and the optional sign have been
   read: a1 = e, the length of the reply's first line; a4 = d0 < e, the index after the sign; a2 = c0, the byte at
   the sign's position (the `neg` of expected_value is c0 = '-'). The premises and the continuation are
   cv_ev_stmt_F's, with s2 already g. *)
Definition cv_dgt_stmt_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 g a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r n cur : Z) (zs : list Z)
         (Q : machine_state -> Prop) (d0 c0 : Z),
    4096 <= r -> 0 < n <= 255 -> Z.of_nat (length zs) = n ->
    (forall i, 0 <= nthz zs i < 256) ->
    (forall i, 0 <= i < n -> mrd rsegs m (wa (r + i)) = Some (Z_to_bv 8 (nthz zs i))) ->
    addressable m r n ->
    ExecF.rng RNG r n ->
    ExecF.rng RNG (shadow_addr r / 8 * 8) (shadow_addr (r + n - 1) / 8 * 8 + 8 - shadow_addr r / 8 * 8) ->
    INT_MIN <= cur <= INT_MAX -> bv_unsigned s0 = cur mod 2 ^ 64 ->
    bv_unsigned a1 = Z.of_nat (length (first_line zs)) -> bv_unsigned a2 = c0 -> bv_unsigned a4 = d0 ->
    0 <= c0 < 256 -> 0 <= d0 < Z.of_nat (length (first_line zs)) ->
    snd (sign_split (skip is_lead_blank (first_line zs))) = skipn (Z.to_nat d0) (first_line zs) ->
    fst (sign_split (skip is_lead_blank (first_line zs))) = (c0 =? 45) ->
    (forall (s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word),
       bv_unsigned s0' = expected_value_m zs cur mod 2 ^ 64 ->
       ExecF.evtF rsegs RNG Q
         (MS (mkR ra sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7' g (Z_to_bv 64 r) (Z_to_bv 64 n)
                  (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CV_TEST) fc None m (seg_rom rsegs))) ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 g (Z_to_bv 64 r) (Z_to_bv 64 n)
               (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CV_AT 0x128)) fc None m (seg_rom rsegs)).
