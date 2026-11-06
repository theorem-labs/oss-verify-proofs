(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R4.v, with its module paths, module names, addresses and numbers changed; 535 of its 675 lines of code are new or changed and 790 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/P6.v; 68 of its 134 lines of code are new or changed and 609 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P6.v p6_evt at a working branch 3803efccea0
     (blob 23917ccc08f4435b78ab4902fb8a546de4d8dcd6);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: p6_evt_of_F composes p6_pre_F, the caller's reac_ctrl_identity_reply_contract premise and
     p6_post_F and re-derives the source statement of P6.p6_evt verbatim; p6_evt_same checks that type
     against P6.p6_evt.  p6_pre_F re-runs P6.v line 136 (0x81d68 .. 0x81d7c, up to the callee entry),
     p6_post_F lines 145-158 (the return pc 0x81d80, no instruction left in the stretch). *)
(* rule 24: no function proved. *)
(* The footprint twin of P6's run [0x81d68, 0x81d80), split at the call (parent ruling: every call splits):
     li a0,0; li a1,0; ld a2,88(s1); ld a3,80(s1); ld a4,72(s1); jal reac_ctrl_identity_reply
       -> p6_pre_F, stops AT the callee entry 0x848fc with ra = 0x81d80.
   The accesses of the stretch are the three reply cells [Ab + 88], [Ab + 80], [Ab + 72], 8 bytes each, with no
   instrumented check.  p6_post_F is the return pc 0x81d80, no step left; its premises are the callee post
   facts P6's proof uses (the write set p6_W S FS of the refused call, the memory invariants it returns and
   the side-stack package fp). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanFP asan_stack_malloc_c
  reac_ctrl_identity_reply_c reac_ctrl_parse_c memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_bp.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P6.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- 0x81d68 .. 0x81d7c: li a0,0; li a1,0; the three loads; jal reac_ctrl_identity_reply ---- *)
Lemma p6_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab pa pp pn : Z),
    s1 = Z_to_bv 64 Ab ->
    0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    0 <= Ab -> Ab + 104 <= 2 ^ 64 ->
    ro_cells rsegs m (Ab + 88) [C8 (Z_to_bv 64 pa)] ->
    ro_cells rsegs m (Ab + 80) [C8 (Z_to_bv 64 pp)] ->
    ro_cells rsegs m (Ab + 72) [C8 (Z_to_bv 64 pn)] ->
    rng RNG (Ab + 88) 8 -> rng RNG (Ab + 80) 8 -> rng RNG (Ab + 72) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81d80) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab)
                                (Z_to_bv 64 0) (Z_to_bv 64 0)
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x848fc) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d68) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab pa pp pn -> Hpa Hpp Hpn HA0 HA64 RO88 RO80 RO72 G88 G80 G72.
  step. step. step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* ---- the return pc 0x81d80: the premises are the callee post facts P6's proof uses ---- *)
Lemma p6_post_F :
  forall (RNG : footprint) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32)
         (m m' : word -> option byte) (sp gp tp s0 s1 s3 s7 s8 s9 s10 : word) (S TP FS : Z),
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 19 = s3 -> getr R 23 = s7 -> getr R 24 = s8 -> getr R 25 = s9 -> getr R 26 = s10 ->
    getr R 10 = Z_to_bv 64 (-1) ->
    munch (P6.p6_W S FS) m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S -> asan_cells m' -> shadow_rw m' ->
    addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    fp [1%nat] m' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
      [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81d80) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 19 = s3 /\ getr R' 23 = s7 /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\ getr R' 26 = s10 /\
         getr R' 10 = Z_to_bv 64 (-1) /\
         munch (P6.p6_W S FS) m m'' /\ wmono rsegs m m'' /\ mem_inv rsegs m'' /\
         stk rsegs m'' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\ asan_cells m'' /\ shadow_rw m'' /\
         addressable m'' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m'' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
           [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [])
      (MS R F (Z_to_bv 64 0x81d80) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m m' sp gp tp s0 s1 s3 s7 s8 s9 s10 S TP FS
    K2 K3 K4 K8 K9 K19 K23 K24 K25 K26 K10 MU WM MI ST HAC HSW HAD HFP.
  apply evtF_done. exists R, m'. split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K23|]. split; [exact K24|]. split; [exact K25|]. split; [exact K26|].
  split; [exact K10|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact HAC|]. split; [exact HSW|]. split; [exact HAD | exact HFP].
Qed.

(* ---- the compare lemma: the source statement of P6.p6_evt ---- *)
Lemma p6_evt_of_F : reac_ctrl_identity_reply_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S Ab TP FS pa pp pn : Z),
    sp = Z_to_bv 64 S -> s1 = Z_to_bv 64 Ab -> tp = Z_to_bv 64 TP -> 0 <= TP < 2 ^ 64 ->
    0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    0 <= Ab -> Ab + 104 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_IDENTITY_REPLY_K <= S -> HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    ro_cells rsegs m (Ab + 88) [C8 (Z_to_bv 64 pa)] ->
    ro_cells rsegs m (Ab + 80) [C8 (Z_to_bv 64 pp)] ->
    ro_cells rsegs m (Ab + 72) [C8 (Z_to_bv 64 pn)] ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
      [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    reac_ctrl_identity_reply_tls m TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81d80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (-1) /\
         munch (P6.p6_W S FS) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\ asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
           [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d68) fc None m (seg_rom rsegs)).
Proof.
  intros HIR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S Ab TP FS pa pp pn -> -> -> HTP Hpa Hpp Hpn HA0 HA64 HS64 HSal HKS Hlo Hhi
    RO88 RO80 RO72 HST HMI HAC HSW HADw HADbc HRB HRM HGC HC254 HC255 HFP HTLS.
  pose proof HIR as HC. unfold reac_ctrl_identity_reply_contract, REAC_CTRL_IDENTITY_REPLY in HC.
  assert (Etp : bv_unsigned (Z_to_bv 64 TP) = TP) by (apply MState.unsigned_lit; exact HTP).
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply p6_pre_F with (Ab := Ab) (pa := pa) (pp := pp) (pn := pn);
      try assumption; try reflexivity; apply rng_all; lia. }
  intros ms' ->.
  eapply evt_cut.
  { eapply HC with (fr := 0) (len := 0) (pa := pa) (pp := pp) (pn := pn) (S := S) (FS := FS)
      (g := repeat (Z_to_bv 8 0) 50) (ja := []) (jp := []) (jn := []).
    all: rewrite ?Etp.
    all: try reflexivity.
    all: try assumption.
    all: try (intros HH; rewrite P6.p6_args0 in HH; discriminate HH).
    all: try lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI & ST & HR & HAC' & HSW' & HAD' & HFP' & HTLS').
  subst ms'. rewrite Etp in HFP', HTLS'.
  rewrite P6.p6_ret0 in *. rewrite (P6.p6_W_eq 0 pa pp pn S FS (repeat (Z_to_bv 8 0) 50)) in MU.
  rewrite P6.p6_Wc0, P6.p6_D0 in HFP'.
  replace (ret_pc (Z_to_bv 64 0x81d80)) with (Z_to_bv 64 0x81d80)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (evtF_evt rsegs RNG_all).
  apply p6_post_F with (m := m) (S := S) (TP := TP) (FS := FS); try reflexivity; assumption.
Qed.

(* p6_evt_of_F has exactly the statement of the source lemma P6.p6_evt. *)
Definition p6_evt_same : ltac:(let T := type of P6.p6_evt in exact T) := p6_evt_of_F.
