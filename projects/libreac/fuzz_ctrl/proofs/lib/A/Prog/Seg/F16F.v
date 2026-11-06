(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F12.v, with its module paths, module names, addresses and numbers changed; 1202 of its 1379 lines of code are new or changed and 1532 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F16.v; 536 of its 868 lines of code are new or changed and 1047 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F16.v blob ed137984f9f8 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F16.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F16.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint twins of Seg/F16.v's seven run lemmas (segment F16 = 0x821d0 .. 0x8229c):
   - f16_loop_F: F16.f16_loop (:276), the byte-sum loop 0x821d0-0x821f4. Its accesses are the record bytes
     p + q and their shadow bytes (Z.shiftr (p + q) 3 + ASAN_K) for q < i + k, which its own ov_read_bytes
     premises name: one rng premise for [p, p + (i + k)) and one for the shadow bytes of that range.
   - f16_p210_F / f16_p238_F / f16_p250_F / f16_p270_F / f16_p284_F: F16's v1.9 tail lemmas (:526 / :490 /
     :457 / :424 / :386), each a continuation (CPS) lemma over the next state; the twin takes the
     continuation as an ExecF.evtF under the same RNG and concludes an ExecF.evtF. Their accesses are the
     spill loads [A+104] / [A+56] / [A+256] / [A+48] / [A+144], the u16 at P256, the two record bytes at X1
     and X2 and their two shadow bytes, each named by the lemma's own premise.
   - f16_evt_F: F16.f16_evt (:570), the whole run: the loop, the sum check, the tail lemmas and the
     reac_identity_ingest call. The callee enters through reac_identity_ingest_contract_F
     (lib/A/Prog/reac_identity_ingest_c.v) in the place of F16.f16_evt's plain contract premise; the callee's
     own rng premises are that contract's, passed through unchanged.
   Each *_of_F re-derives F16's statement at ExecF.RNG_all; the CPS corollaries map their continuation with
   ExecF_all.evt_evtF_all first (the documented use of lib/Lib/ExecF_all.v) and conclude with
   ExecF.evtF_evt. F16.v itself is unchanged; its rd8 / rd2 lemmas and its ush tactic are reused by Import. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentLib RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv bcmp_wrap_c
  reac_identity_ingest_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F13.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_slot Tac_b5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
(* F16 itself, imported for its rd8 / rd2 lemmas and its ush tactic. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F16.
(* Last: StepF's step / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF ExecF_all.
Import ListNotations.
(* As in F16.v: YK11 last among the term-level names (its seg_rom / getr). *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ---- the footprint arithmetic of the shadow bytes of a byte range (the only helper this file adds). ---- *)

(* One shadow byte of [p, p + n) lies in the shadow cover of that range. *)
Lemma f16_sh_rng : forall (RNG : ExecF.footprint) p n q,
  0 <= p -> 0 <= q -> q < n -> p + n <= 2 ^ 64 ->
  ExecF.rng RNG (Z.shiftr p 3 + ASAN_K) (Z.shiftr (p + n - 1) 3 - Z.shiftr p 3 + 1) ->
  ExecF.rng RNG (Z.shiftr (p + q) 3 + ASAN_K) 1.
Proof.
  intros RNG p n q Hp Hq Hqn Hpn H.
  rewrite !Z.shiftr_div_pow2 in H by lia. change (2 ^ 3) with 8 in H.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_le_mono p (p + q) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (p + q) (p + n - 1) 8 ltac:(lia) ltac:(lia)).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* The same two ranges at ExecF.RNG_all (for the *_of_F corollaries). *)
Lemma f16_sh_all : forall p n, 0 <= p -> 0 < n -> p + n <= 2 ^ 64 ->
  ExecF.rng ExecF.RNG_all (Z.shiftr p 3 + ASAN_K) (Z.shiftr (p + n - 1) 3 - Z.shiftr p 3 + 1).
Proof.
  intros p n Hp Hn Hpn. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
Qed.

Lemma f16_sh1_all : forall x, 0 <= x < 2 ^ 64 -> ExecF.rng ExecF.RNG_all (Z.shiftr x 3 + ASAN_K) 1.
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
Qed.

Section D.
Context {fx : FPState}.

(* ---- the byte-sum loop 0x821d0 .. 0x821f4 under a footprint RNG. ---- *)
Lemma f16_loop_F : forall (RNG : ExecF.footprint) (k i : nat)
    (ra0 sp gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bs : list byte),
  0 <= p -> p + Z.of_nat (i + k) + 8 < 2 ^ 64 -> (1 <= k)%nat ->
  (forall q, (q < i + k)%nat -> ov_read_bytes rsegs m (wa (p + Z.of_nat q)) 1 = Some [nth q bs (Z_to_bv 8 0)]) ->
  (forall q, (q < i + k)%nat -> ov_read_bytes rsegs m (wa (Z.shiftr (p + Z.of_nat q) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0]) ->
  ExecF.rng RNG p (Z.of_nat (i + k)) ->
  ExecF.rng RNG (Z.shiftr p 3 + ASAN_K)
    (Z.shiftr (p + Z.of_nat (i + k) - 1) 3 - Z.shiftr p 3 + 1) ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists a6' : word,
       ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + Z.of_nat (i + k))) (Z_to_bv 64 (psum bs (i + k)))
                     a2 a3 (Z_to_bv 64 0) (Z_to_bv 64 (p + Z.of_nat (i + k))) a6' a7
                     s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                Fr (Z_to_bv 64 0x82208) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
             a2 a3 (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (p + Z.of_nat i)) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG k. induction k as [|k IH]; intros i ra0 sp gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
    s11 t3 t4 t5 t6 Fr fc m p bs Hp Hb Hk HRD HSH Gb Gs; [lia|].
  pose proof (HRD i ltac:(lia)) as RDi. pose proof (HSH i ltac:(lia)) as SHi.
  (* the one-byte access facts of this turn, from the two rng premises *)
  pose proof (f16_sh_rng RNG p (Z.of_nat (i + S k)) (Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) Gs) as Gs1.
  step. step. ush. step. step. if_false.
  step. change (zxb (nth i bs (Z_to_bv 8 0))) with (Z_to_bv 64 (bv_unsigned (nth i bs (Z_to_bv 8 0)))).
  step. step. step. step. step.
  clear RDi SHi Gs1.
  destruct k as [|k].
  - if_false. step.
    apply ExecF.evtF_done. exists (Z_to_bv 64 (bv_unsigned (nth i bs (Z_to_bv 8 0)))).
    replace (p + Z.of_nat i + 1) with (p + Z.of_nat (i + 1)) by lia.
    replace (psum bs i + bv_unsigned (nth i bs (Z_to_bv 8 0))) with (psum bs (i + 1))
      by (rewrite Nat.add_1_r; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat 1 + -1)) with (Z_to_bv 64 0) by (f_equal; lia). reflexivity.
  - assert (Hne : negb (bv_eqb (Z_to_bv 64 (Z.of_nat (S (S k)) + -1)) (Z_to_bv 64 0)) = true).
    { apply Bool.negb_true_iff. apply eqb0_false. split; [lia|]. rewrite Nat2Z.inj_succ in *. lia. }
    rewrite Hne; cbv iota.
    replace (p + Z.of_nat i + 1) with (p + Z.of_nat (i + 1)) by lia.
    replace (psum bs i + bv_unsigned (nth i bs (Z_to_bv 8 0))) with (psum bs (i + 1))
      by (rewrite Nat.add_1_r; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat (S (S k)) + -1)) with (Z_to_bv 64 (Z.of_nat (S k)))
      by (f_equal; rewrite Nat2Z.inj_succ; lia).
    replace (i + S (S k))%nat with ((i + 1) + S k)%nat by lia.
    apply IH.
    + exact Hp.
    + replace ((i + 1) + S k)%nat with (i + S (S k))%nat by lia. exact Hb.
    + lia.
    + intros q Hq. apply HRD. lia.
    + intros q Hq. apply HSH. lia.
    + replace ((i + 1) + S k)%nat with (i + S (S k))%nat by lia. exact Gb.
    + replace ((i + 1) + S k)%nat with (i + S (S k))%nat by lia. exact Gs.
Qed.

Lemma f16_loop_of_F : forall (k i : nat)
    (ra0 sp gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bs : list byte),
  0 <= p -> p + Z.of_nat (i + k) + 8 < 2 ^ 64 -> (1 <= k)%nat ->
  (forall q, (q < i + k)%nat -> ov_read_bytes rsegs m (wa (p + Z.of_nat q)) 1 = Some [nth q bs (Z_to_bv 8 0)]) ->
  (forall q, (q < i + k)%nat -> ov_read_bytes rsegs m (wa (Z.shiftr (p + Z.of_nat q) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0]) ->
  LE.evt rsegs
    (fun ms' => exists a6' : word,
       ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + Z.of_nat (i + k))) (Z_to_bv 64 (psum bs (i + k)))
                     a2 a3 (Z_to_bv 64 0) (Z_to_bv 64 (p + Z.of_nat (i + k))) a6' a7
                     s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                Fr (Z_to_bv 64 0x82208) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
             a2 a3 (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (p + Z.of_nat i)) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs)).
Proof.
  intros k i ra0 sp gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    Fr fc m p bs Hp Hb Hk HRD HSH.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f16_loop_F ExecF.RNG_all k i ra0 sp gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11
           t3 t4 t5 t6 Fr fc m p bs Hp Hb Hk HRD HSH).
  - apply ExecF.rng_all; lia.
  - apply f16_sh_all; lia.
Qed.

End D.

Section T.
Context {fx : FPState}.

(* 0x82284 .. 0x82298: the low byte, the 16-bit join, the compare and the identity buffer pointer. *)
Lemma f16_p284_F : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA id X2 : Z) (ch cl : byte),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa X2) 1 = Some [cl] ->
  FA = 256 * bv_unsigned ch + bv_unsigned cl ->
  q64 m (A + 144) id ->
  (forall a4 : word, ExecF.evtF rsegs RNG Q
     (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 id) (Z_to_bv 64 FA) a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82298) fc None m (seg_rom rsegs))) ->
  ExecF.rng RNG X2 1 -> ExecF.rng RNG (A + 144) 8 ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (zxb ch) (Z_to_bv 64 FA) a2 a3 (Z_to_bv 64 X2) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82284) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA id X2 ch cl HA0 HA HX2 RDl HFA H144 K GX2 G144.
  pose proof (rd8 m (A + 144) id H144) as RD144.
  pose proof (f16_byte_range ch) as Rh. pose proof (f16_byte_range cl) as Rl.
  (* 0x82284 lbu a4,0(a4) ; 0x82288 slli a0,a0,8 ; 0x8228c or a0,a0,a4 *)
  step. step. step.
  unfold zxb.
  rewrite ?(unsigned_lit (bv_unsigned ch)) by lia.
  rewrite ?(unsigned_lit (bv_unsigned cl)) by lia.
  rewrite ?(unsigned_lit (Z.shiftl (bv_unsigned ch) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite ?(Z.lor_comm (Z.shiftl (bv_unsigned ch) 8) (bv_unsigned cl)).
  rewrite ?(lor_shiftl8_add (bv_unsigned cl) (bv_unsigned ch)) by lia.
  replace (bv_unsigned cl + 256 * bv_unsigned ch) with FA by lia.
  (* 0x82290 bne a0,a1 : equal, not taken *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x82294 ld a0,144(s1) *)
  step.
  apply K.
Qed.

Lemma f16_p284_of_F : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA id X2 : Z) (ch cl : byte),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa X2) 1 = Some [cl] ->
  FA = 256 * bv_unsigned ch + bv_unsigned cl ->
  q64 m (A + 144) id ->
  (forall a4 : word, LE.evt rsegs Q
     (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 id) (Z_to_bv 64 FA) a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82298) fc None m (seg_rom rsegs))) ->
  LE.evt rsegs Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (zxb ch) (Z_to_bv 64 FA) a2 a3 (Z_to_bv 64 X2) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82284) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA id X2 ch cl HA0 HA HX2 RDl HFA H144 K.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f16_p284_F ExecF.RNG_all Q ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11
           t3 t4 t5 t6 Fr fc m A FA id X2 ch cl HA0 HA HX2 RDl HFA H144).
  - intros a4. apply ExecF_all.evt_evtF_all. apply K.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
Qed.

(* 0x82270 .. 0x82284: the instrumented check of the low byte's address and the high byte load. *)
Lemma f16_p270_F : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA X1 X2 : Z) (b2 ch : byte),
  0 <= X1 < 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (Z.shiftr X2 3 + ASAN_K)) 1 = Some [b2] ->
  (bv_signed b2 = 0 \/ X2 mod 8 < bv_signed b2) ->
  ov_read_bytes rsegs m (wa X1) 1 = Some [ch] ->
  (forall a5' a6' : word, ExecF.evtF rsegs RNG Q
     (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (zxb ch) (Z_to_bv 64 FA) a2 a3 (Z_to_bv 64 X2) a5' a6' a7
              s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82284) fc None m (seg_rom rsegs))) ->
  ExecF.rng RNG (Z.shiftr X2 3 + ASAN_K) 1 -> ExecF.rng RNG X1 1 ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3 (Z_to_bv 64 X2) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82270) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA X1 X2 b2 ch HX1 HX2 RS Hck RDh K GS2 GX1.
  (* 0x82270 srli a5,a4,3 ; 0x82274 add a5,a5,s10 ; 0x82278 lb a5,0(a5) ; 0x8227c lbu a0,0(a0) *)
  step. step. rewrite ?(unsigned_lit X2) by lia. step. step.
  (* 0x82280 bnez a5 *)
  step. rewrite f16_sxb_eqb0.
  destruct (Z.eqb_spec (bv_signed b2) 0) as [K0|K0].
  - cbn [negb]. cbv iota. apply K.
  - cbn [negb]. cbv iota.
    (* 0x829e4 andi a6,a4,7 ; 0x829e8 bge a6,a5 (not taken: X2 mod 8 < k) ; 0x829ec j 82284 *)
    step. step.
    rewrite (f16_bge_slow X2 b2) by (lia || (destruct Hck; lia)). cbn [negb]. cbv iota.
    step. apply K.
Qed.

Lemma f16_p270_of_F : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA X1 X2 : Z) (b2 ch : byte),
  0 <= X1 < 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (Z.shiftr X2 3 + ASAN_K)) 1 = Some [b2] ->
  (bv_signed b2 = 0 \/ X2 mod 8 < bv_signed b2) ->
  ov_read_bytes rsegs m (wa X1) 1 = Some [ch] ->
  (forall a5' a6' : word, LE.evt rsegs Q
     (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (zxb ch) (Z_to_bv 64 FA) a2 a3 (Z_to_bv 64 X2) a5' a6' a7
              s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82284) fc None m (seg_rom rsegs))) ->
  LE.evt rsegs Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3 (Z_to_bv 64 X2) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82270) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA X1 X2 b2 ch HX1 HX2 RS Hck RDh K.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f16_p270_F ExecF.RNG_all Q ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11
           t3 t4 t5 t6 Fr fc m A FA X1 X2 b2 ch HX1 HX2 RS Hck RDh).
  - intros a5' a6'. apply ExecF_all.evt_evtF_all. apply K.
  - apply f16_sh1_all; lia.
  - apply ExecF.rng_all; lia.
Qed.

(* 0x82250 .. 0x82270: the low byte's address, joined_byte (first, blk, 10). *)
Lemma f16_p250_F : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (ra0 sp gp tp t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA X1 n S6 P48 : Z),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 19 < 2 ^ 64 -> 0 <= P48 < 2 ^ 64 ->
  q64 m (A + 48) P48 ->
  (forall a5' : word, ExecF.evtF rsegs RNG Q
     (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3
              (Z_to_bv 64 (if 10 <? n then P48 else S6 + (19 - n))) a5' a6 a7
              s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82270) fc None m (seg_rom rsegs))) ->
  ExecF.rng RNG (A + 48) 8 ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82250) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra0 sp gp tp t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA X1 n S6 P48 HA0 HA Hn HS0 HS HP H48 K G48.
  pose proof (rd8 m (A + 48) P48 H48) as RD48.
  (* 0x82250 ld a4,48(s1) ; 0x82254 li a5,10 ; 0x82258 bltu a5,t0 *)
  step. step. step.
  replace (bv_ltu (Z_to_bv 64 10) (Z_to_bv 64 n)) with (10 <? n)
    by (symmetry; unfold bv_ltu; rewrite !unsigned_lit by lia; reflexivity).
  revert K. destruct (Z.ltb_spec 10 n) as [Hlt|Hge]; intros K; cbv iota in K |- *.
  - apply K.
  -
    (* 0x8225c li a4,19 ; subw a4,a4,t0 ; slli a4,a4,32 ; srli a4,a4,32 ; add a4,s6,a4 *)
    step. step. step. step. step.
    rewrite (f16_zsub S6 19 n) by lia.
    apply K.
Qed.

Lemma f16_p250_of_F : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA X1 n S6 P48 : Z),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 19 < 2 ^ 64 -> 0 <= P48 < 2 ^ 64 ->
  q64 m (A + 48) P48 ->
  (forall a5' : word, LE.evt rsegs Q
     (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3
              (Z_to_bv 64 (if 10 <? n then P48 else S6 + (19 - n))) a5' a6 a7
              s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82270) fc None m (seg_rom rsegs))) ->
  LE.evt rsegs Q
    (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82250) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA X1 n S6 P48 HA0 HA Hn HS0 HS HP H48 K.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f16_p250_F ExecF.RNG_all Q ra0 sp gp tp t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11
           t3 t4 t5 t6 Fr fc m A FA X1 n S6 P48 HA0 HA Hn HS0 HS HP H48).
  - intros a5'. apply ExecF_all.evt_evtF_all. apply K.
  - apply ExecF.rng_all; lia.
Qed.

(* 0x82238 .. 0x82250: the instrumented check of the high byte's address, with FA = [[A+256]]. *)
Lemma f16_p238_F : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA P256 X1 : Z) (b1 : byte),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= X1 < 2 ^ 64 -> 0 <= FA < 65536 -> 0 <= P256 < 2 ^ 64 ->
  q64 m (A + 256) P256 -> u16 m P256 FA ->
  ov_read_bytes rsegs m (wa (Z.shiftr X1 3 + ASAN_K)) 1 = Some [b1] ->
  (bv_signed b1 = 0 \/ X1 mod 8 < bv_signed b1) ->
  (forall a4' a5' : word, ExecF.evtF rsegs RNG Q
     (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3 a4' a5' a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82250) fc None m (seg_rom rsegs))) ->
  ExecF.rng RNG (Z.shiftr X1 3 + ASAN_K) 1 -> ExecF.rng RNG (A + 256) 8 -> ExecF.rng RNG P256 2 ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82238) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA P256 X1 b1 HA0 HA HX1 HFA HP H256 HU RS Hck K GS1 G256 GP.
  pose proof (rd8 m (A + 256) P256 H256) as RD256. pose proof (rd2 m P256 FA HU) as RDFA.
  (* 0x82238 srli a1,a0,3 ; 0x8223c add a1,a1,s10 ; 0x82240 lb a4,0(a1) ; 0x82244 ld a1,256(s1) ;
     0x82248 lhu a1,0(a1) *)
  step. step. rewrite ?(unsigned_lit X1) by lia. step. step. step.
  rewrite (zx16_lit FA) by lia.
  (* 0x8224c bnez a4 *)
  step. rewrite f16_sxb_eqb0.
  destruct (Z.eqb_spec (bv_signed b1) 0) as [K0|K0].
  - cbn [negb]. cbv iota. apply K.
  - cbn [negb]. cbv iota.
    (* 0x829d8 andi a5,a0,7 ; 0x829dc bge a5,a4 (not taken) ; 0x829e0 j 82250 *)
    step. step.
    rewrite (f16_bge_slow X1 b1) by (lia || (destruct Hck; lia)). cbn [negb]. cbv iota.
    step. apply K.
Qed.

Lemma f16_p238_of_F : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA P256 X1 : Z) (b1 : byte),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= X1 < 2 ^ 64 -> 0 <= FA < 65536 -> 0 <= P256 < 2 ^ 64 ->
  q64 m (A + 256) P256 -> u16 m P256 FA ->
  ov_read_bytes rsegs m (wa (Z.shiftr X1 3 + ASAN_K)) 1 = Some [b1] ->
  (bv_signed b1 = 0 \/ X1 mod 8 < bv_signed b1) ->
  (forall a4' a5' : word, LE.evt rsegs Q
     (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3 a4' a5' a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82250) fc None m (seg_rom rsegs))) ->
  LE.evt rsegs Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82238) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA P256 X1 b1 HA0 HA HX1 HFA HP H256 HU RS Hck K.
  pose proof HU as (U1 & U2 & _). unfold u16 in *. rewrite length_le2 in U2.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f16_p238_F ExecF.RNG_all Q ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11
           t3 t4 t5 t6 Fr fc m A FA P256 X1 b1 HA0 HA HX1 HFA HP H256 HU RS Hck).
  - intros a4' a5'. apply ExecF_all.evt_evtF_all. apply K.
  - apply f16_sh1_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
Qed.

(* 0x82210 .. 0x82238: have = [A+104] <> 0, and the high byte's address. *)
Lemma f16_p210_F : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (ra0 sp gp tp t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A vh n S6 P56 : Z),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 18 < 2 ^ 64 -> 0 <= P56 < 2 ^ 64 ->
  0 < vh < 2 ^ 64 ->
  q64 m (A + 104) vh -> q64 m (A + 56) P56 ->
  (forall a1' : word, ExecF.evtF rsegs RNG Q
     (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A)
              (Z_to_bv 64 (if 9 <? n then P56 else S6 + (18 - n))) a1' a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82238) fc None m (seg_rom rsegs))) ->
  ExecF.rng RNG (A + 104) 8 -> ExecF.rng RNG (A + 56) 8 ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82210) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra0 sp gp tp t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A vh n S6 P56 HA0 HA Hn HS0 HS HP Hvh H104 H56 K G104 G56.
  pose proof (rd8 m (A + 104) vh H104) as RD104. pose proof (rd8 m (A + 56) P56 H56) as RD56.
  (* 0x82210 ld a0,104(s1) ; 0x82214 beqz a0 (have <> 0: not taken) *)
  step. step.
  replace (bv_eqb (Z_to_bv 64 vh) (Z_to_bv 64 0)) with false
    by (symmetry; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  cbv iota.
  (* 0x82218 ld a0,56(s1) ; 0x8221c li a1,9 ; 0x82220 bltu a1,t0 *)
  step. step. step.
  replace (bv_ltu (Z_to_bv 64 9) (Z_to_bv 64 n)) with (9 <? n)
    by (symmetry; unfold bv_ltu; rewrite !unsigned_lit by lia; reflexivity).
  revert K. destruct (Z.ltb_spec 9 n) as [Hlt|Hge]; intros K; cbv iota in K |- *.
  - apply K.
  -
    (* 0x82224 li a0,18 ; subw a0,a0,t0 ; slli a0,a0,32 ; srli a0,a0,32 ; add a0,s6,a0 *)
    step. step. step. step. step.
    rewrite (f16_zsub S6 18 n) by lia.
    apply K.
Qed.

Lemma f16_p210_of_F : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A vh n S6 P56 : Z),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 18 < 2 ^ 64 -> 0 <= P56 < 2 ^ 64 ->
  0 < vh < 2 ^ 64 ->
  q64 m (A + 104) vh -> q64 m (A + 56) P56 ->
  (forall a1' : word, LE.evt rsegs Q
     (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A)
              (Z_to_bv 64 (if 9 <? n then P56 else S6 + (18 - n))) a1' a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82238) fc None m (seg_rom rsegs))) ->
  LE.evt rsegs Q
    (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82210) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A vh n S6 P56 HA0 HA Hn HS0 HS HP Hvh H104 H56 K.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f16_p210_F ExecF.RNG_all Q ra0 sp gp tp t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11
           t3 t4 t5 t6 Fr fc m A vh n S6 P56 HA0 HA Hn HS0 HS HP Hvh H104 H56).
  - intros a1'. apply ExecF_all.evt_evtF_all. apply K.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
Qed.

End T.

(* ---- f16_evt: the whole run 0x821d0 -> 0x8229c under a footprint RNG, with the ingest call entering through
   its footprint contract. ---- *)
Section E.
Context {fx : FPState}.

Lemma f16_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 : Z) (K : nat) (rec idb pb : list byte)
         (b1 b2 ch cl : byte),
    reac_identity_ingest_contract_F ->
    Z.of_nat K = pll + 5 -> (1 <= K <= 57)%nat ->
    0 <= fb -> fb mod 8 = 0 -> fb + 100 < 2 ^ 64 ->
    addressable m fb 72 -> bytes_at rsegs m fb rec -> length rec = 72%nat ->
    psum (skipn 15 rec) K mod 128 = 0 -> psum (skipn 15 rec) K < 2 ^ 64 ->
    q64 m (A + 104) vh -> 0 < vh < 2 ^ 64 ->
    q64 m (A + 56) P56 -> q64 m (A + 48) P48 -> 0 <= P56 < 2 ^ 64 -> 0 <= P48 < 2 ^ 64 ->
    0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 19 < 2 ^ 64 ->
    X1 = (if 9 <? n then P56 else S6 + (18 - n)) -> X2 = (if 10 <? n then P48 else S6 + (19 - n)) ->
    0 <= X1 < 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr X1 3 + ASAN_K)) 1 = Some [b1] ->
    (bv_signed b1 = 0 \/ X1 mod 8 < bv_signed b1) ->
    ov_read_bytes rsegs m (wa (Z.shiftr X2 3 + ASAN_K)) 1 = Some [b2] ->
    (bv_signed b2 = 0 \/ X2 mod 8 < bv_signed b2) ->
    ov_read_bytes rsegs m (wa X1) 1 = Some [ch] -> ov_read_bytes rsegs m (wa X2) 1 = Some [cl] ->
    FA = 256 * bv_unsigned ch + bv_unsigned cl -> 0 <= FA < 65536 ->
    q64 m (A + 256) P256 -> u16 m P256 FA -> 0 <= P256 < 2 ^ 64 -> q64 m (A + 144) id ->
    0 <= A -> A + 416 <= 2 ^ 64 ->
    0 <= id < 2 ^ 64 -> 0 <= pll < 2 ^ 64 -> id <> 0 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    length pb = Z.to_nat pll ->
    (0 < pll -> fb + 19 <> 0 -> bytes_at rsegs m (fb + 19) pb) ->
    (id <> 0 -> 0 < pll -> fb + 19 <> 0 -> (fb + 19) + pll <= id \/ id + 38 <= fb + 19) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INGEST_FRAME <= bv_unsigned sp ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= id) ->
    (0 < pll -> fb + 19 <> 0 ->
       (fb + 19) + pll <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= fb + 19) ->
    asan_cells m -> shadow_rw m ->
    (id <> 0 -> addressable m id 38) ->
    (0 < pll -> fb + 19 <> 0 -> addressable m (fb + 19) pll) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_identity_ingest_W (bv_unsigned sp) id) x) ->
    (* the segment's own accesses: the loop's record bytes and their shadow cover, then the tail's loads *)
    ExecF.rng RNG (fb + 15) (Z.of_nat K) ->
    ExecF.rng RNG (Z.shiftr (fb + 15) 3 + ASAN_K)
      (Z.shiftr (fb + 15 + Z.of_nat K - 1) 3 - Z.shiftr (fb + 15) 3 + 1) ->
    ExecF.rng RNG (A + 104) 8 -> ExecF.rng RNG (A + 56) 8 ->
    ExecF.rng RNG (Z.shiftr X1 3 + ASAN_K) 1 -> ExecF.rng RNG (A + 256) 8 -> ExecF.rng RNG P256 2 ->
    ExecF.rng RNG (A + 48) 8 ->
    ExecF.rng RNG (Z.shiftr X2 3 + ASAN_K) 1 -> ExecF.rng RNG X1 1 -> ExecF.rng RNG X2 1 ->
    ExecF.rng RNG (A + 144) 8 ->
    (* the callee's regions (reac_identity_ingest_contract_F's rng premises), unchanged *)
    ExecF.rng RNG (bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME) REAC_IDENTITY_INGEST_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (id <> 0 -> ExecF.rng RNG id 38 /\ ExecF.rng RNG (id / 8 + ASAN_K) ((id + 37) / 8 - id / 8 + 1)) ->
    (0 < pll -> fb + 19 <> 0 ->
       ExecF.rng RNG (fb + 19) pll /\
       ExecF.rng RNG ((fb + 19) / 8 + ASAN_K) ((fb + 19 + pll - 1) / 8 - (fb + 19) / 8 + 1)) ->
    ExecF.evtF rsegs RNG
      (reac_identity_ingest_post (Z_to_bv 64 0x8229c) sp gp tp s0 (Z_to_bv 64 A) s2 s3 s4 s5 (Z_to_bv 64 S6)
         s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 Fr fc m lo id FA (fb + 19) pll idb pb)
      (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (fb + 15)) (Z_to_bv 64 0)
               (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) (Z_to_bv 64 (Z.of_nat K)) (Z_to_bv 64 (fb + 15)) a6 a7
               s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 K rec idb pb b1 b2 ch cl
    HING HK HKb Hfb0 Hfb8 Hfbb ADr BAr Lr Hsum Hsumb
    H104 Hvh H56 H48 HP56 HP48 Hn HS0 HS19 EX1 EX2 HX1 HX2 RS1 Hck1 RS2 Hck2 RDh RDl HFAe HFAb
    H256 HU HP256b H144 HA0 HAb Hidb Hpllb Hidnz
    Hidcells Lpb Hpb Hdjp Hstk Hlo Hdji Hdjps HAC HSW Hadi Hadp Hout
    Gbs Gsh G104 G56 GS1 G256 GP256 G48 GS2 GX1 GX2 G144 Gstk Ggot Gcell Gid Gpb.
  (* ---- the loop 0x821d0 .. 0x821f4, from turn 0 ---- *)
  replace (Z_to_bv 64 (fb + 15)) with (Z_to_bv 64 ((fb + 15) + Z.of_nat 0)) by (f_equal; lia).
  replace (Z_to_bv 64 0) with (Z_to_bv 64 (psum (skipn 15 rec) 0)) by reflexivity.
  eapply ExecF.evtF_cut.
  { apply (f16_loop_F RNG K 0 ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (fb + 19))
             (Z_to_bv 64 pll) a6 a7 s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
             (fb + 15) (skipn 15 rec)).
    - lia.
    - lia.
    - lia.
    - intros q Hq.
      pose proof (bytes_at_read rsegs m fb rec (15 + Z.of_nat q) 1 BAr ltac:(lia) ltac:(rewrite Lr; lia)) as RD.
      replace (fb + 15 + Z.of_nat q) with (fb + (15 + Z.of_nat q)) by lia.
      rewrite RD. f_equal. rewrite nth_sk.
      replace (Z.to_nat (15 + Z.of_nat q)) with (15 + q)%nat by lia.
      apply firstn1_skipn. rewrite Lr. lia.
    - intros q Hq. replace (fb + 15 + Z.of_nat q) with (fb + (15 + Z.of_nat q)) by lia.
      apply shadow0_72; [exact ADr | exact Hfb8 | lia].
    - replace (0 + K)%nat with K by lia. exact Gbs.
    - replace (0 + K)%nat with K by lia. exact Gsh. }
  intros ms1 (a6x & ->).
  (* ---- at 0x82208: andi a0,a1,127 ; bnez a0,82bf4 (not taken: the sum closes) ---- *)
  replace (0 + K)%nat with K by lia.
  step.
  pose proof (psum_nonneg (skipn 15 rec) K) as Hpn.
  rewrite (unsigned_lit (psum (skipn 15 rec) K)) by lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
  rewrite Hsum.
  step. if_false.
  (* ---- 0x82210 .. 0x82298: the v1.9 tail ---- *)
  apply (f16_p210_F RNG _ ra0 sp gp tp t1 t2 s0 _ _ (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) _ _ a6x a7
           s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A vh n S6 P56 HA0 HAb Hn HS0 ltac:(lia) HP56 Hvh
           H104 H56); [| exact G104 | exact G56].
  intros x1. rewrite <- EX1.
  apply (f16_p238_F RNG _ ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 x1 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) _ _
           a6x a7 s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA P256 X1 b1
           HA0 HAb HX1 HFAb HP256b H256 HU RS1 Hck1); [| exact GS1 | exact G256 | exact GP256].
  intros x4 x5.
  apply (f16_p250_F RNG _ ra0 sp gp tp t1 t2 s0 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) x4 x5 a6x a7
           s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA X1 n S6 P48 HA0 HAb Hn HS0 HS19 HP48 H48);
    [| exact G48].
  intros y5. rewrite <- EX2.
  apply (f16_p270_F RNG _ ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) y5 a6x a7
           s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA X1 X2 b2 ch HX1 HX2 RS2 Hck2 RDh);
    [| exact GS2 | exact GX1].
  intros z5 z6.
  apply (f16_p284_F RNG _ ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) z5 z6 a7
           s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA id X2 ch cl HA0 HAb HX2 RDl HFAe
           H144); [| exact GX2 | exact G144].
  intros w4.
  (* 0x82298 jal reac_identity_ingest *)
  step.
  unfold reac_identity_ingest_contract_F in HING.
  eapply HING; try reflexivity; try assumption; try lia.
Qed.

Lemma f16_evt_of_F :
  forall (ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 : Z) (K : nat) (rec idb pb : list byte)
         (b1 b2 ch cl : byte),
    reac_identity_ingest_contract_F ->
    Z.of_nat K = pll + 5 -> (1 <= K <= 57)%nat ->
    0 <= fb -> fb mod 8 = 0 -> fb + 100 < 2 ^ 64 ->
    addressable m fb 72 -> bytes_at rsegs m fb rec -> length rec = 72%nat ->
    psum (skipn 15 rec) K mod 128 = 0 -> psum (skipn 15 rec) K < 2 ^ 64 ->
    q64 m (A + 104) vh -> 0 < vh < 2 ^ 64 ->
    q64 m (A + 56) P56 -> q64 m (A + 48) P48 -> 0 <= P56 < 2 ^ 64 -> 0 <= P48 < 2 ^ 64 ->
    0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 19 < 2 ^ 64 ->
    X1 = (if 9 <? n then P56 else S6 + (18 - n)) -> X2 = (if 10 <? n then P48 else S6 + (19 - n)) ->
    0 <= X1 < 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr X1 3 + ASAN_K)) 1 = Some [b1] ->
    (bv_signed b1 = 0 \/ X1 mod 8 < bv_signed b1) ->
    ov_read_bytes rsegs m (wa (Z.shiftr X2 3 + ASAN_K)) 1 = Some [b2] ->
    (bv_signed b2 = 0 \/ X2 mod 8 < bv_signed b2) ->
    ov_read_bytes rsegs m (wa X1) 1 = Some [ch] -> ov_read_bytes rsegs m (wa X2) 1 = Some [cl] ->
    FA = 256 * bv_unsigned ch + bv_unsigned cl -> 0 <= FA < 65536 ->
    q64 m (A + 256) P256 -> u16 m P256 FA -> 0 <= P256 < 2 ^ 64 -> q64 m (A + 144) id ->
    0 <= A -> A + 416 <= 2 ^ 64 ->
    0 <= id < 2 ^ 64 -> 0 <= pll < 2 ^ 64 -> id <> 0 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    length pb = Z.to_nat pll ->
    (0 < pll -> fb + 19 <> 0 -> bytes_at rsegs m (fb + 19) pb) ->
    (id <> 0 -> 0 < pll -> fb + 19 <> 0 -> (fb + 19) + pll <= id \/ id + 38 <= fb + 19) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INGEST_FRAME <= bv_unsigned sp ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= id) ->
    (0 < pll -> fb + 19 <> 0 ->
       (fb + 19) + pll <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= fb + 19) ->
    asan_cells m -> shadow_rw m ->
    (id <> 0 -> addressable m id 38) ->
    (0 < pll -> fb + 19 <> 0 -> addressable m (fb + 19) pll) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_identity_ingest_W (bv_unsigned sp) id) x) ->
    LE.evt rsegs
      (reac_identity_ingest_post (Z_to_bv 64 0x8229c) sp gp tp s0 (Z_to_bv 64 A) s2 s3 s4 s5 (Z_to_bv 64 S6)
         s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 Fr fc m lo id FA (fb + 19) pll idb pb)
      (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (fb + 15)) (Z_to_bv 64 0)
               (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) (Z_to_bv 64 (Z.of_nat K)) (Z_to_bv 64 (fb + 15)) a6 a7
               s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 K rec idb pb b1 b2 ch cl
    HING HK HKb Hfb0 Hfb8 Hfbb ADr BAr Lr Hsum Hsumb
    H104 Hvh H56 H48 HP56 HP48 Hn HS0 HS19 EX1 EX2 HX1 HX2 RS1 Hck1 RS2 Hck2 RDh RDl HFAe HFAb
    H256 HU HP256b H144 HA0 HAb Hidb Hpllb Hidnz
    Hidcells Lpb Hpb Hdjp Hstk Hlo Hdji Hdjps HAC HSW Hadi Hadp Hout.
  pose proof HU as (U1 & U2 & _). unfold u16 in *. rewrite length_le2 in U2.
  pose proof Hstk as (SK1 & SK2 & _).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f16_evt_F ExecF.RNG_all ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
           A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 K rec idb pb b1 b2 ch cl
           HING HK HKb Hfb0 Hfb8 Hfbb ADr BAr Lr Hsum Hsumb
           H104 Hvh H56 H48 HP56 HP48 Hn HS0 HS19 EX1 EX2 HX1 HX2 RS1 Hck1 RS2 Hck2 RDh RDl HFAe HFAb
           H256 HU HP256b H144 HA0 HAb Hidb Hpllb Hidnz
           Hidcells Lpb Hpb Hdjp Hstk Hlo Hdji Hdjps HAC HSW Hadi Hadp Hout).
  - apply ExecF.rng_all; lia.
  - apply f16_sh_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply f16_sh1_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply f16_sh1_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold REAC_IDENTITY_INGEST_FRAME in *; lia.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - intros I0. destruct (Hadi I0) as (A0 & A1 & A2 & _). unfold APPMEM_END in A2.
    split; [apply ExecF.rng_all; lia|].
    apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
  - intros H1 H2. destruct (Hadp H1 H2) as (A0 & A1 & A2 & _). unfold APPMEM_END in A2.
    split; [apply ExecF.rng_all; lia|].
    apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* ---- Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery)): the _on twins.  f16_evt_F and
   f16_evt_of_F take a callee contract, so they stay as they are, with their own proofs; the twins are new.  The
   callee enters through reac_identity_ingest_contract_F_on (reac_identity_ingest_c.v, a Theorem Labs lane 28e24b8fe6c; proof
   of record a Theorem Labs lane's reac_identity_ingest_F_holds_on), which has no shadow_rw premise.  F16's own run reads
   and stores no shadow byte through `shadow_rw m`: the loop's shadow loads come from `addressable m fb 72`
   (shadow0_72), the tail's two shadow checks from the explicit ov_read_bytes premises, and the proof above uses
   HSW only to close the ingest call's premise.  So the premise is DROPPED; nothing else changes. *)
Lemma f16_evt_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 : Z) (K : nat) (rec idb pb : list byte)
         (b1 b2 ch cl : byte),
    reac_identity_ingest_contract_F_on ->
    Z.of_nat K = pll + 5 -> (1 <= K <= 57)%nat ->
    0 <= fb -> fb mod 8 = 0 -> fb + 100 < 2 ^ 64 ->
    addressable m fb 72 -> bytes_at rsegs m fb rec -> length rec = 72%nat ->
    psum (skipn 15 rec) K mod 128 = 0 -> psum (skipn 15 rec) K < 2 ^ 64 ->
    q64 m (A + 104) vh -> 0 < vh < 2 ^ 64 ->
    q64 m (A + 56) P56 -> q64 m (A + 48) P48 -> 0 <= P56 < 2 ^ 64 -> 0 <= P48 < 2 ^ 64 ->
    0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 19 < 2 ^ 64 ->
    X1 = (if 9 <? n then P56 else S6 + (18 - n)) -> X2 = (if 10 <? n then P48 else S6 + (19 - n)) ->
    0 <= X1 < 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr X1 3 + ASAN_K)) 1 = Some [b1] ->
    (bv_signed b1 = 0 \/ X1 mod 8 < bv_signed b1) ->
    ov_read_bytes rsegs m (wa (Z.shiftr X2 3 + ASAN_K)) 1 = Some [b2] ->
    (bv_signed b2 = 0 \/ X2 mod 8 < bv_signed b2) ->
    ov_read_bytes rsegs m (wa X1) 1 = Some [ch] -> ov_read_bytes rsegs m (wa X2) 1 = Some [cl] ->
    FA = 256 * bv_unsigned ch + bv_unsigned cl -> 0 <= FA < 65536 ->
    q64 m (A + 256) P256 -> u16 m P256 FA -> 0 <= P256 < 2 ^ 64 -> q64 m (A + 144) id ->
    0 <= A -> A + 416 <= 2 ^ 64 ->
    0 <= id < 2 ^ 64 -> 0 <= pll < 2 ^ 64 -> id <> 0 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    length pb = Z.to_nat pll ->
    (0 < pll -> fb + 19 <> 0 -> bytes_at rsegs m (fb + 19) pb) ->
    (id <> 0 -> 0 < pll -> fb + 19 <> 0 -> (fb + 19) + pll <= id \/ id + 38 <= fb + 19) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INGEST_FRAME <= bv_unsigned sp ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= id) ->
    (0 < pll -> fb + 19 <> 0 ->
       (fb + 19) + pll <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= fb + 19) ->
    asan_cells m ->
    (id <> 0 -> addressable m id 38) ->
    (0 < pll -> fb + 19 <> 0 -> addressable m (fb + 19) pll) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_identity_ingest_W (bv_unsigned sp) id) x) ->
    (* the segment's own accesses: the loop's record bytes and their shadow cover, then the tail's loads *)
    ExecF.rng RNG (fb + 15) (Z.of_nat K) ->
    ExecF.rng RNG (Z.shiftr (fb + 15) 3 + ASAN_K)
      (Z.shiftr (fb + 15 + Z.of_nat K - 1) 3 - Z.shiftr (fb + 15) 3 + 1) ->
    ExecF.rng RNG (A + 104) 8 -> ExecF.rng RNG (A + 56) 8 ->
    ExecF.rng RNG (Z.shiftr X1 3 + ASAN_K) 1 -> ExecF.rng RNG (A + 256) 8 -> ExecF.rng RNG P256 2 ->
    ExecF.rng RNG (A + 48) 8 ->
    ExecF.rng RNG (Z.shiftr X2 3 + ASAN_K) 1 -> ExecF.rng RNG X1 1 -> ExecF.rng RNG X2 1 ->
    ExecF.rng RNG (A + 144) 8 ->
    (* the callee's regions (reac_identity_ingest_contract_F_on's rng premises), unchanged *)
    ExecF.rng RNG (bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME) REAC_IDENTITY_INGEST_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (id <> 0 -> ExecF.rng RNG id 38 /\ ExecF.rng RNG (id / 8 + ASAN_K) ((id + 37) / 8 - id / 8 + 1)) ->
    (0 < pll -> fb + 19 <> 0 ->
       ExecF.rng RNG (fb + 19) pll /\
       ExecF.rng RNG ((fb + 19) / 8 + ASAN_K) ((fb + 19 + pll - 1) / 8 - (fb + 19) / 8 + 1)) ->
    ExecF.evtF rsegs RNG
      (reac_identity_ingest_post (Z_to_bv 64 0x8229c) sp gp tp s0 (Z_to_bv 64 A) s2 s3 s4 s5 (Z_to_bv 64 S6)
         s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 Fr fc m lo id FA (fb + 19) pll idb pb)
      (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (fb + 15)) (Z_to_bv 64 0)
               (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) (Z_to_bv 64 (Z.of_nat K)) (Z_to_bv 64 (fb + 15)) a6 a7
               s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 K rec idb pb b1 b2 ch cl
    HING HK HKb Hfb0 Hfb8 Hfbb ADr BAr Lr Hsum Hsumb
    H104 Hvh H56 H48 HP56 HP48 Hn HS0 HS19 EX1 EX2 HX1 HX2 RS1 Hck1 RS2 Hck2 RDh RDl HFAe HFAb
    H256 HU HP256b H144 HA0 HAb Hidb Hpllb Hidnz
    Hidcells Lpb Hpb Hdjp Hstk Hlo Hdji Hdjps HAC Hadi Hadp Hout
    Gbs Gsh G104 G56 GS1 G256 GP256 G48 GS2 GX1 GX2 G144 Gstk Ggot Gcell Gid Gpb.
  (* ---- the loop 0x821d0 .. 0x821f4, from turn 0 ---- *)
  replace (Z_to_bv 64 (fb + 15)) with (Z_to_bv 64 ((fb + 15) + Z.of_nat 0)) by (f_equal; lia).
  replace (Z_to_bv 64 0) with (Z_to_bv 64 (psum (skipn 15 rec) 0)) by reflexivity.
  eapply ExecF.evtF_cut.
  { apply (f16_loop_F RNG K 0 ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (fb + 19))
             (Z_to_bv 64 pll) a6 a7 s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
             (fb + 15) (skipn 15 rec)).
    - lia.
    - lia.
    - lia.
    - intros q Hq.
      pose proof (bytes_at_read rsegs m fb rec (15 + Z.of_nat q) 1 BAr ltac:(lia) ltac:(rewrite Lr; lia)) as RD.
      replace (fb + 15 + Z.of_nat q) with (fb + (15 + Z.of_nat q)) by lia.
      rewrite RD. f_equal. rewrite nth_sk.
      replace (Z.to_nat (15 + Z.of_nat q)) with (15 + q)%nat by lia.
      apply firstn1_skipn. rewrite Lr. lia.
    - intros q Hq. replace (fb + 15 + Z.of_nat q) with (fb + (15 + Z.of_nat q)) by lia.
      apply shadow0_72; [exact ADr | exact Hfb8 | lia].
    - replace (0 + K)%nat with K by lia. exact Gbs.
    - replace (0 + K)%nat with K by lia. exact Gsh. }
  intros ms1 (a6x & ->).
  (* ---- at 0x82208: andi a0,a1,127 ; bnez a0,82bf4 (not taken: the sum closes) ---- *)
  replace (0 + K)%nat with K by lia.
  step.
  pose proof (psum_nonneg (skipn 15 rec) K) as Hpn.
  rewrite (unsigned_lit (psum (skipn 15 rec) K)) by lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
  rewrite Hsum.
  step. if_false.
  (* ---- 0x82210 .. 0x82298: the v1.9 tail ---- *)
  apply (f16_p210_F RNG _ ra0 sp gp tp t1 t2 s0 _ _ (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) _ _ a6x a7
           s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A vh n S6 P56 HA0 HAb Hn HS0 ltac:(lia) HP56 Hvh
           H104 H56); [| exact G104 | exact G56].
  intros x1. rewrite <- EX1.
  apply (f16_p238_F RNG _ ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 x1 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) _ _
           a6x a7 s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA P256 X1 b1
           HA0 HAb HX1 HFAb HP256b H256 HU RS1 Hck1); [| exact GS1 | exact G256 | exact GP256].
  intros x4 x5.
  apply (f16_p250_F RNG _ ra0 sp gp tp t1 t2 s0 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) x4 x5 a6x a7
           s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA X1 n S6 P48 HA0 HAb Hn HS0 HS19 HP48 H48);
    [| exact G48].
  intros y5. rewrite <- EX2.
  apply (f16_p270_F RNG _ ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) y5 a6x a7
           s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA X1 X2 b2 ch HX1 HX2 RS2 Hck2 RDh);
    [| exact GS2 | exact GX1].
  intros z5 z6.
  apply (f16_p284_F RNG _ ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) z5 z6 a7
           s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA id X2 ch cl HA0 HAb HX2 RDl HFAe
           H144); [| exact GX2 | exact G144].
  intros w4.
  (* 0x82298 jal reac_identity_ingest *)
  step.
  unfold reac_identity_ingest_contract_F_on in HING.
  eapply HING; try reflexivity; try assumption; try lia.
Qed.

(* f16_evt_of_F's twin: the run at ExecF.RNG_all, read back as LE.evt, with the same callee and no shadow_rw. *)
Lemma f16_evt_of_F_on :
  forall (ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 : Z) (K : nat) (rec idb pb : list byte)
         (b1 b2 ch cl : byte),
    reac_identity_ingest_contract_F_on ->
    Z.of_nat K = pll + 5 -> (1 <= K <= 57)%nat ->
    0 <= fb -> fb mod 8 = 0 -> fb + 100 < 2 ^ 64 ->
    addressable m fb 72 -> bytes_at rsegs m fb rec -> length rec = 72%nat ->
    psum (skipn 15 rec) K mod 128 = 0 -> psum (skipn 15 rec) K < 2 ^ 64 ->
    q64 m (A + 104) vh -> 0 < vh < 2 ^ 64 ->
    q64 m (A + 56) P56 -> q64 m (A + 48) P48 -> 0 <= P56 < 2 ^ 64 -> 0 <= P48 < 2 ^ 64 ->
    0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 19 < 2 ^ 64 ->
    X1 = (if 9 <? n then P56 else S6 + (18 - n)) -> X2 = (if 10 <? n then P48 else S6 + (19 - n)) ->
    0 <= X1 < 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr X1 3 + ASAN_K)) 1 = Some [b1] ->
    (bv_signed b1 = 0 \/ X1 mod 8 < bv_signed b1) ->
    ov_read_bytes rsegs m (wa (Z.shiftr X2 3 + ASAN_K)) 1 = Some [b2] ->
    (bv_signed b2 = 0 \/ X2 mod 8 < bv_signed b2) ->
    ov_read_bytes rsegs m (wa X1) 1 = Some [ch] -> ov_read_bytes rsegs m (wa X2) 1 = Some [cl] ->
    FA = 256 * bv_unsigned ch + bv_unsigned cl -> 0 <= FA < 65536 ->
    q64 m (A + 256) P256 -> u16 m P256 FA -> 0 <= P256 < 2 ^ 64 -> q64 m (A + 144) id ->
    0 <= A -> A + 416 <= 2 ^ 64 ->
    0 <= id < 2 ^ 64 -> 0 <= pll < 2 ^ 64 -> id <> 0 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    length pb = Z.to_nat pll ->
    (0 < pll -> fb + 19 <> 0 -> bytes_at rsegs m (fb + 19) pb) ->
    (id <> 0 -> 0 < pll -> fb + 19 <> 0 -> (fb + 19) + pll <= id \/ id + 38 <= fb + 19) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INGEST_FRAME <= bv_unsigned sp ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= id) ->
    (0 < pll -> fb + 19 <> 0 ->
       (fb + 19) + pll <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= fb + 19) ->
    asan_cells m ->
    (id <> 0 -> addressable m id 38) ->
    (0 < pll -> fb + 19 <> 0 -> addressable m (fb + 19) pll) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_identity_ingest_W (bv_unsigned sp) id) x) ->
    LE.evt rsegs
      (reac_identity_ingest_post (Z_to_bv 64 0x8229c) sp gp tp s0 (Z_to_bv 64 A) s2 s3 s4 s5 (Z_to_bv 64 S6)
         s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 Fr fc m lo id FA (fb + 19) pll idb pb)
      (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (fb + 15)) (Z_to_bv 64 0)
               (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) (Z_to_bv 64 (Z.of_nat K)) (Z_to_bv 64 (fb + 15)) a6 a7
               s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 K rec idb pb b1 b2 ch cl
    HING HK HKb Hfb0 Hfb8 Hfbb ADr BAr Lr Hsum Hsumb
    H104 Hvh H56 H48 HP56 HP48 Hn HS0 HS19 EX1 EX2 HX1 HX2 RS1 Hck1 RS2 Hck2 RDh RDl HFAe HFAb
    H256 HU HP256b H144 HA0 HAb Hidb Hpllb Hidnz
    Hidcells Lpb Hpb Hdjp Hstk Hlo Hdji Hdjps HAC Hadi Hadp Hout.
  pose proof HU as (U1 & U2 & _). unfold u16 in *. rewrite length_le2 in U2.
  pose proof Hstk as (SK1 & SK2 & _).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f16_evt_F_on ExecF.RNG_all ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
           A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 K rec idb pb b1 b2 ch cl
           HING HK HKb Hfb0 Hfb8 Hfbb ADr BAr Lr Hsum Hsumb
           H104 Hvh H56 H48 HP56 HP48 Hn HS0 HS19 EX1 EX2 HX1 HX2 RS1 Hck1 RS2 Hck2 RDh RDl HFAe HFAb
           H256 HU HP256b H144 HA0 HAb Hidb Hpllb Hidnz
           Hidcells Lpb Hpb Hdjp Hstk Hlo Hdji Hdjps HAC Hadi Hadp Hout).
  - apply ExecF.rng_all; lia.
  - apply f16_sh_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply f16_sh1_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply f16_sh1_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold REAC_IDENTITY_INGEST_FRAME in *; lia.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - intros I0. destruct (Hadi I0) as (A0 & A1 & A2 & _). unfold APPMEM_END in A2.
    split; [apply ExecF.rng_all; lia|].
    apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
  - intros H1 H2. destruct (Hadp H1 H2) as (A0 & A1 & A2 & _). unfold APPMEM_END in A2.
    split; [apply ExecF.rng_all; lia|].
    apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
Qed.

End E.

(* ---- The pins: each *_of_F states F16's v1.9 text, term for term. f16_evt_of_F differs from F16.f16_evt only
   in the callee-contract premise, which names the _F contract in place of the plain one. ---- *)
Example f16_loop_of_F_verbatim : True.
Proof.
  let a := type of (@F16.f16_loop) in let b := type of (@f16_loop_of_F) in constr_eq a b.
  exact I.
Qed.

Example f16_p284_of_F_verbatim : True.
Proof.
  let a := type of (@F16.f16_p284) in let b := type of (@f16_p284_of_F) in constr_eq a b.
  exact I.
Qed.

Example f16_p270_of_F_verbatim : True.
Proof.
  let a := type of (@F16.f16_p270) in let b := type of (@f16_p270_of_F) in constr_eq a b.
  exact I.
Qed.

Example f16_p250_of_F_verbatim : True.
Proof.
  let a := type of (@F16.f16_p250) in let b := type of (@f16_p250_of_F) in constr_eq a b.
  exact I.
Qed.

Example f16_p238_of_F_verbatim : True.
Proof.
  let a := type of (@F16.f16_p238) in let b := type of (@f16_p238_of_F) in constr_eq a b.
  exact I.
Qed.

Example f16_p210_of_F_verbatim : True.
Proof.
  let a := type of (@F16.f16_p210) in let b := type of (@f16_p210_of_F) in constr_eq a b.
  exact I.
Qed.

Example f16_evt_of_F_verbatim : True.
Proof.
  assert (pin : forall (ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
                       (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
                       (A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 : Z) (K : nat) (rec idb pb : list byte)
                       (b1 b2 ch cl : byte), True).
  { intros ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
      A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 K rec idb pb b1 b2 ch cl.
    lazymatch type of (F16.f16_evt ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
                         A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 K rec idb pb b1 b2 ch cl) with
    | ?P -> ?X =>
      lazymatch type of (f16_evt_of_F ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
                           A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 K rec idb pb b1 b2 ch cl) with
      | ?Q -> ?Y =>
        constr_eq P reac_identity_ingest_contract;
        constr_eq Q reac_identity_ingest_contract_F;
        constr_eq X Y
      end
    end.
    exact I. }
  exact I.
Qed.
