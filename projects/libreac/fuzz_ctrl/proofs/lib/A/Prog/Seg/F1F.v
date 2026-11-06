(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module paths, module names and numbers changed; 1340 of its 1484 lines of code are new or changed and 1653 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F1.v; 169 of its 321 lines of code are new or changed and 1332 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F1.v 0f7557862644 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F1.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F1.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint twins of F1.v's four run lemmas (f1_chk0 :185, f1_chk1 :217, f1_tail :250, f1_evt :284 of the
   source blob): the same runs, the same scripts, re-stepped with lib.Lib StepF as ExecF.evtF under a universally
   quantified footprint RNG. The two continuation (CPS) lemmas take their continuation as an evtF under the same
   RNG; their _of_F corollaries map the old evt continuation back with ExecF_all.evt_evtF_all (RNG_all).
   Regions, from the lemmas' own premises only:
     f1_chk0 / f1_chk1 : the one instrumented shadow byte (q >> 3) + ASAN_K that the lemma's ov_read_bytes premise
       names (1 byte);
     f1_tail           : the 8-byte spill [A + 224, A + 232) that the lemma's store_ok premise names;
     f1_evt            : both shadow bytes, the two input bytes at q and q + 1 that its ov_read_bytes premises name,
       and the spill [A + 224, A + 232).
   F1.v is unchanged apart from comment text. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_cls.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F1.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF_all.
Import ListNotations.
(* Restore YK11.getr / rsegs / seg_rom as F1.v has them. *)
Import YK11.
Open Scope Z_scope.

Module EFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF_all.

(* The appended rng premises at RNG_all: every region of this file is an address in [0, 2 ^ 64). *)
Ltac f1_rng_all :=
  apply ExecF.rng_all; rewrite ?Z.shiftr_div_pow2 by lia; unfold ASAN_K in *; Z.div_mod_to_equations; lia.

(* ---- 0x81d40-0x81d4c with the out-of-line piece 0x82978-0x82980: the check of the byte at s6 passes. ---- *)
Lemma f1_chk0_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (q : Z) (k : byte),
    s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 ASAN_K -> 0 <= q < 2 ^ 63 ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k] ->
    (bv_signed k = 0 \/ q mod 8 < bv_signed k) ->
    (forall a0' a1' : word, ExecF.evtF rsegs RNG Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x81d50) fc None m (seg_rom rsegs))) ->
    ExecF.rng RNG (Z.shiftr q 3 + ASAN_K) 1 ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d40) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q q k -> -> Hq HK Hk HC RSH.
  assert (HK' : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 q) ≫ 3 + ASAN_K)) 1 = Some [k])
    by (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia; exact HK).
  (* the same region as RSH, in the address form the code computes it *)
  assert (RSH' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 q) ≫ 3 + ASAN_K) 1)
    by (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia; exact RSH).
  clear HK.
  step. step. step. step.
  destruct (Z.eq_dec (bv_signed k) 0) as [E0|E0].
  - rewrite (byte_s0 k E0).
    if_false_by (eq_refl : negb (bv_eqb (sxb (Z_to_bv 8 0)) (Z_to_bv 64 0)) = false).
    exact (HC _ _).
  - if_true_by (f1_sxb_nz k E0).
    step. step.
    destruct Hk as [Hk|Hk]; [contradiction|].
    if_false_by (f1_bge_ok q k Hq Hk).
    step.
    exact (HC _ _).
Qed.

(* ---- 0x81d6c-0x81d78 with the out-of-line piece 0x82990-0x82998: the check of the byte at s4 passes. ---- *)
Lemma f1_chk1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (q : Z) (k : byte),
    s4 = Z_to_bv 64 q -> s10 = Z_to_bv 64 ASAN_K -> 0 <= q < 2 ^ 63 ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k] ->
    (bv_signed k = 0 \/ q mod 8 < bv_signed k) ->
    (forall a1' a2' : word, ExecF.evtF rsegs RNG Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x81d7c) fc None m (seg_rom rsegs))) ->
    ExecF.rng RNG (Z.shiftr q 3 + ASAN_K) 1 ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d6c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q q k -> -> Hq HK Hk HC RSH.
  assert (HK' : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 q) ≫ 3 + ASAN_K)) 1 = Some [k])
    by (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia; exact HK).
  assert (RSH' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 q) ≫ 3 + ASAN_K) 1)
    by (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia; exact RSH).
  clear HK.
  step. step. step. step.
  destruct (Z.eq_dec (bv_signed k) 0) as [E0|E0].
  - rewrite (byte_s0 k E0).
    if_false_by (eq_refl : negb (bv_eqb (sxb (Z_to_bv 8 0)) (Z_to_bv 64 0)) = false).
    exact (HC _ _).
  - if_true_by (f1_sxb_nz k E0).
    step. step.
    destruct Hk as [Hk|Hk]; [contradiction|].
    if_false_by (f1_bge_ok q k Hq Hk).
    step.
    exact (HC _ _).
Qed.

(* ---- 0x81d8c .. jal 0x5337c: the only write of the segment is the 8 bytes at s1 + 224. ---- *)
Lemma f1_tail_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A lo hi rest : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 lo -> a1 = Z_to_bv 64 hi -> s9 = Z_to_bv 64 rest ->
    0 <= A -> A + 232 <= 2 ^ 64 -> 0 <= lo < 2 ^ 64 -> 0 <= hi < 2 ^ 64 -> 0 <= Z.lor hi lo < 2 ^ 64 ->
    0 <= rest < 2 ^ 64 ->
    store_ok rsegs m (wa (A + 224)) 8 = true ->
    ExecF.rng RNG (A + 224) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81da4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.min (Z.lor hi lo) rest))
                          a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.min (Z.lor hi lo) rest)) s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6)
                    F (Z_to_bv 64 0x5337c) fc None (write_to_mem m (wa (A + 224)) (le8 (Z_to_bv 64 rest)))
                    (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d8c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A lo hi rest -> -> -> -> HA0 HA1 Hlo Hhi HL Hrest HS RSP.
  (* the same region as RSP, in the address form the code computes it *)
  assert (RSP' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 A) + 224) 8)
    by (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia; exact RSP).
  step.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit hi),
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit lo) by lia.
  step.
  destruct (Z_lt_le_dec (Z.lor hi lo) rest) as [Hlt|Hge].
  - if_true_by (eq_trans (f1_ltu _ _ HL Hrest) (proj2 (Z.ltb_lt _ _) Hlt)).
    step. step. step.
    rewrite (Z.min_l _ _ (Z.lt_le_incl _ _ Hlt)).
    apply ExecF.evtF_done. reflexivity.
  - if_false_by (eq_trans (f1_ltu _ _ HL Hrest) (proj2 (Z.ltb_ge _ _) Hge)).
    step. step. step. step.
    rewrite (Z.min_r _ _ Hge).
    apply ExecF.evtF_done. reflexivity.
Qed.

(* ---- the whole run 0x81d40 -> the allocator entry 0x5337c. ---- *)
Lemma f1_evt_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A q left : Z) (b0 b1 k0 k1 : byte),
    s1 = Z_to_bv 64 A -> s6 = Z_to_bv 64 q -> s9 = Z_to_bv 64 left -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= q -> q + left < 2 ^ 63 -> 1 <= left < 2 ^ 26 -> 0 <= A -> A + 232 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k0] ->
    (bv_signed k0 = 0 \/ q mod 8 < bv_signed k0) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    (2 <= left ->
       ov_read_bytes rsegs m (wa (Z.shiftr (q + 1) 3 + ASAN_K)) 1 = Some [k1] /\
       (bv_signed k1 = 0 \/ (q + 1) mod 8 < bv_signed k1) /\
       ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    store_ok rsegs m (wa (A + 224)) 8 = true ->
    ExecF.rng RNG (Z.shiftr q 3 + ASAN_K) 1 ->
    ExecF.rng RNG q 1 ->
    ExecF.rng RNG (Z.shiftr (q + 1) 3 + ASAN_K) 1 ->
    ExecF.rng RNG (q + 1) 1 ->
    ExecF.rng RNG (A + 224) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR (Z_to_bv 64 0x81da4) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0))
                                          (left - Z.min 2 left)))
                       a1' a2' a3 a4 a5 a6 a7
                       (Z_to_bv 64 (Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0))
                                          (left - Z.min 2 left)))
                       s3 (Z_to_bv 64 (q + Z.min 2 left)) s5 s6 s7 s8 (Z_to_bv 64 (left - Z.min 2 left)) s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5337c) fc None
                  (write_to_mem m (wa (A + 224)) (le8 (Z_to_bv 64 (left - Z.min 2 left)))) (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d40) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A q left b0 b1 k0 k1 -> -> -> -> Hq0 Hq1 Hl HA0 HA1 HK0 Hk0 HB0 H2 HS RSH0 RQ0 RSH1 RQ1 RSP.
  pose proof (bv_unsigned_in_range 8 b0) as Hb0. pose proof (bv_unsigned_in_range 8 b1) as Hb1.
  change (bv_modulus 8) with 256 in Hb0, Hb1.
  (* the same regions as RQ0 / RQ1, in the address forms the code computes them *)
  assert (RQ0' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 q)) 1)
    by (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia; exact RQ0).
  assert (RQ1' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 q) + 1) 1)
    by (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia; exact RQ1).
  apply (f1_chk0_F RNG ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 q) s7 s8
           (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6 F fc m _ q k0 eq_refl eq_refl ltac:(lia) HK0 Hk0);
    [| exact RSH0].
  intros a0' a1'.
  step. step. step. step.
  destruct (Z.eq_dec left 1) as [E1|E1].
  - (* left = 1: h = 1, len = 0, the high byte is not read *)
    subst left.
    if_false_by (eq_refl : negb (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 1)) = false).
    step. step. step.
    eapply ExecF.evtF_mono.
    { eapply f1_tail_F with (A := A) (lo := bv_unsigned b0) (hi := 0) (rest := 0);
        [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | | lia | exact HS
         | exact RSP].
      rewrite Z.lor_0_l. lia. }
    intros ms' ->. do 2 eexists.
    replace (Z.min (bv_unsigned b0 + (if 2 <=? 1 then 256 * bv_unsigned b1 else 0)) (1 - Z.min 2 1))
      with (Z.min (Z.lor 0 (bv_unsigned b0)) 0) by (rewrite Z.lor_0_l; cbn; lia).
    replace (1 - Z.min 2 1) with 0 by lia.
    replace (q + Z.min 2 1) with (q + 1) by lia.
    reflexivity.
  - (* left >= 2: h = 2 *)
    if_true_by (f1_ne left 1 ltac:(lia) ltac:(lia) E1).
    destruct (H2 ltac:(lia)) as (HK1 & Hk1 & HB1).
    apply (f1_chk1_F RNG ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (zxb b0) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3
             (Z_to_bv 64 (q + 1)) s5 (Z_to_bv 64 q) s7 s8 (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6
             F fc m _ (q + 1) k1 eq_refl eq_refl ltac:(lia) HK1 Hk1);
      [| exact RSH1].
    intros a1'' a2''.
    step. step. step. step.
    eapply ExecF.evtF_mono.
    { eapply f1_tail_F with (A := A) (lo := bv_unsigned b0) (rest := left + -2);
        [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | | | lia | exact HS
         | exact RSP].
      - rewrite f1_zxb_u, Z.shiftl_mul_pow2 by lia. lia.
      - rewrite f1_L. lia. }
    intros ms' ->. do 2 eexists.
    rewrite f1_L.
    rewrite (proj2 (Z.leb_le 2 left)) by lia.
    replace (Z.min 2 left) with 2 by lia.
    replace (left - 2) with (left + -2) by lia.
    reflexivity.
Qed.

(* ---- F1.v's four statements as corollaries at RNG_all (the check that each _F is the old statement plus the
   footprint premises, nothing weaker). The two CPS continuations come back with ExecF_all.evt_evtF_all. ---- *)

Lemma f1_chk0_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (q : Z) (k : byte),
    s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 ASAN_K -> 0 <= q < 2 ^ 63 ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k] ->
    (bv_signed k = 0 \/ q mod 8 < bv_signed k) ->
    (forall a0' a1' : word, evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x81d50) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d40) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q q k E6 E10 Hq HK Hk HC.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f1_chk0_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m Q q k); try assumption.
  - intros a0' a1'. apply EFA.evt_evtF_all. exact (HC a0' a1').
  - f1_rng_all.
Qed.

Lemma f1_chk1_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (q : Z) (k : byte),
    s4 = Z_to_bv 64 q -> s10 = Z_to_bv 64 ASAN_K -> 0 <= q < 2 ^ 63 ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k] ->
    (bv_signed k = 0 \/ q mod 8 < bv_signed k) ->
    (forall a1' a2' : word, evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x81d7c) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q q k E4 E10 Hq HK Hk HC.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f1_chk1_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m Q q k); try assumption.
  - intros a1' a2'. apply EFA.evt_evtF_all. exact (HC a1' a2').
  - f1_rng_all.
Qed.

Lemma f1_tail_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A lo hi rest : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 lo -> a1 = Z_to_bv 64 hi -> s9 = Z_to_bv 64 rest ->
    0 <= A -> A + 232 <= 2 ^ 64 -> 0 <= lo < 2 ^ 64 -> 0 <= hi < 2 ^ 64 -> 0 <= Z.lor hi lo < 2 ^ 64 ->
    0 <= rest < 2 ^ 64 ->
    store_ok rsegs m (wa (A + 224)) 8 = true ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81da4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.min (Z.lor hi lo) rest))
                          a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.min (Z.lor hi lo) rest)) s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6)
                    F (Z_to_bv 64 0x5337c) fc None (write_to_mem m (wa (A + 224)) (le8 (Z_to_bv 64 rest)))
                    (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d8c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A lo hi rest E1 Ea0 Ea1 E9 HA0 HA1 Hlo Hhi HL Hrest HS.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f1_tail_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m A lo hi rest); try assumption.
  f1_rng_all.
Qed.

Lemma f1_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A q left : Z) (b0 b1 k0 k1 : byte),
    s1 = Z_to_bv 64 A -> s6 = Z_to_bv 64 q -> s9 = Z_to_bv 64 left -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= q -> q + left < 2 ^ 63 -> 1 <= left < 2 ^ 26 -> 0 <= A -> A + 232 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k0] ->
    (bv_signed k0 = 0 \/ q mod 8 < bv_signed k0) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    (2 <= left ->
       ov_read_bytes rsegs m (wa (Z.shiftr (q + 1) 3 + ASAN_K)) 1 = Some [k1] /\
       (bv_signed k1 = 0 \/ (q + 1) mod 8 < bv_signed k1) /\
       ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    store_ok rsegs m (wa (A + 224)) 8 = true ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR (Z_to_bv 64 0x81da4) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0))
                                          (left - Z.min 2 left)))
                       a1' a2' a3 a4 a5 a6 a7
                       (Z_to_bv 64 (Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0))
                                          (left - Z.min 2 left)))
                       s3 (Z_to_bv 64 (q + Z.min 2 left)) s5 s6 s7 s8 (Z_to_bv 64 (left - Z.min 2 left)) s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5337c) fc None
                  (write_to_mem m (wa (A + 224)) (le8 (Z_to_bv 64 (left - Z.min 2 left)))) (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d40) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A q left b0 b1 k0 k1 E1 E6 E9 E10 Hq0 Hq1 Hl HA0 HA1 HK0 Hk0 HB0 H2 HS.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f1_evt_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m A q left b0 b1 k0 k1); try assumption; f1_rng_all.
Qed.

(* ---- The pins: each _of_F states F1.v's text, term for term (constr_eq: syntactic, not up to conversion). ---- *)

Example f1_chk0_of_F_verbatim : True.
Proof. let A := type of F1.f1_chk0 in let B := type of f1_chk0_of_F in constr_eq A B; exact I. Qed.

Example f1_chk1_of_F_verbatim : True.
Proof. let A := type of F1.f1_chk1 in let B := type of f1_chk1_of_F in constr_eq A B; exact I. Qed.

Example f1_tail_of_F_verbatim : True.
Proof. let A := type of F1.f1_tail in let B := type of f1_tail_of_F in constr_eq A B; exact I. Qed.

Example f1_evt_of_F_verbatim : True.
Proof. let A := type of F1.f1_evt in let B := type of f1_evt_of_F in constr_eq A B; exact I. Qed.
